/* solver_assembly_friendly.c
 *
 * 和 optimized_solver_seperate_table_iterative_without_build_table.c 解法相同
 * （IDA* + 兩張 PDB，表來自 tables.h），但 target 部分改寫成容易翻成 RV32I 的樣子。
 *
 * 檔案分成兩部分：
 *   [TARGET] 之後要翻成 solver.s 的程式碼。規則：
 *            1. 不用 *、/、%（RV32I 沒有乘除指令）
 *            2. 區域變數一律 uint32_t（= 一個暫存器），只有陣列用 uint8_t / uint16_t
 *            3. 全域陣列 = solver.s 的 .data；註解寫出對應的 load/store 指令
 *            4. heuristic 直接寫在 IDA* 迴圈裡，不另外呼叫函式
 *   [HOST]   只在 host 上跑的驗證工具（--self-test、--verify），可以自由使用乘除，
 *            用原本的 rank_state / build_table 當標準答案。
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tables.h"

enum {
    CUBIES = 7,
    PERMUTATIONS = 5040, // 7!
    ORIENTATIONS = 729,  // 3 ^ 6
    STATES = PERMUTATIONS * ORIENTATIONS,
    MOVES = 9,
    MAX_DEPTH = 11,      // 直徑
    NO_FACE = 3,         // 起點沒有「上一面」
    NOT_FOUND = 0xFF     // ida_star 失敗時的回傳值
};

/* ======================================================================
 * [TARGET] 資料：對應 solver.s 的 .data
 * ====================================================================== */

/* 轉移表的起始位址。asm：perm_tab: .word perm_move_R, perm_move_B, perm_move_D
 * 取用方式：slli t, face, 2 → add → lw 得到該面的表的位址 */
static const uint16_t *const perm_move[3] = {perm_move_R, perm_move_B, perm_move_D};
static const uint16_t *const ori_move[3] = {ori_move_R, ori_move_B, ori_move_D};

/* move 編號 → 面 / 轉幾次，取代 move / 3 和 move % 3。asm：.byte 表，lbu 讀取 */
static const uint8_t move_face[MOVES] = {0, 0, 0, 1, 1, 1, 2, 2, 2};
static const uint8_t move_turn[MOVES] = {0, 1, 2, 0, 1, 2, 0, 1, 2};

/* 印解答用。asm：每個名稱一個 .string，再用一個 .word 表存 9 個位址 */
static const char *const move_names[MOVES] = {"R",  "R2", "R'", "B", "B2",
                                              "B'", "D",  "D2", "D'"};

/* 解析後的輸入（取代 state_t）。asm：.zero 7 */
static uint8_t in_p[CUBIES], in_o[CUBIES];

/* IDA* 的工作陣列（取代遞迴的 stack）。uint16_t 的陣列索引要 slli 1 */
static uint16_t sp[MAX_DEPTH + 1], so[MAX_DEPTH + 1]; // 第 d 層的狀態
static uint16_t cp[MAX_DEPTH + 1], co[MAX_DEPTH + 1]; // 第 d 層目前試到的子狀態
static uint8_t last_face[MAX_DEPTH + 1];              // 第 d 層的上一步是哪一面
static uint8_t next[MAX_DEPTH + 1];                   // 第 d 層下一個要試的 move
static uint8_t path[MAX_DEPTH];                       // path[d] = 第 d 步的 move
static uint32_t nodes;                                // 展開的節點數（Stage 3 用）

/* ======================================================================
 * [TARGET] 輸入轉換：字串 → in_p / in_o → p、o
 * ====================================================================== */

/* 解析 14 個字元並檢查合法性。合法回傳 1，否則回傳 0。
 * 取代原本的 parse_state + valid：
 *   - 拆成兩個迴圈，不需要 i % 7
 *   - 重複檢查用 bitmask（seen 的第 v 個 bit），不需要雙層迴圈
 *   - sum % 3 改成重複減 3（sum 最大 14，最多減 4 次）
 * 暫存器：a0 = s，t0 = i，t1 = c，t2 = seen，t3 = sum，t4 = bit
 */
static uint32_t parse_input(const char *s)
{
    uint32_t i, c, seen, sum, bit;

    seen = 0;
    for (i = 0; i < 7; ++i) {
        c = (uint8_t) s[i];                    // lbu
        if (c < '1' || c > '7')                // 兩個分支
            return 0;
        c = c - '1';                           // addi
        bit = 1U << c;                         // sll（位移量在暫存器裡）
        if (seen & bit)                        // and + bnez：這個數字出現過了
            return 0;
        seen = seen | bit;                     // or
        in_p[i] = (uint8_t) c;                 // sb
    }

    sum = 0;
    for (i = 0; i < 7; ++i) {
        c = (uint8_t) s[i + 7];                // lbu 7(addr)
        if (c < '1' || c > '3')
            return 0;
        c = c - '1';
        sum = sum + c;
        in_o[i] = (uint8_t) c;                 // sb
    }

    if (s[14] != '\0')                         // 長度必須剛好 14
        return 0;

    while (sum >= 3)                           // 取代 sum % 3
        sum = sum - 3;
    return sum == 0;
}

/* permutation 的 Lehmer code，結果 0..5039。
 * 原本：p = p * (7 - i) + smaller。乘法改成「加 k 次」。
 * i = 6 時 k = 1、smaller = 0，結果不變，所以只跑 i = 0..5。
 * 暫存器：t0 = i，t1 = j，t2 = smaller，t3 = k，t4 = prod，t5/t6 = 暫存，a0 = p
 */
static uint32_t rank_perm(void)
{
    uint32_t i, j, smaller, k, prod, p;

    p = 0;
    for (i = 0; i < 6; ++i) {
        smaller = 0;                           // 排在 i 後面、比 in_p[i] 小的個數
        for (j = i + 1; j < 7; ++j)
            if (in_p[j] < in_p[i])             // 兩次 lbu + bgeu
                smaller = smaller + 1;

        k = 7 - i;                             // 乘數 7, 6, 5, 4, 3, 2
        prod = 0;
        for (j = 0; j < k; ++j)                // prod = p * k
            prod = prod + p;
        p = prod + smaller;
    }
    return p;
}

/* orientation 的 base-3 編碼，結果 0..728。第 7 個由總和決定，不用編進去。
 * 原本：o = o * 3 + in_o[i]。o * 3 = (o << 1) + o。
 * 暫存器：t0 = i，t1 = 暫存，a0 = o
 */
static uint32_t rank_ori(void)
{
    uint32_t i, o;

    o = 0;
    for (i = 0; i < 6; ++i)
        o = (o << 1) + o + in_o[i];            // slli + add + lbu + add
    return o;
}

/* ======================================================================
 * [TARGET] IDA*（迭代版）
 * ====================================================================== */

/* 回傳解的長度，解放在 path[0..長度-1]；失敗回傳 NOT_FOUND。
 * 和原本的 ida_star 走訪順序完全相同，所以解答和 nodes 數也相同。
 *
 * 暫存器規劃（全部 callee-saved，因為整個搜尋都要保留）：
 *   s0 = p0       s1 = o0       s2 = bound    s3 = min
 *   s4 = d        s5 = move     s6 = face     s7 = np（子狀態的 p）
 *   s8 = no（子狀態的 o）       s9 = h / f
 *   t0..t6 = 計算位址用的暫存
 */
static uint32_t ida_star(uint32_t p0, uint32_t o0)
{
    uint32_t bound, min, d, move, face, np, no, h, ho, f;

    nodes = 0;
    if ((p0 | o0) == 0)                        // or + beqz：已經是 solved
        return 0;

    h = pdb_p[p0];                             // lbu
    ho = pdb_o[o0];                            // lbu
    if (ho > h)                                // bgeu
        h = ho;
    bound = h;                                 // 第一輪的 bound = h(root)

    while (bound <= MAX_DEPTH) {
        min = 0xFF;                            // 這一輪被剪掉的最小 f
        d = 0;
        sp[0] = (uint16_t) p0;                 // sh
        so[0] = (uint16_t) o0;
        last_face[0] = NO_FACE;                // sb
        next[0] = 0;
        nodes = nodes + 1;

        for (;;) {
            move = next[d];                    // lbu
            if (move == MOVES) {               // 這層 9 個 move 都試完了：回上一層
                if (d == 0)
                    break;
                d = d - 1;
                continue;
            }
            next[d] = (uint8_t) (move + 1);    // sb

            face = move_face[move];            // lbu
            if (face == last_face[d]) {        // 剪枝：不連續轉同一面，整面跳過
                next[d] = (uint8_t) (move + 3);
                continue;
            }

            // 同一面的 X, X2, X' 依序試：X 從父狀態出發，X2 / X' 在前一個子狀態上再轉 90 度
            if (move_turn[move] == 0) {
                np = sp[d];                    // lhu（位址 = sp + (d << 1)）
                no = so[d];
            } else {
                np = cp[d];
                no = co[d];
            }
            np = perm_move[face][np];          // lw 表位址，再 lhu（位址 = 表 + (np << 1)）
            no = ori_move[face][no];
            cp[d] = (uint16_t) np;             // sh
            co[d] = (uint16_t) no;

            h = pdb_p[np];                     // heuristic 直接寫在這裡
            ho = pdb_o[no];
            if (ho > h)
                h = ho;
            f = d + 1 + h;
            if (f > bound) {                   // 剪掉，記錄最小的 f
                if (f < min)
                    min = f;
                continue;
            }

            path[d] = (uint8_t) move;          // sb
            if ((np | no) == 0)                // 找到 solved
                return d + 1;

            d = d + 1;                         // 往下一層（對應遞迴版的「呼叫 dfs」）
            sp[d] = (uint16_t) np;
            so[d] = (uint16_t) no;
            last_face[d] = (uint8_t) face;
            next[d] = 0;
            nodes = nodes + 1;
        }
        bound = min;                           // 下一輪的 bound = 這輪被剪掉的最小 f
    }
    return NOT_FOUND;
}

/* ======================================================================
 * [TARGET] 輸出：對應 asm 的 ecall（a7 = 4 印字串、a7 = 11 印字元）
 * ====================================================================== */

static void print_solution(uint32_t length)
{
    uint32_t i;

    for (i = 0; i < length; ++i) {
        if (i != 0)
            putchar(' ');                      // ecall 11
        fputs(move_names[path[i]], stdout);    // lw 名稱位址，ecall 4
    }
    putchar('\n');
}

/* ======================================================================
 * [HOST] 以下只在 host 上跑，不需要翻成組合語言
 * ====================================================================== */

typedef struct {
    uint8_t p[CUBIES], o[CUBIES];
} state_t;

static const uint8_t inverse_move[MOVES] = {2, 1, 0, 5, 4, 3, 8, 7, 6};
static const uint8_t source[3][CUBIES] = {
    {1, 4, 2, 0, 3, 5, 6}, // R
    {0, 1, 2, 4, 5, 6, 3}, // B
    {0, 2, 5, 3, 1, 4, 6}, // D
};
static const uint8_t twist[3][CUBIES] = {
    {1, 2, 0, 2, 1, 0, 0}, // R
    {0, 0, 0, 1, 2, 1, 2}, // B
    {0, 0, 0, 0, 0, 0, 0}, // D
};

static state_t quarter_turn(state_t state, uint8_t face)
{
    state_t result;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t from = source[face][i];
        result.p[i] = state.p[from];
        result.o[i] = (uint8_t) ((state.o[from] + twist[face][i]) % 3U);
    }
    return result;
}

static state_t apply_move(state_t state, uint8_t move)
{
    uint8_t turns = (uint8_t) (move % 3U + 1U);
    for (uint8_t i = 0; i < turns; ++i)
        state = quarter_turn(state, (uint8_t) (move / 3U));
    return state;
}

/* 原本的 rank_state：當作 rank_perm / rank_ori 的標準答案 */
static uint32_t rank_state(const state_t *state)
{
    uint32_t p = 0, o = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t smaller = 0;
        for (uint8_t j = (uint8_t) (i + 1U); j < CUBIES; ++j)
            if (state->p[j] < state->p[i])
                ++smaller;
        p = p * (CUBIES - i) + smaller;
    }
    for (uint8_t i = 0; i < 6; ++i)
        o = o * 3U + state->o[i];
    return p * ORIENTATIONS + o;
}

static void unrank_state(uint32_t rank, state_t *state)
{
    uint8_t available[CUBIES] = {0, 1, 2, 3, 4, 5, 6};
    uint32_t p = rank / ORIENTATIONS, o = rank % ORIENTATIONS, f = 720;
    uint8_t sum = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t q = (uint8_t) (p / f);
        p %= f;
        state->p[i] = available[q];
        for (uint8_t j = q; j + 1U < (unsigned) (CUBIES - i); ++j)
            available[j] = available[j + 1U];
        if (i < 5)
            f /= 6U - i;
    }
    for (uint8_t i = 6; i-- > 0;) {
        state->o[i] = (uint8_t) (o % 3U);
        sum = (uint8_t) (sum + state->o[i]);
        o /= 3U;
    }
    state->o[6] = (uint8_t) ((3U - sum % 3U) % 3U);
}

/* 完整的 BFS 表：每個狀態「往解的方向」那一步，用來算精確距離。
 * 轉移表由 quarter_turn 自己建，不用 tables.h，讓標準答案和被測的程式互相獨立。 */
static uint8_t *build_table(uint8_t *diameter)
{
    uint8_t *toward_solved = malloc(STATES);
    uint32_t *queue = malloc((size_t) STATES * sizeof *queue);
    uint16_t permutation[3][PERMUTATIONS], orientation[3][ORIENTATIONS];
    uint32_t head = 0, tail = 1, level_end = 1;
    state_t state;
    if (!toward_solved || !queue) {
        free(toward_solved);
        free(queue);
        return NULL;
    }
    for (uint16_t rank = 0; rank < PERMUTATIONS; ++rank) {
        unrank_state((uint32_t) rank * ORIENTATIONS, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next_state = quarter_turn(state, face);
            permutation[face][rank] =
                (uint16_t) (rank_state(&next_state) / ORIENTATIONS);
        }
    }
    for (uint16_t rank = 0; rank < ORIENTATIONS; ++rank) {
        unrank_state(rank, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next_state = quarter_turn(state, face);
            orientation[face][rank] =
                (uint16_t) (rank_state(&next_state) % ORIENTATIONS);
        }
    }
    memset(toward_solved, UINT8_MAX, STATES);
    queue[0] = 0;
    toward_solved[0] = 0;
    *diameter = 0;
    while (head < tail) {
        if (head == level_end) {
            level_end = tail;
            ++*diameter;
        }
        uint32_t here = queue[head++];
        uint16_t p = (uint16_t) (here / ORIENTATIONS);
        uint16_t o = (uint16_t) (here % ORIENTATIONS);
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next_p = p, next_o = o;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next_p = permutation[face][next_p];
                next_o = orientation[face][next_o];
                uint32_t there = (uint32_t) next_p * ORIENTATIONS + next_o;
                if (toward_solved[there] == UINT8_MAX) {
                    toward_solved[there] = inverse_move[face * 3U + turn];
                    queue[tail++] = there;
                }
            }
        }
    }
    free(queue);
    if (tail != STATES) {
        free(toward_solved);
        return NULL;
    }
    return toward_solved;
}

/* 把 state_t 寫成 14 個字元的輸入字串（parse_input 的反向） */
static void state_to_string(const state_t *state, char *s)
{
    for (int i = 0; i < CUBIES; ++i) {
        s[i] = (char) ('1' + state->p[i]);
        s[i + CUBIES] = (char) ('1' + state->o[i]);
    }
    s[14] = '\0';
}

/* 對全部 3,674,160 個狀態檢查：
 *   輸入轉換：state → 字串 → parse_input → rank_perm / rank_ori，要等於 rank / 729、rank % 729
 *   H1：h <= 精確距離
 *   H3：IDA* 解的長度 = 精確距離，而且套回去真的會到 solved
 */
static int verify(void)
{
    uint8_t diameter;
    uint8_t *table = build_table(&diameter);
    if (!table)
        return 0;
    uint32_t max_nodes = 0;
    uint64_t total_nodes = 0;
    for (uint32_t rank = 0; rank < STATES; ++rank) {
        state_t state;
        char s[15];
        unrank_state(rank, &state);
        state_to_string(&state, s);
        if (!parse_input(s)) {
            fprintf(stderr, "parse_input rejected valid state %s\n", s);
            goto fail;
        }
        uint32_t p = rank_perm(), o = rank_ori();
        if (p != rank / ORIENTATIONS || o != rank % ORIENTATIONS) {
            fprintf(stderr, "rank mismatch at %s: got p=%u o=%u\n", s,
                    (unsigned) p, (unsigned) o);
            goto fail;
        }

        uint8_t d = 0; // 照完整表走回 solved，走幾步就是精確距離
        for (uint32_t r = rank; r; r = rank_state(&state), ++d)
            state = apply_move(state, table[r]);

        uint32_t h = pdb_p[p] > pdb_o[o] ? pdb_p[p] : pdb_o[o];
        if (h > d) {
            fprintf(stderr, "H1 failed at %s\n", s);
            goto fail;
        }
        uint32_t length = ida_star(p, o);
        unrank_state(rank, &state);
        for (uint32_t i = 0; i < length && length != NOT_FOUND; ++i)
            state = apply_move(state, path[i]);
        if (length != d || rank_state(&state) != 0) {
            fprintf(stderr, "H3 failed at %s\n", s);
            goto fail;
        }
        total_nodes += nodes;
        if (nodes > max_nodes)
            max_nodes = nodes;
    }
    free(table);
    printf("input conversion, H1, H3 passed for %u states; "
           "max nodes %u; total nodes %llu\n",
           (unsigned) STATES, (unsigned) max_nodes,
           (unsigned long long) total_nodes);
    return 1;
fail:
    free(table);
    return 0;
}

static int self_test(void)
{
    const state_t solved = {{0, 1, 2, 3, 4, 5, 6}, {0}};
    state_t state;
    for (uint8_t move = 0; move < MOVES; ++move) {
        state = apply_move(solved, move);
        state = apply_move(state, inverse_move[move]);
        if (memcmp(&solved, &state, sizeof solved))
            return 0;
    }
    for (uint32_t rank = 0; rank < STATES; ++rank) {
        unrank_state(rank, &state);
        if (rank_state(&state) != rank)
            return 0;
    }
    uint8_t diameter;
    uint8_t *table = build_table(&diameter);
    if (!table)
        return 0;
    free(table);
    return diameter == 11;
}

static int output_failed(void)
{
    return fflush(stdout) != 0 || ferror(stdout);
}

int main(int argc, char **argv)
{
    if (argc == 2 && !strcmp(argv[1], "--self-test")) {
        if (!self_test()) {
            fputs("self-test failed\n", stderr);
            return 1;
        }
        puts("3674160 states; diameter 11");
        return output_failed();
    }
    if (argc == 2 && !strcmp(argv[1], "--verify"))
        return !verify() || output_failed();

    /* [TARGET] 以下是 solver.s 的 main：在 asm 裡，輸入字串放在 .data */
    if (argc != 2 || !parse_input(argv[1])) {
        fprintf(stderr, "usage: %s PPPPPPPOOOOOOO\n",
                argc > 0 && argv[0] ? argv[0] : "solver");
        return 2;
    }
    uint32_t length = ida_star(rank_perm(), rank_ori());
    if (length == NOT_FOUND) {
        fputs("search failed\n", stderr);
        return 1;
    }
    print_solution(length);
    return output_failed();
}
