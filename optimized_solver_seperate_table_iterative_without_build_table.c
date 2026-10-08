#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tables.h"

static const uint16_t *const perm_move[3] = {perm_move_R, perm_move_B, perm_move_D};
static const uint16_t *const ori_move[3] = {ori_move_R, ori_move_B, ori_move_D};



// (這個code用的方法) HTM - Half-Turn Metric，半轉度量 : 將任何單一面的旋轉（無論是 90 度順時針、90 度逆時針、或是 180 度半轉）都算作 1 步。
// QTM - Quarter-Turn Metric，四分之一轉度量 : 以 90 度（四分之一轉）作為基本單位。 90 度轉與逆 90 度轉算 1 步，而 180 度半轉（例如 R2）被視為連續轉了兩個 90 度，因此算作 2 步。

// 0 : Fix (左上)

/* 展開圖（exterior unfold）：每個面都是從魔方外面看
                UP
                ┌───┬───┐
                │ 7 │ 4 │
                ├───┼───┤
                │ 0 │ 1 │
                └───┴───┘

  LEFT         FRONT         RIGHT         BACK
┌───┬───┐     ┌───┬───┐     ┌───┬───┐     ┌───┬───┐
│ 7 │ 0 │     │ 0 │ 1 │     │ 1 │ 4 │     │ 4 │ 7 │
├───┼───┤     ├───┼───┤     ├───┼───┤     ├───┼───┤
│ 6 │ 3 │     │ 3 │ 2 │     │ 2 │ 5 │     │ 5 │ 6 │
└───┴───┘     └───┴───┘     └───┴───┘     └───┴───┘

                DOWN
                ┌───┬───┐
                │ 3 │ 2 │
                ├───┼───┤
                │ 6 │ 5 │
                └───┴───┘
 */



enum {
    CUBIES = 7,
    PERMUTATIONS = 5040, // 7!
    ORIENTATIONS = 729, // 3 ^ 6
    STATES = PERMUTATIONS * ORIENTATIONS,
    MOVES = 9 // 可轉的面 (3) * 轉法 (3)
};

typedef struct {
    uint8_t p[CUBIES], o[CUBIES];
} state_t;

/*@ predicate valid_state(state_t *state) =
      (\forall integer i; 0 <= i < CUBIES ==>
         state->p[i] < CUBIES && state->o[i] < 3) &&
      (\forall integer i, j; 0 <= i < j < CUBIES ==>
         state->p[i] != state->p[j]) &&
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
 */


 // 面 INDEX - R(0) : 站在魔方的右邊，往左看 / B(1) : 站在魔方的後面，往前看 / D(2) : 躺在魔方的下面，往上看
 
 // MOVES 的各意義和 INDEX
 // R(0) : 右面順時針轉 90 度 / R2(1) : 右面順時針轉 180 度 / R'(2) : 右面順時針轉 270 度 = 逆轉 90 度
 // B(3) : 後面順時針轉 90 度 / B2(4) : 後面順時針轉 180 度 / B'(5) : 面順時針轉 270 度 = 逆轉 90 度
 // D(6) : 下面順時針轉 90 度 / D2(7) : 下面順時針轉 180 度 / D'(8) : 下面時針轉 270 度 = 逆轉 90 度
 static const char *const move_names[MOVES] = {"R",  "R2", "R'", "B", "B2",
                                              "B'", "D",  "D2", "D'"};

// 索引是一個 move 的編號，值是「它的逆 move」的編號
static const uint8_t inverse_move[MOVES] = {2, 1, 0, 5, 4, 3, 8, 7, 6};
/* Each destination takes a cubie from source[face][destination]. */
// 3 : 可轉面(R、B、D)
// R2 = R 套用兩次 / R' = R 套用三次
// source 是寫死的常數表
// 索引是目的地，值是來源
static const uint8_t source[3][CUBIES] = {
    {1, 4, 2, 0, 3, 5, 6},     // R
    {0, 1, 2, 4, 5, 6, 3},     // B
    {0, 2, 5, 3, 1, 4, 6},     // D
};
// 轉完之後要額外加多少扭轉
// twist 是寫死的常數表
// 索引是目的地，值是來源
static const uint8_t twist[3][CUBIES] = {
    {1, 2, 0, 2, 1, 0, 0},     // R
    {0, 0, 0, 1, 2, 1, 2},     // B
    {0, 0, 0, 0, 0, 0, 0},     // D
};



/* The three quarter-turns preserve the fixed front-upper-left corner. */
/*@ requires face < 3;
    assigns \nothing;
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.p[i] == state.p[source[face][i]];
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.o[i] == (state.o[source[face][i]] + twist[face][i]) % 3;
 */
 // 只會轉 90°，R2 和 R' (B、D 都一樣)是 apply_move 重複呼叫產生的
static state_t quarter_turn(state_t state, uint8_t face)
{
    state_t result;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant \forall integer j; 0 <= j < i ==>
          result.p[j] == state.p[source[face][j]];
        loop invariant \forall integer j; 0 <= j < i ==>
          result.o[j] == (state.o[source[face][j]] + twist[face][j]) % 3;
        loop assigns i, result.p[0..6], result.o[0..6];
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t from = source[face][i];
        result.p[i] = state.p[from]; // 方塊編號原封不動地從 from 搬到 i
        result.o[i] = (uint8_t) ((state.o[from] + twist[face][i]) % 3U); // U 是在宣告「這裡的 % 是無號取餘」
    }
    return result;
}

static state_t apply_move(state_t state, uint8_t move)
{
    // /3 和 %3 就能直接拆出面和轉數，不需要任何查表
    // 轉數ex : B2 是 4，4 % 3 = 1，1 + 1 = 2，quarter_run 呼叫兩次
    // 面數ex : B2 是 4，4 / 3 = 1，B 的 index 是 1
    uint8_t turns = (uint8_t) (move % 3U + 1U);
    for (uint8_t i = 0; i < turns; ++i)
        state = quarter_turn(state, (uint8_t) (move / 3U));
    return state;
}

/*@ requires \valid_read(state);
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->p[i] < CUBIES;
    requires \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->o[i] < 3;
    assigns \nothing;
    ensures \result < STATES;
 */
 // 把一個魔方狀態變成一個整數，不重複，不浪費
static uint32_t rank_state(const state_t *state)
{
    uint32_t p = 0, o = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant (i == 0 ==> p == 0) && (i == 1 ==> p <= 6) &&
          (i == 2 ==> p <= 41) && (i == 3 ==> p <= 209) &&
          (i == 4 ==> p <= 839) && (i == 5 ==> p <= 2519) &&
          (i >= 6 ==> p <= 5039);
        loop assigns i, p;
        loop variant CUBIES - i;
     */
     // Lehmer code
    for (uint8_t i = 0; i < CUBIES; ++i) {
        // smaller : c[i] = 「排在 i 後面、數值比 p[i] 小的元素個數」
        uint8_t smaller = 0;
        /*@ loop invariant i + 1 <= j <= CUBIES;
            loop invariant smaller <= j - i - 1;
            loop assigns j, smaller;
            loop variant CUBIES - j;
         */
        for (uint8_t j = (uint8_t) (i + 1U); j < CUBIES; ++j)
            if (state->p[j] < state->p[i])
                ++smaller;
        p = p * (CUBIES - i) + smaller;
    }
    /*@ loop invariant 0 <= i <= 6;
        loop invariant (i == 0 ==> o == 0) && (i == 1 ==> o < 3) &&
          (i == 2 ==> o < 9) && (i == 3 ==> o < 27) &&
          (i == 4 ==> o < 81) && (i == 5 ==> o < 243) &&
          (i == 6 ==> o < 729);
        loop assigns i, o;
        loop variant 6 - i;
     */
    for (uint8_t i = 0; i < 6; ++i)
        o = o * 3U + state->o[i];
    return p * ORIENTATIONS + o;
}

/*@ requires \valid(state); requires rank < STATES; assigns *state; */
// rank 的反函數
static void unrank_state(uint32_t rank, state_t *state)
{
    uint8_t available[CUBIES] = {0, 1, 2, 3, 4, 5, 6};
    uint32_t p = rank / ORIENTATIONS, o = rank % ORIENTATIONS, f = 720;
    uint8_t sum = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t q = (uint8_t) (p / f);
        p %= f;
        state->p[i] = available[q];
        for (uint8_t j = q; j + 1U < CUBIES - i; ++j)
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

/*@ requires \valid_read(state);
    requires \initialized(&state->p[0..6]) && \initialized(&state->o[0..6]);
    assigns \nothing;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures complete: valid_state(state) ==> \result != 0;
 */
 // 判斷一個 state_t 是不是物理上可能存在的魔方擺法
static int valid(const state_t *state)
{
    uint8_t sum = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant sum <= 2 * i;
        loop invariant sum == (i > 0 ? state->o[0] : 0) +
          (i > 1 ? state->o[1] : 0) + (i > 2 ? state->o[2] : 0) +
          (i > 3 ? state->o[3] : 0) + (i > 4 ? state->o[4] : 0) +
          (i > 5 ? state->o[5] : 0) + (i > 6 ? state->o[6] : 0);
        loop invariant \forall integer j; 0 <= j < i ==>
          state->p[j] < CUBIES && state->o[j] < 3;
        loop invariant \forall integer j, k; 0 <= j < k < i ==>
          state->p[j] != state->p[k];
        loop assigns i, sum;
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        // 檢查 1：範圍
        if (state->p[i] >= CUBIES || state->o[i] >= 3)
            return 0;
        /*@ loop invariant 0 <= j <= i;
            loop invariant \forall integer k; 0 <= k < j ==>
              state->p[k] != state->p[i];
            loop assigns j;
            loop variant i - j;
        */
        for (uint8_t j = 0; j < i; ++j)
            // 檢查 2：重複
            if (state->p[j] == state->p[i])
                return 0;
        // 檢查 3：守恆律
        sum = (uint8_t) (sum + state->o[i]);
    }
    return sum % 3U == 0;
}

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
            state_t next = quarter_turn(state, face);
            permutation[face][rank] =
                (uint16_t) (rank_state(&next) / ORIENTATIONS);
        }
    }
    for (uint16_t rank = 0; rank < ORIENTATIONS; ++rank) {
        unrank_state(rank, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            orientation[face][rank] =
                (uint16_t) (rank_state(&next) % ORIENTATIONS);
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
            fprintf(stderr, "When Distance is %u, the number of state are %u.\n",  (unsigned)*diameter,  (unsigned)(level_end - head));
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
                    uint8_t move = (uint8_t) (face * 3U + turn);
                    toward_solved[there] = inverse_move[move];
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

/*@ requires valid_read_string(input);
    requires \valid(state);
    assigns state->p[0..6], state->o[0..6];
    ensures \result != 0 ==> input[14] == '\0';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] == input[i] - '1';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->o[i] == input[i + CUBIES] - '1';
 */

 // 檢查每個字元是不是合法數字、長度對不對
static int parse_state(const char *input, state_t *state)
{
    /*@ loop invariant 0 <= i <= 14;
        loop invariant i <= strlen(input);
        loop invariant i <= 7 ==> \initialized(&state->p[0..i-1]);
        loop invariant i >= 7 ==> \initialized(&state->p[0..6]);
        loop invariant i >= 7 ==> \initialized(&state->o[0..i-8]);
        loop invariant \forall integer j; 0 <= j < i && j < CUBIES ==>
          state->p[j] == input[j] - '1';
        loop invariant \forall integer j; 0 <= j < i - CUBIES ==>
          state->o[j] == input[j + CUBIES] - '1';
        loop assigns i, state->p[0..6], state->o[0..6];
        loop variant 14 - i;
     */
    for (int i = 0; i < 14; ++i) {
        int limit = i < 7 ? 7 : 3;
        if (input[i] < '1' || input[i] > '0' + limit)
            return 0;
        (i < 7 ? state->p : state->o)[i % 7] = (uint8_t) (input[i] - '1');
    }
    return input[14] == '\0' && valid(state);
}




// IDA*（迭代版）：用陣列當 stack，第 d 格存第 d 層的資料
enum {
    MAX_DEPTH = 11, // 直徑
    NO_FACE = 3     // 起點沒有「上一面」
};

// 用查表取代 move / 3 和 move % 3（RV32I 沒有除法）
static const uint8_t move_face[MOVES] = {0, 0, 0, 1, 1, 1, 2, 2, 2};
static const uint8_t move_turn[MOVES] = {0, 1, 2, 0, 1, 2, 0, 1, 2};


static uint8_t path[MAX_DEPTH];  // path[d] = 第 d 步的 move
static uint32_t nodes;           // 展開的節點數（Stage 3 用）

// h = 兩個 PDB 取 max，兩個都是下界，所以 max 也是下界
static uint8_t heuristic(uint16_t p, uint16_t o)
{
    return pdb_p[p] > pdb_o[o] ? pdb_p[p] : pdb_o[o];
}

// 回傳解的長度，解放在 path[0..長度-1]；失敗回傳 UINT8_MAX
static uint8_t ida_star(uint16_t p0, uint16_t o0)
{
    // 遞迴版每一層的參數和區域變數，改存在這些陣列裡
    uint16_t sp[MAX_DEPTH + 1], so[MAX_DEPTH + 1]; // 第 d 層的狀態
    uint16_t cp[MAX_DEPTH + 1], co[MAX_DEPTH + 1]; // 第 d 層目前試到的子狀態
    uint8_t last_face[MAX_DEPTH + 1];               // 第 d 層的上一步是哪一面
    uint8_t next[MAX_DEPTH + 1];                    // 第 d 層下一個要試的 move
    uint8_t bound = heuristic(p0, o0);
    nodes = 0;
    if (p0 == 0 && o0 == 0)
        return 0;
    while (bound <= MAX_DEPTH) {
        uint8_t min = UINT8_MAX; // 這一輪被剪掉的最小 f
        uint8_t d = 0;
        sp[0] = p0;
        so[0] = o0;
        last_face[0] = NO_FACE;
        next[0] = 0;
        ++nodes;
        for (;;) {
            if (next[d] == MOVES) { // 這層 9 個 move 都試完了：回上一層
                if (d == 0)
                    break;
                --d;
                continue;
            }
            uint8_t move = next[d]++;
            uint8_t face = move_face[move];
            if (face == last_face[d]) { // 剪枝：不連續轉同一面，整面跳過
                next[d] = (uint8_t) (move + 3U);
                continue;
            }
            // 同一面的 X, X2, X' 依序試，每次在前一個子狀態上多轉 90 度
            if (move_turn[move] == 0) {
                cp[d] = sp[d];
                co[d] = so[d];
            }
            cp[d] = perm_move[face][cp[d]];
            co[d] = ori_move[face][co[d]];
            uint8_t f = (uint8_t) (d + 1U + heuristic(cp[d], co[d]));
            if (f > bound) {
                if (f < min)
                    min = f;
                continue;
            }
            path[d] = move;
            if (cp[d] == 0 && co[d] == 0)
                return (uint8_t) (d + 1U);
            // 往下一層（對應遞迴版的「呼叫 dfs」）
            sp[d + 1] = cp[d];
            so[d + 1] = co[d];
            last_face[d + 1] = face;
            next[d + 1] = 0;
            ++d;
            ++nodes;
        }
        bound = min; // 下一輪的 bound = 這輪被剪掉的最小 f
    }
    return UINT8_MAX;
}

/* Host-side gate H1、H3：用 build_table 當標準答案，掃過全部狀態 */
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
        unrank_state(rank, &state);
        // 照完整表走回 solved，走幾步就是精確距離 d
        uint8_t d = 0;
        for (uint32_t r = rank; r; r = rank_state(&state), ++d)
            state = apply_move(state, table[r]);
        uint16_t p = (uint16_t) (rank / ORIENTATIONS);
        uint16_t o = (uint16_t) (rank % ORIENTATIONS);
        if (heuristic(p, o) > d) { // H1
            fprintf(stderr, "H1 failed at rank %u\n", (unsigned) rank);
            free(table);
            return 0;
        }
        uint8_t length = ida_star(p, o);
        unrank_state(rank, &state); // 把解套回去，確認真的會到 solved
        for (uint8_t i = 0; i < length && length != UINT8_MAX; ++i)
            state = apply_move(state, path[i]);
        if (length != d || rank_state(&state) != 0) { // H3
            fprintf(stderr, "H3 failed at rank %u\n", (unsigned) rank);
            free(table);
            return 0;
        }
        total_nodes += nodes;
        if (nodes > max_nodes)
            max_nodes = nodes;
    }
    free(table);
    printf("H1, H3 passed for %u states; max nodes %u; total nodes %llu\n",
           (unsigned) STATES, (unsigned) max_nodes,
           (unsigned long long) total_nodes);
    return 1;
}


/* stdout is fully buffered off a terminal, so a write error surfaces at the
 * flush, not at the printf that queued the bytes. Every exit path that has
 * produced output goes through here.
 */
static int output_failed(void)
{
    return fflush(stdout) != 0 || ferror(stdout);
}

static int self_test(void)
{
    const state_t solved = {{0, 1, 2, 3, 4, 5, 6}, {0}};
    state_t state;
    for (uint8_t move = 0; move < MOVES; ++move) {
        state = solved;
        state = apply_move(state, move);
        state = apply_move(state, inverse_move[move]);
        if (memcmp(&solved, &state, sizeof solved))
            return 0;
    }
    for (uint32_t rank = 0; rank < STATES; ++rank) {
        unrank_state(rank, &state);
        if (!valid(&state) || rank_state(&state) != rank)
            return 0;
    }
    return 1;
}

int main(int argc, char **argv)
{
    state_t state;
    uint8_t diameter;
    if (argc == 2 && !strcmp(argv[1], "--self-test")) {
        if (!self_test()) {
            fputs("self-test failed\n", stderr);
            return 1;
        }
        uint8_t *table = build_table(&diameter);
        if (!table) {
            fputs("could not build complete state table\n", stderr);
            return 1;
        }
        free(table);
        if (diameter != 11) {
            fputs("BFS check failed\n", stderr);
            return 1;
        }
        puts("3674160 states; diameter 11");
        return output_failed();
    }

    if (argc == 2 && !strcmp(argv[1], "--verify"))
        return !verify() || output_failed();

    
    if (argc != 2 || !parse_state(argv[1], &state)) {
        /* C99 5.1.2.2.1 lets argv[0] be null when argc is 0. */
        fprintf(stderr, "usage: %s PPPPPPPOOOOOOO\n",
                argc > 0 && argv[0] ? argv[0] : "solver");
        return 2;
    }
    
    uint32_t rank = rank_state(&state);
    uint8_t length = ida_star((uint16_t) (rank / ORIENTATIONS),
                              (uint16_t) (rank % ORIENTATIONS));
    
    if (length == UINT8_MAX) {
        fputs("search failed\n", stderr);
        return 1;
    }
    for (uint8_t i = 0; i < length; ++i)
        printf("%s%s", i ? " " : "", move_names[path[i]]);
    putchar('\n');
    return output_failed();
}
