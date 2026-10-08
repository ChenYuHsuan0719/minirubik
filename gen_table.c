#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

static const uint8_t source[3][CUBIES] = {
    {1, 4, 2, 0, 3, 5, 6},     // R
    {0, 1, 2, 4, 5, 6, 3},     // B
    {0, 2, 5, 3, 1, 4, 6},     // D
};

static const uint8_t twist[3][CUBIES] = {
    {1, 2, 0, 2, 1, 0, 0},     // R
    {0, 0, 0, 1, 2, 1, 2},     // B
    {0, 0, 0, 0, 0, 0, 0},     // D
};

static uint16_t perm_move[3][PERMUTATIONS], ori_move[3][ORIENTATIONS];
static void build_moves(void);

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

// PDB（呼叫前要先 build_moves()）
static uint8_t *PDB_Orientation_table(uint8_t *diameter) {
    uint8_t *dist = malloc(ORIENTATIONS);
    uint32_t *queue = malloc((size_t) ORIENTATIONS * sizeof *queue);
    uint32_t head = 0, tail = 1, level_end = 1;
    if (!dist|| !queue) {
        free(dist);
        free(queue);
        return NULL;
    }
    memset(dist, UINT8_MAX, ORIENTATIONS);
    queue[0] = 0;
    dist[0] = 0;
    *diameter = 0;
    while (head < tail) {
        if (head == level_end) {
            level_end = tail;
            ++*diameter;
        }
        uint32_t here = queue[head++];
        uint16_t o = (uint16_t) here;
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next_o = o;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next_o = ori_move[face][next_o];
                uint32_t there = (uint32_t)next_o;
                if (dist[there] == UINT8_MAX) {
                    dist[there] = (uint8_t) (dist[here] + 1U);
                    queue[tail++] = there;
                }
            }
        }
    }
    free(queue);
    if (tail != ORIENTATIONS) {
        free(dist);
        return NULL;
    }
    return dist;
}

static uint8_t *PDB_Permutation_table(uint8_t *diameter) {
    uint8_t *dist = malloc(PERMUTATIONS);
    uint32_t *queue = malloc((size_t) PERMUTATIONS * sizeof *queue);
    uint32_t head = 0, tail = 1, level_end = 1;
    if (!dist || !queue) {
        free(dist);
        free(queue);
        return NULL;
    }
    memset(dist, UINT8_MAX, PERMUTATIONS);
    queue[0] = 0;
    dist[0] = 0;
    *diameter = 0;
    while (head < tail) {
        if (head == level_end) {
            level_end = tail;
            ++*diameter;
        }
        uint32_t here = queue[head++];
        uint16_t p = (uint16_t) here;
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next_p = p;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next_p = perm_move[face][next_p];
                uint32_t there = (uint32_t)next_p;
                if (dist[there] == UINT8_MAX) {
                    dist[there] = (uint8_t) (dist[here] + 1U);
                    queue[tail++] = there;
                }
            }
        }
    }
    free(queue);
    if (tail != PERMUTATIONS) {
        free(dist);
        return NULL;
    }
    return dist;
}

static void build_moves(void)
{
    state_t state;
    for (uint16_t rank = 0; rank < PERMUTATIONS; ++rank) {
        unrank_state((uint32_t) rank * ORIENTATIONS, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            perm_move[face][rank] =
                (uint16_t) (rank_state(&next) / ORIENTATIONS);
        }
    }
    for (uint16_t rank = 0; rank < ORIENTATIONS; ++rank) {
        unrank_state(rank, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            ori_move[face][rank] =
                (uint16_t) (rank_state(&next) % ORIENTATIONS);
        }
    }
}

static int asm_mode; // 1 = 輸出組合語言，0 = 輸出 C


static void emit_u8(const char *name, const uint8_t *a, unsigned n) {
    if (asm_mode)
        printf("%s:", name);
    else
        printf("static const uint8_t %s[%u] = {", name, n);

    for (unsigned i = 0; i < n; ++i) {

        if(asm_mode) {
            if (i % 16 == 0)
                printf("\n    .byte ");
            else   
                printf(", ");

            printf("%u", (unsigned) a[i]);
        }
        else {
           if (i % 16 == 0)
                printf("\n    ");
           printf("%u, ", (unsigned) a[i]);
        }
    }

    if (asm_mode)
        printf("\n\n");
    else
        printf("\n};\n\n");
}

static void emit_u16(const char *name, const uint16_t *a, unsigned n) {

    if (asm_mode)
        printf("%s:", name);
    else
        printf("static const uint16_t %s[%u] = {", name, n);

    for (unsigned i = 0; i < n; ++i) {
        if(asm_mode) {
            if (i % 16 == 0)
                printf("\n    .half ");
            else   
                printf(", ");

            printf("%u", (unsigned) a[i]);
        }
        else {
            if (i % 16 == 0)
                printf("\n    ");
           printf("%u, ", (unsigned) a[i]);
        }
    }

    if (asm_mode)
        printf("\n\n");
    else
        printf("\n};\n\n");
}


int main(int argc, char **argv) {
    uint8_t diameter_p, diameter_o;

    build_moves();

    uint8_t *pdb_p = PDB_Permutation_table(&diameter_p);
    uint8_t *pdb_o = PDB_Orientation_table(&diameter_o);

    asm_mode = argc == 2 && !strcmp(argv[1], "--asm");

    if(asm_mode) {
        printf("# Generated by gen_table.c. Do not edit.\n");
        printf(".data\n");
    }
    else {
        printf("/* Generated by gen_table.c. Do not edit. */\n");
        printf("#ifndef TABLES_H\n#define TABLES_H\n\n#include <stdint.h>\n\n");
    }

    if(pdb_p == NULL) {
        fprintf(stderr, "pdb_p error\n");
        return 1;
    }
    if(pdb_o == NULL) {
        fprintf(stderr, "pdb_o error\n");
        return 1;
    }


    emit_u16("perm_move_R", perm_move[0], PERMUTATIONS);
    emit_u16("perm_move_B", perm_move[1], PERMUTATIONS);
    emit_u16("perm_move_D", perm_move[2], PERMUTATIONS);
    emit_u16("ori_move_R", ori_move[0], ORIENTATIONS);
    emit_u16("ori_move_B", ori_move[1], ORIENTATIONS);
    emit_u16("ori_move_D", ori_move[2], ORIENTATIONS);

    emit_u8("pdb_p", pdb_p, PERMUTATIONS);
    emit_u8("pdb_o", pdb_o, ORIENTATIONS);

    if (!asm_mode) printf("#endif\n");

    fprintf(stderr, "max distance p : %u, o : %u\n", (unsigned)diameter_p, (unsigned)diameter_o);

    free(pdb_p);
    free(pdb_o);
    return 0;
}