# solver.s — IDA* + PDB solver for the 2x2x2 cube, RV32I only

# ecall（a7）：1 = 印整數、4 = 印字串、10 = 結束、11 = 印字元


.data
.align 2                        # tables.s 的長度是奇數，先對齊到 4 的倍數

# 轉移表的起始位址，用 face 選表：slli t, face, 2 → add → lw
perm_tab:   .word perm_move_R, perm_move_B, perm_move_D
ori_tab:    .word ori_move_R, ori_move_B, ori_move_D

# 印解答用的字串，name_tab[move] = 該 move 名稱的位址
n_R:        .string "R"
n_R2:       .string "R2"
n_Rp:       .string "R'"
n_B:        .string "B"
n_B2:       .string "B2"
n_Bp:       .string "B'"
n_D:        .string "D"
n_D2:       .string "D2"
n_Dp:       .string "D'"
.align 2
name_tab:   .word n_R, n_R2, n_Rp, n_B, n_B2, n_Bp, n_D, n_D2, n_Dp

# IDA* 的工作陣列（uint16_t，索引要 slli 1）
.align 1
sp_arr:     .zero 24            # uint16_t sp[12]：第 d 層的狀態 p
so_arr:     .zero 24            # uint16_t so[12]：第 d 層的狀態 o
cp_arr:     .zero 24            # uint16_t cp[12]：第 d 層目前試到的子狀態 p
co_arr:     .zero 24            # uint16_t co[12]：第 d 層目前試到的子狀態 o

# uint8_t 陣列（索引直接加）
last_face:  .zero 12            # 第 d 層的上一步是哪一面
next_mv:    .zero 12            # 第 d 層下一個要試的 move
path:       .zero 11            # path[d] = 第 d 步的 move
in_p:       .zero 7             # 解析後的 permutation（0..6）
in_o:       .zero 7             # 解析後的 orientation（0..2）
move_face:  .byte 0, 0, 0, 1, 1, 1, 2, 2, 2
move_turn:  .byte 0, 1, 2, 0, 1, 2, 0, 1, 2

# 要解的狀態（Ripes 沒有命令列參數）
input:      .string "21345671111111"
msg_bad:    .string "invalid input\n"
msg_fail:   .string "search failed\n"





.text

main:
    la   a0, input
    jal  ra, parse_input        # a0 = 1 合法 / 0 不合法
    beqz a0, bad_input

    jal  ra, rank_perm          # a0 = p
    mv   s0, a0                 # 先存起來，rank_ori 會用到 a0
    jal  ra, rank_ori           # a0 = o
    mv   a1, a0                 # a1 = o0
    mv   a0, s0                 # a0 = p0
    jal  ra, ida_star           # a0 = 解的長度，或 0xFF（失敗）

    li   t0, 0xFF
    beq  a0, t0, search_fail
    jal  ra, print_solution
    li   a0, 0
    j    exit

bad_input:
    la   a0, msg_bad
    li   a7, 4
    ecall
    j    exit

search_fail:
    la   a0, msg_fail
    li   a7, 4
    ecall

exit:
    li   a7, 10
    ecall


# parse_input(a0 = 字串位址) → a0 = 1 合法 / 0 不合法
# 暫存器：a0 = s，t0 = i，t1 = c，t2 = seen，t3 = sum，t4 = bit，t5/t6 = 暫存

parse_input:
    li   t2, 0                  # seen = 0
    li   t0, 0                  # i = 0
pi_loop_p:
    add  t5, a0, t0
    lbu  t1, 0(t5)              # c = s[i]
    li   t6, 49
    blt  t1, t6, pi_bad         # c < '1'
    li   t6, 55
    bgt  t1, t6, pi_bad         # c > '7'
    addi t1, t1, -49            # c = c - '1'
    li   t4, 1
    sll  t4, t4, t1             # bit = 1 << c
    and  t6, t2, t4
    bnez t6, pi_bad             # 這個數字出現過了
    or   t2, t2, t4             # seen |= bit
    la   t6, in_p
    add  t6, t6, t0
    sb   t1, 0(t6)              # in_p[i] = c
    addi t0, t0, 1
    li   t6, 7
    blt  t0, t6, pi_loop_p

    li   t3, 0                  # sum = 0
    li   t0, 0                  # i = 0
pi_loop_o:
    add  t5, a0, t0
    lbu  t1, 7(t5)              # c = s[i + 7]
    li   t6, 49
    blt  t1, t6, pi_bad         # c < '1'
    li   t6, 51
    bgt  t1, t6, pi_bad         # c > '3'
    addi t1, t1, -49            # c = c - '1'
    add  t3, t3, t1             # sum += c
    la   t6, in_o
    add  t6, t6, t0
    sb   t1, 0(t6)              # in_o[i] = c
    addi t0, t0, 1
    li   t6, 7
    blt  t0, t6, pi_loop_o

    lbu  t1, 14(a0)
    bnez t1, pi_bad             # 長度必須剛好 14

    li   t6, 3
pi_mod3:                        # 取代 sum % 3
    blt  t3, t6, pi_mod3_done
    addi t3, t3, -3
    j    pi_mod3
pi_mod3_done:
    seqz a0, t3                 # return sum == 0
    ret
pi_bad:
    li   a0, 0
    ret



# rank_perm() → a0 = p（0..5039）
# 暫存器：t0 = i，t1 = j，t2 = smaller，t3 = k，t4 = prod，a1 = in_p 位址，a2 = in_p[i]，t5/t6 = 暫存，a0 = p

rank_perm:
    li   a0, 0                  # p = 0
    li   t0, 0                  # i = 0
    la   a1, in_p
rp_outer:
    li   t2, 0                  # smaller = 0
    add  t5, a1, t0
    lbu  a2, 0(t5)              # a2 = in_p[i]
    addi t1, t0, 1              # j = i + 1
    li   t6, 7
rp_count:
    bge  t1, t6, rp_count_done
    add  t5, a1, t1
    lbu  t5, 0(t5)              # in_p[j]
    bgeu t5, a2, rp_count_next
    addi t2, t2, 1              # in_p[j] < in_p[i]：smaller++
rp_count_next:
    addi t1, t1, 1
    j    rp_count
rp_count_done:
    sub  t3, t6, t0             # k = 7 - i
    li   t4, 0                  # prod = 0
rp_mul:                         # prod = p * k（加 k 次）
    beqz t3, rp_mul_done
    add  t4, t4, a0
    addi t3, t3, -1
    j    rp_mul
rp_mul_done:
    add  a0, t4, t2             # p = prod + smaller
    addi t0, t0, 1
    li   t5, 6
    blt  t0, t5, rp_outer
    ret


# rank_ori() → a0 = o（0..728）
# 暫存器：t0 = i，t1 = 暫存，t2 = in_o 位址，t3 = 6，a0 = o

rank_ori:
    li   a0, 0                  # o = 0
    li   t0, 0                  # i = 0
    la   t2, in_o
    li   t3, 6
ro_loop:
    slli t1, a0, 1
    add  a0, t1, a0             # o = o * 3
    add  t1, t2, t0
    lbu  t1, 0(t1)
    add  a0, a0, t1             # o += in_o[i]
    addi t0, t0, 1
    blt  t0, t3, ro_loop
    ret


# 暫存器：
#   s0 = p0     s1 = o0     s2 = bound    s3 = min
#   s4 = d      s5 = move   s6 = face     s7 = np    s8 = no
#   s9 = h / f  s10 = pdb_p 位址          s11 = pdb_o 位址
#   t0..t6 = 算位址用的暫存（t4 = d << 1，uint16_t 陣列的位移）

ida_star:
    addi sp, sp, -64            # 存 ra 和 s0..s11
    sw   ra, 48(sp)
    sw   s0, 0(sp)
    sw   s1, 4(sp)
    sw   s2, 8(sp)
    sw   s3, 12(sp)
    sw   s4, 16(sp)
    sw   s5, 20(sp)
    sw   s6, 24(sp)
    sw   s7, 28(sp)
    sw   s8, 32(sp)
    sw   s9, 36(sp)
    sw   s10, 40(sp)
    sw   s11, 44(sp)

    mv   s0, a0                 # s0 = p0
    mv   s1, a1                 # s1 = o0
    la   s10, pdb_p
    la   s11, pdb_o

    or   t0, s0, s1
    beqz t0, ida_ret0           # 已經是 solved

    add  t0, s10, s0
    lbu  s9, 0(t0)              # h = pdb_p[p0]
    add  t0, s11, s1
    lbu  t1, 0(t0)              # ho = pdb_o[o0]
    bgeu s9, t1, ida_h0_done
    mv   s9, t1                 # h = max(h, ho)
ida_h0_done:
    mv   s2, s9                 # bound = h(root)

ida_round:                      # while (bound <= 11)
    li   t0, 11
    bgt  s2, t0, ida_fail
    li   s3, 0xFF               # min = 0xFF
    li   s4, 0                  # d = 0
    la   t0, sp_arr
    sh   s0, 0(t0)              # sp[0] = p0
    la   t0, so_arr
    sh   s1, 0(t0)              # so[0] = o0
    la   t0, last_face
    li   t1, 3
    sb   t1, 0(t0)              # last_face[0] = NO_FACE
    la   t0, next_mv
    sb   zero, 0(t0)            # next[0] = 0

ida_loop:
    la   t0, next_mv
    add  t0, t0, s4             # t0 = &next[d]（下面還會用到）
    lbu  s5, 0(t0)              # move = next[d]
    li   t1, 9
    beq  s5, t1, ida_up         # 這層 9 個 move 都試完了
    addi t1, s5, 1
    sb   t1, 0(t0)              # next[d] = move + 1

    la   t2, move_face
    add  t2, t2, s5
    lbu  s6, 0(t2)              # face = move_face[move]
    la   t3, last_face
    add  t3, t3, s4
    lbu  t3, 0(t3)              # last_face[d]
    bne  s6, t3, ida_expand
    addi t1, s5, 3              # 同一面剪枝：整面跳過
    sb   t1, 0(t0)              # next[d] = move + 3
    j    ida_loop

ida_up:
    beqz s4, ida_next_round     # d == 0：這一輪結束
    addi s4, s4, -1             # 回上一層
    j    ida_loop

ida_expand:
    slli t4, s4, 1              # t4 = d * 2（uint16_t 陣列的位移）
    la   t2, move_turn
    add  t2, t2, s5
    lbu  t2, 0(t2)
    bnez t2, ida_from_child
    la   t3, sp_arr             # X：從父狀態出發
    add  t3, t3, t4
    lhu  s7, 0(t3)              # np = sp[d]
    la   t3, so_arr
    add  t3, t3, t4
    lhu  s8, 0(t3)              # no = so[d]
    j    ida_turn
ida_from_child:
    la   t3, cp_arr             # X2 / X'：在前一個子狀態上再轉 90 度
    add  t3, t3, t4
    lhu  s7, 0(t3)              # np = cp[d]
    la   t3, co_arr
    add  t3, t3, t4
    lhu  s8, 0(t3)              # no = co[d]

ida_turn:
    slli t5, s6, 2              # face * 4（.word 表的位移）
    la   t3, perm_tab
    add  t3, t3, t5
    lw   t3, 0(t3)              # perm_move[face]
    slli t6, s7, 1
    add  t3, t3, t6
    lhu  s7, 0(t3)              # np = perm_move[face][np]
    la   t3, ori_tab
    add  t3, t3, t5
    lw   t3, 0(t3)              # ori_move[face]
    slli t6, s8, 1
    add  t3, t3, t6
    lhu  s8, 0(t3)              # no = ori_move[face][no]
    la   t3, cp_arr
    add  t3, t3, t4
    sh   s7, 0(t3)              # cp[d] = np
    la   t3, co_arr
    add  t3, t3, t4
    sh   s8, 0(t3)              # co[d] = no

    add  t3, s10, s7
    lbu  s9, 0(t3)              # h = pdb_p[np]
    add  t3, s11, s8
    lbu  t6, 0(t3)              # ho = pdb_o[no]
    bgeu s9, t6, ida_h_done
    mv   s9, t6                 # h = max(h, ho)
ida_h_done:
    add  s9, s9, s4
    addi s9, s9, 1              # f = d + 1 + h
    bleu s9, s2, ida_accept     # f <= bound：往下展開
    bgeu s9, s3, ida_loop       # f > bound：剪掉，更新 min
    mv   s3, s9
    j    ida_loop

ida_accept:
    la   t3, path
    add  t3, t3, s4
    sb   s5, 0(t3)              # path[d] = move
    or   t3, s7, s8
    beqz t3, ida_found          # 到 solved 了
    addi s4, s4, 1              # d = d + 1
    slli t4, s4, 1
    la   t3, sp_arr
    add  t3, t3, t4
    sh   s7, 0(t3)              # sp[d] = np
    la   t3, so_arr
    add  t3, t3, t4
    sh   s8, 0(t3)              # so[d] = no
    la   t3, last_face
    add  t3, t3, s4
    sb   s6, 0(t3)              # last_face[d] = face
    la   t3, next_mv
    add  t3, t3, s4
    sb   zero, 0(t3)            # next[d] = 0
    j    ida_loop

ida_next_round:
    mv   s2, s3                 # bound = min
    j    ida_round

ida_found:
    addi a0, s4, 1              # return d + 1
    j    ida_done
ida_fail:
    li   a0, 0xFF
    j    ida_done
ida_ret0:
    li   a0, 0

ida_done:
    lw   s0, 0(sp)              # 還原 s0..s11 和 ra
    lw   s1, 4(sp)
    lw   s2, 8(sp)
    lw   s3, 12(sp)
    lw   s4, 16(sp)
    lw   s5, 20(sp)
    lw   s6, 24(sp)
    lw   s7, 28(sp)
    lw   s8, 32(sp)
    lw   s9, 36(sp)
    lw   s10, 40(sp)
    lw   s11, 44(sp)
    lw   ra, 48(sp)
    addi sp, sp, 64
    ret





print_solution:
    mv   t1, a0                 # t1 = 長度
    li   t0, 0                  # i = 0
ps_loop:
    bge  t0, t1, ps_end
    beqz t0, ps_name
    li   a0, 32                 # ' '
    li   a7, 11
    ecall
ps_name:
    la   t2, path
    add  t2, t2, t0
    lbu  t2, 0(t2)              # move = path[i]
    slli t2, t2, 2
    la   t3, name_tab
    add  t3, t3, t2
    lw   t3, 0(t3)              # t3 = move_names[move]
ps_char:
    lbu  a0, 0(t3)
    beqz a0, ps_next            # 讀到 '\0' 就停
    li   a7, 11
    ecall
    addi t3, t3, 1
    j    ps_char
ps_next:
    addi t0, t0, 1
    j    ps_loop
ps_end:
    li   a0, 10                 # '\n'
    li   a7, 11
    ecall
    ret
