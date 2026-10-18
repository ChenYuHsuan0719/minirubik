# solver_LED.s — IDA* + PDB solver for the 2x2x2 cube, RV32I only，加上 LED matrix 動畫

# ecall（a7）：1 = 印整數、4 = 印字串、10 = 結束、11 = 印字元
#
# 兩種 build，同一份原始碼，只差在 renderer：
#   Ripes 的組譯器不支援 .if，所以 renderer 用「# >>> RENDER」和「# <<< RENDER」框起來。
#   GUI build（有動畫）：cat tables.s solver_LED.s > full_led.s
#   CLI build（量 iret）：cat tables.s solver_LED.s | sed '/# >>> RENDER/,/# <<< RENDER/d' > full_cli.s
#   CLI build 和 solver.s 執行的指令完全相同。
#
# GUI 要先在 I/O 分頁加一個 LED Matrix：Width = 35、Height = 25


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
msg_ok:     .string "OK\n"
msg_path_bad: .string "FAIL\n"

# ---------------- check_path 和 LED 共用的資料 ----------------
.align 2
# 目前的方塊狀態，8 個位置（位置 0 固定放方塊 0、不扭轉）
# 四個陣列連續擺、對齊 4，複製時用兩個 lw/sw
cube_p:     .zero 8             # cube_p[i] = 位置 i 上的方塊編號
cube_o:     .zero 8             # cube_o[i] = 位置 i 的扭轉（0..2）
next_p:     .zero 8             # quarter turn 的暫存
next_o:     .zero 8

# 8 個位置版本的 source / twist（位置 0 不動），索引是目的地，值是來源
src8:
    .byte 0, 2, 5, 3, 1, 4, 6, 7        # R
    .byte 0, 1, 2, 3, 5, 6, 7, 4        # B
    .byte 0, 1, 3, 6, 4, 2, 5, 7        # D
twist8:
    .byte 0, 1, 2, 0, 2, 1, 0, 0        # R
    .byte 0, 0, 0, 0, 1, 2, 1, 2        # B
    .byte 0, 0, 0, 0, 0, 0, 0, 0        # D

# >>> RENDER
# ---------------- LED 顯示用的資料 ----------------
# 展開圖 8x6 張貼紙，一張 4x3 像素，面與面之間隔 1 像素：寬 35、高 20
.equ LED_STRIDE, 140            # 一列 35 顆 LED * 4 bytes（render 裡的 sw 位移照這個算）
.equ LED_COUNT, 875             # 35 * 25
.equ DELAY, 300000              # 每一步之間的空轉次數，GUI 裡太快或太慢就調這個

.align 2
# corner_rgb[c][k]：方塊 c 的第 k 張貼紙的顏色（0xRRGGBB）
# k = 0 是 U/D 那張，k = 1、2 是從角的外面看順時針繞下去的兩張
# 白 U、黃 D、綠 F、藍 B、紅 R、橘 L
corner_rgb:
    .word 0xFFFFFF, 0xFF5800, 0x009B48  # 0 FUL: U L F
    .word 0xFFFFFF, 0x009B48, 0xB71234  # 1 FUR: U F R
    .word 0xFFD500, 0xB71234, 0x009B48  # 2 FDR: D R F
    .word 0xFFD500, 0x009B48, 0xFF5800  # 3 FDL: D F L
    .word 0xFFFFFF, 0xB71234, 0x0046AD  # 4 BUR: U R B
    .word 0xFFD500, 0x0046AD, 0xB71234  # 5 BDR: D B R
    .word 0xFFD500, 0xFF5800, 0x0046AD  # 6 BDL: D L B
    .word 0xFFFFFF, 0x0046AD, 0xFF5800  # 7 BUL: U B L

# facelet_off[i][k]：位置 i 的第 k 張貼紙，左上角像素相對 LED_MATRIX_0_BASE 的 byte 位移
# 格子 (fx, fy) → x0 = fx*4 + fx/2，y0 = fy*3 + fy/2，位移 = 4 * (y0*35 + x0)
facelet_off:
    .word 456, 996, 1016                # 0: U(2,1) L(1,2) F(2,2)
    .word 472, 1032, 1052               # 1: U(3,1) F(3,2) R(4,2)
    .word 2012, 1472, 1452              # 2: D(3,4) R(4,3) F(3,3)
    .word 1996, 1436, 1416              # 3: D(2,4) F(2,3) L(1,3)
    .word 52, 1068, 1088                # 4: U(3,0) R(5,2) B(6,2)
    .word 2432, 1508, 1488              # 5: D(3,5) B(6,3) R(5,3)
    .word 2416, 1400, 1524              # 6: D(2,5) L(0,3) B(7,3)
    .word 36, 1104, 980                 # 7: U(2,0) B(7,2) L(0,2)

# 3x5 字型：15 bits，一列 3 bits，最高位（bit 14）是左上角
#   U        L        F        R        B        D        2        '
#   1.1      1..      111      11.      11.      11.      111      .1.
#   1.1      1..      1..      1.1      1.1      1.1      ..1      .1.
#   1.1      1..      11.      11.      11.      1.1      111      ...
#   1.1      1..      1..      1.1      1.1      1.1      1..      ...
#   111      111      1..      1.1      11.      11.      111      ...
.align 2
# 面的標籤：疊在每個面中央（面的左上角往右 2、往下 1），用黑色畫
label_glyph:
    .word 0x5B6F, 0x4927, 0x79A4, 0x6BAD, 0x6BAE, 0x6B6E   # U L F R B D
label_off:                              # 4 * (y * 35 + x)
    .word 184, 1128, 1164, 1200, 1236, 2144                # (11,1) (2,8) (11,8) (20,8) (29,8) (11,15)

# 目前這一步：face 字母 + 後綴，畫在 D 下面的空白 5 列（第 20..24 列）
face_glyph:     .word 0x6BAD, 0x6BAE, 0x6B6E               # R B D
suffix_glyph:   .word 0, 0x73E7, 0x2400                    # 無、2、'
.equ STRIP_OFF, 2800            # 第 20 列的開頭 = 4 * 20 * 35
.equ STRIP_WORDS, 175           # 5 列 * 35
.equ MOVE_OFF, 2840             # 步驟文字左上角 (10, 20) = 4 * (20 * 35 + 10)
.equ TEXT_RGB, 0xFFFFFF
# <<< RENDER





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
    mv   s1, a0                 # s1 = 解的長度（print_solution 會蓋掉 a0）
    jal  ra, print_solution
    mv   a0, s1
    jal  ra, check_path         # 重放 path[]，印 OK / FAIL
# >>> RENDER
    mv   a0, s1
    jal  ra, animate            # 照解答一步一步重播並畫到 LED
# <<< RENDER
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



# >>> RENDER
# ======================================================================
# LED 動畫：從輸入狀態開始，照 path[] 一步一步重播，每一步重畫一次
# 畫面來自 solver 實際算出的 path，不是預錄的
# ======================================================================

# animate(a0 = 解的長度)
# 暫存器：s0 = i，s1 = 長度
animate:
    addi sp, sp, -16
    sw   ra, 8(sp)
    sw   s0, 0(sp)
    sw   s1, 4(sp)
    mv   s1, a0

    jal  ra, load_cube          # 從輸入狀態開始
    jal  ra, led_clear
    jal  ra, render             # 先畫出初始狀態（還沒有步驟可以顯示）
    jal  ra, draw_labels
    jal  ra, delay

    li   s0, 0                  # i = 0
an_loop:
    bge  s0, s1, an_done
    la   t0, path
    add  t0, t0, s0
    lbu  a0, 0(t0)              # move = path[i]
    jal  ra, apply_move8
    jal  ra, render
    jal  ra, draw_labels
    la   t0, path
    add  t0, t0, s0
    lbu  a0, 0(t0)              # move = path[i]（apply_move8 會蓋掉 a0）
    jal  ra, draw_move
    jal  ra, delay
    addi s0, s0, 1
    j    an_loop
an_done:
    lw   s0, 0(sp)
    lw   s1, 4(sp)
    lw   ra, 8(sp)
    addi sp, sp, 16
    ret


# render()：狀態 → 24 張貼紙 → LED
# 位置 i 的第 k 張貼紙顏色 = corner_rgb[cube_p[i]][(k - cube_o[i]) mod 3]
# 暫存器：a0 = LED 基底，a1 = cube_p，a2 = cube_o，a3 = 走訪 facelet_off 的指標
#         a4 = corner_rgb，t0 = i，t1 = &corner_rgb[c][0]，t2 = o，t3 = k
render:
    li   a0, LED_MATRIX_0_BASE
    la   a1, cube_p
    la   a2, cube_o
    la   a3, facelet_off
    la   a4, corner_rgb
    li   t0, 0                  # i = 0
rd_pos:
    add  t1, a1, t0
    lbu  t1, 0(t1)              # c = cube_p[i]
    add  t2, a2, t0
    lbu  t2, 0(t2)              # o = cube_o[i]
    slli t3, t1, 3
    slli t1, t1, 2
    add  t1, t1, t3             # c * 12（一列 3 個 word）
    add  t1, a4, t1             # t1 = &corner_rgb[c][0]
    li   t3, 0                  # k = 0
rd_k:
    sub  t4, t3, t2             # j = k - o
    bgez t4, rd_j_ok
    addi t4, t4, 3              # 取代 % 3
rd_j_ok:
    slli t4, t4, 2
    add  t4, t1, t4
    lw   t5, 0(t4)              # rgb = corner_rgb[c][j]
    lw   t6, 0(a3)              # 這張貼紙的位移
    addi a3, a3, 4
    add  t6, a0, t6             # 左上角像素的位址
    sw   t5, 0(t6)              # 第 0 列（4 像素）
    sw   t5, 4(t6)
    sw   t5, 8(t6)
    sw   t5, 12(t6)
    sw   t5, 140(t6)            # 第 1 列 = + LED_STRIDE
    sw   t5, 144(t6)
    sw   t5, 148(t6)
    sw   t5, 152(t6)
    sw   t5, 280(t6)            # 第 2 列 = + 2 * LED_STRIDE
    sw   t5, 284(t6)
    sw   t5, 288(t6)
    sw   t5, 292(t6)
    addi t3, t3, 1
    li   t4, 3
    blt  t3, t4, rd_k
    addi t0, t0, 1
    li   t4, 8
    blt  t0, t4, rd_pos
    ret


# draw_glyph(a0 = 字型 bits, a1 = 左上角像素位址, a2 = 顏色)
# 只畫字型裡為 1 的像素，0 的地方保留原本的顏色
# 只用 a0、a1、t0..t2，呼叫端可以把迴圈狀態放在 a3..a7
draw_glyph:
    slli a0, a0, 17             # bit 14 移到 bit 31，用 bgez 判斷最高位
    li   t0, 5                  # 5 列
dg_row:
    mv   t2, a1
    li   t1, 3                  # 每列 3 像素
dg_col:
    bgez a0, dg_skip            # 最高位是 0：不畫
    sw   a2, 0(t2)
dg_skip:
    slli a0, a0, 1
    addi t2, t2, 4
    addi t1, t1, -1
    bnez t1, dg_col
    addi a1, a1, 140            # 下一列 = + LED_STRIDE
    addi t0, t0, -1
    bnez t0, dg_row
    ret


# draw_labels()：六個面的標籤，黑字疊在面中央
# 暫存器：a3 = label_glyph 指標，a4 = label_off 指標，a5 = 剩幾個，a6 = LED 基底
draw_labels:
    addi sp, sp, -4
    sw   ra, 0(sp)
    la   a3, label_glyph
    la   a4, label_off
    li   a5, 6
    li   a6, LED_MATRIX_0_BASE
lb_loop:
    lw   a0, 0(a3)              # 字型
    lw   a1, 0(a4)
    add  a1, a1, a6             # 位址 = 基底 + 位移
    li   a2, 0                  # 黑色
    jal  ra, draw_glyph
    addi a3, a3, 4
    addi a4, a4, 4
    addi a5, a5, -1
    bnez a5, lb_loop
    lw   ra, 0(sp)
    addi sp, sp, 4
    ret


# draw_move(a0 = move)：先清掉最下面 5 列，再寫 face 字母和後綴
# 暫存器：a3 = move，a4 = LED 基底
draw_move:
    addi sp, sp, -4
    sw   ra, 0(sp)
    mv   a3, a0
    li   a4, LED_MATRIX_0_BASE
    li   t0, STRIP_OFF
    add  t0, t0, a4
    li   t1, STRIP_WORDS
dm_clear:
    sw   zero, 0(t0)
    addi t0, t0, 4
    addi t1, t1, -1
    bnez t1, dm_clear

    la   t0, move_face
    add  t0, t0, a3
    lbu  t0, 0(t0)
    slli t0, t0, 2
    la   t1, face_glyph
    add  t1, t1, t0
    lw   a0, 0(t1)              # face_glyph[move_face[move]]
    li   a1, MOVE_OFF
    add  a1, a1, a4
    li   a2, TEXT_RGB
    jal  ra, draw_glyph

    la   t0, move_turn
    add  t0, t0, a3
    lbu  t0, 0(t0)
    slli t0, t0, 2
    la   t1, suffix_glyph
    add  t1, t1, t0
    lw   a0, 0(t1)              # suffix_glyph[move_turn[move]]
    li   a1, MOVE_OFF
    addi a1, a1, 16             # 往右 4 像素
    add  a1, a1, a4
    li   a2, TEXT_RGB
    jal  ra, draw_glyph
    lw   ra, 0(sp)
    addi sp, sp, 4
    ret


# led_clear()：整片 LED 塗黑（分隔線和空白處之後就不會再寫）
led_clear:
    li   t0, LED_MATRIX_0_BASE
    li   t1, LED_COUNT
lc_loop:
    sw   zero, 0(t0)
    addi t0, t0, 4
    addi t1, t1, -1
    bnez t1, lc_loop
    ret


# delay()：空轉，讓 GUI 看得出每一步
delay:
    li   t0, DELAY
dl_loop:
    addi t0, t0, -1
    bnez t0, dl_loop
    ret
# <<< RENDER

# ======================================================================
# check_path 和 LED 動畫共用：load_cube、apply_move8（不在 RENDER 裡，CLI build 也有）
# ======================================================================

# load_cube()：輸入狀態 → cube_p / cube_o（8 個位置）
# cube_p[0] = 0、cube_o[0] = 0；cube_p[i] = in_p[i-1] + 1、cube_o[i] = in_o[i-1]
# 暫存器：t0 = in_p，t1 = in_o，t2 = cube_p，t3 = cube_o，t4 = i，t5/t6 = 暫存
load_cube:
    la   t0, in_p
    la   t1, in_o
    la   t2, cube_p
    la   t3, cube_o
    sb   zero, 0(t2)
    sb   zero, 0(t3)
    li   t4, 0                  # i = 0
lc_copy:
    add  t5, t0, t4
    lbu  t5, 0(t5)
    addi t5, t5, 1              # 方塊編號 +1（位置 0 是固定的方塊 0）
    add  t6, t2, t4
    sb   t5, 1(t6)              # cube_p[i + 1]
    add  t5, t1, t4
    lbu  t5, 0(t5)
    add  t6, t3, t4
    sb   t5, 1(t6)              # cube_o[i + 1]
    addi t4, t4, 1
    li   t5, 7
    blt  t4, t5, lc_copy
    ret


# apply_move8(a0 = move)：把 move 套到 cube_p / cube_o 上
# 一次 quarter turn：next[i] = cube[src8[face][i]]，next_o 再加 twist8[face][i]
# 暫存器：a1 = face，a2 = 剩幾次 quarter turn，a3 = src8[face]，a4 = twist8[face]
#         a5 = cube_p（cube_o = a5 + 8、next_p = a5 + 16、next_o = a5 + 24）
apply_move8:
    la   t0, move_face
    add  t0, t0, a0
    lbu  a1, 0(t0)              # face = move_face[move]
    la   t0, move_turn
    add  t0, t0, a0
    lbu  a2, 0(t0)
    addi a2, a2, 1              # turns = move_turn[move] + 1
    slli t0, a1, 3              # face * 8
    la   a3, src8
    add  a3, a3, t0
    la   a4, twist8
    add  a4, a4, t0
    la   a5, cube_p
am_turn:
    li   t0, 0                  # i = 0
am_cubie:
    add  t1, a3, t0
    lbu  t1, 0(t1)              # from = src8[face][i]
    add  t2, a5, t1
    lbu  t3, 0(t2)              # cube_p[from]
    lbu  t4, 8(t2)              # cube_o[from]
    add  t2, a4, t0
    lbu  t5, 0(t2)              # twist8[face][i]
    add  t4, t4, t5
    li   t5, 3
    blt  t4, t5, am_nowrap      # 取代 % 3
    addi t4, t4, -3
am_nowrap:
    add  t2, a5, t0
    sb   t3, 16(t2)             # next_p[i] = cube_p[from]
    sb   t4, 24(t2)             # next_o[i] = (cube_o[from] + twist) mod 3
    addi t0, t0, 1
    li   t1, 8
    blt  t0, t1, am_cubie

    lw   t1, 16(a5)             # cube_p = next_p
    sw   t1, 0(a5)
    lw   t1, 20(a5)
    sw   t1, 4(a5)
    lw   t1, 24(a5)             # cube_o = next_o
    sw   t1, 8(a5)
    lw   t1, 28(a5)
    sw   t1, 12(a5)
    addi a2, a2, -1
    bnez a2, am_turn
    ret


# check_path(a0 = 解的長度)：從輸入狀態重放 path[]，確認回到 solved，印 OK / FAIL
# 只用 src8 / twist8，不經過 perm_move / ori_move，所以和搜尋用的表無關
# apply_move8 會用掉 a0..a5、t0..t5，所以迴圈狀態放 s0、s1，要存到 stack
# 暫存器：s0 = i，s1 = 長度
check_path:
    addi sp, sp, -16
    sw   ra, 8(sp)
    sw   s0, 0(sp)
    sw   s1, 4(sp)
    mv   s1, a0                 # s1 = 長度

    jal  ra, load_cube
    li   s0, 0                  # i = 0
cp_loop:
    bge  s0, s1, cp_test        # i >= 長度：重放完了
    la   t0, path
    add  t0, t0, s0
    lbu  a0, 0(t0)              # a0 = path[i]
    jal  ra, apply_move8
    addi s0, s0, 1
    j    cp_loop

cp_test:                        # solved：cube_p[i] == i、cube_o[i] == 0，i = 0..7
    la   t0, cube_p
    li   t1, 0                  # i = 0
cp_cmp:
    add  t2, t0, t1
    lbu  t3, 0(t2)              # cube_p[i]
    bne  t3, t1, cp_fail
    lbu  t3, 8(t2)              # cube_o[i]（cube_o = cube_p + 8）
    bnez t3, cp_fail
    addi t1, t1, 1
    li   t3, 8
    blt  t1, t3, cp_cmp
    la   a0, msg_ok
    j    cp_print
cp_fail:
    la   a0, msg_path_bad
cp_print:
    li   a7, 4
    ecall

    lw   s0, 0(sp)
    lw   s1, 4(sp)
    lw   ra, 8(sp)
    addi sp, sp, 16
    ret

