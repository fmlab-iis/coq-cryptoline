proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 a4_0, uint64 b0_0, uint64 b1_0, uint64 b2_0, uint64 b3_0, uint64 b4_0) =
{ true && and [a0_0 <u 72057594037927928@64, a1_0 <u 72057594037927928@64, a2_0 <u 72057594037927928@64, a3_0 <u 72057594037927928@64, a4_0 <u 4503599627370488@64, b0_0 <u 72057594037927928@64, b1_0 <u 72057594037927928@64, b2_0 <u 72057594037927928@64, b3_0 <u 72057594037927928@64, b4_0 <u 4503599627370488@64] }
mull rdx_1 rax_2 b0_0 a3_0;
mull rdx_2 rax_4 b1_0 a2_0;
adds carry_1 rcx_2 rax_2 rax_4;
adc r15_2 rdx_1 rdx_2 carry_1;
mull rdx_3 rax_6 b2_0 a1_0;
adds carry_2 rcx_3 rcx_2 rax_6;
adc r15_3 r15_2 rdx_3 carry_2;
mull rdx_4 rax_8 b3_0 a0_0;
adds carry_3 rcx_4 rcx_3 rax_8;
adc r15_4 r15_3 rdx_4 carry_3;
mull rdx_5 rax_10 b4_0 a4_0;
and rax_11@uint64 rax_10 4503599627370495@uint64;
mull rdx_8 rax_12 rax_11 68719492368@uint64;
adds carry_4 rcx_5 rcx_4 rax_12;
adc r15_5 r15_4 rdx_8 carry_4;
join tmpp_1 rdx_5 rax_10;
split r8_2 tmp_to_use_1 tmpp_1 52;
vpc r8_3@uint64 r8_2;
vpc tmp_to_use_p_1@uint64 tmp_to_use_1;
assume tmp_to_use_1 = rax_11 && true;
and rsi_2@uint64 rcx_5 4503599627370495@uint64;
join tmp_2 r15_5 rcx_5;
split rcx_6 tmp_to_use_2 tmp_2 52;
vpc rcx_7@uint64 rcx_6;
vpc tmp_to_use_p_2@uint64 tmp_to_use_2;
assume tmp_to_use_2 = rsi_2 && true;
mull rdx_10 rax_14 b0_0 a4_0;
adds carry_5 rcx_8 rcx_7 rax_14;
adc r15_7 0@uint64 rdx_10 carry_5;
mull rdx_11 rax_16 b1_0 a3_0;
adds carry_6 rcx_9 rcx_8 rax_16;
adc r15_8 r15_7 rdx_11 carry_6;
mull rdx_12 rax_18 b2_0 a2_0;
adds carry_7 rcx_10 rcx_9 rax_18;
adc r15_9 r15_8 rdx_12 carry_7;
mull rdx_13 rax_20 b3_0 a1_0;
adds carry_8 rcx_11 rcx_10 rax_20;
adc r15_10 r15_9 rdx_13 carry_8;
mull rdx_14 rax_22 b4_0 a0_0;
adds carry_9 rcx_12 rcx_11 rax_22;
adc r15_11 r15_10 rdx_14 carry_9;
mull rdx_16 rax_24 r8_3 68719492368@uint64;
adds carry_10 rcx_13 rcx_12 rax_24;
adc r15_12 r15_11 rdx_16 carry_10;
and rsi_4@uint64 rcx_13 4503599627370495@uint64;
join tmpp_2 r15_12 rcx_13;
split rcx_14 tmp_to_use_3 tmpp_2 52;
vpc rcx_15@uint64 rcx_14;
vpc tmp_to_use_p_3@uint64 tmp_to_use_3;
assume tmp_to_use_3 = rsi_4 && true;
split rax_26 tmp_to_use_4 rsi_4 48;
and rsi_5@uint64 rsi_4 281474976710655@uint64;
assume rsi_5 = tmp_to_use_4 && true;
mull rdx_18 rax_29 b0_0 a0_0;
mull rdx_19 rax_31 b1_0 a4_0;
adds carry_11 rcx_16 rcx_15 rax_31;
adc r15_14 0@uint64 rdx_19 carry_11;
mull rdx_20 rax_33 b2_0 a3_0;
adds carry_12 rcx_17 rcx_16 rax_33;
adc r15_15 r15_14 rdx_20 carry_12;
mull rdx_21 rax_35 b3_0 a2_0;
adds carry_13 rcx_18 rcx_17 rax_35;
adc r15_16 r15_15 rdx_21 carry_13;
mull rdx_22 rax_37 b4_0 a1_0;
adds carry_14 rcx_19 rcx_18 rax_37;
adc r15_17 r15_16 rdx_22 carry_14;
and rsi_7@uint64 rcx_19 4503599627370495@uint64;
join tmpp_3 r15_17 rcx_19;
split rcx_20 tmp_to_use_5 tmpp_3 52;
vpc rcx_21@uint64 rcx_20;
vpc tmp_to_use_p_4@uint64 tmp_to_use_5;
assume tmp_to_use_5 = rsi_7 && true;
shl rsi_8 rsi_7 4;
or rsi_9@uint64 rsi_8 rax_26;
assume rsi_9 = rsi_8 + rax_26 && true;
mull rdx_24 rax_40 4294968273@uint64 rsi_9;
adds carry_15 r8_5 rax_29 rax_40;
adc r9_3 rdx_18 rdx_24 carry_15;
and rax_42@uint64 r8_5 4503599627370495@uint64;
join tmpp_4 r9_3 r8_5;
split r8_6 tmp_to_use_6 tmpp_4 52;
vpc r8_7@uint64 r8_6;
vpc tmp_to_use_p_5@uint64 tmp_to_use_6;
assume tmp_to_use_6 = rax_42 && true;
mull rdx_26 rax_44 b0_0 a1_0;
adds carry_16 r8_8 r8_7 rax_44;
adc r9_5 0@uint64 rdx_26 carry_16;
mull rdx_27 rax_46 b1_0 a0_0;
adds carry_17 r8_9 r8_8 rax_46;
adc r9_6 r9_5 rdx_27 carry_17;
mull rdx_28 rax_48 b2_0 a4_0;
adds carry_18 rcx_22 rcx_21 rax_48;
adc r15_19 0@uint64 rdx_28 carry_18;
mull rdx_29 rax_50 b3_0 a3_0;
adds carry_19 rcx_23 rcx_22 rax_50;
adc r15_20 r15_19 rdx_29 carry_19;
mull rdx_30 rax_52 b4_0 a2_0;
adds carry_20 rcx_24 rcx_23 rax_52;
adc r15_21 r15_20 rdx_30 carry_20;
and rax_54@uint64 rcx_24 4503599627370495@uint64;
mull rdx_33 rax_55 rax_54 68719492368@uint64;
adds carry_21 r8_10 r8_9 rax_55;
adc r9_7 r9_6 rdx_33 carry_21;
join tmpp_5 r15_21 rcx_24;
split rcx_25 tmp_to_use_7 tmpp_5 52;
vpc rcx_26@uint64 rcx_25;
vpc tmp_to_use_p_6@uint64 tmp_to_use_7;
assume tmp_to_use_7 = rax_54 && true;
and rax_57@uint64 r8_10 4503599627370495@uint64;
join tmpp_6 r9_7 r8_10;
split r8_11 tmp_to_use_8 tmpp_6 52;
vpc r8_12@uint64 r8_11;
vpc tmp_to_use_p_7@uint64 tmp_to_use_8;
assume tmp_to_use_8 = rax_57 && true;
mull rdx_35 rax_59 b0_0 a2_0;
adds carry_22 r8_13 r8_12 rax_59;
adc r9_9 0@uint64 rdx_35 carry_22;
mull rdx_36 rax_61 b1_0 a1_0;
adds carry_23 r8_14 r8_13 rax_61;
adc r9_10 r9_9 rdx_36 carry_23;
mull rdx_37 rax_63 b2_0 a0_0;
adds carry_24 r8_15 r8_14 rax_63;
adc r9_11 r9_10 rdx_37 carry_24;
mull rdx_38 rax_65 b3_0 a4_0;
adds carry_25 rcx_27 rcx_26 rax_65;
adc r15_23 0@uint64 rdx_38 carry_25;
mull rdx_39 rax_67 b4_0 a3_0;
adds carry_26 rcx_28 rcx_27 rax_67;
adc r15_24 r15_23 rdx_39 carry_26;
and rax_69@uint64 rcx_28 4503599627370495@uint64;
mull rdx_42 rax_70 rax_69 68719492368@uint64;
adds carry_27 r8_16 r8_15 rax_70;
adc r9_12 r9_11 rdx_42 carry_27;
join tmpp_7 r15_24 rcx_28;
split rcx_29 tmp_to_use_9 tmpp_7 52;
vpc rcx_30@uint64 rcx_29;
vpc tmp_to_use_p_8@uint64 tmp_to_use_9;
assume tmp_to_use_9 = rax_69 && true;
and rax_72@uint64 r8_16 4503599627370495@uint64;
join tmpp_8 r9_12 r8_16;
split r8_17 tmp_to_use_10 tmpp_8 52;
vpc r8_18@uint64 r8_17;
vpc tmp_to_use_p_9@uint64 tmp_to_use_10;
assume tmp_to_use_10 = rax_72 && true;
add r8_19 r8_18 rsi_2;
mull rdx_45 rax_74 rcx_30 68719492368@uint64;
adds carry_28 r8_20 r8_19 rax_74;
adc r9_14 0@uint64 rdx_45 carry_28;
and rax_76@uint64 r8_20 4503599627370495@uint64;
join tmp_5 r9_14 r8_20;
split r8_21 tmp_to_use_11 tmp_5 52;
vpc r8_22@uint64 r8_21;
vpc tmp_to_use_p_10@uint64 tmp_to_use_11;
assume tmp_to_use_11 = rax_76 && true;
add r8_23 r8_22 rsi_5;
{ rax_42 + (rax_57 * 4503599627370496) + (rax_72 * 20282409603651670423947251286016) + (rax_76 * 91343852333181432387730302044767688728495783936) + (r8_23 * 411376139330301510538742295639337626245683966408394965837152256) = (a0_0 + (a1_0 * 4503599627370496) + (a2_0 * 20282409603651670423947251286016) + (a3_0 * 91343852333181432387730302044767688728495783936) + (a4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (b0_0 + (b1_0 * 4503599627370496) + (b2_0 * 20282409603651670423947251286016) + (b3_0 * 91343852333181432387730302044767688728495783936) + (b4_0 * 411376139330301510538742295639337626245683966408394965837152256)) (mod 115792089237316195423570985008687907853269984665640564039457584007908834671663) && and [tmp_to_use_p_1 = rax_11, tmp_to_use_p_2 = rsi_2, tmp_to_use_p_3 = rsi_4, rsi_5 = tmp_to_use_4, tmp_to_use_p_4 = rsi_7, rsi_9 = add (rsi_8) (rax_26), tmp_to_use_p_5 = rax_42, tmp_to_use_p_6 = rax_54, tmp_to_use_p_7 = rax_57, tmp_to_use_p_8 = rax_69, tmp_to_use_p_9 = rax_72, tmp_to_use_p_10 = rax_76, rax_42 <u 9007199254740991@64, rax_57 <u 9007199254740991@64, rax_72 <u 9007199254740991@64, rax_76 <u 9007199254740991@64, r8_23 <u 562949953421311@64] }