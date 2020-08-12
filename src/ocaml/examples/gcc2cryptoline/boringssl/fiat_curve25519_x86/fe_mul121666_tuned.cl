(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=8G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=8G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  fe_mul121666_tuned.cl

Results of checking CNF formulas:       [OK]            3.302935 seconds
Finding polynomial coefficients         [OK]            0.161511 seconds
Verification result:                    [OK]            4.991026 seconds
*)

proc main(uint32 a0_0, uint32 a1_0, uint32 a2_0, uint32 a3_0, uint32 a4_0, uint32 a5_0, uint32 a6_0, uint32 a7_0, uint32 a8_0, uint32 a9_0) =
{ true && and [a0_0 <=u 221459250@32, a1_0 <=u 110729625@32, a2_0 <=u 221459250@32, a3_0 <=u 110729625@32, a4_0 <=u 221459250@32, a5_0 <=u 110729625@32, a6_0 <=u 221459250@32, a7_0 <=u 110729625@32, a8_0 <=u 221459250@32, a9_0 <=u 110729625@32] }
mov f3_0_1 a0_0;
mov f3_4_1 a1_0;
mov f3_8_1 a2_0;
mov f3_12_1 a3_0;
mov f3_16_1 a4_0;
mov f3_20_1 a5_0;
mov f3_24_1 a6_0;
mov f3_28_1 a7_0;
mov f3_32_1 a8_0;
mov f3_36_1 a9_0;
mov x207_1 f3_36_1;
mov x218_1 f3_32_1;
mov x199_1 f3_28_1;
mov x1710_1 f3_24_1;
mov x1511_1 f3_20_1;
mov x1312_1 f3_16_1;
mov x1113_1 f3_12_1;
mov x914_1 f3_8_1;
mov x715_1 f3_4_1;
mov x516_1 f3_0_1;
mulj x4018_1 x516_1 121666@uint32;
mulj x4120_1 x715_1 121666@uint32;
mulj x4222_1 x914_1 121666@uint32;
mulj x4324_1 x1113_1 121666@uint32;
mulj x4426_1 x1312_1 121666@uint32;
mulj x4528_1 x1511_1 121666@uint32;
mulj x4630_1 x1710_1 121666@uint32;
mulj x4732_1 x199_1 121666@uint32;
mulj x4834_1 x218_1 121666@uint32;
mulj x4936_1 x207_1 121666@uint32;
split x8637_1 tmp_to_use_1 x4018_1 26;
cast v38_1@uint32 x4018_1;
and x8739_1@uint32 v38_1 67108863@uint32;
vpc tmp_to_use_p_1@uint32 tmp_to_use_1;
assume x8739_1 = tmp_to_use_p_1 && true;
add x8840_1 x4120_1 x8637_1;
split x8941_1 tmp_to_use_2 x8840_1 25;
cast v42_1@uint32 x8840_1;
and x9043_1@uint32 v42_1 33554431@uint32;
vpc tmp_to_use_p_2@uint32 tmp_to_use_2;
assume x9043_1 = tmp_to_use_p_2 && true;
add x9144_1 x4222_1 x8941_1;
split x9245_1 tmp_to_use_3 x9144_1 26;
cast v46_1@uint32 x9144_1;
and x9347_1@uint32 v46_1 67108863@uint32;
vpc tmp_to_use_p_3@uint32 tmp_to_use_3;
assume x9347_1 = tmp_to_use_p_3 && true;
add x9448_1 x4324_1 x9245_1;
split x9549_1 tmp_to_use_4 x9448_1 25;
cast v50_1@uint32 x9448_1;
and x9651_1@uint32 v50_1 33554431@uint32;
vpc tmp_to_use_p_4@uint32 tmp_to_use_4;
assume x9651_1 = tmp_to_use_p_4 && true;
add x9752_1 x4426_1 x9549_1;
split x9853_1 tmp_to_use_5 x9752_1 26;
cast v54_1@uint32 x9752_1;
and x9955_1@uint32 v54_1 67108863@uint32;
vpc tmp_to_use_p_5@uint32 tmp_to_use_5;
assume x9955_1 = tmp_to_use_p_5 && true;
add x10056_1 x4528_1 x9853_1;
split x10157_1 tmp_to_use_6 x10056_1 25;
cast v58_1@uint32 x10056_1;
and x10259_1@uint32 v58_1 33554431@uint32;
vpc tmp_to_use_p_6@uint32 tmp_to_use_6;
assume x10259_1 = tmp_to_use_p_6 && true;
add x10360_1 x4630_1 x10157_1;
split x10461_1 tmp_to_use_7 x10360_1 26;
cast v62_1@uint32 x10360_1;
and x10563_1@uint32 v62_1 67108863@uint32;
vpc tmp_to_use_p_7@uint32 tmp_to_use_7;
assume x10563_1 = tmp_to_use_p_7 && true;
add x10664_1 x4732_1 x10461_1;
split x10765_1 tmp_to_use_8 x10664_1 25;
cast v66_1@uint32 x10664_1;
and x10867_1@uint32 v66_1 33554431@uint32;
vpc tmp_to_use_p_8@uint32 tmp_to_use_8;
assume x10867_1 = tmp_to_use_p_8 && true;
add x10968_1 x4834_1 x10765_1;
split x11069_1 tmp_to_use_9 x10968_1 26;
cast v70_1@uint32 x10968_1;
and x11171_1@uint32 v70_1 67108863@uint32;
vpc tmp_to_use_p_9@uint32 tmp_to_use_9;
assume x11171_1 = tmp_to_use_p_9 && true;
add x11272_1 x4936_1 x11069_1;
split x11373_1 tmp_to_use_10 x11272_1 25;
cast v74_1@uint32 x11272_1;
and x11475_1@uint32 v74_1 33554431@uint32;
vpc tmp_to_use_p_10@uint32 tmp_to_use_10;
assume x11475_1 = tmp_to_use_p_10 && true;
vpc v76_1@uint64 x8739_1;
mul v77_1 x11373_1 19@uint64;
add x11578_1 v76_1 v77_1;
split v79_1 tmp_to_use_11 x11578_1 26;
vpc x11680_1@uint32 v79_1;
cast v81_1@uint32 x11578_1;
and x11782_1@uint32 v81_1 67108863@uint32;
vpc tmp_to_use_p_11@uint32 tmp_to_use_11;
assume x11782_1 = tmp_to_use_p_11 && true;
add x11883_1 x9043_1 x11680_1;
split x11984_1 tmp_to_use_12 x11883_1 25;
and x12085_1@uint32 x11883_1 33554431@uint32;
vpc tmp_to_use_p_12@uint32 tmp_to_use_12;
assume x12085_1 = tmp_to_use_p_12 && true;
mov h4_0_1 x11782_1;
mov h4_4_1 x12085_1;
add v86_1 x9347_1 x11984_1;
mov h4_8_1 v86_1;
mov h4_12_1 x9651_1;
mov h4_16_1 x9955_1;
mov h4_20_1 x10259_1;
mov h4_24_1 x10563_1;
mov h4_28_1 x10867_1;
mov h4_32_1 x11171_1;
mov h4_36_1 x11475_1;
mov c0_1 h4_0_1;
mov c1_1 h4_4_1;
mov c2_1 h4_8_1;
mov c3_1 h4_12_1;
mov c4_1 h4_16_1;
mov c5_1 h4_20_1;
mov c6_1 h4_24_1;
mov c7_1 h4_28_1;
mov c8_1 h4_32_1;
mov c9_1 h4_36_1;
{ c0_1 + (c1_1 * 67108864) + (c2_1 * 2251799813685248) + (c3_1 * 151115727451828646838272) + (c4_1 * 5070602400912917605986812821504) + (c5_1 * 340282366920938463463374607431768211456) + (c6_1 * 11417981541647679048466287755595961091061972992) + (c7_1 * 766247770432944429179173513575154591809369561091801088) + (c8_1 * 25711008708143844408671393477458601640355247900524685364822016) + (c9_1 * 1725436586697640946858688965569256363112777243042596638790631055949824) = (a0_0 + (a1_0 * 67108864) + (a2_0 * 2251799813685248) + (a3_0 * 151115727451828646838272) + (a4_0 * 5070602400912917605986812821504) + (a5_0 * 340282366920938463463374607431768211456) + (a6_0 * 11417981541647679048466287755595961091061972992) + (a7_0 * 766247770432944429179173513575154591809369561091801088) + (a8_0 * 25711008708143844408671393477458601640355247900524685364822016) + (a9_0 * 1725436586697640946858688965569256363112777243042596638790631055949824)) * 121666 (mod 57896044618658097711785492504343953926634992332820282019728792003956564819968 - 19) && and [x8739_1 = tmp_to_use_p_1, x9043_1 = tmp_to_use_p_2, x9347_1 = tmp_to_use_p_3, x9651_1 = tmp_to_use_p_4, x9955_1 = tmp_to_use_p_5, x10259_1 = tmp_to_use_p_6, x10563_1 = tmp_to_use_p_7, x10867_1 = tmp_to_use_p_8, x11171_1 = tmp_to_use_p_9, x11475_1 = tmp_to_use_p_10, x11782_1 = tmp_to_use_p_11, x12085_1 = tmp_to_use_p_12, c0_1 <=u 73819750@32, c1_1 <=u 36909875@32, c2_1 <=u 73819750@32, c3_1 <=u 36909875@32, c4_1 <=u 73819750@32, c5_1 <=u 36909875@32, c6_1 <=u 73819750@32, c7_1 <=u 36909875@32, c8_1 <=u 73819750@32, c9_1 <=u 36909875@32] }
