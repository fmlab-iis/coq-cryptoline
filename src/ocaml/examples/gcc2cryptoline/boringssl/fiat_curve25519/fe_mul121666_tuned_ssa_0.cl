proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 a4_0) =
{ true && and [a0_0 <u 2251799813718016@64, a1_0 <u 2251799813718016@64, a2_0 <u 2251799813718016@64, a3_0 <u 2251799813718016@64, a4_0 <u 2251799813718016@64] }
mulj x2013_1 a0_0 121666@uint64;
mulj x2115_1 a1_0 121666@uint64;
mulj x2217_1 a2_0 121666@uint64;
mulj x2319_1 a3_0 121666@uint64;
mulj x2421_1 a4_0 121666@uint64;
split v22_1 tmp_to_use_1 x2013_1 51;
cast v23_1@uint64 x2013_1;
and x3424_1@uint64 v23_1 2251799813685247@uint64;
vpc tmp_to_use_p_1@uint64 tmp_to_use_1;
assume x3424_1 = tmp_to_use_1 && true;
add x3526_1 x2115_1 v22_1;
split v27_1 tmp_to_use_2 x3526_1 51;
cast v28_1@uint64 x3526_1;
and x3729_1@uint64 v28_1 2251799813685247@uint64;
vpc tmp_to_use_p_2@uint64 tmp_to_use_2;
assume x3729_1 = tmp_to_use_2 && true;
add x3831_1 x2217_1 v27_1;
split v32_1 tmp_to_use_3 x3831_1 51;
cast v33_1@uint64 x3831_1;
and x4034_1@uint64 v33_1 2251799813685247@uint64;
vpc tmp_to_use_p_3@uint64 tmp_to_use_3;
assume x4034_1 = tmp_to_use_3 && true;
add x4136_1 x2319_1 v32_1;
split v37_1 tmp_to_use_4 x4136_1 51;
cast v38_1@uint64 x4136_1;
and x4339_1@uint64 v38_1 2251799813685247@uint64;
vpc tmp_to_use_p_4@uint64 tmp_to_use_4;
assume x4339_1 = tmp_to_use_4 && true;
add x4441_1 x2421_1 v37_1;
split v42_1 tmp_to_use_5 x4441_1 51;
vpc x4543_1@uint64 v42_1;
cast v44_1@uint64 x4441_1;
and x4645_1@uint64 v44_1 2251799813685247@uint64;
vpc tmp_to_use_p_5@uint64 tmp_to_use_5;
assume x4645_1 = tmp_to_use_5 && true;
mul v46_1 x4543_1 19@uint64;
add x4747_1 x3424_1 v46_1;
split x4848_1 tmp_to_use_6 x4747_1 51;
and x4949_1@uint64 x4747_1 2251799813685247@uint64;
vpc tmp_to_use_p_6@uint64 tmp_to_use_6;
assume x4949_1 = tmp_to_use_6 && true;
add x5050_1 x3729_1 x4848_1;
split x5151_1 tmp_to_use_7 x5050_1 51;
and x5252_1@uint64 x5050_1 2251799813685247@uint64;
vpc tmp_to_use_p_7@uint64 tmp_to_use_7;
assume x5252_1 = tmp_to_use_7 && true;
add v53_1 x4034_1 x5151_1;
{ x4949_1 + (x5252_1 * 2251799813685248) + (v53_1 * 5070602400912917605986812821504) + (x4339_1 * 11417981541647679048466287755595961091061972992) + (x4645_1 * 25711008708143844408671393477458601640355247900524685364822016) = (a0_0 + (a1_0 * 2251799813685248) + (a2_0 * 5070602400912917605986812821504) + (a3_0 * 11417981541647679048466287755595961091061972992) + (a4_0 * 25711008708143844408671393477458601640355247900524685364822016)) * 121666 (mod 57896044618658097711785492504343953926634992332820282019728792003956564819968 - 19) && and [x3424_1 = tmp_to_use_p_1, x3729_1 = tmp_to_use_p_2, x4034_1 = tmp_to_use_p_3, x4339_1 = tmp_to_use_p_4, x4645_1 = tmp_to_use_p_5, x4949_1 = tmp_to_use_p_6, x5252_1 = tmp_to_use_p_7, x4949_1 <u 2251799813718016@64, x5252_1 <u 2251799813718016@64, v53_1 <u 2251799813718016@64, x4339_1 <u 2251799813718016@64, x4645_1 <u 2251799813718016@64] }