proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 a4_0) =
{ true && and [a0_0 <u 9007199254740992@64, a1_0 <u 9007199254740992@64, a2_0 <u 9007199254740992@64, a3_0 <u 9007199254740992@64, a4_0 <u 9007199254740992@64] }
mul x953_1 a0_0 2@uint64;
mul x1054_1 a1_0 2@uint64;
mul x1155_1 a2_0 38@uint64;
mul x1256_1 a4_0 19@uint64;
mul x1357_1 a4_0 38@uint64;
mulj v2_1 a0_0 a0_0;
mulj v5_1 x1357_1 a1_0;
mulj v9_1 x1155_1 a3_0;
add v88_1 v5_1 v9_1;
add x1458_1 v2_1 v88_1;
mulj v11_1 a1_0 x953_1;
mulj v13_1 x1357_1 a2_0;
add v14_1 v11_1 v13_1;
mul v15_1 a3_0 19@uint64;
mulj v17_1 a3_0 v15_1;
add x1559_1 v14_1 v17_1;
mulj v18_1 x953_1 a2_0;
mulj v19_1 a1_0 a1_0;
mulj v21_1 x1357_1 a3_0;
add v89_1 v18_1 v21_1;
add x1660_1 v19_1 v89_1;
mulj v22_1 a3_0 x953_1;
mulj v24_1 a2_0 x1054_1;
add v25_1 v22_1 v24_1;
mulj v28_1 a4_0 x1256_1;
add x1761_1 v25_1 v28_1;
mulj v29_1 x953_1 a4_0;
mulj v30_1 a3_0 x1054_1;
add v31_1 v29_1 v30_1;
mulj v32_1 a2_0 a2_0;
add x1862_1 v31_1 v32_1;
split v33_1 tmp_to_use_1 x1458_1 51;
cast v34_1@uint64 x1458_1;
and x2063_1@uint64 v34_1 2251799813685247@uint64;
vpc tmp_to_use_p_1@uint64 tmp_to_use_1;
assume x2063_1 = tmp_to_use_1 && true;
join value_1 0@uint64 18446744073709551615@uint64;
and v45_1@uint128 v33_1 value_1;
assume v45_1 = v33_1 && true;
add x2164_1 v45_1 x1559_1;
split v35_1 tmp_to_use_2 x2164_1 51;
cast v36_1@uint64 x2164_1;
and x2365_1@uint64 v36_1 2251799813685247@uint64;
vpc tmp_to_use_p_2@uint64 tmp_to_use_2;
assume x2365_1 = tmp_to_use_2 && true;
join value_2 0@uint64 18446744073709551615@uint64;
and v85_1@uint128 v35_1 value_2;
assume v85_1 = v35_1 && true;
add x2466_1 x1660_1 v85_1;
split v37_1 tmp_to_use_3 x2466_1 51;
cast v38_1@uint64 x2466_1;
and x2667_1@uint64 v38_1 2251799813685247@uint64;
vpc tmp_to_use_p_3@uint64 tmp_to_use_3;
assume x2667_1 = tmp_to_use_3 && true;
join value_3 0@uint64 18446744073709551615@uint64;
and v86_1@uint128 v37_1 value_3;
assume v86_1 = v37_1 && true;
add x2768_1 x1761_1 v86_1;
split v39_1 tmp_to_use_4 x2768_1 51;
cast v40_1@uint64 x2768_1;
and x2969_1@uint64 v40_1 2251799813685247@uint64;
vpc tmp_to_use_p_4@uint64 tmp_to_use_4;
assume x2969_1 = tmp_to_use_4 && true;
join value_4 0@uint64 18446744073709551615@uint64;
and v87_1@uint128 v39_1 value_4;
assume v87_1 = v39_1 && true;
add x3070_1 x1862_1 v87_1;
split v41_1 tmp_to_use_5 x3070_1 51;
vpc x3171_1@uint64 v41_1;
cast v42_1@uint64 x3070_1;
and x3272_1@uint64 v42_1 2251799813685247@uint64;
vpc tmp_to_use_p_5@uint64 tmp_to_use_5;
assume x3272_1 = tmp_to_use_5 && true;
mul v43_1 x3171_1 19@uint64;
add x3373_1 v43_1 x2063_1;
split x3474_1 tmp_to_use_6 x3373_1 51;
and x3575_1@uint64 x3373_1 2251799813685247@uint64;
vpc tmp_to_use_p_6@uint64 tmp_to_use_6;
assume x3575_1 = tmp_to_use_6 && true;
add x3676_1 x2365_1 x3474_1;
split x3777_1 tmp_to_use_7 x3676_1 51;
and x3878_1@uint64 x3676_1 2251799813685247@uint64;
vpc tmp_to_use_p_7@uint64 tmp_to_use_7;
assume x3878_1 = tmp_to_use_7 && true;
add v44_1 x2667_1 x3777_1;
{ x3575_1 + (x3878_1 * 2251799813685248) + (v44_1 * 5070602400912917605986812821504) + (x2969_1 * 11417981541647679048466287755595961091061972992) + (x3272_1 * 25711008708143844408671393477458601640355247900524685364822016) = (a0_0 + (a1_0 * 2251799813685248) + (a2_0 * 5070602400912917605986812821504) + (a3_0 * 11417981541647679048466287755595961091061972992) + (a4_0 * 25711008708143844408671393477458601640355247900524685364822016)) * (a0_0 + (a1_0 * 2251799813685248) + (a2_0 * 5070602400912917605986812821504) + (a3_0 * 11417981541647679048466287755595961091061972992) + (a4_0 * 25711008708143844408671393477458601640355247900524685364822016)) (mod 57896044618658097711785492504343953926634992332820282019728792003956564819968 - 19) && and [x2063_1 = tmp_to_use_p_1, v45_1 = v33_1, x2365_1 = tmp_to_use_p_2, v85_1 = v35_1, x2667_1 = tmp_to_use_p_3, v86_1 = v37_1, x2969_1 = tmp_to_use_p_4, v87_1 = v39_1, x3272_1 = tmp_to_use_p_5, x3575_1 = tmp_to_use_p_6, x3878_1 = tmp_to_use_p_7, x3575_1 <u 2251799813718016@64, x3878_1 <u 2251799813718016@64, v44_1 <u 2251799813718016@64, x2969_1 <u 2251799813718016@64, x3272_1 <u 2251799813718016@64] }