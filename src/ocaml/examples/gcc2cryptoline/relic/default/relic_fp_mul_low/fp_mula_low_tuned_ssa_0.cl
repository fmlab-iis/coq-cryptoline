proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 c0_0, uint64 c1_0, uint64 c2_0, uint64 c3_0, uint64 digit_0) =
{ true && true }
vpc v15_1@uint128 c0_0;
mulj v12_1 a0_0 digit_0;
add v38_1 v12_1 v15_1;
cast v43_1@uint64 v38_1;
split v45_1 tmp_to_use_1 v38_1 64;
vpc tmp_to_use_p_1@uint64 tmp_to_use_1;
assume tmp_to_use_p_1 = v43_1 && true;
vpc v58_1@uint128 c1_0;
mulj v61_1 digit_0 a1_0;
add v39_1 v58_1 v61_1;
add r64_1 v39_1 v45_1;
cast v65_1@uint64 r64_1;
split v67_1 tmp_to_use_2 r64_1 64;
vpc tmp_to_use_p_2@uint64 tmp_to_use_2;
assume tmp_to_use_p_2 = v65_1 && true;
vpc v80_1@uint128 c2_0;
mulj v83_1 digit_0 a2_0;
add v40_1 v80_1 v83_1;
add r86_1 v40_1 v67_1;
cast v87_1@uint64 r86_1;
split v89_1 tmp_to_use_3 r86_1 64;
vpc tmp_to_use_p_3@uint64 tmp_to_use_3;
assume tmp_to_use_p_3 = v87_1 && true;
vpc v2_1@uint128 c3_0;
mulj v6_1 a3_0 digit_0;
add v41_1 v2_1 v6_1;
add r21_1 v41_1 v89_1;
cast v9_1@uint64 r21_1;
split v10_1 tmp_to_use_4 r21_1 64;
vpc tmp_to_use_p_4@uint64 tmp_to_use_4;
assume tmp_to_use_p_4 = v9_1 && true;
vpc carry23_1@uint64 v10_1;
{ v43_1 + (v65_1 * 18446744073709551616) + (v87_1 * 340282366920938463463374607431768211456) + (v9_1 * 6277101735386680763835789423207666416102355444464034512896) + (carry23_1 * 115792089237316195423570985008687907853269984665640564039457584007913129639936) = c0_0 + (c1_0 * 18446744073709551616) + (c2_0 * 340282366920938463463374607431768211456) + (c3_0 * 6277101735386680763835789423207666416102355444464034512896) + ((a0_0 + (a1_0 * 18446744073709551616) + (a2_0 * 340282366920938463463374607431768211456) + (a3_0 * 6277101735386680763835789423207666416102355444464034512896)) * digit_0) && and [tmp_to_use_p_1 = v43_1, tmp_to_use_p_2 = v65_1, tmp_to_use_p_3 = v87_1, tmp_to_use_p_4 = v9_1] }