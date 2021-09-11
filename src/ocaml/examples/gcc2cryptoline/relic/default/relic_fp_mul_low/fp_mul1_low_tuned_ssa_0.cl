proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 b_0) =
{ true && true }
mulj v24_1 b_0 a0_0;
cast v37_1@uint64 v24_1;
split v39_1 tmp_to_use_1 v24_1 64;
vpc tmp_to_use_p_1@uint64 tmp_to_use_1;
assume tmp_to_use_p_1 = v37_1 && true;
mulj v53_1 b_0 a1_0;
add r55_1 v39_1 v53_1;
cast v56_1@uint64 r55_1;
split v58_1 tmp_to_use_2 r55_1 64;
vpc tmp_to_use_p_2@uint64 tmp_to_use_2;
assume tmp_to_use_p_2 = v56_1 && true;
mulj v72_1 b_0 a2_0;
add r74_1 v58_1 v72_1;
cast v75_1@uint64 r74_1;
split v77_1 tmp_to_use_3 r74_1 64;
vpc tmp_to_use_p_3@uint64 tmp_to_use_3;
assume tmp_to_use_p_3 = v75_1 && true;
mulj v4_1 a3_0 b_0;
add r18_1 v4_1 v77_1;
cast v6_1@uint64 r18_1;
split v7_1 tmp_to_use_4 r18_1 64;
vpc tmp_to_use_p_4@uint64 tmp_to_use_4;
assume tmp_to_use_p_4 = v6_1 && true;
vpc carry20_1@uint64 v7_1;
{ v37_1 + (v56_1 * 18446744073709551616) + (v75_1 * 340282366920938463463374607431768211456) + (v6_1 * 6277101735386680763835789423207666416102355444464034512896) + (carry20_1 * 115792089237316195423570985008687907853269984665640564039457584007913129639936) = (a0_0 + (a1_0 * 18446744073709551616) + (a2_0 * 340282366920938463463374607431768211456) + (a3_0 * 6277101735386680763835789423207666416102355444464034512896)) * b_0 && and [tmp_to_use_p_1 = v37_1, tmp_to_use_p_2 = v56_1, tmp_to_use_p_3 = v75_1, tmp_to_use_p_4 = v6_1] }