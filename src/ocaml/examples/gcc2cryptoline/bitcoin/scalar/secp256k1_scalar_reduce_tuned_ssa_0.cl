proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0) =
{ true && true }
subb lt_value_1 dontcare_1 a3_0 18446744073709551615@uint64;
vpc v2_2@uint8 lt_value_1;
add tmp_for_compare_1 18446744073709551613@uint64 1@uint64;
subb v4_1 dontcare_2 a2_0 tmp_for_compare_1;
vpc v4_2@uint8 v4_1;
vpc v2_p_1@uint1 v2_2;
cmov v19_1 v2_p_1 1@uint8 v4_2;
vpc v19_p_1@uint1 v19_1;
subb lt_value_2 dontcare_3 a2_0 18446744073709551615@uint64;
not v5_2@uint1 lt_value_2;
vpc v5_3@uint8 v5_2;
vpc v6_1@uint1 v5_3;
not v7_1@uint1 v19_p_1;
cmov v8_1 v6_1 v7_1 0@uint1;
add tmp_for_compare_2 13451932020343611450@uint64 1@uint64;
subb v10_1 dontcare_4 a1_0 tmp_for_compare_2;
vpc v10_2@uint8 v10_1;
vpc v10_p_1@uint1 v10_2;
cmov v20_1 v10_p_1 1@uint8 v19_1;
vpc no24_1@uint1 v20_1;
subb v11_1 dontcare_5 13451932020343611451@uint64 a1_0;
vpc v11_2@uint8 v11_1;
not v13_1@uint1 no24_1;
subb v16_1 dontcare_6 13822214165235122496@uint64 a0_0;
vpc v16_2@uint8 v16_1;
vpc v11_p_1@uint1 v11_2;
cmov v25_1 v11_p_1 1@uint8 v16_2;
vpc v28_1@uint8 v25_1;
vpc v13_p_1@uint1 v13_1;
cmov v27_1 v13_p_1 v28_1 0@uint8;
vpc v8_p_1@uint1 v8_1;
cmov yes26_1 v8_p_1 1@uint8 v27_1;
vpc yes26_2@int32 yes26_1;
vpc overflow23_1@uint32 yes26_2;
vpc v2_3@uint128 a0_0;
vpc v3_2@uint64 overflow23_1;
mul v4_3 v3_2 4624529908474429119@uint64;
vpc v5_4@uint128 v4_3;
add t24_1 v2_3 v5_4;
adds carry_1 v6_2 a0_0 v4_3;
split t26_1 tmp_to_use_1 t24_1 64;
vpc t26_p_1@uint1 t26_1;
assume t26_1 = carry_1 && true;
vpc v8_2@uint128 a1_0;
mul v9_2 v3_2 4994812053365940164@uint64;
vpc v10_3@uint128 v9_2;
add v11_3 v8_2 v10_3;
add t27_1 v11_3 t26_1;
cast v12_1@uint64 t27_1;
split t29_1 tmp_to_use_2 t27_1 64;
vpc tmp_to_use_p_1@uint64 tmp_to_use_2;
assume tmp_to_use_2 = v12_1 && true;
vpc v14_1@uint128 a2_0;
vpc v15_2@uint128 overflow23_1;
add v16_3 v14_1 v15_2;
add t30_1 v16_3 t29_1;
cast v17_1@uint64 t30_1;
split t32_1 tmp_to_use_3 t30_1 64;
vpc tmp_to_use_p_2@uint64 tmp_to_use_3;
assume tmp_to_use_3 = v17_1 && true;
vpc v19_2@uint128 a3_0;
add t33_1 v19_2 t32_1;
split tmp_3 v20_2 t33_1 64;
vpc v20_3@uint64 v20_2;
vpc tmp_4@uint32 tmp_3;
assume tmp_4 = overflow23_1 && true;
vpc v35_1@int32 overflow23_1;
subb lt_value_3 dontcare_7 v20_3 18446744073709551615@uint64;
vpc v2_5@uint8 lt_value_3;
add tmp_for_compare_3 18446744073709551613@uint64 1@uint64;
subb v4_4 dontcare_8 v17_1 tmp_for_compare_3;
vpc v4_5@uint8 v4_4;
vpc v2_p_2@uint1 v2_5;
cmov v19_3 v2_p_2 1@uint8 v4_5;
vpc v19_p_2@uint1 v19_3;
subb lt_value_4 dontcare_9 v17_1 18446744073709551615@uint64;
not v5_6@uint1 lt_value_4;
vpc v5_7@uint8 v5_6;
vpc v6_3@uint1 v5_7;
not v7_3@uint1 v19_p_2;
cmov v8_3 v6_3 v7_3 0@uint1;
add tmp_for_compare_4 13451932020343611450@uint64 1@uint64;
subb v10_4 dontcare_10 v12_1 tmp_for_compare_4;
vpc v10_5@uint8 v10_4;
vpc v10_p_2@uint1 v10_5;
cmov v20_4 v10_p_2 1@uint8 v19_3;
vpc no24_2@uint1 v20_4;
subb v11_4 dontcare_11 13451932020343611451@uint64 v12_1;
vpc v11_5@uint8 v11_4;
not v13_3@uint1 no24_2;
subb v16_4 dontcare_12 13822214165235122496@uint64 v6_2;
vpc v16_5@uint8 v16_4;
vpc v11_p_2@uint1 v11_5;
cmov v25_2 v11_p_2 1@uint8 v16_5;
vpc v28_2@uint8 v25_2;
vpc v13_p_2@uint1 v13_3;
cmov v27_2 v13_p_2 v28_2 0@uint8;
vpc v8_p_2@uint1 v8_3;
cmov yes26_3 v8_p_2 1@uint8 v27_2;
vpc yes26_4@int32 yes26_3;
{ v6_2 + (v12_1 * 18446744073709551616) + (v17_1 * 340282366920938463463374607431768211456) + (v20_3 * 6277101735386680763835789423207666416102355444464034512896) = a0_0 + (a1_0 * 18446744073709551616) + (a2_0 * 340282366920938463463374607431768211456) + (a3_0 * 6277101735386680763835789423207666416102355444464034512896) (mod 115792089237316195423570985008687907852837564279074904382605163141518161494337) && and [t26_p_1 = carry_1, tmp_to_use_p_1 = v12_1, tmp_to_use_p_2 = v17_1, tmp_4 = overflow23_1, yes26_4 = 0@32] }