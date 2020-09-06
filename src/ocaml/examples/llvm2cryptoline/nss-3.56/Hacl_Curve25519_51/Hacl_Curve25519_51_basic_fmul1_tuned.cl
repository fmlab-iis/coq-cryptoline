(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=32G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=32G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  Hacl_Curve25519_51_basic_fmul1_tuned.cl

Results of checking CNF formulas:       [OK]            27.894233 seconds
Finding polynomial coefficients         [OK]            0.170756 seconds
Verification result:                    [OK]            33.461785 seconds
*)

proc main(uint64 mem0_0_0, uint64 mem0_16_0, uint64 mem0_24_0, uint64 mem0_32_0, uint64 mem0_8_0, uint64 v_f2_0) =
{ true && and [mem0_0_0 <=u 20266198323167223@64, mem0_8_0 <=u 22517998136852470@64, mem0_16_0 <=u 20266198323167223@64, mem0_24_0 <=u 20266198323167223@64, mem0_32_0 <=u 20266198323167223@64, v_f2_0 <=u 2251799813685247@64] }
mov v0_1 mem0_0_0;
mov v1_1 mem0_8_0;
mov v2_1 mem0_16_0;
mov v3_1 mem0_24_0;
mov v4_1 mem0_32_0;
cast v_conv_i_1@uint128 v_f2_0;
cast v_conv1_i_1@uint128 v0_1;
mul v_mul_i_1 v_conv1_i_1 v_conv_i_1;
cast v_conv1_i258_1@uint128 v1_1;
mul v_mul_i259_1 v_conv1_i258_1 v_conv_i_1;
cast v_conv1_i250_1@uint128 v2_1;
mul v_mul_i251_1 v_conv1_i250_1 v_conv_i_1;
cast v_conv1_i242_1@uint128 v3_1;
mul v_mul_i243_1 v_conv1_i242_1 v_conv_i_1;
cast v_conv1_i234_1@uint128 v4_1;
mul v_mul_i235_1 v_conv1_i234_1 v_conv_i_1;
cast v_retval_sroa_0_0_extract_trunc_i230_1@uint64 v_mul_i_1;
and v_and_1@uint64 v_retval_sroa_0_0_extract_trunc_i230_1 2251799813685247@uint64;
split v_shr_i221_1 tmp_to_be_used_1 v_mul_i_1 51;
vpc tmp_v_1@uint64 tmp_to_be_used_1;
assume tmp_v_1 = v_and_1 && true;
and v_y_sroa_0_0_insert_ext_i210_1@uint128 v_shr_i221_1 18446744073709551615@uint128;
assume v_y_sroa_0_0_insert_ext_i210_1 = v_shr_i221_1 && true;
add v_add_i211_1 v_y_sroa_0_0_insert_ext_i210_1 v_mul_i259_1;
cast v_retval_sroa_0_0_extract_trunc_i212_1@uint64 v_add_i211_1;
and v_and34_1@uint64 v_retval_sroa_0_0_extract_trunc_i212_1 2251799813685247@uint64;
split v_shr_i201_1 tmp_to_be_used_2 v_add_i211_1 51;
vpc tmp_v_2@uint64 tmp_to_be_used_2;
assume tmp_v_2 = v_and34_1 && true;
and v_y_sroa_0_0_insert_ext_i190_1@uint128 v_shr_i201_1 18446744073709551615@uint128;
assume v_y_sroa_0_0_insert_ext_i190_1 = v_shr_i201_1 && true;
add v_add_i191_1 v_y_sroa_0_0_insert_ext_i190_1 v_mul_i251_1;
split v_shr_i181_1 tmp_to_be_used_3 v_add_i191_1 51;
and v_y_sroa_0_0_insert_ext_i170_1@uint128 v_shr_i181_1 18446744073709551615@uint128;
assume v_y_sroa_0_0_insert_ext_i170_1 = v_shr_i181_1 && true;
add v_add_i171_1 v_y_sroa_0_0_insert_ext_i170_1 v_mul_i243_1;
mov v5_0_1 v_add_i191_1;
nondet undef_1_1@uint128;
mov v5_1_1 undef_1_1;
mov v6_0_1 v5_0_1;
mov v6_1_1 v_add_i171_1;
cast v7_0_1@uint64 v6_0_1;
cast v7_1_1@uint64 v6_1_1;
and v8_0_1@uint64 v7_0_1 2251799813685247@uint64;
and v8_1_1@uint64 v7_1_1 2251799813685247@uint64;
vpc tmp_v_3@uint64 tmp_to_be_used_3;
assume tmp_v_3 = v8_0_1 && true;
split v_shr_i161_1 tmp_to_be_used_4 v_add_i171_1 51;
vpc tmp_v_4@uint64 tmp_to_be_used_4;
assume tmp_v_4 = v8_1_1 && true;
and v_y_sroa_0_0_insert_ext_i_1@uint128 v_shr_i161_1 18446744073709551615@uint128;
assume v_y_sroa_0_0_insert_ext_i_1 = v_shr_i161_1 && true;
add v_add_i_1 v_y_sroa_0_0_insert_ext_i_1 v_mul_i235_1;
cast v_retval_sroa_0_0_extract_trunc_i152_1@uint64 v_add_i_1;
and v_and76_1@uint64 v_retval_sroa_0_0_extract_trunc_i152_1 2251799813685247@uint64;
split v_shr_i_1 tmp_to_be_used_5 v_add_i_1 51;
vpc tmp_v_5@uint64 tmp_to_be_used_5;
assume tmp_v_5 = v_and76_1 && true;
vpc v_retval_sroa_0_0_extract_trunc_i144_1@uint64 v_shr_i_1;
mul v_mul_1 v_retval_sroa_0_0_extract_trunc_i144_1 19@uint64;
add v_add_1 v_mul_1 v_and_1;
and v_and82_1@uint64 v_add_1 2251799813685247@uint64;
split v_shr_1 tmp_to_be_used_6 v_add_1 51;
vpc tmp_v_6@uint64 tmp_to_be_used_6;
assume tmp_v_6 = v_and82_1 && true;
add v_add83_1 v_shr_1 v_and34_1;
mov mem1_0_1 v_and82_1;
mov mem1_8_1 v_add83_1;
mov mem1_16_1 v8_0_1;
mov mem1_24_1 v8_1_1;
mov mem1_32_1 v_and76_1;
{ mem1_0_1 + (mem1_8_1 * 2251799813685248) + (mem1_16_1 * 5070602400912917605986812821504) + (mem1_24_1 * 11417981541647679048466287755595961091061972992) + (mem1_32_1 * 25711008708143844408671393477458601640355247900524685364822016) = (mem0_0_0 + (mem0_8_0 * 2251799813685248) + (mem0_16_0 * 5070602400912917605986812821504) + (mem0_24_0 * 11417981541647679048466287755595961091061972992) + (mem0_32_0 * 25711008708143844408671393477458601640355247900524685364822016)) * v_f2_0 (mod 57896044618658097711785492504343953926634992332820282019728792003956564819968 - 19) && and [tmp_v_1 = v_and_1, v_y_sroa_0_0_insert_ext_i210_1 = v_shr_i221_1, tmp_v_2 = v_and34_1, v_y_sroa_0_0_insert_ext_i190_1 = v_shr_i201_1, v_y_sroa_0_0_insert_ext_i170_1 = v_shr_i181_1, tmp_v_3 = v8_0_1, tmp_v_4 = v8_1_1, v_y_sroa_0_0_insert_ext_i_1 = v_shr_i161_1, tmp_v_5 = v_and76_1, tmp_v_6 = v_and82_1, mem1_0_1 <=u 2251799813685247@64, mem1_8_1 <=u 2251799813693439@64, mem1_16_1 <=u 2251799813685247@64, mem1_24_1 <=u 2251799813685247@64, mem1_32_1 <=u 2251799813685247@64] }
