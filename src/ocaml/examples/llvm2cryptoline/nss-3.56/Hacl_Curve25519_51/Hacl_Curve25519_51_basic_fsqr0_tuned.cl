(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=32G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=32G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  Hacl_Curve25519_51_basic_fsqr0_tuned.cl

Results of checking CNF formulas:       [OK]            99.060741 seconds
Finding polynomial coefficients         [OK]            0.194676 seconds
Verification result:                    [OK]            116.177026 seconds
*)

proc main(uint64 mem0_0_0, uint64 mem0_16_0, uint64 mem0_24_0, uint64 mem0_32_0, uint64 mem0_8_0) =
{ true && and [mem0_0_0 <=u 20266198323167223@64, mem0_8_0 <=u 22517998136852470@64, mem0_16_0 <=u 20266198323167223@64, mem0_24_0 <=u 20266198323167223@64, mem0_32_0 <=u 20266198323167223@64] }
mov v0_1 mem0_0_0;
mov v1_1 mem0_8_0;
mov v2_1 mem0_16_0;
mov v3_1 mem0_24_0;
mov v4_1 mem0_32_0;
shl v_mul_1 v0_1 1;
shl v_mul5_1 v1_1 1;
mul v_mul6_1 v2_1 38@uint64;
mul v_mul7_1 v3_1 19@uint64;
mul v_mul8_1 v4_1 19@uint64;
mul v_mul9_1 v4_1 38@uint64;
cast v_conv_i_1@uint128 v0_1;
mul v_mul_i_1 v_conv_i_1 v_conv_i_1;
cast v_conv_i572_1@uint128 v_mul9_1;
cast v_conv1_i573_1@uint128 v1_1;
mul v_mul_i574_1 v_conv_i572_1 v_conv1_i573_1;
cast v_conv_i550_1@uint128 v_mul6_1;
cast v_conv1_i551_1@uint128 v3_1;
mul v_mul_i552_1 v_conv1_i551_1 v_conv_i550_1;
add v_add_i566_1 v_mul_i552_1 v_mul_i_1;
add v_add_i544_1 v_add_i566_1 v_mul_i574_1;
cast v_conv_i528_1@uint128 v_mul_1;
mul v_mul_i530_1 v_conv1_i573_1 v_conv_i528_1;
cast v_conv1_i521_1@uint128 v2_1;
mul v_mul_i522_1 v_conv_i572_1 v_conv1_i521_1;
cast v_conv_i498_1@uint128 v_mul7_1;
mul v_mul_i500_1 v_conv_i498_1 v_conv1_i551_1;
mul v_mul_i478_1 v_conv1_i521_1 v_conv_i528_1;
mul v_mul_i470_1 v_conv1_i573_1 v_conv1_i573_1;
add v_add_i462_1 v_mul_i478_1 v_mul_i470_1;
mul v_mul_i448_1 v_conv_i572_1 v_conv1_i551_1;
add v_add_i440_1 v_add_i462_1 v_mul_i448_1;
mul v_mul_i426_1 v_conv1_i551_1 v_conv_i528_1;
cast v_conv_i416_1@uint128 v_mul5_1;
mul v_mul_i418_1 v_conv1_i521_1 v_conv_i416_1;
add v_add_i410_1 v_mul_i426_1 v_mul_i418_1;
cast v_conv_i394_1@uint128 v4_1;
cast v_conv1_i395_1@uint128 v_mul8_1;
mul v_mul_i396_1 v_conv1_i395_1 v_conv_i394_1;
add v_add_i388_1 v_add_i410_1 v_mul_i396_1;
mul v_mul_i374_1 v_conv_i394_1 v_conv_i528_1;
mul v_mul_i366_1 v_conv1_i551_1 v_conv_i416_1;
mul v_mul_i344_1 v_conv1_i521_1 v_conv1_i521_1;
cast v_retval_sroa_0_0_extract_trunc_i328_1@uint64 v_add_i544_1;
and v_and_1@uint64 v_retval_sroa_0_0_extract_trunc_i328_1 2251799813685247@uint64;
split v_shr_i319_1 tmp_to_be_used_1 v_add_i544_1 51;
vpc tmp_v_1@uint64 tmp_to_be_used_1;
assume tmp_v_1 = v_and_1 && true;
and v_y_sroa_0_0_insert_ext_i308_1@uint128 v_shr_i319_1 18446744073709551615@uint128;
assume v_y_sroa_0_0_insert_ext_i308_1 = v_shr_i319_1 && true;
add v_add_i514_1 v_mul_i500_1 v_mul_i530_1;
add v_add_i492_1 v_add_i514_1 v_mul_i522_1;
add v_add_i309_1 v_add_i492_1 v_y_sroa_0_0_insert_ext_i308_1;
cast v_retval_sroa_0_0_extract_trunc_i310_1@uint64 v_add_i309_1;
and v_and99_1@uint64 v_retval_sroa_0_0_extract_trunc_i310_1 2251799813685247@uint64;
split v_shr_i299_1 tmp_to_be_used_2 v_add_i309_1 51;
vpc tmp_v_2@uint64 tmp_to_be_used_2;
assume tmp_v_2 = v_and99_1 && true;
and v_y_sroa_0_0_insert_ext_i288_1@uint128 v_shr_i299_1 18446744073709551615@uint128;
assume v_y_sroa_0_0_insert_ext_i288_1 = v_shr_i299_1 && true;
add v_add_i289_1 v_add_i440_1 v_y_sroa_0_0_insert_ext_i288_1;
split v_shr_i279_1 tmp_to_be_used_3 v_add_i289_1 51;
and v_y_sroa_0_0_insert_ext_i268_1@uint128 v_shr_i279_1 18446744073709551615@uint128;
assume v_y_sroa_0_0_insert_ext_i268_1 = v_shr_i279_1 && true;
add v_add_i269_1 v_add_i388_1 v_y_sroa_0_0_insert_ext_i268_1;
mov v5_0_1 v_add_i289_1;
nondet undef_1_1@uint128;
mov v5_1_1 undef_1_1;
mov v6_0_1 v5_0_1;
mov v6_1_1 v_add_i269_1;
cast v7_0_1@uint64 v6_0_1;
cast v7_1_1@uint64 v6_1_1;
and v8_0_1@uint64 v7_0_1 2251799813685247@uint64;
and v8_1_1@uint64 v7_1_1 2251799813685247@uint64;
vpc tmp_v_3@uint64 tmp_to_be_used_3;
assume tmp_v_3 = v8_0_1 && true;
split v_shr_i259_1 tmp_to_be_used_4 v_add_i269_1 51;
vpc tmp_v_4@uint64 tmp_to_be_used_4;
assume tmp_v_4 = v8_1_1 && true;
and v_y_sroa_0_0_insert_ext_i_1@uint128 v_shr_i259_1 18446744073709551615@uint128;
assume v_y_sroa_0_0_insert_ext_i_1 = v_shr_i259_1 && true;
add v_add_i358_1 v_mul_i366_1 v_mul_i344_1;
add v_add_i336_1 v_add_i358_1 v_mul_i374_1;
add v_add_i_1 v_add_i336_1 v_y_sroa_0_0_insert_ext_i_1;
cast v_retval_sroa_0_0_extract_trunc_i250_1@uint64 v_add_i_1;
and v_and141_1@uint64 v_retval_sroa_0_0_extract_trunc_i250_1 2251799813685247@uint64;
split v_shr_i_1 tmp_to_be_used_5 v_add_i_1 51;
vpc tmp_v_5@uint64 tmp_to_be_used_5;
assume tmp_v_5 = v_and141_1 && true;
vpc v_retval_sroa_0_0_extract_trunc_i242_1@uint64 v_shr_i_1;
mul v_mul147_1 v_retval_sroa_0_0_extract_trunc_i242_1 19@uint64;
add v_add_1 v_mul147_1 v_and_1;
and v_and148_1@uint64 v_add_1 2251799813685247@uint64;
split v_shr_1 tmp_to_be_used_6 v_add_1 51;
vpc tmp_v_6@uint64 tmp_to_be_used_6;
assume tmp_v_6 = v_and148_1 && true;
add v_add149_1 v_shr_1 v_and99_1;
mov mem1_0_1 v_and148_1;
mov mem1_8_1 v_add149_1;
mov mem1_16_1 v8_0_1;
mov mem1_24_1 v8_1_1;
mov mem1_32_1 v_and141_1;
{ mem1_0_1 + (mem1_8_1 * 2251799813685248) + (mem1_16_1 * 5070602400912917605986812821504) + (mem1_24_1 * 11417981541647679048466287755595961091061972992) + (mem1_32_1 * 25711008708143844408671393477458601640355247900524685364822016) = (mem0_0_0 + (mem0_8_0 * 2251799813685248) + (mem0_16_0 * 5070602400912917605986812821504) + (mem0_24_0 * 11417981541647679048466287755595961091061972992) + (mem0_32_0 * 25711008708143844408671393477458601640355247900524685364822016)) * (mem0_0_0 + (mem0_8_0 * 2251799813685248) + (mem0_16_0 * 5070602400912917605986812821504) + (mem0_24_0 * 11417981541647679048466287755595961091061972992) + (mem0_32_0 * 25711008708143844408671393477458601640355247900524685364822016)) (mod 57896044618658097711785492504343953926634992332820282019728792003956564819968 - 19) && and [tmp_v_1 = v_and_1, v_y_sroa_0_0_insert_ext_i308_1 = v_shr_i319_1, tmp_v_2 = v_and99_1, v_y_sroa_0_0_insert_ext_i288_1 = v_shr_i299_1, v_y_sroa_0_0_insert_ext_i268_1 = v_shr_i279_1, tmp_v_3 = v8_0_1, tmp_v_4 = v8_1_1, v_y_sroa_0_0_insert_ext_i_1 = v_shr_i259_1, tmp_v_5 = v_and141_1, tmp_v_6 = v_and148_1, mem1_0_1 <=u 2251799813685247@64, mem1_8_1 <=u 2251799813693439@64, mem1_16_1 <=u 2251799813685247@64, mem1_24_1 <=u 2251799813685247@64, mem1_32_1 <=u 2251799813685247@64] }
