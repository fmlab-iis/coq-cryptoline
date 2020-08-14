(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=8G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=8G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  secp256k1_scalar_add_tuned.cl

Results of checking CNF formulas:       [OK]            2.696818 seconds
Finding polynomial coefficients         [OK]            0.093270 seconds
Verification result:                    [OK]            4.287216 seconds
*)

proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 b0_0, uint64 b1_0, uint64 b2_0, uint64 b3_0, uint64 overflow_0) =
{ true && true }
mov a28_0_1 a0_0;
mov a28_8_1 a1_0;
mov a28_16_1 a2_0;
mov a28_24_1 a3_0;
mov b29_0_1 b0_0;
mov b29_8_1 b1_0;
mov b29_16_1 b2_0;
mov b29_24_1 b3_0;
mov v1_1 a28_0_1;
vpc v2_1@uint128 v1_1;
mov v3_1 b29_0_1;
vpc v4_1@uint128 v3_1;
add t30_1 v2_1 v4_1;
adds carry_1 v5_1 v1_1 v3_1;
split t32_1 tmp_to_use_1 t30_1 64;
vpc t32_p_1@uint1 t32_1;
assume t32_p_1 = carry_1 && true;
mov v6_1 a28_8_1;
vpc v7_1@uint128 v6_1;
mov v8_1 b29_8_1;
vpc v9_1@uint128 v8_1;
add v10_1 v7_1 v9_1;
add t33_1 v10_1 t32_1;
cast v11_1@uint64 t33_1;
split t34_1 tmp_to_use_t33_1 t33_1 64;
vpc tmp_to_use_p_1@uint64 tmp_to_use_t33_1;
assume tmp_to_use_p_1 = v11_1 && true;
mov v12_1 a28_16_1;
vpc v13_1@uint128 v12_1;
mov v14_1 b29_16_1;
vpc v15_1@uint128 v14_1;
add v16_1 v13_1 v15_1;
add t35_1 v16_1 t34_1;
cast v17_1@uint64 t35_1;
split t36_1 tmp_to_use_t35_1 t35_1 64;
vpc tmp_to_use_p_2@uint64 tmp_to_use_t35_1;
assume tmp_to_use_p_2 = v17_1 && true;
mov v18_1 a28_24_1;
vpc v19_1@uint128 v18_1;
mov v20_1 b29_24_1;
vpc v21_1@uint128 v20_1;
add v22_1 v19_1 v21_1;
add t37_1 v22_1 t36_1;
cast v23_1@uint64 t37_1;
split t38_1 tmp_to_use_t37_1 t37_1 64;
vpc tmp_to_use_p_3@uint64 tmp_to_use_t37_1;
assume tmp_to_use_p_3 = v23_1 && true;
subb lt_value_1 dontcare_1 v23_1 18446744073709551615@uint64;
mov v63_1 lt_value_1;
vpc v63_2@uint8 v63_1;
add tmp_for_compare_1 18446744073709551613@uint64 1@uint64;
subb v64_1 dontcare_2 v17_1 tmp_for_compare_1;
vpc v64_2@uint8 v64_1;
vpc v63_p_1@uint1 v63_2;
cmov v65_1 v63_p_1 1@uint8 v64_2;
vpc no66_1@int32 v65_1;
subb lt_value_2 dontcare_3 v17_1 18446744073709551615@uint64;
mov v67_1 lt_value_2;
not v67_2@uint1 v67_1;
vpc v67_3@uint8 v67_2;
vpc v68_1@uint1 v67_3;
vpc no66_2@uint1 no66_1;
not v69_1@uint1 no66_2;
cmov v70_1 v68_1 v69_1 0@uint1;
add tmp_for_compare_2 13451932020343611450@uint64 1@uint64;
subb v71_1 dontcare_4 v11_1 tmp_for_compare_2;
vpc v71_2@uint8 v71_1;
vpc v65_p_1@uint1 v65_1;
cmov v72_1 v65_p_1 1@uint8 v71_2;
vpc no73_1@uint1 v72_1;
subb v74_1 dontcare_5 13451932020343611451@uint64 v11_1;
vpc v74_2@uint8 v74_1;
not v76_1@uint1 no73_1;
subb v79_1 dontcare_6 13822214165235122496@uint64 v5_1;
vpc v79_2@uint8 v79_1;
vpc v74_p_1@uint1 v74_2;
cmov v78_1 v74_p_1 1@uint8 v79_2;
vpc v40_1@uint8 v78_1;
vpc v40_p_1@uint1 v40_1;
cmov v47_1 v40_p_1 v76_1 0@uint1;
vpc v47_p_1@uint1 v47_1;
cmov yes82_1 v47_p_1 1@uint1 v70_1;
vpc yes82_2@int32 yes82_1;
vpc v24_1@uint32 yes82_2;
vpc v25_1@uint32 t38_1;
add v26_1 v24_1 v25_1;
vpc overflow39_1@int32 v26_1;
vpc v54_1@uint128 v5_1;
vpc v41_1@uint64 v26_1;
mul v42_1 v41_1 4624529908474429119@uint64;
vpc v43_1@uint128 v42_1;
add t44_1 v43_1 v54_1;
adds carry_2 v45_1 v5_1 v42_1;
mov r31_0_1 v45_1;
split t46_1 tmp_to_use_2 t44_1 64;
vpc t46_p_1@uint1 t46_1;
assume t46_p_1 = carry_2 && true;
mov value_lo_1 18446744073709551615@uint64;
mov value_hi_1 0@uint64;
join value_1 value_hi_1 value_lo_1;
and v87_1@uint128 t33_1 value_1;
assume v87_1 = tmp_to_use_t33_1 && true;
mul v48_1 v41_1 4994812053365940164@uint64;
vpc v49_1@uint128 v48_1;
add v50_1 v49_1 v87_1;
add t51_1 t46_1 v50_1;
cast v52_1@uint64 t51_1;
mov r31_8_1 v52_1;
split t53_1 tmp_to_use_3 t51_1 64;
vpc tmp_to_use_p_4@uint64 tmp_to_use_3;
assume tmp_to_use_p_4 = v52_1 && true;
mov value_lo_2 18446744073709551615@uint64;
mov value_hi_2 0@uint64;
join value_2 value_hi_2 value_lo_2;
and v88_1@uint128 t35_1 value_2;
assume v88_1 = tmp_to_use_t35_1 && true;
vpc v55_1@uint128 v26_1;
add v56_1 v55_1 v88_1;
add t57_1 t53_1 v56_1;
cast v58_1@uint64 t57_1;
mov r31_16_1 v58_1;
split t59_1 tmp_to_use_4 t57_1 64;
vpc tmp_to_use_p_5@uint64 tmp_to_use_4;
assume tmp_to_use_p_5 = v58_1 && true;
mov value_lo_3 18446744073709551615@uint64;
mov value_hi_3 0@uint64;
join value_3 value_hi_3 value_lo_3;
and v89_1@uint128 t37_1 value_3;
assume v89_1 = tmp_to_use_t37_1 && true;
add t61_1 t59_1 v89_1;
split tmp_1 v62_1 t61_1 64;
vpc tmp_2@uint1 tmp_1;
vpc yes82_p_1@uint1 yes82_2;
assume tmp_2 = yes82_p_1 && true;
vpc v62_2@uint64 v62_1;
mov r31_24_1 v62_2;
mov coverflow_1 overflow39_1;
mov c0_1 r31_0_1;
mov c1_1 r31_8_1;
mov c2_1 r31_16_1;
mov c3_1 r31_24_1;
{ c0_1 + (c1_1 * 18446744073709551616) + (c2_1 * 340282366920938463463374607431768211456) + (c3_1 * 6277101735386680763835789423207666416102355444464034512896) = a0_0 + (a1_0 * 18446744073709551616) + (a2_0 * 340282366920938463463374607431768211456) + (a3_0 * 6277101735386680763835789423207666416102355444464034512896) + b0_0 + (b1_0 * 18446744073709551616) + (b2_0 * 340282366920938463463374607431768211456) + (b3_0 * 6277101735386680763835789423207666416102355444464034512896) (mod 13822214165235122497 + (13451932020343611451 * 18446744073709551616) + (18446744073709551614 * 340282366920938463463374607431768211456) + (18446744073709551615 * 6277101735386680763835789423207666416102355444464034512896)) && and [t32_p_1 = carry_1, tmp_to_use_p_1 = v11_1, tmp_to_use_p_2 = v17_1, tmp_to_use_p_3 = v23_1, t46_p_1 = carry_2, v87_1 = tmp_to_use_t33_1, tmp_to_use_p_4 = v52_1, v88_1 = tmp_to_use_t35_1, tmp_to_use_p_5 = v58_1, v89_1 = tmp_to_use_t37_1, tmp_2 = yes82_p_1] }
