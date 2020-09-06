(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=8G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=8G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  secp256k1_fe_mul_inner_tuned.cl

Results of checking CNF formulas:       [OK]            99.108760 seconds
Finding polynomial coefficients         [OK]            0.199893 seconds
Verification result:                    [OK]            115.840078 seconds
*)

proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 a4_0, uint64 b0_0, uint64 b1_0, uint64 b2_0, uint64 b3_0, uint64 b4_0) =
{ true && and [a0_0 <u 72057594037927928@64, a1_0 <u 72057594037927928@64, a2_0 <u 72057594037927928@64, a3_0 <u 72057594037927928@64, a4_0 <u 4503599627370488@64, b0_0 <u 72057594037927928@64, b1_0 <u 72057594037927928@64, b2_0 <u 72057594037927928@64, b3_0 <u 72057594037927928@64, b4_0 <u 4503599627370488@64] }
mov a82_0_1 a0_0;
mov a82_8_1 a1_0;
mov a82_16_1 a2_0;
mov a82_24_1 a3_0;
mov a82_32_1 a4_0;
mov b89_0_1 b0_0;
mov b89_8_1 b1_0;
mov b89_16_1 b2_0;
mov b89_24_1 b3_0;
mov b89_32_1 b4_0;
mov a083_1 a82_0_1;
mov a184_1 a82_8_1;
mov a285_1 a82_16_1;
mov a386_1 a82_24_1;
mov a487_1 a82_32_1;
mov v2_1 b89_24_1;
mulj v4_1 a083_1 v2_1;
mov v6_1 b89_16_1;
mulj v8_1 a184_1 v6_1;
add v141_1 v4_1 v8_1;
mov v11_1 b89_0_1;
mulj v13_1 a386_1 v11_1;
mov v15_1 b89_8_1;
mulj v17_1 a285_1 v15_1;
add v142_1 v13_1 v141_1;
add d90_1 v17_1 v142_1;
mov v20_1 b89_32_1;
mulj c91_1 a487_1 v20_1;
split tmp_and_1 v22_1 c91_1 52;
mov value_lo_1 68719492368@uint64;
mov value_hi_1 0@uint64;
join value_1 value_hi_1 value_lo_1;
mul v23_1 v22_1 value_1;
add d92_1 v23_1 d90_1;
split c93_1 tmp_to_use_1 c91_1 52;
assume tmp_to_use_1 = v22_1 && true;
cast v24_1@uint64 d92_1;
split tmp_and_2 t394_1 v24_1 52;
split d95_1 tmp_to_use_2 d92_1 52;
vpc tmp_to_use_p_1@uint64 tmp_to_use_2;
assume tmp_to_use_2 = t394_1 && true;
mulj v26_1 a083_1 v20_1;
mulj v27_1 v2_1 a184_1;
add v135_1 v26_1 v27_1;
mulj v29_1 a386_1 v15_1;
mulj v30_1 v6_1 a285_1;
add v136_1 v29_1 v135_1;
add v137_1 v30_1 v136_1;
mulj v33_1 v11_1 a487_1;
add v138_1 v33_1 v137_1;
mov value_lo_2 68719492368@uint64;
mov value_hi_2 0@uint64;
join value_2 value_hi_2 value_lo_2;
mul v35_1 c93_1 value_2;
add v139_1 v35_1 v138_1;
add d97_1 d95_1 v139_1;
cast v36_1@uint64 d97_1;
split d98_1 tmp_to_use1_1 d97_1 52;
split v25_1 tmp_to_use2_1 v36_1 48;
split tmp_and_3 tx99_1 v25_1 4;
vpc tmp_to_use1_p_1@uint64 tmp_to_use1_1;
assume tmp_to_use1_1 = (tx99_1 * 281474976710656) + tmp_to_use2_1 && true;
split tmp_and_4 t4100_1 v36_1 48;
assume tmp_to_use2_1 = t4100_1 && true;
mulj c101_1 a083_1 v11_1;
mulj v37_1 a184_1 v20_1;
mulj v38_1 v2_1 a285_1;
add v132_1 v37_1 v38_1;
mulj v40_1 v15_1 a487_1;
mulj v41_1 v6_1 a386_1;
add v133_1 v40_1 v132_1;
add v43_1 v41_1 v133_1;
add d102_1 v43_1 d98_1;
cast v44_1@uint64 d102_1;
split d103_1 tmp_to_use_3 d102_1 52;
split tmp1_1 tmp2_1 v44_1 60;
shl v88_1 tmp2_1 4;
and v45_1@uint64 v88_1 72057594037927920@uint64;
vpc tmp_to_use_p_2@uint64 tmp_to_use_3;
assume v45_1 = tmp_to_use_3 * 16 && true;
or u0104_1@uint64 v45_1 tx99_1;
assume u0104_1 = v45_1 + tx99_1 && true;
mulj v47_1 u0104_1 4294968273@uint64;
add c105_1 v47_1 c101_1;
cast v48_1@uint64 c105_1;
split tmp_and_5 v49_1 v48_1 52;
mov r106_0_1 v49_1;
split c108_1 tmp_to_use_4 c105_1 52;
vpc tmp_to_use_p_3@uint64 tmp_to_use_4;
assume tmp_to_use_4 = v49_1 && true;
mulj v50_1 a083_1 v15_1;
mulj v51_1 a184_1 v11_1;
add v129_1 v50_1 v51_1;
mulj v53_1 a285_1 v20_1;
mulj v54_1 v2_1 a386_1;
add v55_1 v53_1 v54_1;
mulj v56_1 v6_1 a487_1;
add v57_1 v55_1 v56_1;
add d110_1 v57_1 d103_1;
split tmp_and_6 v58_1 d110_1 52;
mov value_lo_3 68719492368@uint64;
mov value_hi_3 0@uint64;
join value_3 value_hi_3 value_lo_3;
mul v59_1 v58_1 value_3;
add v130_1 v59_1 v129_1;
add c111_1 c108_1 v130_1;
split d112_1 tmp_to_use_5 d110_1 52;
assume tmp_to_use_5 = v58_1 && true;
cast v60_1@uint64 c111_1;
split tmp_and_7 v61_1 v60_1 52;
mov r106_8_1 v61_1;
split c114_1 tmp_to_use_6 c111_1 52;
vpc tmp_to_use_p_4@uint64 tmp_to_use_6;
assume tmp_to_use_6 = v61_1 && true;
mulj v62_1 a083_1 v6_1;
mulj v63_1 a184_1 v15_1;
add v128_1 v62_1 v63_1;
mulj v65_1 v11_1 a285_1;
add v127_1 v65_1 v128_1;
mulj v67_1 a386_1 v20_1;
mulj v68_1 v2_1 a487_1;
add v69_1 v67_1 v68_1;
add d116_1 v69_1 d112_1;
split tmp_and_8 v70_1 d116_1 52;
mov value_lo_4 68719492368@uint64;
mov value_hi_4 0@uint64;
join value_4 value_hi_4 value_lo_4;
mul v71_1 v70_1 value_4;
add v126_1 v71_1 v127_1;
add c117_1 c114_1 v126_1;
split d118_1 tmp_to_use_7 d116_1 52;
assume tmp_to_use_7 = v70_1 && true;
cast v72_1@uint64 c117_1;
split tmp_and_9 v73_1 v72_1 52;
mov r106_16_1 v73_1;
split c120_1 tmp_to_use_8 c117_1 52;
vpc tmp_to_use_p_5@uint64 tmp_to_use_8;
assume tmp_to_use_8 = v73_1 && true;
mov value_lo_5 68719492368@uint64;
mov value_hi_5 0@uint64;
join value_5 value_hi_5 value_lo_5;
mul v74_1 d118_1 value_5;
vpc v75_1@uint128 t394_1;
add v76_1 v74_1 v75_1;
add c121_1 v76_1 c120_1;
cast v77_1@uint64 c121_1;
split tmp_and_10 v78_1 v77_1 52;
mov r106_24_1 v78_1;
split c123_1 tmp_to_use_9 c121_1 52;
vpc tmp_to_use_p_6@uint64 tmp_to_use_9;
assume tmp_to_use_9 = v78_1 && true;
vpc v79_1@uint128 t4100_1;
add c124_1 v79_1 c123_1;
vpc v80_1@uint64 c124_1;
mov r106_32_1 v80_1;
mov c0_1 r106_0_1;
mov c1_1 r106_8_1;
mov c2_1 r106_16_1;
mov c3_1 r106_24_1;
mov c4_1 r106_32_1;
{ c0_1 + (c1_1 * 4503599627370496) + (c2_1 * 20282409603651670423947251286016) + (c3_1 * 91343852333181432387730302044767688728495783936) + (c4_1 * 411376139330301510538742295639337626245683966408394965837152256) = (a0_0 + (a1_0 * 4503599627370496) + (a2_0 * 20282409603651670423947251286016) + (a3_0 * 91343852333181432387730302044767688728495783936) + (a4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (b0_0 + (b1_0 * 4503599627370496) + (b2_0 * 20282409603651670423947251286016) + (b3_0 * 91343852333181432387730302044767688728495783936) + (b4_0 * 411376139330301510538742295639337626245683966408394965837152256)) (mod 115792089237316195423570985008687907853269984665640564039457584007908834671663) && and [tmp_to_use_1 = v22_1, tmp_to_use_p_1 = t394_1, tmp_to_use1_p_1 = add (mul (tx99_1) (281474976710656@64)) (tmp_to_use2_1), tmp_to_use2_1 = t4100_1, v45_1 = mul (tmp_to_use_p_2) (16@64), u0104_1 = add (v45_1) (tx99_1), tmp_to_use_p_3 = v49_1, tmp_to_use_5 = v58_1, tmp_to_use_p_4 = v61_1, tmp_to_use_7 = v70_1, tmp_to_use_p_5 = v73_1, tmp_to_use_p_6 = v78_1, c0_1 <u 9007199254740991@64, c1_1 <u 9007199254740991@64, c2_1 <u 9007199254740991@64, c3_1 <u 9007199254740991@64, c4_1 <u 562949953421311@64] }