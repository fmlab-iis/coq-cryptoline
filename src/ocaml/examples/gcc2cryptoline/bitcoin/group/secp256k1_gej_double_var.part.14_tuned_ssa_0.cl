proc main(uint64 x0_0, uint64 x1_0, uint64 x2_0, uint64 x3_0, uint64 x4_0, uint64 y0_0, uint64 y1_0, uint64 y2_0, uint64 y3_0, uint64 y4_0, uint64 z0_0, uint64 z1_0, uint64 z2_0, uint64 z3_0, uint64 z4_0) =
{ true && and [x0_0 <u 72057594037927928@64, x1_0 <u 72057594037927928@64, x2_0 <u 72057594037927928@64, x3_0 <u 72057594037927928@64, x4_0 <u 4503599627370488@64, y0_0 <u 72057594037927928@64, y1_0 <u 72057594037927928@64, y2_0 <u 72057594037927928@64, y3_0 <u 72057594037927928@64, y4_0 <u 4503599627370488@64, z0_0 <u 72057594037927928@64, z1_0 <u 72057594037927928@64, z2_0 <u 72057594037927928@64, z3_0 <u 72057594037927928@64, z4_0 <u 4503599627370488@64] }
split x13_1 t414_1 y4_0 48;
mul v1_1 x13_1 4294968273@uint64;
add t015_1 v1_1 y0_0;
split v2_1 t017_1 t015_1 52;
add t116_1 v2_1 y1_0;
split v3_1 t119_1 t116_1 52;
add t218_1 v3_1 y2_0;
split v4_1 t221_1 t218_1 52;
add t320_1 v4_1 y3_0;
split v5_1 t323_1 t320_1 52;
add t422_1 v5_1 t414_1;
mul v4_2 t017_1 2@uint64;
mul v6_1 t119_1 2@uint64;
mul v8_1 t221_1 2@uint64;
mul v10_1 t323_1 2@uint64;
mul v12_1 t422_1 2@uint64;
mulj v4_3 z0_0 y3_0;
mulj v8_2 z1_0 y2_0;
add v141_1 v4_3 v8_2;
mulj v13_1 z3_0 y0_0;
mulj v17_1 z2_0 y1_0;
add v142_1 v13_1 v141_1;
add d90_1 v17_1 v142_1;
mulj c91_1 z4_0 y4_0;
split tmp_and_1 v22_1 c91_1 52;
join value_1 0@uint64 68719492368@uint64;
mul v23_1 v22_1 value_1;
add d92_1 v23_1 d90_1;
split c93_1 tmp_to_use_1 c91_1 52;
assume tmp_to_use_1 = v22_1 && true;
cast v24_1@uint64 d92_1;
split tmp_and_2 t394_1 v24_1 52;
split d95_1 tmp_to_use_2 d92_1 52;
vpc tmp_to_use_p_1@uint64 tmp_to_use_2;
assume tmp_to_use_2 = t394_1 && true;
mulj v26_1 z0_0 y4_0;
mulj v27_1 y3_0 z1_0;
add v135_1 v26_1 v27_1;
mulj v29_1 z3_0 y1_0;
mulj v30_1 y2_0 z2_0;
add v136_1 v29_1 v135_1;
add v137_1 v30_1 v136_1;
mulj v33_1 y0_0 z4_0;
add v138_1 v33_1 v137_1;
join value_2 0@uint64 68719492368@uint64;
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
mulj c101_1 z0_0 y0_0;
mulj v37_1 z1_0 y4_0;
mulj v38_1 y3_0 z2_0;
add v132_1 v37_1 v38_1;
mulj v40_1 y1_0 z4_0;
mulj v41_1 y2_0 z3_0;
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
split c108_1 tmp_to_use_4 c105_1 52;
vpc tmp_to_use_p_3@uint64 tmp_to_use_4;
assume tmp_to_use_4 = v49_1 && true;
mulj v50_1 z0_0 y1_0;
mulj v51_1 z1_0 y0_0;
add v129_1 v50_1 v51_1;
mulj v53_1 z2_0 y4_0;
mulj v54_1 y3_0 z3_0;
add v55_1 v53_1 v54_1;
mulj v56_1 y2_0 z4_0;
add v57_1 v55_1 v56_1;
add d110_1 v57_1 d103_1;
split tmp_and_6 v58_1 d110_1 52;
join value_3 0@uint64 68719492368@uint64;
mul v59_1 v58_1 value_3;
add v130_1 v59_1 v129_1;
add c111_1 c108_1 v130_1;
split d112_1 tmp_to_use_5 d110_1 52;
assume tmp_to_use_5 = v58_1 && true;
cast v60_1@uint64 c111_1;
split tmp_and_7 v61_1 v60_1 52;
split c114_1 tmp_to_use_6 c111_1 52;
vpc tmp_to_use_p_4@uint64 tmp_to_use_6;
assume tmp_to_use_6 = v61_1 && true;
mulj v62_1 z0_0 y2_0;
mulj v63_1 z1_0 y1_0;
add v128_1 v62_1 v63_1;
mulj v65_1 y0_0 z2_0;
add v127_1 v65_1 v128_1;
mulj v67_1 z3_0 y4_0;
mulj v68_1 y3_0 z4_0;
add v69_1 v67_1 v68_1;
add d116_1 v69_1 d112_1;
split tmp_and_8 v70_1 d116_1 52;
join value_4 0@uint64 68719492368@uint64;
mul v71_1 v70_1 value_4;
add v126_1 v71_1 v127_1;
add c117_1 c114_1 v126_1;
split d118_1 tmp_to_use_7 d116_1 52;
assume tmp_to_use_7 = v70_1 && true;
cast v72_1@uint64 c117_1;
split tmp_and_9 v73_1 v72_1 52;
split c120_1 tmp_to_use_8 c117_1 52;
vpc tmp_to_use_p_5@uint64 tmp_to_use_8;
assume tmp_to_use_8 = v73_1 && true;
join value_5 0@uint64 68719492368@uint64;
mul v74_1 d118_1 value_5;
vpc v75_1@uint128 t394_1;
add v76_1 v74_1 v75_1;
add c121_1 v76_1 c120_1;
cast v77_1@uint64 c121_1;
split tmp_and_10 v78_1 v77_1 52;
split c123_1 tmp_to_use_9 c121_1 52;
vpc tmp_to_use_p_6@uint64 tmp_to_use_9;
assume tmp_to_use_9 = v78_1 && true;
vpc v79_1@uint128 t4100_1;
add c124_1 v79_1 c123_1;
vpc v80_1@uint64 c124_1;
mul v18_1 v49_1 2@uint64;
mul v20_2 v61_1 2@uint64;
mul v22_2 v73_1 2@uint64;
mul v24_2 v78_1 2@uint64;
mul v26_2 v80_1 2@uint64;
mul v1_2 x0_0 2@uint64;
mulj v4_4 v1_2 x3_0;
mul v5_3 x1_0 2@uint64;
mulj v8_3 v5_3 x2_0;
add d66_1 v4_4 v8_3;
mulj c67_1 x4_0 x4_0;
join value_6 0@uint64 4503599627370495@uint64;
and v11_3@uint128 c67_1 value_6;
join value_7 0@uint64 68719492368@uint64;
mul v12_2 v11_3 value_7;
add d68_1 v12_2 d66_1;
split c69_1 tmp_to_use_10 c67_1 52;
assume tmp_to_use_10 = v11_3 && true;
cast v13_2@int64 d68_1;
and t370_1@int64 v13_2 4503599627370495@int64;
split d71_1 tmp_to_use_11 d68_1 52;
vpc tmp_to_use_p_7@uint64 tmp_to_use_11;
assume tmp_to_use_11 = t370_1 && true;
mul a472_1 x4_0 2@uint64;
mulj v16_1 x0_0 a472_1;
mulj v17_3 x3_0 v5_3;
add v18_2 v16_1 v17_3;
mulj v19_2 x2_0 x2_0;
add v20_3 v18_2 v19_2;
join value_8 0@uint64 68719492368@uint64;
mul v21_2 c69_1 value_8;
add v105_1 v20_3 v21_2;
add d74_1 d71_1 v105_1;
cast v22_3@int64 d74_1;
split d75_1 tmp_to_use1_2 d74_1 52;
split v10_2 tmp_to_use2_2 v22_3 48;
and tx76_1@int64 v10_2 15@int64;
vpc tmp_to_use1_p_2@uint64 tmp_to_use1_2;
assume tmp_to_use1_2 = (tx76_1 * 281474976710656) + tmp_to_use2_2 && true;
and t477_1@int64 v22_3 281474976710655@int64;
assume tmp_to_use2_2 = t477_1 && true;
mulj c78_1 x0_0 x0_0;
mulj v24_3 a472_1 x1_0;
mul v25_3 x2_0 2@uint64;
mulj v27_2 x3_0 v25_3;
add v28_1 v24_3 v27_2;
add d79_1 v28_1 d75_1;
cast v29_2@int64 d79_1;
split d80_1 tmp_to_use_12 d79_1 52;
split tmp1_2 tmp2_2 v29_2 60;
shl v65_2 tmp2_2 4;
and v30_2@int64 v65_2 72057594037927920@int64;
vpc tmp_to_use_p_8@uint64 tmp_to_use_12;
assume v30_2 = tmp_to_use_12 * 16 && true;
vpc v30_3@uint64 v30_2;
vpc tx76_2@uint64 tx76_1;
add u081_1 v30_3 tx76_2;
mulj v32_1 u081_1 4294968273@uint64;
add c82_1 v32_1 c78_1;
cast v33_2@uint64 c82_1;
and v34_1@uint64 v33_2 4503599627370495@uint64;
split c85_1 tmp_to_use_13 c82_1 52;
vpc tmp_to_use_p_9@uint64 tmp_to_use_13;
assume tmp_to_use_13 = v34_1 && true;
mulj v35_2 v1_2 x1_0;
mulj v36_2 x2_0 a472_1;
mulj v37_2 x3_0 x3_0;
add v38_2 v36_2 v37_2;
add d87_1 v38_2 d80_1;
join value_9 0@uint64 4503599627370495@uint64;
and v39_1@uint128 d87_1 value_9;
join value_10 0@uint64 68719492368@uint64;
mul v40_2 v39_1 value_10;
add v103_1 v35_2 v40_2;
add c88_1 c85_1 v103_1;
split d89_1 tmp_to_use_14 d87_1 52;
assume tmp_to_use_14 = v39_1 && true;
cast v41_2@uint64 c88_1;
and v42_1@uint64 v41_2 4503599627370495@uint64;
split c91_2 tmp_to_use_15 c88_1 52;
vpc tmp_to_use_p_10@uint64 tmp_to_use_15;
assume tmp_to_use_15 = v42_1 && true;
mulj v43_2 v1_2 x2_0;
mulj v44_2 x1_0 x1_0;
add v45_2 v43_2 v44_2;
mulj v46_1 x3_0 a472_1;
add d93_1 v46_1 d89_1;
join value_11 0@uint64 4503599627370495@uint64;
and v47_2@uint128 d93_1 value_11;
join value_12 0@uint64 68719492368@uint64;
mul v48_2 v47_2 value_12;
add v104_1 v45_2 v48_2;
add c94_1 c91_2 v104_1;
split d95_2 tmp_to_use_16 d93_1 52;
assume tmp_to_use_16 = v47_2 && true;
cast v49_2@uint64 c94_1;
and v50_2@uint64 v49_2 4503599627370495@uint64;
split c97_1 tmp_to_use_17 c94_1 52;
vpc tmp_to_use_p_11@uint64 tmp_to_use_17;
assume tmp_to_use_17 = v50_2 && true;
join value_13 0@uint64 68719492368@uint64;
mul v51_2 d95_2 value_13;
vpc v52_1@uint128 t370_1;
add v53_2 v51_2 v52_1;
add c98_1 v53_2 c97_1;
cast v54_2@uint64 c98_1;
and v55_2@uint64 v54_2 4503599627370495@uint64;
split c100_1 tmp_to_use_18 c98_1 52;
vpc tmp_to_use_p_12@uint64 tmp_to_use_18;
assume tmp_to_use_18 = v55_2 && true;
vpc v56_2@uint128 t477_1;
add c101_2 v56_2 c100_1;
vpc v57_2@uint64 c101_2;
mul v29_3 v34_1 3@uint64;
mul v31_1 v42_1 3@uint64;
mul v33_3 v50_2 3@uint64;
mul v35_3 v55_2 3@uint64;
mul v37_3 v57_2 3@uint64;
mul v190_1 v34_1 6@uint64;
mulj v193_1 v190_1 v35_3;
mul v194_1 v42_1 6@uint64;
mulj v197_1 v194_1 v33_3;
add d198_1 v193_1 v197_1;
mulj c200_1 v37_3 v37_3;
join value_14 0@uint64 4503599627370495@uint64;
and v201_1@uint128 c200_1 value_14;
join value_15 0@uint64 68719492368@uint64;
mul v202_1 v201_1 value_15;
add d203_1 d198_1 v202_1;
split c204_1 tmp_to_use_19 c200_1 52;
assume tmp_to_use_19 = v201_1 && true;
cast v205_1@int64 d203_1;
and t3206_1@int64 v205_1 4503599627370495@int64;
split d207_1 tmp_to_use_20 d203_1 52;
vpc tmp_to_use_p_13@uint64 tmp_to_use_20;
assume tmp_to_use_20 = t3206_1 && true;
mul a4208_1 v57_2 6@uint64;
mulj v211_1 v29_3 a4208_1;
mulj v212_1 v35_3 v194_1;
add v213_1 v211_1 v212_1;
mulj v214_1 v33_3 v33_3;
add v215_1 v213_1 v214_1;
join value_16 0@uint64 68719492368@uint64;
mul v217_1 c204_1 value_16;
add v285_1 v215_1 v217_1;
add d218_1 d207_1 v285_1;
cast v219_1@int64 d218_1;
split d220_1 tmp_to_use1_3 d218_1 52;
split v221_1 tmp_to_use2_3 v219_1 48;
and tx222_1@int64 v221_1 15@int64;
vpc tmp_to_use1_p_3@uint64 tmp_to_use1_3;
assume tmp_to_use1_3 = (tx222_1 * 281474976710656) + tmp_to_use2_3 && true;
and t4223_1@int64 v219_1 281474976710655@int64;
assume tmp_to_use2_3 = t4223_1 && true;
mulj c224_1 v29_3 v29_3;
mulj v226_1 a4208_1 v31_1;
mul v227_1 v50_2 6@uint64;
mulj v229_1 v35_3 v227_1;
add v230_1 v226_1 v229_1;
add d231_1 d220_1 v230_1;
cast v232_1@int64 d231_1;
split d233_1 tmp_to_use_21 d231_1 52;
split tmp1_3 tmp2_3 v232_1 60;
shl v234_1 tmp2_3 4;
and v235_1@int64 v234_1 72057594037927920@int64;
vpc tmp_to_use_p_14@uint64 tmp_to_use_21;
assume v235_1 = tmp_to_use_21 * 16 && true;
vpc v235_2@uint64 v235_1;
vpc tx222_2@uint64 tx222_1;
add u0236_1 tx222_2 v235_2;
mulj v238_1 u0236_1 4294968273@uint64;
add c239_1 c224_1 v238_1;
cast v240_1@uint64 c239_1;
and v241_1@uint64 v240_1 4503599627370495@uint64;
split c242_1 tmp_to_use_22 c239_1 52;
vpc tmp_to_use_p_15@uint64 tmp_to_use_22;
assume tmp_to_use_22 = v241_1 && true;
mulj v243_1 v190_1 v31_1;
mulj v245_1 v33_3 a4208_1;
mulj v246_1 v35_3 v35_3;
add v247_1 v245_1 v246_1;
add d248_1 d233_1 v247_1;
join value_17 0@uint64 4503599627370495@uint64;
and v249_1@uint128 d248_1 value_17;
join value_18 0@uint64 68719492368@uint64;
mul v250_1 v249_1 value_18;
add v284_1 v243_1 v250_1;
add c251_1 c242_1 v284_1;
split d252_1 tmp_to_use_23 d248_1 52;
assume tmp_to_use_23 = v249_1 && true;
cast v253_1@uint64 c251_1;
and v254_1@uint64 v253_1 4503599627370495@uint64;
split c255_1 tmp_to_use_24 c251_1 52;
vpc tmp_to_use_p_16@uint64 tmp_to_use_24;
assume tmp_to_use_24 = v254_1 && true;
mulj v256_1 v190_1 v33_3;
mulj v257_1 v31_1 v31_1;
add v258_1 v256_1 v257_1;
mulj v260_1 v35_3 a4208_1;
add d261_1 d252_1 v260_1;
join value_19 0@uint64 4503599627370495@uint64;
and v262_1@uint128 d261_1 value_19;
join value_20 0@uint64 68719492368@uint64;
mul v263_1 v262_1 value_20;
add v145_1 v258_1 v263_1;
add c264_1 v145_1 c255_1;
split d265_1 tmp_to_use_25 d261_1 52;
assume tmp_to_use_25 = v262_1 && true;
cast v266_1@uint64 c264_1;
and v267_1@uint64 v266_1 4503599627370495@uint64;
split c268_1 tmp_to_use_26 c264_1 52;
vpc tmp_to_use_p_17@uint64 tmp_to_use_26;
assume tmp_to_use_26 = v267_1 && true;
join value_21 0@uint64 68719492368@uint64;
mul v269_1 d265_1 value_21;
vpc v270_1@uint128 t3206_1;
add v271_1 v269_1 v270_1;
add c272_1 c268_1 v271_1;
cast v273_1@uint64 c272_1;
and v274_1@uint64 v273_1 4503599627370495@uint64;
split c275_1 tmp_to_use_27 c272_1 52;
vpc tmp_to_use_p_18@uint64 tmp_to_use_27;
assume tmp_to_use_27 = v274_1 && true;
vpc v276_1@uint128 t4223_1;
add c277_1 c275_1 v276_1;
vpc v278_1@uint64 c277_1;
mul v1_3 y0_0 2@uint64;
mulj v4_5 v1_3 y3_0;
mul v5_4 y1_0 2@uint64;
mulj v8_4 v5_4 y2_0;
add d66_2 v4_5 v8_4;
mulj c67_2 y4_0 y4_0;
join value_22 0@uint64 4503599627370495@uint64;
and v11_4@uint128 c67_2 value_22;
join value_23 0@uint64 68719492368@uint64;
mul v12_3 v11_4 value_23;
add d68_2 v12_3 d66_2;
split c69_2 tmp_to_use_28 c67_2 52;
assume tmp_to_use_28 = v11_4 && true;
cast v13_3@int64 d68_2;
and t370_2@int64 v13_3 4503599627370495@int64;
split d71_2 tmp_to_use_29 d68_2 52;
vpc tmp_to_use_p_19@uint64 tmp_to_use_29;
assume tmp_to_use_29 = t370_2 && true;
mul a472_2 y4_0 2@uint64;
mulj v16_2 y0_0 a472_2;
mulj v17_4 y3_0 v5_4;
add v18_3 v16_2 v17_4;
mulj v19_3 y2_0 y2_0;
add v20_4 v18_3 v19_3;
join value_24 0@uint64 68719492368@uint64;
mul v21_3 c69_2 value_24;
add v105_2 v20_4 v21_3;
add d74_2 d71_2 v105_2;
cast v22_4@int64 d74_2;
split d75_2 tmp_to_use1_4 d74_2 52;
split v10_3 tmp_to_use2_4 v22_4 48;
and tx76_3@int64 v10_3 15@int64;
vpc tmp_to_use1_p_4@uint64 tmp_to_use1_4;
assume tmp_to_use1_4 = (tx76_3 * 281474976710656) + tmp_to_use2_4 && true;
and t477_2@int64 v22_4 281474976710655@int64;
assume tmp_to_use2_4 = t477_2 && true;
mulj c78_2 y0_0 y0_0;
mulj v24_4 a472_2 y1_0;
mul v25_4 y2_0 2@uint64;
mulj v27_3 y3_0 v25_4;
add v28_3 v24_4 v27_3;
add d79_2 v28_3 d75_2;
cast v29_4@int64 d79_2;
split d80_2 tmp_to_use_30 d79_2 52;
split tmp1_4 tmp2_4 v29_4 60;
shl v65_3 tmp2_4 4;
and v30_5@int64 v65_3 72057594037927920@int64;
vpc tmp_to_use_p_20@uint64 tmp_to_use_30;
assume v30_5 = tmp_to_use_30 * 16 && true;
vpc v30_6@uint64 v30_5;
vpc tx76_4@uint64 tx76_3;
add u081_2 v30_6 tx76_4;
mulj v32_3 u081_2 4294968273@uint64;
add c82_2 v32_3 c78_2;
cast v33_4@uint64 c82_2;
and v34_3@uint64 v33_4 4503599627370495@uint64;
split c85_2 tmp_to_use_31 c82_2 52;
vpc tmp_to_use_p_21@uint64 tmp_to_use_31;
assume tmp_to_use_31 = v34_3 && true;
mulj v35_4 v1_3 y1_0;
mulj v36_4 y2_0 a472_2;
mulj v37_4 y3_0 y3_0;
add v38_3 v36_4 v37_4;
add d87_2 v38_3 d80_2;
join value_25 0@uint64 4503599627370495@uint64;
and v39_2@uint128 d87_2 value_25;
join value_26 0@uint64 68719492368@uint64;
mul v40_3 v39_2 value_26;
add v103_2 v35_4 v40_3;
add c88_2 c85_2 v103_2;
split d89_2 tmp_to_use_32 d87_2 52;
assume tmp_to_use_32 = v39_2 && true;
cast v41_3@uint64 c88_2;
and v42_2@uint64 v41_3 4503599627370495@uint64;
split c91_3 tmp_to_use_33 c88_2 52;
vpc tmp_to_use_p_22@uint64 tmp_to_use_33;
assume tmp_to_use_33 = v42_2 && true;
mulj v43_3 v1_3 y2_0;
mulj v44_3 y1_0 y1_0;
add v45_3 v43_3 v44_3;
mulj v46_2 y3_0 a472_2;
add d93_2 v46_2 d89_2;
join value_27 0@uint64 4503599627370495@uint64;
and v47_3@uint128 d93_2 value_27;
join value_28 0@uint64 68719492368@uint64;
mul v48_3 v47_3 value_28;
add v104_2 v45_3 v48_3;
add c94_2 c91_3 v104_2;
split d95_3 tmp_to_use_34 d93_2 52;
assume tmp_to_use_34 = v47_3 && true;
cast v49_3@uint64 c94_2;
and v50_3@uint64 v49_3 4503599627370495@uint64;
split c97_2 tmp_to_use_35 c94_2 52;
vpc tmp_to_use_p_23@uint64 tmp_to_use_35;
assume tmp_to_use_35 = v50_3 && true;
join value_29 0@uint64 68719492368@uint64;
mul v51_3 d95_3 value_29;
vpc v52_2@uint128 t370_2;
add v53_3 v51_3 v52_2;
add c98_2 v53_3 c97_2;
cast v54_3@uint64 c98_2;
and v55_3@uint64 v54_3 4503599627370495@uint64;
split c100_2 tmp_to_use_36 c98_2 52;
vpc tmp_to_use_p_24@uint64 tmp_to_use_36;
assume tmp_to_use_36 = v55_3 && true;
vpc v56_3@uint128 t477_2;
add c101_3 v56_3 c100_2;
vpc v57_3@uint64 c101_3;
mul v39_3 v34_3 2@uint64;
mul v41_4 v42_2 2@uint64;
mul v43_4 v50_3 2@uint64;
mul v45_4 v55_3 2@uint64;
mul v47_4 v57_3 2@uint64;
mul v1_4 v39_3 2@uint64;
mulj v4_6 v1_4 v45_4;
mul v5_5 v41_4 2@uint64;
mulj v8_5 v5_5 v43_4;
add d66_3 v4_6 v8_5;
mulj c67_3 v47_4 v47_4;
join value_30 0@uint64 4503599627370495@uint64;
and v11_5@uint128 c67_3 value_30;
join value_31 0@uint64 68719492368@uint64;
mul v12_4 v11_5 value_31;
add d68_3 v12_4 d66_3;
split c69_3 tmp_to_use_37 c67_3 52;
assume tmp_to_use_37 = v11_5 && true;
cast v13_4@int64 d68_3;
and t370_3@int64 v13_4 4503599627370495@int64;
split d71_3 tmp_to_use_38 d68_3 52;
vpc tmp_to_use_p_25@uint64 tmp_to_use_38;
assume tmp_to_use_38 = t370_3 && true;
mul a472_3 v47_4 2@uint64;
mulj v16_3 v39_3 a472_3;
mulj v17_5 v45_4 v5_5;
add v18_4 v16_3 v17_5;
mulj v19_4 v43_4 v43_4;
add v20_5 v18_4 v19_4;
join value_32 0@uint64 68719492368@uint64;
mul v21_4 c69_3 value_32;
add v105_3 v20_5 v21_4;
add d74_3 d71_3 v105_3;
cast v22_5@int64 d74_3;
split d75_3 tmp_to_use1_5 d74_3 52;
split v10_4 tmp_to_use2_5 v22_5 48;
and tx76_5@int64 v10_4 15@int64;
vpc tmp_to_use1_p_5@uint64 tmp_to_use1_5;
assume tmp_to_use1_5 = (tx76_5 * 281474976710656) + tmp_to_use2_5 && true;
and t477_3@int64 v22_5 281474976710655@int64;
assume tmp_to_use2_5 = t477_3 && true;
mulj c78_3 v39_3 v39_3;
mulj v24_5 a472_3 v41_4;
mul v25_5 v43_4 2@uint64;
mulj v27_4 v45_4 v25_5;
add v28_4 v24_5 v27_4;
add d79_3 v28_4 d75_3;
cast v29_5@int64 d79_3;
split d80_3 tmp_to_use_39 d79_3 52;
split tmp1_5 tmp2_5 v29_5 60;
shl v65_4 tmp2_5 4;
and v30_7@int64 v65_4 72057594037927920@int64;
vpc tmp_to_use_p_26@uint64 tmp_to_use_39;
assume v30_7 = tmp_to_use_39 * 16 && true;
vpc v30_8@uint64 v30_7;
vpc tx76_6@uint64 tx76_5;
add u081_3 v30_8 tx76_6;
mulj v32_4 u081_3 4294968273@uint64;
add c82_3 v32_4 c78_3;
cast v33_5@uint64 c82_3;
and v34_4@uint64 v33_5 4503599627370495@uint64;
split c85_3 tmp_to_use_40 c82_3 52;
vpc tmp_to_use_p_27@uint64 tmp_to_use_40;
assume tmp_to_use_40 = v34_4 && true;
mulj v35_5 v1_4 v41_4;
mulj v36_5 v43_4 a472_3;
mulj v37_5 v45_4 v45_4;
add v38_5 v36_5 v37_5;
add d87_3 v38_5 d80_3;
join value_33 0@uint64 4503599627370495@uint64;
and v39_4@uint128 d87_3 value_33;
join value_34 0@uint64 68719492368@uint64;
mul v40_5 v39_4 value_34;
add v103_3 v35_5 v40_5;
add c88_3 c85_3 v103_3;
split d89_3 tmp_to_use_41 d87_3 52;
assume tmp_to_use_41 = v39_4 && true;
cast v41_5@uint64 c88_3;
and v42_4@uint64 v41_5 4503599627370495@uint64;
split c91_4 tmp_to_use_42 c88_3 52;
vpc tmp_to_use_p_28@uint64 tmp_to_use_42;
assume tmp_to_use_42 = v42_4 && true;
mulj v43_5 v1_4 v43_4;
mulj v44_5 v41_4 v41_4;
add v45_5 v43_5 v44_5;
mulj v46_4 v45_4 a472_3;
add d93_3 v46_4 d89_3;
join value_35 0@uint64 4503599627370495@uint64;
and v47_5@uint128 d93_3 value_35;
join value_36 0@uint64 68719492368@uint64;
mul v48_4 v47_5 value_36;
add v104_3 v45_5 v48_4;
add c94_3 c91_4 v104_3;
split d95_4 tmp_to_use_43 d93_3 52;
assume tmp_to_use_43 = v47_5 && true;
cast v49_4@uint64 c94_3;
and v50_4@uint64 v49_4 4503599627370495@uint64;
split c97_3 tmp_to_use_44 c94_3 52;
vpc tmp_to_use_p_29@uint64 tmp_to_use_44;
assume tmp_to_use_44 = v50_4 && true;
join value_37 0@uint64 68719492368@uint64;
mul v51_4 d95_4 value_37;
vpc v52_3@uint128 t370_3;
add v53_4 v51_4 v52_3;
add c98_3 v53_4 c97_3;
cast v54_4@uint64 c98_3;
and v55_4@uint64 v54_4 4503599627370495@uint64;
split c100_3 tmp_to_use_45 c98_3 52;
vpc tmp_to_use_p_30@uint64 tmp_to_use_45;
assume tmp_to_use_45 = v55_4 && true;
vpc v56_4@uint128 t477_3;
add c101_4 v56_4 c100_3;
vpc v57_4@uint64 c101_4;
mul v49_5 v34_4 2@uint64;
mul v51_5 v42_4 2@uint64;
mul v53_5 v50_4 2@uint64;
mul v55_5 v55_4 2@uint64;
mul v57_5 v57_4 2@uint64;
mulj v4_7 v39_3 x3_0;
mulj v8_6 v41_4 x2_0;
add v141_2 v4_7 v8_6;
mulj v13_5 v45_4 x0_0;
mulj v17_6 v43_4 x1_0;
add v142_2 v13_5 v141_2;
add d90_2 v17_6 v142_2;
mulj c91_5 v47_4 x4_0;
split tmp_and_11 v22_6 c91_5 52;
join value_38 0@uint64 68719492368@uint64;
mul v23_3 v22_6 value_38;
add d92_2 v23_3 d90_2;
split c93_2 tmp_to_use_46 c91_5 52;
assume tmp_to_use_46 = v22_6 && true;
cast v24_6@uint64 d92_2;
split tmp_and_12 t394_2 v24_6 52;
split d95_5 tmp_to_use_47 d92_2 52;
vpc tmp_to_use_p_31@uint64 tmp_to_use_47;
assume tmp_to_use_47 = t394_2 && true;
mulj v26_3 v39_3 x4_0;
mulj v27_5 x3_0 v41_4;
add v135_2 v26_3 v27_5;
mulj v29_6 v45_4 x1_0;
mulj v30_9 x2_0 v43_4;
add v136_2 v29_6 v135_2;
add v137_2 v30_9 v136_2;
mulj v33_6 x0_0 v47_4;
add v138_2 v33_6 v137_2;
join value_39 0@uint64 68719492368@uint64;
mul v35_6 c93_2 value_39;
add v139_2 v35_6 v138_2;
add d97_2 d95_5 v139_2;
cast v36_6@uint64 d97_2;
split d98_2 tmp_to_use1_6 d97_2 52;
split v25_6 tmp_to_use2_6 v36_6 48;
split tmp_and_13 tx99_2 v25_6 4;
vpc tmp_to_use1_p_6@uint64 tmp_to_use1_6;
assume tmp_to_use1_6 = (tx99_2 * 281474976710656) + tmp_to_use2_6 && true;
split tmp_and_14 t4100_2 v36_6 48;
assume tmp_to_use2_6 = t4100_2 && true;
mulj c101_5 v39_3 x0_0;
mulj v37_6 v41_4 x4_0;
mulj v38_6 x3_0 v43_4;
add v132_2 v37_6 v38_6;
mulj v40_6 x1_0 v47_4;
mulj v41_6 x2_0 v45_4;
add v133_2 v40_6 v132_2;
add v43_6 v41_6 v133_2;
add d102_2 v43_6 d98_2;
cast v44_6@uint64 d102_2;
split d103_2 tmp_to_use_48 d102_2 52;
split tmp1_6 tmp2_6 v44_6 60;
shl v88_2 tmp2_6 4;
and v45_6@uint64 v88_2 72057594037927920@uint64;
vpc tmp_to_use_p_32@uint64 tmp_to_use_48;
assume v45_6 = tmp_to_use_48 * 16 && true;
or u0104_2@uint64 v45_6 tx99_2;
assume u0104_2 = v45_6 + tx99_2 && true;
mulj v47_6 u0104_2 4294968273@uint64;
add c105_2 v47_6 c101_5;
cast v48_6@uint64 c105_2;
split tmp_and_15 v49_6 v48_6 52;
split c108_2 tmp_to_use_49 c105_2 52;
vpc tmp_to_use_p_33@uint64 tmp_to_use_49;
assume tmp_to_use_49 = v49_6 && true;
mulj v50_6 v39_3 x1_0;
mulj v51_6 v41_4 x0_0;
add v129_2 v50_6 v51_6;
mulj v53_6 v43_4 x4_0;
mulj v54_6 x3_0 v45_4;
add v55_6 v53_6 v54_6;
mulj v56_6 x2_0 v47_4;
add v57_6 v55_6 v56_6;
add d110_2 v57_6 d103_2;
split tmp_and_16 v58_2 d110_2 52;
join value_40 0@uint64 68719492368@uint64;
mul v59_2 v58_2 value_40;
add v130_2 v59_2 v129_2;
add c111_2 c108_2 v130_2;
split d112_2 tmp_to_use_50 d110_2 52;
assume tmp_to_use_50 = v58_2 && true;
cast v60_2@uint64 c111_2;
split tmp_and_17 v61_2 v60_2 52;
split c114_2 tmp_to_use_51 c111_2 52;
vpc tmp_to_use_p_34@uint64 tmp_to_use_51;
assume tmp_to_use_51 = v61_2 && true;
mulj v62_2 v39_3 x2_0;
mulj v63_2 v41_4 x1_0;
add v128_2 v62_2 v63_2;
mulj v65_5 x0_0 v43_4;
add v127_2 v65_5 v128_2;
mulj v67_2 v45_4 x4_0;
mulj v68_2 x3_0 v47_4;
add v69_2 v67_2 v68_2;
add d116_2 v69_2 d112_2;
split tmp_and_18 v70_2 d116_2 52;
join value_41 0@uint64 68719492368@uint64;
mul v71_2 v70_2 value_41;
add v126_2 v71_2 v127_2;
add c117_2 c114_2 v126_2;
split d118_2 tmp_to_use_52 d116_2 52;
assume tmp_to_use_52 = v70_2 && true;
cast v72_2@uint64 c117_2;
split tmp_and_19 v73_2 v72_2 52;
split c120_2 tmp_to_use_53 c117_2 52;
vpc tmp_to_use_p_35@uint64 tmp_to_use_53;
assume tmp_to_use_53 = v73_2 && true;
join value_42 0@uint64 68719492368@uint64;
mul v74_2 d118_2 value_42;
vpc v75_2@uint128 t394_2;
add v76_2 v74_2 v75_2;
add c121_2 v76_2 c120_2;
cast v77_2@uint64 c121_2;
split tmp_and_20 v78_2 v77_2 52;
split c123_2 tmp_to_use_54 c121_2 52;
vpc tmp_to_use_p_36@uint64 tmp_to_use_54;
assume tmp_to_use_54 = v78_2 && true;
vpc v79_2@uint128 t4100_2;
add c124_2 v79_2 c123_2;
vpc v80_2@uint64 c124_2;
mul v59_3 v49_6 4@uint64;
mul v61_3 v61_2 4@uint64;
mul v63_3 v73_2 4@uint64;
mul v65_6 v78_2 4@uint64;
mul v67_3 v80_2 4@uint64;
sub v68_3 45035953324022230@uint64 v59_3;
sub v69_3 45035996273704950@uint64 v61_3;
sub v70_3 45035996273704950@uint64 v63_3;
sub v71_3 45035996273704950@uint64 v65_6;
sub v72_3 2814749767106550@uint64 v67_3;
add v74_3 v68_3 v241_1;
add v76_3 v69_3 v254_1;
add v78_3 v70_3 v267_1;
add v80_3 v71_3 v274_1;
add v82_1 v72_3 v278_1;
mul v89_1 v49_6 6@uint64;
add v81_1 v89_1 18014381329608892@uint64;
mul v91_1 v61_2 6@uint64;
add v79_3 v91_1 18014398509481980@uint64;
mul v93_1 v73_2 6@uint64;
add v77_3 v93_1 18014398509481980@uint64;
mul v95_1 v78_2 6@uint64;
add v75_3 v95_1 18014398509481980@uint64;
mul v97_1 v80_2 6@uint64;
add v73_3 v97_1 1125899906842620@uint64;
sub v98_1 v81_1 v241_1;
sub v99_1 v79_3 v254_1;
sub v100_1 v77_3 v267_1;
sub v101_1 v75_3 v274_1;
sub v102_1 v73_3 v278_1;
mulj v4_8 v29_3 v101_1;
mulj v8_7 v31_1 v100_1;
add v141_3 v4_8 v8_7;
mulj v13_6 v35_3 v98_1;
mulj v17_7 v33_3 v99_1;
add v142_3 v13_6 v141_3;
add d90_3 v17_7 v142_3;
mulj c91_6 v37_3 v102_1;
split tmp_and_21 v22_7 c91_6 52;
join value_43 0@uint64 68719492368@uint64;
mul v23_4 v22_7 value_43;
add d92_3 v23_4 d90_3;
split c93_3 tmp_to_use_55 c91_6 52;
assume tmp_to_use_55 = v22_7 && true;
cast v24_7@uint64 d92_3;
split tmp_and_22 t394_3 v24_7 52;
split d95_6 tmp_to_use_56 d92_3 52;
vpc tmp_to_use_p_37@uint64 tmp_to_use_56;
assume tmp_to_use_56 = t394_3 && true;
mulj v26_4 v29_3 v102_1;
mulj v27_6 v101_1 v31_1;
add v135_3 v26_4 v27_6;
mulj v29_7 v35_3 v99_1;
mulj v30_10 v100_1 v33_3;
add v136_3 v29_7 v135_3;
add v137_3 v30_10 v136_3;
mulj v33_7 v98_1 v37_3;
add v138_3 v33_7 v137_3;
join value_44 0@uint64 68719492368@uint64;
mul v35_7 c93_3 value_44;
add v139_3 v35_7 v138_3;
add d97_3 d95_6 v139_3;
cast v36_7@uint64 d97_3;
split d98_3 tmp_to_use1_7 d97_3 52;
split v25_7 tmp_to_use2_7 v36_7 48;
split tmp_and_23 tx99_3 v25_7 4;
vpc tmp_to_use1_p_7@uint64 tmp_to_use1_7;
assume tmp_to_use1_7 = (tx99_3 * 281474976710656) + tmp_to_use2_7 && true;
split tmp_and_24 t4100_3 v36_7 48;
assume tmp_to_use2_7 = t4100_3 && true;
mulj c101_6 v29_3 v98_1;
mulj v37_7 v31_1 v102_1;
mulj v38_7 v101_1 v33_3;
add v132_3 v37_7 v38_7;
mulj v40_7 v99_1 v37_3;
mulj v41_7 v100_1 v35_3;
add v133_3 v40_7 v132_3;
add v43_7 v41_7 v133_3;
add d102_3 v43_7 d98_3;
cast v44_7@uint64 d102_3;
split d103_3 tmp_to_use_57 d102_3 52;
split tmp1_7 tmp2_7 v44_7 60;
shl v88_4 tmp2_7 4;
and v45_7@uint64 v88_4 72057594037927920@uint64;
vpc tmp_to_use_p_38@uint64 tmp_to_use_57;
assume v45_7 = tmp_to_use_57 * 16 && true;
or u0104_3@uint64 v45_7 tx99_3;
assume u0104_3 = v45_7 + tx99_3 && true;
mulj v47_7 u0104_3 4294968273@uint64;
add c105_3 v47_7 c101_6;
cast v48_7@uint64 c105_3;
split tmp_and_25 v49_7 v48_7 52;
split c108_3 tmp_to_use_58 c105_3 52;
vpc tmp_to_use_p_39@uint64 tmp_to_use_58;
assume tmp_to_use_58 = v49_7 && true;
mulj v50_7 v29_3 v99_1;
mulj v51_7 v31_1 v98_1;
add v129_3 v50_7 v51_7;
mulj v53_7 v33_3 v102_1;
mulj v54_7 v101_1 v35_3;
add v55_7 v53_7 v54_7;
mulj v56_7 v100_1 v37_3;
add v57_7 v55_7 v56_7;
add d110_3 v57_7 d103_3;
split tmp_and_26 v58_4 d110_3 52;
join value_45 0@uint64 68719492368@uint64;
mul v59_4 v58_4 value_45;
add v130_3 v59_4 v129_3;
add c111_3 c108_3 v130_3;
split d112_3 tmp_to_use_59 d110_3 52;
assume tmp_to_use_59 = v58_4 && true;
cast v60_4@uint64 c111_3;
split tmp_and_27 v61_4 v60_4 52;
split c114_3 tmp_to_use_60 c111_3 52;
vpc tmp_to_use_p_40@uint64 tmp_to_use_60;
assume tmp_to_use_60 = v61_4 && true;
mulj v62_4 v29_3 v100_1;
mulj v63_4 v31_1 v99_1;
add v128_3 v62_4 v63_4;
mulj v65_7 v98_1 v33_3;
add v127_3 v65_7 v128_3;
mulj v67_4 v35_3 v102_1;
mulj v68_4 v101_1 v37_3;
add v69_4 v67_4 v68_4;
add d116_3 v69_4 d112_3;
split tmp_and_28 v70_4 d116_3 52;
join value_46 0@uint64 68719492368@uint64;
mul v71_4 v70_4 value_46;
add v126_3 v71_4 v127_3;
add c117_3 c114_3 v126_3;
split d118_3 tmp_to_use_61 d116_3 52;
assume tmp_to_use_61 = v70_4 && true;
cast v72_4@uint64 c117_3;
split tmp_and_29 v73_4 v72_4 52;
split c120_3 tmp_to_use_62 c117_3 52;
vpc tmp_to_use_p_41@uint64 tmp_to_use_62;
assume tmp_to_use_62 = v73_4 && true;
join value_47 0@uint64 68719492368@uint64;
mul v74_4 d118_3 value_47;
vpc v75_4@uint128 t394_3;
add v76_4 v74_4 v75_4;
add c121_3 v76_4 c120_3;
cast v77_4@uint64 c121_3;
split tmp_and_30 v78_4 v77_4 52;
split c123_3 tmp_to_use_63 c121_3 52;
vpc tmp_to_use_p_42@uint64 tmp_to_use_63;
assume tmp_to_use_63 = v78_4 && true;
vpc v79_4@uint128 t4100_3;
add c124_3 v79_4 c123_3;
vpc v80_4@uint64 c124_3;
sub vect__105345166_0_1 27021571994413338@uint64 v49_5;
sub vect__105345166_1_1 27021597764222970@uint64 v51_5;
sub vect__105345167_0_1 27021597764222970@uint64 v53_5;
sub vect__105345167_1_1 27021597764222970@uint64 v55_5;
sub v113_1 1688849860263930@uint64 v57_5;
add vect__115350188_0_1 vect__105345166_0_1 v49_7;
add vect__115350188_1_1 vect__105345166_1_1 v61_4;
add vect__115350189_0_1 vect__105345167_0_1 v73_4;
add vect__115350189_1_1 vect__105345167_1_1 v78_4;
add v123_1 v113_1 v80_4;
{ v74_3 + (v76_3 * 4503599627370496) + (v78_3 * 20282409603651670423947251286016) + (v80_3 * 91343852333181432387730302044767688728495783936) + (v82_1 * 411376139330301510538742295639337626245683966408394965837152256) = (9 * (x0_0 + (x1_0 * 4503599627370496) + (x2_0 * 20282409603651670423947251286016) + (x3_0 * 91343852333181432387730302044767688728495783936) + (x4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (x0_0 + (x1_0 * 4503599627370496) + (x2_0 * 20282409603651670423947251286016) + (x3_0 * 91343852333181432387730302044767688728495783936) + (x4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (x0_0 + (x1_0 * 4503599627370496) + (x2_0 * 20282409603651670423947251286016) + (x3_0 * 91343852333181432387730302044767688728495783936) + (x4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (x0_0 + (x1_0 * 4503599627370496) + (x2_0 * 20282409603651670423947251286016) + (x3_0 * 91343852333181432387730302044767688728495783936) + (x4_0 * 411376139330301510538742295639337626245683966408394965837152256))) - (8 * (x0_0 + (x1_0 * 4503599627370496) + (x2_0 * 20282409603651670423947251286016) + (x3_0 * 91343852333181432387730302044767688728495783936) + (x4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (y0_0 + (y1_0 * 4503599627370496) + (y2_0 * 20282409603651670423947251286016) + (y3_0 * 91343852333181432387730302044767688728495783936) + (y4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (y0_0 + (y1_0 * 4503599627370496) + (y2_0 * 20282409603651670423947251286016) + (y3_0 * 91343852333181432387730302044767688728495783936) + (y4_0 * 411376139330301510538742295639337626245683966408394965837152256))) (mod 115792089237316195423570985008687907853269984665640564039457584007908834671663) /\ vect__115350188_0_1 + (vect__115350188_1_1 * 4503599627370496) + (vect__115350189_0_1 * 20282409603651670423947251286016) + (vect__115350189_1_1 * 91343852333181432387730302044767688728495783936) + (v123_1 * 411376139330301510538742295639337626245683966408394965837152256) = (36 * (x0_0 + (x1_0 * 4503599627370496) + (x2_0 * 20282409603651670423947251286016) + (x3_0 * 91343852333181432387730302044767688728495783936) + (x4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (x0_0 + (x1_0 * 4503599627370496) + (x2_0 * 20282409603651670423947251286016) + (x3_0 * 91343852333181432387730302044767688728495783936) + (x4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (x0_0 + (x1_0 * 4503599627370496) + (x2_0 * 20282409603651670423947251286016) + (x3_0 * 91343852333181432387730302044767688728495783936) + (x4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (y0_0 + (y1_0 * 4503599627370496) + (y2_0 * 20282409603651670423947251286016) + (y3_0 * 91343852333181432387730302044767688728495783936) + (y4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (y0_0 + (y1_0 * 4503599627370496) + (y2_0 * 20282409603651670423947251286016) + (y3_0 * 91343852333181432387730302044767688728495783936) + (y4_0 * 411376139330301510538742295639337626245683966408394965837152256))) - (27 * (x0_0 + (x1_0 * 4503599627370496) + (x2_0 * 20282409603651670423947251286016) + (x3_0 * 91343852333181432387730302044767688728495783936) + (x4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (x0_0 + (x1_0 * 4503599627370496) + (x2_0 * 20282409603651670423947251286016) + (x3_0 * 91343852333181432387730302044767688728495783936) + (x4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (x0_0 + (x1_0 * 4503599627370496) + (x2_0 * 20282409603651670423947251286016) + (x3_0 * 91343852333181432387730302044767688728495783936) + (x4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (x0_0 + (x1_0 * 4503599627370496) + (x2_0 * 20282409603651670423947251286016) + (x3_0 * 91343852333181432387730302044767688728495783936) + (x4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (x0_0 + (x1_0 * 4503599627370496) + (x2_0 * 20282409603651670423947251286016) + (x3_0 * 91343852333181432387730302044767688728495783936) + (x4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (x0_0 + (x1_0 * 4503599627370496) + (x2_0 * 20282409603651670423947251286016) + (x3_0 * 91343852333181432387730302044767688728495783936) + (x4_0 * 411376139330301510538742295639337626245683966408394965837152256))) - (8 * (y0_0 + (y1_0 * 4503599627370496) + (y2_0 * 20282409603651670423947251286016) + (y3_0 * 91343852333181432387730302044767688728495783936) + (y4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (y0_0 + (y1_0 * 4503599627370496) + (y2_0 * 20282409603651670423947251286016) + (y3_0 * 91343852333181432387730302044767688728495783936) + (y4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (y0_0 + (y1_0 * 4503599627370496) + (y2_0 * 20282409603651670423947251286016) + (y3_0 * 91343852333181432387730302044767688728495783936) + (y4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * (y0_0 + (y1_0 * 4503599627370496) + (y2_0 * 20282409603651670423947251286016) + (y3_0 * 91343852333181432387730302044767688728495783936) + (y4_0 * 411376139330301510538742295639337626245683966408394965837152256))) (mod 115792089237316195423570985008687907853269984665640564039457584007908834671663) && and [tmp_to_use_1 = v22_1, tmp_to_use_p_1 = t394_1, tmp_to_use1_p_1 = add (mul (tx99_1) (281474976710656@64)) (tmp_to_use2_1), tmp_to_use2_1 = t4100_1, v45_1 = mul (tmp_to_use_p_2) (16@64), u0104_1 = add (v45_1) (tx99_1), tmp_to_use_p_3 = v49_1, tmp_to_use_5 = v58_1, tmp_to_use_p_4 = v61_1, tmp_to_use_7 = v70_1, tmp_to_use_p_5 = v73_1, tmp_to_use_p_6 = v78_1, tmp_to_use_10 = v11_3, tmp_to_use_p_7 = t370_1, tmp_to_use1_p_2 = add (mul (tx76_1) (281474976710656@64)) (tmp_to_use2_2), tmp_to_use2_2 = t477_1, v30_2 = mul (tmp_to_use_p_8) (16@64), tmp_to_use_p_9 = v34_1, tmp_to_use_14 = v39_1, tmp_to_use_p_10 = v42_1, tmp_to_use_16 = v47_2, tmp_to_use_p_11 = v50_2, tmp_to_use_p_12 = v55_2, tmp_to_use_19 = v201_1, tmp_to_use_p_13 = t3206_1, tmp_to_use1_p_3 = add (mul (tx222_1) (281474976710656@64)) (tmp_to_use2_3), tmp_to_use2_3 = t4223_1, v235_1 = mul (tmp_to_use_p_14) (16@64), tmp_to_use_p_15 = v241_1, tmp_to_use_23 = v249_1, tmp_to_use_p_16 = v254_1, tmp_to_use_25 = v262_1, tmp_to_use_p_17 = v267_1, tmp_to_use_p_18 = v274_1, tmp_to_use_28 = v11_4, tmp_to_use_p_19 = t370_2, tmp_to_use1_p_4 = add (mul (tx76_3) (281474976710656@64)) (tmp_to_use2_4), tmp_to_use2_4 = t477_2, v30_5 = mul (tmp_to_use_p_20) (16@64), tmp_to_use_p_21 = v34_3, tmp_to_use_32 = v39_2, tmp_to_use_p_22 = v42_2, tmp_to_use_34 = v47_3, tmp_to_use_p_23 = v50_3, tmp_to_use_p_24 = v55_3, tmp_to_use_37 = v11_5, tmp_to_use_p_25 = t370_3, tmp_to_use1_p_5 = add (mul (tx76_5) (281474976710656@64)) (tmp_to_use2_5), tmp_to_use2_5 = t477_3, v30_7 = mul (tmp_to_use_p_26) (16@64), tmp_to_use_p_27 = v34_4, tmp_to_use_41 = v39_4, tmp_to_use_p_28 = v42_4, tmp_to_use_43 = v47_5, tmp_to_use_p_29 = v50_4, tmp_to_use_p_30 = v55_4, tmp_to_use_46 = v22_6, tmp_to_use_p_31 = t394_2, tmp_to_use1_p_6 = add (mul (tx99_2) (281474976710656@64)) (tmp_to_use2_6), tmp_to_use2_6 = t4100_2, v45_6 = mul (tmp_to_use_p_32) (16@64), u0104_2 = add (v45_6) (tx99_2), tmp_to_use_p_33 = v49_6, tmp_to_use_50 = v58_2, tmp_to_use_p_34 = v61_2, tmp_to_use_52 = v70_2, tmp_to_use_p_35 = v73_2, tmp_to_use_p_36 = v78_2, tmp_to_use_55 = v22_7, tmp_to_use_p_37 = t394_3, tmp_to_use1_p_7 = add (mul (tx99_3) (281474976710656@64)) (tmp_to_use2_7), tmp_to_use2_7 = t4100_3, v45_7 = mul (tmp_to_use_p_38) (16@64), u0104_3 = add (v45_7) (tx99_3), tmp_to_use_p_39 = v49_7, tmp_to_use_59 = v58_4, tmp_to_use_p_40 = v61_4, tmp_to_use_61 = v70_4, tmp_to_use_p_41 = v73_4, tmp_to_use_p_42 = v78_4] }