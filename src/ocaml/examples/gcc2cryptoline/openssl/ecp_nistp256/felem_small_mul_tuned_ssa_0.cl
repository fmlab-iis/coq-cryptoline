proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint128 b0_0, uint128 b1_0, uint128 b2_0, uint128 b3_0) =
{ true && and [b0_0 <u 649037107316853453566312041152512@128, b1_0 <u 649037107316853453566312041152512@128, b2_0 <u 649037107316853453566312041152512@128, b3_0 <u 649037107316853453566312041152512@128] }
join value_1 0@uint64 18446744069414584320@uint64;
add v9_1 b3_0 value_1;
split v11_1 tmp_to_use_1 b2_0 64;
add v12_1 v9_1 v11_1;
join value_2 0@uint64 18446744073709551615@uint64;
and v13_1@uint128 b2_0 value_2;
assume v13_1 = tmp_to_use_1 && true;
join value_3 0@uint64 18446673704965373952@uint64;
add v14_1 v13_1 value_3;
join value_4 0@uint64 18446744073709551615@uint64;
add v16_1 b0_0 value_4;
join value_5 70368744177664@uint64 4294967295@uint64;
add v18_1 b1_0 value_5;
split v19_1 tmp_to_use_2 v12_1 64;
vpc a20_1@uint64 v19_1;
join value_6 0@uint64 18446744073709551615@uint64;
and v21_1@uint128 v12_1 value_6;
assume v21_1 = tmp_to_use_2 && true;
split tmp1_1 tmp2_1 v19_1 96;
shl v23_1 tmp2_1 32;
assume tmp1_1 = 0 && true;
sub v79_1 v23_1 v19_1;
add v24_1 v21_1 v79_1;
split v25_1 tmp_to_use_3 v24_1 64;
vpc a26_1@uint64 v25_1;
add b27_1 a20_1 a26_1;
join value_7 0@uint64 18446744073709551615@uint64;
and v28_1@uint128 v24_1 value_7;
assume v28_1 = tmp_to_use_3 && true;
split tmp1_2 tmp2_2 v25_1 96;
shl v30_1 tmp2_2 32;
assume tmp1_2 = 0 && true;
sub v78_1 v30_1 v25_1;
add v31_1 v28_1 v78_1;
vpc v32_1@uint128 b27_1;
add v33_1 v16_1 v32_1;
split tmp1_3 tmp2_3 v32_1 96;
shl v34_1 tmp2_3 32;
assume tmp1_3 = 0 && true;
sub v35_1 v18_1 v34_1;
split v36_1 tmp_to_use_4 v31_1 64;
cast high37_1@uint64 v36_1;
subb high_1 high38_1 0@uint64 high37_1;
cast low39_1@uint64 v31_1;
vpc tmp_to_use_p_1@uint64 tmp_to_use_4;
assume low39_1 = tmp_to_use_4 && true;
cast v40_1@int64 v31_1;
assume v40_1 = low39_1 && true;
split low_h1bit_1 low_l63bit_1 low39_1 63;
vpc mask_1@uint1 low_h1bit_1;
and low43_1@uint64 low39_1 9223372036854775807@uint64;
adds discarded_1 low44_1 low43_1 9223372041149743103@uint64;
not low45_1@uint64 low44_1;
split low_1 discarded_2 low45_1 63;
vpc low_2@uint1 low_1;
cmov v49_1 mask_1 low_2 0@uint1;
cmov mask50_1 high_1 1@uint1 v49_1;
cmov v51_1 mask50_1 18446744073709551615@uint128 0@uint128;
sub v52_1 v33_1 v51_1;
cmov v53_1 mask50_1 4294967295@uint64 0@uint64;
vpc v54_1@uint128 v53_1;
sub v55_1 v35_1 v54_1;
cmov v56_1 mask50_1 18446744069414584321@uint64 0@uint64;
vpc v57_1@uint128 v56_1;
sub v58_1 v31_1 v57_1;
split v59_1 tmp_to_use_5 v52_1 64;
add v60_1 v55_1 v59_1;
cast v61_1@uint64 v52_1;
vpc tmp_to_use_p_2@uint64 tmp_to_use_5;
assume v61_1 = tmp_to_use_p_2 && true;
split v62_1 tmp_to_use_6 v60_1 64;
add v63_1 v14_1 v62_1;
cast v64_1@uint64 v60_1;
vpc tmp_to_use_p_3@uint64 tmp_to_use_6;
assume v64_1 = tmp_to_use_p_3 && true;
split v65_1 tmp_to_use_7 v63_1 64;
add v66_1 v58_1 v65_1;
cast v67_1@uint64 v63_1;
vpc tmp_to_use_p_4@uint64 tmp_to_use_7;
assume v67_1 = tmp_to_use_p_4 && true;
vpc v68_1@uint64 v66_1;
mulj a60_1 a0_0 v61_1;
split v5_1 tmp_to_use_8 a60_1 64;
join value_8 0@uint64 18446744073709551615@uint64;
and v85_1@uint128 a60_1 value_8;
assume v85_1 = tmp_to_use_8 && true;
mulj a63_1 a0_0 v64_1;
split v8_2 tmp_to_use_9 a63_1 64;
join value_9 0@uint64 18446744073709551615@uint64;
and v86_1@uint128 a63_1 value_9;
assume v86_1 = tmp_to_use_9 && true;
add v9_2 v5_1 v86_1;
mulj a64_1 v61_1 a1_0;
split v12_2 tmp_to_use_10 a64_1 64;
join value_10 0@uint64 18446744073709551615@uint64;
and v87_1@uint128 a64_1 value_10;
assume v87_1 = tmp_to_use_10 && true;
add v13_2 v9_2 v87_1;
add v14_2 v8_2 v12_2;
mulj a66_1 a0_0 v67_1;
split v17_2 tmp_to_use_11 a66_1 64;
join value_11 0@uint64 18446744073709551615@uint64;
and v88_1@uint128 a66_1 value_11;
assume v88_1 = tmp_to_use_11 && true;
add v18_2 v14_2 v88_1;
mulj a67_1 v64_1 a1_0;
split v19_2 tmp_to_use_12 a67_1 64;
join value_12 0@uint64 18446744073709551615@uint64;
and v89_1@uint128 a67_1 value_12;
assume v89_1 = tmp_to_use_12 && true;
add v20_1 v18_2 v89_1;
add v21_2 v17_2 v19_2;
mulj a68_1 v61_1 a2_0;
split v24_2 tmp_to_use_13 a68_1 64;
join value_13 0@uint64 18446744073709551615@uint64;
and v90_1@uint128 a68_1 value_13;
assume v90_1 = tmp_to_use_13 && true;
add v25_2 v20_1 v90_1;
add v26_1 v21_2 v24_2;
mulj a70_1 a0_0 v68_1;
split v29_1 tmp_to_use_14 a70_1 64;
join value_14 0@uint64 18446744073709551615@uint64;
and v91_1@uint128 a70_1 value_14;
assume v91_1 = tmp_to_use_14 && true;
add v30_2 v26_1 v91_1;
mulj a71_1 a1_0 v67_1;
split v31_2 tmp_to_use_15 a71_1 64;
join value_15 0@uint64 18446744073709551615@uint64;
and v92_1@uint128 a71_1 value_15;
assume v92_1 = tmp_to_use_15 && true;
add v32_2 v30_2 v92_1;
add v33_2 v29_1 v31_2;
mulj a72_1 v64_1 a2_0;
split v34_2 tmp_to_use_16 a72_1 64;
join value_16 0@uint64 18446744073709551615@uint64;
and v93_1@uint128 a72_1 value_16;
assume v93_1 = tmp_to_use_16 && true;
add v35_2 v32_2 v93_1;
add v36_2 v33_2 v34_2;
mulj a73_1 v61_1 a3_0;
split v39_1 tmp_to_use_17 a73_1 64;
join value_17 0@uint64 18446744073709551615@uint64;
and v94_1@uint128 a73_1 value_17;
assume v94_1 = tmp_to_use_17 && true;
add v40_2 v35_2 v94_1;
add v41_1 v36_2 v39_1;
mulj a75_1 a1_0 v68_1;
split v42_1 tmp_to_use_18 a75_1 64;
join value_18 0@uint64 18446744073709551615@uint64;
and v95_1@uint128 a75_1 value_18;
assume v95_1 = tmp_to_use_18 && true;
add v43_1 v41_1 v95_1;
mulj a76_1 v67_1 a2_0;
split v44_1 tmp_to_use_19 a76_1 64;
join value_19 0@uint64 18446744073709551615@uint64;
and v96_1@uint128 a76_1 value_19;
assume v96_1 = tmp_to_use_19 && true;
add v45_1 v43_1 v96_1;
add v46_1 v42_1 v44_1;
mulj a77_1 v64_1 a3_0;
split v47_1 tmp_to_use_20 a77_1 64;
join value_20 0@uint64 18446744073709551615@uint64;
and v97_1@uint128 a77_1 value_20;
assume v97_1 = tmp_to_use_20 && true;
add v48_1 v45_1 v97_1;
add v49_2 v46_1 v47_1;
mulj a79_1 a2_0 v68_1;
split v50_1 tmp_to_use_21 a79_1 64;
join value_21 0@uint64 18446744073709551615@uint64;
and v98_1@uint128 a79_1 value_21;
assume v98_1 = tmp_to_use_21 && true;
add v51_2 v49_2 v98_1;
mulj a80_1 v67_1 a3_0;
split v52_2 tmp_to_use_22 a80_1 64;
join value_22 0@uint64 18446744073709551615@uint64;
and v99_1@uint128 a80_1 value_22;
assume v99_1 = tmp_to_use_22 && true;
add v53_2 v51_2 v99_1;
add v54_2 v50_1 v52_2;
mulj a82_1 v68_1 a3_0;
split v55_2 tmp_to_use_23 a82_1 64;
join value_23 0@uint64 18446744073709551615@uint64;
and v100_1@uint128 a82_1 value_23;
assume v100_1 = tmp_to_use_23 && true;
add v56_2 v54_2 v100_1;
{ v85_1 + (v13_2 * 18446744073709551616) + (v25_2 * 340282366920938463463374607431768211456) + (v40_2 * 6277101735386680763835789423207666416102355444464034512896) + (v48_1 * 115792089237316195423570985008687907853269984665640564039457584007913129639936) + (v53_2 * 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576) + (v56_2 * 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816) + (v55_2 * 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656) = (a0_0 + (a1_0 * 18446744073709551616) + (a2_0 * 340282366920938463463374607431768211456) + (a3_0 * 6277101735386680763835789423207666416102355444464034512896)) * (b0_0 + (b1_0 * 18446744073709551616) + (b2_0 * 340282366920938463463374607431768211456) + (b3_0 * 6277101735386680763835789423207666416102355444464034512896)) (mod 18446744073709551615 + (4294967295 * 18446744073709551616) + (0 * 340282366920938463463374607431768211456) + (18446744069414584321 * 6277101735386680763835789423207666416102355444464034512896)) && and [v13_1 = tmp_to_use_1, v21_1 = tmp_to_use_2, tmp1_1 = 0@128, v28_1 = tmp_to_use_3, tmp1_2 = 0@128, tmp1_3 = 0@128, low39_1 = tmp_to_use_p_1, v40_1 = low39_1, v61_1 = tmp_to_use_p_2, v64_1 = tmp_to_use_p_3, v67_1 = tmp_to_use_p_4, v85_1 = tmp_to_use_8, v86_1 = tmp_to_use_9, v87_1 = tmp_to_use_10, v88_1 = tmp_to_use_11, v89_1 = tmp_to_use_12, v90_1 = tmp_to_use_13, v91_1 = tmp_to_use_14, v92_1 = tmp_to_use_15, v93_1 = tmp_to_use_16, v94_1 = tmp_to_use_17, v95_1 = tmp_to_use_18, v96_1 = tmp_to_use_19, v97_1 = tmp_to_use_20, v98_1 = tmp_to_use_21, v99_1 = tmp_to_use_22, v100_1 = tmp_to_use_23, v85_1 <u 129127208515966861312@128, v13_2 <u 129127208515966861312@128, v25_2 <u 129127208515966861312@128, v40_2 <u 129127208515966861312@128, v48_1 <u 129127208515966861312@128, v53_2 <u 129127208515966861312@128, v56_2 <u 129127208515966861312@128, v55_2 <u 129127208515966861312@128] }