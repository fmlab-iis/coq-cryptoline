proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 a4_0, uint64 a5_0, uint64 a6_0, uint64 a7_0, uint64 a8_0) =
{ true && and [a0_0 <u 4611686018427387904@64, a1_0 <u 4611686018427387904@64, a2_0 <u 4611686018427387904@64, a3_0 <u 4611686018427387904@64, a4_0 <u 4611686018427387904@64, a5_0 <u 4611686018427387904@64, a6_0 <u 4611686018427387904@64, a7_0 <u 4611686018427387904@64, a8_0 <u 4611686018427387904@64] }
mov in104_0_1 a0_0;
mov in104_8_1 a1_0;
mov in104_16_1 a2_0;
mov in104_24_1 a3_0;
mov in104_32_1 a4_0;
mov in104_40_1 a5_0;
mov in104_48_1 a6_0;
mov in104_56_1 a7_0;
mov in104_64_1 a8_0;
mov v119_1 in104_0_1;
mov v120_1 in104_8_1;
mul v121_1 v120_1 2@uint64;
mov v122_1 in104_16_1;
mul v123_1 v122_1 2@uint64;
mov v124_1 in104_24_1;
mul v125_1 v124_1 2@uint64;
mov v126_1 in104_32_1;
mul v127_1 v126_1 2@uint64;
mov v128_1 in104_40_1;
mul v129_1 v128_1 2@uint64;
mov v130_1 in104_48_1;
mul v131_1 v130_1 2@uint64;
mov v132_1 in104_56_1;
mul v133_1 v132_1 2@uint64;
mov v134_1 in104_64_1;
mul v135_1 v134_1 2@uint64;
mul v115_1 v128_1 4@uint64;
mul v116_1 v130_1 4@uint64;
mul v117_1 v132_1 4@uint64;
mul v118_1 v134_1 4@uint64;
mulj v2_1 v119_1 v119_1;
mulj v4_1 v119_1 v121_1;
mulj v6_1 v119_1 v123_1;
mulj v8_1 v120_1 v120_1;
mulj v11_1 v119_1 v125_1;
mulj v12_1 v123_1 v120_1;
add v149_1 v11_1 v12_1;
mulj v15_1 v119_1 v127_1;
mulj v16_1 v120_1 v125_1;
add v17_1 v15_1 v16_1;
mulj v19_1 v122_1 v122_1;
add v20_1 v17_1 v19_1;
mulj v22_1 v119_1 v129_1;
mulj v23_1 v120_1 v127_1;
add v142_1 v22_1 v23_1;
mulj v25_1 v125_1 v122_1;
add v143_1 v25_1 v142_1;
mulj v28_1 v119_1 v131_1;
mulj v29_1 v120_1 v129_1;
add v30_1 v28_1 v29_1;
mulj v32_1 v124_1 v124_1;
mulj v33_1 v127_1 v122_1;
add v140_1 v30_1 v32_1;
add v35_1 v33_1 v140_1;
mulj v37_1 v119_1 v133_1;
mulj v38_1 v120_1 v131_1;
add v136_1 v37_1 v38_1;
mulj v40_1 v127_1 v124_1;
mulj v41_1 v122_1 v129_1;
add v138_1 v40_1 v136_1;
add v43_1 v41_1 v138_1;
mulj v45_1 v119_1 v135_1;
mulj v46_1 v120_1 v133_1;
add v47_1 v45_1 v46_1;
mulj v48_1 v129_1 v124_1;
mulj v49_1 v122_1 v131_1;
mulj v53_1 v126_1 v126_1;
add v165_1 v47_1 v53_1;
add v166_1 v48_1 v165_1;
add v54_1 v49_1 v166_1;
mov out105_128_1 v54_1;
mulj v56_1 v120_1 v118_1;
mulj v58_1 v122_1 v117_1;
add v59_1 v56_1 v58_1;
mulj v61_1 v126_1 v115_1;
mulj v63_1 v124_1 v116_1;
add v162_1 v2_1 v59_1;
add v163_1 v61_1 v162_1;
add v66_1 v63_1 v163_1;
mov out105_0_1 v66_1;
mulj v67_1 v122_1 v118_1;
mulj v68_1 v124_1 v117_1;
add v158_1 v4_1 v67_1;
mulj v71_1 v129_1 v128_1;
mulj v72_1 v126_1 v116_1;
add v159_1 v68_1 v158_1;
add v160_1 v71_1 v159_1;
add v75_1 v72_1 v160_1;
mov out105_16_1 v75_1;
mulj v76_1 v124_1 v118_1;
add v154_1 v6_1 v76_1;
mulj v77_1 v126_1 v117_1;
mulj v79_1 v116_1 v128_1;
add v155_1 v8_1 v154_1;
add v156_1 v77_1 v155_1;
add v81_1 v79_1 v156_1;
mov out105_32_1 v81_1;
mulj v82_1 v126_1 v118_1;
mulj v83_1 v117_1 v128_1;
mulj v86_1 v131_1 v130_1;
add v150_1 v82_1 v149_1;
add v151_1 v83_1 v150_1;
add v88_1 v86_1 v151_1;
mov out105_48_1 v88_1;
mulj v89_1 v118_1 v128_1;
mulj v90_1 v117_1 v130_1;
add v146_1 v20_1 v89_1;
add v92_1 v90_1 v146_1;
mov out105_64_1 v92_1;
mulj v93_1 v118_1 v130_1;
mulj v95_1 v133_1 v132_1;
add v144_1 v93_1 v143_1;
add v97_1 v95_1 v144_1;
mov out105_80_1 v97_1;
mulj v98_1 v118_1 v132_1;
add v99_1 v35_1 v98_1;
mov out105_96_1 v99_1;
mulj v101_1 v135_1 v134_1;
add v102_1 v43_1 v101_1;
mov out105_112_1 v102_1;
mov c0_1 out105_0_1;
mov c1_1 out105_16_1;
mov c2_1 out105_32_1;
mov c3_1 out105_48_1;
mov c4_1 out105_64_1;
mov c5_1 out105_80_1;
mov c6_1 out105_96_1;
mov c7_1 out105_112_1;
mov c8_1 out105_128_1;
{ c0_1 + (c1_1 * 288230376151711744) + (c2_1 * 83076749736557242056487941267521536) + (c3_1 * 23945242826029513411849172299223580994042798784118784) + (c4_1 * 6901746346790563787434755862277025452451108972170386555162524223799296) + (c5_1 * 1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224) + (c6_1 * 573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656) + (c7_1 * 165263992197562149737978827008192759957101170741070304821162198818601447809077836456297302609928821211897803006255839576064) + (c8_1 * 47634102635436893179040485073748265163400240214004076398607741693502376385799646303105256699577209032590132615988260237052123652332890095616) = (a0_0 + (a1_0 * 288230376151711744) + (a2_0 * 83076749736557242056487941267521536) + (a3_0 * 23945242826029513411849172299223580994042798784118784) + (a4_0 * 6901746346790563787434755862277025452451108972170386555162524223799296) + (a5_0 * 1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224) + (a6_0 * 573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656) + (a7_0 * 165263992197562149737978827008192759957101170741070304821162198818601447809077836456297302609928821211897803006255839576064) + (a8_0 * 47634102635436893179040485073748265163400240214004076398607741693502376385799646303105256699577209032590132615988260237052123652332890095616)) * (a0_0 + (a1_0 * 288230376151711744) + (a2_0 * 83076749736557242056487941267521536) + (a3_0 * 23945242826029513411849172299223580994042798784118784) + (a4_0 * 6901746346790563787434755862277025452451108972170386555162524223799296) + (a5_0 * 1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224) + (a6_0 * 573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656) + (a7_0 * 165263992197562149737978827008192759957101170741070304821162198818601447809077836456297302609928821211897803006255839576064) + (a8_0 * 47634102635436893179040485073748265163400240214004076398607741693502376385799646303105256699577209032590132615988260237052123652332890095616)) (mod 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057152 - 1) && and [c0_1 <u 361550014853497117429835520396253724672@128, c1_1 <u 361550014853497117429835520396253724672@128, c2_1 <u 361550014853497117429835520396253724672@128, c3_1 <u 361550014853497117429835520396253724672@128, c4_1 <u 361550014853497117429835520396253724672@128, c5_1 <u 361550014853497117429835520396253724672@128, c6_1 <u 361550014853497117429835520396253724672@128, c7_1 <u 361550014853497117429835520396253724672@128, c8_1 <u 361550014853497117429835520396253724672@128] }