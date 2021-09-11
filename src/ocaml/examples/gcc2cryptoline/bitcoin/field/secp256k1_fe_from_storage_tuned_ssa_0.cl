proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0) =
{ true && true }
and v2_1@uint64 a0_0 4503599627370495@uint64;
split v3_1 tmp_to_use_1 a0_0 52;
assume tmp_to_use_1 = v2_1 && true;
split tmp1_1 tmp2_1 a1_0 52;
shl v5_1 tmp2_1 12;
and v6_1@uint64 v5_1 4503599627370495@uint64;
or v7_1@uint64 v3_1 v6_1;
assume v7_1 = v3_1 + v6_1 && true;
split v8_1 tmp_to_use_2 a1_0 40;
assume v6_1 = tmp_to_use_2 * 4096 && true;
split tmp1_2 tmp2_2 a2_0 40;
shl v10_1 tmp2_2 24;
and v11_1@uint64 v10_1 4503599627370495@uint64;
or v12_1@uint64 v8_1 v11_1;
assume v12_1 = v8_1 + v11_1 && true;
split v13_1 tmp_to_use_3 a2_0 28;
assume v11_1 = tmp_to_use_3 * 16777216 && true;
split tmp1_3 tmp2_3 a3_0 28;
shl v15_1 tmp2_3 36;
and v16_1@uint64 v15_1 4503599627370495@uint64;
or v17_1@uint64 v13_1 v16_1;
assume v17_1 = v13_1 + v16_1 && true;
split v18_1 tmp_to_use_4 a3_0 16;
assume v16_1 = tmp_to_use_4 * 68719476736 && true;
{ v2_1 + (v7_1 * 4503599627370496) + (v12_1 * 20282409603651670423947251286016) + (v17_1 * 91343852333181432387730302044767688728495783936) + (v18_1 * 411376139330301510538742295639337626245683966408394965837152256) = a0_0 + (a1_0 * 18446744073709551616) + (a2_0 * 340282366920938463463374607431768211456) + (a3_0 * 6277101735386680763835789423207666416102355444464034512896) && and [tmp_to_use_1 = v2_1, v7_1 = add (v3_1) (v6_1), v6_1 = mul (tmp_to_use_2) (4096@64), v12_1 = add (v8_1) (v11_1), v11_1 = mul (tmp_to_use_3) (16777216@64), v17_1 = add (v13_1) (v16_1), v16_1 = mul (tmp_to_use_4) (68719476736@64)] }