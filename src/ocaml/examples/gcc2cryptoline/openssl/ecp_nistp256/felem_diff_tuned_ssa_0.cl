proc main(uint128 a0_0, uint128 a1_0, uint128 a2_0, uint128 a3_0, uint128 b0_0, uint128 b1_0, uint128 b2_0, uint128 b3_0) =
{ true && and [a0_0 <u 81129638414606681695789005144064@128, a1_0 <u 81129638414606681695789005144064@128, a2_0 <u 81129638414606681695789005144064@128, a3_0 <u 81129638414606681695789005144064@128, b0_0 <u 20282409603651670423947251286016@128, b1_0 <u 20282409603651670423947251286016@128, b2_0 <u 20282409603651670423947251286016@128, b3_0 <u 20282409603651670423947251286016@128] }
join value_1 2199023255551@uint64 18446741874686295552@uint64;
add v2_1 a0_0 value_1;
join value_2 2199023255552@uint64 0@uint64;
add v4_1 a1_0 value_2;
join value_3 2199023255551@uint64 18446741874686296576@uint64;
add v6_1 a2_0 value_3;
join value_4 2199023255551@uint64 18446741874686296576@uint64;
add v8_1 a3_0 value_4;
sub v10_1 v2_1 b0_0;
sub v12_1 v4_1 b1_0;
sub v14_1 v6_1 b2_0;
sub v16_1 v8_1 b3_0;
{ v10_1 + (v12_1 * 18446744073709551616) + (v14_1 * 340282366920938463463374607431768211456) + (v16_1 * 6277101735386680763835789423207666416102355444464034512896) = a0_0 + (a1_0 * 18446744073709551616) + (a2_0 * 340282366920938463463374607431768211456) + (a3_0 * 6277101735386680763835789423207666416102355444464034512896) - (b0_0 + (b1_0 * 18446744073709551616) + (b2_0 * 340282366920938463463374607431768211456) + (b3_0 * 6277101735386680763835789423207666416102355444464034512896)) (mod 18446744073709551615 + (4294967295 * 18446744073709551616) + (0 * 340282366920938463463374607431768211456) + (18446744069414584321 * 6277101735386680763835789423207666416102355444464034512896)) && and [v10_1 <u add (a0_0) (40564819207303340847894502572032@128), v12_1 <=u add (a1_0) (40564819207303340847894502572032@128), v14_1 <u add (a2_0) (40564819207303340847894502572032@128), v16_1 <u add (a3_0) (40564819207303340847894502572032@128)] }