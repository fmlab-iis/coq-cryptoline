(*_build/default/coqcryptoline.exe -v -jobs 16 -sat_solver cadical -sat_cert grat -no_carry_constraint ~/tmp/coqcv_ntt_k16_separated.cl
Parsing Cryptoline file:                [OK]            0.240599 seconds
Results of checking CNF formulas:       [OK]            1292.318625 seconds
Finding polynomial coefficients
         Polynomials #11:               [DONE]          1586.426705 seconds
         Polynomials #7:                [DONE]          1591.044071 seconds
         Polynomials #5:                [DONE]          1595.964934 seconds
         Polynomials #3:                [DONE]          1596.383645 seconds
         Polynomials #13:               [DONE]          1598.465000 seconds
         Polynomials #10:               [DONE]          1601.683990 seconds
         Polynomials #12:               [DONE]          1602.273058 seconds
         Polynomials #14:               [DONE]          1610.799013 seconds
         Polynomials #6:                [DONE]          1618.181877 seconds
         Polynomials #4:                [DONE]          1625.043556 seconds
         Polynomials #2:                [DONE]          1648.867335 seconds
         Polynomials #0:                [DONE]          1649.077228 seconds
         Polynomials #8:                [DONE]          1666.082532 seconds
         Polynomials #15:               [DONE]          1667.048740 seconds
         Polynomials #1:                [DONE]          1690.947333 seconds
         Polynomials #9:                [DONE]          1734.294340 seconds
         Polynomials #21:               [DONE]          1649.168459 seconds
         Polynomials #16:               [DONE]          1671.266749 seconds
         Polynomials #20:               [DONE]          1669.862215 seconds
         Polynomials #19:               [DONE]          1684.484024 seconds
         Polynomials #24:               [DONE]          1675.491859 seconds
         Polynomials #26:               [DONE]          1653.165021 seconds
         Polynomials #17:               [DONE]          1713.028209 seconds
         Polynomials #22:               [DONE]          1706.704255 seconds
         Polynomials #23:               [DONE]          1709.990693 seconds
         Polynomials #25:               [DONE]          1716.602210 seconds
         Polynomials #27:               [DONE]          1705.768250 seconds
         Polynomials #29:               [DONE]          1702.228582 seconds
         Polynomials #30:               [DONE]          1685.636738 seconds
         Polynomials #28:               [DONE]          1727.392907 seconds
         Polynomials #31:               [DONE]          1663.177358 seconds
         Polynomials #18:               [DONE]          1814.064288 seconds
Finished finding polynomial coefficients                3410.784611 seconds
Verification result:                    [OK]            5253.535081 seconds

*)

proc PQCLEAN_KYBER512_CLEAN_montgomery_reduce (sint32 v_a, sint16 ret) =
{ true
  && and [ (-3329)@32 * (2**15)@32 <=s v_a, v_a <s 3329@32 * (2**15)@32 ]
}

assume eqmod (ret * (2**16)) v_a 3329
    && and [ (-3329)@16 <s ret, ret <s 3329@16 ];

{ true && true }


proc main (  
	     sint16 mem0_0,   sint16 mem0_2,   sint16 mem0_4,   sint16 mem0_6,
             sint16 mem0_8,  sint16 mem0_10,  sint16 mem0_12,  sint16 mem0_14,
            sint16 mem0_16,  sint16 mem0_18,  sint16 mem0_20,  sint16 mem0_22,
            sint16 mem0_24,  sint16 mem0_26,  sint16 mem0_28,  sint16 mem0_30,
            sint16 mem0_32,  sint16 mem0_34,  sint16 mem0_36,  sint16 mem0_38,
            sint16 mem0_40,  sint16 mem0_42,  sint16 mem0_44,  sint16 mem0_46,
            sint16 mem0_48,  sint16 mem0_50,  sint16 mem0_52,  sint16 mem0_54,
            sint16 mem0_56,  sint16 mem0_58,  sint16 mem0_60,  sint16 mem0_62,
            sint16 mem0_64,  sint16 mem0_66,  sint16 mem0_68,  sint16 mem0_70,
            sint16 mem0_72,  sint16 mem0_74,  sint16 mem0_76,  sint16 mem0_78,
            sint16 mem0_80,  sint16 mem0_82,  sint16 mem0_84,  sint16 mem0_86,
            sint16 mem0_88,  sint16 mem0_90,  sint16 mem0_92,  sint16 mem0_94,
            sint16 mem0_96,  sint16 mem0_98, sint16 mem0_100, sint16 mem0_102,
           sint16 mem0_104, sint16 mem0_106, sint16 mem0_108, sint16 mem0_110,
           sint16 mem0_112, sint16 mem0_114, sint16 mem0_116, sint16 mem0_118,
           sint16 mem0_120, sint16 mem0_122, sint16 mem0_124, sint16 mem0_126,
           sint16 mem0_128, sint16 mem0_130, sint16 mem0_132, sint16 mem0_134,
           sint16 mem0_136, sint16 mem0_138, sint16 mem0_140, sint16 mem0_142,
           sint16 mem0_144, sint16 mem0_146, sint16 mem0_148, sint16 mem0_150,
           sint16 mem0_152, sint16 mem0_154, sint16 mem0_156, sint16 mem0_158,
           sint16 mem0_160, sint16 mem0_162, sint16 mem0_164, sint16 mem0_166,
           sint16 mem0_168, sint16 mem0_170, sint16 mem0_172, sint16 mem0_174,
           sint16 mem0_176, sint16 mem0_178, sint16 mem0_180, sint16 mem0_182,
           sint16 mem0_184, sint16 mem0_186, sint16 mem0_188, sint16 mem0_190,
           sint16 mem0_192, sint16 mem0_194, sint16 mem0_196, sint16 mem0_198,
           sint16 mem0_200, sint16 mem0_202, sint16 mem0_204, sint16 mem0_206,
           sint16 mem0_208, sint16 mem0_210, sint16 mem0_212, sint16 mem0_214,
           sint16 mem0_216, sint16 mem0_218, sint16 mem0_220, sint16 mem0_222,
           sint16 mem0_224, sint16 mem0_226, sint16 mem0_228, sint16 mem0_230,
           sint16 mem0_232, sint16 mem0_234, sint16 mem0_236, sint16 mem0_238,
           sint16 mem0_240, sint16 mem0_242, sint16 mem0_244, sint16 mem0_246,
           sint16 mem0_248, sint16 mem0_250, sint16 mem0_252, sint16 mem0_254,
           sint16 mem0_256, sint16 mem0_258, sint16 mem0_260, sint16 mem0_262,
           sint16 mem0_264, sint16 mem0_266, sint16 mem0_268, sint16 mem0_270,
           sint16 mem0_272, sint16 mem0_274, sint16 mem0_276, sint16 mem0_278,
           sint16 mem0_280, sint16 mem0_282, sint16 mem0_284, sint16 mem0_286,
           sint16 mem0_288, sint16 mem0_290, sint16 mem0_292, sint16 mem0_294,
           sint16 mem0_296, sint16 mem0_298, sint16 mem0_300, sint16 mem0_302,
           sint16 mem0_304, sint16 mem0_306, sint16 mem0_308, sint16 mem0_310,
           sint16 mem0_312, sint16 mem0_314, sint16 mem0_316, sint16 mem0_318,
           sint16 mem0_320, sint16 mem0_322, sint16 mem0_324, sint16 mem0_326,
           sint16 mem0_328, sint16 mem0_330, sint16 mem0_332, sint16 mem0_334,
           sint16 mem0_336, sint16 mem0_338, sint16 mem0_340, sint16 mem0_342,
           sint16 mem0_344, sint16 mem0_346, sint16 mem0_348, sint16 mem0_350,
           sint16 mem0_352, sint16 mem0_354, sint16 mem0_356, sint16 mem0_358,
           sint16 mem0_360, sint16 mem0_362, sint16 mem0_364, sint16 mem0_366,
           sint16 mem0_368, sint16 mem0_370, sint16 mem0_372, sint16 mem0_374,
           sint16 mem0_376, sint16 mem0_378, sint16 mem0_380, sint16 mem0_382,
           sint16 mem0_384, sint16 mem0_386, sint16 mem0_388, sint16 mem0_390,
           sint16 mem0_392, sint16 mem0_394, sint16 mem0_396, sint16 mem0_398,
           sint16 mem0_400, sint16 mem0_402, sint16 mem0_404, sint16 mem0_406,
           sint16 mem0_408, sint16 mem0_410, sint16 mem0_412, sint16 mem0_414,
           sint16 mem0_416, sint16 mem0_418, sint16 mem0_420, sint16 mem0_422,
           sint16 mem0_424, sint16 mem0_426, sint16 mem0_428, sint16 mem0_430,
           sint16 mem0_432, sint16 mem0_434, sint16 mem0_436, sint16 mem0_438,
           sint16 mem0_440, sint16 mem0_442, sint16 mem0_444, sint16 mem0_446,
           sint16 mem0_448, sint16 mem0_450, sint16 mem0_452, sint16 mem0_454,
           sint16 mem0_456, sint16 mem0_458, sint16 mem0_460, sint16 mem0_462,
           sint16 mem0_464, sint16 mem0_466, sint16 mem0_468, sint16 mem0_470,
           sint16 mem0_472, sint16 mem0_474, sint16 mem0_476, sint16 mem0_478,
           sint16 mem0_480, sint16 mem0_482, sint16 mem0_484, sint16 mem0_486,
           sint16 mem0_488, sint16 mem0_490, sint16 mem0_492, sint16 mem0_494,
           sint16 mem0_496, sint16 mem0_498, sint16 mem0_500, sint16 mem0_502,
           sint16 mem0_504, sint16 mem0_506, sint16 mem0_508, sint16 mem0_510, bit x) =

{true
&& and [
   (-6)@16 * 3329@16 <s mem0_0, mem0_0 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_2, mem0_2 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_4, mem0_4 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_6, mem0_6 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_8, mem0_8 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_10, mem0_10 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_12, mem0_12 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_14, mem0_14 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_16, mem0_16 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_18, mem0_18 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_20, mem0_20 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_22, mem0_22 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_24, mem0_24 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_26, mem0_26 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_28, mem0_28 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_30, mem0_30 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_32, mem0_32 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_34, mem0_34 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_36, mem0_36 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_38, mem0_38 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_40, mem0_40 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_42, mem0_42 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_44, mem0_44 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_46, mem0_46 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_48, mem0_48 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_50, mem0_50 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_52, mem0_52 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_54, mem0_54 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_56, mem0_56 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_58, mem0_58 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_60, mem0_60 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_62, mem0_62 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_64, mem0_64 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_66, mem0_66 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_68, mem0_68 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_70, mem0_70 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_72, mem0_72 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_74, mem0_74 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_76, mem0_76 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_78, mem0_78 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_80, mem0_80 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_82, mem0_82 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_84, mem0_84 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_86, mem0_86 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_88, mem0_88 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_90, mem0_90 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_92, mem0_92 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_94, mem0_94 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_96, mem0_96 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_98, mem0_98 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_100, mem0_100 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_102, mem0_102 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_104, mem0_104 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_106, mem0_106 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_108, mem0_108 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_110, mem0_110 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_112, mem0_112 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_114, mem0_114 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_116, mem0_116 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_118, mem0_118 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_120, mem0_120 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_122, mem0_122 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_124, mem0_124 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_126, mem0_126 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_128, mem0_128 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_130, mem0_130 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_132, mem0_132 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_134, mem0_134 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_136, mem0_136 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_138, mem0_138 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_140, mem0_140 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_142, mem0_142 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_144, mem0_144 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_146, mem0_146 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_148, mem0_148 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_150, mem0_150 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_152, mem0_152 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_154, mem0_154 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_156, mem0_156 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_158, mem0_158 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_160, mem0_160 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_162, mem0_162 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_164, mem0_164 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_166, mem0_166 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_168, mem0_168 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_170, mem0_170 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_172, mem0_172 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_174, mem0_174 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_176, mem0_176 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_178, mem0_178 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_180, mem0_180 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_182, mem0_182 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_184, mem0_184 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_186, mem0_186 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_188, mem0_188 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_190, mem0_190 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_192, mem0_192 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_194, mem0_194 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_196, mem0_196 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_198, mem0_198 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_200, mem0_200 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_202, mem0_202 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_204, mem0_204 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_206, mem0_206 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_208, mem0_208 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_210, mem0_210 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_212, mem0_212 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_214, mem0_214 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_216, mem0_216 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_218, mem0_218 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_220, mem0_220 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_222, mem0_222 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_224, mem0_224 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_226, mem0_226 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_228, mem0_228 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_230, mem0_230 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_232, mem0_232 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_234, mem0_234 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_236, mem0_236 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_238, mem0_238 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_240, mem0_240 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_242, mem0_242 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_244, mem0_244 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_246, mem0_246 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_248, mem0_248 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_250, mem0_250 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_252, mem0_252 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_254, mem0_254 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_256, mem0_256 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_258, mem0_258 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_260, mem0_260 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_262, mem0_262 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_264, mem0_264 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_266, mem0_266 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_268, mem0_268 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_270, mem0_270 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_272, mem0_272 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_274, mem0_274 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_276, mem0_276 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_278, mem0_278 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_280, mem0_280 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_282, mem0_282 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_284, mem0_284 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_286, mem0_286 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_288, mem0_288 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_290, mem0_290 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_292, mem0_292 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_294, mem0_294 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_296, mem0_296 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_298, mem0_298 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_300, mem0_300 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_302, mem0_302 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_304, mem0_304 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_306, mem0_306 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_308, mem0_308 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_310, mem0_310 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_312, mem0_312 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_314, mem0_314 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_316, mem0_316 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_318, mem0_318 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_320, mem0_320 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_322, mem0_322 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_324, mem0_324 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_326, mem0_326 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_328, mem0_328 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_330, mem0_330 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_332, mem0_332 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_334, mem0_334 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_336, mem0_336 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_338, mem0_338 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_340, mem0_340 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_342, mem0_342 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_344, mem0_344 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_346, mem0_346 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_348, mem0_348 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_350, mem0_350 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_352, mem0_352 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_354, mem0_354 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_356, mem0_356 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_358, mem0_358 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_360, mem0_360 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_362, mem0_362 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_364, mem0_364 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_366, mem0_366 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_368, mem0_368 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_370, mem0_370 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_372, mem0_372 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_374, mem0_374 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_376, mem0_376 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_378, mem0_378 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_380, mem0_380 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_382, mem0_382 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_384, mem0_384 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_386, mem0_386 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_388, mem0_388 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_390, mem0_390 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_392, mem0_392 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_394, mem0_394 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_396, mem0_396 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_398, mem0_398 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_400, mem0_400 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_402, mem0_402 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_404, mem0_404 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_406, mem0_406 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_408, mem0_408 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_410, mem0_410 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_412, mem0_412 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_414, mem0_414 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_416, mem0_416 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_418, mem0_418 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_420, mem0_420 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_422, mem0_422 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_424, mem0_424 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_426, mem0_426 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_428, mem0_428 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_430, mem0_430 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_432, mem0_432 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_434, mem0_434 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_436, mem0_436 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_438, mem0_438 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_440, mem0_440 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_442, mem0_442 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_444, mem0_444 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_446, mem0_446 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_448, mem0_448 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_450, mem0_450 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_452, mem0_452 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_454, mem0_454 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_456, mem0_456 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_458, mem0_458 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_460, mem0_460 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_462, mem0_462 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_464, mem0_464 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_466, mem0_466 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_468, mem0_468 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_470, mem0_470 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_472, mem0_472 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_474, mem0_474 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_476, mem0_476 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_478, mem0_478 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_480, mem0_480 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_482, mem0_482 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_484, mem0_484 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_486, mem0_486 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_488, mem0_488 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_490, mem0_490 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_492, mem0_492 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_494, mem0_494 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_496, mem0_496 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_498, mem0_498 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_500, mem0_500 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_502, mem0_502 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_504, mem0_504 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_506, mem0_506 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_508, mem0_508 <s 6@16 * 3329@16,
   (-6)@16 * 3329@16 <s mem0_510, mem0_510 <s 6@16 * 3329@16
]
}


nondet v_call_i@sint16;
nondet v_call_i_1289@sint16;
nondet v_call_i_2296@sint16;
nondet v_call_i_3303@sint16;
nondet v_call_i_4310@sint16;
nondet v_call_i_5317@sint16;
nondet v_call_i_6324@sint16;
nondet v_call_i_7@sint16;
nondet v_call_i_8@sint16;
nondet v_call_i_9@sint16;
nondet v_call_i_10@sint16;
nondet v_call_i_11@sint16;
nondet v_call_i_12@sint16;
nondet v_call_i_13@sint16;
nondet v_call_i_14@sint16;
nondet v_call_i_15@sint16;
nondet v_call_i_16@sint16;
nondet v_call_i_17@sint16;
nondet v_call_i_18@sint16;
nondet v_call_i_19@sint16;
nondet v_call_i_20@sint16;
nondet v_call_i_21@sint16;
nondet v_call_i_22@sint16;
nondet v_call_i_23@sint16;
nondet v_call_i_24@sint16;
nondet v_call_i_25@sint16;
nondet v_call_i_26@sint16;
nondet v_call_i_27@sint16;
nondet v_call_i_28@sint16;
nondet v_call_i_29@sint16;
nondet v_call_i_30@sint16;
nondet v_call_i_31@sint16;
nondet v_call_i_32@sint16;
nondet v_call_i_33@sint16;
nondet v_call_i_34@sint16;
nondet v_call_i_35@sint16;
nondet v_call_i_36@sint16;
nondet v_call_i_37@sint16;
nondet v_call_i_38@sint16;
nondet v_call_i_39@sint16;
nondet v_call_i_40@sint16;
nondet v_call_i_41@sint16;
nondet v_call_i_42@sint16;
nondet v_call_i_43@sint16;
nondet v_call_i_44@sint16;
nondet v_call_i_45@sint16;
nondet v_call_i_46@sint16;
nondet v_call_i_47@sint16;
nondet v_call_i_48@sint16;
nondet v_call_i_49@sint16;
nondet v_call_i_50@sint16;
nondet v_call_i_51@sint16;
nondet v_call_i_52@sint16;
nondet v_call_i_53@sint16;
nondet v_call_i_54@sint16;
nondet v_call_i_55@sint16;
nondet v_call_i_56@sint16;
nondet v_call_i_57@sint16;
nondet v_call_i_58@sint16;
nondet v_call_i_59@sint16;
nondet v_call_i_60@sint16;
nondet v_call_i_61@sint16;
nondet v_call_i_62@sint16;
nondet v_call_i_63@sint16;
nondet v_call_i_64@sint16;
nondet v_call_i_65@sint16;
nondet v_call_i_66@sint16;
nondet v_call_i_67@sint16;
nondet v_call_i_68@sint16;
nondet v_call_i_69@sint16;
nondet v_call_i_70@sint16;
nondet v_call_i_71@sint16;
nondet v_call_i_72@sint16;
nondet v_call_i_73@sint16;
nondet v_call_i_74@sint16;
nondet v_call_i_75@sint16;
nondet v_call_i_76@sint16;
nondet v_call_i_77@sint16;
nondet v_call_i_78@sint16;
nondet v_call_i_79@sint16;
nondet v_call_i_80@sint16;
nondet v_call_i_81@sint16;
nondet v_call_i_82@sint16;
nondet v_call_i_83@sint16;
nondet v_call_i_84@sint16;
nondet v_call_i_85@sint16;
nondet v_call_i_86@sint16;
nondet v_call_i_87@sint16;
nondet v_call_i_88@sint16;
nondet v_call_i_89@sint16;
nondet v_call_i_90@sint16;
nondet v_call_i_91@sint16;
nondet v_call_i_92@sint16;
nondet v_call_i_93@sint16;
nondet v_call_i_94@sint16;
nondet v_call_i_95@sint16;
nondet v_call_i_96@sint16;
nondet v_call_i_97@sint16;
nondet v_call_i_98@sint16;
nondet v_call_i_99@sint16;
nondet v_call_i_100@sint16;
nondet v_call_i_101@sint16;
nondet v_call_i_102@sint16;
nondet v_call_i_103@sint16;
nondet v_call_i_104@sint16;
nondet v_call_i_105@sint16;
nondet v_call_i_106@sint16;
nondet v_call_i_107@sint16;
nondet v_call_i_108@sint16;
nondet v_call_i_109@sint16;
nondet v_call_i_110@sint16;
nondet v_call_i_111@sint16;
nondet v_call_i_112@sint16;
nondet v_call_i_113@sint16;
nondet v_call_i_114@sint16;
nondet v_call_i_115@sint16;
nondet v_call_i_116@sint16;
nondet v_call_i_117@sint16;
nondet v_call_i_118@sint16;
nondet v_call_i_119@sint16;
nondet v_call_i_120@sint16;
nondet v_call_i_121@sint16;
nondet v_call_i_122@sint16;
nondet v_call_i_123@sint16;
nondet v_call_i_124@sint16;
nondet v_call_i_125@sint16;
nondet v_call_i_126@sint16;
nondet v_call_i_127@sint16;
nondet v_call_i_1@sint16;
nondet v_call_i_1_1@sint16;
nondet v_call_i_1_2@sint16;
nondet v_call_i_1_3@sint16;
nondet v_call_i_1_4@sint16;
nondet v_call_i_1_5@sint16;
nondet v_call_i_1_6@sint16;
nondet v_call_i_1_7@sint16;
nondet v_call_i_1_8@sint16;
nondet v_call_i_1_9@sint16;
nondet v_call_i_1_10@sint16;
nondet v_call_i_1_11@sint16;
nondet v_call_i_1_12@sint16;
nondet v_call_i_1_13@sint16;
nondet v_call_i_1_14@sint16;
nondet v_call_i_1_15@sint16;
nondet v_call_i_1_16@sint16;
nondet v_call_i_1_17@sint16;
nondet v_call_i_1_18@sint16;
nondet v_call_i_1_19@sint16;
nondet v_call_i_1_20@sint16;
nondet v_call_i_1_21@sint16;
nondet v_call_i_1_22@sint16;
nondet v_call_i_1_23@sint16;
nondet v_call_i_1_24@sint16;
nondet v_call_i_1_25@sint16;
nondet v_call_i_1_26@sint16;
nondet v_call_i_1_27@sint16;
nondet v_call_i_1_28@sint16;
nondet v_call_i_1_29@sint16;
nondet v_call_i_1_30@sint16;
nondet v_call_i_1_31@sint16;
nondet v_call_i_1_32@sint16;
nondet v_call_i_1_33@sint16;
nondet v_call_i_1_34@sint16;
nondet v_call_i_1_35@sint16;
nondet v_call_i_1_36@sint16;
nondet v_call_i_1_37@sint16;
nondet v_call_i_1_38@sint16;
nondet v_call_i_1_39@sint16;
nondet v_call_i_1_40@sint16;
nondet v_call_i_1_41@sint16;
nondet v_call_i_1_42@sint16;
nondet v_call_i_1_43@sint16;
nondet v_call_i_1_44@sint16;
nondet v_call_i_1_45@sint16;
nondet v_call_i_1_46@sint16;
nondet v_call_i_1_47@sint16;
nondet v_call_i_1_48@sint16;
nondet v_call_i_1_49@sint16;
nondet v_call_i_1_50@sint16;
nondet v_call_i_1_51@sint16;
nondet v_call_i_1_52@sint16;
nondet v_call_i_1_53@sint16;
nondet v_call_i_1_54@sint16;
nondet v_call_i_1_55@sint16;
nondet v_call_i_1_56@sint16;
nondet v_call_i_1_57@sint16;
nondet v_call_i_1_58@sint16;
nondet v_call_i_1_59@sint16;
nondet v_call_i_1_60@sint16;
nondet v_call_i_1_61@sint16;
nondet v_call_i_1_62@sint16;
nondet v_call_i_1_63@sint16;
nondet v_call_i_1_1281@sint16;
nondet v_call_i_1_1_1@sint16;
nondet v_call_i_1_2_1@sint16;
nondet v_call_i_1_3_1@sint16;
nondet v_call_i_1_4_1@sint16;
nondet v_call_i_1_5_1@sint16;
nondet v_call_i_1_6_1@sint16;
nondet v_call_i_1_7_1@sint16;
nondet v_call_i_1_8_1@sint16;
nondet v_call_i_1_9_1@sint16;
nondet v_call_i_1_10_1@sint16;
nondet v_call_i_1_11_1@sint16;
nondet v_call_i_1_12_1@sint16;
nondet v_call_i_1_13_1@sint16;
nondet v_call_i_1_14_1@sint16;
nondet v_call_i_1_15_1@sint16;
nondet v_call_i_1_16_1@sint16;
nondet v_call_i_1_17_1@sint16;
nondet v_call_i_1_18_1@sint16;
nondet v_call_i_1_19_1@sint16;
nondet v_call_i_1_20_1@sint16;
nondet v_call_i_1_21_1@sint16;
nondet v_call_i_1_22_1@sint16;
nondet v_call_i_1_23_1@sint16;
nondet v_call_i_1_24_1@sint16;
nondet v_call_i_1_25_1@sint16;
nondet v_call_i_1_26_1@sint16;
nondet v_call_i_1_27_1@sint16;
nondet v_call_i_1_28_1@sint16;
nondet v_call_i_1_29_1@sint16;
nondet v_call_i_1_30_1@sint16;
nondet v_call_i_1_31_1@sint16;
nondet v_call_i_1_32_1@sint16;
nondet v_call_i_1_33_1@sint16;
nondet v_call_i_1_34_1@sint16;
nondet v_call_i_1_35_1@sint16;
nondet v_call_i_1_36_1@sint16;
nondet v_call_i_1_37_1@sint16;
nondet v_call_i_1_38_1@sint16;
nondet v_call_i_1_39_1@sint16;
nondet v_call_i_1_40_1@sint16;
nondet v_call_i_1_41_1@sint16;
nondet v_call_i_1_42_1@sint16;
nondet v_call_i_1_43_1@sint16;
nondet v_call_i_1_44_1@sint16;
nondet v_call_i_1_45_1@sint16;
nondet v_call_i_1_46_1@sint16;
nondet v_call_i_1_47_1@sint16;
nondet v_call_i_1_48_1@sint16;
nondet v_call_i_1_49_1@sint16;
nondet v_call_i_1_50_1@sint16;
nondet v_call_i_1_51_1@sint16;
nondet v_call_i_1_52_1@sint16;
nondet v_call_i_1_53_1@sint16;
nondet v_call_i_1_54_1@sint16;
nondet v_call_i_1_55_1@sint16;
nondet v_call_i_1_56_1@sint16;
nondet v_call_i_1_57_1@sint16;
nondet v_call_i_1_58_1@sint16;
nondet v_call_i_1_59_1@sint16;
nondet v_call_i_1_60_1@sint16;
nondet v_call_i_1_61_1@sint16;
nondet v_call_i_1_62_1@sint16;
nondet v_call_i_1_63_1@sint16;
nondet v_call_i_2@sint16;
nondet v_call_i_2_1@sint16;
nondet v_call_i_2_2@sint16;
nondet v_call_i_2_3@sint16;
nondet v_call_i_2_4@sint16;
nondet v_call_i_2_5@sint16;
nondet v_call_i_2_6@sint16;
nondet v_call_i_2_7@sint16;
nondet v_call_i_2_8@sint16;
nondet v_call_i_2_9@sint16;
nondet v_call_i_2_10@sint16;
nondet v_call_i_2_11@sint16;
nondet v_call_i_2_12@sint16;
nondet v_call_i_2_13@sint16;
nondet v_call_i_2_14@sint16;
nondet v_call_i_2_15@sint16;
nondet v_call_i_2_16@sint16;
nondet v_call_i_2_17@sint16;
nondet v_call_i_2_18@sint16;
nondet v_call_i_2_19@sint16;
nondet v_call_i_2_20@sint16;
nondet v_call_i_2_21@sint16;
nondet v_call_i_2_22@sint16;
nondet v_call_i_2_23@sint16;
nondet v_call_i_2_24@sint16;
nondet v_call_i_2_25@sint16;
nondet v_call_i_2_26@sint16;
nondet v_call_i_2_27@sint16;
nondet v_call_i_2_28@sint16;
nondet v_call_i_2_29@sint16;
nondet v_call_i_2_30@sint16;
nondet v_call_i_2_31@sint16;
nondet v_call_i_2_1251@sint16;
nondet v_call_i_2_1_1@sint16;
nondet v_call_i_2_2_1@sint16;
nondet v_call_i_2_3_1@sint16;
nondet v_call_i_2_4_1@sint16;
nondet v_call_i_2_5_1@sint16;
nondet v_call_i_2_6_1@sint16;
nondet v_call_i_2_7_1@sint16;
nondet v_call_i_2_8_1@sint16;
nondet v_call_i_2_9_1@sint16;
nondet v_call_i_2_10_1@sint16;
nondet v_call_i_2_11_1@sint16;
nondet v_call_i_2_12_1@sint16;
nondet v_call_i_2_13_1@sint16;
nondet v_call_i_2_14_1@sint16;
nondet v_call_i_2_15_1@sint16;
nondet v_call_i_2_16_1@sint16;
nondet v_call_i_2_17_1@sint16;
nondet v_call_i_2_18_1@sint16;
nondet v_call_i_2_19_1@sint16;
nondet v_call_i_2_20_1@sint16;
nondet v_call_i_2_21_1@sint16;
nondet v_call_i_2_22_1@sint16;
nondet v_call_i_2_23_1@sint16;
nondet v_call_i_2_24_1@sint16;
nondet v_call_i_2_25_1@sint16;
nondet v_call_i_2_26_1@sint16;
nondet v_call_i_2_27_1@sint16;
nondet v_call_i_2_28_1@sint16;
nondet v_call_i_2_29_1@sint16;
nondet v_call_i_2_30_1@sint16;
nondet v_call_i_2_31_1@sint16;
nondet v_call_i_2_2261@sint16;
nondet v_call_i_2_1_2@sint16;
nondet v_call_i_2_2_2@sint16;
nondet v_call_i_2_3_2@sint16;
nondet v_call_i_2_4_2@sint16;
nondet v_call_i_2_5_2@sint16;
nondet v_call_i_2_6_2@sint16;
nondet v_call_i_2_7_2@sint16;
nondet v_call_i_2_8_2@sint16;
nondet v_call_i_2_9_2@sint16;
nondet v_call_i_2_10_2@sint16;
nondet v_call_i_2_11_2@sint16;
nondet v_call_i_2_12_2@sint16;
nondet v_call_i_2_13_2@sint16;
nondet v_call_i_2_14_2@sint16;
nondet v_call_i_2_15_2@sint16;
nondet v_call_i_2_16_2@sint16;
nondet v_call_i_2_17_2@sint16;
nondet v_call_i_2_18_2@sint16;
nondet v_call_i_2_19_2@sint16;
nondet v_call_i_2_20_2@sint16;
nondet v_call_i_2_21_2@sint16;
nondet v_call_i_2_22_2@sint16;
nondet v_call_i_2_23_2@sint16;
nondet v_call_i_2_24_2@sint16;
nondet v_call_i_2_25_2@sint16;
nondet v_call_i_2_26_2@sint16;
nondet v_call_i_2_27_2@sint16;
nondet v_call_i_2_28_2@sint16;
nondet v_call_i_2_29_2@sint16;
nondet v_call_i_2_30_2@sint16;
nondet v_call_i_2_31_2@sint16;
nondet v_call_i_2_3271@sint16;
nondet v_call_i_2_1_3@sint16;
nondet v_call_i_2_2_3@sint16;
nondet v_call_i_2_3_3@sint16;
nondet v_call_i_2_4_3@sint16;
nondet v_call_i_2_5_3@sint16;
nondet v_call_i_2_6_3@sint16;
nondet v_call_i_2_7_3@sint16;
nondet v_call_i_2_8_3@sint16;
nondet v_call_i_2_9_3@sint16;
nondet v_call_i_2_10_3@sint16;
nondet v_call_i_2_11_3@sint16;
nondet v_call_i_2_12_3@sint16;
nondet v_call_i_2_13_3@sint16;
nondet v_call_i_2_14_3@sint16;
nondet v_call_i_2_15_3@sint16;
nondet v_call_i_2_16_3@sint16;
nondet v_call_i_2_17_3@sint16;
nondet v_call_i_2_18_3@sint16;
nondet v_call_i_2_19_3@sint16;
nondet v_call_i_2_20_3@sint16;
nondet v_call_i_2_21_3@sint16;
nondet v_call_i_2_22_3@sint16;
nondet v_call_i_2_23_3@sint16;
nondet v_call_i_2_24_3@sint16;
nondet v_call_i_2_25_3@sint16;
nondet v_call_i_2_26_3@sint16;
nondet v_call_i_2_27_3@sint16;
nondet v_call_i_2_28_3@sint16;
nondet v_call_i_2_29_3@sint16;
nondet v_call_i_2_30_3@sint16;
nondet v_call_i_2_31_3@sint16;
nondet v_call_i_3@sint16;
nondet v_call_i_3_1@sint16;
nondet v_call_i_3_2@sint16;
nondet v_call_i_3_3@sint16;
nondet v_call_i_3_4@sint16;
nondet v_call_i_3_5@sint16;
nondet v_call_i_3_6@sint16;
nondet v_call_i_3_7@sint16;
nondet v_call_i_3_8@sint16;
nondet v_call_i_3_9@sint16;
nondet v_call_i_3_10@sint16;
nondet v_call_i_3_11@sint16;
nondet v_call_i_3_12@sint16;
nondet v_call_i_3_13@sint16;
nondet v_call_i_3_14@sint16;
nondet v_call_i_3_15@sint16;
nondet v_call_i_3_1181@sint16;
nondet v_call_i_3_1_1@sint16;
nondet v_call_i_3_2_1@sint16;
nondet v_call_i_3_3_1@sint16;
nondet v_call_i_3_4_1@sint16;
nondet v_call_i_3_5_1@sint16;
nondet v_call_i_3_6_1@sint16;
nondet v_call_i_3_7_1@sint16;
nondet v_call_i_3_8_1@sint16;
nondet v_call_i_3_9_1@sint16;
nondet v_call_i_3_10_1@sint16;
nondet v_call_i_3_11_1@sint16;
nondet v_call_i_3_12_1@sint16;
nondet v_call_i_3_13_1@sint16;
nondet v_call_i_3_14_1@sint16;
nondet v_call_i_3_15_1@sint16;
nondet v_call_i_3_2191@sint16;
nondet v_call_i_3_1_2@sint16;
nondet v_call_i_3_2_2@sint16;
nondet v_call_i_3_3_2@sint16;
nondet v_call_i_3_4_2@sint16;
nondet v_call_i_3_5_2@sint16;
nondet v_call_i_3_6_2@sint16;
nondet v_call_i_3_7_2@sint16;
nondet v_call_i_3_8_2@sint16;
nondet v_call_i_3_9_2@sint16;
nondet v_call_i_3_10_2@sint16;
nondet v_call_i_3_11_2@sint16;
nondet v_call_i_3_12_2@sint16;
nondet v_call_i_3_13_2@sint16;
nondet v_call_i_3_14_2@sint16;
nondet v_call_i_3_15_2@sint16;
nondet v_call_i_3_3201@sint16;
nondet v_call_i_3_1_3@sint16;
nondet v_call_i_3_2_3@sint16;
nondet v_call_i_3_3_3@sint16;
nondet v_call_i_3_4_3@sint16;
nondet v_call_i_3_5_3@sint16;
nondet v_call_i_3_6_3@sint16;
nondet v_call_i_3_7_3@sint16;
nondet v_call_i_3_8_3@sint16;
nondet v_call_i_3_9_3@sint16;
nondet v_call_i_3_10_3@sint16;
nondet v_call_i_3_11_3@sint16;
nondet v_call_i_3_12_3@sint16;
nondet v_call_i_3_13_3@sint16;
nondet v_call_i_3_14_3@sint16;
nondet v_call_i_3_15_3@sint16;
nondet v_call_i_3_4211@sint16;
nondet v_call_i_3_1_4@sint16;
nondet v_call_i_3_2_4@sint16;
nondet v_call_i_3_3_4@sint16;
nondet v_call_i_3_4_4@sint16;
nondet v_call_i_3_5_4@sint16;
nondet v_call_i_3_6_4@sint16;
nondet v_call_i_3_7_4@sint16;
nondet v_call_i_3_8_4@sint16;
nondet v_call_i_3_9_4@sint16;
nondet v_call_i_3_10_4@sint16;
nondet v_call_i_3_11_4@sint16;
nondet v_call_i_3_12_4@sint16;
nondet v_call_i_3_13_4@sint16;
nondet v_call_i_3_14_4@sint16;
nondet v_call_i_3_15_4@sint16;
nondet v_call_i_3_5221@sint16;
nondet v_call_i_3_1_5@sint16;
nondet v_call_i_3_2_5@sint16;
nondet v_call_i_3_3_5@sint16;
nondet v_call_i_3_4_5@sint16;
nondet v_call_i_3_5_5@sint16;
nondet v_call_i_3_6_5@sint16;
nondet v_call_i_3_7_5@sint16;
nondet v_call_i_3_8_5@sint16;
nondet v_call_i_3_9_5@sint16;
nondet v_call_i_3_10_5@sint16;
nondet v_call_i_3_11_5@sint16;
nondet v_call_i_3_12_5@sint16;
nondet v_call_i_3_13_5@sint16;
nondet v_call_i_3_14_5@sint16;
nondet v_call_i_3_15_5@sint16;
nondet v_call_i_3_6231@sint16;
nondet v_call_i_3_1_6@sint16;
nondet v_call_i_3_2_6@sint16;
nondet v_call_i_3_3_6@sint16;
nondet v_call_i_3_4_6@sint16;
nondet v_call_i_3_5_6@sint16;
nondet v_call_i_3_6_6@sint16;
nondet v_call_i_3_7_6@sint16;
nondet v_call_i_3_8_6@sint16;
nondet v_call_i_3_9_6@sint16;
nondet v_call_i_3_10_6@sint16;
nondet v_call_i_3_11_6@sint16;
nondet v_call_i_3_12_6@sint16;
nondet v_call_i_3_13_6@sint16;
nondet v_call_i_3_14_6@sint16;
nondet v_call_i_3_15_6@sint16;
nondet v_call_i_3_7241@sint16;
nondet v_call_i_3_1_7@sint16;
nondet v_call_i_3_2_7@sint16;
nondet v_call_i_3_3_7@sint16;
nondet v_call_i_3_4_7@sint16;
nondet v_call_i_3_5_7@sint16;
nondet v_call_i_3_6_7@sint16;
nondet v_call_i_3_7_7@sint16;
nondet v_call_i_3_8_7@sint16;
nondet v_call_i_3_9_7@sint16;
nondet v_call_i_3_10_7@sint16;
nondet v_call_i_3_11_7@sint16;
nondet v_call_i_3_12_7@sint16;
nondet v_call_i_3_13_7@sint16;
nondet v_call_i_3_14_7@sint16;
nondet v_call_i_3_15_7@sint16;
nondet v_call_i_4@sint16;
nondet v_call_i_4_1@sint16;
nondet v_call_i_4_2@sint16;
nondet v_call_i_4_3@sint16;
nondet v_call_i_4_4@sint16;
nondet v_call_i_4_5@sint16;
nondet v_call_i_4_6@sint16;
nondet v_call_i_4_7@sint16;
nondet v_call_i_4_1111@sint16;
nondet v_call_i_4_1_1@sint16;
nondet v_call_i_4_2_1@sint16;
nondet v_call_i_4_3_1@sint16;
nondet v_call_i_4_4_1@sint16;
nondet v_call_i_4_5_1@sint16;
nondet v_call_i_4_6_1@sint16;
nondet v_call_i_4_7_1@sint16;
nondet v_call_i_4_2121@sint16;
nondet v_call_i_4_1_2@sint16;
nondet v_call_i_4_2_2@sint16;
nondet v_call_i_4_3_2@sint16;
nondet v_call_i_4_4_2@sint16;
nondet v_call_i_4_5_2@sint16;
nondet v_call_i_4_6_2@sint16;
nondet v_call_i_4_7_2@sint16;
nondet v_call_i_4_3131@sint16;
nondet v_call_i_4_1_3@sint16;
nondet v_call_i_4_2_3@sint16;
nondet v_call_i_4_3_3@sint16;
nondet v_call_i_4_4_3@sint16;
nondet v_call_i_4_5_3@sint16;
nondet v_call_i_4_6_3@sint16;
nondet v_call_i_4_7_3@sint16;
nondet v_call_i_4_4141@sint16;
nondet v_call_i_4_1_4@sint16;
nondet v_call_i_4_2_4@sint16;
nondet v_call_i_4_3_4@sint16;
nondet v_call_i_4_4_4@sint16;
nondet v_call_i_4_5_4@sint16;
nondet v_call_i_4_6_4@sint16;
nondet v_call_i_4_7_4@sint16;
nondet v_call_i_4_5151@sint16;
nondet v_call_i_4_1_5@sint16;
nondet v_call_i_4_2_5@sint16;
nondet v_call_i_4_3_5@sint16;
nondet v_call_i_4_4_5@sint16;
nondet v_call_i_4_5_5@sint16;
nondet v_call_i_4_6_5@sint16;
nondet v_call_i_4_7_5@sint16;
nondet v_call_i_4_6161@sint16;
nondet v_call_i_4_1_6@sint16;
nondet v_call_i_4_2_6@sint16;
nondet v_call_i_4_3_6@sint16;
nondet v_call_i_4_4_6@sint16;
nondet v_call_i_4_5_6@sint16;
nondet v_call_i_4_6_6@sint16;
nondet v_call_i_4_7_6@sint16;
nondet v_call_i_4_7171@sint16;
nondet v_call_i_4_1_7@sint16;
nondet v_call_i_4_2_7@sint16;
nondet v_call_i_4_3_7@sint16;
nondet v_call_i_4_4_7@sint16;
nondet v_call_i_4_5_7@sint16;
nondet v_call_i_4_6_7@sint16;
nondet v_call_i_4_7_7@sint16;
nondet v_call_i_4_8@sint16;
nondet v_call_i_4_1_8@sint16;
nondet v_call_i_4_2_8@sint16;
nondet v_call_i_4_3_8@sint16;
nondet v_call_i_4_4_8@sint16;
nondet v_call_i_4_5_8@sint16;
nondet v_call_i_4_6_8@sint16;
nondet v_call_i_4_7_8@sint16;
nondet v_call_i_4_9@sint16;
nondet v_call_i_4_1_9@sint16;
nondet v_call_i_4_2_9@sint16;
nondet v_call_i_4_3_9@sint16;
nondet v_call_i_4_4_9@sint16;
nondet v_call_i_4_5_9@sint16;
nondet v_call_i_4_6_9@sint16;
nondet v_call_i_4_7_9@sint16;
nondet v_call_i_4_10@sint16;
nondet v_call_i_4_1_10@sint16;
nondet v_call_i_4_2_10@sint16;
nondet v_call_i_4_3_10@sint16;
nondet v_call_i_4_4_10@sint16;
nondet v_call_i_4_5_10@sint16;
nondet v_call_i_4_6_10@sint16;
nondet v_call_i_4_7_10@sint16;
nondet v_call_i_4_11@sint16;
nondet v_call_i_4_1_11@sint16;
nondet v_call_i_4_2_11@sint16;
nondet v_call_i_4_3_11@sint16;
nondet v_call_i_4_4_11@sint16;
nondet v_call_i_4_5_11@sint16;
nondet v_call_i_4_6_11@sint16;
nondet v_call_i_4_7_11@sint16;
nondet v_call_i_4_12@sint16;
nondet v_call_i_4_1_12@sint16;
nondet v_call_i_4_2_12@sint16;
nondet v_call_i_4_3_12@sint16;
nondet v_call_i_4_4_12@sint16;
nondet v_call_i_4_5_12@sint16;
nondet v_call_i_4_6_12@sint16;
nondet v_call_i_4_7_12@sint16;
nondet v_call_i_4_13@sint16;
nondet v_call_i_4_1_13@sint16;
nondet v_call_i_4_2_13@sint16;
nondet v_call_i_4_3_13@sint16;
nondet v_call_i_4_4_13@sint16;
nondet v_call_i_4_5_13@sint16;
nondet v_call_i_4_6_13@sint16;
nondet v_call_i_4_7_13@sint16;
nondet v_call_i_4_14@sint16;
nondet v_call_i_4_1_14@sint16;
nondet v_call_i_4_2_14@sint16;
nondet v_call_i_4_3_14@sint16;
nondet v_call_i_4_4_14@sint16;
nondet v_call_i_4_5_14@sint16;
nondet v_call_i_4_6_14@sint16;
nondet v_call_i_4_7_14@sint16;
nondet v_call_i_4_15@sint16;
nondet v_call_i_4_1_15@sint16;
nondet v_call_i_4_2_15@sint16;
nondet v_call_i_4_3_15@sint16;
nondet v_call_i_4_4_15@sint16;
nondet v_call_i_4_5_15@sint16;
nondet v_call_i_4_6_15@sint16;
nondet v_call_i_4_7_15@sint16;
nondet v_call_i_5@sint16;
nondet v_call_i_5_1@sint16;
nondet v_call_i_5_2@sint16;
nondet v_call_i_5_3@sint16;
nondet v_call_i_5_181@sint16;
nondet v_call_i_5_1_1@sint16;
nondet v_call_i_5_2_1@sint16;
nondet v_call_i_5_3_1@sint16;
nondet v_call_i_5_291@sint16;
nondet v_call_i_5_1_2@sint16;
nondet v_call_i_5_2_2@sint16;
nondet v_call_i_5_3_2@sint16;
nondet v_call_i_5_3101@sint16;
nondet v_call_i_5_1_3@sint16;
nondet v_call_i_5_2_3@sint16;
nondet v_call_i_5_3_3@sint16;
nondet v_call_i_5_4@sint16;
nondet v_call_i_5_1_4@sint16;
nondet v_call_i_5_2_4@sint16;
nondet v_call_i_5_3_4@sint16;
nondet v_call_i_5_5@sint16;
nondet v_call_i_5_1_5@sint16;
nondet v_call_i_5_2_5@sint16;
nondet v_call_i_5_3_5@sint16;
nondet v_call_i_5_6@sint16;
nondet v_call_i_5_1_6@sint16;
nondet v_call_i_5_2_6@sint16;
nondet v_call_i_5_3_6@sint16;
nondet v_call_i_5_7@sint16;
nondet v_call_i_5_1_7@sint16;
nondet v_call_i_5_2_7@sint16;
nondet v_call_i_5_3_7@sint16;
nondet v_call_i_5_8@sint16;
nondet v_call_i_5_1_8@sint16;
nondet v_call_i_5_2_8@sint16;
nondet v_call_i_5_3_8@sint16;
nondet v_call_i_5_9@sint16;
nondet v_call_i_5_1_9@sint16;
nondet v_call_i_5_2_9@sint16;
nondet v_call_i_5_3_9@sint16;
nondet v_call_i_5_10@sint16;
nondet v_call_i_5_1_10@sint16;
nondet v_call_i_5_2_10@sint16;
nondet v_call_i_5_3_10@sint16;
nondet v_call_i_5_11@sint16;
nondet v_call_i_5_1_11@sint16;
nondet v_call_i_5_2_11@sint16;
nondet v_call_i_5_3_11@sint16;
nondet v_call_i_5_12@sint16;
nondet v_call_i_5_1_12@sint16;
nondet v_call_i_5_2_12@sint16;
nondet v_call_i_5_3_12@sint16;
nondet v_call_i_5_13@sint16;
nondet v_call_i_5_1_13@sint16;
nondet v_call_i_5_2_13@sint16;
nondet v_call_i_5_3_13@sint16;
nondet v_call_i_5_14@sint16;
nondet v_call_i_5_1_14@sint16;
nondet v_call_i_5_2_14@sint16;
nondet v_call_i_5_3_14@sint16;
nondet v_call_i_5_15@sint16;
nondet v_call_i_5_1_15@sint16;
nondet v_call_i_5_2_15@sint16;
nondet v_call_i_5_3_15@sint16;
nondet v_call_i_5_16@sint16;
nondet v_call_i_5_1_16@sint16;
nondet v_call_i_5_2_16@sint16;
nondet v_call_i_5_3_16@sint16;
nondet v_call_i_5_17@sint16;
nondet v_call_i_5_1_17@sint16;
nondet v_call_i_5_2_17@sint16;
nondet v_call_i_5_3_17@sint16;
nondet v_call_i_5_18@sint16;
nondet v_call_i_5_1_18@sint16;
nondet v_call_i_5_2_18@sint16;
nondet v_call_i_5_3_18@sint16;
nondet v_call_i_5_19@sint16;
nondet v_call_i_5_1_19@sint16;
nondet v_call_i_5_2_19@sint16;
nondet v_call_i_5_3_19@sint16;
nondet v_call_i_5_20@sint16;
nondet v_call_i_5_1_20@sint16;
nondet v_call_i_5_2_20@sint16;
nondet v_call_i_5_3_20@sint16;
nondet v_call_i_5_21@sint16;
nondet v_call_i_5_1_21@sint16;
nondet v_call_i_5_2_21@sint16;
nondet v_call_i_5_3_21@sint16;
nondet v_call_i_5_22@sint16;
nondet v_call_i_5_1_22@sint16;
nondet v_call_i_5_2_22@sint16;
nondet v_call_i_5_3_22@sint16;
nondet v_call_i_5_23@sint16;
nondet v_call_i_5_1_23@sint16;
nondet v_call_i_5_2_23@sint16;
nondet v_call_i_5_3_23@sint16;
nondet v_call_i_5_24@sint16;
nondet v_call_i_5_1_24@sint16;
nondet v_call_i_5_2_24@sint16;
nondet v_call_i_5_3_24@sint16;
nondet v_call_i_5_25@sint16;
nondet v_call_i_5_1_25@sint16;
nondet v_call_i_5_2_25@sint16;
nondet v_call_i_5_3_25@sint16;
nondet v_call_i_5_26@sint16;
nondet v_call_i_5_1_26@sint16;
nondet v_call_i_5_2_26@sint16;
nondet v_call_i_5_3_26@sint16;
nondet v_call_i_5_27@sint16;
nondet v_call_i_5_1_27@sint16;
nondet v_call_i_5_2_27@sint16;
nondet v_call_i_5_3_27@sint16;
nondet v_call_i_5_28@sint16;
nondet v_call_i_5_1_28@sint16;
nondet v_call_i_5_2_28@sint16;
nondet v_call_i_5_3_28@sint16;
nondet v_call_i_5_29@sint16;
nondet v_call_i_5_1_29@sint16;
nondet v_call_i_5_2_29@sint16;
nondet v_call_i_5_3_29@sint16;
nondet v_call_i_5_30@sint16;
nondet v_call_i_5_1_30@sint16;
nondet v_call_i_5_2_30@sint16;
nondet v_call_i_5_3_30@sint16;
nondet v_call_i_5_31@sint16;
nondet v_call_i_5_1_31@sint16;
nondet v_call_i_5_2_31@sint16;
nondet v_call_i_5_3_31@sint16;
nondet v_call_i_6@sint16;
nondet v_call_i_6_1@sint16;
nondet v_call_i_6_171@sint16;
nondet v_call_i_6_1_1@sint16;
nondet v_call_i_6_2@sint16;
nondet v_call_i_6_1_2@sint16;
nondet v_call_i_6_3@sint16;
nondet v_call_i_6_1_3@sint16;
nondet v_call_i_6_4@sint16;
nondet v_call_i_6_1_4@sint16;
nondet v_call_i_6_5@sint16;
nondet v_call_i_6_1_5@sint16;
nondet v_call_i_6_6@sint16;
nondet v_call_i_6_1_6@sint16;
nondet v_call_i_6_7@sint16;
nondet v_call_i_6_1_7@sint16;
nondet v_call_i_6_8@sint16;
nondet v_call_i_6_1_8@sint16;
nondet v_call_i_6_9@sint16;
nondet v_call_i_6_1_9@sint16;
nondet v_call_i_6_10@sint16;
nondet v_call_i_6_1_10@sint16;
nondet v_call_i_6_11@sint16;
nondet v_call_i_6_1_11@sint16;
nondet v_call_i_6_12@sint16;
nondet v_call_i_6_1_12@sint16;
nondet v_call_i_6_13@sint16;
nondet v_call_i_6_1_13@sint16;
nondet v_call_i_6_14@sint16;
nondet v_call_i_6_1_14@sint16;
nondet v_call_i_6_15@sint16;
nondet v_call_i_6_1_15@sint16;
nondet v_call_i_6_16@sint16;
nondet v_call_i_6_1_16@sint16;
nondet v_call_i_6_17@sint16;
nondet v_call_i_6_1_17@sint16;
nondet v_call_i_6_18@sint16;
nondet v_call_i_6_1_18@sint16;
nondet v_call_i_6_19@sint16;
nondet v_call_i_6_1_19@sint16;
nondet v_call_i_6_20@sint16;
nondet v_call_i_6_1_20@sint16;
nondet v_call_i_6_21@sint16;
nondet v_call_i_6_1_21@sint16;
nondet v_call_i_6_22@sint16;
nondet v_call_i_6_1_22@sint16;
nondet v_call_i_6_23@sint16;
nondet v_call_i_6_1_23@sint16;
nondet v_call_i_6_24@sint16;
nondet v_call_i_6_1_24@sint16;
nondet v_call_i_6_25@sint16;
nondet v_call_i_6_1_25@sint16;
nondet v_call_i_6_26@sint16;
nondet v_call_i_6_1_26@sint16;
nondet v_call_i_6_27@sint16;
nondet v_call_i_6_1_27@sint16;
nondet v_call_i_6_28@sint16;
nondet v_call_i_6_1_28@sint16;
nondet v_call_i_6_29@sint16;
nondet v_call_i_6_1_29@sint16;
nondet v_call_i_6_30@sint16;
nondet v_call_i_6_1_30@sint16;
nondet v_call_i_6_31@sint16;
nondet v_call_i_6_1_31@sint16;
nondet v_call_i_6_32@sint16;
nondet v_call_i_6_1_32@sint16;
nondet v_call_i_6_33@sint16;
nondet v_call_i_6_1_33@sint16;
nondet v_call_i_6_34@sint16;
nondet v_call_i_6_1_34@sint16;
nondet v_call_i_6_35@sint16;
nondet v_call_i_6_1_35@sint16;
nondet v_call_i_6_36@sint16;
nondet v_call_i_6_1_36@sint16;
nondet v_call_i_6_37@sint16;
nondet v_call_i_6_1_37@sint16;
nondet v_call_i_6_38@sint16;
nondet v_call_i_6_1_38@sint16;
nondet v_call_i_6_39@sint16;
nondet v_call_i_6_1_39@sint16;
nondet v_call_i_6_40@sint16;
nondet v_call_i_6_1_40@sint16;
nondet v_call_i_6_41@sint16;
nondet v_call_i_6_1_41@sint16;
nondet v_call_i_6_42@sint16;
nondet v_call_i_6_1_42@sint16;
nondet v_call_i_6_43@sint16;
nondet v_call_i_6_1_43@sint16;
nondet v_call_i_6_44@sint16;
nondet v_call_i_6_1_44@sint16;
nondet v_call_i_6_45@sint16;
nondet v_call_i_6_1_45@sint16;
nondet v_call_i_6_46@sint16;
nondet v_call_i_6_1_46@sint16;
nondet v_call_i_6_47@sint16;
nondet v_call_i_6_1_47@sint16;
nondet v_call_i_6_48@sint16;
nondet v_call_i_6_1_48@sint16;
nondet v_call_i_6_49@sint16;
nondet v_call_i_6_1_49@sint16;
nondet v_call_i_6_50@sint16;
nondet v_call_i_6_1_50@sint16;
nondet v_call_i_6_51@sint16;
nondet v_call_i_6_1_51@sint16;
nondet v_call_i_6_52@sint16;
nondet v_call_i_6_1_52@sint16;
nondet v_call_i_6_53@sint16;
nondet v_call_i_6_1_53@sint16;
nondet v_call_i_6_54@sint16;
nondet v_call_i_6_1_54@sint16;
nondet v_call_i_6_55@sint16;
nondet v_call_i_6_1_55@sint16;
nondet v_call_i_6_56@sint16;
nondet v_call_i_6_1_56@sint16;
nondet v_call_i_6_57@sint16;
nondet v_call_i_6_1_57@sint16;
nondet v_call_i_6_58@sint16;
nondet v_call_i_6_1_58@sint16;
nondet v_call_i_6_59@sint16;
nondet v_call_i_6_1_59@sint16;
nondet v_call_i_6_60@sint16;
nondet v_call_i_6_1_60@sint16;
nondet v_call_i_6_61@sint16;
nondet v_call_i_6_1_61@sint16;
nondet v_call_i_6_62@sint16;
nondet v_call_i_6_1_62@sint16;
nondet v_call_i_6_63@sint16;
nondet v_call_i_6_1_63@sint16;

mov mem0_0_k15 mem0_0;
mov mem0_2_k15 mem0_2;
mov mem0_4_k15 mem0_4;
mov mem0_6_k15 mem0_6;
mov mem0_8_k15 mem0_8;
mov mem0_10_k15 mem0_10;
mov mem0_12_k15 mem0_12;
mov mem0_14_k15 mem0_14;
mov mem0_16_k15 mem0_16;
mov mem0_18_k15 mem0_18;
mov mem0_20_k15 mem0_20;
mov mem0_22_k15 mem0_22;
mov mem0_24_k15 mem0_24;
mov mem0_26_k15 mem0_26;
mov mem0_28_k15 mem0_28;
mov mem0_30_k15 mem0_30;
mov mem0_32_k15 mem0_32;
mov mem0_34_k15 mem0_34;
mov mem0_36_k15 mem0_36;
mov mem0_38_k15 mem0_38;
mov mem0_40_k15 mem0_40;
mov mem0_42_k15 mem0_42;
mov mem0_44_k15 mem0_44;
mov mem0_46_k15 mem0_46;
mov mem0_48_k15 mem0_48;
mov mem0_50_k15 mem0_50;
mov mem0_52_k15 mem0_52;
mov mem0_54_k15 mem0_54;
mov mem0_56_k15 mem0_56;
mov mem0_58_k15 mem0_58;
mov mem0_60_k15 mem0_60;
mov mem0_62_k15 mem0_62;
mov mem0_64_k15 mem0_64;
mov mem0_66_k15 mem0_66;
mov mem0_68_k15 mem0_68;
mov mem0_70_k15 mem0_70;
mov mem0_72_k15 mem0_72;
mov mem0_74_k15 mem0_74;
mov mem0_76_k15 mem0_76;
mov mem0_78_k15 mem0_78;
mov mem0_80_k15 mem0_80;
mov mem0_82_k15 mem0_82;
mov mem0_84_k15 mem0_84;
mov mem0_86_k15 mem0_86;
mov mem0_88_k15 mem0_88;
mov mem0_90_k15 mem0_90;
mov mem0_92_k15 mem0_92;
mov mem0_94_k15 mem0_94;
mov mem0_96_k15 mem0_96;
mov mem0_98_k15 mem0_98;
mov mem0_100_k15 mem0_100;
mov mem0_102_k15 mem0_102;
mov mem0_104_k15 mem0_104;
mov mem0_106_k15 mem0_106;
mov mem0_108_k15 mem0_108;
mov mem0_110_k15 mem0_110;
mov mem0_112_k15 mem0_112;
mov mem0_114_k15 mem0_114;
mov mem0_116_k15 mem0_116;
mov mem0_118_k15 mem0_118;
mov mem0_120_k15 mem0_120;
mov mem0_122_k15 mem0_122;
mov mem0_124_k15 mem0_124;
mov mem0_126_k15 mem0_126;
mov mem0_128_k15 mem0_128;
mov mem0_130_k15 mem0_130;
mov mem0_132_k15 mem0_132;
mov mem0_134_k15 mem0_134;
mov mem0_136_k15 mem0_136;
mov mem0_138_k15 mem0_138;
mov mem0_140_k15 mem0_140;
mov mem0_142_k15 mem0_142;
mov mem0_144_k15 mem0_144;
mov mem0_146_k15 mem0_146;
mov mem0_148_k15 mem0_148;
mov mem0_150_k15 mem0_150;
mov mem0_152_k15 mem0_152;
mov mem0_154_k15 mem0_154;
mov mem0_156_k15 mem0_156;
mov mem0_158_k15 mem0_158;
mov mem0_160_k15 mem0_160;
mov mem0_162_k15 mem0_162;
mov mem0_164_k15 mem0_164;
mov mem0_166_k15 mem0_166;
mov mem0_168_k15 mem0_168;
mov mem0_170_k15 mem0_170;
mov mem0_172_k15 mem0_172;
mov mem0_174_k15 mem0_174;
mov mem0_176_k15 mem0_176;
mov mem0_178_k15 mem0_178;
mov mem0_180_k15 mem0_180;
mov mem0_182_k15 mem0_182;
mov mem0_184_k15 mem0_184;
mov mem0_186_k15 mem0_186;
mov mem0_188_k15 mem0_188;
mov mem0_190_k15 mem0_190;
mov mem0_192_k15 mem0_192;
mov mem0_194_k15 mem0_194;
mov mem0_196_k15 mem0_196;
mov mem0_198_k15 mem0_198;
mov mem0_200_k15 mem0_200;
mov mem0_202_k15 mem0_202;
mov mem0_204_k15 mem0_204;
mov mem0_206_k15 mem0_206;
mov mem0_208_k15 mem0_208;
mov mem0_210_k15 mem0_210;
mov mem0_212_k15 mem0_212;
mov mem0_214_k15 mem0_214;
mov mem0_216_k15 mem0_216;
mov mem0_218_k15 mem0_218;
mov mem0_220_k15 mem0_220;
mov mem0_222_k15 mem0_222;
mov mem0_224_k15 mem0_224;
mov mem0_226_k15 mem0_226;
mov mem0_228_k15 mem0_228;
mov mem0_230_k15 mem0_230;
mov mem0_232_k15 mem0_232;
mov mem0_234_k15 mem0_234;
mov mem0_236_k15 mem0_236;
mov mem0_238_k15 mem0_238;
mov mem0_240_k15 mem0_240;
mov mem0_242_k15 mem0_242;
mov mem0_244_k15 mem0_244;
mov mem0_246_k15 mem0_246;
mov mem0_248_k15 mem0_248;
mov mem0_250_k15 mem0_250;
mov mem0_252_k15 mem0_252;
mov mem0_254_k15 mem0_254;
mov mem0_256_k15 mem0_256;
mov mem0_258_k15 mem0_258;
mov mem0_260_k15 mem0_260;
mov mem0_262_k15 mem0_262;
mov mem0_264_k15 mem0_264;
mov mem0_266_k15 mem0_266;
mov mem0_268_k15 mem0_268;
mov mem0_270_k15 mem0_270;
mov mem0_272_k15 mem0_272;
mov mem0_274_k15 mem0_274;
mov mem0_276_k15 mem0_276;
mov mem0_278_k15 mem0_278;
mov mem0_280_k15 mem0_280;
mov mem0_282_k15 mem0_282;
mov mem0_284_k15 mem0_284;
mov mem0_286_k15 mem0_286;
mov mem0_288_k15 mem0_288;
mov mem0_290_k15 mem0_290;
mov mem0_292_k15 mem0_292;
mov mem0_294_k15 mem0_294;
mov mem0_296_k15 mem0_296;
mov mem0_298_k15 mem0_298;
mov mem0_300_k15 mem0_300;
mov mem0_302_k15 mem0_302;
mov mem0_304_k15 mem0_304;
mov mem0_306_k15 mem0_306;
mov mem0_308_k15 mem0_308;
mov mem0_310_k15 mem0_310;
mov mem0_312_k15 mem0_312;
mov mem0_314_k15 mem0_314;
mov mem0_316_k15 mem0_316;
mov mem0_318_k15 mem0_318;
mov mem0_320_k15 mem0_320;
mov mem0_322_k15 mem0_322;
mov mem0_324_k15 mem0_324;
mov mem0_326_k15 mem0_326;
mov mem0_328_k15 mem0_328;
mov mem0_330_k15 mem0_330;
mov mem0_332_k15 mem0_332;
mov mem0_334_k15 mem0_334;
mov mem0_336_k15 mem0_336;
mov mem0_338_k15 mem0_338;
mov mem0_340_k15 mem0_340;
mov mem0_342_k15 mem0_342;
mov mem0_344_k15 mem0_344;
mov mem0_346_k15 mem0_346;
mov mem0_348_k15 mem0_348;
mov mem0_350_k15 mem0_350;
mov mem0_352_k15 mem0_352;
mov mem0_354_k15 mem0_354;
mov mem0_356_k15 mem0_356;
mov mem0_358_k15 mem0_358;
mov mem0_360_k15 mem0_360;
mov mem0_362_k15 mem0_362;
mov mem0_364_k15 mem0_364;
mov mem0_366_k15 mem0_366;
mov mem0_368_k15 mem0_368;
mov mem0_370_k15 mem0_370;
mov mem0_372_k15 mem0_372;
mov mem0_374_k15 mem0_374;
mov mem0_376_k15 mem0_376;
mov mem0_378_k15 mem0_378;
mov mem0_380_k15 mem0_380;
mov mem0_382_k15 mem0_382;
mov mem0_384_k15 mem0_384;
mov mem0_386_k15 mem0_386;
mov mem0_388_k15 mem0_388;
mov mem0_390_k15 mem0_390;
mov mem0_392_k15 mem0_392;
mov mem0_394_k15 mem0_394;
mov mem0_396_k15 mem0_396;
mov mem0_398_k15 mem0_398;
mov mem0_400_k15 mem0_400;
mov mem0_402_k15 mem0_402;
mov mem0_404_k15 mem0_404;
mov mem0_406_k15 mem0_406;
mov mem0_408_k15 mem0_408;
mov mem0_410_k15 mem0_410;
mov mem0_412_k15 mem0_412;
mov mem0_414_k15 mem0_414;
mov mem0_416_k15 mem0_416;
mov mem0_418_k15 mem0_418;
mov mem0_420_k15 mem0_420;
mov mem0_422_k15 mem0_422;
mov mem0_424_k15 mem0_424;
mov mem0_426_k15 mem0_426;
mov mem0_428_k15 mem0_428;
mov mem0_430_k15 mem0_430;
mov mem0_432_k15 mem0_432;
mov mem0_434_k15 mem0_434;
mov mem0_436_k15 mem0_436;
mov mem0_438_k15 mem0_438;
mov mem0_440_k15 mem0_440;
mov mem0_442_k15 mem0_442;
mov mem0_444_k15 mem0_444;
mov mem0_446_k15 mem0_446;
mov mem0_448_k15 mem0_448;
mov mem0_450_k15 mem0_450;
mov mem0_452_k15 mem0_452;
mov mem0_454_k15 mem0_454;
mov mem0_456_k15 mem0_456;
mov mem0_458_k15 mem0_458;
mov mem0_460_k15 mem0_460;
mov mem0_462_k15 mem0_462;
mov mem0_464_k15 mem0_464;
mov mem0_466_k15 mem0_466;
mov mem0_468_k15 mem0_468;
mov mem0_470_k15 mem0_470;
mov mem0_472_k15 mem0_472;
mov mem0_474_k15 mem0_474;
mov mem0_476_k15 mem0_476;
mov mem0_478_k15 mem0_478;
mov mem0_480_k15 mem0_480;
mov mem0_482_k15 mem0_482;
mov mem0_484_k15 mem0_484;
mov mem0_486_k15 mem0_486;
mov mem0_488_k15 mem0_488;
mov mem0_490_k15 mem0_490;
mov mem0_492_k15 mem0_492;
mov mem0_494_k15 mem0_494;
mov mem0_496_k15 mem0_496;
mov mem0_498_k15 mem0_498;
mov mem0_500_k15 mem0_500;
mov mem0_502_k15 mem0_502;
mov mem0_504_k15 mem0_504;
mov mem0_506_k15 mem0_506;
mov mem0_508_k15 mem0_508;
mov mem0_510_k15 mem0_510;

(* NOTE: k = 16 *)

(*   %arrayidx9.4 = getelementptr inbounds i16, i16* %r, i64 8 *)
(*   %1024 = load i16, i16* %arrayidx9.4, align 2, !tbaa !3 *)
mov v1024 mem0_16;
(*   %conv1.i.4 = sext i16 %1024 to i32 *)
cast v_conv1_i_4@sint32 v1024@sint16;
(*   %mul.i.4 = mul nsw i32 %conv1.i.4, 573 *)
mul v_mul_i_4 v_conv1_i_4 (573)@sint32;
(*   %call.i.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4, v_call_i_4);
(*   %1025 = load i16, i16* %r, align 2, !tbaa !3 *)
mov v1025 mem0_0;
(*   %sub.4 = sub i16 %1025, %call.i.4 *)
sub v_sub_4 v1025 v_call_i_4;
(*   store i16 %sub.4, i16* %arrayidx9.4, align 2, !tbaa !3 *)
mov mem0_16 v_sub_4;
(*   %add21.4 = add i16 %1025, %call.i.4 *)
add v_add21_4 v1025 v_call_i_4;
(*   store i16 %add21.4, i16* %r, align 2, !tbaa !3 *)
mov mem0_0 v_add21_4;
(*   %arrayidx9.4.1 = getelementptr inbounds i16, i16* %r, i64 9 *)
(*   %1026 = load i16, i16* %arrayidx9.4.1, align 2, !tbaa !3 *)
mov v1026 mem0_18;
(*   %conv1.i.4.1 = sext i16 %1026 to i32 *)
cast v_conv1_i_4_1@sint32 v1026@sint16;
(*   %mul.i.4.1 = mul nsw i32 %conv1.i.4.1, 573 *)
mul v_mul_i_4_1 v_conv1_i_4_1 (573)@sint32;
(*   %call.i.4.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1, v_call_i_4_1);
(*   %arrayidx11.4.1 = getelementptr inbounds i16, i16* %r, i64 1 *)
(*   %1027 = load i16, i16* %arrayidx11.4.1, align 2, !tbaa !3 *)
mov v1027 mem0_2;
(*   %sub.4.1 = sub i16 %1027, %call.i.4.1 *)
sub v_sub_4_1 v1027 v_call_i_4_1;
(*   store i16 %sub.4.1, i16* %arrayidx9.4.1, align 2, !tbaa !3 *)
mov mem0_18 v_sub_4_1;
(*   %add21.4.1 = add i16 %1027, %call.i.4.1 *)
add v_add21_4_1 v1027 v_call_i_4_1;
(*   store i16 %add21.4.1, i16* %arrayidx11.4.1, align 2, !tbaa !3 *)
mov mem0_2 v_add21_4_1;
(*   %arrayidx9.4.2 = getelementptr inbounds i16, i16* %r, i64 10 *)
(*   %1028 = load i16, i16* %arrayidx9.4.2, align 2, !tbaa !3 *)
mov v1028 mem0_20;
(*   %conv1.i.4.2 = sext i16 %1028 to i32 *)
cast v_conv1_i_4_2@sint32 v1028@sint16;
(*   %mul.i.4.2 = mul nsw i32 %conv1.i.4.2, 573 *)
mul v_mul_i_4_2 v_conv1_i_4_2 (573)@sint32;
(*   %call.i.4.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2, v_call_i_4_2);
(*   %arrayidx11.4.2 = getelementptr inbounds i16, i16* %r, i64 2 *)
(*   %1029 = load i16, i16* %arrayidx11.4.2, align 2, !tbaa !3 *)
mov v1029 mem0_4;
(*   %sub.4.2 = sub i16 %1029, %call.i.4.2 *)
sub v_sub_4_2 v1029 v_call_i_4_2;
(*   store i16 %sub.4.2, i16* %arrayidx9.4.2, align 2, !tbaa !3 *)
mov mem0_20 v_sub_4_2;
(*   %add21.4.2 = add i16 %1029, %call.i.4.2 *)
add v_add21_4_2 v1029 v_call_i_4_2;
(*   store i16 %add21.4.2, i16* %arrayidx11.4.2, align 2, !tbaa !3 *)
mov mem0_4 v_add21_4_2;
(*   %arrayidx9.4.3 = getelementptr inbounds i16, i16* %r, i64 11 *)
(*   %1030 = load i16, i16* %arrayidx9.4.3, align 2, !tbaa !3 *)
mov v1030 mem0_22;
(*   %conv1.i.4.3 = sext i16 %1030 to i32 *)
cast v_conv1_i_4_3@sint32 v1030@sint16;
(*   %mul.i.4.3 = mul nsw i32 %conv1.i.4.3, 573 *)
mul v_mul_i_4_3 v_conv1_i_4_3 (573)@sint32;
(*   %call.i.4.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3, v_call_i_4_3);
(*   %arrayidx11.4.3 = getelementptr inbounds i16, i16* %r, i64 3 *)
(*   %1031 = load i16, i16* %arrayidx11.4.3, align 2, !tbaa !3 *)
mov v1031 mem0_6;
(*   %sub.4.3 = sub i16 %1031, %call.i.4.3 *)
sub v_sub_4_3 v1031 v_call_i_4_3;
(*   store i16 %sub.4.3, i16* %arrayidx9.4.3, align 2, !tbaa !3 *)
mov mem0_22 v_sub_4_3;
(*   %add21.4.3 = add i16 %1031, %call.i.4.3 *)
add v_add21_4_3 v1031 v_call_i_4_3;
(*   store i16 %add21.4.3, i16* %arrayidx11.4.3, align 2, !tbaa !3 *)
mov mem0_6 v_add21_4_3;
(*   %arrayidx9.4.4 = getelementptr inbounds i16, i16* %r, i64 12 *)
(*   %1032 = load i16, i16* %arrayidx9.4.4, align 2, !tbaa !3 *)
mov v1032 mem0_24;
(*   %conv1.i.4.4 = sext i16 %1032 to i32 *)
cast v_conv1_i_4_4@sint32 v1032@sint16;
(*   %mul.i.4.4 = mul nsw i32 %conv1.i.4.4, 573 *)
mul v_mul_i_4_4 v_conv1_i_4_4 (573)@sint32;
(*   %call.i.4.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4, v_call_i_4_4);
(*   %arrayidx11.4.4 = getelementptr inbounds i16, i16* %r, i64 4 *)
(*   %1033 = load i16, i16* %arrayidx11.4.4, align 2, !tbaa !3 *)
mov v1033 mem0_8;
(*   %sub.4.4 = sub i16 %1033, %call.i.4.4 *)
sub v_sub_4_4 v1033 v_call_i_4_4;
(*   store i16 %sub.4.4, i16* %arrayidx9.4.4, align 2, !tbaa !3 *)
mov mem0_24 v_sub_4_4;
(*   %add21.4.4 = add i16 %1033, %call.i.4.4 *)
add v_add21_4_4 v1033 v_call_i_4_4;
(*   store i16 %add21.4.4, i16* %arrayidx11.4.4, align 2, !tbaa !3 *)
mov mem0_8 v_add21_4_4;
(*   %arrayidx9.4.5 = getelementptr inbounds i16, i16* %r, i64 13 *)
(*   %1034 = load i16, i16* %arrayidx9.4.5, align 2, !tbaa !3 *)
mov v1034 mem0_26;
(*   %conv1.i.4.5 = sext i16 %1034 to i32 *)
cast v_conv1_i_4_5@sint32 v1034@sint16;
(*   %mul.i.4.5 = mul nsw i32 %conv1.i.4.5, 573 *)
mul v_mul_i_4_5 v_conv1_i_4_5 (573)@sint32;
(*   %call.i.4.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5, v_call_i_4_5);
(*   %arrayidx11.4.5 = getelementptr inbounds i16, i16* %r, i64 5 *)
(*   %1035 = load i16, i16* %arrayidx11.4.5, align 2, !tbaa !3 *)
mov v1035 mem0_10;
(*   %sub.4.5 = sub i16 %1035, %call.i.4.5 *)
sub v_sub_4_5 v1035 v_call_i_4_5;
(*   store i16 %sub.4.5, i16* %arrayidx9.4.5, align 2, !tbaa !3 *)
mov mem0_26 v_sub_4_5;
(*   %add21.4.5 = add i16 %1035, %call.i.4.5 *)
add v_add21_4_5 v1035 v_call_i_4_5;
(*   store i16 %add21.4.5, i16* %arrayidx11.4.5, align 2, !tbaa !3 *)
mov mem0_10 v_add21_4_5;
(*   %arrayidx9.4.6 = getelementptr inbounds i16, i16* %r, i64 14 *)
(*   %1036 = load i16, i16* %arrayidx9.4.6, align 2, !tbaa !3 *)
mov v1036 mem0_28;
(*   %conv1.i.4.6 = sext i16 %1036 to i32 *)
cast v_conv1_i_4_6@sint32 v1036@sint16;
(*   %mul.i.4.6 = mul nsw i32 %conv1.i.4.6, 573 *)
mul v_mul_i_4_6 v_conv1_i_4_6 (573)@sint32;
(*   %call.i.4.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6, v_call_i_4_6);
(*   %arrayidx11.4.6 = getelementptr inbounds i16, i16* %r, i64 6 *)
(*   %1037 = load i16, i16* %arrayidx11.4.6, align 2, !tbaa !3 *)
mov v1037 mem0_12;
(*   %sub.4.6 = sub i16 %1037, %call.i.4.6 *)
sub v_sub_4_6 v1037 v_call_i_4_6;
(*   store i16 %sub.4.6, i16* %arrayidx9.4.6, align 2, !tbaa !3 *)
mov mem0_28 v_sub_4_6;
(*   %add21.4.6 = add i16 %1037, %call.i.4.6 *)
add v_add21_4_6 v1037 v_call_i_4_6;
(*   store i16 %add21.4.6, i16* %arrayidx11.4.6, align 2, !tbaa !3 *)
mov mem0_12 v_add21_4_6;
(*   %arrayidx9.4.7 = getelementptr inbounds i16, i16* %r, i64 15 *)
(*   %1038 = load i16, i16* %arrayidx9.4.7, align 2, !tbaa !3 *)
mov v1038 mem0_30;
(*   %conv1.i.4.7 = sext i16 %1038 to i32 *)
cast v_conv1_i_4_7@sint32 v1038@sint16;
(*   %mul.i.4.7 = mul nsw i32 %conv1.i.4.7, 573 *)
mul v_mul_i_4_7 v_conv1_i_4_7 (573)@sint32;
(*   %call.i.4.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7, v_call_i_4_7);
(*   %arrayidx11.4.7 = getelementptr inbounds i16, i16* %r, i64 7 *)
(*   %1039 = load i16, i16* %arrayidx11.4.7, align 2, !tbaa !3 *)
mov v1039 mem0_14;
(*   %sub.4.7 = sub i16 %1039, %call.i.4.7 *)
sub v_sub_4_7 v1039 v_call_i_4_7;
(*   store i16 %sub.4.7, i16* %arrayidx9.4.7, align 2, !tbaa !3 *)
mov mem0_30 v_sub_4_7;
(*   %add21.4.7 = add i16 %1039, %call.i.4.7 *)
add v_add21_4_7 v1039 v_call_i_4_7;
(*   store i16 %add21.4.7, i16* %arrayidx11.4.7, align 2, !tbaa !3 *)
mov mem0_14 v_add21_4_7;

(* NOTE: k = 17 *)

(*   %arrayidx9.4.1108 = getelementptr inbounds i16, i16* %r, i64 24 *)
(*   %1040 = load i16, i16* %arrayidx9.4.1108, align 2, !tbaa !3 *)
mov v1040 mem0_48;
(*   %conv1.i.4.1109 = sext i16 %1040 to i32 *)
cast v_conv1_i_4_1109@sint32 v1040@sint16;
(*   %mul.i.4.1110 = mul nsw i32 %conv1.i.4.1109, -1325 *)
mul v_mul_i_4_1110 v_conv1_i_4_1109 (-1325)@sint32;
(*   %call.i.4.1111 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1110) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1110, v_call_i_4_1111);
(*   %arrayidx11.4.1112 = getelementptr inbounds i16, i16* %r, i64 16 *)
(*   %1041 = load i16, i16* %arrayidx11.4.1112, align 2, !tbaa !3 *)
mov v1041 mem0_32;
(*   %sub.4.1113 = sub i16 %1041, %call.i.4.1111 *)
sub v_sub_4_1113 v1041 v_call_i_4_1111;
(*   store i16 %sub.4.1113, i16* %arrayidx9.4.1108, align 2, !tbaa !3 *)
mov mem0_48 v_sub_4_1113;
(*   %add21.4.1114 = add i16 %1041, %call.i.4.1111 *)
add v_add21_4_1114 v1041 v_call_i_4_1111;
(*   store i16 %add21.4.1114, i16* %arrayidx11.4.1112, align 2, !tbaa !3 *)
mov mem0_32 v_add21_4_1114;
(*   %arrayidx9.4.1.1 = getelementptr inbounds i16, i16* %r, i64 25 *)
(*   %1042 = load i16, i16* %arrayidx9.4.1.1, align 2, !tbaa !3 *)
mov v1042 mem0_50;
(*   %conv1.i.4.1.1 = sext i16 %1042 to i32 *)
cast v_conv1_i_4_1_1@sint32 v1042@sint16;
(*   %mul.i.4.1.1 = mul nsw i32 %conv1.i.4.1.1, -1325 *)
mul v_mul_i_4_1_1 v_conv1_i_4_1_1 (-1325)@sint32;
(*   %call.i.4.1.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1_1, v_call_i_4_1_1);
(*   %arrayidx11.4.1.1 = getelementptr inbounds i16, i16* %r, i64 17 *)
(*   %1043 = load i16, i16* %arrayidx11.4.1.1, align 2, !tbaa !3 *)
mov v1043 mem0_34;
(*   %sub.4.1.1 = sub i16 %1043, %call.i.4.1.1 *)
sub v_sub_4_1_1 v1043 v_call_i_4_1_1;
(*   store i16 %sub.4.1.1, i16* %arrayidx9.4.1.1, align 2, !tbaa !3 *)
mov mem0_50 v_sub_4_1_1;
(*   %add21.4.1.1 = add i16 %1043, %call.i.4.1.1 *)
add v_add21_4_1_1 v1043 v_call_i_4_1_1;
(*   store i16 %add21.4.1.1, i16* %arrayidx11.4.1.1, align 2, !tbaa !3 *)
mov mem0_34 v_add21_4_1_1;
(*   %arrayidx9.4.2.1 = getelementptr inbounds i16, i16* %r, i64 26 *)
(*   %1044 = load i16, i16* %arrayidx9.4.2.1, align 2, !tbaa !3 *)
mov v1044 mem0_52;
(*   %conv1.i.4.2.1 = sext i16 %1044 to i32 *)
cast v_conv1_i_4_2_1@sint32 v1044@sint16;
(*   %mul.i.4.2.1 = mul nsw i32 %conv1.i.4.2.1, -1325 *)
mul v_mul_i_4_2_1 v_conv1_i_4_2_1 (-1325)@sint32;
(*   %call.i.4.2.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2_1, v_call_i_4_2_1);
(*   %arrayidx11.4.2.1 = getelementptr inbounds i16, i16* %r, i64 18 *)
(*   %1045 = load i16, i16* %arrayidx11.4.2.1, align 2, !tbaa !3 *)
mov v1045 mem0_36;
(*   %sub.4.2.1 = sub i16 %1045, %call.i.4.2.1 *)
sub v_sub_4_2_1 v1045 v_call_i_4_2_1;
(*   store i16 %sub.4.2.1, i16* %arrayidx9.4.2.1, align 2, !tbaa !3 *)
mov mem0_52 v_sub_4_2_1;
(*   %add21.4.2.1 = add i16 %1045, %call.i.4.2.1 *)
add v_add21_4_2_1 v1045 v_call_i_4_2_1;
(*   store i16 %add21.4.2.1, i16* %arrayidx11.4.2.1, align 2, !tbaa !3 *)
mov mem0_36 v_add21_4_2_1;
(*   %arrayidx9.4.3.1 = getelementptr inbounds i16, i16* %r, i64 27 *)
(*   %1046 = load i16, i16* %arrayidx9.4.3.1, align 2, !tbaa !3 *)
mov v1046 mem0_54;
(*   %conv1.i.4.3.1 = sext i16 %1046 to i32 *)
cast v_conv1_i_4_3_1@sint32 v1046@sint16;
(*   %mul.i.4.3.1 = mul nsw i32 %conv1.i.4.3.1, -1325 *)
mul v_mul_i_4_3_1 v_conv1_i_4_3_1 (-1325)@sint32;
(*   %call.i.4.3.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3_1, v_call_i_4_3_1);
(*   %arrayidx11.4.3.1 = getelementptr inbounds i16, i16* %r, i64 19 *)
(*   %1047 = load i16, i16* %arrayidx11.4.3.1, align 2, !tbaa !3 *)
mov v1047 mem0_38;
(*   %sub.4.3.1 = sub i16 %1047, %call.i.4.3.1 *)
sub v_sub_4_3_1 v1047 v_call_i_4_3_1;
(*   store i16 %sub.4.3.1, i16* %arrayidx9.4.3.1, align 2, !tbaa !3 *)
mov mem0_54 v_sub_4_3_1;
(*   %add21.4.3.1 = add i16 %1047, %call.i.4.3.1 *)
add v_add21_4_3_1 v1047 v_call_i_4_3_1;
(*   store i16 %add21.4.3.1, i16* %arrayidx11.4.3.1, align 2, !tbaa !3 *)
mov mem0_38 v_add21_4_3_1;
(*   %arrayidx9.4.4.1 = getelementptr inbounds i16, i16* %r, i64 28 *)
(*   %1048 = load i16, i16* %arrayidx9.4.4.1, align 2, !tbaa !3 *)
mov v1048 mem0_56;
(*   %conv1.i.4.4.1 = sext i16 %1048 to i32 *)
cast v_conv1_i_4_4_1@sint32 v1048@sint16;
(*   %mul.i.4.4.1 = mul nsw i32 %conv1.i.4.4.1, -1325 *)
mul v_mul_i_4_4_1 v_conv1_i_4_4_1 (-1325)@sint32;
(*   %call.i.4.4.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4_1, v_call_i_4_4_1);
(*   %arrayidx11.4.4.1 = getelementptr inbounds i16, i16* %r, i64 20 *)
(*   %1049 = load i16, i16* %arrayidx11.4.4.1, align 2, !tbaa !3 *)
mov v1049 mem0_40;
(*   %sub.4.4.1 = sub i16 %1049, %call.i.4.4.1 *)
sub v_sub_4_4_1 v1049 v_call_i_4_4_1;
(*   store i16 %sub.4.4.1, i16* %arrayidx9.4.4.1, align 2, !tbaa !3 *)
mov mem0_56 v_sub_4_4_1;
(*   %add21.4.4.1 = add i16 %1049, %call.i.4.4.1 *)
add v_add21_4_4_1 v1049 v_call_i_4_4_1;
(*   store i16 %add21.4.4.1, i16* %arrayidx11.4.4.1, align 2, !tbaa !3 *)
mov mem0_40 v_add21_4_4_1;
(*   %arrayidx9.4.5.1 = getelementptr inbounds i16, i16* %r, i64 29 *)
(*   %1050 = load i16, i16* %arrayidx9.4.5.1, align 2, !tbaa !3 *)
mov v1050 mem0_58;
(*   %conv1.i.4.5.1 = sext i16 %1050 to i32 *)
cast v_conv1_i_4_5_1@sint32 v1050@sint16;
(*   %mul.i.4.5.1 = mul nsw i32 %conv1.i.4.5.1, -1325 *)
mul v_mul_i_4_5_1 v_conv1_i_4_5_1 (-1325)@sint32;
(*   %call.i.4.5.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5_1, v_call_i_4_5_1);
(*   %arrayidx11.4.5.1 = getelementptr inbounds i16, i16* %r, i64 21 *)
(*   %1051 = load i16, i16* %arrayidx11.4.5.1, align 2, !tbaa !3 *)
mov v1051 mem0_42;
(*   %sub.4.5.1 = sub i16 %1051, %call.i.4.5.1 *)
sub v_sub_4_5_1 v1051 v_call_i_4_5_1;
(*   store i16 %sub.4.5.1, i16* %arrayidx9.4.5.1, align 2, !tbaa !3 *)
mov mem0_58 v_sub_4_5_1;
(*   %add21.4.5.1 = add i16 %1051, %call.i.4.5.1 *)
add v_add21_4_5_1 v1051 v_call_i_4_5_1;
(*   store i16 %add21.4.5.1, i16* %arrayidx11.4.5.1, align 2, !tbaa !3 *)
mov mem0_42 v_add21_4_5_1;
(*   %arrayidx9.4.6.1 = getelementptr inbounds i16, i16* %r, i64 30 *)
(*   %1052 = load i16, i16* %arrayidx9.4.6.1, align 2, !tbaa !3 *)
mov v1052 mem0_60;
(*   %conv1.i.4.6.1 = sext i16 %1052 to i32 *)
cast v_conv1_i_4_6_1@sint32 v1052@sint16;
(*   %mul.i.4.6.1 = mul nsw i32 %conv1.i.4.6.1, -1325 *)
mul v_mul_i_4_6_1 v_conv1_i_4_6_1 (-1325)@sint32;
(*   %call.i.4.6.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6_1, v_call_i_4_6_1);
(*   %arrayidx11.4.6.1 = getelementptr inbounds i16, i16* %r, i64 22 *)
(*   %1053 = load i16, i16* %arrayidx11.4.6.1, align 2, !tbaa !3 *)
mov v1053 mem0_44;
(*   %sub.4.6.1 = sub i16 %1053, %call.i.4.6.1 *)
sub v_sub_4_6_1 v1053 v_call_i_4_6_1;
(*   store i16 %sub.4.6.1, i16* %arrayidx9.4.6.1, align 2, !tbaa !3 *)
mov mem0_60 v_sub_4_6_1;
(*   %add21.4.6.1 = add i16 %1053, %call.i.4.6.1 *)
add v_add21_4_6_1 v1053 v_call_i_4_6_1;
(*   store i16 %add21.4.6.1, i16* %arrayidx11.4.6.1, align 2, !tbaa !3 *)
mov mem0_44 v_add21_4_6_1;
(*   %arrayidx9.4.7.1 = getelementptr inbounds i16, i16* %r, i64 31 *)
(*   %1054 = load i16, i16* %arrayidx9.4.7.1, align 2, !tbaa !3 *)
mov v1054 mem0_62;
(*   %conv1.i.4.7.1 = sext i16 %1054 to i32 *)
cast v_conv1_i_4_7_1@sint32 v1054@sint16;
(*   %mul.i.4.7.1 = mul nsw i32 %conv1.i.4.7.1, -1325 *)
mul v_mul_i_4_7_1 v_conv1_i_4_7_1 (-1325)@sint32;
(*   %call.i.4.7.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7_1, v_call_i_4_7_1);
(*   %arrayidx11.4.7.1 = getelementptr inbounds i16, i16* %r, i64 23 *)
(*   %1055 = load i16, i16* %arrayidx11.4.7.1, align 2, !tbaa !3 *)
mov v1055 mem0_46;
(*   %sub.4.7.1 = sub i16 %1055, %call.i.4.7.1 *)
sub v_sub_4_7_1 v1055 v_call_i_4_7_1;
(*   store i16 %sub.4.7.1, i16* %arrayidx9.4.7.1, align 2, !tbaa !3 *)
mov mem0_62 v_sub_4_7_1;
(*   %add21.4.7.1 = add i16 %1055, %call.i.4.7.1 *)
add v_add21_4_7_1 v1055 v_call_i_4_7_1;
(*   store i16 %add21.4.7.1, i16* %arrayidx11.4.7.1, align 2, !tbaa !3 *)
mov mem0_46 v_add21_4_7_1;

(* NOTE: k = 18 *)

(*   %arrayidx9.4.2118 = getelementptr inbounds i16, i16* %r, i64 40 *)
(*   %1056 = load i16, i16* %arrayidx9.4.2118, align 2, !tbaa !3 *)
mov v1056 mem0_80;
(*   %conv1.i.4.2119 = sext i16 %1056 to i32 *)
cast v_conv1_i_4_2119@sint32 v1056@sint16;
(*   %mul.i.4.2120 = mul nsw i32 %conv1.i.4.2119, 264 *)
mul v_mul_i_4_2120 v_conv1_i_4_2119 (264)@sint32;
(*   %call.i.4.2121 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2120) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2120, v_call_i_4_2121);
(*   %arrayidx11.4.2122 = getelementptr inbounds i16, i16* %r, i64 32 *)
(*   %1057 = load i16, i16* %arrayidx11.4.2122, align 2, !tbaa !3 *)
mov v1057 mem0_64;
(*   %sub.4.2123 = sub i16 %1057, %call.i.4.2121 *)
sub v_sub_4_2123 v1057 v_call_i_4_2121;
(*   store i16 %sub.4.2123, i16* %arrayidx9.4.2118, align 2, !tbaa !3 *)
mov mem0_80 v_sub_4_2123;
(*   %add21.4.2124 = add i16 %1057, %call.i.4.2121 *)
add v_add21_4_2124 v1057 v_call_i_4_2121;
(*   store i16 %add21.4.2124, i16* %arrayidx11.4.2122, align 2, !tbaa !3 *)
mov mem0_64 v_add21_4_2124;
(*   %arrayidx9.4.1.2 = getelementptr inbounds i16, i16* %r, i64 41 *)
(*   %1058 = load i16, i16* %arrayidx9.4.1.2, align 2, !tbaa !3 *)
mov v1058 mem0_82;
(*   %conv1.i.4.1.2 = sext i16 %1058 to i32 *)
cast v_conv1_i_4_1_2@sint32 v1058@sint16;
(*   %mul.i.4.1.2 = mul nsw i32 %conv1.i.4.1.2, 264 *)
mul v_mul_i_4_1_2 v_conv1_i_4_1_2 (264)@sint32;
(*   %call.i.4.1.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1_2, v_call_i_4_1_2);
(*   %arrayidx11.4.1.2 = getelementptr inbounds i16, i16* %r, i64 33 *)
(*   %1059 = load i16, i16* %arrayidx11.4.1.2, align 2, !tbaa !3 *)
mov v1059 mem0_66;
(*   %sub.4.1.2 = sub i16 %1059, %call.i.4.1.2 *)
sub v_sub_4_1_2 v1059 v_call_i_4_1_2;
(*   store i16 %sub.4.1.2, i16* %arrayidx9.4.1.2, align 2, !tbaa !3 *)
mov mem0_82 v_sub_4_1_2;
(*   %add21.4.1.2 = add i16 %1059, %call.i.4.1.2 *)
add v_add21_4_1_2 v1059 v_call_i_4_1_2;
(*   store i16 %add21.4.1.2, i16* %arrayidx11.4.1.2, align 2, !tbaa !3 *)
mov mem0_66 v_add21_4_1_2;
(*   %arrayidx9.4.2.2 = getelementptr inbounds i16, i16* %r, i64 42 *)
(*   %1060 = load i16, i16* %arrayidx9.4.2.2, align 2, !tbaa !3 *)
mov v1060 mem0_84;
(*   %conv1.i.4.2.2 = sext i16 %1060 to i32 *)
cast v_conv1_i_4_2_2@sint32 v1060@sint16;
(*   %mul.i.4.2.2 = mul nsw i32 %conv1.i.4.2.2, 264 *)
mul v_mul_i_4_2_2 v_conv1_i_4_2_2 (264)@sint32;
(*   %call.i.4.2.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2_2, v_call_i_4_2_2);
(*   %arrayidx11.4.2.2 = getelementptr inbounds i16, i16* %r, i64 34 *)
(*   %1061 = load i16, i16* %arrayidx11.4.2.2, align 2, !tbaa !3 *)
mov v1061 mem0_68;
(*   %sub.4.2.2 = sub i16 %1061, %call.i.4.2.2 *)
sub v_sub_4_2_2 v1061 v_call_i_4_2_2;
(*   store i16 %sub.4.2.2, i16* %arrayidx9.4.2.2, align 2, !tbaa !3 *)
mov mem0_84 v_sub_4_2_2;
(*   %add21.4.2.2 = add i16 %1061, %call.i.4.2.2 *)
add v_add21_4_2_2 v1061 v_call_i_4_2_2;
(*   store i16 %add21.4.2.2, i16* %arrayidx11.4.2.2, align 2, !tbaa !3 *)
mov mem0_68 v_add21_4_2_2;
(*   %arrayidx9.4.3.2 = getelementptr inbounds i16, i16* %r, i64 43 *)
(*   %1062 = load i16, i16* %arrayidx9.4.3.2, align 2, !tbaa !3 *)
mov v1062 mem0_86;
(*   %conv1.i.4.3.2 = sext i16 %1062 to i32 *)
cast v_conv1_i_4_3_2@sint32 v1062@sint16;
(*   %mul.i.4.3.2 = mul nsw i32 %conv1.i.4.3.2, 264 *)
mul v_mul_i_4_3_2 v_conv1_i_4_3_2 (264)@sint32;
(*   %call.i.4.3.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3_2, v_call_i_4_3_2);
(*   %arrayidx11.4.3.2 = getelementptr inbounds i16, i16* %r, i64 35 *)
(*   %1063 = load i16, i16* %arrayidx11.4.3.2, align 2, !tbaa !3 *)
mov v1063 mem0_70;
(*   %sub.4.3.2 = sub i16 %1063, %call.i.4.3.2 *)
sub v_sub_4_3_2 v1063 v_call_i_4_3_2;
(*   store i16 %sub.4.3.2, i16* %arrayidx9.4.3.2, align 2, !tbaa !3 *)
mov mem0_86 v_sub_4_3_2;
(*   %add21.4.3.2 = add i16 %1063, %call.i.4.3.2 *)
add v_add21_4_3_2 v1063 v_call_i_4_3_2;
(*   store i16 %add21.4.3.2, i16* %arrayidx11.4.3.2, align 2, !tbaa !3 *)
mov mem0_70 v_add21_4_3_2;
(*   %arrayidx9.4.4.2 = getelementptr inbounds i16, i16* %r, i64 44 *)
(*   %1064 = load i16, i16* %arrayidx9.4.4.2, align 2, !tbaa !3 *)
mov v1064 mem0_88;
(*   %conv1.i.4.4.2 = sext i16 %1064 to i32 *)
cast v_conv1_i_4_4_2@sint32 v1064@sint16;
(*   %mul.i.4.4.2 = mul nsw i32 %conv1.i.4.4.2, 264 *)
mul v_mul_i_4_4_2 v_conv1_i_4_4_2 (264)@sint32;
(*   %call.i.4.4.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4_2, v_call_i_4_4_2);
(*   %arrayidx11.4.4.2 = getelementptr inbounds i16, i16* %r, i64 36 *)
(*   %1065 = load i16, i16* %arrayidx11.4.4.2, align 2, !tbaa !3 *)
mov v1065 mem0_72;
(*   %sub.4.4.2 = sub i16 %1065, %call.i.4.4.2 *)
sub v_sub_4_4_2 v1065 v_call_i_4_4_2;
(*   store i16 %sub.4.4.2, i16* %arrayidx9.4.4.2, align 2, !tbaa !3 *)
mov mem0_88 v_sub_4_4_2;
(*   %add21.4.4.2 = add i16 %1065, %call.i.4.4.2 *)
add v_add21_4_4_2 v1065 v_call_i_4_4_2;
(*   store i16 %add21.4.4.2, i16* %arrayidx11.4.4.2, align 2, !tbaa !3 *)
mov mem0_72 v_add21_4_4_2;
(*   %arrayidx9.4.5.2 = getelementptr inbounds i16, i16* %r, i64 45 *)
(*   %1066 = load i16, i16* %arrayidx9.4.5.2, align 2, !tbaa !3 *)
mov v1066 mem0_90;
(*   %conv1.i.4.5.2 = sext i16 %1066 to i32 *)
cast v_conv1_i_4_5_2@sint32 v1066@sint16;
(*   %mul.i.4.5.2 = mul nsw i32 %conv1.i.4.5.2, 264 *)
mul v_mul_i_4_5_2 v_conv1_i_4_5_2 (264)@sint32;
(*   %call.i.4.5.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5_2, v_call_i_4_5_2);
(*   %arrayidx11.4.5.2 = getelementptr inbounds i16, i16* %r, i64 37 *)
(*   %1067 = load i16, i16* %arrayidx11.4.5.2, align 2, !tbaa !3 *)
mov v1067 mem0_74;
(*   %sub.4.5.2 = sub i16 %1067, %call.i.4.5.2 *)
sub v_sub_4_5_2 v1067 v_call_i_4_5_2;
(*   store i16 %sub.4.5.2, i16* %arrayidx9.4.5.2, align 2, !tbaa !3 *)
mov mem0_90 v_sub_4_5_2;
(*   %add21.4.5.2 = add i16 %1067, %call.i.4.5.2 *)
add v_add21_4_5_2 v1067 v_call_i_4_5_2;
(*   store i16 %add21.4.5.2, i16* %arrayidx11.4.5.2, align 2, !tbaa !3 *)
mov mem0_74 v_add21_4_5_2;
(*   %arrayidx9.4.6.2 = getelementptr inbounds i16, i16* %r, i64 46 *)
(*   %1068 = load i16, i16* %arrayidx9.4.6.2, align 2, !tbaa !3 *)
mov v1068 mem0_92;
(*   %conv1.i.4.6.2 = sext i16 %1068 to i32 *)
cast v_conv1_i_4_6_2@sint32 v1068@sint16;
(*   %mul.i.4.6.2 = mul nsw i32 %conv1.i.4.6.2, 264 *)
mul v_mul_i_4_6_2 v_conv1_i_4_6_2 (264)@sint32;
(*   %call.i.4.6.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6_2, v_call_i_4_6_2);
(*   %arrayidx11.4.6.2 = getelementptr inbounds i16, i16* %r, i64 38 *)
(*   %1069 = load i16, i16* %arrayidx11.4.6.2, align 2, !tbaa !3 *)
mov v1069 mem0_76;
(*   %sub.4.6.2 = sub i16 %1069, %call.i.4.6.2 *)
sub v_sub_4_6_2 v1069 v_call_i_4_6_2;
(*   store i16 %sub.4.6.2, i16* %arrayidx9.4.6.2, align 2, !tbaa !3 *)
mov mem0_92 v_sub_4_6_2;
(*   %add21.4.6.2 = add i16 %1069, %call.i.4.6.2 *)
add v_add21_4_6_2 v1069 v_call_i_4_6_2;
(*   store i16 %add21.4.6.2, i16* %arrayidx11.4.6.2, align 2, !tbaa !3 *)
mov mem0_76 v_add21_4_6_2;
(*   %arrayidx9.4.7.2 = getelementptr inbounds i16, i16* %r, i64 47 *)
(*   %1070 = load i16, i16* %arrayidx9.4.7.2, align 2, !tbaa !3 *)
mov v1070 mem0_94;
(*   %conv1.i.4.7.2 = sext i16 %1070 to i32 *)
cast v_conv1_i_4_7_2@sint32 v1070@sint16;
(*   %mul.i.4.7.2 = mul nsw i32 %conv1.i.4.7.2, 264 *)
mul v_mul_i_4_7_2 v_conv1_i_4_7_2 (264)@sint32;
(*   %call.i.4.7.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7_2, v_call_i_4_7_2);
(*   %arrayidx11.4.7.2 = getelementptr inbounds i16, i16* %r, i64 39 *)
(*   %1071 = load i16, i16* %arrayidx11.4.7.2, align 2, !tbaa !3 *)
mov v1071 mem0_78;
(*   %sub.4.7.2 = sub i16 %1071, %call.i.4.7.2 *)
sub v_sub_4_7_2 v1071 v_call_i_4_7_2;
(*   store i16 %sub.4.7.2, i16* %arrayidx9.4.7.2, align 2, !tbaa !3 *)
mov mem0_94 v_sub_4_7_2;
(*   %add21.4.7.2 = add i16 %1071, %call.i.4.7.2 *)
add v_add21_4_7_2 v1071 v_call_i_4_7_2;
(*   store i16 %add21.4.7.2, i16* %arrayidx11.4.7.2, align 2, !tbaa !3 *)
mov mem0_78 v_add21_4_7_2;

(* NOTE: k = 19 *)

(*   %arrayidx9.4.3128 = getelementptr inbounds i16, i16* %r, i64 56 *)
(*   %1072 = load i16, i16* %arrayidx9.4.3128, align 2, !tbaa !3 *)
mov v1072 mem0_112;
(*   %conv1.i.4.3129 = sext i16 %1072 to i32 *)
cast v_conv1_i_4_3129@sint32 v1072@sint16;
(*   %mul.i.4.3130 = mul nsw i32 %conv1.i.4.3129, 383 *)
mul v_mul_i_4_3130 v_conv1_i_4_3129 (383)@sint32;
(*   %call.i.4.3131 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3130) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3130, v_call_i_4_3131);
(*   %arrayidx11.4.3132 = getelementptr inbounds i16, i16* %r, i64 48 *)
(*   %1073 = load i16, i16* %arrayidx11.4.3132, align 2, !tbaa !3 *)
mov v1073 mem0_96;
(*   %sub.4.3133 = sub i16 %1073, %call.i.4.3131 *)
sub v_sub_4_3133 v1073 v_call_i_4_3131;
(*   store i16 %sub.4.3133, i16* %arrayidx9.4.3128, align 2, !tbaa !3 *)
mov mem0_112 v_sub_4_3133;
(*   %add21.4.3134 = add i16 %1073, %call.i.4.3131 *)
add v_add21_4_3134 v1073 v_call_i_4_3131;
(*   store i16 %add21.4.3134, i16* %arrayidx11.4.3132, align 2, !tbaa !3 *)
mov mem0_96 v_add21_4_3134;
(*   %arrayidx9.4.1.3 = getelementptr inbounds i16, i16* %r, i64 57 *)
(*   %1074 = load i16, i16* %arrayidx9.4.1.3, align 2, !tbaa !3 *)
mov v1074 mem0_114;
(*   %conv1.i.4.1.3 = sext i16 %1074 to i32 *)
cast v_conv1_i_4_1_3@sint32 v1074@sint16;
(*   %mul.i.4.1.3 = mul nsw i32 %conv1.i.4.1.3, 383 *)
mul v_mul_i_4_1_3 v_conv1_i_4_1_3 (383)@sint32;
(*   %call.i.4.1.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1_3, v_call_i_4_1_3);
(*   %arrayidx11.4.1.3 = getelementptr inbounds i16, i16* %r, i64 49 *)
(*   %1075 = load i16, i16* %arrayidx11.4.1.3, align 2, !tbaa !3 *)
mov v1075 mem0_98;
(*   %sub.4.1.3 = sub i16 %1075, %call.i.4.1.3 *)
sub v_sub_4_1_3 v1075 v_call_i_4_1_3;
(*   store i16 %sub.4.1.3, i16* %arrayidx9.4.1.3, align 2, !tbaa !3 *)
mov mem0_114 v_sub_4_1_3;
(*   %add21.4.1.3 = add i16 %1075, %call.i.4.1.3 *)
add v_add21_4_1_3 v1075 v_call_i_4_1_3;
(*   store i16 %add21.4.1.3, i16* %arrayidx11.4.1.3, align 2, !tbaa !3 *)
mov mem0_98 v_add21_4_1_3;
(*   %arrayidx9.4.2.3 = getelementptr inbounds i16, i16* %r, i64 58 *)
(*   %1076 = load i16, i16* %arrayidx9.4.2.3, align 2, !tbaa !3 *)
mov v1076 mem0_116;
(*   %conv1.i.4.2.3 = sext i16 %1076 to i32 *)
cast v_conv1_i_4_2_3@sint32 v1076@sint16;
(*   %mul.i.4.2.3 = mul nsw i32 %conv1.i.4.2.3, 383 *)
mul v_mul_i_4_2_3 v_conv1_i_4_2_3 (383)@sint32;
(*   %call.i.4.2.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2_3, v_call_i_4_2_3);
(*   %arrayidx11.4.2.3 = getelementptr inbounds i16, i16* %r, i64 50 *)
(*   %1077 = load i16, i16* %arrayidx11.4.2.3, align 2, !tbaa !3 *)
mov v1077 mem0_100;
(*   %sub.4.2.3 = sub i16 %1077, %call.i.4.2.3 *)
sub v_sub_4_2_3 v1077 v_call_i_4_2_3;
(*   store i16 %sub.4.2.3, i16* %arrayidx9.4.2.3, align 2, !tbaa !3 *)
mov mem0_116 v_sub_4_2_3;
(*   %add21.4.2.3 = add i16 %1077, %call.i.4.2.3 *)
add v_add21_4_2_3 v1077 v_call_i_4_2_3;
(*   store i16 %add21.4.2.3, i16* %arrayidx11.4.2.3, align 2, !tbaa !3 *)
mov mem0_100 v_add21_4_2_3;
(*   %arrayidx9.4.3.3 = getelementptr inbounds i16, i16* %r, i64 59 *)
(*   %1078 = load i16, i16* %arrayidx9.4.3.3, align 2, !tbaa !3 *)
mov v1078 mem0_118;
(*   %conv1.i.4.3.3 = sext i16 %1078 to i32 *)
cast v_conv1_i_4_3_3@sint32 v1078@sint16;
(*   %mul.i.4.3.3 = mul nsw i32 %conv1.i.4.3.3, 383 *)
mul v_mul_i_4_3_3 v_conv1_i_4_3_3 (383)@sint32;
(*   %call.i.4.3.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3_3, v_call_i_4_3_3);
(*   %arrayidx11.4.3.3 = getelementptr inbounds i16, i16* %r, i64 51 *)
(*   %1079 = load i16, i16* %arrayidx11.4.3.3, align 2, !tbaa !3 *)
mov v1079 mem0_102;
(*   %sub.4.3.3 = sub i16 %1079, %call.i.4.3.3 *)
sub v_sub_4_3_3 v1079 v_call_i_4_3_3;
(*   store i16 %sub.4.3.3, i16* %arrayidx9.4.3.3, align 2, !tbaa !3 *)
mov mem0_118 v_sub_4_3_3;
(*   %add21.4.3.3 = add i16 %1079, %call.i.4.3.3 *)
add v_add21_4_3_3 v1079 v_call_i_4_3_3;
(*   store i16 %add21.4.3.3, i16* %arrayidx11.4.3.3, align 2, !tbaa !3 *)
mov mem0_102 v_add21_4_3_3;
(*   %arrayidx9.4.4.3 = getelementptr inbounds i16, i16* %r, i64 60 *)
(*   %1080 = load i16, i16* %arrayidx9.4.4.3, align 2, !tbaa !3 *)
mov v1080 mem0_120;
(*   %conv1.i.4.4.3 = sext i16 %1080 to i32 *)
cast v_conv1_i_4_4_3@sint32 v1080@sint16;
(*   %mul.i.4.4.3 = mul nsw i32 %conv1.i.4.4.3, 383 *)
mul v_mul_i_4_4_3 v_conv1_i_4_4_3 (383)@sint32;
(*   %call.i.4.4.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4_3, v_call_i_4_4_3);
(*   %arrayidx11.4.4.3 = getelementptr inbounds i16, i16* %r, i64 52 *)
(*   %1081 = load i16, i16* %arrayidx11.4.4.3, align 2, !tbaa !3 *)
mov v1081 mem0_104;
(*   %sub.4.4.3 = sub i16 %1081, %call.i.4.4.3 *)
sub v_sub_4_4_3 v1081 v_call_i_4_4_3;
(*   store i16 %sub.4.4.3, i16* %arrayidx9.4.4.3, align 2, !tbaa !3 *)
mov mem0_120 v_sub_4_4_3;
(*   %add21.4.4.3 = add i16 %1081, %call.i.4.4.3 *)
add v_add21_4_4_3 v1081 v_call_i_4_4_3;
(*   store i16 %add21.4.4.3, i16* %arrayidx11.4.4.3, align 2, !tbaa !3 *)
mov mem0_104 v_add21_4_4_3;
(*   %arrayidx9.4.5.3 = getelementptr inbounds i16, i16* %r, i64 61 *)
(*   %1082 = load i16, i16* %arrayidx9.4.5.3, align 2, !tbaa !3 *)
mov v1082 mem0_122;
(*   %conv1.i.4.5.3 = sext i16 %1082 to i32 *)
cast v_conv1_i_4_5_3@sint32 v1082@sint16;
(*   %mul.i.4.5.3 = mul nsw i32 %conv1.i.4.5.3, 383 *)
mul v_mul_i_4_5_3 v_conv1_i_4_5_3 (383)@sint32;
(*   %call.i.4.5.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5_3, v_call_i_4_5_3);
(*   %arrayidx11.4.5.3 = getelementptr inbounds i16, i16* %r, i64 53 *)
(*   %1083 = load i16, i16* %arrayidx11.4.5.3, align 2, !tbaa !3 *)
mov v1083 mem0_106;
(*   %sub.4.5.3 = sub i16 %1083, %call.i.4.5.3 *)
sub v_sub_4_5_3 v1083 v_call_i_4_5_3;
(*   store i16 %sub.4.5.3, i16* %arrayidx9.4.5.3, align 2, !tbaa !3 *)
mov mem0_122 v_sub_4_5_3;
(*   %add21.4.5.3 = add i16 %1083, %call.i.4.5.3 *)
add v_add21_4_5_3 v1083 v_call_i_4_5_3;
(*   store i16 %add21.4.5.3, i16* %arrayidx11.4.5.3, align 2, !tbaa !3 *)
mov mem0_106 v_add21_4_5_3;
(*   %arrayidx9.4.6.3 = getelementptr inbounds i16, i16* %r, i64 62 *)
(*   %1084 = load i16, i16* %arrayidx9.4.6.3, align 2, !tbaa !3 *)
mov v1084 mem0_124;
(*   %conv1.i.4.6.3 = sext i16 %1084 to i32 *)
cast v_conv1_i_4_6_3@sint32 v1084@sint16;
(*   %mul.i.4.6.3 = mul nsw i32 %conv1.i.4.6.3, 383 *)
mul v_mul_i_4_6_3 v_conv1_i_4_6_3 (383)@sint32;
(*   %call.i.4.6.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6_3, v_call_i_4_6_3);
(*   %arrayidx11.4.6.3 = getelementptr inbounds i16, i16* %r, i64 54 *)
(*   %1085 = load i16, i16* %arrayidx11.4.6.3, align 2, !tbaa !3 *)
mov v1085 mem0_108;
(*   %sub.4.6.3 = sub i16 %1085, %call.i.4.6.3 *)
sub v_sub_4_6_3 v1085 v_call_i_4_6_3;
(*   store i16 %sub.4.6.3, i16* %arrayidx9.4.6.3, align 2, !tbaa !3 *)
mov mem0_124 v_sub_4_6_3;
(*   %add21.4.6.3 = add i16 %1085, %call.i.4.6.3 *)
add v_add21_4_6_3 v1085 v_call_i_4_6_3;
(*   store i16 %add21.4.6.3, i16* %arrayidx11.4.6.3, align 2, !tbaa !3 *)
mov mem0_108 v_add21_4_6_3;
(*   %arrayidx9.4.7.3 = getelementptr inbounds i16, i16* %r, i64 63 *)
(*   %1086 = load i16, i16* %arrayidx9.4.7.3, align 2, !tbaa !3 *)
mov v1086 mem0_126;
(*   %conv1.i.4.7.3 = sext i16 %1086 to i32 *)
cast v_conv1_i_4_7_3@sint32 v1086@sint16;
(*   %mul.i.4.7.3 = mul nsw i32 %conv1.i.4.7.3, 383 *)
mul v_mul_i_4_7_3 v_conv1_i_4_7_3 (383)@sint32;
(*   %call.i.4.7.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7_3, v_call_i_4_7_3);
(*   %arrayidx11.4.7.3 = getelementptr inbounds i16, i16* %r, i64 55 *)
(*   %1087 = load i16, i16* %arrayidx11.4.7.3, align 2, !tbaa !3 *)
mov v1087 mem0_110;
(*   %sub.4.7.3 = sub i16 %1087, %call.i.4.7.3 *)
sub v_sub_4_7_3 v1087 v_call_i_4_7_3;
(*   store i16 %sub.4.7.3, i16* %arrayidx9.4.7.3, align 2, !tbaa !3 *)
mov mem0_126 v_sub_4_7_3;
(*   %add21.4.7.3 = add i16 %1087, %call.i.4.7.3 *)
add v_add21_4_7_3 v1087 v_call_i_4_7_3;
(*   store i16 %add21.4.7.3, i16* %arrayidx11.4.7.3, align 2, !tbaa !3 *)
mov mem0_110 v_add21_4_7_3;

(* NOTE: k = 20 *)

(*   %arrayidx9.4.4138 = getelementptr inbounds i16, i16* %r, i64 72 *)
(*   %1088 = load i16, i16* %arrayidx9.4.4138, align 2, !tbaa !3 *)
mov v1088 mem0_144;
(*   %conv1.i.4.4139 = sext i16 %1088 to i32 *)
cast v_conv1_i_4_4139@sint32 v1088@sint16;
(*   %mul.i.4.4140 = mul nsw i32 %conv1.i.4.4139, -829 *)
mul v_mul_i_4_4140 v_conv1_i_4_4139 (-829)@sint32;
(*   %call.i.4.4141 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4140) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4140, v_call_i_4_4141);
(*   %arrayidx11.4.4142 = getelementptr inbounds i16, i16* %r, i64 64 *)
(*   %1089 = load i16, i16* %arrayidx11.4.4142, align 2, !tbaa !3 *)
mov v1089 mem0_128;
(*   %sub.4.4143 = sub i16 %1089, %call.i.4.4141 *)
sub v_sub_4_4143 v1089 v_call_i_4_4141;
(*   store i16 %sub.4.4143, i16* %arrayidx9.4.4138, align 2, !tbaa !3 *)
mov mem0_144 v_sub_4_4143;
(*   %add21.4.4144 = add i16 %1089, %call.i.4.4141 *)
add v_add21_4_4144 v1089 v_call_i_4_4141;
(*   store i16 %add21.4.4144, i16* %arrayidx11.4.4142, align 2, !tbaa !3 *)
mov mem0_128 v_add21_4_4144;
(*   %arrayidx9.4.1.4 = getelementptr inbounds i16, i16* %r, i64 73 *)
(*   %1090 = load i16, i16* %arrayidx9.4.1.4, align 2, !tbaa !3 *)
mov v1090 mem0_146;
(*   %conv1.i.4.1.4 = sext i16 %1090 to i32 *)
cast v_conv1_i_4_1_4@sint32 v1090@sint16;
(*   %mul.i.4.1.4 = mul nsw i32 %conv1.i.4.1.4, -829 *)
mul v_mul_i_4_1_4 v_conv1_i_4_1_4 (-829)@sint32;
(*   %call.i.4.1.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1_4, v_call_i_4_1_4);
(*   %arrayidx11.4.1.4 = getelementptr inbounds i16, i16* %r, i64 65 *)
(*   %1091 = load i16, i16* %arrayidx11.4.1.4, align 2, !tbaa !3 *)
mov v1091 mem0_130;
(*   %sub.4.1.4 = sub i16 %1091, %call.i.4.1.4 *)
sub v_sub_4_1_4 v1091 v_call_i_4_1_4;
(*   store i16 %sub.4.1.4, i16* %arrayidx9.4.1.4, align 2, !tbaa !3 *)
mov mem0_146 v_sub_4_1_4;
(*   %add21.4.1.4 = add i16 %1091, %call.i.4.1.4 *)
add v_add21_4_1_4 v1091 v_call_i_4_1_4;
(*   store i16 %add21.4.1.4, i16* %arrayidx11.4.1.4, align 2, !tbaa !3 *)
mov mem0_130 v_add21_4_1_4;
(*   %arrayidx9.4.2.4 = getelementptr inbounds i16, i16* %r, i64 74 *)
(*   %1092 = load i16, i16* %arrayidx9.4.2.4, align 2, !tbaa !3 *)
mov v1092 mem0_148;
(*   %conv1.i.4.2.4 = sext i16 %1092 to i32 *)
cast v_conv1_i_4_2_4@sint32 v1092@sint16;
(*   %mul.i.4.2.4 = mul nsw i32 %conv1.i.4.2.4, -829 *)
mul v_mul_i_4_2_4 v_conv1_i_4_2_4 (-829)@sint32;
(*   %call.i.4.2.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2_4, v_call_i_4_2_4);
(*   %arrayidx11.4.2.4 = getelementptr inbounds i16, i16* %r, i64 66 *)
(*   %1093 = load i16, i16* %arrayidx11.4.2.4, align 2, !tbaa !3 *)
mov v1093 mem0_132;
(*   %sub.4.2.4 = sub i16 %1093, %call.i.4.2.4 *)
sub v_sub_4_2_4 v1093 v_call_i_4_2_4;
(*   store i16 %sub.4.2.4, i16* %arrayidx9.4.2.4, align 2, !tbaa !3 *)
mov mem0_148 v_sub_4_2_4;
(*   %add21.4.2.4 = add i16 %1093, %call.i.4.2.4 *)
add v_add21_4_2_4 v1093 v_call_i_4_2_4;
(*   store i16 %add21.4.2.4, i16* %arrayidx11.4.2.4, align 2, !tbaa !3 *)
mov mem0_132 v_add21_4_2_4;
(*   %arrayidx9.4.3.4 = getelementptr inbounds i16, i16* %r, i64 75 *)
(*   %1094 = load i16, i16* %arrayidx9.4.3.4, align 2, !tbaa !3 *)
mov v1094 mem0_150;
(*   %conv1.i.4.3.4 = sext i16 %1094 to i32 *)
cast v_conv1_i_4_3_4@sint32 v1094@sint16;
(*   %mul.i.4.3.4 = mul nsw i32 %conv1.i.4.3.4, -829 *)
mul v_mul_i_4_3_4 v_conv1_i_4_3_4 (-829)@sint32;
(*   %call.i.4.3.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3_4, v_call_i_4_3_4);
(*   %arrayidx11.4.3.4 = getelementptr inbounds i16, i16* %r, i64 67 *)
(*   %1095 = load i16, i16* %arrayidx11.4.3.4, align 2, !tbaa !3 *)
mov v1095 mem0_134;
(*   %sub.4.3.4 = sub i16 %1095, %call.i.4.3.4 *)
sub v_sub_4_3_4 v1095 v_call_i_4_3_4;
(*   store i16 %sub.4.3.4, i16* %arrayidx9.4.3.4, align 2, !tbaa !3 *)
mov mem0_150 v_sub_4_3_4;
(*   %add21.4.3.4 = add i16 %1095, %call.i.4.3.4 *)
add v_add21_4_3_4 v1095 v_call_i_4_3_4;
(*   store i16 %add21.4.3.4, i16* %arrayidx11.4.3.4, align 2, !tbaa !3 *)
mov mem0_134 v_add21_4_3_4;
(*   %arrayidx9.4.4.4 = getelementptr inbounds i16, i16* %r, i64 76 *)
(*   %1096 = load i16, i16* %arrayidx9.4.4.4, align 2, !tbaa !3 *)
mov v1096 mem0_152;
(*   %conv1.i.4.4.4 = sext i16 %1096 to i32 *)
cast v_conv1_i_4_4_4@sint32 v1096@sint16;
(*   %mul.i.4.4.4 = mul nsw i32 %conv1.i.4.4.4, -829 *)
mul v_mul_i_4_4_4 v_conv1_i_4_4_4 (-829)@sint32;
(*   %call.i.4.4.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4_4, v_call_i_4_4_4);
(*   %arrayidx11.4.4.4 = getelementptr inbounds i16, i16* %r, i64 68 *)
(*   %1097 = load i16, i16* %arrayidx11.4.4.4, align 2, !tbaa !3 *)
mov v1097 mem0_136;
(*   %sub.4.4.4 = sub i16 %1097, %call.i.4.4.4 *)
sub v_sub_4_4_4 v1097 v_call_i_4_4_4;
(*   store i16 %sub.4.4.4, i16* %arrayidx9.4.4.4, align 2, !tbaa !3 *)
mov mem0_152 v_sub_4_4_4;
(*   %add21.4.4.4 = add i16 %1097, %call.i.4.4.4 *)
add v_add21_4_4_4 v1097 v_call_i_4_4_4;
(*   store i16 %add21.4.4.4, i16* %arrayidx11.4.4.4, align 2, !tbaa !3 *)
mov mem0_136 v_add21_4_4_4;
(*   %arrayidx9.4.5.4 = getelementptr inbounds i16, i16* %r, i64 77 *)
(*   %1098 = load i16, i16* %arrayidx9.4.5.4, align 2, !tbaa !3 *)
mov v1098 mem0_154;
(*   %conv1.i.4.5.4 = sext i16 %1098 to i32 *)
cast v_conv1_i_4_5_4@sint32 v1098@sint16;
(*   %mul.i.4.5.4 = mul nsw i32 %conv1.i.4.5.4, -829 *)
mul v_mul_i_4_5_4 v_conv1_i_4_5_4 (-829)@sint32;
(*   %call.i.4.5.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5_4, v_call_i_4_5_4);
(*   %arrayidx11.4.5.4 = getelementptr inbounds i16, i16* %r, i64 69 *)
(*   %1099 = load i16, i16* %arrayidx11.4.5.4, align 2, !tbaa !3 *)
mov v1099 mem0_138;
(*   %sub.4.5.4 = sub i16 %1099, %call.i.4.5.4 *)
sub v_sub_4_5_4 v1099 v_call_i_4_5_4;
(*   store i16 %sub.4.5.4, i16* %arrayidx9.4.5.4, align 2, !tbaa !3 *)
mov mem0_154 v_sub_4_5_4;
(*   %add21.4.5.4 = add i16 %1099, %call.i.4.5.4 *)
add v_add21_4_5_4 v1099 v_call_i_4_5_4;
(*   store i16 %add21.4.5.4, i16* %arrayidx11.4.5.4, align 2, !tbaa !3 *)
mov mem0_138 v_add21_4_5_4;
(*   %arrayidx9.4.6.4 = getelementptr inbounds i16, i16* %r, i64 78 *)
(*   %1100 = load i16, i16* %arrayidx9.4.6.4, align 2, !tbaa !3 *)
mov v1100 mem0_156;
(*   %conv1.i.4.6.4 = sext i16 %1100 to i32 *)
cast v_conv1_i_4_6_4@sint32 v1100@sint16;
(*   %mul.i.4.6.4 = mul nsw i32 %conv1.i.4.6.4, -829 *)
mul v_mul_i_4_6_4 v_conv1_i_4_6_4 (-829)@sint32;
(*   %call.i.4.6.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6_4, v_call_i_4_6_4);
(*   %arrayidx11.4.6.4 = getelementptr inbounds i16, i16* %r, i64 70 *)
(*   %1101 = load i16, i16* %arrayidx11.4.6.4, align 2, !tbaa !3 *)
mov v1101 mem0_140;
(*   %sub.4.6.4 = sub i16 %1101, %call.i.4.6.4 *)
sub v_sub_4_6_4 v1101 v_call_i_4_6_4;
(*   store i16 %sub.4.6.4, i16* %arrayidx9.4.6.4, align 2, !tbaa !3 *)
mov mem0_156 v_sub_4_6_4;
(*   %add21.4.6.4 = add i16 %1101, %call.i.4.6.4 *)
add v_add21_4_6_4 v1101 v_call_i_4_6_4;
(*   store i16 %add21.4.6.4, i16* %arrayidx11.4.6.4, align 2, !tbaa !3 *)
mov mem0_140 v_add21_4_6_4;
(*   %arrayidx9.4.7.4 = getelementptr inbounds i16, i16* %r, i64 79 *)
(*   %1102 = load i16, i16* %arrayidx9.4.7.4, align 2, !tbaa !3 *)
mov v1102 mem0_158;
(*   %conv1.i.4.7.4 = sext i16 %1102 to i32 *)
cast v_conv1_i_4_7_4@sint32 v1102@sint16;
(*   %mul.i.4.7.4 = mul nsw i32 %conv1.i.4.7.4, -829 *)
mul v_mul_i_4_7_4 v_conv1_i_4_7_4 (-829)@sint32;
(*   %call.i.4.7.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7_4, v_call_i_4_7_4);
(*   %arrayidx11.4.7.4 = getelementptr inbounds i16, i16* %r, i64 71 *)
(*   %1103 = load i16, i16* %arrayidx11.4.7.4, align 2, !tbaa !3 *)
mov v1103 mem0_142;
(*   %sub.4.7.4 = sub i16 %1103, %call.i.4.7.4 *)
sub v_sub_4_7_4 v1103 v_call_i_4_7_4;
(*   store i16 %sub.4.7.4, i16* %arrayidx9.4.7.4, align 2, !tbaa !3 *)
mov mem0_158 v_sub_4_7_4;
(*   %add21.4.7.4 = add i16 %1103, %call.i.4.7.4 *)
add v_add21_4_7_4 v1103 v_call_i_4_7_4;
(*   store i16 %add21.4.7.4, i16* %arrayidx11.4.7.4, align 2, !tbaa !3 *)
mov mem0_142 v_add21_4_7_4;

(* NOTE: k = 21 *)

(*   %arrayidx9.4.5148 = getelementptr inbounds i16, i16* %r, i64 88 *)
(*   %1104 = load i16, i16* %arrayidx9.4.5148, align 2, !tbaa !3 *)
mov v1104 mem0_176;
(*   %conv1.i.4.5149 = sext i16 %1104 to i32 *)
cast v_conv1_i_4_5149@sint32 v1104@sint16;
(*   %mul.i.4.5150 = mul nsw i32 %conv1.i.4.5149, 1458 *)
mul v_mul_i_4_5150 v_conv1_i_4_5149 (1458)@sint32;
(*   %call.i.4.5151 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5150) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5150, v_call_i_4_5151);
(*   %arrayidx11.4.5152 = getelementptr inbounds i16, i16* %r, i64 80 *)
(*   %1105 = load i16, i16* %arrayidx11.4.5152, align 2, !tbaa !3 *)
mov v1105 mem0_160;
(*   %sub.4.5153 = sub i16 %1105, %call.i.4.5151 *)
sub v_sub_4_5153 v1105 v_call_i_4_5151;
(*   store i16 %sub.4.5153, i16* %arrayidx9.4.5148, align 2, !tbaa !3 *)
mov mem0_176 v_sub_4_5153;
(*   %add21.4.5154 = add i16 %1105, %call.i.4.5151 *)
add v_add21_4_5154 v1105 v_call_i_4_5151;
(*   store i16 %add21.4.5154, i16* %arrayidx11.4.5152, align 2, !tbaa !3 *)
mov mem0_160 v_add21_4_5154;
(*   %arrayidx9.4.1.5 = getelementptr inbounds i16, i16* %r, i64 89 *)
(*   %1106 = load i16, i16* %arrayidx9.4.1.5, align 2, !tbaa !3 *)
mov v1106 mem0_178;
(*   %conv1.i.4.1.5 = sext i16 %1106 to i32 *)
cast v_conv1_i_4_1_5@sint32 v1106@sint16;
(*   %mul.i.4.1.5 = mul nsw i32 %conv1.i.4.1.5, 1458 *)
mul v_mul_i_4_1_5 v_conv1_i_4_1_5 (1458)@sint32;
(*   %call.i.4.1.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1_5, v_call_i_4_1_5);
(*   %arrayidx11.4.1.5 = getelementptr inbounds i16, i16* %r, i64 81 *)
(*   %1107 = load i16, i16* %arrayidx11.4.1.5, align 2, !tbaa !3 *)
mov v1107 mem0_162;
(*   %sub.4.1.5 = sub i16 %1107, %call.i.4.1.5 *)
sub v_sub_4_1_5 v1107 v_call_i_4_1_5;
(*   store i16 %sub.4.1.5, i16* %arrayidx9.4.1.5, align 2, !tbaa !3 *)
mov mem0_178 v_sub_4_1_5;
(*   %add21.4.1.5 = add i16 %1107, %call.i.4.1.5 *)
add v_add21_4_1_5 v1107 v_call_i_4_1_5;
(*   store i16 %add21.4.1.5, i16* %arrayidx11.4.1.5, align 2, !tbaa !3 *)
mov mem0_162 v_add21_4_1_5;
(*   %arrayidx9.4.2.5 = getelementptr inbounds i16, i16* %r, i64 90 *)
(*   %1108 = load i16, i16* %arrayidx9.4.2.5, align 2, !tbaa !3 *)
mov v1108 mem0_180;
(*   %conv1.i.4.2.5 = sext i16 %1108 to i32 *)
cast v_conv1_i_4_2_5@sint32 v1108@sint16;
(*   %mul.i.4.2.5 = mul nsw i32 %conv1.i.4.2.5, 1458 *)
mul v_mul_i_4_2_5 v_conv1_i_4_2_5 (1458)@sint32;
(*   %call.i.4.2.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2_5, v_call_i_4_2_5);
(*   %arrayidx11.4.2.5 = getelementptr inbounds i16, i16* %r, i64 82 *)
(*   %1109 = load i16, i16* %arrayidx11.4.2.5, align 2, !tbaa !3 *)
mov v1109 mem0_164;
(*   %sub.4.2.5 = sub i16 %1109, %call.i.4.2.5 *)
sub v_sub_4_2_5 v1109 v_call_i_4_2_5;
(*   store i16 %sub.4.2.5, i16* %arrayidx9.4.2.5, align 2, !tbaa !3 *)
mov mem0_180 v_sub_4_2_5;
(*   %add21.4.2.5 = add i16 %1109, %call.i.4.2.5 *)
add v_add21_4_2_5 v1109 v_call_i_4_2_5;
(*   store i16 %add21.4.2.5, i16* %arrayidx11.4.2.5, align 2, !tbaa !3 *)
mov mem0_164 v_add21_4_2_5;
(*   %arrayidx9.4.3.5 = getelementptr inbounds i16, i16* %r, i64 91 *)
(*   %1110 = load i16, i16* %arrayidx9.4.3.5, align 2, !tbaa !3 *)
mov v1110 mem0_182;
(*   %conv1.i.4.3.5 = sext i16 %1110 to i32 *)
cast v_conv1_i_4_3_5@sint32 v1110@sint16;
(*   %mul.i.4.3.5 = mul nsw i32 %conv1.i.4.3.5, 1458 *)
mul v_mul_i_4_3_5 v_conv1_i_4_3_5 (1458)@sint32;
(*   %call.i.4.3.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3_5, v_call_i_4_3_5);
(*   %arrayidx11.4.3.5 = getelementptr inbounds i16, i16* %r, i64 83 *)
(*   %1111 = load i16, i16* %arrayidx11.4.3.5, align 2, !tbaa !3 *)
mov v1111 mem0_166;
(*   %sub.4.3.5 = sub i16 %1111, %call.i.4.3.5 *)
sub v_sub_4_3_5 v1111 v_call_i_4_3_5;
(*   store i16 %sub.4.3.5, i16* %arrayidx9.4.3.5, align 2, !tbaa !3 *)
mov mem0_182 v_sub_4_3_5;
(*   %add21.4.3.5 = add i16 %1111, %call.i.4.3.5 *)
add v_add21_4_3_5 v1111 v_call_i_4_3_5;
(*   store i16 %add21.4.3.5, i16* %arrayidx11.4.3.5, align 2, !tbaa !3 *)
mov mem0_166 v_add21_4_3_5;
(*   %arrayidx9.4.4.5 = getelementptr inbounds i16, i16* %r, i64 92 *)
(*   %1112 = load i16, i16* %arrayidx9.4.4.5, align 2, !tbaa !3 *)
mov v1112 mem0_184;
(*   %conv1.i.4.4.5 = sext i16 %1112 to i32 *)
cast v_conv1_i_4_4_5@sint32 v1112@sint16;
(*   %mul.i.4.4.5 = mul nsw i32 %conv1.i.4.4.5, 1458 *)
mul v_mul_i_4_4_5 v_conv1_i_4_4_5 (1458)@sint32;
(*   %call.i.4.4.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4_5, v_call_i_4_4_5);
(*   %arrayidx11.4.4.5 = getelementptr inbounds i16, i16* %r, i64 84 *)
(*   %1113 = load i16, i16* %arrayidx11.4.4.5, align 2, !tbaa !3 *)
mov v1113 mem0_168;
(*   %sub.4.4.5 = sub i16 %1113, %call.i.4.4.5 *)
sub v_sub_4_4_5 v1113 v_call_i_4_4_5;
(*   store i16 %sub.4.4.5, i16* %arrayidx9.4.4.5, align 2, !tbaa !3 *)
mov mem0_184 v_sub_4_4_5;
(*   %add21.4.4.5 = add i16 %1113, %call.i.4.4.5 *)
add v_add21_4_4_5 v1113 v_call_i_4_4_5;
(*   store i16 %add21.4.4.5, i16* %arrayidx11.4.4.5, align 2, !tbaa !3 *)
mov mem0_168 v_add21_4_4_5;
(*   %arrayidx9.4.5.5 = getelementptr inbounds i16, i16* %r, i64 93 *)
(*   %1114 = load i16, i16* %arrayidx9.4.5.5, align 2, !tbaa !3 *)
mov v1114 mem0_186;
(*   %conv1.i.4.5.5 = sext i16 %1114 to i32 *)
cast v_conv1_i_4_5_5@sint32 v1114@sint16;
(*   %mul.i.4.5.5 = mul nsw i32 %conv1.i.4.5.5, 1458 *)
mul v_mul_i_4_5_5 v_conv1_i_4_5_5 (1458)@sint32;
(*   %call.i.4.5.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5_5, v_call_i_4_5_5);
(*   %arrayidx11.4.5.5 = getelementptr inbounds i16, i16* %r, i64 85 *)
(*   %1115 = load i16, i16* %arrayidx11.4.5.5, align 2, !tbaa !3 *)
mov v1115 mem0_170;
(*   %sub.4.5.5 = sub i16 %1115, %call.i.4.5.5 *)
sub v_sub_4_5_5 v1115 v_call_i_4_5_5;
(*   store i16 %sub.4.5.5, i16* %arrayidx9.4.5.5, align 2, !tbaa !3 *)
mov mem0_186 v_sub_4_5_5;
(*   %add21.4.5.5 = add i16 %1115, %call.i.4.5.5 *)
add v_add21_4_5_5 v1115 v_call_i_4_5_5;
(*   store i16 %add21.4.5.5, i16* %arrayidx11.4.5.5, align 2, !tbaa !3 *)
mov mem0_170 v_add21_4_5_5;
(*   %arrayidx9.4.6.5 = getelementptr inbounds i16, i16* %r, i64 94 *)
(*   %1116 = load i16, i16* %arrayidx9.4.6.5, align 2, !tbaa !3 *)
mov v1116 mem0_188;
(*   %conv1.i.4.6.5 = sext i16 %1116 to i32 *)
cast v_conv1_i_4_6_5@sint32 v1116@sint16;
(*   %mul.i.4.6.5 = mul nsw i32 %conv1.i.4.6.5, 1458 *)
mul v_mul_i_4_6_5 v_conv1_i_4_6_5 (1458)@sint32;
(*   %call.i.4.6.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6_5, v_call_i_4_6_5);
(*   %arrayidx11.4.6.5 = getelementptr inbounds i16, i16* %r, i64 86 *)
(*   %1117 = load i16, i16* %arrayidx11.4.6.5, align 2, !tbaa !3 *)
mov v1117 mem0_172;
(*   %sub.4.6.5 = sub i16 %1117, %call.i.4.6.5 *)
sub v_sub_4_6_5 v1117 v_call_i_4_6_5;
(*   store i16 %sub.4.6.5, i16* %arrayidx9.4.6.5, align 2, !tbaa !3 *)
mov mem0_188 v_sub_4_6_5;
(*   %add21.4.6.5 = add i16 %1117, %call.i.4.6.5 *)
add v_add21_4_6_5 v1117 v_call_i_4_6_5;
(*   store i16 %add21.4.6.5, i16* %arrayidx11.4.6.5, align 2, !tbaa !3 *)
mov mem0_172 v_add21_4_6_5;
(*   %arrayidx9.4.7.5 = getelementptr inbounds i16, i16* %r, i64 95 *)
(*   %1118 = load i16, i16* %arrayidx9.4.7.5, align 2, !tbaa !3 *)
mov v1118 mem0_190;
(*   %conv1.i.4.7.5 = sext i16 %1118 to i32 *)
cast v_conv1_i_4_7_5@sint32 v1118@sint16;
(*   %mul.i.4.7.5 = mul nsw i32 %conv1.i.4.7.5, 1458 *)
mul v_mul_i_4_7_5 v_conv1_i_4_7_5 (1458)@sint32;
(*   %call.i.4.7.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7_5, v_call_i_4_7_5);
(*   %arrayidx11.4.7.5 = getelementptr inbounds i16, i16* %r, i64 87 *)
(*   %1119 = load i16, i16* %arrayidx11.4.7.5, align 2, !tbaa !3 *)
mov v1119 mem0_174;
(*   %sub.4.7.5 = sub i16 %1119, %call.i.4.7.5 *)
sub v_sub_4_7_5 v1119 v_call_i_4_7_5;
(*   store i16 %sub.4.7.5, i16* %arrayidx9.4.7.5, align 2, !tbaa !3 *)
mov mem0_190 v_sub_4_7_5;
(*   %add21.4.7.5 = add i16 %1119, %call.i.4.7.5 *)
add v_add21_4_7_5 v1119 v_call_i_4_7_5;
(*   store i16 %add21.4.7.5, i16* %arrayidx11.4.7.5, align 2, !tbaa !3 *)
mov mem0_174 v_add21_4_7_5;

(* NOTE: k = 22 *)

(*   %arrayidx9.4.6158 = getelementptr inbounds i16, i16* %r, i64 104 *)
(*   %1120 = load i16, i16* %arrayidx9.4.6158, align 2, !tbaa !3 *)
mov v1120 mem0_208;
(*   %conv1.i.4.6159 = sext i16 %1120 to i32 *)
cast v_conv1_i_4_6159@sint32 v1120@sint16;
(*   %mul.i.4.6160 = mul nsw i32 %conv1.i.4.6159, -1602 *)
mul v_mul_i_4_6160 v_conv1_i_4_6159 (-1602)@sint32;
(*   %call.i.4.6161 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6160) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6160, v_call_i_4_6161);
(*   %arrayidx11.4.6162 = getelementptr inbounds i16, i16* %r, i64 96 *)
(*   %1121 = load i16, i16* %arrayidx11.4.6162, align 2, !tbaa !3 *)
mov v1121 mem0_192;
(*   %sub.4.6163 = sub i16 %1121, %call.i.4.6161 *)
sub v_sub_4_6163 v1121 v_call_i_4_6161;
(*   store i16 %sub.4.6163, i16* %arrayidx9.4.6158, align 2, !tbaa !3 *)
mov mem0_208 v_sub_4_6163;
(*   %add21.4.6164 = add i16 %1121, %call.i.4.6161 *)
add v_add21_4_6164 v1121 v_call_i_4_6161;
(*   store i16 %add21.4.6164, i16* %arrayidx11.4.6162, align 2, !tbaa !3 *)
mov mem0_192 v_add21_4_6164;
(*   %arrayidx9.4.1.6 = getelementptr inbounds i16, i16* %r, i64 105 *)
(*   %1122 = load i16, i16* %arrayidx9.4.1.6, align 2, !tbaa !3 *)
mov v1122 mem0_210;
(*   %conv1.i.4.1.6 = sext i16 %1122 to i32 *)
cast v_conv1_i_4_1_6@sint32 v1122@sint16;
(*   %mul.i.4.1.6 = mul nsw i32 %conv1.i.4.1.6, -1602 *)
mul v_mul_i_4_1_6 v_conv1_i_4_1_6 (-1602)@sint32;
(*   %call.i.4.1.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1_6, v_call_i_4_1_6);
(*   %arrayidx11.4.1.6 = getelementptr inbounds i16, i16* %r, i64 97 *)
(*   %1123 = load i16, i16* %arrayidx11.4.1.6, align 2, !tbaa !3 *)
mov v1123 mem0_194;
(*   %sub.4.1.6 = sub i16 %1123, %call.i.4.1.6 *)
sub v_sub_4_1_6 v1123 v_call_i_4_1_6;
(*   store i16 %sub.4.1.6, i16* %arrayidx9.4.1.6, align 2, !tbaa !3 *)
mov mem0_210 v_sub_4_1_6;
(*   %add21.4.1.6 = add i16 %1123, %call.i.4.1.6 *)
add v_add21_4_1_6 v1123 v_call_i_4_1_6;
(*   store i16 %add21.4.1.6, i16* %arrayidx11.4.1.6, align 2, !tbaa !3 *)
mov mem0_194 v_add21_4_1_6;
(*   %arrayidx9.4.2.6 = getelementptr inbounds i16, i16* %r, i64 106 *)
(*   %1124 = load i16, i16* %arrayidx9.4.2.6, align 2, !tbaa !3 *)
mov v1124 mem0_212;
(*   %conv1.i.4.2.6 = sext i16 %1124 to i32 *)
cast v_conv1_i_4_2_6@sint32 v1124@sint16;
(*   %mul.i.4.2.6 = mul nsw i32 %conv1.i.4.2.6, -1602 *)
mul v_mul_i_4_2_6 v_conv1_i_4_2_6 (-1602)@sint32;
(*   %call.i.4.2.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2_6, v_call_i_4_2_6);
(*   %arrayidx11.4.2.6 = getelementptr inbounds i16, i16* %r, i64 98 *)
(*   %1125 = load i16, i16* %arrayidx11.4.2.6, align 2, !tbaa !3 *)
mov v1125 mem0_196;
(*   %sub.4.2.6 = sub i16 %1125, %call.i.4.2.6 *)
sub v_sub_4_2_6 v1125 v_call_i_4_2_6;
(*   store i16 %sub.4.2.6, i16* %arrayidx9.4.2.6, align 2, !tbaa !3 *)
mov mem0_212 v_sub_4_2_6;
(*   %add21.4.2.6 = add i16 %1125, %call.i.4.2.6 *)
add v_add21_4_2_6 v1125 v_call_i_4_2_6;
(*   store i16 %add21.4.2.6, i16* %arrayidx11.4.2.6, align 2, !tbaa !3 *)
mov mem0_196 v_add21_4_2_6;
(*   %arrayidx9.4.3.6 = getelementptr inbounds i16, i16* %r, i64 107 *)
(*   %1126 = load i16, i16* %arrayidx9.4.3.6, align 2, !tbaa !3 *)
mov v1126 mem0_214;
(*   %conv1.i.4.3.6 = sext i16 %1126 to i32 *)
cast v_conv1_i_4_3_6@sint32 v1126@sint16;
(*   %mul.i.4.3.6 = mul nsw i32 %conv1.i.4.3.6, -1602 *)
mul v_mul_i_4_3_6 v_conv1_i_4_3_6 (-1602)@sint32;
(*   %call.i.4.3.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3_6, v_call_i_4_3_6);
(*   %arrayidx11.4.3.6 = getelementptr inbounds i16, i16* %r, i64 99 *)
(*   %1127 = load i16, i16* %arrayidx11.4.3.6, align 2, !tbaa !3 *)
mov v1127 mem0_198;
(*   %sub.4.3.6 = sub i16 %1127, %call.i.4.3.6 *)
sub v_sub_4_3_6 v1127 v_call_i_4_3_6;
(*   store i16 %sub.4.3.6, i16* %arrayidx9.4.3.6, align 2, !tbaa !3 *)
mov mem0_214 v_sub_4_3_6;
(*   %add21.4.3.6 = add i16 %1127, %call.i.4.3.6 *)
add v_add21_4_3_6 v1127 v_call_i_4_3_6;
(*   store i16 %add21.4.3.6, i16* %arrayidx11.4.3.6, align 2, !tbaa !3 *)
mov mem0_198 v_add21_4_3_6;
(*   %arrayidx9.4.4.6 = getelementptr inbounds i16, i16* %r, i64 108 *)
(*   %1128 = load i16, i16* %arrayidx9.4.4.6, align 2, !tbaa !3 *)
mov v1128 mem0_216;
(*   %conv1.i.4.4.6 = sext i16 %1128 to i32 *)
cast v_conv1_i_4_4_6@sint32 v1128@sint16;
(*   %mul.i.4.4.6 = mul nsw i32 %conv1.i.4.4.6, -1602 *)
mul v_mul_i_4_4_6 v_conv1_i_4_4_6 (-1602)@sint32;
(*   %call.i.4.4.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4_6, v_call_i_4_4_6);
(*   %arrayidx11.4.4.6 = getelementptr inbounds i16, i16* %r, i64 100 *)
(*   %1129 = load i16, i16* %arrayidx11.4.4.6, align 2, !tbaa !3 *)
mov v1129 mem0_200;
(*   %sub.4.4.6 = sub i16 %1129, %call.i.4.4.6 *)
sub v_sub_4_4_6 v1129 v_call_i_4_4_6;
(*   store i16 %sub.4.4.6, i16* %arrayidx9.4.4.6, align 2, !tbaa !3 *)
mov mem0_216 v_sub_4_4_6;
(*   %add21.4.4.6 = add i16 %1129, %call.i.4.4.6 *)
add v_add21_4_4_6 v1129 v_call_i_4_4_6;
(*   store i16 %add21.4.4.6, i16* %arrayidx11.4.4.6, align 2, !tbaa !3 *)
mov mem0_200 v_add21_4_4_6;
(*   %arrayidx9.4.5.6 = getelementptr inbounds i16, i16* %r, i64 109 *)
(*   %1130 = load i16, i16* %arrayidx9.4.5.6, align 2, !tbaa !3 *)
mov v1130 mem0_218;
(*   %conv1.i.4.5.6 = sext i16 %1130 to i32 *)
cast v_conv1_i_4_5_6@sint32 v1130@sint16;
(*   %mul.i.4.5.6 = mul nsw i32 %conv1.i.4.5.6, -1602 *)
mul v_mul_i_4_5_6 v_conv1_i_4_5_6 (-1602)@sint32;
(*   %call.i.4.5.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5_6, v_call_i_4_5_6);
(*   %arrayidx11.4.5.6 = getelementptr inbounds i16, i16* %r, i64 101 *)
(*   %1131 = load i16, i16* %arrayidx11.4.5.6, align 2, !tbaa !3 *)
mov v1131 mem0_202;
(*   %sub.4.5.6 = sub i16 %1131, %call.i.4.5.6 *)
sub v_sub_4_5_6 v1131 v_call_i_4_5_6;
(*   store i16 %sub.4.5.6, i16* %arrayidx9.4.5.6, align 2, !tbaa !3 *)
mov mem0_218 v_sub_4_5_6;
(*   %add21.4.5.6 = add i16 %1131, %call.i.4.5.6 *)
add v_add21_4_5_6 v1131 v_call_i_4_5_6;
(*   store i16 %add21.4.5.6, i16* %arrayidx11.4.5.6, align 2, !tbaa !3 *)
mov mem0_202 v_add21_4_5_6;
(*   %arrayidx9.4.6.6 = getelementptr inbounds i16, i16* %r, i64 110 *)
(*   %1132 = load i16, i16* %arrayidx9.4.6.6, align 2, !tbaa !3 *)
mov v1132 mem0_220;
(*   %conv1.i.4.6.6 = sext i16 %1132 to i32 *)
cast v_conv1_i_4_6_6@sint32 v1132@sint16;
(*   %mul.i.4.6.6 = mul nsw i32 %conv1.i.4.6.6, -1602 *)
mul v_mul_i_4_6_6 v_conv1_i_4_6_6 (-1602)@sint32;
(*   %call.i.4.6.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6_6, v_call_i_4_6_6);
(*   %arrayidx11.4.6.6 = getelementptr inbounds i16, i16* %r, i64 102 *)
(*   %1133 = load i16, i16* %arrayidx11.4.6.6, align 2, !tbaa !3 *)
mov v1133 mem0_204;
(*   %sub.4.6.6 = sub i16 %1133, %call.i.4.6.6 *)
sub v_sub_4_6_6 v1133 v_call_i_4_6_6;
(*   store i16 %sub.4.6.6, i16* %arrayidx9.4.6.6, align 2, !tbaa !3 *)
mov mem0_220 v_sub_4_6_6;
(*   %add21.4.6.6 = add i16 %1133, %call.i.4.6.6 *)
add v_add21_4_6_6 v1133 v_call_i_4_6_6;
(*   store i16 %add21.4.6.6, i16* %arrayidx11.4.6.6, align 2, !tbaa !3 *)
mov mem0_204 v_add21_4_6_6;
(*   %arrayidx9.4.7.6 = getelementptr inbounds i16, i16* %r, i64 111 *)
(*   %1134 = load i16, i16* %arrayidx9.4.7.6, align 2, !tbaa !3 *)
mov v1134 mem0_222;
(*   %conv1.i.4.7.6 = sext i16 %1134 to i32 *)
cast v_conv1_i_4_7_6@sint32 v1134@sint16;
(*   %mul.i.4.7.6 = mul nsw i32 %conv1.i.4.7.6, -1602 *)
mul v_mul_i_4_7_6 v_conv1_i_4_7_6 (-1602)@sint32;
(*   %call.i.4.7.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7_6, v_call_i_4_7_6);
(*   %arrayidx11.4.7.6 = getelementptr inbounds i16, i16* %r, i64 103 *)
(*   %1135 = load i16, i16* %arrayidx11.4.7.6, align 2, !tbaa !3 *)
mov v1135 mem0_206;
(*   %sub.4.7.6 = sub i16 %1135, %call.i.4.7.6 *)
sub v_sub_4_7_6 v1135 v_call_i_4_7_6;
(*   store i16 %sub.4.7.6, i16* %arrayidx9.4.7.6, align 2, !tbaa !3 *)
mov mem0_222 v_sub_4_7_6;
(*   %add21.4.7.6 = add i16 %1135, %call.i.4.7.6 *)
add v_add21_4_7_6 v1135 v_call_i_4_7_6;
(*   store i16 %add21.4.7.6, i16* %arrayidx11.4.7.6, align 2, !tbaa !3 *)
mov mem0_206 v_add21_4_7_6;

(* NOTE: k = 23 *)

(*   %arrayidx9.4.7168 = getelementptr inbounds i16, i16* %r, i64 120 *)
(*   %1136 = load i16, i16* %arrayidx9.4.7168, align 2, !tbaa !3 *)
mov v1136 mem0_240;
(*   %conv1.i.4.7169 = sext i16 %1136 to i32 *)
cast v_conv1_i_4_7169@sint32 v1136@sint16;
(*   %mul.i.4.7170 = mul nsw i32 %conv1.i.4.7169, -130 *)
mul v_mul_i_4_7170 v_conv1_i_4_7169 (-130)@sint32;
(*   %call.i.4.7171 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7170) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7170, v_call_i_4_7171);
(*   %arrayidx11.4.7172 = getelementptr inbounds i16, i16* %r, i64 112 *)
(*   %1137 = load i16, i16* %arrayidx11.4.7172, align 2, !tbaa !3 *)
mov v1137 mem0_224;
(*   %sub.4.7173 = sub i16 %1137, %call.i.4.7171 *)
sub v_sub_4_7173 v1137 v_call_i_4_7171;
(*   store i16 %sub.4.7173, i16* %arrayidx9.4.7168, align 2, !tbaa !3 *)
mov mem0_240 v_sub_4_7173;
(*   %add21.4.7174 = add i16 %1137, %call.i.4.7171 *)
add v_add21_4_7174 v1137 v_call_i_4_7171;
(*   store i16 %add21.4.7174, i16* %arrayidx11.4.7172, align 2, !tbaa !3 *)
mov mem0_224 v_add21_4_7174;
(*   %arrayidx9.4.1.7 = getelementptr inbounds i16, i16* %r, i64 121 *)
(*   %1138 = load i16, i16* %arrayidx9.4.1.7, align 2, !tbaa !3 *)
mov v1138 mem0_242;
(*   %conv1.i.4.1.7 = sext i16 %1138 to i32 *)
cast v_conv1_i_4_1_7@sint32 v1138@sint16;
(*   %mul.i.4.1.7 = mul nsw i32 %conv1.i.4.1.7, -130 *)
mul v_mul_i_4_1_7 v_conv1_i_4_1_7 (-130)@sint32;
(*   %call.i.4.1.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1_7, v_call_i_4_1_7);
(*   %arrayidx11.4.1.7 = getelementptr inbounds i16, i16* %r, i64 113 *)
(*   %1139 = load i16, i16* %arrayidx11.4.1.7, align 2, !tbaa !3 *)
mov v1139 mem0_226;
(*   %sub.4.1.7 = sub i16 %1139, %call.i.4.1.7 *)
sub v_sub_4_1_7 v1139 v_call_i_4_1_7;
(*   store i16 %sub.4.1.7, i16* %arrayidx9.4.1.7, align 2, !tbaa !3 *)
mov mem0_242 v_sub_4_1_7;
(*   %add21.4.1.7 = add i16 %1139, %call.i.4.1.7 *)
add v_add21_4_1_7 v1139 v_call_i_4_1_7;
(*   store i16 %add21.4.1.7, i16* %arrayidx11.4.1.7, align 2, !tbaa !3 *)
mov mem0_226 v_add21_4_1_7;
(*   %arrayidx9.4.2.7 = getelementptr inbounds i16, i16* %r, i64 122 *)
(*   %1140 = load i16, i16* %arrayidx9.4.2.7, align 2, !tbaa !3 *)
mov v1140 mem0_244;
(*   %conv1.i.4.2.7 = sext i16 %1140 to i32 *)
cast v_conv1_i_4_2_7@sint32 v1140@sint16;
(*   %mul.i.4.2.7 = mul nsw i32 %conv1.i.4.2.7, -130 *)
mul v_mul_i_4_2_7 v_conv1_i_4_2_7 (-130)@sint32;
(*   %call.i.4.2.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2_7, v_call_i_4_2_7);
(*   %arrayidx11.4.2.7 = getelementptr inbounds i16, i16* %r, i64 114 *)
(*   %1141 = load i16, i16* %arrayidx11.4.2.7, align 2, !tbaa !3 *)
mov v1141 mem0_228;
(*   %sub.4.2.7 = sub i16 %1141, %call.i.4.2.7 *)
sub v_sub_4_2_7 v1141 v_call_i_4_2_7;
(*   store i16 %sub.4.2.7, i16* %arrayidx9.4.2.7, align 2, !tbaa !3 *)
mov mem0_244 v_sub_4_2_7;
(*   %add21.4.2.7 = add i16 %1141, %call.i.4.2.7 *)
add v_add21_4_2_7 v1141 v_call_i_4_2_7;
(*   store i16 %add21.4.2.7, i16* %arrayidx11.4.2.7, align 2, !tbaa !3 *)
mov mem0_228 v_add21_4_2_7;
(*   %arrayidx9.4.3.7 = getelementptr inbounds i16, i16* %r, i64 123 *)
(*   %1142 = load i16, i16* %arrayidx9.4.3.7, align 2, !tbaa !3 *)
mov v1142 mem0_246;
(*   %conv1.i.4.3.7 = sext i16 %1142 to i32 *)
cast v_conv1_i_4_3_7@sint32 v1142@sint16;
(*   %mul.i.4.3.7 = mul nsw i32 %conv1.i.4.3.7, -130 *)
mul v_mul_i_4_3_7 v_conv1_i_4_3_7 (-130)@sint32;
(*   %call.i.4.3.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3_7, v_call_i_4_3_7);
(*   %arrayidx11.4.3.7 = getelementptr inbounds i16, i16* %r, i64 115 *)
(*   %1143 = load i16, i16* %arrayidx11.4.3.7, align 2, !tbaa !3 *)
mov v1143 mem0_230;
(*   %sub.4.3.7 = sub i16 %1143, %call.i.4.3.7 *)
sub v_sub_4_3_7 v1143 v_call_i_4_3_7;
(*   store i16 %sub.4.3.7, i16* %arrayidx9.4.3.7, align 2, !tbaa !3 *)
mov mem0_246 v_sub_4_3_7;
(*   %add21.4.3.7 = add i16 %1143, %call.i.4.3.7 *)
add v_add21_4_3_7 v1143 v_call_i_4_3_7;
(*   store i16 %add21.4.3.7, i16* %arrayidx11.4.3.7, align 2, !tbaa !3 *)
mov mem0_230 v_add21_4_3_7;
(*   %arrayidx9.4.4.7 = getelementptr inbounds i16, i16* %r, i64 124 *)
(*   %1144 = load i16, i16* %arrayidx9.4.4.7, align 2, !tbaa !3 *)
mov v1144 mem0_248;
(*   %conv1.i.4.4.7 = sext i16 %1144 to i32 *)
cast v_conv1_i_4_4_7@sint32 v1144@sint16;
(*   %mul.i.4.4.7 = mul nsw i32 %conv1.i.4.4.7, -130 *)
mul v_mul_i_4_4_7 v_conv1_i_4_4_7 (-130)@sint32;
(*   %call.i.4.4.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4_7, v_call_i_4_4_7);
(*   %arrayidx11.4.4.7 = getelementptr inbounds i16, i16* %r, i64 116 *)
(*   %1145 = load i16, i16* %arrayidx11.4.4.7, align 2, !tbaa !3 *)
mov v1145 mem0_232;
(*   %sub.4.4.7 = sub i16 %1145, %call.i.4.4.7 *)
sub v_sub_4_4_7 v1145 v_call_i_4_4_7;
(*   store i16 %sub.4.4.7, i16* %arrayidx9.4.4.7, align 2, !tbaa !3 *)
mov mem0_248 v_sub_4_4_7;
(*   %add21.4.4.7 = add i16 %1145, %call.i.4.4.7 *)
add v_add21_4_4_7 v1145 v_call_i_4_4_7;
(*   store i16 %add21.4.4.7, i16* %arrayidx11.4.4.7, align 2, !tbaa !3 *)
mov mem0_232 v_add21_4_4_7;
(*   %arrayidx9.4.5.7 = getelementptr inbounds i16, i16* %r, i64 125 *)
(*   %1146 = load i16, i16* %arrayidx9.4.5.7, align 2, !tbaa !3 *)
mov v1146 mem0_250;
(*   %conv1.i.4.5.7 = sext i16 %1146 to i32 *)
cast v_conv1_i_4_5_7@sint32 v1146@sint16;
(*   %mul.i.4.5.7 = mul nsw i32 %conv1.i.4.5.7, -130 *)
mul v_mul_i_4_5_7 v_conv1_i_4_5_7 (-130)@sint32;
(*   %call.i.4.5.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5_7, v_call_i_4_5_7);
(*   %arrayidx11.4.5.7 = getelementptr inbounds i16, i16* %r, i64 117 *)
(*   %1147 = load i16, i16* %arrayidx11.4.5.7, align 2, !tbaa !3 *)
mov v1147 mem0_234;
(*   %sub.4.5.7 = sub i16 %1147, %call.i.4.5.7 *)
sub v_sub_4_5_7 v1147 v_call_i_4_5_7;
(*   store i16 %sub.4.5.7, i16* %arrayidx9.4.5.7, align 2, !tbaa !3 *)
mov mem0_250 v_sub_4_5_7;
(*   %add21.4.5.7 = add i16 %1147, %call.i.4.5.7 *)
add v_add21_4_5_7 v1147 v_call_i_4_5_7;
(*   store i16 %add21.4.5.7, i16* %arrayidx11.4.5.7, align 2, !tbaa !3 *)
mov mem0_234 v_add21_4_5_7;
(*   %arrayidx9.4.6.7 = getelementptr inbounds i16, i16* %r, i64 126 *)
(*   %1148 = load i16, i16* %arrayidx9.4.6.7, align 2, !tbaa !3 *)
mov v1148 mem0_252;
(*   %conv1.i.4.6.7 = sext i16 %1148 to i32 *)
cast v_conv1_i_4_6_7@sint32 v1148@sint16;
(*   %mul.i.4.6.7 = mul nsw i32 %conv1.i.4.6.7, -130 *)
mul v_mul_i_4_6_7 v_conv1_i_4_6_7 (-130)@sint32;
(*   %call.i.4.6.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6_7, v_call_i_4_6_7);
(*   %arrayidx11.4.6.7 = getelementptr inbounds i16, i16* %r, i64 118 *)
(*   %1149 = load i16, i16* %arrayidx11.4.6.7, align 2, !tbaa !3 *)
mov v1149 mem0_236;
(*   %sub.4.6.7 = sub i16 %1149, %call.i.4.6.7 *)
sub v_sub_4_6_7 v1149 v_call_i_4_6_7;
(*   store i16 %sub.4.6.7, i16* %arrayidx9.4.6.7, align 2, !tbaa !3 *)
mov mem0_252 v_sub_4_6_7;
(*   %add21.4.6.7 = add i16 %1149, %call.i.4.6.7 *)
add v_add21_4_6_7 v1149 v_call_i_4_6_7;
(*   store i16 %add21.4.6.7, i16* %arrayidx11.4.6.7, align 2, !tbaa !3 *)
mov mem0_236 v_add21_4_6_7;
(*   %arrayidx9.4.7.7 = getelementptr inbounds i16, i16* %r, i64 127 *)
(*   %1150 = load i16, i16* %arrayidx9.4.7.7, align 2, !tbaa !3 *)
mov v1150 mem0_254;
(*   %conv1.i.4.7.7 = sext i16 %1150 to i32 *)
cast v_conv1_i_4_7_7@sint32 v1150@sint16;
(*   %mul.i.4.7.7 = mul nsw i32 %conv1.i.4.7.7, -130 *)
mul v_mul_i_4_7_7 v_conv1_i_4_7_7 (-130)@sint32;
(*   %call.i.4.7.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7_7, v_call_i_4_7_7);
(*   %arrayidx11.4.7.7 = getelementptr inbounds i16, i16* %r, i64 119 *)
(*   %1151 = load i16, i16* %arrayidx11.4.7.7, align 2, !tbaa !3 *)
mov v1151 mem0_238;
(*   %sub.4.7.7 = sub i16 %1151, %call.i.4.7.7 *)
sub v_sub_4_7_7 v1151 v_call_i_4_7_7;
(*   store i16 %sub.4.7.7, i16* %arrayidx9.4.7.7, align 2, !tbaa !3 *)
mov mem0_254 v_sub_4_7_7;
(*   %add21.4.7.7 = add i16 %1151, %call.i.4.7.7 *)
add v_add21_4_7_7 v1151 v_call_i_4_7_7;
(*   store i16 %add21.4.7.7, i16* %arrayidx11.4.7.7, align 2, !tbaa !3 *)
mov mem0_238 v_add21_4_7_7;

(* NOTE: k = 24 *)

(*   %arrayidx9.4.8 = getelementptr inbounds i16, i16* %r, i64 136 *)
(*   %1152 = load i16, i16* %arrayidx9.4.8, align 2, !tbaa !3 *)
mov v1152 mem0_272;
(*   %conv1.i.4.8 = sext i16 %1152 to i32 *)
cast v_conv1_i_4_8@sint32 v1152@sint16;
(*   %mul.i.4.8 = mul nsw i32 %conv1.i.4.8, -681 *)
mul v_mul_i_4_8 v_conv1_i_4_8 (-681)@sint32;
(*   %call.i.4.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_8, v_call_i_4_8);
(*   %arrayidx11.4.8 = getelementptr inbounds i16, i16* %r, i64 128 *)
(*   %1153 = load i16, i16* %arrayidx11.4.8, align 2, !tbaa !3 *)
mov v1153 mem0_256;
(*   %sub.4.8 = sub i16 %1153, %call.i.4.8 *)
sub v_sub_4_8 v1153 v_call_i_4_8;
(*   store i16 %sub.4.8, i16* %arrayidx9.4.8, align 2, !tbaa !3 *)
mov mem0_272 v_sub_4_8;
(*   %add21.4.8 = add i16 %1153, %call.i.4.8 *)
add v_add21_4_8 v1153 v_call_i_4_8;
(*   store i16 %add21.4.8, i16* %arrayidx11.4.8, align 2, !tbaa !3 *)
mov mem0_256 v_add21_4_8;
(*   %arrayidx9.4.1.8 = getelementptr inbounds i16, i16* %r, i64 137 *)
(*   %1154 = load i16, i16* %arrayidx9.4.1.8, align 2, !tbaa !3 *)
mov v1154 mem0_274;
(*   %conv1.i.4.1.8 = sext i16 %1154 to i32 *)
cast v_conv1_i_4_1_8@sint32 v1154@sint16;
(*   %mul.i.4.1.8 = mul nsw i32 %conv1.i.4.1.8, -681 *)
mul v_mul_i_4_1_8 v_conv1_i_4_1_8 (-681)@sint32;
(*   %call.i.4.1.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1_8, v_call_i_4_1_8);
(*   %arrayidx11.4.1.8 = getelementptr inbounds i16, i16* %r, i64 129 *)
(*   %1155 = load i16, i16* %arrayidx11.4.1.8, align 2, !tbaa !3 *)
mov v1155 mem0_258;
(*   %sub.4.1.8 = sub i16 %1155, %call.i.4.1.8 *)
sub v_sub_4_1_8 v1155 v_call_i_4_1_8;
(*   store i16 %sub.4.1.8, i16* %arrayidx9.4.1.8, align 2, !tbaa !3 *)
mov mem0_274 v_sub_4_1_8;
(*   %add21.4.1.8 = add i16 %1155, %call.i.4.1.8 *)
add v_add21_4_1_8 v1155 v_call_i_4_1_8;
(*   store i16 %add21.4.1.8, i16* %arrayidx11.4.1.8, align 2, !tbaa !3 *)
mov mem0_258 v_add21_4_1_8;
(*   %arrayidx9.4.2.8 = getelementptr inbounds i16, i16* %r, i64 138 *)
(*   %1156 = load i16, i16* %arrayidx9.4.2.8, align 2, !tbaa !3 *)
mov v1156 mem0_276;
(*   %conv1.i.4.2.8 = sext i16 %1156 to i32 *)
cast v_conv1_i_4_2_8@sint32 v1156@sint16;
(*   %mul.i.4.2.8 = mul nsw i32 %conv1.i.4.2.8, -681 *)
mul v_mul_i_4_2_8 v_conv1_i_4_2_8 (-681)@sint32;
(*   %call.i.4.2.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2_8, v_call_i_4_2_8);
(*   %arrayidx11.4.2.8 = getelementptr inbounds i16, i16* %r, i64 130 *)
(*   %1157 = load i16, i16* %arrayidx11.4.2.8, align 2, !tbaa !3 *)
mov v1157 mem0_260;
(*   %sub.4.2.8 = sub i16 %1157, %call.i.4.2.8 *)
sub v_sub_4_2_8 v1157 v_call_i_4_2_8;
(*   store i16 %sub.4.2.8, i16* %arrayidx9.4.2.8, align 2, !tbaa !3 *)
mov mem0_276 v_sub_4_2_8;
(*   %add21.4.2.8 = add i16 %1157, %call.i.4.2.8 *)
add v_add21_4_2_8 v1157 v_call_i_4_2_8;
(*   store i16 %add21.4.2.8, i16* %arrayidx11.4.2.8, align 2, !tbaa !3 *)
mov mem0_260 v_add21_4_2_8;
(*   %arrayidx9.4.3.8 = getelementptr inbounds i16, i16* %r, i64 139 *)
(*   %1158 = load i16, i16* %arrayidx9.4.3.8, align 2, !tbaa !3 *)
mov v1158 mem0_278;
(*   %conv1.i.4.3.8 = sext i16 %1158 to i32 *)
cast v_conv1_i_4_3_8@sint32 v1158@sint16;
(*   %mul.i.4.3.8 = mul nsw i32 %conv1.i.4.3.8, -681 *)
mul v_mul_i_4_3_8 v_conv1_i_4_3_8 (-681)@sint32;
(*   %call.i.4.3.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3_8, v_call_i_4_3_8);
(*   %arrayidx11.4.3.8 = getelementptr inbounds i16, i16* %r, i64 131 *)
(*   %1159 = load i16, i16* %arrayidx11.4.3.8, align 2, !tbaa !3 *)
mov v1159 mem0_262;
(*   %sub.4.3.8 = sub i16 %1159, %call.i.4.3.8 *)
sub v_sub_4_3_8 v1159 v_call_i_4_3_8;
(*   store i16 %sub.4.3.8, i16* %arrayidx9.4.3.8, align 2, !tbaa !3 *)
mov mem0_278 v_sub_4_3_8;
(*   %add21.4.3.8 = add i16 %1159, %call.i.4.3.8 *)
add v_add21_4_3_8 v1159 v_call_i_4_3_8;
(*   store i16 %add21.4.3.8, i16* %arrayidx11.4.3.8, align 2, !tbaa !3 *)
mov mem0_262 v_add21_4_3_8;
(*   %arrayidx9.4.4.8 = getelementptr inbounds i16, i16* %r, i64 140 *)
(*   %1160 = load i16, i16* %arrayidx9.4.4.8, align 2, !tbaa !3 *)
mov v1160 mem0_280;
(*   %conv1.i.4.4.8 = sext i16 %1160 to i32 *)
cast v_conv1_i_4_4_8@sint32 v1160@sint16;
(*   %mul.i.4.4.8 = mul nsw i32 %conv1.i.4.4.8, -681 *)
mul v_mul_i_4_4_8 v_conv1_i_4_4_8 (-681)@sint32;
(*   %call.i.4.4.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4_8, v_call_i_4_4_8);
(*   %arrayidx11.4.4.8 = getelementptr inbounds i16, i16* %r, i64 132 *)
(*   %1161 = load i16, i16* %arrayidx11.4.4.8, align 2, !tbaa !3 *)
mov v1161 mem0_264;
(*   %sub.4.4.8 = sub i16 %1161, %call.i.4.4.8 *)
sub v_sub_4_4_8 v1161 v_call_i_4_4_8;
(*   store i16 %sub.4.4.8, i16* %arrayidx9.4.4.8, align 2, !tbaa !3 *)
mov mem0_280 v_sub_4_4_8;
(*   %add21.4.4.8 = add i16 %1161, %call.i.4.4.8 *)
add v_add21_4_4_8 v1161 v_call_i_4_4_8;
(*   store i16 %add21.4.4.8, i16* %arrayidx11.4.4.8, align 2, !tbaa !3 *)
mov mem0_264 v_add21_4_4_8;
(*   %arrayidx9.4.5.8 = getelementptr inbounds i16, i16* %r, i64 141 *)
(*   %1162 = load i16, i16* %arrayidx9.4.5.8, align 2, !tbaa !3 *)
mov v1162 mem0_282;
(*   %conv1.i.4.5.8 = sext i16 %1162 to i32 *)
cast v_conv1_i_4_5_8@sint32 v1162@sint16;
(*   %mul.i.4.5.8 = mul nsw i32 %conv1.i.4.5.8, -681 *)
mul v_mul_i_4_5_8 v_conv1_i_4_5_8 (-681)@sint32;
(*   %call.i.4.5.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5_8, v_call_i_4_5_8);
(*   %arrayidx11.4.5.8 = getelementptr inbounds i16, i16* %r, i64 133 *)
(*   %1163 = load i16, i16* %arrayidx11.4.5.8, align 2, !tbaa !3 *)
mov v1163 mem0_266;
(*   %sub.4.5.8 = sub i16 %1163, %call.i.4.5.8 *)
sub v_sub_4_5_8 v1163 v_call_i_4_5_8;
(*   store i16 %sub.4.5.8, i16* %arrayidx9.4.5.8, align 2, !tbaa !3 *)
mov mem0_282 v_sub_4_5_8;
(*   %add21.4.5.8 = add i16 %1163, %call.i.4.5.8 *)
add v_add21_4_5_8 v1163 v_call_i_4_5_8;
(*   store i16 %add21.4.5.8, i16* %arrayidx11.4.5.8, align 2, !tbaa !3 *)
mov mem0_266 v_add21_4_5_8;
(*   %arrayidx9.4.6.8 = getelementptr inbounds i16, i16* %r, i64 142 *)
(*   %1164 = load i16, i16* %arrayidx9.4.6.8, align 2, !tbaa !3 *)
mov v1164 mem0_284;
(*   %conv1.i.4.6.8 = sext i16 %1164 to i32 *)
cast v_conv1_i_4_6_8@sint32 v1164@sint16;
(*   %mul.i.4.6.8 = mul nsw i32 %conv1.i.4.6.8, -681 *)
mul v_mul_i_4_6_8 v_conv1_i_4_6_8 (-681)@sint32;
(*   %call.i.4.6.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6_8, v_call_i_4_6_8);
(*   %arrayidx11.4.6.8 = getelementptr inbounds i16, i16* %r, i64 134 *)
(*   %1165 = load i16, i16* %arrayidx11.4.6.8, align 2, !tbaa !3 *)
mov v1165 mem0_268;
(*   %sub.4.6.8 = sub i16 %1165, %call.i.4.6.8 *)
sub v_sub_4_6_8 v1165 v_call_i_4_6_8;
(*   store i16 %sub.4.6.8, i16* %arrayidx9.4.6.8, align 2, !tbaa !3 *)
mov mem0_284 v_sub_4_6_8;
(*   %add21.4.6.8 = add i16 %1165, %call.i.4.6.8 *)
add v_add21_4_6_8 v1165 v_call_i_4_6_8;
(*   store i16 %add21.4.6.8, i16* %arrayidx11.4.6.8, align 2, !tbaa !3 *)
mov mem0_268 v_add21_4_6_8;
(*   %arrayidx9.4.7.8 = getelementptr inbounds i16, i16* %r, i64 143 *)
(*   %1166 = load i16, i16* %arrayidx9.4.7.8, align 2, !tbaa !3 *)
mov v1166 mem0_286;
(*   %conv1.i.4.7.8 = sext i16 %1166 to i32 *)
cast v_conv1_i_4_7_8@sint32 v1166@sint16;
(*   %mul.i.4.7.8 = mul nsw i32 %conv1.i.4.7.8, -681 *)
mul v_mul_i_4_7_8 v_conv1_i_4_7_8 (-681)@sint32;
(*   %call.i.4.7.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7_8, v_call_i_4_7_8);
(*   %arrayidx11.4.7.8 = getelementptr inbounds i16, i16* %r, i64 135 *)
(*   %1167 = load i16, i16* %arrayidx11.4.7.8, align 2, !tbaa !3 *)
mov v1167 mem0_270;
(*   %sub.4.7.8 = sub i16 %1167, %call.i.4.7.8 *)
sub v_sub_4_7_8 v1167 v_call_i_4_7_8;
(*   store i16 %sub.4.7.8, i16* %arrayidx9.4.7.8, align 2, !tbaa !3 *)
mov mem0_286 v_sub_4_7_8;
(*   %add21.4.7.8 = add i16 %1167, %call.i.4.7.8 *)
add v_add21_4_7_8 v1167 v_call_i_4_7_8;
(*   store i16 %add21.4.7.8, i16* %arrayidx11.4.7.8, align 2, !tbaa !3 *)
mov mem0_270 v_add21_4_7_8;

(* NOTE: k = 25 *)

(*   %arrayidx9.4.9 = getelementptr inbounds i16, i16* %r, i64 152 *)
(*   %1168 = load i16, i16* %arrayidx9.4.9, align 2, !tbaa !3 *)
mov v1168 mem0_304;
(*   %conv1.i.4.9 = sext i16 %1168 to i32 *)
cast v_conv1_i_4_9@sint32 v1168@sint16;
(*   %mul.i.4.9 = mul nsw i32 %conv1.i.4.9, 1017 *)
mul v_mul_i_4_9 v_conv1_i_4_9 (1017)@sint32;
(*   %call.i.4.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_9, v_call_i_4_9);
(*   %arrayidx11.4.9 = getelementptr inbounds i16, i16* %r, i64 144 *)
(*   %1169 = load i16, i16* %arrayidx11.4.9, align 2, !tbaa !3 *)
mov v1169 mem0_288;
(*   %sub.4.9 = sub i16 %1169, %call.i.4.9 *)
sub v_sub_4_9 v1169 v_call_i_4_9;
(*   store i16 %sub.4.9, i16* %arrayidx9.4.9, align 2, !tbaa !3 *)
mov mem0_304 v_sub_4_9;
(*   %add21.4.9 = add i16 %1169, %call.i.4.9 *)
add v_add21_4_9 v1169 v_call_i_4_9;
(*   store i16 %add21.4.9, i16* %arrayidx11.4.9, align 2, !tbaa !3 *)
mov mem0_288 v_add21_4_9;
(*   %arrayidx9.4.1.9 = getelementptr inbounds i16, i16* %r, i64 153 *)
(*   %1170 = load i16, i16* %arrayidx9.4.1.9, align 2, !tbaa !3 *)
mov v1170 mem0_306;
(*   %conv1.i.4.1.9 = sext i16 %1170 to i32 *)
cast v_conv1_i_4_1_9@sint32 v1170@sint16;
(*   %mul.i.4.1.9 = mul nsw i32 %conv1.i.4.1.9, 1017 *)
mul v_mul_i_4_1_9 v_conv1_i_4_1_9 (1017)@sint32;
(*   %call.i.4.1.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1_9, v_call_i_4_1_9);
(*   %arrayidx11.4.1.9 = getelementptr inbounds i16, i16* %r, i64 145 *)
(*   %1171 = load i16, i16* %arrayidx11.4.1.9, align 2, !tbaa !3 *)
mov v1171 mem0_290;
(*   %sub.4.1.9 = sub i16 %1171, %call.i.4.1.9 *)
sub v_sub_4_1_9 v1171 v_call_i_4_1_9;
(*   store i16 %sub.4.1.9, i16* %arrayidx9.4.1.9, align 2, !tbaa !3 *)
mov mem0_306 v_sub_4_1_9;
(*   %add21.4.1.9 = add i16 %1171, %call.i.4.1.9 *)
add v_add21_4_1_9 v1171 v_call_i_4_1_9;
(*   store i16 %add21.4.1.9, i16* %arrayidx11.4.1.9, align 2, !tbaa !3 *)
mov mem0_290 v_add21_4_1_9;
(*   %arrayidx9.4.2.9 = getelementptr inbounds i16, i16* %r, i64 154 *)
(*   %1172 = load i16, i16* %arrayidx9.4.2.9, align 2, !tbaa !3 *)
mov v1172 mem0_308;
(*   %conv1.i.4.2.9 = sext i16 %1172 to i32 *)
cast v_conv1_i_4_2_9@sint32 v1172@sint16;
(*   %mul.i.4.2.9 = mul nsw i32 %conv1.i.4.2.9, 1017 *)
mul v_mul_i_4_2_9 v_conv1_i_4_2_9 (1017)@sint32;
(*   %call.i.4.2.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2_9, v_call_i_4_2_9);
(*   %arrayidx11.4.2.9 = getelementptr inbounds i16, i16* %r, i64 146 *)
(*   %1173 = load i16, i16* %arrayidx11.4.2.9, align 2, !tbaa !3 *)
mov v1173 mem0_292;
(*   %sub.4.2.9 = sub i16 %1173, %call.i.4.2.9 *)
sub v_sub_4_2_9 v1173 v_call_i_4_2_9;
(*   store i16 %sub.4.2.9, i16* %arrayidx9.4.2.9, align 2, !tbaa !3 *)
mov mem0_308 v_sub_4_2_9;
(*   %add21.4.2.9 = add i16 %1173, %call.i.4.2.9 *)
add v_add21_4_2_9 v1173 v_call_i_4_2_9;
(*   store i16 %add21.4.2.9, i16* %arrayidx11.4.2.9, align 2, !tbaa !3 *)
mov mem0_292 v_add21_4_2_9;
(*   %arrayidx9.4.3.9 = getelementptr inbounds i16, i16* %r, i64 155 *)
(*   %1174 = load i16, i16* %arrayidx9.4.3.9, align 2, !tbaa !3 *)
mov v1174 mem0_310;
(*   %conv1.i.4.3.9 = sext i16 %1174 to i32 *)
cast v_conv1_i_4_3_9@sint32 v1174@sint16;
(*   %mul.i.4.3.9 = mul nsw i32 %conv1.i.4.3.9, 1017 *)
mul v_mul_i_4_3_9 v_conv1_i_4_3_9 (1017)@sint32;
(*   %call.i.4.3.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3_9, v_call_i_4_3_9);
(*   %arrayidx11.4.3.9 = getelementptr inbounds i16, i16* %r, i64 147 *)
(*   %1175 = load i16, i16* %arrayidx11.4.3.9, align 2, !tbaa !3 *)
mov v1175 mem0_294;
(*   %sub.4.3.9 = sub i16 %1175, %call.i.4.3.9 *)
sub v_sub_4_3_9 v1175 v_call_i_4_3_9;
(*   store i16 %sub.4.3.9, i16* %arrayidx9.4.3.9, align 2, !tbaa !3 *)
mov mem0_310 v_sub_4_3_9;
(*   %add21.4.3.9 = add i16 %1175, %call.i.4.3.9 *)
add v_add21_4_3_9 v1175 v_call_i_4_3_9;
(*   store i16 %add21.4.3.9, i16* %arrayidx11.4.3.9, align 2, !tbaa !3 *)
mov mem0_294 v_add21_4_3_9;
(*   %arrayidx9.4.4.9 = getelementptr inbounds i16, i16* %r, i64 156 *)
(*   %1176 = load i16, i16* %arrayidx9.4.4.9, align 2, !tbaa !3 *)
mov v1176 mem0_312;
(*   %conv1.i.4.4.9 = sext i16 %1176 to i32 *)
cast v_conv1_i_4_4_9@sint32 v1176@sint16;
(*   %mul.i.4.4.9 = mul nsw i32 %conv1.i.4.4.9, 1017 *)
mul v_mul_i_4_4_9 v_conv1_i_4_4_9 (1017)@sint32;
(*   %call.i.4.4.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4_9, v_call_i_4_4_9);
(*   %arrayidx11.4.4.9 = getelementptr inbounds i16, i16* %r, i64 148 *)
(*   %1177 = load i16, i16* %arrayidx11.4.4.9, align 2, !tbaa !3 *)
mov v1177 mem0_296;
(*   %sub.4.4.9 = sub i16 %1177, %call.i.4.4.9 *)
sub v_sub_4_4_9 v1177 v_call_i_4_4_9;
(*   store i16 %sub.4.4.9, i16* %arrayidx9.4.4.9, align 2, !tbaa !3 *)
mov mem0_312 v_sub_4_4_9;
(*   %add21.4.4.9 = add i16 %1177, %call.i.4.4.9 *)
add v_add21_4_4_9 v1177 v_call_i_4_4_9;
(*   store i16 %add21.4.4.9, i16* %arrayidx11.4.4.9, align 2, !tbaa !3 *)
mov mem0_296 v_add21_4_4_9;
(*   %arrayidx9.4.5.9 = getelementptr inbounds i16, i16* %r, i64 157 *)
(*   %1178 = load i16, i16* %arrayidx9.4.5.9, align 2, !tbaa !3 *)
mov v1178 mem0_314;
(*   %conv1.i.4.5.9 = sext i16 %1178 to i32 *)
cast v_conv1_i_4_5_9@sint32 v1178@sint16;
(*   %mul.i.4.5.9 = mul nsw i32 %conv1.i.4.5.9, 1017 *)
mul v_mul_i_4_5_9 v_conv1_i_4_5_9 (1017)@sint32;
(*   %call.i.4.5.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5_9, v_call_i_4_5_9);
(*   %arrayidx11.4.5.9 = getelementptr inbounds i16, i16* %r, i64 149 *)
(*   %1179 = load i16, i16* %arrayidx11.4.5.9, align 2, !tbaa !3 *)
mov v1179 mem0_298;
(*   %sub.4.5.9 = sub i16 %1179, %call.i.4.5.9 *)
sub v_sub_4_5_9 v1179 v_call_i_4_5_9;
(*   store i16 %sub.4.5.9, i16* %arrayidx9.4.5.9, align 2, !tbaa !3 *)
mov mem0_314 v_sub_4_5_9;
(*   %add21.4.5.9 = add i16 %1179, %call.i.4.5.9 *)
add v_add21_4_5_9 v1179 v_call_i_4_5_9;
(*   store i16 %add21.4.5.9, i16* %arrayidx11.4.5.9, align 2, !tbaa !3 *)
mov mem0_298 v_add21_4_5_9;
(*   %arrayidx9.4.6.9 = getelementptr inbounds i16, i16* %r, i64 158 *)
(*   %1180 = load i16, i16* %arrayidx9.4.6.9, align 2, !tbaa !3 *)
mov v1180 mem0_316;
(*   %conv1.i.4.6.9 = sext i16 %1180 to i32 *)
cast v_conv1_i_4_6_9@sint32 v1180@sint16;
(*   %mul.i.4.6.9 = mul nsw i32 %conv1.i.4.6.9, 1017 *)
mul v_mul_i_4_6_9 v_conv1_i_4_6_9 (1017)@sint32;
(*   %call.i.4.6.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6_9, v_call_i_4_6_9);
(*   %arrayidx11.4.6.9 = getelementptr inbounds i16, i16* %r, i64 150 *)
(*   %1181 = load i16, i16* %arrayidx11.4.6.9, align 2, !tbaa !3 *)
mov v1181 mem0_300;
(*   %sub.4.6.9 = sub i16 %1181, %call.i.4.6.9 *)
sub v_sub_4_6_9 v1181 v_call_i_4_6_9;
(*   store i16 %sub.4.6.9, i16* %arrayidx9.4.6.9, align 2, !tbaa !3 *)
mov mem0_316 v_sub_4_6_9;
(*   %add21.4.6.9 = add i16 %1181, %call.i.4.6.9 *)
add v_add21_4_6_9 v1181 v_call_i_4_6_9;
(*   store i16 %add21.4.6.9, i16* %arrayidx11.4.6.9, align 2, !tbaa !3 *)
mov mem0_300 v_add21_4_6_9;
(*   %arrayidx9.4.7.9 = getelementptr inbounds i16, i16* %r, i64 159 *)
(*   %1182 = load i16, i16* %arrayidx9.4.7.9, align 2, !tbaa !3 *)
mov v1182 mem0_318;
(*   %conv1.i.4.7.9 = sext i16 %1182 to i32 *)
cast v_conv1_i_4_7_9@sint32 v1182@sint16;
(*   %mul.i.4.7.9 = mul nsw i32 %conv1.i.4.7.9, 1017 *)
mul v_mul_i_4_7_9 v_conv1_i_4_7_9 (1017)@sint32;
(*   %call.i.4.7.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7_9, v_call_i_4_7_9);
(*   %arrayidx11.4.7.9 = getelementptr inbounds i16, i16* %r, i64 151 *)
(*   %1183 = load i16, i16* %arrayidx11.4.7.9, align 2, !tbaa !3 *)
mov v1183 mem0_302;
(*   %sub.4.7.9 = sub i16 %1183, %call.i.4.7.9 *)
sub v_sub_4_7_9 v1183 v_call_i_4_7_9;
(*   store i16 %sub.4.7.9, i16* %arrayidx9.4.7.9, align 2, !tbaa !3 *)
mov mem0_318 v_sub_4_7_9;
(*   %add21.4.7.9 = add i16 %1183, %call.i.4.7.9 *)
add v_add21_4_7_9 v1183 v_call_i_4_7_9;
(*   store i16 %add21.4.7.9, i16* %arrayidx11.4.7.9, align 2, !tbaa !3 *)
mov mem0_302 v_add21_4_7_9;

(* NOTE: k = 26 *)

(*   %arrayidx9.4.10 = getelementptr inbounds i16, i16* %r, i64 168 *)
(*   %1184 = load i16, i16* %arrayidx9.4.10, align 2, !tbaa !3 *)
mov v1184 mem0_336;
(*   %conv1.i.4.10 = sext i16 %1184 to i32 *)
cast v_conv1_i_4_10@sint32 v1184@sint16;
(*   %mul.i.4.10 = mul nsw i32 %conv1.i.4.10, 732 *)
mul v_mul_i_4_10 v_conv1_i_4_10 (732)@sint32;
(*   %call.i.4.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_10, v_call_i_4_10);
(*   %arrayidx11.4.10 = getelementptr inbounds i16, i16* %r, i64 160 *)
(*   %1185 = load i16, i16* %arrayidx11.4.10, align 2, !tbaa !3 *)
mov v1185 mem0_320;
(*   %sub.4.10 = sub i16 %1185, %call.i.4.10 *)
sub v_sub_4_10 v1185 v_call_i_4_10;
(*   store i16 %sub.4.10, i16* %arrayidx9.4.10, align 2, !tbaa !3 *)
mov mem0_336 v_sub_4_10;
(*   %add21.4.10 = add i16 %1185, %call.i.4.10 *)
add v_add21_4_10 v1185 v_call_i_4_10;
(*   store i16 %add21.4.10, i16* %arrayidx11.4.10, align 2, !tbaa !3 *)
mov mem0_320 v_add21_4_10;
(*   %arrayidx9.4.1.10 = getelementptr inbounds i16, i16* %r, i64 169 *)
(*   %1186 = load i16, i16* %arrayidx9.4.1.10, align 2, !tbaa !3 *)
mov v1186 mem0_338;
(*   %conv1.i.4.1.10 = sext i16 %1186 to i32 *)
cast v_conv1_i_4_1_10@sint32 v1186@sint16;
(*   %mul.i.4.1.10 = mul nsw i32 %conv1.i.4.1.10, 732 *)
mul v_mul_i_4_1_10 v_conv1_i_4_1_10 (732)@sint32;
(*   %call.i.4.1.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1_10, v_call_i_4_1_10);
(*   %arrayidx11.4.1.10 = getelementptr inbounds i16, i16* %r, i64 161 *)
(*   %1187 = load i16, i16* %arrayidx11.4.1.10, align 2, !tbaa !3 *)
mov v1187 mem0_322;
(*   %sub.4.1.10 = sub i16 %1187, %call.i.4.1.10 *)
sub v_sub_4_1_10 v1187 v_call_i_4_1_10;
(*   store i16 %sub.4.1.10, i16* %arrayidx9.4.1.10, align 2, !tbaa !3 *)
mov mem0_338 v_sub_4_1_10;
(*   %add21.4.1.10 = add i16 %1187, %call.i.4.1.10 *)
add v_add21_4_1_10 v1187 v_call_i_4_1_10;
(*   store i16 %add21.4.1.10, i16* %arrayidx11.4.1.10, align 2, !tbaa !3 *)
mov mem0_322 v_add21_4_1_10;
(*   %arrayidx9.4.2.10 = getelementptr inbounds i16, i16* %r, i64 170 *)
(*   %1188 = load i16, i16* %arrayidx9.4.2.10, align 2, !tbaa !3 *)
mov v1188 mem0_340;
(*   %conv1.i.4.2.10 = sext i16 %1188 to i32 *)
cast v_conv1_i_4_2_10@sint32 v1188@sint16;
(*   %mul.i.4.2.10 = mul nsw i32 %conv1.i.4.2.10, 732 *)
mul v_mul_i_4_2_10 v_conv1_i_4_2_10 (732)@sint32;
(*   %call.i.4.2.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2_10, v_call_i_4_2_10);
(*   %arrayidx11.4.2.10 = getelementptr inbounds i16, i16* %r, i64 162 *)
(*   %1189 = load i16, i16* %arrayidx11.4.2.10, align 2, !tbaa !3 *)
mov v1189 mem0_324;
(*   %sub.4.2.10 = sub i16 %1189, %call.i.4.2.10 *)
sub v_sub_4_2_10 v1189 v_call_i_4_2_10;
(*   store i16 %sub.4.2.10, i16* %arrayidx9.4.2.10, align 2, !tbaa !3 *)
mov mem0_340 v_sub_4_2_10;
(*   %add21.4.2.10 = add i16 %1189, %call.i.4.2.10 *)
add v_add21_4_2_10 v1189 v_call_i_4_2_10;
(*   store i16 %add21.4.2.10, i16* %arrayidx11.4.2.10, align 2, !tbaa !3 *)
mov mem0_324 v_add21_4_2_10;
(*   %arrayidx9.4.3.10 = getelementptr inbounds i16, i16* %r, i64 171 *)
(*   %1190 = load i16, i16* %arrayidx9.4.3.10, align 2, !tbaa !3 *)
mov v1190 mem0_342;
(*   %conv1.i.4.3.10 = sext i16 %1190 to i32 *)
cast v_conv1_i_4_3_10@sint32 v1190@sint16;
(*   %mul.i.4.3.10 = mul nsw i32 %conv1.i.4.3.10, 732 *)
mul v_mul_i_4_3_10 v_conv1_i_4_3_10 (732)@sint32;
(*   %call.i.4.3.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3_10, v_call_i_4_3_10);
(*   %arrayidx11.4.3.10 = getelementptr inbounds i16, i16* %r, i64 163 *)
(*   %1191 = load i16, i16* %arrayidx11.4.3.10, align 2, !tbaa !3 *)
mov v1191 mem0_326;
(*   %sub.4.3.10 = sub i16 %1191, %call.i.4.3.10 *)
sub v_sub_4_3_10 v1191 v_call_i_4_3_10;
(*   store i16 %sub.4.3.10, i16* %arrayidx9.4.3.10, align 2, !tbaa !3 *)
mov mem0_342 v_sub_4_3_10;
(*   %add21.4.3.10 = add i16 %1191, %call.i.4.3.10 *)
add v_add21_4_3_10 v1191 v_call_i_4_3_10;
(*   store i16 %add21.4.3.10, i16* %arrayidx11.4.3.10, align 2, !tbaa !3 *)
mov mem0_326 v_add21_4_3_10;
(*   %arrayidx9.4.4.10 = getelementptr inbounds i16, i16* %r, i64 172 *)
(*   %1192 = load i16, i16* %arrayidx9.4.4.10, align 2, !tbaa !3 *)
mov v1192 mem0_344;
(*   %conv1.i.4.4.10 = sext i16 %1192 to i32 *)
cast v_conv1_i_4_4_10@sint32 v1192@sint16;
(*   %mul.i.4.4.10 = mul nsw i32 %conv1.i.4.4.10, 732 *)
mul v_mul_i_4_4_10 v_conv1_i_4_4_10 (732)@sint32;
(*   %call.i.4.4.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4_10, v_call_i_4_4_10);
(*   %arrayidx11.4.4.10 = getelementptr inbounds i16, i16* %r, i64 164 *)
(*   %1193 = load i16, i16* %arrayidx11.4.4.10, align 2, !tbaa !3 *)
mov v1193 mem0_328;
(*   %sub.4.4.10 = sub i16 %1193, %call.i.4.4.10 *)
sub v_sub_4_4_10 v1193 v_call_i_4_4_10;
(*   store i16 %sub.4.4.10, i16* %arrayidx9.4.4.10, align 2, !tbaa !3 *)
mov mem0_344 v_sub_4_4_10;
(*   %add21.4.4.10 = add i16 %1193, %call.i.4.4.10 *)
add v_add21_4_4_10 v1193 v_call_i_4_4_10;
(*   store i16 %add21.4.4.10, i16* %arrayidx11.4.4.10, align 2, !tbaa !3 *)
mov mem0_328 v_add21_4_4_10;
(*   %arrayidx9.4.5.10 = getelementptr inbounds i16, i16* %r, i64 173 *)
(*   %1194 = load i16, i16* %arrayidx9.4.5.10, align 2, !tbaa !3 *)
mov v1194 mem0_346;
(*   %conv1.i.4.5.10 = sext i16 %1194 to i32 *)
cast v_conv1_i_4_5_10@sint32 v1194@sint16;
(*   %mul.i.4.5.10 = mul nsw i32 %conv1.i.4.5.10, 732 *)
mul v_mul_i_4_5_10 v_conv1_i_4_5_10 (732)@sint32;
(*   %call.i.4.5.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5_10, v_call_i_4_5_10);
(*   %arrayidx11.4.5.10 = getelementptr inbounds i16, i16* %r, i64 165 *)
(*   %1195 = load i16, i16* %arrayidx11.4.5.10, align 2, !tbaa !3 *)
mov v1195 mem0_330;
(*   %sub.4.5.10 = sub i16 %1195, %call.i.4.5.10 *)
sub v_sub_4_5_10 v1195 v_call_i_4_5_10;
(*   store i16 %sub.4.5.10, i16* %arrayidx9.4.5.10, align 2, !tbaa !3 *)
mov mem0_346 v_sub_4_5_10;
(*   %add21.4.5.10 = add i16 %1195, %call.i.4.5.10 *)
add v_add21_4_5_10 v1195 v_call_i_4_5_10;
(*   store i16 %add21.4.5.10, i16* %arrayidx11.4.5.10, align 2, !tbaa !3 *)
mov mem0_330 v_add21_4_5_10;
(*   %arrayidx9.4.6.10 = getelementptr inbounds i16, i16* %r, i64 174 *)
(*   %1196 = load i16, i16* %arrayidx9.4.6.10, align 2, !tbaa !3 *)
mov v1196 mem0_348;
(*   %conv1.i.4.6.10 = sext i16 %1196 to i32 *)
cast v_conv1_i_4_6_10@sint32 v1196@sint16;
(*   %mul.i.4.6.10 = mul nsw i32 %conv1.i.4.6.10, 732 *)
mul v_mul_i_4_6_10 v_conv1_i_4_6_10 (732)@sint32;
(*   %call.i.4.6.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6_10, v_call_i_4_6_10);
(*   %arrayidx11.4.6.10 = getelementptr inbounds i16, i16* %r, i64 166 *)
(*   %1197 = load i16, i16* %arrayidx11.4.6.10, align 2, !tbaa !3 *)
mov v1197 mem0_332;
(*   %sub.4.6.10 = sub i16 %1197, %call.i.4.6.10 *)
sub v_sub_4_6_10 v1197 v_call_i_4_6_10;
(*   store i16 %sub.4.6.10, i16* %arrayidx9.4.6.10, align 2, !tbaa !3 *)
mov mem0_348 v_sub_4_6_10;
(*   %add21.4.6.10 = add i16 %1197, %call.i.4.6.10 *)
add v_add21_4_6_10 v1197 v_call_i_4_6_10;
(*   store i16 %add21.4.6.10, i16* %arrayidx11.4.6.10, align 2, !tbaa !3 *)
mov mem0_332 v_add21_4_6_10;
(*   %arrayidx9.4.7.10 = getelementptr inbounds i16, i16* %r, i64 175 *)
(*   %1198 = load i16, i16* %arrayidx9.4.7.10, align 2, !tbaa !3 *)
mov v1198 mem0_350;
(*   %conv1.i.4.7.10 = sext i16 %1198 to i32 *)
cast v_conv1_i_4_7_10@sint32 v1198@sint16;
(*   %mul.i.4.7.10 = mul nsw i32 %conv1.i.4.7.10, 732 *)
mul v_mul_i_4_7_10 v_conv1_i_4_7_10 (732)@sint32;
(*   %call.i.4.7.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7_10, v_call_i_4_7_10);
(*   %arrayidx11.4.7.10 = getelementptr inbounds i16, i16* %r, i64 167 *)
(*   %1199 = load i16, i16* %arrayidx11.4.7.10, align 2, !tbaa !3 *)
mov v1199 mem0_334;
(*   %sub.4.7.10 = sub i16 %1199, %call.i.4.7.10 *)
sub v_sub_4_7_10 v1199 v_call_i_4_7_10;
(*   store i16 %sub.4.7.10, i16* %arrayidx9.4.7.10, align 2, !tbaa !3 *)
mov mem0_350 v_sub_4_7_10;
(*   %add21.4.7.10 = add i16 %1199, %call.i.4.7.10 *)
add v_add21_4_7_10 v1199 v_call_i_4_7_10;
(*   store i16 %add21.4.7.10, i16* %arrayidx11.4.7.10, align 2, !tbaa !3 *)
mov mem0_334 v_add21_4_7_10;

(* NOTE: k = 27 *)

(*   %arrayidx9.4.11 = getelementptr inbounds i16, i16* %r, i64 184 *)
(*   %1200 = load i16, i16* %arrayidx9.4.11, align 2, !tbaa !3 *)
mov v1200 mem0_368;
(*   %conv1.i.4.11 = sext i16 %1200 to i32 *)
cast v_conv1_i_4_11@sint32 v1200@sint16;
(*   %mul.i.4.11 = mul nsw i32 %conv1.i.4.11, 608 *)
mul v_mul_i_4_11 v_conv1_i_4_11 (608)@sint32;
(*   %call.i.4.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_11, v_call_i_4_11);
(*   %arrayidx11.4.11 = getelementptr inbounds i16, i16* %r, i64 176 *)
(*   %1201 = load i16, i16* %arrayidx11.4.11, align 2, !tbaa !3 *)
mov v1201 mem0_352;
(*   %sub.4.11 = sub i16 %1201, %call.i.4.11 *)
sub v_sub_4_11 v1201 v_call_i_4_11;
(*   store i16 %sub.4.11, i16* %arrayidx9.4.11, align 2, !tbaa !3 *)
mov mem0_368 v_sub_4_11;
(*   %add21.4.11 = add i16 %1201, %call.i.4.11 *)
add v_add21_4_11 v1201 v_call_i_4_11;
(*   store i16 %add21.4.11, i16* %arrayidx11.4.11, align 2, !tbaa !3 *)
mov mem0_352 v_add21_4_11;
(*   %arrayidx9.4.1.11 = getelementptr inbounds i16, i16* %r, i64 185 *)
(*   %1202 = load i16, i16* %arrayidx9.4.1.11, align 2, !tbaa !3 *)
mov v1202 mem0_370;
(*   %conv1.i.4.1.11 = sext i16 %1202 to i32 *)
cast v_conv1_i_4_1_11@sint32 v1202@sint16;
(*   %mul.i.4.1.11 = mul nsw i32 %conv1.i.4.1.11, 608 *)
mul v_mul_i_4_1_11 v_conv1_i_4_1_11 (608)@sint32;
(*   %call.i.4.1.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1_11, v_call_i_4_1_11);
(*   %arrayidx11.4.1.11 = getelementptr inbounds i16, i16* %r, i64 177 *)
(*   %1203 = load i16, i16* %arrayidx11.4.1.11, align 2, !tbaa !3 *)
mov v1203 mem0_354;
(*   %sub.4.1.11 = sub i16 %1203, %call.i.4.1.11 *)
sub v_sub_4_1_11 v1203 v_call_i_4_1_11;
(*   store i16 %sub.4.1.11, i16* %arrayidx9.4.1.11, align 2, !tbaa !3 *)
mov mem0_370 v_sub_4_1_11;
(*   %add21.4.1.11 = add i16 %1203, %call.i.4.1.11 *)
add v_add21_4_1_11 v1203 v_call_i_4_1_11;
(*   store i16 %add21.4.1.11, i16* %arrayidx11.4.1.11, align 2, !tbaa !3 *)
mov mem0_354 v_add21_4_1_11;
(*   %arrayidx9.4.2.11 = getelementptr inbounds i16, i16* %r, i64 186 *)
(*   %1204 = load i16, i16* %arrayidx9.4.2.11, align 2, !tbaa !3 *)
mov v1204 mem0_372;
(*   %conv1.i.4.2.11 = sext i16 %1204 to i32 *)
cast v_conv1_i_4_2_11@sint32 v1204@sint16;
(*   %mul.i.4.2.11 = mul nsw i32 %conv1.i.4.2.11, 608 *)
mul v_mul_i_4_2_11 v_conv1_i_4_2_11 (608)@sint32;
(*   %call.i.4.2.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2_11, v_call_i_4_2_11);
(*   %arrayidx11.4.2.11 = getelementptr inbounds i16, i16* %r, i64 178 *)
(*   %1205 = load i16, i16* %arrayidx11.4.2.11, align 2, !tbaa !3 *)
mov v1205 mem0_356;
(*   %sub.4.2.11 = sub i16 %1205, %call.i.4.2.11 *)
sub v_sub_4_2_11 v1205 v_call_i_4_2_11;
(*   store i16 %sub.4.2.11, i16* %arrayidx9.4.2.11, align 2, !tbaa !3 *)
mov mem0_372 v_sub_4_2_11;
(*   %add21.4.2.11 = add i16 %1205, %call.i.4.2.11 *)
add v_add21_4_2_11 v1205 v_call_i_4_2_11;
(*   store i16 %add21.4.2.11, i16* %arrayidx11.4.2.11, align 2, !tbaa !3 *)
mov mem0_356 v_add21_4_2_11;
(*   %arrayidx9.4.3.11 = getelementptr inbounds i16, i16* %r, i64 187 *)
(*   %1206 = load i16, i16* %arrayidx9.4.3.11, align 2, !tbaa !3 *)
mov v1206 mem0_374;
(*   %conv1.i.4.3.11 = sext i16 %1206 to i32 *)
cast v_conv1_i_4_3_11@sint32 v1206@sint16;
(*   %mul.i.4.3.11 = mul nsw i32 %conv1.i.4.3.11, 608 *)
mul v_mul_i_4_3_11 v_conv1_i_4_3_11 (608)@sint32;
(*   %call.i.4.3.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3_11, v_call_i_4_3_11);
(*   %arrayidx11.4.3.11 = getelementptr inbounds i16, i16* %r, i64 179 *)
(*   %1207 = load i16, i16* %arrayidx11.4.3.11, align 2, !tbaa !3 *)
mov v1207 mem0_358;
(*   %sub.4.3.11 = sub i16 %1207, %call.i.4.3.11 *)
sub v_sub_4_3_11 v1207 v_call_i_4_3_11;
(*   store i16 %sub.4.3.11, i16* %arrayidx9.4.3.11, align 2, !tbaa !3 *)
mov mem0_374 v_sub_4_3_11;
(*   %add21.4.3.11 = add i16 %1207, %call.i.4.3.11 *)
add v_add21_4_3_11 v1207 v_call_i_4_3_11;
(*   store i16 %add21.4.3.11, i16* %arrayidx11.4.3.11, align 2, !tbaa !3 *)
mov mem0_358 v_add21_4_3_11;
(*   %arrayidx9.4.4.11 = getelementptr inbounds i16, i16* %r, i64 188 *)
(*   %1208 = load i16, i16* %arrayidx9.4.4.11, align 2, !tbaa !3 *)
mov v1208 mem0_376;
(*   %conv1.i.4.4.11 = sext i16 %1208 to i32 *)
cast v_conv1_i_4_4_11@sint32 v1208@sint16;
(*   %mul.i.4.4.11 = mul nsw i32 %conv1.i.4.4.11, 608 *)
mul v_mul_i_4_4_11 v_conv1_i_4_4_11 (608)@sint32;
(*   %call.i.4.4.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4_11, v_call_i_4_4_11);
(*   %arrayidx11.4.4.11 = getelementptr inbounds i16, i16* %r, i64 180 *)
(*   %1209 = load i16, i16* %arrayidx11.4.4.11, align 2, !tbaa !3 *)
mov v1209 mem0_360;
(*   %sub.4.4.11 = sub i16 %1209, %call.i.4.4.11 *)
sub v_sub_4_4_11 v1209 v_call_i_4_4_11;
(*   store i16 %sub.4.4.11, i16* %arrayidx9.4.4.11, align 2, !tbaa !3 *)
mov mem0_376 v_sub_4_4_11;
(*   %add21.4.4.11 = add i16 %1209, %call.i.4.4.11 *)
add v_add21_4_4_11 v1209 v_call_i_4_4_11;
(*   store i16 %add21.4.4.11, i16* %arrayidx11.4.4.11, align 2, !tbaa !3 *)
mov mem0_360 v_add21_4_4_11;
(*   %arrayidx9.4.5.11 = getelementptr inbounds i16, i16* %r, i64 189 *)
(*   %1210 = load i16, i16* %arrayidx9.4.5.11, align 2, !tbaa !3 *)
mov v1210 mem0_378;
(*   %conv1.i.4.5.11 = sext i16 %1210 to i32 *)
cast v_conv1_i_4_5_11@sint32 v1210@sint16;
(*   %mul.i.4.5.11 = mul nsw i32 %conv1.i.4.5.11, 608 *)
mul v_mul_i_4_5_11 v_conv1_i_4_5_11 (608)@sint32;
(*   %call.i.4.5.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5_11, v_call_i_4_5_11);
(*   %arrayidx11.4.5.11 = getelementptr inbounds i16, i16* %r, i64 181 *)
(*   %1211 = load i16, i16* %arrayidx11.4.5.11, align 2, !tbaa !3 *)
mov v1211 mem0_362;
(*   %sub.4.5.11 = sub i16 %1211, %call.i.4.5.11 *)
sub v_sub_4_5_11 v1211 v_call_i_4_5_11;
(*   store i16 %sub.4.5.11, i16* %arrayidx9.4.5.11, align 2, !tbaa !3 *)
mov mem0_378 v_sub_4_5_11;
(*   %add21.4.5.11 = add i16 %1211, %call.i.4.5.11 *)
add v_add21_4_5_11 v1211 v_call_i_4_5_11;
(*   store i16 %add21.4.5.11, i16* %arrayidx11.4.5.11, align 2, !tbaa !3 *)
mov mem0_362 v_add21_4_5_11;
(*   %arrayidx9.4.6.11 = getelementptr inbounds i16, i16* %r, i64 190 *)
(*   %1212 = load i16, i16* %arrayidx9.4.6.11, align 2, !tbaa !3 *)
mov v1212 mem0_380;
(*   %conv1.i.4.6.11 = sext i16 %1212 to i32 *)
cast v_conv1_i_4_6_11@sint32 v1212@sint16;
(*   %mul.i.4.6.11 = mul nsw i32 %conv1.i.4.6.11, 608 *)
mul v_mul_i_4_6_11 v_conv1_i_4_6_11 (608)@sint32;
(*   %call.i.4.6.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6_11, v_call_i_4_6_11);
(*   %arrayidx11.4.6.11 = getelementptr inbounds i16, i16* %r, i64 182 *)
(*   %1213 = load i16, i16* %arrayidx11.4.6.11, align 2, !tbaa !3 *)
mov v1213 mem0_364;
(*   %sub.4.6.11 = sub i16 %1213, %call.i.4.6.11 *)
sub v_sub_4_6_11 v1213 v_call_i_4_6_11;
(*   store i16 %sub.4.6.11, i16* %arrayidx9.4.6.11, align 2, !tbaa !3 *)
mov mem0_380 v_sub_4_6_11;
(*   %add21.4.6.11 = add i16 %1213, %call.i.4.6.11 *)
add v_add21_4_6_11 v1213 v_call_i_4_6_11;
(*   store i16 %add21.4.6.11, i16* %arrayidx11.4.6.11, align 2, !tbaa !3 *)
mov mem0_364 v_add21_4_6_11;
(*   %arrayidx9.4.7.11 = getelementptr inbounds i16, i16* %r, i64 191 *)
(*   %1214 = load i16, i16* %arrayidx9.4.7.11, align 2, !tbaa !3 *)
mov v1214 mem0_382;
(*   %conv1.i.4.7.11 = sext i16 %1214 to i32 *)
cast v_conv1_i_4_7_11@sint32 v1214@sint16;
(*   %mul.i.4.7.11 = mul nsw i32 %conv1.i.4.7.11, 608 *)
mul v_mul_i_4_7_11 v_conv1_i_4_7_11 (608)@sint32;
(*   %call.i.4.7.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7_11, v_call_i_4_7_11);
(*   %arrayidx11.4.7.11 = getelementptr inbounds i16, i16* %r, i64 183 *)
(*   %1215 = load i16, i16* %arrayidx11.4.7.11, align 2, !tbaa !3 *)
mov v1215 mem0_366;
(*   %sub.4.7.11 = sub i16 %1215, %call.i.4.7.11 *)
sub v_sub_4_7_11 v1215 v_call_i_4_7_11;
(*   store i16 %sub.4.7.11, i16* %arrayidx9.4.7.11, align 2, !tbaa !3 *)
mov mem0_382 v_sub_4_7_11;
(*   %add21.4.7.11 = add i16 %1215, %call.i.4.7.11 *)
add v_add21_4_7_11 v1215 v_call_i_4_7_11;
(*   store i16 %add21.4.7.11, i16* %arrayidx11.4.7.11, align 2, !tbaa !3 *)
mov mem0_366 v_add21_4_7_11;

(* NOTE: k = 28 *)

(*   %arrayidx9.4.12 = getelementptr inbounds i16, i16* %r, i64 200 *)
(*   %1216 = load i16, i16* %arrayidx9.4.12, align 2, !tbaa !3 *)
mov v1216 mem0_400;
(*   %conv1.i.4.12 = sext i16 %1216 to i32 *)
cast v_conv1_i_4_12@sint32 v1216@sint16;
(*   %mul.i.4.12 = mul nsw i32 %conv1.i.4.12, -1542 *)
mul v_mul_i_4_12 v_conv1_i_4_12 (-1542)@sint32;
(*   %call.i.4.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_12, v_call_i_4_12);
(*   %arrayidx11.4.12 = getelementptr inbounds i16, i16* %r, i64 192 *)
(*   %1217 = load i16, i16* %arrayidx11.4.12, align 2, !tbaa !3 *)
mov v1217 mem0_384;
(*   %sub.4.12 = sub i16 %1217, %call.i.4.12 *)
sub v_sub_4_12 v1217 v_call_i_4_12;
(*   store i16 %sub.4.12, i16* %arrayidx9.4.12, align 2, !tbaa !3 *)
mov mem0_400 v_sub_4_12;
(*   %add21.4.12 = add i16 %1217, %call.i.4.12 *)
add v_add21_4_12 v1217 v_call_i_4_12;
(*   store i16 %add21.4.12, i16* %arrayidx11.4.12, align 2, !tbaa !3 *)
mov mem0_384 v_add21_4_12;
(*   %arrayidx9.4.1.12 = getelementptr inbounds i16, i16* %r, i64 201 *)
(*   %1218 = load i16, i16* %arrayidx9.4.1.12, align 2, !tbaa !3 *)
mov v1218 mem0_402;
(*   %conv1.i.4.1.12 = sext i16 %1218 to i32 *)
cast v_conv1_i_4_1_12@sint32 v1218@sint16;
(*   %mul.i.4.1.12 = mul nsw i32 %conv1.i.4.1.12, -1542 *)
mul v_mul_i_4_1_12 v_conv1_i_4_1_12 (-1542)@sint32;
(*   %call.i.4.1.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1_12, v_call_i_4_1_12);
(*   %arrayidx11.4.1.12 = getelementptr inbounds i16, i16* %r, i64 193 *)
(*   %1219 = load i16, i16* %arrayidx11.4.1.12, align 2, !tbaa !3 *)
mov v1219 mem0_386;
(*   %sub.4.1.12 = sub i16 %1219, %call.i.4.1.12 *)
sub v_sub_4_1_12 v1219 v_call_i_4_1_12;
(*   store i16 %sub.4.1.12, i16* %arrayidx9.4.1.12, align 2, !tbaa !3 *)
mov mem0_402 v_sub_4_1_12;
(*   %add21.4.1.12 = add i16 %1219, %call.i.4.1.12 *)
add v_add21_4_1_12 v1219 v_call_i_4_1_12;
(*   store i16 %add21.4.1.12, i16* %arrayidx11.4.1.12, align 2, !tbaa !3 *)
mov mem0_386 v_add21_4_1_12;
(*   %arrayidx9.4.2.12 = getelementptr inbounds i16, i16* %r, i64 202 *)
(*   %1220 = load i16, i16* %arrayidx9.4.2.12, align 2, !tbaa !3 *)
mov v1220 mem0_404;
(*   %conv1.i.4.2.12 = sext i16 %1220 to i32 *)
cast v_conv1_i_4_2_12@sint32 v1220@sint16;
(*   %mul.i.4.2.12 = mul nsw i32 %conv1.i.4.2.12, -1542 *)
mul v_mul_i_4_2_12 v_conv1_i_4_2_12 (-1542)@sint32;
(*   %call.i.4.2.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2_12, v_call_i_4_2_12);
(*   %arrayidx11.4.2.12 = getelementptr inbounds i16, i16* %r, i64 194 *)
(*   %1221 = load i16, i16* %arrayidx11.4.2.12, align 2, !tbaa !3 *)
mov v1221 mem0_388;
(*   %sub.4.2.12 = sub i16 %1221, %call.i.4.2.12 *)
sub v_sub_4_2_12 v1221 v_call_i_4_2_12;
(*   store i16 %sub.4.2.12, i16* %arrayidx9.4.2.12, align 2, !tbaa !3 *)
mov mem0_404 v_sub_4_2_12;
(*   %add21.4.2.12 = add i16 %1221, %call.i.4.2.12 *)
add v_add21_4_2_12 v1221 v_call_i_4_2_12;
(*   store i16 %add21.4.2.12, i16* %arrayidx11.4.2.12, align 2, !tbaa !3 *)
mov mem0_388 v_add21_4_2_12;
(*   %arrayidx9.4.3.12 = getelementptr inbounds i16, i16* %r, i64 203 *)
(*   %1222 = load i16, i16* %arrayidx9.4.3.12, align 2, !tbaa !3 *)
mov v1222 mem0_406;
(*   %conv1.i.4.3.12 = sext i16 %1222 to i32 *)
cast v_conv1_i_4_3_12@sint32 v1222@sint16;
(*   %mul.i.4.3.12 = mul nsw i32 %conv1.i.4.3.12, -1542 *)
mul v_mul_i_4_3_12 v_conv1_i_4_3_12 (-1542)@sint32;
(*   %call.i.4.3.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3_12, v_call_i_4_3_12);
(*   %arrayidx11.4.3.12 = getelementptr inbounds i16, i16* %r, i64 195 *)
(*   %1223 = load i16, i16* %arrayidx11.4.3.12, align 2, !tbaa !3 *)
mov v1223 mem0_390;
(*   %sub.4.3.12 = sub i16 %1223, %call.i.4.3.12 *)
sub v_sub_4_3_12 v1223 v_call_i_4_3_12;
(*   store i16 %sub.4.3.12, i16* %arrayidx9.4.3.12, align 2, !tbaa !3 *)
mov mem0_406 v_sub_4_3_12;
(*   %add21.4.3.12 = add i16 %1223, %call.i.4.3.12 *)
add v_add21_4_3_12 v1223 v_call_i_4_3_12;
(*   store i16 %add21.4.3.12, i16* %arrayidx11.4.3.12, align 2, !tbaa !3 *)
mov mem0_390 v_add21_4_3_12;
(*   %arrayidx9.4.4.12 = getelementptr inbounds i16, i16* %r, i64 204 *)
(*   %1224 = load i16, i16* %arrayidx9.4.4.12, align 2, !tbaa !3 *)
mov v1224 mem0_408;
(*   %conv1.i.4.4.12 = sext i16 %1224 to i32 *)
cast v_conv1_i_4_4_12@sint32 v1224@sint16;
(*   %mul.i.4.4.12 = mul nsw i32 %conv1.i.4.4.12, -1542 *)
mul v_mul_i_4_4_12 v_conv1_i_4_4_12 (-1542)@sint32;
(*   %call.i.4.4.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4_12, v_call_i_4_4_12);
(*   %arrayidx11.4.4.12 = getelementptr inbounds i16, i16* %r, i64 196 *)
(*   %1225 = load i16, i16* %arrayidx11.4.4.12, align 2, !tbaa !3 *)
mov v1225 mem0_392;
(*   %sub.4.4.12 = sub i16 %1225, %call.i.4.4.12 *)
sub v_sub_4_4_12 v1225 v_call_i_4_4_12;
(*   store i16 %sub.4.4.12, i16* %arrayidx9.4.4.12, align 2, !tbaa !3 *)
mov mem0_408 v_sub_4_4_12;
(*   %add21.4.4.12 = add i16 %1225, %call.i.4.4.12 *)
add v_add21_4_4_12 v1225 v_call_i_4_4_12;
(*   store i16 %add21.4.4.12, i16* %arrayidx11.4.4.12, align 2, !tbaa !3 *)
mov mem0_392 v_add21_4_4_12;
(*   %arrayidx9.4.5.12 = getelementptr inbounds i16, i16* %r, i64 205 *)
(*   %1226 = load i16, i16* %arrayidx9.4.5.12, align 2, !tbaa !3 *)
mov v1226 mem0_410;
(*   %conv1.i.4.5.12 = sext i16 %1226 to i32 *)
cast v_conv1_i_4_5_12@sint32 v1226@sint16;
(*   %mul.i.4.5.12 = mul nsw i32 %conv1.i.4.5.12, -1542 *)
mul v_mul_i_4_5_12 v_conv1_i_4_5_12 (-1542)@sint32;
(*   %call.i.4.5.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5_12, v_call_i_4_5_12);
(*   %arrayidx11.4.5.12 = getelementptr inbounds i16, i16* %r, i64 197 *)
(*   %1227 = load i16, i16* %arrayidx11.4.5.12, align 2, !tbaa !3 *)
mov v1227 mem0_394;
(*   %sub.4.5.12 = sub i16 %1227, %call.i.4.5.12 *)
sub v_sub_4_5_12 v1227 v_call_i_4_5_12;
(*   store i16 %sub.4.5.12, i16* %arrayidx9.4.5.12, align 2, !tbaa !3 *)
mov mem0_410 v_sub_4_5_12;
(*   %add21.4.5.12 = add i16 %1227, %call.i.4.5.12 *)
add v_add21_4_5_12 v1227 v_call_i_4_5_12;
(*   store i16 %add21.4.5.12, i16* %arrayidx11.4.5.12, align 2, !tbaa !3 *)
mov mem0_394 v_add21_4_5_12;
(*   %arrayidx9.4.6.12 = getelementptr inbounds i16, i16* %r, i64 206 *)
(*   %1228 = load i16, i16* %arrayidx9.4.6.12, align 2, !tbaa !3 *)
mov v1228 mem0_412;
(*   %conv1.i.4.6.12 = sext i16 %1228 to i32 *)
cast v_conv1_i_4_6_12@sint32 v1228@sint16;
(*   %mul.i.4.6.12 = mul nsw i32 %conv1.i.4.6.12, -1542 *)
mul v_mul_i_4_6_12 v_conv1_i_4_6_12 (-1542)@sint32;
(*   %call.i.4.6.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6_12, v_call_i_4_6_12);
(*   %arrayidx11.4.6.12 = getelementptr inbounds i16, i16* %r, i64 198 *)
(*   %1229 = load i16, i16* %arrayidx11.4.6.12, align 2, !tbaa !3 *)
mov v1229 mem0_396;
(*   %sub.4.6.12 = sub i16 %1229, %call.i.4.6.12 *)
sub v_sub_4_6_12 v1229 v_call_i_4_6_12;
(*   store i16 %sub.4.6.12, i16* %arrayidx9.4.6.12, align 2, !tbaa !3 *)
mov mem0_412 v_sub_4_6_12;
(*   %add21.4.6.12 = add i16 %1229, %call.i.4.6.12 *)
add v_add21_4_6_12 v1229 v_call_i_4_6_12;
(*   store i16 %add21.4.6.12, i16* %arrayidx11.4.6.12, align 2, !tbaa !3 *)
mov mem0_396 v_add21_4_6_12;
(*   %arrayidx9.4.7.12 = getelementptr inbounds i16, i16* %r, i64 207 *)
(*   %1230 = load i16, i16* %arrayidx9.4.7.12, align 2, !tbaa !3 *)
mov v1230 mem0_414;
(*   %conv1.i.4.7.12 = sext i16 %1230 to i32 *)
cast v_conv1_i_4_7_12@sint32 v1230@sint16;
(*   %mul.i.4.7.12 = mul nsw i32 %conv1.i.4.7.12, -1542 *)
mul v_mul_i_4_7_12 v_conv1_i_4_7_12 (-1542)@sint32;
(*   %call.i.4.7.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7_12, v_call_i_4_7_12);
(*   %arrayidx11.4.7.12 = getelementptr inbounds i16, i16* %r, i64 199 *)
(*   %1231 = load i16, i16* %arrayidx11.4.7.12, align 2, !tbaa !3 *)
mov v1231 mem0_398;
(*   %sub.4.7.12 = sub i16 %1231, %call.i.4.7.12 *)
sub v_sub_4_7_12 v1231 v_call_i_4_7_12;
(*   store i16 %sub.4.7.12, i16* %arrayidx9.4.7.12, align 2, !tbaa !3 *)
mov mem0_414 v_sub_4_7_12;
(*   %add21.4.7.12 = add i16 %1231, %call.i.4.7.12 *)
add v_add21_4_7_12 v1231 v_call_i_4_7_12;
(*   store i16 %add21.4.7.12, i16* %arrayidx11.4.7.12, align 2, !tbaa !3 *)
mov mem0_398 v_add21_4_7_12;

(* NOTE: k = 29 *)

(*   %arrayidx9.4.13 = getelementptr inbounds i16, i16* %r, i64 216 *)
(*   %1232 = load i16, i16* %arrayidx9.4.13, align 2, !tbaa !3 *)
mov v1232 mem0_432;
(*   %conv1.i.4.13 = sext i16 %1232 to i32 *)
cast v_conv1_i_4_13@sint32 v1232@sint16;
(*   %mul.i.4.13 = mul nsw i32 %conv1.i.4.13, 411 *)
mul v_mul_i_4_13 v_conv1_i_4_13 (411)@sint32;
(*   %call.i.4.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_13, v_call_i_4_13);
(*   %arrayidx11.4.13 = getelementptr inbounds i16, i16* %r, i64 208 *)
(*   %1233 = load i16, i16* %arrayidx11.4.13, align 2, !tbaa !3 *)
mov v1233 mem0_416;
(*   %sub.4.13 = sub i16 %1233, %call.i.4.13 *)
sub v_sub_4_13 v1233 v_call_i_4_13;
(*   store i16 %sub.4.13, i16* %arrayidx9.4.13, align 2, !tbaa !3 *)
mov mem0_432 v_sub_4_13;
(*   %add21.4.13 = add i16 %1233, %call.i.4.13 *)
add v_add21_4_13 v1233 v_call_i_4_13;
(*   store i16 %add21.4.13, i16* %arrayidx11.4.13, align 2, !tbaa !3 *)
mov mem0_416 v_add21_4_13;
(*   %arrayidx9.4.1.13 = getelementptr inbounds i16, i16* %r, i64 217 *)
(*   %1234 = load i16, i16* %arrayidx9.4.1.13, align 2, !tbaa !3 *)
mov v1234 mem0_434;
(*   %conv1.i.4.1.13 = sext i16 %1234 to i32 *)
cast v_conv1_i_4_1_13@sint32 v1234@sint16;
(*   %mul.i.4.1.13 = mul nsw i32 %conv1.i.4.1.13, 411 *)
mul v_mul_i_4_1_13 v_conv1_i_4_1_13 (411)@sint32;
(*   %call.i.4.1.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1_13, v_call_i_4_1_13);
(*   %arrayidx11.4.1.13 = getelementptr inbounds i16, i16* %r, i64 209 *)
(*   %1235 = load i16, i16* %arrayidx11.4.1.13, align 2, !tbaa !3 *)
mov v1235 mem0_418;
(*   %sub.4.1.13 = sub i16 %1235, %call.i.4.1.13 *)
sub v_sub_4_1_13 v1235 v_call_i_4_1_13;
(*   store i16 %sub.4.1.13, i16* %arrayidx9.4.1.13, align 2, !tbaa !3 *)
mov mem0_434 v_sub_4_1_13;
(*   %add21.4.1.13 = add i16 %1235, %call.i.4.1.13 *)
add v_add21_4_1_13 v1235 v_call_i_4_1_13;
(*   store i16 %add21.4.1.13, i16* %arrayidx11.4.1.13, align 2, !tbaa !3 *)
mov mem0_418 v_add21_4_1_13;
(*   %arrayidx9.4.2.13 = getelementptr inbounds i16, i16* %r, i64 218 *)
(*   %1236 = load i16, i16* %arrayidx9.4.2.13, align 2, !tbaa !3 *)
mov v1236 mem0_436;
(*   %conv1.i.4.2.13 = sext i16 %1236 to i32 *)
cast v_conv1_i_4_2_13@sint32 v1236@sint16;
(*   %mul.i.4.2.13 = mul nsw i32 %conv1.i.4.2.13, 411 *)
mul v_mul_i_4_2_13 v_conv1_i_4_2_13 (411)@sint32;
(*   %call.i.4.2.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2_13, v_call_i_4_2_13);
(*   %arrayidx11.4.2.13 = getelementptr inbounds i16, i16* %r, i64 210 *)
(*   %1237 = load i16, i16* %arrayidx11.4.2.13, align 2, !tbaa !3 *)
mov v1237 mem0_420;
(*   %sub.4.2.13 = sub i16 %1237, %call.i.4.2.13 *)
sub v_sub_4_2_13 v1237 v_call_i_4_2_13;
(*   store i16 %sub.4.2.13, i16* %arrayidx9.4.2.13, align 2, !tbaa !3 *)
mov mem0_436 v_sub_4_2_13;
(*   %add21.4.2.13 = add i16 %1237, %call.i.4.2.13 *)
add v_add21_4_2_13 v1237 v_call_i_4_2_13;
(*   store i16 %add21.4.2.13, i16* %arrayidx11.4.2.13, align 2, !tbaa !3 *)
mov mem0_420 v_add21_4_2_13;
(*   %arrayidx9.4.3.13 = getelementptr inbounds i16, i16* %r, i64 219 *)
(*   %1238 = load i16, i16* %arrayidx9.4.3.13, align 2, !tbaa !3 *)
mov v1238 mem0_438;
(*   %conv1.i.4.3.13 = sext i16 %1238 to i32 *)
cast v_conv1_i_4_3_13@sint32 v1238@sint16;
(*   %mul.i.4.3.13 = mul nsw i32 %conv1.i.4.3.13, 411 *)
mul v_mul_i_4_3_13 v_conv1_i_4_3_13 (411)@sint32;
(*   %call.i.4.3.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3_13, v_call_i_4_3_13);
(*   %arrayidx11.4.3.13 = getelementptr inbounds i16, i16* %r, i64 211 *)
(*   %1239 = load i16, i16* %arrayidx11.4.3.13, align 2, !tbaa !3 *)
mov v1239 mem0_422;
(*   %sub.4.3.13 = sub i16 %1239, %call.i.4.3.13 *)
sub v_sub_4_3_13 v1239 v_call_i_4_3_13;
(*   store i16 %sub.4.3.13, i16* %arrayidx9.4.3.13, align 2, !tbaa !3 *)
mov mem0_438 v_sub_4_3_13;
(*   %add21.4.3.13 = add i16 %1239, %call.i.4.3.13 *)
add v_add21_4_3_13 v1239 v_call_i_4_3_13;
(*   store i16 %add21.4.3.13, i16* %arrayidx11.4.3.13, align 2, !tbaa !3 *)
mov mem0_422 v_add21_4_3_13;
(*   %arrayidx9.4.4.13 = getelementptr inbounds i16, i16* %r, i64 220 *)
(*   %1240 = load i16, i16* %arrayidx9.4.4.13, align 2, !tbaa !3 *)
mov v1240 mem0_440;
(*   %conv1.i.4.4.13 = sext i16 %1240 to i32 *)
cast v_conv1_i_4_4_13@sint32 v1240@sint16;
(*   %mul.i.4.4.13 = mul nsw i32 %conv1.i.4.4.13, 411 *)
mul v_mul_i_4_4_13 v_conv1_i_4_4_13 (411)@sint32;
(*   %call.i.4.4.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4_13, v_call_i_4_4_13);
(*   %arrayidx11.4.4.13 = getelementptr inbounds i16, i16* %r, i64 212 *)
(*   %1241 = load i16, i16* %arrayidx11.4.4.13, align 2, !tbaa !3 *)
mov v1241 mem0_424;
(*   %sub.4.4.13 = sub i16 %1241, %call.i.4.4.13 *)
sub v_sub_4_4_13 v1241 v_call_i_4_4_13;
(*   store i16 %sub.4.4.13, i16* %arrayidx9.4.4.13, align 2, !tbaa !3 *)
mov mem0_440 v_sub_4_4_13;
(*   %add21.4.4.13 = add i16 %1241, %call.i.4.4.13 *)
add v_add21_4_4_13 v1241 v_call_i_4_4_13;
(*   store i16 %add21.4.4.13, i16* %arrayidx11.4.4.13, align 2, !tbaa !3 *)
mov mem0_424 v_add21_4_4_13;
(*   %arrayidx9.4.5.13 = getelementptr inbounds i16, i16* %r, i64 221 *)
(*   %1242 = load i16, i16* %arrayidx9.4.5.13, align 2, !tbaa !3 *)
mov v1242 mem0_442;
(*   %conv1.i.4.5.13 = sext i16 %1242 to i32 *)
cast v_conv1_i_4_5_13@sint32 v1242@sint16;
(*   %mul.i.4.5.13 = mul nsw i32 %conv1.i.4.5.13, 411 *)
mul v_mul_i_4_5_13 v_conv1_i_4_5_13 (411)@sint32;
(*   %call.i.4.5.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5_13, v_call_i_4_5_13);
(*   %arrayidx11.4.5.13 = getelementptr inbounds i16, i16* %r, i64 213 *)
(*   %1243 = load i16, i16* %arrayidx11.4.5.13, align 2, !tbaa !3 *)
mov v1243 mem0_426;
(*   %sub.4.5.13 = sub i16 %1243, %call.i.4.5.13 *)
sub v_sub_4_5_13 v1243 v_call_i_4_5_13;
(*   store i16 %sub.4.5.13, i16* %arrayidx9.4.5.13, align 2, !tbaa !3 *)
mov mem0_442 v_sub_4_5_13;
(*   %add21.4.5.13 = add i16 %1243, %call.i.4.5.13 *)
add v_add21_4_5_13 v1243 v_call_i_4_5_13;
(*   store i16 %add21.4.5.13, i16* %arrayidx11.4.5.13, align 2, !tbaa !3 *)
mov mem0_426 v_add21_4_5_13;
(*   %arrayidx9.4.6.13 = getelementptr inbounds i16, i16* %r, i64 222 *)
(*   %1244 = load i16, i16* %arrayidx9.4.6.13, align 2, !tbaa !3 *)
mov v1244 mem0_444;
(*   %conv1.i.4.6.13 = sext i16 %1244 to i32 *)
cast v_conv1_i_4_6_13@sint32 v1244@sint16;
(*   %mul.i.4.6.13 = mul nsw i32 %conv1.i.4.6.13, 411 *)
mul v_mul_i_4_6_13 v_conv1_i_4_6_13 (411)@sint32;
(*   %call.i.4.6.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6_13, v_call_i_4_6_13);
(*   %arrayidx11.4.6.13 = getelementptr inbounds i16, i16* %r, i64 214 *)
(*   %1245 = load i16, i16* %arrayidx11.4.6.13, align 2, !tbaa !3 *)
mov v1245 mem0_428;
(*   %sub.4.6.13 = sub i16 %1245, %call.i.4.6.13 *)
sub v_sub_4_6_13 v1245 v_call_i_4_6_13;
(*   store i16 %sub.4.6.13, i16* %arrayidx9.4.6.13, align 2, !tbaa !3 *)
mov mem0_444 v_sub_4_6_13;
(*   %add21.4.6.13 = add i16 %1245, %call.i.4.6.13 *)
add v_add21_4_6_13 v1245 v_call_i_4_6_13;
(*   store i16 %add21.4.6.13, i16* %arrayidx11.4.6.13, align 2, !tbaa !3 *)
mov mem0_428 v_add21_4_6_13;
(*   %arrayidx9.4.7.13 = getelementptr inbounds i16, i16* %r, i64 223 *)
(*   %1246 = load i16, i16* %arrayidx9.4.7.13, align 2, !tbaa !3 *)
mov v1246 mem0_446;
(*   %conv1.i.4.7.13 = sext i16 %1246 to i32 *)
cast v_conv1_i_4_7_13@sint32 v1246@sint16;
(*   %mul.i.4.7.13 = mul nsw i32 %conv1.i.4.7.13, 411 *)
mul v_mul_i_4_7_13 v_conv1_i_4_7_13 (411)@sint32;
(*   %call.i.4.7.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7_13, v_call_i_4_7_13);
(*   %arrayidx11.4.7.13 = getelementptr inbounds i16, i16* %r, i64 215 *)
(*   %1247 = load i16, i16* %arrayidx11.4.7.13, align 2, !tbaa !3 *)
mov v1247 mem0_430;
(*   %sub.4.7.13 = sub i16 %1247, %call.i.4.7.13 *)
sub v_sub_4_7_13 v1247 v_call_i_4_7_13;
(*   store i16 %sub.4.7.13, i16* %arrayidx9.4.7.13, align 2, !tbaa !3 *)
mov mem0_446 v_sub_4_7_13;
(*   %add21.4.7.13 = add i16 %1247, %call.i.4.7.13 *)
add v_add21_4_7_13 v1247 v_call_i_4_7_13;
(*   store i16 %add21.4.7.13, i16* %arrayidx11.4.7.13, align 2, !tbaa !3 *)
mov mem0_430 v_add21_4_7_13;

(* NOTE: k = 30 *)

(*   %arrayidx9.4.14 = getelementptr inbounds i16, i16* %r, i64 232 *)
(*   %1248 = load i16, i16* %arrayidx9.4.14, align 2, !tbaa !3 *)
mov v1248 mem0_464;
(*   %conv1.i.4.14 = sext i16 %1248 to i32 *)
cast v_conv1_i_4_14@sint32 v1248@sint16;
(*   %mul.i.4.14 = mul nsw i32 %conv1.i.4.14, -205 *)
mul v_mul_i_4_14 v_conv1_i_4_14 (-205)@sint32;
(*   %call.i.4.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_14, v_call_i_4_14);
(*   %arrayidx11.4.14 = getelementptr inbounds i16, i16* %r, i64 224 *)
(*   %1249 = load i16, i16* %arrayidx11.4.14, align 2, !tbaa !3 *)
mov v1249 mem0_448;
(*   %sub.4.14 = sub i16 %1249, %call.i.4.14 *)
sub v_sub_4_14 v1249 v_call_i_4_14;
(*   store i16 %sub.4.14, i16* %arrayidx9.4.14, align 2, !tbaa !3 *)
mov mem0_464 v_sub_4_14;
(*   %add21.4.14 = add i16 %1249, %call.i.4.14 *)
add v_add21_4_14 v1249 v_call_i_4_14;
(*   store i16 %add21.4.14, i16* %arrayidx11.4.14, align 2, !tbaa !3 *)
mov mem0_448 v_add21_4_14;
(*   %arrayidx9.4.1.14 = getelementptr inbounds i16, i16* %r, i64 233 *)
(*   %1250 = load i16, i16* %arrayidx9.4.1.14, align 2, !tbaa !3 *)
mov v1250 mem0_466;
(*   %conv1.i.4.1.14 = sext i16 %1250 to i32 *)
cast v_conv1_i_4_1_14@sint32 v1250@sint16;
(*   %mul.i.4.1.14 = mul nsw i32 %conv1.i.4.1.14, -205 *)
mul v_mul_i_4_1_14 v_conv1_i_4_1_14 (-205)@sint32;
(*   %call.i.4.1.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1_14, v_call_i_4_1_14);
(*   %arrayidx11.4.1.14 = getelementptr inbounds i16, i16* %r, i64 225 *)
(*   %1251 = load i16, i16* %arrayidx11.4.1.14, align 2, !tbaa !3 *)
mov v1251 mem0_450;
(*   %sub.4.1.14 = sub i16 %1251, %call.i.4.1.14 *)
sub v_sub_4_1_14 v1251 v_call_i_4_1_14;
(*   store i16 %sub.4.1.14, i16* %arrayidx9.4.1.14, align 2, !tbaa !3 *)
mov mem0_466 v_sub_4_1_14;
(*   %add21.4.1.14 = add i16 %1251, %call.i.4.1.14 *)
add v_add21_4_1_14 v1251 v_call_i_4_1_14;
(*   store i16 %add21.4.1.14, i16* %arrayidx11.4.1.14, align 2, !tbaa !3 *)
mov mem0_450 v_add21_4_1_14;
(*   %arrayidx9.4.2.14 = getelementptr inbounds i16, i16* %r, i64 234 *)
(*   %1252 = load i16, i16* %arrayidx9.4.2.14, align 2, !tbaa !3 *)
mov v1252 mem0_468;
(*   %conv1.i.4.2.14 = sext i16 %1252 to i32 *)
cast v_conv1_i_4_2_14@sint32 v1252@sint16;
(*   %mul.i.4.2.14 = mul nsw i32 %conv1.i.4.2.14, -205 *)
mul v_mul_i_4_2_14 v_conv1_i_4_2_14 (-205)@sint32;
(*   %call.i.4.2.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2_14, v_call_i_4_2_14);
(*   %arrayidx11.4.2.14 = getelementptr inbounds i16, i16* %r, i64 226 *)
(*   %1253 = load i16, i16* %arrayidx11.4.2.14, align 2, !tbaa !3 *)
mov v1253 mem0_452;
(*   %sub.4.2.14 = sub i16 %1253, %call.i.4.2.14 *)
sub v_sub_4_2_14 v1253 v_call_i_4_2_14;
(*   store i16 %sub.4.2.14, i16* %arrayidx9.4.2.14, align 2, !tbaa !3 *)
mov mem0_468 v_sub_4_2_14;
(*   %add21.4.2.14 = add i16 %1253, %call.i.4.2.14 *)
add v_add21_4_2_14 v1253 v_call_i_4_2_14;
(*   store i16 %add21.4.2.14, i16* %arrayidx11.4.2.14, align 2, !tbaa !3 *)
mov mem0_452 v_add21_4_2_14;
(*   %arrayidx9.4.3.14 = getelementptr inbounds i16, i16* %r, i64 235 *)
(*   %1254 = load i16, i16* %arrayidx9.4.3.14, align 2, !tbaa !3 *)
mov v1254 mem0_470;
(*   %conv1.i.4.3.14 = sext i16 %1254 to i32 *)
cast v_conv1_i_4_3_14@sint32 v1254@sint16;
(*   %mul.i.4.3.14 = mul nsw i32 %conv1.i.4.3.14, -205 *)
mul v_mul_i_4_3_14 v_conv1_i_4_3_14 (-205)@sint32;
(*   %call.i.4.3.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3_14, v_call_i_4_3_14);
(*   %arrayidx11.4.3.14 = getelementptr inbounds i16, i16* %r, i64 227 *)
(*   %1255 = load i16, i16* %arrayidx11.4.3.14, align 2, !tbaa !3 *)
mov v1255 mem0_454;
(*   %sub.4.3.14 = sub i16 %1255, %call.i.4.3.14 *)
sub v_sub_4_3_14 v1255 v_call_i_4_3_14;
(*   store i16 %sub.4.3.14, i16* %arrayidx9.4.3.14, align 2, !tbaa !3 *)
mov mem0_470 v_sub_4_3_14;
(*   %add21.4.3.14 = add i16 %1255, %call.i.4.3.14 *)
add v_add21_4_3_14 v1255 v_call_i_4_3_14;
(*   store i16 %add21.4.3.14, i16* %arrayidx11.4.3.14, align 2, !tbaa !3 *)
mov mem0_454 v_add21_4_3_14;
(*   %arrayidx9.4.4.14 = getelementptr inbounds i16, i16* %r, i64 236 *)
(*   %1256 = load i16, i16* %arrayidx9.4.4.14, align 2, !tbaa !3 *)
mov v1256 mem0_472;
(*   %conv1.i.4.4.14 = sext i16 %1256 to i32 *)
cast v_conv1_i_4_4_14@sint32 v1256@sint16;
(*   %mul.i.4.4.14 = mul nsw i32 %conv1.i.4.4.14, -205 *)
mul v_mul_i_4_4_14 v_conv1_i_4_4_14 (-205)@sint32;
(*   %call.i.4.4.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4_14, v_call_i_4_4_14);
(*   %arrayidx11.4.4.14 = getelementptr inbounds i16, i16* %r, i64 228 *)
(*   %1257 = load i16, i16* %arrayidx11.4.4.14, align 2, !tbaa !3 *)
mov v1257 mem0_456;
(*   %sub.4.4.14 = sub i16 %1257, %call.i.4.4.14 *)
sub v_sub_4_4_14 v1257 v_call_i_4_4_14;
(*   store i16 %sub.4.4.14, i16* %arrayidx9.4.4.14, align 2, !tbaa !3 *)
mov mem0_472 v_sub_4_4_14;
(*   %add21.4.4.14 = add i16 %1257, %call.i.4.4.14 *)
add v_add21_4_4_14 v1257 v_call_i_4_4_14;
(*   store i16 %add21.4.4.14, i16* %arrayidx11.4.4.14, align 2, !tbaa !3 *)
mov mem0_456 v_add21_4_4_14;
(*   %arrayidx9.4.5.14 = getelementptr inbounds i16, i16* %r, i64 237 *)
(*   %1258 = load i16, i16* %arrayidx9.4.5.14, align 2, !tbaa !3 *)
mov v1258 mem0_474;
(*   %conv1.i.4.5.14 = sext i16 %1258 to i32 *)
cast v_conv1_i_4_5_14@sint32 v1258@sint16;
(*   %mul.i.4.5.14 = mul nsw i32 %conv1.i.4.5.14, -205 *)
mul v_mul_i_4_5_14 v_conv1_i_4_5_14 (-205)@sint32;
(*   %call.i.4.5.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5_14, v_call_i_4_5_14);
(*   %arrayidx11.4.5.14 = getelementptr inbounds i16, i16* %r, i64 229 *)
(*   %1259 = load i16, i16* %arrayidx11.4.5.14, align 2, !tbaa !3 *)
mov v1259 mem0_458;
(*   %sub.4.5.14 = sub i16 %1259, %call.i.4.5.14 *)
sub v_sub_4_5_14 v1259 v_call_i_4_5_14;
(*   store i16 %sub.4.5.14, i16* %arrayidx9.4.5.14, align 2, !tbaa !3 *)
mov mem0_474 v_sub_4_5_14;
(*   %add21.4.5.14 = add i16 %1259, %call.i.4.5.14 *)
add v_add21_4_5_14 v1259 v_call_i_4_5_14;
(*   store i16 %add21.4.5.14, i16* %arrayidx11.4.5.14, align 2, !tbaa !3 *)
mov mem0_458 v_add21_4_5_14;
(*   %arrayidx9.4.6.14 = getelementptr inbounds i16, i16* %r, i64 238 *)
(*   %1260 = load i16, i16* %arrayidx9.4.6.14, align 2, !tbaa !3 *)
mov v1260 mem0_476;
(*   %conv1.i.4.6.14 = sext i16 %1260 to i32 *)
cast v_conv1_i_4_6_14@sint32 v1260@sint16;
(*   %mul.i.4.6.14 = mul nsw i32 %conv1.i.4.6.14, -205 *)
mul v_mul_i_4_6_14 v_conv1_i_4_6_14 (-205)@sint32;
(*   %call.i.4.6.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6_14, v_call_i_4_6_14);
(*   %arrayidx11.4.6.14 = getelementptr inbounds i16, i16* %r, i64 230 *)
(*   %1261 = load i16, i16* %arrayidx11.4.6.14, align 2, !tbaa !3 *)
mov v1261 mem0_460;
(*   %sub.4.6.14 = sub i16 %1261, %call.i.4.6.14 *)
sub v_sub_4_6_14 v1261 v_call_i_4_6_14;
(*   store i16 %sub.4.6.14, i16* %arrayidx9.4.6.14, align 2, !tbaa !3 *)
mov mem0_476 v_sub_4_6_14;
(*   %add21.4.6.14 = add i16 %1261, %call.i.4.6.14 *)
add v_add21_4_6_14 v1261 v_call_i_4_6_14;
(*   store i16 %add21.4.6.14, i16* %arrayidx11.4.6.14, align 2, !tbaa !3 *)
mov mem0_460 v_add21_4_6_14;
(*   %arrayidx9.4.7.14 = getelementptr inbounds i16, i16* %r, i64 239 *)
(*   %1262 = load i16, i16* %arrayidx9.4.7.14, align 2, !tbaa !3 *)
mov v1262 mem0_478;
(*   %conv1.i.4.7.14 = sext i16 %1262 to i32 *)
cast v_conv1_i_4_7_14@sint32 v1262@sint16;
(*   %mul.i.4.7.14 = mul nsw i32 %conv1.i.4.7.14, -205 *)
mul v_mul_i_4_7_14 v_conv1_i_4_7_14 (-205)@sint32;
(*   %call.i.4.7.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7_14, v_call_i_4_7_14);
(*   %arrayidx11.4.7.14 = getelementptr inbounds i16, i16* %r, i64 231 *)
(*   %1263 = load i16, i16* %arrayidx11.4.7.14, align 2, !tbaa !3 *)
mov v1263 mem0_462;
(*   %sub.4.7.14 = sub i16 %1263, %call.i.4.7.14 *)
sub v_sub_4_7_14 v1263 v_call_i_4_7_14;
(*   store i16 %sub.4.7.14, i16* %arrayidx9.4.7.14, align 2, !tbaa !3 *)
mov mem0_478 v_sub_4_7_14;
(*   %add21.4.7.14 = add i16 %1263, %call.i.4.7.14 *)
add v_add21_4_7_14 v1263 v_call_i_4_7_14;
(*   store i16 %add21.4.7.14, i16* %arrayidx11.4.7.14, align 2, !tbaa !3 *)
mov mem0_462 v_add21_4_7_14;

(* NOTE: k = 31 *)

(*   %arrayidx9.4.15 = getelementptr inbounds i16, i16* %r, i64 248 *)
(*   %1264 = load i16, i16* %arrayidx9.4.15, align 2, !tbaa !3 *)
mov v1264 mem0_496;
(*   %conv1.i.4.15 = sext i16 %1264 to i32 *)
cast v_conv1_i_4_15@sint32 v1264@sint16;
(*   %mul.i.4.15 = mul nsw i32 %conv1.i.4.15, -1571 *)
mul v_mul_i_4_15 v_conv1_i_4_15 (-1571)@sint32;
(*   %call.i.4.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_15, v_call_i_4_15);
(*   %arrayidx11.4.15 = getelementptr inbounds i16, i16* %r, i64 240 *)
(*   %1265 = load i16, i16* %arrayidx11.4.15, align 2, !tbaa !3 *)
mov v1265 mem0_480;
(*   %sub.4.15 = sub i16 %1265, %call.i.4.15 *)
sub v_sub_4_15 v1265 v_call_i_4_15;
(*   store i16 %sub.4.15, i16* %arrayidx9.4.15, align 2, !tbaa !3 *)
mov mem0_496 v_sub_4_15;
(*   %add21.4.15 = add i16 %1265, %call.i.4.15 *)
add v_add21_4_15 v1265 v_call_i_4_15;
(*   store i16 %add21.4.15, i16* %arrayidx11.4.15, align 2, !tbaa !3 *)
mov mem0_480 v_add21_4_15;
(*   %arrayidx9.4.1.15 = getelementptr inbounds i16, i16* %r, i64 249 *)
(*   %1266 = load i16, i16* %arrayidx9.4.1.15, align 2, !tbaa !3 *)
mov v1266 mem0_498;
(*   %conv1.i.4.1.15 = sext i16 %1266 to i32 *)
cast v_conv1_i_4_1_15@sint32 v1266@sint16;
(*   %mul.i.4.1.15 = mul nsw i32 %conv1.i.4.1.15, -1571 *)
mul v_mul_i_4_1_15 v_conv1_i_4_1_15 (-1571)@sint32;
(*   %call.i.4.1.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.1.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_1_15, v_call_i_4_1_15);
(*   %arrayidx11.4.1.15 = getelementptr inbounds i16, i16* %r, i64 241 *)
(*   %1267 = load i16, i16* %arrayidx11.4.1.15, align 2, !tbaa !3 *)
mov v1267 mem0_482;
(*   %sub.4.1.15 = sub i16 %1267, %call.i.4.1.15 *)
sub v_sub_4_1_15 v1267 v_call_i_4_1_15;
(*   store i16 %sub.4.1.15, i16* %arrayidx9.4.1.15, align 2, !tbaa !3 *)
mov mem0_498 v_sub_4_1_15;
(*   %add21.4.1.15 = add i16 %1267, %call.i.4.1.15 *)
add v_add21_4_1_15 v1267 v_call_i_4_1_15;
(*   store i16 %add21.4.1.15, i16* %arrayidx11.4.1.15, align 2, !tbaa !3 *)
mov mem0_482 v_add21_4_1_15;
(*   %arrayidx9.4.2.15 = getelementptr inbounds i16, i16* %r, i64 250 *)
(*   %1268 = load i16, i16* %arrayidx9.4.2.15, align 2, !tbaa !3 *)
mov v1268 mem0_500;
(*   %conv1.i.4.2.15 = sext i16 %1268 to i32 *)
cast v_conv1_i_4_2_15@sint32 v1268@sint16;
(*   %mul.i.4.2.15 = mul nsw i32 %conv1.i.4.2.15, -1571 *)
mul v_mul_i_4_2_15 v_conv1_i_4_2_15 (-1571)@sint32;
(*   %call.i.4.2.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.2.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_2_15, v_call_i_4_2_15);
(*   %arrayidx11.4.2.15 = getelementptr inbounds i16, i16* %r, i64 242 *)
(*   %1269 = load i16, i16* %arrayidx11.4.2.15, align 2, !tbaa !3 *)
mov v1269 mem0_484;
(*   %sub.4.2.15 = sub i16 %1269, %call.i.4.2.15 *)
sub v_sub_4_2_15 v1269 v_call_i_4_2_15;
(*   store i16 %sub.4.2.15, i16* %arrayidx9.4.2.15, align 2, !tbaa !3 *)
mov mem0_500 v_sub_4_2_15;
(*   %add21.4.2.15 = add i16 %1269, %call.i.4.2.15 *)
add v_add21_4_2_15 v1269 v_call_i_4_2_15;
(*   store i16 %add21.4.2.15, i16* %arrayidx11.4.2.15, align 2, !tbaa !3 *)
mov mem0_484 v_add21_4_2_15;
(*   %arrayidx9.4.3.15 = getelementptr inbounds i16, i16* %r, i64 251 *)
(*   %1270 = load i16, i16* %arrayidx9.4.3.15, align 2, !tbaa !3 *)
mov v1270 mem0_502;
(*   %conv1.i.4.3.15 = sext i16 %1270 to i32 *)
cast v_conv1_i_4_3_15@sint32 v1270@sint16;
(*   %mul.i.4.3.15 = mul nsw i32 %conv1.i.4.3.15, -1571 *)
mul v_mul_i_4_3_15 v_conv1_i_4_3_15 (-1571)@sint32;
(*   %call.i.4.3.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.3.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_3_15, v_call_i_4_3_15);
(*   %arrayidx11.4.3.15 = getelementptr inbounds i16, i16* %r, i64 243 *)
(*   %1271 = load i16, i16* %arrayidx11.4.3.15, align 2, !tbaa !3 *)
mov v1271 mem0_486;
(*   %sub.4.3.15 = sub i16 %1271, %call.i.4.3.15 *)
sub v_sub_4_3_15 v1271 v_call_i_4_3_15;
(*   store i16 %sub.4.3.15, i16* %arrayidx9.4.3.15, align 2, !tbaa !3 *)
mov mem0_502 v_sub_4_3_15;
(*   %add21.4.3.15 = add i16 %1271, %call.i.4.3.15 *)
add v_add21_4_3_15 v1271 v_call_i_4_3_15;
(*   store i16 %add21.4.3.15, i16* %arrayidx11.4.3.15, align 2, !tbaa !3 *)
mov mem0_486 v_add21_4_3_15;
(*   %arrayidx9.4.4.15 = getelementptr inbounds i16, i16* %r, i64 252 *)
(*   %1272 = load i16, i16* %arrayidx9.4.4.15, align 2, !tbaa !3 *)
mov v1272 mem0_504;
(*   %conv1.i.4.4.15 = sext i16 %1272 to i32 *)
cast v_conv1_i_4_4_15@sint32 v1272@sint16;
(*   %mul.i.4.4.15 = mul nsw i32 %conv1.i.4.4.15, -1571 *)
mul v_mul_i_4_4_15 v_conv1_i_4_4_15 (-1571)@sint32;
(*   %call.i.4.4.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.4.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_4_15, v_call_i_4_4_15);
(*   %arrayidx11.4.4.15 = getelementptr inbounds i16, i16* %r, i64 244 *)
(*   %1273 = load i16, i16* %arrayidx11.4.4.15, align 2, !tbaa !3 *)
mov v1273 mem0_488;
(*   %sub.4.4.15 = sub i16 %1273, %call.i.4.4.15 *)
sub v_sub_4_4_15 v1273 v_call_i_4_4_15;
(*   store i16 %sub.4.4.15, i16* %arrayidx9.4.4.15, align 2, !tbaa !3 *)
mov mem0_504 v_sub_4_4_15;
(*   %add21.4.4.15 = add i16 %1273, %call.i.4.4.15 *)
add v_add21_4_4_15 v1273 v_call_i_4_4_15;
(*   store i16 %add21.4.4.15, i16* %arrayidx11.4.4.15, align 2, !tbaa !3 *)
mov mem0_488 v_add21_4_4_15;
(*   %arrayidx9.4.5.15 = getelementptr inbounds i16, i16* %r, i64 253 *)
(*   %1274 = load i16, i16* %arrayidx9.4.5.15, align 2, !tbaa !3 *)
mov v1274 mem0_506;
(*   %conv1.i.4.5.15 = sext i16 %1274 to i32 *)
cast v_conv1_i_4_5_15@sint32 v1274@sint16;
(*   %mul.i.4.5.15 = mul nsw i32 %conv1.i.4.5.15, -1571 *)
mul v_mul_i_4_5_15 v_conv1_i_4_5_15 (-1571)@sint32;
(*   %call.i.4.5.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.5.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_5_15, v_call_i_4_5_15);
(*   %arrayidx11.4.5.15 = getelementptr inbounds i16, i16* %r, i64 245 *)
(*   %1275 = load i16, i16* %arrayidx11.4.5.15, align 2, !tbaa !3 *)
mov v1275 mem0_490;
(*   %sub.4.5.15 = sub i16 %1275, %call.i.4.5.15 *)
sub v_sub_4_5_15 v1275 v_call_i_4_5_15;
(*   store i16 %sub.4.5.15, i16* %arrayidx9.4.5.15, align 2, !tbaa !3 *)
mov mem0_506 v_sub_4_5_15;
(*   %add21.4.5.15 = add i16 %1275, %call.i.4.5.15 *)
add v_add21_4_5_15 v1275 v_call_i_4_5_15;
(*   store i16 %add21.4.5.15, i16* %arrayidx11.4.5.15, align 2, !tbaa !3 *)
mov mem0_490 v_add21_4_5_15;
(*   %arrayidx9.4.6.15 = getelementptr inbounds i16, i16* %r, i64 254 *)
(*   %1276 = load i16, i16* %arrayidx9.4.6.15, align 2, !tbaa !3 *)
mov v1276 mem0_508;
(*   %conv1.i.4.6.15 = sext i16 %1276 to i32 *)
cast v_conv1_i_4_6_15@sint32 v1276@sint16;
(*   %mul.i.4.6.15 = mul nsw i32 %conv1.i.4.6.15, -1571 *)
mul v_mul_i_4_6_15 v_conv1_i_4_6_15 (-1571)@sint32;
(*   %call.i.4.6.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.6.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_6_15, v_call_i_4_6_15);
(*   %arrayidx11.4.6.15 = getelementptr inbounds i16, i16* %r, i64 246 *)
(*   %1277 = load i16, i16* %arrayidx11.4.6.15, align 2, !tbaa !3 *)
mov v1277 mem0_492;
(*   %sub.4.6.15 = sub i16 %1277, %call.i.4.6.15 *)
sub v_sub_4_6_15 v1277 v_call_i_4_6_15;
(*   store i16 %sub.4.6.15, i16* %arrayidx9.4.6.15, align 2, !tbaa !3 *)
mov mem0_508 v_sub_4_6_15;
(*   %add21.4.6.15 = add i16 %1277, %call.i.4.6.15 *)
add v_add21_4_6_15 v1277 v_call_i_4_6_15;
(*   store i16 %add21.4.6.15, i16* %arrayidx11.4.6.15, align 2, !tbaa !3 *)
mov mem0_492 v_add21_4_6_15;
(*   %arrayidx9.4.7.15 = getelementptr inbounds i16, i16* %r, i64 255 *)
(*   %1278 = load i16, i16* %arrayidx9.4.7.15, align 2, !tbaa !3 *)
mov v1278 mem0_510;
(*   %conv1.i.4.7.15 = sext i16 %1278 to i32 *)
cast v_conv1_i_4_7_15@sint32 v1278@sint16;
(*   %mul.i.4.7.15 = mul nsw i32 %conv1.i.4.7.15, -1571 *)
mul v_mul_i_4_7_15 v_conv1_i_4_7_15 (-1571)@sint32;
(*   %call.i.4.7.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4.7.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4_7_15, v_call_i_4_7_15);
(*   %arrayidx11.4.7.15 = getelementptr inbounds i16, i16* %r, i64 247 *)
(*   %1279 = load i16, i16* %arrayidx11.4.7.15, align 2, !tbaa !3 *)
mov v1279 mem0_494;
(*   %sub.4.7.15 = sub i16 %1279, %call.i.4.7.15 *)
sub v_sub_4_7_15 v1279 v_call_i_4_7_15;
(*   store i16 %sub.4.7.15, i16* %arrayidx9.4.7.15, align 2, !tbaa !3 *)
mov mem0_510 v_sub_4_7_15;
(*   %add21.4.7.15 = add i16 %1279, %call.i.4.7.15 *)
add v_add21_4_7_15 v1279 v_call_i_4_7_15;
(*   store i16 %add21.4.7.15, i16* %arrayidx11.4.7.15, align 2, !tbaa !3 *)
mov mem0_494 v_add21_4_7_15;

(* NOTE: summary of 5 iterations *)

{
and [ 

eqmod 
(
mem0_0_k15*(x**0) + mem0_2_k15*(x**1) + mem0_4_k15*(x**2) + mem0_6_k15*(x**3) +
mem0_8_k15*(x**4) + mem0_10_k15*(x**5) + mem0_12_k15*(x**6) + mem0_14_k15*(x**7) +
mem0_16_k15*(x**8) + mem0_18_k15*(x**9) + mem0_20_k15*(x**10) + mem0_22_k15*(x**11) +
mem0_24_k15*(x**12) + mem0_26_k15*(x**13) + mem0_28_k15*(x**14) + mem0_30_k15*(x**15)
)
(
mem0_0*(x**0) + mem0_2*(x**1) + mem0_4*(x**2) + mem0_6*(x**3) + 
mem0_8*(x**4) + mem0_10*(x**5) + mem0_12*(x**6) + mem0_14*(x**7)
)
[3329, x**8 - 296],
eqmod 
(
mem0_0_k15*(x**0) + mem0_2_k15*(x**1) + mem0_4_k15*(x**2) + mem0_6_k15*(x**3) +
mem0_8_k15*(x**4) + mem0_10_k15*(x**5) + mem0_12_k15*(x**6) + mem0_14_k15*(x**7) +
mem0_16_k15*(x**8) + mem0_18_k15*(x**9) + mem0_20_k15*(x**10) + mem0_22_k15*(x**11) +
mem0_24_k15*(x**12) + mem0_26_k15*(x**13) + mem0_28_k15*(x**14) + mem0_30_k15*(x**15) 
)
(
mem0_16*(x**0) + mem0_18*(x**1) + mem0_20*(x**2) + mem0_22*(x**3) + 
mem0_24*(x**4) + mem0_26*(x**5) + mem0_28*(x**6) + mem0_30*(x**7)
)
[3329, x**8 - 3033],
eqmod 
(
mem0_32_k15*(x**0) + mem0_34_k15*(x**1) + mem0_36_k15*(x**2) + mem0_38_k15*(x**3) +
mem0_40_k15*(x**4) + mem0_42_k15*(x**5) + mem0_44_k15*(x**6) + mem0_46_k15*(x**7) +
mem0_48_k15*(x**8) + mem0_50_k15*(x**9) + mem0_52_k15*(x**10) + mem0_54_k15*(x**11) +
mem0_56_k15*(x**12) + mem0_58_k15*(x**13) + mem0_60_k15*(x**14) + mem0_62_k15*(x**15) 
)
(
mem0_32*(x**0) + mem0_34*(x**1) + mem0_36*(x**2) + mem0_38*(x**3) + 
mem0_40*(x**4) + mem0_42*(x**5) + mem0_44*(x**6) + mem0_46*(x**7)
)
[3329, x**8 - 2447],
eqmod 
(
mem0_32_k15*(x**0) + mem0_34_k15*(x**1) + mem0_36_k15*(x**2) + mem0_38_k15*(x**3) +
mem0_40_k15*(x**4) + mem0_42_k15*(x**5) + mem0_44_k15*(x**6) + mem0_46_k15*(x**7) +
mem0_48_k15*(x**8) + mem0_50_k15*(x**9) + mem0_52_k15*(x**10) + mem0_54_k15*(x**11) +
mem0_56_k15*(x**12) + mem0_58_k15*(x**13) + mem0_60_k15*(x**14) + mem0_62_k15*(x**15) 
)
(
mem0_48*(x**0) + mem0_50*(x**1) + mem0_52*(x**2) + mem0_54*(x**3) + 
mem0_56*(x**4) + mem0_58*(x**5) + mem0_60*(x**6) + mem0_62*(x**7)
)
[3329, x**8 - 882],
eqmod 
(
mem0_64_k15*(x**0) + mem0_66_k15*(x**1) + mem0_68_k15*(x**2) + mem0_70_k15*(x**3) +
mem0_72_k15*(x**4) + mem0_74_k15*(x**5) + mem0_76_k15*(x**6) + mem0_78_k15*(x**7) +
mem0_80_k15*(x**8) + mem0_82_k15*(x**9) + mem0_84_k15*(x**10) + mem0_86_k15*(x**11) +
mem0_88_k15*(x**12) + mem0_90_k15*(x**13) + mem0_92_k15*(x**14) + mem0_94_k15*(x**15) 
)
(
mem0_64*(x**0) + mem0_66*(x**1) + mem0_68*(x**2) + mem0_70*(x**3) + 
mem0_72*(x**4) + mem0_74*(x**5) + mem0_76*(x**6) + mem0_78*(x**7)
)
[3329, x**8 - 1339],
eqmod 
(
mem0_64_k15*(x**0) + mem0_66_k15*(x**1) + mem0_68_k15*(x**2) + mem0_70_k15*(x**3) +
mem0_72_k15*(x**4) + mem0_74_k15*(x**5) + mem0_76_k15*(x**6) + mem0_78_k15*(x**7) +
mem0_80_k15*(x**8) + mem0_82_k15*(x**9) + mem0_84_k15*(x**10) + mem0_86_k15*(x**11) +
mem0_88_k15*(x**12) + mem0_90_k15*(x**13) + mem0_92_k15*(x**14) + mem0_94_k15*(x**15) 
)
(
mem0_80*(x**0) + mem0_82*(x**1) + mem0_84*(x**2) + mem0_86*(x**3) + 
mem0_88*(x**4) + mem0_90*(x**5) + mem0_92*(x**6) + mem0_94*(x**7)
)
[3329, x**8 - 1990],
eqmod 
(
mem0_96_k15*(x**0) + mem0_98_k15*(x**1) + mem0_100_k15*(x**2) + mem0_102_k15*(x**3) +
mem0_104_k15*(x**4) + mem0_106_k15*(x**5) + mem0_108_k15*(x**6) + mem0_110_k15*(x**7) +
mem0_112_k15*(x**8) + mem0_114_k15*(x**9) + mem0_116_k15*(x**10) + mem0_118_k15*(x**11) +
mem0_120_k15*(x**12) + mem0_122_k15*(x**13) + mem0_124_k15*(x**14) + mem0_126_k15*(x**15) 
)
(
mem0_96*(x**0) + mem0_98*(x**1) + mem0_100*(x**2) + mem0_102*(x**3) + 
mem0_104*(x**4) + mem0_106*(x**5) + mem0_108*(x**6) + mem0_110*(x**7)
)
[3329, x**8 - 1476],
eqmod 
(
mem0_96_k15*(x**0) + mem0_98_k15*(x**1) + mem0_100_k15*(x**2) + mem0_102_k15*(x**3) +
mem0_104_k15*(x**4) + mem0_106_k15*(x**5) + mem0_108_k15*(x**6) + mem0_110_k15*(x**7) +
mem0_112_k15*(x**8) + mem0_114_k15*(x**9) + mem0_116_k15*(x**10) + mem0_118_k15*(x**11) +
mem0_120_k15*(x**12) + mem0_122_k15*(x**13) + mem0_124_k15*(x**14) + mem0_126_k15*(x**15) 
)
(
mem0_112*(x**0) + mem0_114*(x**1) + mem0_116*(x**2) + mem0_118*(x**3) + 
mem0_120*(x**4) + mem0_122*(x**5) + mem0_124*(x**6) + mem0_126*(x**7)
)
[3329, x**8 - 1853],
eqmod 
(
mem0_128_k15*(x**0) + mem0_130_k15*(x**1) + mem0_132_k15*(x**2) + mem0_134_k15*(x**3) +
mem0_136_k15*(x**4) + mem0_138_k15*(x**5) + mem0_140_k15*(x**6) + mem0_142_k15*(x**7) +
mem0_144_k15*(x**8) + mem0_146_k15*(x**9) + mem0_148_k15*(x**10) + mem0_150_k15*(x**11) +
mem0_152_k15*(x**12) + mem0_154_k15*(x**13) + mem0_156_k15*(x**14) + mem0_158_k15*(x**15) 
)
(
mem0_128*(x**0) + mem0_130*(x**1) + mem0_132*(x**2) + mem0_134*(x**3) + 
mem0_136*(x**4) + mem0_138*(x**5) + mem0_140*(x**6) + mem0_142*(x**7)
)
[3329, x**8 - 3046],
eqmod 
(
mem0_128_k15*(x**0) + mem0_130_k15*(x**1) + mem0_132_k15*(x**2) + mem0_134_k15*(x**3) +
mem0_136_k15*(x**4) + mem0_138_k15*(x**5) + mem0_140_k15*(x**6) + mem0_142_k15*(x**7) +
mem0_144_k15*(x**8) + mem0_146_k15*(x**9) + mem0_148_k15*(x**10) + mem0_150_k15*(x**11) +
mem0_152_k15*(x**12) + mem0_154_k15*(x**13) + mem0_156_k15*(x**14) + mem0_158_k15*(x**15) 
)
(
mem0_144*(x**0) + mem0_146*(x**1) + mem0_148*(x**2) + mem0_150*(x**3) + 
mem0_152*(x**4) + mem0_154*(x**5) + mem0_156*(x**6) + mem0_158*(x**7)
)
[3329, x**8 - 283],
eqmod 
(
mem0_160_k15*(x**0) + mem0_162_k15*(x**1) + mem0_164_k15*(x**2) + mem0_166_k15*(x**3) +
mem0_168_k15*(x**4) + mem0_170_k15*(x**5) + mem0_172_k15*(x**6) + mem0_174_k15*(x**7) +
mem0_176_k15*(x**8) + mem0_178_k15*(x**9) + mem0_180_k15*(x**10) + mem0_182_k15*(x**11) +
mem0_184_k15*(x**12) + mem0_186_k15*(x**13) + mem0_188_k15*(x**14) + mem0_190_k15*(x**15) 
)
(
mem0_160*(x**0) + mem0_162*(x**1) + mem0_164*(x**2) + mem0_166*(x**3) + 
mem0_168*(x**4) + mem0_170*(x**5) + mem0_172*(x**6) + mem0_174*(x**7)
)
[3329, x**8 - 56],
eqmod 
(
mem0_160_k15*(x**0) + mem0_162_k15*(x**1) + mem0_164_k15*(x**2) + mem0_166_k15*(x**3) +
mem0_168_k15*(x**4) + mem0_170_k15*(x**5) + mem0_172_k15*(x**6) + mem0_174_k15*(x**7) +
mem0_176_k15*(x**8) + mem0_178_k15*(x**9) + mem0_180_k15*(x**10) + mem0_182_k15*(x**11) +
mem0_184_k15*(x**12) + mem0_186_k15*(x**13) + mem0_188_k15*(x**14) + mem0_190_k15*(x**15) 
)
(
mem0_176*(x**0) + mem0_178*(x**1) + mem0_180*(x**2) + mem0_182*(x**3) + 
mem0_184*(x**4) + mem0_186*(x**5) + mem0_188*(x**6) + mem0_190*(x**7)
)
[3329, x**8 - 3273],
eqmod 
(
mem0_192_k15*(x**0) + mem0_194_k15*(x**1) + mem0_196_k15*(x**2) + mem0_198_k15*(x**3) +
mem0_200_k15*(x**4) + mem0_202_k15*(x**5) + mem0_204_k15*(x**6) + mem0_206_k15*(x**7) +
mem0_208_k15*(x**8) + mem0_210_k15*(x**9) + mem0_212_k15*(x**10) + mem0_214_k15*(x**11) +
mem0_216_k15*(x**12) + mem0_218_k15*(x**13) + mem0_220_k15*(x**14) + mem0_222_k15*(x**15) 
)
(
mem0_192*(x**0) + mem0_194*(x**1) + mem0_196*(x**2) + mem0_198*(x**3) + 
mem0_200*(x**4) + mem0_202*(x**5) + mem0_204*(x**6) + mem0_206*(x**7)
)
[3329, x**8 - 2240],
eqmod 
(
mem0_192_k15*(x**0) + mem0_194_k15*(x**1) + mem0_196_k15*(x**2) + mem0_198_k15*(x**3) +
mem0_200_k15*(x**4) + mem0_202_k15*(x**5) + mem0_204_k15*(x**6) + mem0_206_k15*(x**7) +
mem0_208_k15*(x**8) + mem0_210_k15*(x**9) + mem0_212_k15*(x**10) + mem0_214_k15*(x**11) +
mem0_216_k15*(x**12) + mem0_218_k15*(x**13) + mem0_220_k15*(x**14) + mem0_222_k15*(x**15) 
)
(
mem0_208*(x**0) + mem0_210*(x**1) + mem0_212*(x**2) + mem0_214*(x**3) + 
mem0_216*(x**4) + mem0_218*(x**5) + mem0_220*(x**6) + mem0_222*(x**7)
)
[3329, x**8 - 1089],
eqmod 
(
mem0_224_k15*(x**0) + mem0_226_k15*(x**1) + mem0_228_k15*(x**2) + mem0_230_k15*(x**3) +
mem0_232_k15*(x**4) + mem0_234_k15*(x**5) + mem0_236_k15*(x**6) + mem0_238_k15*(x**7) +
mem0_240_k15*(x**8) + mem0_242_k15*(x**9) + mem0_244_k15*(x**10) + mem0_246_k15*(x**11) +
mem0_248_k15*(x**12) + mem0_250_k15*(x**13) + mem0_252_k15*(x**14) + mem0_254_k15*(x**15) 
)
(
mem0_224*(x**0) + mem0_226*(x**1) + mem0_228*(x**2) + mem0_230*(x**3) + 
mem0_232*(x**4) + mem0_234*(x**5) + mem0_236*(x**6) + mem0_238*(x**7)
)
[3329, x**8 - 1333],
eqmod 
(
mem0_224_k15*(x**0) + mem0_226_k15*(x**1) + mem0_228_k15*(x**2) + mem0_230_k15*(x**3) +
mem0_232_k15*(x**4) + mem0_234_k15*(x**5) + mem0_236_k15*(x**6) + mem0_238_k15*(x**7) +
mem0_240_k15*(x**8) + mem0_242_k15*(x**9) + mem0_244_k15*(x**10) + mem0_246_k15*(x**11) +
mem0_248_k15*(x**12) + mem0_250_k15*(x**13) + mem0_252_k15*(x**14) + mem0_254_k15*(x**15) 
)
(
mem0_240*(x**0) + mem0_242*(x**1) + mem0_244*(x**2) + mem0_246*(x**3) + 
mem0_248*(x**4) + mem0_250*(x**5) + mem0_252*(x**6) + mem0_254*(x**7)
)
[3329, x**8 - 1996],
eqmod 
(
mem0_256_k15*(x**0) + mem0_258_k15*(x**1) + mem0_260_k15*(x**2) + mem0_262_k15*(x**3) +
mem0_264_k15*(x**4) + mem0_266_k15*(x**5) + mem0_268_k15*(x**6) + mem0_270_k15*(x**7) +
mem0_272_k15*(x**8) + mem0_274_k15*(x**9) + mem0_276_k15*(x**10) + mem0_278_k15*(x**11) +
mem0_280_k15*(x**12) + mem0_282_k15*(x**13) + mem0_284_k15*(x**14) + mem0_286_k15*(x**15) 
)
(
mem0_256*(x**0) + mem0_258*(x**1) + mem0_260*(x**2) + mem0_262*(x**3) + 
mem0_264*(x**4) + mem0_266*(x**5) + mem0_268*(x**6) + mem0_270*(x**7)
)
[3329, x**8 - 1426],
eqmod 
(
mem0_256_k15*(x**0) + mem0_258_k15*(x**1) + mem0_260_k15*(x**2) + mem0_262_k15*(x**3) +
mem0_264_k15*(x**4) + mem0_266_k15*(x**5) + mem0_268_k15*(x**6) + mem0_270_k15*(x**7) +
mem0_272_k15*(x**8) + mem0_274_k15*(x**9) + mem0_276_k15*(x**10) + mem0_278_k15*(x**11) +
mem0_280_k15*(x**12) + mem0_282_k15*(x**13) + mem0_284_k15*(x**14) + mem0_286_k15*(x**15) 
)
(
mem0_272*(x**0) + mem0_274*(x**1) + mem0_276*(x**2) + mem0_278*(x**3) + 
mem0_280*(x**4) + mem0_282*(x**5) + mem0_284*(x**6) + mem0_286*(x**7)
)
[3329, x**8 - 1903],
eqmod 
(
mem0_288_k15*(x**0) + mem0_290_k15*(x**1) + mem0_292_k15*(x**2) + mem0_294_k15*(x**3) +
mem0_296_k15*(x**4) + mem0_298_k15*(x**5) + mem0_300_k15*(x**6) + mem0_302_k15*(x**7) +
mem0_304_k15*(x**8) + mem0_306_k15*(x**9) + mem0_308_k15*(x**10) + mem0_310_k15*(x**11) +
mem0_312_k15*(x**12) + mem0_314_k15*(x**13) + mem0_316_k15*(x**14) + mem0_318_k15*(x**15) 
)
(
mem0_288*(x**0) + mem0_290*(x**1) + mem0_292*(x**2) + mem0_294*(x**3) + 
mem0_296*(x**4) + mem0_298*(x**5) + mem0_300*(x**6) + mem0_302*(x**7)
)
[3329, x**8 - 2094],
eqmod 
(
mem0_288_k15*(x**0) + mem0_290_k15*(x**1) + mem0_292_k15*(x**2) + mem0_294_k15*(x**3) +
mem0_296_k15*(x**4) + mem0_298_k15*(x**5) + mem0_300_k15*(x**6) + mem0_302_k15*(x**7) +
mem0_304_k15*(x**8) + mem0_306_k15*(x**9) + mem0_308_k15*(x**10) + mem0_310_k15*(x**11) +
mem0_312_k15*(x**12) + mem0_314_k15*(x**13) + mem0_316_k15*(x**14) + mem0_318_k15*(x**15) 
)
(
mem0_304*(x**0) + mem0_306*(x**1) + mem0_308*(x**2) + mem0_310*(x**3) + 
mem0_312*(x**4) + mem0_314*(x**5) + mem0_316*(x**6) + mem0_318*(x**7)
)
[3329, x**8 - 1235],
eqmod 
(
mem0_320_k15*(x**0) + mem0_322_k15*(x**1) + mem0_324_k15*(x**2) + mem0_326_k15*(x**3) +
mem0_328_k15*(x**4) + mem0_330_k15*(x**5) + mem0_332_k15*(x**6) + mem0_334_k15*(x**7) +
mem0_336_k15*(x**8) + mem0_338_k15*(x**9) + mem0_340_k15*(x**10) + mem0_342_k15*(x**11) +
mem0_344_k15*(x**12) + mem0_346_k15*(x**13) + mem0_348_k15*(x**14) + mem0_350_k15*(x**15) 
)
(
mem0_320*(x**0) + mem0_322*(x**1) + mem0_324*(x**2) + mem0_326*(x**3) + 
mem0_328*(x**4) + mem0_330*(x**5) + mem0_332*(x**6) + mem0_334*(x**7)
)
[3329, x**8 - 535],
eqmod 
(
mem0_320_k15*(x**0) + mem0_322_k15*(x**1) + mem0_324_k15*(x**2) + mem0_326_k15*(x**3) +
mem0_328_k15*(x**4) + mem0_330_k15*(x**5) + mem0_332_k15*(x**6) + mem0_334_k15*(x**7) +
mem0_336_k15*(x**8) + mem0_338_k15*(x**9) + mem0_340_k15*(x**10) + mem0_342_k15*(x**11) +
mem0_344_k15*(x**12) + mem0_346_k15*(x**13) + mem0_348_k15*(x**14) + mem0_350_k15*(x**15) 
)
(
mem0_336*(x**0) + mem0_338*(x**1) + mem0_340*(x**2) + mem0_342*(x**3) + 
mem0_344*(x**4) + mem0_346*(x**5) + mem0_348*(x**6) + mem0_350*(x**7)
)
[3329, x**8 - 2794],
eqmod 
(
mem0_352_k15*(x**0) + mem0_354_k15*(x**1) + mem0_356_k15*(x**2) + mem0_358_k15*(x**3) +
mem0_360_k15*(x**4) + mem0_362_k15*(x**5) + mem0_364_k15*(x**6) + mem0_366_k15*(x**7) +
mem0_368_k15*(x**8) + mem0_370_k15*(x**9) + mem0_372_k15*(x**10) + mem0_374_k15*(x**11) +
mem0_376_k15*(x**12) + mem0_378_k15*(x**13) + mem0_380_k15*(x**14) + mem0_382_k15*(x**15) 
)
(
mem0_352*(x**0) + mem0_354*(x**1) + mem0_356*(x**2) + mem0_358*(x**3) + 
mem0_360*(x**4) + mem0_362*(x**5) + mem0_364*(x**6) + mem0_366*(x**7)
)
[3329, x**8 - 2882],
eqmod 
(
mem0_352_k15*(x**0) + mem0_354_k15*(x**1) + mem0_356_k15*(x**2) + mem0_358_k15*(x**3) +
mem0_360_k15*(x**4) + mem0_362_k15*(x**5) + mem0_364_k15*(x**6) + mem0_366_k15*(x**7) +
mem0_368_k15*(x**8) + mem0_370_k15*(x**9) + mem0_372_k15*(x**10) + mem0_374_k15*(x**11) +
mem0_376_k15*(x**12) + mem0_378_k15*(x**13) + mem0_380_k15*(x**14) + mem0_382_k15*(x**15) 
)
(
mem0_368*(x**0) + mem0_370*(x**1) + mem0_372*(x**2) + mem0_374*(x**3) + 
mem0_376*(x**4) + mem0_378*(x**5) + mem0_380*(x**6) + mem0_382*(x**7)
)
[3329, x**8 - 447],
eqmod 
(
mem0_384_k15*(x**0) + mem0_386_k15*(x**1) + mem0_388_k15*(x**2) + mem0_390_k15*(x**3) +
mem0_392_k15*(x**4) + mem0_394_k15*(x**5) + mem0_396_k15*(x**6) + mem0_398_k15*(x**7) +
mem0_400_k15*(x**8) + mem0_402_k15*(x**9) + mem0_404_k15*(x**10) + mem0_406_k15*(x**11) +
mem0_408_k15*(x**12) + mem0_410_k15*(x**13) + mem0_412_k15*(x**14) + mem0_414_k15*(x**15) 
)
(
mem0_384*(x**0) + mem0_386*(x**1) + mem0_388*(x**2) + mem0_390*(x**3) + 
mem0_392*(x**4) + mem0_394*(x**5) + mem0_396*(x**6) + mem0_398*(x**7)
)
[3329, x**8 - 2393],
eqmod 
(
mem0_384_k15*(x**0) + mem0_386_k15*(x**1) + mem0_388_k15*(x**2) + mem0_390_k15*(x**3) +
mem0_392_k15*(x**4) + mem0_394_k15*(x**5) + mem0_396_k15*(x**6) + mem0_398_k15*(x**7) +
mem0_400_k15*(x**8) + mem0_402_k15*(x**9) + mem0_404_k15*(x**10) + mem0_406_k15*(x**11) +
mem0_408_k15*(x**12) + mem0_410_k15*(x**13) + mem0_412_k15*(x**14) + mem0_414_k15*(x**15) 
)
(
mem0_400*(x**0) + mem0_402*(x**1) + mem0_404*(x**2) + mem0_406*(x**3) + 
mem0_408*(x**4) + mem0_410*(x**5) + mem0_412*(x**6) + mem0_414*(x**7)
)
[3329, x**8 - 936],
eqmod 
(
mem0_416_k15*(x**0) + mem0_418_k15*(x**1) + mem0_420_k15*(x**2) + mem0_422_k15*(x**3) +
mem0_424_k15*(x**4) + mem0_426_k15*(x**5) + mem0_428_k15*(x**6) + mem0_430_k15*(x**7) +
mem0_432_k15*(x**8) + mem0_434_k15*(x**9) + mem0_436_k15*(x**10) + mem0_438_k15*(x**11) +
mem0_440_k15*(x**12) + mem0_442_k15*(x**13) + mem0_444_k15*(x**14) + mem0_446_k15*(x**15) 
)
(
mem0_416*(x**0) + mem0_418*(x**1) + mem0_420*(x**2) + mem0_422*(x**3) + 
mem0_424*(x**4) + mem0_426*(x**5) + mem0_428*(x**6) + mem0_430*(x**7)
)
[3329, x**8 - 2879],
eqmod 
(
mem0_416_k15*(x**0) + mem0_418_k15*(x**1) + mem0_420_k15*(x**2) + mem0_422_k15*(x**3) +
mem0_424_k15*(x**4) + mem0_426_k15*(x**5) + mem0_428_k15*(x**6) + mem0_430_k15*(x**7) +
mem0_432_k15*(x**8) + mem0_434_k15*(x**9) + mem0_436_k15*(x**10) + mem0_438_k15*(x**11) +
mem0_440_k15*(x**12) + mem0_442_k15*(x**13) + mem0_444_k15*(x**14) + mem0_446_k15*(x**15) 
)
(
mem0_432*(x**0) + mem0_434*(x**1) + mem0_436*(x**2) + mem0_438*(x**3) + 
mem0_440*(x**4) + mem0_442*(x**5) + mem0_444*(x**6) + mem0_446*(x**7)
)
[3329, x**8 - 450],
eqmod 
(
mem0_448_k15*(x**0) + mem0_450_k15*(x**1) + mem0_452_k15*(x**2) + mem0_454_k15*(x**3) +
mem0_456_k15*(x**4) + mem0_458_k15*(x**5) + mem0_460_k15*(x**6) + mem0_462_k15*(x**7) +
mem0_464_k15*(x**8) + mem0_466_k15*(x**9) + mem0_468_k15*(x**10) + mem0_470_k15*(x**11) +
mem0_472_k15*(x**12) + mem0_474_k15*(x**13) + mem0_476_k15*(x**14) + mem0_478_k15*(x**15) 
)
(
mem0_448*(x**0) + mem0_450*(x**1) + mem0_452*(x**2) + mem0_454*(x**3) + 
mem0_456*(x**4) + mem0_458*(x**5) + mem0_460*(x**6) + mem0_462*(x**7)
)
[3329, x**8 - 1974],
eqmod 
(
mem0_448_k15*(x**0) + mem0_450_k15*(x**1) + mem0_452_k15*(x**2) + mem0_454_k15*(x**3) +
mem0_456_k15*(x**4) + mem0_458_k15*(x**5) + mem0_460_k15*(x**6) + mem0_462_k15*(x**7) +
mem0_464_k15*(x**8) + mem0_466_k15*(x**9) + mem0_468_k15*(x**10) + mem0_470_k15*(x**11) +
mem0_472_k15*(x**12) + mem0_474_k15*(x**13) + mem0_476_k15*(x**14) + mem0_478_k15*(x**15) 
)
(
mem0_464*(x**0) + mem0_466*(x**1) + mem0_468*(x**2) + mem0_470*(x**3) + 
mem0_472*(x**4) + mem0_474*(x**5) + mem0_476*(x**6) + mem0_478*(x**7)
)
[3329, x**8 - 1355],
eqmod 
(
mem0_480_k15*(x**0) + mem0_482_k15*(x**1) + mem0_484_k15*(x**2) + mem0_486_k15*(x**3) +
mem0_488_k15*(x**4) + mem0_490_k15*(x**5) + mem0_492_k15*(x**6) + mem0_494_k15*(x**7) +
mem0_496_k15*(x**8) + mem0_498_k15*(x**9) + mem0_500_k15*(x**10) + mem0_502_k15*(x**11) +
mem0_504_k15*(x**12) + mem0_506_k15*(x**13) + mem0_508_k15*(x**14) + mem0_510_k15*(x**15) 
)
(
mem0_480*(x**0) + mem0_482*(x**1) + mem0_484*(x**2) + mem0_486*(x**3) + 
mem0_488*(x**4) + mem0_490*(x**5) + mem0_492*(x**6) + mem0_494*(x**7)
)
[3329, x**8 - 821],
eqmod 
(
mem0_480_k15*(x**0) + mem0_482_k15*(x**1) + mem0_484_k15*(x**2) + mem0_486_k15*(x**3) +
mem0_488_k15*(x**4) + mem0_490_k15*(x**5) + mem0_492_k15*(x**6) + mem0_494_k15*(x**7) +
mem0_496_k15*(x**8) + mem0_498_k15*(x**9) + mem0_500_k15*(x**10) + mem0_502_k15*(x**11) +
mem0_504_k15*(x**12) + mem0_506_k15*(x**13) + mem0_508_k15*(x**14) + mem0_510_k15*(x**15) 
)
(
mem0_496*(x**0) + mem0_498*(x**1) + mem0_500*(x**2) + mem0_502*(x**3) + 
mem0_504*(x**4) + mem0_506*(x**5) + mem0_508*(x**6) + mem0_510*(x**7)
)
[3329, x**8 - 2508]

] && and [
   (-7)@16 * 3329@16 <s mem0_0, mem0_0 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_2, mem0_2 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_4, mem0_4 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_6, mem0_6 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_8, mem0_8 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_10, mem0_10 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_12, mem0_12 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_14, mem0_14 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_16, mem0_16 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_18, mem0_18 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_20, mem0_20 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_22, mem0_22 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_24, mem0_24 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_26, mem0_26 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_28, mem0_28 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_30, mem0_30 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_32, mem0_32 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_34, mem0_34 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_36, mem0_36 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_38, mem0_38 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_40, mem0_40 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_42, mem0_42 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_44, mem0_44 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_46, mem0_46 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_48, mem0_48 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_50, mem0_50 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_52, mem0_52 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_54, mem0_54 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_56, mem0_56 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_58, mem0_58 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_60, mem0_60 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_62, mem0_62 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_64, mem0_64 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_66, mem0_66 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_68, mem0_68 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_70, mem0_70 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_72, mem0_72 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_74, mem0_74 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_76, mem0_76 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_78, mem0_78 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_80, mem0_80 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_82, mem0_82 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_84, mem0_84 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_86, mem0_86 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_88, mem0_88 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_90, mem0_90 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_92, mem0_92 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_94, mem0_94 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_96, mem0_96 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_98, mem0_98 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_100, mem0_100 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_102, mem0_102 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_104, mem0_104 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_106, mem0_106 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_108, mem0_108 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_110, mem0_110 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_112, mem0_112 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_114, mem0_114 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_116, mem0_116 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_118, mem0_118 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_120, mem0_120 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_122, mem0_122 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_124, mem0_124 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_126, mem0_126 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_128, mem0_128 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_130, mem0_130 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_132, mem0_132 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_134, mem0_134 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_136, mem0_136 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_138, mem0_138 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_140, mem0_140 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_142, mem0_142 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_144, mem0_144 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_146, mem0_146 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_148, mem0_148 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_150, mem0_150 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_152, mem0_152 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_154, mem0_154 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_156, mem0_156 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_158, mem0_158 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_160, mem0_160 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_162, mem0_162 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_164, mem0_164 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_166, mem0_166 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_168, mem0_168 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_170, mem0_170 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_172, mem0_172 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_174, mem0_174 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_176, mem0_176 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_178, mem0_178 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_180, mem0_180 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_182, mem0_182 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_184, mem0_184 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_186, mem0_186 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_188, mem0_188 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_190, mem0_190 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_192, mem0_192 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_194, mem0_194 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_196, mem0_196 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_198, mem0_198 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_200, mem0_200 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_202, mem0_202 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_204, mem0_204 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_206, mem0_206 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_208, mem0_208 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_210, mem0_210 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_212, mem0_212 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_214, mem0_214 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_216, mem0_216 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_218, mem0_218 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_220, mem0_220 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_222, mem0_222 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_224, mem0_224 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_226, mem0_226 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_228, mem0_228 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_230, mem0_230 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_232, mem0_232 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_234, mem0_234 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_236, mem0_236 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_238, mem0_238 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_240, mem0_240 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_242, mem0_242 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_244, mem0_244 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_246, mem0_246 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_248, mem0_248 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_250, mem0_250 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_252, mem0_252 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_254, mem0_254 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_256, mem0_256 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_258, mem0_258 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_260, mem0_260 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_262, mem0_262 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_264, mem0_264 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_266, mem0_266 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_268, mem0_268 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_270, mem0_270 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_272, mem0_272 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_274, mem0_274 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_276, mem0_276 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_278, mem0_278 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_280, mem0_280 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_282, mem0_282 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_284, mem0_284 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_286, mem0_286 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_288, mem0_288 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_290, mem0_290 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_292, mem0_292 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_294, mem0_294 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_296, mem0_296 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_298, mem0_298 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_300, mem0_300 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_302, mem0_302 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_304, mem0_304 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_306, mem0_306 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_308, mem0_308 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_310, mem0_310 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_312, mem0_312 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_314, mem0_314 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_316, mem0_316 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_318, mem0_318 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_320, mem0_320 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_322, mem0_322 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_324, mem0_324 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_326, mem0_326 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_328, mem0_328 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_330, mem0_330 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_332, mem0_332 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_334, mem0_334 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_336, mem0_336 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_338, mem0_338 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_340, mem0_340 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_342, mem0_342 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_344, mem0_344 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_346, mem0_346 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_348, mem0_348 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_350, mem0_350 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_352, mem0_352 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_354, mem0_354 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_356, mem0_356 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_358, mem0_358 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_360, mem0_360 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_362, mem0_362 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_364, mem0_364 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_366, mem0_366 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_368, mem0_368 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_370, mem0_370 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_372, mem0_372 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_374, mem0_374 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_376, mem0_376 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_378, mem0_378 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_380, mem0_380 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_382, mem0_382 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_384, mem0_384 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_386, mem0_386 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_388, mem0_388 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_390, mem0_390 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_392, mem0_392 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_394, mem0_394 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_396, mem0_396 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_398, mem0_398 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_400, mem0_400 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_402, mem0_402 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_404, mem0_404 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_406, mem0_406 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_408, mem0_408 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_410, mem0_410 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_412, mem0_412 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_414, mem0_414 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_416, mem0_416 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_418, mem0_418 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_420, mem0_420 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_422, mem0_422 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_424, mem0_424 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_426, mem0_426 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_428, mem0_428 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_430, mem0_430 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_432, mem0_432 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_434, mem0_434 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_436, mem0_436 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_438, mem0_438 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_440, mem0_440 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_442, mem0_442 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_444, mem0_444 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_446, mem0_446 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_448, mem0_448 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_450, mem0_450 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_452, mem0_452 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_454, mem0_454 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_456, mem0_456 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_458, mem0_458 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_460, mem0_460 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_462, mem0_462 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_464, mem0_464 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_466, mem0_466 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_468, mem0_468 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_470, mem0_470 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_472, mem0_472 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_474, mem0_474 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_476, mem0_476 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_478, mem0_478 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_480, mem0_480 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_482, mem0_482 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_484, mem0_484 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_486, mem0_486 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_488, mem0_488 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_490, mem0_490 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_492, mem0_492 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_494, mem0_494 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_496, mem0_496 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_498, mem0_498 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_500, mem0_500 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_502, mem0_502 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_504, mem0_504 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_506, mem0_506 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_508, mem0_508 <s 7@16 * 3329@16,
   (-7)@16 * 3329@16 <s mem0_510, mem0_510 <s 7@16 * 3329@16
]
}
