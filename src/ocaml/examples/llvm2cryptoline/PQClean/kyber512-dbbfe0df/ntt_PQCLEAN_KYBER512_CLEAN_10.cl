(*
_build/default/coqcryptoline.exe -v -jobs 16 -sat_solver cadical -sat_cert grat -no_carry_constraint ~/tmp/coqcv_ntt_k32_separated.cl
Parsing Cryptoline file:                [OK]            0.255995 seconds
Results of checking CNF formulas:       [OK]            1466.857265 seconds
Finding polynomial coefficients

Finished finding polynomial coefficients                6142.785770 seconds
Verification result:                    [OK]            8181.191165 seconds

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
{ true

&& and [

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

mov mem0_0_k31 mem0_0;
mov mem0_2_k31 mem0_2;
mov mem0_4_k31 mem0_4;
mov mem0_6_k31 mem0_6;
mov mem0_8_k31 mem0_8;
mov mem0_10_k31 mem0_10;
mov mem0_12_k31 mem0_12;
mov mem0_14_k31 mem0_14;
mov mem0_16_k31 mem0_16;
mov mem0_18_k31 mem0_18;
mov mem0_20_k31 mem0_20;
mov mem0_22_k31 mem0_22;
mov mem0_24_k31 mem0_24;
mov mem0_26_k31 mem0_26;
mov mem0_28_k31 mem0_28;
mov mem0_30_k31 mem0_30;
mov mem0_32_k31 mem0_32;
mov mem0_34_k31 mem0_34;
mov mem0_36_k31 mem0_36;
mov mem0_38_k31 mem0_38;
mov mem0_40_k31 mem0_40;
mov mem0_42_k31 mem0_42;
mov mem0_44_k31 mem0_44;
mov mem0_46_k31 mem0_46;
mov mem0_48_k31 mem0_48;
mov mem0_50_k31 mem0_50;
mov mem0_52_k31 mem0_52;
mov mem0_54_k31 mem0_54;
mov mem0_56_k31 mem0_56;
mov mem0_58_k31 mem0_58;
mov mem0_60_k31 mem0_60;
mov mem0_62_k31 mem0_62;
mov mem0_64_k31 mem0_64;
mov mem0_66_k31 mem0_66;
mov mem0_68_k31 mem0_68;
mov mem0_70_k31 mem0_70;
mov mem0_72_k31 mem0_72;
mov mem0_74_k31 mem0_74;
mov mem0_76_k31 mem0_76;
mov mem0_78_k31 mem0_78;
mov mem0_80_k31 mem0_80;
mov mem0_82_k31 mem0_82;
mov mem0_84_k31 mem0_84;
mov mem0_86_k31 mem0_86;
mov mem0_88_k31 mem0_88;
mov mem0_90_k31 mem0_90;
mov mem0_92_k31 mem0_92;
mov mem0_94_k31 mem0_94;
mov mem0_96_k31 mem0_96;
mov mem0_98_k31 mem0_98;
mov mem0_100_k31 mem0_100;
mov mem0_102_k31 mem0_102;
mov mem0_104_k31 mem0_104;
mov mem0_106_k31 mem0_106;
mov mem0_108_k31 mem0_108;
mov mem0_110_k31 mem0_110;
mov mem0_112_k31 mem0_112;
mov mem0_114_k31 mem0_114;
mov mem0_116_k31 mem0_116;
mov mem0_118_k31 mem0_118;
mov mem0_120_k31 mem0_120;
mov mem0_122_k31 mem0_122;
mov mem0_124_k31 mem0_124;
mov mem0_126_k31 mem0_126;
mov mem0_128_k31 mem0_128;
mov mem0_130_k31 mem0_130;
mov mem0_132_k31 mem0_132;
mov mem0_134_k31 mem0_134;
mov mem0_136_k31 mem0_136;
mov mem0_138_k31 mem0_138;
mov mem0_140_k31 mem0_140;
mov mem0_142_k31 mem0_142;
mov mem0_144_k31 mem0_144;
mov mem0_146_k31 mem0_146;
mov mem0_148_k31 mem0_148;
mov mem0_150_k31 mem0_150;
mov mem0_152_k31 mem0_152;
mov mem0_154_k31 mem0_154;
mov mem0_156_k31 mem0_156;
mov mem0_158_k31 mem0_158;
mov mem0_160_k31 mem0_160;
mov mem0_162_k31 mem0_162;
mov mem0_164_k31 mem0_164;
mov mem0_166_k31 mem0_166;
mov mem0_168_k31 mem0_168;
mov mem0_170_k31 mem0_170;
mov mem0_172_k31 mem0_172;
mov mem0_174_k31 mem0_174;
mov mem0_176_k31 mem0_176;
mov mem0_178_k31 mem0_178;
mov mem0_180_k31 mem0_180;
mov mem0_182_k31 mem0_182;
mov mem0_184_k31 mem0_184;
mov mem0_186_k31 mem0_186;
mov mem0_188_k31 mem0_188;
mov mem0_190_k31 mem0_190;
mov mem0_192_k31 mem0_192;
mov mem0_194_k31 mem0_194;
mov mem0_196_k31 mem0_196;
mov mem0_198_k31 mem0_198;
mov mem0_200_k31 mem0_200;
mov mem0_202_k31 mem0_202;
mov mem0_204_k31 mem0_204;
mov mem0_206_k31 mem0_206;
mov mem0_208_k31 mem0_208;
mov mem0_210_k31 mem0_210;
mov mem0_212_k31 mem0_212;
mov mem0_214_k31 mem0_214;
mov mem0_216_k31 mem0_216;
mov mem0_218_k31 mem0_218;
mov mem0_220_k31 mem0_220;
mov mem0_222_k31 mem0_222;
mov mem0_224_k31 mem0_224;
mov mem0_226_k31 mem0_226;
mov mem0_228_k31 mem0_228;
mov mem0_230_k31 mem0_230;
mov mem0_232_k31 mem0_232;
mov mem0_234_k31 mem0_234;
mov mem0_236_k31 mem0_236;
mov mem0_238_k31 mem0_238;
mov mem0_240_k31 mem0_240;
mov mem0_242_k31 mem0_242;
mov mem0_244_k31 mem0_244;
mov mem0_246_k31 mem0_246;
mov mem0_248_k31 mem0_248;
mov mem0_250_k31 mem0_250;
mov mem0_252_k31 mem0_252;
mov mem0_254_k31 mem0_254;
mov mem0_256_k31 mem0_256;
mov mem0_258_k31 mem0_258;
mov mem0_260_k31 mem0_260;
mov mem0_262_k31 mem0_262;
mov mem0_264_k31 mem0_264;
mov mem0_266_k31 mem0_266;
mov mem0_268_k31 mem0_268;
mov mem0_270_k31 mem0_270;
mov mem0_272_k31 mem0_272;
mov mem0_274_k31 mem0_274;
mov mem0_276_k31 mem0_276;
mov mem0_278_k31 mem0_278;
mov mem0_280_k31 mem0_280;
mov mem0_282_k31 mem0_282;
mov mem0_284_k31 mem0_284;
mov mem0_286_k31 mem0_286;
mov mem0_288_k31 mem0_288;
mov mem0_290_k31 mem0_290;
mov mem0_292_k31 mem0_292;
mov mem0_294_k31 mem0_294;
mov mem0_296_k31 mem0_296;
mov mem0_298_k31 mem0_298;
mov mem0_300_k31 mem0_300;
mov mem0_302_k31 mem0_302;
mov mem0_304_k31 mem0_304;
mov mem0_306_k31 mem0_306;
mov mem0_308_k31 mem0_308;
mov mem0_310_k31 mem0_310;
mov mem0_312_k31 mem0_312;
mov mem0_314_k31 mem0_314;
mov mem0_316_k31 mem0_316;
mov mem0_318_k31 mem0_318;
mov mem0_320_k31 mem0_320;
mov mem0_322_k31 mem0_322;
mov mem0_324_k31 mem0_324;
mov mem0_326_k31 mem0_326;
mov mem0_328_k31 mem0_328;
mov mem0_330_k31 mem0_330;
mov mem0_332_k31 mem0_332;
mov mem0_334_k31 mem0_334;
mov mem0_336_k31 mem0_336;
mov mem0_338_k31 mem0_338;
mov mem0_340_k31 mem0_340;
mov mem0_342_k31 mem0_342;
mov mem0_344_k31 mem0_344;
mov mem0_346_k31 mem0_346;
mov mem0_348_k31 mem0_348;
mov mem0_350_k31 mem0_350;
mov mem0_352_k31 mem0_352;
mov mem0_354_k31 mem0_354;
mov mem0_356_k31 mem0_356;
mov mem0_358_k31 mem0_358;
mov mem0_360_k31 mem0_360;
mov mem0_362_k31 mem0_362;
mov mem0_364_k31 mem0_364;
mov mem0_366_k31 mem0_366;
mov mem0_368_k31 mem0_368;
mov mem0_370_k31 mem0_370;
mov mem0_372_k31 mem0_372;
mov mem0_374_k31 mem0_374;
mov mem0_376_k31 mem0_376;
mov mem0_378_k31 mem0_378;
mov mem0_380_k31 mem0_380;
mov mem0_382_k31 mem0_382;
mov mem0_384_k31 mem0_384;
mov mem0_386_k31 mem0_386;
mov mem0_388_k31 mem0_388;
mov mem0_390_k31 mem0_390;
mov mem0_392_k31 mem0_392;
mov mem0_394_k31 mem0_394;
mov mem0_396_k31 mem0_396;
mov mem0_398_k31 mem0_398;
mov mem0_400_k31 mem0_400;
mov mem0_402_k31 mem0_402;
mov mem0_404_k31 mem0_404;
mov mem0_406_k31 mem0_406;
mov mem0_408_k31 mem0_408;
mov mem0_410_k31 mem0_410;
mov mem0_412_k31 mem0_412;
mov mem0_414_k31 mem0_414;
mov mem0_416_k31 mem0_416;
mov mem0_418_k31 mem0_418;
mov mem0_420_k31 mem0_420;
mov mem0_422_k31 mem0_422;
mov mem0_424_k31 mem0_424;
mov mem0_426_k31 mem0_426;
mov mem0_428_k31 mem0_428;
mov mem0_430_k31 mem0_430;
mov mem0_432_k31 mem0_432;
mov mem0_434_k31 mem0_434;
mov mem0_436_k31 mem0_436;
mov mem0_438_k31 mem0_438;
mov mem0_440_k31 mem0_440;
mov mem0_442_k31 mem0_442;
mov mem0_444_k31 mem0_444;
mov mem0_446_k31 mem0_446;
mov mem0_448_k31 mem0_448;
mov mem0_450_k31 mem0_450;
mov mem0_452_k31 mem0_452;
mov mem0_454_k31 mem0_454;
mov mem0_456_k31 mem0_456;
mov mem0_458_k31 mem0_458;
mov mem0_460_k31 mem0_460;
mov mem0_462_k31 mem0_462;
mov mem0_464_k31 mem0_464;
mov mem0_466_k31 mem0_466;
mov mem0_468_k31 mem0_468;
mov mem0_470_k31 mem0_470;
mov mem0_472_k31 mem0_472;
mov mem0_474_k31 mem0_474;
mov mem0_476_k31 mem0_476;
mov mem0_478_k31 mem0_478;
mov mem0_480_k31 mem0_480;
mov mem0_482_k31 mem0_482;
mov mem0_484_k31 mem0_484;
mov mem0_486_k31 mem0_486;
mov mem0_488_k31 mem0_488;
mov mem0_490_k31 mem0_490;
mov mem0_492_k31 mem0_492;
mov mem0_494_k31 mem0_494;
mov mem0_496_k31 mem0_496;
mov mem0_498_k31 mem0_498;
mov mem0_500_k31 mem0_500;
mov mem0_502_k31 mem0_502;
mov mem0_504_k31 mem0_504;
mov mem0_506_k31 mem0_506;
mov mem0_508_k31 mem0_508;
mov mem0_510_k31 mem0_510;


(* NOTE: k = 32 *)

(*   %arrayidx9.5 = getelementptr inbounds i16, i16* %r, i64 4 *)
(*   %1280 = load i16, i16* %arrayidx9.5, align 2, !tbaa !3 *)
mov v1280 mem0_8;
(*   %conv1.i.5 = sext i16 %1280 to i32 *)
cast v_conv1_i_5@sint32 v1280@sint16;
(*   %mul.i.5 = mul nsw i32 %conv1.i.5, 1223 *)
mul v_mul_i_5 v_conv1_i_5 (1223)@sint32;
(*   %call.i.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5, v_call_i_5);
(*   %1281 = load i16, i16* %r, align 2, !tbaa !3 *)
mov v1281 mem0_0;
(*   %sub.5 = sub i16 %1281, %call.i.5 *)
sub v_sub_5 v1281 v_call_i_5;
(*   store i16 %sub.5, i16* %arrayidx9.5, align 2, !tbaa !3 *)
mov mem0_8 v_sub_5;
(*   %add21.5 = add i16 %1281, %call.i.5 *)
add v_add21_5 v1281 v_call_i_5;
(*   store i16 %add21.5, i16* %r, align 2, !tbaa !3 *)
mov mem0_0 v_add21_5;
(*   %arrayidx9.5.1 = getelementptr inbounds i16, i16* %r, i64 5 *)
(*   %1282 = load i16, i16* %arrayidx9.5.1, align 2, !tbaa !3 *)
mov v1282 mem0_10;
(*   %conv1.i.5.1 = sext i16 %1282 to i32 *)
cast v_conv1_i_5_1@sint32 v1282@sint16;
(*   %mul.i.5.1 = mul nsw i32 %conv1.i.5.1, 1223 *)
mul v_mul_i_5_1 v_conv1_i_5_1 (1223)@sint32;
(*   %call.i.5.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1, v_call_i_5_1);
(*   %arrayidx11.5.1 = getelementptr inbounds i16, i16* %r, i64 1 *)
(*   %1283 = load i16, i16* %arrayidx11.5.1, align 2, !tbaa !3 *)
mov v1283 mem0_2;
(*   %sub.5.1 = sub i16 %1283, %call.i.5.1 *)
sub v_sub_5_1 v1283 v_call_i_5_1;
(*   store i16 %sub.5.1, i16* %arrayidx9.5.1, align 2, !tbaa !3 *)
mov mem0_10 v_sub_5_1;
(*   %add21.5.1 = add i16 %1283, %call.i.5.1 *)
add v_add21_5_1 v1283 v_call_i_5_1;
(*   store i16 %add21.5.1, i16* %arrayidx11.5.1, align 2, !tbaa !3 *)
mov mem0_2 v_add21_5_1;
(*   %arrayidx9.5.2 = getelementptr inbounds i16, i16* %r, i64 6 *)
(*   %1284 = load i16, i16* %arrayidx9.5.2, align 2, !tbaa !3 *)
mov v1284 mem0_12;
(*   %conv1.i.5.2 = sext i16 %1284 to i32 *)
cast v_conv1_i_5_2@sint32 v1284@sint16;
(*   %mul.i.5.2 = mul nsw i32 %conv1.i.5.2, 1223 *)
mul v_mul_i_5_2 v_conv1_i_5_2 (1223)@sint32;
(*   %call.i.5.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2, v_call_i_5_2);
(*   %arrayidx11.5.2 = getelementptr inbounds i16, i16* %r, i64 2 *)
(*   %1285 = load i16, i16* %arrayidx11.5.2, align 2, !tbaa !3 *)
mov v1285 mem0_4;
(*   %sub.5.2 = sub i16 %1285, %call.i.5.2 *)
sub v_sub_5_2 v1285 v_call_i_5_2;
(*   store i16 %sub.5.2, i16* %arrayidx9.5.2, align 2, !tbaa !3 *)
mov mem0_12 v_sub_5_2;
(*   %add21.5.2 = add i16 %1285, %call.i.5.2 *)
add v_add21_5_2 v1285 v_call_i_5_2;
(*   store i16 %add21.5.2, i16* %arrayidx11.5.2, align 2, !tbaa !3 *)
mov mem0_4 v_add21_5_2;
(*   %arrayidx9.5.3 = getelementptr inbounds i16, i16* %r, i64 7 *)
(*   %1286 = load i16, i16* %arrayidx9.5.3, align 2, !tbaa !3 *)
mov v1286 mem0_14;
(*   %conv1.i.5.3 = sext i16 %1286 to i32 *)
cast v_conv1_i_5_3@sint32 v1286@sint16;
(*   %mul.i.5.3 = mul nsw i32 %conv1.i.5.3, 1223 *)
mul v_mul_i_5_3 v_conv1_i_5_3 (1223)@sint32;
(*   %call.i.5.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3, v_call_i_5_3);
(*   %arrayidx11.5.3 = getelementptr inbounds i16, i16* %r, i64 3 *)
(*   %1287 = load i16, i16* %arrayidx11.5.3, align 2, !tbaa !3 *)
mov v1287 mem0_6;
(*   %sub.5.3 = sub i16 %1287, %call.i.5.3 *)
sub v_sub_5_3 v1287 v_call_i_5_3;
(*   store i16 %sub.5.3, i16* %arrayidx9.5.3, align 2, !tbaa !3 *)
mov mem0_14 v_sub_5_3;
(*   %add21.5.3 = add i16 %1287, %call.i.5.3 *)
add v_add21_5_3 v1287 v_call_i_5_3;
(*   store i16 %add21.5.3, i16* %arrayidx11.5.3, align 2, !tbaa !3 *)
mov mem0_6 v_add21_5_3;

(* NOTE: k = 33 *)

(*   %arrayidx9.5.178 = getelementptr inbounds i16, i16* %r, i64 12 *)
(*   %1288 = load i16, i16* %arrayidx9.5.178, align 2, !tbaa !3 *)
mov v1288 mem0_24;
(*   %conv1.i.5.179 = sext i16 %1288 to i32 *)
cast v_conv1_i_5_179@sint32 v1288@sint16;
(*   %mul.i.5.180 = mul nsw i32 %conv1.i.5.179, 652 *)
mul v_mul_i_5_180 v_conv1_i_5_179 (652)@sint32;
(*   %call.i.5.181 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.180) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_180, v_call_i_5_181);
(*   %arrayidx11.5.182 = getelementptr inbounds i16, i16* %r, i64 8 *)
(*   %1289 = load i16, i16* %arrayidx11.5.182, align 2, !tbaa !3 *)
mov v1289 mem0_16;
(*   %sub.5.183 = sub i16 %1289, %call.i.5.181 *)
sub v_sub_5_183 v1289 v_call_i_5_181;
(*   store i16 %sub.5.183, i16* %arrayidx9.5.178, align 2, !tbaa !3 *)
mov mem0_24 v_sub_5_183;
(*   %add21.5.184 = add i16 %1289, %call.i.5.181 *)
add v_add21_5_184 v1289 v_call_i_5_181;
(*   store i16 %add21.5.184, i16* %arrayidx11.5.182, align 2, !tbaa !3 *)
mov mem0_16 v_add21_5_184;
(*   %arrayidx9.5.1.1 = getelementptr inbounds i16, i16* %r, i64 13 *)
(*   %1290 = load i16, i16* %arrayidx9.5.1.1, align 2, !tbaa !3 *)
mov v1290 mem0_26;
(*   %conv1.i.5.1.1 = sext i16 %1290 to i32 *)
cast v_conv1_i_5_1_1@sint32 v1290@sint16;
(*   %mul.i.5.1.1 = mul nsw i32 %conv1.i.5.1.1, 652 *)
mul v_mul_i_5_1_1 v_conv1_i_5_1_1 (652)@sint32;
(*   %call.i.5.1.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_1, v_call_i_5_1_1);
(*   %arrayidx11.5.1.1 = getelementptr inbounds i16, i16* %r, i64 9 *)
(*   %1291 = load i16, i16* %arrayidx11.5.1.1, align 2, !tbaa !3 *)
mov v1291 mem0_18;
(*   %sub.5.1.1 = sub i16 %1291, %call.i.5.1.1 *)
sub v_sub_5_1_1 v1291 v_call_i_5_1_1;
(*   store i16 %sub.5.1.1, i16* %arrayidx9.5.1.1, align 2, !tbaa !3 *)
mov mem0_26 v_sub_5_1_1;
(*   %add21.5.1.1 = add i16 %1291, %call.i.5.1.1 *)
add v_add21_5_1_1 v1291 v_call_i_5_1_1;
(*   store i16 %add21.5.1.1, i16* %arrayidx11.5.1.1, align 2, !tbaa !3 *)
mov mem0_18 v_add21_5_1_1;
(*   %arrayidx9.5.2.1 = getelementptr inbounds i16, i16* %r, i64 14 *)
(*   %1292 = load i16, i16* %arrayidx9.5.2.1, align 2, !tbaa !3 *)
mov v1292 mem0_28;
(*   %conv1.i.5.2.1 = sext i16 %1292 to i32 *)
cast v_conv1_i_5_2_1@sint32 v1292@sint16;
(*   %mul.i.5.2.1 = mul nsw i32 %conv1.i.5.2.1, 652 *)
mul v_mul_i_5_2_1 v_conv1_i_5_2_1 (652)@sint32;
(*   %call.i.5.2.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_1, v_call_i_5_2_1);
(*   %arrayidx11.5.2.1 = getelementptr inbounds i16, i16* %r, i64 10 *)
(*   %1293 = load i16, i16* %arrayidx11.5.2.1, align 2, !tbaa !3 *)
mov v1293 mem0_20;
(*   %sub.5.2.1 = sub i16 %1293, %call.i.5.2.1 *)
sub v_sub_5_2_1 v1293 v_call_i_5_2_1;
(*   store i16 %sub.5.2.1, i16* %arrayidx9.5.2.1, align 2, !tbaa !3 *)
mov mem0_28 v_sub_5_2_1;
(*   %add21.5.2.1 = add i16 %1293, %call.i.5.2.1 *)
add v_add21_5_2_1 v1293 v_call_i_5_2_1;
(*   store i16 %add21.5.2.1, i16* %arrayidx11.5.2.1, align 2, !tbaa !3 *)
mov mem0_20 v_add21_5_2_1;
(*   %arrayidx9.5.3.1 = getelementptr inbounds i16, i16* %r, i64 15 *)
(*   %1294 = load i16, i16* %arrayidx9.5.3.1, align 2, !tbaa !3 *)
mov v1294 mem0_30;
(*   %conv1.i.5.3.1 = sext i16 %1294 to i32 *)
cast v_conv1_i_5_3_1@sint32 v1294@sint16;
(*   %mul.i.5.3.1 = mul nsw i32 %conv1.i.5.3.1, 652 *)
mul v_mul_i_5_3_1 v_conv1_i_5_3_1 (652)@sint32;
(*   %call.i.5.3.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_1, v_call_i_5_3_1);
(*   %arrayidx11.5.3.1 = getelementptr inbounds i16, i16* %r, i64 11 *)
(*   %1295 = load i16, i16* %arrayidx11.5.3.1, align 2, !tbaa !3 *)
mov v1295 mem0_22;
(*   %sub.5.3.1 = sub i16 %1295, %call.i.5.3.1 *)
sub v_sub_5_3_1 v1295 v_call_i_5_3_1;
(*   store i16 %sub.5.3.1, i16* %arrayidx9.5.3.1, align 2, !tbaa !3 *)
mov mem0_30 v_sub_5_3_1;
(*   %add21.5.3.1 = add i16 %1295, %call.i.5.3.1 *)
add v_add21_5_3_1 v1295 v_call_i_5_3_1;
(*   store i16 %add21.5.3.1, i16* %arrayidx11.5.3.1, align 2, !tbaa !3 *)
mov mem0_22 v_add21_5_3_1;

(* NOTE: k = 34 *)

(*   %arrayidx9.5.288 = getelementptr inbounds i16, i16* %r, i64 20 *)
(*   %1296 = load i16, i16* %arrayidx9.5.288, align 2, !tbaa !3 *)
mov v1296 mem0_40;
(*   %conv1.i.5.289 = sext i16 %1296 to i32 *)
cast v_conv1_i_5_289@sint32 v1296@sint16;
(*   %mul.i.5.290 = mul nsw i32 %conv1.i.5.289, -552 *)
mul v_mul_i_5_290 v_conv1_i_5_289 (-552)@sint32;
(*   %call.i.5.291 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.290) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_290, v_call_i_5_291);
(*   %arrayidx11.5.292 = getelementptr inbounds i16, i16* %r, i64 16 *)
(*   %1297 = load i16, i16* %arrayidx11.5.292, align 2, !tbaa !3 *)
mov v1297 mem0_32;
(*   %sub.5.293 = sub i16 %1297, %call.i.5.291 *)
sub v_sub_5_293 v1297 v_call_i_5_291;
(*   store i16 %sub.5.293, i16* %arrayidx9.5.288, align 2, !tbaa !3 *)
mov mem0_40 v_sub_5_293;
(*   %add21.5.294 = add i16 %1297, %call.i.5.291 *)
add v_add21_5_294 v1297 v_call_i_5_291;
(*   store i16 %add21.5.294, i16* %arrayidx11.5.292, align 2, !tbaa !3 *)
mov mem0_32 v_add21_5_294;
(*   %arrayidx9.5.1.2 = getelementptr inbounds i16, i16* %r, i64 21 *)
(*   %1298 = load i16, i16* %arrayidx9.5.1.2, align 2, !tbaa !3 *)
mov v1298 mem0_42;
(*   %conv1.i.5.1.2 = sext i16 %1298 to i32 *)
cast v_conv1_i_5_1_2@sint32 v1298@sint16;
(*   %mul.i.5.1.2 = mul nsw i32 %conv1.i.5.1.2, -552 *)
mul v_mul_i_5_1_2 v_conv1_i_5_1_2 (-552)@sint32;
(*   %call.i.5.1.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_2, v_call_i_5_1_2);
(*   %arrayidx11.5.1.2 = getelementptr inbounds i16, i16* %r, i64 17 *)
(*   %1299 = load i16, i16* %arrayidx11.5.1.2, align 2, !tbaa !3 *)
mov v1299 mem0_34;
(*   %sub.5.1.2 = sub i16 %1299, %call.i.5.1.2 *)
sub v_sub_5_1_2 v1299 v_call_i_5_1_2;
(*   store i16 %sub.5.1.2, i16* %arrayidx9.5.1.2, align 2, !tbaa !3 *)
mov mem0_42 v_sub_5_1_2;
(*   %add21.5.1.2 = add i16 %1299, %call.i.5.1.2 *)
add v_add21_5_1_2 v1299 v_call_i_5_1_2;
(*   store i16 %add21.5.1.2, i16* %arrayidx11.5.1.2, align 2, !tbaa !3 *)
mov mem0_34 v_add21_5_1_2;
(*   %arrayidx9.5.2.2 = getelementptr inbounds i16, i16* %r, i64 22 *)
(*   %1300 = load i16, i16* %arrayidx9.5.2.2, align 2, !tbaa !3 *)
mov v1300 mem0_44;
(*   %conv1.i.5.2.2 = sext i16 %1300 to i32 *)
cast v_conv1_i_5_2_2@sint32 v1300@sint16;
(*   %mul.i.5.2.2 = mul nsw i32 %conv1.i.5.2.2, -552 *)
mul v_mul_i_5_2_2 v_conv1_i_5_2_2 (-552)@sint32;
(*   %call.i.5.2.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_2, v_call_i_5_2_2);
(*   %arrayidx11.5.2.2 = getelementptr inbounds i16, i16* %r, i64 18 *)
(*   %1301 = load i16, i16* %arrayidx11.5.2.2, align 2, !tbaa !3 *)
mov v1301 mem0_36;
(*   %sub.5.2.2 = sub i16 %1301, %call.i.5.2.2 *)
sub v_sub_5_2_2 v1301 v_call_i_5_2_2;
(*   store i16 %sub.5.2.2, i16* %arrayidx9.5.2.2, align 2, !tbaa !3 *)
mov mem0_44 v_sub_5_2_2;
(*   %add21.5.2.2 = add i16 %1301, %call.i.5.2.2 *)
add v_add21_5_2_2 v1301 v_call_i_5_2_2;
(*   store i16 %add21.5.2.2, i16* %arrayidx11.5.2.2, align 2, !tbaa !3 *)
mov mem0_36 v_add21_5_2_2;
(*   %arrayidx9.5.3.2 = getelementptr inbounds i16, i16* %r, i64 23 *)
(*   %1302 = load i16, i16* %arrayidx9.5.3.2, align 2, !tbaa !3 *)
mov v1302 mem0_46;
(*   %conv1.i.5.3.2 = sext i16 %1302 to i32 *)
cast v_conv1_i_5_3_2@sint32 v1302@sint16;
(*   %mul.i.5.3.2 = mul nsw i32 %conv1.i.5.3.2, -552 *)
mul v_mul_i_5_3_2 v_conv1_i_5_3_2 (-552)@sint32;
(*   %call.i.5.3.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_2, v_call_i_5_3_2);
(*   %arrayidx11.5.3.2 = getelementptr inbounds i16, i16* %r, i64 19 *)
(*   %1303 = load i16, i16* %arrayidx11.5.3.2, align 2, !tbaa !3 *)
mov v1303 mem0_38;
(*   %sub.5.3.2 = sub i16 %1303, %call.i.5.3.2 *)
sub v_sub_5_3_2 v1303 v_call_i_5_3_2;
(*   store i16 %sub.5.3.2, i16* %arrayidx9.5.3.2, align 2, !tbaa !3 *)
mov mem0_46 v_sub_5_3_2;
(*   %add21.5.3.2 = add i16 %1303, %call.i.5.3.2 *)
add v_add21_5_3_2 v1303 v_call_i_5_3_2;
(*   store i16 %add21.5.3.2, i16* %arrayidx11.5.3.2, align 2, !tbaa !3 *)
mov mem0_38 v_add21_5_3_2;

(* NOTE: k = 35 *)

(*   %arrayidx9.5.398 = getelementptr inbounds i16, i16* %r, i64 28 *)
(*   %1304 = load i16, i16* %arrayidx9.5.398, align 2, !tbaa !3 *)
mov v1304 mem0_56;
(*   %conv1.i.5.399 = sext i16 %1304 to i32 *)
cast v_conv1_i_5_399@sint32 v1304@sint16;
(*   %mul.i.5.3100 = mul nsw i32 %conv1.i.5.399, 1015 *)
mul v_mul_i_5_3100 v_conv1_i_5_399 (1015)@sint32;
(*   %call.i.5.3101 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3100) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3100, v_call_i_5_3101);
(*   %arrayidx11.5.3102 = getelementptr inbounds i16, i16* %r, i64 24 *)
(*   %1305 = load i16, i16* %arrayidx11.5.3102, align 2, !tbaa !3 *)
mov v1305 mem0_48;
(*   %sub.5.3103 = sub i16 %1305, %call.i.5.3101 *)
sub v_sub_5_3103 v1305 v_call_i_5_3101;
(*   store i16 %sub.5.3103, i16* %arrayidx9.5.398, align 2, !tbaa !3 *)
mov mem0_56 v_sub_5_3103;
(*   %add21.5.3104 = add i16 %1305, %call.i.5.3101 *)
add v_add21_5_3104 v1305 v_call_i_5_3101;
(*   store i16 %add21.5.3104, i16* %arrayidx11.5.3102, align 2, !tbaa !3 *)
mov mem0_48 v_add21_5_3104;
(*   %arrayidx9.5.1.3 = getelementptr inbounds i16, i16* %r, i64 29 *)
(*   %1306 = load i16, i16* %arrayidx9.5.1.3, align 2, !tbaa !3 *)
mov v1306 mem0_58;
(*   %conv1.i.5.1.3 = sext i16 %1306 to i32 *)
cast v_conv1_i_5_1_3@sint32 v1306@sint16;
(*   %mul.i.5.1.3 = mul nsw i32 %conv1.i.5.1.3, 1015 *)
mul v_mul_i_5_1_3 v_conv1_i_5_1_3 (1015)@sint32;
(*   %call.i.5.1.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_3, v_call_i_5_1_3);
(*   %arrayidx11.5.1.3 = getelementptr inbounds i16, i16* %r, i64 25 *)
(*   %1307 = load i16, i16* %arrayidx11.5.1.3, align 2, !tbaa !3 *)
mov v1307 mem0_50;
(*   %sub.5.1.3 = sub i16 %1307, %call.i.5.1.3 *)
sub v_sub_5_1_3 v1307 v_call_i_5_1_3;
(*   store i16 %sub.5.1.3, i16* %arrayidx9.5.1.3, align 2, !tbaa !3 *)
mov mem0_58 v_sub_5_1_3;
(*   %add21.5.1.3 = add i16 %1307, %call.i.5.1.3 *)
add v_add21_5_1_3 v1307 v_call_i_5_1_3;
(*   store i16 %add21.5.1.3, i16* %arrayidx11.5.1.3, align 2, !tbaa !3 *)
mov mem0_50 v_add21_5_1_3;
(*   %arrayidx9.5.2.3 = getelementptr inbounds i16, i16* %r, i64 30 *)
(*   %1308 = load i16, i16* %arrayidx9.5.2.3, align 2, !tbaa !3 *)
mov v1308 mem0_60;
(*   %conv1.i.5.2.3 = sext i16 %1308 to i32 *)
cast v_conv1_i_5_2_3@sint32 v1308@sint16;
(*   %mul.i.5.2.3 = mul nsw i32 %conv1.i.5.2.3, 1015 *)
mul v_mul_i_5_2_3 v_conv1_i_5_2_3 (1015)@sint32;
(*   %call.i.5.2.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_3, v_call_i_5_2_3);
(*   %arrayidx11.5.2.3 = getelementptr inbounds i16, i16* %r, i64 26 *)
(*   %1309 = load i16, i16* %arrayidx11.5.2.3, align 2, !tbaa !3 *)
mov v1309 mem0_52;
(*   %sub.5.2.3 = sub i16 %1309, %call.i.5.2.3 *)
sub v_sub_5_2_3 v1309 v_call_i_5_2_3;
(*   store i16 %sub.5.2.3, i16* %arrayidx9.5.2.3, align 2, !tbaa !3 *)
mov mem0_60 v_sub_5_2_3;
(*   %add21.5.2.3 = add i16 %1309, %call.i.5.2.3 *)
add v_add21_5_2_3 v1309 v_call_i_5_2_3;
(*   store i16 %add21.5.2.3, i16* %arrayidx11.5.2.3, align 2, !tbaa !3 *)
mov mem0_52 v_add21_5_2_3;
(*   %arrayidx9.5.3.3 = getelementptr inbounds i16, i16* %r, i64 31 *)
(*   %1310 = load i16, i16* %arrayidx9.5.3.3, align 2, !tbaa !3 *)
mov v1310 mem0_62;
(*   %conv1.i.5.3.3 = sext i16 %1310 to i32 *)
cast v_conv1_i_5_3_3@sint32 v1310@sint16;
(*   %mul.i.5.3.3 = mul nsw i32 %conv1.i.5.3.3, 1015 *)
mul v_mul_i_5_3_3 v_conv1_i_5_3_3 (1015)@sint32;
(*   %call.i.5.3.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_3, v_call_i_5_3_3);
(*   %arrayidx11.5.3.3 = getelementptr inbounds i16, i16* %r, i64 27 *)
(*   %1311 = load i16, i16* %arrayidx11.5.3.3, align 2, !tbaa !3 *)
mov v1311 mem0_54;
(*   %sub.5.3.3 = sub i16 %1311, %call.i.5.3.3 *)
sub v_sub_5_3_3 v1311 v_call_i_5_3_3;
(*   store i16 %sub.5.3.3, i16* %arrayidx9.5.3.3, align 2, !tbaa !3 *)
mov mem0_62 v_sub_5_3_3;
(*   %add21.5.3.3 = add i16 %1311, %call.i.5.3.3 *)
add v_add21_5_3_3 v1311 v_call_i_5_3_3;
(*   store i16 %add21.5.3.3, i16* %arrayidx11.5.3.3, align 2, !tbaa !3 *)
mov mem0_54 v_add21_5_3_3;

(* NOTE: k = 36 *)

(*   %arrayidx9.5.4 = getelementptr inbounds i16, i16* %r, i64 36 *)
(*   %1312 = load i16, i16* %arrayidx9.5.4, align 2, !tbaa !3 *)
mov v1312 mem0_72;
(*   %conv1.i.5.4 = sext i16 %1312 to i32 *)
cast v_conv1_i_5_4@sint32 v1312@sint16;
(*   %mul.i.5.4 = mul nsw i32 %conv1.i.5.4, -1293 *)
mul v_mul_i_5_4 v_conv1_i_5_4 (-1293)@sint32;
(*   %call.i.5.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_4, v_call_i_5_4);
(*   %arrayidx11.5.4 = getelementptr inbounds i16, i16* %r, i64 32 *)
(*   %1313 = load i16, i16* %arrayidx11.5.4, align 2, !tbaa !3 *)
mov v1313 mem0_64;
(*   %sub.5.4 = sub i16 %1313, %call.i.5.4 *)
sub v_sub_5_4 v1313 v_call_i_5_4;
(*   store i16 %sub.5.4, i16* %arrayidx9.5.4, align 2, !tbaa !3 *)
mov mem0_72 v_sub_5_4;
(*   %add21.5.4 = add i16 %1313, %call.i.5.4 *)
add v_add21_5_4 v1313 v_call_i_5_4;
(*   store i16 %add21.5.4, i16* %arrayidx11.5.4, align 2, !tbaa !3 *)
mov mem0_64 v_add21_5_4;
(*   %arrayidx9.5.1.4 = getelementptr inbounds i16, i16* %r, i64 37 *)
(*   %1314 = load i16, i16* %arrayidx9.5.1.4, align 2, !tbaa !3 *)
mov v1314 mem0_74;
(*   %conv1.i.5.1.4 = sext i16 %1314 to i32 *)
cast v_conv1_i_5_1_4@sint32 v1314@sint16;
(*   %mul.i.5.1.4 = mul nsw i32 %conv1.i.5.1.4, -1293 *)
mul v_mul_i_5_1_4 v_conv1_i_5_1_4 (-1293)@sint32;
(*   %call.i.5.1.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_4, v_call_i_5_1_4);
(*   %arrayidx11.5.1.4 = getelementptr inbounds i16, i16* %r, i64 33 *)
(*   %1315 = load i16, i16* %arrayidx11.5.1.4, align 2, !tbaa !3 *)
mov v1315 mem0_66;
(*   %sub.5.1.4 = sub i16 %1315, %call.i.5.1.4 *)
sub v_sub_5_1_4 v1315 v_call_i_5_1_4;
(*   store i16 %sub.5.1.4, i16* %arrayidx9.5.1.4, align 2, !tbaa !3 *)
mov mem0_74 v_sub_5_1_4;
(*   %add21.5.1.4 = add i16 %1315, %call.i.5.1.4 *)
add v_add21_5_1_4 v1315 v_call_i_5_1_4;
(*   store i16 %add21.5.1.4, i16* %arrayidx11.5.1.4, align 2, !tbaa !3 *)
mov mem0_66 v_add21_5_1_4;
(*   %arrayidx9.5.2.4 = getelementptr inbounds i16, i16* %r, i64 38 *)
(*   %1316 = load i16, i16* %arrayidx9.5.2.4, align 2, !tbaa !3 *)
mov v1316 mem0_76;
(*   %conv1.i.5.2.4 = sext i16 %1316 to i32 *)
cast v_conv1_i_5_2_4@sint32 v1316@sint16;
(*   %mul.i.5.2.4 = mul nsw i32 %conv1.i.5.2.4, -1293 *)
mul v_mul_i_5_2_4 v_conv1_i_5_2_4 (-1293)@sint32;
(*   %call.i.5.2.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_4, v_call_i_5_2_4);
(*   %arrayidx11.5.2.4 = getelementptr inbounds i16, i16* %r, i64 34 *)
(*   %1317 = load i16, i16* %arrayidx11.5.2.4, align 2, !tbaa !3 *)
mov v1317 mem0_68;
(*   %sub.5.2.4 = sub i16 %1317, %call.i.5.2.4 *)
sub v_sub_5_2_4 v1317 v_call_i_5_2_4;
(*   store i16 %sub.5.2.4, i16* %arrayidx9.5.2.4, align 2, !tbaa !3 *)
mov mem0_76 v_sub_5_2_4;
(*   %add21.5.2.4 = add i16 %1317, %call.i.5.2.4 *)
add v_add21_5_2_4 v1317 v_call_i_5_2_4;
(*   store i16 %add21.5.2.4, i16* %arrayidx11.5.2.4, align 2, !tbaa !3 *)
mov mem0_68 v_add21_5_2_4;
(*   %arrayidx9.5.3.4 = getelementptr inbounds i16, i16* %r, i64 39 *)
(*   %1318 = load i16, i16* %arrayidx9.5.3.4, align 2, !tbaa !3 *)
mov v1318 mem0_78;
(*   %conv1.i.5.3.4 = sext i16 %1318 to i32 *)
cast v_conv1_i_5_3_4@sint32 v1318@sint16;
(*   %mul.i.5.3.4 = mul nsw i32 %conv1.i.5.3.4, -1293 *)
mul v_mul_i_5_3_4 v_conv1_i_5_3_4 (-1293)@sint32;
(*   %call.i.5.3.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_4, v_call_i_5_3_4);
(*   %arrayidx11.5.3.4 = getelementptr inbounds i16, i16* %r, i64 35 *)
(*   %1319 = load i16, i16* %arrayidx11.5.3.4, align 2, !tbaa !3 *)
mov v1319 mem0_70;
(*   %sub.5.3.4 = sub i16 %1319, %call.i.5.3.4 *)
sub v_sub_5_3_4 v1319 v_call_i_5_3_4;
(*   store i16 %sub.5.3.4, i16* %arrayidx9.5.3.4, align 2, !tbaa !3 *)
mov mem0_78 v_sub_5_3_4;
(*   %add21.5.3.4 = add i16 %1319, %call.i.5.3.4 *)
add v_add21_5_3_4 v1319 v_call_i_5_3_4;
(*   store i16 %add21.5.3.4, i16* %arrayidx11.5.3.4, align 2, !tbaa !3 *)
mov mem0_70 v_add21_5_3_4;

(* NOTE: k = 37 *)

(*   %arrayidx9.5.5 = getelementptr inbounds i16, i16* %r, i64 44 *)
(*   %1320 = load i16, i16* %arrayidx9.5.5, align 2, !tbaa !3 *)
mov v1320 mem0_88;
(*   %conv1.i.5.5 = sext i16 %1320 to i32 *)
cast v_conv1_i_5_5@sint32 v1320@sint16;
(*   %mul.i.5.5 = mul nsw i32 %conv1.i.5.5, 1491 *)
mul v_mul_i_5_5 v_conv1_i_5_5 (1491)@sint32;
(*   %call.i.5.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_5, v_call_i_5_5);
(*   %arrayidx11.5.5 = getelementptr inbounds i16, i16* %r, i64 40 *)
(*   %1321 = load i16, i16* %arrayidx11.5.5, align 2, !tbaa !3 *)
mov v1321 mem0_80;
(*   %sub.5.5 = sub i16 %1321, %call.i.5.5 *)
sub v_sub_5_5 v1321 v_call_i_5_5;
(*   store i16 %sub.5.5, i16* %arrayidx9.5.5, align 2, !tbaa !3 *)
mov mem0_88 v_sub_5_5;
(*   %add21.5.5 = add i16 %1321, %call.i.5.5 *)
add v_add21_5_5 v1321 v_call_i_5_5;
(*   store i16 %add21.5.5, i16* %arrayidx11.5.5, align 2, !tbaa !3 *)
mov mem0_80 v_add21_5_5;
(*   %arrayidx9.5.1.5 = getelementptr inbounds i16, i16* %r, i64 45 *)
(*   %1322 = load i16, i16* %arrayidx9.5.1.5, align 2, !tbaa !3 *)
mov v1322 mem0_90;
(*   %conv1.i.5.1.5 = sext i16 %1322 to i32 *)
cast v_conv1_i_5_1_5@sint32 v1322@sint16;
(*   %mul.i.5.1.5 = mul nsw i32 %conv1.i.5.1.5, 1491 *)
mul v_mul_i_5_1_5 v_conv1_i_5_1_5 (1491)@sint32;
(*   %call.i.5.1.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_5, v_call_i_5_1_5);
(*   %arrayidx11.5.1.5 = getelementptr inbounds i16, i16* %r, i64 41 *)
(*   %1323 = load i16, i16* %arrayidx11.5.1.5, align 2, !tbaa !3 *)
mov v1323 mem0_82;
(*   %sub.5.1.5 = sub i16 %1323, %call.i.5.1.5 *)
sub v_sub_5_1_5 v1323 v_call_i_5_1_5;
(*   store i16 %sub.5.1.5, i16* %arrayidx9.5.1.5, align 2, !tbaa !3 *)
mov mem0_90 v_sub_5_1_5;
(*   %add21.5.1.5 = add i16 %1323, %call.i.5.1.5 *)
add v_add21_5_1_5 v1323 v_call_i_5_1_5;
(*   store i16 %add21.5.1.5, i16* %arrayidx11.5.1.5, align 2, !tbaa !3 *)
mov mem0_82 v_add21_5_1_5;
(*   %arrayidx9.5.2.5 = getelementptr inbounds i16, i16* %r, i64 46 *)
(*   %1324 = load i16, i16* %arrayidx9.5.2.5, align 2, !tbaa !3 *)
mov v1324 mem0_92;
(*   %conv1.i.5.2.5 = sext i16 %1324 to i32 *)
cast v_conv1_i_5_2_5@sint32 v1324@sint16;
(*   %mul.i.5.2.5 = mul nsw i32 %conv1.i.5.2.5, 1491 *)
mul v_mul_i_5_2_5 v_conv1_i_5_2_5 (1491)@sint32;
(*   %call.i.5.2.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_5, v_call_i_5_2_5);
(*   %arrayidx11.5.2.5 = getelementptr inbounds i16, i16* %r, i64 42 *)
(*   %1325 = load i16, i16* %arrayidx11.5.2.5, align 2, !tbaa !3 *)
mov v1325 mem0_84;
(*   %sub.5.2.5 = sub i16 %1325, %call.i.5.2.5 *)
sub v_sub_5_2_5 v1325 v_call_i_5_2_5;
(*   store i16 %sub.5.2.5, i16* %arrayidx9.5.2.5, align 2, !tbaa !3 *)
mov mem0_92 v_sub_5_2_5;
(*   %add21.5.2.5 = add i16 %1325, %call.i.5.2.5 *)
add v_add21_5_2_5 v1325 v_call_i_5_2_5;
(*   store i16 %add21.5.2.5, i16* %arrayidx11.5.2.5, align 2, !tbaa !3 *)
mov mem0_84 v_add21_5_2_5;
(*   %arrayidx9.5.3.5 = getelementptr inbounds i16, i16* %r, i64 47 *)
(*   %1326 = load i16, i16* %arrayidx9.5.3.5, align 2, !tbaa !3 *)
mov v1326 mem0_94;
(*   %conv1.i.5.3.5 = sext i16 %1326 to i32 *)
cast v_conv1_i_5_3_5@sint32 v1326@sint16;
(*   %mul.i.5.3.5 = mul nsw i32 %conv1.i.5.3.5, 1491 *)
mul v_mul_i_5_3_5 v_conv1_i_5_3_5 (1491)@sint32;
(*   %call.i.5.3.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_5, v_call_i_5_3_5);
(*   %arrayidx11.5.3.5 = getelementptr inbounds i16, i16* %r, i64 43 *)
(*   %1327 = load i16, i16* %arrayidx11.5.3.5, align 2, !tbaa !3 *)
mov v1327 mem0_86;
(*   %sub.5.3.5 = sub i16 %1327, %call.i.5.3.5 *)
sub v_sub_5_3_5 v1327 v_call_i_5_3_5;
(*   store i16 %sub.5.3.5, i16* %arrayidx9.5.3.5, align 2, !tbaa !3 *)
mov mem0_94 v_sub_5_3_5;
(*   %add21.5.3.5 = add i16 %1327, %call.i.5.3.5 *)
add v_add21_5_3_5 v1327 v_call_i_5_3_5;
(*   store i16 %add21.5.3.5, i16* %arrayidx11.5.3.5, align 2, !tbaa !3 *)
mov mem0_86 v_add21_5_3_5;

(* NOTE: k = 38 *)

(*   %arrayidx9.5.6 = getelementptr inbounds i16, i16* %r, i64 52 *)
(*   %1328 = load i16, i16* %arrayidx9.5.6, align 2, !tbaa !3 *)
mov v1328 mem0_104;
(*   %conv1.i.5.6 = sext i16 %1328 to i32 *)
cast v_conv1_i_5_6@sint32 v1328@sint16;
(*   %mul.i.5.6 = mul nsw i32 %conv1.i.5.6, -282 *)
mul v_mul_i_5_6 v_conv1_i_5_6 (-282)@sint32;
(*   %call.i.5.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_6, v_call_i_5_6);
(*   %arrayidx11.5.6 = getelementptr inbounds i16, i16* %r, i64 48 *)
(*   %1329 = load i16, i16* %arrayidx11.5.6, align 2, !tbaa !3 *)
mov v1329 mem0_96;
(*   %sub.5.6 = sub i16 %1329, %call.i.5.6 *)
sub v_sub_5_6 v1329 v_call_i_5_6;
(*   store i16 %sub.5.6, i16* %arrayidx9.5.6, align 2, !tbaa !3 *)
mov mem0_104 v_sub_5_6;
(*   %add21.5.6 = add i16 %1329, %call.i.5.6 *)
add v_add21_5_6 v1329 v_call_i_5_6;
(*   store i16 %add21.5.6, i16* %arrayidx11.5.6, align 2, !tbaa !3 *)
mov mem0_96 v_add21_5_6;
(*   %arrayidx9.5.1.6 = getelementptr inbounds i16, i16* %r, i64 53 *)
(*   %1330 = load i16, i16* %arrayidx9.5.1.6, align 2, !tbaa !3 *)
mov v1330 mem0_106;
(*   %conv1.i.5.1.6 = sext i16 %1330 to i32 *)
cast v_conv1_i_5_1_6@sint32 v1330@sint16;
(*   %mul.i.5.1.6 = mul nsw i32 %conv1.i.5.1.6, -282 *)
mul v_mul_i_5_1_6 v_conv1_i_5_1_6 (-282)@sint32;
(*   %call.i.5.1.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_6, v_call_i_5_1_6);
(*   %arrayidx11.5.1.6 = getelementptr inbounds i16, i16* %r, i64 49 *)
(*   %1331 = load i16, i16* %arrayidx11.5.1.6, align 2, !tbaa !3 *)
mov v1331 mem0_98;
(*   %sub.5.1.6 = sub i16 %1331, %call.i.5.1.6 *)
sub v_sub_5_1_6 v1331 v_call_i_5_1_6;
(*   store i16 %sub.5.1.6, i16* %arrayidx9.5.1.6, align 2, !tbaa !3 *)
mov mem0_106 v_sub_5_1_6;
(*   %add21.5.1.6 = add i16 %1331, %call.i.5.1.6 *)
add v_add21_5_1_6 v1331 v_call_i_5_1_6;
(*   store i16 %add21.5.1.6, i16* %arrayidx11.5.1.6, align 2, !tbaa !3 *)
mov mem0_98 v_add21_5_1_6;
(*   %arrayidx9.5.2.6 = getelementptr inbounds i16, i16* %r, i64 54 *)
(*   %1332 = load i16, i16* %arrayidx9.5.2.6, align 2, !tbaa !3 *)
mov v1332 mem0_108;
(*   %conv1.i.5.2.6 = sext i16 %1332 to i32 *)
cast v_conv1_i_5_2_6@sint32 v1332@sint16;
(*   %mul.i.5.2.6 = mul nsw i32 %conv1.i.5.2.6, -282 *)
mul v_mul_i_5_2_6 v_conv1_i_5_2_6 (-282)@sint32;
(*   %call.i.5.2.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_6, v_call_i_5_2_6);
(*   %arrayidx11.5.2.6 = getelementptr inbounds i16, i16* %r, i64 50 *)
(*   %1333 = load i16, i16* %arrayidx11.5.2.6, align 2, !tbaa !3 *)
mov v1333 mem0_100;
(*   %sub.5.2.6 = sub i16 %1333, %call.i.5.2.6 *)
sub v_sub_5_2_6 v1333 v_call_i_5_2_6;
(*   store i16 %sub.5.2.6, i16* %arrayidx9.5.2.6, align 2, !tbaa !3 *)
mov mem0_108 v_sub_5_2_6;
(*   %add21.5.2.6 = add i16 %1333, %call.i.5.2.6 *)
add v_add21_5_2_6 v1333 v_call_i_5_2_6;
(*   store i16 %add21.5.2.6, i16* %arrayidx11.5.2.6, align 2, !tbaa !3 *)
mov mem0_100 v_add21_5_2_6;
(*   %arrayidx9.5.3.6 = getelementptr inbounds i16, i16* %r, i64 55 *)
(*   %1334 = load i16, i16* %arrayidx9.5.3.6, align 2, !tbaa !3 *)
mov v1334 mem0_110;
(*   %conv1.i.5.3.6 = sext i16 %1334 to i32 *)
cast v_conv1_i_5_3_6@sint32 v1334@sint16;
(*   %mul.i.5.3.6 = mul nsw i32 %conv1.i.5.3.6, -282 *)
mul v_mul_i_5_3_6 v_conv1_i_5_3_6 (-282)@sint32;
(*   %call.i.5.3.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_6, v_call_i_5_3_6);
(*   %arrayidx11.5.3.6 = getelementptr inbounds i16, i16* %r, i64 51 *)
(*   %1335 = load i16, i16* %arrayidx11.5.3.6, align 2, !tbaa !3 *)
mov v1335 mem0_102;
(*   %sub.5.3.6 = sub i16 %1335, %call.i.5.3.6 *)
sub v_sub_5_3_6 v1335 v_call_i_5_3_6;
(*   store i16 %sub.5.3.6, i16* %arrayidx9.5.3.6, align 2, !tbaa !3 *)
mov mem0_110 v_sub_5_3_6;
(*   %add21.5.3.6 = add i16 %1335, %call.i.5.3.6 *)
add v_add21_5_3_6 v1335 v_call_i_5_3_6;
(*   store i16 %add21.5.3.6, i16* %arrayidx11.5.3.6, align 2, !tbaa !3 *)
mov mem0_102 v_add21_5_3_6;

(* NOTE: k = 39 *)

(*   %arrayidx9.5.7 = getelementptr inbounds i16, i16* %r, i64 60 *)
(*   %1336 = load i16, i16* %arrayidx9.5.7, align 2, !tbaa !3 *)
mov v1336 mem0_120;
(*   %conv1.i.5.7 = sext i16 %1336 to i32 *)
cast v_conv1_i_5_7@sint32 v1336@sint16;
(*   %mul.i.5.7 = mul nsw i32 %conv1.i.5.7, -1544 *)
mul v_mul_i_5_7 v_conv1_i_5_7 (-1544)@sint32;
(*   %call.i.5.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_7, v_call_i_5_7);
(*   %arrayidx11.5.7 = getelementptr inbounds i16, i16* %r, i64 56 *)
(*   %1337 = load i16, i16* %arrayidx11.5.7, align 2, !tbaa !3 *)
mov v1337 mem0_112;
(*   %sub.5.7 = sub i16 %1337, %call.i.5.7 *)
sub v_sub_5_7 v1337 v_call_i_5_7;
(*   store i16 %sub.5.7, i16* %arrayidx9.5.7, align 2, !tbaa !3 *)
mov mem0_120 v_sub_5_7;
(*   %add21.5.7 = add i16 %1337, %call.i.5.7 *)
add v_add21_5_7 v1337 v_call_i_5_7;
(*   store i16 %add21.5.7, i16* %arrayidx11.5.7, align 2, !tbaa !3 *)
mov mem0_112 v_add21_5_7;
(*   %arrayidx9.5.1.7 = getelementptr inbounds i16, i16* %r, i64 61 *)
(*   %1338 = load i16, i16* %arrayidx9.5.1.7, align 2, !tbaa !3 *)
mov v1338 mem0_122;
(*   %conv1.i.5.1.7 = sext i16 %1338 to i32 *)
cast v_conv1_i_5_1_7@sint32 v1338@sint16;
(*   %mul.i.5.1.7 = mul nsw i32 %conv1.i.5.1.7, -1544 *)
mul v_mul_i_5_1_7 v_conv1_i_5_1_7 (-1544)@sint32;
(*   %call.i.5.1.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_7, v_call_i_5_1_7);
(*   %arrayidx11.5.1.7 = getelementptr inbounds i16, i16* %r, i64 57 *)
(*   %1339 = load i16, i16* %arrayidx11.5.1.7, align 2, !tbaa !3 *)
mov v1339 mem0_114;
(*   %sub.5.1.7 = sub i16 %1339, %call.i.5.1.7 *)
sub v_sub_5_1_7 v1339 v_call_i_5_1_7;
(*   store i16 %sub.5.1.7, i16* %arrayidx9.5.1.7, align 2, !tbaa !3 *)
mov mem0_122 v_sub_5_1_7;
(*   %add21.5.1.7 = add i16 %1339, %call.i.5.1.7 *)
add v_add21_5_1_7 v1339 v_call_i_5_1_7;
(*   store i16 %add21.5.1.7, i16* %arrayidx11.5.1.7, align 2, !tbaa !3 *)
mov mem0_114 v_add21_5_1_7;
(*   %arrayidx9.5.2.7 = getelementptr inbounds i16, i16* %r, i64 62 *)
(*   %1340 = load i16, i16* %arrayidx9.5.2.7, align 2, !tbaa !3 *)
mov v1340 mem0_124;
(*   %conv1.i.5.2.7 = sext i16 %1340 to i32 *)
cast v_conv1_i_5_2_7@sint32 v1340@sint16;
(*   %mul.i.5.2.7 = mul nsw i32 %conv1.i.5.2.7, -1544 *)
mul v_mul_i_5_2_7 v_conv1_i_5_2_7 (-1544)@sint32;
(*   %call.i.5.2.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_7, v_call_i_5_2_7);
(*   %arrayidx11.5.2.7 = getelementptr inbounds i16, i16* %r, i64 58 *)
(*   %1341 = load i16, i16* %arrayidx11.5.2.7, align 2, !tbaa !3 *)
mov v1341 mem0_116;
(*   %sub.5.2.7 = sub i16 %1341, %call.i.5.2.7 *)
sub v_sub_5_2_7 v1341 v_call_i_5_2_7;
(*   store i16 %sub.5.2.7, i16* %arrayidx9.5.2.7, align 2, !tbaa !3 *)
mov mem0_124 v_sub_5_2_7;
(*   %add21.5.2.7 = add i16 %1341, %call.i.5.2.7 *)
add v_add21_5_2_7 v1341 v_call_i_5_2_7;
(*   store i16 %add21.5.2.7, i16* %arrayidx11.5.2.7, align 2, !tbaa !3 *)
mov mem0_116 v_add21_5_2_7;
(*   %arrayidx9.5.3.7 = getelementptr inbounds i16, i16* %r, i64 63 *)
(*   %1342 = load i16, i16* %arrayidx9.5.3.7, align 2, !tbaa !3 *)
mov v1342 mem0_126;
(*   %conv1.i.5.3.7 = sext i16 %1342 to i32 *)
cast v_conv1_i_5_3_7@sint32 v1342@sint16;
(*   %mul.i.5.3.7 = mul nsw i32 %conv1.i.5.3.7, -1544 *)
mul v_mul_i_5_3_7 v_conv1_i_5_3_7 (-1544)@sint32;
(*   %call.i.5.3.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_7, v_call_i_5_3_7);
(*   %arrayidx11.5.3.7 = getelementptr inbounds i16, i16* %r, i64 59 *)
(*   %1343 = load i16, i16* %arrayidx11.5.3.7, align 2, !tbaa !3 *)
mov v1343 mem0_118;
(*   %sub.5.3.7 = sub i16 %1343, %call.i.5.3.7 *)
sub v_sub_5_3_7 v1343 v_call_i_5_3_7;
(*   store i16 %sub.5.3.7, i16* %arrayidx9.5.3.7, align 2, !tbaa !3 *)
mov mem0_126 v_sub_5_3_7;
(*   %add21.5.3.7 = add i16 %1343, %call.i.5.3.7 *)
add v_add21_5_3_7 v1343 v_call_i_5_3_7;
(*   store i16 %add21.5.3.7, i16* %arrayidx11.5.3.7, align 2, !tbaa !3 *)
mov mem0_118 v_add21_5_3_7;

(* NOTE: k = 40 *)

(*   %arrayidx9.5.8 = getelementptr inbounds i16, i16* %r, i64 68 *)
(*   %1344 = load i16, i16* %arrayidx9.5.8, align 2, !tbaa !3 *)
mov v1344 mem0_136;
(*   %conv1.i.5.8 = sext i16 %1344 to i32 *)
cast v_conv1_i_5_8@sint32 v1344@sint16;
(*   %mul.i.5.8 = mul nsw i32 %conv1.i.5.8, 516 *)
mul v_mul_i_5_8 v_conv1_i_5_8 (516)@sint32;
(*   %call.i.5.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_8, v_call_i_5_8);
(*   %arrayidx11.5.8 = getelementptr inbounds i16, i16* %r, i64 64 *)
(*   %1345 = load i16, i16* %arrayidx11.5.8, align 2, !tbaa !3 *)
mov v1345 mem0_128;
(*   %sub.5.8 = sub i16 %1345, %call.i.5.8 *)
sub v_sub_5_8 v1345 v_call_i_5_8;
(*   store i16 %sub.5.8, i16* %arrayidx9.5.8, align 2, !tbaa !3 *)
mov mem0_136 v_sub_5_8;
(*   %add21.5.8 = add i16 %1345, %call.i.5.8 *)
add v_add21_5_8 v1345 v_call_i_5_8;
(*   store i16 %add21.5.8, i16* %arrayidx11.5.8, align 2, !tbaa !3 *)
mov mem0_128 v_add21_5_8;
(*   %arrayidx9.5.1.8 = getelementptr inbounds i16, i16* %r, i64 69 *)
(*   %1346 = load i16, i16* %arrayidx9.5.1.8, align 2, !tbaa !3 *)
mov v1346 mem0_138;
(*   %conv1.i.5.1.8 = sext i16 %1346 to i32 *)
cast v_conv1_i_5_1_8@sint32 v1346@sint16;
(*   %mul.i.5.1.8 = mul nsw i32 %conv1.i.5.1.8, 516 *)
mul v_mul_i_5_1_8 v_conv1_i_5_1_8 (516)@sint32;
(*   %call.i.5.1.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_8, v_call_i_5_1_8);
(*   %arrayidx11.5.1.8 = getelementptr inbounds i16, i16* %r, i64 65 *)
(*   %1347 = load i16, i16* %arrayidx11.5.1.8, align 2, !tbaa !3 *)
mov v1347 mem0_130;
(*   %sub.5.1.8 = sub i16 %1347, %call.i.5.1.8 *)
sub v_sub_5_1_8 v1347 v_call_i_5_1_8;
(*   store i16 %sub.5.1.8, i16* %arrayidx9.5.1.8, align 2, !tbaa !3 *)
mov mem0_138 v_sub_5_1_8;
(*   %add21.5.1.8 = add i16 %1347, %call.i.5.1.8 *)
add v_add21_5_1_8 v1347 v_call_i_5_1_8;
(*   store i16 %add21.5.1.8, i16* %arrayidx11.5.1.8, align 2, !tbaa !3 *)
mov mem0_130 v_add21_5_1_8;
(*   %arrayidx9.5.2.8 = getelementptr inbounds i16, i16* %r, i64 70 *)
(*   %1348 = load i16, i16* %arrayidx9.5.2.8, align 2, !tbaa !3 *)
mov v1348 mem0_140;
(*   %conv1.i.5.2.8 = sext i16 %1348 to i32 *)
cast v_conv1_i_5_2_8@sint32 v1348@sint16;
(*   %mul.i.5.2.8 = mul nsw i32 %conv1.i.5.2.8, 516 *)
mul v_mul_i_5_2_8 v_conv1_i_5_2_8 (516)@sint32;
(*   %call.i.5.2.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_8, v_call_i_5_2_8);
(*   %arrayidx11.5.2.8 = getelementptr inbounds i16, i16* %r, i64 66 *)
(*   %1349 = load i16, i16* %arrayidx11.5.2.8, align 2, !tbaa !3 *)
mov v1349 mem0_132;
(*   %sub.5.2.8 = sub i16 %1349, %call.i.5.2.8 *)
sub v_sub_5_2_8 v1349 v_call_i_5_2_8;
(*   store i16 %sub.5.2.8, i16* %arrayidx9.5.2.8, align 2, !tbaa !3 *)
mov mem0_140 v_sub_5_2_8;
(*   %add21.5.2.8 = add i16 %1349, %call.i.5.2.8 *)
add v_add21_5_2_8 v1349 v_call_i_5_2_8;
(*   store i16 %add21.5.2.8, i16* %arrayidx11.5.2.8, align 2, !tbaa !3 *)
mov mem0_132 v_add21_5_2_8;
(*   %arrayidx9.5.3.8 = getelementptr inbounds i16, i16* %r, i64 71 *)
(*   %1350 = load i16, i16* %arrayidx9.5.3.8, align 2, !tbaa !3 *)
mov v1350 mem0_142;
(*   %conv1.i.5.3.8 = sext i16 %1350 to i32 *)
cast v_conv1_i_5_3_8@sint32 v1350@sint16;
(*   %mul.i.5.3.8 = mul nsw i32 %conv1.i.5.3.8, 516 *)
mul v_mul_i_5_3_8 v_conv1_i_5_3_8 (516)@sint32;
(*   %call.i.5.3.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_8, v_call_i_5_3_8);
(*   %arrayidx11.5.3.8 = getelementptr inbounds i16, i16* %r, i64 67 *)
(*   %1351 = load i16, i16* %arrayidx11.5.3.8, align 2, !tbaa !3 *)
mov v1351 mem0_134;
(*   %sub.5.3.8 = sub i16 %1351, %call.i.5.3.8 *)
sub v_sub_5_3_8 v1351 v_call_i_5_3_8;
(*   store i16 %sub.5.3.8, i16* %arrayidx9.5.3.8, align 2, !tbaa !3 *)
mov mem0_142 v_sub_5_3_8;
(*   %add21.5.3.8 = add i16 %1351, %call.i.5.3.8 *)
add v_add21_5_3_8 v1351 v_call_i_5_3_8;
(*   store i16 %add21.5.3.8, i16* %arrayidx11.5.3.8, align 2, !tbaa !3 *)
mov mem0_134 v_add21_5_3_8;

(* NOTE: k = 41 *)

(*   %arrayidx9.5.9 = getelementptr inbounds i16, i16* %r, i64 76 *)
(*   %1352 = load i16, i16* %arrayidx9.5.9, align 2, !tbaa !3 *)
mov v1352 mem0_152;
(*   %conv1.i.5.9 = sext i16 %1352 to i32 *)
cast v_conv1_i_5_9@sint32 v1352@sint16;
(*   %mul.i.5.9 = mul nsw i32 %conv1.i.5.9, -8 *)
mul v_mul_i_5_9 v_conv1_i_5_9 (-8)@sint32;
(*   %call.i.5.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_9, v_call_i_5_9);
(*   %arrayidx11.5.9 = getelementptr inbounds i16, i16* %r, i64 72 *)
(*   %1353 = load i16, i16* %arrayidx11.5.9, align 2, !tbaa !3 *)
mov v1353 mem0_144;
(*   %sub.5.9 = sub i16 %1353, %call.i.5.9 *)
sub v_sub_5_9 v1353 v_call_i_5_9;
(*   store i16 %sub.5.9, i16* %arrayidx9.5.9, align 2, !tbaa !3 *)
mov mem0_152 v_sub_5_9;
(*   %add21.5.9 = add i16 %1353, %call.i.5.9 *)
add v_add21_5_9 v1353 v_call_i_5_9;
(*   store i16 %add21.5.9, i16* %arrayidx11.5.9, align 2, !tbaa !3 *)
mov mem0_144 v_add21_5_9;
(*   %arrayidx9.5.1.9 = getelementptr inbounds i16, i16* %r, i64 77 *)
(*   %1354 = load i16, i16* %arrayidx9.5.1.9, align 2, !tbaa !3 *)
mov v1354 mem0_154;
(*   %conv1.i.5.1.9 = sext i16 %1354 to i32 *)
cast v_conv1_i_5_1_9@sint32 v1354@sint16;
(*   %mul.i.5.1.9 = mul nsw i32 %conv1.i.5.1.9, -8 *)
mul v_mul_i_5_1_9 v_conv1_i_5_1_9 (-8)@sint32;
(*   %call.i.5.1.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_9, v_call_i_5_1_9);
(*   %arrayidx11.5.1.9 = getelementptr inbounds i16, i16* %r, i64 73 *)
(*   %1355 = load i16, i16* %arrayidx11.5.1.9, align 2, !tbaa !3 *)
mov v1355 mem0_146;
(*   %sub.5.1.9 = sub i16 %1355, %call.i.5.1.9 *)
sub v_sub_5_1_9 v1355 v_call_i_5_1_9;
(*   store i16 %sub.5.1.9, i16* %arrayidx9.5.1.9, align 2, !tbaa !3 *)
mov mem0_154 v_sub_5_1_9;
(*   %add21.5.1.9 = add i16 %1355, %call.i.5.1.9 *)
add v_add21_5_1_9 v1355 v_call_i_5_1_9;
(*   store i16 %add21.5.1.9, i16* %arrayidx11.5.1.9, align 2, !tbaa !3 *)
mov mem0_146 v_add21_5_1_9;
(*   %arrayidx9.5.2.9 = getelementptr inbounds i16, i16* %r, i64 78 *)
(*   %1356 = load i16, i16* %arrayidx9.5.2.9, align 2, !tbaa !3 *)
mov v1356 mem0_156;
(*   %conv1.i.5.2.9 = sext i16 %1356 to i32 *)
cast v_conv1_i_5_2_9@sint32 v1356@sint16;
(*   %mul.i.5.2.9 = mul nsw i32 %conv1.i.5.2.9, -8 *)
mul v_mul_i_5_2_9 v_conv1_i_5_2_9 (-8)@sint32;
(*   %call.i.5.2.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_9, v_call_i_5_2_9);
(*   %arrayidx11.5.2.9 = getelementptr inbounds i16, i16* %r, i64 74 *)
(*   %1357 = load i16, i16* %arrayidx11.5.2.9, align 2, !tbaa !3 *)
mov v1357 mem0_148;
(*   %sub.5.2.9 = sub i16 %1357, %call.i.5.2.9 *)
sub v_sub_5_2_9 v1357 v_call_i_5_2_9;
(*   store i16 %sub.5.2.9, i16* %arrayidx9.5.2.9, align 2, !tbaa !3 *)
mov mem0_156 v_sub_5_2_9;
(*   %add21.5.2.9 = add i16 %1357, %call.i.5.2.9 *)
add v_add21_5_2_9 v1357 v_call_i_5_2_9;
(*   store i16 %add21.5.2.9, i16* %arrayidx11.5.2.9, align 2, !tbaa !3 *)
mov mem0_148 v_add21_5_2_9;
(*   %arrayidx9.5.3.9 = getelementptr inbounds i16, i16* %r, i64 79 *)
(*   %1358 = load i16, i16* %arrayidx9.5.3.9, align 2, !tbaa !3 *)
mov v1358 mem0_158;
(*   %conv1.i.5.3.9 = sext i16 %1358 to i32 *)
cast v_conv1_i_5_3_9@sint32 v1358@sint16;
(*   %mul.i.5.3.9 = mul nsw i32 %conv1.i.5.3.9, -8 *)
mul v_mul_i_5_3_9 v_conv1_i_5_3_9 (-8)@sint32;
(*   %call.i.5.3.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_9, v_call_i_5_3_9);
(*   %arrayidx11.5.3.9 = getelementptr inbounds i16, i16* %r, i64 75 *)
(*   %1359 = load i16, i16* %arrayidx11.5.3.9, align 2, !tbaa !3 *)
mov v1359 mem0_150;
(*   %sub.5.3.9 = sub i16 %1359, %call.i.5.3.9 *)
sub v_sub_5_3_9 v1359 v_call_i_5_3_9;
(*   store i16 %sub.5.3.9, i16* %arrayidx9.5.3.9, align 2, !tbaa !3 *)
mov mem0_158 v_sub_5_3_9;
(*   %add21.5.3.9 = add i16 %1359, %call.i.5.3.9 *)
add v_add21_5_3_9 v1359 v_call_i_5_3_9;
(*   store i16 %add21.5.3.9, i16* %arrayidx11.5.3.9, align 2, !tbaa !3 *)
mov mem0_150 v_add21_5_3_9;

(* NOTE: k = 42 *)

(*   %arrayidx9.5.10 = getelementptr inbounds i16, i16* %r, i64 84 *)
(*   %1360 = load i16, i16* %arrayidx9.5.10, align 2, !tbaa !3 *)
mov v1360 mem0_168;
(*   %conv1.i.5.10 = sext i16 %1360 to i32 *)
cast v_conv1_i_5_10@sint32 v1360@sint16;
(*   %mul.i.5.10 = mul nsw i32 %conv1.i.5.10, -320 *)
mul v_mul_i_5_10 v_conv1_i_5_10 (-320)@sint32;
(*   %call.i.5.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_10, v_call_i_5_10);
(*   %arrayidx11.5.10 = getelementptr inbounds i16, i16* %r, i64 80 *)
(*   %1361 = load i16, i16* %arrayidx11.5.10, align 2, !tbaa !3 *)
mov v1361 mem0_160;
(*   %sub.5.10 = sub i16 %1361, %call.i.5.10 *)
sub v_sub_5_10 v1361 v_call_i_5_10;
(*   store i16 %sub.5.10, i16* %arrayidx9.5.10, align 2, !tbaa !3 *)
mov mem0_168 v_sub_5_10;
(*   %add21.5.10 = add i16 %1361, %call.i.5.10 *)
add v_add21_5_10 v1361 v_call_i_5_10;
(*   store i16 %add21.5.10, i16* %arrayidx11.5.10, align 2, !tbaa !3 *)
mov mem0_160 v_add21_5_10;
(*   %arrayidx9.5.1.10 = getelementptr inbounds i16, i16* %r, i64 85 *)
(*   %1362 = load i16, i16* %arrayidx9.5.1.10, align 2, !tbaa !3 *)
mov v1362 mem0_170;
(*   %conv1.i.5.1.10 = sext i16 %1362 to i32 *)
cast v_conv1_i_5_1_10@sint32 v1362@sint16;
(*   %mul.i.5.1.10 = mul nsw i32 %conv1.i.5.1.10, -320 *)
mul v_mul_i_5_1_10 v_conv1_i_5_1_10 (-320)@sint32;
(*   %call.i.5.1.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_10, v_call_i_5_1_10);
(*   %arrayidx11.5.1.10 = getelementptr inbounds i16, i16* %r, i64 81 *)
(*   %1363 = load i16, i16* %arrayidx11.5.1.10, align 2, !tbaa !3 *)
mov v1363 mem0_162;
(*   %sub.5.1.10 = sub i16 %1363, %call.i.5.1.10 *)
sub v_sub_5_1_10 v1363 v_call_i_5_1_10;
(*   store i16 %sub.5.1.10, i16* %arrayidx9.5.1.10, align 2, !tbaa !3 *)
mov mem0_170 v_sub_5_1_10;
(*   %add21.5.1.10 = add i16 %1363, %call.i.5.1.10 *)
add v_add21_5_1_10 v1363 v_call_i_5_1_10;
(*   store i16 %add21.5.1.10, i16* %arrayidx11.5.1.10, align 2, !tbaa !3 *)
mov mem0_162 v_add21_5_1_10;
(*   %arrayidx9.5.2.10 = getelementptr inbounds i16, i16* %r, i64 86 *)
(*   %1364 = load i16, i16* %arrayidx9.5.2.10, align 2, !tbaa !3 *)
mov v1364 mem0_172;
(*   %conv1.i.5.2.10 = sext i16 %1364 to i32 *)
cast v_conv1_i_5_2_10@sint32 v1364@sint16;
(*   %mul.i.5.2.10 = mul nsw i32 %conv1.i.5.2.10, -320 *)
mul v_mul_i_5_2_10 v_conv1_i_5_2_10 (-320)@sint32;
(*   %call.i.5.2.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_10, v_call_i_5_2_10);
(*   %arrayidx11.5.2.10 = getelementptr inbounds i16, i16* %r, i64 82 *)
(*   %1365 = load i16, i16* %arrayidx11.5.2.10, align 2, !tbaa !3 *)
mov v1365 mem0_164;
(*   %sub.5.2.10 = sub i16 %1365, %call.i.5.2.10 *)
sub v_sub_5_2_10 v1365 v_call_i_5_2_10;
(*   store i16 %sub.5.2.10, i16* %arrayidx9.5.2.10, align 2, !tbaa !3 *)
mov mem0_172 v_sub_5_2_10;
(*   %add21.5.2.10 = add i16 %1365, %call.i.5.2.10 *)
add v_add21_5_2_10 v1365 v_call_i_5_2_10;
(*   store i16 %add21.5.2.10, i16* %arrayidx11.5.2.10, align 2, !tbaa !3 *)
mov mem0_164 v_add21_5_2_10;
(*   %arrayidx9.5.3.10 = getelementptr inbounds i16, i16* %r, i64 87 *)
(*   %1366 = load i16, i16* %arrayidx9.5.3.10, align 2, !tbaa !3 *)
mov v1366 mem0_174;
(*   %conv1.i.5.3.10 = sext i16 %1366 to i32 *)
cast v_conv1_i_5_3_10@sint32 v1366@sint16;
(*   %mul.i.5.3.10 = mul nsw i32 %conv1.i.5.3.10, -320 *)
mul v_mul_i_5_3_10 v_conv1_i_5_3_10 (-320)@sint32;
(*   %call.i.5.3.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_10, v_call_i_5_3_10);
(*   %arrayidx11.5.3.10 = getelementptr inbounds i16, i16* %r, i64 83 *)
(*   %1367 = load i16, i16* %arrayidx11.5.3.10, align 2, !tbaa !3 *)
mov v1367 mem0_166;
(*   %sub.5.3.10 = sub i16 %1367, %call.i.5.3.10 *)
sub v_sub_5_3_10 v1367 v_call_i_5_3_10;
(*   store i16 %sub.5.3.10, i16* %arrayidx9.5.3.10, align 2, !tbaa !3 *)
mov mem0_174 v_sub_5_3_10;
(*   %add21.5.3.10 = add i16 %1367, %call.i.5.3.10 *)
add v_add21_5_3_10 v1367 v_call_i_5_3_10;
(*   store i16 %add21.5.3.10, i16* %arrayidx11.5.3.10, align 2, !tbaa !3 *)
mov mem0_166 v_add21_5_3_10;

(* NOTE: k = 43 *)

(*   %arrayidx9.5.11 = getelementptr inbounds i16, i16* %r, i64 92 *)
(*   %1368 = load i16, i16* %arrayidx9.5.11, align 2, !tbaa !3 *)
mov v1368 mem0_184;
(*   %conv1.i.5.11 = sext i16 %1368 to i32 *)
cast v_conv1_i_5_11@sint32 v1368@sint16;
(*   %mul.i.5.11 = mul nsw i32 %conv1.i.5.11, -666 *)
mul v_mul_i_5_11 v_conv1_i_5_11 (-666)@sint32;
(*   %call.i.5.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_11, v_call_i_5_11);
(*   %arrayidx11.5.11 = getelementptr inbounds i16, i16* %r, i64 88 *)
(*   %1369 = load i16, i16* %arrayidx11.5.11, align 2, !tbaa !3 *)
mov v1369 mem0_176;
(*   %sub.5.11 = sub i16 %1369, %call.i.5.11 *)
sub v_sub_5_11 v1369 v_call_i_5_11;
(*   store i16 %sub.5.11, i16* %arrayidx9.5.11, align 2, !tbaa !3 *)
mov mem0_184 v_sub_5_11;
(*   %add21.5.11 = add i16 %1369, %call.i.5.11 *)
add v_add21_5_11 v1369 v_call_i_5_11;
(*   store i16 %add21.5.11, i16* %arrayidx11.5.11, align 2, !tbaa !3 *)
mov mem0_176 v_add21_5_11;
(*   %arrayidx9.5.1.11 = getelementptr inbounds i16, i16* %r, i64 93 *)
(*   %1370 = load i16, i16* %arrayidx9.5.1.11, align 2, !tbaa !3 *)
mov v1370 mem0_186;
(*   %conv1.i.5.1.11 = sext i16 %1370 to i32 *)
cast v_conv1_i_5_1_11@sint32 v1370@sint16;
(*   %mul.i.5.1.11 = mul nsw i32 %conv1.i.5.1.11, -666 *)
mul v_mul_i_5_1_11 v_conv1_i_5_1_11 (-666)@sint32;
(*   %call.i.5.1.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_11, v_call_i_5_1_11);
(*   %arrayidx11.5.1.11 = getelementptr inbounds i16, i16* %r, i64 89 *)
(*   %1371 = load i16, i16* %arrayidx11.5.1.11, align 2, !tbaa !3 *)
mov v1371 mem0_178;
(*   %sub.5.1.11 = sub i16 %1371, %call.i.5.1.11 *)
sub v_sub_5_1_11 v1371 v_call_i_5_1_11;
(*   store i16 %sub.5.1.11, i16* %arrayidx9.5.1.11, align 2, !tbaa !3 *)
mov mem0_186 v_sub_5_1_11;
(*   %add21.5.1.11 = add i16 %1371, %call.i.5.1.11 *)
add v_add21_5_1_11 v1371 v_call_i_5_1_11;
(*   store i16 %add21.5.1.11, i16* %arrayidx11.5.1.11, align 2, !tbaa !3 *)
mov mem0_178 v_add21_5_1_11;
(*   %arrayidx9.5.2.11 = getelementptr inbounds i16, i16* %r, i64 94 *)
(*   %1372 = load i16, i16* %arrayidx9.5.2.11, align 2, !tbaa !3 *)
mov v1372 mem0_188;
(*   %conv1.i.5.2.11 = sext i16 %1372 to i32 *)
cast v_conv1_i_5_2_11@sint32 v1372@sint16;
(*   %mul.i.5.2.11 = mul nsw i32 %conv1.i.5.2.11, -666 *)
mul v_mul_i_5_2_11 v_conv1_i_5_2_11 (-666)@sint32;
(*   %call.i.5.2.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_11, v_call_i_5_2_11);
(*   %arrayidx11.5.2.11 = getelementptr inbounds i16, i16* %r, i64 90 *)
(*   %1373 = load i16, i16* %arrayidx11.5.2.11, align 2, !tbaa !3 *)
mov v1373 mem0_180;
(*   %sub.5.2.11 = sub i16 %1373, %call.i.5.2.11 *)
sub v_sub_5_2_11 v1373 v_call_i_5_2_11;
(*   store i16 %sub.5.2.11, i16* %arrayidx9.5.2.11, align 2, !tbaa !3 *)
mov mem0_188 v_sub_5_2_11;
(*   %add21.5.2.11 = add i16 %1373, %call.i.5.2.11 *)
add v_add21_5_2_11 v1373 v_call_i_5_2_11;
(*   store i16 %add21.5.2.11, i16* %arrayidx11.5.2.11, align 2, !tbaa !3 *)
mov mem0_180 v_add21_5_2_11;
(*   %arrayidx9.5.3.11 = getelementptr inbounds i16, i16* %r, i64 95 *)
(*   %1374 = load i16, i16* %arrayidx9.5.3.11, align 2, !tbaa !3 *)
mov v1374 mem0_190;
(*   %conv1.i.5.3.11 = sext i16 %1374 to i32 *)
cast v_conv1_i_5_3_11@sint32 v1374@sint16;
(*   %mul.i.5.3.11 = mul nsw i32 %conv1.i.5.3.11, -666 *)
mul v_mul_i_5_3_11 v_conv1_i_5_3_11 (-666)@sint32;
(*   %call.i.5.3.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_11, v_call_i_5_3_11);
(*   %arrayidx11.5.3.11 = getelementptr inbounds i16, i16* %r, i64 91 *)
(*   %1375 = load i16, i16* %arrayidx11.5.3.11, align 2, !tbaa !3 *)
mov v1375 mem0_182;
(*   %sub.5.3.11 = sub i16 %1375, %call.i.5.3.11 *)
sub v_sub_5_3_11 v1375 v_call_i_5_3_11;
(*   store i16 %sub.5.3.11, i16* %arrayidx9.5.3.11, align 2, !tbaa !3 *)
mov mem0_190 v_sub_5_3_11;
(*   %add21.5.3.11 = add i16 %1375, %call.i.5.3.11 *)
add v_add21_5_3_11 v1375 v_call_i_5_3_11;
(*   store i16 %add21.5.3.11, i16* %arrayidx11.5.3.11, align 2, !tbaa !3 *)
mov mem0_182 v_add21_5_3_11;

(* NOTE: k = 44 *)

(*   %arrayidx9.5.12 = getelementptr inbounds i16, i16* %r, i64 100 *)
(*   %1376 = load i16, i16* %arrayidx9.5.12, align 2, !tbaa !3 *)
mov v1376 mem0_200;
(*   %conv1.i.5.12 = sext i16 %1376 to i32 *)
cast v_conv1_i_5_12@sint32 v1376@sint16;
(*   %mul.i.5.12 = mul nsw i32 %conv1.i.5.12, -1618 *)
mul v_mul_i_5_12 v_conv1_i_5_12 (-1618)@sint32;
(*   %call.i.5.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_12, v_call_i_5_12);
(*   %arrayidx11.5.12 = getelementptr inbounds i16, i16* %r, i64 96 *)
(*   %1377 = load i16, i16* %arrayidx11.5.12, align 2, !tbaa !3 *)
mov v1377 mem0_192;
(*   %sub.5.12 = sub i16 %1377, %call.i.5.12 *)
sub v_sub_5_12 v1377 v_call_i_5_12;
(*   store i16 %sub.5.12, i16* %arrayidx9.5.12, align 2, !tbaa !3 *)
mov mem0_200 v_sub_5_12;
(*   %add21.5.12 = add i16 %1377, %call.i.5.12 *)
add v_add21_5_12 v1377 v_call_i_5_12;
(*   store i16 %add21.5.12, i16* %arrayidx11.5.12, align 2, !tbaa !3 *)
mov mem0_192 v_add21_5_12;
(*   %arrayidx9.5.1.12 = getelementptr inbounds i16, i16* %r, i64 101 *)
(*   %1378 = load i16, i16* %arrayidx9.5.1.12, align 2, !tbaa !3 *)
mov v1378 mem0_202;
(*   %conv1.i.5.1.12 = sext i16 %1378 to i32 *)
cast v_conv1_i_5_1_12@sint32 v1378@sint16;
(*   %mul.i.5.1.12 = mul nsw i32 %conv1.i.5.1.12, -1618 *)
mul v_mul_i_5_1_12 v_conv1_i_5_1_12 (-1618)@sint32;
(*   %call.i.5.1.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_12, v_call_i_5_1_12);
(*   %arrayidx11.5.1.12 = getelementptr inbounds i16, i16* %r, i64 97 *)
(*   %1379 = load i16, i16* %arrayidx11.5.1.12, align 2, !tbaa !3 *)
mov v1379 mem0_194;
(*   %sub.5.1.12 = sub i16 %1379, %call.i.5.1.12 *)
sub v_sub_5_1_12 v1379 v_call_i_5_1_12;
(*   store i16 %sub.5.1.12, i16* %arrayidx9.5.1.12, align 2, !tbaa !3 *)
mov mem0_202 v_sub_5_1_12;
(*   %add21.5.1.12 = add i16 %1379, %call.i.5.1.12 *)
add v_add21_5_1_12 v1379 v_call_i_5_1_12;
(*   store i16 %add21.5.1.12, i16* %arrayidx11.5.1.12, align 2, !tbaa !3 *)
mov mem0_194 v_add21_5_1_12;
(*   %arrayidx9.5.2.12 = getelementptr inbounds i16, i16* %r, i64 102 *)
(*   %1380 = load i16, i16* %arrayidx9.5.2.12, align 2, !tbaa !3 *)
mov v1380 mem0_204;
(*   %conv1.i.5.2.12 = sext i16 %1380 to i32 *)
cast v_conv1_i_5_2_12@sint32 v1380@sint16;
(*   %mul.i.5.2.12 = mul nsw i32 %conv1.i.5.2.12, -1618 *)
mul v_mul_i_5_2_12 v_conv1_i_5_2_12 (-1618)@sint32;
(*   %call.i.5.2.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_12, v_call_i_5_2_12);
(*   %arrayidx11.5.2.12 = getelementptr inbounds i16, i16* %r, i64 98 *)
(*   %1381 = load i16, i16* %arrayidx11.5.2.12, align 2, !tbaa !3 *)
mov v1381 mem0_196;
(*   %sub.5.2.12 = sub i16 %1381, %call.i.5.2.12 *)
sub v_sub_5_2_12 v1381 v_call_i_5_2_12;
(*   store i16 %sub.5.2.12, i16* %arrayidx9.5.2.12, align 2, !tbaa !3 *)
mov mem0_204 v_sub_5_2_12;
(*   %add21.5.2.12 = add i16 %1381, %call.i.5.2.12 *)
add v_add21_5_2_12 v1381 v_call_i_5_2_12;
(*   store i16 %add21.5.2.12, i16* %arrayidx11.5.2.12, align 2, !tbaa !3 *)
mov mem0_196 v_add21_5_2_12;
(*   %arrayidx9.5.3.12 = getelementptr inbounds i16, i16* %r, i64 103 *)
(*   %1382 = load i16, i16* %arrayidx9.5.3.12, align 2, !tbaa !3 *)
mov v1382 mem0_206;
(*   %conv1.i.5.3.12 = sext i16 %1382 to i32 *)
cast v_conv1_i_5_3_12@sint32 v1382@sint16;
(*   %mul.i.5.3.12 = mul nsw i32 %conv1.i.5.3.12, -1618 *)
mul v_mul_i_5_3_12 v_conv1_i_5_3_12 (-1618)@sint32;
(*   %call.i.5.3.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_12, v_call_i_5_3_12);
(*   %arrayidx11.5.3.12 = getelementptr inbounds i16, i16* %r, i64 99 *)
(*   %1383 = load i16, i16* %arrayidx11.5.3.12, align 2, !tbaa !3 *)
mov v1383 mem0_198;
(*   %sub.5.3.12 = sub i16 %1383, %call.i.5.3.12 *)
sub v_sub_5_3_12 v1383 v_call_i_5_3_12;
(*   store i16 %sub.5.3.12, i16* %arrayidx9.5.3.12, align 2, !tbaa !3 *)
mov mem0_206 v_sub_5_3_12;
(*   %add21.5.3.12 = add i16 %1383, %call.i.5.3.12 *)
add v_add21_5_3_12 v1383 v_call_i_5_3_12;
(*   store i16 %add21.5.3.12, i16* %arrayidx11.5.3.12, align 2, !tbaa !3 *)
mov mem0_198 v_add21_5_3_12;

(* NOTE: k = 45 *)

(*   %arrayidx9.5.13 = getelementptr inbounds i16, i16* %r, i64 108 *)
(*   %1384 = load i16, i16* %arrayidx9.5.13, align 2, !tbaa !3 *)
mov v1384 mem0_216;
(*   %conv1.i.5.13 = sext i16 %1384 to i32 *)
cast v_conv1_i_5_13@sint32 v1384@sint16;
(*   %mul.i.5.13 = mul nsw i32 %conv1.i.5.13, -1162 *)
mul v_mul_i_5_13 v_conv1_i_5_13 (-1162)@sint32;
(*   %call.i.5.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_13, v_call_i_5_13);
(*   %arrayidx11.5.13 = getelementptr inbounds i16, i16* %r, i64 104 *)
(*   %1385 = load i16, i16* %arrayidx11.5.13, align 2, !tbaa !3 *)
mov v1385 mem0_208;
(*   %sub.5.13 = sub i16 %1385, %call.i.5.13 *)
sub v_sub_5_13 v1385 v_call_i_5_13;
(*   store i16 %sub.5.13, i16* %arrayidx9.5.13, align 2, !tbaa !3 *)
mov mem0_216 v_sub_5_13;
(*   %add21.5.13 = add i16 %1385, %call.i.5.13 *)
add v_add21_5_13 v1385 v_call_i_5_13;
(*   store i16 %add21.5.13, i16* %arrayidx11.5.13, align 2, !tbaa !3 *)
mov mem0_208 v_add21_5_13;
(*   %arrayidx9.5.1.13 = getelementptr inbounds i16, i16* %r, i64 109 *)
(*   %1386 = load i16, i16* %arrayidx9.5.1.13, align 2, !tbaa !3 *)
mov v1386 mem0_218;
(*   %conv1.i.5.1.13 = sext i16 %1386 to i32 *)
cast v_conv1_i_5_1_13@sint32 v1386@sint16;
(*   %mul.i.5.1.13 = mul nsw i32 %conv1.i.5.1.13, -1162 *)
mul v_mul_i_5_1_13 v_conv1_i_5_1_13 (-1162)@sint32;
(*   %call.i.5.1.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_13, v_call_i_5_1_13);
(*   %arrayidx11.5.1.13 = getelementptr inbounds i16, i16* %r, i64 105 *)
(*   %1387 = load i16, i16* %arrayidx11.5.1.13, align 2, !tbaa !3 *)
mov v1387 mem0_210;
(*   %sub.5.1.13 = sub i16 %1387, %call.i.5.1.13 *)
sub v_sub_5_1_13 v1387 v_call_i_5_1_13;
(*   store i16 %sub.5.1.13, i16* %arrayidx9.5.1.13, align 2, !tbaa !3 *)
mov mem0_218 v_sub_5_1_13;
(*   %add21.5.1.13 = add i16 %1387, %call.i.5.1.13 *)
add v_add21_5_1_13 v1387 v_call_i_5_1_13;
(*   store i16 %add21.5.1.13, i16* %arrayidx11.5.1.13, align 2, !tbaa !3 *)
mov mem0_210 v_add21_5_1_13;
(*   %arrayidx9.5.2.13 = getelementptr inbounds i16, i16* %r, i64 110 *)
(*   %1388 = load i16, i16* %arrayidx9.5.2.13, align 2, !tbaa !3 *)
mov v1388 mem0_220;
(*   %conv1.i.5.2.13 = sext i16 %1388 to i32 *)
cast v_conv1_i_5_2_13@sint32 v1388@sint16;
(*   %mul.i.5.2.13 = mul nsw i32 %conv1.i.5.2.13, -1162 *)
mul v_mul_i_5_2_13 v_conv1_i_5_2_13 (-1162)@sint32;
(*   %call.i.5.2.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_13, v_call_i_5_2_13);
(*   %arrayidx11.5.2.13 = getelementptr inbounds i16, i16* %r, i64 106 *)
(*   %1389 = load i16, i16* %arrayidx11.5.2.13, align 2, !tbaa !3 *)
mov v1389 mem0_212;
(*   %sub.5.2.13 = sub i16 %1389, %call.i.5.2.13 *)
sub v_sub_5_2_13 v1389 v_call_i_5_2_13;
(*   store i16 %sub.5.2.13, i16* %arrayidx9.5.2.13, align 2, !tbaa !3 *)
mov mem0_220 v_sub_5_2_13;
(*   %add21.5.2.13 = add i16 %1389, %call.i.5.2.13 *)
add v_add21_5_2_13 v1389 v_call_i_5_2_13;
(*   store i16 %add21.5.2.13, i16* %arrayidx11.5.2.13, align 2, !tbaa !3 *)
mov mem0_212 v_add21_5_2_13;
(*   %arrayidx9.5.3.13 = getelementptr inbounds i16, i16* %r, i64 111 *)
(*   %1390 = load i16, i16* %arrayidx9.5.3.13, align 2, !tbaa !3 *)
mov v1390 mem0_222;
(*   %conv1.i.5.3.13 = sext i16 %1390 to i32 *)
cast v_conv1_i_5_3_13@sint32 v1390@sint16;
(*   %mul.i.5.3.13 = mul nsw i32 %conv1.i.5.3.13, -1162 *)
mul v_mul_i_5_3_13 v_conv1_i_5_3_13 (-1162)@sint32;
(*   %call.i.5.3.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_13, v_call_i_5_3_13);
(*   %arrayidx11.5.3.13 = getelementptr inbounds i16, i16* %r, i64 107 *)
(*   %1391 = load i16, i16* %arrayidx11.5.3.13, align 2, !tbaa !3 *)
mov v1391 mem0_214;
(*   %sub.5.3.13 = sub i16 %1391, %call.i.5.3.13 *)
sub v_sub_5_3_13 v1391 v_call_i_5_3_13;
(*   store i16 %sub.5.3.13, i16* %arrayidx9.5.3.13, align 2, !tbaa !3 *)
mov mem0_222 v_sub_5_3_13;
(*   %add21.5.3.13 = add i16 %1391, %call.i.5.3.13 *)
add v_add21_5_3_13 v1391 v_call_i_5_3_13;
(*   store i16 %add21.5.3.13, i16* %arrayidx11.5.3.13, align 2, !tbaa !3 *)
mov mem0_214 v_add21_5_3_13;

(* NOTE: k = 46 *)

(*   %arrayidx9.5.14 = getelementptr inbounds i16, i16* %r, i64 116 *)
(*   %1392 = load i16, i16* %arrayidx9.5.14, align 2, !tbaa !3 *)
mov v1392 mem0_232;
(*   %conv1.i.5.14 = sext i16 %1392 to i32 *)
cast v_conv1_i_5_14@sint32 v1392@sint16;
(*   %mul.i.5.14 = mul nsw i32 %conv1.i.5.14, 126 *)
mul v_mul_i_5_14 v_conv1_i_5_14 (126)@sint32;
(*   %call.i.5.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_14, v_call_i_5_14);
(*   %arrayidx11.5.14 = getelementptr inbounds i16, i16* %r, i64 112 *)
(*   %1393 = load i16, i16* %arrayidx11.5.14, align 2, !tbaa !3 *)
mov v1393 mem0_224;
(*   %sub.5.14 = sub i16 %1393, %call.i.5.14 *)
sub v_sub_5_14 v1393 v_call_i_5_14;
(*   store i16 %sub.5.14, i16* %arrayidx9.5.14, align 2, !tbaa !3 *)
mov mem0_232 v_sub_5_14;
(*   %add21.5.14 = add i16 %1393, %call.i.5.14 *)
add v_add21_5_14 v1393 v_call_i_5_14;
(*   store i16 %add21.5.14, i16* %arrayidx11.5.14, align 2, !tbaa !3 *)
mov mem0_224 v_add21_5_14;
(*   %arrayidx9.5.1.14 = getelementptr inbounds i16, i16* %r, i64 117 *)
(*   %1394 = load i16, i16* %arrayidx9.5.1.14, align 2, !tbaa !3 *)
mov v1394 mem0_234;
(*   %conv1.i.5.1.14 = sext i16 %1394 to i32 *)
cast v_conv1_i_5_1_14@sint32 v1394@sint16;
(*   %mul.i.5.1.14 = mul nsw i32 %conv1.i.5.1.14, 126 *)
mul v_mul_i_5_1_14 v_conv1_i_5_1_14 (126)@sint32;
(*   %call.i.5.1.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_14, v_call_i_5_1_14);
(*   %arrayidx11.5.1.14 = getelementptr inbounds i16, i16* %r, i64 113 *)
(*   %1395 = load i16, i16* %arrayidx11.5.1.14, align 2, !tbaa !3 *)
mov v1395 mem0_226;
(*   %sub.5.1.14 = sub i16 %1395, %call.i.5.1.14 *)
sub v_sub_5_1_14 v1395 v_call_i_5_1_14;
(*   store i16 %sub.5.1.14, i16* %arrayidx9.5.1.14, align 2, !tbaa !3 *)
mov mem0_234 v_sub_5_1_14;
(*   %add21.5.1.14 = add i16 %1395, %call.i.5.1.14 *)
add v_add21_5_1_14 v1395 v_call_i_5_1_14;
(*   store i16 %add21.5.1.14, i16* %arrayidx11.5.1.14, align 2, !tbaa !3 *)
mov mem0_226 v_add21_5_1_14;
(*   %arrayidx9.5.2.14 = getelementptr inbounds i16, i16* %r, i64 118 *)
(*   %1396 = load i16, i16* %arrayidx9.5.2.14, align 2, !tbaa !3 *)
mov v1396 mem0_236;
(*   %conv1.i.5.2.14 = sext i16 %1396 to i32 *)
cast v_conv1_i_5_2_14@sint32 v1396@sint16;
(*   %mul.i.5.2.14 = mul nsw i32 %conv1.i.5.2.14, 126 *)
mul v_mul_i_5_2_14 v_conv1_i_5_2_14 (126)@sint32;
(*   %call.i.5.2.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_14, v_call_i_5_2_14);
(*   %arrayidx11.5.2.14 = getelementptr inbounds i16, i16* %r, i64 114 *)
(*   %1397 = load i16, i16* %arrayidx11.5.2.14, align 2, !tbaa !3 *)
mov v1397 mem0_228;
(*   %sub.5.2.14 = sub i16 %1397, %call.i.5.2.14 *)
sub v_sub_5_2_14 v1397 v_call_i_5_2_14;
(*   store i16 %sub.5.2.14, i16* %arrayidx9.5.2.14, align 2, !tbaa !3 *)
mov mem0_236 v_sub_5_2_14;
(*   %add21.5.2.14 = add i16 %1397, %call.i.5.2.14 *)
add v_add21_5_2_14 v1397 v_call_i_5_2_14;
(*   store i16 %add21.5.2.14, i16* %arrayidx11.5.2.14, align 2, !tbaa !3 *)
mov mem0_228 v_add21_5_2_14;
(*   %arrayidx9.5.3.14 = getelementptr inbounds i16, i16* %r, i64 119 *)
(*   %1398 = load i16, i16* %arrayidx9.5.3.14, align 2, !tbaa !3 *)
mov v1398 mem0_238;
(*   %conv1.i.5.3.14 = sext i16 %1398 to i32 *)
cast v_conv1_i_5_3_14@sint32 v1398@sint16;
(*   %mul.i.5.3.14 = mul nsw i32 %conv1.i.5.3.14, 126 *)
mul v_mul_i_5_3_14 v_conv1_i_5_3_14 (126)@sint32;
(*   %call.i.5.3.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_14, v_call_i_5_3_14);
(*   %arrayidx11.5.3.14 = getelementptr inbounds i16, i16* %r, i64 115 *)
(*   %1399 = load i16, i16* %arrayidx11.5.3.14, align 2, !tbaa !3 *)
mov v1399 mem0_230;
(*   %sub.5.3.14 = sub i16 %1399, %call.i.5.3.14 *)
sub v_sub_5_3_14 v1399 v_call_i_5_3_14;
(*   store i16 %sub.5.3.14, i16* %arrayidx9.5.3.14, align 2, !tbaa !3 *)
mov mem0_238 v_sub_5_3_14;
(*   %add21.5.3.14 = add i16 %1399, %call.i.5.3.14 *)
add v_add21_5_3_14 v1399 v_call_i_5_3_14;
(*   store i16 %add21.5.3.14, i16* %arrayidx11.5.3.14, align 2, !tbaa !3 *)
mov mem0_230 v_add21_5_3_14;

(* NOTE: k = 47 *)

(*   %arrayidx9.5.15 = getelementptr inbounds i16, i16* %r, i64 124 *)
(*   %1400 = load i16, i16* %arrayidx9.5.15, align 2, !tbaa !3 *)
mov v1400 mem0_248;
(*   %conv1.i.5.15 = sext i16 %1400 to i32 *)
cast v_conv1_i_5_15@sint32 v1400@sint16;
(*   %mul.i.5.15 = mul nsw i32 %conv1.i.5.15, 1469 *)
mul v_mul_i_5_15 v_conv1_i_5_15 (1469)@sint32;
(*   %call.i.5.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_15, v_call_i_5_15);
(*   %arrayidx11.5.15 = getelementptr inbounds i16, i16* %r, i64 120 *)
(*   %1401 = load i16, i16* %arrayidx11.5.15, align 2, !tbaa !3 *)
mov v1401 mem0_240;
(*   %sub.5.15 = sub i16 %1401, %call.i.5.15 *)
sub v_sub_5_15 v1401 v_call_i_5_15;
(*   store i16 %sub.5.15, i16* %arrayidx9.5.15, align 2, !tbaa !3 *)
mov mem0_248 v_sub_5_15;
(*   %add21.5.15 = add i16 %1401, %call.i.5.15 *)
add v_add21_5_15 v1401 v_call_i_5_15;
(*   store i16 %add21.5.15, i16* %arrayidx11.5.15, align 2, !tbaa !3 *)
mov mem0_240 v_add21_5_15;
(*   %arrayidx9.5.1.15 = getelementptr inbounds i16, i16* %r, i64 125 *)
(*   %1402 = load i16, i16* %arrayidx9.5.1.15, align 2, !tbaa !3 *)
mov v1402 mem0_250;
(*   %conv1.i.5.1.15 = sext i16 %1402 to i32 *)
cast v_conv1_i_5_1_15@sint32 v1402@sint16;
(*   %mul.i.5.1.15 = mul nsw i32 %conv1.i.5.1.15, 1469 *)
mul v_mul_i_5_1_15 v_conv1_i_5_1_15 (1469)@sint32;
(*   %call.i.5.1.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_15, v_call_i_5_1_15);
(*   %arrayidx11.5.1.15 = getelementptr inbounds i16, i16* %r, i64 121 *)
(*   %1403 = load i16, i16* %arrayidx11.5.1.15, align 2, !tbaa !3 *)
mov v1403 mem0_242;
(*   %sub.5.1.15 = sub i16 %1403, %call.i.5.1.15 *)
sub v_sub_5_1_15 v1403 v_call_i_5_1_15;
(*   store i16 %sub.5.1.15, i16* %arrayidx9.5.1.15, align 2, !tbaa !3 *)
mov mem0_250 v_sub_5_1_15;
(*   %add21.5.1.15 = add i16 %1403, %call.i.5.1.15 *)
add v_add21_5_1_15 v1403 v_call_i_5_1_15;
(*   store i16 %add21.5.1.15, i16* %arrayidx11.5.1.15, align 2, !tbaa !3 *)
mov mem0_242 v_add21_5_1_15;
(*   %arrayidx9.5.2.15 = getelementptr inbounds i16, i16* %r, i64 126 *)
(*   %1404 = load i16, i16* %arrayidx9.5.2.15, align 2, !tbaa !3 *)
mov v1404 mem0_252;
(*   %conv1.i.5.2.15 = sext i16 %1404 to i32 *)
cast v_conv1_i_5_2_15@sint32 v1404@sint16;
(*   %mul.i.5.2.15 = mul nsw i32 %conv1.i.5.2.15, 1469 *)
mul v_mul_i_5_2_15 v_conv1_i_5_2_15 (1469)@sint32;
(*   %call.i.5.2.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_15, v_call_i_5_2_15);
(*   %arrayidx11.5.2.15 = getelementptr inbounds i16, i16* %r, i64 122 *)
(*   %1405 = load i16, i16* %arrayidx11.5.2.15, align 2, !tbaa !3 *)
mov v1405 mem0_244;
(*   %sub.5.2.15 = sub i16 %1405, %call.i.5.2.15 *)
sub v_sub_5_2_15 v1405 v_call_i_5_2_15;
(*   store i16 %sub.5.2.15, i16* %arrayidx9.5.2.15, align 2, !tbaa !3 *)
mov mem0_252 v_sub_5_2_15;
(*   %add21.5.2.15 = add i16 %1405, %call.i.5.2.15 *)
add v_add21_5_2_15 v1405 v_call_i_5_2_15;
(*   store i16 %add21.5.2.15, i16* %arrayidx11.5.2.15, align 2, !tbaa !3 *)
mov mem0_244 v_add21_5_2_15;
(*   %arrayidx9.5.3.15 = getelementptr inbounds i16, i16* %r, i64 127 *)
(*   %1406 = load i16, i16* %arrayidx9.5.3.15, align 2, !tbaa !3 *)
mov v1406 mem0_254;
(*   %conv1.i.5.3.15 = sext i16 %1406 to i32 *)
cast v_conv1_i_5_3_15@sint32 v1406@sint16;
(*   %mul.i.5.3.15 = mul nsw i32 %conv1.i.5.3.15, 1469 *)
mul v_mul_i_5_3_15 v_conv1_i_5_3_15 (1469)@sint32;
(*   %call.i.5.3.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_15, v_call_i_5_3_15);
(*   %arrayidx11.5.3.15 = getelementptr inbounds i16, i16* %r, i64 123 *)
(*   %1407 = load i16, i16* %arrayidx11.5.3.15, align 2, !tbaa !3 *)
mov v1407 mem0_246;
(*   %sub.5.3.15 = sub i16 %1407, %call.i.5.3.15 *)
sub v_sub_5_3_15 v1407 v_call_i_5_3_15;
(*   store i16 %sub.5.3.15, i16* %arrayidx9.5.3.15, align 2, !tbaa !3 *)
mov mem0_254 v_sub_5_3_15;
(*   %add21.5.3.15 = add i16 %1407, %call.i.5.3.15 *)
add v_add21_5_3_15 v1407 v_call_i_5_3_15;
(*   store i16 %add21.5.3.15, i16* %arrayidx11.5.3.15, align 2, !tbaa !3 *)
mov mem0_246 v_add21_5_3_15;

(* NOTE: k = 48 *)

(*   %arrayidx9.5.16 = getelementptr inbounds i16, i16* %r, i64 132 *)
(*   %1408 = load i16, i16* %arrayidx9.5.16, align 2, !tbaa !3 *)
mov v1408 mem0_264;
(*   %conv1.i.5.16 = sext i16 %1408 to i32 *)
cast v_conv1_i_5_16@sint32 v1408@sint16;
(*   %mul.i.5.16 = mul nsw i32 %conv1.i.5.16, -853 *)
mul v_mul_i_5_16 v_conv1_i_5_16 (-853)@sint32;
(*   %call.i.5.16 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.16) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_16, v_call_i_5_16);
(*   %arrayidx11.5.16 = getelementptr inbounds i16, i16* %r, i64 128 *)
(*   %1409 = load i16, i16* %arrayidx11.5.16, align 2, !tbaa !3 *)
mov v1409 mem0_256;
(*   %sub.5.16 = sub i16 %1409, %call.i.5.16 *)
sub v_sub_5_16 v1409 v_call_i_5_16;
(*   store i16 %sub.5.16, i16* %arrayidx9.5.16, align 2, !tbaa !3 *)
mov mem0_264 v_sub_5_16;
(*   %add21.5.16 = add i16 %1409, %call.i.5.16 *)
add v_add21_5_16 v1409 v_call_i_5_16;
(*   store i16 %add21.5.16, i16* %arrayidx11.5.16, align 2, !tbaa !3 *)
mov mem0_256 v_add21_5_16;
(*   %arrayidx9.5.1.16 = getelementptr inbounds i16, i16* %r, i64 133 *)
(*   %1410 = load i16, i16* %arrayidx9.5.1.16, align 2, !tbaa !3 *)
mov v1410 mem0_266;
(*   %conv1.i.5.1.16 = sext i16 %1410 to i32 *)
cast v_conv1_i_5_1_16@sint32 v1410@sint16;
(*   %mul.i.5.1.16 = mul nsw i32 %conv1.i.5.1.16, -853 *)
mul v_mul_i_5_1_16 v_conv1_i_5_1_16 (-853)@sint32;
(*   %call.i.5.1.16 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.16) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_16, v_call_i_5_1_16);
(*   %arrayidx11.5.1.16 = getelementptr inbounds i16, i16* %r, i64 129 *)
(*   %1411 = load i16, i16* %arrayidx11.5.1.16, align 2, !tbaa !3 *)
mov v1411 mem0_258;
(*   %sub.5.1.16 = sub i16 %1411, %call.i.5.1.16 *)
sub v_sub_5_1_16 v1411 v_call_i_5_1_16;
(*   store i16 %sub.5.1.16, i16* %arrayidx9.5.1.16, align 2, !tbaa !3 *)
mov mem0_266 v_sub_5_1_16;
(*   %add21.5.1.16 = add i16 %1411, %call.i.5.1.16 *)
add v_add21_5_1_16 v1411 v_call_i_5_1_16;
(*   store i16 %add21.5.1.16, i16* %arrayidx11.5.1.16, align 2, !tbaa !3 *)
mov mem0_258 v_add21_5_1_16;
(*   %arrayidx9.5.2.16 = getelementptr inbounds i16, i16* %r, i64 134 *)
(*   %1412 = load i16, i16* %arrayidx9.5.2.16, align 2, !tbaa !3 *)
mov v1412 mem0_268;
(*   %conv1.i.5.2.16 = sext i16 %1412 to i32 *)
cast v_conv1_i_5_2_16@sint32 v1412@sint16;
(*   %mul.i.5.2.16 = mul nsw i32 %conv1.i.5.2.16, -853 *)
mul v_mul_i_5_2_16 v_conv1_i_5_2_16 (-853)@sint32;
(*   %call.i.5.2.16 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.16) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_16, v_call_i_5_2_16);
(*   %arrayidx11.5.2.16 = getelementptr inbounds i16, i16* %r, i64 130 *)
(*   %1413 = load i16, i16* %arrayidx11.5.2.16, align 2, !tbaa !3 *)
mov v1413 mem0_260;
(*   %sub.5.2.16 = sub i16 %1413, %call.i.5.2.16 *)
sub v_sub_5_2_16 v1413 v_call_i_5_2_16;
(*   store i16 %sub.5.2.16, i16* %arrayidx9.5.2.16, align 2, !tbaa !3 *)
mov mem0_268 v_sub_5_2_16;
(*   %add21.5.2.16 = add i16 %1413, %call.i.5.2.16 *)
add v_add21_5_2_16 v1413 v_call_i_5_2_16;
(*   store i16 %add21.5.2.16, i16* %arrayidx11.5.2.16, align 2, !tbaa !3 *)
mov mem0_260 v_add21_5_2_16;
(*   %arrayidx9.5.3.16 = getelementptr inbounds i16, i16* %r, i64 135 *)
(*   %1414 = load i16, i16* %arrayidx9.5.3.16, align 2, !tbaa !3 *)
mov v1414 mem0_270;
(*   %conv1.i.5.3.16 = sext i16 %1414 to i32 *)
cast v_conv1_i_5_3_16@sint32 v1414@sint16;
(*   %mul.i.5.3.16 = mul nsw i32 %conv1.i.5.3.16, -853 *)
mul v_mul_i_5_3_16 v_conv1_i_5_3_16 (-853)@sint32;
(*   %call.i.5.3.16 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.16) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_16, v_call_i_5_3_16);
(*   %arrayidx11.5.3.16 = getelementptr inbounds i16, i16* %r, i64 131 *)
(*   %1415 = load i16, i16* %arrayidx11.5.3.16, align 2, !tbaa !3 *)
mov v1415 mem0_262;
(*   %sub.5.3.16 = sub i16 %1415, %call.i.5.3.16 *)
sub v_sub_5_3_16 v1415 v_call_i_5_3_16;
(*   store i16 %sub.5.3.16, i16* %arrayidx9.5.3.16, align 2, !tbaa !3 *)
mov mem0_270 v_sub_5_3_16;
(*   %add21.5.3.16 = add i16 %1415, %call.i.5.3.16 *)
add v_add21_5_3_16 v1415 v_call_i_5_3_16;
(*   store i16 %add21.5.3.16, i16* %arrayidx11.5.3.16, align 2, !tbaa !3 *)
mov mem0_262 v_add21_5_3_16;

(* NOTE: k = 49 *)

(*   %arrayidx9.5.17 = getelementptr inbounds i16, i16* %r, i64 140 *)
(*   %1416 = load i16, i16* %arrayidx9.5.17, align 2, !tbaa !3 *)
mov v1416 mem0_280;
(*   %conv1.i.5.17 = sext i16 %1416 to i32 *)
cast v_conv1_i_5_17@sint32 v1416@sint16;
(*   %mul.i.5.17 = mul nsw i32 %conv1.i.5.17, -90 *)
mul v_mul_i_5_17 v_conv1_i_5_17 (-90)@sint32;
(*   %call.i.5.17 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.17) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_17, v_call_i_5_17);
(*   %arrayidx11.5.17 = getelementptr inbounds i16, i16* %r, i64 136 *)
(*   %1417 = load i16, i16* %arrayidx11.5.17, align 2, !tbaa !3 *)
mov v1417 mem0_272;
(*   %sub.5.17 = sub i16 %1417, %call.i.5.17 *)
sub v_sub_5_17 v1417 v_call_i_5_17;
(*   store i16 %sub.5.17, i16* %arrayidx9.5.17, align 2, !tbaa !3 *)
mov mem0_280 v_sub_5_17;
(*   %add21.5.17 = add i16 %1417, %call.i.5.17 *)
add v_add21_5_17 v1417 v_call_i_5_17;
(*   store i16 %add21.5.17, i16* %arrayidx11.5.17, align 2, !tbaa !3 *)
mov mem0_272 v_add21_5_17;
(*   %arrayidx9.5.1.17 = getelementptr inbounds i16, i16* %r, i64 141 *)
(*   %1418 = load i16, i16* %arrayidx9.5.1.17, align 2, !tbaa !3 *)
mov v1418 mem0_282;
(*   %conv1.i.5.1.17 = sext i16 %1418 to i32 *)
cast v_conv1_i_5_1_17@sint32 v1418@sint16;
(*   %mul.i.5.1.17 = mul nsw i32 %conv1.i.5.1.17, -90 *)
mul v_mul_i_5_1_17 v_conv1_i_5_1_17 (-90)@sint32;
(*   %call.i.5.1.17 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.17) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_17, v_call_i_5_1_17);
(*   %arrayidx11.5.1.17 = getelementptr inbounds i16, i16* %r, i64 137 *)
(*   %1419 = load i16, i16* %arrayidx11.5.1.17, align 2, !tbaa !3 *)
mov v1419 mem0_274;
(*   %sub.5.1.17 = sub i16 %1419, %call.i.5.1.17 *)
sub v_sub_5_1_17 v1419 v_call_i_5_1_17;
(*   store i16 %sub.5.1.17, i16* %arrayidx9.5.1.17, align 2, !tbaa !3 *)
mov mem0_282 v_sub_5_1_17;
(*   %add21.5.1.17 = add i16 %1419, %call.i.5.1.17 *)
add v_add21_5_1_17 v1419 v_call_i_5_1_17;
(*   store i16 %add21.5.1.17, i16* %arrayidx11.5.1.17, align 2, !tbaa !3 *)
mov mem0_274 v_add21_5_1_17;
(*   %arrayidx9.5.2.17 = getelementptr inbounds i16, i16* %r, i64 142 *)
(*   %1420 = load i16, i16* %arrayidx9.5.2.17, align 2, !tbaa !3 *)
mov v1420 mem0_284;
(*   %conv1.i.5.2.17 = sext i16 %1420 to i32 *)
cast v_conv1_i_5_2_17@sint32 v1420@sint16;
(*   %mul.i.5.2.17 = mul nsw i32 %conv1.i.5.2.17, -90 *)
mul v_mul_i_5_2_17 v_conv1_i_5_2_17 (-90)@sint32;
(*   %call.i.5.2.17 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.17) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_17, v_call_i_5_2_17);
(*   %arrayidx11.5.2.17 = getelementptr inbounds i16, i16* %r, i64 138 *)
(*   %1421 = load i16, i16* %arrayidx11.5.2.17, align 2, !tbaa !3 *)
mov v1421 mem0_276;
(*   %sub.5.2.17 = sub i16 %1421, %call.i.5.2.17 *)
sub v_sub_5_2_17 v1421 v_call_i_5_2_17;
(*   store i16 %sub.5.2.17, i16* %arrayidx9.5.2.17, align 2, !tbaa !3 *)
mov mem0_284 v_sub_5_2_17;
(*   %add21.5.2.17 = add i16 %1421, %call.i.5.2.17 *)
add v_add21_5_2_17 v1421 v_call_i_5_2_17;
(*   store i16 %add21.5.2.17, i16* %arrayidx11.5.2.17, align 2, !tbaa !3 *)
mov mem0_276 v_add21_5_2_17;
(*   %arrayidx9.5.3.17 = getelementptr inbounds i16, i16* %r, i64 143 *)
(*   %1422 = load i16, i16* %arrayidx9.5.3.17, align 2, !tbaa !3 *)
mov v1422 mem0_286;
(*   %conv1.i.5.3.17 = sext i16 %1422 to i32 *)
cast v_conv1_i_5_3_17@sint32 v1422@sint16;
(*   %mul.i.5.3.17 = mul nsw i32 %conv1.i.5.3.17, -90 *)
mul v_mul_i_5_3_17 v_conv1_i_5_3_17 (-90)@sint32;
(*   %call.i.5.3.17 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.17) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_17, v_call_i_5_3_17);
(*   %arrayidx11.5.3.17 = getelementptr inbounds i16, i16* %r, i64 139 *)
(*   %1423 = load i16, i16* %arrayidx11.5.3.17, align 2, !tbaa !3 *)
mov v1423 mem0_278;
(*   %sub.5.3.17 = sub i16 %1423, %call.i.5.3.17 *)
sub v_sub_5_3_17 v1423 v_call_i_5_3_17;
(*   store i16 %sub.5.3.17, i16* %arrayidx9.5.3.17, align 2, !tbaa !3 *)
mov mem0_286 v_sub_5_3_17;
(*   %add21.5.3.17 = add i16 %1423, %call.i.5.3.17 *)
add v_add21_5_3_17 v1423 v_call_i_5_3_17;
(*   store i16 %add21.5.3.17, i16* %arrayidx11.5.3.17, align 2, !tbaa !3 *)
mov mem0_278 v_add21_5_3_17;

(* NOTE: k = 50 *)

(*   %arrayidx9.5.18 = getelementptr inbounds i16, i16* %r, i64 148 *)
(*   %1424 = load i16, i16* %arrayidx9.5.18, align 2, !tbaa !3 *)
mov v1424 mem0_296;
(*   %conv1.i.5.18 = sext i16 %1424 to i32 *)
cast v_conv1_i_5_18@sint32 v1424@sint16;
(*   %mul.i.5.18 = mul nsw i32 %conv1.i.5.18, -271 *)
mul v_mul_i_5_18 v_conv1_i_5_18 (-271)@sint32;
(*   %call.i.5.18 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.18) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_18, v_call_i_5_18);
(*   %arrayidx11.5.18 = getelementptr inbounds i16, i16* %r, i64 144 *)
(*   %1425 = load i16, i16* %arrayidx11.5.18, align 2, !tbaa !3 *)
mov v1425 mem0_288;
(*   %sub.5.18 = sub i16 %1425, %call.i.5.18 *)
sub v_sub_5_18 v1425 v_call_i_5_18;
(*   store i16 %sub.5.18, i16* %arrayidx9.5.18, align 2, !tbaa !3 *)
mov mem0_296 v_sub_5_18;
(*   %add21.5.18 = add i16 %1425, %call.i.5.18 *)
add v_add21_5_18 v1425 v_call_i_5_18;
(*   store i16 %add21.5.18, i16* %arrayidx11.5.18, align 2, !tbaa !3 *)
mov mem0_288 v_add21_5_18;
(*   %arrayidx9.5.1.18 = getelementptr inbounds i16, i16* %r, i64 149 *)
(*   %1426 = load i16, i16* %arrayidx9.5.1.18, align 2, !tbaa !3 *)
mov v1426 mem0_298;
(*   %conv1.i.5.1.18 = sext i16 %1426 to i32 *)
cast v_conv1_i_5_1_18@sint32 v1426@sint16;
(*   %mul.i.5.1.18 = mul nsw i32 %conv1.i.5.1.18, -271 *)
mul v_mul_i_5_1_18 v_conv1_i_5_1_18 (-271)@sint32;
(*   %call.i.5.1.18 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.18) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_18, v_call_i_5_1_18);
(*   %arrayidx11.5.1.18 = getelementptr inbounds i16, i16* %r, i64 145 *)
(*   %1427 = load i16, i16* %arrayidx11.5.1.18, align 2, !tbaa !3 *)
mov v1427 mem0_290;
(*   %sub.5.1.18 = sub i16 %1427, %call.i.5.1.18 *)
sub v_sub_5_1_18 v1427 v_call_i_5_1_18;
(*   store i16 %sub.5.1.18, i16* %arrayidx9.5.1.18, align 2, !tbaa !3 *)
mov mem0_298 v_sub_5_1_18;
(*   %add21.5.1.18 = add i16 %1427, %call.i.5.1.18 *)
add v_add21_5_1_18 v1427 v_call_i_5_1_18;
(*   store i16 %add21.5.1.18, i16* %arrayidx11.5.1.18, align 2, !tbaa !3 *)
mov mem0_290 v_add21_5_1_18;
(*   %arrayidx9.5.2.18 = getelementptr inbounds i16, i16* %r, i64 150 *)
(*   %1428 = load i16, i16* %arrayidx9.5.2.18, align 2, !tbaa !3 *)
mov v1428 mem0_300;
(*   %conv1.i.5.2.18 = sext i16 %1428 to i32 *)
cast v_conv1_i_5_2_18@sint32 v1428@sint16;
(*   %mul.i.5.2.18 = mul nsw i32 %conv1.i.5.2.18, -271 *)
mul v_mul_i_5_2_18 v_conv1_i_5_2_18 (-271)@sint32;
(*   %call.i.5.2.18 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.18) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_18, v_call_i_5_2_18);
(*   %arrayidx11.5.2.18 = getelementptr inbounds i16, i16* %r, i64 146 *)
(*   %1429 = load i16, i16* %arrayidx11.5.2.18, align 2, !tbaa !3 *)
mov v1429 mem0_292;
(*   %sub.5.2.18 = sub i16 %1429, %call.i.5.2.18 *)
sub v_sub_5_2_18 v1429 v_call_i_5_2_18;
(*   store i16 %sub.5.2.18, i16* %arrayidx9.5.2.18, align 2, !tbaa !3 *)
mov mem0_300 v_sub_5_2_18;
(*   %add21.5.2.18 = add i16 %1429, %call.i.5.2.18 *)
add v_add21_5_2_18 v1429 v_call_i_5_2_18;
(*   store i16 %add21.5.2.18, i16* %arrayidx11.5.2.18, align 2, !tbaa !3 *)
mov mem0_292 v_add21_5_2_18;
(*   %arrayidx9.5.3.18 = getelementptr inbounds i16, i16* %r, i64 151 *)
(*   %1430 = load i16, i16* %arrayidx9.5.3.18, align 2, !tbaa !3 *)
mov v1430 mem0_302;
(*   %conv1.i.5.3.18 = sext i16 %1430 to i32 *)
cast v_conv1_i_5_3_18@sint32 v1430@sint16;
(*   %mul.i.5.3.18 = mul nsw i32 %conv1.i.5.3.18, -271 *)
mul v_mul_i_5_3_18 v_conv1_i_5_3_18 (-271)@sint32;
(*   %call.i.5.3.18 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.18) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_18, v_call_i_5_3_18);
(*   %arrayidx11.5.3.18 = getelementptr inbounds i16, i16* %r, i64 147 *)
(*   %1431 = load i16, i16* %arrayidx11.5.3.18, align 2, !tbaa !3 *)
mov v1431 mem0_294;
(*   %sub.5.3.18 = sub i16 %1431, %call.i.5.3.18 *)
sub v_sub_5_3_18 v1431 v_call_i_5_3_18;
(*   store i16 %sub.5.3.18, i16* %arrayidx9.5.3.18, align 2, !tbaa !3 *)
mov mem0_302 v_sub_5_3_18;
(*   %add21.5.3.18 = add i16 %1431, %call.i.5.3.18 *)
add v_add21_5_3_18 v1431 v_call_i_5_3_18;
(*   store i16 %add21.5.3.18, i16* %arrayidx11.5.3.18, align 2, !tbaa !3 *)
mov mem0_294 v_add21_5_3_18;

(* NOTE: k = 51 *)

(*   %arrayidx9.5.19 = getelementptr inbounds i16, i16* %r, i64 156 *)
(*   %1432 = load i16, i16* %arrayidx9.5.19, align 2, !tbaa !3 *)
mov v1432 mem0_312;
(*   %conv1.i.5.19 = sext i16 %1432 to i32 *)
cast v_conv1_i_5_19@sint32 v1432@sint16;
(*   %mul.i.5.19 = mul nsw i32 %conv1.i.5.19, 830 *)
mul v_mul_i_5_19 v_conv1_i_5_19 (830)@sint32;
(*   %call.i.5.19 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.19) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_19, v_call_i_5_19);
(*   %arrayidx11.5.19 = getelementptr inbounds i16, i16* %r, i64 152 *)
(*   %1433 = load i16, i16* %arrayidx11.5.19, align 2, !tbaa !3 *)
mov v1433 mem0_304;
(*   %sub.5.19 = sub i16 %1433, %call.i.5.19 *)
sub v_sub_5_19 v1433 v_call_i_5_19;
(*   store i16 %sub.5.19, i16* %arrayidx9.5.19, align 2, !tbaa !3 *)
mov mem0_312 v_sub_5_19;
(*   %add21.5.19 = add i16 %1433, %call.i.5.19 *)
add v_add21_5_19 v1433 v_call_i_5_19;
(*   store i16 %add21.5.19, i16* %arrayidx11.5.19, align 2, !tbaa !3 *)
mov mem0_304 v_add21_5_19;
(*   %arrayidx9.5.1.19 = getelementptr inbounds i16, i16* %r, i64 157 *)
(*   %1434 = load i16, i16* %arrayidx9.5.1.19, align 2, !tbaa !3 *)
mov v1434 mem0_314;
(*   %conv1.i.5.1.19 = sext i16 %1434 to i32 *)
cast v_conv1_i_5_1_19@sint32 v1434@sint16;
(*   %mul.i.5.1.19 = mul nsw i32 %conv1.i.5.1.19, 830 *)
mul v_mul_i_5_1_19 v_conv1_i_5_1_19 (830)@sint32;
(*   %call.i.5.1.19 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.19) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_19, v_call_i_5_1_19);
(*   %arrayidx11.5.1.19 = getelementptr inbounds i16, i16* %r, i64 153 *)
(*   %1435 = load i16, i16* %arrayidx11.5.1.19, align 2, !tbaa !3 *)
mov v1435 mem0_306;
(*   %sub.5.1.19 = sub i16 %1435, %call.i.5.1.19 *)
sub v_sub_5_1_19 v1435 v_call_i_5_1_19;
(*   store i16 %sub.5.1.19, i16* %arrayidx9.5.1.19, align 2, !tbaa !3 *)
mov mem0_314 v_sub_5_1_19;
(*   %add21.5.1.19 = add i16 %1435, %call.i.5.1.19 *)
add v_add21_5_1_19 v1435 v_call_i_5_1_19;
(*   store i16 %add21.5.1.19, i16* %arrayidx11.5.1.19, align 2, !tbaa !3 *)
mov mem0_306 v_add21_5_1_19;
(*   %arrayidx9.5.2.19 = getelementptr inbounds i16, i16* %r, i64 158 *)
(*   %1436 = load i16, i16* %arrayidx9.5.2.19, align 2, !tbaa !3 *)
mov v1436 mem0_316;
(*   %conv1.i.5.2.19 = sext i16 %1436 to i32 *)
cast v_conv1_i_5_2_19@sint32 v1436@sint16;
(*   %mul.i.5.2.19 = mul nsw i32 %conv1.i.5.2.19, 830 *)
mul v_mul_i_5_2_19 v_conv1_i_5_2_19 (830)@sint32;
(*   %call.i.5.2.19 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.19) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_19, v_call_i_5_2_19);
(*   %arrayidx11.5.2.19 = getelementptr inbounds i16, i16* %r, i64 154 *)
(*   %1437 = load i16, i16* %arrayidx11.5.2.19, align 2, !tbaa !3 *)
mov v1437 mem0_308;
(*   %sub.5.2.19 = sub i16 %1437, %call.i.5.2.19 *)
sub v_sub_5_2_19 v1437 v_call_i_5_2_19;
(*   store i16 %sub.5.2.19, i16* %arrayidx9.5.2.19, align 2, !tbaa !3 *)
mov mem0_316 v_sub_5_2_19;
(*   %add21.5.2.19 = add i16 %1437, %call.i.5.2.19 *)
add v_add21_5_2_19 v1437 v_call_i_5_2_19;
(*   store i16 %add21.5.2.19, i16* %arrayidx11.5.2.19, align 2, !tbaa !3 *)
mov mem0_308 v_add21_5_2_19;
(*   %arrayidx9.5.3.19 = getelementptr inbounds i16, i16* %r, i64 159 *)
(*   %1438 = load i16, i16* %arrayidx9.5.3.19, align 2, !tbaa !3 *)
mov v1438 mem0_318;
(*   %conv1.i.5.3.19 = sext i16 %1438 to i32 *)
cast v_conv1_i_5_3_19@sint32 v1438@sint16;
(*   %mul.i.5.3.19 = mul nsw i32 %conv1.i.5.3.19, 830 *)
mul v_mul_i_5_3_19 v_conv1_i_5_3_19 (830)@sint32;
(*   %call.i.5.3.19 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.19) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_19, v_call_i_5_3_19);
(*   %arrayidx11.5.3.19 = getelementptr inbounds i16, i16* %r, i64 155 *)
(*   %1439 = load i16, i16* %arrayidx11.5.3.19, align 2, !tbaa !3 *)
mov v1439 mem0_310;
(*   %sub.5.3.19 = sub i16 %1439, %call.i.5.3.19 *)
sub v_sub_5_3_19 v1439 v_call_i_5_3_19;
(*   store i16 %sub.5.3.19, i16* %arrayidx9.5.3.19, align 2, !tbaa !3 *)
mov mem0_318 v_sub_5_3_19;
(*   %add21.5.3.19 = add i16 %1439, %call.i.5.3.19 *)
add v_add21_5_3_19 v1439 v_call_i_5_3_19;
(*   store i16 %add21.5.3.19, i16* %arrayidx11.5.3.19, align 2, !tbaa !3 *)
mov mem0_310 v_add21_5_3_19;

(* NOTE: k = 52 *)

(*   %arrayidx9.5.20 = getelementptr inbounds i16, i16* %r, i64 164 *)
(*   %1440 = load i16, i16* %arrayidx9.5.20, align 2, !tbaa !3 *)
mov v1440 mem0_328;
(*   %conv1.i.5.20 = sext i16 %1440 to i32 *)
cast v_conv1_i_5_20@sint32 v1440@sint16;
(*   %mul.i.5.20 = mul nsw i32 %conv1.i.5.20, 107 *)
mul v_mul_i_5_20 v_conv1_i_5_20 (107)@sint32;
(*   %call.i.5.20 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.20) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_20, v_call_i_5_20);
(*   %arrayidx11.5.20 = getelementptr inbounds i16, i16* %r, i64 160 *)
(*   %1441 = load i16, i16* %arrayidx11.5.20, align 2, !tbaa !3 *)
mov v1441 mem0_320;
(*   %sub.5.20 = sub i16 %1441, %call.i.5.20 *)
sub v_sub_5_20 v1441 v_call_i_5_20;
(*   store i16 %sub.5.20, i16* %arrayidx9.5.20, align 2, !tbaa !3 *)
mov mem0_328 v_sub_5_20;
(*   %add21.5.20 = add i16 %1441, %call.i.5.20 *)
add v_add21_5_20 v1441 v_call_i_5_20;
(*   store i16 %add21.5.20, i16* %arrayidx11.5.20, align 2, !tbaa !3 *)
mov mem0_320 v_add21_5_20;
(*   %arrayidx9.5.1.20 = getelementptr inbounds i16, i16* %r, i64 165 *)
(*   %1442 = load i16, i16* %arrayidx9.5.1.20, align 2, !tbaa !3 *)
mov v1442 mem0_330;
(*   %conv1.i.5.1.20 = sext i16 %1442 to i32 *)
cast v_conv1_i_5_1_20@sint32 v1442@sint16;
(*   %mul.i.5.1.20 = mul nsw i32 %conv1.i.5.1.20, 107 *)
mul v_mul_i_5_1_20 v_conv1_i_5_1_20 (107)@sint32;
(*   %call.i.5.1.20 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.20) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_20, v_call_i_5_1_20);
(*   %arrayidx11.5.1.20 = getelementptr inbounds i16, i16* %r, i64 161 *)
(*   %1443 = load i16, i16* %arrayidx11.5.1.20, align 2, !tbaa !3 *)
mov v1443 mem0_322;
(*   %sub.5.1.20 = sub i16 %1443, %call.i.5.1.20 *)
sub v_sub_5_1_20 v1443 v_call_i_5_1_20;
(*   store i16 %sub.5.1.20, i16* %arrayidx9.5.1.20, align 2, !tbaa !3 *)
mov mem0_330 v_sub_5_1_20;
(*   %add21.5.1.20 = add i16 %1443, %call.i.5.1.20 *)
add v_add21_5_1_20 v1443 v_call_i_5_1_20;
(*   store i16 %add21.5.1.20, i16* %arrayidx11.5.1.20, align 2, !tbaa !3 *)
mov mem0_322 v_add21_5_1_20;
(*   %arrayidx9.5.2.20 = getelementptr inbounds i16, i16* %r, i64 166 *)
(*   %1444 = load i16, i16* %arrayidx9.5.2.20, align 2, !tbaa !3 *)
mov v1444 mem0_332;
(*   %conv1.i.5.2.20 = sext i16 %1444 to i32 *)
cast v_conv1_i_5_2_20@sint32 v1444@sint16;
(*   %mul.i.5.2.20 = mul nsw i32 %conv1.i.5.2.20, 107 *)
mul v_mul_i_5_2_20 v_conv1_i_5_2_20 (107)@sint32;
(*   %call.i.5.2.20 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.20) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_20, v_call_i_5_2_20);
(*   %arrayidx11.5.2.20 = getelementptr inbounds i16, i16* %r, i64 162 *)
(*   %1445 = load i16, i16* %arrayidx11.5.2.20, align 2, !tbaa !3 *)
mov v1445 mem0_324;
(*   %sub.5.2.20 = sub i16 %1445, %call.i.5.2.20 *)
sub v_sub_5_2_20 v1445 v_call_i_5_2_20;
(*   store i16 %sub.5.2.20, i16* %arrayidx9.5.2.20, align 2, !tbaa !3 *)
mov mem0_332 v_sub_5_2_20;
(*   %add21.5.2.20 = add i16 %1445, %call.i.5.2.20 *)
add v_add21_5_2_20 v1445 v_call_i_5_2_20;
(*   store i16 %add21.5.2.20, i16* %arrayidx11.5.2.20, align 2, !tbaa !3 *)
mov mem0_324 v_add21_5_2_20;
(*   %arrayidx9.5.3.20 = getelementptr inbounds i16, i16* %r, i64 167 *)
(*   %1446 = load i16, i16* %arrayidx9.5.3.20, align 2, !tbaa !3 *)
mov v1446 mem0_334;
(*   %conv1.i.5.3.20 = sext i16 %1446 to i32 *)
cast v_conv1_i_5_3_20@sint32 v1446@sint16;
(*   %mul.i.5.3.20 = mul nsw i32 %conv1.i.5.3.20, 107 *)
mul v_mul_i_5_3_20 v_conv1_i_5_3_20 (107)@sint32;
(*   %call.i.5.3.20 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.20) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_20, v_call_i_5_3_20);
(*   %arrayidx11.5.3.20 = getelementptr inbounds i16, i16* %r, i64 163 *)
(*   %1447 = load i16, i16* %arrayidx11.5.3.20, align 2, !tbaa !3 *)
mov v1447 mem0_326;
(*   %sub.5.3.20 = sub i16 %1447, %call.i.5.3.20 *)
sub v_sub_5_3_20 v1447 v_call_i_5_3_20;
(*   store i16 %sub.5.3.20, i16* %arrayidx9.5.3.20, align 2, !tbaa !3 *)
mov mem0_334 v_sub_5_3_20;
(*   %add21.5.3.20 = add i16 %1447, %call.i.5.3.20 *)
add v_add21_5_3_20 v1447 v_call_i_5_3_20;
(*   store i16 %add21.5.3.20, i16* %arrayidx11.5.3.20, align 2, !tbaa !3 *)
mov mem0_326 v_add21_5_3_20;

(* NOTE: k = 53 *)

(*   %arrayidx9.5.21 = getelementptr inbounds i16, i16* %r, i64 172 *)
(*   %1448 = load i16, i16* %arrayidx9.5.21, align 2, !tbaa !3 *)
mov v1448 mem0_344;
(*   %conv1.i.5.21 = sext i16 %1448 to i32 *)
cast v_conv1_i_5_21@sint32 v1448@sint16;
(*   %mul.i.5.21 = mul nsw i32 %conv1.i.5.21, -1421 *)
mul v_mul_i_5_21 v_conv1_i_5_21 (-1421)@sint32;
(*   %call.i.5.21 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.21) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_21, v_call_i_5_21);
(*   %arrayidx11.5.21 = getelementptr inbounds i16, i16* %r, i64 168 *)
(*   %1449 = load i16, i16* %arrayidx11.5.21, align 2, !tbaa !3 *)
mov v1449 mem0_336;
(*   %sub.5.21 = sub i16 %1449, %call.i.5.21 *)
sub v_sub_5_21 v1449 v_call_i_5_21;
(*   store i16 %sub.5.21, i16* %arrayidx9.5.21, align 2, !tbaa !3 *)
mov mem0_344 v_sub_5_21;
(*   %add21.5.21 = add i16 %1449, %call.i.5.21 *)
add v_add21_5_21 v1449 v_call_i_5_21;
(*   store i16 %add21.5.21, i16* %arrayidx11.5.21, align 2, !tbaa !3 *)
mov mem0_336 v_add21_5_21;
(*   %arrayidx9.5.1.21 = getelementptr inbounds i16, i16* %r, i64 173 *)
(*   %1450 = load i16, i16* %arrayidx9.5.1.21, align 2, !tbaa !3 *)
mov v1450 mem0_346;
(*   %conv1.i.5.1.21 = sext i16 %1450 to i32 *)
cast v_conv1_i_5_1_21@sint32 v1450@sint16;
(*   %mul.i.5.1.21 = mul nsw i32 %conv1.i.5.1.21, -1421 *)
mul v_mul_i_5_1_21 v_conv1_i_5_1_21 (-1421)@sint32;
(*   %call.i.5.1.21 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.21) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_21, v_call_i_5_1_21);
(*   %arrayidx11.5.1.21 = getelementptr inbounds i16, i16* %r, i64 169 *)
(*   %1451 = load i16, i16* %arrayidx11.5.1.21, align 2, !tbaa !3 *)
mov v1451 mem0_338;
(*   %sub.5.1.21 = sub i16 %1451, %call.i.5.1.21 *)
sub v_sub_5_1_21 v1451 v_call_i_5_1_21;
(*   store i16 %sub.5.1.21, i16* %arrayidx9.5.1.21, align 2, !tbaa !3 *)
mov mem0_346 v_sub_5_1_21;
(*   %add21.5.1.21 = add i16 %1451, %call.i.5.1.21 *)
add v_add21_5_1_21 v1451 v_call_i_5_1_21;
(*   store i16 %add21.5.1.21, i16* %arrayidx11.5.1.21, align 2, !tbaa !3 *)
mov mem0_338 v_add21_5_1_21;
(*   %arrayidx9.5.2.21 = getelementptr inbounds i16, i16* %r, i64 174 *)
(*   %1452 = load i16, i16* %arrayidx9.5.2.21, align 2, !tbaa !3 *)
mov v1452 mem0_348;
(*   %conv1.i.5.2.21 = sext i16 %1452 to i32 *)
cast v_conv1_i_5_2_21@sint32 v1452@sint16;
(*   %mul.i.5.2.21 = mul nsw i32 %conv1.i.5.2.21, -1421 *)
mul v_mul_i_5_2_21 v_conv1_i_5_2_21 (-1421)@sint32;
(*   %call.i.5.2.21 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.21) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_21, v_call_i_5_2_21);
(*   %arrayidx11.5.2.21 = getelementptr inbounds i16, i16* %r, i64 170 *)
(*   %1453 = load i16, i16* %arrayidx11.5.2.21, align 2, !tbaa !3 *)
mov v1453 mem0_340;
(*   %sub.5.2.21 = sub i16 %1453, %call.i.5.2.21 *)
sub v_sub_5_2_21 v1453 v_call_i_5_2_21;
(*   store i16 %sub.5.2.21, i16* %arrayidx9.5.2.21, align 2, !tbaa !3 *)
mov mem0_348 v_sub_5_2_21;
(*   %add21.5.2.21 = add i16 %1453, %call.i.5.2.21 *)
add v_add21_5_2_21 v1453 v_call_i_5_2_21;
(*   store i16 %add21.5.2.21, i16* %arrayidx11.5.2.21, align 2, !tbaa !3 *)
mov mem0_340 v_add21_5_2_21;
(*   %arrayidx9.5.3.21 = getelementptr inbounds i16, i16* %r, i64 175 *)
(*   %1454 = load i16, i16* %arrayidx9.5.3.21, align 2, !tbaa !3 *)
mov v1454 mem0_350;
(*   %conv1.i.5.3.21 = sext i16 %1454 to i32 *)
cast v_conv1_i_5_3_21@sint32 v1454@sint16;
(*   %mul.i.5.3.21 = mul nsw i32 %conv1.i.5.3.21, -1421 *)
mul v_mul_i_5_3_21 v_conv1_i_5_3_21 (-1421)@sint32;
(*   %call.i.5.3.21 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.21) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_21, v_call_i_5_3_21);
(*   %arrayidx11.5.3.21 = getelementptr inbounds i16, i16* %r, i64 171 *)
(*   %1455 = load i16, i16* %arrayidx11.5.3.21, align 2, !tbaa !3 *)
mov v1455 mem0_342;
(*   %sub.5.3.21 = sub i16 %1455, %call.i.5.3.21 *)
sub v_sub_5_3_21 v1455 v_call_i_5_3_21;
(*   store i16 %sub.5.3.21, i16* %arrayidx9.5.3.21, align 2, !tbaa !3 *)
mov mem0_350 v_sub_5_3_21;
(*   %add21.5.3.21 = add i16 %1455, %call.i.5.3.21 *)
add v_add21_5_3_21 v1455 v_call_i_5_3_21;
(*   store i16 %add21.5.3.21, i16* %arrayidx11.5.3.21, align 2, !tbaa !3 *)
mov mem0_342 v_add21_5_3_21;

(* NOTE: k = 54 *)

(*   %arrayidx9.5.22 = getelementptr inbounds i16, i16* %r, i64 180 *)
(*   %1456 = load i16, i16* %arrayidx9.5.22, align 2, !tbaa !3 *)
mov v1456 mem0_360;
(*   %conv1.i.5.22 = sext i16 %1456 to i32 *)
cast v_conv1_i_5_22@sint32 v1456@sint16;
(*   %mul.i.5.22 = mul nsw i32 %conv1.i.5.22, -247 *)
mul v_mul_i_5_22 v_conv1_i_5_22 (-247)@sint32;
(*   %call.i.5.22 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.22) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_22, v_call_i_5_22);
(*   %arrayidx11.5.22 = getelementptr inbounds i16, i16* %r, i64 176 *)
(*   %1457 = load i16, i16* %arrayidx11.5.22, align 2, !tbaa !3 *)
mov v1457 mem0_352;
(*   %sub.5.22 = sub i16 %1457, %call.i.5.22 *)
sub v_sub_5_22 v1457 v_call_i_5_22;
(*   store i16 %sub.5.22, i16* %arrayidx9.5.22, align 2, !tbaa !3 *)
mov mem0_360 v_sub_5_22;
(*   %add21.5.22 = add i16 %1457, %call.i.5.22 *)
add v_add21_5_22 v1457 v_call_i_5_22;
(*   store i16 %add21.5.22, i16* %arrayidx11.5.22, align 2, !tbaa !3 *)
mov mem0_352 v_add21_5_22;
(*   %arrayidx9.5.1.22 = getelementptr inbounds i16, i16* %r, i64 181 *)
(*   %1458 = load i16, i16* %arrayidx9.5.1.22, align 2, !tbaa !3 *)
mov v1458 mem0_362;
(*   %conv1.i.5.1.22 = sext i16 %1458 to i32 *)
cast v_conv1_i_5_1_22@sint32 v1458@sint16;
(*   %mul.i.5.1.22 = mul nsw i32 %conv1.i.5.1.22, -247 *)
mul v_mul_i_5_1_22 v_conv1_i_5_1_22 (-247)@sint32;
(*   %call.i.5.1.22 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.22) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_22, v_call_i_5_1_22);
(*   %arrayidx11.5.1.22 = getelementptr inbounds i16, i16* %r, i64 177 *)
(*   %1459 = load i16, i16* %arrayidx11.5.1.22, align 2, !tbaa !3 *)
mov v1459 mem0_354;
(*   %sub.5.1.22 = sub i16 %1459, %call.i.5.1.22 *)
sub v_sub_5_1_22 v1459 v_call_i_5_1_22;
(*   store i16 %sub.5.1.22, i16* %arrayidx9.5.1.22, align 2, !tbaa !3 *)
mov mem0_362 v_sub_5_1_22;
(*   %add21.5.1.22 = add i16 %1459, %call.i.5.1.22 *)
add v_add21_5_1_22 v1459 v_call_i_5_1_22;
(*   store i16 %add21.5.1.22, i16* %arrayidx11.5.1.22, align 2, !tbaa !3 *)
mov mem0_354 v_add21_5_1_22;
(*   %arrayidx9.5.2.22 = getelementptr inbounds i16, i16* %r, i64 182 *)
(*   %1460 = load i16, i16* %arrayidx9.5.2.22, align 2, !tbaa !3 *)
mov v1460 mem0_364;
(*   %conv1.i.5.2.22 = sext i16 %1460 to i32 *)
cast v_conv1_i_5_2_22@sint32 v1460@sint16;
(*   %mul.i.5.2.22 = mul nsw i32 %conv1.i.5.2.22, -247 *)
mul v_mul_i_5_2_22 v_conv1_i_5_2_22 (-247)@sint32;
(*   %call.i.5.2.22 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.22) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_22, v_call_i_5_2_22);
(*   %arrayidx11.5.2.22 = getelementptr inbounds i16, i16* %r, i64 178 *)
(*   %1461 = load i16, i16* %arrayidx11.5.2.22, align 2, !tbaa !3 *)
mov v1461 mem0_356;
(*   %sub.5.2.22 = sub i16 %1461, %call.i.5.2.22 *)
sub v_sub_5_2_22 v1461 v_call_i_5_2_22;
(*   store i16 %sub.5.2.22, i16* %arrayidx9.5.2.22, align 2, !tbaa !3 *)
mov mem0_364 v_sub_5_2_22;
(*   %add21.5.2.22 = add i16 %1461, %call.i.5.2.22 *)
add v_add21_5_2_22 v1461 v_call_i_5_2_22;
(*   store i16 %add21.5.2.22, i16* %arrayidx11.5.2.22, align 2, !tbaa !3 *)
mov mem0_356 v_add21_5_2_22;
(*   %arrayidx9.5.3.22 = getelementptr inbounds i16, i16* %r, i64 183 *)
(*   %1462 = load i16, i16* %arrayidx9.5.3.22, align 2, !tbaa !3 *)
mov v1462 mem0_366;
(*   %conv1.i.5.3.22 = sext i16 %1462 to i32 *)
cast v_conv1_i_5_3_22@sint32 v1462@sint16;
(*   %mul.i.5.3.22 = mul nsw i32 %conv1.i.5.3.22, -247 *)
mul v_mul_i_5_3_22 v_conv1_i_5_3_22 (-247)@sint32;
(*   %call.i.5.3.22 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.22) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_22, v_call_i_5_3_22);
(*   %arrayidx11.5.3.22 = getelementptr inbounds i16, i16* %r, i64 179 *)
(*   %1463 = load i16, i16* %arrayidx11.5.3.22, align 2, !tbaa !3 *)
mov v1463 mem0_358;
(*   %sub.5.3.22 = sub i16 %1463, %call.i.5.3.22 *)
sub v_sub_5_3_22 v1463 v_call_i_5_3_22;
(*   store i16 %sub.5.3.22, i16* %arrayidx9.5.3.22, align 2, !tbaa !3 *)
mov mem0_366 v_sub_5_3_22;
(*   %add21.5.3.22 = add i16 %1463, %call.i.5.3.22 *)
add v_add21_5_3_22 v1463 v_call_i_5_3_22;
(*   store i16 %add21.5.3.22, i16* %arrayidx11.5.3.22, align 2, !tbaa !3 *)
mov mem0_358 v_add21_5_3_22;

(* NOTE: k = 55 *)

(*   %arrayidx9.5.23 = getelementptr inbounds i16, i16* %r, i64 188 *)
(*   %1464 = load i16, i16* %arrayidx9.5.23, align 2, !tbaa !3 *)
mov v1464 mem0_376;
(*   %conv1.i.5.23 = sext i16 %1464 to i32 *)
cast v_conv1_i_5_23@sint32 v1464@sint16;
(*   %mul.i.5.23 = mul nsw i32 %conv1.i.5.23, -951 *)
mul v_mul_i_5_23 v_conv1_i_5_23 (-951)@sint32;
(*   %call.i.5.23 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.23) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_23, v_call_i_5_23);
(*   %arrayidx11.5.23 = getelementptr inbounds i16, i16* %r, i64 184 *)
(*   %1465 = load i16, i16* %arrayidx11.5.23, align 2, !tbaa !3 *)
mov v1465 mem0_368;
(*   %sub.5.23 = sub i16 %1465, %call.i.5.23 *)
sub v_sub_5_23 v1465 v_call_i_5_23;
(*   store i16 %sub.5.23, i16* %arrayidx9.5.23, align 2, !tbaa !3 *)
mov mem0_376 v_sub_5_23;
(*   %add21.5.23 = add i16 %1465, %call.i.5.23 *)
add v_add21_5_23 v1465 v_call_i_5_23;
(*   store i16 %add21.5.23, i16* %arrayidx11.5.23, align 2, !tbaa !3 *)
mov mem0_368 v_add21_5_23;
(*   %arrayidx9.5.1.23 = getelementptr inbounds i16, i16* %r, i64 189 *)
(*   %1466 = load i16, i16* %arrayidx9.5.1.23, align 2, !tbaa !3 *)
mov v1466 mem0_378;
(*   %conv1.i.5.1.23 = sext i16 %1466 to i32 *)
cast v_conv1_i_5_1_23@sint32 v1466@sint16;
(*   %mul.i.5.1.23 = mul nsw i32 %conv1.i.5.1.23, -951 *)
mul v_mul_i_5_1_23 v_conv1_i_5_1_23 (-951)@sint32;
(*   %call.i.5.1.23 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.23) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_23, v_call_i_5_1_23);
(*   %arrayidx11.5.1.23 = getelementptr inbounds i16, i16* %r, i64 185 *)
(*   %1467 = load i16, i16* %arrayidx11.5.1.23, align 2, !tbaa !3 *)
mov v1467 mem0_370;
(*   %sub.5.1.23 = sub i16 %1467, %call.i.5.1.23 *)
sub v_sub_5_1_23 v1467 v_call_i_5_1_23;
(*   store i16 %sub.5.1.23, i16* %arrayidx9.5.1.23, align 2, !tbaa !3 *)
mov mem0_378 v_sub_5_1_23;
(*   %add21.5.1.23 = add i16 %1467, %call.i.5.1.23 *)
add v_add21_5_1_23 v1467 v_call_i_5_1_23;
(*   store i16 %add21.5.1.23, i16* %arrayidx11.5.1.23, align 2, !tbaa !3 *)
mov mem0_370 v_add21_5_1_23;
(*   %arrayidx9.5.2.23 = getelementptr inbounds i16, i16* %r, i64 190 *)
(*   %1468 = load i16, i16* %arrayidx9.5.2.23, align 2, !tbaa !3 *)
mov v1468 mem0_380;
(*   %conv1.i.5.2.23 = sext i16 %1468 to i32 *)
cast v_conv1_i_5_2_23@sint32 v1468@sint16;
(*   %mul.i.5.2.23 = mul nsw i32 %conv1.i.5.2.23, -951 *)
mul v_mul_i_5_2_23 v_conv1_i_5_2_23 (-951)@sint32;
(*   %call.i.5.2.23 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.23) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_23, v_call_i_5_2_23);
(*   %arrayidx11.5.2.23 = getelementptr inbounds i16, i16* %r, i64 186 *)
(*   %1469 = load i16, i16* %arrayidx11.5.2.23, align 2, !tbaa !3 *)
mov v1469 mem0_372;
(*   %sub.5.2.23 = sub i16 %1469, %call.i.5.2.23 *)
sub v_sub_5_2_23 v1469 v_call_i_5_2_23;
(*   store i16 %sub.5.2.23, i16* %arrayidx9.5.2.23, align 2, !tbaa !3 *)
mov mem0_380 v_sub_5_2_23;
(*   %add21.5.2.23 = add i16 %1469, %call.i.5.2.23 *)
add v_add21_5_2_23 v1469 v_call_i_5_2_23;
(*   store i16 %add21.5.2.23, i16* %arrayidx11.5.2.23, align 2, !tbaa !3 *)
mov mem0_372 v_add21_5_2_23;
(*   %arrayidx9.5.3.23 = getelementptr inbounds i16, i16* %r, i64 191 *)
(*   %1470 = load i16, i16* %arrayidx9.5.3.23, align 2, !tbaa !3 *)
mov v1470 mem0_382;
(*   %conv1.i.5.3.23 = sext i16 %1470 to i32 *)
cast v_conv1_i_5_3_23@sint32 v1470@sint16;
(*   %mul.i.5.3.23 = mul nsw i32 %conv1.i.5.3.23, -951 *)
mul v_mul_i_5_3_23 v_conv1_i_5_3_23 (-951)@sint32;
(*   %call.i.5.3.23 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.23) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_23, v_call_i_5_3_23);
(*   %arrayidx11.5.3.23 = getelementptr inbounds i16, i16* %r, i64 187 *)
(*   %1471 = load i16, i16* %arrayidx11.5.3.23, align 2, !tbaa !3 *)
mov v1471 mem0_374;
(*   %sub.5.3.23 = sub i16 %1471, %call.i.5.3.23 *)
sub v_sub_5_3_23 v1471 v_call_i_5_3_23;
(*   store i16 %sub.5.3.23, i16* %arrayidx9.5.3.23, align 2, !tbaa !3 *)
mov mem0_382 v_sub_5_3_23;
(*   %add21.5.3.23 = add i16 %1471, %call.i.5.3.23 *)
add v_add21_5_3_23 v1471 v_call_i_5_3_23;
(*   store i16 %add21.5.3.23, i16* %arrayidx11.5.3.23, align 2, !tbaa !3 *)
mov mem0_374 v_add21_5_3_23;

(* NOTE: k = 56 *)

(*   %arrayidx9.5.24 = getelementptr inbounds i16, i16* %r, i64 196 *)
(*   %1472 = load i16, i16* %arrayidx9.5.24, align 2, !tbaa !3 *)
mov v1472 mem0_392;
(*   %conv1.i.5.24 = sext i16 %1472 to i32 *)
cast v_conv1_i_5_24@sint32 v1472@sint16;
(*   %mul.i.5.24 = mul nsw i32 %conv1.i.5.24, -398 *)
mul v_mul_i_5_24 v_conv1_i_5_24 (-398)@sint32;
(*   %call.i.5.24 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.24) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_24, v_call_i_5_24);
(*   %arrayidx11.5.24 = getelementptr inbounds i16, i16* %r, i64 192 *)
(*   %1473 = load i16, i16* %arrayidx11.5.24, align 2, !tbaa !3 *)
mov v1473 mem0_384;
(*   %sub.5.24 = sub i16 %1473, %call.i.5.24 *)
sub v_sub_5_24 v1473 v_call_i_5_24;
(*   store i16 %sub.5.24, i16* %arrayidx9.5.24, align 2, !tbaa !3 *)
mov mem0_392 v_sub_5_24;
(*   %add21.5.24 = add i16 %1473, %call.i.5.24 *)
add v_add21_5_24 v1473 v_call_i_5_24;
(*   store i16 %add21.5.24, i16* %arrayidx11.5.24, align 2, !tbaa !3 *)
mov mem0_384 v_add21_5_24;
(*   %arrayidx9.5.1.24 = getelementptr inbounds i16, i16* %r, i64 197 *)
(*   %1474 = load i16, i16* %arrayidx9.5.1.24, align 2, !tbaa !3 *)
mov v1474 mem0_394;
(*   %conv1.i.5.1.24 = sext i16 %1474 to i32 *)
cast v_conv1_i_5_1_24@sint32 v1474@sint16;
(*   %mul.i.5.1.24 = mul nsw i32 %conv1.i.5.1.24, -398 *)
mul v_mul_i_5_1_24 v_conv1_i_5_1_24 (-398)@sint32;
(*   %call.i.5.1.24 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.24) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_24, v_call_i_5_1_24);
(*   %arrayidx11.5.1.24 = getelementptr inbounds i16, i16* %r, i64 193 *)
(*   %1475 = load i16, i16* %arrayidx11.5.1.24, align 2, !tbaa !3 *)
mov v1475 mem0_386;
(*   %sub.5.1.24 = sub i16 %1475, %call.i.5.1.24 *)
sub v_sub_5_1_24 v1475 v_call_i_5_1_24;
(*   store i16 %sub.5.1.24, i16* %arrayidx9.5.1.24, align 2, !tbaa !3 *)
mov mem0_394 v_sub_5_1_24;
(*   %add21.5.1.24 = add i16 %1475, %call.i.5.1.24 *)
add v_add21_5_1_24 v1475 v_call_i_5_1_24;
(*   store i16 %add21.5.1.24, i16* %arrayidx11.5.1.24, align 2, !tbaa !3 *)
mov mem0_386 v_add21_5_1_24;
(*   %arrayidx9.5.2.24 = getelementptr inbounds i16, i16* %r, i64 198 *)
(*   %1476 = load i16, i16* %arrayidx9.5.2.24, align 2, !tbaa !3 *)
mov v1476 mem0_396;
(*   %conv1.i.5.2.24 = sext i16 %1476 to i32 *)
cast v_conv1_i_5_2_24@sint32 v1476@sint16;
(*   %mul.i.5.2.24 = mul nsw i32 %conv1.i.5.2.24, -398 *)
mul v_mul_i_5_2_24 v_conv1_i_5_2_24 (-398)@sint32;
(*   %call.i.5.2.24 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.24) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_24, v_call_i_5_2_24);
(*   %arrayidx11.5.2.24 = getelementptr inbounds i16, i16* %r, i64 194 *)
(*   %1477 = load i16, i16* %arrayidx11.5.2.24, align 2, !tbaa !3 *)
mov v1477 mem0_388;
(*   %sub.5.2.24 = sub i16 %1477, %call.i.5.2.24 *)
sub v_sub_5_2_24 v1477 v_call_i_5_2_24;
(*   store i16 %sub.5.2.24, i16* %arrayidx9.5.2.24, align 2, !tbaa !3 *)
mov mem0_396 v_sub_5_2_24;
(*   %add21.5.2.24 = add i16 %1477, %call.i.5.2.24 *)
add v_add21_5_2_24 v1477 v_call_i_5_2_24;
(*   store i16 %add21.5.2.24, i16* %arrayidx11.5.2.24, align 2, !tbaa !3 *)
mov mem0_388 v_add21_5_2_24;
(*   %arrayidx9.5.3.24 = getelementptr inbounds i16, i16* %r, i64 199 *)
(*   %1478 = load i16, i16* %arrayidx9.5.3.24, align 2, !tbaa !3 *)
mov v1478 mem0_398;
(*   %conv1.i.5.3.24 = sext i16 %1478 to i32 *)
cast v_conv1_i_5_3_24@sint32 v1478@sint16;
(*   %mul.i.5.3.24 = mul nsw i32 %conv1.i.5.3.24, -398 *)
mul v_mul_i_5_3_24 v_conv1_i_5_3_24 (-398)@sint32;
(*   %call.i.5.3.24 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.24) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_24, v_call_i_5_3_24);
(*   %arrayidx11.5.3.24 = getelementptr inbounds i16, i16* %r, i64 195 *)
(*   %1479 = load i16, i16* %arrayidx11.5.3.24, align 2, !tbaa !3 *)
mov v1479 mem0_390;
(*   %sub.5.3.24 = sub i16 %1479, %call.i.5.3.24 *)
sub v_sub_5_3_24 v1479 v_call_i_5_3_24;
(*   store i16 %sub.5.3.24, i16* %arrayidx9.5.3.24, align 2, !tbaa !3 *)
mov mem0_398 v_sub_5_3_24;
(*   %add21.5.3.24 = add i16 %1479, %call.i.5.3.24 *)
add v_add21_5_3_24 v1479 v_call_i_5_3_24;
(*   store i16 %add21.5.3.24, i16* %arrayidx11.5.3.24, align 2, !tbaa !3 *)
mov mem0_390 v_add21_5_3_24;

(* NOTE: k = 57 *)

(*   %arrayidx9.5.25 = getelementptr inbounds i16, i16* %r, i64 204 *)
(*   %1480 = load i16, i16* %arrayidx9.5.25, align 2, !tbaa !3 *)
mov v1480 mem0_408;
(*   %conv1.i.5.25 = sext i16 %1480 to i32 *)
cast v_conv1_i_5_25@sint32 v1480@sint16;
(*   %mul.i.5.25 = mul nsw i32 %conv1.i.5.25, 961 *)
mul v_mul_i_5_25 v_conv1_i_5_25 (961)@sint32;
(*   %call.i.5.25 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.25) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_25, v_call_i_5_25);
(*   %arrayidx11.5.25 = getelementptr inbounds i16, i16* %r, i64 200 *)
(*   %1481 = load i16, i16* %arrayidx11.5.25, align 2, !tbaa !3 *)
mov v1481 mem0_400;
(*   %sub.5.25 = sub i16 %1481, %call.i.5.25 *)
sub v_sub_5_25 v1481 v_call_i_5_25;
(*   store i16 %sub.5.25, i16* %arrayidx9.5.25, align 2, !tbaa !3 *)
mov mem0_408 v_sub_5_25;
(*   %add21.5.25 = add i16 %1481, %call.i.5.25 *)
add v_add21_5_25 v1481 v_call_i_5_25;
(*   store i16 %add21.5.25, i16* %arrayidx11.5.25, align 2, !tbaa !3 *)
mov mem0_400 v_add21_5_25;
(*   %arrayidx9.5.1.25 = getelementptr inbounds i16, i16* %r, i64 205 *)
(*   %1482 = load i16, i16* %arrayidx9.5.1.25, align 2, !tbaa !3 *)
mov v1482 mem0_410;
(*   %conv1.i.5.1.25 = sext i16 %1482 to i32 *)
cast v_conv1_i_5_1_25@sint32 v1482@sint16;
(*   %mul.i.5.1.25 = mul nsw i32 %conv1.i.5.1.25, 961 *)
mul v_mul_i_5_1_25 v_conv1_i_5_1_25 (961)@sint32;
(*   %call.i.5.1.25 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.25) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_25, v_call_i_5_1_25);
(*   %arrayidx11.5.1.25 = getelementptr inbounds i16, i16* %r, i64 201 *)
(*   %1483 = load i16, i16* %arrayidx11.5.1.25, align 2, !tbaa !3 *)
mov v1483 mem0_402;
(*   %sub.5.1.25 = sub i16 %1483, %call.i.5.1.25 *)
sub v_sub_5_1_25 v1483 v_call_i_5_1_25;
(*   store i16 %sub.5.1.25, i16* %arrayidx9.5.1.25, align 2, !tbaa !3 *)
mov mem0_410 v_sub_5_1_25;
(*   %add21.5.1.25 = add i16 %1483, %call.i.5.1.25 *)
add v_add21_5_1_25 v1483 v_call_i_5_1_25;
(*   store i16 %add21.5.1.25, i16* %arrayidx11.5.1.25, align 2, !tbaa !3 *)
mov mem0_402 v_add21_5_1_25;
(*   %arrayidx9.5.2.25 = getelementptr inbounds i16, i16* %r, i64 206 *)
(*   %1484 = load i16, i16* %arrayidx9.5.2.25, align 2, !tbaa !3 *)
mov v1484 mem0_412;
(*   %conv1.i.5.2.25 = sext i16 %1484 to i32 *)
cast v_conv1_i_5_2_25@sint32 v1484@sint16;
(*   %mul.i.5.2.25 = mul nsw i32 %conv1.i.5.2.25, 961 *)
mul v_mul_i_5_2_25 v_conv1_i_5_2_25 (961)@sint32;
(*   %call.i.5.2.25 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.25) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_25, v_call_i_5_2_25);
(*   %arrayidx11.5.2.25 = getelementptr inbounds i16, i16* %r, i64 202 *)
(*   %1485 = load i16, i16* %arrayidx11.5.2.25, align 2, !tbaa !3 *)
mov v1485 mem0_404;
(*   %sub.5.2.25 = sub i16 %1485, %call.i.5.2.25 *)
sub v_sub_5_2_25 v1485 v_call_i_5_2_25;
(*   store i16 %sub.5.2.25, i16* %arrayidx9.5.2.25, align 2, !tbaa !3 *)
mov mem0_412 v_sub_5_2_25;
(*   %add21.5.2.25 = add i16 %1485, %call.i.5.2.25 *)
add v_add21_5_2_25 v1485 v_call_i_5_2_25;
(*   store i16 %add21.5.2.25, i16* %arrayidx11.5.2.25, align 2, !tbaa !3 *)
mov mem0_404 v_add21_5_2_25;
(*   %arrayidx9.5.3.25 = getelementptr inbounds i16, i16* %r, i64 207 *)
(*   %1486 = load i16, i16* %arrayidx9.5.3.25, align 2, !tbaa !3 *)
mov v1486 mem0_414;
(*   %conv1.i.5.3.25 = sext i16 %1486 to i32 *)
cast v_conv1_i_5_3_25@sint32 v1486@sint16;
(*   %mul.i.5.3.25 = mul nsw i32 %conv1.i.5.3.25, 961 *)
mul v_mul_i_5_3_25 v_conv1_i_5_3_25 (961)@sint32;
(*   %call.i.5.3.25 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.25) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_25, v_call_i_5_3_25);
(*   %arrayidx11.5.3.25 = getelementptr inbounds i16, i16* %r, i64 203 *)
(*   %1487 = load i16, i16* %arrayidx11.5.3.25, align 2, !tbaa !3 *)
mov v1487 mem0_406;
(*   %sub.5.3.25 = sub i16 %1487, %call.i.5.3.25 *)
sub v_sub_5_3_25 v1487 v_call_i_5_3_25;
(*   store i16 %sub.5.3.25, i16* %arrayidx9.5.3.25, align 2, !tbaa !3 *)
mov mem0_414 v_sub_5_3_25;
(*   %add21.5.3.25 = add i16 %1487, %call.i.5.3.25 *)
add v_add21_5_3_25 v1487 v_call_i_5_3_25;
(*   store i16 %add21.5.3.25, i16* %arrayidx11.5.3.25, align 2, !tbaa !3 *)
mov mem0_406 v_add21_5_3_25;

(* NOTE: k = 58 *)

(*   %arrayidx9.5.26 = getelementptr inbounds i16, i16* %r, i64 212 *)
(*   %1488 = load i16, i16* %arrayidx9.5.26, align 2, !tbaa !3 *)
mov v1488 mem0_424;
(*   %conv1.i.5.26 = sext i16 %1488 to i32 *)
cast v_conv1_i_5_26@sint32 v1488@sint16;
(*   %mul.i.5.26 = mul nsw i32 %conv1.i.5.26, -1508 *)
mul v_mul_i_5_26 v_conv1_i_5_26 (-1508)@sint32;
(*   %call.i.5.26 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.26) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_26, v_call_i_5_26);
(*   %arrayidx11.5.26 = getelementptr inbounds i16, i16* %r, i64 208 *)
(*   %1489 = load i16, i16* %arrayidx11.5.26, align 2, !tbaa !3 *)
mov v1489 mem0_416;
(*   %sub.5.26 = sub i16 %1489, %call.i.5.26 *)
sub v_sub_5_26 v1489 v_call_i_5_26;
(*   store i16 %sub.5.26, i16* %arrayidx9.5.26, align 2, !tbaa !3 *)
mov mem0_424 v_sub_5_26;
(*   %add21.5.26 = add i16 %1489, %call.i.5.26 *)
add v_add21_5_26 v1489 v_call_i_5_26;
(*   store i16 %add21.5.26, i16* %arrayidx11.5.26, align 2, !tbaa !3 *)
mov mem0_416 v_add21_5_26;
(*   %arrayidx9.5.1.26 = getelementptr inbounds i16, i16* %r, i64 213 *)
(*   %1490 = load i16, i16* %arrayidx9.5.1.26, align 2, !tbaa !3 *)
mov v1490 mem0_426;
(*   %conv1.i.5.1.26 = sext i16 %1490 to i32 *)
cast v_conv1_i_5_1_26@sint32 v1490@sint16;
(*   %mul.i.5.1.26 = mul nsw i32 %conv1.i.5.1.26, -1508 *)
mul v_mul_i_5_1_26 v_conv1_i_5_1_26 (-1508)@sint32;
(*   %call.i.5.1.26 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.26) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_26, v_call_i_5_1_26);
(*   %arrayidx11.5.1.26 = getelementptr inbounds i16, i16* %r, i64 209 *)
(*   %1491 = load i16, i16* %arrayidx11.5.1.26, align 2, !tbaa !3 *)
mov v1491 mem0_418;
(*   %sub.5.1.26 = sub i16 %1491, %call.i.5.1.26 *)
sub v_sub_5_1_26 v1491 v_call_i_5_1_26;
(*   store i16 %sub.5.1.26, i16* %arrayidx9.5.1.26, align 2, !tbaa !3 *)
mov mem0_426 v_sub_5_1_26;
(*   %add21.5.1.26 = add i16 %1491, %call.i.5.1.26 *)
add v_add21_5_1_26 v1491 v_call_i_5_1_26;
(*   store i16 %add21.5.1.26, i16* %arrayidx11.5.1.26, align 2, !tbaa !3 *)
mov mem0_418 v_add21_5_1_26;
(*   %arrayidx9.5.2.26 = getelementptr inbounds i16, i16* %r, i64 214 *)
(*   %1492 = load i16, i16* %arrayidx9.5.2.26, align 2, !tbaa !3 *)
mov v1492 mem0_428;
(*   %conv1.i.5.2.26 = sext i16 %1492 to i32 *)
cast v_conv1_i_5_2_26@sint32 v1492@sint16;
(*   %mul.i.5.2.26 = mul nsw i32 %conv1.i.5.2.26, -1508 *)
mul v_mul_i_5_2_26 v_conv1_i_5_2_26 (-1508)@sint32;
(*   %call.i.5.2.26 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.26) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_26, v_call_i_5_2_26);
(*   %arrayidx11.5.2.26 = getelementptr inbounds i16, i16* %r, i64 210 *)
(*   %1493 = load i16, i16* %arrayidx11.5.2.26, align 2, !tbaa !3 *)
mov v1493 mem0_420;
(*   %sub.5.2.26 = sub i16 %1493, %call.i.5.2.26 *)
sub v_sub_5_2_26 v1493 v_call_i_5_2_26;
(*   store i16 %sub.5.2.26, i16* %arrayidx9.5.2.26, align 2, !tbaa !3 *)
mov mem0_428 v_sub_5_2_26;
(*   %add21.5.2.26 = add i16 %1493, %call.i.5.2.26 *)
add v_add21_5_2_26 v1493 v_call_i_5_2_26;
(*   store i16 %add21.5.2.26, i16* %arrayidx11.5.2.26, align 2, !tbaa !3 *)
mov mem0_420 v_add21_5_2_26;
(*   %arrayidx9.5.3.26 = getelementptr inbounds i16, i16* %r, i64 215 *)
(*   %1494 = load i16, i16* %arrayidx9.5.3.26, align 2, !tbaa !3 *)
mov v1494 mem0_430;
(*   %conv1.i.5.3.26 = sext i16 %1494 to i32 *)
cast v_conv1_i_5_3_26@sint32 v1494@sint16;
(*   %mul.i.5.3.26 = mul nsw i32 %conv1.i.5.3.26, -1508 *)
mul v_mul_i_5_3_26 v_conv1_i_5_3_26 (-1508)@sint32;
(*   %call.i.5.3.26 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.26) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_26, v_call_i_5_3_26);
(*   %arrayidx11.5.3.26 = getelementptr inbounds i16, i16* %r, i64 211 *)
(*   %1495 = load i16, i16* %arrayidx11.5.3.26, align 2, !tbaa !3 *)
mov v1495 mem0_422;
(*   %sub.5.3.26 = sub i16 %1495, %call.i.5.3.26 *)
sub v_sub_5_3_26 v1495 v_call_i_5_3_26;
(*   store i16 %sub.5.3.26, i16* %arrayidx9.5.3.26, align 2, !tbaa !3 *)
mov mem0_430 v_sub_5_3_26;
(*   %add21.5.3.26 = add i16 %1495, %call.i.5.3.26 *)
add v_add21_5_3_26 v1495 v_call_i_5_3_26;
(*   store i16 %add21.5.3.26, i16* %arrayidx11.5.3.26, align 2, !tbaa !3 *)
mov mem0_422 v_add21_5_3_26;
(*   %arrayidx9.5.27 = getelementptr inbounds i16, i16* %r, i64 220 *)
(*   %1496 = load i16, i16* %arrayidx9.5.27, align 2, !tbaa !3 *)
mov v1496 mem0_440;
(*   %conv1.i.5.27 = sext i16 %1496 to i32 *)
cast v_conv1_i_5_27@sint32 v1496@sint16;
(*   %mul.i.5.27 = mul nsw i32 %conv1.i.5.27, -725 *)
mul v_mul_i_5_27 v_conv1_i_5_27 (-725)@sint32;
(*   %call.i.5.27 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.27) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_27, v_call_i_5_27);
(*   %arrayidx11.5.27 = getelementptr inbounds i16, i16* %r, i64 216 *)
(*   %1497 = load i16, i16* %arrayidx11.5.27, align 2, !tbaa !3 *)
mov v1497 mem0_432;
(*   %sub.5.27 = sub i16 %1497, %call.i.5.27 *)
sub v_sub_5_27 v1497 v_call_i_5_27;
(*   store i16 %sub.5.27, i16* %arrayidx9.5.27, align 2, !tbaa !3 *)
mov mem0_440 v_sub_5_27;
(*   %add21.5.27 = add i16 %1497, %call.i.5.27 *)
add v_add21_5_27 v1497 v_call_i_5_27;
(*   store i16 %add21.5.27, i16* %arrayidx11.5.27, align 2, !tbaa !3 *)
mov mem0_432 v_add21_5_27;

(* NOTE: k = 59 *)

(*   %arrayidx9.5.1.27 = getelementptr inbounds i16, i16* %r, i64 221 *)
(*   %1498 = load i16, i16* %arrayidx9.5.1.27, align 2, !tbaa !3 *)
mov v1498 mem0_442;
(*   %conv1.i.5.1.27 = sext i16 %1498 to i32 *)
cast v_conv1_i_5_1_27@sint32 v1498@sint16;
(*   %mul.i.5.1.27 = mul nsw i32 %conv1.i.5.1.27, -725 *)
mul v_mul_i_5_1_27 v_conv1_i_5_1_27 (-725)@sint32;
(*   %call.i.5.1.27 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.27) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_27, v_call_i_5_1_27);
(*   %arrayidx11.5.1.27 = getelementptr inbounds i16, i16* %r, i64 217 *)
(*   %1499 = load i16, i16* %arrayidx11.5.1.27, align 2, !tbaa !3 *)
mov v1499 mem0_434;
(*   %sub.5.1.27 = sub i16 %1499, %call.i.5.1.27 *)
sub v_sub_5_1_27 v1499 v_call_i_5_1_27;
(*   store i16 %sub.5.1.27, i16* %arrayidx9.5.1.27, align 2, !tbaa !3 *)
mov mem0_442 v_sub_5_1_27;
(*   %add21.5.1.27 = add i16 %1499, %call.i.5.1.27 *)
add v_add21_5_1_27 v1499 v_call_i_5_1_27;
(*   store i16 %add21.5.1.27, i16* %arrayidx11.5.1.27, align 2, !tbaa !3 *)
mov mem0_434 v_add21_5_1_27;
(*   %arrayidx9.5.2.27 = getelementptr inbounds i16, i16* %r, i64 222 *)
(*   %1500 = load i16, i16* %arrayidx9.5.2.27, align 2, !tbaa !3 *)
mov v1500 mem0_444;
(*   %conv1.i.5.2.27 = sext i16 %1500 to i32 *)
cast v_conv1_i_5_2_27@sint32 v1500@sint16;
(*   %mul.i.5.2.27 = mul nsw i32 %conv1.i.5.2.27, -725 *)
mul v_mul_i_5_2_27 v_conv1_i_5_2_27 (-725)@sint32;
(*   %call.i.5.2.27 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.27) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_27, v_call_i_5_2_27);
(*   %arrayidx11.5.2.27 = getelementptr inbounds i16, i16* %r, i64 218 *)
(*   %1501 = load i16, i16* %arrayidx11.5.2.27, align 2, !tbaa !3 *)
mov v1501 mem0_436;
(*   %sub.5.2.27 = sub i16 %1501, %call.i.5.2.27 *)
sub v_sub_5_2_27 v1501 v_call_i_5_2_27;
(*   store i16 %sub.5.2.27, i16* %arrayidx9.5.2.27, align 2, !tbaa !3 *)
mov mem0_444 v_sub_5_2_27;
(*   %add21.5.2.27 = add i16 %1501, %call.i.5.2.27 *)
add v_add21_5_2_27 v1501 v_call_i_5_2_27;
(*   store i16 %add21.5.2.27, i16* %arrayidx11.5.2.27, align 2, !tbaa !3 *)
mov mem0_436 v_add21_5_2_27;
(*   %arrayidx9.5.3.27 = getelementptr inbounds i16, i16* %r, i64 223 *)
(*   %1502 = load i16, i16* %arrayidx9.5.3.27, align 2, !tbaa !3 *)
mov v1502 mem0_446;
(*   %conv1.i.5.3.27 = sext i16 %1502 to i32 *)
cast v_conv1_i_5_3_27@sint32 v1502@sint16;
(*   %mul.i.5.3.27 = mul nsw i32 %conv1.i.5.3.27, -725 *)
mul v_mul_i_5_3_27 v_conv1_i_5_3_27 (-725)@sint32;
(*   %call.i.5.3.27 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.27) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_27, v_call_i_5_3_27);
(*   %arrayidx11.5.3.27 = getelementptr inbounds i16, i16* %r, i64 219 *)
(*   %1503 = load i16, i16* %arrayidx11.5.3.27, align 2, !tbaa !3 *)
mov v1503 mem0_438;
(*   %sub.5.3.27 = sub i16 %1503, %call.i.5.3.27 *)
sub v_sub_5_3_27 v1503 v_call_i_5_3_27;
(*   store i16 %sub.5.3.27, i16* %arrayidx9.5.3.27, align 2, !tbaa !3 *)
mov mem0_446 v_sub_5_3_27;
(*   %add21.5.3.27 = add i16 %1503, %call.i.5.3.27 *)
add v_add21_5_3_27 v1503 v_call_i_5_3_27;
(*   store i16 %add21.5.3.27, i16* %arrayidx11.5.3.27, align 2, !tbaa !3 *)
mov mem0_438 v_add21_5_3_27;

(* NOTE: k = 60 *)

(*   %arrayidx9.5.28 = getelementptr inbounds i16, i16* %r, i64 228 *)
(*   %1504 = load i16, i16* %arrayidx9.5.28, align 2, !tbaa !3 *)
mov v1504 mem0_456;
(*   %conv1.i.5.28 = sext i16 %1504 to i32 *)
cast v_conv1_i_5_28@sint32 v1504@sint16;
(*   %mul.i.5.28 = mul nsw i32 %conv1.i.5.28, 448 *)
mul v_mul_i_5_28 v_conv1_i_5_28 (448)@sint32;
(*   %call.i.5.28 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.28) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_28, v_call_i_5_28);
(*   %arrayidx11.5.28 = getelementptr inbounds i16, i16* %r, i64 224 *)
(*   %1505 = load i16, i16* %arrayidx11.5.28, align 2, !tbaa !3 *)
mov v1505 mem0_448;
(*   %sub.5.28 = sub i16 %1505, %call.i.5.28 *)
sub v_sub_5_28 v1505 v_call_i_5_28;
(*   store i16 %sub.5.28, i16* %arrayidx9.5.28, align 2, !tbaa !3 *)
mov mem0_456 v_sub_5_28;
(*   %add21.5.28 = add i16 %1505, %call.i.5.28 *)
add v_add21_5_28 v1505 v_call_i_5_28;
(*   store i16 %add21.5.28, i16* %arrayidx11.5.28, align 2, !tbaa !3 *)
mov mem0_448 v_add21_5_28;
(*   %arrayidx9.5.1.28 = getelementptr inbounds i16, i16* %r, i64 229 *)
(*   %1506 = load i16, i16* %arrayidx9.5.1.28, align 2, !tbaa !3 *)
mov v1506 mem0_458;
(*   %conv1.i.5.1.28 = sext i16 %1506 to i32 *)
cast v_conv1_i_5_1_28@sint32 v1506@sint16;
(*   %mul.i.5.1.28 = mul nsw i32 %conv1.i.5.1.28, 448 *)
mul v_mul_i_5_1_28 v_conv1_i_5_1_28 (448)@sint32;
(*   %call.i.5.1.28 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.28) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_28, v_call_i_5_1_28);
(*   %arrayidx11.5.1.28 = getelementptr inbounds i16, i16* %r, i64 225 *)
(*   %1507 = load i16, i16* %arrayidx11.5.1.28, align 2, !tbaa !3 *)
mov v1507 mem0_450;
(*   %sub.5.1.28 = sub i16 %1507, %call.i.5.1.28 *)
sub v_sub_5_1_28 v1507 v_call_i_5_1_28;
(*   store i16 %sub.5.1.28, i16* %arrayidx9.5.1.28, align 2, !tbaa !3 *)
mov mem0_458 v_sub_5_1_28;
(*   %add21.5.1.28 = add i16 %1507, %call.i.5.1.28 *)
add v_add21_5_1_28 v1507 v_call_i_5_1_28;
(*   store i16 %add21.5.1.28, i16* %arrayidx11.5.1.28, align 2, !tbaa !3 *)
mov mem0_450 v_add21_5_1_28;
(*   %arrayidx9.5.2.28 = getelementptr inbounds i16, i16* %r, i64 230 *)
(*   %1508 = load i16, i16* %arrayidx9.5.2.28, align 2, !tbaa !3 *)
mov v1508 mem0_460;
(*   %conv1.i.5.2.28 = sext i16 %1508 to i32 *)
cast v_conv1_i_5_2_28@sint32 v1508@sint16;
(*   %mul.i.5.2.28 = mul nsw i32 %conv1.i.5.2.28, 448 *)
mul v_mul_i_5_2_28 v_conv1_i_5_2_28 (448)@sint32;
(*   %call.i.5.2.28 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.28) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_28, v_call_i_5_2_28);
(*   %arrayidx11.5.2.28 = getelementptr inbounds i16, i16* %r, i64 226 *)
(*   %1509 = load i16, i16* %arrayidx11.5.2.28, align 2, !tbaa !3 *)
mov v1509 mem0_452;
(*   %sub.5.2.28 = sub i16 %1509, %call.i.5.2.28 *)
sub v_sub_5_2_28 v1509 v_call_i_5_2_28;
(*   store i16 %sub.5.2.28, i16* %arrayidx9.5.2.28, align 2, !tbaa !3 *)
mov mem0_460 v_sub_5_2_28;
(*   %add21.5.2.28 = add i16 %1509, %call.i.5.2.28 *)
add v_add21_5_2_28 v1509 v_call_i_5_2_28;
(*   store i16 %add21.5.2.28, i16* %arrayidx11.5.2.28, align 2, !tbaa !3 *)
mov mem0_452 v_add21_5_2_28;
(*   %arrayidx9.5.3.28 = getelementptr inbounds i16, i16* %r, i64 231 *)
(*   %1510 = load i16, i16* %arrayidx9.5.3.28, align 2, !tbaa !3 *)
mov v1510 mem0_462;
(*   %conv1.i.5.3.28 = sext i16 %1510 to i32 *)
cast v_conv1_i_5_3_28@sint32 v1510@sint16;
(*   %mul.i.5.3.28 = mul nsw i32 %conv1.i.5.3.28, 448 *)
mul v_mul_i_5_3_28 v_conv1_i_5_3_28 (448)@sint32;
(*   %call.i.5.3.28 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.28) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_28, v_call_i_5_3_28);
(*   %arrayidx11.5.3.28 = getelementptr inbounds i16, i16* %r, i64 227 *)
(*   %1511 = load i16, i16* %arrayidx11.5.3.28, align 2, !tbaa !3 *)
mov v1511 mem0_454;
(*   %sub.5.3.28 = sub i16 %1511, %call.i.5.3.28 *)
sub v_sub_5_3_28 v1511 v_call_i_5_3_28;
(*   store i16 %sub.5.3.28, i16* %arrayidx9.5.3.28, align 2, !tbaa !3 *)
mov mem0_462 v_sub_5_3_28;
(*   %add21.5.3.28 = add i16 %1511, %call.i.5.3.28 *)
add v_add21_5_3_28 v1511 v_call_i_5_3_28;
(*   store i16 %add21.5.3.28, i16* %arrayidx11.5.3.28, align 2, !tbaa !3 *)
mov mem0_454 v_add21_5_3_28;

(* NOTE: k = 61 *)

(*   %arrayidx9.5.29 = getelementptr inbounds i16, i16* %r, i64 236 *)
(*   %1512 = load i16, i16* %arrayidx9.5.29, align 2, !tbaa !3 *)
mov v1512 mem0_472;
(*   %conv1.i.5.29 = sext i16 %1512 to i32 *)
cast v_conv1_i_5_29@sint32 v1512@sint16;
(*   %mul.i.5.29 = mul nsw i32 %conv1.i.5.29, -1065 *)
mul v_mul_i_5_29 v_conv1_i_5_29 (-1065)@sint32;
(*   %call.i.5.29 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.29) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_29, v_call_i_5_29);
(*   %arrayidx11.5.29 = getelementptr inbounds i16, i16* %r, i64 232 *)
(*   %1513 = load i16, i16* %arrayidx11.5.29, align 2, !tbaa !3 *)
mov v1513 mem0_464;
(*   %sub.5.29 = sub i16 %1513, %call.i.5.29 *)
sub v_sub_5_29 v1513 v_call_i_5_29;
(*   store i16 %sub.5.29, i16* %arrayidx9.5.29, align 2, !tbaa !3 *)
mov mem0_472 v_sub_5_29;
(*   %add21.5.29 = add i16 %1513, %call.i.5.29 *)
add v_add21_5_29 v1513 v_call_i_5_29;
(*   store i16 %add21.5.29, i16* %arrayidx11.5.29, align 2, !tbaa !3 *)
mov mem0_464 v_add21_5_29;
(*   %arrayidx9.5.1.29 = getelementptr inbounds i16, i16* %r, i64 237 *)
(*   %1514 = load i16, i16* %arrayidx9.5.1.29, align 2, !tbaa !3 *)
mov v1514 mem0_474;
(*   %conv1.i.5.1.29 = sext i16 %1514 to i32 *)
cast v_conv1_i_5_1_29@sint32 v1514@sint16;
(*   %mul.i.5.1.29 = mul nsw i32 %conv1.i.5.1.29, -1065 *)
mul v_mul_i_5_1_29 v_conv1_i_5_1_29 (-1065)@sint32;
(*   %call.i.5.1.29 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.29) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_29, v_call_i_5_1_29);
(*   %arrayidx11.5.1.29 = getelementptr inbounds i16, i16* %r, i64 233 *)
(*   %1515 = load i16, i16* %arrayidx11.5.1.29, align 2, !tbaa !3 *)
mov v1515 mem0_466;
(*   %sub.5.1.29 = sub i16 %1515, %call.i.5.1.29 *)
sub v_sub_5_1_29 v1515 v_call_i_5_1_29;
(*   store i16 %sub.5.1.29, i16* %arrayidx9.5.1.29, align 2, !tbaa !3 *)
mov mem0_474 v_sub_5_1_29;
(*   %add21.5.1.29 = add i16 %1515, %call.i.5.1.29 *)
add v_add21_5_1_29 v1515 v_call_i_5_1_29;
(*   store i16 %add21.5.1.29, i16* %arrayidx11.5.1.29, align 2, !tbaa !3 *)
mov mem0_466 v_add21_5_1_29;
(*   %arrayidx9.5.2.29 = getelementptr inbounds i16, i16* %r, i64 238 *)
(*   %1516 = load i16, i16* %arrayidx9.5.2.29, align 2, !tbaa !3 *)
mov v1516 mem0_476;
(*   %conv1.i.5.2.29 = sext i16 %1516 to i32 *)
cast v_conv1_i_5_2_29@sint32 v1516@sint16;
(*   %mul.i.5.2.29 = mul nsw i32 %conv1.i.5.2.29, -1065 *)
mul v_mul_i_5_2_29 v_conv1_i_5_2_29 (-1065)@sint32;
(*   %call.i.5.2.29 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.29) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_29, v_call_i_5_2_29);
(*   %arrayidx11.5.2.29 = getelementptr inbounds i16, i16* %r, i64 234 *)
(*   %1517 = load i16, i16* %arrayidx11.5.2.29, align 2, !tbaa !3 *)
mov v1517 mem0_468;
(*   %sub.5.2.29 = sub i16 %1517, %call.i.5.2.29 *)
sub v_sub_5_2_29 v1517 v_call_i_5_2_29;
(*   store i16 %sub.5.2.29, i16* %arrayidx9.5.2.29, align 2, !tbaa !3 *)
mov mem0_476 v_sub_5_2_29;
(*   %add21.5.2.29 = add i16 %1517, %call.i.5.2.29 *)
add v_add21_5_2_29 v1517 v_call_i_5_2_29;
(*   store i16 %add21.5.2.29, i16* %arrayidx11.5.2.29, align 2, !tbaa !3 *)
mov mem0_468 v_add21_5_2_29;
(*   %arrayidx9.5.3.29 = getelementptr inbounds i16, i16* %r, i64 239 *)
(*   %1518 = load i16, i16* %arrayidx9.5.3.29, align 2, !tbaa !3 *)
mov v1518 mem0_478;
(*   %conv1.i.5.3.29 = sext i16 %1518 to i32 *)
cast v_conv1_i_5_3_29@sint32 v1518@sint16;
(*   %mul.i.5.3.29 = mul nsw i32 %conv1.i.5.3.29, -1065 *)
mul v_mul_i_5_3_29 v_conv1_i_5_3_29 (-1065)@sint32;
(*   %call.i.5.3.29 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.29) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_29, v_call_i_5_3_29);
(*   %arrayidx11.5.3.29 = getelementptr inbounds i16, i16* %r, i64 235 *)
(*   %1519 = load i16, i16* %arrayidx11.5.3.29, align 2, !tbaa !3 *)
mov v1519 mem0_470;
(*   %sub.5.3.29 = sub i16 %1519, %call.i.5.3.29 *)
sub v_sub_5_3_29 v1519 v_call_i_5_3_29;
(*   store i16 %sub.5.3.29, i16* %arrayidx9.5.3.29, align 2, !tbaa !3 *)
mov mem0_478 v_sub_5_3_29;
(*   %add21.5.3.29 = add i16 %1519, %call.i.5.3.29 *)
add v_add21_5_3_29 v1519 v_call_i_5_3_29;
(*   store i16 %add21.5.3.29, i16* %arrayidx11.5.3.29, align 2, !tbaa !3 *)
mov mem0_470 v_add21_5_3_29;

(* NOTE: k = 62 *)

(*   %arrayidx9.5.30 = getelementptr inbounds i16, i16* %r, i64 244 *)
(*   %1520 = load i16, i16* %arrayidx9.5.30, align 2, !tbaa !3 *)
mov v1520 mem0_488;
(*   %conv1.i.5.30 = sext i16 %1520 to i32 *)
cast v_conv1_i_5_30@sint32 v1520@sint16;
(*   %mul.i.5.30 = mul nsw i32 %conv1.i.5.30, 677 *)
mul v_mul_i_5_30 v_conv1_i_5_30 (677)@sint32;
(*   %call.i.5.30 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.30) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_30, v_call_i_5_30);
(*   %arrayidx11.5.30 = getelementptr inbounds i16, i16* %r, i64 240 *)
(*   %1521 = load i16, i16* %arrayidx11.5.30, align 2, !tbaa !3 *)
mov v1521 mem0_480;
(*   %sub.5.30 = sub i16 %1521, %call.i.5.30 *)
sub v_sub_5_30 v1521 v_call_i_5_30;
(*   store i16 %sub.5.30, i16* %arrayidx9.5.30, align 2, !tbaa !3 *)
mov mem0_488 v_sub_5_30;
(*   %add21.5.30 = add i16 %1521, %call.i.5.30 *)
add v_add21_5_30 v1521 v_call_i_5_30;
(*   store i16 %add21.5.30, i16* %arrayidx11.5.30, align 2, !tbaa !3 *)
mov mem0_480 v_add21_5_30;
(*   %arrayidx9.5.1.30 = getelementptr inbounds i16, i16* %r, i64 245 *)
(*   %1522 = load i16, i16* %arrayidx9.5.1.30, align 2, !tbaa !3 *)
mov v1522 mem0_490;
(*   %conv1.i.5.1.30 = sext i16 %1522 to i32 *)
cast v_conv1_i_5_1_30@sint32 v1522@sint16;
(*   %mul.i.5.1.30 = mul nsw i32 %conv1.i.5.1.30, 677 *)
mul v_mul_i_5_1_30 v_conv1_i_5_1_30 (677)@sint32;
(*   %call.i.5.1.30 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.30) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_30, v_call_i_5_1_30);
(*   %arrayidx11.5.1.30 = getelementptr inbounds i16, i16* %r, i64 241 *)
(*   %1523 = load i16, i16* %arrayidx11.5.1.30, align 2, !tbaa !3 *)
mov v1523 mem0_482;
(*   %sub.5.1.30 = sub i16 %1523, %call.i.5.1.30 *)
sub v_sub_5_1_30 v1523 v_call_i_5_1_30;
(*   store i16 %sub.5.1.30, i16* %arrayidx9.5.1.30, align 2, !tbaa !3 *)
mov mem0_490 v_sub_5_1_30;
(*   %add21.5.1.30 = add i16 %1523, %call.i.5.1.30 *)
add v_add21_5_1_30 v1523 v_call_i_5_1_30;
(*   store i16 %add21.5.1.30, i16* %arrayidx11.5.1.30, align 2, !tbaa !3 *)
mov mem0_482 v_add21_5_1_30;
(*   %arrayidx9.5.2.30 = getelementptr inbounds i16, i16* %r, i64 246 *)
(*   %1524 = load i16, i16* %arrayidx9.5.2.30, align 2, !tbaa !3 *)
mov v1524 mem0_492;
(*   %conv1.i.5.2.30 = sext i16 %1524 to i32 *)
cast v_conv1_i_5_2_30@sint32 v1524@sint16;
(*   %mul.i.5.2.30 = mul nsw i32 %conv1.i.5.2.30, 677 *)
mul v_mul_i_5_2_30 v_conv1_i_5_2_30 (677)@sint32;
(*   %call.i.5.2.30 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.30) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_30, v_call_i_5_2_30);
(*   %arrayidx11.5.2.30 = getelementptr inbounds i16, i16* %r, i64 242 *)
(*   %1525 = load i16, i16* %arrayidx11.5.2.30, align 2, !tbaa !3 *)
mov v1525 mem0_484;
(*   %sub.5.2.30 = sub i16 %1525, %call.i.5.2.30 *)
sub v_sub_5_2_30 v1525 v_call_i_5_2_30;
(*   store i16 %sub.5.2.30, i16* %arrayidx9.5.2.30, align 2, !tbaa !3 *)
mov mem0_492 v_sub_5_2_30;
(*   %add21.5.2.30 = add i16 %1525, %call.i.5.2.30 *)
add v_add21_5_2_30 v1525 v_call_i_5_2_30;
(*   store i16 %add21.5.2.30, i16* %arrayidx11.5.2.30, align 2, !tbaa !3 *)
mov mem0_484 v_add21_5_2_30;
(*   %arrayidx9.5.3.30 = getelementptr inbounds i16, i16* %r, i64 247 *)
(*   %1526 = load i16, i16* %arrayidx9.5.3.30, align 2, !tbaa !3 *)
mov v1526 mem0_494;
(*   %conv1.i.5.3.30 = sext i16 %1526 to i32 *)
cast v_conv1_i_5_3_30@sint32 v1526@sint16;
(*   %mul.i.5.3.30 = mul nsw i32 %conv1.i.5.3.30, 677 *)
mul v_mul_i_5_3_30 v_conv1_i_5_3_30 (677)@sint32;
(*   %call.i.5.3.30 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.30) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_30, v_call_i_5_3_30);
(*   %arrayidx11.5.3.30 = getelementptr inbounds i16, i16* %r, i64 243 *)
(*   %1527 = load i16, i16* %arrayidx11.5.3.30, align 2, !tbaa !3 *)
mov v1527 mem0_486;
(*   %sub.5.3.30 = sub i16 %1527, %call.i.5.3.30 *)
sub v_sub_5_3_30 v1527 v_call_i_5_3_30;
(*   store i16 %sub.5.3.30, i16* %arrayidx9.5.3.30, align 2, !tbaa !3 *)
mov mem0_494 v_sub_5_3_30;
(*   %add21.5.3.30 = add i16 %1527, %call.i.5.3.30 *)
add v_add21_5_3_30 v1527 v_call_i_5_3_30;
(*   store i16 %add21.5.3.30, i16* %arrayidx11.5.3.30, align 2, !tbaa !3 *)
mov mem0_486 v_add21_5_3_30;

(* NOTE: k = 63 *)

(*   %arrayidx9.5.31 = getelementptr inbounds i16, i16* %r, i64 252 *)
(*   %1528 = load i16, i16* %arrayidx9.5.31, align 2, !tbaa !3 *)
mov v1528 mem0_504;
(*   %conv1.i.5.31 = sext i16 %1528 to i32 *)
cast v_conv1_i_5_31@sint32 v1528@sint16;
(*   %mul.i.5.31 = mul nsw i32 %conv1.i.5.31, -1275 *)
mul v_mul_i_5_31 v_conv1_i_5_31 (-1275)@sint32;
(*   %call.i.5.31 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.31) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_31, v_call_i_5_31);
(*   %arrayidx11.5.31 = getelementptr inbounds i16, i16* %r, i64 248 *)
(*   %1529 = load i16, i16* %arrayidx11.5.31, align 2, !tbaa !3 *)
mov v1529 mem0_496;
(*   %sub.5.31 = sub i16 %1529, %call.i.5.31 *)
sub v_sub_5_31 v1529 v_call_i_5_31;
(*   store i16 %sub.5.31, i16* %arrayidx9.5.31, align 2, !tbaa !3 *)
mov mem0_504 v_sub_5_31;
(*   %add21.5.31 = add i16 %1529, %call.i.5.31 *)
add v_add21_5_31 v1529 v_call_i_5_31;
(*   store i16 %add21.5.31, i16* %arrayidx11.5.31, align 2, !tbaa !3 *)
mov mem0_496 v_add21_5_31;
(*   %arrayidx9.5.1.31 = getelementptr inbounds i16, i16* %r, i64 253 *)
(*   %1530 = load i16, i16* %arrayidx9.5.1.31, align 2, !tbaa !3 *)
mov v1530 mem0_506;
(*   %conv1.i.5.1.31 = sext i16 %1530 to i32 *)
cast v_conv1_i_5_1_31@sint32 v1530@sint16;
(*   %mul.i.5.1.31 = mul nsw i32 %conv1.i.5.1.31, -1275 *)
mul v_mul_i_5_1_31 v_conv1_i_5_1_31 (-1275)@sint32;
(*   %call.i.5.1.31 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.1.31) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_1_31, v_call_i_5_1_31);
(*   %arrayidx11.5.1.31 = getelementptr inbounds i16, i16* %r, i64 249 *)
(*   %1531 = load i16, i16* %arrayidx11.5.1.31, align 2, !tbaa !3 *)
mov v1531 mem0_498;
(*   %sub.5.1.31 = sub i16 %1531, %call.i.5.1.31 *)
sub v_sub_5_1_31 v1531 v_call_i_5_1_31;
(*   store i16 %sub.5.1.31, i16* %arrayidx9.5.1.31, align 2, !tbaa !3 *)
mov mem0_506 v_sub_5_1_31;
(*   %add21.5.1.31 = add i16 %1531, %call.i.5.1.31 *)
add v_add21_5_1_31 v1531 v_call_i_5_1_31;
(*   store i16 %add21.5.1.31, i16* %arrayidx11.5.1.31, align 2, !tbaa !3 *)
mov mem0_498 v_add21_5_1_31;
(*   %arrayidx9.5.2.31 = getelementptr inbounds i16, i16* %r, i64 254 *)
(*   %1532 = load i16, i16* %arrayidx9.5.2.31, align 2, !tbaa !3 *)
mov v1532 mem0_508;
(*   %conv1.i.5.2.31 = sext i16 %1532 to i32 *)
cast v_conv1_i_5_2_31@sint32 v1532@sint16;
(*   %mul.i.5.2.31 = mul nsw i32 %conv1.i.5.2.31, -1275 *)
mul v_mul_i_5_2_31 v_conv1_i_5_2_31 (-1275)@sint32;
(*   %call.i.5.2.31 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.2.31) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_2_31, v_call_i_5_2_31);
(*   %arrayidx11.5.2.31 = getelementptr inbounds i16, i16* %r, i64 250 *)
(*   %1533 = load i16, i16* %arrayidx11.5.2.31, align 2, !tbaa !3 *)
mov v1533 mem0_500;
(*   %sub.5.2.31 = sub i16 %1533, %call.i.5.2.31 *)
sub v_sub_5_2_31 v1533 v_call_i_5_2_31;
(*   store i16 %sub.5.2.31, i16* %arrayidx9.5.2.31, align 2, !tbaa !3 *)
mov mem0_508 v_sub_5_2_31;
(*   %add21.5.2.31 = add i16 %1533, %call.i.5.2.31 *)
add v_add21_5_2_31 v1533 v_call_i_5_2_31;
(*   store i16 %add21.5.2.31, i16* %arrayidx11.5.2.31, align 2, !tbaa !3 *)
mov mem0_500 v_add21_5_2_31;
(*   %arrayidx9.5.3.31 = getelementptr inbounds i16, i16* %r, i64 255 *)
(*   %1534 = load i16, i16* %arrayidx9.5.3.31, align 2, !tbaa !3 *)
mov v1534 mem0_510;
(*   %conv1.i.5.3.31 = sext i16 %1534 to i32 *)
cast v_conv1_i_5_3_31@sint32 v1534@sint16;
(*   %mul.i.5.3.31 = mul nsw i32 %conv1.i.5.3.31, -1275 *)
mul v_mul_i_5_3_31 v_conv1_i_5_3_31 (-1275)@sint32;
(*   %call.i.5.3.31 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5.3.31) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5_3_31, v_call_i_5_3_31);
(*   %arrayidx11.5.3.31 = getelementptr inbounds i16, i16* %r, i64 251 *)
(*   %1535 = load i16, i16* %arrayidx11.5.3.31, align 2, !tbaa !3 *)
mov v1535 mem0_502;
(*   %sub.5.3.31 = sub i16 %1535, %call.i.5.3.31 *)
sub v_sub_5_3_31 v1535 v_call_i_5_3_31;
(*   store i16 %sub.5.3.31, i16* %arrayidx9.5.3.31, align 2, !tbaa !3 *)
mov mem0_510 v_sub_5_3_31;
(*   %add21.5.3.31 = add i16 %1535, %call.i.5.3.31 *)
add v_add21_5_3_31 v1535 v_call_i_5_3_31;
(*   store i16 %add21.5.3.31, i16* %arrayidx11.5.3.31, align 2, !tbaa !3 *)
mov mem0_502 v_add21_5_3_31;

{
and [ 
eqmod 
(
mem0_0_k31*(x**0) + mem0_2_k31*(x**1) + mem0_4_k31*(x**2) + mem0_6_k31*(x**3) +
mem0_8_k31*(x**4) + mem0_10_k31*(x**5) + mem0_12_k31*(x**6) + mem0_14_k31*(x**7) 
)
(
mem0_0*(x**0) + mem0_2*(x**1) + mem0_4*(x**2) + mem0_6*(x**3)
)
[3329, x**4 - 289],
eqmod 
(
mem0_0_k31*(x**0) + mem0_2_k31*(x**1) + mem0_4_k31*(x**2) + mem0_6_k31*(x**3) +
mem0_8_k31*(x**4) + mem0_10_k31*(x**5) + mem0_12_k31*(x**6) + mem0_14_k31*(x**7) 
)
(
mem0_8*(x**0) + mem0_10*(x**1) + mem0_12*(x**2) + mem0_14*(x**3)
)
[3329, x**4 - 3040],
eqmod 
(
mem0_16_k31*(x**0) + mem0_18_k31*(x**1) + mem0_20_k31*(x**2) + mem0_22_k31*(x**3) +
mem0_24_k31*(x**4) + mem0_26_k31*(x**5) + mem0_28_k31*(x**6) + mem0_30_k31*(x**7)
)
(
mem0_16*(x**0) + mem0_18*(x**1) + mem0_20*(x**2) + mem0_22*(x**3)
)
[3329, x**4 - 331],
eqmod 
(
mem0_16_k31*(x**0) + mem0_18_k31*(x**1) + mem0_20_k31*(x**2) + mem0_22_k31*(x**3) +
mem0_24_k31*(x**4) + mem0_26_k31*(x**5) + mem0_28_k31*(x**6) + mem0_30_k31*(x**7)
)
(
mem0_24*(x**0) + mem0_26*(x**1) + mem0_28*(x**2) + mem0_30*(x**3)
)
[3329, x**4 - 2998],
eqmod 
(
mem0_32_k31*(x**0) + mem0_34_k31*(x**1) + mem0_36_k31*(x**2) + mem0_38_k31*(x**3) +
mem0_40_k31*(x**4) + mem0_42_k31*(x**5) + mem0_44_k31*(x**6) + mem0_46_k31*(x**7) 
)
(
mem0_32*(x**0) + mem0_34*(x**1) + mem0_36*(x**2) + mem0_38*(x**3)
)
[3329, x**4 - 3253],
eqmod 
(
mem0_32_k31*(x**0) + mem0_34_k31*(x**1) + mem0_36_k31*(x**2) + mem0_38_k31*(x**3) +
mem0_40_k31*(x**4) + mem0_42_k31*(x**5) + mem0_44_k31*(x**6) + mem0_46_k31*(x**7) 
)
(
mem0_40*(x**0) + mem0_42*(x**1) + mem0_44*(x**2) + mem0_46*(x**3)
)
[3329, x**4 - 76],
eqmod 
(
mem0_48_k31*(x**0) + mem0_50_k31*(x**1) + mem0_52_k31*(x**2) + mem0_54_k31*(x**3) +
mem0_56_k31*(x**4) + mem0_58_k31*(x**5) + mem0_60_k31*(x**6) + mem0_62_k31*(x**7)
)
(
mem0_48*(x**0) + mem0_50*(x**1) + mem0_52*(x**2) + mem0_54*(x**3)
)
[3329, x**4 - 1756],
eqmod 
(
mem0_48_k31*(x**0) + mem0_50_k31*(x**1) + mem0_52_k31*(x**2) + mem0_54_k31*(x**3) +
mem0_56_k31*(x**4) + mem0_58_k31*(x**5) + mem0_60_k31*(x**6) + mem0_62_k31*(x**7)
)
(
mem0_56*(x**0) + mem0_58*(x**1) + mem0_60*(x**2) + mem0_62*(x**3)
)
[3329, x**4 - 1573],
eqmod 
(
mem0_64_k31*(x**0) + mem0_66_k31*(x**1) + mem0_68_k31*(x**2) + mem0_70_k31*(x**3) +
mem0_72_k31*(x**4) + mem0_74_k31*(x**5) + mem0_76_k31*(x**6) + mem0_78_k31*(x**7)
)
(
mem0_64*(x**0) + mem0_66*(x**1) + mem0_68*(x**2) + mem0_70*(x**3)
)
[3329, x**4 - 1197],
eqmod 
(
mem0_64_k31*(x**0) + mem0_66_k31*(x**1) + mem0_68_k31*(x**2) + mem0_70_k31*(x**3) +
mem0_72_k31*(x**4) + mem0_74_k31*(x**5) + mem0_76_k31*(x**6) + mem0_78_k31*(x**7)
)
(
mem0_72*(x**0) + mem0_74*(x**1) + mem0_76*(x**2) + mem0_78*(x**3)
)
[3329, x**4 - 2132],
eqmod 
(
mem0_80_k31*(x**0) + mem0_82_k31*(x**1) + mem0_84_k31*(x**2) + mem0_86_k31*(x**3) +
mem0_88_k31*(x**4) + mem0_90_k31*(x**5) + mem0_92_k31*(x**6) + mem0_94_k31*(x**7)
)
(
mem0_80*(x**0) + mem0_82*(x**1) + mem0_84*(x**2) + mem0_86*(x**3)
)
[3329, x**4 - 2304],
eqmod 
(
mem0_80_k31*(x**0) + mem0_82_k31*(x**1) + mem0_84_k31*(x**2) + mem0_86_k31*(x**3) +
mem0_88_k31*(x**4) + mem0_90_k31*(x**5) + mem0_92_k31*(x**6) + mem0_94_k31*(x**7)
)
(
mem0_88*(x**0) + mem0_90*(x**1) + mem0_92*(x**2) + mem0_94*(x**3)
)
[3329, x**4 - 1025],
eqmod 
(
mem0_96_k31*(x**0) + mem0_98_k31*(x**1) + mem0_100_k31*(x**2) + mem0_102_k31*(x**3) +
mem0_104_k31*(x**4) + mem0_106_k31*(x**5) + mem0_108_k31*(x**6) + mem0_110_k31*(x**7)
)
(
mem0_96*(x**0) + mem0_98*(x**1) + mem0_100*(x**2) + mem0_102*(x**3)
)
[3329, x**4 - 2277],
eqmod 
(
mem0_96_k31*(x**0) + mem0_98_k31*(x**1) + mem0_100_k31*(x**2) + mem0_102_k31*(x**3) +
mem0_104_k31*(x**4) + mem0_106_k31*(x**5) + mem0_108_k31*(x**6) + mem0_110_k31*(x**7)
)
(
mem0_104*(x**0) + mem0_106*(x**1) + mem0_108*(x**2) + mem0_110*(x**3)
)
[3329, x**4 - 1052],
eqmod 
(
mem0_112_k31*(x**0) + mem0_114_k31*(x**1) + mem0_116_k31*(x**2) + mem0_118_k31*(x**3) +
mem0_120_k31*(x**4) + mem0_122_k31*(x**5) + mem0_124_k31*(x**6) + mem0_126_k31*(x**7)
)
(
mem0_112*(x**0) + mem0_114*(x**1) + mem0_116*(x**2) + mem0_118*(x**3)
)
[3329, x**4 - 2055],
eqmod 
(
mem0_112_k31*(x**0) + mem0_114_k31*(x**1) + mem0_116_k31*(x**2) + mem0_118_k31*(x**3) +
mem0_120_k31*(x**4) + mem0_122_k31*(x**5) + mem0_124_k31*(x**6) + mem0_126_k31*(x**7)
)
(
mem0_120*(x**0) + mem0_122*(x**1) + mem0_124*(x**2) + mem0_126*(x**3)
)
[3329, x**4 - 1274],
eqmod 
(
mem0_128_k31*(x**0) + mem0_130_k31*(x**1) + mem0_132_k31*(x**2) + mem0_134_k31*(x**3) +
mem0_136_k31*(x**4) + mem0_138_k31*(x**5) + mem0_140_k31*(x**6) + mem0_142_k31*(x**7)
)
(
mem0_128*(x**0) + mem0_130*(x**1) + mem0_132*(x**2) + mem0_134*(x**3)
)
[3329, x**4 - 650],
eqmod 
(
mem0_128_k31*(x**0) + mem0_130_k31*(x**1) + mem0_132_k31*(x**2) + mem0_134_k31*(x**3) +
mem0_136_k31*(x**4) + mem0_138_k31*(x**5) + mem0_140_k31*(x**6) + mem0_142_k31*(x**7)
)
(
mem0_136*(x**0) + mem0_138*(x**1) + mem0_140*(x**2) + mem0_142*(x**3)
)
[3329, x**4 - 2679],
eqmod 
(
mem0_144_k31*(x**0) + mem0_146_k31*(x**1) + mem0_148_k31*(x**2) + mem0_150_k31*(x**3) +
mem0_152_k31*(x**4) + mem0_154_k31*(x**5) + mem0_156_k31*(x**6) + mem0_158_k31*(x**7)
)
(
mem0_144*(x**0) + mem0_146*(x**1) + mem0_148*(x**2) + mem0_150*(x**3)
)
[3329, x**4 - 1977],
eqmod 
(
mem0_144_k31*(x**0) + mem0_146_k31*(x**1) + mem0_148_k31*(x**2) + mem0_150_k31*(x**3) +
mem0_152_k31*(x**4) + mem0_154_k31*(x**5) + mem0_156_k31*(x**6) + mem0_158_k31*(x**7)
)
(
mem0_152*(x**0) + mem0_154*(x**1) + mem0_156*(x**2) + mem0_158*(x**3)
)
[3329, x**4 - 1352],
eqmod 
(
mem0_160_k31*(x**0) + mem0_162_k31*(x**1) + mem0_164_k31*(x**2) + mem0_166_k31*(x**3) +
mem0_168_k31*(x**4) + mem0_170_k31*(x**5) + mem0_172_k31*(x**6) + mem0_174_k31*(x**7)
)
(
mem0_160*(x**0) + mem0_162*(x**1) + mem0_164*(x**2) + mem0_166*(x**3)
)
[3329, x**4 - 2513],
eqmod 
(
mem0_160_k31*(x**0) + mem0_162_k31*(x**1) + mem0_164_k31*(x**2) + mem0_166_k31*(x**3) +
mem0_168_k31*(x**4) + mem0_170_k31*(x**5) + mem0_172_k31*(x**6) + mem0_174_k31*(x**7)
)
(
mem0_168*(x**0) + mem0_170*(x**1) + mem0_172*(x**2) + mem0_174*(x**3)
)
[3329, x**4 - 816],
eqmod 
(
mem0_176_k31*(x**0) + mem0_178_k31*(x**1) + mem0_180_k31*(x**2) + mem0_182_k31*(x**3) +
mem0_184_k31*(x**4) + mem0_186_k31*(x**5) + mem0_188_k31*(x**6) + mem0_190_k31*(x**7)
)
(
mem0_176*(x**0) + mem0_178*(x**1) + mem0_180*(x**2) + mem0_182*(x**3)
)
[3329, x**4 - 632],
eqmod 
(
mem0_176_k31*(x**0) + mem0_178_k31*(x**1) + mem0_180_k31*(x**2) + mem0_182_k31*(x**3) +
mem0_184_k31*(x**4) + mem0_186_k31*(x**5) + mem0_188_k31*(x**6) + mem0_190_k31*(x**7)
)
(
mem0_184*(x**0) + mem0_186*(x**1) + mem0_188*(x**2) + mem0_190*(x**3)
)
[3329, x**4 - 2697],
eqmod 
(
mem0_192_k31*(x**0) + mem0_194_k31*(x**1) + mem0_196_k31*(x**2) + mem0_198_k31*(x**3) +
mem0_200_k31*(x**4) + mem0_202_k31*(x**5) + mem0_204_k31*(x**6) + mem0_206_k31*(x**7)
)
(
mem0_192*(x**0) + mem0_194*(x**1) + mem0_196*(x**2) + mem0_198*(x**3)
)
[3329, x**4 - 2865],
eqmod 
(
mem0_192_k31*(x**0) + mem0_194_k31*(x**1) + mem0_196_k31*(x**2) + mem0_198_k31*(x**3) +
mem0_200_k31*(x**4) + mem0_202_k31*(x**5) + mem0_204_k31*(x**6) + mem0_206_k31*(x**7)
)
(
mem0_200*(x**0) + mem0_202*(x**1) + mem0_204*(x**2) + mem0_206*(x**3)
)
[3329, x**4 - 464],
eqmod 
(
mem0_208_k31*(x**0) + mem0_210_k31*(x**1) + mem0_212_k31*(x**2) + mem0_214_k31*(x**3) +
mem0_216_k31*(x**4) + mem0_218_k31*(x**5) + mem0_220_k31*(x**6) + mem0_222_k31*(x**7)
)
(
mem0_208*(x**0) + mem0_210*(x**1) + mem0_212*(x**2) + mem0_214*(x**3)
)
[3329, x**4 - 33],
eqmod 
(
mem0_208_k31*(x**0) + mem0_210_k31*(x**1) + mem0_212_k31*(x**2) + mem0_214_k31*(x**3) +
mem0_216_k31*(x**4) + mem0_218_k31*(x**5) + mem0_220_k31*(x**6) + mem0_222_k31*(x**7)
)
(
mem0_216*(x**0) + mem0_218*(x**1) + mem0_220*(x**2) + mem0_222*(x**3)
)
[3329, x**4 - 3296],
eqmod 
(
mem0_224_k31*(x**0) + mem0_226_k31*(x**1) + mem0_228_k31*(x**2) + mem0_230_k31*(x**3) +
mem0_232_k31*(x**4) + mem0_234_k31*(x**5) + mem0_236_k31*(x**6) + mem0_238_k31*(x**7)
)
(
mem0_224*(x**0) + mem0_226*(x**1) + mem0_228*(x**2) + mem0_230*(x**3)
)
[3329, x**4 - 1320],
eqmod 
(
mem0_224_k31*(x**0) + mem0_226_k31*(x**1) + mem0_228_k31*(x**2) + mem0_230_k31*(x**3) +
mem0_232_k31*(x**4) + mem0_234_k31*(x**5) + mem0_236_k31*(x**6) + mem0_238_k31*(x**7)
)
(
mem0_232*(x**0) + mem0_234*(x**1) + mem0_236*(x**2) + mem0_238*(x**3)
)
[3329, x**4 - 2009],
eqmod 
(
mem0_240_k31*(x**0) + mem0_242_k31*(x**1) + mem0_244_k31*(x**2) + mem0_246_k31*(x**3) +
mem0_248_k31*(x**4) + mem0_250_k31*(x**5) + mem0_252_k31*(x**6) + mem0_254_k31*(x**7)
)
(
mem0_240*(x**0) + mem0_242*(x**1) + mem0_244*(x**2) + mem0_246*(x**3)
)
[3329, x**4 - 1915],
eqmod 
(
mem0_240_k31*(x**0) + mem0_242_k31*(x**1) + mem0_244_k31*(x**2) + mem0_246_k31*(x**3) +
mem0_248_k31*(x**4) + mem0_250_k31*(x**5) + mem0_252_k31*(x**6) + mem0_254_k31*(x**7)
)
(
mem0_248*(x**0) + mem0_250*(x**1) + mem0_252*(x**2) + mem0_254*(x**3)
)
[3329, x**4 - 1414],
eqmod 
(
mem0_256_k31*(x**0) + mem0_258_k31*(x**1) + mem0_260_k31*(x**2) + mem0_262_k31*(x**3) +
mem0_264_k31*(x**4) + mem0_266_k31*(x**5) + mem0_268_k31*(x**6) + mem0_270_k31*(x**7)
)
(
mem0_256*(x**0) + mem0_258*(x**1) + mem0_260*(x**2) + mem0_262*(x**3)
)
[3329, x**4 - 2319],
eqmod 
(
mem0_256_k31*(x**0) + mem0_258_k31*(x**1) + mem0_260_k31*(x**2) + mem0_262_k31*(x**3) +
mem0_264_k31*(x**4) + mem0_266_k31*(x**5) + mem0_268_k31*(x**6) + mem0_270_k31*(x**7)
)
(
mem0_264*(x**0) + mem0_266*(x**1) + mem0_268*(x**2) + mem0_270*(x**3)
)
[3329, x**4 - 1010],
eqmod 
(
mem0_272_k31*(x**0) + mem0_274_k31*(x**1) + mem0_276_k31*(x**2) + mem0_278_k31*(x**3) +
mem0_280_k31*(x**4) + mem0_282_k31*(x**5) + mem0_284_k31*(x**6) + mem0_286_k31*(x**7)
)
(
mem0_272*(x**0) + mem0_274*(x**1) + mem0_276*(x**2) + mem0_278*(x**3)
)
[3329, x**4 - 1435],
eqmod 
(
mem0_272_k31*(x**0) + mem0_274_k31*(x**1) + mem0_276_k31*(x**2) + mem0_278_k31*(x**3) +
mem0_280_k31*(x**4) + mem0_282_k31*(x**5) + mem0_284_k31*(x**6) + mem0_286_k31*(x**7)
)
(
mem0_280*(x**0) + mem0_282*(x**1) + mem0_284*(x**2) + mem0_286*(x**3)
)
[3329, x**4 - 1894],
eqmod 
(
mem0_288_k31*(x**0) + mem0_290_k31*(x**1) + mem0_292_k31*(x**2) + mem0_294_k31*(x**3) +
mem0_296_k31*(x**4) + mem0_298_k31*(x**5) + mem0_300_k31*(x**6) + mem0_302_k31*(x**7)
)
(
mem0_288*(x**0) + mem0_290*(x**1) + mem0_292*(x**2) + mem0_294*(x**3)
)
[3329, x**4 - 807],
eqmod 
(
mem0_288_k31*(x**0) + mem0_290_k31*(x**1) + mem0_292_k31*(x**2) + mem0_294_k31*(x**3) +
mem0_296_k31*(x**4) + mem0_298_k31*(x**5) + mem0_300_k31*(x**6) + mem0_302_k31*(x**7)
)
(
mem0_296*(x**0) + mem0_298*(x**1) + mem0_300*(x**2) + mem0_302*(x**3)
)
[3329, x**4 - 2522],
eqmod 
(
mem0_304_k31*(x**0) + mem0_306_k31*(x**1) + mem0_308_k31*(x**2) + mem0_310_k31*(x**3) +
mem0_312_k31*(x**4) + mem0_314_k31*(x**5) + mem0_316_k31*(x**6) + mem0_318_k31*(x**7)
)
(
mem0_304*(x**0) + mem0_306*(x**1) + mem0_308*(x**2) + mem0_310*(x**3)
)
[3329, x**4 - 452],
eqmod 
(
mem0_304_k31*(x**0) + mem0_306_k31*(x**1) + mem0_308_k31*(x**2) + mem0_310_k31*(x**3) +
mem0_312_k31*(x**4) + mem0_314_k31*(x**5) + mem0_316_k31*(x**6) + mem0_318_k31*(x**7)
)
(
mem0_312*(x**0) + mem0_314*(x**1) + mem0_316*(x**2) + mem0_318*(x**3)
)
[3329, x**4 - 2877],
eqmod 
(
mem0_320_k31*(x**0) + mem0_322_k31*(x**1) + mem0_324_k31*(x**2) + mem0_326_k31*(x**3) +
mem0_328_k31*(x**4) + mem0_330_k31*(x**5) + mem0_332_k31*(x**6) + mem0_334_k31*(x**7)
)
(
mem0_320*(x**0) + mem0_322*(x**1) + mem0_324*(x**2) + mem0_326*(x**3)
)
[3329, x**4 - 1438],
eqmod 
(
mem0_320_k31*(x**0) + mem0_322_k31*(x**1) + mem0_324_k31*(x**2) + mem0_326_k31*(x**3) +
mem0_328_k31*(x**4) + mem0_330_k31*(x**5) + mem0_332_k31*(x**6) + mem0_334_k31*(x**7)
)
(
mem0_328*(x**0) + mem0_330*(x**1) + mem0_332*(x**2) + mem0_334*(x**3)
)
[3329, x**4 - 1891],
eqmod 
(
mem0_336_k31*(x**0) + mem0_338_k31*(x**1) + mem0_340_k31*(x**2) + mem0_342_k31*(x**3) +
mem0_344_k31*(x**4) + mem0_346_k31*(x**5) + mem0_348_k31*(x**6) + mem0_350_k31*(x**7)
)
(
mem0_336*(x**0) + mem0_338*(x**1) + mem0_340*(x**2) + mem0_342*(x**3)
)
[3329, x**4 - 2868],
eqmod 
(
mem0_336_k31*(x**0) + mem0_338_k31*(x**1) + mem0_340_k31*(x**2) + mem0_342_k31*(x**3) +
mem0_344_k31*(x**4) + mem0_346_k31*(x**5) + mem0_348_k31*(x**6) + mem0_350_k31*(x**7)
)
(
mem0_344*(x**0) + mem0_346*(x**1) + mem0_348*(x**2) + mem0_350*(x**3)
)
[3329, x**4 - 461],
eqmod 
(
mem0_352_k31*(x**0) + mem0_354_k31*(x**1) + mem0_356_k31*(x**2) + mem0_358_k31*(x**3) +
mem0_360_k31*(x**4) + mem0_362_k31*(x**5) + mem0_364_k31*(x**6) + mem0_366_k31*(x**7)
)
(
mem0_352*(x**0) + mem0_354*(x**1) + mem0_356*(x**2) + mem0_358*(x**3)
)
[3329, x**4 - 1534],
eqmod 
(
mem0_352_k31*(x**0) + mem0_354_k31*(x**1) + mem0_356_k31*(x**2) + mem0_358_k31*(x**3) +
mem0_360_k31*(x**4) + mem0_362_k31*(x**5) + mem0_364_k31*(x**6) + mem0_366_k31*(x**7)
)
(
mem0_360*(x**0) + mem0_362*(x**1) + mem0_364*(x**2) + mem0_366*(x**3)
)
[3329, x**4 - 1795],
eqmod 
(
mem0_368_k31*(x**0) + mem0_370_k31*(x**1) + mem0_372_k31*(x**2) + mem0_374_k31*(x**3) +
mem0_376_k31*(x**4) + mem0_378_k31*(x**5) + mem0_380_k31*(x**6) + mem0_382_k31*(x**7)
)
(
mem0_368*(x**0) + mem0_370*(x**1) + mem0_372*(x**2) + mem0_374*(x**3)
)
[3329, x**4 - 2402],
eqmod 
(
mem0_368_k31*(x**0) + mem0_370_k31*(x**1) + mem0_372_k31*(x**2) + mem0_374_k31*(x**3) +
mem0_376_k31*(x**4) + mem0_378_k31*(x**5) + mem0_380_k31*(x**6) + mem0_382_k31*(x**7)
)
(
mem0_376*(x**0) + mem0_378*(x**1) + mem0_380*(x**2) + mem0_382*(x**3)
)
[3329, x**4 - 927],
eqmod 
(
mem0_384_k31*(x**0) + mem0_386_k31*(x**1) + mem0_388_k31*(x**2) + mem0_390_k31*(x**3) +
mem0_392_k31*(x**4) + mem0_394_k31*(x**5) + mem0_396_k31*(x**6) + mem0_398_k31*(x**7)
)
(
mem0_384*(x**0) + mem0_386*(x**1) + mem0_388*(x**2) + mem0_390*(x**3)
)
[3329, x**4 - 2647],
eqmod 
(
mem0_384_k31*(x**0) + mem0_386_k31*(x**1) + mem0_388_k31*(x**2) + mem0_390_k31*(x**3) +
mem0_392_k31*(x**4) + mem0_394_k31*(x**5) + mem0_396_k31*(x**6) + mem0_398_k31*(x**7)
)
(
mem0_392*(x**0) + mem0_394*(x**1) + mem0_396*(x**2) + mem0_398*(x**3)
)
[3329, x**4 - 682],
eqmod 
(
mem0_400_k31*(x**0) + mem0_402_k31*(x**1) + mem0_404_k31*(x**2) + mem0_406_k31*(x**3) +
mem0_408_k31*(x**4) + mem0_410_k31*(x**5) + mem0_412_k31*(x**6) + mem0_414_k31*(x**7)
)
(
mem0_400*(x**0) + mem0_402*(x**1) + mem0_404*(x**2) + mem0_406*(x**3)
)
[3329, x**4 - 2617],
eqmod 
(
mem0_400_k31*(x**0) + mem0_402_k31*(x**1) + mem0_404_k31*(x**2) + mem0_406_k31*(x**3) +
mem0_408_k31*(x**4) + mem0_410_k31*(x**5) + mem0_412_k31*(x**6) + mem0_414_k31*(x**7)
)
(
mem0_408*(x**0) + mem0_410*(x**1) + mem0_412*(x**2) + mem0_414*(x**3)
)
[3329, x**4 - 712],
eqmod 
(
mem0_416_k31*(x**0) + mem0_418_k31*(x**1) + mem0_420_k31*(x**2) + mem0_422_k31*(x**3) +
mem0_424_k31*(x**4) + mem0_426_k31*(x**5) + mem0_428_k31*(x**6) + mem0_430_k31*(x**7)
)
(
mem0_416*(x**0) + mem0_418*(x**1) + mem0_420*(x**2) + mem0_422*(x**3)
)
[3329, x**4 - 1481],
eqmod 
(
mem0_416_k31*(x**0) + mem0_418_k31*(x**1) + mem0_420_k31*(x**2) + mem0_422_k31*(x**3) +
mem0_424_k31*(x**4) + mem0_426_k31*(x**5) + mem0_428_k31*(x**6) + mem0_430_k31*(x**7)
)
(
mem0_424*(x**0) + mem0_426*(x**1) + mem0_428*(x**2) + mem0_430*(x**3)
)
[3329, x**4 - 1848],
eqmod 
(
mem0_432_k31*(x**0) + mem0_434_k31*(x**1) + mem0_436_k31*(x**2) + mem0_438_k31*(x**3) +
mem0_440_k31*(x**4) + mem0_442_k31*(x**5) + mem0_444_k31*(x**6) + mem0_446_k31*(x**7)
)
(
mem0_432*(x**0) + mem0_434*(x**1) + mem0_436*(x**2) + mem0_438*(x**3)
)
[3329, x**4 - 648],
eqmod 
(
mem0_432_k31*(x**0) + mem0_434_k31*(x**1) + mem0_436_k31*(x**2) + mem0_438_k31*(x**3) +
mem0_440_k31*(x**4) + mem0_442_k31*(x**5) + mem0_444_k31*(x**6) + mem0_446_k31*(x**7)
)
(
mem0_440*(x**0) + mem0_442*(x**1) + mem0_444*(x**2) + mem0_446*(x**3)
)
[3329, x**4 - 2681],
eqmod 
(
mem0_448_k31*(x**0) + mem0_450_k31*(x**1) + mem0_452_k31*(x**2) + mem0_454_k31*(x**3) +
mem0_456_k31*(x**4) + mem0_458_k31*(x**5) + mem0_460_k31*(x**6) + mem0_462_k31*(x**7)
)
(
mem0_448*(x**0) + mem0_450*(x**1) + mem0_452*(x**2) + mem0_454*(x**3)
)
[3329, x**4 - 2474],
eqmod 
(
mem0_448_k31*(x**0) + mem0_450_k31*(x**1) + mem0_452_k31*(x**2) + mem0_454_k31*(x**3) +
mem0_456_k31*(x**4) + mem0_458_k31*(x**5) + mem0_460_k31*(x**6) + mem0_462_k31*(x**7)
)
(
mem0_456*(x**0) + mem0_458*(x**1) + mem0_460*(x**2) + mem0_462*(x**3)
)
[3329, x**4 - 855],
eqmod 
(
mem0_464_k31*(x**0) + mem0_466_k31*(x**1) + mem0_468_k31*(x**2) + mem0_470_k31*(x**3) +
mem0_472_k31*(x**4) + mem0_474_k31*(x**5) + mem0_476_k31*(x**6) + mem0_478_k31*(x**7)
)
(
mem0_464*(x**0) + mem0_466*(x**1) + mem0_468*(x**2) + mem0_470*(x**3)
)
[3329, x**4 - 3110],
eqmod 
(
mem0_464_k31*(x**0) + mem0_466_k31*(x**1) + mem0_468_k31*(x**2) + mem0_470_k31*(x**3) +
mem0_472_k31*(x**4) + mem0_474_k31*(x**5) + mem0_476_k31*(x**6) + mem0_478_k31*(x**7)
)
(
mem0_472*(x**0) + mem0_474*(x**1) + mem0_476*(x**2) + mem0_478*(x**3)
)
[3329, x**4 - 219],
eqmod 
(
mem0_480_k31*(x**0) + mem0_482_k31*(x**1) + mem0_484_k31*(x**2) + mem0_486_k31*(x**3) +
mem0_488_k31*(x**4) + mem0_490_k31*(x**5) + mem0_492_k31*(x**6) + mem0_494_k31*(x**7)
)
(
mem0_480*(x**0) + mem0_482*(x**1) + mem0_484*(x**2) + mem0_486*(x**3)
)
[3329, x**4 - 1227],
eqmod 
(
mem0_480_k31*(x**0) + mem0_482_k31*(x**1) + mem0_484_k31*(x**2) + mem0_486_k31*(x**3) +
mem0_488_k31*(x**4) + mem0_490_k31*(x**5) + mem0_492_k31*(x**6) + mem0_494_k31*(x**7)
)
(
mem0_488*(x**0) + mem0_490*(x**1) + mem0_492*(x**2) + mem0_494*(x**3)
)
[3329, x**4 - 2102],
eqmod 
(
mem0_496_k31*(x**0) + mem0_498_k31*(x**1) + mem0_500_k31*(x**2) + mem0_502_k31*(x**3) +
mem0_504_k31*(x**4) + mem0_506_k31*(x**5) + mem0_508_k31*(x**6) + mem0_510_k31*(x**7)
)
(
mem0_496*(x**0) + mem0_498*(x**1) + mem0_500*(x**2) + mem0_502*(x**3)
)
[3329, x**4 - 910],
eqmod 
(
mem0_496_k31*(x**0) + mem0_498_k31*(x**1) + mem0_500_k31*(x**2) + mem0_502_k31*(x**3) +
mem0_504_k31*(x**4) + mem0_506_k31*(x**5) + mem0_508_k31*(x**6) + mem0_510_k31*(x**7)
)
(
mem0_504*(x**0) + mem0_506*(x**1) + mem0_508*(x**2) + mem0_510*(x**3)
)
[3329, x**4 - 2419]
] && and [
   (-8)@16 * 3329@16 <s mem0_0, mem0_0 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_2, mem0_2 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_4, mem0_4 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_6, mem0_6 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_8, mem0_8 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_10, mem0_10 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_12, mem0_12 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_14, mem0_14 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_16, mem0_16 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_18, mem0_18 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_20, mem0_20 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_22, mem0_22 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_24, mem0_24 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_26, mem0_26 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_28, mem0_28 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_30, mem0_30 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_32, mem0_32 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_34, mem0_34 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_36, mem0_36 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_38, mem0_38 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_40, mem0_40 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_42, mem0_42 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_44, mem0_44 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_46, mem0_46 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_48, mem0_48 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_50, mem0_50 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_52, mem0_52 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_54, mem0_54 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_56, mem0_56 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_58, mem0_58 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_60, mem0_60 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_62, mem0_62 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_64, mem0_64 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_66, mem0_66 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_68, mem0_68 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_70, mem0_70 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_72, mem0_72 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_74, mem0_74 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_76, mem0_76 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_78, mem0_78 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_80, mem0_80 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_82, mem0_82 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_84, mem0_84 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_86, mem0_86 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_88, mem0_88 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_90, mem0_90 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_92, mem0_92 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_94, mem0_94 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_96, mem0_96 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_98, mem0_98 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_100, mem0_100 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_102, mem0_102 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_104, mem0_104 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_106, mem0_106 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_108, mem0_108 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_110, mem0_110 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_112, mem0_112 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_114, mem0_114 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_116, mem0_116 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_118, mem0_118 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_120, mem0_120 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_122, mem0_122 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_124, mem0_124 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_126, mem0_126 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_128, mem0_128 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_130, mem0_130 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_132, mem0_132 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_134, mem0_134 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_136, mem0_136 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_138, mem0_138 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_140, mem0_140 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_142, mem0_142 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_144, mem0_144 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_146, mem0_146 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_148, mem0_148 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_150, mem0_150 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_152, mem0_152 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_154, mem0_154 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_156, mem0_156 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_158, mem0_158 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_160, mem0_160 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_162, mem0_162 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_164, mem0_164 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_166, mem0_166 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_168, mem0_168 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_170, mem0_170 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_172, mem0_172 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_174, mem0_174 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_176, mem0_176 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_178, mem0_178 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_180, mem0_180 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_182, mem0_182 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_184, mem0_184 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_186, mem0_186 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_188, mem0_188 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_190, mem0_190 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_192, mem0_192 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_194, mem0_194 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_196, mem0_196 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_198, mem0_198 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_200, mem0_200 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_202, mem0_202 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_204, mem0_204 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_206, mem0_206 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_208, mem0_208 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_210, mem0_210 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_212, mem0_212 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_214, mem0_214 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_216, mem0_216 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_218, mem0_218 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_220, mem0_220 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_222, mem0_222 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_224, mem0_224 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_226, mem0_226 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_228, mem0_228 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_230, mem0_230 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_232, mem0_232 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_234, mem0_234 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_236, mem0_236 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_238, mem0_238 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_240, mem0_240 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_242, mem0_242 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_244, mem0_244 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_246, mem0_246 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_248, mem0_248 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_250, mem0_250 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_252, mem0_252 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_254, mem0_254 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_256, mem0_256 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_258, mem0_258 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_260, mem0_260 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_262, mem0_262 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_264, mem0_264 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_266, mem0_266 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_268, mem0_268 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_270, mem0_270 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_272, mem0_272 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_274, mem0_274 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_276, mem0_276 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_278, mem0_278 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_280, mem0_280 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_282, mem0_282 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_284, mem0_284 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_286, mem0_286 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_288, mem0_288 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_290, mem0_290 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_292, mem0_292 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_294, mem0_294 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_296, mem0_296 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_298, mem0_298 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_300, mem0_300 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_302, mem0_302 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_304, mem0_304 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_306, mem0_306 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_308, mem0_308 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_310, mem0_310 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_312, mem0_312 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_314, mem0_314 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_316, mem0_316 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_318, mem0_318 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_320, mem0_320 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_322, mem0_322 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_324, mem0_324 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_326, mem0_326 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_328, mem0_328 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_330, mem0_330 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_332, mem0_332 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_334, mem0_334 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_336, mem0_336 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_338, mem0_338 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_340, mem0_340 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_342, mem0_342 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_344, mem0_344 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_346, mem0_346 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_348, mem0_348 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_350, mem0_350 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_352, mem0_352 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_354, mem0_354 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_356, mem0_356 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_358, mem0_358 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_360, mem0_360 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_362, mem0_362 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_364, mem0_364 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_366, mem0_366 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_368, mem0_368 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_370, mem0_370 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_372, mem0_372 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_374, mem0_374 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_376, mem0_376 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_378, mem0_378 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_380, mem0_380 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_382, mem0_382 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_384, mem0_384 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_386, mem0_386 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_388, mem0_388 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_390, mem0_390 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_392, mem0_392 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_394, mem0_394 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_396, mem0_396 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_398, mem0_398 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_400, mem0_400 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_402, mem0_402 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_404, mem0_404 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_406, mem0_406 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_408, mem0_408 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_410, mem0_410 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_412, mem0_412 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_414, mem0_414 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_416, mem0_416 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_418, mem0_418 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_420, mem0_420 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_422, mem0_422 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_424, mem0_424 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_426, mem0_426 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_428, mem0_428 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_430, mem0_430 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_432, mem0_432 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_434, mem0_434 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_436, mem0_436 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_438, mem0_438 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_440, mem0_440 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_442, mem0_442 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_444, mem0_444 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_446, mem0_446 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_448, mem0_448 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_450, mem0_450 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_452, mem0_452 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_454, mem0_454 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_456, mem0_456 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_458, mem0_458 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_460, mem0_460 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_462, mem0_462 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_464, mem0_464 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_466, mem0_466 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_468, mem0_468 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_470, mem0_470 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_472, mem0_472 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_474, mem0_474 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_476, mem0_476 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_478, mem0_478 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_480, mem0_480 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_482, mem0_482 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_484, mem0_484 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_486, mem0_486 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_488, mem0_488 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_490, mem0_490 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_492, mem0_492 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_494, mem0_494 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_496, mem0_496 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_498, mem0_498 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_500, mem0_500 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_502, mem0_502 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_504, mem0_504 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_506, mem0_506 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_508, mem0_508 <s 8@16 * 3329@16,
   (-8)@16 * 3329@16 <s mem0_510, mem0_510 <s 8@16 * 3329@16
]
}