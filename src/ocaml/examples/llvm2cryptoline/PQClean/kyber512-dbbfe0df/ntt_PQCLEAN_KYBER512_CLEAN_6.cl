(*
~/git/cryptoline/_build/default/cv.exe -v -no_carry_constraint -o coqcryptoline.log ~/git/llvm2cryptoline-draft_examples/examples/PQClean/kyber512-dbbfe0df/coqcv_ntt_k8_separated.cl 
Parsing CryptoLine file:		[OK]		0.161638 seconds
Checking well-formedness:		[OK]		0.010447 seconds
Transforming to SSA form:		[OK]		0.002266 seconds
Normalizing specification:		[OK]		0.001990 seconds
Rewriting assignments:			[OK]		0.001880 seconds
Verifying program safety:		[OK]		45.170213 seconds
Verifying range specification:		[OK]		51.871791 seconds
Rewriting value-preserved casting:	[OK]		0.000169 seconds
Verifying algebraic specification:	[OK]		4.768428 seconds
Verification result:			[OK]		101.991254 seconds

_build/default/coqcryptoline.exe -v -jobs 16 -sat_solver cadical -sat_cert grat -no_carry_constraint ~/tmp/coqcv_ntt_k8_separated.cl 
Results of checking CNF formulas:       [OK]            1111.191317 seconds
Finding polynomial coefficients
         Polynomials #8:                [DONE]          1137.626297 seconds
         Polynomials #12:               [DONE]          1140.850270 seconds
         Polynomials #0:                [DONE]          1148.809467 seconds
         Polynomials #1:                [DONE]          1152.682939 seconds
         Polynomials #13:               [DONE]          1158.630167 seconds
         Polynomials #5:                [DONE]          1159.106179 seconds
         Polynomials #7:                [DONE]          1163.170504 seconds
         Polynomials #11:               [DONE]          1168.374493 seconds
         Polynomials #14:               [DONE]          1169.829859 seconds
         Polynomials #6:                [DONE]          1172.573656 seconds
         Polynomials #15:               [DONE]          1176.696514 seconds
         Polynomials #10:               [DONE]          1178.350251 seconds
         Polynomials #2:                [DONE]          1178.420294 seconds
         Polynomials #9:                [DONE]          1181.463491 seconds
         Polynomials #4:                [DONE]          1185.312230 seconds
         Polynomials #3:                [DONE]          1188.598730 seconds
Finished finding polynomial coefficients                1189.138719 seconds
Verification result:                    [OK]            2834.521998 seconds
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

{
true

&& and [
   (-5)@16 * 3329@16 <s mem0_0, mem0_0 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_2, mem0_2 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_4, mem0_4 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_6, mem0_6 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_8, mem0_8 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_10, mem0_10 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_12, mem0_12 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_14, mem0_14 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_16, mem0_16 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_18, mem0_18 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_20, mem0_20 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_22, mem0_22 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_24, mem0_24 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_26, mem0_26 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_28, mem0_28 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_30, mem0_30 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_32, mem0_32 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_34, mem0_34 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_36, mem0_36 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_38, mem0_38 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_40, mem0_40 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_42, mem0_42 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_44, mem0_44 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_46, mem0_46 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_48, mem0_48 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_50, mem0_50 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_52, mem0_52 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_54, mem0_54 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_56, mem0_56 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_58, mem0_58 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_60, mem0_60 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_62, mem0_62 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_64, mem0_64 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_66, mem0_66 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_68, mem0_68 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_70, mem0_70 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_72, mem0_72 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_74, mem0_74 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_76, mem0_76 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_78, mem0_78 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_80, mem0_80 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_82, mem0_82 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_84, mem0_84 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_86, mem0_86 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_88, mem0_88 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_90, mem0_90 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_92, mem0_92 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_94, mem0_94 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_96, mem0_96 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_98, mem0_98 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_100, mem0_100 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_102, mem0_102 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_104, mem0_104 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_106, mem0_106 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_108, mem0_108 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_110, mem0_110 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_112, mem0_112 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_114, mem0_114 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_116, mem0_116 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_118, mem0_118 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_120, mem0_120 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_122, mem0_122 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_124, mem0_124 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_126, mem0_126 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_128, mem0_128 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_130, mem0_130 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_132, mem0_132 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_134, mem0_134 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_136, mem0_136 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_138, mem0_138 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_140, mem0_140 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_142, mem0_142 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_144, mem0_144 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_146, mem0_146 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_148, mem0_148 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_150, mem0_150 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_152, mem0_152 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_154, mem0_154 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_156, mem0_156 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_158, mem0_158 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_160, mem0_160 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_162, mem0_162 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_164, mem0_164 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_166, mem0_166 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_168, mem0_168 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_170, mem0_170 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_172, mem0_172 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_174, mem0_174 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_176, mem0_176 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_178, mem0_178 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_180, mem0_180 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_182, mem0_182 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_184, mem0_184 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_186, mem0_186 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_188, mem0_188 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_190, mem0_190 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_192, mem0_192 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_194, mem0_194 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_196, mem0_196 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_198, mem0_198 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_200, mem0_200 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_202, mem0_202 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_204, mem0_204 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_206, mem0_206 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_208, mem0_208 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_210, mem0_210 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_212, mem0_212 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_214, mem0_214 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_216, mem0_216 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_218, mem0_218 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_220, mem0_220 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_222, mem0_222 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_224, mem0_224 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_226, mem0_226 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_228, mem0_228 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_230, mem0_230 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_232, mem0_232 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_234, mem0_234 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_236, mem0_236 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_238, mem0_238 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_240, mem0_240 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_242, mem0_242 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_244, mem0_244 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_246, mem0_246 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_248, mem0_248 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_250, mem0_250 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_252, mem0_252 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_254, mem0_254 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_256, mem0_256 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_258, mem0_258 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_260, mem0_260 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_262, mem0_262 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_264, mem0_264 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_266, mem0_266 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_268, mem0_268 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_270, mem0_270 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_272, mem0_272 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_274, mem0_274 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_276, mem0_276 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_278, mem0_278 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_280, mem0_280 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_282, mem0_282 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_284, mem0_284 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_286, mem0_286 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_288, mem0_288 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_290, mem0_290 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_292, mem0_292 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_294, mem0_294 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_296, mem0_296 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_298, mem0_298 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_300, mem0_300 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_302, mem0_302 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_304, mem0_304 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_306, mem0_306 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_308, mem0_308 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_310, mem0_310 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_312, mem0_312 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_314, mem0_314 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_316, mem0_316 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_318, mem0_318 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_320, mem0_320 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_322, mem0_322 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_324, mem0_324 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_326, mem0_326 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_328, mem0_328 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_330, mem0_330 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_332, mem0_332 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_334, mem0_334 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_336, mem0_336 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_338, mem0_338 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_340, mem0_340 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_342, mem0_342 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_344, mem0_344 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_346, mem0_346 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_348, mem0_348 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_350, mem0_350 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_352, mem0_352 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_354, mem0_354 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_356, mem0_356 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_358, mem0_358 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_360, mem0_360 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_362, mem0_362 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_364, mem0_364 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_366, mem0_366 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_368, mem0_368 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_370, mem0_370 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_372, mem0_372 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_374, mem0_374 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_376, mem0_376 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_378, mem0_378 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_380, mem0_380 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_382, mem0_382 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_384, mem0_384 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_386, mem0_386 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_388, mem0_388 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_390, mem0_390 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_392, mem0_392 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_394, mem0_394 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_396, mem0_396 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_398, mem0_398 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_400, mem0_400 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_402, mem0_402 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_404, mem0_404 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_406, mem0_406 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_408, mem0_408 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_410, mem0_410 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_412, mem0_412 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_414, mem0_414 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_416, mem0_416 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_418, mem0_418 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_420, mem0_420 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_422, mem0_422 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_424, mem0_424 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_426, mem0_426 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_428, mem0_428 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_430, mem0_430 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_432, mem0_432 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_434, mem0_434 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_436, mem0_436 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_438, mem0_438 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_440, mem0_440 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_442, mem0_442 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_444, mem0_444 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_446, mem0_446 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_448, mem0_448 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_450, mem0_450 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_452, mem0_452 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_454, mem0_454 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_456, mem0_456 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_458, mem0_458 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_460, mem0_460 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_462, mem0_462 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_464, mem0_464 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_466, mem0_466 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_468, mem0_468 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_470, mem0_470 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_472, mem0_472 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_474, mem0_474 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_476, mem0_476 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_478, mem0_478 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_480, mem0_480 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_482, mem0_482 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_484, mem0_484 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_486, mem0_486 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_488, mem0_488 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_490, mem0_490 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_492, mem0_492 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_494, mem0_494 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_496, mem0_496 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_498, mem0_498 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_500, mem0_500 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_502, mem0_502 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_504, mem0_504 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_506, mem0_506 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_508, mem0_508 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_510, mem0_510 <s 5@16 * 3329@16
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

mov mem0_0_k7 mem0_0;
mov mem0_2_k7 mem0_2;
mov mem0_4_k7 mem0_4;
mov mem0_6_k7 mem0_6;
mov mem0_8_k7 mem0_8;
mov mem0_10_k7 mem0_10;
mov mem0_12_k7 mem0_12;
mov mem0_14_k7 mem0_14;
mov mem0_16_k7 mem0_16;
mov mem0_18_k7 mem0_18;
mov mem0_20_k7 mem0_20;
mov mem0_22_k7 mem0_22;
mov mem0_24_k7 mem0_24;
mov mem0_26_k7 mem0_26;
mov mem0_28_k7 mem0_28;
mov mem0_30_k7 mem0_30;
mov mem0_32_k7 mem0_32;
mov mem0_34_k7 mem0_34;
mov mem0_36_k7 mem0_36;
mov mem0_38_k7 mem0_38;
mov mem0_40_k7 mem0_40;
mov mem0_42_k7 mem0_42;
mov mem0_44_k7 mem0_44;
mov mem0_46_k7 mem0_46;
mov mem0_48_k7 mem0_48;
mov mem0_50_k7 mem0_50;
mov mem0_52_k7 mem0_52;
mov mem0_54_k7 mem0_54;
mov mem0_56_k7 mem0_56;
mov mem0_58_k7 mem0_58;
mov mem0_60_k7 mem0_60;
mov mem0_62_k7 mem0_62;
mov mem0_64_k7 mem0_64;
mov mem0_66_k7 mem0_66;
mov mem0_68_k7 mem0_68;
mov mem0_70_k7 mem0_70;
mov mem0_72_k7 mem0_72;
mov mem0_74_k7 mem0_74;
mov mem0_76_k7 mem0_76;
mov mem0_78_k7 mem0_78;
mov mem0_80_k7 mem0_80;
mov mem0_82_k7 mem0_82;
mov mem0_84_k7 mem0_84;
mov mem0_86_k7 mem0_86;
mov mem0_88_k7 mem0_88;
mov mem0_90_k7 mem0_90;
mov mem0_92_k7 mem0_92;
mov mem0_94_k7 mem0_94;
mov mem0_96_k7 mem0_96;
mov mem0_98_k7 mem0_98;
mov mem0_100_k7 mem0_100;
mov mem0_102_k7 mem0_102;
mov mem0_104_k7 mem0_104;
mov mem0_106_k7 mem0_106;
mov mem0_108_k7 mem0_108;
mov mem0_110_k7 mem0_110;
mov mem0_112_k7 mem0_112;
mov mem0_114_k7 mem0_114;
mov mem0_116_k7 mem0_116;
mov mem0_118_k7 mem0_118;
mov mem0_120_k7 mem0_120;
mov mem0_122_k7 mem0_122;
mov mem0_124_k7 mem0_124;
mov mem0_126_k7 mem0_126;
mov mem0_128_k7 mem0_128;
mov mem0_130_k7 mem0_130;
mov mem0_132_k7 mem0_132;
mov mem0_134_k7 mem0_134;
mov mem0_136_k7 mem0_136;
mov mem0_138_k7 mem0_138;
mov mem0_140_k7 mem0_140;
mov mem0_142_k7 mem0_142;
mov mem0_144_k7 mem0_144;
mov mem0_146_k7 mem0_146;
mov mem0_148_k7 mem0_148;
mov mem0_150_k7 mem0_150;
mov mem0_152_k7 mem0_152;
mov mem0_154_k7 mem0_154;
mov mem0_156_k7 mem0_156;
mov mem0_158_k7 mem0_158;
mov mem0_160_k7 mem0_160;
mov mem0_162_k7 mem0_162;
mov mem0_164_k7 mem0_164;
mov mem0_166_k7 mem0_166;
mov mem0_168_k7 mem0_168;
mov mem0_170_k7 mem0_170;
mov mem0_172_k7 mem0_172;
mov mem0_174_k7 mem0_174;
mov mem0_176_k7 mem0_176;
mov mem0_178_k7 mem0_178;
mov mem0_180_k7 mem0_180;
mov mem0_182_k7 mem0_182;
mov mem0_184_k7 mem0_184;
mov mem0_186_k7 mem0_186;
mov mem0_188_k7 mem0_188;
mov mem0_190_k7 mem0_190;
mov mem0_192_k7 mem0_192;
mov mem0_194_k7 mem0_194;
mov mem0_196_k7 mem0_196;
mov mem0_198_k7 mem0_198;
mov mem0_200_k7 mem0_200;
mov mem0_202_k7 mem0_202;
mov mem0_204_k7 mem0_204;
mov mem0_206_k7 mem0_206;
mov mem0_208_k7 mem0_208;
mov mem0_210_k7 mem0_210;
mov mem0_212_k7 mem0_212;
mov mem0_214_k7 mem0_214;
mov mem0_216_k7 mem0_216;
mov mem0_218_k7 mem0_218;
mov mem0_220_k7 mem0_220;
mov mem0_222_k7 mem0_222;
mov mem0_224_k7 mem0_224;
mov mem0_226_k7 mem0_226;
mov mem0_228_k7 mem0_228;
mov mem0_230_k7 mem0_230;
mov mem0_232_k7 mem0_232;
mov mem0_234_k7 mem0_234;
mov mem0_236_k7 mem0_236;
mov mem0_238_k7 mem0_238;
mov mem0_240_k7 mem0_240;
mov mem0_242_k7 mem0_242;
mov mem0_244_k7 mem0_244;
mov mem0_246_k7 mem0_246;
mov mem0_248_k7 mem0_248;
mov mem0_250_k7 mem0_250;
mov mem0_252_k7 mem0_252;
mov mem0_254_k7 mem0_254;
mov mem0_256_k7 mem0_256;
mov mem0_258_k7 mem0_258;
mov mem0_260_k7 mem0_260;
mov mem0_262_k7 mem0_262;
mov mem0_264_k7 mem0_264;
mov mem0_266_k7 mem0_266;
mov mem0_268_k7 mem0_268;
mov mem0_270_k7 mem0_270;
mov mem0_272_k7 mem0_272;
mov mem0_274_k7 mem0_274;
mov mem0_276_k7 mem0_276;
mov mem0_278_k7 mem0_278;
mov mem0_280_k7 mem0_280;
mov mem0_282_k7 mem0_282;
mov mem0_284_k7 mem0_284;
mov mem0_286_k7 mem0_286;
mov mem0_288_k7 mem0_288;
mov mem0_290_k7 mem0_290;
mov mem0_292_k7 mem0_292;
mov mem0_294_k7 mem0_294;
mov mem0_296_k7 mem0_296;
mov mem0_298_k7 mem0_298;
mov mem0_300_k7 mem0_300;
mov mem0_302_k7 mem0_302;
mov mem0_304_k7 mem0_304;
mov mem0_306_k7 mem0_306;
mov mem0_308_k7 mem0_308;
mov mem0_310_k7 mem0_310;
mov mem0_312_k7 mem0_312;
mov mem0_314_k7 mem0_314;
mov mem0_316_k7 mem0_316;
mov mem0_318_k7 mem0_318;
mov mem0_320_k7 mem0_320;
mov mem0_322_k7 mem0_322;
mov mem0_324_k7 mem0_324;
mov mem0_326_k7 mem0_326;
mov mem0_328_k7 mem0_328;
mov mem0_330_k7 mem0_330;
mov mem0_332_k7 mem0_332;
mov mem0_334_k7 mem0_334;
mov mem0_336_k7 mem0_336;
mov mem0_338_k7 mem0_338;
mov mem0_340_k7 mem0_340;
mov mem0_342_k7 mem0_342;
mov mem0_344_k7 mem0_344;
mov mem0_346_k7 mem0_346;
mov mem0_348_k7 mem0_348;
mov mem0_350_k7 mem0_350;
mov mem0_352_k7 mem0_352;
mov mem0_354_k7 mem0_354;
mov mem0_356_k7 mem0_356;
mov mem0_358_k7 mem0_358;
mov mem0_360_k7 mem0_360;
mov mem0_362_k7 mem0_362;
mov mem0_364_k7 mem0_364;
mov mem0_366_k7 mem0_366;
mov mem0_368_k7 mem0_368;
mov mem0_370_k7 mem0_370;
mov mem0_372_k7 mem0_372;
mov mem0_374_k7 mem0_374;
mov mem0_376_k7 mem0_376;
mov mem0_378_k7 mem0_378;
mov mem0_380_k7 mem0_380;
mov mem0_382_k7 mem0_382;
mov mem0_384_k7 mem0_384;
mov mem0_386_k7 mem0_386;
mov mem0_388_k7 mem0_388;
mov mem0_390_k7 mem0_390;
mov mem0_392_k7 mem0_392;
mov mem0_394_k7 mem0_394;
mov mem0_396_k7 mem0_396;
mov mem0_398_k7 mem0_398;
mov mem0_400_k7 mem0_400;
mov mem0_402_k7 mem0_402;
mov mem0_404_k7 mem0_404;
mov mem0_406_k7 mem0_406;
mov mem0_408_k7 mem0_408;
mov mem0_410_k7 mem0_410;
mov mem0_412_k7 mem0_412;
mov mem0_414_k7 mem0_414;
mov mem0_416_k7 mem0_416;
mov mem0_418_k7 mem0_418;
mov mem0_420_k7 mem0_420;
mov mem0_422_k7 mem0_422;
mov mem0_424_k7 mem0_424;
mov mem0_426_k7 mem0_426;
mov mem0_428_k7 mem0_428;
mov mem0_430_k7 mem0_430;
mov mem0_432_k7 mem0_432;
mov mem0_434_k7 mem0_434;
mov mem0_436_k7 mem0_436;
mov mem0_438_k7 mem0_438;
mov mem0_440_k7 mem0_440;
mov mem0_442_k7 mem0_442;
mov mem0_444_k7 mem0_444;
mov mem0_446_k7 mem0_446;
mov mem0_448_k7 mem0_448;
mov mem0_450_k7 mem0_450;
mov mem0_452_k7 mem0_452;
mov mem0_454_k7 mem0_454;
mov mem0_456_k7 mem0_456;
mov mem0_458_k7 mem0_458;
mov mem0_460_k7 mem0_460;
mov mem0_462_k7 mem0_462;
mov mem0_464_k7 mem0_464;
mov mem0_466_k7 mem0_466;
mov mem0_468_k7 mem0_468;
mov mem0_470_k7 mem0_470;
mov mem0_472_k7 mem0_472;
mov mem0_474_k7 mem0_474;
mov mem0_476_k7 mem0_476;
mov mem0_478_k7 mem0_478;
mov mem0_480_k7 mem0_480;
mov mem0_482_k7 mem0_482;
mov mem0_484_k7 mem0_484;
mov mem0_486_k7 mem0_486;
mov mem0_488_k7 mem0_488;
mov mem0_490_k7 mem0_490;
mov mem0_492_k7 mem0_492;
mov mem0_494_k7 mem0_494;
mov mem0_496_k7 mem0_496;
mov mem0_498_k7 mem0_498;
mov mem0_500_k7 mem0_500;
mov mem0_502_k7 mem0_502;
mov mem0_504_k7 mem0_504;
mov mem0_506_k7 mem0_506;
mov mem0_508_k7 mem0_508;
mov mem0_510_k7 mem0_510;

(* NOTE: k = 8 *)

(*   %arrayidx9.3 = getelementptr inbounds i16, i16* %r, i64 16 *)
(*   %768 = load i16, i16* %arrayidx9.3, align 2, !tbaa !3 *)
mov v768 mem0_32;
(*   %conv1.i.3 = sext i16 %768 to i32 *)
cast v_conv1_i_3@sint32 v768@sint16;
(*   %mul.i.3 = mul nsw i32 %conv1.i.3, -171 *)
mul v_mul_i_3 v_conv1_i_3 (-171)@sint32;
(*   %call.i.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3, v_call_i_3);
(*   %769 = load i16, i16* %r, align 2, !tbaa !3 *)
mov v769 mem0_0;
(*   %sub.3 = sub i16 %769, %call.i.3 *)
sub v_sub_3 v769 v_call_i_3;
(*   store i16 %sub.3, i16* %arrayidx9.3, align 2, !tbaa !3 *)
mov mem0_32 v_sub_3;
(*   %add21.3 = add i16 %769, %call.i.3 *)
add v_add21_3 v769 v_call_i_3;
(*   store i16 %add21.3, i16* %r, align 2, !tbaa !3 *)
mov mem0_0 v_add21_3;
(*   %arrayidx9.3.1 = getelementptr inbounds i16, i16* %r, i64 17 *)
(*   %770 = load i16, i16* %arrayidx9.3.1, align 2, !tbaa !3 *)
mov v770 mem0_34;
(*   %conv1.i.3.1 = sext i16 %770 to i32 *)
cast v_conv1_i_3_1@sint32 v770@sint16;
(*   %mul.i.3.1 = mul nsw i32 %conv1.i.3.1, -171 *)
mul v_mul_i_3_1 v_conv1_i_3_1 (-171)@sint32;
(*   %call.i.3.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_1, v_call_i_3_1);
(*   %arrayidx11.3.1 = getelementptr inbounds i16, i16* %r, i64 1 *)
(*   %771 = load i16, i16* %arrayidx11.3.1, align 2, !tbaa !3 *)
mov v771 mem0_2;
(*   %sub.3.1 = sub i16 %771, %call.i.3.1 *)
sub v_sub_3_1 v771 v_call_i_3_1;
(*   store i16 %sub.3.1, i16* %arrayidx9.3.1, align 2, !tbaa !3 *)
mov mem0_34 v_sub_3_1;
(*   %add21.3.1 = add i16 %771, %call.i.3.1 *)
add v_add21_3_1 v771 v_call_i_3_1;
(*   store i16 %add21.3.1, i16* %arrayidx11.3.1, align 2, !tbaa !3 *)
mov mem0_2 v_add21_3_1;
(*   %arrayidx9.3.2 = getelementptr inbounds i16, i16* %r, i64 18 *)
(*   %772 = load i16, i16* %arrayidx9.3.2, align 2, !tbaa !3 *)
mov v772 mem0_36;
(*   %conv1.i.3.2 = sext i16 %772 to i32 *)
cast v_conv1_i_3_2@sint32 v772@sint16;
(*   %mul.i.3.2 = mul nsw i32 %conv1.i.3.2, -171 *)
mul v_mul_i_3_2 v_conv1_i_3_2 (-171)@sint32;
(*   %call.i.3.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_2, v_call_i_3_2);
(*   %arrayidx11.3.2 = getelementptr inbounds i16, i16* %r, i64 2 *)
(*   %773 = load i16, i16* %arrayidx11.3.2, align 2, !tbaa !3 *)
mov v773 mem0_4;
(*   %sub.3.2 = sub i16 %773, %call.i.3.2 *)
sub v_sub_3_2 v773 v_call_i_3_2;
(*   store i16 %sub.3.2, i16* %arrayidx9.3.2, align 2, !tbaa !3 *)
mov mem0_36 v_sub_3_2;
(*   %add21.3.2 = add i16 %773, %call.i.3.2 *)
add v_add21_3_2 v773 v_call_i_3_2;
(*   store i16 %add21.3.2, i16* %arrayidx11.3.2, align 2, !tbaa !3 *)
mov mem0_4 v_add21_3_2;
(*   %arrayidx9.3.3 = getelementptr inbounds i16, i16* %r, i64 19 *)
(*   %774 = load i16, i16* %arrayidx9.3.3, align 2, !tbaa !3 *)
mov v774 mem0_38;
(*   %conv1.i.3.3 = sext i16 %774 to i32 *)
cast v_conv1_i_3_3@sint32 v774@sint16;
(*   %mul.i.3.3 = mul nsw i32 %conv1.i.3.3, -171 *)
mul v_mul_i_3_3 v_conv1_i_3_3 (-171)@sint32;
(*   %call.i.3.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_3, v_call_i_3_3);
(*   %arrayidx11.3.3 = getelementptr inbounds i16, i16* %r, i64 3 *)
(*   %775 = load i16, i16* %arrayidx11.3.3, align 2, !tbaa !3 *)
mov v775 mem0_6;
(*   %sub.3.3 = sub i16 %775, %call.i.3.3 *)
sub v_sub_3_3 v775 v_call_i_3_3;
(*   store i16 %sub.3.3, i16* %arrayidx9.3.3, align 2, !tbaa !3 *)
mov mem0_38 v_sub_3_3;
(*   %add21.3.3 = add i16 %775, %call.i.3.3 *)
add v_add21_3_3 v775 v_call_i_3_3;
(*   store i16 %add21.3.3, i16* %arrayidx11.3.3, align 2, !tbaa !3 *)
mov mem0_6 v_add21_3_3;
(*   %arrayidx9.3.4 = getelementptr inbounds i16, i16* %r, i64 20 *)
(*   %776 = load i16, i16* %arrayidx9.3.4, align 2, !tbaa !3 *)
mov v776 mem0_40;
(*   %conv1.i.3.4 = sext i16 %776 to i32 *)
cast v_conv1_i_3_4@sint32 v776@sint16;
(*   %mul.i.3.4 = mul nsw i32 %conv1.i.3.4, -171 *)
mul v_mul_i_3_4 v_conv1_i_3_4 (-171)@sint32;
(*   %call.i.3.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_4, v_call_i_3_4);
(*   %arrayidx11.3.4 = getelementptr inbounds i16, i16* %r, i64 4 *)
(*   %777 = load i16, i16* %arrayidx11.3.4, align 2, !tbaa !3 *)
mov v777 mem0_8;
(*   %sub.3.4 = sub i16 %777, %call.i.3.4 *)
sub v_sub_3_4 v777 v_call_i_3_4;
(*   store i16 %sub.3.4, i16* %arrayidx9.3.4, align 2, !tbaa !3 *)
mov mem0_40 v_sub_3_4;
(*   %add21.3.4 = add i16 %777, %call.i.3.4 *)
add v_add21_3_4 v777 v_call_i_3_4;
(*   store i16 %add21.3.4, i16* %arrayidx11.3.4, align 2, !tbaa !3 *)
mov mem0_8 v_add21_3_4;
(*   %arrayidx9.3.5 = getelementptr inbounds i16, i16* %r, i64 21 *)
(*   %778 = load i16, i16* %arrayidx9.3.5, align 2, !tbaa !3 *)
mov v778 mem0_42;
(*   %conv1.i.3.5 = sext i16 %778 to i32 *)
cast v_conv1_i_3_5@sint32 v778@sint16;
(*   %mul.i.3.5 = mul nsw i32 %conv1.i.3.5, -171 *)
mul v_mul_i_3_5 v_conv1_i_3_5 (-171)@sint32;
(*   %call.i.3.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_5, v_call_i_3_5);
(*   %arrayidx11.3.5 = getelementptr inbounds i16, i16* %r, i64 5 *)
(*   %779 = load i16, i16* %arrayidx11.3.5, align 2, !tbaa !3 *)
mov v779 mem0_10;
(*   %sub.3.5 = sub i16 %779, %call.i.3.5 *)
sub v_sub_3_5 v779 v_call_i_3_5;
(*   store i16 %sub.3.5, i16* %arrayidx9.3.5, align 2, !tbaa !3 *)
mov mem0_42 v_sub_3_5;
(*   %add21.3.5 = add i16 %779, %call.i.3.5 *)
add v_add21_3_5 v779 v_call_i_3_5;
(*   store i16 %add21.3.5, i16* %arrayidx11.3.5, align 2, !tbaa !3 *)
mov mem0_10 v_add21_3_5;
(*   %arrayidx9.3.6 = getelementptr inbounds i16, i16* %r, i64 22 *)
(*   %780 = load i16, i16* %arrayidx9.3.6, align 2, !tbaa !3 *)
mov v780 mem0_44;
(*   %conv1.i.3.6 = sext i16 %780 to i32 *)
cast v_conv1_i_3_6@sint32 v780@sint16;
(*   %mul.i.3.6 = mul nsw i32 %conv1.i.3.6, -171 *)
mul v_mul_i_3_6 v_conv1_i_3_6 (-171)@sint32;
(*   %call.i.3.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_6, v_call_i_3_6);
(*   %arrayidx11.3.6 = getelementptr inbounds i16, i16* %r, i64 6 *)
(*   %781 = load i16, i16* %arrayidx11.3.6, align 2, !tbaa !3 *)
mov v781 mem0_12;
(*   %sub.3.6 = sub i16 %781, %call.i.3.6 *)
sub v_sub_3_6 v781 v_call_i_3_6;
(*   store i16 %sub.3.6, i16* %arrayidx9.3.6, align 2, !tbaa !3 *)
mov mem0_44 v_sub_3_6;
(*   %add21.3.6 = add i16 %781, %call.i.3.6 *)
add v_add21_3_6 v781 v_call_i_3_6;
(*   store i16 %add21.3.6, i16* %arrayidx11.3.6, align 2, !tbaa !3 *)
mov mem0_12 v_add21_3_6;
(*   %arrayidx9.3.7 = getelementptr inbounds i16, i16* %r, i64 23 *)
(*   %782 = load i16, i16* %arrayidx9.3.7, align 2, !tbaa !3 *)
mov v782 mem0_46;
(*   %conv1.i.3.7 = sext i16 %782 to i32 *)
cast v_conv1_i_3_7@sint32 v782@sint16;
(*   %mul.i.3.7 = mul nsw i32 %conv1.i.3.7, -171 *)
mul v_mul_i_3_7 v_conv1_i_3_7 (-171)@sint32;
(*   %call.i.3.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_7, v_call_i_3_7);
(*   %arrayidx11.3.7 = getelementptr inbounds i16, i16* %r, i64 7 *)
(*   %783 = load i16, i16* %arrayidx11.3.7, align 2, !tbaa !3 *)
mov v783 mem0_14;
(*   %sub.3.7 = sub i16 %783, %call.i.3.7 *)
sub v_sub_3_7 v783 v_call_i_3_7;
(*   store i16 %sub.3.7, i16* %arrayidx9.3.7, align 2, !tbaa !3 *)
mov mem0_46 v_sub_3_7;
(*   %add21.3.7 = add i16 %783, %call.i.3.7 *)
add v_add21_3_7 v783 v_call_i_3_7;
(*   store i16 %add21.3.7, i16* %arrayidx11.3.7, align 2, !tbaa !3 *)
mov mem0_14 v_add21_3_7;
(*   %arrayidx9.3.8 = getelementptr inbounds i16, i16* %r, i64 24 *)
(*   %784 = load i16, i16* %arrayidx9.3.8, align 2, !tbaa !3 *)
mov v784 mem0_48;
(*   %conv1.i.3.8 = sext i16 %784 to i32 *)
cast v_conv1_i_3_8@sint32 v784@sint16;
(*   %mul.i.3.8 = mul nsw i32 %conv1.i.3.8, -171 *)
mul v_mul_i_3_8 v_conv1_i_3_8 (-171)@sint32;
(*   %call.i.3.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_8, v_call_i_3_8);
(*   %arrayidx11.3.8 = getelementptr inbounds i16, i16* %r, i64 8 *)
(*   %785 = load i16, i16* %arrayidx11.3.8, align 2, !tbaa !3 *)
mov v785 mem0_16;
(*   %sub.3.8 = sub i16 %785, %call.i.3.8 *)
sub v_sub_3_8 v785 v_call_i_3_8;
(*   store i16 %sub.3.8, i16* %arrayidx9.3.8, align 2, !tbaa !3 *)
mov mem0_48 v_sub_3_8;
(*   %add21.3.8 = add i16 %785, %call.i.3.8 *)
add v_add21_3_8 v785 v_call_i_3_8;
(*   store i16 %add21.3.8, i16* %arrayidx11.3.8, align 2, !tbaa !3 *)
mov mem0_16 v_add21_3_8;
(*   %arrayidx9.3.9 = getelementptr inbounds i16, i16* %r, i64 25 *)
(*   %786 = load i16, i16* %arrayidx9.3.9, align 2, !tbaa !3 *)
mov v786 mem0_50;
(*   %conv1.i.3.9 = sext i16 %786 to i32 *)
cast v_conv1_i_3_9@sint32 v786@sint16;
(*   %mul.i.3.9 = mul nsw i32 %conv1.i.3.9, -171 *)
mul v_mul_i_3_9 v_conv1_i_3_9 (-171)@sint32;
(*   %call.i.3.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_9, v_call_i_3_9);
(*   %arrayidx11.3.9 = getelementptr inbounds i16, i16* %r, i64 9 *)
(*   %787 = load i16, i16* %arrayidx11.3.9, align 2, !tbaa !3 *)
mov v787 mem0_18;
(*   %sub.3.9 = sub i16 %787, %call.i.3.9 *)
sub v_sub_3_9 v787 v_call_i_3_9;
(*   store i16 %sub.3.9, i16* %arrayidx9.3.9, align 2, !tbaa !3 *)
mov mem0_50 v_sub_3_9;
(*   %add21.3.9 = add i16 %787, %call.i.3.9 *)
add v_add21_3_9 v787 v_call_i_3_9;
(*   store i16 %add21.3.9, i16* %arrayidx11.3.9, align 2, !tbaa !3 *)
mov mem0_18 v_add21_3_9;
(*   %arrayidx9.3.10 = getelementptr inbounds i16, i16* %r, i64 26 *)
(*   %788 = load i16, i16* %arrayidx9.3.10, align 2, !tbaa !3 *)
mov v788 mem0_52;
(*   %conv1.i.3.10 = sext i16 %788 to i32 *)
cast v_conv1_i_3_10@sint32 v788@sint16;
(*   %mul.i.3.10 = mul nsw i32 %conv1.i.3.10, -171 *)
mul v_mul_i_3_10 v_conv1_i_3_10 (-171)@sint32;
(*   %call.i.3.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_10, v_call_i_3_10);
(*   %arrayidx11.3.10 = getelementptr inbounds i16, i16* %r, i64 10 *)
(*   %789 = load i16, i16* %arrayidx11.3.10, align 2, !tbaa !3 *)
mov v789 mem0_20;
(*   %sub.3.10 = sub i16 %789, %call.i.3.10 *)
sub v_sub_3_10 v789 v_call_i_3_10;
(*   store i16 %sub.3.10, i16* %arrayidx9.3.10, align 2, !tbaa !3 *)
mov mem0_52 v_sub_3_10;
(*   %add21.3.10 = add i16 %789, %call.i.3.10 *)
add v_add21_3_10 v789 v_call_i_3_10;
(*   store i16 %add21.3.10, i16* %arrayidx11.3.10, align 2, !tbaa !3 *)
mov mem0_20 v_add21_3_10;
(*   %arrayidx9.3.11 = getelementptr inbounds i16, i16* %r, i64 27 *)
(*   %790 = load i16, i16* %arrayidx9.3.11, align 2, !tbaa !3 *)
mov v790 mem0_54;
(*   %conv1.i.3.11 = sext i16 %790 to i32 *)
cast v_conv1_i_3_11@sint32 v790@sint16;
(*   %mul.i.3.11 = mul nsw i32 %conv1.i.3.11, -171 *)
mul v_mul_i_3_11 v_conv1_i_3_11 (-171)@sint32;
(*   %call.i.3.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_11, v_call_i_3_11);
(*   %arrayidx11.3.11 = getelementptr inbounds i16, i16* %r, i64 11 *)
(*   %791 = load i16, i16* %arrayidx11.3.11, align 2, !tbaa !3 *)
mov v791 mem0_22;
(*   %sub.3.11 = sub i16 %791, %call.i.3.11 *)
sub v_sub_3_11 v791 v_call_i_3_11;
(*   store i16 %sub.3.11, i16* %arrayidx9.3.11, align 2, !tbaa !3 *)
mov mem0_54 v_sub_3_11;
(*   %add21.3.11 = add i16 %791, %call.i.3.11 *)
add v_add21_3_11 v791 v_call_i_3_11;
(*   store i16 %add21.3.11, i16* %arrayidx11.3.11, align 2, !tbaa !3 *)
mov mem0_22 v_add21_3_11;
(*   %arrayidx9.3.12 = getelementptr inbounds i16, i16* %r, i64 28 *)
(*   %792 = load i16, i16* %arrayidx9.3.12, align 2, !tbaa !3 *)
mov v792 mem0_56;
(*   %conv1.i.3.12 = sext i16 %792 to i32 *)
cast v_conv1_i_3_12@sint32 v792@sint16;
(*   %mul.i.3.12 = mul nsw i32 %conv1.i.3.12, -171 *)
mul v_mul_i_3_12 v_conv1_i_3_12 (-171)@sint32;
(*   %call.i.3.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_12, v_call_i_3_12);
(*   %arrayidx11.3.12 = getelementptr inbounds i16, i16* %r, i64 12 *)
(*   %793 = load i16, i16* %arrayidx11.3.12, align 2, !tbaa !3 *)
mov v793 mem0_24;
(*   %sub.3.12 = sub i16 %793, %call.i.3.12 *)
sub v_sub_3_12 v793 v_call_i_3_12;
(*   store i16 %sub.3.12, i16* %arrayidx9.3.12, align 2, !tbaa !3 *)
mov mem0_56 v_sub_3_12;
(*   %add21.3.12 = add i16 %793, %call.i.3.12 *)
add v_add21_3_12 v793 v_call_i_3_12;
(*   store i16 %add21.3.12, i16* %arrayidx11.3.12, align 2, !tbaa !3 *)
mov mem0_24 v_add21_3_12;
(*   %arrayidx9.3.13 = getelementptr inbounds i16, i16* %r, i64 29 *)
(*   %794 = load i16, i16* %arrayidx9.3.13, align 2, !tbaa !3 *)
mov v794 mem0_58;
(*   %conv1.i.3.13 = sext i16 %794 to i32 *)
cast v_conv1_i_3_13@sint32 v794@sint16;
(*   %mul.i.3.13 = mul nsw i32 %conv1.i.3.13, -171 *)
mul v_mul_i_3_13 v_conv1_i_3_13 (-171)@sint32;
(*   %call.i.3.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_13, v_call_i_3_13);
(*   %arrayidx11.3.13 = getelementptr inbounds i16, i16* %r, i64 13 *)
(*   %795 = load i16, i16* %arrayidx11.3.13, align 2, !tbaa !3 *)
mov v795 mem0_26;
(*   %sub.3.13 = sub i16 %795, %call.i.3.13 *)
sub v_sub_3_13 v795 v_call_i_3_13;
(*   store i16 %sub.3.13, i16* %arrayidx9.3.13, align 2, !tbaa !3 *)
mov mem0_58 v_sub_3_13;
(*   %add21.3.13 = add i16 %795, %call.i.3.13 *)
add v_add21_3_13 v795 v_call_i_3_13;
(*   store i16 %add21.3.13, i16* %arrayidx11.3.13, align 2, !tbaa !3 *)
mov mem0_26 v_add21_3_13;
(*   %arrayidx9.3.14 = getelementptr inbounds i16, i16* %r, i64 30 *)
(*   %796 = load i16, i16* %arrayidx9.3.14, align 2, !tbaa !3 *)
mov v796 mem0_60;
(*   %conv1.i.3.14 = sext i16 %796 to i32 *)
cast v_conv1_i_3_14@sint32 v796@sint16;
(*   %mul.i.3.14 = mul nsw i32 %conv1.i.3.14, -171 *)
mul v_mul_i_3_14 v_conv1_i_3_14 (-171)@sint32;
(*   %call.i.3.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_14, v_call_i_3_14);
(*   %arrayidx11.3.14 = getelementptr inbounds i16, i16* %r, i64 14 *)
(*   %797 = load i16, i16* %arrayidx11.3.14, align 2, !tbaa !3 *)
mov v797 mem0_28;
(*   %sub.3.14 = sub i16 %797, %call.i.3.14 *)
sub v_sub_3_14 v797 v_call_i_3_14;
(*   store i16 %sub.3.14, i16* %arrayidx9.3.14, align 2, !tbaa !3 *)
mov mem0_60 v_sub_3_14;
(*   %add21.3.14 = add i16 %797, %call.i.3.14 *)
add v_add21_3_14 v797 v_call_i_3_14;
(*   store i16 %add21.3.14, i16* %arrayidx11.3.14, align 2, !tbaa !3 *)
mov mem0_28 v_add21_3_14;
(*   %arrayidx9.3.15 = getelementptr inbounds i16, i16* %r, i64 31 *)
(*   %798 = load i16, i16* %arrayidx9.3.15, align 2, !tbaa !3 *)
mov v798 mem0_62;
(*   %conv1.i.3.15 = sext i16 %798 to i32 *)
cast v_conv1_i_3_15@sint32 v798@sint16;
(*   %mul.i.3.15 = mul nsw i32 %conv1.i.3.15, -171 *)
mul v_mul_i_3_15 v_conv1_i_3_15 (-171)@sint32;
(*   %call.i.3.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_15, v_call_i_3_15);
(*   %arrayidx11.3.15 = getelementptr inbounds i16, i16* %r, i64 15 *)
(*   %799 = load i16, i16* %arrayidx11.3.15, align 2, !tbaa !3 *)
mov v799 mem0_30;
(*   %sub.3.15 = sub i16 %799, %call.i.3.15 *)
sub v_sub_3_15 v799 v_call_i_3_15;
(*   store i16 %sub.3.15, i16* %arrayidx9.3.15, align 2, !tbaa !3 *)
mov mem0_62 v_sub_3_15;
(*   %add21.3.15 = add i16 %799, %call.i.3.15 *)
add v_add21_3_15 v799 v_call_i_3_15;
(*   store i16 %add21.3.15, i16* %arrayidx11.3.15, align 2, !tbaa !3 *)
mov mem0_30 v_add21_3_15;

(* NOTE: k = 9 *)

(*   %arrayidx9.3.1178 = getelementptr inbounds i16, i16* %r, i64 48 *)
(*   %800 = load i16, i16* %arrayidx9.3.1178, align 2, !tbaa !3 *)
mov v800 mem0_96;
(*   %conv1.i.3.1179 = sext i16 %800 to i32 *)
cast v_conv1_i_3_1179@sint32 v800@sint16;
(*   %mul.i.3.1180 = mul nsw i32 %conv1.i.3.1179, 622 *)
mul v_mul_i_3_1180 v_conv1_i_3_1179 (622)@sint32;
(*   %call.i.3.1181 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.1180) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_1180, v_call_i_3_1181);
(*   %arrayidx11.3.1182 = getelementptr inbounds i16, i16* %r, i64 32 *)
(*   %801 = load i16, i16* %arrayidx11.3.1182, align 2, !tbaa !3 *)
mov v801 mem0_64;
(*   %sub.3.1183 = sub i16 %801, %call.i.3.1181 *)
sub v_sub_3_1183 v801 v_call_i_3_1181;
(*   store i16 %sub.3.1183, i16* %arrayidx9.3.1178, align 2, !tbaa !3 *)
mov mem0_96 v_sub_3_1183;
(*   %add21.3.1184 = add i16 %801, %call.i.3.1181 *)
add v_add21_3_1184 v801 v_call_i_3_1181;
(*   store i16 %add21.3.1184, i16* %arrayidx11.3.1182, align 2, !tbaa !3 *)
mov mem0_64 v_add21_3_1184;
(*   %arrayidx9.3.1.1 = getelementptr inbounds i16, i16* %r, i64 49 *)
(*   %802 = load i16, i16* %arrayidx9.3.1.1, align 2, !tbaa !3 *)
mov v802 mem0_98;
(*   %conv1.i.3.1.1 = sext i16 %802 to i32 *)
cast v_conv1_i_3_1_1@sint32 v802@sint16;
(*   %mul.i.3.1.1 = mul nsw i32 %conv1.i.3.1.1, 622 *)
mul v_mul_i_3_1_1 v_conv1_i_3_1_1 (622)@sint32;
(*   %call.i.3.1.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.1.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_1_1, v_call_i_3_1_1);
(*   %arrayidx11.3.1.1 = getelementptr inbounds i16, i16* %r, i64 33 *)
(*   %803 = load i16, i16* %arrayidx11.3.1.1, align 2, !tbaa !3 *)
mov v803 mem0_66;
(*   %sub.3.1.1 = sub i16 %803, %call.i.3.1.1 *)
sub v_sub_3_1_1 v803 v_call_i_3_1_1;
(*   store i16 %sub.3.1.1, i16* %arrayidx9.3.1.1, align 2, !tbaa !3 *)
mov mem0_98 v_sub_3_1_1;
(*   %add21.3.1.1 = add i16 %803, %call.i.3.1.1 *)
add v_add21_3_1_1 v803 v_call_i_3_1_1;
(*   store i16 %add21.3.1.1, i16* %arrayidx11.3.1.1, align 2, !tbaa !3 *)
mov mem0_66 v_add21_3_1_1;
(*   %arrayidx9.3.2.1 = getelementptr inbounds i16, i16* %r, i64 50 *)
(*   %804 = load i16, i16* %arrayidx9.3.2.1, align 2, !tbaa !3 *)
mov v804 mem0_100;
(*   %conv1.i.3.2.1 = sext i16 %804 to i32 *)
cast v_conv1_i_3_2_1@sint32 v804@sint16;
(*   %mul.i.3.2.1 = mul nsw i32 %conv1.i.3.2.1, 622 *)
mul v_mul_i_3_2_1 v_conv1_i_3_2_1 (622)@sint32;
(*   %call.i.3.2.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.2.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_2_1, v_call_i_3_2_1);
(*   %arrayidx11.3.2.1 = getelementptr inbounds i16, i16* %r, i64 34 *)
(*   %805 = load i16, i16* %arrayidx11.3.2.1, align 2, !tbaa !3 *)
mov v805 mem0_68;
(*   %sub.3.2.1 = sub i16 %805, %call.i.3.2.1 *)
sub v_sub_3_2_1 v805 v_call_i_3_2_1;
(*   store i16 %sub.3.2.1, i16* %arrayidx9.3.2.1, align 2, !tbaa !3 *)
mov mem0_100 v_sub_3_2_1;
(*   %add21.3.2.1 = add i16 %805, %call.i.3.2.1 *)
add v_add21_3_2_1 v805 v_call_i_3_2_1;
(*   store i16 %add21.3.2.1, i16* %arrayidx11.3.2.1, align 2, !tbaa !3 *)
mov mem0_68 v_add21_3_2_1;
(*   %arrayidx9.3.3.1 = getelementptr inbounds i16, i16* %r, i64 51 *)
(*   %806 = load i16, i16* %arrayidx9.3.3.1, align 2, !tbaa !3 *)
mov v806 mem0_102;
(*   %conv1.i.3.3.1 = sext i16 %806 to i32 *)
cast v_conv1_i_3_3_1@sint32 v806@sint16;
(*   %mul.i.3.3.1 = mul nsw i32 %conv1.i.3.3.1, 622 *)
mul v_mul_i_3_3_1 v_conv1_i_3_3_1 (622)@sint32;
(*   %call.i.3.3.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.3.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_3_1, v_call_i_3_3_1);
(*   %arrayidx11.3.3.1 = getelementptr inbounds i16, i16* %r, i64 35 *)
(*   %807 = load i16, i16* %arrayidx11.3.3.1, align 2, !tbaa !3 *)
mov v807 mem0_70;
(*   %sub.3.3.1 = sub i16 %807, %call.i.3.3.1 *)
sub v_sub_3_3_1 v807 v_call_i_3_3_1;
(*   store i16 %sub.3.3.1, i16* %arrayidx9.3.3.1, align 2, !tbaa !3 *)
mov mem0_102 v_sub_3_3_1;
(*   %add21.3.3.1 = add i16 %807, %call.i.3.3.1 *)
add v_add21_3_3_1 v807 v_call_i_3_3_1;
(*   store i16 %add21.3.3.1, i16* %arrayidx11.3.3.1, align 2, !tbaa !3 *)
mov mem0_70 v_add21_3_3_1;
(*   %arrayidx9.3.4.1 = getelementptr inbounds i16, i16* %r, i64 52 *)
(*   %808 = load i16, i16* %arrayidx9.3.4.1, align 2, !tbaa !3 *)
mov v808 mem0_104;
(*   %conv1.i.3.4.1 = sext i16 %808 to i32 *)
cast v_conv1_i_3_4_1@sint32 v808@sint16;
(*   %mul.i.3.4.1 = mul nsw i32 %conv1.i.3.4.1, 622 *)
mul v_mul_i_3_4_1 v_conv1_i_3_4_1 (622)@sint32;
(*   %call.i.3.4.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.4.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_4_1, v_call_i_3_4_1);
(*   %arrayidx11.3.4.1 = getelementptr inbounds i16, i16* %r, i64 36 *)
(*   %809 = load i16, i16* %arrayidx11.3.4.1, align 2, !tbaa !3 *)
mov v809 mem0_72;
(*   %sub.3.4.1 = sub i16 %809, %call.i.3.4.1 *)
sub v_sub_3_4_1 v809 v_call_i_3_4_1;
(*   store i16 %sub.3.4.1, i16* %arrayidx9.3.4.1, align 2, !tbaa !3 *)
mov mem0_104 v_sub_3_4_1;
(*   %add21.3.4.1 = add i16 %809, %call.i.3.4.1 *)
add v_add21_3_4_1 v809 v_call_i_3_4_1;
(*   store i16 %add21.3.4.1, i16* %arrayidx11.3.4.1, align 2, !tbaa !3 *)
mov mem0_72 v_add21_3_4_1;
(*   %arrayidx9.3.5.1 = getelementptr inbounds i16, i16* %r, i64 53 *)
(*   %810 = load i16, i16* %arrayidx9.3.5.1, align 2, !tbaa !3 *)
mov v810 mem0_106;
(*   %conv1.i.3.5.1 = sext i16 %810 to i32 *)
cast v_conv1_i_3_5_1@sint32 v810@sint16;
(*   %mul.i.3.5.1 = mul nsw i32 %conv1.i.3.5.1, 622 *)
mul v_mul_i_3_5_1 v_conv1_i_3_5_1 (622)@sint32;
(*   %call.i.3.5.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.5.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_5_1, v_call_i_3_5_1);
(*   %arrayidx11.3.5.1 = getelementptr inbounds i16, i16* %r, i64 37 *)
(*   %811 = load i16, i16* %arrayidx11.3.5.1, align 2, !tbaa !3 *)
mov v811 mem0_74;
(*   %sub.3.5.1 = sub i16 %811, %call.i.3.5.1 *)
sub v_sub_3_5_1 v811 v_call_i_3_5_1;
(*   store i16 %sub.3.5.1, i16* %arrayidx9.3.5.1, align 2, !tbaa !3 *)
mov mem0_106 v_sub_3_5_1;
(*   %add21.3.5.1 = add i16 %811, %call.i.3.5.1 *)
add v_add21_3_5_1 v811 v_call_i_3_5_1;
(*   store i16 %add21.3.5.1, i16* %arrayidx11.3.5.1, align 2, !tbaa !3 *)
mov mem0_74 v_add21_3_5_1;
(*   %arrayidx9.3.6.1 = getelementptr inbounds i16, i16* %r, i64 54 *)
(*   %812 = load i16, i16* %arrayidx9.3.6.1, align 2, !tbaa !3 *)
mov v812 mem0_108;
(*   %conv1.i.3.6.1 = sext i16 %812 to i32 *)
cast v_conv1_i_3_6_1@sint32 v812@sint16;
(*   %mul.i.3.6.1 = mul nsw i32 %conv1.i.3.6.1, 622 *)
mul v_mul_i_3_6_1 v_conv1_i_3_6_1 (622)@sint32;
(*   %call.i.3.6.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.6.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_6_1, v_call_i_3_6_1);
(*   %arrayidx11.3.6.1 = getelementptr inbounds i16, i16* %r, i64 38 *)
(*   %813 = load i16, i16* %arrayidx11.3.6.1, align 2, !tbaa !3 *)
mov v813 mem0_76;
(*   %sub.3.6.1 = sub i16 %813, %call.i.3.6.1 *)
sub v_sub_3_6_1 v813 v_call_i_3_6_1;
(*   store i16 %sub.3.6.1, i16* %arrayidx9.3.6.1, align 2, !tbaa !3 *)
mov mem0_108 v_sub_3_6_1;
(*   %add21.3.6.1 = add i16 %813, %call.i.3.6.1 *)
add v_add21_3_6_1 v813 v_call_i_3_6_1;
(*   store i16 %add21.3.6.1, i16* %arrayidx11.3.6.1, align 2, !tbaa !3 *)
mov mem0_76 v_add21_3_6_1;
(*   %arrayidx9.3.7.1 = getelementptr inbounds i16, i16* %r, i64 55 *)
(*   %814 = load i16, i16* %arrayidx9.3.7.1, align 2, !tbaa !3 *)
mov v814 mem0_110;
(*   %conv1.i.3.7.1 = sext i16 %814 to i32 *)
cast v_conv1_i_3_7_1@sint32 v814@sint16;
(*   %mul.i.3.7.1 = mul nsw i32 %conv1.i.3.7.1, 622 *)
mul v_mul_i_3_7_1 v_conv1_i_3_7_1 (622)@sint32;
(*   %call.i.3.7.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.7.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_7_1, v_call_i_3_7_1);
(*   %arrayidx11.3.7.1 = getelementptr inbounds i16, i16* %r, i64 39 *)
(*   %815 = load i16, i16* %arrayidx11.3.7.1, align 2, !tbaa !3 *)
mov v815 mem0_78;
(*   %sub.3.7.1 = sub i16 %815, %call.i.3.7.1 *)
sub v_sub_3_7_1 v815 v_call_i_3_7_1;
(*   store i16 %sub.3.7.1, i16* %arrayidx9.3.7.1, align 2, !tbaa !3 *)
mov mem0_110 v_sub_3_7_1;
(*   %add21.3.7.1 = add i16 %815, %call.i.3.7.1 *)
add v_add21_3_7_1 v815 v_call_i_3_7_1;
(*   store i16 %add21.3.7.1, i16* %arrayidx11.3.7.1, align 2, !tbaa !3 *)
mov mem0_78 v_add21_3_7_1;
(*   %arrayidx9.3.8.1 = getelementptr inbounds i16, i16* %r, i64 56 *)
(*   %816 = load i16, i16* %arrayidx9.3.8.1, align 2, !tbaa !3 *)
mov v816 mem0_112;
(*   %conv1.i.3.8.1 = sext i16 %816 to i32 *)
cast v_conv1_i_3_8_1@sint32 v816@sint16;
(*   %mul.i.3.8.1 = mul nsw i32 %conv1.i.3.8.1, 622 *)
mul v_mul_i_3_8_1 v_conv1_i_3_8_1 (622)@sint32;
(*   %call.i.3.8.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.8.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_8_1, v_call_i_3_8_1);
(*   %arrayidx11.3.8.1 = getelementptr inbounds i16, i16* %r, i64 40 *)
(*   %817 = load i16, i16* %arrayidx11.3.8.1, align 2, !tbaa !3 *)
mov v817 mem0_80;
(*   %sub.3.8.1 = sub i16 %817, %call.i.3.8.1 *)
sub v_sub_3_8_1 v817 v_call_i_3_8_1;
(*   store i16 %sub.3.8.1, i16* %arrayidx9.3.8.1, align 2, !tbaa !3 *)
mov mem0_112 v_sub_3_8_1;
(*   %add21.3.8.1 = add i16 %817, %call.i.3.8.1 *)
add v_add21_3_8_1 v817 v_call_i_3_8_1;
(*   store i16 %add21.3.8.1, i16* %arrayidx11.3.8.1, align 2, !tbaa !3 *)
mov mem0_80 v_add21_3_8_1;
(*   %arrayidx9.3.9.1 = getelementptr inbounds i16, i16* %r, i64 57 *)
(*   %818 = load i16, i16* %arrayidx9.3.9.1, align 2, !tbaa !3 *)
mov v818 mem0_114;
(*   %conv1.i.3.9.1 = sext i16 %818 to i32 *)
cast v_conv1_i_3_9_1@sint32 v818@sint16;
(*   %mul.i.3.9.1 = mul nsw i32 %conv1.i.3.9.1, 622 *)
mul v_mul_i_3_9_1 v_conv1_i_3_9_1 (622)@sint32;
(*   %call.i.3.9.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.9.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_9_1, v_call_i_3_9_1);
(*   %arrayidx11.3.9.1 = getelementptr inbounds i16, i16* %r, i64 41 *)
(*   %819 = load i16, i16* %arrayidx11.3.9.1, align 2, !tbaa !3 *)
mov v819 mem0_82;
(*   %sub.3.9.1 = sub i16 %819, %call.i.3.9.1 *)
sub v_sub_3_9_1 v819 v_call_i_3_9_1;
(*   store i16 %sub.3.9.1, i16* %arrayidx9.3.9.1, align 2, !tbaa !3 *)
mov mem0_114 v_sub_3_9_1;
(*   %add21.3.9.1 = add i16 %819, %call.i.3.9.1 *)
add v_add21_3_9_1 v819 v_call_i_3_9_1;
(*   store i16 %add21.3.9.1, i16* %arrayidx11.3.9.1, align 2, !tbaa !3 *)
mov mem0_82 v_add21_3_9_1;
(*   %arrayidx9.3.10.1 = getelementptr inbounds i16, i16* %r, i64 58 *)
(*   %820 = load i16, i16* %arrayidx9.3.10.1, align 2, !tbaa !3 *)
mov v820 mem0_116;
(*   %conv1.i.3.10.1 = sext i16 %820 to i32 *)
cast v_conv1_i_3_10_1@sint32 v820@sint16;
(*   %mul.i.3.10.1 = mul nsw i32 %conv1.i.3.10.1, 622 *)
mul v_mul_i_3_10_1 v_conv1_i_3_10_1 (622)@sint32;
(*   %call.i.3.10.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.10.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_10_1, v_call_i_3_10_1);
(*   %arrayidx11.3.10.1 = getelementptr inbounds i16, i16* %r, i64 42 *)
(*   %821 = load i16, i16* %arrayidx11.3.10.1, align 2, !tbaa !3 *)
mov v821 mem0_84;
(*   %sub.3.10.1 = sub i16 %821, %call.i.3.10.1 *)
sub v_sub_3_10_1 v821 v_call_i_3_10_1;
(*   store i16 %sub.3.10.1, i16* %arrayidx9.3.10.1, align 2, !tbaa !3 *)
mov mem0_116 v_sub_3_10_1;
(*   %add21.3.10.1 = add i16 %821, %call.i.3.10.1 *)
add v_add21_3_10_1 v821 v_call_i_3_10_1;
(*   store i16 %add21.3.10.1, i16* %arrayidx11.3.10.1, align 2, !tbaa !3 *)
mov mem0_84 v_add21_3_10_1;
(*   %arrayidx9.3.11.1 = getelementptr inbounds i16, i16* %r, i64 59 *)
(*   %822 = load i16, i16* %arrayidx9.3.11.1, align 2, !tbaa !3 *)
mov v822 mem0_118;
(*   %conv1.i.3.11.1 = sext i16 %822 to i32 *)
cast v_conv1_i_3_11_1@sint32 v822@sint16;
(*   %mul.i.3.11.1 = mul nsw i32 %conv1.i.3.11.1, 622 *)
mul v_mul_i_3_11_1 v_conv1_i_3_11_1 (622)@sint32;
(*   %call.i.3.11.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.11.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_11_1, v_call_i_3_11_1);
(*   %arrayidx11.3.11.1 = getelementptr inbounds i16, i16* %r, i64 43 *)
(*   %823 = load i16, i16* %arrayidx11.3.11.1, align 2, !tbaa !3 *)
mov v823 mem0_86;
(*   %sub.3.11.1 = sub i16 %823, %call.i.3.11.1 *)
sub v_sub_3_11_1 v823 v_call_i_3_11_1;
(*   store i16 %sub.3.11.1, i16* %arrayidx9.3.11.1, align 2, !tbaa !3 *)
mov mem0_118 v_sub_3_11_1;
(*   %add21.3.11.1 = add i16 %823, %call.i.3.11.1 *)
add v_add21_3_11_1 v823 v_call_i_3_11_1;
(*   store i16 %add21.3.11.1, i16* %arrayidx11.3.11.1, align 2, !tbaa !3 *)
mov mem0_86 v_add21_3_11_1;
(*   %arrayidx9.3.12.1 = getelementptr inbounds i16, i16* %r, i64 60 *)
(*   %824 = load i16, i16* %arrayidx9.3.12.1, align 2, !tbaa !3 *)
mov v824 mem0_120;
(*   %conv1.i.3.12.1 = sext i16 %824 to i32 *)
cast v_conv1_i_3_12_1@sint32 v824@sint16;
(*   %mul.i.3.12.1 = mul nsw i32 %conv1.i.3.12.1, 622 *)
mul v_mul_i_3_12_1 v_conv1_i_3_12_1 (622)@sint32;
(*   %call.i.3.12.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.12.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_12_1, v_call_i_3_12_1);
(*   %arrayidx11.3.12.1 = getelementptr inbounds i16, i16* %r, i64 44 *)
(*   %825 = load i16, i16* %arrayidx11.3.12.1, align 2, !tbaa !3 *)
mov v825 mem0_88;
(*   %sub.3.12.1 = sub i16 %825, %call.i.3.12.1 *)
sub v_sub_3_12_1 v825 v_call_i_3_12_1;
(*   store i16 %sub.3.12.1, i16* %arrayidx9.3.12.1, align 2, !tbaa !3 *)
mov mem0_120 v_sub_3_12_1;
(*   %add21.3.12.1 = add i16 %825, %call.i.3.12.1 *)
add v_add21_3_12_1 v825 v_call_i_3_12_1;
(*   store i16 %add21.3.12.1, i16* %arrayidx11.3.12.1, align 2, !tbaa !3 *)
mov mem0_88 v_add21_3_12_1;
(*   %arrayidx9.3.13.1 = getelementptr inbounds i16, i16* %r, i64 61 *)
(*   %826 = load i16, i16* %arrayidx9.3.13.1, align 2, !tbaa !3 *)
mov v826 mem0_122;
(*   %conv1.i.3.13.1 = sext i16 %826 to i32 *)
cast v_conv1_i_3_13_1@sint32 v826@sint16;
(*   %mul.i.3.13.1 = mul nsw i32 %conv1.i.3.13.1, 622 *)
mul v_mul_i_3_13_1 v_conv1_i_3_13_1 (622)@sint32;
(*   %call.i.3.13.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.13.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_13_1, v_call_i_3_13_1);
(*   %arrayidx11.3.13.1 = getelementptr inbounds i16, i16* %r, i64 45 *)
(*   %827 = load i16, i16* %arrayidx11.3.13.1, align 2, !tbaa !3 *)
mov v827 mem0_90;
(*   %sub.3.13.1 = sub i16 %827, %call.i.3.13.1 *)
sub v_sub_3_13_1 v827 v_call_i_3_13_1;
(*   store i16 %sub.3.13.1, i16* %arrayidx9.3.13.1, align 2, !tbaa !3 *)
mov mem0_122 v_sub_3_13_1;
(*   %add21.3.13.1 = add i16 %827, %call.i.3.13.1 *)
add v_add21_3_13_1 v827 v_call_i_3_13_1;
(*   store i16 %add21.3.13.1, i16* %arrayidx11.3.13.1, align 2, !tbaa !3 *)
mov mem0_90 v_add21_3_13_1;
(*   %arrayidx9.3.14.1 = getelementptr inbounds i16, i16* %r, i64 62 *)
(*   %828 = load i16, i16* %arrayidx9.3.14.1, align 2, !tbaa !3 *)
mov v828 mem0_124;
(*   %conv1.i.3.14.1 = sext i16 %828 to i32 *)
cast v_conv1_i_3_14_1@sint32 v828@sint16;
(*   %mul.i.3.14.1 = mul nsw i32 %conv1.i.3.14.1, 622 *)
mul v_mul_i_3_14_1 v_conv1_i_3_14_1 (622)@sint32;
(*   %call.i.3.14.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.14.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_14_1, v_call_i_3_14_1);
(*   %arrayidx11.3.14.1 = getelementptr inbounds i16, i16* %r, i64 46 *)
(*   %829 = load i16, i16* %arrayidx11.3.14.1, align 2, !tbaa !3 *)
mov v829 mem0_92;
(*   %sub.3.14.1 = sub i16 %829, %call.i.3.14.1 *)
sub v_sub_3_14_1 v829 v_call_i_3_14_1;
(*   store i16 %sub.3.14.1, i16* %arrayidx9.3.14.1, align 2, !tbaa !3 *)
mov mem0_124 v_sub_3_14_1;
(*   %add21.3.14.1 = add i16 %829, %call.i.3.14.1 *)
add v_add21_3_14_1 v829 v_call_i_3_14_1;
(*   store i16 %add21.3.14.1, i16* %arrayidx11.3.14.1, align 2, !tbaa !3 *)
mov mem0_92 v_add21_3_14_1;
(*   %arrayidx9.3.15.1 = getelementptr inbounds i16, i16* %r, i64 63 *)
(*   %830 = load i16, i16* %arrayidx9.3.15.1, align 2, !tbaa !3 *)
mov v830 mem0_126;
(*   %conv1.i.3.15.1 = sext i16 %830 to i32 *)
cast v_conv1_i_3_15_1@sint32 v830@sint16;
(*   %mul.i.3.15.1 = mul nsw i32 %conv1.i.3.15.1, 622 *)
mul v_mul_i_3_15_1 v_conv1_i_3_15_1 (622)@sint32;
(*   %call.i.3.15.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.15.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_15_1, v_call_i_3_15_1);
(*   %arrayidx11.3.15.1 = getelementptr inbounds i16, i16* %r, i64 47 *)
(*   %831 = load i16, i16* %arrayidx11.3.15.1, align 2, !tbaa !3 *)
mov v831 mem0_94;
(*   %sub.3.15.1 = sub i16 %831, %call.i.3.15.1 *)
sub v_sub_3_15_1 v831 v_call_i_3_15_1;
(*   store i16 %sub.3.15.1, i16* %arrayidx9.3.15.1, align 2, !tbaa !3 *)
mov mem0_126 v_sub_3_15_1;
(*   %add21.3.15.1 = add i16 %831, %call.i.3.15.1 *)
add v_add21_3_15_1 v831 v_call_i_3_15_1;
(*   store i16 %add21.3.15.1, i16* %arrayidx11.3.15.1, align 2, !tbaa !3 *)
mov mem0_94 v_add21_3_15_1;

(* NOTE: k = 10 *)

(*   %arrayidx9.3.2188 = getelementptr inbounds i16, i16* %r, i64 80 *)
(*   %832 = load i16, i16* %arrayidx9.3.2188, align 2, !tbaa !3 *)
mov v832 mem0_160;
(*   %conv1.i.3.2189 = sext i16 %832 to i32 *)
cast v_conv1_i_3_2189@sint32 v832@sint16;
(*   %mul.i.3.2190 = mul nsw i32 %conv1.i.3.2189, 1577 *)
mul v_mul_i_3_2190 v_conv1_i_3_2189 (1577)@sint32;
(*   %call.i.3.2191 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.2190) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_2190, v_call_i_3_2191);
(*   %arrayidx11.3.2192 = getelementptr inbounds i16, i16* %r, i64 64 *)
(*   %833 = load i16, i16* %arrayidx11.3.2192, align 2, !tbaa !3 *)
mov v833 mem0_128;
(*   %sub.3.2193 = sub i16 %833, %call.i.3.2191 *)
sub v_sub_3_2193 v833 v_call_i_3_2191;
(*   store i16 %sub.3.2193, i16* %arrayidx9.3.2188, align 2, !tbaa !3 *)
mov mem0_160 v_sub_3_2193;
(*   %add21.3.2194 = add i16 %833, %call.i.3.2191 *)
add v_add21_3_2194 v833 v_call_i_3_2191;
(*   store i16 %add21.3.2194, i16* %arrayidx11.3.2192, align 2, !tbaa !3 *)
mov mem0_128 v_add21_3_2194;
(*   %arrayidx9.3.1.2 = getelementptr inbounds i16, i16* %r, i64 81 *)
(*   %834 = load i16, i16* %arrayidx9.3.1.2, align 2, !tbaa !3 *)
mov v834 mem0_162;
(*   %conv1.i.3.1.2 = sext i16 %834 to i32 *)
cast v_conv1_i_3_1_2@sint32 v834@sint16;
(*   %mul.i.3.1.2 = mul nsw i32 %conv1.i.3.1.2, 1577 *)
mul v_mul_i_3_1_2 v_conv1_i_3_1_2 (1577)@sint32;
(*   %call.i.3.1.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.1.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_1_2, v_call_i_3_1_2);
(*   %arrayidx11.3.1.2 = getelementptr inbounds i16, i16* %r, i64 65 *)
(*   %835 = load i16, i16* %arrayidx11.3.1.2, align 2, !tbaa !3 *)
mov v835 mem0_130;
(*   %sub.3.1.2 = sub i16 %835, %call.i.3.1.2 *)
sub v_sub_3_1_2 v835 v_call_i_3_1_2;
(*   store i16 %sub.3.1.2, i16* %arrayidx9.3.1.2, align 2, !tbaa !3 *)
mov mem0_162 v_sub_3_1_2;
(*   %add21.3.1.2 = add i16 %835, %call.i.3.1.2 *)
add v_add21_3_1_2 v835 v_call_i_3_1_2;
(*   store i16 %add21.3.1.2, i16* %arrayidx11.3.1.2, align 2, !tbaa !3 *)
mov mem0_130 v_add21_3_1_2;
(*   %arrayidx9.3.2.2 = getelementptr inbounds i16, i16* %r, i64 82 *)
(*   %836 = load i16, i16* %arrayidx9.3.2.2, align 2, !tbaa !3 *)
mov v836 mem0_164;
(*   %conv1.i.3.2.2 = sext i16 %836 to i32 *)
cast v_conv1_i_3_2_2@sint32 v836@sint16;
(*   %mul.i.3.2.2 = mul nsw i32 %conv1.i.3.2.2, 1577 *)
mul v_mul_i_3_2_2 v_conv1_i_3_2_2 (1577)@sint32;
(*   %call.i.3.2.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.2.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_2_2, v_call_i_3_2_2);
(*   %arrayidx11.3.2.2 = getelementptr inbounds i16, i16* %r, i64 66 *)
(*   %837 = load i16, i16* %arrayidx11.3.2.2, align 2, !tbaa !3 *)
mov v837 mem0_132;
(*   %sub.3.2.2 = sub i16 %837, %call.i.3.2.2 *)
sub v_sub_3_2_2 v837 v_call_i_3_2_2;
(*   store i16 %sub.3.2.2, i16* %arrayidx9.3.2.2, align 2, !tbaa !3 *)
mov mem0_164 v_sub_3_2_2;
(*   %add21.3.2.2 = add i16 %837, %call.i.3.2.2 *)
add v_add21_3_2_2 v837 v_call_i_3_2_2;
(*   store i16 %add21.3.2.2, i16* %arrayidx11.3.2.2, align 2, !tbaa !3 *)
mov mem0_132 v_add21_3_2_2;
(*   %arrayidx9.3.3.2 = getelementptr inbounds i16, i16* %r, i64 83 *)
(*   %838 = load i16, i16* %arrayidx9.3.3.2, align 2, !tbaa !3 *)
mov v838 mem0_166;
(*   %conv1.i.3.3.2 = sext i16 %838 to i32 *)
cast v_conv1_i_3_3_2@sint32 v838@sint16;
(*   %mul.i.3.3.2 = mul nsw i32 %conv1.i.3.3.2, 1577 *)
mul v_mul_i_3_3_2 v_conv1_i_3_3_2 (1577)@sint32;
(*   %call.i.3.3.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.3.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_3_2, v_call_i_3_3_2);
(*   %arrayidx11.3.3.2 = getelementptr inbounds i16, i16* %r, i64 67 *)
(*   %839 = load i16, i16* %arrayidx11.3.3.2, align 2, !tbaa !3 *)
mov v839 mem0_134;
(*   %sub.3.3.2 = sub i16 %839, %call.i.3.3.2 *)
sub v_sub_3_3_2 v839 v_call_i_3_3_2;
(*   store i16 %sub.3.3.2, i16* %arrayidx9.3.3.2, align 2, !tbaa !3 *)
mov mem0_166 v_sub_3_3_2;
(*   %add21.3.3.2 = add i16 %839, %call.i.3.3.2 *)
add v_add21_3_3_2 v839 v_call_i_3_3_2;
(*   store i16 %add21.3.3.2, i16* %arrayidx11.3.3.2, align 2, !tbaa !3 *)
mov mem0_134 v_add21_3_3_2;
(*   %arrayidx9.3.4.2 = getelementptr inbounds i16, i16* %r, i64 84 *)
(*   %840 = load i16, i16* %arrayidx9.3.4.2, align 2, !tbaa !3 *)
mov v840 mem0_168;
(*   %conv1.i.3.4.2 = sext i16 %840 to i32 *)
cast v_conv1_i_3_4_2@sint32 v840@sint16;
(*   %mul.i.3.4.2 = mul nsw i32 %conv1.i.3.4.2, 1577 *)
mul v_mul_i_3_4_2 v_conv1_i_3_4_2 (1577)@sint32;
(*   %call.i.3.4.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.4.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_4_2, v_call_i_3_4_2);
(*   %arrayidx11.3.4.2 = getelementptr inbounds i16, i16* %r, i64 68 *)
(*   %841 = load i16, i16* %arrayidx11.3.4.2, align 2, !tbaa !3 *)
mov v841 mem0_136;
(*   %sub.3.4.2 = sub i16 %841, %call.i.3.4.2 *)
sub v_sub_3_4_2 v841 v_call_i_3_4_2;
(*   store i16 %sub.3.4.2, i16* %arrayidx9.3.4.2, align 2, !tbaa !3 *)
mov mem0_168 v_sub_3_4_2;
(*   %add21.3.4.2 = add i16 %841, %call.i.3.4.2 *)
add v_add21_3_4_2 v841 v_call_i_3_4_2;
(*   store i16 %add21.3.4.2, i16* %arrayidx11.3.4.2, align 2, !tbaa !3 *)
mov mem0_136 v_add21_3_4_2;
(*   %arrayidx9.3.5.2 = getelementptr inbounds i16, i16* %r, i64 85 *)
(*   %842 = load i16, i16* %arrayidx9.3.5.2, align 2, !tbaa !3 *)
mov v842 mem0_170;
(*   %conv1.i.3.5.2 = sext i16 %842 to i32 *)
cast v_conv1_i_3_5_2@sint32 v842@sint16;
(*   %mul.i.3.5.2 = mul nsw i32 %conv1.i.3.5.2, 1577 *)
mul v_mul_i_3_5_2 v_conv1_i_3_5_2 (1577)@sint32;
(*   %call.i.3.5.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.5.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_5_2, v_call_i_3_5_2);
(*   %arrayidx11.3.5.2 = getelementptr inbounds i16, i16* %r, i64 69 *)
(*   %843 = load i16, i16* %arrayidx11.3.5.2, align 2, !tbaa !3 *)
mov v843 mem0_138;
(*   %sub.3.5.2 = sub i16 %843, %call.i.3.5.2 *)
sub v_sub_3_5_2 v843 v_call_i_3_5_2;
(*   store i16 %sub.3.5.2, i16* %arrayidx9.3.5.2, align 2, !tbaa !3 *)
mov mem0_170 v_sub_3_5_2;
(*   %add21.3.5.2 = add i16 %843, %call.i.3.5.2 *)
add v_add21_3_5_2 v843 v_call_i_3_5_2;
(*   store i16 %add21.3.5.2, i16* %arrayidx11.3.5.2, align 2, !tbaa !3 *)
mov mem0_138 v_add21_3_5_2;
(*   %arrayidx9.3.6.2 = getelementptr inbounds i16, i16* %r, i64 86 *)
(*   %844 = load i16, i16* %arrayidx9.3.6.2, align 2, !tbaa !3 *)
mov v844 mem0_172;
(*   %conv1.i.3.6.2 = sext i16 %844 to i32 *)
cast v_conv1_i_3_6_2@sint32 v844@sint16;
(*   %mul.i.3.6.2 = mul nsw i32 %conv1.i.3.6.2, 1577 *)
mul v_mul_i_3_6_2 v_conv1_i_3_6_2 (1577)@sint32;
(*   %call.i.3.6.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.6.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_6_2, v_call_i_3_6_2);
(*   %arrayidx11.3.6.2 = getelementptr inbounds i16, i16* %r, i64 70 *)
(*   %845 = load i16, i16* %arrayidx11.3.6.2, align 2, !tbaa !3 *)
mov v845 mem0_140;
(*   %sub.3.6.2 = sub i16 %845, %call.i.3.6.2 *)
sub v_sub_3_6_2 v845 v_call_i_3_6_2;
(*   store i16 %sub.3.6.2, i16* %arrayidx9.3.6.2, align 2, !tbaa !3 *)
mov mem0_172 v_sub_3_6_2;
(*   %add21.3.6.2 = add i16 %845, %call.i.3.6.2 *)
add v_add21_3_6_2 v845 v_call_i_3_6_2;
(*   store i16 %add21.3.6.2, i16* %arrayidx11.3.6.2, align 2, !tbaa !3 *)
mov mem0_140 v_add21_3_6_2;
(*   %arrayidx9.3.7.2 = getelementptr inbounds i16, i16* %r, i64 87 *)
(*   %846 = load i16, i16* %arrayidx9.3.7.2, align 2, !tbaa !3 *)
mov v846 mem0_174;
(*   %conv1.i.3.7.2 = sext i16 %846 to i32 *)
cast v_conv1_i_3_7_2@sint32 v846@sint16;
(*   %mul.i.3.7.2 = mul nsw i32 %conv1.i.3.7.2, 1577 *)
mul v_mul_i_3_7_2 v_conv1_i_3_7_2 (1577)@sint32;
(*   %call.i.3.7.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.7.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_7_2, v_call_i_3_7_2);
(*   %arrayidx11.3.7.2 = getelementptr inbounds i16, i16* %r, i64 71 *)
(*   %847 = load i16, i16* %arrayidx11.3.7.2, align 2, !tbaa !3 *)
mov v847 mem0_142;
(*   %sub.3.7.2 = sub i16 %847, %call.i.3.7.2 *)
sub v_sub_3_7_2 v847 v_call_i_3_7_2;
(*   store i16 %sub.3.7.2, i16* %arrayidx9.3.7.2, align 2, !tbaa !3 *)
mov mem0_174 v_sub_3_7_2;
(*   %add21.3.7.2 = add i16 %847, %call.i.3.7.2 *)
add v_add21_3_7_2 v847 v_call_i_3_7_2;
(*   store i16 %add21.3.7.2, i16* %arrayidx11.3.7.2, align 2, !tbaa !3 *)
mov mem0_142 v_add21_3_7_2;
(*   %arrayidx9.3.8.2 = getelementptr inbounds i16, i16* %r, i64 88 *)
(*   %848 = load i16, i16* %arrayidx9.3.8.2, align 2, !tbaa !3 *)
mov v848 mem0_176;
(*   %conv1.i.3.8.2 = sext i16 %848 to i32 *)
cast v_conv1_i_3_8_2@sint32 v848@sint16;
(*   %mul.i.3.8.2 = mul nsw i32 %conv1.i.3.8.2, 1577 *)
mul v_mul_i_3_8_2 v_conv1_i_3_8_2 (1577)@sint32;
(*   %call.i.3.8.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.8.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_8_2, v_call_i_3_8_2);
(*   %arrayidx11.3.8.2 = getelementptr inbounds i16, i16* %r, i64 72 *)
(*   %849 = load i16, i16* %arrayidx11.3.8.2, align 2, !tbaa !3 *)
mov v849 mem0_144;
(*   %sub.3.8.2 = sub i16 %849, %call.i.3.8.2 *)
sub v_sub_3_8_2 v849 v_call_i_3_8_2;
(*   store i16 %sub.3.8.2, i16* %arrayidx9.3.8.2, align 2, !tbaa !3 *)
mov mem0_176 v_sub_3_8_2;
(*   %add21.3.8.2 = add i16 %849, %call.i.3.8.2 *)
add v_add21_3_8_2 v849 v_call_i_3_8_2;
(*   store i16 %add21.3.8.2, i16* %arrayidx11.3.8.2, align 2, !tbaa !3 *)
mov mem0_144 v_add21_3_8_2;
(*   %arrayidx9.3.9.2 = getelementptr inbounds i16, i16* %r, i64 89 *)
(*   %850 = load i16, i16* %arrayidx9.3.9.2, align 2, !tbaa !3 *)
mov v850 mem0_178;
(*   %conv1.i.3.9.2 = sext i16 %850 to i32 *)
cast v_conv1_i_3_9_2@sint32 v850@sint16;
(*   %mul.i.3.9.2 = mul nsw i32 %conv1.i.3.9.2, 1577 *)
mul v_mul_i_3_9_2 v_conv1_i_3_9_2 (1577)@sint32;
(*   %call.i.3.9.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.9.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_9_2, v_call_i_3_9_2);
(*   %arrayidx11.3.9.2 = getelementptr inbounds i16, i16* %r, i64 73 *)
(*   %851 = load i16, i16* %arrayidx11.3.9.2, align 2, !tbaa !3 *)
mov v851 mem0_146;
(*   %sub.3.9.2 = sub i16 %851, %call.i.3.9.2 *)
sub v_sub_3_9_2 v851 v_call_i_3_9_2;
(*   store i16 %sub.3.9.2, i16* %arrayidx9.3.9.2, align 2, !tbaa !3 *)
mov mem0_178 v_sub_3_9_2;
(*   %add21.3.9.2 = add i16 %851, %call.i.3.9.2 *)
add v_add21_3_9_2 v851 v_call_i_3_9_2;
(*   store i16 %add21.3.9.2, i16* %arrayidx11.3.9.2, align 2, !tbaa !3 *)
mov mem0_146 v_add21_3_9_2;
(*   %arrayidx9.3.10.2 = getelementptr inbounds i16, i16* %r, i64 90 *)
(*   %852 = load i16, i16* %arrayidx9.3.10.2, align 2, !tbaa !3 *)
mov v852 mem0_180;
(*   %conv1.i.3.10.2 = sext i16 %852 to i32 *)
cast v_conv1_i_3_10_2@sint32 v852@sint16;
(*   %mul.i.3.10.2 = mul nsw i32 %conv1.i.3.10.2, 1577 *)
mul v_mul_i_3_10_2 v_conv1_i_3_10_2 (1577)@sint32;
(*   %call.i.3.10.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.10.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_10_2, v_call_i_3_10_2);
(*   %arrayidx11.3.10.2 = getelementptr inbounds i16, i16* %r, i64 74 *)
(*   %853 = load i16, i16* %arrayidx11.3.10.2, align 2, !tbaa !3 *)
mov v853 mem0_148;
(*   %sub.3.10.2 = sub i16 %853, %call.i.3.10.2 *)
sub v_sub_3_10_2 v853 v_call_i_3_10_2;
(*   store i16 %sub.3.10.2, i16* %arrayidx9.3.10.2, align 2, !tbaa !3 *)
mov mem0_180 v_sub_3_10_2;
(*   %add21.3.10.2 = add i16 %853, %call.i.3.10.2 *)
add v_add21_3_10_2 v853 v_call_i_3_10_2;
(*   store i16 %add21.3.10.2, i16* %arrayidx11.3.10.2, align 2, !tbaa !3 *)
mov mem0_148 v_add21_3_10_2;
(*   %arrayidx9.3.11.2 = getelementptr inbounds i16, i16* %r, i64 91 *)
(*   %854 = load i16, i16* %arrayidx9.3.11.2, align 2, !tbaa !3 *)
mov v854 mem0_182;
(*   %conv1.i.3.11.2 = sext i16 %854 to i32 *)
cast v_conv1_i_3_11_2@sint32 v854@sint16;
(*   %mul.i.3.11.2 = mul nsw i32 %conv1.i.3.11.2, 1577 *)
mul v_mul_i_3_11_2 v_conv1_i_3_11_2 (1577)@sint32;
(*   %call.i.3.11.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.11.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_11_2, v_call_i_3_11_2);
(*   %arrayidx11.3.11.2 = getelementptr inbounds i16, i16* %r, i64 75 *)
(*   %855 = load i16, i16* %arrayidx11.3.11.2, align 2, !tbaa !3 *)
mov v855 mem0_150;
(*   %sub.3.11.2 = sub i16 %855, %call.i.3.11.2 *)
sub v_sub_3_11_2 v855 v_call_i_3_11_2;
(*   store i16 %sub.3.11.2, i16* %arrayidx9.3.11.2, align 2, !tbaa !3 *)
mov mem0_182 v_sub_3_11_2;
(*   %add21.3.11.2 = add i16 %855, %call.i.3.11.2 *)
add v_add21_3_11_2 v855 v_call_i_3_11_2;
(*   store i16 %add21.3.11.2, i16* %arrayidx11.3.11.2, align 2, !tbaa !3 *)
mov mem0_150 v_add21_3_11_2;
(*   %arrayidx9.3.12.2 = getelementptr inbounds i16, i16* %r, i64 92 *)
(*   %856 = load i16, i16* %arrayidx9.3.12.2, align 2, !tbaa !3 *)
mov v856 mem0_184;
(*   %conv1.i.3.12.2 = sext i16 %856 to i32 *)
cast v_conv1_i_3_12_2@sint32 v856@sint16;
(*   %mul.i.3.12.2 = mul nsw i32 %conv1.i.3.12.2, 1577 *)
mul v_mul_i_3_12_2 v_conv1_i_3_12_2 (1577)@sint32;
(*   %call.i.3.12.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.12.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_12_2, v_call_i_3_12_2);
(*   %arrayidx11.3.12.2 = getelementptr inbounds i16, i16* %r, i64 76 *)
(*   %857 = load i16, i16* %arrayidx11.3.12.2, align 2, !tbaa !3 *)
mov v857 mem0_152;
(*   %sub.3.12.2 = sub i16 %857, %call.i.3.12.2 *)
sub v_sub_3_12_2 v857 v_call_i_3_12_2;
(*   store i16 %sub.3.12.2, i16* %arrayidx9.3.12.2, align 2, !tbaa !3 *)
mov mem0_184 v_sub_3_12_2;
(*   %add21.3.12.2 = add i16 %857, %call.i.3.12.2 *)
add v_add21_3_12_2 v857 v_call_i_3_12_2;
(*   store i16 %add21.3.12.2, i16* %arrayidx11.3.12.2, align 2, !tbaa !3 *)
mov mem0_152 v_add21_3_12_2;
(*   %arrayidx9.3.13.2 = getelementptr inbounds i16, i16* %r, i64 93 *)
(*   %858 = load i16, i16* %arrayidx9.3.13.2, align 2, !tbaa !3 *)
mov v858 mem0_186;
(*   %conv1.i.3.13.2 = sext i16 %858 to i32 *)
cast v_conv1_i_3_13_2@sint32 v858@sint16;
(*   %mul.i.3.13.2 = mul nsw i32 %conv1.i.3.13.2, 1577 *)
mul v_mul_i_3_13_2 v_conv1_i_3_13_2 (1577)@sint32;
(*   %call.i.3.13.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.13.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_13_2, v_call_i_3_13_2);
(*   %arrayidx11.3.13.2 = getelementptr inbounds i16, i16* %r, i64 77 *)
(*   %859 = load i16, i16* %arrayidx11.3.13.2, align 2, !tbaa !3 *)
mov v859 mem0_154;
(*   %sub.3.13.2 = sub i16 %859, %call.i.3.13.2 *)
sub v_sub_3_13_2 v859 v_call_i_3_13_2;
(*   store i16 %sub.3.13.2, i16* %arrayidx9.3.13.2, align 2, !tbaa !3 *)
mov mem0_186 v_sub_3_13_2;
(*   %add21.3.13.2 = add i16 %859, %call.i.3.13.2 *)
add v_add21_3_13_2 v859 v_call_i_3_13_2;
(*   store i16 %add21.3.13.2, i16* %arrayidx11.3.13.2, align 2, !tbaa !3 *)
mov mem0_154 v_add21_3_13_2;
(*   %arrayidx9.3.14.2 = getelementptr inbounds i16, i16* %r, i64 94 *)
(*   %860 = load i16, i16* %arrayidx9.3.14.2, align 2, !tbaa !3 *)
mov v860 mem0_188;
(*   %conv1.i.3.14.2 = sext i16 %860 to i32 *)
cast v_conv1_i_3_14_2@sint32 v860@sint16;
(*   %mul.i.3.14.2 = mul nsw i32 %conv1.i.3.14.2, 1577 *)
mul v_mul_i_3_14_2 v_conv1_i_3_14_2 (1577)@sint32;
(*   %call.i.3.14.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.14.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_14_2, v_call_i_3_14_2);
(*   %arrayidx11.3.14.2 = getelementptr inbounds i16, i16* %r, i64 78 *)
(*   %861 = load i16, i16* %arrayidx11.3.14.2, align 2, !tbaa !3 *)
mov v861 mem0_156;
(*   %sub.3.14.2 = sub i16 %861, %call.i.3.14.2 *)
sub v_sub_3_14_2 v861 v_call_i_3_14_2;
(*   store i16 %sub.3.14.2, i16* %arrayidx9.3.14.2, align 2, !tbaa !3 *)
mov mem0_188 v_sub_3_14_2;
(*   %add21.3.14.2 = add i16 %861, %call.i.3.14.2 *)
add v_add21_3_14_2 v861 v_call_i_3_14_2;
(*   store i16 %add21.3.14.2, i16* %arrayidx11.3.14.2, align 2, !tbaa !3 *)
mov mem0_156 v_add21_3_14_2;
(*   %arrayidx9.3.15.2 = getelementptr inbounds i16, i16* %r, i64 95 *)
(*   %862 = load i16, i16* %arrayidx9.3.15.2, align 2, !tbaa !3 *)
mov v862 mem0_190;
(*   %conv1.i.3.15.2 = sext i16 %862 to i32 *)
cast v_conv1_i_3_15_2@sint32 v862@sint16;
(*   %mul.i.3.15.2 = mul nsw i32 %conv1.i.3.15.2, 1577 *)
mul v_mul_i_3_15_2 v_conv1_i_3_15_2 (1577)@sint32;
(*   %call.i.3.15.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.15.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_15_2, v_call_i_3_15_2);
(*   %arrayidx11.3.15.2 = getelementptr inbounds i16, i16* %r, i64 79 *)
(*   %863 = load i16, i16* %arrayidx11.3.15.2, align 2, !tbaa !3 *)
mov v863 mem0_158;
(*   %sub.3.15.2 = sub i16 %863, %call.i.3.15.2 *)
sub v_sub_3_15_2 v863 v_call_i_3_15_2;
(*   store i16 %sub.3.15.2, i16* %arrayidx9.3.15.2, align 2, !tbaa !3 *)
mov mem0_190 v_sub_3_15_2;
(*   %add21.3.15.2 = add i16 %863, %call.i.3.15.2 *)
add v_add21_3_15_2 v863 v_call_i_3_15_2;
(*   store i16 %add21.3.15.2, i16* %arrayidx11.3.15.2, align 2, !tbaa !3 *)
mov mem0_158 v_add21_3_15_2;

(* NOTE: k = 11 *)

(*   %arrayidx9.3.3198 = getelementptr inbounds i16, i16* %r, i64 112 *)
(*   %864 = load i16, i16* %arrayidx9.3.3198, align 2, !tbaa !3 *)
mov v864 mem0_224;
(*   %conv1.i.3.3199 = sext i16 %864 to i32 *)
cast v_conv1_i_3_3199@sint32 v864@sint16;
(*   %mul.i.3.3200 = mul nsw i32 %conv1.i.3.3199, 182 *)
mul v_mul_i_3_3200 v_conv1_i_3_3199 (182)@sint32;
(*   %call.i.3.3201 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.3200) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_3200, v_call_i_3_3201);
(*   %arrayidx11.3.3202 = getelementptr inbounds i16, i16* %r, i64 96 *)
(*   %865 = load i16, i16* %arrayidx11.3.3202, align 2, !tbaa !3 *)
mov v865 mem0_192;
(*   %sub.3.3203 = sub i16 %865, %call.i.3.3201 *)
sub v_sub_3_3203 v865 v_call_i_3_3201;
(*   store i16 %sub.3.3203, i16* %arrayidx9.3.3198, align 2, !tbaa !3 *)
mov mem0_224 v_sub_3_3203;
(*   %add21.3.3204 = add i16 %865, %call.i.3.3201 *)
add v_add21_3_3204 v865 v_call_i_3_3201;
(*   store i16 %add21.3.3204, i16* %arrayidx11.3.3202, align 2, !tbaa !3 *)
mov mem0_192 v_add21_3_3204;
(*   %arrayidx9.3.1.3 = getelementptr inbounds i16, i16* %r, i64 113 *)
(*   %866 = load i16, i16* %arrayidx9.3.1.3, align 2, !tbaa !3 *)
mov v866 mem0_226;
(*   %conv1.i.3.1.3 = sext i16 %866 to i32 *)
cast v_conv1_i_3_1_3@sint32 v866@sint16;
(*   %mul.i.3.1.3 = mul nsw i32 %conv1.i.3.1.3, 182 *)
mul v_mul_i_3_1_3 v_conv1_i_3_1_3 (182)@sint32;
(*   %call.i.3.1.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.1.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_1_3, v_call_i_3_1_3);
(*   %arrayidx11.3.1.3 = getelementptr inbounds i16, i16* %r, i64 97 *)
(*   %867 = load i16, i16* %arrayidx11.3.1.3, align 2, !tbaa !3 *)
mov v867 mem0_194;
(*   %sub.3.1.3 = sub i16 %867, %call.i.3.1.3 *)
sub v_sub_3_1_3 v867 v_call_i_3_1_3;
(*   store i16 %sub.3.1.3, i16* %arrayidx9.3.1.3, align 2, !tbaa !3 *)
mov mem0_226 v_sub_3_1_3;
(*   %add21.3.1.3 = add i16 %867, %call.i.3.1.3 *)
add v_add21_3_1_3 v867 v_call_i_3_1_3;
(*   store i16 %add21.3.1.3, i16* %arrayidx11.3.1.3, align 2, !tbaa !3 *)
mov mem0_194 v_add21_3_1_3;
(*   %arrayidx9.3.2.3 = getelementptr inbounds i16, i16* %r, i64 114 *)
(*   %868 = load i16, i16* %arrayidx9.3.2.3, align 2, !tbaa !3 *)
mov v868 mem0_228;
(*   %conv1.i.3.2.3 = sext i16 %868 to i32 *)
cast v_conv1_i_3_2_3@sint32 v868@sint16;
(*   %mul.i.3.2.3 = mul nsw i32 %conv1.i.3.2.3, 182 *)
mul v_mul_i_3_2_3 v_conv1_i_3_2_3 (182)@sint32;
(*   %call.i.3.2.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.2.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_2_3, v_call_i_3_2_3);
(*   %arrayidx11.3.2.3 = getelementptr inbounds i16, i16* %r, i64 98 *)
(*   %869 = load i16, i16* %arrayidx11.3.2.3, align 2, !tbaa !3 *)
mov v869 mem0_196;
(*   %sub.3.2.3 = sub i16 %869, %call.i.3.2.3 *)
sub v_sub_3_2_3 v869 v_call_i_3_2_3;
(*   store i16 %sub.3.2.3, i16* %arrayidx9.3.2.3, align 2, !tbaa !3 *)
mov mem0_228 v_sub_3_2_3;
(*   %add21.3.2.3 = add i16 %869, %call.i.3.2.3 *)
add v_add21_3_2_3 v869 v_call_i_3_2_3;
(*   store i16 %add21.3.2.3, i16* %arrayidx11.3.2.3, align 2, !tbaa !3 *)
mov mem0_196 v_add21_3_2_3;
(*   %arrayidx9.3.3.3 = getelementptr inbounds i16, i16* %r, i64 115 *)
(*   %870 = load i16, i16* %arrayidx9.3.3.3, align 2, !tbaa !3 *)
mov v870 mem0_230;
(*   %conv1.i.3.3.3 = sext i16 %870 to i32 *)
cast v_conv1_i_3_3_3@sint32 v870@sint16;
(*   %mul.i.3.3.3 = mul nsw i32 %conv1.i.3.3.3, 182 *)
mul v_mul_i_3_3_3 v_conv1_i_3_3_3 (182)@sint32;
(*   %call.i.3.3.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.3.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_3_3, v_call_i_3_3_3);
(*   %arrayidx11.3.3.3 = getelementptr inbounds i16, i16* %r, i64 99 *)
(*   %871 = load i16, i16* %arrayidx11.3.3.3, align 2, !tbaa !3 *)
mov v871 mem0_198;
(*   %sub.3.3.3 = sub i16 %871, %call.i.3.3.3 *)
sub v_sub_3_3_3 v871 v_call_i_3_3_3;
(*   store i16 %sub.3.3.3, i16* %arrayidx9.3.3.3, align 2, !tbaa !3 *)
mov mem0_230 v_sub_3_3_3;
(*   %add21.3.3.3 = add i16 %871, %call.i.3.3.3 *)
add v_add21_3_3_3 v871 v_call_i_3_3_3;
(*   store i16 %add21.3.3.3, i16* %arrayidx11.3.3.3, align 2, !tbaa !3 *)
mov mem0_198 v_add21_3_3_3;
(*   %arrayidx9.3.4.3 = getelementptr inbounds i16, i16* %r, i64 116 *)
(*   %872 = load i16, i16* %arrayidx9.3.4.3, align 2, !tbaa !3 *)
mov v872 mem0_232;
(*   %conv1.i.3.4.3 = sext i16 %872 to i32 *)
cast v_conv1_i_3_4_3@sint32 v872@sint16;
(*   %mul.i.3.4.3 = mul nsw i32 %conv1.i.3.4.3, 182 *)
mul v_mul_i_3_4_3 v_conv1_i_3_4_3 (182)@sint32;
(*   %call.i.3.4.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.4.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_4_3, v_call_i_3_4_3);
(*   %arrayidx11.3.4.3 = getelementptr inbounds i16, i16* %r, i64 100 *)
(*   %873 = load i16, i16* %arrayidx11.3.4.3, align 2, !tbaa !3 *)
mov v873 mem0_200;
(*   %sub.3.4.3 = sub i16 %873, %call.i.3.4.3 *)
sub v_sub_3_4_3 v873 v_call_i_3_4_3;
(*   store i16 %sub.3.4.3, i16* %arrayidx9.3.4.3, align 2, !tbaa !3 *)
mov mem0_232 v_sub_3_4_3;
(*   %add21.3.4.3 = add i16 %873, %call.i.3.4.3 *)
add v_add21_3_4_3 v873 v_call_i_3_4_3;
(*   store i16 %add21.3.4.3, i16* %arrayidx11.3.4.3, align 2, !tbaa !3 *)
mov mem0_200 v_add21_3_4_3;
(*   %arrayidx9.3.5.3 = getelementptr inbounds i16, i16* %r, i64 117 *)
(*   %874 = load i16, i16* %arrayidx9.3.5.3, align 2, !tbaa !3 *)
mov v874 mem0_234;
(*   %conv1.i.3.5.3 = sext i16 %874 to i32 *)
cast v_conv1_i_3_5_3@sint32 v874@sint16;
(*   %mul.i.3.5.3 = mul nsw i32 %conv1.i.3.5.3, 182 *)
mul v_mul_i_3_5_3 v_conv1_i_3_5_3 (182)@sint32;
(*   %call.i.3.5.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.5.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_5_3, v_call_i_3_5_3);
(*   %arrayidx11.3.5.3 = getelementptr inbounds i16, i16* %r, i64 101 *)
(*   %875 = load i16, i16* %arrayidx11.3.5.3, align 2, !tbaa !3 *)
mov v875 mem0_202;
(*   %sub.3.5.3 = sub i16 %875, %call.i.3.5.3 *)
sub v_sub_3_5_3 v875 v_call_i_3_5_3;
(*   store i16 %sub.3.5.3, i16* %arrayidx9.3.5.3, align 2, !tbaa !3 *)
mov mem0_234 v_sub_3_5_3;
(*   %add21.3.5.3 = add i16 %875, %call.i.3.5.3 *)
add v_add21_3_5_3 v875 v_call_i_3_5_3;
(*   store i16 %add21.3.5.3, i16* %arrayidx11.3.5.3, align 2, !tbaa !3 *)
mov mem0_202 v_add21_3_5_3;
(*   %arrayidx9.3.6.3 = getelementptr inbounds i16, i16* %r, i64 118 *)
(*   %876 = load i16, i16* %arrayidx9.3.6.3, align 2, !tbaa !3 *)
mov v876 mem0_236;
(*   %conv1.i.3.6.3 = sext i16 %876 to i32 *)
cast v_conv1_i_3_6_3@sint32 v876@sint16;
(*   %mul.i.3.6.3 = mul nsw i32 %conv1.i.3.6.3, 182 *)
mul v_mul_i_3_6_3 v_conv1_i_3_6_3 (182)@sint32;
(*   %call.i.3.6.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.6.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_6_3, v_call_i_3_6_3);
(*   %arrayidx11.3.6.3 = getelementptr inbounds i16, i16* %r, i64 102 *)
(*   %877 = load i16, i16* %arrayidx11.3.6.3, align 2, !tbaa !3 *)
mov v877 mem0_204;
(*   %sub.3.6.3 = sub i16 %877, %call.i.3.6.3 *)
sub v_sub_3_6_3 v877 v_call_i_3_6_3;
(*   store i16 %sub.3.6.3, i16* %arrayidx9.3.6.3, align 2, !tbaa !3 *)
mov mem0_236 v_sub_3_6_3;
(*   %add21.3.6.3 = add i16 %877, %call.i.3.6.3 *)
add v_add21_3_6_3 v877 v_call_i_3_6_3;
(*   store i16 %add21.3.6.3, i16* %arrayidx11.3.6.3, align 2, !tbaa !3 *)
mov mem0_204 v_add21_3_6_3;
(*   %arrayidx9.3.7.3 = getelementptr inbounds i16, i16* %r, i64 119 *)
(*   %878 = load i16, i16* %arrayidx9.3.7.3, align 2, !tbaa !3 *)
mov v878 mem0_238;
(*   %conv1.i.3.7.3 = sext i16 %878 to i32 *)
cast v_conv1_i_3_7_3@sint32 v878@sint16;
(*   %mul.i.3.7.3 = mul nsw i32 %conv1.i.3.7.3, 182 *)
mul v_mul_i_3_7_3 v_conv1_i_3_7_3 (182)@sint32;
(*   %call.i.3.7.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.7.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_7_3, v_call_i_3_7_3);
(*   %arrayidx11.3.7.3 = getelementptr inbounds i16, i16* %r, i64 103 *)
(*   %879 = load i16, i16* %arrayidx11.3.7.3, align 2, !tbaa !3 *)
mov v879 mem0_206;
(*   %sub.3.7.3 = sub i16 %879, %call.i.3.7.3 *)
sub v_sub_3_7_3 v879 v_call_i_3_7_3;
(*   store i16 %sub.3.7.3, i16* %arrayidx9.3.7.3, align 2, !tbaa !3 *)
mov mem0_238 v_sub_3_7_3;
(*   %add21.3.7.3 = add i16 %879, %call.i.3.7.3 *)
add v_add21_3_7_3 v879 v_call_i_3_7_3;
(*   store i16 %add21.3.7.3, i16* %arrayidx11.3.7.3, align 2, !tbaa !3 *)
mov mem0_206 v_add21_3_7_3;
(*   %arrayidx9.3.8.3 = getelementptr inbounds i16, i16* %r, i64 120 *)
(*   %880 = load i16, i16* %arrayidx9.3.8.3, align 2, !tbaa !3 *)
mov v880 mem0_240;
(*   %conv1.i.3.8.3 = sext i16 %880 to i32 *)
cast v_conv1_i_3_8_3@sint32 v880@sint16;
(*   %mul.i.3.8.3 = mul nsw i32 %conv1.i.3.8.3, 182 *)
mul v_mul_i_3_8_3 v_conv1_i_3_8_3 (182)@sint32;
(*   %call.i.3.8.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.8.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_8_3, v_call_i_3_8_3);
(*   %arrayidx11.3.8.3 = getelementptr inbounds i16, i16* %r, i64 104 *)
(*   %881 = load i16, i16* %arrayidx11.3.8.3, align 2, !tbaa !3 *)
mov v881 mem0_208;
(*   %sub.3.8.3 = sub i16 %881, %call.i.3.8.3 *)
sub v_sub_3_8_3 v881 v_call_i_3_8_3;
(*   store i16 %sub.3.8.3, i16* %arrayidx9.3.8.3, align 2, !tbaa !3 *)
mov mem0_240 v_sub_3_8_3;
(*   %add21.3.8.3 = add i16 %881, %call.i.3.8.3 *)
add v_add21_3_8_3 v881 v_call_i_3_8_3;
(*   store i16 %add21.3.8.3, i16* %arrayidx11.3.8.3, align 2, !tbaa !3 *)
mov mem0_208 v_add21_3_8_3;
(*   %arrayidx9.3.9.3 = getelementptr inbounds i16, i16* %r, i64 121 *)
(*   %882 = load i16, i16* %arrayidx9.3.9.3, align 2, !tbaa !3 *)
mov v882 mem0_242;
(*   %conv1.i.3.9.3 = sext i16 %882 to i32 *)
cast v_conv1_i_3_9_3@sint32 v882@sint16;
(*   %mul.i.3.9.3 = mul nsw i32 %conv1.i.3.9.3, 182 *)
mul v_mul_i_3_9_3 v_conv1_i_3_9_3 (182)@sint32;
(*   %call.i.3.9.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.9.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_9_3, v_call_i_3_9_3);
(*   %arrayidx11.3.9.3 = getelementptr inbounds i16, i16* %r, i64 105 *)
(*   %883 = load i16, i16* %arrayidx11.3.9.3, align 2, !tbaa !3 *)
mov v883 mem0_210;
(*   %sub.3.9.3 = sub i16 %883, %call.i.3.9.3 *)
sub v_sub_3_9_3 v883 v_call_i_3_9_3;
(*   store i16 %sub.3.9.3, i16* %arrayidx9.3.9.3, align 2, !tbaa !3 *)
mov mem0_242 v_sub_3_9_3;
(*   %add21.3.9.3 = add i16 %883, %call.i.3.9.3 *)
add v_add21_3_9_3 v883 v_call_i_3_9_3;
(*   store i16 %add21.3.9.3, i16* %arrayidx11.3.9.3, align 2, !tbaa !3 *)
mov mem0_210 v_add21_3_9_3;
(*   %arrayidx9.3.10.3 = getelementptr inbounds i16, i16* %r, i64 122 *)
(*   %884 = load i16, i16* %arrayidx9.3.10.3, align 2, !tbaa !3 *)
mov v884 mem0_244;
(*   %conv1.i.3.10.3 = sext i16 %884 to i32 *)
cast v_conv1_i_3_10_3@sint32 v884@sint16;
(*   %mul.i.3.10.3 = mul nsw i32 %conv1.i.3.10.3, 182 *)
mul v_mul_i_3_10_3 v_conv1_i_3_10_3 (182)@sint32;
(*   %call.i.3.10.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.10.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_10_3, v_call_i_3_10_3);
(*   %arrayidx11.3.10.3 = getelementptr inbounds i16, i16* %r, i64 106 *)
(*   %885 = load i16, i16* %arrayidx11.3.10.3, align 2, !tbaa !3 *)
mov v885 mem0_212;
(*   %sub.3.10.3 = sub i16 %885, %call.i.3.10.3 *)
sub v_sub_3_10_3 v885 v_call_i_3_10_3;
(*   store i16 %sub.3.10.3, i16* %arrayidx9.3.10.3, align 2, !tbaa !3 *)
mov mem0_244 v_sub_3_10_3;
(*   %add21.3.10.3 = add i16 %885, %call.i.3.10.3 *)
add v_add21_3_10_3 v885 v_call_i_3_10_3;
(*   store i16 %add21.3.10.3, i16* %arrayidx11.3.10.3, align 2, !tbaa !3 *)
mov mem0_212 v_add21_3_10_3;
(*   %arrayidx9.3.11.3 = getelementptr inbounds i16, i16* %r, i64 123 *)
(*   %886 = load i16, i16* %arrayidx9.3.11.3, align 2, !tbaa !3 *)
mov v886 mem0_246;
(*   %conv1.i.3.11.3 = sext i16 %886 to i32 *)
cast v_conv1_i_3_11_3@sint32 v886@sint16;
(*   %mul.i.3.11.3 = mul nsw i32 %conv1.i.3.11.3, 182 *)
mul v_mul_i_3_11_3 v_conv1_i_3_11_3 (182)@sint32;
(*   %call.i.3.11.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.11.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_11_3, v_call_i_3_11_3);
(*   %arrayidx11.3.11.3 = getelementptr inbounds i16, i16* %r, i64 107 *)
(*   %887 = load i16, i16* %arrayidx11.3.11.3, align 2, !tbaa !3 *)
mov v887 mem0_214;
(*   %sub.3.11.3 = sub i16 %887, %call.i.3.11.3 *)
sub v_sub_3_11_3 v887 v_call_i_3_11_3;
(*   store i16 %sub.3.11.3, i16* %arrayidx9.3.11.3, align 2, !tbaa !3 *)
mov mem0_246 v_sub_3_11_3;
(*   %add21.3.11.3 = add i16 %887, %call.i.3.11.3 *)
add v_add21_3_11_3 v887 v_call_i_3_11_3;
(*   store i16 %add21.3.11.3, i16* %arrayidx11.3.11.3, align 2, !tbaa !3 *)
mov mem0_214 v_add21_3_11_3;
(*   %arrayidx9.3.12.3 = getelementptr inbounds i16, i16* %r, i64 124 *)
(*   %888 = load i16, i16* %arrayidx9.3.12.3, align 2, !tbaa !3 *)
mov v888 mem0_248;
(*   %conv1.i.3.12.3 = sext i16 %888 to i32 *)
cast v_conv1_i_3_12_3@sint32 v888@sint16;
(*   %mul.i.3.12.3 = mul nsw i32 %conv1.i.3.12.3, 182 *)
mul v_mul_i_3_12_3 v_conv1_i_3_12_3 (182)@sint32;
(*   %call.i.3.12.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.12.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_12_3, v_call_i_3_12_3);
(*   %arrayidx11.3.12.3 = getelementptr inbounds i16, i16* %r, i64 108 *)
(*   %889 = load i16, i16* %arrayidx11.3.12.3, align 2, !tbaa !3 *)
mov v889 mem0_216;
(*   %sub.3.12.3 = sub i16 %889, %call.i.3.12.3 *)
sub v_sub_3_12_3 v889 v_call_i_3_12_3;
(*   store i16 %sub.3.12.3, i16* %arrayidx9.3.12.3, align 2, !tbaa !3 *)
mov mem0_248 v_sub_3_12_3;
(*   %add21.3.12.3 = add i16 %889, %call.i.3.12.3 *)
add v_add21_3_12_3 v889 v_call_i_3_12_3;
(*   store i16 %add21.3.12.3, i16* %arrayidx11.3.12.3, align 2, !tbaa !3 *)
mov mem0_216 v_add21_3_12_3;
(*   %arrayidx9.3.13.3 = getelementptr inbounds i16, i16* %r, i64 125 *)
(*   %890 = load i16, i16* %arrayidx9.3.13.3, align 2, !tbaa !3 *)
mov v890 mem0_250;
(*   %conv1.i.3.13.3 = sext i16 %890 to i32 *)
cast v_conv1_i_3_13_3@sint32 v890@sint16;
(*   %mul.i.3.13.3 = mul nsw i32 %conv1.i.3.13.3, 182 *)
mul v_mul_i_3_13_3 v_conv1_i_3_13_3 (182)@sint32;
(*   %call.i.3.13.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.13.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_13_3, v_call_i_3_13_3);
(*   %arrayidx11.3.13.3 = getelementptr inbounds i16, i16* %r, i64 109 *)
(*   %891 = load i16, i16* %arrayidx11.3.13.3, align 2, !tbaa !3 *)
mov v891 mem0_218;
(*   %sub.3.13.3 = sub i16 %891, %call.i.3.13.3 *)
sub v_sub_3_13_3 v891 v_call_i_3_13_3;
(*   store i16 %sub.3.13.3, i16* %arrayidx9.3.13.3, align 2, !tbaa !3 *)
mov mem0_250 v_sub_3_13_3;
(*   %add21.3.13.3 = add i16 %891, %call.i.3.13.3 *)
add v_add21_3_13_3 v891 v_call_i_3_13_3;
(*   store i16 %add21.3.13.3, i16* %arrayidx11.3.13.3, align 2, !tbaa !3 *)
mov mem0_218 v_add21_3_13_3;
(*   %arrayidx9.3.14.3 = getelementptr inbounds i16, i16* %r, i64 126 *)
(*   %892 = load i16, i16* %arrayidx9.3.14.3, align 2, !tbaa !3 *)
mov v892 mem0_252;
(*   %conv1.i.3.14.3 = sext i16 %892 to i32 *)
cast v_conv1_i_3_14_3@sint32 v892@sint16;
(*   %mul.i.3.14.3 = mul nsw i32 %conv1.i.3.14.3, 182 *)
mul v_mul_i_3_14_3 v_conv1_i_3_14_3 (182)@sint32;
(*   %call.i.3.14.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.14.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_14_3, v_call_i_3_14_3);
(*   %arrayidx11.3.14.3 = getelementptr inbounds i16, i16* %r, i64 110 *)
(*   %893 = load i16, i16* %arrayidx11.3.14.3, align 2, !tbaa !3 *)
mov v893 mem0_220;
(*   %sub.3.14.3 = sub i16 %893, %call.i.3.14.3 *)
sub v_sub_3_14_3 v893 v_call_i_3_14_3;
(*   store i16 %sub.3.14.3, i16* %arrayidx9.3.14.3, align 2, !tbaa !3 *)
mov mem0_252 v_sub_3_14_3;
(*   %add21.3.14.3 = add i16 %893, %call.i.3.14.3 *)
add v_add21_3_14_3 v893 v_call_i_3_14_3;
(*   store i16 %add21.3.14.3, i16* %arrayidx11.3.14.3, align 2, !tbaa !3 *)
mov mem0_220 v_add21_3_14_3;
(*   %arrayidx9.3.15.3 = getelementptr inbounds i16, i16* %r, i64 127 *)
(*   %894 = load i16, i16* %arrayidx9.3.15.3, align 2, !tbaa !3 *)
mov v894 mem0_254;
(*   %conv1.i.3.15.3 = sext i16 %894 to i32 *)
cast v_conv1_i_3_15_3@sint32 v894@sint16;
(*   %mul.i.3.15.3 = mul nsw i32 %conv1.i.3.15.3, 182 *)
mul v_mul_i_3_15_3 v_conv1_i_3_15_3 (182)@sint32;
(*   %call.i.3.15.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.15.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_15_3, v_call_i_3_15_3);
(*   %arrayidx11.3.15.3 = getelementptr inbounds i16, i16* %r, i64 111 *)
(*   %895 = load i16, i16* %arrayidx11.3.15.3, align 2, !tbaa !3 *)
mov v895 mem0_222;
(*   %sub.3.15.3 = sub i16 %895, %call.i.3.15.3 *)
sub v_sub_3_15_3 v895 v_call_i_3_15_3;
(*   store i16 %sub.3.15.3, i16* %arrayidx9.3.15.3, align 2, !tbaa !3 *)
mov mem0_254 v_sub_3_15_3;
(*   %add21.3.15.3 = add i16 %895, %call.i.3.15.3 *)
add v_add21_3_15_3 v895 v_call_i_3_15_3;
(*   store i16 %add21.3.15.3, i16* %arrayidx11.3.15.3, align 2, !tbaa !3 *)
mov mem0_222 v_add21_3_15_3;

(* NOTE: k = 12 *)

(*   %arrayidx9.3.4208 = getelementptr inbounds i16, i16* %r, i64 144 *)
(*   %896 = load i16, i16* %arrayidx9.3.4208, align 2, !tbaa !3 *)
mov v896 mem0_288;
(*   %conv1.i.3.4209 = sext i16 %896 to i32 *)
cast v_conv1_i_3_4209@sint32 v896@sint16;
(*   %mul.i.3.4210 = mul nsw i32 %conv1.i.3.4209, 962 *)
mul v_mul_i_3_4210 v_conv1_i_3_4209 (962)@sint32;
(*   %call.i.3.4211 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.4210) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_4210, v_call_i_3_4211);
(*   %arrayidx11.3.4212 = getelementptr inbounds i16, i16* %r, i64 128 *)
(*   %897 = load i16, i16* %arrayidx11.3.4212, align 2, !tbaa !3 *)
mov v897 mem0_256;
(*   %sub.3.4213 = sub i16 %897, %call.i.3.4211 *)
sub v_sub_3_4213 v897 v_call_i_3_4211;
(*   store i16 %sub.3.4213, i16* %arrayidx9.3.4208, align 2, !tbaa !3 *)
mov mem0_288 v_sub_3_4213;
(*   %add21.3.4214 = add i16 %897, %call.i.3.4211 *)
add v_add21_3_4214 v897 v_call_i_3_4211;
(*   store i16 %add21.3.4214, i16* %arrayidx11.3.4212, align 2, !tbaa !3 *)
mov mem0_256 v_add21_3_4214;
(*   %arrayidx9.3.1.4 = getelementptr inbounds i16, i16* %r, i64 145 *)
(*   %898 = load i16, i16* %arrayidx9.3.1.4, align 2, !tbaa !3 *)
mov v898 mem0_290;
(*   %conv1.i.3.1.4 = sext i16 %898 to i32 *)
cast v_conv1_i_3_1_4@sint32 v898@sint16;
(*   %mul.i.3.1.4 = mul nsw i32 %conv1.i.3.1.4, 962 *)
mul v_mul_i_3_1_4 v_conv1_i_3_1_4 (962)@sint32;
(*   %call.i.3.1.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.1.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_1_4, v_call_i_3_1_4);
(*   %arrayidx11.3.1.4 = getelementptr inbounds i16, i16* %r, i64 129 *)
(*   %899 = load i16, i16* %arrayidx11.3.1.4, align 2, !tbaa !3 *)
mov v899 mem0_258;
(*   %sub.3.1.4 = sub i16 %899, %call.i.3.1.4 *)
sub v_sub_3_1_4 v899 v_call_i_3_1_4;
(*   store i16 %sub.3.1.4, i16* %arrayidx9.3.1.4, align 2, !tbaa !3 *)
mov mem0_290 v_sub_3_1_4;
(*   %add21.3.1.4 = add i16 %899, %call.i.3.1.4 *)
add v_add21_3_1_4 v899 v_call_i_3_1_4;
(*   store i16 %add21.3.1.4, i16* %arrayidx11.3.1.4, align 2, !tbaa !3 *)
mov mem0_258 v_add21_3_1_4;
(*   %arrayidx9.3.2.4 = getelementptr inbounds i16, i16* %r, i64 146 *)
(*   %900 = load i16, i16* %arrayidx9.3.2.4, align 2, !tbaa !3 *)
mov v900 mem0_292;
(*   %conv1.i.3.2.4 = sext i16 %900 to i32 *)
cast v_conv1_i_3_2_4@sint32 v900@sint16;
(*   %mul.i.3.2.4 = mul nsw i32 %conv1.i.3.2.4, 962 *)
mul v_mul_i_3_2_4 v_conv1_i_3_2_4 (962)@sint32;
(*   %call.i.3.2.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.2.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_2_4, v_call_i_3_2_4);
(*   %arrayidx11.3.2.4 = getelementptr inbounds i16, i16* %r, i64 130 *)
(*   %901 = load i16, i16* %arrayidx11.3.2.4, align 2, !tbaa !3 *)
mov v901 mem0_260;
(*   %sub.3.2.4 = sub i16 %901, %call.i.3.2.4 *)
sub v_sub_3_2_4 v901 v_call_i_3_2_4;
(*   store i16 %sub.3.2.4, i16* %arrayidx9.3.2.4, align 2, !tbaa !3 *)
mov mem0_292 v_sub_3_2_4;
(*   %add21.3.2.4 = add i16 %901, %call.i.3.2.4 *)
add v_add21_3_2_4 v901 v_call_i_3_2_4;
(*   store i16 %add21.3.2.4, i16* %arrayidx11.3.2.4, align 2, !tbaa !3 *)
mov mem0_260 v_add21_3_2_4;
(*   %arrayidx9.3.3.4 = getelementptr inbounds i16, i16* %r, i64 147 *)
(*   %902 = load i16, i16* %arrayidx9.3.3.4, align 2, !tbaa !3 *)
mov v902 mem0_294;
(*   %conv1.i.3.3.4 = sext i16 %902 to i32 *)
cast v_conv1_i_3_3_4@sint32 v902@sint16;
(*   %mul.i.3.3.4 = mul nsw i32 %conv1.i.3.3.4, 962 *)
mul v_mul_i_3_3_4 v_conv1_i_3_3_4 (962)@sint32;
(*   %call.i.3.3.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.3.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_3_4, v_call_i_3_3_4);
(*   %arrayidx11.3.3.4 = getelementptr inbounds i16, i16* %r, i64 131 *)
(*   %903 = load i16, i16* %arrayidx11.3.3.4, align 2, !tbaa !3 *)
mov v903 mem0_262;
(*   %sub.3.3.4 = sub i16 %903, %call.i.3.3.4 *)
sub v_sub_3_3_4 v903 v_call_i_3_3_4;
(*   store i16 %sub.3.3.4, i16* %arrayidx9.3.3.4, align 2, !tbaa !3 *)
mov mem0_294 v_sub_3_3_4;
(*   %add21.3.3.4 = add i16 %903, %call.i.3.3.4 *)
add v_add21_3_3_4 v903 v_call_i_3_3_4;
(*   store i16 %add21.3.3.4, i16* %arrayidx11.3.3.4, align 2, !tbaa !3 *)
mov mem0_262 v_add21_3_3_4;
(*   %arrayidx9.3.4.4 = getelementptr inbounds i16, i16* %r, i64 148 *)
(*   %904 = load i16, i16* %arrayidx9.3.4.4, align 2, !tbaa !3 *)
mov v904 mem0_296;
(*   %conv1.i.3.4.4 = sext i16 %904 to i32 *)
cast v_conv1_i_3_4_4@sint32 v904@sint16;
(*   %mul.i.3.4.4 = mul nsw i32 %conv1.i.3.4.4, 962 *)
mul v_mul_i_3_4_4 v_conv1_i_3_4_4 (962)@sint32;
(*   %call.i.3.4.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.4.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_4_4, v_call_i_3_4_4);
(*   %arrayidx11.3.4.4 = getelementptr inbounds i16, i16* %r, i64 132 *)
(*   %905 = load i16, i16* %arrayidx11.3.4.4, align 2, !tbaa !3 *)
mov v905 mem0_264;
(*   %sub.3.4.4 = sub i16 %905, %call.i.3.4.4 *)
sub v_sub_3_4_4 v905 v_call_i_3_4_4;
(*   store i16 %sub.3.4.4, i16* %arrayidx9.3.4.4, align 2, !tbaa !3 *)
mov mem0_296 v_sub_3_4_4;
(*   %add21.3.4.4 = add i16 %905, %call.i.3.4.4 *)
add v_add21_3_4_4 v905 v_call_i_3_4_4;
(*   store i16 %add21.3.4.4, i16* %arrayidx11.3.4.4, align 2, !tbaa !3 *)
mov mem0_264 v_add21_3_4_4;
(*   %arrayidx9.3.5.4 = getelementptr inbounds i16, i16* %r, i64 149 *)
(*   %906 = load i16, i16* %arrayidx9.3.5.4, align 2, !tbaa !3 *)
mov v906 mem0_298;
(*   %conv1.i.3.5.4 = sext i16 %906 to i32 *)
cast v_conv1_i_3_5_4@sint32 v906@sint16;
(*   %mul.i.3.5.4 = mul nsw i32 %conv1.i.3.5.4, 962 *)
mul v_mul_i_3_5_4 v_conv1_i_3_5_4 (962)@sint32;
(*   %call.i.3.5.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.5.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_5_4, v_call_i_3_5_4);
(*   %arrayidx11.3.5.4 = getelementptr inbounds i16, i16* %r, i64 133 *)
(*   %907 = load i16, i16* %arrayidx11.3.5.4, align 2, !tbaa !3 *)
mov v907 mem0_266;
(*   %sub.3.5.4 = sub i16 %907, %call.i.3.5.4 *)
sub v_sub_3_5_4 v907 v_call_i_3_5_4;
(*   store i16 %sub.3.5.4, i16* %arrayidx9.3.5.4, align 2, !tbaa !3 *)
mov mem0_298 v_sub_3_5_4;
(*   %add21.3.5.4 = add i16 %907, %call.i.3.5.4 *)
add v_add21_3_5_4 v907 v_call_i_3_5_4;
(*   store i16 %add21.3.5.4, i16* %arrayidx11.3.5.4, align 2, !tbaa !3 *)
mov mem0_266 v_add21_3_5_4;
(*   %arrayidx9.3.6.4 = getelementptr inbounds i16, i16* %r, i64 150 *)
(*   %908 = load i16, i16* %arrayidx9.3.6.4, align 2, !tbaa !3 *)
mov v908 mem0_300;
(*   %conv1.i.3.6.4 = sext i16 %908 to i32 *)
cast v_conv1_i_3_6_4@sint32 v908@sint16;
(*   %mul.i.3.6.4 = mul nsw i32 %conv1.i.3.6.4, 962 *)
mul v_mul_i_3_6_4 v_conv1_i_3_6_4 (962)@sint32;
(*   %call.i.3.6.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.6.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_6_4, v_call_i_3_6_4);
(*   %arrayidx11.3.6.4 = getelementptr inbounds i16, i16* %r, i64 134 *)
(*   %909 = load i16, i16* %arrayidx11.3.6.4, align 2, !tbaa !3 *)
mov v909 mem0_268;
(*   %sub.3.6.4 = sub i16 %909, %call.i.3.6.4 *)
sub v_sub_3_6_4 v909 v_call_i_3_6_4;
(*   store i16 %sub.3.6.4, i16* %arrayidx9.3.6.4, align 2, !tbaa !3 *)
mov mem0_300 v_sub_3_6_4;
(*   %add21.3.6.4 = add i16 %909, %call.i.3.6.4 *)
add v_add21_3_6_4 v909 v_call_i_3_6_4;
(*   store i16 %add21.3.6.4, i16* %arrayidx11.3.6.4, align 2, !tbaa !3 *)
mov mem0_268 v_add21_3_6_4;
(*   %arrayidx9.3.7.4 = getelementptr inbounds i16, i16* %r, i64 151 *)
(*   %910 = load i16, i16* %arrayidx9.3.7.4, align 2, !tbaa !3 *)
mov v910 mem0_302;
(*   %conv1.i.3.7.4 = sext i16 %910 to i32 *)
cast v_conv1_i_3_7_4@sint32 v910@sint16;
(*   %mul.i.3.7.4 = mul nsw i32 %conv1.i.3.7.4, 962 *)
mul v_mul_i_3_7_4 v_conv1_i_3_7_4 (962)@sint32;
(*   %call.i.3.7.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.7.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_7_4, v_call_i_3_7_4);
(*   %arrayidx11.3.7.4 = getelementptr inbounds i16, i16* %r, i64 135 *)
(*   %911 = load i16, i16* %arrayidx11.3.7.4, align 2, !tbaa !3 *)
mov v911 mem0_270;
(*   %sub.3.7.4 = sub i16 %911, %call.i.3.7.4 *)
sub v_sub_3_7_4 v911 v_call_i_3_7_4;
(*   store i16 %sub.3.7.4, i16* %arrayidx9.3.7.4, align 2, !tbaa !3 *)
mov mem0_302 v_sub_3_7_4;
(*   %add21.3.7.4 = add i16 %911, %call.i.3.7.4 *)
add v_add21_3_7_4 v911 v_call_i_3_7_4;
(*   store i16 %add21.3.7.4, i16* %arrayidx11.3.7.4, align 2, !tbaa !3 *)
mov mem0_270 v_add21_3_7_4;
(*   %arrayidx9.3.8.4 = getelementptr inbounds i16, i16* %r, i64 152 *)
(*   %912 = load i16, i16* %arrayidx9.3.8.4, align 2, !tbaa !3 *)
mov v912 mem0_304;
(*   %conv1.i.3.8.4 = sext i16 %912 to i32 *)
cast v_conv1_i_3_8_4@sint32 v912@sint16;
(*   %mul.i.3.8.4 = mul nsw i32 %conv1.i.3.8.4, 962 *)
mul v_mul_i_3_8_4 v_conv1_i_3_8_4 (962)@sint32;
(*   %call.i.3.8.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.8.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_8_4, v_call_i_3_8_4);
(*   %arrayidx11.3.8.4 = getelementptr inbounds i16, i16* %r, i64 136 *)
(*   %913 = load i16, i16* %arrayidx11.3.8.4, align 2, !tbaa !3 *)
mov v913 mem0_272;
(*   %sub.3.8.4 = sub i16 %913, %call.i.3.8.4 *)
sub v_sub_3_8_4 v913 v_call_i_3_8_4;
(*   store i16 %sub.3.8.4, i16* %arrayidx9.3.8.4, align 2, !tbaa !3 *)
mov mem0_304 v_sub_3_8_4;
(*   %add21.3.8.4 = add i16 %913, %call.i.3.8.4 *)
add v_add21_3_8_4 v913 v_call_i_3_8_4;
(*   store i16 %add21.3.8.4, i16* %arrayidx11.3.8.4, align 2, !tbaa !3 *)
mov mem0_272 v_add21_3_8_4;
(*   %arrayidx9.3.9.4 = getelementptr inbounds i16, i16* %r, i64 153 *)
(*   %914 = load i16, i16* %arrayidx9.3.9.4, align 2, !tbaa !3 *)
mov v914 mem0_306;
(*   %conv1.i.3.9.4 = sext i16 %914 to i32 *)
cast v_conv1_i_3_9_4@sint32 v914@sint16;
(*   %mul.i.3.9.4 = mul nsw i32 %conv1.i.3.9.4, 962 *)
mul v_mul_i_3_9_4 v_conv1_i_3_9_4 (962)@sint32;
(*   %call.i.3.9.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.9.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_9_4, v_call_i_3_9_4);
(*   %arrayidx11.3.9.4 = getelementptr inbounds i16, i16* %r, i64 137 *)
(*   %915 = load i16, i16* %arrayidx11.3.9.4, align 2, !tbaa !3 *)
mov v915 mem0_274;
(*   %sub.3.9.4 = sub i16 %915, %call.i.3.9.4 *)
sub v_sub_3_9_4 v915 v_call_i_3_9_4;
(*   store i16 %sub.3.9.4, i16* %arrayidx9.3.9.4, align 2, !tbaa !3 *)
mov mem0_306 v_sub_3_9_4;
(*   %add21.3.9.4 = add i16 %915, %call.i.3.9.4 *)
add v_add21_3_9_4 v915 v_call_i_3_9_4;
(*   store i16 %add21.3.9.4, i16* %arrayidx11.3.9.4, align 2, !tbaa !3 *)
mov mem0_274 v_add21_3_9_4;
(*   %arrayidx9.3.10.4 = getelementptr inbounds i16, i16* %r, i64 154 *)
(*   %916 = load i16, i16* %arrayidx9.3.10.4, align 2, !tbaa !3 *)
mov v916 mem0_308;
(*   %conv1.i.3.10.4 = sext i16 %916 to i32 *)
cast v_conv1_i_3_10_4@sint32 v916@sint16;
(*   %mul.i.3.10.4 = mul nsw i32 %conv1.i.3.10.4, 962 *)
mul v_mul_i_3_10_4 v_conv1_i_3_10_4 (962)@sint32;
(*   %call.i.3.10.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.10.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_10_4, v_call_i_3_10_4);
(*   %arrayidx11.3.10.4 = getelementptr inbounds i16, i16* %r, i64 138 *)
(*   %917 = load i16, i16* %arrayidx11.3.10.4, align 2, !tbaa !3 *)
mov v917 mem0_276;
(*   %sub.3.10.4 = sub i16 %917, %call.i.3.10.4 *)
sub v_sub_3_10_4 v917 v_call_i_3_10_4;
(*   store i16 %sub.3.10.4, i16* %arrayidx9.3.10.4, align 2, !tbaa !3 *)
mov mem0_308 v_sub_3_10_4;
(*   %add21.3.10.4 = add i16 %917, %call.i.3.10.4 *)
add v_add21_3_10_4 v917 v_call_i_3_10_4;
(*   store i16 %add21.3.10.4, i16* %arrayidx11.3.10.4, align 2, !tbaa !3 *)
mov mem0_276 v_add21_3_10_4;
(*   %arrayidx9.3.11.4 = getelementptr inbounds i16, i16* %r, i64 155 *)
(*   %918 = load i16, i16* %arrayidx9.3.11.4, align 2, !tbaa !3 *)
mov v918 mem0_310;
(*   %conv1.i.3.11.4 = sext i16 %918 to i32 *)
cast v_conv1_i_3_11_4@sint32 v918@sint16;
(*   %mul.i.3.11.4 = mul nsw i32 %conv1.i.3.11.4, 962 *)
mul v_mul_i_3_11_4 v_conv1_i_3_11_4 (962)@sint32;
(*   %call.i.3.11.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.11.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_11_4, v_call_i_3_11_4);
(*   %arrayidx11.3.11.4 = getelementptr inbounds i16, i16* %r, i64 139 *)
(*   %919 = load i16, i16* %arrayidx11.3.11.4, align 2, !tbaa !3 *)
mov v919 mem0_278;
(*   %sub.3.11.4 = sub i16 %919, %call.i.3.11.4 *)
sub v_sub_3_11_4 v919 v_call_i_3_11_4;
(*   store i16 %sub.3.11.4, i16* %arrayidx9.3.11.4, align 2, !tbaa !3 *)
mov mem0_310 v_sub_3_11_4;
(*   %add21.3.11.4 = add i16 %919, %call.i.3.11.4 *)
add v_add21_3_11_4 v919 v_call_i_3_11_4;
(*   store i16 %add21.3.11.4, i16* %arrayidx11.3.11.4, align 2, !tbaa !3 *)
mov mem0_278 v_add21_3_11_4;
(*   %arrayidx9.3.12.4 = getelementptr inbounds i16, i16* %r, i64 156 *)
(*   %920 = load i16, i16* %arrayidx9.3.12.4, align 2, !tbaa !3 *)
mov v920 mem0_312;
(*   %conv1.i.3.12.4 = sext i16 %920 to i32 *)
cast v_conv1_i_3_12_4@sint32 v920@sint16;
(*   %mul.i.3.12.4 = mul nsw i32 %conv1.i.3.12.4, 962 *)
mul v_mul_i_3_12_4 v_conv1_i_3_12_4 (962)@sint32;
(*   %call.i.3.12.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.12.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_12_4, v_call_i_3_12_4);
(*   %arrayidx11.3.12.4 = getelementptr inbounds i16, i16* %r, i64 140 *)
(*   %921 = load i16, i16* %arrayidx11.3.12.4, align 2, !tbaa !3 *)
mov v921 mem0_280;
(*   %sub.3.12.4 = sub i16 %921, %call.i.3.12.4 *)
sub v_sub_3_12_4 v921 v_call_i_3_12_4;
(*   store i16 %sub.3.12.4, i16* %arrayidx9.3.12.4, align 2, !tbaa !3 *)
mov mem0_312 v_sub_3_12_4;
(*   %add21.3.12.4 = add i16 %921, %call.i.3.12.4 *)
add v_add21_3_12_4 v921 v_call_i_3_12_4;
(*   store i16 %add21.3.12.4, i16* %arrayidx11.3.12.4, align 2, !tbaa !3 *)
mov mem0_280 v_add21_3_12_4;
(*   %arrayidx9.3.13.4 = getelementptr inbounds i16, i16* %r, i64 157 *)
(*   %922 = load i16, i16* %arrayidx9.3.13.4, align 2, !tbaa !3 *)
mov v922 mem0_314;
(*   %conv1.i.3.13.4 = sext i16 %922 to i32 *)
cast v_conv1_i_3_13_4@sint32 v922@sint16;
(*   %mul.i.3.13.4 = mul nsw i32 %conv1.i.3.13.4, 962 *)
mul v_mul_i_3_13_4 v_conv1_i_3_13_4 (962)@sint32;
(*   %call.i.3.13.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.13.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_13_4, v_call_i_3_13_4);
(*   %arrayidx11.3.13.4 = getelementptr inbounds i16, i16* %r, i64 141 *)
(*   %923 = load i16, i16* %arrayidx11.3.13.4, align 2, !tbaa !3 *)
mov v923 mem0_282;
(*   %sub.3.13.4 = sub i16 %923, %call.i.3.13.4 *)
sub v_sub_3_13_4 v923 v_call_i_3_13_4;
(*   store i16 %sub.3.13.4, i16* %arrayidx9.3.13.4, align 2, !tbaa !3 *)
mov mem0_314 v_sub_3_13_4;
(*   %add21.3.13.4 = add i16 %923, %call.i.3.13.4 *)
add v_add21_3_13_4 v923 v_call_i_3_13_4;
(*   store i16 %add21.3.13.4, i16* %arrayidx11.3.13.4, align 2, !tbaa !3 *)
mov mem0_282 v_add21_3_13_4;
(*   %arrayidx9.3.14.4 = getelementptr inbounds i16, i16* %r, i64 158 *)
(*   %924 = load i16, i16* %arrayidx9.3.14.4, align 2, !tbaa !3 *)
mov v924 mem0_316;
(*   %conv1.i.3.14.4 = sext i16 %924 to i32 *)
cast v_conv1_i_3_14_4@sint32 v924@sint16;
(*   %mul.i.3.14.4 = mul nsw i32 %conv1.i.3.14.4, 962 *)
mul v_mul_i_3_14_4 v_conv1_i_3_14_4 (962)@sint32;
(*   %call.i.3.14.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.14.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_14_4, v_call_i_3_14_4);
(*   %arrayidx11.3.14.4 = getelementptr inbounds i16, i16* %r, i64 142 *)
(*   %925 = load i16, i16* %arrayidx11.3.14.4, align 2, !tbaa !3 *)
mov v925 mem0_284;
(*   %sub.3.14.4 = sub i16 %925, %call.i.3.14.4 *)
sub v_sub_3_14_4 v925 v_call_i_3_14_4;
(*   store i16 %sub.3.14.4, i16* %arrayidx9.3.14.4, align 2, !tbaa !3 *)
mov mem0_316 v_sub_3_14_4;
(*   %add21.3.14.4 = add i16 %925, %call.i.3.14.4 *)
add v_add21_3_14_4 v925 v_call_i_3_14_4;
(*   store i16 %add21.3.14.4, i16* %arrayidx11.3.14.4, align 2, !tbaa !3 *)
mov mem0_284 v_add21_3_14_4;
(*   %arrayidx9.3.15.4 = getelementptr inbounds i16, i16* %r, i64 159 *)
(*   %926 = load i16, i16* %arrayidx9.3.15.4, align 2, !tbaa !3 *)
mov v926 mem0_318;
(*   %conv1.i.3.15.4 = sext i16 %926 to i32 *)
cast v_conv1_i_3_15_4@sint32 v926@sint16;
(*   %mul.i.3.15.4 = mul nsw i32 %conv1.i.3.15.4, 962 *)
mul v_mul_i_3_15_4 v_conv1_i_3_15_4 (962)@sint32;
(*   %call.i.3.15.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.15.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_15_4, v_call_i_3_15_4);
(*   %arrayidx11.3.15.4 = getelementptr inbounds i16, i16* %r, i64 143 *)
(*   %927 = load i16, i16* %arrayidx11.3.15.4, align 2, !tbaa !3 *)
mov v927 mem0_286;
(*   %sub.3.15.4 = sub i16 %927, %call.i.3.15.4 *)
sub v_sub_3_15_4 v927 v_call_i_3_15_4;
(*   store i16 %sub.3.15.4, i16* %arrayidx9.3.15.4, align 2, !tbaa !3 *)
mov mem0_318 v_sub_3_15_4;
(*   %add21.3.15.4 = add i16 %927, %call.i.3.15.4 *)
add v_add21_3_15_4 v927 v_call_i_3_15_4;
(*   store i16 %add21.3.15.4, i16* %arrayidx11.3.15.4, align 2, !tbaa !3 *)
mov mem0_286 v_add21_3_15_4;

(* NOTE: k = 13 *)

(*   %arrayidx9.3.5218 = getelementptr inbounds i16, i16* %r, i64 176 *)
(*   %928 = load i16, i16* %arrayidx9.3.5218, align 2, !tbaa !3 *)
mov v928 mem0_352;
(*   %conv1.i.3.5219 = sext i16 %928 to i32 *)
cast v_conv1_i_3_5219@sint32 v928@sint16;
(*   %mul.i.3.5220 = mul nsw i32 %conv1.i.3.5219, -1202 *)
mul v_mul_i_3_5220 v_conv1_i_3_5219 (-1202)@sint32;
(*   %call.i.3.5221 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.5220) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_5220, v_call_i_3_5221);
(*   %arrayidx11.3.5222 = getelementptr inbounds i16, i16* %r, i64 160 *)
(*   %929 = load i16, i16* %arrayidx11.3.5222, align 2, !tbaa !3 *)
mov v929 mem0_320;
(*   %sub.3.5223 = sub i16 %929, %call.i.3.5221 *)
sub v_sub_3_5223 v929 v_call_i_3_5221;
(*   store i16 %sub.3.5223, i16* %arrayidx9.3.5218, align 2, !tbaa !3 *)
mov mem0_352 v_sub_3_5223;
(*   %add21.3.5224 = add i16 %929, %call.i.3.5221 *)
add v_add21_3_5224 v929 v_call_i_3_5221;
(*   store i16 %add21.3.5224, i16* %arrayidx11.3.5222, align 2, !tbaa !3 *)
mov mem0_320 v_add21_3_5224;
(*   %arrayidx9.3.1.5 = getelementptr inbounds i16, i16* %r, i64 177 *)
(*   %930 = load i16, i16* %arrayidx9.3.1.5, align 2, !tbaa !3 *)
mov v930 mem0_354;
(*   %conv1.i.3.1.5 = sext i16 %930 to i32 *)
cast v_conv1_i_3_1_5@sint32 v930@sint16;
(*   %mul.i.3.1.5 = mul nsw i32 %conv1.i.3.1.5, -1202 *)
mul v_mul_i_3_1_5 v_conv1_i_3_1_5 (-1202)@sint32;
(*   %call.i.3.1.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.1.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_1_5, v_call_i_3_1_5);
(*   %arrayidx11.3.1.5 = getelementptr inbounds i16, i16* %r, i64 161 *)
(*   %931 = load i16, i16* %arrayidx11.3.1.5, align 2, !tbaa !3 *)
mov v931 mem0_322;
(*   %sub.3.1.5 = sub i16 %931, %call.i.3.1.5 *)
sub v_sub_3_1_5 v931 v_call_i_3_1_5;
(*   store i16 %sub.3.1.5, i16* %arrayidx9.3.1.5, align 2, !tbaa !3 *)
mov mem0_354 v_sub_3_1_5;
(*   %add21.3.1.5 = add i16 %931, %call.i.3.1.5 *)
add v_add21_3_1_5 v931 v_call_i_3_1_5;
(*   store i16 %add21.3.1.5, i16* %arrayidx11.3.1.5, align 2, !tbaa !3 *)
mov mem0_322 v_add21_3_1_5;
(*   %arrayidx9.3.2.5 = getelementptr inbounds i16, i16* %r, i64 178 *)
(*   %932 = load i16, i16* %arrayidx9.3.2.5, align 2, !tbaa !3 *)
mov v932 mem0_356;
(*   %conv1.i.3.2.5 = sext i16 %932 to i32 *)
cast v_conv1_i_3_2_5@sint32 v932@sint16;
(*   %mul.i.3.2.5 = mul nsw i32 %conv1.i.3.2.5, -1202 *)
mul v_mul_i_3_2_5 v_conv1_i_3_2_5 (-1202)@sint32;
(*   %call.i.3.2.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.2.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_2_5, v_call_i_3_2_5);
(*   %arrayidx11.3.2.5 = getelementptr inbounds i16, i16* %r, i64 162 *)
(*   %933 = load i16, i16* %arrayidx11.3.2.5, align 2, !tbaa !3 *)
mov v933 mem0_324;
(*   %sub.3.2.5 = sub i16 %933, %call.i.3.2.5 *)
sub v_sub_3_2_5 v933 v_call_i_3_2_5;
(*   store i16 %sub.3.2.5, i16* %arrayidx9.3.2.5, align 2, !tbaa !3 *)
mov mem0_356 v_sub_3_2_5;
(*   %add21.3.2.5 = add i16 %933, %call.i.3.2.5 *)
add v_add21_3_2_5 v933 v_call_i_3_2_5;
(*   store i16 %add21.3.2.5, i16* %arrayidx11.3.2.5, align 2, !tbaa !3 *)
mov mem0_324 v_add21_3_2_5;
(*   %arrayidx9.3.3.5 = getelementptr inbounds i16, i16* %r, i64 179 *)
(*   %934 = load i16, i16* %arrayidx9.3.3.5, align 2, !tbaa !3 *)
mov v934 mem0_358;
(*   %conv1.i.3.3.5 = sext i16 %934 to i32 *)
cast v_conv1_i_3_3_5@sint32 v934@sint16;
(*   %mul.i.3.3.5 = mul nsw i32 %conv1.i.3.3.5, -1202 *)
mul v_mul_i_3_3_5 v_conv1_i_3_3_5 (-1202)@sint32;
(*   %call.i.3.3.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.3.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_3_5, v_call_i_3_3_5);
(*   %arrayidx11.3.3.5 = getelementptr inbounds i16, i16* %r, i64 163 *)
(*   %935 = load i16, i16* %arrayidx11.3.3.5, align 2, !tbaa !3 *)
mov v935 mem0_326;
(*   %sub.3.3.5 = sub i16 %935, %call.i.3.3.5 *)
sub v_sub_3_3_5 v935 v_call_i_3_3_5;
(*   store i16 %sub.3.3.5, i16* %arrayidx9.3.3.5, align 2, !tbaa !3 *)
mov mem0_358 v_sub_3_3_5;
(*   %add21.3.3.5 = add i16 %935, %call.i.3.3.5 *)
add v_add21_3_3_5 v935 v_call_i_3_3_5;
(*   store i16 %add21.3.3.5, i16* %arrayidx11.3.3.5, align 2, !tbaa !3 *)
mov mem0_326 v_add21_3_3_5;
(*   %arrayidx9.3.4.5 = getelementptr inbounds i16, i16* %r, i64 180 *)
(*   %936 = load i16, i16* %arrayidx9.3.4.5, align 2, !tbaa !3 *)
mov v936 mem0_360;
(*   %conv1.i.3.4.5 = sext i16 %936 to i32 *)
cast v_conv1_i_3_4_5@sint32 v936@sint16;
(*   %mul.i.3.4.5 = mul nsw i32 %conv1.i.3.4.5, -1202 *)
mul v_mul_i_3_4_5 v_conv1_i_3_4_5 (-1202)@sint32;
(*   %call.i.3.4.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.4.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_4_5, v_call_i_3_4_5);
(*   %arrayidx11.3.4.5 = getelementptr inbounds i16, i16* %r, i64 164 *)
(*   %937 = load i16, i16* %arrayidx11.3.4.5, align 2, !tbaa !3 *)
mov v937 mem0_328;
(*   %sub.3.4.5 = sub i16 %937, %call.i.3.4.5 *)
sub v_sub_3_4_5 v937 v_call_i_3_4_5;
(*   store i16 %sub.3.4.5, i16* %arrayidx9.3.4.5, align 2, !tbaa !3 *)
mov mem0_360 v_sub_3_4_5;
(*   %add21.3.4.5 = add i16 %937, %call.i.3.4.5 *)
add v_add21_3_4_5 v937 v_call_i_3_4_5;
(*   store i16 %add21.3.4.5, i16* %arrayidx11.3.4.5, align 2, !tbaa !3 *)
mov mem0_328 v_add21_3_4_5;
(*   %arrayidx9.3.5.5 = getelementptr inbounds i16, i16* %r, i64 181 *)
(*   %938 = load i16, i16* %arrayidx9.3.5.5, align 2, !tbaa !3 *)
mov v938 mem0_362;
(*   %conv1.i.3.5.5 = sext i16 %938 to i32 *)
cast v_conv1_i_3_5_5@sint32 v938@sint16;
(*   %mul.i.3.5.5 = mul nsw i32 %conv1.i.3.5.5, -1202 *)
mul v_mul_i_3_5_5 v_conv1_i_3_5_5 (-1202)@sint32;
(*   %call.i.3.5.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.5.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_5_5, v_call_i_3_5_5);
(*   %arrayidx11.3.5.5 = getelementptr inbounds i16, i16* %r, i64 165 *)
(*   %939 = load i16, i16* %arrayidx11.3.5.5, align 2, !tbaa !3 *)
mov v939 mem0_330;
(*   %sub.3.5.5 = sub i16 %939, %call.i.3.5.5 *)
sub v_sub_3_5_5 v939 v_call_i_3_5_5;
(*   store i16 %sub.3.5.5, i16* %arrayidx9.3.5.5, align 2, !tbaa !3 *)
mov mem0_362 v_sub_3_5_5;
(*   %add21.3.5.5 = add i16 %939, %call.i.3.5.5 *)
add v_add21_3_5_5 v939 v_call_i_3_5_5;
(*   store i16 %add21.3.5.5, i16* %arrayidx11.3.5.5, align 2, !tbaa !3 *)
mov mem0_330 v_add21_3_5_5;
(*   %arrayidx9.3.6.5 = getelementptr inbounds i16, i16* %r, i64 182 *)
(*   %940 = load i16, i16* %arrayidx9.3.6.5, align 2, !tbaa !3 *)
mov v940 mem0_364;
(*   %conv1.i.3.6.5 = sext i16 %940 to i32 *)
cast v_conv1_i_3_6_5@sint32 v940@sint16;
(*   %mul.i.3.6.5 = mul nsw i32 %conv1.i.3.6.5, -1202 *)
mul v_mul_i_3_6_5 v_conv1_i_3_6_5 (-1202)@sint32;
(*   %call.i.3.6.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.6.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_6_5, v_call_i_3_6_5);
(*   %arrayidx11.3.6.5 = getelementptr inbounds i16, i16* %r, i64 166 *)
(*   %941 = load i16, i16* %arrayidx11.3.6.5, align 2, !tbaa !3 *)
mov v941 mem0_332;
(*   %sub.3.6.5 = sub i16 %941, %call.i.3.6.5 *)
sub v_sub_3_6_5 v941 v_call_i_3_6_5;
(*   store i16 %sub.3.6.5, i16* %arrayidx9.3.6.5, align 2, !tbaa !3 *)
mov mem0_364 v_sub_3_6_5;
(*   %add21.3.6.5 = add i16 %941, %call.i.3.6.5 *)
add v_add21_3_6_5 v941 v_call_i_3_6_5;
(*   store i16 %add21.3.6.5, i16* %arrayidx11.3.6.5, align 2, !tbaa !3 *)
mov mem0_332 v_add21_3_6_5;
(*   %arrayidx9.3.7.5 = getelementptr inbounds i16, i16* %r, i64 183 *)
(*   %942 = load i16, i16* %arrayidx9.3.7.5, align 2, !tbaa !3 *)
mov v942 mem0_366;
(*   %conv1.i.3.7.5 = sext i16 %942 to i32 *)
cast v_conv1_i_3_7_5@sint32 v942@sint16;
(*   %mul.i.3.7.5 = mul nsw i32 %conv1.i.3.7.5, -1202 *)
mul v_mul_i_3_7_5 v_conv1_i_3_7_5 (-1202)@sint32;
(*   %call.i.3.7.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.7.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_7_5, v_call_i_3_7_5);
(*   %arrayidx11.3.7.5 = getelementptr inbounds i16, i16* %r, i64 167 *)
(*   %943 = load i16, i16* %arrayidx11.3.7.5, align 2, !tbaa !3 *)
mov v943 mem0_334;
(*   %sub.3.7.5 = sub i16 %943, %call.i.3.7.5 *)
sub v_sub_3_7_5 v943 v_call_i_3_7_5;
(*   store i16 %sub.3.7.5, i16* %arrayidx9.3.7.5, align 2, !tbaa !3 *)
mov mem0_366 v_sub_3_7_5;
(*   %add21.3.7.5 = add i16 %943, %call.i.3.7.5 *)
add v_add21_3_7_5 v943 v_call_i_3_7_5;
(*   store i16 %add21.3.7.5, i16* %arrayidx11.3.7.5, align 2, !tbaa !3 *)
mov mem0_334 v_add21_3_7_5;
(*   %arrayidx9.3.8.5 = getelementptr inbounds i16, i16* %r, i64 184 *)
(*   %944 = load i16, i16* %arrayidx9.3.8.5, align 2, !tbaa !3 *)
mov v944 mem0_368;
(*   %conv1.i.3.8.5 = sext i16 %944 to i32 *)
cast v_conv1_i_3_8_5@sint32 v944@sint16;
(*   %mul.i.3.8.5 = mul nsw i32 %conv1.i.3.8.5, -1202 *)
mul v_mul_i_3_8_5 v_conv1_i_3_8_5 (-1202)@sint32;
(*   %call.i.3.8.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.8.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_8_5, v_call_i_3_8_5);
(*   %arrayidx11.3.8.5 = getelementptr inbounds i16, i16* %r, i64 168 *)
(*   %945 = load i16, i16* %arrayidx11.3.8.5, align 2, !tbaa !3 *)
mov v945 mem0_336;
(*   %sub.3.8.5 = sub i16 %945, %call.i.3.8.5 *)
sub v_sub_3_8_5 v945 v_call_i_3_8_5;
(*   store i16 %sub.3.8.5, i16* %arrayidx9.3.8.5, align 2, !tbaa !3 *)
mov mem0_368 v_sub_3_8_5;
(*   %add21.3.8.5 = add i16 %945, %call.i.3.8.5 *)
add v_add21_3_8_5 v945 v_call_i_3_8_5;
(*   store i16 %add21.3.8.5, i16* %arrayidx11.3.8.5, align 2, !tbaa !3 *)
mov mem0_336 v_add21_3_8_5;
(*   %arrayidx9.3.9.5 = getelementptr inbounds i16, i16* %r, i64 185 *)
(*   %946 = load i16, i16* %arrayidx9.3.9.5, align 2, !tbaa !3 *)
mov v946 mem0_370;
(*   %conv1.i.3.9.5 = sext i16 %946 to i32 *)
cast v_conv1_i_3_9_5@sint32 v946@sint16;
(*   %mul.i.3.9.5 = mul nsw i32 %conv1.i.3.9.5, -1202 *)
mul v_mul_i_3_9_5 v_conv1_i_3_9_5 (-1202)@sint32;
(*   %call.i.3.9.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.9.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_9_5, v_call_i_3_9_5);
(*   %arrayidx11.3.9.5 = getelementptr inbounds i16, i16* %r, i64 169 *)
(*   %947 = load i16, i16* %arrayidx11.3.9.5, align 2, !tbaa !3 *)
mov v947 mem0_338;
(*   %sub.3.9.5 = sub i16 %947, %call.i.3.9.5 *)
sub v_sub_3_9_5 v947 v_call_i_3_9_5;
(*   store i16 %sub.3.9.5, i16* %arrayidx9.3.9.5, align 2, !tbaa !3 *)
mov mem0_370 v_sub_3_9_5;
(*   %add21.3.9.5 = add i16 %947, %call.i.3.9.5 *)
add v_add21_3_9_5 v947 v_call_i_3_9_5;
(*   store i16 %add21.3.9.5, i16* %arrayidx11.3.9.5, align 2, !tbaa !3 *)
mov mem0_338 v_add21_3_9_5;
(*   %arrayidx9.3.10.5 = getelementptr inbounds i16, i16* %r, i64 186 *)
(*   %948 = load i16, i16* %arrayidx9.3.10.5, align 2, !tbaa !3 *)
mov v948 mem0_372;
(*   %conv1.i.3.10.5 = sext i16 %948 to i32 *)
cast v_conv1_i_3_10_5@sint32 v948@sint16;
(*   %mul.i.3.10.5 = mul nsw i32 %conv1.i.3.10.5, -1202 *)
mul v_mul_i_3_10_5 v_conv1_i_3_10_5 (-1202)@sint32;
(*   %call.i.3.10.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.10.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_10_5, v_call_i_3_10_5);
(*   %arrayidx11.3.10.5 = getelementptr inbounds i16, i16* %r, i64 170 *)
(*   %949 = load i16, i16* %arrayidx11.3.10.5, align 2, !tbaa !3 *)
mov v949 mem0_340;
(*   %sub.3.10.5 = sub i16 %949, %call.i.3.10.5 *)
sub v_sub_3_10_5 v949 v_call_i_3_10_5;
(*   store i16 %sub.3.10.5, i16* %arrayidx9.3.10.5, align 2, !tbaa !3 *)
mov mem0_372 v_sub_3_10_5;
(*   %add21.3.10.5 = add i16 %949, %call.i.3.10.5 *)
add v_add21_3_10_5 v949 v_call_i_3_10_5;
(*   store i16 %add21.3.10.5, i16* %arrayidx11.3.10.5, align 2, !tbaa !3 *)
mov mem0_340 v_add21_3_10_5;
(*   %arrayidx9.3.11.5 = getelementptr inbounds i16, i16* %r, i64 187 *)
(*   %950 = load i16, i16* %arrayidx9.3.11.5, align 2, !tbaa !3 *)
mov v950 mem0_374;
(*   %conv1.i.3.11.5 = sext i16 %950 to i32 *)
cast v_conv1_i_3_11_5@sint32 v950@sint16;
(*   %mul.i.3.11.5 = mul nsw i32 %conv1.i.3.11.5, -1202 *)
mul v_mul_i_3_11_5 v_conv1_i_3_11_5 (-1202)@sint32;
(*   %call.i.3.11.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.11.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_11_5, v_call_i_3_11_5);
(*   %arrayidx11.3.11.5 = getelementptr inbounds i16, i16* %r, i64 171 *)
(*   %951 = load i16, i16* %arrayidx11.3.11.5, align 2, !tbaa !3 *)
mov v951 mem0_342;
(*   %sub.3.11.5 = sub i16 %951, %call.i.3.11.5 *)
sub v_sub_3_11_5 v951 v_call_i_3_11_5;
(*   store i16 %sub.3.11.5, i16* %arrayidx9.3.11.5, align 2, !tbaa !3 *)
mov mem0_374 v_sub_3_11_5;
(*   %add21.3.11.5 = add i16 %951, %call.i.3.11.5 *)
add v_add21_3_11_5 v951 v_call_i_3_11_5;
(*   store i16 %add21.3.11.5, i16* %arrayidx11.3.11.5, align 2, !tbaa !3 *)
mov mem0_342 v_add21_3_11_5;
(*   %arrayidx9.3.12.5 = getelementptr inbounds i16, i16* %r, i64 188 *)
(*   %952 = load i16, i16* %arrayidx9.3.12.5, align 2, !tbaa !3 *)
mov v952 mem0_376;
(*   %conv1.i.3.12.5 = sext i16 %952 to i32 *)
cast v_conv1_i_3_12_5@sint32 v952@sint16;
(*   %mul.i.3.12.5 = mul nsw i32 %conv1.i.3.12.5, -1202 *)
mul v_mul_i_3_12_5 v_conv1_i_3_12_5 (-1202)@sint32;
(*   %call.i.3.12.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.12.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_12_5, v_call_i_3_12_5);
(*   %arrayidx11.3.12.5 = getelementptr inbounds i16, i16* %r, i64 172 *)
(*   %953 = load i16, i16* %arrayidx11.3.12.5, align 2, !tbaa !3 *)
mov v953 mem0_344;
(*   %sub.3.12.5 = sub i16 %953, %call.i.3.12.5 *)
sub v_sub_3_12_5 v953 v_call_i_3_12_5;
(*   store i16 %sub.3.12.5, i16* %arrayidx9.3.12.5, align 2, !tbaa !3 *)
mov mem0_376 v_sub_3_12_5;
(*   %add21.3.12.5 = add i16 %953, %call.i.3.12.5 *)
add v_add21_3_12_5 v953 v_call_i_3_12_5;
(*   store i16 %add21.3.12.5, i16* %arrayidx11.3.12.5, align 2, !tbaa !3 *)
mov mem0_344 v_add21_3_12_5;
(*   %arrayidx9.3.13.5 = getelementptr inbounds i16, i16* %r, i64 189 *)
(*   %954 = load i16, i16* %arrayidx9.3.13.5, align 2, !tbaa !3 *)
mov v954 mem0_378;
(*   %conv1.i.3.13.5 = sext i16 %954 to i32 *)
cast v_conv1_i_3_13_5@sint32 v954@sint16;
(*   %mul.i.3.13.5 = mul nsw i32 %conv1.i.3.13.5, -1202 *)
mul v_mul_i_3_13_5 v_conv1_i_3_13_5 (-1202)@sint32;
(*   %call.i.3.13.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.13.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_13_5, v_call_i_3_13_5);
(*   %arrayidx11.3.13.5 = getelementptr inbounds i16, i16* %r, i64 173 *)
(*   %955 = load i16, i16* %arrayidx11.3.13.5, align 2, !tbaa !3 *)
mov v955 mem0_346;
(*   %sub.3.13.5 = sub i16 %955, %call.i.3.13.5 *)
sub v_sub_3_13_5 v955 v_call_i_3_13_5;
(*   store i16 %sub.3.13.5, i16* %arrayidx9.3.13.5, align 2, !tbaa !3 *)
mov mem0_378 v_sub_3_13_5;
(*   %add21.3.13.5 = add i16 %955, %call.i.3.13.5 *)
add v_add21_3_13_5 v955 v_call_i_3_13_5;
(*   store i16 %add21.3.13.5, i16* %arrayidx11.3.13.5, align 2, !tbaa !3 *)
mov mem0_346 v_add21_3_13_5;
(*   %arrayidx9.3.14.5 = getelementptr inbounds i16, i16* %r, i64 190 *)
(*   %956 = load i16, i16* %arrayidx9.3.14.5, align 2, !tbaa !3 *)
mov v956 mem0_380;
(*   %conv1.i.3.14.5 = sext i16 %956 to i32 *)
cast v_conv1_i_3_14_5@sint32 v956@sint16;
(*   %mul.i.3.14.5 = mul nsw i32 %conv1.i.3.14.5, -1202 *)
mul v_mul_i_3_14_5 v_conv1_i_3_14_5 (-1202)@sint32;
(*   %call.i.3.14.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.14.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_14_5, v_call_i_3_14_5);
(*   %arrayidx11.3.14.5 = getelementptr inbounds i16, i16* %r, i64 174 *)
(*   %957 = load i16, i16* %arrayidx11.3.14.5, align 2, !tbaa !3 *)
mov v957 mem0_348;
(*   %sub.3.14.5 = sub i16 %957, %call.i.3.14.5 *)
sub v_sub_3_14_5 v957 v_call_i_3_14_5;
(*   store i16 %sub.3.14.5, i16* %arrayidx9.3.14.5, align 2, !tbaa !3 *)
mov mem0_380 v_sub_3_14_5;
(*   %add21.3.14.5 = add i16 %957, %call.i.3.14.5 *)
add v_add21_3_14_5 v957 v_call_i_3_14_5;
(*   store i16 %add21.3.14.5, i16* %arrayidx11.3.14.5, align 2, !tbaa !3 *)
mov mem0_348 v_add21_3_14_5;
(*   %arrayidx9.3.15.5 = getelementptr inbounds i16, i16* %r, i64 191 *)
(*   %958 = load i16, i16* %arrayidx9.3.15.5, align 2, !tbaa !3 *)
mov v958 mem0_382;
(*   %conv1.i.3.15.5 = sext i16 %958 to i32 *)
cast v_conv1_i_3_15_5@sint32 v958@sint16;
(*   %mul.i.3.15.5 = mul nsw i32 %conv1.i.3.15.5, -1202 *)
mul v_mul_i_3_15_5 v_conv1_i_3_15_5 (-1202)@sint32;
(*   %call.i.3.15.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.15.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_15_5, v_call_i_3_15_5);
(*   %arrayidx11.3.15.5 = getelementptr inbounds i16, i16* %r, i64 175 *)
(*   %959 = load i16, i16* %arrayidx11.3.15.5, align 2, !tbaa !3 *)
mov v959 mem0_350;
(*   %sub.3.15.5 = sub i16 %959, %call.i.3.15.5 *)
sub v_sub_3_15_5 v959 v_call_i_3_15_5;
(*   store i16 %sub.3.15.5, i16* %arrayidx9.3.15.5, align 2, !tbaa !3 *)
mov mem0_382 v_sub_3_15_5;
(*   %add21.3.15.5 = add i16 %959, %call.i.3.15.5 *)
add v_add21_3_15_5 v959 v_call_i_3_15_5;
(*   store i16 %add21.3.15.5, i16* %arrayidx11.3.15.5, align 2, !tbaa !3 *)
mov mem0_350 v_add21_3_15_5;

(* NOTE: k = 14 *)

(*   %arrayidx9.3.6228 = getelementptr inbounds i16, i16* %r, i64 208 *)
(*   %960 = load i16, i16* %arrayidx9.3.6228, align 2, !tbaa !3 *)
mov v960 mem0_416;
(*   %conv1.i.3.6229 = sext i16 %960 to i32 *)
cast v_conv1_i_3_6229@sint32 v960@sint16;
(*   %mul.i.3.6230 = mul nsw i32 %conv1.i.3.6229, -1474 *)
mul v_mul_i_3_6230 v_conv1_i_3_6229 (-1474)@sint32;
(*   %call.i.3.6231 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.6230) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_6230, v_call_i_3_6231);
(*   %arrayidx11.3.6232 = getelementptr inbounds i16, i16* %r, i64 192 *)
(*   %961 = load i16, i16* %arrayidx11.3.6232, align 2, !tbaa !3 *)
mov v961 mem0_384;
(*   %sub.3.6233 = sub i16 %961, %call.i.3.6231 *)
sub v_sub_3_6233 v961 v_call_i_3_6231;
(*   store i16 %sub.3.6233, i16* %arrayidx9.3.6228, align 2, !tbaa !3 *)
mov mem0_416 v_sub_3_6233;
(*   %add21.3.6234 = add i16 %961, %call.i.3.6231 *)
add v_add21_3_6234 v961 v_call_i_3_6231;
(*   store i16 %add21.3.6234, i16* %arrayidx11.3.6232, align 2, !tbaa !3 *)
mov mem0_384 v_add21_3_6234;
(*   %arrayidx9.3.1.6 = getelementptr inbounds i16, i16* %r, i64 209 *)
(*   %962 = load i16, i16* %arrayidx9.3.1.6, align 2, !tbaa !3 *)
mov v962 mem0_418;
(*   %conv1.i.3.1.6 = sext i16 %962 to i32 *)
cast v_conv1_i_3_1_6@sint32 v962@sint16;
(*   %mul.i.3.1.6 = mul nsw i32 %conv1.i.3.1.6, -1474 *)
mul v_mul_i_3_1_6 v_conv1_i_3_1_6 (-1474)@sint32;
(*   %call.i.3.1.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.1.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_1_6, v_call_i_3_1_6);
(*   %arrayidx11.3.1.6 = getelementptr inbounds i16, i16* %r, i64 193 *)
(*   %963 = load i16, i16* %arrayidx11.3.1.6, align 2, !tbaa !3 *)
mov v963 mem0_386;
(*   %sub.3.1.6 = sub i16 %963, %call.i.3.1.6 *)
sub v_sub_3_1_6 v963 v_call_i_3_1_6;
(*   store i16 %sub.3.1.6, i16* %arrayidx9.3.1.6, align 2, !tbaa !3 *)
mov mem0_418 v_sub_3_1_6;
(*   %add21.3.1.6 = add i16 %963, %call.i.3.1.6 *)
add v_add21_3_1_6 v963 v_call_i_3_1_6;
(*   store i16 %add21.3.1.6, i16* %arrayidx11.3.1.6, align 2, !tbaa !3 *)
mov mem0_386 v_add21_3_1_6;
(*   %arrayidx9.3.2.6 = getelementptr inbounds i16, i16* %r, i64 210 *)
(*   %964 = load i16, i16* %arrayidx9.3.2.6, align 2, !tbaa !3 *)
mov v964 mem0_420;
(*   %conv1.i.3.2.6 = sext i16 %964 to i32 *)
cast v_conv1_i_3_2_6@sint32 v964@sint16;
(*   %mul.i.3.2.6 = mul nsw i32 %conv1.i.3.2.6, -1474 *)
mul v_mul_i_3_2_6 v_conv1_i_3_2_6 (-1474)@sint32;
(*   %call.i.3.2.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.2.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_2_6, v_call_i_3_2_6);
(*   %arrayidx11.3.2.6 = getelementptr inbounds i16, i16* %r, i64 194 *)
(*   %965 = load i16, i16* %arrayidx11.3.2.6, align 2, !tbaa !3 *)
mov v965 mem0_388;
(*   %sub.3.2.6 = sub i16 %965, %call.i.3.2.6 *)
sub v_sub_3_2_6 v965 v_call_i_3_2_6;
(*   store i16 %sub.3.2.6, i16* %arrayidx9.3.2.6, align 2, !tbaa !3 *)
mov mem0_420 v_sub_3_2_6;
(*   %add21.3.2.6 = add i16 %965, %call.i.3.2.6 *)
add v_add21_3_2_6 v965 v_call_i_3_2_6;
(*   store i16 %add21.3.2.6, i16* %arrayidx11.3.2.6, align 2, !tbaa !3 *)
mov mem0_388 v_add21_3_2_6;
(*   %arrayidx9.3.3.6 = getelementptr inbounds i16, i16* %r, i64 211 *)
(*   %966 = load i16, i16* %arrayidx9.3.3.6, align 2, !tbaa !3 *)
mov v966 mem0_422;
(*   %conv1.i.3.3.6 = sext i16 %966 to i32 *)
cast v_conv1_i_3_3_6@sint32 v966@sint16;
(*   %mul.i.3.3.6 = mul nsw i32 %conv1.i.3.3.6, -1474 *)
mul v_mul_i_3_3_6 v_conv1_i_3_3_6 (-1474)@sint32;
(*   %call.i.3.3.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.3.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_3_6, v_call_i_3_3_6);
(*   %arrayidx11.3.3.6 = getelementptr inbounds i16, i16* %r, i64 195 *)
(*   %967 = load i16, i16* %arrayidx11.3.3.6, align 2, !tbaa !3 *)
mov v967 mem0_390;
(*   %sub.3.3.6 = sub i16 %967, %call.i.3.3.6 *)
sub v_sub_3_3_6 v967 v_call_i_3_3_6;
(*   store i16 %sub.3.3.6, i16* %arrayidx9.3.3.6, align 2, !tbaa !3 *)
mov mem0_422 v_sub_3_3_6;
(*   %add21.3.3.6 = add i16 %967, %call.i.3.3.6 *)
add v_add21_3_3_6 v967 v_call_i_3_3_6;
(*   store i16 %add21.3.3.6, i16* %arrayidx11.3.3.6, align 2, !tbaa !3 *)
mov mem0_390 v_add21_3_3_6;
(*   %arrayidx9.3.4.6 = getelementptr inbounds i16, i16* %r, i64 212 *)
(*   %968 = load i16, i16* %arrayidx9.3.4.6, align 2, !tbaa !3 *)
mov v968 mem0_424;
(*   %conv1.i.3.4.6 = sext i16 %968 to i32 *)
cast v_conv1_i_3_4_6@sint32 v968@sint16;
(*   %mul.i.3.4.6 = mul nsw i32 %conv1.i.3.4.6, -1474 *)
mul v_mul_i_3_4_6 v_conv1_i_3_4_6 (-1474)@sint32;
(*   %call.i.3.4.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.4.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_4_6, v_call_i_3_4_6);
(*   %arrayidx11.3.4.6 = getelementptr inbounds i16, i16* %r, i64 196 *)
(*   %969 = load i16, i16* %arrayidx11.3.4.6, align 2, !tbaa !3 *)
mov v969 mem0_392;
(*   %sub.3.4.6 = sub i16 %969, %call.i.3.4.6 *)
sub v_sub_3_4_6 v969 v_call_i_3_4_6;
(*   store i16 %sub.3.4.6, i16* %arrayidx9.3.4.6, align 2, !tbaa !3 *)
mov mem0_424 v_sub_3_4_6;
(*   %add21.3.4.6 = add i16 %969, %call.i.3.4.6 *)
add v_add21_3_4_6 v969 v_call_i_3_4_6;
(*   store i16 %add21.3.4.6, i16* %arrayidx11.3.4.6, align 2, !tbaa !3 *)
mov mem0_392 v_add21_3_4_6;
(*   %arrayidx9.3.5.6 = getelementptr inbounds i16, i16* %r, i64 213 *)
(*   %970 = load i16, i16* %arrayidx9.3.5.6, align 2, !tbaa !3 *)
mov v970 mem0_426;
(*   %conv1.i.3.5.6 = sext i16 %970 to i32 *)
cast v_conv1_i_3_5_6@sint32 v970@sint16;
(*   %mul.i.3.5.6 = mul nsw i32 %conv1.i.3.5.6, -1474 *)
mul v_mul_i_3_5_6 v_conv1_i_3_5_6 (-1474)@sint32;
(*   %call.i.3.5.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.5.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_5_6, v_call_i_3_5_6);
(*   %arrayidx11.3.5.6 = getelementptr inbounds i16, i16* %r, i64 197 *)
(*   %971 = load i16, i16* %arrayidx11.3.5.6, align 2, !tbaa !3 *)
mov v971 mem0_394;
(*   %sub.3.5.6 = sub i16 %971, %call.i.3.5.6 *)
sub v_sub_3_5_6 v971 v_call_i_3_5_6;
(*   store i16 %sub.3.5.6, i16* %arrayidx9.3.5.6, align 2, !tbaa !3 *)
mov mem0_426 v_sub_3_5_6;
(*   %add21.3.5.6 = add i16 %971, %call.i.3.5.6 *)
add v_add21_3_5_6 v971 v_call_i_3_5_6;
(*   store i16 %add21.3.5.6, i16* %arrayidx11.3.5.6, align 2, !tbaa !3 *)
mov mem0_394 v_add21_3_5_6;
(*   %arrayidx9.3.6.6 = getelementptr inbounds i16, i16* %r, i64 214 *)
(*   %972 = load i16, i16* %arrayidx9.3.6.6, align 2, !tbaa !3 *)
mov v972 mem0_428;
(*   %conv1.i.3.6.6 = sext i16 %972 to i32 *)
cast v_conv1_i_3_6_6@sint32 v972@sint16;
(*   %mul.i.3.6.6 = mul nsw i32 %conv1.i.3.6.6, -1474 *)
mul v_mul_i_3_6_6 v_conv1_i_3_6_6 (-1474)@sint32;
(*   %call.i.3.6.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.6.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_6_6, v_call_i_3_6_6);
(*   %arrayidx11.3.6.6 = getelementptr inbounds i16, i16* %r, i64 198 *)
(*   %973 = load i16, i16* %arrayidx11.3.6.6, align 2, !tbaa !3 *)
mov v973 mem0_396;
(*   %sub.3.6.6 = sub i16 %973, %call.i.3.6.6 *)
sub v_sub_3_6_6 v973 v_call_i_3_6_6;
(*   store i16 %sub.3.6.6, i16* %arrayidx9.3.6.6, align 2, !tbaa !3 *)
mov mem0_428 v_sub_3_6_6;
(*   %add21.3.6.6 = add i16 %973, %call.i.3.6.6 *)
add v_add21_3_6_6 v973 v_call_i_3_6_6;
(*   store i16 %add21.3.6.6, i16* %arrayidx11.3.6.6, align 2, !tbaa !3 *)
mov mem0_396 v_add21_3_6_6;
(*   %arrayidx9.3.7.6 = getelementptr inbounds i16, i16* %r, i64 215 *)
(*   %974 = load i16, i16* %arrayidx9.3.7.6, align 2, !tbaa !3 *)
mov v974 mem0_430;
(*   %conv1.i.3.7.6 = sext i16 %974 to i32 *)
cast v_conv1_i_3_7_6@sint32 v974@sint16;
(*   %mul.i.3.7.6 = mul nsw i32 %conv1.i.3.7.6, -1474 *)
mul v_mul_i_3_7_6 v_conv1_i_3_7_6 (-1474)@sint32;
(*   %call.i.3.7.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.7.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_7_6, v_call_i_3_7_6);
(*   %arrayidx11.3.7.6 = getelementptr inbounds i16, i16* %r, i64 199 *)
(*   %975 = load i16, i16* %arrayidx11.3.7.6, align 2, !tbaa !3 *)
mov v975 mem0_398;
(*   %sub.3.7.6 = sub i16 %975, %call.i.3.7.6 *)
sub v_sub_3_7_6 v975 v_call_i_3_7_6;
(*   store i16 %sub.3.7.6, i16* %arrayidx9.3.7.6, align 2, !tbaa !3 *)
mov mem0_430 v_sub_3_7_6;
(*   %add21.3.7.6 = add i16 %975, %call.i.3.7.6 *)
add v_add21_3_7_6 v975 v_call_i_3_7_6;
(*   store i16 %add21.3.7.6, i16* %arrayidx11.3.7.6, align 2, !tbaa !3 *)
mov mem0_398 v_add21_3_7_6;
(*   %arrayidx9.3.8.6 = getelementptr inbounds i16, i16* %r, i64 216 *)
(*   %976 = load i16, i16* %arrayidx9.3.8.6, align 2, !tbaa !3 *)
mov v976 mem0_432;
(*   %conv1.i.3.8.6 = sext i16 %976 to i32 *)
cast v_conv1_i_3_8_6@sint32 v976@sint16;
(*   %mul.i.3.8.6 = mul nsw i32 %conv1.i.3.8.6, -1474 *)
mul v_mul_i_3_8_6 v_conv1_i_3_8_6 (-1474)@sint32;
(*   %call.i.3.8.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.8.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_8_6, v_call_i_3_8_6);
(*   %arrayidx11.3.8.6 = getelementptr inbounds i16, i16* %r, i64 200 *)
(*   %977 = load i16, i16* %arrayidx11.3.8.6, align 2, !tbaa !3 *)
mov v977 mem0_400;
(*   %sub.3.8.6 = sub i16 %977, %call.i.3.8.6 *)
sub v_sub_3_8_6 v977 v_call_i_3_8_6;
(*   store i16 %sub.3.8.6, i16* %arrayidx9.3.8.6, align 2, !tbaa !3 *)
mov mem0_432 v_sub_3_8_6;
(*   %add21.3.8.6 = add i16 %977, %call.i.3.8.6 *)
add v_add21_3_8_6 v977 v_call_i_3_8_6;
(*   store i16 %add21.3.8.6, i16* %arrayidx11.3.8.6, align 2, !tbaa !3 *)
mov mem0_400 v_add21_3_8_6;
(*   %arrayidx9.3.9.6 = getelementptr inbounds i16, i16* %r, i64 217 *)
(*   %978 = load i16, i16* %arrayidx9.3.9.6, align 2, !tbaa !3 *)
mov v978 mem0_434;
(*   %conv1.i.3.9.6 = sext i16 %978 to i32 *)
cast v_conv1_i_3_9_6@sint32 v978@sint16;
(*   %mul.i.3.9.6 = mul nsw i32 %conv1.i.3.9.6, -1474 *)
mul v_mul_i_3_9_6 v_conv1_i_3_9_6 (-1474)@sint32;
(*   %call.i.3.9.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.9.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_9_6, v_call_i_3_9_6);
(*   %arrayidx11.3.9.6 = getelementptr inbounds i16, i16* %r, i64 201 *)
(*   %979 = load i16, i16* %arrayidx11.3.9.6, align 2, !tbaa !3 *)
mov v979 mem0_402;
(*   %sub.3.9.6 = sub i16 %979, %call.i.3.9.6 *)
sub v_sub_3_9_6 v979 v_call_i_3_9_6;
(*   store i16 %sub.3.9.6, i16* %arrayidx9.3.9.6, align 2, !tbaa !3 *)
mov mem0_434 v_sub_3_9_6;
(*   %add21.3.9.6 = add i16 %979, %call.i.3.9.6 *)
add v_add21_3_9_6 v979 v_call_i_3_9_6;
(*   store i16 %add21.3.9.6, i16* %arrayidx11.3.9.6, align 2, !tbaa !3 *)
mov mem0_402 v_add21_3_9_6;
(*   %arrayidx9.3.10.6 = getelementptr inbounds i16, i16* %r, i64 218 *)
(*   %980 = load i16, i16* %arrayidx9.3.10.6, align 2, !tbaa !3 *)
mov v980 mem0_436;
(*   %conv1.i.3.10.6 = sext i16 %980 to i32 *)
cast v_conv1_i_3_10_6@sint32 v980@sint16;
(*   %mul.i.3.10.6 = mul nsw i32 %conv1.i.3.10.6, -1474 *)
mul v_mul_i_3_10_6 v_conv1_i_3_10_6 (-1474)@sint32;
(*   %call.i.3.10.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.10.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_10_6, v_call_i_3_10_6);
(*   %arrayidx11.3.10.6 = getelementptr inbounds i16, i16* %r, i64 202 *)
(*   %981 = load i16, i16* %arrayidx11.3.10.6, align 2, !tbaa !3 *)
mov v981 mem0_404;
(*   %sub.3.10.6 = sub i16 %981, %call.i.3.10.6 *)
sub v_sub_3_10_6 v981 v_call_i_3_10_6;
(*   store i16 %sub.3.10.6, i16* %arrayidx9.3.10.6, align 2, !tbaa !3 *)
mov mem0_436 v_sub_3_10_6;
(*   %add21.3.10.6 = add i16 %981, %call.i.3.10.6 *)
add v_add21_3_10_6 v981 v_call_i_3_10_6;
(*   store i16 %add21.3.10.6, i16* %arrayidx11.3.10.6, align 2, !tbaa !3 *)
mov mem0_404 v_add21_3_10_6;
(*   %arrayidx9.3.11.6 = getelementptr inbounds i16, i16* %r, i64 219 *)
(*   %982 = load i16, i16* %arrayidx9.3.11.6, align 2, !tbaa !3 *)
mov v982 mem0_438;
(*   %conv1.i.3.11.6 = sext i16 %982 to i32 *)
cast v_conv1_i_3_11_6@sint32 v982@sint16;
(*   %mul.i.3.11.6 = mul nsw i32 %conv1.i.3.11.6, -1474 *)
mul v_mul_i_3_11_6 v_conv1_i_3_11_6 (-1474)@sint32;
(*   %call.i.3.11.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.11.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_11_6, v_call_i_3_11_6);
(*   %arrayidx11.3.11.6 = getelementptr inbounds i16, i16* %r, i64 203 *)
(*   %983 = load i16, i16* %arrayidx11.3.11.6, align 2, !tbaa !3 *)
mov v983 mem0_406;
(*   %sub.3.11.6 = sub i16 %983, %call.i.3.11.6 *)
sub v_sub_3_11_6 v983 v_call_i_3_11_6;
(*   store i16 %sub.3.11.6, i16* %arrayidx9.3.11.6, align 2, !tbaa !3 *)
mov mem0_438 v_sub_3_11_6;
(*   %add21.3.11.6 = add i16 %983, %call.i.3.11.6 *)
add v_add21_3_11_6 v983 v_call_i_3_11_6;
(*   store i16 %add21.3.11.6, i16* %arrayidx11.3.11.6, align 2, !tbaa !3 *)
mov mem0_406 v_add21_3_11_6;
(*   %arrayidx9.3.12.6 = getelementptr inbounds i16, i16* %r, i64 220 *)
(*   %984 = load i16, i16* %arrayidx9.3.12.6, align 2, !tbaa !3 *)
mov v984 mem0_440;
(*   %conv1.i.3.12.6 = sext i16 %984 to i32 *)
cast v_conv1_i_3_12_6@sint32 v984@sint16;
(*   %mul.i.3.12.6 = mul nsw i32 %conv1.i.3.12.6, -1474 *)
mul v_mul_i_3_12_6 v_conv1_i_3_12_6 (-1474)@sint32;
(*   %call.i.3.12.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.12.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_12_6, v_call_i_3_12_6);
(*   %arrayidx11.3.12.6 = getelementptr inbounds i16, i16* %r, i64 204 *)
(*   %985 = load i16, i16* %arrayidx11.3.12.6, align 2, !tbaa !3 *)
mov v985 mem0_408;
(*   %sub.3.12.6 = sub i16 %985, %call.i.3.12.6 *)
sub v_sub_3_12_6 v985 v_call_i_3_12_6;
(*   store i16 %sub.3.12.6, i16* %arrayidx9.3.12.6, align 2, !tbaa !3 *)
mov mem0_440 v_sub_3_12_6;
(*   %add21.3.12.6 = add i16 %985, %call.i.3.12.6 *)
add v_add21_3_12_6 v985 v_call_i_3_12_6;
(*   store i16 %add21.3.12.6, i16* %arrayidx11.3.12.6, align 2, !tbaa !3 *)
mov mem0_408 v_add21_3_12_6;
(*   %arrayidx9.3.13.6 = getelementptr inbounds i16, i16* %r, i64 221 *)
(*   %986 = load i16, i16* %arrayidx9.3.13.6, align 2, !tbaa !3 *)
mov v986 mem0_442;
(*   %conv1.i.3.13.6 = sext i16 %986 to i32 *)
cast v_conv1_i_3_13_6@sint32 v986@sint16;
(*   %mul.i.3.13.6 = mul nsw i32 %conv1.i.3.13.6, -1474 *)
mul v_mul_i_3_13_6 v_conv1_i_3_13_6 (-1474)@sint32;
(*   %call.i.3.13.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.13.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_13_6, v_call_i_3_13_6);
(*   %arrayidx11.3.13.6 = getelementptr inbounds i16, i16* %r, i64 205 *)
(*   %987 = load i16, i16* %arrayidx11.3.13.6, align 2, !tbaa !3 *)
mov v987 mem0_410;
(*   %sub.3.13.6 = sub i16 %987, %call.i.3.13.6 *)
sub v_sub_3_13_6 v987 v_call_i_3_13_6;
(*   store i16 %sub.3.13.6, i16* %arrayidx9.3.13.6, align 2, !tbaa !3 *)
mov mem0_442 v_sub_3_13_6;
(*   %add21.3.13.6 = add i16 %987, %call.i.3.13.6 *)
add v_add21_3_13_6 v987 v_call_i_3_13_6;
(*   store i16 %add21.3.13.6, i16* %arrayidx11.3.13.6, align 2, !tbaa !3 *)
mov mem0_410 v_add21_3_13_6;
(*   %arrayidx9.3.14.6 = getelementptr inbounds i16, i16* %r, i64 222 *)
(*   %988 = load i16, i16* %arrayidx9.3.14.6, align 2, !tbaa !3 *)
mov v988 mem0_444;
(*   %conv1.i.3.14.6 = sext i16 %988 to i32 *)
cast v_conv1_i_3_14_6@sint32 v988@sint16;
(*   %mul.i.3.14.6 = mul nsw i32 %conv1.i.3.14.6, -1474 *)
mul v_mul_i_3_14_6 v_conv1_i_3_14_6 (-1474)@sint32;
(*   %call.i.3.14.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.14.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_14_6, v_call_i_3_14_6);
(*   %arrayidx11.3.14.6 = getelementptr inbounds i16, i16* %r, i64 206 *)
(*   %989 = load i16, i16* %arrayidx11.3.14.6, align 2, !tbaa !3 *)
mov v989 mem0_412;
(*   %sub.3.14.6 = sub i16 %989, %call.i.3.14.6 *)
sub v_sub_3_14_6 v989 v_call_i_3_14_6;
(*   store i16 %sub.3.14.6, i16* %arrayidx9.3.14.6, align 2, !tbaa !3 *)
mov mem0_444 v_sub_3_14_6;
(*   %add21.3.14.6 = add i16 %989, %call.i.3.14.6 *)
add v_add21_3_14_6 v989 v_call_i_3_14_6;
(*   store i16 %add21.3.14.6, i16* %arrayidx11.3.14.6, align 2, !tbaa !3 *)
mov mem0_412 v_add21_3_14_6;
(*   %arrayidx9.3.15.6 = getelementptr inbounds i16, i16* %r, i64 223 *)
(*   %990 = load i16, i16* %arrayidx9.3.15.6, align 2, !tbaa !3 *)
mov v990 mem0_446;
(*   %conv1.i.3.15.6 = sext i16 %990 to i32 *)
cast v_conv1_i_3_15_6@sint32 v990@sint16;
(*   %mul.i.3.15.6 = mul nsw i32 %conv1.i.3.15.6, -1474 *)
mul v_mul_i_3_15_6 v_conv1_i_3_15_6 (-1474)@sint32;
(*   %call.i.3.15.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.15.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_15_6, v_call_i_3_15_6);
(*   %arrayidx11.3.15.6 = getelementptr inbounds i16, i16* %r, i64 207 *)
(*   %991 = load i16, i16* %arrayidx11.3.15.6, align 2, !tbaa !3 *)
mov v991 mem0_414;
(*   %sub.3.15.6 = sub i16 %991, %call.i.3.15.6 *)
sub v_sub_3_15_6 v991 v_call_i_3_15_6;
(*   store i16 %sub.3.15.6, i16* %arrayidx9.3.15.6, align 2, !tbaa !3 *)
mov mem0_446 v_sub_3_15_6;
(*   %add21.3.15.6 = add i16 %991, %call.i.3.15.6 *)
add v_add21_3_15_6 v991 v_call_i_3_15_6;
(*   store i16 %add21.3.15.6, i16* %arrayidx11.3.15.6, align 2, !tbaa !3 *)
mov mem0_414 v_add21_3_15_6;

(* NOTE: k = 15 *)

(*   %arrayidx9.3.7238 = getelementptr inbounds i16, i16* %r, i64 240 *)
(*   %992 = load i16, i16* %arrayidx9.3.7238, align 2, !tbaa !3 *)
mov v992 mem0_480;
(*   %conv1.i.3.7239 = sext i16 %992 to i32 *)
cast v_conv1_i_3_7239@sint32 v992@sint16;
(*   %mul.i.3.7240 = mul nsw i32 %conv1.i.3.7239, 1468 *)
mul v_mul_i_3_7240 v_conv1_i_3_7239 (1468)@sint32;
(*   %call.i.3.7241 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.7240) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_7240, v_call_i_3_7241);
(*   %arrayidx11.3.7242 = getelementptr inbounds i16, i16* %r, i64 224 *)
(*   %993 = load i16, i16* %arrayidx11.3.7242, align 2, !tbaa !3 *)
mov v993 mem0_448;
(*   %sub.3.7243 = sub i16 %993, %call.i.3.7241 *)
sub v_sub_3_7243 v993 v_call_i_3_7241;
(*   store i16 %sub.3.7243, i16* %arrayidx9.3.7238, align 2, !tbaa !3 *)
mov mem0_480 v_sub_3_7243;
(*   %add21.3.7244 = add i16 %993, %call.i.3.7241 *)
add v_add21_3_7244 v993 v_call_i_3_7241;
(*   store i16 %add21.3.7244, i16* %arrayidx11.3.7242, align 2, !tbaa !3 *)
mov mem0_448 v_add21_3_7244;
(*   %arrayidx9.3.1.7 = getelementptr inbounds i16, i16* %r, i64 241 *)
(*   %994 = load i16, i16* %arrayidx9.3.1.7, align 2, !tbaa !3 *)
mov v994 mem0_482;
(*   %conv1.i.3.1.7 = sext i16 %994 to i32 *)
cast v_conv1_i_3_1_7@sint32 v994@sint16;
(*   %mul.i.3.1.7 = mul nsw i32 %conv1.i.3.1.7, 1468 *)
mul v_mul_i_3_1_7 v_conv1_i_3_1_7 (1468)@sint32;
(*   %call.i.3.1.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.1.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_1_7, v_call_i_3_1_7);
(*   %arrayidx11.3.1.7 = getelementptr inbounds i16, i16* %r, i64 225 *)
(*   %995 = load i16, i16* %arrayidx11.3.1.7, align 2, !tbaa !3 *)
mov v995 mem0_450;
(*   %sub.3.1.7 = sub i16 %995, %call.i.3.1.7 *)
sub v_sub_3_1_7 v995 v_call_i_3_1_7;
(*   store i16 %sub.3.1.7, i16* %arrayidx9.3.1.7, align 2, !tbaa !3 *)
mov mem0_482 v_sub_3_1_7;
(*   %add21.3.1.7 = add i16 %995, %call.i.3.1.7 *)
add v_add21_3_1_7 v995 v_call_i_3_1_7;
(*   store i16 %add21.3.1.7, i16* %arrayidx11.3.1.7, align 2, !tbaa !3 *)
mov mem0_450 v_add21_3_1_7;
(*   %arrayidx9.3.2.7 = getelementptr inbounds i16, i16* %r, i64 242 *)
(*   %996 = load i16, i16* %arrayidx9.3.2.7, align 2, !tbaa !3 *)
mov v996 mem0_484;
(*   %conv1.i.3.2.7 = sext i16 %996 to i32 *)
cast v_conv1_i_3_2_7@sint32 v996@sint16;
(*   %mul.i.3.2.7 = mul nsw i32 %conv1.i.3.2.7, 1468 *)
mul v_mul_i_3_2_7 v_conv1_i_3_2_7 (1468)@sint32;
(*   %call.i.3.2.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.2.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_2_7, v_call_i_3_2_7);
(*   %arrayidx11.3.2.7 = getelementptr inbounds i16, i16* %r, i64 226 *)
(*   %997 = load i16, i16* %arrayidx11.3.2.7, align 2, !tbaa !3 *)
mov v997 mem0_452;
(*   %sub.3.2.7 = sub i16 %997, %call.i.3.2.7 *)
sub v_sub_3_2_7 v997 v_call_i_3_2_7;
(*   store i16 %sub.3.2.7, i16* %arrayidx9.3.2.7, align 2, !tbaa !3 *)
mov mem0_484 v_sub_3_2_7;
(*   %add21.3.2.7 = add i16 %997, %call.i.3.2.7 *)
add v_add21_3_2_7 v997 v_call_i_3_2_7;
(*   store i16 %add21.3.2.7, i16* %arrayidx11.3.2.7, align 2, !tbaa !3 *)
mov mem0_452 v_add21_3_2_7;
(*   %arrayidx9.3.3.7 = getelementptr inbounds i16, i16* %r, i64 243 *)
(*   %998 = load i16, i16* %arrayidx9.3.3.7, align 2, !tbaa !3 *)
mov v998 mem0_486;
(*   %conv1.i.3.3.7 = sext i16 %998 to i32 *)
cast v_conv1_i_3_3_7@sint32 v998@sint16;
(*   %mul.i.3.3.7 = mul nsw i32 %conv1.i.3.3.7, 1468 *)
mul v_mul_i_3_3_7 v_conv1_i_3_3_7 (1468)@sint32;
(*   %call.i.3.3.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.3.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_3_7, v_call_i_3_3_7);
(*   %arrayidx11.3.3.7 = getelementptr inbounds i16, i16* %r, i64 227 *)
(*   %999 = load i16, i16* %arrayidx11.3.3.7, align 2, !tbaa !3 *)
mov v999 mem0_454;
(*   %sub.3.3.7 = sub i16 %999, %call.i.3.3.7 *)
sub v_sub_3_3_7 v999 v_call_i_3_3_7;
(*   store i16 %sub.3.3.7, i16* %arrayidx9.3.3.7, align 2, !tbaa !3 *)
mov mem0_486 v_sub_3_3_7;
(*   %add21.3.3.7 = add i16 %999, %call.i.3.3.7 *)
add v_add21_3_3_7 v999 v_call_i_3_3_7;
(*   store i16 %add21.3.3.7, i16* %arrayidx11.3.3.7, align 2, !tbaa !3 *)
mov mem0_454 v_add21_3_3_7;
(*   %arrayidx9.3.4.7 = getelementptr inbounds i16, i16* %r, i64 244 *)
(*   %1000 = load i16, i16* %arrayidx9.3.4.7, align 2, !tbaa !3 *)
mov v1000 mem0_488;
(*   %conv1.i.3.4.7 = sext i16 %1000 to i32 *)
cast v_conv1_i_3_4_7@sint32 v1000@sint16;
(*   %mul.i.3.4.7 = mul nsw i32 %conv1.i.3.4.7, 1468 *)
mul v_mul_i_3_4_7 v_conv1_i_3_4_7 (1468)@sint32;
(*   %call.i.3.4.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.4.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_4_7, v_call_i_3_4_7);
(*   %arrayidx11.3.4.7 = getelementptr inbounds i16, i16* %r, i64 228 *)
(*   %1001 = load i16, i16* %arrayidx11.3.4.7, align 2, !tbaa !3 *)
mov v1001 mem0_456;
(*   %sub.3.4.7 = sub i16 %1001, %call.i.3.4.7 *)
sub v_sub_3_4_7 v1001 v_call_i_3_4_7;
(*   store i16 %sub.3.4.7, i16* %arrayidx9.3.4.7, align 2, !tbaa !3 *)
mov mem0_488 v_sub_3_4_7;
(*   %add21.3.4.7 = add i16 %1001, %call.i.3.4.7 *)
add v_add21_3_4_7 v1001 v_call_i_3_4_7;
(*   store i16 %add21.3.4.7, i16* %arrayidx11.3.4.7, align 2, !tbaa !3 *)
mov mem0_456 v_add21_3_4_7;
(*   %arrayidx9.3.5.7 = getelementptr inbounds i16, i16* %r, i64 245 *)
(*   %1002 = load i16, i16* %arrayidx9.3.5.7, align 2, !tbaa !3 *)
mov v1002 mem0_490;
(*   %conv1.i.3.5.7 = sext i16 %1002 to i32 *)
cast v_conv1_i_3_5_7@sint32 v1002@sint16;
(*   %mul.i.3.5.7 = mul nsw i32 %conv1.i.3.5.7, 1468 *)
mul v_mul_i_3_5_7 v_conv1_i_3_5_7 (1468)@sint32;
(*   %call.i.3.5.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.5.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_5_7, v_call_i_3_5_7);
(*   %arrayidx11.3.5.7 = getelementptr inbounds i16, i16* %r, i64 229 *)
(*   %1003 = load i16, i16* %arrayidx11.3.5.7, align 2, !tbaa !3 *)
mov v1003 mem0_458;
(*   %sub.3.5.7 = sub i16 %1003, %call.i.3.5.7 *)
sub v_sub_3_5_7 v1003 v_call_i_3_5_7;
(*   store i16 %sub.3.5.7, i16* %arrayidx9.3.5.7, align 2, !tbaa !3 *)
mov mem0_490 v_sub_3_5_7;
(*   %add21.3.5.7 = add i16 %1003, %call.i.3.5.7 *)
add v_add21_3_5_7 v1003 v_call_i_3_5_7;
(*   store i16 %add21.3.5.7, i16* %arrayidx11.3.5.7, align 2, !tbaa !3 *)
mov mem0_458 v_add21_3_5_7;
(*   %arrayidx9.3.6.7 = getelementptr inbounds i16, i16* %r, i64 246 *)
(*   %1004 = load i16, i16* %arrayidx9.3.6.7, align 2, !tbaa !3 *)
mov v1004 mem0_492;
(*   %conv1.i.3.6.7 = sext i16 %1004 to i32 *)
cast v_conv1_i_3_6_7@sint32 v1004@sint16;
(*   %mul.i.3.6.7 = mul nsw i32 %conv1.i.3.6.7, 1468 *)
mul v_mul_i_3_6_7 v_conv1_i_3_6_7 (1468)@sint32;
(*   %call.i.3.6.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.6.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_6_7, v_call_i_3_6_7);
(*   %arrayidx11.3.6.7 = getelementptr inbounds i16, i16* %r, i64 230 *)
(*   %1005 = load i16, i16* %arrayidx11.3.6.7, align 2, !tbaa !3 *)
mov v1005 mem0_460;
(*   %sub.3.6.7 = sub i16 %1005, %call.i.3.6.7 *)
sub v_sub_3_6_7 v1005 v_call_i_3_6_7;
(*   store i16 %sub.3.6.7, i16* %arrayidx9.3.6.7, align 2, !tbaa !3 *)
mov mem0_492 v_sub_3_6_7;
(*   %add21.3.6.7 = add i16 %1005, %call.i.3.6.7 *)
add v_add21_3_6_7 v1005 v_call_i_3_6_7;
(*   store i16 %add21.3.6.7, i16* %arrayidx11.3.6.7, align 2, !tbaa !3 *)
mov mem0_460 v_add21_3_6_7;
(*   %arrayidx9.3.7.7 = getelementptr inbounds i16, i16* %r, i64 247 *)
(*   %1006 = load i16, i16* %arrayidx9.3.7.7, align 2, !tbaa !3 *)
mov v1006 mem0_494;
(*   %conv1.i.3.7.7 = sext i16 %1006 to i32 *)
cast v_conv1_i_3_7_7@sint32 v1006@sint16;
(*   %mul.i.3.7.7 = mul nsw i32 %conv1.i.3.7.7, 1468 *)
mul v_mul_i_3_7_7 v_conv1_i_3_7_7 (1468)@sint32;
(*   %call.i.3.7.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.7.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_7_7, v_call_i_3_7_7);
(*   %arrayidx11.3.7.7 = getelementptr inbounds i16, i16* %r, i64 231 *)
(*   %1007 = load i16, i16* %arrayidx11.3.7.7, align 2, !tbaa !3 *)
mov v1007 mem0_462;
(*   %sub.3.7.7 = sub i16 %1007, %call.i.3.7.7 *)
sub v_sub_3_7_7 v1007 v_call_i_3_7_7;
(*   store i16 %sub.3.7.7, i16* %arrayidx9.3.7.7, align 2, !tbaa !3 *)
mov mem0_494 v_sub_3_7_7;
(*   %add21.3.7.7 = add i16 %1007, %call.i.3.7.7 *)
add v_add21_3_7_7 v1007 v_call_i_3_7_7;
(*   store i16 %add21.3.7.7, i16* %arrayidx11.3.7.7, align 2, !tbaa !3 *)
mov mem0_462 v_add21_3_7_7;
(*   %arrayidx9.3.8.7 = getelementptr inbounds i16, i16* %r, i64 248 *)
(*   %1008 = load i16, i16* %arrayidx9.3.8.7, align 2, !tbaa !3 *)
mov v1008 mem0_496;
(*   %conv1.i.3.8.7 = sext i16 %1008 to i32 *)
cast v_conv1_i_3_8_7@sint32 v1008@sint16;
(*   %mul.i.3.8.7 = mul nsw i32 %conv1.i.3.8.7, 1468 *)
mul v_mul_i_3_8_7 v_conv1_i_3_8_7 (1468)@sint32;
(*   %call.i.3.8.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.8.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_8_7, v_call_i_3_8_7);
(*   %arrayidx11.3.8.7 = getelementptr inbounds i16, i16* %r, i64 232 *)
(*   %1009 = load i16, i16* %arrayidx11.3.8.7, align 2, !tbaa !3 *)
mov v1009 mem0_464;
(*   %sub.3.8.7 = sub i16 %1009, %call.i.3.8.7 *)
sub v_sub_3_8_7 v1009 v_call_i_3_8_7;
(*   store i16 %sub.3.8.7, i16* %arrayidx9.3.8.7, align 2, !tbaa !3 *)
mov mem0_496 v_sub_3_8_7;
(*   %add21.3.8.7 = add i16 %1009, %call.i.3.8.7 *)
add v_add21_3_8_7 v1009 v_call_i_3_8_7;
(*   store i16 %add21.3.8.7, i16* %arrayidx11.3.8.7, align 2, !tbaa !3 *)
mov mem0_464 v_add21_3_8_7;
(*   %arrayidx9.3.9.7 = getelementptr inbounds i16, i16* %r, i64 249 *)
(*   %1010 = load i16, i16* %arrayidx9.3.9.7, align 2, !tbaa !3 *)
mov v1010 mem0_498;
(*   %conv1.i.3.9.7 = sext i16 %1010 to i32 *)
cast v_conv1_i_3_9_7@sint32 v1010@sint16;
(*   %mul.i.3.9.7 = mul nsw i32 %conv1.i.3.9.7, 1468 *)
mul v_mul_i_3_9_7 v_conv1_i_3_9_7 (1468)@sint32;
(*   %call.i.3.9.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.9.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_9_7, v_call_i_3_9_7);
(*   %arrayidx11.3.9.7 = getelementptr inbounds i16, i16* %r, i64 233 *)
(*   %1011 = load i16, i16* %arrayidx11.3.9.7, align 2, !tbaa !3 *)
mov v1011 mem0_466;
(*   %sub.3.9.7 = sub i16 %1011, %call.i.3.9.7 *)
sub v_sub_3_9_7 v1011 v_call_i_3_9_7;
(*   store i16 %sub.3.9.7, i16* %arrayidx9.3.9.7, align 2, !tbaa !3 *)
mov mem0_498 v_sub_3_9_7;
(*   %add21.3.9.7 = add i16 %1011, %call.i.3.9.7 *)
add v_add21_3_9_7 v1011 v_call_i_3_9_7;
(*   store i16 %add21.3.9.7, i16* %arrayidx11.3.9.7, align 2, !tbaa !3 *)
mov mem0_466 v_add21_3_9_7;
(*   %arrayidx9.3.10.7 = getelementptr inbounds i16, i16* %r, i64 250 *)
(*   %1012 = load i16, i16* %arrayidx9.3.10.7, align 2, !tbaa !3 *)
mov v1012 mem0_500;
(*   %conv1.i.3.10.7 = sext i16 %1012 to i32 *)
cast v_conv1_i_3_10_7@sint32 v1012@sint16;
(*   %mul.i.3.10.7 = mul nsw i32 %conv1.i.3.10.7, 1468 *)
mul v_mul_i_3_10_7 v_conv1_i_3_10_7 (1468)@sint32;
(*   %call.i.3.10.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.10.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_10_7, v_call_i_3_10_7);
(*   %arrayidx11.3.10.7 = getelementptr inbounds i16, i16* %r, i64 234 *)
(*   %1013 = load i16, i16* %arrayidx11.3.10.7, align 2, !tbaa !3 *)
mov v1013 mem0_468;
(*   %sub.3.10.7 = sub i16 %1013, %call.i.3.10.7 *)
sub v_sub_3_10_7 v1013 v_call_i_3_10_7;
(*   store i16 %sub.3.10.7, i16* %arrayidx9.3.10.7, align 2, !tbaa !3 *)
mov mem0_500 v_sub_3_10_7;
(*   %add21.3.10.7 = add i16 %1013, %call.i.3.10.7 *)
add v_add21_3_10_7 v1013 v_call_i_3_10_7;
(*   store i16 %add21.3.10.7, i16* %arrayidx11.3.10.7, align 2, !tbaa !3 *)
mov mem0_468 v_add21_3_10_7;
(*   %arrayidx9.3.11.7 = getelementptr inbounds i16, i16* %r, i64 251 *)
(*   %1014 = load i16, i16* %arrayidx9.3.11.7, align 2, !tbaa !3 *)
mov v1014 mem0_502;
(*   %conv1.i.3.11.7 = sext i16 %1014 to i32 *)
cast v_conv1_i_3_11_7@sint32 v1014@sint16;
(*   %mul.i.3.11.7 = mul nsw i32 %conv1.i.3.11.7, 1468 *)
mul v_mul_i_3_11_7 v_conv1_i_3_11_7 (1468)@sint32;
(*   %call.i.3.11.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.11.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_11_7, v_call_i_3_11_7);
(*   %arrayidx11.3.11.7 = getelementptr inbounds i16, i16* %r, i64 235 *)
(*   %1015 = load i16, i16* %arrayidx11.3.11.7, align 2, !tbaa !3 *)
mov v1015 mem0_470;
(*   %sub.3.11.7 = sub i16 %1015, %call.i.3.11.7 *)
sub v_sub_3_11_7 v1015 v_call_i_3_11_7;
(*   store i16 %sub.3.11.7, i16* %arrayidx9.3.11.7, align 2, !tbaa !3 *)
mov mem0_502 v_sub_3_11_7;
(*   %add21.3.11.7 = add i16 %1015, %call.i.3.11.7 *)
add v_add21_3_11_7 v1015 v_call_i_3_11_7;
(*   store i16 %add21.3.11.7, i16* %arrayidx11.3.11.7, align 2, !tbaa !3 *)
mov mem0_470 v_add21_3_11_7;
(*   %arrayidx9.3.12.7 = getelementptr inbounds i16, i16* %r, i64 252 *)
(*   %1016 = load i16, i16* %arrayidx9.3.12.7, align 2, !tbaa !3 *)
mov v1016 mem0_504;
(*   %conv1.i.3.12.7 = sext i16 %1016 to i32 *)
cast v_conv1_i_3_12_7@sint32 v1016@sint16;
(*   %mul.i.3.12.7 = mul nsw i32 %conv1.i.3.12.7, 1468 *)
mul v_mul_i_3_12_7 v_conv1_i_3_12_7 (1468)@sint32;
(*   %call.i.3.12.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.12.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_12_7, v_call_i_3_12_7);
(*   %arrayidx11.3.12.7 = getelementptr inbounds i16, i16* %r, i64 236 *)
(*   %1017 = load i16, i16* %arrayidx11.3.12.7, align 2, !tbaa !3 *)
mov v1017 mem0_472;
(*   %sub.3.12.7 = sub i16 %1017, %call.i.3.12.7 *)
sub v_sub_3_12_7 v1017 v_call_i_3_12_7;
(*   store i16 %sub.3.12.7, i16* %arrayidx9.3.12.7, align 2, !tbaa !3 *)
mov mem0_504 v_sub_3_12_7;
(*   %add21.3.12.7 = add i16 %1017, %call.i.3.12.7 *)
add v_add21_3_12_7 v1017 v_call_i_3_12_7;
(*   store i16 %add21.3.12.7, i16* %arrayidx11.3.12.7, align 2, !tbaa !3 *)
mov mem0_472 v_add21_3_12_7;
(*   %arrayidx9.3.13.7 = getelementptr inbounds i16, i16* %r, i64 253 *)
(*   %1018 = load i16, i16* %arrayidx9.3.13.7, align 2, !tbaa !3 *)
mov v1018 mem0_506;
(*   %conv1.i.3.13.7 = sext i16 %1018 to i32 *)
cast v_conv1_i_3_13_7@sint32 v1018@sint16;
(*   %mul.i.3.13.7 = mul nsw i32 %conv1.i.3.13.7, 1468 *)
mul v_mul_i_3_13_7 v_conv1_i_3_13_7 (1468)@sint32;
(*   %call.i.3.13.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.13.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_13_7, v_call_i_3_13_7);
(*   %arrayidx11.3.13.7 = getelementptr inbounds i16, i16* %r, i64 237 *)
(*   %1019 = load i16, i16* %arrayidx11.3.13.7, align 2, !tbaa !3 *)
mov v1019 mem0_474;
(*   %sub.3.13.7 = sub i16 %1019, %call.i.3.13.7 *)
sub v_sub_3_13_7 v1019 v_call_i_3_13_7;
(*   store i16 %sub.3.13.7, i16* %arrayidx9.3.13.7, align 2, !tbaa !3 *)
mov mem0_506 v_sub_3_13_7;
(*   %add21.3.13.7 = add i16 %1019, %call.i.3.13.7 *)
add v_add21_3_13_7 v1019 v_call_i_3_13_7;
(*   store i16 %add21.3.13.7, i16* %arrayidx11.3.13.7, align 2, !tbaa !3 *)
mov mem0_474 v_add21_3_13_7;
(*   %arrayidx9.3.14.7 = getelementptr inbounds i16, i16* %r, i64 254 *)
(*   %1020 = load i16, i16* %arrayidx9.3.14.7, align 2, !tbaa !3 *)
mov v1020 mem0_508;
(*   %conv1.i.3.14.7 = sext i16 %1020 to i32 *)
cast v_conv1_i_3_14_7@sint32 v1020@sint16;
(*   %mul.i.3.14.7 = mul nsw i32 %conv1.i.3.14.7, 1468 *)
mul v_mul_i_3_14_7 v_conv1_i_3_14_7 (1468)@sint32;
(*   %call.i.3.14.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.14.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_14_7, v_call_i_3_14_7);
(*   %arrayidx11.3.14.7 = getelementptr inbounds i16, i16* %r, i64 238 *)
(*   %1021 = load i16, i16* %arrayidx11.3.14.7, align 2, !tbaa !3 *)
mov v1021 mem0_476;
(*   %sub.3.14.7 = sub i16 %1021, %call.i.3.14.7 *)
sub v_sub_3_14_7 v1021 v_call_i_3_14_7;
(*   store i16 %sub.3.14.7, i16* %arrayidx9.3.14.7, align 2, !tbaa !3 *)
mov mem0_508 v_sub_3_14_7;
(*   %add21.3.14.7 = add i16 %1021, %call.i.3.14.7 *)
add v_add21_3_14_7 v1021 v_call_i_3_14_7;
(*   store i16 %add21.3.14.7, i16* %arrayidx11.3.14.7, align 2, !tbaa !3 *)
mov mem0_476 v_add21_3_14_7;
(*   %arrayidx9.3.15.7 = getelementptr inbounds i16, i16* %r, i64 255 *)
(*   %1022 = load i16, i16* %arrayidx9.3.15.7, align 2, !tbaa !3 *)
mov v1022 mem0_510;
(*   %conv1.i.3.15.7 = sext i16 %1022 to i32 *)
cast v_conv1_i_3_15_7@sint32 v1022@sint16;
(*   %mul.i.3.15.7 = mul nsw i32 %conv1.i.3.15.7, 1468 *)
mul v_mul_i_3_15_7 v_conv1_i_3_15_7 (1468)@sint32;
(*   %call.i.3.15.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3.15.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3_15_7, v_call_i_3_15_7);
(*   %arrayidx11.3.15.7 = getelementptr inbounds i16, i16* %r, i64 239 *)
(*   %1023 = load i16, i16* %arrayidx11.3.15.7, align 2, !tbaa !3 *)
mov v1023 mem0_478;
(*   %sub.3.15.7 = sub i16 %1023, %call.i.3.15.7 *)
sub v_sub_3_15_7 v1023 v_call_i_3_15_7;
(*   store i16 %sub.3.15.7, i16* %arrayidx9.3.15.7, align 2, !tbaa !3 *)
mov mem0_510 v_sub_3_15_7;
(*   %add21.3.15.7 = add i16 %1023, %call.i.3.15.7 *)
add v_add21_3_15_7 v1023 v_call_i_3_15_7;
(*   store i16 %add21.3.15.7, i16* %arrayidx11.3.15.7, align 2, !tbaa !3 *)
mov mem0_478 v_add21_3_15_7;

{
and [

eqmod
(
mem0_0_k7*(x**0) + mem0_2_k7*(x**1) + mem0_4_k7*(x**2) + mem0_6_k7*(x**3) + 
mem0_8_k7*(x**4) + mem0_10_k7*(x**5) + mem0_12_k7*(x**6) + mem0_14_k7*(x**7) + 
mem0_16_k7*(x**8) + mem0_18_k7*(x**9) + mem0_20_k7*(x**10) + mem0_22_k7*(x**11) + 
mem0_24_k7*(x**12) + mem0_26_k7*(x**13) + mem0_28_k7*(x**14) + mem0_30_k7*(x**15) + 
mem0_32_k7*(x**16) + mem0_34_k7*(x**17) + mem0_36_k7*(x**18) + mem0_38_k7*(x**19) + 
mem0_40_k7*(x**20) + mem0_42_k7*(x**21) + mem0_44_k7*(x**22) + mem0_46_k7*(x**23) + 
mem0_48_k7*(x**24) + mem0_50_k7*(x**25) + mem0_52_k7*(x**26) + mem0_54_k7*(x**27) + 
mem0_56_k7*(x**28) + mem0_58_k7*(x**29) + mem0_60_k7*(x**30) + mem0_62_k7*(x**31)
)
(
mem0_0*(x**0) + mem0_2*(x**1) + mem0_4*(x**2) + mem0_6*(x**3) + 
mem0_8*(x**4) + mem0_10*(x**5) + mem0_12*(x**6) + mem0_14*(x**7) + 
mem0_16*(x**8) + mem0_18*(x**9) + mem0_20*(x**10) + mem0_22*(x**11) + 
mem0_24*(x**12) + mem0_26*(x**13) + mem0_28*(x**14) + mem0_30*(x**15)
)
[3329, x**16 - 1062],
eqmod 
(
mem0_0_k7*(x**0) + mem0_2_k7*(x**1) + mem0_4_k7*(x**2) + mem0_6_k7*(x**3) + 
mem0_8_k7*(x**4) + mem0_10_k7*(x**5) + mem0_12_k7*(x**6) + mem0_14_k7*(x**7) + 
mem0_16_k7*(x**8) + mem0_18_k7*(x**9) + mem0_20_k7*(x**10) + mem0_22_k7*(x**11) + 
mem0_24_k7*(x**12) + mem0_26_k7*(x**13) + mem0_28_k7*(x**14) + mem0_30_k7*(x**15) + 
mem0_32_k7*(x**16) + mem0_34_k7*(x**17) + mem0_36_k7*(x**18) + mem0_38_k7*(x**19) + 
mem0_40_k7*(x**20) + mem0_42_k7*(x**21) + mem0_44_k7*(x**22) + mem0_46_k7*(x**23) + 
mem0_48_k7*(x**24) + mem0_50_k7*(x**25) + mem0_52_k7*(x**26) + mem0_54_k7*(x**27) + 
mem0_56_k7*(x**28) + mem0_58_k7*(x**29) + mem0_60_k7*(x**30) + mem0_62_k7*(x**31)
)
(
mem0_32*(x**0) + mem0_34*(x**1) + mem0_36*(x**2) + mem0_38*(x**3) + 
mem0_40*(x**4) + mem0_42*(x**5) + mem0_44*(x**6) + mem0_46*(x**7) + 
mem0_48*(x**8) + mem0_50*(x**9) + mem0_52*(x**10) + mem0_54*(x**11) + 
mem0_56*(x**12) + mem0_58*(x**13) + mem0_60*(x**14) + mem0_62*(x**15)
)
[3329, x**16 - 2267],
eqmod 
(
mem0_64_k7*(x**0) + mem0_66_k7*(x**1) + mem0_68_k7*(x**2) + mem0_70_k7*(x**3) + 
mem0_72_k7*(x**4) + mem0_74_k7*(x**5) + mem0_76_k7*(x**6) + mem0_78_k7*(x**7) + 
mem0_80_k7*(x**8) + mem0_82_k7*(x**9) + mem0_84_k7*(x**10) + mem0_86_k7*(x**11) + 
mem0_88_k7*(x**12) + mem0_90_k7*(x**13) + mem0_92_k7*(x**14) + mem0_94_k7*(x**15) + 
mem0_96_k7*(x**16) + mem0_98_k7*(x**17) + mem0_100_k7*(x**18) + mem0_102_k7*(x**19) + 
mem0_104_k7*(x**20) + mem0_106_k7*(x**21) + mem0_108_k7*(x**22) + mem0_110_k7*(x**23) + 
mem0_112_k7*(x**24) + mem0_114_k7*(x**25) + mem0_116_k7*(x**26) + mem0_118_k7*(x**27) + 
mem0_120_k7*(x**28) + mem0_122_k7*(x**29) + mem0_124_k7*(x**30) + mem0_126_k7*(x**31)
)
(
mem0_64*(x**0) + mem0_66*(x**1) + mem0_68*(x**2) + mem0_70*(x**3) + 
mem0_72*(x**4) + mem0_74*(x**5) + mem0_76*(x**6) + mem0_78*(x**7) + 
mem0_80*(x**8) + mem0_82*(x**9) + mem0_84*(x**10) + mem0_86*(x**11) + 
mem0_88*(x**12) + mem0_90*(x**13) + mem0_92*(x**14) + mem0_94*(x**15)
)
[3329, x**16 - 1919],
eqmod 
(
mem0_64_k7*(x**0) + mem0_66_k7*(x**1) + mem0_68_k7*(x**2) + mem0_70_k7*(x**3) + 
mem0_72_k7*(x**4) + mem0_74_k7*(x**5) + mem0_76_k7*(x**6) + mem0_78_k7*(x**7) + 
mem0_80_k7*(x**8) + mem0_82_k7*(x**9) + mem0_84_k7*(x**10) + mem0_86_k7*(x**11) + 
mem0_88_k7*(x**12) + mem0_90_k7*(x**13) + mem0_92_k7*(x**14) + mem0_94_k7*(x**15) + 
mem0_96_k7*(x**16) + mem0_98_k7*(x**17) + mem0_100_k7*(x**18) + mem0_102_k7*(x**19) + 
mem0_104_k7*(x**20) + mem0_106_k7*(x**21) + mem0_108_k7*(x**22) + mem0_110_k7*(x**23) + 
mem0_112_k7*(x**24) + mem0_114_k7*(x**25) + mem0_116_k7*(x**26) + mem0_118_k7*(x**27) + 
mem0_120_k7*(x**28) + mem0_122_k7*(x**29) + mem0_124_k7*(x**30) + mem0_126_k7*(x**31)
)
(
mem0_96*(x**0) + mem0_98*(x**1) + mem0_100*(x**2) + mem0_102*(x**3) + 
mem0_104*(x**4) + mem0_106*(x**5) + mem0_108*(x**6) + mem0_110*(x**7) + 
mem0_112*(x**8) + mem0_114*(x**9) + mem0_116*(x**10) + mem0_118*(x**11) + 
mem0_120*(x**12) + mem0_122*(x**13) + mem0_124*(x**14) + mem0_126*(x**15)
)
[3329, x**16 - 1410],
eqmod 
(
mem0_128_k7*(x**0) + mem0_130_k7*(x**1) + mem0_132_k7*(x**2) + mem0_134_k7*(x**3) + 
mem0_136_k7*(x**4) + mem0_138_k7*(x**5) + mem0_140_k7*(x**6) + mem0_142_k7*(x**7) + 
mem0_144_k7*(x**8) + mem0_146_k7*(x**9) + mem0_148_k7*(x**10) + mem0_150_k7*(x**11) + 
mem0_152_k7*(x**12) + mem0_154_k7*(x**13) + mem0_156_k7*(x**14) + mem0_158_k7*(x**15) + 
mem0_160_k7*(x**16) + mem0_162_k7*(x**17) + mem0_164_k7*(x**18) + mem0_166_k7*(x**19) + 
mem0_168_k7*(x**20) + mem0_170_k7*(x**21) + mem0_172_k7*(x**22) + mem0_174_k7*(x**23) + 
mem0_176_k7*(x**24) + mem0_178_k7*(x**25) + mem0_180_k7*(x**26) + mem0_182_k7*(x**27) + 
mem0_184_k7*(x**28) + mem0_186_k7*(x**29) + mem0_188_k7*(x**30) + mem0_190_k7*(x**31)
)
(
mem0_128*(x**0) + mem0_130*(x**1) + mem0_132*(x**2) + mem0_134*(x**3) + 
mem0_136*(x**4) + mem0_138*(x**5) + mem0_140*(x**6) + mem0_142*(x**7) + 
mem0_144*(x**8) + mem0_146*(x**9) + mem0_148*(x**10) + mem0_150*(x**11) + 
mem0_152*(x**12) + mem0_154*(x**13) + mem0_156*(x**14) + mem0_158*(x**15)
)
[3329, x**16 - 193],
eqmod 
(
mem0_128_k7*(x**0) + mem0_130_k7*(x**1) + mem0_132_k7*(x**2) + mem0_134_k7*(x**3) + 
mem0_136_k7*(x**4) + mem0_138_k7*(x**5) + mem0_140_k7*(x**6) + mem0_142_k7*(x**7) + 
mem0_144_k7*(x**8) + mem0_146_k7*(x**9) + mem0_148_k7*(x**10) + mem0_150_k7*(x**11) + 
mem0_152_k7*(x**12) + mem0_154_k7*(x**13) + mem0_156_k7*(x**14) + mem0_158_k7*(x**15) + 
mem0_160_k7*(x**16) + mem0_162_k7*(x**17) + mem0_164_k7*(x**18) + mem0_166_k7*(x**19) + 
mem0_168_k7*(x**20) + mem0_170_k7*(x**21) + mem0_172_k7*(x**22) + mem0_174_k7*(x**23) + 
mem0_176_k7*(x**24) + mem0_178_k7*(x**25) + mem0_180_k7*(x**26) + mem0_182_k7*(x**27) + 
mem0_184_k7*(x**28) + mem0_186_k7*(x**29) + mem0_188_k7*(x**30) + mem0_190_k7*(x**31)
)
(
mem0_160*(x**0) + mem0_162*(x**1) + mem0_164*(x**2) + mem0_166*(x**3) + 
mem0_168*(x**4) + mem0_170*(x**5) + mem0_172*(x**6) + mem0_174*(x**7) + 
mem0_176*(x**8) + mem0_178*(x**9) + mem0_180*(x**10) + mem0_182*(x**11) + 
mem0_184*(x**12) + mem0_186*(x**13) + mem0_188*(x**14) + mem0_190*(x**15)
)
[3329, x**16 - 3136],
eqmod 
(
mem0_192_k7*(x**0) + mem0_194_k7*(x**1) + mem0_196_k7*(x**2) + mem0_198_k7*(x**3) + 
mem0_200_k7*(x**4) + mem0_202_k7*(x**5) + mem0_204_k7*(x**6) + mem0_206_k7*(x**7) + 
mem0_208_k7*(x**8) + mem0_210_k7*(x**9) + mem0_212_k7*(x**10) + mem0_214_k7*(x**11) + 
mem0_216_k7*(x**12) + mem0_218_k7*(x**13) + mem0_220_k7*(x**14) + mem0_222_k7*(x**15) + 
mem0_224_k7*(x**16) + mem0_226_k7*(x**17) + mem0_228_k7*(x**18) + mem0_230_k7*(x**19) + 
mem0_232_k7*(x**20) + mem0_234_k7*(x**21) + mem0_236_k7*(x**22) + mem0_238_k7*(x**23) + 
mem0_240_k7*(x**24) + mem0_242_k7*(x**25) + mem0_244_k7*(x**26) + mem0_246_k7*(x**27) + 
mem0_248_k7*(x**28) + mem0_250_k7*(x**29) + mem0_252_k7*(x**30) + mem0_254_k7*(x**31)
)
(
mem0_192*(x**0) + mem0_194*(x**1) + mem0_196*(x**2) + mem0_198*(x**3) + 
mem0_200*(x**4) + mem0_202*(x**5) + mem0_204*(x**6) + mem0_206*(x**7) + 
mem0_208*(x**8) + mem0_210*(x**9) + mem0_212*(x**10) + mem0_214*(x**11) + 
mem0_216*(x**12) + mem0_218*(x**13) + mem0_220*(x**14) + mem0_222*(x**15)
)
[3329, x**16 - 797],
eqmod 
(
mem0_192_k7*(x**0) + mem0_194_k7*(x**1) + mem0_196_k7*(x**2) + mem0_198_k7*(x**3) + 
mem0_200_k7*(x**4) + mem0_202_k7*(x**5) + mem0_204_k7*(x**6) + mem0_206_k7*(x**7) + 
mem0_208_k7*(x**8) + mem0_210_k7*(x**9) + mem0_212_k7*(x**10) + mem0_214_k7*(x**11) + 
mem0_216_k7*(x**12) + mem0_218_k7*(x**13) + mem0_220_k7*(x**14) + mem0_222_k7*(x**15) + 
mem0_224_k7*(x**16) + mem0_226_k7*(x**17) + mem0_228_k7*(x**18) + mem0_230_k7*(x**19) + 
mem0_232_k7*(x**20) + mem0_234_k7*(x**21) + mem0_236_k7*(x**22) + mem0_238_k7*(x**23) + 
mem0_240_k7*(x**24) + mem0_242_k7*(x**25) + mem0_244_k7*(x**26) + mem0_246_k7*(x**27) + 
mem0_248_k7*(x**28) + mem0_250_k7*(x**29) + mem0_252_k7*(x**30) + mem0_254_k7*(x**31)
) 
(
mem0_224*(x**0) + mem0_226*(x**1) + mem0_228*(x**2) + mem0_230*(x**3) + 
mem0_232*(x**4) + mem0_234*(x**5) + mem0_236*(x**6) + mem0_238*(x**7) + 
mem0_240*(x**8) + mem0_242*(x**9) + mem0_244*(x**10) + mem0_246*(x**11) + 
mem0_248*(x**12) + mem0_250*(x**13) + mem0_252*(x**14) + mem0_254*(x**15)
)
[3329, x**16 - 2532],
eqmod 
(
mem0_256_k7*(x**0) + mem0_258_k7*(x**1) + mem0_260_k7*(x**2) + mem0_262_k7*(x**3) + 
mem0_264_k7*(x**4) + mem0_266_k7*(x**5) + mem0_268_k7*(x**6) + mem0_270_k7*(x**7) + 
mem0_272_k7*(x**8) + mem0_274_k7*(x**9) + mem0_276_k7*(x**10) + mem0_278_k7*(x**11) + 
mem0_280_k7*(x**12) + mem0_282_k7*(x**13) + mem0_284_k7*(x**14) + mem0_286_k7*(x**15) + 
mem0_288_k7*(x**16) + mem0_290_k7*(x**17) + mem0_292_k7*(x**18) + mem0_294_k7*(x**19) + 
mem0_296_k7*(x**20) + mem0_298_k7*(x**21) + mem0_300_k7*(x**22) + mem0_302_k7*(x**23) + 
mem0_304_k7*(x**24) + mem0_306_k7*(x**25) + mem0_308_k7*(x**26) + mem0_310_k7*(x**27) + 
mem0_312_k7*(x**28) + mem0_314_k7*(x**29) + mem0_316_k7*(x**30) + mem0_318_k7*(x**31)
)
(
mem0_256*(x**0) + mem0_258*(x**1) + mem0_260*(x**2) + mem0_262*(x**3) + 
mem0_264*(x**4) + mem0_266*(x**5) + mem0_268*(x**6) + mem0_270*(x**7) + 
mem0_272*(x**8) + mem0_274*(x**9) + mem0_276*(x**10) + mem0_278*(x**11) + 
mem0_280*(x**12) + mem0_282*(x**13) + mem0_284*(x**14) + mem0_286*(x**15)
)
[3329, x**16 - 2786],
eqmod 
(
mem0_256_k7*(x**0) + mem0_258_k7*(x**1) + mem0_260_k7*(x**2) + mem0_262_k7*(x**3) + 
mem0_264_k7*(x**4) + mem0_266_k7*(x**5) + mem0_268_k7*(x**6) + mem0_270_k7*(x**7) + 
mem0_272_k7*(x**8) + mem0_274_k7*(x**9) + mem0_276_k7*(x**10) + mem0_278_k7*(x**11) + 
mem0_280_k7*(x**12) + mem0_282_k7*(x**13) + mem0_284_k7*(x**14) + mem0_286_k7*(x**15) + 
mem0_288_k7*(x**16) + mem0_290_k7*(x**17) + mem0_292_k7*(x**18) + mem0_294_k7*(x**19) + 
mem0_296_k7*(x**20) + mem0_298_k7*(x**21) + mem0_300_k7*(x**22) + mem0_302_k7*(x**23) + 
mem0_304_k7*(x**24) + mem0_306_k7*(x**25) + mem0_308_k7*(x**26) + mem0_310_k7*(x**27) + 
mem0_312_k7*(x**28) + mem0_314_k7*(x**29) + mem0_316_k7*(x**30) + mem0_318_k7*(x**31)
)
(
mem0_288*(x**0) + mem0_290*(x**1) + mem0_292*(x**2) + mem0_294*(x**3) + 
mem0_296*(x**4) + mem0_298*(x**5) + mem0_300*(x**6) + mem0_302*(x**7) + 
mem0_304*(x**8) + mem0_306*(x**9) + mem0_308*(x**10) + mem0_310*(x**11) + 
mem0_312*(x**12) + mem0_314*(x**13) + mem0_316*(x**14) + mem0_318*(x**15)
)
[3329, x**16 - 543],
eqmod 
(
mem0_320_k7*(x**0) + mem0_322_k7*(x**1) + mem0_324_k7*(x**2) + mem0_326_k7*(x**3) + 
mem0_328_k7*(x**4) + mem0_330_k7*(x**5) + mem0_332_k7*(x**6) + mem0_334_k7*(x**7) + 
mem0_336_k7*(x**8) + mem0_338_k7*(x**9) + mem0_340_k7*(x**10) + mem0_342_k7*(x**11) + 
mem0_344_k7*(x**12) + mem0_346_k7*(x**13) + mem0_348_k7*(x**14) + mem0_350_k7*(x**15) + 
mem0_352_k7*(x**16) + mem0_354_k7*(x**17) + mem0_356_k7*(x**18) + mem0_358_k7*(x**19) + 
mem0_360_k7*(x**20) + mem0_362_k7*(x**21) + mem0_364_k7*(x**22) + mem0_366_k7*(x**23) + 
mem0_368_k7*(x**24) + mem0_370_k7*(x**25) + mem0_372_k7*(x**26) + mem0_374_k7*(x**27) + 
mem0_376_k7*(x**28) + mem0_378_k7*(x**29) + mem0_380_k7*(x**30) + mem0_382_k7*(x**31)
)
(
mem0_320*(x**0) + mem0_322*(x**1) + mem0_324*(x**2) + mem0_326*(x**3) + 
mem0_328*(x**4) + mem0_330*(x**5) + mem0_332*(x**6) + mem0_334*(x**7) + 
mem0_336*(x**8) + mem0_338*(x**9) + mem0_340*(x**10) + mem0_342*(x**11) + 
mem0_344*(x**12) + mem0_346*(x**13) + mem0_348*(x**14) + mem0_350*(x**15)
)
[3329, x**16 - 3260],
eqmod 
(
mem0_320_k7*(x**0) + mem0_322_k7*(x**1) + mem0_324_k7*(x**2) + mem0_326_k7*(x**3) + 
mem0_328_k7*(x**4) + mem0_330_k7*(x**5) + mem0_332_k7*(x**6) + mem0_334_k7*(x**7) + 
mem0_336_k7*(x**8) + mem0_338_k7*(x**9) + mem0_340_k7*(x**10) + mem0_342_k7*(x**11) + 
mem0_344_k7*(x**12) + mem0_346_k7*(x**13) + mem0_348_k7*(x**14) + mem0_350_k7*(x**15) + 
mem0_352_k7*(x**16) + mem0_354_k7*(x**17) + mem0_356_k7*(x**18) + mem0_358_k7*(x**19) + 
mem0_360_k7*(x**20) + mem0_362_k7*(x**21) + mem0_364_k7*(x**22) + mem0_366_k7*(x**23) + 
mem0_368_k7*(x**24) + mem0_370_k7*(x**25) + mem0_372_k7*(x**26) + mem0_374_k7*(x**27) + 
mem0_376_k7*(x**28) + mem0_378_k7*(x**29) + mem0_380_k7*(x**30) + mem0_382_k7*(x**31)
)
(
mem0_352*(x**0) + mem0_354*(x**1) + mem0_356*(x**2) + mem0_358*(x**3) + 
mem0_360*(x**4) + mem0_362*(x**5) + mem0_364*(x**6) + mem0_366*(x**7) + 
mem0_368*(x**8) + mem0_370*(x**9) + mem0_372*(x**10) + mem0_374*(x**11) + 
mem0_376*(x**12) + mem0_378*(x**13) + mem0_380*(x**14) + mem0_382*(x**15)
)
[3329, x**16 - 69],
eqmod 
(
mem0_384_k7*(x**0) + mem0_386_k7*(x**1) + mem0_388_k7*(x**2) + mem0_390_k7*(x**3) + 
mem0_392_k7*(x**4) + mem0_394_k7*(x**5) + mem0_396_k7*(x**6) + mem0_398_k7*(x**7) + 
mem0_400_k7*(x**8) + mem0_402_k7*(x**9) + mem0_404_k7*(x**10) + mem0_406_k7*(x**11) + 
mem0_408_k7*(x**12) + mem0_410_k7*(x**13) + mem0_412_k7*(x**14) + mem0_414_k7*(x**15) + 
mem0_416_k7*(x**16) + mem0_418_k7*(x**17) + mem0_420_k7*(x**18) + mem0_422_k7*(x**19) + 
mem0_424_k7*(x**20) + mem0_426_k7*(x**21) + mem0_428_k7*(x**22) + mem0_430_k7*(x**23) + 
mem0_432_k7*(x**24) + mem0_434_k7*(x**25) + mem0_436_k7*(x**26) + mem0_438_k7*(x**27) + 
mem0_440_k7*(x**28) + mem0_442_k7*(x**29) + mem0_444_k7*(x**30) + mem0_446_k7*(x**31)
)
(
mem0_384*(x**0) + mem0_386*(x**1) + mem0_388*(x**2) + mem0_390*(x**3) + 
mem0_392*(x**4) + mem0_394*(x**5) + mem0_396*(x**6) + mem0_398*(x**7) + 
mem0_400*(x**8) + mem0_402*(x**9) + mem0_404*(x**10) + mem0_406*(x**11) + 
mem0_408*(x**12) + mem0_410*(x**13) + mem0_412*(x**14) + mem0_414*(x**15)
)
[3329, x**16 - 569],
eqmod 
(
mem0_384_k7*(x**0) + mem0_386_k7*(x**1) + mem0_388_k7*(x**2) + mem0_390_k7*(x**3) + 
mem0_392_k7*(x**4) + mem0_394_k7*(x**5) + mem0_396_k7*(x**6) + mem0_398_k7*(x**7) + 
mem0_400_k7*(x**8) + mem0_402_k7*(x**9) + mem0_404_k7*(x**10) + mem0_406_k7*(x**11) + 
mem0_408_k7*(x**12) + mem0_410_k7*(x**13) + mem0_412_k7*(x**14) + mem0_414_k7*(x**15) + 
mem0_416_k7*(x**16) + mem0_418_k7*(x**17) + mem0_420_k7*(x**18) + mem0_422_k7*(x**19) + 
mem0_424_k7*(x**20) + mem0_426_k7*(x**21) + mem0_428_k7*(x**22) + mem0_430_k7*(x**23) + 
mem0_432_k7*(x**24) + mem0_434_k7*(x**25) + mem0_436_k7*(x**26) + mem0_438_k7*(x**27) + 
mem0_440_k7*(x**28) + mem0_442_k7*(x**29) + mem0_444_k7*(x**30) + mem0_446_k7*(x**31)
)
(
mem0_416*(x**0) + mem0_418*(x**1) + mem0_420*(x**2) + mem0_422*(x**3) + 
mem0_424*(x**4) + mem0_426*(x**5) + mem0_428*(x**6) + mem0_430*(x**7) + 
mem0_432*(x**8) + mem0_434*(x**9) + mem0_436*(x**10) + mem0_438*(x**11) + 
mem0_440*(x**12) + mem0_442*(x**13) + mem0_444*(x**14) + mem0_446*(x**15)
)
[3329, x**16 - 2760],
eqmod 
(
mem0_448_k7*(x**0) + mem0_450_k7*(x**1) + mem0_452_k7*(x**2) + mem0_454_k7*(x**3) + 
mem0_456_k7*(x**4) + mem0_458_k7*(x**5) + mem0_460_k7*(x**6) + mem0_462_k7*(x**7) + 
mem0_464_k7*(x**8) + mem0_466_k7*(x**9) + mem0_468_k7*(x**10) + mem0_470_k7*(x**11) + 
mem0_472_k7*(x**12) + mem0_474_k7*(x**13) + mem0_476_k7*(x**14) + mem0_478_k7*(x**15) + 
mem0_480_k7*(x**16) + mem0_482_k7*(x**17) + mem0_484_k7*(x**18) + mem0_486_k7*(x**19) + 
mem0_488_k7*(x**20) + mem0_490_k7*(x**21) + mem0_492_k7*(x**22) + mem0_494_k7*(x**23) + 
mem0_496_k7*(x**24) + mem0_498_k7*(x**25) + mem0_500_k7*(x**26) + mem0_502_k7*(x**27) + 
mem0_504_k7*(x**28) + mem0_506_k7*(x**29) + mem0_508_k7*(x**30) + mem0_510_k7*(x**31)
)
(
mem0_448*(x**0) + mem0_450*(x**1) + mem0_452*(x**2) + mem0_454*(x**3) + 
mem0_456*(x**4) + mem0_458*(x**5) + mem0_460*(x**6) + mem0_462*(x**7) + 
mem0_464*(x**8) + mem0_466*(x**9) + mem0_468*(x**10) + mem0_470*(x**11) + 
mem0_472*(x**12) + mem0_474*(x**13) + mem0_476*(x**14) + mem0_478*(x**15)
)
[3329, x**16 - 1746],
eqmod 
(
mem0_448_k7*(x**0) + mem0_450_k7*(x**1) + mem0_452_k7*(x**2) + mem0_454_k7*(x**3) + 
mem0_456_k7*(x**4) + mem0_458_k7*(x**5) + mem0_460_k7*(x**6) + mem0_462_k7*(x**7) + 
mem0_464_k7*(x**8) + mem0_466_k7*(x**9) + mem0_468_k7*(x**10) + mem0_470_k7*(x**11) + 
mem0_472_k7*(x**12) + mem0_474_k7*(x**13) + mem0_476_k7*(x**14) + mem0_478_k7*(x**15) + 
mem0_480_k7*(x**16) + mem0_482_k7*(x**17) + mem0_484_k7*(x**18) + mem0_486_k7*(x**19) + 
mem0_488_k7*(x**20) + mem0_490_k7*(x**21) + mem0_492_k7*(x**22) + mem0_494_k7*(x**23) + 
mem0_496_k7*(x**24) + mem0_498_k7*(x**25) + mem0_500_k7*(x**26) + mem0_502_k7*(x**27) + 
mem0_504_k7*(x**28) + mem0_506_k7*(x**29) + mem0_508_k7*(x**30) + mem0_510_k7*(x**31)
)
(
mem0_480*(x**0) + mem0_482*(x**1) + mem0_484*(x**2) + mem0_486*(x**3) + 
mem0_488*(x**4) + mem0_490*(x**5) + mem0_492*(x**6) + mem0_494*(x**7) + 
mem0_496*(x**8) + mem0_498*(x**9) + mem0_500*(x**10) + mem0_502*(x**11) + 
mem0_504*(x**12) + mem0_506*(x**13) + mem0_508*(x**14) + mem0_510*(x**15)
)
[3329, x**16 - 1583]
] && and [
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