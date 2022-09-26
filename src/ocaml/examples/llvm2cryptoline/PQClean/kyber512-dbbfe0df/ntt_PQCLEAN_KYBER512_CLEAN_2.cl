(*
Xiaomus-MacBook-Pro-2:kyber512-dbbfe0df xshi$ ~/git/cryptoline/_build/default/cv.exe -v -no_carry_constraint -o coqcryptoline.log ~/git/llvm2cryptoline-draft_examples/examples/PQClean/kyber512-dbbfe0df/coqcv_ntt_k2_separated.cl 
Parsing CryptoLine file:		[OK]		0.161782 seconds
Checking well-formedness:		[OK]		0.010207 seconds
Transforming to SSA form:		[OK]		0.001979 seconds
Normalizing specification:		[OK]		0.002317 seconds
Rewriting assignments:			[OK]		0.001603 seconds
Verifying program safety:		[OK]		45.444554 seconds
Verifying range specification:		[OK]		53.299356 seconds
Rewriting value-preserved casting:	[OK]		0.000183 seconds
Verifying algebraic specification:	[OK]		1.319396 seconds
Verification result:			[OK]		100.243860 seconds

_build/default/coqcryptoline.exe -v -jobs 16 -sat_solver cadical -sat_cert grat -no_carry_constraint ~/tmp/coqcv_ntt_k2_separated.cl 
Results of checking CNF formulas:       [OK]            1888.841796 seconds
Finding polynomial coefficients
         Polynomials #0:                [DONE]          674.738165 seconds
         Polynomials #1:                [DONE]          683.738076 seconds
         Polynomials #2:                [DONE]          686.937376 seconds
         Polynomials #3:                [DONE]          693.259432 seconds
Finished finding polynomial coefficients                693.357917 seconds
Verification result:                    [OK]            3141.596638 seconds
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

    (-3)@16 * 3329@16 <s mem0_0, mem0_0 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_2, mem0_2 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_4, mem0_4 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_6, mem0_6 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_8, mem0_8 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_10, mem0_10 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_12, mem0_12 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_14, mem0_14 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_16, mem0_16 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_18, mem0_18 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_20, mem0_20 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_22, mem0_22 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_24, mem0_24 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_26, mem0_26 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_28, mem0_28 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_30, mem0_30 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_32, mem0_32 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_34, mem0_34 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_36, mem0_36 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_38, mem0_38 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_40, mem0_40 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_42, mem0_42 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_44, mem0_44 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_46, mem0_46 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_48, mem0_48 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_50, mem0_50 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_52, mem0_52 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_54, mem0_54 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_56, mem0_56 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_58, mem0_58 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_60, mem0_60 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_62, mem0_62 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_64, mem0_64 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_66, mem0_66 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_68, mem0_68 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_70, mem0_70 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_72, mem0_72 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_74, mem0_74 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_76, mem0_76 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_78, mem0_78 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_80, mem0_80 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_82, mem0_82 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_84, mem0_84 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_86, mem0_86 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_88, mem0_88 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_90, mem0_90 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_92, mem0_92 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_94, mem0_94 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_96, mem0_96 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_98, mem0_98 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_100, mem0_100 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_102, mem0_102 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_104, mem0_104 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_106, mem0_106 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_108, mem0_108 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_110, mem0_110 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_112, mem0_112 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_114, mem0_114 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_116, mem0_116 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_118, mem0_118 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_120, mem0_120 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_122, mem0_122 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_124, mem0_124 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_126, mem0_126 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_128, mem0_128 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_130, mem0_130 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_132, mem0_132 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_134, mem0_134 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_136, mem0_136 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_138, mem0_138 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_140, mem0_140 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_142, mem0_142 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_144, mem0_144 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_146, mem0_146 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_148, mem0_148 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_150, mem0_150 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_152, mem0_152 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_154, mem0_154 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_156, mem0_156 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_158, mem0_158 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_160, mem0_160 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_162, mem0_162 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_164, mem0_164 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_166, mem0_166 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_168, mem0_168 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_170, mem0_170 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_172, mem0_172 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_174, mem0_174 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_176, mem0_176 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_178, mem0_178 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_180, mem0_180 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_182, mem0_182 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_184, mem0_184 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_186, mem0_186 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_188, mem0_188 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_190, mem0_190 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_192, mem0_192 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_194, mem0_194 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_196, mem0_196 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_198, mem0_198 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_200, mem0_200 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_202, mem0_202 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_204, mem0_204 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_206, mem0_206 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_208, mem0_208 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_210, mem0_210 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_212, mem0_212 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_214, mem0_214 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_216, mem0_216 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_218, mem0_218 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_220, mem0_220 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_222, mem0_222 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_224, mem0_224 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_226, mem0_226 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_228, mem0_228 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_230, mem0_230 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_232, mem0_232 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_234, mem0_234 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_236, mem0_236 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_238, mem0_238 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_240, mem0_240 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_242, mem0_242 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_244, mem0_244 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_246, mem0_246 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_248, mem0_248 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_250, mem0_250 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_252, mem0_252 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_254, mem0_254 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_256, mem0_256 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_258, mem0_258 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_260, mem0_260 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_262, mem0_262 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_264, mem0_264 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_266, mem0_266 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_268, mem0_268 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_270, mem0_270 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_272, mem0_272 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_274, mem0_274 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_276, mem0_276 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_278, mem0_278 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_280, mem0_280 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_282, mem0_282 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_284, mem0_284 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_286, mem0_286 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_288, mem0_288 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_290, mem0_290 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_292, mem0_292 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_294, mem0_294 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_296, mem0_296 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_298, mem0_298 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_300, mem0_300 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_302, mem0_302 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_304, mem0_304 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_306, mem0_306 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_308, mem0_308 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_310, mem0_310 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_312, mem0_312 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_314, mem0_314 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_316, mem0_316 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_318, mem0_318 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_320, mem0_320 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_322, mem0_322 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_324, mem0_324 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_326, mem0_326 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_328, mem0_328 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_330, mem0_330 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_332, mem0_332 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_334, mem0_334 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_336, mem0_336 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_338, mem0_338 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_340, mem0_340 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_342, mem0_342 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_344, mem0_344 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_346, mem0_346 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_348, mem0_348 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_350, mem0_350 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_352, mem0_352 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_354, mem0_354 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_356, mem0_356 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_358, mem0_358 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_360, mem0_360 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_362, mem0_362 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_364, mem0_364 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_366, mem0_366 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_368, mem0_368 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_370, mem0_370 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_372, mem0_372 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_374, mem0_374 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_376, mem0_376 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_378, mem0_378 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_380, mem0_380 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_382, mem0_382 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_384, mem0_384 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_386, mem0_386 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_388, mem0_388 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_390, mem0_390 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_392, mem0_392 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_394, mem0_394 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_396, mem0_396 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_398, mem0_398 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_400, mem0_400 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_402, mem0_402 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_404, mem0_404 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_406, mem0_406 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_408, mem0_408 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_410, mem0_410 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_412, mem0_412 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_414, mem0_414 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_416, mem0_416 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_418, mem0_418 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_420, mem0_420 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_422, mem0_422 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_424, mem0_424 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_426, mem0_426 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_428, mem0_428 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_430, mem0_430 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_432, mem0_432 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_434, mem0_434 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_436, mem0_436 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_438, mem0_438 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_440, mem0_440 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_442, mem0_442 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_444, mem0_444 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_446, mem0_446 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_448, mem0_448 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_450, mem0_450 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_452, mem0_452 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_454, mem0_454 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_456, mem0_456 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_458, mem0_458 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_460, mem0_460 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_462, mem0_462 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_464, mem0_464 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_466, mem0_466 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_468, mem0_468 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_470, mem0_470 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_472, mem0_472 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_474, mem0_474 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_476, mem0_476 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_478, mem0_478 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_480, mem0_480 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_482, mem0_482 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_484, mem0_484 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_486, mem0_486 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_488, mem0_488 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_490, mem0_490 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_492, mem0_492 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_494, mem0_494 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_496, mem0_496 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_498, mem0_498 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_500, mem0_500 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_502, mem0_502 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_504, mem0_504 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_506, mem0_506 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_508, mem0_508 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_510, mem0_510 <s 3@16 * 3329@16


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

mov mem0_0_k1 mem0_0;
mov mem0_2_k1 mem0_2;
mov mem0_4_k1 mem0_4;
mov mem0_6_k1 mem0_6;
mov mem0_8_k1 mem0_8;
mov mem0_10_k1 mem0_10;
mov mem0_12_k1 mem0_12;
mov mem0_14_k1 mem0_14;
mov mem0_16_k1 mem0_16;
mov mem0_18_k1 mem0_18;
mov mem0_20_k1 mem0_20;
mov mem0_22_k1 mem0_22;
mov mem0_24_k1 mem0_24;
mov mem0_26_k1 mem0_26;
mov mem0_28_k1 mem0_28;
mov mem0_30_k1 mem0_30;
mov mem0_32_k1 mem0_32;
mov mem0_34_k1 mem0_34;
mov mem0_36_k1 mem0_36;
mov mem0_38_k1 mem0_38;
mov mem0_40_k1 mem0_40;
mov mem0_42_k1 mem0_42;
mov mem0_44_k1 mem0_44;
mov mem0_46_k1 mem0_46;
mov mem0_48_k1 mem0_48;
mov mem0_50_k1 mem0_50;
mov mem0_52_k1 mem0_52;
mov mem0_54_k1 mem0_54;
mov mem0_56_k1 mem0_56;
mov mem0_58_k1 mem0_58;
mov mem0_60_k1 mem0_60;
mov mem0_62_k1 mem0_62;
mov mem0_64_k1 mem0_64;
mov mem0_66_k1 mem0_66;
mov mem0_68_k1 mem0_68;
mov mem0_70_k1 mem0_70;
mov mem0_72_k1 mem0_72;
mov mem0_74_k1 mem0_74;
mov mem0_76_k1 mem0_76;
mov mem0_78_k1 mem0_78;
mov mem0_80_k1 mem0_80;
mov mem0_82_k1 mem0_82;
mov mem0_84_k1 mem0_84;
mov mem0_86_k1 mem0_86;
mov mem0_88_k1 mem0_88;
mov mem0_90_k1 mem0_90;
mov mem0_92_k1 mem0_92;
mov mem0_94_k1 mem0_94;
mov mem0_96_k1 mem0_96;
mov mem0_98_k1 mem0_98;
mov mem0_100_k1 mem0_100;
mov mem0_102_k1 mem0_102;
mov mem0_104_k1 mem0_104;
mov mem0_106_k1 mem0_106;
mov mem0_108_k1 mem0_108;
mov mem0_110_k1 mem0_110;
mov mem0_112_k1 mem0_112;
mov mem0_114_k1 mem0_114;
mov mem0_116_k1 mem0_116;
mov mem0_118_k1 mem0_118;
mov mem0_120_k1 mem0_120;
mov mem0_122_k1 mem0_122;
mov mem0_124_k1 mem0_124;
mov mem0_126_k1 mem0_126;
mov mem0_128_k1 mem0_128;
mov mem0_130_k1 mem0_130;
mov mem0_132_k1 mem0_132;
mov mem0_134_k1 mem0_134;
mov mem0_136_k1 mem0_136;
mov mem0_138_k1 mem0_138;
mov mem0_140_k1 mem0_140;
mov mem0_142_k1 mem0_142;
mov mem0_144_k1 mem0_144;
mov mem0_146_k1 mem0_146;
mov mem0_148_k1 mem0_148;
mov mem0_150_k1 mem0_150;
mov mem0_152_k1 mem0_152;
mov mem0_154_k1 mem0_154;
mov mem0_156_k1 mem0_156;
mov mem0_158_k1 mem0_158;
mov mem0_160_k1 mem0_160;
mov mem0_162_k1 mem0_162;
mov mem0_164_k1 mem0_164;
mov mem0_166_k1 mem0_166;
mov mem0_168_k1 mem0_168;
mov mem0_170_k1 mem0_170;
mov mem0_172_k1 mem0_172;
mov mem0_174_k1 mem0_174;
mov mem0_176_k1 mem0_176;
mov mem0_178_k1 mem0_178;
mov mem0_180_k1 mem0_180;
mov mem0_182_k1 mem0_182;
mov mem0_184_k1 mem0_184;
mov mem0_186_k1 mem0_186;
mov mem0_188_k1 mem0_188;
mov mem0_190_k1 mem0_190;
mov mem0_192_k1 mem0_192;
mov mem0_194_k1 mem0_194;
mov mem0_196_k1 mem0_196;
mov mem0_198_k1 mem0_198;
mov mem0_200_k1 mem0_200;
mov mem0_202_k1 mem0_202;
mov mem0_204_k1 mem0_204;
mov mem0_206_k1 mem0_206;
mov mem0_208_k1 mem0_208;
mov mem0_210_k1 mem0_210;
mov mem0_212_k1 mem0_212;
mov mem0_214_k1 mem0_214;
mov mem0_216_k1 mem0_216;
mov mem0_218_k1 mem0_218;
mov mem0_220_k1 mem0_220;
mov mem0_222_k1 mem0_222;
mov mem0_224_k1 mem0_224;
mov mem0_226_k1 mem0_226;
mov mem0_228_k1 mem0_228;
mov mem0_230_k1 mem0_230;
mov mem0_232_k1 mem0_232;
mov mem0_234_k1 mem0_234;
mov mem0_236_k1 mem0_236;
mov mem0_238_k1 mem0_238;
mov mem0_240_k1 mem0_240;
mov mem0_242_k1 mem0_242;
mov mem0_244_k1 mem0_244;
mov mem0_246_k1 mem0_246;
mov mem0_248_k1 mem0_248;
mov mem0_250_k1 mem0_250;
mov mem0_252_k1 mem0_252;
mov mem0_254_k1 mem0_254;
mov mem0_256_k1 mem0_256;
mov mem0_258_k1 mem0_258;
mov mem0_260_k1 mem0_260;
mov mem0_262_k1 mem0_262;
mov mem0_264_k1 mem0_264;
mov mem0_266_k1 mem0_266;
mov mem0_268_k1 mem0_268;
mov mem0_270_k1 mem0_270;
mov mem0_272_k1 mem0_272;
mov mem0_274_k1 mem0_274;
mov mem0_276_k1 mem0_276;
mov mem0_278_k1 mem0_278;
mov mem0_280_k1 mem0_280;
mov mem0_282_k1 mem0_282;
mov mem0_284_k1 mem0_284;
mov mem0_286_k1 mem0_286;
mov mem0_288_k1 mem0_288;
mov mem0_290_k1 mem0_290;
mov mem0_292_k1 mem0_292;
mov mem0_294_k1 mem0_294;
mov mem0_296_k1 mem0_296;
mov mem0_298_k1 mem0_298;
mov mem0_300_k1 mem0_300;
mov mem0_302_k1 mem0_302;
mov mem0_304_k1 mem0_304;
mov mem0_306_k1 mem0_306;
mov mem0_308_k1 mem0_308;
mov mem0_310_k1 mem0_310;
mov mem0_312_k1 mem0_312;
mov mem0_314_k1 mem0_314;
mov mem0_316_k1 mem0_316;
mov mem0_318_k1 mem0_318;
mov mem0_320_k1 mem0_320;
mov mem0_322_k1 mem0_322;
mov mem0_324_k1 mem0_324;
mov mem0_326_k1 mem0_326;
mov mem0_328_k1 mem0_328;
mov mem0_330_k1 mem0_330;
mov mem0_332_k1 mem0_332;
mov mem0_334_k1 mem0_334;
mov mem0_336_k1 mem0_336;
mov mem0_338_k1 mem0_338;
mov mem0_340_k1 mem0_340;
mov mem0_342_k1 mem0_342;
mov mem0_344_k1 mem0_344;
mov mem0_346_k1 mem0_346;
mov mem0_348_k1 mem0_348;
mov mem0_350_k1 mem0_350;
mov mem0_352_k1 mem0_352;
mov mem0_354_k1 mem0_354;
mov mem0_356_k1 mem0_356;
mov mem0_358_k1 mem0_358;
mov mem0_360_k1 mem0_360;
mov mem0_362_k1 mem0_362;
mov mem0_364_k1 mem0_364;
mov mem0_366_k1 mem0_366;
mov mem0_368_k1 mem0_368;
mov mem0_370_k1 mem0_370;
mov mem0_372_k1 mem0_372;
mov mem0_374_k1 mem0_374;
mov mem0_376_k1 mem0_376;
mov mem0_378_k1 mem0_378;
mov mem0_380_k1 mem0_380;
mov mem0_382_k1 mem0_382;
mov mem0_384_k1 mem0_384;
mov mem0_386_k1 mem0_386;
mov mem0_388_k1 mem0_388;
mov mem0_390_k1 mem0_390;
mov mem0_392_k1 mem0_392;
mov mem0_394_k1 mem0_394;
mov mem0_396_k1 mem0_396;
mov mem0_398_k1 mem0_398;
mov mem0_400_k1 mem0_400;
mov mem0_402_k1 mem0_402;
mov mem0_404_k1 mem0_404;
mov mem0_406_k1 mem0_406;
mov mem0_408_k1 mem0_408;
mov mem0_410_k1 mem0_410;
mov mem0_412_k1 mem0_412;
mov mem0_414_k1 mem0_414;
mov mem0_416_k1 mem0_416;
mov mem0_418_k1 mem0_418;
mov mem0_420_k1 mem0_420;
mov mem0_422_k1 mem0_422;
mov mem0_424_k1 mem0_424;
mov mem0_426_k1 mem0_426;
mov mem0_428_k1 mem0_428;
mov mem0_430_k1 mem0_430;
mov mem0_432_k1 mem0_432;
mov mem0_434_k1 mem0_434;
mov mem0_436_k1 mem0_436;
mov mem0_438_k1 mem0_438;
mov mem0_440_k1 mem0_440;
mov mem0_442_k1 mem0_442;
mov mem0_444_k1 mem0_444;
mov mem0_446_k1 mem0_446;
mov mem0_448_k1 mem0_448;
mov mem0_450_k1 mem0_450;
mov mem0_452_k1 mem0_452;
mov mem0_454_k1 mem0_454;
mov mem0_456_k1 mem0_456;
mov mem0_458_k1 mem0_458;
mov mem0_460_k1 mem0_460;
mov mem0_462_k1 mem0_462;
mov mem0_464_k1 mem0_464;
mov mem0_466_k1 mem0_466;
mov mem0_468_k1 mem0_468;
mov mem0_470_k1 mem0_470;
mov mem0_472_k1 mem0_472;
mov mem0_474_k1 mem0_474;
mov mem0_476_k1 mem0_476;
mov mem0_478_k1 mem0_478;
mov mem0_480_k1 mem0_480;
mov mem0_482_k1 mem0_482;
mov mem0_484_k1 mem0_484;
mov mem0_486_k1 mem0_486;
mov mem0_488_k1 mem0_488;
mov mem0_490_k1 mem0_490;
mov mem0_492_k1 mem0_492;
mov mem0_494_k1 mem0_494;
mov mem0_496_k1 mem0_496;
mov mem0_498_k1 mem0_498;
mov mem0_500_k1 mem0_500;
mov mem0_502_k1 mem0_502;
mov mem0_504_k1 mem0_504;
mov mem0_506_k1 mem0_506;
mov mem0_508_k1 mem0_508;
mov mem0_510_k1 mem0_510;

(*   %arrayidx9.1 = getelementptr inbounds i16, i16* %r, i64 64 *)
(*   %256 = load i16, i16* %arrayidx9.1, align 2, !tbaa !3 *)
mov v256 mem0_128;
(*   %conv1.i.1 = sext i16 %256 to i32 *)
cast v_conv1_i_1@sint32 v256@sint16;
(*   %mul.i.1 = mul nsw i32 %conv1.i.1, -359 *)
mul v_mul_i_1 v_conv1_i_1 (-359)@sint32;
(*   %call.i.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1, v_call_i_1);
(*   %257 = load i16, i16* %r, align 2, !tbaa !3 *)
mov v257 mem0_0;
(*   %sub.1 = sub i16 %257, %call.i.1 *)
sub v_sub_1 v257 v_call_i_1;
(*   store i16 %sub.1, i16* %arrayidx9.1, align 2, !tbaa !3 *)
mov mem0_128 v_sub_1;
(*   %add21.1 = add i16 %257, %call.i.1 *)
add v_add21_1 v257 v_call_i_1;
(*   store i16 %add21.1, i16* %r, align 2, !tbaa !3 *)
mov mem0_0 v_add21_1;
(*   %arrayidx9.1.1 = getelementptr inbounds i16, i16* %r, i64 65 *)
(*   %258 = load i16, i16* %arrayidx9.1.1, align 2, !tbaa !3 *)
mov v258 mem0_130;
(*   %conv1.i.1.1 = sext i16 %258 to i32 *)
cast v_conv1_i_1_1@sint32 v258@sint16;
(*   %mul.i.1.1 = mul nsw i32 %conv1.i.1.1, -359 *)
mul v_mul_i_1_1 v_conv1_i_1_1 (-359)@sint32;
(*   %call.i.1.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_1, v_call_i_1_1);
(*   %arrayidx11.1.1 = getelementptr inbounds i16, i16* %r, i64 1 *)
(*   %259 = load i16, i16* %arrayidx11.1.1, align 2, !tbaa !3 *)
mov v259 mem0_2;
(*   %sub.1.1 = sub i16 %259, %call.i.1.1 *)
sub v_sub_1_1 v259 v_call_i_1_1;
(*   store i16 %sub.1.1, i16* %arrayidx9.1.1, align 2, !tbaa !3 *)
mov mem0_130 v_sub_1_1;
(*   %add21.1.1 = add i16 %259, %call.i.1.1 *)
add v_add21_1_1 v259 v_call_i_1_1;
(*   store i16 %add21.1.1, i16* %arrayidx11.1.1, align 2, !tbaa !3 *)
mov mem0_2 v_add21_1_1;
(*   %arrayidx9.1.2 = getelementptr inbounds i16, i16* %r, i64 66 *)
(*   %260 = load i16, i16* %arrayidx9.1.2, align 2, !tbaa !3 *)
mov v260 mem0_132;
(*   %conv1.i.1.2 = sext i16 %260 to i32 *)
cast v_conv1_i_1_2@sint32 v260@sint16;
(*   %mul.i.1.2 = mul nsw i32 %conv1.i.1.2, -359 *)
mul v_mul_i_1_2 v_conv1_i_1_2 (-359)@sint32;
(*   %call.i.1.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_2, v_call_i_1_2);
(*   %arrayidx11.1.2 = getelementptr inbounds i16, i16* %r, i64 2 *)
(*   %261 = load i16, i16* %arrayidx11.1.2, align 2, !tbaa !3 *)
mov v261 mem0_4;
(*   %sub.1.2 = sub i16 %261, %call.i.1.2 *)
sub v_sub_1_2 v261 v_call_i_1_2;
(*   store i16 %sub.1.2, i16* %arrayidx9.1.2, align 2, !tbaa !3 *)
mov mem0_132 v_sub_1_2;
(*   %add21.1.2 = add i16 %261, %call.i.1.2 *)
add v_add21_1_2 v261 v_call_i_1_2;
(*   store i16 %add21.1.2, i16* %arrayidx11.1.2, align 2, !tbaa !3 *)
mov mem0_4 v_add21_1_2;
(*   %arrayidx9.1.3 = getelementptr inbounds i16, i16* %r, i64 67 *)
(*   %262 = load i16, i16* %arrayidx9.1.3, align 2, !tbaa !3 *)
mov v262 mem0_134;
(*   %conv1.i.1.3 = sext i16 %262 to i32 *)
cast v_conv1_i_1_3@sint32 v262@sint16;
(*   %mul.i.1.3 = mul nsw i32 %conv1.i.1.3, -359 *)
mul v_mul_i_1_3 v_conv1_i_1_3 (-359)@sint32;
(*   %call.i.1.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_3, v_call_i_1_3);
(*   %arrayidx11.1.3 = getelementptr inbounds i16, i16* %r, i64 3 *)
(*   %263 = load i16, i16* %arrayidx11.1.3, align 2, !tbaa !3 *)
mov v263 mem0_6;
(*   %sub.1.3 = sub i16 %263, %call.i.1.3 *)
sub v_sub_1_3 v263 v_call_i_1_3;
(*   store i16 %sub.1.3, i16* %arrayidx9.1.3, align 2, !tbaa !3 *)
mov mem0_134 v_sub_1_3;
(*   %add21.1.3 = add i16 %263, %call.i.1.3 *)
add v_add21_1_3 v263 v_call_i_1_3;
(*   store i16 %add21.1.3, i16* %arrayidx11.1.3, align 2, !tbaa !3 *)
mov mem0_6 v_add21_1_3;
(*   %arrayidx9.1.4 = getelementptr inbounds i16, i16* %r, i64 68 *)
(*   %264 = load i16, i16* %arrayidx9.1.4, align 2, !tbaa !3 *)
mov v264 mem0_136;
(*   %conv1.i.1.4 = sext i16 %264 to i32 *)
cast v_conv1_i_1_4@sint32 v264@sint16;
(*   %mul.i.1.4 = mul nsw i32 %conv1.i.1.4, -359 *)
mul v_mul_i_1_4 v_conv1_i_1_4 (-359)@sint32;
(*   %call.i.1.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_4, v_call_i_1_4);
(*   %arrayidx11.1.4 = getelementptr inbounds i16, i16* %r, i64 4 *)
(*   %265 = load i16, i16* %arrayidx11.1.4, align 2, !tbaa !3 *)
mov v265 mem0_8;
(*   %sub.1.4 = sub i16 %265, %call.i.1.4 *)
sub v_sub_1_4 v265 v_call_i_1_4;
(*   store i16 %sub.1.4, i16* %arrayidx9.1.4, align 2, !tbaa !3 *)
mov mem0_136 v_sub_1_4;
(*   %add21.1.4 = add i16 %265, %call.i.1.4 *)
add v_add21_1_4 v265 v_call_i_1_4;
(*   store i16 %add21.1.4, i16* %arrayidx11.1.4, align 2, !tbaa !3 *)
mov mem0_8 v_add21_1_4;
(*   %arrayidx9.1.5 = getelementptr inbounds i16, i16* %r, i64 69 *)
(*   %266 = load i16, i16* %arrayidx9.1.5, align 2, !tbaa !3 *)
mov v266 mem0_138;
(*   %conv1.i.1.5 = sext i16 %266 to i32 *)
cast v_conv1_i_1_5@sint32 v266@sint16;
(*   %mul.i.1.5 = mul nsw i32 %conv1.i.1.5, -359 *)
mul v_mul_i_1_5 v_conv1_i_1_5 (-359)@sint32;
(*   %call.i.1.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_5, v_call_i_1_5);
(*   %arrayidx11.1.5 = getelementptr inbounds i16, i16* %r, i64 5 *)
(*   %267 = load i16, i16* %arrayidx11.1.5, align 2, !tbaa !3 *)
mov v267 mem0_10;
(*   %sub.1.5 = sub i16 %267, %call.i.1.5 *)
sub v_sub_1_5 v267 v_call_i_1_5;
(*   store i16 %sub.1.5, i16* %arrayidx9.1.5, align 2, !tbaa !3 *)
mov mem0_138 v_sub_1_5;
(*   %add21.1.5 = add i16 %267, %call.i.1.5 *)
add v_add21_1_5 v267 v_call_i_1_5;
(*   store i16 %add21.1.5, i16* %arrayidx11.1.5, align 2, !tbaa !3 *)
mov mem0_10 v_add21_1_5;
(*   %arrayidx9.1.6 = getelementptr inbounds i16, i16* %r, i64 70 *)
(*   %268 = load i16, i16* %arrayidx9.1.6, align 2, !tbaa !3 *)
mov v268 mem0_140;
(*   %conv1.i.1.6 = sext i16 %268 to i32 *)
cast v_conv1_i_1_6@sint32 v268@sint16;
(*   %mul.i.1.6 = mul nsw i32 %conv1.i.1.6, -359 *)
mul v_mul_i_1_6 v_conv1_i_1_6 (-359)@sint32;
(*   %call.i.1.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_6, v_call_i_1_6);
(*   %arrayidx11.1.6 = getelementptr inbounds i16, i16* %r, i64 6 *)
(*   %269 = load i16, i16* %arrayidx11.1.6, align 2, !tbaa !3 *)
mov v269 mem0_12;
(*   %sub.1.6 = sub i16 %269, %call.i.1.6 *)
sub v_sub_1_6 v269 v_call_i_1_6;
(*   store i16 %sub.1.6, i16* %arrayidx9.1.6, align 2, !tbaa !3 *)
mov mem0_140 v_sub_1_6;
(*   %add21.1.6 = add i16 %269, %call.i.1.6 *)
add v_add21_1_6 v269 v_call_i_1_6;
(*   store i16 %add21.1.6, i16* %arrayidx11.1.6, align 2, !tbaa !3 *)
mov mem0_12 v_add21_1_6;
(*   %arrayidx9.1.7 = getelementptr inbounds i16, i16* %r, i64 71 *)
(*   %270 = load i16, i16* %arrayidx9.1.7, align 2, !tbaa !3 *)
mov v270 mem0_142;
(*   %conv1.i.1.7 = sext i16 %270 to i32 *)
cast v_conv1_i_1_7@sint32 v270@sint16;
(*   %mul.i.1.7 = mul nsw i32 %conv1.i.1.7, -359 *)
mul v_mul_i_1_7 v_conv1_i_1_7 (-359)@sint32;
(*   %call.i.1.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_7, v_call_i_1_7);
(*   %arrayidx11.1.7 = getelementptr inbounds i16, i16* %r, i64 7 *)
(*   %271 = load i16, i16* %arrayidx11.1.7, align 2, !tbaa !3 *)
mov v271 mem0_14;
(*   %sub.1.7 = sub i16 %271, %call.i.1.7 *)
sub v_sub_1_7 v271 v_call_i_1_7;
(*   store i16 %sub.1.7, i16* %arrayidx9.1.7, align 2, !tbaa !3 *)
mov mem0_142 v_sub_1_7;
(*   %add21.1.7 = add i16 %271, %call.i.1.7 *)
add v_add21_1_7 v271 v_call_i_1_7;
(*   store i16 %add21.1.7, i16* %arrayidx11.1.7, align 2, !tbaa !3 *)
mov mem0_14 v_add21_1_7;
(*   %arrayidx9.1.8 = getelementptr inbounds i16, i16* %r, i64 72 *)
(*   %272 = load i16, i16* %arrayidx9.1.8, align 2, !tbaa !3 *)
mov v272 mem0_144;
(*   %conv1.i.1.8 = sext i16 %272 to i32 *)
cast v_conv1_i_1_8@sint32 v272@sint16;
(*   %mul.i.1.8 = mul nsw i32 %conv1.i.1.8, -359 *)
mul v_mul_i_1_8 v_conv1_i_1_8 (-359)@sint32;
(*   %call.i.1.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_8, v_call_i_1_8);
(*   %arrayidx11.1.8 = getelementptr inbounds i16, i16* %r, i64 8 *)
(*   %273 = load i16, i16* %arrayidx11.1.8, align 2, !tbaa !3 *)
mov v273 mem0_16;
(*   %sub.1.8 = sub i16 %273, %call.i.1.8 *)
sub v_sub_1_8 v273 v_call_i_1_8;
(*   store i16 %sub.1.8, i16* %arrayidx9.1.8, align 2, !tbaa !3 *)
mov mem0_144 v_sub_1_8;
(*   %add21.1.8 = add i16 %273, %call.i.1.8 *)
add v_add21_1_8 v273 v_call_i_1_8;
(*   store i16 %add21.1.8, i16* %arrayidx11.1.8, align 2, !tbaa !3 *)
mov mem0_16 v_add21_1_8;
(*   %arrayidx9.1.9 = getelementptr inbounds i16, i16* %r, i64 73 *)
(*   %274 = load i16, i16* %arrayidx9.1.9, align 2, !tbaa !3 *)
mov v274 mem0_146;
(*   %conv1.i.1.9 = sext i16 %274 to i32 *)
cast v_conv1_i_1_9@sint32 v274@sint16;
(*   %mul.i.1.9 = mul nsw i32 %conv1.i.1.9, -359 *)
mul v_mul_i_1_9 v_conv1_i_1_9 (-359)@sint32;
(*   %call.i.1.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_9, v_call_i_1_9);
(*   %arrayidx11.1.9 = getelementptr inbounds i16, i16* %r, i64 9 *)
(*   %275 = load i16, i16* %arrayidx11.1.9, align 2, !tbaa !3 *)
mov v275 mem0_18;
(*   %sub.1.9 = sub i16 %275, %call.i.1.9 *)
sub v_sub_1_9 v275 v_call_i_1_9;
(*   store i16 %sub.1.9, i16* %arrayidx9.1.9, align 2, !tbaa !3 *)
mov mem0_146 v_sub_1_9;
(*   %add21.1.9 = add i16 %275, %call.i.1.9 *)
add v_add21_1_9 v275 v_call_i_1_9;
(*   store i16 %add21.1.9, i16* %arrayidx11.1.9, align 2, !tbaa !3 *)
mov mem0_18 v_add21_1_9;
(*   %arrayidx9.1.10 = getelementptr inbounds i16, i16* %r, i64 74 *)
(*   %276 = load i16, i16* %arrayidx9.1.10, align 2, !tbaa !3 *)
mov v276 mem0_148;
(*   %conv1.i.1.10 = sext i16 %276 to i32 *)
cast v_conv1_i_1_10@sint32 v276@sint16;
(*   %mul.i.1.10 = mul nsw i32 %conv1.i.1.10, -359 *)
mul v_mul_i_1_10 v_conv1_i_1_10 (-359)@sint32;
(*   %call.i.1.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_10, v_call_i_1_10);
(*   %arrayidx11.1.10 = getelementptr inbounds i16, i16* %r, i64 10 *)
(*   %277 = load i16, i16* %arrayidx11.1.10, align 2, !tbaa !3 *)
mov v277 mem0_20;
(*   %sub.1.10 = sub i16 %277, %call.i.1.10 *)
sub v_sub_1_10 v277 v_call_i_1_10;
(*   store i16 %sub.1.10, i16* %arrayidx9.1.10, align 2, !tbaa !3 *)
mov mem0_148 v_sub_1_10;
(*   %add21.1.10 = add i16 %277, %call.i.1.10 *)
add v_add21_1_10 v277 v_call_i_1_10;
(*   store i16 %add21.1.10, i16* %arrayidx11.1.10, align 2, !tbaa !3 *)
mov mem0_20 v_add21_1_10;
(*   %arrayidx9.1.11 = getelementptr inbounds i16, i16* %r, i64 75 *)
(*   %278 = load i16, i16* %arrayidx9.1.11, align 2, !tbaa !3 *)
mov v278 mem0_150;
(*   %conv1.i.1.11 = sext i16 %278 to i32 *)
cast v_conv1_i_1_11@sint32 v278@sint16;
(*   %mul.i.1.11 = mul nsw i32 %conv1.i.1.11, -359 *)
mul v_mul_i_1_11 v_conv1_i_1_11 (-359)@sint32;
(*   %call.i.1.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_11, v_call_i_1_11);
(*   %arrayidx11.1.11 = getelementptr inbounds i16, i16* %r, i64 11 *)
(*   %279 = load i16, i16* %arrayidx11.1.11, align 2, !tbaa !3 *)
mov v279 mem0_22;
(*   %sub.1.11 = sub i16 %279, %call.i.1.11 *)
sub v_sub_1_11 v279 v_call_i_1_11;
(*   store i16 %sub.1.11, i16* %arrayidx9.1.11, align 2, !tbaa !3 *)
mov mem0_150 v_sub_1_11;
(*   %add21.1.11 = add i16 %279, %call.i.1.11 *)
add v_add21_1_11 v279 v_call_i_1_11;
(*   store i16 %add21.1.11, i16* %arrayidx11.1.11, align 2, !tbaa !3 *)
mov mem0_22 v_add21_1_11;
(*   %arrayidx9.1.12 = getelementptr inbounds i16, i16* %r, i64 76 *)
(*   %280 = load i16, i16* %arrayidx9.1.12, align 2, !tbaa !3 *)
mov v280 mem0_152;
(*   %conv1.i.1.12 = sext i16 %280 to i32 *)
cast v_conv1_i_1_12@sint32 v280@sint16;
(*   %mul.i.1.12 = mul nsw i32 %conv1.i.1.12, -359 *)
mul v_mul_i_1_12 v_conv1_i_1_12 (-359)@sint32;
(*   %call.i.1.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_12, v_call_i_1_12);
(*   %arrayidx11.1.12 = getelementptr inbounds i16, i16* %r, i64 12 *)
(*   %281 = load i16, i16* %arrayidx11.1.12, align 2, !tbaa !3 *)
mov v281 mem0_24;
(*   %sub.1.12 = sub i16 %281, %call.i.1.12 *)
sub v_sub_1_12 v281 v_call_i_1_12;
(*   store i16 %sub.1.12, i16* %arrayidx9.1.12, align 2, !tbaa !3 *)
mov mem0_152 v_sub_1_12;
(*   %add21.1.12 = add i16 %281, %call.i.1.12 *)
add v_add21_1_12 v281 v_call_i_1_12;
(*   store i16 %add21.1.12, i16* %arrayidx11.1.12, align 2, !tbaa !3 *)
mov mem0_24 v_add21_1_12;
(*   %arrayidx9.1.13 = getelementptr inbounds i16, i16* %r, i64 77 *)
(*   %282 = load i16, i16* %arrayidx9.1.13, align 2, !tbaa !3 *)
mov v282 mem0_154;
(*   %conv1.i.1.13 = sext i16 %282 to i32 *)
cast v_conv1_i_1_13@sint32 v282@sint16;
(*   %mul.i.1.13 = mul nsw i32 %conv1.i.1.13, -359 *)
mul v_mul_i_1_13 v_conv1_i_1_13 (-359)@sint32;
(*   %call.i.1.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_13, v_call_i_1_13);
(*   %arrayidx11.1.13 = getelementptr inbounds i16, i16* %r, i64 13 *)
(*   %283 = load i16, i16* %arrayidx11.1.13, align 2, !tbaa !3 *)
mov v283 mem0_26;
(*   %sub.1.13 = sub i16 %283, %call.i.1.13 *)
sub v_sub_1_13 v283 v_call_i_1_13;
(*   store i16 %sub.1.13, i16* %arrayidx9.1.13, align 2, !tbaa !3 *)
mov mem0_154 v_sub_1_13;
(*   %add21.1.13 = add i16 %283, %call.i.1.13 *)
add v_add21_1_13 v283 v_call_i_1_13;
(*   store i16 %add21.1.13, i16* %arrayidx11.1.13, align 2, !tbaa !3 *)
mov mem0_26 v_add21_1_13;
(*   %arrayidx9.1.14 = getelementptr inbounds i16, i16* %r, i64 78 *)
(*   %284 = load i16, i16* %arrayidx9.1.14, align 2, !tbaa !3 *)
mov v284 mem0_156;
(*   %conv1.i.1.14 = sext i16 %284 to i32 *)
cast v_conv1_i_1_14@sint32 v284@sint16;
(*   %mul.i.1.14 = mul nsw i32 %conv1.i.1.14, -359 *)
mul v_mul_i_1_14 v_conv1_i_1_14 (-359)@sint32;
(*   %call.i.1.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_14, v_call_i_1_14);
(*   %arrayidx11.1.14 = getelementptr inbounds i16, i16* %r, i64 14 *)
(*   %285 = load i16, i16* %arrayidx11.1.14, align 2, !tbaa !3 *)
mov v285 mem0_28;
(*   %sub.1.14 = sub i16 %285, %call.i.1.14 *)
sub v_sub_1_14 v285 v_call_i_1_14;
(*   store i16 %sub.1.14, i16* %arrayidx9.1.14, align 2, !tbaa !3 *)
mov mem0_156 v_sub_1_14;
(*   %add21.1.14 = add i16 %285, %call.i.1.14 *)
add v_add21_1_14 v285 v_call_i_1_14;
(*   store i16 %add21.1.14, i16* %arrayidx11.1.14, align 2, !tbaa !3 *)
mov mem0_28 v_add21_1_14;
(*   %arrayidx9.1.15 = getelementptr inbounds i16, i16* %r, i64 79 *)
(*   %286 = load i16, i16* %arrayidx9.1.15, align 2, !tbaa !3 *)
mov v286 mem0_158;
(*   %conv1.i.1.15 = sext i16 %286 to i32 *)
cast v_conv1_i_1_15@sint32 v286@sint16;
(*   %mul.i.1.15 = mul nsw i32 %conv1.i.1.15, -359 *)
mul v_mul_i_1_15 v_conv1_i_1_15 (-359)@sint32;
(*   %call.i.1.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_15, v_call_i_1_15);
(*   %arrayidx11.1.15 = getelementptr inbounds i16, i16* %r, i64 15 *)
(*   %287 = load i16, i16* %arrayidx11.1.15, align 2, !tbaa !3 *)
mov v287 mem0_30;
(*   %sub.1.15 = sub i16 %287, %call.i.1.15 *)
sub v_sub_1_15 v287 v_call_i_1_15;
(*   store i16 %sub.1.15, i16* %arrayidx9.1.15, align 2, !tbaa !3 *)
mov mem0_158 v_sub_1_15;
(*   %add21.1.15 = add i16 %287, %call.i.1.15 *)
add v_add21_1_15 v287 v_call_i_1_15;
(*   store i16 %add21.1.15, i16* %arrayidx11.1.15, align 2, !tbaa !3 *)
mov mem0_30 v_add21_1_15;
(*   %arrayidx9.1.16 = getelementptr inbounds i16, i16* %r, i64 80 *)
(*   %288 = load i16, i16* %arrayidx9.1.16, align 2, !tbaa !3 *)
mov v288 mem0_160;
(*   %conv1.i.1.16 = sext i16 %288 to i32 *)
cast v_conv1_i_1_16@sint32 v288@sint16;
(*   %mul.i.1.16 = mul nsw i32 %conv1.i.1.16, -359 *)
mul v_mul_i_1_16 v_conv1_i_1_16 (-359)@sint32;
(*   %call.i.1.16 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.16) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_16, v_call_i_1_16);
(*   %arrayidx11.1.16 = getelementptr inbounds i16, i16* %r, i64 16 *)
(*   %289 = load i16, i16* %arrayidx11.1.16, align 2, !tbaa !3 *)
mov v289 mem0_32;
(*   %sub.1.16 = sub i16 %289, %call.i.1.16 *)
sub v_sub_1_16 v289 v_call_i_1_16;
(*   store i16 %sub.1.16, i16* %arrayidx9.1.16, align 2, !tbaa !3 *)
mov mem0_160 v_sub_1_16;
(*   %add21.1.16 = add i16 %289, %call.i.1.16 *)
add v_add21_1_16 v289 v_call_i_1_16;
(*   store i16 %add21.1.16, i16* %arrayidx11.1.16, align 2, !tbaa !3 *)
mov mem0_32 v_add21_1_16;
(*   %arrayidx9.1.17 = getelementptr inbounds i16, i16* %r, i64 81 *)
(*   %290 = load i16, i16* %arrayidx9.1.17, align 2, !tbaa !3 *)
mov v290 mem0_162;
(*   %conv1.i.1.17 = sext i16 %290 to i32 *)
cast v_conv1_i_1_17@sint32 v290@sint16;
(*   %mul.i.1.17 = mul nsw i32 %conv1.i.1.17, -359 *)
mul v_mul_i_1_17 v_conv1_i_1_17 (-359)@sint32;
(*   %call.i.1.17 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.17) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_17, v_call_i_1_17);
(*   %arrayidx11.1.17 = getelementptr inbounds i16, i16* %r, i64 17 *)
(*   %291 = load i16, i16* %arrayidx11.1.17, align 2, !tbaa !3 *)
mov v291 mem0_34;
(*   %sub.1.17 = sub i16 %291, %call.i.1.17 *)
sub v_sub_1_17 v291 v_call_i_1_17;
(*   store i16 %sub.1.17, i16* %arrayidx9.1.17, align 2, !tbaa !3 *)
mov mem0_162 v_sub_1_17;
(*   %add21.1.17 = add i16 %291, %call.i.1.17 *)
add v_add21_1_17 v291 v_call_i_1_17;
(*   store i16 %add21.1.17, i16* %arrayidx11.1.17, align 2, !tbaa !3 *)
mov mem0_34 v_add21_1_17;
(*   %arrayidx9.1.18 = getelementptr inbounds i16, i16* %r, i64 82 *)
(*   %292 = load i16, i16* %arrayidx9.1.18, align 2, !tbaa !3 *)
mov v292 mem0_164;
(*   %conv1.i.1.18 = sext i16 %292 to i32 *)
cast v_conv1_i_1_18@sint32 v292@sint16;
(*   %mul.i.1.18 = mul nsw i32 %conv1.i.1.18, -359 *)
mul v_mul_i_1_18 v_conv1_i_1_18 (-359)@sint32;
(*   %call.i.1.18 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.18) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_18, v_call_i_1_18);
(*   %arrayidx11.1.18 = getelementptr inbounds i16, i16* %r, i64 18 *)
(*   %293 = load i16, i16* %arrayidx11.1.18, align 2, !tbaa !3 *)
mov v293 mem0_36;
(*   %sub.1.18 = sub i16 %293, %call.i.1.18 *)
sub v_sub_1_18 v293 v_call_i_1_18;
(*   store i16 %sub.1.18, i16* %arrayidx9.1.18, align 2, !tbaa !3 *)
mov mem0_164 v_sub_1_18;
(*   %add21.1.18 = add i16 %293, %call.i.1.18 *)
add v_add21_1_18 v293 v_call_i_1_18;
(*   store i16 %add21.1.18, i16* %arrayidx11.1.18, align 2, !tbaa !3 *)
mov mem0_36 v_add21_1_18;
(*   %arrayidx9.1.19 = getelementptr inbounds i16, i16* %r, i64 83 *)
(*   %294 = load i16, i16* %arrayidx9.1.19, align 2, !tbaa !3 *)
mov v294 mem0_166;
(*   %conv1.i.1.19 = sext i16 %294 to i32 *)
cast v_conv1_i_1_19@sint32 v294@sint16;
(*   %mul.i.1.19 = mul nsw i32 %conv1.i.1.19, -359 *)
mul v_mul_i_1_19 v_conv1_i_1_19 (-359)@sint32;
(*   %call.i.1.19 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.19) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_19, v_call_i_1_19);
(*   %arrayidx11.1.19 = getelementptr inbounds i16, i16* %r, i64 19 *)
(*   %295 = load i16, i16* %arrayidx11.1.19, align 2, !tbaa !3 *)
mov v295 mem0_38;
(*   %sub.1.19 = sub i16 %295, %call.i.1.19 *)
sub v_sub_1_19 v295 v_call_i_1_19;
(*   store i16 %sub.1.19, i16* %arrayidx9.1.19, align 2, !tbaa !3 *)
mov mem0_166 v_sub_1_19;
(*   %add21.1.19 = add i16 %295, %call.i.1.19 *)
add v_add21_1_19 v295 v_call_i_1_19;
(*   store i16 %add21.1.19, i16* %arrayidx11.1.19, align 2, !tbaa !3 *)
mov mem0_38 v_add21_1_19;
(*   %arrayidx9.1.20 = getelementptr inbounds i16, i16* %r, i64 84 *)
(*   %296 = load i16, i16* %arrayidx9.1.20, align 2, !tbaa !3 *)
mov v296 mem0_168;
(*   %conv1.i.1.20 = sext i16 %296 to i32 *)
cast v_conv1_i_1_20@sint32 v296@sint16;
(*   %mul.i.1.20 = mul nsw i32 %conv1.i.1.20, -359 *)
mul v_mul_i_1_20 v_conv1_i_1_20 (-359)@sint32;
(*   %call.i.1.20 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.20) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_20, v_call_i_1_20);
(*   %arrayidx11.1.20 = getelementptr inbounds i16, i16* %r, i64 20 *)
(*   %297 = load i16, i16* %arrayidx11.1.20, align 2, !tbaa !3 *)
mov v297 mem0_40;
(*   %sub.1.20 = sub i16 %297, %call.i.1.20 *)
sub v_sub_1_20 v297 v_call_i_1_20;
(*   store i16 %sub.1.20, i16* %arrayidx9.1.20, align 2, !tbaa !3 *)
mov mem0_168 v_sub_1_20;
(*   %add21.1.20 = add i16 %297, %call.i.1.20 *)
add v_add21_1_20 v297 v_call_i_1_20;
(*   store i16 %add21.1.20, i16* %arrayidx11.1.20, align 2, !tbaa !3 *)
mov mem0_40 v_add21_1_20;
(*   %arrayidx9.1.21 = getelementptr inbounds i16, i16* %r, i64 85 *)
(*   %298 = load i16, i16* %arrayidx9.1.21, align 2, !tbaa !3 *)
mov v298 mem0_170;
(*   %conv1.i.1.21 = sext i16 %298 to i32 *)
cast v_conv1_i_1_21@sint32 v298@sint16;
(*   %mul.i.1.21 = mul nsw i32 %conv1.i.1.21, -359 *)
mul v_mul_i_1_21 v_conv1_i_1_21 (-359)@sint32;
(*   %call.i.1.21 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.21) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_21, v_call_i_1_21);
(*   %arrayidx11.1.21 = getelementptr inbounds i16, i16* %r, i64 21 *)
(*   %299 = load i16, i16* %arrayidx11.1.21, align 2, !tbaa !3 *)
mov v299 mem0_42;
(*   %sub.1.21 = sub i16 %299, %call.i.1.21 *)
sub v_sub_1_21 v299 v_call_i_1_21;
(*   store i16 %sub.1.21, i16* %arrayidx9.1.21, align 2, !tbaa !3 *)
mov mem0_170 v_sub_1_21;
(*   %add21.1.21 = add i16 %299, %call.i.1.21 *)
add v_add21_1_21 v299 v_call_i_1_21;
(*   store i16 %add21.1.21, i16* %arrayidx11.1.21, align 2, !tbaa !3 *)
mov mem0_42 v_add21_1_21;
(*   %arrayidx9.1.22 = getelementptr inbounds i16, i16* %r, i64 86 *)
(*   %300 = load i16, i16* %arrayidx9.1.22, align 2, !tbaa !3 *)
mov v300 mem0_172;
(*   %conv1.i.1.22 = sext i16 %300 to i32 *)
cast v_conv1_i_1_22@sint32 v300@sint16;
(*   %mul.i.1.22 = mul nsw i32 %conv1.i.1.22, -359 *)
mul v_mul_i_1_22 v_conv1_i_1_22 (-359)@sint32;
(*   %call.i.1.22 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.22) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_22, v_call_i_1_22);
(*   %arrayidx11.1.22 = getelementptr inbounds i16, i16* %r, i64 22 *)
(*   %301 = load i16, i16* %arrayidx11.1.22, align 2, !tbaa !3 *)
mov v301 mem0_44;
(*   %sub.1.22 = sub i16 %301, %call.i.1.22 *)
sub v_sub_1_22 v301 v_call_i_1_22;
(*   store i16 %sub.1.22, i16* %arrayidx9.1.22, align 2, !tbaa !3 *)
mov mem0_172 v_sub_1_22;
(*   %add21.1.22 = add i16 %301, %call.i.1.22 *)
add v_add21_1_22 v301 v_call_i_1_22;
(*   store i16 %add21.1.22, i16* %arrayidx11.1.22, align 2, !tbaa !3 *)
mov mem0_44 v_add21_1_22;
(*   %arrayidx9.1.23 = getelementptr inbounds i16, i16* %r, i64 87 *)
(*   %302 = load i16, i16* %arrayidx9.1.23, align 2, !tbaa !3 *)
mov v302 mem0_174;
(*   %conv1.i.1.23 = sext i16 %302 to i32 *)
cast v_conv1_i_1_23@sint32 v302@sint16;
(*   %mul.i.1.23 = mul nsw i32 %conv1.i.1.23, -359 *)
mul v_mul_i_1_23 v_conv1_i_1_23 (-359)@sint32;
(*   %call.i.1.23 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.23) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_23, v_call_i_1_23);
(*   %arrayidx11.1.23 = getelementptr inbounds i16, i16* %r, i64 23 *)
(*   %303 = load i16, i16* %arrayidx11.1.23, align 2, !tbaa !3 *)
mov v303 mem0_46;
(*   %sub.1.23 = sub i16 %303, %call.i.1.23 *)
sub v_sub_1_23 v303 v_call_i_1_23;
(*   store i16 %sub.1.23, i16* %arrayidx9.1.23, align 2, !tbaa !3 *)
mov mem0_174 v_sub_1_23;
(*   %add21.1.23 = add i16 %303, %call.i.1.23 *)
add v_add21_1_23 v303 v_call_i_1_23;
(*   store i16 %add21.1.23, i16* %arrayidx11.1.23, align 2, !tbaa !3 *)
mov mem0_46 v_add21_1_23;
(*   %arrayidx9.1.24 = getelementptr inbounds i16, i16* %r, i64 88 *)
(*   %304 = load i16, i16* %arrayidx9.1.24, align 2, !tbaa !3 *)
mov v304 mem0_176;
(*   %conv1.i.1.24 = sext i16 %304 to i32 *)
cast v_conv1_i_1_24@sint32 v304@sint16;
(*   %mul.i.1.24 = mul nsw i32 %conv1.i.1.24, -359 *)
mul v_mul_i_1_24 v_conv1_i_1_24 (-359)@sint32;
(*   %call.i.1.24 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.24) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_24, v_call_i_1_24);
(*   %arrayidx11.1.24 = getelementptr inbounds i16, i16* %r, i64 24 *)
(*   %305 = load i16, i16* %arrayidx11.1.24, align 2, !tbaa !3 *)
mov v305 mem0_48;
(*   %sub.1.24 = sub i16 %305, %call.i.1.24 *)
sub v_sub_1_24 v305 v_call_i_1_24;
(*   store i16 %sub.1.24, i16* %arrayidx9.1.24, align 2, !tbaa !3 *)
mov mem0_176 v_sub_1_24;
(*   %add21.1.24 = add i16 %305, %call.i.1.24 *)
add v_add21_1_24 v305 v_call_i_1_24;
(*   store i16 %add21.1.24, i16* %arrayidx11.1.24, align 2, !tbaa !3 *)
mov mem0_48 v_add21_1_24;
(*   %arrayidx9.1.25 = getelementptr inbounds i16, i16* %r, i64 89 *)
(*   %306 = load i16, i16* %arrayidx9.1.25, align 2, !tbaa !3 *)
mov v306 mem0_178;
(*   %conv1.i.1.25 = sext i16 %306 to i32 *)
cast v_conv1_i_1_25@sint32 v306@sint16;
(*   %mul.i.1.25 = mul nsw i32 %conv1.i.1.25, -359 *)
mul v_mul_i_1_25 v_conv1_i_1_25 (-359)@sint32;
(*   %call.i.1.25 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.25) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_25, v_call_i_1_25);
(*   %arrayidx11.1.25 = getelementptr inbounds i16, i16* %r, i64 25 *)
(*   %307 = load i16, i16* %arrayidx11.1.25, align 2, !tbaa !3 *)
mov v307 mem0_50;
(*   %sub.1.25 = sub i16 %307, %call.i.1.25 *)
sub v_sub_1_25 v307 v_call_i_1_25;
(*   store i16 %sub.1.25, i16* %arrayidx9.1.25, align 2, !tbaa !3 *)
mov mem0_178 v_sub_1_25;
(*   %add21.1.25 = add i16 %307, %call.i.1.25 *)
add v_add21_1_25 v307 v_call_i_1_25;
(*   store i16 %add21.1.25, i16* %arrayidx11.1.25, align 2, !tbaa !3 *)
mov mem0_50 v_add21_1_25;
(*   %arrayidx9.1.26 = getelementptr inbounds i16, i16* %r, i64 90 *)
(*   %308 = load i16, i16* %arrayidx9.1.26, align 2, !tbaa !3 *)
mov v308 mem0_180;
(*   %conv1.i.1.26 = sext i16 %308 to i32 *)
cast v_conv1_i_1_26@sint32 v308@sint16;
(*   %mul.i.1.26 = mul nsw i32 %conv1.i.1.26, -359 *)
mul v_mul_i_1_26 v_conv1_i_1_26 (-359)@sint32;
(*   %call.i.1.26 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.26) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_26, v_call_i_1_26);
(*   %arrayidx11.1.26 = getelementptr inbounds i16, i16* %r, i64 26 *)
(*   %309 = load i16, i16* %arrayidx11.1.26, align 2, !tbaa !3 *)
mov v309 mem0_52;
(*   %sub.1.26 = sub i16 %309, %call.i.1.26 *)
sub v_sub_1_26 v309 v_call_i_1_26;
(*   store i16 %sub.1.26, i16* %arrayidx9.1.26, align 2, !tbaa !3 *)
mov mem0_180 v_sub_1_26;
(*   %add21.1.26 = add i16 %309, %call.i.1.26 *)
add v_add21_1_26 v309 v_call_i_1_26;
(*   store i16 %add21.1.26, i16* %arrayidx11.1.26, align 2, !tbaa !3 *)
mov mem0_52 v_add21_1_26;
(*   %arrayidx9.1.27 = getelementptr inbounds i16, i16* %r, i64 91 *)
(*   %310 = load i16, i16* %arrayidx9.1.27, align 2, !tbaa !3 *)
mov v310 mem0_182;
(*   %conv1.i.1.27 = sext i16 %310 to i32 *)
cast v_conv1_i_1_27@sint32 v310@sint16;
(*   %mul.i.1.27 = mul nsw i32 %conv1.i.1.27, -359 *)
mul v_mul_i_1_27 v_conv1_i_1_27 (-359)@sint32;
(*   %call.i.1.27 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.27) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_27, v_call_i_1_27);
(*   %arrayidx11.1.27 = getelementptr inbounds i16, i16* %r, i64 27 *)
(*   %311 = load i16, i16* %arrayidx11.1.27, align 2, !tbaa !3 *)
mov v311 mem0_54;
(*   %sub.1.27 = sub i16 %311, %call.i.1.27 *)
sub v_sub_1_27 v311 v_call_i_1_27;
(*   store i16 %sub.1.27, i16* %arrayidx9.1.27, align 2, !tbaa !3 *)
mov mem0_182 v_sub_1_27;
(*   %add21.1.27 = add i16 %311, %call.i.1.27 *)
add v_add21_1_27 v311 v_call_i_1_27;
(*   store i16 %add21.1.27, i16* %arrayidx11.1.27, align 2, !tbaa !3 *)
mov mem0_54 v_add21_1_27;
(*   %arrayidx9.1.28 = getelementptr inbounds i16, i16* %r, i64 92 *)
(*   %312 = load i16, i16* %arrayidx9.1.28, align 2, !tbaa !3 *)
mov v312 mem0_184;
(*   %conv1.i.1.28 = sext i16 %312 to i32 *)
cast v_conv1_i_1_28@sint32 v312@sint16;
(*   %mul.i.1.28 = mul nsw i32 %conv1.i.1.28, -359 *)
mul v_mul_i_1_28 v_conv1_i_1_28 (-359)@sint32;
(*   %call.i.1.28 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.28) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_28, v_call_i_1_28);
(*   %arrayidx11.1.28 = getelementptr inbounds i16, i16* %r, i64 28 *)
(*   %313 = load i16, i16* %arrayidx11.1.28, align 2, !tbaa !3 *)
mov v313 mem0_56;
(*   %sub.1.28 = sub i16 %313, %call.i.1.28 *)
sub v_sub_1_28 v313 v_call_i_1_28;
(*   store i16 %sub.1.28, i16* %arrayidx9.1.28, align 2, !tbaa !3 *)
mov mem0_184 v_sub_1_28;
(*   %add21.1.28 = add i16 %313, %call.i.1.28 *)
add v_add21_1_28 v313 v_call_i_1_28;
(*   store i16 %add21.1.28, i16* %arrayidx11.1.28, align 2, !tbaa !3 *)
mov mem0_56 v_add21_1_28;
(*   %arrayidx9.1.29 = getelementptr inbounds i16, i16* %r, i64 93 *)
(*   %314 = load i16, i16* %arrayidx9.1.29, align 2, !tbaa !3 *)
mov v314 mem0_186;
(*   %conv1.i.1.29 = sext i16 %314 to i32 *)
cast v_conv1_i_1_29@sint32 v314@sint16;
(*   %mul.i.1.29 = mul nsw i32 %conv1.i.1.29, -359 *)
mul v_mul_i_1_29 v_conv1_i_1_29 (-359)@sint32;
(*   %call.i.1.29 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.29) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_29, v_call_i_1_29);
(*   %arrayidx11.1.29 = getelementptr inbounds i16, i16* %r, i64 29 *)
(*   %315 = load i16, i16* %arrayidx11.1.29, align 2, !tbaa !3 *)
mov v315 mem0_58;
(*   %sub.1.29 = sub i16 %315, %call.i.1.29 *)
sub v_sub_1_29 v315 v_call_i_1_29;
(*   store i16 %sub.1.29, i16* %arrayidx9.1.29, align 2, !tbaa !3 *)
mov mem0_186 v_sub_1_29;
(*   %add21.1.29 = add i16 %315, %call.i.1.29 *)
add v_add21_1_29 v315 v_call_i_1_29;
(*   store i16 %add21.1.29, i16* %arrayidx11.1.29, align 2, !tbaa !3 *)
mov mem0_58 v_add21_1_29;
(*   %arrayidx9.1.30 = getelementptr inbounds i16, i16* %r, i64 94 *)
(*   %316 = load i16, i16* %arrayidx9.1.30, align 2, !tbaa !3 *)
mov v316 mem0_188;
(*   %conv1.i.1.30 = sext i16 %316 to i32 *)
cast v_conv1_i_1_30@sint32 v316@sint16;
(*   %mul.i.1.30 = mul nsw i32 %conv1.i.1.30, -359 *)
mul v_mul_i_1_30 v_conv1_i_1_30 (-359)@sint32;
(*   %call.i.1.30 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.30) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_30, v_call_i_1_30);
(*   %arrayidx11.1.30 = getelementptr inbounds i16, i16* %r, i64 30 *)
(*   %317 = load i16, i16* %arrayidx11.1.30, align 2, !tbaa !3 *)
mov v317 mem0_60;
(*   %sub.1.30 = sub i16 %317, %call.i.1.30 *)
sub v_sub_1_30 v317 v_call_i_1_30;
(*   store i16 %sub.1.30, i16* %arrayidx9.1.30, align 2, !tbaa !3 *)
mov mem0_188 v_sub_1_30;
(*   %add21.1.30 = add i16 %317, %call.i.1.30 *)
add v_add21_1_30 v317 v_call_i_1_30;
(*   store i16 %add21.1.30, i16* %arrayidx11.1.30, align 2, !tbaa !3 *)
mov mem0_60 v_add21_1_30;
(*   %arrayidx9.1.31 = getelementptr inbounds i16, i16* %r, i64 95 *)
(*   %318 = load i16, i16* %arrayidx9.1.31, align 2, !tbaa !3 *)
mov v318 mem0_190;
(*   %conv1.i.1.31 = sext i16 %318 to i32 *)
cast v_conv1_i_1_31@sint32 v318@sint16;
(*   %mul.i.1.31 = mul nsw i32 %conv1.i.1.31, -359 *)
mul v_mul_i_1_31 v_conv1_i_1_31 (-359)@sint32;
(*   %call.i.1.31 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.31) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_31, v_call_i_1_31);
(*   %arrayidx11.1.31 = getelementptr inbounds i16, i16* %r, i64 31 *)
(*   %319 = load i16, i16* %arrayidx11.1.31, align 2, !tbaa !3 *)
mov v319 mem0_62;
(*   %sub.1.31 = sub i16 %319, %call.i.1.31 *)
sub v_sub_1_31 v319 v_call_i_1_31;
(*   store i16 %sub.1.31, i16* %arrayidx9.1.31, align 2, !tbaa !3 *)
mov mem0_190 v_sub_1_31;
(*   %add21.1.31 = add i16 %319, %call.i.1.31 *)
add v_add21_1_31 v319 v_call_i_1_31;
(*   store i16 %add21.1.31, i16* %arrayidx11.1.31, align 2, !tbaa !3 *)
mov mem0_62 v_add21_1_31;
(*   %arrayidx9.1.32 = getelementptr inbounds i16, i16* %r, i64 96 *)
(*   %320 = load i16, i16* %arrayidx9.1.32, align 2, !tbaa !3 *)
mov v320 mem0_192;
(*   %conv1.i.1.32 = sext i16 %320 to i32 *)
cast v_conv1_i_1_32@sint32 v320@sint16;
(*   %mul.i.1.32 = mul nsw i32 %conv1.i.1.32, -359 *)
mul v_mul_i_1_32 v_conv1_i_1_32 (-359)@sint32;
(*   %call.i.1.32 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.32) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_32, v_call_i_1_32);
(*   %arrayidx11.1.32 = getelementptr inbounds i16, i16* %r, i64 32 *)
(*   %321 = load i16, i16* %arrayidx11.1.32, align 2, !tbaa !3 *)
mov v321 mem0_64;
(*   %sub.1.32 = sub i16 %321, %call.i.1.32 *)
sub v_sub_1_32 v321 v_call_i_1_32;
(*   store i16 %sub.1.32, i16* %arrayidx9.1.32, align 2, !tbaa !3 *)
mov mem0_192 v_sub_1_32;
(*   %add21.1.32 = add i16 %321, %call.i.1.32 *)
add v_add21_1_32 v321 v_call_i_1_32;
(*   store i16 %add21.1.32, i16* %arrayidx11.1.32, align 2, !tbaa !3 *)
mov mem0_64 v_add21_1_32;
(*   %arrayidx9.1.33 = getelementptr inbounds i16, i16* %r, i64 97 *)
(*   %322 = load i16, i16* %arrayidx9.1.33, align 2, !tbaa !3 *)
mov v322 mem0_194;
(*   %conv1.i.1.33 = sext i16 %322 to i32 *)
cast v_conv1_i_1_33@sint32 v322@sint16;
(*   %mul.i.1.33 = mul nsw i32 %conv1.i.1.33, -359 *)
mul v_mul_i_1_33 v_conv1_i_1_33 (-359)@sint32;
(*   %call.i.1.33 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.33) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_33, v_call_i_1_33);
(*   %arrayidx11.1.33 = getelementptr inbounds i16, i16* %r, i64 33 *)
(*   %323 = load i16, i16* %arrayidx11.1.33, align 2, !tbaa !3 *)
mov v323 mem0_66;
(*   %sub.1.33 = sub i16 %323, %call.i.1.33 *)
sub v_sub_1_33 v323 v_call_i_1_33;
(*   store i16 %sub.1.33, i16* %arrayidx9.1.33, align 2, !tbaa !3 *)
mov mem0_194 v_sub_1_33;
(*   %add21.1.33 = add i16 %323, %call.i.1.33 *)
add v_add21_1_33 v323 v_call_i_1_33;
(*   store i16 %add21.1.33, i16* %arrayidx11.1.33, align 2, !tbaa !3 *)
mov mem0_66 v_add21_1_33;
(*   %arrayidx9.1.34 = getelementptr inbounds i16, i16* %r, i64 98 *)
(*   %324 = load i16, i16* %arrayidx9.1.34, align 2, !tbaa !3 *)
mov v324 mem0_196;
(*   %conv1.i.1.34 = sext i16 %324 to i32 *)
cast v_conv1_i_1_34@sint32 v324@sint16;
(*   %mul.i.1.34 = mul nsw i32 %conv1.i.1.34, -359 *)
mul v_mul_i_1_34 v_conv1_i_1_34 (-359)@sint32;
(*   %call.i.1.34 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.34) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_34, v_call_i_1_34);
(*   %arrayidx11.1.34 = getelementptr inbounds i16, i16* %r, i64 34 *)
(*   %325 = load i16, i16* %arrayidx11.1.34, align 2, !tbaa !3 *)
mov v325 mem0_68;
(*   %sub.1.34 = sub i16 %325, %call.i.1.34 *)
sub v_sub_1_34 v325 v_call_i_1_34;
(*   store i16 %sub.1.34, i16* %arrayidx9.1.34, align 2, !tbaa !3 *)
mov mem0_196 v_sub_1_34;
(*   %add21.1.34 = add i16 %325, %call.i.1.34 *)
add v_add21_1_34 v325 v_call_i_1_34;
(*   store i16 %add21.1.34, i16* %arrayidx11.1.34, align 2, !tbaa !3 *)
mov mem0_68 v_add21_1_34;
(*   %arrayidx9.1.35 = getelementptr inbounds i16, i16* %r, i64 99 *)
(*   %326 = load i16, i16* %arrayidx9.1.35, align 2, !tbaa !3 *)
mov v326 mem0_198;
(*   %conv1.i.1.35 = sext i16 %326 to i32 *)
cast v_conv1_i_1_35@sint32 v326@sint16;
(*   %mul.i.1.35 = mul nsw i32 %conv1.i.1.35, -359 *)
mul v_mul_i_1_35 v_conv1_i_1_35 (-359)@sint32;
(*   %call.i.1.35 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.35) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_35, v_call_i_1_35);
(*   %arrayidx11.1.35 = getelementptr inbounds i16, i16* %r, i64 35 *)
(*   %327 = load i16, i16* %arrayidx11.1.35, align 2, !tbaa !3 *)
mov v327 mem0_70;
(*   %sub.1.35 = sub i16 %327, %call.i.1.35 *)
sub v_sub_1_35 v327 v_call_i_1_35;
(*   store i16 %sub.1.35, i16* %arrayidx9.1.35, align 2, !tbaa !3 *)
mov mem0_198 v_sub_1_35;
(*   %add21.1.35 = add i16 %327, %call.i.1.35 *)
add v_add21_1_35 v327 v_call_i_1_35;
(*   store i16 %add21.1.35, i16* %arrayidx11.1.35, align 2, !tbaa !3 *)
mov mem0_70 v_add21_1_35;
(*   %arrayidx9.1.36 = getelementptr inbounds i16, i16* %r, i64 100 *)
(*   %328 = load i16, i16* %arrayidx9.1.36, align 2, !tbaa !3 *)
mov v328 mem0_200;
(*   %conv1.i.1.36 = sext i16 %328 to i32 *)
cast v_conv1_i_1_36@sint32 v328@sint16;
(*   %mul.i.1.36 = mul nsw i32 %conv1.i.1.36, -359 *)
mul v_mul_i_1_36 v_conv1_i_1_36 (-359)@sint32;
(*   %call.i.1.36 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.36) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_36, v_call_i_1_36);
(*   %arrayidx11.1.36 = getelementptr inbounds i16, i16* %r, i64 36 *)
(*   %329 = load i16, i16* %arrayidx11.1.36, align 2, !tbaa !3 *)
mov v329 mem0_72;
(*   %sub.1.36 = sub i16 %329, %call.i.1.36 *)
sub v_sub_1_36 v329 v_call_i_1_36;
(*   store i16 %sub.1.36, i16* %arrayidx9.1.36, align 2, !tbaa !3 *)
mov mem0_200 v_sub_1_36;
(*   %add21.1.36 = add i16 %329, %call.i.1.36 *)
add v_add21_1_36 v329 v_call_i_1_36;
(*   store i16 %add21.1.36, i16* %arrayidx11.1.36, align 2, !tbaa !3 *)
mov mem0_72 v_add21_1_36;
(*   %arrayidx9.1.37 = getelementptr inbounds i16, i16* %r, i64 101 *)
(*   %330 = load i16, i16* %arrayidx9.1.37, align 2, !tbaa !3 *)
mov v330 mem0_202;
(*   %conv1.i.1.37 = sext i16 %330 to i32 *)
cast v_conv1_i_1_37@sint32 v330@sint16;
(*   %mul.i.1.37 = mul nsw i32 %conv1.i.1.37, -359 *)
mul v_mul_i_1_37 v_conv1_i_1_37 (-359)@sint32;
(*   %call.i.1.37 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.37) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_37, v_call_i_1_37);
(*   %arrayidx11.1.37 = getelementptr inbounds i16, i16* %r, i64 37 *)
(*   %331 = load i16, i16* %arrayidx11.1.37, align 2, !tbaa !3 *)
mov v331 mem0_74;
(*   %sub.1.37 = sub i16 %331, %call.i.1.37 *)
sub v_sub_1_37 v331 v_call_i_1_37;
(*   store i16 %sub.1.37, i16* %arrayidx9.1.37, align 2, !tbaa !3 *)
mov mem0_202 v_sub_1_37;
(*   %add21.1.37 = add i16 %331, %call.i.1.37 *)
add v_add21_1_37 v331 v_call_i_1_37;
(*   store i16 %add21.1.37, i16* %arrayidx11.1.37, align 2, !tbaa !3 *)
mov mem0_74 v_add21_1_37;
(*   %arrayidx9.1.38 = getelementptr inbounds i16, i16* %r, i64 102 *)
(*   %332 = load i16, i16* %arrayidx9.1.38, align 2, !tbaa !3 *)
mov v332 mem0_204;
(*   %conv1.i.1.38 = sext i16 %332 to i32 *)
cast v_conv1_i_1_38@sint32 v332@sint16;
(*   %mul.i.1.38 = mul nsw i32 %conv1.i.1.38, -359 *)
mul v_mul_i_1_38 v_conv1_i_1_38 (-359)@sint32;
(*   %call.i.1.38 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.38) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_38, v_call_i_1_38);
(*   %arrayidx11.1.38 = getelementptr inbounds i16, i16* %r, i64 38 *)
(*   %333 = load i16, i16* %arrayidx11.1.38, align 2, !tbaa !3 *)
mov v333 mem0_76;
(*   %sub.1.38 = sub i16 %333, %call.i.1.38 *)
sub v_sub_1_38 v333 v_call_i_1_38;
(*   store i16 %sub.1.38, i16* %arrayidx9.1.38, align 2, !tbaa !3 *)
mov mem0_204 v_sub_1_38;
(*   %add21.1.38 = add i16 %333, %call.i.1.38 *)
add v_add21_1_38 v333 v_call_i_1_38;
(*   store i16 %add21.1.38, i16* %arrayidx11.1.38, align 2, !tbaa !3 *)
mov mem0_76 v_add21_1_38;
(*   %arrayidx9.1.39 = getelementptr inbounds i16, i16* %r, i64 103 *)
(*   %334 = load i16, i16* %arrayidx9.1.39, align 2, !tbaa !3 *)
mov v334 mem0_206;
(*   %conv1.i.1.39 = sext i16 %334 to i32 *)
cast v_conv1_i_1_39@sint32 v334@sint16;
(*   %mul.i.1.39 = mul nsw i32 %conv1.i.1.39, -359 *)
mul v_mul_i_1_39 v_conv1_i_1_39 (-359)@sint32;
(*   %call.i.1.39 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.39) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_39, v_call_i_1_39);
(*   %arrayidx11.1.39 = getelementptr inbounds i16, i16* %r, i64 39 *)
(*   %335 = load i16, i16* %arrayidx11.1.39, align 2, !tbaa !3 *)
mov v335 mem0_78;
(*   %sub.1.39 = sub i16 %335, %call.i.1.39 *)
sub v_sub_1_39 v335 v_call_i_1_39;
(*   store i16 %sub.1.39, i16* %arrayidx9.1.39, align 2, !tbaa !3 *)
mov mem0_206 v_sub_1_39;
(*   %add21.1.39 = add i16 %335, %call.i.1.39 *)
add v_add21_1_39 v335 v_call_i_1_39;
(*   store i16 %add21.1.39, i16* %arrayidx11.1.39, align 2, !tbaa !3 *)
mov mem0_78 v_add21_1_39;
(*   %arrayidx9.1.40 = getelementptr inbounds i16, i16* %r, i64 104 *)
(*   %336 = load i16, i16* %arrayidx9.1.40, align 2, !tbaa !3 *)
mov v336 mem0_208;
(*   %conv1.i.1.40 = sext i16 %336 to i32 *)
cast v_conv1_i_1_40@sint32 v336@sint16;
(*   %mul.i.1.40 = mul nsw i32 %conv1.i.1.40, -359 *)
mul v_mul_i_1_40 v_conv1_i_1_40 (-359)@sint32;
(*   %call.i.1.40 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.40) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_40, v_call_i_1_40);
(*   %arrayidx11.1.40 = getelementptr inbounds i16, i16* %r, i64 40 *)
(*   %337 = load i16, i16* %arrayidx11.1.40, align 2, !tbaa !3 *)
mov v337 mem0_80;
(*   %sub.1.40 = sub i16 %337, %call.i.1.40 *)
sub v_sub_1_40 v337 v_call_i_1_40;
(*   store i16 %sub.1.40, i16* %arrayidx9.1.40, align 2, !tbaa !3 *)
mov mem0_208 v_sub_1_40;
(*   %add21.1.40 = add i16 %337, %call.i.1.40 *)
add v_add21_1_40 v337 v_call_i_1_40;
(*   store i16 %add21.1.40, i16* %arrayidx11.1.40, align 2, !tbaa !3 *)
mov mem0_80 v_add21_1_40;
(*   %arrayidx9.1.41 = getelementptr inbounds i16, i16* %r, i64 105 *)
(*   %338 = load i16, i16* %arrayidx9.1.41, align 2, !tbaa !3 *)
mov v338 mem0_210;
(*   %conv1.i.1.41 = sext i16 %338 to i32 *)
cast v_conv1_i_1_41@sint32 v338@sint16;
(*   %mul.i.1.41 = mul nsw i32 %conv1.i.1.41, -359 *)
mul v_mul_i_1_41 v_conv1_i_1_41 (-359)@sint32;
(*   %call.i.1.41 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.41) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_41, v_call_i_1_41);
(*   %arrayidx11.1.41 = getelementptr inbounds i16, i16* %r, i64 41 *)
(*   %339 = load i16, i16* %arrayidx11.1.41, align 2, !tbaa !3 *)
mov v339 mem0_82;
(*   %sub.1.41 = sub i16 %339, %call.i.1.41 *)
sub v_sub_1_41 v339 v_call_i_1_41;
(*   store i16 %sub.1.41, i16* %arrayidx9.1.41, align 2, !tbaa !3 *)
mov mem0_210 v_sub_1_41;
(*   %add21.1.41 = add i16 %339, %call.i.1.41 *)
add v_add21_1_41 v339 v_call_i_1_41;
(*   store i16 %add21.1.41, i16* %arrayidx11.1.41, align 2, !tbaa !3 *)
mov mem0_82 v_add21_1_41;
(*   %arrayidx9.1.42 = getelementptr inbounds i16, i16* %r, i64 106 *)
(*   %340 = load i16, i16* %arrayidx9.1.42, align 2, !tbaa !3 *)
mov v340 mem0_212;
(*   %conv1.i.1.42 = sext i16 %340 to i32 *)
cast v_conv1_i_1_42@sint32 v340@sint16;
(*   %mul.i.1.42 = mul nsw i32 %conv1.i.1.42, -359 *)
mul v_mul_i_1_42 v_conv1_i_1_42 (-359)@sint32;
(*   %call.i.1.42 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.42) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_42, v_call_i_1_42);
(*   %arrayidx11.1.42 = getelementptr inbounds i16, i16* %r, i64 42 *)
(*   %341 = load i16, i16* %arrayidx11.1.42, align 2, !tbaa !3 *)
mov v341 mem0_84;
(*   %sub.1.42 = sub i16 %341, %call.i.1.42 *)
sub v_sub_1_42 v341 v_call_i_1_42;
(*   store i16 %sub.1.42, i16* %arrayidx9.1.42, align 2, !tbaa !3 *)
mov mem0_212 v_sub_1_42;
(*   %add21.1.42 = add i16 %341, %call.i.1.42 *)
add v_add21_1_42 v341 v_call_i_1_42;
(*   store i16 %add21.1.42, i16* %arrayidx11.1.42, align 2, !tbaa !3 *)
mov mem0_84 v_add21_1_42;
(*   %arrayidx9.1.43 = getelementptr inbounds i16, i16* %r, i64 107 *)
(*   %342 = load i16, i16* %arrayidx9.1.43, align 2, !tbaa !3 *)
mov v342 mem0_214;
(*   %conv1.i.1.43 = sext i16 %342 to i32 *)
cast v_conv1_i_1_43@sint32 v342@sint16;
(*   %mul.i.1.43 = mul nsw i32 %conv1.i.1.43, -359 *)
mul v_mul_i_1_43 v_conv1_i_1_43 (-359)@sint32;
(*   %call.i.1.43 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.43) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_43, v_call_i_1_43);
(*   %arrayidx11.1.43 = getelementptr inbounds i16, i16* %r, i64 43 *)
(*   %343 = load i16, i16* %arrayidx11.1.43, align 2, !tbaa !3 *)
mov v343 mem0_86;
(*   %sub.1.43 = sub i16 %343, %call.i.1.43 *)
sub v_sub_1_43 v343 v_call_i_1_43;
(*   store i16 %sub.1.43, i16* %arrayidx9.1.43, align 2, !tbaa !3 *)
mov mem0_214 v_sub_1_43;
(*   %add21.1.43 = add i16 %343, %call.i.1.43 *)
add v_add21_1_43 v343 v_call_i_1_43;
(*   store i16 %add21.1.43, i16* %arrayidx11.1.43, align 2, !tbaa !3 *)
mov mem0_86 v_add21_1_43;
(*   %arrayidx9.1.44 = getelementptr inbounds i16, i16* %r, i64 108 *)
(*   %344 = load i16, i16* %arrayidx9.1.44, align 2, !tbaa !3 *)
mov v344 mem0_216;
(*   %conv1.i.1.44 = sext i16 %344 to i32 *)
cast v_conv1_i_1_44@sint32 v344@sint16;
(*   %mul.i.1.44 = mul nsw i32 %conv1.i.1.44, -359 *)
mul v_mul_i_1_44 v_conv1_i_1_44 (-359)@sint32;
(*   %call.i.1.44 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.44) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_44, v_call_i_1_44);
(*   %arrayidx11.1.44 = getelementptr inbounds i16, i16* %r, i64 44 *)
(*   %345 = load i16, i16* %arrayidx11.1.44, align 2, !tbaa !3 *)
mov v345 mem0_88;
(*   %sub.1.44 = sub i16 %345, %call.i.1.44 *)
sub v_sub_1_44 v345 v_call_i_1_44;
(*   store i16 %sub.1.44, i16* %arrayidx9.1.44, align 2, !tbaa !3 *)
mov mem0_216 v_sub_1_44;
(*   %add21.1.44 = add i16 %345, %call.i.1.44 *)
add v_add21_1_44 v345 v_call_i_1_44;
(*   store i16 %add21.1.44, i16* %arrayidx11.1.44, align 2, !tbaa !3 *)
mov mem0_88 v_add21_1_44;
(*   %arrayidx9.1.45 = getelementptr inbounds i16, i16* %r, i64 109 *)
(*   %346 = load i16, i16* %arrayidx9.1.45, align 2, !tbaa !3 *)
mov v346 mem0_218;
(*   %conv1.i.1.45 = sext i16 %346 to i32 *)
cast v_conv1_i_1_45@sint32 v346@sint16;
(*   %mul.i.1.45 = mul nsw i32 %conv1.i.1.45, -359 *)
mul v_mul_i_1_45 v_conv1_i_1_45 (-359)@sint32;
(*   %call.i.1.45 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.45) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_45, v_call_i_1_45);
(*   %arrayidx11.1.45 = getelementptr inbounds i16, i16* %r, i64 45 *)
(*   %347 = load i16, i16* %arrayidx11.1.45, align 2, !tbaa !3 *)
mov v347 mem0_90;
(*   %sub.1.45 = sub i16 %347, %call.i.1.45 *)
sub v_sub_1_45 v347 v_call_i_1_45;
(*   store i16 %sub.1.45, i16* %arrayidx9.1.45, align 2, !tbaa !3 *)
mov mem0_218 v_sub_1_45;
(*   %add21.1.45 = add i16 %347, %call.i.1.45 *)
add v_add21_1_45 v347 v_call_i_1_45;
(*   store i16 %add21.1.45, i16* %arrayidx11.1.45, align 2, !tbaa !3 *)
mov mem0_90 v_add21_1_45;
(*   %arrayidx9.1.46 = getelementptr inbounds i16, i16* %r, i64 110 *)
(*   %348 = load i16, i16* %arrayidx9.1.46, align 2, !tbaa !3 *)
mov v348 mem0_220;
(*   %conv1.i.1.46 = sext i16 %348 to i32 *)
cast v_conv1_i_1_46@sint32 v348@sint16;
(*   %mul.i.1.46 = mul nsw i32 %conv1.i.1.46, -359 *)
mul v_mul_i_1_46 v_conv1_i_1_46 (-359)@sint32;
(*   %call.i.1.46 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.46) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_46, v_call_i_1_46);
(*   %arrayidx11.1.46 = getelementptr inbounds i16, i16* %r, i64 46 *)
(*   %349 = load i16, i16* %arrayidx11.1.46, align 2, !tbaa !3 *)
mov v349 mem0_92;
(*   %sub.1.46 = sub i16 %349, %call.i.1.46 *)
sub v_sub_1_46 v349 v_call_i_1_46;
(*   store i16 %sub.1.46, i16* %arrayidx9.1.46, align 2, !tbaa !3 *)
mov mem0_220 v_sub_1_46;
(*   %add21.1.46 = add i16 %349, %call.i.1.46 *)
add v_add21_1_46 v349 v_call_i_1_46;
(*   store i16 %add21.1.46, i16* %arrayidx11.1.46, align 2, !tbaa !3 *)
mov mem0_92 v_add21_1_46;
(*   %arrayidx9.1.47 = getelementptr inbounds i16, i16* %r, i64 111 *)
(*   %350 = load i16, i16* %arrayidx9.1.47, align 2, !tbaa !3 *)
mov v350 mem0_222;
(*   %conv1.i.1.47 = sext i16 %350 to i32 *)
cast v_conv1_i_1_47@sint32 v350@sint16;
(*   %mul.i.1.47 = mul nsw i32 %conv1.i.1.47, -359 *)
mul v_mul_i_1_47 v_conv1_i_1_47 (-359)@sint32;
(*   %call.i.1.47 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.47) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_47, v_call_i_1_47);
(*   %arrayidx11.1.47 = getelementptr inbounds i16, i16* %r, i64 47 *)
(*   %351 = load i16, i16* %arrayidx11.1.47, align 2, !tbaa !3 *)
mov v351 mem0_94;
(*   %sub.1.47 = sub i16 %351, %call.i.1.47 *)
sub v_sub_1_47 v351 v_call_i_1_47;
(*   store i16 %sub.1.47, i16* %arrayidx9.1.47, align 2, !tbaa !3 *)
mov mem0_222 v_sub_1_47;
(*   %add21.1.47 = add i16 %351, %call.i.1.47 *)
add v_add21_1_47 v351 v_call_i_1_47;
(*   store i16 %add21.1.47, i16* %arrayidx11.1.47, align 2, !tbaa !3 *)
mov mem0_94 v_add21_1_47;
(*   %arrayidx9.1.48 = getelementptr inbounds i16, i16* %r, i64 112 *)
(*   %352 = load i16, i16* %arrayidx9.1.48, align 2, !tbaa !3 *)
mov v352 mem0_224;
(*   %conv1.i.1.48 = sext i16 %352 to i32 *)
cast v_conv1_i_1_48@sint32 v352@sint16;
(*   %mul.i.1.48 = mul nsw i32 %conv1.i.1.48, -359 *)
mul v_mul_i_1_48 v_conv1_i_1_48 (-359)@sint32;
(*   %call.i.1.48 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.48) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_48, v_call_i_1_48);
(*   %arrayidx11.1.48 = getelementptr inbounds i16, i16* %r, i64 48 *)
(*   %353 = load i16, i16* %arrayidx11.1.48, align 2, !tbaa !3 *)
mov v353 mem0_96;
(*   %sub.1.48 = sub i16 %353, %call.i.1.48 *)
sub v_sub_1_48 v353 v_call_i_1_48;
(*   store i16 %sub.1.48, i16* %arrayidx9.1.48, align 2, !tbaa !3 *)
mov mem0_224 v_sub_1_48;
(*   %add21.1.48 = add i16 %353, %call.i.1.48 *)
add v_add21_1_48 v353 v_call_i_1_48;
(*   store i16 %add21.1.48, i16* %arrayidx11.1.48, align 2, !tbaa !3 *)
mov mem0_96 v_add21_1_48;
(*   %arrayidx9.1.49 = getelementptr inbounds i16, i16* %r, i64 113 *)
(*   %354 = load i16, i16* %arrayidx9.1.49, align 2, !tbaa !3 *)
mov v354 mem0_226;
(*   %conv1.i.1.49 = sext i16 %354 to i32 *)
cast v_conv1_i_1_49@sint32 v354@sint16;
(*   %mul.i.1.49 = mul nsw i32 %conv1.i.1.49, -359 *)
mul v_mul_i_1_49 v_conv1_i_1_49 (-359)@sint32;
(*   %call.i.1.49 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.49) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_49, v_call_i_1_49);
(*   %arrayidx11.1.49 = getelementptr inbounds i16, i16* %r, i64 49 *)
(*   %355 = load i16, i16* %arrayidx11.1.49, align 2, !tbaa !3 *)
mov v355 mem0_98;
(*   %sub.1.49 = sub i16 %355, %call.i.1.49 *)
sub v_sub_1_49 v355 v_call_i_1_49;
(*   store i16 %sub.1.49, i16* %arrayidx9.1.49, align 2, !tbaa !3 *)
mov mem0_226 v_sub_1_49;
(*   %add21.1.49 = add i16 %355, %call.i.1.49 *)
add v_add21_1_49 v355 v_call_i_1_49;
(*   store i16 %add21.1.49, i16* %arrayidx11.1.49, align 2, !tbaa !3 *)
mov mem0_98 v_add21_1_49;
(*   %arrayidx9.1.50 = getelementptr inbounds i16, i16* %r, i64 114 *)
(*   %356 = load i16, i16* %arrayidx9.1.50, align 2, !tbaa !3 *)
mov v356 mem0_228;
(*   %conv1.i.1.50 = sext i16 %356 to i32 *)
cast v_conv1_i_1_50@sint32 v356@sint16;
(*   %mul.i.1.50 = mul nsw i32 %conv1.i.1.50, -359 *)
mul v_mul_i_1_50 v_conv1_i_1_50 (-359)@sint32;
(*   %call.i.1.50 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.50) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_50, v_call_i_1_50);
(*   %arrayidx11.1.50 = getelementptr inbounds i16, i16* %r, i64 50 *)
(*   %357 = load i16, i16* %arrayidx11.1.50, align 2, !tbaa !3 *)
mov v357 mem0_100;
(*   %sub.1.50 = sub i16 %357, %call.i.1.50 *)
sub v_sub_1_50 v357 v_call_i_1_50;
(*   store i16 %sub.1.50, i16* %arrayidx9.1.50, align 2, !tbaa !3 *)
mov mem0_228 v_sub_1_50;
(*   %add21.1.50 = add i16 %357, %call.i.1.50 *)
add v_add21_1_50 v357 v_call_i_1_50;
(*   store i16 %add21.1.50, i16* %arrayidx11.1.50, align 2, !tbaa !3 *)
mov mem0_100 v_add21_1_50;
(*   %arrayidx9.1.51 = getelementptr inbounds i16, i16* %r, i64 115 *)
(*   %358 = load i16, i16* %arrayidx9.1.51, align 2, !tbaa !3 *)
mov v358 mem0_230;
(*   %conv1.i.1.51 = sext i16 %358 to i32 *)
cast v_conv1_i_1_51@sint32 v358@sint16;
(*   %mul.i.1.51 = mul nsw i32 %conv1.i.1.51, -359 *)
mul v_mul_i_1_51 v_conv1_i_1_51 (-359)@sint32;
(*   %call.i.1.51 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.51) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_51, v_call_i_1_51);
(*   %arrayidx11.1.51 = getelementptr inbounds i16, i16* %r, i64 51 *)
(*   %359 = load i16, i16* %arrayidx11.1.51, align 2, !tbaa !3 *)
mov v359 mem0_102;
(*   %sub.1.51 = sub i16 %359, %call.i.1.51 *)
sub v_sub_1_51 v359 v_call_i_1_51;
(*   store i16 %sub.1.51, i16* %arrayidx9.1.51, align 2, !tbaa !3 *)
mov mem0_230 v_sub_1_51;
(*   %add21.1.51 = add i16 %359, %call.i.1.51 *)
add v_add21_1_51 v359 v_call_i_1_51;
(*   store i16 %add21.1.51, i16* %arrayidx11.1.51, align 2, !tbaa !3 *)
mov mem0_102 v_add21_1_51;
(*   %arrayidx9.1.52 = getelementptr inbounds i16, i16* %r, i64 116 *)
(*   %360 = load i16, i16* %arrayidx9.1.52, align 2, !tbaa !3 *)
mov v360 mem0_232;
(*   %conv1.i.1.52 = sext i16 %360 to i32 *)
cast v_conv1_i_1_52@sint32 v360@sint16;
(*   %mul.i.1.52 = mul nsw i32 %conv1.i.1.52, -359 *)
mul v_mul_i_1_52 v_conv1_i_1_52 (-359)@sint32;
(*   %call.i.1.52 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.52) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_52, v_call_i_1_52);
(*   %arrayidx11.1.52 = getelementptr inbounds i16, i16* %r, i64 52 *)
(*   %361 = load i16, i16* %arrayidx11.1.52, align 2, !tbaa !3 *)
mov v361 mem0_104;
(*   %sub.1.52 = sub i16 %361, %call.i.1.52 *)
sub v_sub_1_52 v361 v_call_i_1_52;
(*   store i16 %sub.1.52, i16* %arrayidx9.1.52, align 2, !tbaa !3 *)
mov mem0_232 v_sub_1_52;
(*   %add21.1.52 = add i16 %361, %call.i.1.52 *)
add v_add21_1_52 v361 v_call_i_1_52;
(*   store i16 %add21.1.52, i16* %arrayidx11.1.52, align 2, !tbaa !3 *)
mov mem0_104 v_add21_1_52;
(*   %arrayidx9.1.53 = getelementptr inbounds i16, i16* %r, i64 117 *)
(*   %362 = load i16, i16* %arrayidx9.1.53, align 2, !tbaa !3 *)
mov v362 mem0_234;
(*   %conv1.i.1.53 = sext i16 %362 to i32 *)
cast v_conv1_i_1_53@sint32 v362@sint16;
(*   %mul.i.1.53 = mul nsw i32 %conv1.i.1.53, -359 *)
mul v_mul_i_1_53 v_conv1_i_1_53 (-359)@sint32;
(*   %call.i.1.53 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.53) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_53, v_call_i_1_53);
(*   %arrayidx11.1.53 = getelementptr inbounds i16, i16* %r, i64 53 *)
(*   %363 = load i16, i16* %arrayidx11.1.53, align 2, !tbaa !3 *)
mov v363 mem0_106;
(*   %sub.1.53 = sub i16 %363, %call.i.1.53 *)
sub v_sub_1_53 v363 v_call_i_1_53;
(*   store i16 %sub.1.53, i16* %arrayidx9.1.53, align 2, !tbaa !3 *)
mov mem0_234 v_sub_1_53;
(*   %add21.1.53 = add i16 %363, %call.i.1.53 *)
add v_add21_1_53 v363 v_call_i_1_53;
(*   store i16 %add21.1.53, i16* %arrayidx11.1.53, align 2, !tbaa !3 *)
mov mem0_106 v_add21_1_53;
(*   %arrayidx9.1.54 = getelementptr inbounds i16, i16* %r, i64 118 *)
(*   %364 = load i16, i16* %arrayidx9.1.54, align 2, !tbaa !3 *)
mov v364 mem0_236;
(*   %conv1.i.1.54 = sext i16 %364 to i32 *)
cast v_conv1_i_1_54@sint32 v364@sint16;
(*   %mul.i.1.54 = mul nsw i32 %conv1.i.1.54, -359 *)
mul v_mul_i_1_54 v_conv1_i_1_54 (-359)@sint32;
(*   %call.i.1.54 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.54) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_54, v_call_i_1_54);
(*   %arrayidx11.1.54 = getelementptr inbounds i16, i16* %r, i64 54 *)
(*   %365 = load i16, i16* %arrayidx11.1.54, align 2, !tbaa !3 *)
mov v365 mem0_108;
(*   %sub.1.54 = sub i16 %365, %call.i.1.54 *)
sub v_sub_1_54 v365 v_call_i_1_54;
(*   store i16 %sub.1.54, i16* %arrayidx9.1.54, align 2, !tbaa !3 *)
mov mem0_236 v_sub_1_54;
(*   %add21.1.54 = add i16 %365, %call.i.1.54 *)
add v_add21_1_54 v365 v_call_i_1_54;
(*   store i16 %add21.1.54, i16* %arrayidx11.1.54, align 2, !tbaa !3 *)
mov mem0_108 v_add21_1_54;
(*   %arrayidx9.1.55 = getelementptr inbounds i16, i16* %r, i64 119 *)
(*   %366 = load i16, i16* %arrayidx9.1.55, align 2, !tbaa !3 *)
mov v366 mem0_238;
(*   %conv1.i.1.55 = sext i16 %366 to i32 *)
cast v_conv1_i_1_55@sint32 v366@sint16;
(*   %mul.i.1.55 = mul nsw i32 %conv1.i.1.55, -359 *)
mul v_mul_i_1_55 v_conv1_i_1_55 (-359)@sint32;
(*   %call.i.1.55 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.55) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_55, v_call_i_1_55);
(*   %arrayidx11.1.55 = getelementptr inbounds i16, i16* %r, i64 55 *)
(*   %367 = load i16, i16* %arrayidx11.1.55, align 2, !tbaa !3 *)
mov v367 mem0_110;
(*   %sub.1.55 = sub i16 %367, %call.i.1.55 *)
sub v_sub_1_55 v367 v_call_i_1_55;
(*   store i16 %sub.1.55, i16* %arrayidx9.1.55, align 2, !tbaa !3 *)
mov mem0_238 v_sub_1_55;
(*   %add21.1.55 = add i16 %367, %call.i.1.55 *)
add v_add21_1_55 v367 v_call_i_1_55;
(*   store i16 %add21.1.55, i16* %arrayidx11.1.55, align 2, !tbaa !3 *)
mov mem0_110 v_add21_1_55;
(*   %arrayidx9.1.56 = getelementptr inbounds i16, i16* %r, i64 120 *)
(*   %368 = load i16, i16* %arrayidx9.1.56, align 2, !tbaa !3 *)
mov v368 mem0_240;
(*   %conv1.i.1.56 = sext i16 %368 to i32 *)
cast v_conv1_i_1_56@sint32 v368@sint16;
(*   %mul.i.1.56 = mul nsw i32 %conv1.i.1.56, -359 *)
mul v_mul_i_1_56 v_conv1_i_1_56 (-359)@sint32;
(*   %call.i.1.56 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.56) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_56, v_call_i_1_56);
(*   %arrayidx11.1.56 = getelementptr inbounds i16, i16* %r, i64 56 *)
(*   %369 = load i16, i16* %arrayidx11.1.56, align 2, !tbaa !3 *)
mov v369 mem0_112;
(*   %sub.1.56 = sub i16 %369, %call.i.1.56 *)
sub v_sub_1_56 v369 v_call_i_1_56;
(*   store i16 %sub.1.56, i16* %arrayidx9.1.56, align 2, !tbaa !3 *)
mov mem0_240 v_sub_1_56;
(*   %add21.1.56 = add i16 %369, %call.i.1.56 *)
add v_add21_1_56 v369 v_call_i_1_56;
(*   store i16 %add21.1.56, i16* %arrayidx11.1.56, align 2, !tbaa !3 *)
mov mem0_112 v_add21_1_56;
(*   %arrayidx9.1.57 = getelementptr inbounds i16, i16* %r, i64 121 *)
(*   %370 = load i16, i16* %arrayidx9.1.57, align 2, !tbaa !3 *)
mov v370 mem0_242;
(*   %conv1.i.1.57 = sext i16 %370 to i32 *)
cast v_conv1_i_1_57@sint32 v370@sint16;
(*   %mul.i.1.57 = mul nsw i32 %conv1.i.1.57, -359 *)
mul v_mul_i_1_57 v_conv1_i_1_57 (-359)@sint32;
(*   %call.i.1.57 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.57) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_57, v_call_i_1_57);
(*   %arrayidx11.1.57 = getelementptr inbounds i16, i16* %r, i64 57 *)
(*   %371 = load i16, i16* %arrayidx11.1.57, align 2, !tbaa !3 *)
mov v371 mem0_114;
(*   %sub.1.57 = sub i16 %371, %call.i.1.57 *)
sub v_sub_1_57 v371 v_call_i_1_57;
(*   store i16 %sub.1.57, i16* %arrayidx9.1.57, align 2, !tbaa !3 *)
mov mem0_242 v_sub_1_57;
(*   %add21.1.57 = add i16 %371, %call.i.1.57 *)
add v_add21_1_57 v371 v_call_i_1_57;
(*   store i16 %add21.1.57, i16* %arrayidx11.1.57, align 2, !tbaa !3 *)
mov mem0_114 v_add21_1_57;
(*   %arrayidx9.1.58 = getelementptr inbounds i16, i16* %r, i64 122 *)
(*   %372 = load i16, i16* %arrayidx9.1.58, align 2, !tbaa !3 *)
mov v372 mem0_244;
(*   %conv1.i.1.58 = sext i16 %372 to i32 *)
cast v_conv1_i_1_58@sint32 v372@sint16;
(*   %mul.i.1.58 = mul nsw i32 %conv1.i.1.58, -359 *)
mul v_mul_i_1_58 v_conv1_i_1_58 (-359)@sint32;
(*   %call.i.1.58 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.58) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_58, v_call_i_1_58);
(*   %arrayidx11.1.58 = getelementptr inbounds i16, i16* %r, i64 58 *)
(*   %373 = load i16, i16* %arrayidx11.1.58, align 2, !tbaa !3 *)
mov v373 mem0_116;
(*   %sub.1.58 = sub i16 %373, %call.i.1.58 *)
sub v_sub_1_58 v373 v_call_i_1_58;
(*   store i16 %sub.1.58, i16* %arrayidx9.1.58, align 2, !tbaa !3 *)
mov mem0_244 v_sub_1_58;
(*   %add21.1.58 = add i16 %373, %call.i.1.58 *)
add v_add21_1_58 v373 v_call_i_1_58;
(*   store i16 %add21.1.58, i16* %arrayidx11.1.58, align 2, !tbaa !3 *)
mov mem0_116 v_add21_1_58;
(*   %arrayidx9.1.59 = getelementptr inbounds i16, i16* %r, i64 123 *)
(*   %374 = load i16, i16* %arrayidx9.1.59, align 2, !tbaa !3 *)
mov v374 mem0_246;
(*   %conv1.i.1.59 = sext i16 %374 to i32 *)
cast v_conv1_i_1_59@sint32 v374@sint16;
(*   %mul.i.1.59 = mul nsw i32 %conv1.i.1.59, -359 *)
mul v_mul_i_1_59 v_conv1_i_1_59 (-359)@sint32;
(*   %call.i.1.59 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.59) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_59, v_call_i_1_59);
(*   %arrayidx11.1.59 = getelementptr inbounds i16, i16* %r, i64 59 *)
(*   %375 = load i16, i16* %arrayidx11.1.59, align 2, !tbaa !3 *)
mov v375 mem0_118;
(*   %sub.1.59 = sub i16 %375, %call.i.1.59 *)
sub v_sub_1_59 v375 v_call_i_1_59;
(*   store i16 %sub.1.59, i16* %arrayidx9.1.59, align 2, !tbaa !3 *)
mov mem0_246 v_sub_1_59;
(*   %add21.1.59 = add i16 %375, %call.i.1.59 *)
add v_add21_1_59 v375 v_call_i_1_59;
(*   store i16 %add21.1.59, i16* %arrayidx11.1.59, align 2, !tbaa !3 *)
mov mem0_118 v_add21_1_59;
(*   %arrayidx9.1.60 = getelementptr inbounds i16, i16* %r, i64 124 *)
(*   %376 = load i16, i16* %arrayidx9.1.60, align 2, !tbaa !3 *)
mov v376 mem0_248;
(*   %conv1.i.1.60 = sext i16 %376 to i32 *)
cast v_conv1_i_1_60@sint32 v376@sint16;
(*   %mul.i.1.60 = mul nsw i32 %conv1.i.1.60, -359 *)
mul v_mul_i_1_60 v_conv1_i_1_60 (-359)@sint32;
(*   %call.i.1.60 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.60) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_60, v_call_i_1_60);
(*   %arrayidx11.1.60 = getelementptr inbounds i16, i16* %r, i64 60 *)
(*   %377 = load i16, i16* %arrayidx11.1.60, align 2, !tbaa !3 *)
mov v377 mem0_120;
(*   %sub.1.60 = sub i16 %377, %call.i.1.60 *)
sub v_sub_1_60 v377 v_call_i_1_60;
(*   store i16 %sub.1.60, i16* %arrayidx9.1.60, align 2, !tbaa !3 *)
mov mem0_248 v_sub_1_60;
(*   %add21.1.60 = add i16 %377, %call.i.1.60 *)
add v_add21_1_60 v377 v_call_i_1_60;
(*   store i16 %add21.1.60, i16* %arrayidx11.1.60, align 2, !tbaa !3 *)
mov mem0_120 v_add21_1_60;
(*   %arrayidx9.1.61 = getelementptr inbounds i16, i16* %r, i64 125 *)
(*   %378 = load i16, i16* %arrayidx9.1.61, align 2, !tbaa !3 *)
mov v378 mem0_250;
(*   %conv1.i.1.61 = sext i16 %378 to i32 *)
cast v_conv1_i_1_61@sint32 v378@sint16;
(*   %mul.i.1.61 = mul nsw i32 %conv1.i.1.61, -359 *)
mul v_mul_i_1_61 v_conv1_i_1_61 (-359)@sint32;
(*   %call.i.1.61 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.61) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_61, v_call_i_1_61);
(*   %arrayidx11.1.61 = getelementptr inbounds i16, i16* %r, i64 61 *)
(*   %379 = load i16, i16* %arrayidx11.1.61, align 2, !tbaa !3 *)
mov v379 mem0_122;
(*   %sub.1.61 = sub i16 %379, %call.i.1.61 *)
sub v_sub_1_61 v379 v_call_i_1_61;
(*   store i16 %sub.1.61, i16* %arrayidx9.1.61, align 2, !tbaa !3 *)
mov mem0_250 v_sub_1_61;
(*   %add21.1.61 = add i16 %379, %call.i.1.61 *)
add v_add21_1_61 v379 v_call_i_1_61;
(*   store i16 %add21.1.61, i16* %arrayidx11.1.61, align 2, !tbaa !3 *)
mov mem0_122 v_add21_1_61;
(*   %arrayidx9.1.62 = getelementptr inbounds i16, i16* %r, i64 126 *)
(*   %380 = load i16, i16* %arrayidx9.1.62, align 2, !tbaa !3 *)
mov v380 mem0_252;
(*   %conv1.i.1.62 = sext i16 %380 to i32 *)
cast v_conv1_i_1_62@sint32 v380@sint16;
(*   %mul.i.1.62 = mul nsw i32 %conv1.i.1.62, -359 *)
mul v_mul_i_1_62 v_conv1_i_1_62 (-359)@sint32;
(*   %call.i.1.62 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.62) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_62, v_call_i_1_62);
(*   %arrayidx11.1.62 = getelementptr inbounds i16, i16* %r, i64 62 *)
(*   %381 = load i16, i16* %arrayidx11.1.62, align 2, !tbaa !3 *)
mov v381 mem0_124;
(*   %sub.1.62 = sub i16 %381, %call.i.1.62 *)
sub v_sub_1_62 v381 v_call_i_1_62;
(*   store i16 %sub.1.62, i16* %arrayidx9.1.62, align 2, !tbaa !3 *)
mov mem0_252 v_sub_1_62;
(*   %add21.1.62 = add i16 %381, %call.i.1.62 *)
add v_add21_1_62 v381 v_call_i_1_62;
(*   store i16 %add21.1.62, i16* %arrayidx11.1.62, align 2, !tbaa !3 *)
mov mem0_124 v_add21_1_62;
(*   %arrayidx9.1.63 = getelementptr inbounds i16, i16* %r, i64 127 *)
(*   %382 = load i16, i16* %arrayidx9.1.63, align 2, !tbaa !3 *)
mov v382 mem0_254;
(*   %conv1.i.1.63 = sext i16 %382 to i32 *)
cast v_conv1_i_1_63@sint32 v382@sint16;
(*   %mul.i.1.63 = mul nsw i32 %conv1.i.1.63, -359 *)
mul v_mul_i_1_63 v_conv1_i_1_63 (-359)@sint32;
(*   %call.i.1.63 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.63) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_63, v_call_i_1_63);
(*   %arrayidx11.1.63 = getelementptr inbounds i16, i16* %r, i64 63 *)
(*   %383 = load i16, i16* %arrayidx11.1.63, align 2, !tbaa !3 *)
mov v383 mem0_126;
(*   %sub.1.63 = sub i16 %383, %call.i.1.63 *)
sub v_sub_1_63 v383 v_call_i_1_63;
(*   store i16 %sub.1.63, i16* %arrayidx9.1.63, align 2, !tbaa !3 *)
mov mem0_254 v_sub_1_63;
(*   %add21.1.63 = add i16 %383, %call.i.1.63 *)
add v_add21_1_63 v383 v_call_i_1_63;
(*   store i16 %add21.1.63, i16* %arrayidx11.1.63, align 2, !tbaa !3 *)
mov mem0_126 v_add21_1_63;

(* NOTE: k = 3 *)

(*   %arrayidx9.1.1278 = getelementptr inbounds i16, i16* %r, i64 192 *)
(*   %384 = load i16, i16* %arrayidx9.1.1278, align 2, !tbaa !3 *)
mov v384 mem0_384;
(*   %conv1.i.1.1279 = sext i16 %384 to i32 *)
cast v_conv1_i_1_1279@sint32 v384@sint16;
(*   %mul.i.1.1280 = mul nsw i32 %conv1.i.1.1279, -1517 *)
mul v_mul_i_1_1280 v_conv1_i_1_1279 (-1517)@sint32;
(*   %call.i.1.1281 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.1280) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_1280, v_call_i_1_1281);
(*   %arrayidx11.1.1282 = getelementptr inbounds i16, i16* %r, i64 128 *)
(*   %385 = load i16, i16* %arrayidx11.1.1282, align 2, !tbaa !3 *)
mov v385 mem0_256;
(*   %sub.1.1283 = sub i16 %385, %call.i.1.1281 *)
sub v_sub_1_1283 v385 v_call_i_1_1281;
(*   store i16 %sub.1.1283, i16* %arrayidx9.1.1278, align 2, !tbaa !3 *)
mov mem0_384 v_sub_1_1283;
(*   %add21.1.1284 = add i16 %385, %call.i.1.1281 *)
add v_add21_1_1284 v385 v_call_i_1_1281;
(*   store i16 %add21.1.1284, i16* %arrayidx11.1.1282, align 2, !tbaa !3 *)
mov mem0_256 v_add21_1_1284;
(*   %arrayidx9.1.1.1 = getelementptr inbounds i16, i16* %r, i64 193 *)
(*   %386 = load i16, i16* %arrayidx9.1.1.1, align 2, !tbaa !3 *)
mov v386 mem0_386;
(*   %conv1.i.1.1.1 = sext i16 %386 to i32 *)
cast v_conv1_i_1_1_1@sint32 v386@sint16;
(*   %mul.i.1.1.1 = mul nsw i32 %conv1.i.1.1.1, -1517 *)
mul v_mul_i_1_1_1 v_conv1_i_1_1_1 (-1517)@sint32;
(*   %call.i.1.1.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.1.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_1_1, v_call_i_1_1_1);
(*   %arrayidx11.1.1.1 = getelementptr inbounds i16, i16* %r, i64 129 *)
(*   %387 = load i16, i16* %arrayidx11.1.1.1, align 2, !tbaa !3 *)
mov v387 mem0_258;
(*   %sub.1.1.1 = sub i16 %387, %call.i.1.1.1 *)
sub v_sub_1_1_1 v387 v_call_i_1_1_1;
(*   store i16 %sub.1.1.1, i16* %arrayidx9.1.1.1, align 2, !tbaa !3 *)
mov mem0_386 v_sub_1_1_1;
(*   %add21.1.1.1 = add i16 %387, %call.i.1.1.1 *)
add v_add21_1_1_1 v387 v_call_i_1_1_1;
(*   store i16 %add21.1.1.1, i16* %arrayidx11.1.1.1, align 2, !tbaa !3 *)
mov mem0_258 v_add21_1_1_1;
(*   %arrayidx9.1.2.1 = getelementptr inbounds i16, i16* %r, i64 194 *)
(*   %388 = load i16, i16* %arrayidx9.1.2.1, align 2, !tbaa !3 *)
mov v388 mem0_388;
(*   %conv1.i.1.2.1 = sext i16 %388 to i32 *)
cast v_conv1_i_1_2_1@sint32 v388@sint16;
(*   %mul.i.1.2.1 = mul nsw i32 %conv1.i.1.2.1, -1517 *)
mul v_mul_i_1_2_1 v_conv1_i_1_2_1 (-1517)@sint32;
(*   %call.i.1.2.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.2.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_2_1, v_call_i_1_2_1);
(*   %arrayidx11.1.2.1 = getelementptr inbounds i16, i16* %r, i64 130 *)
(*   %389 = load i16, i16* %arrayidx11.1.2.1, align 2, !tbaa !3 *)
mov v389 mem0_260;
(*   %sub.1.2.1 = sub i16 %389, %call.i.1.2.1 *)
sub v_sub_1_2_1 v389 v_call_i_1_2_1;
(*   store i16 %sub.1.2.1, i16* %arrayidx9.1.2.1, align 2, !tbaa !3 *)
mov mem0_388 v_sub_1_2_1;
(*   %add21.1.2.1 = add i16 %389, %call.i.1.2.1 *)
add v_add21_1_2_1 v389 v_call_i_1_2_1;
(*   store i16 %add21.1.2.1, i16* %arrayidx11.1.2.1, align 2, !tbaa !3 *)
mov mem0_260 v_add21_1_2_1;
(*   %arrayidx9.1.3.1 = getelementptr inbounds i16, i16* %r, i64 195 *)
(*   %390 = load i16, i16* %arrayidx9.1.3.1, align 2, !tbaa !3 *)
mov v390 mem0_390;
(*   %conv1.i.1.3.1 = sext i16 %390 to i32 *)
cast v_conv1_i_1_3_1@sint32 v390@sint16;
(*   %mul.i.1.3.1 = mul nsw i32 %conv1.i.1.3.1, -1517 *)
mul v_mul_i_1_3_1 v_conv1_i_1_3_1 (-1517)@sint32;
(*   %call.i.1.3.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.3.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_3_1, v_call_i_1_3_1);
(*   %arrayidx11.1.3.1 = getelementptr inbounds i16, i16* %r, i64 131 *)
(*   %391 = load i16, i16* %arrayidx11.1.3.1, align 2, !tbaa !3 *)
mov v391 mem0_262;
(*   %sub.1.3.1 = sub i16 %391, %call.i.1.3.1 *)
sub v_sub_1_3_1 v391 v_call_i_1_3_1;
(*   store i16 %sub.1.3.1, i16* %arrayidx9.1.3.1, align 2, !tbaa !3 *)
mov mem0_390 v_sub_1_3_1;
(*   %add21.1.3.1 = add i16 %391, %call.i.1.3.1 *)
add v_add21_1_3_1 v391 v_call_i_1_3_1;
(*   store i16 %add21.1.3.1, i16* %arrayidx11.1.3.1, align 2, !tbaa !3 *)
mov mem0_262 v_add21_1_3_1;
(*   %arrayidx9.1.4.1 = getelementptr inbounds i16, i16* %r, i64 196 *)
(*   %392 = load i16, i16* %arrayidx9.1.4.1, align 2, !tbaa !3 *)
mov v392 mem0_392;
(*   %conv1.i.1.4.1 = sext i16 %392 to i32 *)
cast v_conv1_i_1_4_1@sint32 v392@sint16;
(*   %mul.i.1.4.1 = mul nsw i32 %conv1.i.1.4.1, -1517 *)
mul v_mul_i_1_4_1 v_conv1_i_1_4_1 (-1517)@sint32;
(*   %call.i.1.4.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.4.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_4_1, v_call_i_1_4_1);
(*   %arrayidx11.1.4.1 = getelementptr inbounds i16, i16* %r, i64 132 *)
(*   %393 = load i16, i16* %arrayidx11.1.4.1, align 2, !tbaa !3 *)
mov v393 mem0_264;
(*   %sub.1.4.1 = sub i16 %393, %call.i.1.4.1 *)
sub v_sub_1_4_1 v393 v_call_i_1_4_1;
(*   store i16 %sub.1.4.1, i16* %arrayidx9.1.4.1, align 2, !tbaa !3 *)
mov mem0_392 v_sub_1_4_1;
(*   %add21.1.4.1 = add i16 %393, %call.i.1.4.1 *)
add v_add21_1_4_1 v393 v_call_i_1_4_1;
(*   store i16 %add21.1.4.1, i16* %arrayidx11.1.4.1, align 2, !tbaa !3 *)
mov mem0_264 v_add21_1_4_1;
(*   %arrayidx9.1.5.1 = getelementptr inbounds i16, i16* %r, i64 197 *)
(*   %394 = load i16, i16* %arrayidx9.1.5.1, align 2, !tbaa !3 *)
mov v394 mem0_394;
(*   %conv1.i.1.5.1 = sext i16 %394 to i32 *)
cast v_conv1_i_1_5_1@sint32 v394@sint16;
(*   %mul.i.1.5.1 = mul nsw i32 %conv1.i.1.5.1, -1517 *)
mul v_mul_i_1_5_1 v_conv1_i_1_5_1 (-1517)@sint32;
(*   %call.i.1.5.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.5.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_5_1, v_call_i_1_5_1);
(*   %arrayidx11.1.5.1 = getelementptr inbounds i16, i16* %r, i64 133 *)
(*   %395 = load i16, i16* %arrayidx11.1.5.1, align 2, !tbaa !3 *)
mov v395 mem0_266;
(*   %sub.1.5.1 = sub i16 %395, %call.i.1.5.1 *)
sub v_sub_1_5_1 v395 v_call_i_1_5_1;
(*   store i16 %sub.1.5.1, i16* %arrayidx9.1.5.1, align 2, !tbaa !3 *)
mov mem0_394 v_sub_1_5_1;
(*   %add21.1.5.1 = add i16 %395, %call.i.1.5.1 *)
add v_add21_1_5_1 v395 v_call_i_1_5_1;
(*   store i16 %add21.1.5.1, i16* %arrayidx11.1.5.1, align 2, !tbaa !3 *)
mov mem0_266 v_add21_1_5_1;
(*   %arrayidx9.1.6.1 = getelementptr inbounds i16, i16* %r, i64 198 *)
(*   %396 = load i16, i16* %arrayidx9.1.6.1, align 2, !tbaa !3 *)
mov v396 mem0_396;
(*   %conv1.i.1.6.1 = sext i16 %396 to i32 *)
cast v_conv1_i_1_6_1@sint32 v396@sint16;
(*   %mul.i.1.6.1 = mul nsw i32 %conv1.i.1.6.1, -1517 *)
mul v_mul_i_1_6_1 v_conv1_i_1_6_1 (-1517)@sint32;
(*   %call.i.1.6.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.6.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_6_1, v_call_i_1_6_1);
(*   %arrayidx11.1.6.1 = getelementptr inbounds i16, i16* %r, i64 134 *)
(*   %397 = load i16, i16* %arrayidx11.1.6.1, align 2, !tbaa !3 *)
mov v397 mem0_268;
(*   %sub.1.6.1 = sub i16 %397, %call.i.1.6.1 *)
sub v_sub_1_6_1 v397 v_call_i_1_6_1;
(*   store i16 %sub.1.6.1, i16* %arrayidx9.1.6.1, align 2, !tbaa !3 *)
mov mem0_396 v_sub_1_6_1;
(*   %add21.1.6.1 = add i16 %397, %call.i.1.6.1 *)
add v_add21_1_6_1 v397 v_call_i_1_6_1;
(*   store i16 %add21.1.6.1, i16* %arrayidx11.1.6.1, align 2, !tbaa !3 *)
mov mem0_268 v_add21_1_6_1;
(*   %arrayidx9.1.7.1 = getelementptr inbounds i16, i16* %r, i64 199 *)
(*   %398 = load i16, i16* %arrayidx9.1.7.1, align 2, !tbaa !3 *)
mov v398 mem0_398;
(*   %conv1.i.1.7.1 = sext i16 %398 to i32 *)
cast v_conv1_i_1_7_1@sint32 v398@sint16;
(*   %mul.i.1.7.1 = mul nsw i32 %conv1.i.1.7.1, -1517 *)
mul v_mul_i_1_7_1 v_conv1_i_1_7_1 (-1517)@sint32;
(*   %call.i.1.7.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.7.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_7_1, v_call_i_1_7_1);
(*   %arrayidx11.1.7.1 = getelementptr inbounds i16, i16* %r, i64 135 *)
(*   %399 = load i16, i16* %arrayidx11.1.7.1, align 2, !tbaa !3 *)
mov v399 mem0_270;
(*   %sub.1.7.1 = sub i16 %399, %call.i.1.7.1 *)
sub v_sub_1_7_1 v399 v_call_i_1_7_1;
(*   store i16 %sub.1.7.1, i16* %arrayidx9.1.7.1, align 2, !tbaa !3 *)
mov mem0_398 v_sub_1_7_1;
(*   %add21.1.7.1 = add i16 %399, %call.i.1.7.1 *)
add v_add21_1_7_1 v399 v_call_i_1_7_1;
(*   store i16 %add21.1.7.1, i16* %arrayidx11.1.7.1, align 2, !tbaa !3 *)
mov mem0_270 v_add21_1_7_1;
(*   %arrayidx9.1.8.1 = getelementptr inbounds i16, i16* %r, i64 200 *)
(*   %400 = load i16, i16* %arrayidx9.1.8.1, align 2, !tbaa !3 *)
mov v400 mem0_400;
(*   %conv1.i.1.8.1 = sext i16 %400 to i32 *)
cast v_conv1_i_1_8_1@sint32 v400@sint16;
(*   %mul.i.1.8.1 = mul nsw i32 %conv1.i.1.8.1, -1517 *)
mul v_mul_i_1_8_1 v_conv1_i_1_8_1 (-1517)@sint32;
(*   %call.i.1.8.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.8.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_8_1, v_call_i_1_8_1);
(*   %arrayidx11.1.8.1 = getelementptr inbounds i16, i16* %r, i64 136 *)
(*   %401 = load i16, i16* %arrayidx11.1.8.1, align 2, !tbaa !3 *)
mov v401 mem0_272;
(*   %sub.1.8.1 = sub i16 %401, %call.i.1.8.1 *)
sub v_sub_1_8_1 v401 v_call_i_1_8_1;
(*   store i16 %sub.1.8.1, i16* %arrayidx9.1.8.1, align 2, !tbaa !3 *)
mov mem0_400 v_sub_1_8_1;
(*   %add21.1.8.1 = add i16 %401, %call.i.1.8.1 *)
add v_add21_1_8_1 v401 v_call_i_1_8_1;
(*   store i16 %add21.1.8.1, i16* %arrayidx11.1.8.1, align 2, !tbaa !3 *)
mov mem0_272 v_add21_1_8_1;
(*   %arrayidx9.1.9.1 = getelementptr inbounds i16, i16* %r, i64 201 *)
(*   %402 = load i16, i16* %arrayidx9.1.9.1, align 2, !tbaa !3 *)
mov v402 mem0_402;
(*   %conv1.i.1.9.1 = sext i16 %402 to i32 *)
cast v_conv1_i_1_9_1@sint32 v402@sint16;
(*   %mul.i.1.9.1 = mul nsw i32 %conv1.i.1.9.1, -1517 *)
mul v_mul_i_1_9_1 v_conv1_i_1_9_1 (-1517)@sint32;
(*   %call.i.1.9.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.9.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_9_1, v_call_i_1_9_1);
(*   %arrayidx11.1.9.1 = getelementptr inbounds i16, i16* %r, i64 137 *)
(*   %403 = load i16, i16* %arrayidx11.1.9.1, align 2, !tbaa !3 *)
mov v403 mem0_274;
(*   %sub.1.9.1 = sub i16 %403, %call.i.1.9.1 *)
sub v_sub_1_9_1 v403 v_call_i_1_9_1;
(*   store i16 %sub.1.9.1, i16* %arrayidx9.1.9.1, align 2, !tbaa !3 *)
mov mem0_402 v_sub_1_9_1;
(*   %add21.1.9.1 = add i16 %403, %call.i.1.9.1 *)
add v_add21_1_9_1 v403 v_call_i_1_9_1;
(*   store i16 %add21.1.9.1, i16* %arrayidx11.1.9.1, align 2, !tbaa !3 *)
mov mem0_274 v_add21_1_9_1;
(*   %arrayidx9.1.10.1 = getelementptr inbounds i16, i16* %r, i64 202 *)
(*   %404 = load i16, i16* %arrayidx9.1.10.1, align 2, !tbaa !3 *)
mov v404 mem0_404;
(*   %conv1.i.1.10.1 = sext i16 %404 to i32 *)
cast v_conv1_i_1_10_1@sint32 v404@sint16;
(*   %mul.i.1.10.1 = mul nsw i32 %conv1.i.1.10.1, -1517 *)
mul v_mul_i_1_10_1 v_conv1_i_1_10_1 (-1517)@sint32;
(*   %call.i.1.10.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.10.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_10_1, v_call_i_1_10_1);
(*   %arrayidx11.1.10.1 = getelementptr inbounds i16, i16* %r, i64 138 *)
(*   %405 = load i16, i16* %arrayidx11.1.10.1, align 2, !tbaa !3 *)
mov v405 mem0_276;
(*   %sub.1.10.1 = sub i16 %405, %call.i.1.10.1 *)
sub v_sub_1_10_1 v405 v_call_i_1_10_1;
(*   store i16 %sub.1.10.1, i16* %arrayidx9.1.10.1, align 2, !tbaa !3 *)
mov mem0_404 v_sub_1_10_1;
(*   %add21.1.10.1 = add i16 %405, %call.i.1.10.1 *)
add v_add21_1_10_1 v405 v_call_i_1_10_1;
(*   store i16 %add21.1.10.1, i16* %arrayidx11.1.10.1, align 2, !tbaa !3 *)
mov mem0_276 v_add21_1_10_1;
(*   %arrayidx9.1.11.1 = getelementptr inbounds i16, i16* %r, i64 203 *)
(*   %406 = load i16, i16* %arrayidx9.1.11.1, align 2, !tbaa !3 *)
mov v406 mem0_406;
(*   %conv1.i.1.11.1 = sext i16 %406 to i32 *)
cast v_conv1_i_1_11_1@sint32 v406@sint16;
(*   %mul.i.1.11.1 = mul nsw i32 %conv1.i.1.11.1, -1517 *)
mul v_mul_i_1_11_1 v_conv1_i_1_11_1 (-1517)@sint32;
(*   %call.i.1.11.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.11.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_11_1, v_call_i_1_11_1);
(*   %arrayidx11.1.11.1 = getelementptr inbounds i16, i16* %r, i64 139 *)
(*   %407 = load i16, i16* %arrayidx11.1.11.1, align 2, !tbaa !3 *)
mov v407 mem0_278;
(*   %sub.1.11.1 = sub i16 %407, %call.i.1.11.1 *)
sub v_sub_1_11_1 v407 v_call_i_1_11_1;
(*   store i16 %sub.1.11.1, i16* %arrayidx9.1.11.1, align 2, !tbaa !3 *)
mov mem0_406 v_sub_1_11_1;
(*   %add21.1.11.1 = add i16 %407, %call.i.1.11.1 *)
add v_add21_1_11_1 v407 v_call_i_1_11_1;
(*   store i16 %add21.1.11.1, i16* %arrayidx11.1.11.1, align 2, !tbaa !3 *)
mov mem0_278 v_add21_1_11_1;
(*   %arrayidx9.1.12.1 = getelementptr inbounds i16, i16* %r, i64 204 *)
(*   %408 = load i16, i16* %arrayidx9.1.12.1, align 2, !tbaa !3 *)
mov v408 mem0_408;
(*   %conv1.i.1.12.1 = sext i16 %408 to i32 *)
cast v_conv1_i_1_12_1@sint32 v408@sint16;
(*   %mul.i.1.12.1 = mul nsw i32 %conv1.i.1.12.1, -1517 *)
mul v_mul_i_1_12_1 v_conv1_i_1_12_1 (-1517)@sint32;
(*   %call.i.1.12.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.12.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_12_1, v_call_i_1_12_1);
(*   %arrayidx11.1.12.1 = getelementptr inbounds i16, i16* %r, i64 140 *)
(*   %409 = load i16, i16* %arrayidx11.1.12.1, align 2, !tbaa !3 *)
mov v409 mem0_280;
(*   %sub.1.12.1 = sub i16 %409, %call.i.1.12.1 *)
sub v_sub_1_12_1 v409 v_call_i_1_12_1;
(*   store i16 %sub.1.12.1, i16* %arrayidx9.1.12.1, align 2, !tbaa !3 *)
mov mem0_408 v_sub_1_12_1;
(*   %add21.1.12.1 = add i16 %409, %call.i.1.12.1 *)
add v_add21_1_12_1 v409 v_call_i_1_12_1;
(*   store i16 %add21.1.12.1, i16* %arrayidx11.1.12.1, align 2, !tbaa !3 *)
mov mem0_280 v_add21_1_12_1;
(*   %arrayidx9.1.13.1 = getelementptr inbounds i16, i16* %r, i64 205 *)
(*   %410 = load i16, i16* %arrayidx9.1.13.1, align 2, !tbaa !3 *)
mov v410 mem0_410;
(*   %conv1.i.1.13.1 = sext i16 %410 to i32 *)
cast v_conv1_i_1_13_1@sint32 v410@sint16;
(*   %mul.i.1.13.1 = mul nsw i32 %conv1.i.1.13.1, -1517 *)
mul v_mul_i_1_13_1 v_conv1_i_1_13_1 (-1517)@sint32;
(*   %call.i.1.13.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.13.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_13_1, v_call_i_1_13_1);
(*   %arrayidx11.1.13.1 = getelementptr inbounds i16, i16* %r, i64 141 *)
(*   %411 = load i16, i16* %arrayidx11.1.13.1, align 2, !tbaa !3 *)
mov v411 mem0_282;
(*   %sub.1.13.1 = sub i16 %411, %call.i.1.13.1 *)
sub v_sub_1_13_1 v411 v_call_i_1_13_1;
(*   store i16 %sub.1.13.1, i16* %arrayidx9.1.13.1, align 2, !tbaa !3 *)
mov mem0_410 v_sub_1_13_1;
(*   %add21.1.13.1 = add i16 %411, %call.i.1.13.1 *)
add v_add21_1_13_1 v411 v_call_i_1_13_1;
(*   store i16 %add21.1.13.1, i16* %arrayidx11.1.13.1, align 2, !tbaa !3 *)
mov mem0_282 v_add21_1_13_1;
(*   %arrayidx9.1.14.1 = getelementptr inbounds i16, i16* %r, i64 206 *)
(*   %412 = load i16, i16* %arrayidx9.1.14.1, align 2, !tbaa !3 *)
mov v412 mem0_412;
(*   %conv1.i.1.14.1 = sext i16 %412 to i32 *)
cast v_conv1_i_1_14_1@sint32 v412@sint16;
(*   %mul.i.1.14.1 = mul nsw i32 %conv1.i.1.14.1, -1517 *)
mul v_mul_i_1_14_1 v_conv1_i_1_14_1 (-1517)@sint32;
(*   %call.i.1.14.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.14.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_14_1, v_call_i_1_14_1);
(*   %arrayidx11.1.14.1 = getelementptr inbounds i16, i16* %r, i64 142 *)
(*   %413 = load i16, i16* %arrayidx11.1.14.1, align 2, !tbaa !3 *)
mov v413 mem0_284;
(*   %sub.1.14.1 = sub i16 %413, %call.i.1.14.1 *)
sub v_sub_1_14_1 v413 v_call_i_1_14_1;
(*   store i16 %sub.1.14.1, i16* %arrayidx9.1.14.1, align 2, !tbaa !3 *)
mov mem0_412 v_sub_1_14_1;
(*   %add21.1.14.1 = add i16 %413, %call.i.1.14.1 *)
add v_add21_1_14_1 v413 v_call_i_1_14_1;
(*   store i16 %add21.1.14.1, i16* %arrayidx11.1.14.1, align 2, !tbaa !3 *)
mov mem0_284 v_add21_1_14_1;
(*   %arrayidx9.1.15.1 = getelementptr inbounds i16, i16* %r, i64 207 *)
(*   %414 = load i16, i16* %arrayidx9.1.15.1, align 2, !tbaa !3 *)
mov v414 mem0_414;
(*   %conv1.i.1.15.1 = sext i16 %414 to i32 *)
cast v_conv1_i_1_15_1@sint32 v414@sint16;
(*   %mul.i.1.15.1 = mul nsw i32 %conv1.i.1.15.1, -1517 *)
mul v_mul_i_1_15_1 v_conv1_i_1_15_1 (-1517)@sint32;
(*   %call.i.1.15.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.15.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_15_1, v_call_i_1_15_1);
(*   %arrayidx11.1.15.1 = getelementptr inbounds i16, i16* %r, i64 143 *)
(*   %415 = load i16, i16* %arrayidx11.1.15.1, align 2, !tbaa !3 *)
mov v415 mem0_286;
(*   %sub.1.15.1 = sub i16 %415, %call.i.1.15.1 *)
sub v_sub_1_15_1 v415 v_call_i_1_15_1;
(*   store i16 %sub.1.15.1, i16* %arrayidx9.1.15.1, align 2, !tbaa !3 *)
mov mem0_414 v_sub_1_15_1;
(*   %add21.1.15.1 = add i16 %415, %call.i.1.15.1 *)
add v_add21_1_15_1 v415 v_call_i_1_15_1;
(*   store i16 %add21.1.15.1, i16* %arrayidx11.1.15.1, align 2, !tbaa !3 *)
mov mem0_286 v_add21_1_15_1;
(*   %arrayidx9.1.16.1 = getelementptr inbounds i16, i16* %r, i64 208 *)
(*   %416 = load i16, i16* %arrayidx9.1.16.1, align 2, !tbaa !3 *)
mov v416 mem0_416;
(*   %conv1.i.1.16.1 = sext i16 %416 to i32 *)
cast v_conv1_i_1_16_1@sint32 v416@sint16;
(*   %mul.i.1.16.1 = mul nsw i32 %conv1.i.1.16.1, -1517 *)
mul v_mul_i_1_16_1 v_conv1_i_1_16_1 (-1517)@sint32;
(*   %call.i.1.16.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.16.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_16_1, v_call_i_1_16_1);
(*   %arrayidx11.1.16.1 = getelementptr inbounds i16, i16* %r, i64 144 *)
(*   %417 = load i16, i16* %arrayidx11.1.16.1, align 2, !tbaa !3 *)
mov v417 mem0_288;
(*   %sub.1.16.1 = sub i16 %417, %call.i.1.16.1 *)
sub v_sub_1_16_1 v417 v_call_i_1_16_1;
(*   store i16 %sub.1.16.1, i16* %arrayidx9.1.16.1, align 2, !tbaa !3 *)
mov mem0_416 v_sub_1_16_1;
(*   %add21.1.16.1 = add i16 %417, %call.i.1.16.1 *)
add v_add21_1_16_1 v417 v_call_i_1_16_1;
(*   store i16 %add21.1.16.1, i16* %arrayidx11.1.16.1, align 2, !tbaa !3 *)
mov mem0_288 v_add21_1_16_1;
(*   %arrayidx9.1.17.1 = getelementptr inbounds i16, i16* %r, i64 209 *)
(*   %418 = load i16, i16* %arrayidx9.1.17.1, align 2, !tbaa !3 *)
mov v418 mem0_418;
(*   %conv1.i.1.17.1 = sext i16 %418 to i32 *)
cast v_conv1_i_1_17_1@sint32 v418@sint16;
(*   %mul.i.1.17.1 = mul nsw i32 %conv1.i.1.17.1, -1517 *)
mul v_mul_i_1_17_1 v_conv1_i_1_17_1 (-1517)@sint32;
(*   %call.i.1.17.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.17.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_17_1, v_call_i_1_17_1);
(*   %arrayidx11.1.17.1 = getelementptr inbounds i16, i16* %r, i64 145 *)
(*   %419 = load i16, i16* %arrayidx11.1.17.1, align 2, !tbaa !3 *)
mov v419 mem0_290;
(*   %sub.1.17.1 = sub i16 %419, %call.i.1.17.1 *)
sub v_sub_1_17_1 v419 v_call_i_1_17_1;
(*   store i16 %sub.1.17.1, i16* %arrayidx9.1.17.1, align 2, !tbaa !3 *)
mov mem0_418 v_sub_1_17_1;
(*   %add21.1.17.1 = add i16 %419, %call.i.1.17.1 *)
add v_add21_1_17_1 v419 v_call_i_1_17_1;
(*   store i16 %add21.1.17.1, i16* %arrayidx11.1.17.1, align 2, !tbaa !3 *)
mov mem0_290 v_add21_1_17_1;
(*   %arrayidx9.1.18.1 = getelementptr inbounds i16, i16* %r, i64 210 *)
(*   %420 = load i16, i16* %arrayidx9.1.18.1, align 2, !tbaa !3 *)
mov v420 mem0_420;
(*   %conv1.i.1.18.1 = sext i16 %420 to i32 *)
cast v_conv1_i_1_18_1@sint32 v420@sint16;
(*   %mul.i.1.18.1 = mul nsw i32 %conv1.i.1.18.1, -1517 *)
mul v_mul_i_1_18_1 v_conv1_i_1_18_1 (-1517)@sint32;
(*   %call.i.1.18.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.18.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_18_1, v_call_i_1_18_1);
(*   %arrayidx11.1.18.1 = getelementptr inbounds i16, i16* %r, i64 146 *)
(*   %421 = load i16, i16* %arrayidx11.1.18.1, align 2, !tbaa !3 *)
mov v421 mem0_292;
(*   %sub.1.18.1 = sub i16 %421, %call.i.1.18.1 *)
sub v_sub_1_18_1 v421 v_call_i_1_18_1;
(*   store i16 %sub.1.18.1, i16* %arrayidx9.1.18.1, align 2, !tbaa !3 *)
mov mem0_420 v_sub_1_18_1;
(*   %add21.1.18.1 = add i16 %421, %call.i.1.18.1 *)
add v_add21_1_18_1 v421 v_call_i_1_18_1;
(*   store i16 %add21.1.18.1, i16* %arrayidx11.1.18.1, align 2, !tbaa !3 *)
mov mem0_292 v_add21_1_18_1;
(*   %arrayidx9.1.19.1 = getelementptr inbounds i16, i16* %r, i64 211 *)
(*   %422 = load i16, i16* %arrayidx9.1.19.1, align 2, !tbaa !3 *)
mov v422 mem0_422;
(*   %conv1.i.1.19.1 = sext i16 %422 to i32 *)
cast v_conv1_i_1_19_1@sint32 v422@sint16;
(*   %mul.i.1.19.1 = mul nsw i32 %conv1.i.1.19.1, -1517 *)
mul v_mul_i_1_19_1 v_conv1_i_1_19_1 (-1517)@sint32;
(*   %call.i.1.19.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.19.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_19_1, v_call_i_1_19_1);
(*   %arrayidx11.1.19.1 = getelementptr inbounds i16, i16* %r, i64 147 *)
(*   %423 = load i16, i16* %arrayidx11.1.19.1, align 2, !tbaa !3 *)
mov v423 mem0_294;
(*   %sub.1.19.1 = sub i16 %423, %call.i.1.19.1 *)
sub v_sub_1_19_1 v423 v_call_i_1_19_1;
(*   store i16 %sub.1.19.1, i16* %arrayidx9.1.19.1, align 2, !tbaa !3 *)
mov mem0_422 v_sub_1_19_1;
(*   %add21.1.19.1 = add i16 %423, %call.i.1.19.1 *)
add v_add21_1_19_1 v423 v_call_i_1_19_1;
(*   store i16 %add21.1.19.1, i16* %arrayidx11.1.19.1, align 2, !tbaa !3 *)
mov mem0_294 v_add21_1_19_1;
(*   %arrayidx9.1.20.1 = getelementptr inbounds i16, i16* %r, i64 212 *)
(*   %424 = load i16, i16* %arrayidx9.1.20.1, align 2, !tbaa !3 *)
mov v424 mem0_424;
(*   %conv1.i.1.20.1 = sext i16 %424 to i32 *)
cast v_conv1_i_1_20_1@sint32 v424@sint16;
(*   %mul.i.1.20.1 = mul nsw i32 %conv1.i.1.20.1, -1517 *)
mul v_mul_i_1_20_1 v_conv1_i_1_20_1 (-1517)@sint32;
(*   %call.i.1.20.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.20.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_20_1, v_call_i_1_20_1);
(*   %arrayidx11.1.20.1 = getelementptr inbounds i16, i16* %r, i64 148 *)
(*   %425 = load i16, i16* %arrayidx11.1.20.1, align 2, !tbaa !3 *)
mov v425 mem0_296;
(*   %sub.1.20.1 = sub i16 %425, %call.i.1.20.1 *)
sub v_sub_1_20_1 v425 v_call_i_1_20_1;
(*   store i16 %sub.1.20.1, i16* %arrayidx9.1.20.1, align 2, !tbaa !3 *)
mov mem0_424 v_sub_1_20_1;
(*   %add21.1.20.1 = add i16 %425, %call.i.1.20.1 *)
add v_add21_1_20_1 v425 v_call_i_1_20_1;
(*   store i16 %add21.1.20.1, i16* %arrayidx11.1.20.1, align 2, !tbaa !3 *)
mov mem0_296 v_add21_1_20_1;
(*   %arrayidx9.1.21.1 = getelementptr inbounds i16, i16* %r, i64 213 *)
(*   %426 = load i16, i16* %arrayidx9.1.21.1, align 2, !tbaa !3 *)
mov v426 mem0_426;
(*   %conv1.i.1.21.1 = sext i16 %426 to i32 *)
cast v_conv1_i_1_21_1@sint32 v426@sint16;
(*   %mul.i.1.21.1 = mul nsw i32 %conv1.i.1.21.1, -1517 *)
mul v_mul_i_1_21_1 v_conv1_i_1_21_1 (-1517)@sint32;
(*   %call.i.1.21.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.21.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_21_1, v_call_i_1_21_1);
(*   %arrayidx11.1.21.1 = getelementptr inbounds i16, i16* %r, i64 149 *)
(*   %427 = load i16, i16* %arrayidx11.1.21.1, align 2, !tbaa !3 *)
mov v427 mem0_298;
(*   %sub.1.21.1 = sub i16 %427, %call.i.1.21.1 *)
sub v_sub_1_21_1 v427 v_call_i_1_21_1;
(*   store i16 %sub.1.21.1, i16* %arrayidx9.1.21.1, align 2, !tbaa !3 *)
mov mem0_426 v_sub_1_21_1;
(*   %add21.1.21.1 = add i16 %427, %call.i.1.21.1 *)
add v_add21_1_21_1 v427 v_call_i_1_21_1;
(*   store i16 %add21.1.21.1, i16* %arrayidx11.1.21.1, align 2, !tbaa !3 *)
mov mem0_298 v_add21_1_21_1;
(*   %arrayidx9.1.22.1 = getelementptr inbounds i16, i16* %r, i64 214 *)
(*   %428 = load i16, i16* %arrayidx9.1.22.1, align 2, !tbaa !3 *)
mov v428 mem0_428;
(*   %conv1.i.1.22.1 = sext i16 %428 to i32 *)
cast v_conv1_i_1_22_1@sint32 v428@sint16;
(*   %mul.i.1.22.1 = mul nsw i32 %conv1.i.1.22.1, -1517 *)
mul v_mul_i_1_22_1 v_conv1_i_1_22_1 (-1517)@sint32;
(*   %call.i.1.22.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.22.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_22_1, v_call_i_1_22_1);
(*   %arrayidx11.1.22.1 = getelementptr inbounds i16, i16* %r, i64 150 *)
(*   %429 = load i16, i16* %arrayidx11.1.22.1, align 2, !tbaa !3 *)
mov v429 mem0_300;
(*   %sub.1.22.1 = sub i16 %429, %call.i.1.22.1 *)
sub v_sub_1_22_1 v429 v_call_i_1_22_1;
(*   store i16 %sub.1.22.1, i16* %arrayidx9.1.22.1, align 2, !tbaa !3 *)
mov mem0_428 v_sub_1_22_1;
(*   %add21.1.22.1 = add i16 %429, %call.i.1.22.1 *)
add v_add21_1_22_1 v429 v_call_i_1_22_1;
(*   store i16 %add21.1.22.1, i16* %arrayidx11.1.22.1, align 2, !tbaa !3 *)
mov mem0_300 v_add21_1_22_1;
(*   %arrayidx9.1.23.1 = getelementptr inbounds i16, i16* %r, i64 215 *)
(*   %430 = load i16, i16* %arrayidx9.1.23.1, align 2, !tbaa !3 *)
mov v430 mem0_430;
(*   %conv1.i.1.23.1 = sext i16 %430 to i32 *)
cast v_conv1_i_1_23_1@sint32 v430@sint16;
(*   %mul.i.1.23.1 = mul nsw i32 %conv1.i.1.23.1, -1517 *)
mul v_mul_i_1_23_1 v_conv1_i_1_23_1 (-1517)@sint32;
(*   %call.i.1.23.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.23.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_23_1, v_call_i_1_23_1);
(*   %arrayidx11.1.23.1 = getelementptr inbounds i16, i16* %r, i64 151 *)
(*   %431 = load i16, i16* %arrayidx11.1.23.1, align 2, !tbaa !3 *)
mov v431 mem0_302;
(*   %sub.1.23.1 = sub i16 %431, %call.i.1.23.1 *)
sub v_sub_1_23_1 v431 v_call_i_1_23_1;
(*   store i16 %sub.1.23.1, i16* %arrayidx9.1.23.1, align 2, !tbaa !3 *)
mov mem0_430 v_sub_1_23_1;
(*   %add21.1.23.1 = add i16 %431, %call.i.1.23.1 *)
add v_add21_1_23_1 v431 v_call_i_1_23_1;
(*   store i16 %add21.1.23.1, i16* %arrayidx11.1.23.1, align 2, !tbaa !3 *)
mov mem0_302 v_add21_1_23_1;
(*   %arrayidx9.1.24.1 = getelementptr inbounds i16, i16* %r, i64 216 *)
(*   %432 = load i16, i16* %arrayidx9.1.24.1, align 2, !tbaa !3 *)
mov v432 mem0_432;
(*   %conv1.i.1.24.1 = sext i16 %432 to i32 *)
cast v_conv1_i_1_24_1@sint32 v432@sint16;
(*   %mul.i.1.24.1 = mul nsw i32 %conv1.i.1.24.1, -1517 *)
mul v_mul_i_1_24_1 v_conv1_i_1_24_1 (-1517)@sint32;
(*   %call.i.1.24.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.24.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_24_1, v_call_i_1_24_1);
(*   %arrayidx11.1.24.1 = getelementptr inbounds i16, i16* %r, i64 152 *)
(*   %433 = load i16, i16* %arrayidx11.1.24.1, align 2, !tbaa !3 *)
mov v433 mem0_304;
(*   %sub.1.24.1 = sub i16 %433, %call.i.1.24.1 *)
sub v_sub_1_24_1 v433 v_call_i_1_24_1;
(*   store i16 %sub.1.24.1, i16* %arrayidx9.1.24.1, align 2, !tbaa !3 *)
mov mem0_432 v_sub_1_24_1;
(*   %add21.1.24.1 = add i16 %433, %call.i.1.24.1 *)
add v_add21_1_24_1 v433 v_call_i_1_24_1;
(*   store i16 %add21.1.24.1, i16* %arrayidx11.1.24.1, align 2, !tbaa !3 *)
mov mem0_304 v_add21_1_24_1;
(*   %arrayidx9.1.25.1 = getelementptr inbounds i16, i16* %r, i64 217 *)
(*   %434 = load i16, i16* %arrayidx9.1.25.1, align 2, !tbaa !3 *)
mov v434 mem0_434;
(*   %conv1.i.1.25.1 = sext i16 %434 to i32 *)
cast v_conv1_i_1_25_1@sint32 v434@sint16;
(*   %mul.i.1.25.1 = mul nsw i32 %conv1.i.1.25.1, -1517 *)
mul v_mul_i_1_25_1 v_conv1_i_1_25_1 (-1517)@sint32;
(*   %call.i.1.25.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.25.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_25_1, v_call_i_1_25_1);
(*   %arrayidx11.1.25.1 = getelementptr inbounds i16, i16* %r, i64 153 *)
(*   %435 = load i16, i16* %arrayidx11.1.25.1, align 2, !tbaa !3 *)
mov v435 mem0_306;
(*   %sub.1.25.1 = sub i16 %435, %call.i.1.25.1 *)
sub v_sub_1_25_1 v435 v_call_i_1_25_1;
(*   store i16 %sub.1.25.1, i16* %arrayidx9.1.25.1, align 2, !tbaa !3 *)
mov mem0_434 v_sub_1_25_1;
(*   %add21.1.25.1 = add i16 %435, %call.i.1.25.1 *)
add v_add21_1_25_1 v435 v_call_i_1_25_1;
(*   store i16 %add21.1.25.1, i16* %arrayidx11.1.25.1, align 2, !tbaa !3 *)
mov mem0_306 v_add21_1_25_1;
(*   %arrayidx9.1.26.1 = getelementptr inbounds i16, i16* %r, i64 218 *)
(*   %436 = load i16, i16* %arrayidx9.1.26.1, align 2, !tbaa !3 *)
mov v436 mem0_436;
(*   %conv1.i.1.26.1 = sext i16 %436 to i32 *)
cast v_conv1_i_1_26_1@sint32 v436@sint16;
(*   %mul.i.1.26.1 = mul nsw i32 %conv1.i.1.26.1, -1517 *)
mul v_mul_i_1_26_1 v_conv1_i_1_26_1 (-1517)@sint32;
(*   %call.i.1.26.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.26.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_26_1, v_call_i_1_26_1);
(*   %arrayidx11.1.26.1 = getelementptr inbounds i16, i16* %r, i64 154 *)
(*   %437 = load i16, i16* %arrayidx11.1.26.1, align 2, !tbaa !3 *)
mov v437 mem0_308;
(*   %sub.1.26.1 = sub i16 %437, %call.i.1.26.1 *)
sub v_sub_1_26_1 v437 v_call_i_1_26_1;
(*   store i16 %sub.1.26.1, i16* %arrayidx9.1.26.1, align 2, !tbaa !3 *)
mov mem0_436 v_sub_1_26_1;
(*   %add21.1.26.1 = add i16 %437, %call.i.1.26.1 *)
add v_add21_1_26_1 v437 v_call_i_1_26_1;
(*   store i16 %add21.1.26.1, i16* %arrayidx11.1.26.1, align 2, !tbaa !3 *)
mov mem0_308 v_add21_1_26_1;
(*   %arrayidx9.1.27.1 = getelementptr inbounds i16, i16* %r, i64 219 *)
(*   %438 = load i16, i16* %arrayidx9.1.27.1, align 2, !tbaa !3 *)
mov v438 mem0_438;
(*   %conv1.i.1.27.1 = sext i16 %438 to i32 *)
cast v_conv1_i_1_27_1@sint32 v438@sint16;
(*   %mul.i.1.27.1 = mul nsw i32 %conv1.i.1.27.1, -1517 *)
mul v_mul_i_1_27_1 v_conv1_i_1_27_1 (-1517)@sint32;
(*   %call.i.1.27.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.27.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_27_1, v_call_i_1_27_1);
(*   %arrayidx11.1.27.1 = getelementptr inbounds i16, i16* %r, i64 155 *)
(*   %439 = load i16, i16* %arrayidx11.1.27.1, align 2, !tbaa !3 *)
mov v439 mem0_310;
(*   %sub.1.27.1 = sub i16 %439, %call.i.1.27.1 *)
sub v_sub_1_27_1 v439 v_call_i_1_27_1;
(*   store i16 %sub.1.27.1, i16* %arrayidx9.1.27.1, align 2, !tbaa !3 *)
mov mem0_438 v_sub_1_27_1;
(*   %add21.1.27.1 = add i16 %439, %call.i.1.27.1 *)
add v_add21_1_27_1 v439 v_call_i_1_27_1;
(*   store i16 %add21.1.27.1, i16* %arrayidx11.1.27.1, align 2, !tbaa !3 *)
mov mem0_310 v_add21_1_27_1;
(*   %arrayidx9.1.28.1 = getelementptr inbounds i16, i16* %r, i64 220 *)
(*   %440 = load i16, i16* %arrayidx9.1.28.1, align 2, !tbaa !3 *)
mov v440 mem0_440;
(*   %conv1.i.1.28.1 = sext i16 %440 to i32 *)
cast v_conv1_i_1_28_1@sint32 v440@sint16;
(*   %mul.i.1.28.1 = mul nsw i32 %conv1.i.1.28.1, -1517 *)
mul v_mul_i_1_28_1 v_conv1_i_1_28_1 (-1517)@sint32;
(*   %call.i.1.28.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.28.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_28_1, v_call_i_1_28_1);
(*   %arrayidx11.1.28.1 = getelementptr inbounds i16, i16* %r, i64 156 *)
(*   %441 = load i16, i16* %arrayidx11.1.28.1, align 2, !tbaa !3 *)
mov v441 mem0_312;
(*   %sub.1.28.1 = sub i16 %441, %call.i.1.28.1 *)
sub v_sub_1_28_1 v441 v_call_i_1_28_1;
(*   store i16 %sub.1.28.1, i16* %arrayidx9.1.28.1, align 2, !tbaa !3 *)
mov mem0_440 v_sub_1_28_1;
(*   %add21.1.28.1 = add i16 %441, %call.i.1.28.1 *)
add v_add21_1_28_1 v441 v_call_i_1_28_1;
(*   store i16 %add21.1.28.1, i16* %arrayidx11.1.28.1, align 2, !tbaa !3 *)
mov mem0_312 v_add21_1_28_1;
(*   %arrayidx9.1.29.1 = getelementptr inbounds i16, i16* %r, i64 221 *)
(*   %442 = load i16, i16* %arrayidx9.1.29.1, align 2, !tbaa !3 *)
mov v442 mem0_442;
(*   %conv1.i.1.29.1 = sext i16 %442 to i32 *)
cast v_conv1_i_1_29_1@sint32 v442@sint16;
(*   %mul.i.1.29.1 = mul nsw i32 %conv1.i.1.29.1, -1517 *)
mul v_mul_i_1_29_1 v_conv1_i_1_29_1 (-1517)@sint32;
(*   %call.i.1.29.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.29.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_29_1, v_call_i_1_29_1);
(*   %arrayidx11.1.29.1 = getelementptr inbounds i16, i16* %r, i64 157 *)
(*   %443 = load i16, i16* %arrayidx11.1.29.1, align 2, !tbaa !3 *)
mov v443 mem0_314;
(*   %sub.1.29.1 = sub i16 %443, %call.i.1.29.1 *)
sub v_sub_1_29_1 v443 v_call_i_1_29_1;
(*   store i16 %sub.1.29.1, i16* %arrayidx9.1.29.1, align 2, !tbaa !3 *)
mov mem0_442 v_sub_1_29_1;
(*   %add21.1.29.1 = add i16 %443, %call.i.1.29.1 *)
add v_add21_1_29_1 v443 v_call_i_1_29_1;
(*   store i16 %add21.1.29.1, i16* %arrayidx11.1.29.1, align 2, !tbaa !3 *)
mov mem0_314 v_add21_1_29_1;
(*   %arrayidx9.1.30.1 = getelementptr inbounds i16, i16* %r, i64 222 *)
(*   %444 = load i16, i16* %arrayidx9.1.30.1, align 2, !tbaa !3 *)
mov v444 mem0_444;
(*   %conv1.i.1.30.1 = sext i16 %444 to i32 *)
cast v_conv1_i_1_30_1@sint32 v444@sint16;
(*   %mul.i.1.30.1 = mul nsw i32 %conv1.i.1.30.1, -1517 *)
mul v_mul_i_1_30_1 v_conv1_i_1_30_1 (-1517)@sint32;
(*   %call.i.1.30.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.30.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_30_1, v_call_i_1_30_1);
(*   %arrayidx11.1.30.1 = getelementptr inbounds i16, i16* %r, i64 158 *)
(*   %445 = load i16, i16* %arrayidx11.1.30.1, align 2, !tbaa !3 *)
mov v445 mem0_316;
(*   %sub.1.30.1 = sub i16 %445, %call.i.1.30.1 *)
sub v_sub_1_30_1 v445 v_call_i_1_30_1;
(*   store i16 %sub.1.30.1, i16* %arrayidx9.1.30.1, align 2, !tbaa !3 *)
mov mem0_444 v_sub_1_30_1;
(*   %add21.1.30.1 = add i16 %445, %call.i.1.30.1 *)
add v_add21_1_30_1 v445 v_call_i_1_30_1;
(*   store i16 %add21.1.30.1, i16* %arrayidx11.1.30.1, align 2, !tbaa !3 *)
mov mem0_316 v_add21_1_30_1;
(*   %arrayidx9.1.31.1 = getelementptr inbounds i16, i16* %r, i64 223 *)
(*   %446 = load i16, i16* %arrayidx9.1.31.1, align 2, !tbaa !3 *)
mov v446 mem0_446;
(*   %conv1.i.1.31.1 = sext i16 %446 to i32 *)
cast v_conv1_i_1_31_1@sint32 v446@sint16;
(*   %mul.i.1.31.1 = mul nsw i32 %conv1.i.1.31.1, -1517 *)
mul v_mul_i_1_31_1 v_conv1_i_1_31_1 (-1517)@sint32;
(*   %call.i.1.31.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.31.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_31_1, v_call_i_1_31_1);
(*   %arrayidx11.1.31.1 = getelementptr inbounds i16, i16* %r, i64 159 *)
(*   %447 = load i16, i16* %arrayidx11.1.31.1, align 2, !tbaa !3 *)
mov v447 mem0_318;
(*   %sub.1.31.1 = sub i16 %447, %call.i.1.31.1 *)
sub v_sub_1_31_1 v447 v_call_i_1_31_1;
(*   store i16 %sub.1.31.1, i16* %arrayidx9.1.31.1, align 2, !tbaa !3 *)
mov mem0_446 v_sub_1_31_1;
(*   %add21.1.31.1 = add i16 %447, %call.i.1.31.1 *)
add v_add21_1_31_1 v447 v_call_i_1_31_1;
(*   store i16 %add21.1.31.1, i16* %arrayidx11.1.31.1, align 2, !tbaa !3 *)
mov mem0_318 v_add21_1_31_1;
(*   %arrayidx9.1.32.1 = getelementptr inbounds i16, i16* %r, i64 224 *)
(*   %448 = load i16, i16* %arrayidx9.1.32.1, align 2, !tbaa !3 *)
mov v448 mem0_448;
(*   %conv1.i.1.32.1 = sext i16 %448 to i32 *)
cast v_conv1_i_1_32_1@sint32 v448@sint16;
(*   %mul.i.1.32.1 = mul nsw i32 %conv1.i.1.32.1, -1517 *)
mul v_mul_i_1_32_1 v_conv1_i_1_32_1 (-1517)@sint32;
(*   %call.i.1.32.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.32.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_32_1, v_call_i_1_32_1);
(*   %arrayidx11.1.32.1 = getelementptr inbounds i16, i16* %r, i64 160 *)
(*   %449 = load i16, i16* %arrayidx11.1.32.1, align 2, !tbaa !3 *)
mov v449 mem0_320;
(*   %sub.1.32.1 = sub i16 %449, %call.i.1.32.1 *)
sub v_sub_1_32_1 v449 v_call_i_1_32_1;
(*   store i16 %sub.1.32.1, i16* %arrayidx9.1.32.1, align 2, !tbaa !3 *)
mov mem0_448 v_sub_1_32_1;
(*   %add21.1.32.1 = add i16 %449, %call.i.1.32.1 *)
add v_add21_1_32_1 v449 v_call_i_1_32_1;
(*   store i16 %add21.1.32.1, i16* %arrayidx11.1.32.1, align 2, !tbaa !3 *)
mov mem0_320 v_add21_1_32_1;
(*   %arrayidx9.1.33.1 = getelementptr inbounds i16, i16* %r, i64 225 *)
(*   %450 = load i16, i16* %arrayidx9.1.33.1, align 2, !tbaa !3 *)
mov v450 mem0_450;
(*   %conv1.i.1.33.1 = sext i16 %450 to i32 *)
cast v_conv1_i_1_33_1@sint32 v450@sint16;
(*   %mul.i.1.33.1 = mul nsw i32 %conv1.i.1.33.1, -1517 *)
mul v_mul_i_1_33_1 v_conv1_i_1_33_1 (-1517)@sint32;
(*   %call.i.1.33.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.33.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_33_1, v_call_i_1_33_1);
(*   %arrayidx11.1.33.1 = getelementptr inbounds i16, i16* %r, i64 161 *)
(*   %451 = load i16, i16* %arrayidx11.1.33.1, align 2, !tbaa !3 *)
mov v451 mem0_322;
(*   %sub.1.33.1 = sub i16 %451, %call.i.1.33.1 *)
sub v_sub_1_33_1 v451 v_call_i_1_33_1;
(*   store i16 %sub.1.33.1, i16* %arrayidx9.1.33.1, align 2, !tbaa !3 *)
mov mem0_450 v_sub_1_33_1;
(*   %add21.1.33.1 = add i16 %451, %call.i.1.33.1 *)
add v_add21_1_33_1 v451 v_call_i_1_33_1;
(*   store i16 %add21.1.33.1, i16* %arrayidx11.1.33.1, align 2, !tbaa !3 *)
mov mem0_322 v_add21_1_33_1;
(*   %arrayidx9.1.34.1 = getelementptr inbounds i16, i16* %r, i64 226 *)
(*   %452 = load i16, i16* %arrayidx9.1.34.1, align 2, !tbaa !3 *)
mov v452 mem0_452;
(*   %conv1.i.1.34.1 = sext i16 %452 to i32 *)
cast v_conv1_i_1_34_1@sint32 v452@sint16;
(*   %mul.i.1.34.1 = mul nsw i32 %conv1.i.1.34.1, -1517 *)
mul v_mul_i_1_34_1 v_conv1_i_1_34_1 (-1517)@sint32;
(*   %call.i.1.34.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.34.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_34_1, v_call_i_1_34_1);
(*   %arrayidx11.1.34.1 = getelementptr inbounds i16, i16* %r, i64 162 *)
(*   %453 = load i16, i16* %arrayidx11.1.34.1, align 2, !tbaa !3 *)
mov v453 mem0_324;
(*   %sub.1.34.1 = sub i16 %453, %call.i.1.34.1 *)
sub v_sub_1_34_1 v453 v_call_i_1_34_1;
(*   store i16 %sub.1.34.1, i16* %arrayidx9.1.34.1, align 2, !tbaa !3 *)
mov mem0_452 v_sub_1_34_1;
(*   %add21.1.34.1 = add i16 %453, %call.i.1.34.1 *)
add v_add21_1_34_1 v453 v_call_i_1_34_1;
(*   store i16 %add21.1.34.1, i16* %arrayidx11.1.34.1, align 2, !tbaa !3 *)
mov mem0_324 v_add21_1_34_1;
(*   %arrayidx9.1.35.1 = getelementptr inbounds i16, i16* %r, i64 227 *)
(*   %454 = load i16, i16* %arrayidx9.1.35.1, align 2, !tbaa !3 *)
mov v454 mem0_454;
(*   %conv1.i.1.35.1 = sext i16 %454 to i32 *)
cast v_conv1_i_1_35_1@sint32 v454@sint16;
(*   %mul.i.1.35.1 = mul nsw i32 %conv1.i.1.35.1, -1517 *)
mul v_mul_i_1_35_1 v_conv1_i_1_35_1 (-1517)@sint32;
(*   %call.i.1.35.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.35.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_35_1, v_call_i_1_35_1);
(*   %arrayidx11.1.35.1 = getelementptr inbounds i16, i16* %r, i64 163 *)
(*   %455 = load i16, i16* %arrayidx11.1.35.1, align 2, !tbaa !3 *)
mov v455 mem0_326;
(*   %sub.1.35.1 = sub i16 %455, %call.i.1.35.1 *)
sub v_sub_1_35_1 v455 v_call_i_1_35_1;
(*   store i16 %sub.1.35.1, i16* %arrayidx9.1.35.1, align 2, !tbaa !3 *)
mov mem0_454 v_sub_1_35_1;
(*   %add21.1.35.1 = add i16 %455, %call.i.1.35.1 *)
add v_add21_1_35_1 v455 v_call_i_1_35_1;
(*   store i16 %add21.1.35.1, i16* %arrayidx11.1.35.1, align 2, !tbaa !3 *)
mov mem0_326 v_add21_1_35_1;
(*   %arrayidx9.1.36.1 = getelementptr inbounds i16, i16* %r, i64 228 *)
(*   %456 = load i16, i16* %arrayidx9.1.36.1, align 2, !tbaa !3 *)
mov v456 mem0_456;
(*   %conv1.i.1.36.1 = sext i16 %456 to i32 *)
cast v_conv1_i_1_36_1@sint32 v456@sint16;
(*   %mul.i.1.36.1 = mul nsw i32 %conv1.i.1.36.1, -1517 *)
mul v_mul_i_1_36_1 v_conv1_i_1_36_1 (-1517)@sint32;
(*   %call.i.1.36.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.36.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_36_1, v_call_i_1_36_1);
(*   %arrayidx11.1.36.1 = getelementptr inbounds i16, i16* %r, i64 164 *)
(*   %457 = load i16, i16* %arrayidx11.1.36.1, align 2, !tbaa !3 *)
mov v457 mem0_328;
(*   %sub.1.36.1 = sub i16 %457, %call.i.1.36.1 *)
sub v_sub_1_36_1 v457 v_call_i_1_36_1;
(*   store i16 %sub.1.36.1, i16* %arrayidx9.1.36.1, align 2, !tbaa !3 *)
mov mem0_456 v_sub_1_36_1;
(*   %add21.1.36.1 = add i16 %457, %call.i.1.36.1 *)
add v_add21_1_36_1 v457 v_call_i_1_36_1;
(*   store i16 %add21.1.36.1, i16* %arrayidx11.1.36.1, align 2, !tbaa !3 *)
mov mem0_328 v_add21_1_36_1;
(*   %arrayidx9.1.37.1 = getelementptr inbounds i16, i16* %r, i64 229 *)
(*   %458 = load i16, i16* %arrayidx9.1.37.1, align 2, !tbaa !3 *)
mov v458 mem0_458;
(*   %conv1.i.1.37.1 = sext i16 %458 to i32 *)
cast v_conv1_i_1_37_1@sint32 v458@sint16;
(*   %mul.i.1.37.1 = mul nsw i32 %conv1.i.1.37.1, -1517 *)
mul v_mul_i_1_37_1 v_conv1_i_1_37_1 (-1517)@sint32;
(*   %call.i.1.37.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.37.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_37_1, v_call_i_1_37_1);
(*   %arrayidx11.1.37.1 = getelementptr inbounds i16, i16* %r, i64 165 *)
(*   %459 = load i16, i16* %arrayidx11.1.37.1, align 2, !tbaa !3 *)
mov v459 mem0_330;
(*   %sub.1.37.1 = sub i16 %459, %call.i.1.37.1 *)
sub v_sub_1_37_1 v459 v_call_i_1_37_1;
(*   store i16 %sub.1.37.1, i16* %arrayidx9.1.37.1, align 2, !tbaa !3 *)
mov mem0_458 v_sub_1_37_1;
(*   %add21.1.37.1 = add i16 %459, %call.i.1.37.1 *)
add v_add21_1_37_1 v459 v_call_i_1_37_1;
(*   store i16 %add21.1.37.1, i16* %arrayidx11.1.37.1, align 2, !tbaa !3 *)
mov mem0_330 v_add21_1_37_1;
(*   %arrayidx9.1.38.1 = getelementptr inbounds i16, i16* %r, i64 230 *)
(*   %460 = load i16, i16* %arrayidx9.1.38.1, align 2, !tbaa !3 *)
mov v460 mem0_460;
(*   %conv1.i.1.38.1 = sext i16 %460 to i32 *)
cast v_conv1_i_1_38_1@sint32 v460@sint16;
(*   %mul.i.1.38.1 = mul nsw i32 %conv1.i.1.38.1, -1517 *)
mul v_mul_i_1_38_1 v_conv1_i_1_38_1 (-1517)@sint32;
(*   %call.i.1.38.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.38.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_38_1, v_call_i_1_38_1);
(*   %arrayidx11.1.38.1 = getelementptr inbounds i16, i16* %r, i64 166 *)
(*   %461 = load i16, i16* %arrayidx11.1.38.1, align 2, !tbaa !3 *)
mov v461 mem0_332;
(*   %sub.1.38.1 = sub i16 %461, %call.i.1.38.1 *)
sub v_sub_1_38_1 v461 v_call_i_1_38_1;
(*   store i16 %sub.1.38.1, i16* %arrayidx9.1.38.1, align 2, !tbaa !3 *)
mov mem0_460 v_sub_1_38_1;
(*   %add21.1.38.1 = add i16 %461, %call.i.1.38.1 *)
add v_add21_1_38_1 v461 v_call_i_1_38_1;
(*   store i16 %add21.1.38.1, i16* %arrayidx11.1.38.1, align 2, !tbaa !3 *)
mov mem0_332 v_add21_1_38_1;
(*   %arrayidx9.1.39.1 = getelementptr inbounds i16, i16* %r, i64 231 *)
(*   %462 = load i16, i16* %arrayidx9.1.39.1, align 2, !tbaa !3 *)
mov v462 mem0_462;
(*   %conv1.i.1.39.1 = sext i16 %462 to i32 *)
cast v_conv1_i_1_39_1@sint32 v462@sint16;
(*   %mul.i.1.39.1 = mul nsw i32 %conv1.i.1.39.1, -1517 *)
mul v_mul_i_1_39_1 v_conv1_i_1_39_1 (-1517)@sint32;
(*   %call.i.1.39.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.39.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_39_1, v_call_i_1_39_1);
(*   %arrayidx11.1.39.1 = getelementptr inbounds i16, i16* %r, i64 167 *)
(*   %463 = load i16, i16* %arrayidx11.1.39.1, align 2, !tbaa !3 *)
mov v463 mem0_334;
(*   %sub.1.39.1 = sub i16 %463, %call.i.1.39.1 *)
sub v_sub_1_39_1 v463 v_call_i_1_39_1;
(*   store i16 %sub.1.39.1, i16* %arrayidx9.1.39.1, align 2, !tbaa !3 *)
mov mem0_462 v_sub_1_39_1;
(*   %add21.1.39.1 = add i16 %463, %call.i.1.39.1 *)
add v_add21_1_39_1 v463 v_call_i_1_39_1;
(*   store i16 %add21.1.39.1, i16* %arrayidx11.1.39.1, align 2, !tbaa !3 *)
mov mem0_334 v_add21_1_39_1;
(*   %arrayidx9.1.40.1 = getelementptr inbounds i16, i16* %r, i64 232 *)
(*   %464 = load i16, i16* %arrayidx9.1.40.1, align 2, !tbaa !3 *)
mov v464 mem0_464;
(*   %conv1.i.1.40.1 = sext i16 %464 to i32 *)
cast v_conv1_i_1_40_1@sint32 v464@sint16;
(*   %mul.i.1.40.1 = mul nsw i32 %conv1.i.1.40.1, -1517 *)
mul v_mul_i_1_40_1 v_conv1_i_1_40_1 (-1517)@sint32;
(*   %call.i.1.40.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.40.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_40_1, v_call_i_1_40_1);
(*   %arrayidx11.1.40.1 = getelementptr inbounds i16, i16* %r, i64 168 *)
(*   %465 = load i16, i16* %arrayidx11.1.40.1, align 2, !tbaa !3 *)
mov v465 mem0_336;
(*   %sub.1.40.1 = sub i16 %465, %call.i.1.40.1 *)
sub v_sub_1_40_1 v465 v_call_i_1_40_1;
(*   store i16 %sub.1.40.1, i16* %arrayidx9.1.40.1, align 2, !tbaa !3 *)
mov mem0_464 v_sub_1_40_1;
(*   %add21.1.40.1 = add i16 %465, %call.i.1.40.1 *)
add v_add21_1_40_1 v465 v_call_i_1_40_1;
(*   store i16 %add21.1.40.1, i16* %arrayidx11.1.40.1, align 2, !tbaa !3 *)
mov mem0_336 v_add21_1_40_1;
(*   %arrayidx9.1.41.1 = getelementptr inbounds i16, i16* %r, i64 233 *)
(*   %466 = load i16, i16* %arrayidx9.1.41.1, align 2, !tbaa !3 *)
mov v466 mem0_466;
(*   %conv1.i.1.41.1 = sext i16 %466 to i32 *)
cast v_conv1_i_1_41_1@sint32 v466@sint16;
(*   %mul.i.1.41.1 = mul nsw i32 %conv1.i.1.41.1, -1517 *)
mul v_mul_i_1_41_1 v_conv1_i_1_41_1 (-1517)@sint32;
(*   %call.i.1.41.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.41.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_41_1, v_call_i_1_41_1);
(*   %arrayidx11.1.41.1 = getelementptr inbounds i16, i16* %r, i64 169 *)
(*   %467 = load i16, i16* %arrayidx11.1.41.1, align 2, !tbaa !3 *)
mov v467 mem0_338;
(*   %sub.1.41.1 = sub i16 %467, %call.i.1.41.1 *)
sub v_sub_1_41_1 v467 v_call_i_1_41_1;
(*   store i16 %sub.1.41.1, i16* %arrayidx9.1.41.1, align 2, !tbaa !3 *)
mov mem0_466 v_sub_1_41_1;
(*   %add21.1.41.1 = add i16 %467, %call.i.1.41.1 *)
add v_add21_1_41_1 v467 v_call_i_1_41_1;
(*   store i16 %add21.1.41.1, i16* %arrayidx11.1.41.1, align 2, !tbaa !3 *)
mov mem0_338 v_add21_1_41_1;
(*   %arrayidx9.1.42.1 = getelementptr inbounds i16, i16* %r, i64 234 *)
(*   %468 = load i16, i16* %arrayidx9.1.42.1, align 2, !tbaa !3 *)
mov v468 mem0_468;
(*   %conv1.i.1.42.1 = sext i16 %468 to i32 *)
cast v_conv1_i_1_42_1@sint32 v468@sint16;
(*   %mul.i.1.42.1 = mul nsw i32 %conv1.i.1.42.1, -1517 *)
mul v_mul_i_1_42_1 v_conv1_i_1_42_1 (-1517)@sint32;
(*   %call.i.1.42.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.42.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_42_1, v_call_i_1_42_1);
(*   %arrayidx11.1.42.1 = getelementptr inbounds i16, i16* %r, i64 170 *)
(*   %469 = load i16, i16* %arrayidx11.1.42.1, align 2, !tbaa !3 *)
mov v469 mem0_340;
(*   %sub.1.42.1 = sub i16 %469, %call.i.1.42.1 *)
sub v_sub_1_42_1 v469 v_call_i_1_42_1;
(*   store i16 %sub.1.42.1, i16* %arrayidx9.1.42.1, align 2, !tbaa !3 *)
mov mem0_468 v_sub_1_42_1;
(*   %add21.1.42.1 = add i16 %469, %call.i.1.42.1 *)
add v_add21_1_42_1 v469 v_call_i_1_42_1;
(*   store i16 %add21.1.42.1, i16* %arrayidx11.1.42.1, align 2, !tbaa !3 *)
mov mem0_340 v_add21_1_42_1;
(*   %arrayidx9.1.43.1 = getelementptr inbounds i16, i16* %r, i64 235 *)
(*   %470 = load i16, i16* %arrayidx9.1.43.1, align 2, !tbaa !3 *)
mov v470 mem0_470;
(*   %conv1.i.1.43.1 = sext i16 %470 to i32 *)
cast v_conv1_i_1_43_1@sint32 v470@sint16;
(*   %mul.i.1.43.1 = mul nsw i32 %conv1.i.1.43.1, -1517 *)
mul v_mul_i_1_43_1 v_conv1_i_1_43_1 (-1517)@sint32;
(*   %call.i.1.43.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.43.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_43_1, v_call_i_1_43_1);
(*   %arrayidx11.1.43.1 = getelementptr inbounds i16, i16* %r, i64 171 *)
(*   %471 = load i16, i16* %arrayidx11.1.43.1, align 2, !tbaa !3 *)
mov v471 mem0_342;
(*   %sub.1.43.1 = sub i16 %471, %call.i.1.43.1 *)
sub v_sub_1_43_1 v471 v_call_i_1_43_1;
(*   store i16 %sub.1.43.1, i16* %arrayidx9.1.43.1, align 2, !tbaa !3 *)
mov mem0_470 v_sub_1_43_1;
(*   %add21.1.43.1 = add i16 %471, %call.i.1.43.1 *)
add v_add21_1_43_1 v471 v_call_i_1_43_1;
(*   store i16 %add21.1.43.1, i16* %arrayidx11.1.43.1, align 2, !tbaa !3 *)
mov mem0_342 v_add21_1_43_1;
(*   %arrayidx9.1.44.1 = getelementptr inbounds i16, i16* %r, i64 236 *)
(*   %472 = load i16, i16* %arrayidx9.1.44.1, align 2, !tbaa !3 *)
mov v472 mem0_472;
(*   %conv1.i.1.44.1 = sext i16 %472 to i32 *)
cast v_conv1_i_1_44_1@sint32 v472@sint16;
(*   %mul.i.1.44.1 = mul nsw i32 %conv1.i.1.44.1, -1517 *)
mul v_mul_i_1_44_1 v_conv1_i_1_44_1 (-1517)@sint32;
(*   %call.i.1.44.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.44.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_44_1, v_call_i_1_44_1);
(*   %arrayidx11.1.44.1 = getelementptr inbounds i16, i16* %r, i64 172 *)
(*   %473 = load i16, i16* %arrayidx11.1.44.1, align 2, !tbaa !3 *)
mov v473 mem0_344;
(*   %sub.1.44.1 = sub i16 %473, %call.i.1.44.1 *)
sub v_sub_1_44_1 v473 v_call_i_1_44_1;
(*   store i16 %sub.1.44.1, i16* %arrayidx9.1.44.1, align 2, !tbaa !3 *)
mov mem0_472 v_sub_1_44_1;
(*   %add21.1.44.1 = add i16 %473, %call.i.1.44.1 *)
add v_add21_1_44_1 v473 v_call_i_1_44_1;
(*   store i16 %add21.1.44.1, i16* %arrayidx11.1.44.1, align 2, !tbaa !3 *)
mov mem0_344 v_add21_1_44_1;
(*   %arrayidx9.1.45.1 = getelementptr inbounds i16, i16* %r, i64 237 *)
(*   %474 = load i16, i16* %arrayidx9.1.45.1, align 2, !tbaa !3 *)
mov v474 mem0_474;
(*   %conv1.i.1.45.1 = sext i16 %474 to i32 *)
cast v_conv1_i_1_45_1@sint32 v474@sint16;
(*   %mul.i.1.45.1 = mul nsw i32 %conv1.i.1.45.1, -1517 *)
mul v_mul_i_1_45_1 v_conv1_i_1_45_1 (-1517)@sint32;
(*   %call.i.1.45.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.45.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_45_1, v_call_i_1_45_1);
(*   %arrayidx11.1.45.1 = getelementptr inbounds i16, i16* %r, i64 173 *)
(*   %475 = load i16, i16* %arrayidx11.1.45.1, align 2, !tbaa !3 *)
mov v475 mem0_346;
(*   %sub.1.45.1 = sub i16 %475, %call.i.1.45.1 *)
sub v_sub_1_45_1 v475 v_call_i_1_45_1;
(*   store i16 %sub.1.45.1, i16* %arrayidx9.1.45.1, align 2, !tbaa !3 *)
mov mem0_474 v_sub_1_45_1;
(*   %add21.1.45.1 = add i16 %475, %call.i.1.45.1 *)
add v_add21_1_45_1 v475 v_call_i_1_45_1;
(*   store i16 %add21.1.45.1, i16* %arrayidx11.1.45.1, align 2, !tbaa !3 *)
mov mem0_346 v_add21_1_45_1;
(*   %arrayidx9.1.46.1 = getelementptr inbounds i16, i16* %r, i64 238 *)
(*   %476 = load i16, i16* %arrayidx9.1.46.1, align 2, !tbaa !3 *)
mov v476 mem0_476;
(*   %conv1.i.1.46.1 = sext i16 %476 to i32 *)
cast v_conv1_i_1_46_1@sint32 v476@sint16;
(*   %mul.i.1.46.1 = mul nsw i32 %conv1.i.1.46.1, -1517 *)
mul v_mul_i_1_46_1 v_conv1_i_1_46_1 (-1517)@sint32;
(*   %call.i.1.46.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.46.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_46_1, v_call_i_1_46_1);
(*   %arrayidx11.1.46.1 = getelementptr inbounds i16, i16* %r, i64 174 *)
(*   %477 = load i16, i16* %arrayidx11.1.46.1, align 2, !tbaa !3 *)
mov v477 mem0_348;
(*   %sub.1.46.1 = sub i16 %477, %call.i.1.46.1 *)
sub v_sub_1_46_1 v477 v_call_i_1_46_1;
(*   store i16 %sub.1.46.1, i16* %arrayidx9.1.46.1, align 2, !tbaa !3 *)
mov mem0_476 v_sub_1_46_1;
(*   %add21.1.46.1 = add i16 %477, %call.i.1.46.1 *)
add v_add21_1_46_1 v477 v_call_i_1_46_1;
(*   store i16 %add21.1.46.1, i16* %arrayidx11.1.46.1, align 2, !tbaa !3 *)
mov mem0_348 v_add21_1_46_1;
(*   %arrayidx9.1.47.1 = getelementptr inbounds i16, i16* %r, i64 239 *)
(*   %478 = load i16, i16* %arrayidx9.1.47.1, align 2, !tbaa !3 *)
mov v478 mem0_478;
(*   %conv1.i.1.47.1 = sext i16 %478 to i32 *)
cast v_conv1_i_1_47_1@sint32 v478@sint16;
(*   %mul.i.1.47.1 = mul nsw i32 %conv1.i.1.47.1, -1517 *)
mul v_mul_i_1_47_1 v_conv1_i_1_47_1 (-1517)@sint32;
(*   %call.i.1.47.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.47.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_47_1, v_call_i_1_47_1);
(*   %arrayidx11.1.47.1 = getelementptr inbounds i16, i16* %r, i64 175 *)
(*   %479 = load i16, i16* %arrayidx11.1.47.1, align 2, !tbaa !3 *)
mov v479 mem0_350;
(*   %sub.1.47.1 = sub i16 %479, %call.i.1.47.1 *)
sub v_sub_1_47_1 v479 v_call_i_1_47_1;
(*   store i16 %sub.1.47.1, i16* %arrayidx9.1.47.1, align 2, !tbaa !3 *)
mov mem0_478 v_sub_1_47_1;
(*   %add21.1.47.1 = add i16 %479, %call.i.1.47.1 *)
add v_add21_1_47_1 v479 v_call_i_1_47_1;
(*   store i16 %add21.1.47.1, i16* %arrayidx11.1.47.1, align 2, !tbaa !3 *)
mov mem0_350 v_add21_1_47_1;
(*   %arrayidx9.1.48.1 = getelementptr inbounds i16, i16* %r, i64 240 *)
(*   %480 = load i16, i16* %arrayidx9.1.48.1, align 2, !tbaa !3 *)
mov v480 mem0_480;
(*   %conv1.i.1.48.1 = sext i16 %480 to i32 *)
cast v_conv1_i_1_48_1@sint32 v480@sint16;
(*   %mul.i.1.48.1 = mul nsw i32 %conv1.i.1.48.1, -1517 *)
mul v_mul_i_1_48_1 v_conv1_i_1_48_1 (-1517)@sint32;
(*   %call.i.1.48.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.48.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_48_1, v_call_i_1_48_1);
(*   %arrayidx11.1.48.1 = getelementptr inbounds i16, i16* %r, i64 176 *)
(*   %481 = load i16, i16* %arrayidx11.1.48.1, align 2, !tbaa !3 *)
mov v481 mem0_352;
(*   %sub.1.48.1 = sub i16 %481, %call.i.1.48.1 *)
sub v_sub_1_48_1 v481 v_call_i_1_48_1;
(*   store i16 %sub.1.48.1, i16* %arrayidx9.1.48.1, align 2, !tbaa !3 *)
mov mem0_480 v_sub_1_48_1;
(*   %add21.1.48.1 = add i16 %481, %call.i.1.48.1 *)
add v_add21_1_48_1 v481 v_call_i_1_48_1;
(*   store i16 %add21.1.48.1, i16* %arrayidx11.1.48.1, align 2, !tbaa !3 *)
mov mem0_352 v_add21_1_48_1;
(*   %arrayidx9.1.49.1 = getelementptr inbounds i16, i16* %r, i64 241 *)
(*   %482 = load i16, i16* %arrayidx9.1.49.1, align 2, !tbaa !3 *)
mov v482 mem0_482;
(*   %conv1.i.1.49.1 = sext i16 %482 to i32 *)
cast v_conv1_i_1_49_1@sint32 v482@sint16;
(*   %mul.i.1.49.1 = mul nsw i32 %conv1.i.1.49.1, -1517 *)
mul v_mul_i_1_49_1 v_conv1_i_1_49_1 (-1517)@sint32;
(*   %call.i.1.49.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.49.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_49_1, v_call_i_1_49_1);
(*   %arrayidx11.1.49.1 = getelementptr inbounds i16, i16* %r, i64 177 *)
(*   %483 = load i16, i16* %arrayidx11.1.49.1, align 2, !tbaa !3 *)
mov v483 mem0_354;
(*   %sub.1.49.1 = sub i16 %483, %call.i.1.49.1 *)
sub v_sub_1_49_1 v483 v_call_i_1_49_1;
(*   store i16 %sub.1.49.1, i16* %arrayidx9.1.49.1, align 2, !tbaa !3 *)
mov mem0_482 v_sub_1_49_1;
(*   %add21.1.49.1 = add i16 %483, %call.i.1.49.1 *)
add v_add21_1_49_1 v483 v_call_i_1_49_1;
(*   store i16 %add21.1.49.1, i16* %arrayidx11.1.49.1, align 2, !tbaa !3 *)
mov mem0_354 v_add21_1_49_1;
(*   %arrayidx9.1.50.1 = getelementptr inbounds i16, i16* %r, i64 242 *)
(*   %484 = load i16, i16* %arrayidx9.1.50.1, align 2, !tbaa !3 *)
mov v484 mem0_484;
(*   %conv1.i.1.50.1 = sext i16 %484 to i32 *)
cast v_conv1_i_1_50_1@sint32 v484@sint16;
(*   %mul.i.1.50.1 = mul nsw i32 %conv1.i.1.50.1, -1517 *)
mul v_mul_i_1_50_1 v_conv1_i_1_50_1 (-1517)@sint32;
(*   %call.i.1.50.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.50.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_50_1, v_call_i_1_50_1);
(*   %arrayidx11.1.50.1 = getelementptr inbounds i16, i16* %r, i64 178 *)
(*   %485 = load i16, i16* %arrayidx11.1.50.1, align 2, !tbaa !3 *)
mov v485 mem0_356;
(*   %sub.1.50.1 = sub i16 %485, %call.i.1.50.1 *)
sub v_sub_1_50_1 v485 v_call_i_1_50_1;
(*   store i16 %sub.1.50.1, i16* %arrayidx9.1.50.1, align 2, !tbaa !3 *)
mov mem0_484 v_sub_1_50_1;
(*   %add21.1.50.1 = add i16 %485, %call.i.1.50.1 *)
add v_add21_1_50_1 v485 v_call_i_1_50_1;
(*   store i16 %add21.1.50.1, i16* %arrayidx11.1.50.1, align 2, !tbaa !3 *)
mov mem0_356 v_add21_1_50_1;
(*   %arrayidx9.1.51.1 = getelementptr inbounds i16, i16* %r, i64 243 *)
(*   %486 = load i16, i16* %arrayidx9.1.51.1, align 2, !tbaa !3 *)
mov v486 mem0_486;
(*   %conv1.i.1.51.1 = sext i16 %486 to i32 *)
cast v_conv1_i_1_51_1@sint32 v486@sint16;
(*   %mul.i.1.51.1 = mul nsw i32 %conv1.i.1.51.1, -1517 *)
mul v_mul_i_1_51_1 v_conv1_i_1_51_1 (-1517)@sint32;
(*   %call.i.1.51.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.51.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_51_1, v_call_i_1_51_1);
(*   %arrayidx11.1.51.1 = getelementptr inbounds i16, i16* %r, i64 179 *)
(*   %487 = load i16, i16* %arrayidx11.1.51.1, align 2, !tbaa !3 *)
mov v487 mem0_358;
(*   %sub.1.51.1 = sub i16 %487, %call.i.1.51.1 *)
sub v_sub_1_51_1 v487 v_call_i_1_51_1;
(*   store i16 %sub.1.51.1, i16* %arrayidx9.1.51.1, align 2, !tbaa !3 *)
mov mem0_486 v_sub_1_51_1;
(*   %add21.1.51.1 = add i16 %487, %call.i.1.51.1 *)
add v_add21_1_51_1 v487 v_call_i_1_51_1;
(*   store i16 %add21.1.51.1, i16* %arrayidx11.1.51.1, align 2, !tbaa !3 *)
mov mem0_358 v_add21_1_51_1;
(*   %arrayidx9.1.52.1 = getelementptr inbounds i16, i16* %r, i64 244 *)
(*   %488 = load i16, i16* %arrayidx9.1.52.1, align 2, !tbaa !3 *)
mov v488 mem0_488;
(*   %conv1.i.1.52.1 = sext i16 %488 to i32 *)
cast v_conv1_i_1_52_1@sint32 v488@sint16;
(*   %mul.i.1.52.1 = mul nsw i32 %conv1.i.1.52.1, -1517 *)
mul v_mul_i_1_52_1 v_conv1_i_1_52_1 (-1517)@sint32;
(*   %call.i.1.52.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.52.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_52_1, v_call_i_1_52_1);
(*   %arrayidx11.1.52.1 = getelementptr inbounds i16, i16* %r, i64 180 *)
(*   %489 = load i16, i16* %arrayidx11.1.52.1, align 2, !tbaa !3 *)
mov v489 mem0_360;
(*   %sub.1.52.1 = sub i16 %489, %call.i.1.52.1 *)
sub v_sub_1_52_1 v489 v_call_i_1_52_1;
(*   store i16 %sub.1.52.1, i16* %arrayidx9.1.52.1, align 2, !tbaa !3 *)
mov mem0_488 v_sub_1_52_1;
(*   %add21.1.52.1 = add i16 %489, %call.i.1.52.1 *)
add v_add21_1_52_1 v489 v_call_i_1_52_1;
(*   store i16 %add21.1.52.1, i16* %arrayidx11.1.52.1, align 2, !tbaa !3 *)
mov mem0_360 v_add21_1_52_1;
(*   %arrayidx9.1.53.1 = getelementptr inbounds i16, i16* %r, i64 245 *)
(*   %490 = load i16, i16* %arrayidx9.1.53.1, align 2, !tbaa !3 *)
mov v490 mem0_490;
(*   %conv1.i.1.53.1 = sext i16 %490 to i32 *)
cast v_conv1_i_1_53_1@sint32 v490@sint16;
(*   %mul.i.1.53.1 = mul nsw i32 %conv1.i.1.53.1, -1517 *)
mul v_mul_i_1_53_1 v_conv1_i_1_53_1 (-1517)@sint32;
(*   %call.i.1.53.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.53.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_53_1, v_call_i_1_53_1);
(*   %arrayidx11.1.53.1 = getelementptr inbounds i16, i16* %r, i64 181 *)
(*   %491 = load i16, i16* %arrayidx11.1.53.1, align 2, !tbaa !3 *)
mov v491 mem0_362;
(*   %sub.1.53.1 = sub i16 %491, %call.i.1.53.1 *)
sub v_sub_1_53_1 v491 v_call_i_1_53_1;
(*   store i16 %sub.1.53.1, i16* %arrayidx9.1.53.1, align 2, !tbaa !3 *)
mov mem0_490 v_sub_1_53_1;
(*   %add21.1.53.1 = add i16 %491, %call.i.1.53.1 *)
add v_add21_1_53_1 v491 v_call_i_1_53_1;
(*   store i16 %add21.1.53.1, i16* %arrayidx11.1.53.1, align 2, !tbaa !3 *)
mov mem0_362 v_add21_1_53_1;
(*   %arrayidx9.1.54.1 = getelementptr inbounds i16, i16* %r, i64 246 *)
(*   %492 = load i16, i16* %arrayidx9.1.54.1, align 2, !tbaa !3 *)
mov v492 mem0_492;
(*   %conv1.i.1.54.1 = sext i16 %492 to i32 *)
cast v_conv1_i_1_54_1@sint32 v492@sint16;
(*   %mul.i.1.54.1 = mul nsw i32 %conv1.i.1.54.1, -1517 *)
mul v_mul_i_1_54_1 v_conv1_i_1_54_1 (-1517)@sint32;
(*   %call.i.1.54.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.54.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_54_1, v_call_i_1_54_1);
(*   %arrayidx11.1.54.1 = getelementptr inbounds i16, i16* %r, i64 182 *)
(*   %493 = load i16, i16* %arrayidx11.1.54.1, align 2, !tbaa !3 *)
mov v493 mem0_364;
(*   %sub.1.54.1 = sub i16 %493, %call.i.1.54.1 *)
sub v_sub_1_54_1 v493 v_call_i_1_54_1;
(*   store i16 %sub.1.54.1, i16* %arrayidx9.1.54.1, align 2, !tbaa !3 *)
mov mem0_492 v_sub_1_54_1;
(*   %add21.1.54.1 = add i16 %493, %call.i.1.54.1 *)
add v_add21_1_54_1 v493 v_call_i_1_54_1;
(*   store i16 %add21.1.54.1, i16* %arrayidx11.1.54.1, align 2, !tbaa !3 *)
mov mem0_364 v_add21_1_54_1;
(*   %arrayidx9.1.55.1 = getelementptr inbounds i16, i16* %r, i64 247 *)
(*   %494 = load i16, i16* %arrayidx9.1.55.1, align 2, !tbaa !3 *)
mov v494 mem0_494;
(*   %conv1.i.1.55.1 = sext i16 %494 to i32 *)
cast v_conv1_i_1_55_1@sint32 v494@sint16;
(*   %mul.i.1.55.1 = mul nsw i32 %conv1.i.1.55.1, -1517 *)
mul v_mul_i_1_55_1 v_conv1_i_1_55_1 (-1517)@sint32;
(*   %call.i.1.55.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.55.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_55_1, v_call_i_1_55_1);
(*   %arrayidx11.1.55.1 = getelementptr inbounds i16, i16* %r, i64 183 *)
(*   %495 = load i16, i16* %arrayidx11.1.55.1, align 2, !tbaa !3 *)
mov v495 mem0_366;
(*   %sub.1.55.1 = sub i16 %495, %call.i.1.55.1 *)
sub v_sub_1_55_1 v495 v_call_i_1_55_1;
(*   store i16 %sub.1.55.1, i16* %arrayidx9.1.55.1, align 2, !tbaa !3 *)
mov mem0_494 v_sub_1_55_1;
(*   %add21.1.55.1 = add i16 %495, %call.i.1.55.1 *)
add v_add21_1_55_1 v495 v_call_i_1_55_1;
(*   store i16 %add21.1.55.1, i16* %arrayidx11.1.55.1, align 2, !tbaa !3 *)
mov mem0_366 v_add21_1_55_1;
(*   %arrayidx9.1.56.1 = getelementptr inbounds i16, i16* %r, i64 248 *)
(*   %496 = load i16, i16* %arrayidx9.1.56.1, align 2, !tbaa !3 *)
mov v496 mem0_496;
(*   %conv1.i.1.56.1 = sext i16 %496 to i32 *)
cast v_conv1_i_1_56_1@sint32 v496@sint16;
(*   %mul.i.1.56.1 = mul nsw i32 %conv1.i.1.56.1, -1517 *)
mul v_mul_i_1_56_1 v_conv1_i_1_56_1 (-1517)@sint32;
(*   %call.i.1.56.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.56.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_56_1, v_call_i_1_56_1);
(*   %arrayidx11.1.56.1 = getelementptr inbounds i16, i16* %r, i64 184 *)
(*   %497 = load i16, i16* %arrayidx11.1.56.1, align 2, !tbaa !3 *)
mov v497 mem0_368;
(*   %sub.1.56.1 = sub i16 %497, %call.i.1.56.1 *)
sub v_sub_1_56_1 v497 v_call_i_1_56_1;
(*   store i16 %sub.1.56.1, i16* %arrayidx9.1.56.1, align 2, !tbaa !3 *)
mov mem0_496 v_sub_1_56_1;
(*   %add21.1.56.1 = add i16 %497, %call.i.1.56.1 *)
add v_add21_1_56_1 v497 v_call_i_1_56_1;
(*   store i16 %add21.1.56.1, i16* %arrayidx11.1.56.1, align 2, !tbaa !3 *)
mov mem0_368 v_add21_1_56_1;
(*   %arrayidx9.1.57.1 = getelementptr inbounds i16, i16* %r, i64 249 *)
(*   %498 = load i16, i16* %arrayidx9.1.57.1, align 2, !tbaa !3 *)
mov v498 mem0_498;
(*   %conv1.i.1.57.1 = sext i16 %498 to i32 *)
cast v_conv1_i_1_57_1@sint32 v498@sint16;
(*   %mul.i.1.57.1 = mul nsw i32 %conv1.i.1.57.1, -1517 *)
mul v_mul_i_1_57_1 v_conv1_i_1_57_1 (-1517)@sint32;
(*   %call.i.1.57.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.57.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_57_1, v_call_i_1_57_1);
(*   %arrayidx11.1.57.1 = getelementptr inbounds i16, i16* %r, i64 185 *)
(*   %499 = load i16, i16* %arrayidx11.1.57.1, align 2, !tbaa !3 *)
mov v499 mem0_370;
(*   %sub.1.57.1 = sub i16 %499, %call.i.1.57.1 *)
sub v_sub_1_57_1 v499 v_call_i_1_57_1;
(*   store i16 %sub.1.57.1, i16* %arrayidx9.1.57.1, align 2, !tbaa !3 *)
mov mem0_498 v_sub_1_57_1;
(*   %add21.1.57.1 = add i16 %499, %call.i.1.57.1 *)
add v_add21_1_57_1 v499 v_call_i_1_57_1;
(*   store i16 %add21.1.57.1, i16* %arrayidx11.1.57.1, align 2, !tbaa !3 *)
mov mem0_370 v_add21_1_57_1;
(*   %arrayidx9.1.58.1 = getelementptr inbounds i16, i16* %r, i64 250 *)
(*   %500 = load i16, i16* %arrayidx9.1.58.1, align 2, !tbaa !3 *)
mov v500 mem0_500;
(*   %conv1.i.1.58.1 = sext i16 %500 to i32 *)
cast v_conv1_i_1_58_1@sint32 v500@sint16;
(*   %mul.i.1.58.1 = mul nsw i32 %conv1.i.1.58.1, -1517 *)
mul v_mul_i_1_58_1 v_conv1_i_1_58_1 (-1517)@sint32;
(*   %call.i.1.58.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.58.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_58_1, v_call_i_1_58_1);
(*   %arrayidx11.1.58.1 = getelementptr inbounds i16, i16* %r, i64 186 *)
(*   %501 = load i16, i16* %arrayidx11.1.58.1, align 2, !tbaa !3 *)
mov v501 mem0_372;
(*   %sub.1.58.1 = sub i16 %501, %call.i.1.58.1 *)
sub v_sub_1_58_1 v501 v_call_i_1_58_1;
(*   store i16 %sub.1.58.1, i16* %arrayidx9.1.58.1, align 2, !tbaa !3 *)
mov mem0_500 v_sub_1_58_1;
(*   %add21.1.58.1 = add i16 %501, %call.i.1.58.1 *)
add v_add21_1_58_1 v501 v_call_i_1_58_1;
(*   store i16 %add21.1.58.1, i16* %arrayidx11.1.58.1, align 2, !tbaa !3 *)
mov mem0_372 v_add21_1_58_1;
(*   %arrayidx9.1.59.1 = getelementptr inbounds i16, i16* %r, i64 251 *)
(*   %502 = load i16, i16* %arrayidx9.1.59.1, align 2, !tbaa !3 *)
mov v502 mem0_502;
(*   %conv1.i.1.59.1 = sext i16 %502 to i32 *)
cast v_conv1_i_1_59_1@sint32 v502@sint16;
(*   %mul.i.1.59.1 = mul nsw i32 %conv1.i.1.59.1, -1517 *)
mul v_mul_i_1_59_1 v_conv1_i_1_59_1 (-1517)@sint32;
(*   %call.i.1.59.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.59.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_59_1, v_call_i_1_59_1);
(*   %arrayidx11.1.59.1 = getelementptr inbounds i16, i16* %r, i64 187 *)
(*   %503 = load i16, i16* %arrayidx11.1.59.1, align 2, !tbaa !3 *)
mov v503 mem0_374;
(*   %sub.1.59.1 = sub i16 %503, %call.i.1.59.1 *)
sub v_sub_1_59_1 v503 v_call_i_1_59_1;
(*   store i16 %sub.1.59.1, i16* %arrayidx9.1.59.1, align 2, !tbaa !3 *)
mov mem0_502 v_sub_1_59_1;
(*   %add21.1.59.1 = add i16 %503, %call.i.1.59.1 *)
add v_add21_1_59_1 v503 v_call_i_1_59_1;
(*   store i16 %add21.1.59.1, i16* %arrayidx11.1.59.1, align 2, !tbaa !3 *)
mov mem0_374 v_add21_1_59_1;
(*   %arrayidx9.1.60.1 = getelementptr inbounds i16, i16* %r, i64 252 *)
(*   %504 = load i16, i16* %arrayidx9.1.60.1, align 2, !tbaa !3 *)
mov v504 mem0_504;
(*   %conv1.i.1.60.1 = sext i16 %504 to i32 *)
cast v_conv1_i_1_60_1@sint32 v504@sint16;
(*   %mul.i.1.60.1 = mul nsw i32 %conv1.i.1.60.1, -1517 *)
mul v_mul_i_1_60_1 v_conv1_i_1_60_1 (-1517)@sint32;
(*   %call.i.1.60.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.60.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_60_1, v_call_i_1_60_1);
(*   %arrayidx11.1.60.1 = getelementptr inbounds i16, i16* %r, i64 188 *)
(*   %505 = load i16, i16* %arrayidx11.1.60.1, align 2, !tbaa !3 *)
mov v505 mem0_376;
(*   %sub.1.60.1 = sub i16 %505, %call.i.1.60.1 *)
sub v_sub_1_60_1 v505 v_call_i_1_60_1;
(*   store i16 %sub.1.60.1, i16* %arrayidx9.1.60.1, align 2, !tbaa !3 *)
mov mem0_504 v_sub_1_60_1;
(*   %add21.1.60.1 = add i16 %505, %call.i.1.60.1 *)
add v_add21_1_60_1 v505 v_call_i_1_60_1;
(*   store i16 %add21.1.60.1, i16* %arrayidx11.1.60.1, align 2, !tbaa !3 *)
mov mem0_376 v_add21_1_60_1;
(*   %arrayidx9.1.61.1 = getelementptr inbounds i16, i16* %r, i64 253 *)
(*   %506 = load i16, i16* %arrayidx9.1.61.1, align 2, !tbaa !3 *)
mov v506 mem0_506;
(*   %conv1.i.1.61.1 = sext i16 %506 to i32 *)
cast v_conv1_i_1_61_1@sint32 v506@sint16;
(*   %mul.i.1.61.1 = mul nsw i32 %conv1.i.1.61.1, -1517 *)
mul v_mul_i_1_61_1 v_conv1_i_1_61_1 (-1517)@sint32;
(*   %call.i.1.61.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.61.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_61_1, v_call_i_1_61_1);
(*   %arrayidx11.1.61.1 = getelementptr inbounds i16, i16* %r, i64 189 *)
(*   %507 = load i16, i16* %arrayidx11.1.61.1, align 2, !tbaa !3 *)
mov v507 mem0_378;
(*   %sub.1.61.1 = sub i16 %507, %call.i.1.61.1 *)
sub v_sub_1_61_1 v507 v_call_i_1_61_1;
(*   store i16 %sub.1.61.1, i16* %arrayidx9.1.61.1, align 2, !tbaa !3 *)
mov mem0_506 v_sub_1_61_1;
(*   %add21.1.61.1 = add i16 %507, %call.i.1.61.1 *)
add v_add21_1_61_1 v507 v_call_i_1_61_1;
(*   store i16 %add21.1.61.1, i16* %arrayidx11.1.61.1, align 2, !tbaa !3 *)
mov mem0_378 v_add21_1_61_1;
(*   %arrayidx9.1.62.1 = getelementptr inbounds i16, i16* %r, i64 254 *)
(*   %508 = load i16, i16* %arrayidx9.1.62.1, align 2, !tbaa !3 *)
mov v508 mem0_508;
(*   %conv1.i.1.62.1 = sext i16 %508 to i32 *)
cast v_conv1_i_1_62_1@sint32 v508@sint16;
(*   %mul.i.1.62.1 = mul nsw i32 %conv1.i.1.62.1, -1517 *)
mul v_mul_i_1_62_1 v_conv1_i_1_62_1 (-1517)@sint32;
(*   %call.i.1.62.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.62.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_62_1, v_call_i_1_62_1);
(*   %arrayidx11.1.62.1 = getelementptr inbounds i16, i16* %r, i64 190 *)
(*   %509 = load i16, i16* %arrayidx11.1.62.1, align 2, !tbaa !3 *)
mov v509 mem0_380;
(*   %sub.1.62.1 = sub i16 %509, %call.i.1.62.1 *)
sub v_sub_1_62_1 v509 v_call_i_1_62_1;
(*   store i16 %sub.1.62.1, i16* %arrayidx9.1.62.1, align 2, !tbaa !3 *)
mov mem0_508 v_sub_1_62_1;
(*   %add21.1.62.1 = add i16 %509, %call.i.1.62.1 *)
add v_add21_1_62_1 v509 v_call_i_1_62_1;
(*   store i16 %add21.1.62.1, i16* %arrayidx11.1.62.1, align 2, !tbaa !3 *)
mov mem0_380 v_add21_1_62_1;
(*   %arrayidx9.1.63.1 = getelementptr inbounds i16, i16* %r, i64 255 *)
(*   %510 = load i16, i16* %arrayidx9.1.63.1, align 2, !tbaa !3 *)
mov v510 mem0_510;
(*   %conv1.i.1.63.1 = sext i16 %510 to i32 *)
cast v_conv1_i_1_63_1@sint32 v510@sint16;
(*   %mul.i.1.63.1 = mul nsw i32 %conv1.i.1.63.1, -1517 *)
mul v_mul_i_1_63_1 v_conv1_i_1_63_1 (-1517)@sint32;
(*   %call.i.1.63.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1.63.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1_63_1, v_call_i_1_63_1);
(*   %arrayidx11.1.63.1 = getelementptr inbounds i16, i16* %r, i64 191 *)
(*   %511 = load i16, i16* %arrayidx11.1.63.1, align 2, !tbaa !3 *)
mov v511 mem0_382;
(*   %sub.1.63.1 = sub i16 %511, %call.i.1.63.1 *)
sub v_sub_1_63_1 v511 v_call_i_1_63_1;
(*   store i16 %sub.1.63.1, i16* %arrayidx9.1.63.1, align 2, !tbaa !3 *)
mov mem0_510 v_sub_1_63_1;
(*   %add21.1.63.1 = add i16 %511, %call.i.1.63.1 *)
add v_add21_1_63_1 v511 v_call_i_1_63_1;
(*   store i16 %add21.1.63.1, i16* %arrayidx11.1.63.1, align 2, !tbaa !3 *)
mov mem0_382 v_add21_1_63_1;


{and [ 
eqmod
(
mem0_0_k1*(x**0) + mem0_2_k1*(x**1) + mem0_4_k1*(x**2) + mem0_6_k1*(x**3) + 
mem0_8_k1*(x**4) + mem0_10_k1*(x**5) + mem0_12_k1*(x**6) + mem0_14_k1*(x**7) + 
mem0_16_k1*(x**8) + mem0_18_k1*(x**9) + mem0_20_k1*(x**10) + mem0_22_k1*(x**11) + 
mem0_24_k1*(x**12) + mem0_26_k1*(x**13) + mem0_28_k1*(x**14) + mem0_30_k1*(x**15) + 
mem0_32_k1*(x**16) + mem0_34_k1*(x**17) + mem0_36_k1*(x**18) + mem0_38_k1*(x**19) + 
mem0_40_k1*(x**20) + mem0_42_k1*(x**21) + mem0_44_k1*(x**22) + mem0_46_k1*(x**23) + 
mem0_48_k1*(x**24) + mem0_50_k1*(x**25) + mem0_52_k1*(x**26) + mem0_54_k1*(x**27) + 
mem0_56_k1*(x**28) + mem0_58_k1*(x**29) + mem0_60_k1*(x**30) + mem0_62_k1*(x**31) + 
mem0_64_k1*(x**32) + mem0_66_k1*(x**33) + mem0_68_k1*(x**34) + mem0_70_k1*(x**35) + 
mem0_72_k1*(x**36) + mem0_74_k1*(x**37) + mem0_76_k1*(x**38) + mem0_78_k1*(x**39) + 
mem0_80_k1*(x**40) + mem0_82_k1*(x**41) + mem0_84_k1*(x**42) + mem0_86_k1*(x**43) + 
mem0_88_k1*(x**44) + mem0_90_k1*(x**45) + mem0_92_k1*(x**46) + mem0_94_k1*(x**47) + 
mem0_96_k1*(x**48) + mem0_98_k1*(x**49) + mem0_100_k1*(x**50) + mem0_102_k1*(x**51) + 
mem0_104_k1*(x**52) + mem0_106_k1*(x**53) + mem0_108_k1*(x**54) + mem0_110_k1*(x**55) + 
mem0_112_k1*(x**56) + mem0_114_k1*(x**57) + mem0_116_k1*(x**58) + mem0_118_k1*(x**59) + 
mem0_120_k1*(x**60) + mem0_122_k1*(x**61) + mem0_124_k1*(x**62) + mem0_126_k1*(x**63) + 
mem0_128_k1*(x**64) + mem0_130_k1*(x**65) + mem0_132_k1*(x**66) + mem0_134_k1*(x**67) + 
mem0_136_k1*(x**68) + mem0_138_k1*(x**69) + mem0_140_k1*(x**70) + mem0_142_k1*(x**71) + 
mem0_144_k1*(x**72) + mem0_146_k1*(x**73) + mem0_148_k1*(x**74) + mem0_150_k1*(x**75) + 
mem0_152_k1*(x**76) + mem0_154_k1*(x**77) + mem0_156_k1*(x**78) + mem0_158_k1*(x**79) + 
mem0_160_k1*(x**80) + mem0_162_k1*(x**81) + mem0_164_k1*(x**82) + mem0_166_k1*(x**83) + 
mem0_168_k1*(x**84) + mem0_170_k1*(x**85) + mem0_172_k1*(x**86) + mem0_174_k1*(x**87) + 
mem0_176_k1*(x**88) + mem0_178_k1*(x**89) + mem0_180_k1*(x**90) + mem0_182_k1*(x**91) + 
mem0_184_k1*(x**92) + mem0_186_k1*(x**93) + mem0_188_k1*(x**94) + mem0_190_k1*(x**95) + 
mem0_192_k1*(x**96) + mem0_194_k1*(x**97) + mem0_196_k1*(x**98) + mem0_198_k1*(x**99) + 
mem0_200_k1*(x**100) + mem0_202_k1*(x**101) + mem0_204_k1*(x**102) + mem0_206_k1*(x**103) + 
mem0_208_k1*(x**104) + mem0_210_k1*(x**105) + mem0_212_k1*(x**106) + mem0_214_k1*(x**107) + 
mem0_216_k1*(x**108) + mem0_218_k1*(x**109) + mem0_220_k1*(x**110) + mem0_222_k1*(x**111) + 
mem0_224_k1*(x**112) + mem0_226_k1*(x**113) + mem0_228_k1*(x**114) + mem0_230_k1*(x**115) + 
mem0_232_k1*(x**116) + mem0_234_k1*(x**117) + mem0_236_k1*(x**118) + mem0_238_k1*(x**119) + 
mem0_240_k1*(x**120) + mem0_242_k1*(x**121) + mem0_244_k1*(x**122) + mem0_246_k1*(x**123) + 
mem0_248_k1*(x**124) + mem0_250_k1*(x**125) + mem0_252_k1*(x**126) + mem0_254_k1*(x**127)
)
(
mem0_0*(x**0) + mem0_2*(x**1) + mem0_4*(x**2) + mem0_6*(x**3) + 
mem0_8*(x**4) + mem0_10*(x**5) + mem0_12*(x**6) + mem0_14*(x**7) + 
mem0_16*(x**8) + mem0_18*(x**9) + mem0_20*(x**10) + mem0_22*(x**11) + 
mem0_24*(x**12) + mem0_26*(x**13) + mem0_28*(x**14) + mem0_30*(x**15) + 
mem0_32*(x**16) + mem0_34*(x**17) + mem0_36*(x**18) + mem0_38*(x**19) + 
mem0_40*(x**20) + mem0_42*(x**21) + mem0_44*(x**22) + mem0_46*(x**23) + 
mem0_48*(x**24) + mem0_50*(x**25) + mem0_52*(x**26) + mem0_54*(x**27) + 
mem0_56*(x**28) + mem0_58*(x**29) + mem0_60*(x**30) + mem0_62*(x**31) + 
mem0_64*(x**32) + mem0_66*(x**33) + mem0_68*(x**34) + mem0_70*(x**35) + 
mem0_72*(x**36) + mem0_74*(x**37) + mem0_76*(x**38) + mem0_78*(x**39) + 
mem0_80*(x**40) + mem0_82*(x**41) + mem0_84*(x**42) + mem0_86*(x**43) + 
mem0_88*(x**44) + mem0_90*(x**45) + mem0_92*(x**46) + mem0_94*(x**47) + 
mem0_96*(x**48) + mem0_98*(x**49) + mem0_100*(x**50) + mem0_102*(x**51) + 
mem0_104*(x**52) + mem0_106*(x**53) + mem0_108*(x**54) + mem0_110*(x**55) + 
mem0_112*(x**56) + mem0_114*(x**57) + mem0_116*(x**58) + mem0_118*(x**59) + 
mem0_120*(x**60) + mem0_122*(x**61) + mem0_124*(x**62) + mem0_126*(x**63)
)
[3329, x**64 - 2580],

eqmod
(
mem0_0_k1*(x**0) + mem0_2_k1*(x**1) + mem0_4_k1*(x**2) + mem0_6_k1*(x**3) + 
mem0_8_k1*(x**4) + mem0_10_k1*(x**5) + mem0_12_k1*(x**6) + mem0_14_k1*(x**7) + 
mem0_16_k1*(x**8) + mem0_18_k1*(x**9) + mem0_20_k1*(x**10) + mem0_22_k1*(x**11) + 
mem0_24_k1*(x**12) + mem0_26_k1*(x**13) + mem0_28_k1*(x**14) + mem0_30_k1*(x**15) + 
mem0_32_k1*(x**16) + mem0_34_k1*(x**17) + mem0_36_k1*(x**18) + mem0_38_k1*(x**19) + 
mem0_40_k1*(x**20) + mem0_42_k1*(x**21) + mem0_44_k1*(x**22) + mem0_46_k1*(x**23) + 
mem0_48_k1*(x**24) + mem0_50_k1*(x**25) + mem0_52_k1*(x**26) + mem0_54_k1*(x**27) + 
mem0_56_k1*(x**28) + mem0_58_k1*(x**29) + mem0_60_k1*(x**30) + mem0_62_k1*(x**31) + 
mem0_64_k1*(x**32) + mem0_66_k1*(x**33) + mem0_68_k1*(x**34) + mem0_70_k1*(x**35) + 
mem0_72_k1*(x**36) + mem0_74_k1*(x**37) + mem0_76_k1*(x**38) + mem0_78_k1*(x**39) + 
mem0_80_k1*(x**40) + mem0_82_k1*(x**41) + mem0_84_k1*(x**42) + mem0_86_k1*(x**43) + 
mem0_88_k1*(x**44) + mem0_90_k1*(x**45) + mem0_92_k1*(x**46) + mem0_94_k1*(x**47) + 
mem0_96_k1*(x**48) + mem0_98_k1*(x**49) + mem0_100_k1*(x**50) + mem0_102_k1*(x**51) + 
mem0_104_k1*(x**52) + mem0_106_k1*(x**53) + mem0_108_k1*(x**54) + mem0_110_k1*(x**55) + 
mem0_112_k1*(x**56) + mem0_114_k1*(x**57) + mem0_116_k1*(x**58) + mem0_118_k1*(x**59) + 
mem0_120_k1*(x**60) + mem0_122_k1*(x**61) + mem0_124_k1*(x**62) + mem0_126_k1*(x**63) + 
mem0_128_k1*(x**64) + mem0_130_k1*(x**65) + mem0_132_k1*(x**66) + mem0_134_k1*(x**67) + 
mem0_136_k1*(x**68) + mem0_138_k1*(x**69) + mem0_140_k1*(x**70) + mem0_142_k1*(x**71) + 
mem0_144_k1*(x**72) + mem0_146_k1*(x**73) + mem0_148_k1*(x**74) + mem0_150_k1*(x**75) + 
mem0_152_k1*(x**76) + mem0_154_k1*(x**77) + mem0_156_k1*(x**78) + mem0_158_k1*(x**79) + 
mem0_160_k1*(x**80) + mem0_162_k1*(x**81) + mem0_164_k1*(x**82) + mem0_166_k1*(x**83) + 
mem0_168_k1*(x**84) + mem0_170_k1*(x**85) + mem0_172_k1*(x**86) + mem0_174_k1*(x**87) + 
mem0_176_k1*(x**88) + mem0_178_k1*(x**89) + mem0_180_k1*(x**90) + mem0_182_k1*(x**91) + 
mem0_184_k1*(x**92) + mem0_186_k1*(x**93) + mem0_188_k1*(x**94) + mem0_190_k1*(x**95) + 
mem0_192_k1*(x**96) + mem0_194_k1*(x**97) + mem0_196_k1*(x**98) + mem0_198_k1*(x**99) + 
mem0_200_k1*(x**100) + mem0_202_k1*(x**101) + mem0_204_k1*(x**102) + mem0_206_k1*(x**103) + 
mem0_208_k1*(x**104) + mem0_210_k1*(x**105) + mem0_212_k1*(x**106) + mem0_214_k1*(x**107) + 
mem0_216_k1*(x**108) + mem0_218_k1*(x**109) + mem0_220_k1*(x**110) + mem0_222_k1*(x**111) + 
mem0_224_k1*(x**112) + mem0_226_k1*(x**113) + mem0_228_k1*(x**114) + mem0_230_k1*(x**115) + 
mem0_232_k1*(x**116) + mem0_234_k1*(x**117) + mem0_236_k1*(x**118) + mem0_238_k1*(x**119) + 
mem0_240_k1*(x**120) + mem0_242_k1*(x**121) + mem0_244_k1*(x**122) + mem0_246_k1*(x**123) + 
mem0_248_k1*(x**124) + mem0_250_k1*(x**125) + mem0_252_k1*(x**126) + mem0_254_k1*(x**127)
)
(
mem0_128*(x**0) + mem0_130*(x**1) + mem0_132*(x**2) + mem0_134*(x**3) + 
mem0_136*(x**4) + mem0_138*(x**5) + mem0_140*(x**6) + mem0_142*(x**7) + 
mem0_144*(x**8) + mem0_146*(x**9) + mem0_148*(x**10) + mem0_150*(x**11) + 
mem0_152*(x**12) + mem0_154*(x**13) + mem0_156*(x**14) + mem0_158*(x**15) + 
mem0_160*(x**16) + mem0_162*(x**17) + mem0_164*(x**18) + mem0_166*(x**19) + 
mem0_168*(x**20) + mem0_170*(x**21) + mem0_172*(x**22) + mem0_174*(x**23) + 
mem0_176*(x**24) + mem0_178*(x**25) + mem0_180*(x**26) + mem0_182*(x**27) + 
mem0_184*(x**28) + mem0_186*(x**29) + mem0_188*(x**30) + mem0_190*(x**31) + 
mem0_192*(x**32) + mem0_194*(x**33) + mem0_196*(x**34) + mem0_198*(x**35) + 
mem0_200*(x**36) + mem0_202*(x**37) + mem0_204*(x**38) + mem0_206*(x**39) + 
mem0_208*(x**40) + mem0_210*(x**41) + mem0_212*(x**42) + mem0_214*(x**43) + 
mem0_216*(x**44) + mem0_218*(x**45) + mem0_220*(x**46) + mem0_222*(x**47) + 
mem0_224*(x**48) + mem0_226*(x**49) + mem0_228*(x**50) + mem0_230*(x**51) + 
mem0_232*(x**52) + mem0_234*(x**53) + mem0_236*(x**54) + mem0_238*(x**55) + 
mem0_240*(x**56) + mem0_242*(x**57) + mem0_244*(x**58) + mem0_246*(x**59) + 
mem0_248*(x**60) + mem0_250*(x**61) + mem0_252*(x**62) + mem0_254*(x**63)
)
[3329, x**64 - 749],
eqmod
(
mem0_256_k1*(x**0) + mem0_258_k1*(x**1) + mem0_260_k1*(x**2) + mem0_262_k1*(x**3) + 
mem0_264_k1*(x**4) + mem0_266_k1*(x**5) + mem0_268_k1*(x**6) + mem0_270_k1*(x**7) + 
mem0_272_k1*(x**8) + mem0_274_k1*(x**9) + mem0_276_k1*(x**10) + mem0_278_k1*(x**11) + 
mem0_280_k1*(x**12) + mem0_282_k1*(x**13) + mem0_284_k1*(x**14) + mem0_286_k1*(x**15) + 
mem0_288_k1*(x**16) + mem0_290_k1*(x**17) + mem0_292_k1*(x**18) + mem0_294_k1*(x**19) + 
mem0_296_k1*(x**20) + mem0_298_k1*(x**21) + mem0_300_k1*(x**22) + mem0_302_k1*(x**23) + 
mem0_304_k1*(x**24) + mem0_306_k1*(x**25) + mem0_308_k1*(x**26) + mem0_310_k1*(x**27) + 
mem0_312_k1*(x**28) + mem0_314_k1*(x**29) + mem0_316_k1*(x**30) + mem0_318_k1*(x**31) + 
mem0_320_k1*(x**32) + mem0_322_k1*(x**33) + mem0_324_k1*(x**34) + mem0_326_k1*(x**35) + 
mem0_328_k1*(x**36) + mem0_330_k1*(x**37) + mem0_332_k1*(x**38) + mem0_334_k1*(x**39) + 
mem0_336_k1*(x**40) + mem0_338_k1*(x**41) + mem0_340_k1*(x**42) + mem0_342_k1*(x**43) + 
mem0_344_k1*(x**44) + mem0_346_k1*(x**45) + mem0_348_k1*(x**46) + mem0_350_k1*(x**47) + 
mem0_352_k1*(x**48) + mem0_354_k1*(x**49) + mem0_356_k1*(x**50) + mem0_358_k1*(x**51) + 
mem0_360_k1*(x**52) + mem0_362_k1*(x**53) + mem0_364_k1*(x**54) + mem0_366_k1*(x**55) + 
mem0_368_k1*(x**56) + mem0_370_k1*(x**57) + mem0_372_k1*(x**58) + mem0_374_k1*(x**59) + 
mem0_376_k1*(x**60) + mem0_378_k1*(x**61) + mem0_380_k1*(x**62) + mem0_382_k1*(x**63) + 
mem0_384_k1*(x**64) + mem0_386_k1*(x**65) + mem0_388_k1*(x**66) + mem0_390_k1*(x**67) + 
mem0_392_k1*(x**68) + mem0_394_k1*(x**69) + mem0_396_k1*(x**70) + mem0_398_k1*(x**71) + 
mem0_400_k1*(x**72) + mem0_402_k1*(x**73) + mem0_404_k1*(x**74) + mem0_406_k1*(x**75) + 
mem0_408_k1*(x**76) + mem0_410_k1*(x**77) + mem0_412_k1*(x**78) + mem0_414_k1*(x**79) + 
mem0_416_k1*(x**80) + mem0_418_k1*(x**81) + mem0_420_k1*(x**82) + mem0_422_k1*(x**83) + 
mem0_424_k1*(x**84) + mem0_426_k1*(x**85) + mem0_428_k1*(x**86) + mem0_430_k1*(x**87) + 
mem0_432_k1*(x**88) + mem0_434_k1*(x**89) + mem0_436_k1*(x**90) + mem0_438_k1*(x**91) + 
mem0_440_k1*(x**92) + mem0_442_k1*(x**93) + mem0_444_k1*(x**94) + mem0_446_k1*(x**95) + 
mem0_448_k1*(x**96) + mem0_450_k1*(x**97) + mem0_452_k1*(x**98) + mem0_454_k1*(x**99) + 
mem0_456_k1*(x**100) + mem0_458_k1*(x**101) + mem0_460_k1*(x**102) + mem0_462_k1*(x**103) + 
mem0_464_k1*(x**104) + mem0_466_k1*(x**105) + mem0_468_k1*(x**106) + mem0_470_k1*(x**107) + 
mem0_472_k1*(x**108) + mem0_474_k1*(x**109) + mem0_476_k1*(x**110) + mem0_478_k1*(x**111) + 
mem0_480_k1*(x**112) + mem0_482_k1*(x**113) + mem0_484_k1*(x**114) + mem0_486_k1*(x**115) + 
mem0_488_k1*(x**116) + mem0_490_k1*(x**117) + mem0_492_k1*(x**118) + mem0_494_k1*(x**119) + 
mem0_496_k1*(x**120) + mem0_498_k1*(x**121) + mem0_500_k1*(x**122) + mem0_502_k1*(x**123) + 
mem0_504_k1*(x**124) + mem0_506_k1*(x**125) + mem0_508_k1*(x**126) + mem0_510_k1*(x**127)
)
(
mem0_256*(x**0) + mem0_258*(x**1) + mem0_260*(x**2) + mem0_262*(x**3) + 
mem0_264*(x**4) + mem0_266*(x**5) + mem0_268*(x**6) + mem0_270*(x**7) + 
mem0_272*(x**8) + mem0_274*(x**9) + mem0_276*(x**10) + mem0_278*(x**11) + 
mem0_280*(x**12) + mem0_282*(x**13) + mem0_284*(x**14) + mem0_286*(x**15) + 
mem0_288*(x**16) + mem0_290*(x**17) + mem0_292*(x**18) + mem0_294*(x**19) + 
mem0_296*(x**20) + mem0_298*(x**21) + mem0_300*(x**22) + mem0_302*(x**23) + 
mem0_304*(x**24) + mem0_306*(x**25) + mem0_308*(x**26) + mem0_310*(x**27) + 
mem0_312*(x**28) + mem0_314*(x**29) + mem0_316*(x**30) + mem0_318*(x**31) + 
mem0_320*(x**32) + mem0_322*(x**33) + mem0_324*(x**34) + mem0_326*(x**35) + 
mem0_328*(x**36) + mem0_330*(x**37) + mem0_332*(x**38) + mem0_334*(x**39) + 
mem0_336*(x**40) + mem0_338*(x**41) + mem0_340*(x**42) + mem0_342*(x**43) + 
mem0_344*(x**44) + mem0_346*(x**45) + mem0_348*(x**46) + mem0_350*(x**47) + 
mem0_352*(x**48) + mem0_354*(x**49) + mem0_356*(x**50) + mem0_358*(x**51) + 
mem0_360*(x**52) + mem0_362*(x**53) + mem0_364*(x**54) + mem0_366*(x**55) + 
mem0_368*(x**56) + mem0_370*(x**57) + mem0_372*(x**58) + mem0_374*(x**59) + 
mem0_376*(x**60) + mem0_378*(x**61) + mem0_380*(x**62) + mem0_382*(x**63)
)
[3329, x**64 - 3289],

eqmod
(
mem0_256_k1*(x**0) + mem0_258_k1*(x**1) + mem0_260_k1*(x**2) + mem0_262_k1*(x**3) + 
mem0_264_k1*(x**4) + mem0_266_k1*(x**5) + mem0_268_k1*(x**6) + mem0_270_k1*(x**7) + 
mem0_272_k1*(x**8) + mem0_274_k1*(x**9) + mem0_276_k1*(x**10) + mem0_278_k1*(x**11) + 
mem0_280_k1*(x**12) + mem0_282_k1*(x**13) + mem0_284_k1*(x**14) + mem0_286_k1*(x**15) + 
mem0_288_k1*(x**16) + mem0_290_k1*(x**17) + mem0_292_k1*(x**18) + mem0_294_k1*(x**19) + 
mem0_296_k1*(x**20) + mem0_298_k1*(x**21) + mem0_300_k1*(x**22) + mem0_302_k1*(x**23) + 
mem0_304_k1*(x**24) + mem0_306_k1*(x**25) + mem0_308_k1*(x**26) + mem0_310_k1*(x**27) + 
mem0_312_k1*(x**28) + mem0_314_k1*(x**29) + mem0_316_k1*(x**30) + mem0_318_k1*(x**31) + 
mem0_320_k1*(x**32) + mem0_322_k1*(x**33) + mem0_324_k1*(x**34) + mem0_326_k1*(x**35) + 
mem0_328_k1*(x**36) + mem0_330_k1*(x**37) + mem0_332_k1*(x**38) + mem0_334_k1*(x**39) + 
mem0_336_k1*(x**40) + mem0_338_k1*(x**41) + mem0_340_k1*(x**42) + mem0_342_k1*(x**43) + 
mem0_344_k1*(x**44) + mem0_346_k1*(x**45) + mem0_348_k1*(x**46) + mem0_350_k1*(x**47) + 
mem0_352_k1*(x**48) + mem0_354_k1*(x**49) + mem0_356_k1*(x**50) + mem0_358_k1*(x**51) + 
mem0_360_k1*(x**52) + mem0_362_k1*(x**53) + mem0_364_k1*(x**54) + mem0_366_k1*(x**55) + 
mem0_368_k1*(x**56) + mem0_370_k1*(x**57) + mem0_372_k1*(x**58) + mem0_374_k1*(x**59) + 
mem0_376_k1*(x**60) + mem0_378_k1*(x**61) + mem0_380_k1*(x**62) + mem0_382_k1*(x**63) + 
mem0_384_k1*(x**64) + mem0_386_k1*(x**65) + mem0_388_k1*(x**66) + mem0_390_k1*(x**67) + 
mem0_392_k1*(x**68) + mem0_394_k1*(x**69) + mem0_396_k1*(x**70) + mem0_398_k1*(x**71) + 
mem0_400_k1*(x**72) + mem0_402_k1*(x**73) + mem0_404_k1*(x**74) + mem0_406_k1*(x**75) + 
mem0_408_k1*(x**76) + mem0_410_k1*(x**77) + mem0_412_k1*(x**78) + mem0_414_k1*(x**79) + 
mem0_416_k1*(x**80) + mem0_418_k1*(x**81) + mem0_420_k1*(x**82) + mem0_422_k1*(x**83) + 
mem0_424_k1*(x**84) + mem0_426_k1*(x**85) + mem0_428_k1*(x**86) + mem0_430_k1*(x**87) + 
mem0_432_k1*(x**88) + mem0_434_k1*(x**89) + mem0_436_k1*(x**90) + mem0_438_k1*(x**91) + 
mem0_440_k1*(x**92) + mem0_442_k1*(x**93) + mem0_444_k1*(x**94) + mem0_446_k1*(x**95) + 
mem0_448_k1*(x**96) + mem0_450_k1*(x**97) + mem0_452_k1*(x**98) + mem0_454_k1*(x**99) + 
mem0_456_k1*(x**100) + mem0_458_k1*(x**101) + mem0_460_k1*(x**102) + mem0_462_k1*(x**103) + 
mem0_464_k1*(x**104) + mem0_466_k1*(x**105) + mem0_468_k1*(x**106) + mem0_470_k1*(x**107) + 
mem0_472_k1*(x**108) + mem0_474_k1*(x**109) + mem0_476_k1*(x**110) + mem0_478_k1*(x**111) + 
mem0_480_k1*(x**112) + mem0_482_k1*(x**113) + mem0_484_k1*(x**114) + mem0_486_k1*(x**115) + 
mem0_488_k1*(x**116) + mem0_490_k1*(x**117) + mem0_492_k1*(x**118) + mem0_494_k1*(x**119) + 
mem0_496_k1*(x**120) + mem0_498_k1*(x**121) + mem0_500_k1*(x**122) + mem0_502_k1*(x**123) + 
mem0_504_k1*(x**124) + mem0_506_k1*(x**125) + mem0_508_k1*(x**126) + mem0_510_k1*(x**127)
)
(
mem0_384*(x**0) + mem0_386*(x**1) + mem0_388*(x**2) + mem0_390*(x**3) + 
mem0_392*(x**4) + mem0_394*(x**5) + mem0_396*(x**6) + mem0_398*(x**7) + 
mem0_400*(x**8) + mem0_402*(x**9) + mem0_404*(x**10) + mem0_406*(x**11) + 
mem0_408*(x**12) + mem0_410*(x**13) + mem0_412*(x**14) + mem0_414*(x**15) + 
mem0_416*(x**16) + mem0_418*(x**17) + mem0_420*(x**18) + mem0_422*(x**19) + 
mem0_424*(x**20) + mem0_426*(x**21) + mem0_428*(x**22) + mem0_430*(x**23) + 
mem0_432*(x**24) + mem0_434*(x**25) + mem0_436*(x**26) + mem0_438*(x**27) + 
mem0_440*(x**28) + mem0_442*(x**29) + mem0_444*(x**30) + mem0_446*(x**31) + 
mem0_448*(x**32) + mem0_450*(x**33) + mem0_452*(x**34) + mem0_454*(x**35) + 
mem0_456*(x**36) + mem0_458*(x**37) + mem0_460*(x**38) + mem0_462*(x**39) + 
mem0_464*(x**40) + mem0_466*(x**41) + mem0_468*(x**42) + mem0_470*(x**43) + 
mem0_472*(x**44) + mem0_474*(x**45) + mem0_476*(x**46) + mem0_478*(x**47) + 
mem0_480*(x**48) + mem0_482*(x**49) + mem0_484*(x**50) + mem0_486*(x**51) + 
mem0_488*(x**52) + mem0_490*(x**53) + mem0_492*(x**54) + mem0_494*(x**55) + 
mem0_496*(x**56) + mem0_498*(x**57) + mem0_500*(x**58) + mem0_502*(x**59) + 
mem0_504*(x**60) + mem0_506*(x**61) + mem0_508*(x**62) + mem0_510*(x**63)
)
[3329, x**64 - 40]
] && and [
   (-4)@16 * 3329@16 <s mem0_0, mem0_0 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_2, mem0_2 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_4, mem0_4 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_6, mem0_6 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_8, mem0_8 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_10, mem0_10 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_12, mem0_12 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_14, mem0_14 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_16, mem0_16 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_18, mem0_18 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_20, mem0_20 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_22, mem0_22 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_24, mem0_24 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_26, mem0_26 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_28, mem0_28 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_30, mem0_30 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_32, mem0_32 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_34, mem0_34 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_36, mem0_36 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_38, mem0_38 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_40, mem0_40 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_42, mem0_42 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_44, mem0_44 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_46, mem0_46 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_48, mem0_48 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_50, mem0_50 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_52, mem0_52 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_54, mem0_54 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_56, mem0_56 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_58, mem0_58 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_60, mem0_60 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_62, mem0_62 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_64, mem0_64 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_66, mem0_66 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_68, mem0_68 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_70, mem0_70 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_72, mem0_72 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_74, mem0_74 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_76, mem0_76 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_78, mem0_78 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_80, mem0_80 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_82, mem0_82 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_84, mem0_84 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_86, mem0_86 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_88, mem0_88 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_90, mem0_90 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_92, mem0_92 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_94, mem0_94 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_96, mem0_96 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_98, mem0_98 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_100, mem0_100 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_102, mem0_102 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_104, mem0_104 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_106, mem0_106 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_108, mem0_108 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_110, mem0_110 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_112, mem0_112 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_114, mem0_114 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_116, mem0_116 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_118, mem0_118 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_120, mem0_120 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_122, mem0_122 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_124, mem0_124 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_126, mem0_126 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_128, mem0_128 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_130, mem0_130 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_132, mem0_132 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_134, mem0_134 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_136, mem0_136 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_138, mem0_138 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_140, mem0_140 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_142, mem0_142 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_144, mem0_144 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_146, mem0_146 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_148, mem0_148 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_150, mem0_150 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_152, mem0_152 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_154, mem0_154 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_156, mem0_156 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_158, mem0_158 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_160, mem0_160 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_162, mem0_162 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_164, mem0_164 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_166, mem0_166 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_168, mem0_168 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_170, mem0_170 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_172, mem0_172 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_174, mem0_174 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_176, mem0_176 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_178, mem0_178 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_180, mem0_180 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_182, mem0_182 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_184, mem0_184 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_186, mem0_186 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_188, mem0_188 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_190, mem0_190 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_192, mem0_192 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_194, mem0_194 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_196, mem0_196 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_198, mem0_198 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_200, mem0_200 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_202, mem0_202 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_204, mem0_204 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_206, mem0_206 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_208, mem0_208 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_210, mem0_210 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_212, mem0_212 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_214, mem0_214 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_216, mem0_216 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_218, mem0_218 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_220, mem0_220 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_222, mem0_222 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_224, mem0_224 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_226, mem0_226 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_228, mem0_228 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_230, mem0_230 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_232, mem0_232 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_234, mem0_234 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_236, mem0_236 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_238, mem0_238 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_240, mem0_240 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_242, mem0_242 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_244, mem0_244 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_246, mem0_246 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_248, mem0_248 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_250, mem0_250 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_252, mem0_252 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_254, mem0_254 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_256, mem0_256 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_258, mem0_258 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_260, mem0_260 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_262, mem0_262 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_264, mem0_264 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_266, mem0_266 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_268, mem0_268 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_270, mem0_270 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_272, mem0_272 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_274, mem0_274 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_276, mem0_276 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_278, mem0_278 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_280, mem0_280 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_282, mem0_282 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_284, mem0_284 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_286, mem0_286 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_288, mem0_288 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_290, mem0_290 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_292, mem0_292 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_294, mem0_294 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_296, mem0_296 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_298, mem0_298 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_300, mem0_300 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_302, mem0_302 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_304, mem0_304 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_306, mem0_306 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_308, mem0_308 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_310, mem0_310 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_312, mem0_312 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_314, mem0_314 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_316, mem0_316 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_318, mem0_318 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_320, mem0_320 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_322, mem0_322 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_324, mem0_324 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_326, mem0_326 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_328, mem0_328 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_330, mem0_330 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_332, mem0_332 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_334, mem0_334 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_336, mem0_336 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_338, mem0_338 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_340, mem0_340 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_342, mem0_342 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_344, mem0_344 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_346, mem0_346 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_348, mem0_348 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_350, mem0_350 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_352, mem0_352 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_354, mem0_354 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_356, mem0_356 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_358, mem0_358 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_360, mem0_360 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_362, mem0_362 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_364, mem0_364 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_366, mem0_366 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_368, mem0_368 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_370, mem0_370 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_372, mem0_372 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_374, mem0_374 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_376, mem0_376 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_378, mem0_378 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_380, mem0_380 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_382, mem0_382 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_384, mem0_384 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_386, mem0_386 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_388, mem0_388 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_390, mem0_390 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_392, mem0_392 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_394, mem0_394 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_396, mem0_396 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_398, mem0_398 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_400, mem0_400 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_402, mem0_402 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_404, mem0_404 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_406, mem0_406 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_408, mem0_408 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_410, mem0_410 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_412, mem0_412 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_414, mem0_414 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_416, mem0_416 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_418, mem0_418 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_420, mem0_420 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_422, mem0_422 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_424, mem0_424 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_426, mem0_426 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_428, mem0_428 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_430, mem0_430 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_432, mem0_432 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_434, mem0_434 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_436, mem0_436 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_438, mem0_438 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_440, mem0_440 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_442, mem0_442 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_444, mem0_444 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_446, mem0_446 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_448, mem0_448 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_450, mem0_450 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_452, mem0_452 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_454, mem0_454 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_456, mem0_456 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_458, mem0_458 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_460, mem0_460 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_462, mem0_462 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_464, mem0_464 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_466, mem0_466 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_468, mem0_468 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_470, mem0_470 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_472, mem0_472 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_474, mem0_474 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_476, mem0_476 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_478, mem0_478 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_480, mem0_480 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_482, mem0_482 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_484, mem0_484 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_486, mem0_486 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_488, mem0_488 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_490, mem0_490 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_492, mem0_492 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_494, mem0_494 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_496, mem0_496 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_498, mem0_498 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_500, mem0_500 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_502, mem0_502 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_504, mem0_504 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_506, mem0_506 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_508, mem0_508 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_510, mem0_510 <s 4@16 * 3329@16
]
}