/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8C.HigmanSims
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8C.AbelianAut
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8C.MathieuEleven
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8C.MathieuTwelve
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8C.PrimeDegree
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8C.SimpleStabilizer
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8C.SimpleOrder120

/-!
# Isaacs, Finite Group Theory — Problems 8C (pp. 256–257)

Isaacs §8C (`PSL(n, q)` の単純性) の章末演習を束ねる hub。実体は `Problems8C/` 配下の
topic 別 leaf にある (下流は本 module を import するだけでよい)。

* `Problems8C/SimpleOrder120.lean` — **8C.1**: `A₆` は位数 120 の部分群をもたず,
  位数 120 の群は単純でない。
* `Problems8C/PrimeDegree.lean` — **8C.2 の準備**: 素数次数 `p` の置換群で位数 `p` の
  部分群の中心化群・正規化群。
* `Problems8C/MathieuEleven.lean` — **8C.2**: 次数 11 位数 7920 の置換群は単純 (`M₁₁`)。
* `Problems8C/MathieuTwelve.lean` — **8C.3**: 次数 12 位数 95040 の推移置換群は単純 (`M₁₂`)。
* `Problems8C/SimpleStabilizer.lean` — **8C.3 / 8C.4 共通**: 点安定化群が単純なら
  推移的な真の正規部分群は regular。
* `Problems8C/HigmanSims.lean` — **8C.4**: 次数 100, 点安定化群が単純で軌道長 22, 77 なら
  原始的かつ単純 (`HS`)。
* `Problems8C/AbelianAut.lean` — **8C.6 の一部**: 位数 3 の群の自己同型群は単純。
-/
