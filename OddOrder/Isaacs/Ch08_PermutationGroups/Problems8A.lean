/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8A.AffineLine
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8A.CosetOrbits
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8A.MultiplyTransitive
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8A.PermutationCharacter
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8A.PointStabilizers
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8A.RegularRepresentations
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8A.SharplyThreeTransitive

/-!
# Isaacs, Finite Group Theory — Problems 8A (pp. 235–236)

Isaacs §8A の章末演習を束ねる hub。実体は `Problems8A/` 配下の topic 別 leaf にある
(下流は本 module を import するだけでよい)。

* `Problems8A/RegularRepresentations.lean` — **8A.1–8A.4**: 左右の正則表現、
  regular normal 部分群の対、中心化群の半正則性。
* `Problems8A/PointStabilizers.lean` — **8A.5–8A.9**: 点安定化群の固定点集合と
  その正規化群、Sylow 版、可換 half-transitive 作用、正規部分群の軌道。
* `Problems8A/MultiplyTransitive.lean` — **8A.10**: 可解 4-transitive 群は `S₄`。
* `Problems8A/PermutationCharacter.lean` — **8A.12 / 8A.13**: 置換指標の
  2 乗・3 乗の平均と `Ω²` / `Ω³` の軌道数。
* `Problems8A/CosetOrbits.lean` — **8A.14 / 8A.15 / 8A.16**: 剰余類空間と相対指数から
  数える軌道数、二重剰余類と剰余類への 2-transitivity、指数が `n-1` と互いに素な
  推移的部分群の 2-transitivity。
* `Problems8A/SharplyThreeTransitive.lean` — **8A.17**: `q` が 2 の冪なら `SL(2, q)` は
  射影直線 (`q + 1` 点) に sharply 3-transitive。
* `Problems8A/AffineLine.lean` — **8A.11**: 1 次元アフィン群 `AGL(1, F)`。
-/
