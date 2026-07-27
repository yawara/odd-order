/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8D.ArrowKernelIndex
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8D.DegreeEight
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8D.RankBound
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8D.RankThree
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8D.SubdegreeTwo

/-!
# Isaacs, Finite Group Theory — Problems 8D (p. 269)

Isaacs §8D (suborbit と orbital) の章末演習を束ねる hub。実体は `Problems8D/` 配下の
topic 別 leaf にある (下流は本 module を import するだけでよい)。

* `Problems8D/SubdegreeTwo.lean` — **8D.1**: 原始的作用で長さ 2 の suborbit が
  現れるなら, `α` 以外の suborbit はすべて長さ 2。
* `Problems8D/DegreeEight.lean` — **8D.2**: 次数 8 の原始置換群は 2-transitive。
* `Problems8D/RankBound.lean` — **8D.3**: rank `r`・最大 subdegree `n` なら `|G| ≤ (r·n)!`。
* `Problems8D/ArrowKernelIndex.lean` — **8D.4**: `k_m ≥ m` / 等号なら `G_α G_β = K_m(α)` /
  原始的で `m > 1` なら `k_m > m`。
* `Problems8D/RankThree.lean` — **8D.5**: rank 3 で subdegree `1 < m < n` が互いに素なら
  `(m+1) ∣ n`。
-/
