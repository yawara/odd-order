/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8B.Blocks
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8B.CyclicGenerated
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8B.DihedralStructure
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8B.SmallSuborbits

/-!
# Isaacs, Finite Group Theory — Problems 8B (pp. 248–249)

Isaacs §8B (block と原始性) の章末演習を束ねる hub。実体は `Problems8B/` 配下の
topic 別 leaf にある (下流は本 module を import するだけでよい)。

* `Problems8B/Blocks.lean` — **8B.1–8B.4**: block の作り方, 原始群の分離性,
  極小正規部分群の対, 可解原始群の次数。
* `Problems8B/SmallSuborbits.lean` — **8B.5–8B.7**: 点安定化群が `Ω ∖ {α}` 上に
  長さ 1 / 2 / 3 の軌道をもつ場合の構造。
* `Problems8B/CyclicGenerated.lean` — **8B.8**: `n`-巡回と部分推移群が生成する群の原始性。
* `Problems8B/DihedralStructure.lean` — **8B.6 の結論**: 長さ 2 の軌道をもつ原始置換群は
  `DihedralGroup p` (`p = |Ω|` は奇素数) に同型。二面体群の認識補題 `dihedralEquiv` 込み。
-/
