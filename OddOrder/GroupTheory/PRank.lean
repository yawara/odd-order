/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.ElementaryAbelian
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# p-Rank of a Group

`OddOrder.GroupTheory` shared module: BG / Isaacs FGT の `r_p(G)` (`p`-rank) の概念.

mathlib v4.29.1 の `Group.rank G` は **minimum generators 数** (`Mathlib/GroupTheory/Rank.lean`)
で BG の `r_p(G)` (= max log_p of elementary abelian p-subgroup) とは別概念. 命名衝突を
避けるため `pRank G p` (or `IsPGroup.pRank`) を採用.

**BG §4 全節 (Blackburn rank theory)**, **BG §5 (Narrow p-Groups)** で必要.

## Main definitions

* `OddOrder.GroupTheory.pRank G p`: `G` の `p`-rank, i.e. 最大の `n` で `G` が
  位数 `p^n` の elementary abelian p-subgroup を含む.

## Main results (本 module で提供, 最小)

* `pRank` の def のみ. 性質は future work (BddAbove 条件下の `le_pRank`,
  `pRank_eq_zero_of_one`, etc.) に分離.

## Design notes

* `noncomputable def` (iSup based). 一般 `G` で型は通るが, `[Finite G]` 下でのみ
  意味のある値 (無限群では unbounded → mathlib `iSup` convention で 0 等になる可能性).
* mathlib `Group.rank` (min generators) と区別するため必ず `pRank` 命名を使用.
* BG 教科書の `m(A) = log_p |Ω₁(A)|` for abelian は **abelian A** での specialization;
  `pRank` は全 elementary abelian sub 上の max なので, abelian G では `pRank G p = m(G)`.
* 将来 mathlib upstream 視野で `OddOrder/Mathlib/PRank.lean` 候補.

## References

* BG §4 (p-Groups of Small Rank), Lem 4.7 (rank ↔ SCN_3).
* BG §5 (Narrow p-Groups), 全節.
* Gorenstein, _Finite Groups_ (1968), Definition 5.4.10.

## Audit context

Phase 2a 第 1 波 audit 2026-05-23 で新規 shared module 候補として確定.
詳細は `notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`.
-/

namespace OddOrder.GroupTheory

variable (G : Type*) [Group G]

/-- **p-Rank of a group**: the maximum `n` such that `G` contains an elementary abelian
`p`-subgroup of order `p^n`.

For `G = ⊥` or no elementary abelian `p`-subgroup besides `⊥`, this is `0`.

**注**: mathlib v4.29.1 の `Group.rank G` は **minimum generators 数** で別概念.
本 def の命名 `pRank` で衝突回避. -/
noncomputable def pRank (p : ℕ) : ℕ :=
  ⨆ A : {A : Subgroup G // A.IsElementaryAbelian p}, Nat.log p (Nat.card (A.val : Subgroup G))

end OddOrder.GroupTheory
