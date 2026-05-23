/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Self-Centralizing Normal Abelian Subgroups (SCN)

`OddOrder.GroupTheory` shared module: 'SCN subgroup' (Self-Centralizing Normal abelian
subgroup) の概念.

mathlib v4.29.1 に `IsSCN` / `SCN` 不在 (0 hits). BG / Isaacs FGT における基本概念で,
**BG §4 Prop 4.4** (existence of `SCN` in p-群), **BG §4 Lem 4.7** (rank ≥ 3 ⇔ `SCN_3` 非空),
**BG §5 Lem 5.1** (SCN₃ argument), **Isaacs Ch.7** (J(P) 関連) で必要.

## Main definitions

* `OddOrder.GroupTheory.IsSCN A`: 部分群 `A : Subgroup G` is SCN.
  - `A.Normal` (`A ⊴ G`),
  - `IsMulCommutative A` (`A` is abelian),
  - `centralizer (A : Set G) = A` (`C_G(A) = A`).

## Main results (本 module で提供, 最小)

* 構造体投影: `isNormal`, `isMulCommutative`, `selfCentralizing`.

## Design notes

* `SCN_n(G)` (= rank ≥ `n` の `SCN`) は **`OddOrder/GroupTheory/PRank.lean` 完成後に追加**.
  Phase 2a 第 1 波 audit 2026-05-23 で別 module として分離決定.
* `structure` 形 (Prop). dot-notation 利用可.
* 将来 mathlib upstream 視野で `OddOrder/Mathlib/SCN.lean` 候補.

## References

* BG §4 (p-Groups of Small Rank), Prop 4.4, Lem 4.7.
* BG §5 (Narrow p-Groups), Lem 5.1.
* Isaacs, _Finite Group Theory_ (AMS GSM 92, 2008), Chapter 7.
* Gorenstein, _Finite Groups_ (1968), §5.3.

## Audit context

Phase 2a 第 1 波 audit 2026-05-23 で新規 shared module 候補として確定.
詳細は `notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`.
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **SCN subgroup** (Self-Centralizing Normal abelian subgroup):
`A ≤ G` is SCN iff `A` is normal in `G`, abelian, and equals its own centralizer
`C_G(A) = A`.

教科書 (Isaacs FGT Ch.7, BG §4) 標準定義. `A = C_G(A)` 条件は **A self-centralizing**
を意味し, abelian + normal と組み合わせて p-群構造解析の鍵となる. -/
structure IsSCN (A : Subgroup G) : Prop where
  /-- `A` is normal in `G`. -/
  isNormal : A.Normal
  /-- `A` is abelian. -/
  isMulCommutative : IsMulCommutative A
  /-- `A` is self-centralizing: `C_G(A) = A`. -/
  selfCentralizing : Subgroup.centralizer (A : Set G) = A

namespace IsSCN

variable {A : Subgroup G}

/-- An SCN subgroup is contained in its own centralizer (abelian ⇒ `A ⊆ C_G(A)`).
This is a one-direction restatement; the other direction `C_G(A) ⊆ A` is `selfCentralizing`. -/
theorem le_centralizer (h : IsSCN A) : A ≤ Subgroup.centralizer (A : Set G) := by
  rw [h.selfCentralizing]

/-- An SCN subgroup is contained in the center of its centralizer (trivially since
`C_G(A) = A` and `A` is abelian, hence in the center of itself). -/
theorem centralizer_le (h : IsSCN A) : Subgroup.centralizer (A : Set G) ≤ A :=
  h.selfCentralizing.le

end IsSCN

end OddOrder.GroupTheory
