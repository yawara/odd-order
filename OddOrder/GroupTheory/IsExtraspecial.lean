/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.Subgroup.Center

/-!
# Extraspecial p-Groups

`OddOrder.GroupTheory` shared module: 'extraspecial p-group' の概念.

mathlib v4.29.1 に `IsExtraspecial` 不在を確認済 (0 hits in `Mathlib/`,
`RootSystem/GeckConstruction/Basic.lean` の "extraspecial pair" は別概念).

**BG §2 Thm 2.5** (faithful irreducible FG-module of extraspecial group), **BG §4 Lem 4.15**
(extraspecial commutator constraint), Isaacs FGT Ch.6 §6 で必要.

## Main definitions

* `OddOrder.GroupTheory.IsExtraspecial p G`: `G` is an extraspecial `p`-group.
* `OddOrder.GroupTheory.IsExpPExtraspecial p G`: `G` is an extraspecial `p`-group
  of exponent `p` (`Monoid.exponent G = p`). BG §4 Thm 4.16 case (2) /
  Cor 10.7(b) の中心積の非可換因子 `R₁` (Heisenberg 群 `M(p,1)`) を述語化したもの.

教科書 (Isaacs FGT Defn 6.6, Aschbacher §23) 標準定義:
**`Z(G) = [G, G] = Φ(G)`** かつ **`|Z(G)| = p`**.

## Main results (本 module で提供, 最小)

* 構造体投影 (projections): `isPGroup`, `commutator_eq_center`, `frattini_eq_center`, `center_card`.

## Design notes

* `structure` 形 (Prop). 4 条件を field 化することで dot-notation 利用可
  (`h.isPGroup`, `h.center_card` 等).
* 同値 characterization (G/Z elementary abelian, `∀ g, g^p ∈ Z` 等) は補強で.
* `p` prime 仮定は def 段階では不要 (mathlib 慣用). 主結果記述時に `[Fact p.Prime]`.
* 将来 mathlib upstream 視野で `OddOrder/Mathlib/IsExtraspecial.lean` 候補.

## References

* Isaacs, _Finite Group Theory_ (AMS GSM 92, 2008), Chapter 6 §6, Definition 6.6.
* Aschbacher, _Finite Group Theory_ (CUP, 1986), §23.
* BG §2 Thm 2.5 (Gorenstein 1968 Thm 5.5.4-5.5.5 の odd-order 適用).
* BG §4 Lem 4.15, Thm 4.16 case (2).

## Audit context

Phase 2a 第 1 波 audit 2026-05-23 で新規 shared module 候補として確定.
詳細は `notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`.
-/

namespace OddOrder.GroupTheory

/-- **Extraspecial p-group**: `G` is a `p`-group with
`Z(G) = [G, G] = Φ(G)` and `|Z(G)| = p`.

これは Isaacs FGT Defn 6.6 / Aschbacher §23 の標準定義. `frattini = center`
は p-群 G で `Φ(G) = [G, G] ⊔ {g^p}_{g∈G}` を介して `∀ g, g^p ∈ Z(G)` と同値. -/
structure IsExtraspecial (p : ℕ) (G : Type*) [Group G] : Prop where
  /-- `G` is a `p`-group. -/
  isPGroup : IsPGroup p G
  /-- The commutator subgroup equals the center: `[G, G] = Z(G)`. -/
  commutator_eq_center : commutator G = Subgroup.center G
  /-- The Frattini subgroup equals the center: `Φ(G) = Z(G)`. -/
  frattini_eq_center : frattini G = Subgroup.center G
  /-- The center has order `p`. -/
  center_card : Nat.card (Subgroup.center G) = p

namespace IsExtraspecial

variable {p : ℕ} {G : Type*} [Group G]

/-- The commutator subgroup of an extraspecial group equals its Frattini subgroup. -/
theorem commutator_eq_frattini (h : IsExtraspecial p G) :
    commutator G = frattini G :=
  h.commutator_eq_center.trans h.frattini_eq_center.symm

/-- The commutator subgroup of an extraspecial group has cardinality `p`. -/
theorem commutator_card (h : IsExtraspecial p G) : Nat.card (commutator G) = p := by
  rw [h.commutator_eq_center]; exact h.center_card

/-- The Frattini subgroup of an extraspecial group has cardinality `p`. -/
theorem frattini_card (h : IsExtraspecial p G) : Nat.card (frattini G) = p := by
  rw [h.frattini_eq_center]; exact h.center_card

end IsExtraspecial

/-- **Extraspecial p-group of exponent p**: an extraspecial `p`-group all of whose
elements satisfy `g ^ p = 1` (equivalently `Monoid.exponent G = p`).

これは **BG §4 Thm 4.16** condition (2) / **BG Cor 10.7(b)** で現れる中心積の
非可換因子 `R₁` (= Heisenberg 群 `M(p,1)`, 位数 `p³`) の構造を記述する再利用可能な
述語. Thm 4.16 の Case B-1 では `S = Ω₁(R)` が `r(R) = 2` から非可換 ⇒ extraspecial,
かつ Prop 4.8 から exponent `p` であることが示され, この述語の witness となる.

**重要**: 位数 `p³` はこの述語に **含めない**. Thm 4.16 の証明内部で `|Ω₁(R)| = p³`
として別途確立される (Prop 4.8) ため, ここでは exponent-`p` 部分のみを述語化する.

`p` prime 仮定は def 段階では不要 (`IsExtraspecial` と同様 mathlib 慣用). -/
def IsExpPExtraspecial (p : ℕ) (G : Type*) [Group G] : Prop :=
  IsExtraspecial p G ∧ Monoid.exponent G = p

namespace IsExpPExtraspecial

variable {p : ℕ} {G : Type*} [Group G]

/-- An exponent-`p` extraspecial group is extraspecial. -/
theorem isExtraspecial (h : IsExpPExtraspecial p G) : IsExtraspecial p G := h.1

/-- An exponent-`p` extraspecial group has `Monoid.exponent` equal to `p`. -/
theorem exponent_eq (h : IsExpPExtraspecial p G) : Monoid.exponent G = p := h.2

/-- Every element of an exponent-`p` extraspecial group satisfies `g ^ p = 1`.

This is the form consumed in BG §4 Thm 4.16 Case B-1, where `S = Ω₁(R)` has exponent
`p` and hence every element of `S` is killed by `p`-th power. -/
theorem pow_eq_one (h : IsExpPExtraspecial p G) (g : G) : g ^ p = 1 := by
  rw [← h.exponent_eq]; exact Monoid.pow_exponent_eq_one g

end IsExpPExtraspecial

end OddOrder.GroupTheory
