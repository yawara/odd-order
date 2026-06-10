/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.Subgroup.Center
import OddOrder.GroupTheory.ElementaryAbelian

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

/-- **Special p-group** (Gorenstein, _Finite Groups_, §3, after Theorem 3.7): a `p`-group
`G` is *special* if it is either elementary abelian, or of class `2` with
`G' = Z(G) = Φ(G)` elementary abelian. (The class-`2` case with `|G'| = p` is exactly
extraspecial.) Equivalently `Φ(G) = G' ⊆ Z(G)` with `G/G'` and the common subgroup
elementary abelian.

Used in **BG §4 Lemma 4.13** (= **G** Theorem 4.15(ii), precursor 2, issue 0051): a minimal
`A`-invariant subgroup on which a nontrivial `p'`-automorphism acts is special of exponent
`p` (Gorenstein Theorems 3.7/3.8/3.10). -/
def IsSpecial (p : ℕ) (G : Type*) [Group G] : Prop :=
  IsPGroup p G ∧
    (IsElementaryAbelian p G ∨
      (commutator G = Subgroup.center G ∧ frattini G = Subgroup.center G ∧
        (Subgroup.center G).IsElementaryAbelian p))

namespace IsSpecial

variable {p : ℕ} {G : Type*} [Group G]

/-- A special `p`-group is a `p`-group. -/
theorem isPGroup (h : IsSpecial p G) : IsPGroup p G := h.1

/-- An elementary abelian `p`-group is special. -/
theorem of_isElementaryAbelian (h : IsElementaryAbelian p G) : IsSpecial p G :=
  ⟨h.isPGroup, Or.inl h⟩

/-- **`IsSpecial` transports along group isomorphisms** (each ingredient — `p`-group,
elementary abelian, commutator, centre, Frattini — corresponds under `e`). -/
theorem of_mulEquiv {H : Type*} [Group H] (e : G ≃* H) (h : IsSpecial p G) : IsSpecial p H := by
  obtain ⟨hpg, hcase⟩ := h
  refine ⟨hpg.of_injective e.symm.toMonoidHom e.symm.injective, ?_⟩
  rcases hcase with hEA | ⟨hcomm, hfrat, hZEA⟩
  · exact Or.inl (IsElementaryAbelian.of_mulEquiv e hEA)
  refine Or.inr ?_
  have hcenter : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      calc g * e z = e (e.symm g * z) := by rw [map_mul, e.apply_symm_apply]
        _ = e (z * e.symm g) := by rw [hz (e.symm g)]
        _ = e z * g := by rw [map_mul, e.apply_symm_apply]
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hx (e g)
  have hcommutator : (commutator G).map e.toMonoidHom = commutator H := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hfrattini : (frattini G).map e.toMonoidHom = frattini H := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      exact frattini_le_comap_frattini_of_surjective e.surjective
    · have h2 := frattini_le_comap_frattini_of_surjective
        (φ := e.symm.toMonoidHom) e.symm.surjective
      rwa [Subgroup.map_equiv_eq_comap_symm']
  refine ⟨?_, ?_, ?_⟩
  · rw [← hcommutator, hcomm]
    exact hcenter
  · rw [← hfrattini, hfrat]
    exact hcenter
  · rw [← hcenter]
    exact Subgroup.IsElementaryAbelian.map e.injective hZEA

end IsSpecial

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

/-- **A nonabelian special group with cyclic centre is extraspecial.**
A special `p`-group `G` (`IsSpecial p G`) that is *not* elementary abelian (equivalently,
nonabelian) and whose centre is cyclic is extraspecial: in the nonabelian branch of `IsSpecial`,
`Z(G) = [G, G] = Φ(G)` is elementary abelian, and being additionally cyclic forces `|Z(G)| = p`.

This is the closing structural step of **BG Theorem 3.4** (step 7): Gorenstein's Theorem 5.3.7
leaves `K` either elementary abelian or nonabelian special; the elementary abelian case is excluded
earlier, and `Z(K) ⊆ Z(G)` is cyclic, so `K` is extraspecial and Theorem 2.5 applies. -/
theorem of_isSpecial_of_isCyclic_center [Finite G] [Fact p.Prime]
    (hsp : IsSpecial p G) (hnonab : ¬ IsElementaryAbelian p G)
    (hcyc : IsCyclic (Subgroup.center G)) :
    IsExtraspecial p G := by
  obtain ⟨hpg, hdisj⟩ := hsp
  rcases hdisj with helem | ⟨hcomm, hfrat, hZelem⟩
  · exact absurd helem hnonab
  -- Nonabelian branch: `Z(G) = [G,G] = Φ(G)` elementary abelian.  `G` (hence `Z(G)`) is nontrivial.
  haveI : Nontrivial G := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact hnonab ⟨fun x y => Subsingleton.elim _ _, fun x => Subsingleton.elim _ _⟩
  haveI hZnt : Nontrivial (Subgroup.center G) := hpg.center_nontrivial
  haveI : IsCyclic (Subgroup.center G) := hcyc
  refine ⟨hpg, hcomm, hfrat, ?_⟩
  -- `Z(G)` cyclic + elementary abelian ⟹ `exponent = card` divides `p`; nontrivial ⟹ `card = p`.
  have hZea : IsElementaryAbelian p (Subgroup.center G) := hZelem
  have hdvd : Nat.card (Subgroup.center G) ∣ p := by
    rw [← IsCyclic.exponent_eq_card, Monoid.exponent_dvd_iff_forall_pow_eq_one]
    exact hZea.pow_eq_one
  have hgt : 1 < Nat.card (Subgroup.center G) := Finite.one_lt_card_iff_nontrivial.mpr hZnt
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | hp
  · omega
  · exact hp

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
