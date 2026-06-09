/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S05_TICyclic
import OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier

/-!
# Peterfalvi §5: The isometry `σ` (Theorem (3.2)) and its construction (3.5)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§5, pp. 17-20.

This file continues `S05_TICyclic` (which fixes Hypothesis (3.1) and builds the
`ω`/`α` families and the `CF(W, V)` basis (3.3)-(3.4)).  Here we build the
linear isometry `σ : CF(W) → CF(G)` of **Theorem (3.2)**, whose existence is the
content of **(3.5)**: there is an orthonormal family `(χ_{ij})` of virtual
characters of `G` with `χ_{00} = 1_G` and `Ind_W^G α_{ij} = 1_G - χ_{i0} - χ_{0j}
+ χ_{ij}` for `i, j ≥ 1`.

The current slice is **(3.5.1)**, the inner-product foundations: the Gram matrix
of the family `(Ind_W^G α_{ij})`.  Writing `α_{ij} = 1_W - ω_{i0} - ω_{0j} +
ω_{ij}` (`alphaCF_eq_omega_combination`) and using that `Ind_W^G` is an isometry
on `CF(W, V)` (the §4 Dade isometry, carried by `FullDadeApplication`), the inner
products of the induced family are read off from the orthonormality of the
`ω_{ij}`.

Reference note: `notes/peterfalvi/s06_dade_certain_subgroup.md` (session 11+).
-/

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

namespace TICyclicHypothesis

/- 3.5.1: the Gram matrix of `(Ind_W^G α_{ij})` (pp. 17-18) -/

open Classical in
/-- Orthonormality of the `ω`-family, in the `omegaProdChar`-indexed form used to compute the
Gram matrix of the `α_{ij}`: `⟨ω_{b}, ω_{a}⟩ = δ_{b,a}`, with the Kronecker delta decided by
equality of the two index pairs (`omegaProdChar` is injective). -/
theorem omega_omegaProdChar_inner (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)]
    (b₁ a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (b₂ a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    ClassFunction.inner (hyp.omega (hyp.omegaProdChar b₁ b₂) : ClassFunction hyp.W ℂ)
        (hyp.omega (hyp.omegaProdChar a₁ a₂) : ClassFunction hyp.W ℂ) =
      if b₁ = a₁ ∧ b₂ = a₂ then 1 else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact hyp.omega_inner_self _
  · exact hyp.omega_inner_ne (hyp.omegaProdChar_ne h)

/-- **Peterfalvi (3.4)/(3.5)**: `α_{ij} = ω_{00} - ω_{i0} - ω_{0j} + ω_{ij}`, with every term
written as `ω` of an `omegaProdChar` index pair.  This is the form of
`alphaCF_eq_omega_combination` that makes the Gram-matrix computation uniform
(`omega_omegaProdChar_inner`). -/
theorem alphaCF_eq_omegaProdChar_combination (hyp : TICyclicHypothesis G)
    (p₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (p₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    (hyp.alphaCF p₁ p₂ : ClassFunction hyp.W ℂ) =
      (hyp.omega (hyp.omegaProdChar 1 1) : ClassFunction hyp.W ℂ)
        - hyp.omega (hyp.omegaProdChar p₁ 1) - hyp.omega (hyp.omegaProdChar 1 p₂)
        + hyp.omega (hyp.omegaProdChar p₁ p₂) := by
  rw [hyp.omegaProdChar_one_one, hyp.omegaProdChar_one_right, hyp.omegaProdChar_one_left]
  exact hyp.alphaCF_eq_omega_combination p₁ p₂

open Classical in
/-- **Peterfalvi (3.5.1)**: the Gram matrix of the family `(α_{ij})` (`i, j ≥ 1`).  For nontrivial
index characters,
`⟨α_{ij}, α_{kl}⟩ = 1 + δ_{ik} + δ_{jl} + δ_{(ij),(kl)}`,
i.e. `4` on the diagonal, `2` when exactly one index agrees, and `1` when both differ.  This is the
inner-product input that, after applying the `Ind_W^G` isometry and subtracting `1_G`, gives the
norm-`3` virtual characters `β_{ij}` of (3.5.1). -/
theorem alphaCF_inner (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)]
    {p₁ q₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {p₂ q₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (hp₁ : p₁ ≠ 1) (hp₂ : p₂ ≠ 1) (hq₁ : q₁ ≠ 1) (hq₂ : q₂ ≠ 1) :
    ClassFunction.inner (hyp.alphaCF p₁ p₂) (hyp.alphaCF q₁ q₂) =
      1 + (if p₁ = q₁ then 1 else 0) + (if p₂ = q₂ then 1 else 0)
        + (if p₁ = q₁ ∧ p₂ = q₂ then 1 else 0) := by
  rw [hyp.alphaCF_eq_omegaProdChar_combination p₁ p₂,
      hyp.alphaCF_eq_omegaProdChar_combination q₁ q₂]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_add_left,
    ClassFunction.inner_sub_right, ClassFunction.inner_add_right,
    hyp.omega_omegaProdChar_inner]
  -- Kill the cross-type matches (any condition forcing a nontrivial character to be `1`).
  simp only [hp₁, hp₂, hq₁.symm, hq₂.symm,
    false_and, and_false, if_false, if_true, true_and, and_true]
  ring

end TICyclicHypothesis

namespace TICyclicHypothesis

open Classical in
/-- **Peterfalvi (3.5.1)**, induced form: the Gram matrix of `(Ind_W^G α_{ij})` (`i, j ≥ 1`).
Since `Ind_W^G` is an isometry on `CF(W, V)` (the §4 Dade isometry, `full_inner_eq`), the inner
products of the induced family equal those of the `α_{ij}` (`alphaCF_inner`):
`⟨Ind α_{ij}, Ind α_{kl}⟩ = 1 + δ_{ik} + δ_{jl} + δ_{(ij),(kl)}`. -/
theorem tau_alpha_inner (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {p₁ q₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {p₂ q₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (hp₁ : p₁ ≠ 1) (hp₂ : p₂ ≠ 1) (hq₁ : q₁ ≠ 1) (hq₂ : q₂ ≠ 1) :
    ClassFunction.inner (app.tau.toDadeMap (hyp.alpha hVeq p₁ p₂))
        (app.tau.toDadeMap (hyp.alpha hVeq q₁ q₂)) =
      1 + (if p₁ = q₁ then 1 else 0) + (if p₂ = q₂ then 1 else 0)
        + (if p₁ = q₁ ∧ p₂ = q₂ then 1 else 0) := by
  rw [hyp.full_inner_eq app, hyp.alpha_coe, hyp.alpha_coe, hyp.alphaCF_inner hp₁ hp₂ hq₁ hq₂]

end TICyclicHypothesis

/- 3.2(a): the Dade map is induction `Ind_W^G` on `CF(W, V)` (pp. 17) -/

section DadeMapIsInduction

variable {k : Type*} [CommRing k]

namespace TICyclicHypothesis

open Classical in
/-- The `x`-summand of `Ind_W^G α` at `a ∈ V`: it is `α(a)` when `x ∈ W` (then `x⁻¹ a x ∈ V`
since `W` normalizes `V`, and `α` is `W`-class-invariant) and `0` otherwise (then `x⁻¹ a x ∉ V`
by the TI property, so the `V`-supported `α` vanishes there).  This is the per-term computation
behind `induce_apply_eq_self_of_mem_V`. -/
theorem induceTerm_eq_of_mem_V (hyp : TICyclicHypothesis G)
    (α : SupportedOnV (G := G) k hyp) {a : G} (ha : a ∈ hyp.V) (x : G) :
    ClassFunction.induceTerm hyp.W (α : ClassFunction hyp.W k) x a =
      if x ∈ hyp.W then (α : ClassFunction hyp.W k) ⟨a, hyp.V_subset_W ha⟩ else 0 := by
  by_cases hx : x ∈ hyp.W
  · rw [if_pos hx]
    have haxV : x⁻¹ * a * x ∈ hyp.V := by
      have h := hyp.W_normalizes_V ⟨x⁻¹, hyp.W.inv_mem hx⟩ ha
      simpa using h
    have haxW : x⁻¹ * a * x ∈ hyp.W := hyp.V_subset_W haxV
    rw [ClassFunction.induceTerm_of_mem _ haxW]
    have harg : (⟨x⁻¹ * a * x, haxW⟩ : hyp.W) =
        ⟨x⁻¹, hyp.W.inv_mem hx⟩ * ⟨a, hyp.V_subset_W ha⟩ * ⟨x⁻¹, hyp.W.inv_mem hx⟩⁻¹ := by
      apply Subtype.ext
      simp [inv_inv]
    rw [harg]
    exact (α : ClassFunction hyp.W k).conj_eq ⟨a, hyp.V_subset_W ha⟩ ⟨x⁻¹, hyp.W.inv_mem hx⟩
  · rw [if_neg hx]
    by_cases hax : x⁻¹ * a * x ∈ hyp.W
    · rw [ClassFunction.induceTerm_of_mem _ hax]
      have hnotV : x⁻¹ * a * x ∉ hyp.V := by
        intro hV
        exact hx (by simpa using hyp.W.inv_mem (hyp.V_ti x⁻¹ ⟨a, ha, by simpa using hV⟩))
      by_contra hne
      exact hnotV ((OddOrder.Peterfalvi.S04.mem_supportInSubgroup).mp
        (α.2 (ClassFunction.mem_support.mpr hne)))
    · rw [ClassFunction.induceTerm_of_not_mem _ hax]

/-- **Peterfalvi (3.2.c)** at `a ∈ V` (value half): the induced class function `Ind_W^G α`
equals `α` on `V`.  Only the `|W|` conjugators `x ∈ W` contribute to the induction sum, each with
value `α(a)`, so `Ind_W^G α(a) = ⅟|W| · |W| · α(a) = α(a)`. -/
theorem induce_apply_eq_self_of_mem_V (hyp : TICyclicHypothesis G)
    [Invertible (Nat.card hyp.W : k)]
    (α : SupportedOnV (G := G) k hyp) {a : G} (ha : a ∈ hyp.V) :
    ClassFunction.induce hyp.W (α : ClassFunction hyp.W k) a =
      (α : ClassFunction hyp.W k) ⟨a, hyp.V_subset_W ha⟩ := by
  classical
  haveI : Fintype ↥hyp.W := Fintype.ofFinite _
  rw [ClassFunction.induce_apply,
    Finset.sum_congr rfl (fun x _ => hyp.induceTerm_eq_of_mem_V α ha x),
    ← Finset.sum_filter, Finset.sum_const]
  have hcard : (Finset.univ.filter (· ∈ hyp.W)).card = Nat.card hyp.W := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype _).symm
  rw [hcard, nsmul_eq_mul, ← mul_assoc, invOf_mul_self, one_mul]

/-- The induced-class-function `DadeMap` candidate for the TI-cyclic hypothesis: `α ↦ Ind_W^G α`. -/
noncomputable def inducedDadeMap (hyp : TICyclicHypothesis G) [Invertible (Nat.card hyp.W : k)] :
    OddOrder.Peterfalvi.S04.DadeMap (G := G) k hyp.V hyp.W :=
  fun α => ClassFunction.induce hyp.W (α : ClassFunction hyp.W k)

/-- **Peterfalvi (3.2.a)/(2.5)**: `Ind_W^G` (restricted to `CF(W, V)`) satisfies the §4 Dade-map
equations for the TI-cyclic hypothesis.  Value half = `induce_apply_eq_self_of_mem_V` (`H(a) = ⊥`,
so the coset condition reduces to `IsConj a g`); support half = induced functions vanish off the
conjugates `V^G` of the support. -/
theorem isDadeMap_inducedDadeMap (hyp : TICyclicHypothesis G)
    [Invertible (Nat.card hyp.W : k)] :
    OddOrder.Peterfalvi.S04.IsDadeMap hyp.toDadeHypothesis (hyp.inducedDadeMap (k := k)) where
  map_eq_of_isConj_hCoset := by
    intro α g a h hh hconj
    have hh1 : h = 1 := by
      have : h ∈ (⊥ : Subgroup G) := by rw [← hyp.toDadeHypothesis_H a]; exact hh
      exact Subgroup.mem_bot.mp this
    subst hh1
    have hga : IsConj a.1 g := by simpa using hconj
    change ClassFunction.induce hyp.W (α : ClassFunction hyp.W k) g = _
    rw [← (ClassFunction.induce hyp.W (α : ClassFunction hyp.W k)).of_isConj hga,
      hyp.induce_apply_eq_self_of_mem_V α a.2]
  map_eq_zero_of_not_mem_dadeSupport := by
    intro α g hg
    change ClassFunction.induce hyp.W (α : ClassFunction hyp.W k) g = 0
    refine ClassFunction.induce_eq_zero_of_not_conjugatesIntoSet α.2 (fun hgin => hg ?_)
    rw [hyp.toDadeHypothesis.dadeSupport_eq_conjugatesOfSet_of_forall_H_eq_bot
      (fun a => hyp.toDadeHypothesis_H a)]
    obtain ⟨x, hx, hxV⟩ := hgin
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hxV
    exact Group.mem_conjugatesOfSet_iff.mpr ⟨x⁻¹ * g * x, hxV, isConj_iff.mpr ⟨x, by group⟩⟩

end TICyclicHypothesis

end DadeMapIsInduction

namespace TICyclicHypothesis

/-- **Peterfalvi (3.2.a)**: on `CF(W, V)`, the §4 Dade map *is* induction `Ind_W^G`.  By the
uniqueness of the Dade map (`IsDadeMap.unique`), any §4 Dade-isometry carrier `τ` for the
TI-cyclic hypothesis agrees with the concrete `inducedDadeMap`.  This is the bridge that makes
Frobenius reciprocity (`inner_induce_eq_inner_restrict`) available for the abstract `τ` (both
`DadeApplication` and `FullDadeApplication` expose such a `DadeIsometryData`). -/
theorem tau_eq_induce {k : Type*} [CommRing k] [StarRing k] [Invertible (Nat.card G : k)]
    (hyp : TICyclicHypothesis G) [Fintype hyp.W] [Invertible (Nat.card hyp.W : k)]
    (τ : OddOrder.Peterfalvi.S04.DadeIsometryData (G := G) (k := k) hyp.toDadeHypothesis)
    (α : SupportedOnV (G := G) k hyp) :
    τ.toDadeMap α = ClassFunction.induce hyp.W (α : ClassFunction hyp.W k) :=
  congrFun (OddOrder.Peterfalvi.S04.IsDadeMap.unique τ.isDadeMap
    hyp.isDadeMap_inducedDadeMap) α

/- 3.5.1 (cont.): Frobenius reciprocity `⟨Ind_W^G α_{ij}, 1_G⟩ = 1` -/

/-- `Res^G_W 1_G = ω_{00}`: the trivial character of `G` restricts to the trivial linear character
`ω(omegaProdChar 1 1) = ω_{00}` of `W` (both are constant `1`). -/
theorem restrict_trivialClassFunction_eq (hyp : TICyclicHypothesis G) :
    ClassFunction.restrict hyp.W (trivialClassFunction G) =
      (hyp.omega (hyp.omegaProdChar 1 1) : ClassFunction hyp.W ℂ) := by
  ext w
  rw [ClassFunction.restrict_apply, trivialClassFunction_apply, omega_apply,
    hyp.omegaProdChar_one_one, MonoidHom.one_apply, Units.val_one]

open Classical in
/-- `⟨α_{ij}, ω_{00}⟩ = 1` for `i, j ≥ 1`: the trivial-character coefficient of
`α_{ij} = ω_{00} - ω_{i0} - ω_{0j} + ω_{ij}` is `1` (the other three terms are orthogonal to
`ω_{00}` since `i, j ≥ 1`). -/
theorem alphaCF_inner_omega_one (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)]
    {p₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {p₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (hp₁ : p₁ ≠ 1) (hp₂ : p₂ ≠ 1) :
    ClassFunction.inner (hyp.alphaCF p₁ p₂)
        (hyp.omega (hyp.omegaProdChar 1 1) : ClassFunction hyp.W ℂ) = 1 := by
  rw [hyp.alphaCF_eq_omegaProdChar_combination p₁ p₂]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_add_left,
    hyp.omega_omegaProdChar_inner]
  simp only [hp₁, hp₂, and_false, if_false, if_true, and_true]
  ring

/-- **Peterfalvi (3.5.1)** (Frobenius reciprocity): `⟨Ind_W^G α_{ij}, 1_G⟩ = ⟨α_{ij}, 1_W⟩ = 1`
for `i, j ≥ 1`.  Via the bridge `tau_eq_induce` (`τ = Ind_W^G`), Frobenius reciprocity
(`inner_induce_eq_inner_restrict`) turns this into `⟨α_{ij}, Res^G_W 1_G⟩ = ⟨α_{ij}, ω_{00}⟩ = 1`.
Together with the Gram matrix `tau_alpha_inner`, this is the second input that makes
`β_{ij} = Ind_W^G α_{ij} - 1_G` a norm-`3` virtual character orthogonal to `1_G`. -/
theorem tau_alpha_inner_trivial (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {p₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {p₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (hp₁ : p₁ ≠ 1) (hp₂ : p₂ ≠ 1) :
    ClassFunction.inner (app.tau.toDadeMap (hyp.alpha hVeq p₁ p₂))
        (trivialClassFunction G) = 1 := by
  change ClassFunction.inner (app.tau.toDadeIsometryData.toDadeMap (hyp.alpha hVeq p₁ p₂))
    (trivialClassFunction G) = 1
  rw [hyp.tau_eq_induce app.tau.toDadeIsometryData (hyp.alpha hVeq p₁ p₂),
    ClassFunction.inner_induce_eq_inner_restrict, hyp.alpha_coe,
    hyp.restrict_trivialClassFunction_eq, hyp.alphaCF_inner_omega_one hp₁ hp₂]

/-- `α_{ij} ∈ ℤ[Irr W]`: it is the ℤ-combination `ω_{00} - ω_{i0} - ω_{0j} + ω_{ij}` of irreducible
(linear) characters of `W`. -/
theorem alpha_mem_ZIrr (hyp : TICyclicHypothesis G) (hVeq : hyp.V = hyp.Vdiff)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    (hyp.alpha hVeq χ₁ χ₂ : ClassFunction hyp.W ℂ) ∈ ZIrr hyp.W := by
  rw [hyp.alpha_coe, hyp.alphaCF_eq_omega_combination]
  exact Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _
    (hyp.omega 1).mem_ZIrr (hyp.omega (χ₁.comp hyp.wFst)).mem_ZIrr)
    (hyp.omega (χ₂.comp hyp.wSnd)).mem_ZIrr)
    (hyp.omega (χ₁.comp hyp.wFst * χ₂.comp hyp.wSnd)).mem_ZIrr

end TICyclicHypothesis

/-- `⟨1_G, 1_G⟩ = 1`: the trivial character has norm `1`. -/
theorem inner_trivialClassFunction_self (G : Type*) [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] :
    ClassFunction.inner (trivialClassFunction G) (trivialClassFunction G) = 1 := by
  rw [← IrreducibleCharacter.coe_trivialIrreducibleCharacter, irreducibleCharacter_inner,
    if_pos rfl]

/-! ### Norm-`3` virtual characters orthogonal to `1_G` (abstract, candidate for `ZIrrFourier`)

The combinatorial heart of Peterfalvi (3.5.1): a virtual character of squared norm `3` orthogonal
to the trivial character is a sum of three pairwise-orthogonal *signed nontrivial irreducibles*.
These three results are `G`-level and TI-cyclic-independent — companions to the norm-`2` lemma
`OddOrder.RepresentationTheory.exists_irr_sub_irr_of_inner_self_two`.  They are kept here, rather
than in the shared `ZIrrFourier` module, to leave the active frontier in this leaf. -/

/-- Finite integer-vector combinatorics: if integer coefficients on a finite set `s` are all
nonzero and their squares sum to `3`, then `s` has exactly three elements, each with coefficient
`±1`.  (`3` is a sum of nonzero integer squares only as `1 + 1 + 1`: a square `≥ 2` is `≥ 4`.)
Companion to `OddOrder.RepresentationTheory.exists_pair_of_sum_sq_eq_two`. -/
theorem card_eq_three_of_sum_sq_eq_three {ι : Type*} {s : Finset ι} {c : ι → ℤ}
    (hne : ∀ a ∈ s, c a ≠ 0) (hsum : ∑ a ∈ s, c a ^ 2 = 3) :
    s.card = 3 ∧ ∀ a ∈ s, c a = 1 ∨ c a = -1 := by
  have hle : ∀ a ∈ s, c a ^ 2 ≤ 3 := fun a ha =>
    le_of_le_of_eq (Finset.single_le_sum (fun b _ => sq_nonneg (c b)) ha) hsum
  have hsign : ∀ a ∈ s, c a = 1 ∨ c a = -1 := fun a ha => by
    have hane := hne a ha
    have hb := hle a ha
    -- `c a ^ 2 ≤ 3` forces `|c a| ≤ 1` (a square `≥ 2 ` is `≥ 4`), and `c a ≠ 0`.
    have habs1 : |c a| ≤ 1 := by
      by_contra h
      have h2 : (2 : ℤ) ≤ |c a| := by omega
      have h4 : (4 : ℤ) ≤ c a ^ 2 :=
        calc (4 : ℤ) = 2 ^ 2 := by norm_num
          _ ≤ |c a| ^ 2 := by gcongr
          _ = c a ^ 2 := sq_abs (c a)
      omega
    rcases abs_le.mp habs1 with ⟨h1, h2⟩
    omega
  have hone : ∀ a ∈ s, c a ^ 2 = 1 := fun a ha => by
    rcases hsign a ha with h | h <;> rw [h] <;> norm_num
  refine ⟨?_, hsign⟩
  have hcard : (s.card : ℤ) = 3 :=
    calc (s.card : ℤ) = ∑ _a ∈ s, (1 : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ a ∈ s, c a ^ 2 := (Finset.sum_congr rfl hone).symm
      _ = 3 := hsum
  exact_mod_cast hcard

/-- The set `±(Irr(G) - {1_G})` of *signed nontrivial irreducible characters*, as class functions:
`x` is `±χ` for some nontrivial irreducible character `χ`.  This is the type of the elements of
Peterfalvi's set `A_{ij}` in (3.5.1). -/
def IsSignedNontrivialIrr (x : ClassFunction G ℂ) : Prop :=
  ∃ χ : IrreducibleCharacter G, χ ≠ trivialIrreducibleCharacter G ∧
    (x = (χ : ClassFunction G ℂ) ∨ x = -(χ : ClassFunction G ℂ))

/-- **Peterfalvi (3.5.1)** (abstract form): a virtual character `φ ∈ ℤ[Irr G]` of squared norm `3`
orthogonal to `1_G` is `φ = ∑_{x ∈ A} x` for a `3`-element set `A` of pairwise-orthogonal signed
nontrivial irreducibles.  Indeed `φ = ∑ c_a · a` over irreducibles with `∑ c_a² = 3`, so the
support has three elements with `c_a = ±1` (`card_eq_three_of_sum_sq_eq_three`); orthogonality to
`1_G` excludes the trivial character from the support, and the signed irreducibles `c_a · a` form
the set `A`.  Companion to the norm-`2` lemma `exists_irr_sub_irr_of_inner_self_two`. -/
theorem exists_signedTriple_of_inner_self_three [Invertible (Nat.card G : ℂ)]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) (hnorm : ClassFunction.inner φ φ = 3)
    (htriv : ClassFunction.inner φ (trivialClassFunction G) = 0) :
    ∃ A : Finset (ClassFunction G ℂ),
      A.card = 3 ∧ (∀ x ∈ A, IsSignedNontrivialIrr x) ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → ClassFunction.inner x y = 0) ∧
      φ = ∑ x ∈ A, x := by
  classical
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hφ
  have hsumC : ∑ a ∈ c.support, (c a : ℂ) ^ 2 = 3 := hsq.symm.trans hnorm
  have hsumZ : ∑ a ∈ c.support, c a ^ 2 = 3 := by exact_mod_cast hsumC
  have hne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  obtain ⟨hcard3, hsign⟩ := card_eq_three_of_sum_sq_eq_three hne hsumZ
  -- the trivial character is not in the support (else `⟨φ, 1_G⟩ = c_{1_G} ≠ 0`)
  have htrivnot : trivialClassFunction G ∉ c.support := by
    intro hmem
    have hcoeff : ClassFunction.inner φ (trivialClassFunction G) =
        (c (trivialClassFunction G) : ℂ) := by
      rw [hrepr]; exact inner_eq_coeff_of_repr (trivialIrreducibleCharacter G) hsupp
    rw [htriv] at hcoeff
    exact (Finsupp.mem_support_iff.mp hmem) (by exact_mod_cast hcoeff.symm)
  -- the signed-irreducible map `a ↦ (c a) • a` is injective on the support
  have hinj : Set.InjOn (fun a => (c a : ℂ) • a) (c.support : Set (ClassFunction G ℂ)) := by
    intro a ha b hb hfab
    by_contra hab
    have haa : a ∈ irreducibleCharacters G := hsupp ha
    have hba : b ∈ irreducibleCharacters G := hsupp hb
    have e1 : ClassFunction.inner ((c a : ℂ) • a) a = (c a : ℂ) := by
      rw [ClassFunction.inner_smul_left, irr_cf_inner haa haa, if_pos rfl, mul_one]
    have e2 : ClassFunction.inner ((c b : ℂ) • b) a = 0 := by
      rw [ClassFunction.inner_smul_left, irr_cf_inner hba haa, if_neg (Ne.symm hab), mul_zero]
    change (c a : ℂ) • a = (c b : ℂ) • b at hfab
    have hca0 : (c a : ℂ) = 0 := by rw [← e1, hfab, e2]
    exact hne a (Finset.mem_coe.mp ha) (by exact_mod_cast hca0)
  refine ⟨c.support.image (fun a => (c a : ℂ) • a), ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinj]; exact hcard3
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have haa : a ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr ha)
    have hane : a ≠ trivialClassFunction G := fun h => htrivnot (h ▸ ha)
    refine ⟨⟨a, haa⟩, fun h => hane (Subtype.ext_iff.mp h), ?_⟩
    rcases hsign a ha with h | h
    · refine Or.inl ?_
      change (c a : ℂ) • a = a
      rw [h, Int.cast_one, one_smul]
    · refine Or.inr ?_
      change (c a : ℂ) • a = -a
      rw [h, Int.cast_neg, Int.cast_one, neg_one_smul]
  · intro x hx y hy hxy
    rw [Finset.mem_image] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have haa : a ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr ha)
    have hbb : b ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr hb)
    have hab : a ≠ b := fun h => hxy (by rw [h])
    change ClassFunction.inner ((c a : ℂ) • a) ((c b : ℂ) • b) = 0
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      irr_cf_inner haa hbb, if_neg hab, mul_zero, mul_zero]
  · rw [Finset.sum_image hinj]; exact hrepr

/- 3.5.2: the combinatorics of the sets `A_{ij}` -- the signed-irreducible API -/

omit [Fintype G] in
/-- A signed nontrivial irreducible character is nonzero at `1`: its value there is `±d` with
`d > 0` the degree. -/
theorem IsSignedNontrivialIrr.apply_one_ne_zero {x : ClassFunction G ℂ}
    (hx : IsSignedNontrivialIrr x) : x 1 ≠ 0 := by
  obtain ⟨χ, _, hx⟩ := hx
  obtain ⟨d, hd, hd1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  rcases hx with rfl | rfl
  · rw [hd1]; exact_mod_cast hd.ne'
  · rw [ClassFunction.neg_apply, hd1, neg_ne_zero]; exact_mod_cast hd.ne'

omit [Fintype G] in
/-- A signed nontrivial irreducible character is nonzero (it is nonzero at `1`). -/
theorem IsSignedNontrivialIrr.ne_zero {x : ClassFunction G ℂ}
    (hx : IsSignedNontrivialIrr x) : x ≠ 0 := fun h => hx.apply_one_ne_zero (by rw [h]; rfl)

omit [Fintype G] in
/-- The coercion of an irreducible character is never the negative of the coercion of an
irreducible character: at `1` one value is `+d` and the other `-d'` with `d, d' > 0`. -/
theorem irreducibleCharacter_coe_ne_neg (χ ψ : IrreducibleCharacter G) :
    (χ : ClassFunction G ℂ) ≠ -(ψ : ClassFunction G ℂ) := by
  obtain ⟨dχ, hdχ, hχ1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  obtain ⟨dψ, hdψ, hψ1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ψ
  intro h
  have h1 : (χ : ClassFunction G ℂ) (1 : G) = (-(ψ : ClassFunction G ℂ)) (1 : G) := by rw [h]
  rw [hχ1, ClassFunction.neg_apply, hψ1] at h1
  have hsum : ((dχ + dψ : ℕ) : ℂ) = 0 := by push_cast; rw [h1]; ring
  have : dχ + dψ = 0 := by exact_mod_cast hsum
  omega

open Classical in
/-- **Inner product of two signed nontrivial irreducibles** (the orthonormality of `±Irr`):
`⟨x, c⟩` is `1` if `x = c`, `-1` if `x = -c`, and `0` otherwise. -/
theorem isSignedNontrivialIrr_inner [Invertible (Nat.card G : ℂ)] {x c : ClassFunction G ℂ}
    (hx : IsSignedNontrivialIrr x) (hc : IsSignedNontrivialIrr c) :
    ClassFunction.inner x c = (if x = c then 1 else 0) - (if x = -c then 1 else 0) := by
  obtain ⟨χ, -, hxχ⟩ := hx
  obtain ⟨ψ, -, hcψ⟩ := hc
  set X : ClassFunction G ℂ := (χ : ClassFunction G ℂ) with hX
  set Y : ClassFunction G ℂ := (ψ : ClassFunction G ℂ) with hY
  have hXY : ClassFunction.inner X Y = if X = Y then (1 : ℂ) else 0 :=
    irr_cf_inner χ.mem_irreducibleCharacters ψ.mem_irreducibleCharacters
  have hXnegY : ¬ (X = -Y) := irreducibleCharacter_coe_ne_neg χ ψ
  rcases hxχ with rfl | rfl <;> rcases hcψ with rfl | rfl
  · rw [hXY, if_neg hXnegY, sub_zero]
  · rw [ClassFunction.inner_neg_right, hXY, neg_neg, if_neg hXnegY, zero_sub]
  · rw [ClassFunction.inner_neg_left, hXY, neg_inj,
      if_neg (fun h => hXnegY (neg_eq_iff_eq_neg.mp h)), zero_sub]
  · rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg, hXY, neg_inj,
      neg_neg, if_neg (fun h => hXnegY (neg_eq_iff_eq_neg.mp h)), sub_zero]

omit [Fintype G] in
/-- A signed nontrivial irreducible is not its own negative (it is nonzero). -/
theorem IsSignedNontrivialIrr.ne_neg_self {x : ClassFunction G ℂ}
    (hx : IsSignedNontrivialIrr x) : x ≠ -x := by
  intro h
  apply hx.apply_one_ne_zero
  have hval : x 1 = -(x 1) := by
    conv_lhs => rw [h]
    rw [ClassFunction.neg_apply]
  linear_combination hval / 2

open Classical in
/-- A signed nontrivial irreducible has unit norm: `⟨x, x⟩ = 1`. -/
theorem IsSignedNontrivialIrr.inner_self [Invertible (Nat.card G : ℂ)] {x : ClassFunction G ℂ}
    (hx : IsSignedNontrivialIrr x) : ClassFunction.inner x x = 1 := by
  rw [isSignedNontrivialIrr_inner hx hx, if_pos rfl, if_neg (fun h => hx.ne_neg_self h), sub_zero]

/-- A *signed triple*: `β` is the sum of a 3-element set `A` of pairwise-orthogonal signed
nontrivial irreducible characters.  This is the structure of each `β_{ij}` of Peterfalvi (3.5.1)
(`exists_betaSet`); the `A_{ij}` of the (3.5.2)-(3.5.5) combinatorics are the carriers `A`. -/
structure IsSignedTriple [Invertible (Nat.card G : ℂ)] (β : ClassFunction G ℂ)
    (A : Finset (ClassFunction G ℂ)) : Prop where
  card_eq_three : A.card = 3
  signed : ∀ x ∈ A, IsSignedNontrivialIrr x
  pairwise_orthogonal : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ClassFunction.inner x y = 0
  sum_eq : β = ∑ x ∈ A, x

/-- Packaging of `exists_signedTriple_of_inner_self_three` as an `IsSignedTriple`. -/
theorem exists_isSignedTriple_of_inner_self_three [Invertible (Nat.card G : ℂ)]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) (hnorm : ClassFunction.inner φ φ = 3)
    (htriv : ClassFunction.inner φ (trivialClassFunction G) = 0) :
    ∃ A : Finset (ClassFunction G ℂ), IsSignedTriple φ A := by
  obtain ⟨A, hcard, hsig, horth, hsum⟩ := exists_signedTriple_of_inner_self_three hφ hnorm htriv
  exact ⟨A, ⟨hcard, hsig, horth, hsum⟩⟩

/-- In a signed triple, the negative of a member is not a member (else the member and its
negative, both in `A`, would not be orthogonal: `⟨x, -x⟩ = -1 ≠ 0`). -/
theorem IsSignedTriple.neg_not_mem [Invertible (Nat.card G : ℂ)]
    {β : ClassFunction G ℂ} {A : Finset (ClassFunction G ℂ)} (hA : IsSignedTriple β A)
    {x : ClassFunction G ℂ} (hx : x ∈ A) : -x ∉ A := by
  intro hnx
  have hxsig := hA.signed x hx
  have h0 := hA.pairwise_orthogonal x hx (-x) hnx (fun h => hxsig.ne_neg_self h)
  rw [ClassFunction.inner_neg_right, hxsig.inner_self] at h0
  exact one_ne_zero (neg_eq_zero.mp h0)

open Classical in
/-- **(3.5.2) coefficient formula**: for a signed triple `β = ∑ A` and a signed irreducible `c`,
`⟨β, c⟩ = [c ∈ A] - [-c ∈ A]`. -/
theorem IsSignedTriple.inner_right_signed [Invertible (Nat.card G : ℂ)]
    {β : ClassFunction G ℂ} {A : Finset (ClassFunction G ℂ)} (hA : IsSignedTriple β A)
    {c : ClassFunction G ℂ} (hc : IsSignedNontrivialIrr c) :
    ClassFunction.inner β c = (if c ∈ A then 1 else 0) - (if -c ∈ A then 1 else 0) := by
  rw [hA.sum_eq, inner_sum_left,
    Finset.sum_congr rfl (fun x hx => isSignedNontrivialIrr_inner (hA.signed x hx) hc),
    Finset.sum_sub_distrib, Finset.sum_ite_eq' A c (fun _ => (1 : ℂ)),
    Finset.sum_ite_eq' A (-c) (fun _ => (1 : ℂ))]

/-- **(3.5.1) norm**: a signed triple has `⟨β, β⟩ = |A| = 3`. -/
theorem IsSignedTriple.inner_self [Invertible (Nat.card G : ℂ)]
    {β : ClassFunction G ℂ} {A : Finset (ClassFunction G ℂ)} (hA : IsSignedTriple β A) :
    ClassFunction.inner β β = (A.card : ℂ) := by
  classical
  nth_rewrite 2 [hA.sum_eq]
  rw [inner_sum_right]
  rw [Finset.sum_congr rfl (fun x hx => by
    rw [hA.inner_right_signed (hA.signed x hx), if_pos hx,
      if_neg (hA.neg_not_mem hx), sub_zero])]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Peterfalvi (3.5.2)** (no-negatives half): if two signed triples `β = ∑ A`, `β' = ∑ A'` have
`⟨β, β'⟩ = 1` and agree at `1` (`β 1 = β' 1`), then no `c ∈ A` has `-c ∈ A'`.  Were there such a
`c`, then `⟨β, c⟩ = 1`, `⟨β', c⟩ = -1`, so `⟨β - β', c⟩ = 2`; with `‖β - β'‖² = 4`, the vector
`(β - β') - 2c` has zero norm, hence `β - β' = 2c`.  But `(β - β')(1) = β(1) - β'(1) = 0` while
`2 · c(1) ≠ 0` (signed irreducibles are nonzero at `1`) — a contradiction.  (Peterfalvi's
`2χ₃ = Ind(α₁₁ - α₁₂)` vanishing at `1 ∈ G`.) -/
theorem IsSignedTriple.no_neg_of_inner_one [Invertible (Nat.card G : ℂ)]
    {β β' : ClassFunction G ℂ} {A A' : Finset (ClassFunction G ℂ)}
    (hA : IsSignedTriple β A) (hA' : IsSignedTriple β' A')
    (hinner : ClassFunction.inner β β' = 1) (hone : β 1 = β' 1)
    {c : ClassFunction G ℂ} (hcA : c ∈ A) (hcA' : -c ∈ A') : False := by
  have hcsig : IsSignedNontrivialIrr c := hA.signed c hcA
  -- `⟨β, c⟩ = 1` and `⟨β', c⟩ = -1`.
  have hbc : ClassFunction.inner β c = 1 := by
    rw [hA.inner_right_signed hcsig, if_pos hcA, if_neg (hA.neg_not_mem hcA), sub_zero]
  have hcnA' : c ∉ A' := fun h => hA'.neg_not_mem h hcA'
  have hb'c : ClassFunction.inner β' c = -1 := by
    rw [hA'.inner_right_signed hcsig, if_neg hcnA', if_pos hcA', zero_sub]
  -- norms: `⟨β,β⟩ = ⟨β',β'⟩ = 3`, `⟨β',β⟩ = 1`.
  have hbb : ClassFunction.inner β β = 3 := by rw [hA.inner_self, hA.card_eq_three]; norm_num
  have hb'b' : ClassFunction.inner β' β' = 3 := by rw [hA'.inner_self, hA'.card_eq_three]; norm_num
  have hb'b : ClassFunction.inner β' β = 1 := by rw [inner_conj_symm β β', hinner, star_one]
  set g : ClassFunction G ℂ := β - β' with hg
  -- `⟨g, c⟩ = 2`, `⟨c, g⟩ = 2`, `⟨g, g⟩ = 4`.
  have hgc : ClassFunction.inner g c = 2 := by
    rw [hg, ClassFunction.inner_sub_left, hbc, hb'c]; ring
  have hcg : ClassFunction.inner c g = 2 := by rw [inner_conj_symm g c, hgc]; norm_num
  have hgg : ClassFunction.inner g g = 4 := by
    rw [hg, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hbb, hb'b', hinner, hb'b]; norm_num
  -- `(β - β') - 2c` has zero norm, so it is `0`.
  have hs2 : star (2 : ℂ) = 2 := by norm_num
  have hzero : ClassFunction.inner (g - (2 : ℂ) • c) (g - (2 : ℂ) • c) = 0 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hgg, hgc, hcg, hcsig.inner_self, hs2]
    ring
  have hg2c : g = (2 : ℂ) • c :=
    sub_eq_zero.mp (eq_zero_of_inner_self_re_eq_zero (by rw [hzero]; exact Complex.zero_re))
  -- evaluate at `1`: `0 = g(1) = 2 · c(1)`, contradicting `c(1) ≠ 0`.
  have hg1 : g 1 = 0 := by rw [hg, ClassFunction.sub_apply, hone, sub_self]
  rw [hg2c, ClassFunction.smul_apply] at hg1
  exact hcsig.apply_one_ne_zero ((mul_eq_zero.mp hg1).resolve_left (by norm_num))

open Classical in
/-- **Peterfalvi (3.5.2)** `L(ij, i'j')`: two signed triples with `⟨β, β'⟩ = 1` that agree at `1`
share exactly one element (`|A ∩ A'| = 1`) and no element of one is the negative of an element of
the other (`∀ x ∈ A, -x ∉ A'`).  The no-negatives half is `no_neg_of_inner_one`; given it,
`⟨β', β⟩ = ∑_{x ∈ A} [x ∈ A'] = |A ∩ A'|`, which equals `⟨β, β'⟩* = 1`. -/
theorem IsSignedTriple.L_of_inner_one [Invertible (Nat.card G : ℂ)]
    {β β' : ClassFunction G ℂ} {A A' : Finset (ClassFunction G ℂ)}
    (hA : IsSignedTriple β A) (hA' : IsSignedTriple β' A')
    (hinner : ClassFunction.inner β β' = 1) (hone : β 1 = β' 1) :
    (A ∩ A').card = 1 ∧ ∀ x ∈ A, -x ∉ A' := by
  have hno : ∀ x ∈ A, -x ∉ A' :=
    fun x hx hnx => hA.no_neg_of_inner_one hA' hinner hone hx hnx
  refine ⟨?_, hno⟩
  have key : ClassFunction.inner β' β = ((A ∩ A').card : ℂ) := by
    conv_lhs => rw [hA.sum_eq]
    rw [inner_sum_right, Finset.sum_congr rfl (fun x hx => by
      rw [hA'.inner_right_signed (hA.signed x hx), if_neg (hno x hx), sub_zero]),
      Finset.sum_boole, Finset.filter_mem_eq_inter]
  have : ((A ∩ A').card : ℂ) = 1 := by rw [← key, inner_conj_symm β β', hinner, star_one]
  exact_mod_cast this

open Classical in
/-- **Peterfalvi (3.5.2)** `O(ij, i'j')`: two signed triples that are orthogonal (`⟨β, β'⟩ = 0`)
have `|A ∩ A'| = |{x ∈ A : -x ∈ A'}|`.  (Expanding `⟨β', β⟩ = ∑_{x ∈ A}([x ∈ A'] - [-x ∈ A'])`
gives `|A ∩ A'| - |{x ∈ A : -x ∈ A'}|`, which equals `⟨β, β'⟩* = 0`.)  Downstream this is used as:
a shared element of `A` and `A'` forces a *negated* shared element too. -/
theorem IsSignedTriple.O_card_inter_eq [Invertible (Nat.card G : ℂ)]
    {β β' : ClassFunction G ℂ} {A A' : Finset (ClassFunction G ℂ)}
    (hA : IsSignedTriple β A) (hA' : IsSignedTriple β' A')
    (hinner : ClassFunction.inner β β' = 0) :
    (A ∩ A').card = (A.filter (fun x => -x ∈ A')).card := by
  have key : ClassFunction.inner β' β =
      ((A ∩ A').card : ℂ) - ((A.filter (fun x => -x ∈ A')).card : ℂ) := by
    conv_lhs => rw [hA.sum_eq]
    rw [inner_sum_right,
      Finset.sum_congr rfl (fun x hx => hA'.inner_right_signed (hA.signed x hx)),
      Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, Finset.filter_mem_eq_inter]
  rw [inner_conj_symm β β', hinner, star_zero] at key
  have hpm : ((A ∩ A').card : ℂ) = ((A.filter (fun x => -x ∈ A')).card : ℂ) :=
    sub_eq_zero.mp key.symm
  exact_mod_cast hpm

/- 3.5.1 (cont.): the virtual characters `β_{ij} = Ind_W^G α_{ij} - 1_G` -/

namespace TICyclicHypothesis

/-- **Peterfalvi (3.5.1)**: `β_{ij} = Ind_W^G α_{ij} - 1_G` (for `i, j ≥ 1`). -/
noncomputable def beta (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    ClassFunction G ℂ :=
  app.tau.toDadeMap (hyp.alpha hVeq χ₁ χ₂) - trivialClassFunction G

/-- `β_{ij} ∈ ℤ[Irr G]`: `Ind_W^G` preserves virtual characters (`α_{ij} ∈ ℤ[Irr W]`) and `1_G`
is a character. -/
theorem beta_mem_ZIrr (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    hyp.beta hVeq app χ₁ χ₂ ∈ ZIrr G :=
  Submodule.sub_mem _
    (app.tau.maps_virtualCharacter (hyp.alpha hVeq χ₁ χ₂) (hyp.alpha_mem_ZIrr hVeq χ₁ χ₂))
    (trivialClassFunction_isIrreducible.mem_ZIrr)

/-- **Peterfalvi (3.5.2)** input: every `β_{ij}` takes the value `-1` at `1 ∈ G`.  Indeed
`Ind_W^G α_{ij}(1) = [G : W] · α_{ij}(1) = 0` because `α_{ij}` vanishes on `W₁ ⊇ {1}`, so
`β_{ij}(1) = 0 - 1_G(1) = -1`.  In particular all the `β_{ij}` agree at `1`, which is what powers
the no-negatives half of `L(ij, i'j')` (Peterfalvi's `2χ₃ = Ind(α₁₁ - α₁₂)` vanishing at `1`). -/
theorem beta_apply_one (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    (hyp.beta hVeq app χ₁ χ₂ : ClassFunction G ℂ) 1 = -1 := by
  change (app.tau.toDadeIsometryData.toDadeMap (hyp.alpha hVeq χ₁ χ₂) -
    trivialClassFunction G) 1 = -1
  rw [ClassFunction.sub_apply, trivialClassFunction_apply,
    hyp.tau_eq_induce app.tau.toDadeIsometryData (hyp.alpha hVeq χ₁ χ₂),
    ClassFunction.induce_apply_one, hyp.alpha_coe,
    hyp.alphaCF_eq_zero_of_mem_W1_subgroupOf χ₁ χ₂ (Subgroup.one_mem _), mul_zero, zero_sub]

open Classical in
/-- **Peterfalvi (3.5.1)**: the Gram matrix of the `β_{ij}` family (`i, j ≥ 1`):
`⟨β_{ij}, β_{kl}⟩ = δ_{ik} + δ_{jl} + δ_{(ij),(kl)}`.  Subtracting `1_G` from the induced family
(whose Gram matrix is `tau_alpha_inner`) drops each entry by `1` (Frobenius
`tau_alpha_inner_trivial` and `⟨1_G, 1_G⟩ = 1`), giving `3` on the diagonal, `1` for one shared
index, and `0` when both indices differ. -/
theorem beta_inner (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ b₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ b₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) (hb₁ : b₁ ≠ 1) (hb₂ : b₂ ≠ 1) :
    ClassFunction.inner (hyp.beta hVeq app a₁ a₂) (hyp.beta hVeq app b₁ b₂) =
      (if a₁ = b₁ then 1 else 0) + (if a₂ = b₂ then 1 else 0)
        + (if a₁ = b₁ ∧ a₂ = b₂ then 1 else 0) := by
  change ClassFunction.inner
      (app.tau.toDadeMap (hyp.alpha hVeq a₁ a₂) - trivialClassFunction G)
      (app.tau.toDadeMap (hyp.alpha hVeq b₁ b₂) - trivialClassFunction G) = _
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    hyp.tau_alpha_inner hVeq app ha₁ ha₂ hb₁ hb₂,
    hyp.tau_alpha_inner_trivial hVeq app ha₁ ha₂,
    inner_conj_symm (app.tau.toDadeMap (hyp.alpha hVeq b₁ b₂)) (trivialClassFunction G),
    hyp.tau_alpha_inner_trivial hVeq app hb₁ hb₂, inner_trivialClassFunction_self]
  simp only [star_one]
  ring

/-- **Peterfalvi (3.5.1)**: `‖β_{ij}‖² = 3` for `i, j ≥ 1`. -/
theorem beta_inner_self (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) :
    ClassFunction.inner (hyp.beta hVeq app a₁ a₂) (hyp.beta hVeq app a₁ a₂) = 3 := by
  rw [hyp.beta_inner hVeq app ha₁ ha₂ ha₁ ha₂]
  norm_num

/-- **Peterfalvi (3.5.1)**: `⟨β_{ij}, 1_G⟩ = 0` for `i, j ≥ 1` (Frobenius `⟨Ind α_{ij}, 1_G⟩ = 1`
cancels `⟨1_G, 1_G⟩ = 1`). -/
theorem beta_inner_trivial (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) :
    ClassFunction.inner (hyp.beta hVeq app a₁ a₂) (trivialClassFunction G) = 0 := by
  change ClassFunction.inner
      (app.tau.toDadeMap (hyp.alpha hVeq a₁ a₂) - trivialClassFunction G)
      (trivialClassFunction G) = 0
  rw [ClassFunction.inner_sub_left, hyp.tau_alpha_inner_trivial hVeq app ha₁ ha₂,
    inner_trivialClassFunction_self, sub_self]

/-- **Peterfalvi (3.5.1)**: `β_{ij} = ∑_{χ ∈ A_{ij}} χ` for a set `A_{ij}` of three pairwise
orthogonal elements of `±(Irr(G) - {1_G})` (`i, j ≥ 1`).  This extracts the set `A_{ij}` from the
norm-`3` virtual character `β_{ij}` (`beta_mem_ZIrr`, `beta_inner_self = 3`, `beta_inner_trivial =
0`) via `exists_signedTriple_of_inner_self_three`.  It is the combinatorial starting point of
(3.5.2)-(3.5.5). -/
theorem exists_betaSet (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) :
    ∃ A : Finset (ClassFunction G ℂ),
      A.card = 3 ∧ (∀ x ∈ A, IsSignedNontrivialIrr x) ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → ClassFunction.inner x y = 0) ∧
      hyp.beta hVeq app a₁ a₂ = ∑ x ∈ A, x :=
  exists_signedTriple_of_inner_self_three (hyp.beta_mem_ZIrr hVeq app a₁ a₂)
    (hyp.beta_inner_self hVeq app ha₁ ha₂) (hyp.beta_inner_trivial hVeq app ha₁ ha₂)

/-- `β_{ij}` packaged as a signed triple: `∃ A, IsSignedTriple β_{ij} A`. -/
theorem exists_isSignedTriple_beta (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) :
    ∃ A : Finset (ClassFunction G ℂ), IsSignedTriple (hyp.beta hVeq app a₁ a₂) A :=
  exists_isSignedTriple_of_inner_self_three (hyp.beta_mem_ZIrr hVeq app a₁ a₂)
    (hyp.beta_inner_self hVeq app ha₁ ha₂) (hyp.beta_inner_trivial hVeq app ha₁ ha₂)

open Classical in
/-- `⟨β_{ij}, β_{i'j'}⟩ = 1` when the two index pairs agree in **exactly one** coordinate
(`i = i', j ≠ j'` or `i ≠ i', j = j'`).  Immediate from the Gram matrix `beta_inner`. -/
theorem beta_inner_eq_one_of_one_shared (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ b₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ b₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) (hb₁ : b₁ ≠ 1) (hb₂ : b₂ ≠ 1)
    (hshared : (a₁ = b₁ ∧ a₂ ≠ b₂) ∨ (a₁ ≠ b₁ ∧ a₂ = b₂)) :
    ClassFunction.inner (hyp.beta hVeq app a₁ a₂) (hyp.beta hVeq app b₁ b₂) = 1 := by
  rw [hyp.beta_inner hVeq app ha₁ ha₂ hb₁ hb₂]
  rcases hshared with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]; norm_num
  · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.1)]; norm_num

open Classical in
/-- **Peterfalvi (3.5.2)** `L(ij, i'j')` for the `β_{ij}`: signed triples `A`, `A'` of two
`β`-characters whose index pairs share exactly one coordinate intersect in exactly one element and
admit no negated common element.  Combines `beta_inner_eq_one_of_one_shared`, the common value
`β(1) = -1` (`beta_apply_one`), and the abstract `IsSignedTriple.L_of_inner_one`. -/
theorem betaTriple_L (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ b₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ b₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) (hb₁ : b₁ ≠ 1) (hb₂ : b₂ ≠ 1)
    (hshared : (a₁ = b₁ ∧ a₂ ≠ b₂) ∨ (a₁ ≠ b₁ ∧ a₂ = b₂)) :
    ∃ A A' : Finset (ClassFunction G ℂ),
      IsSignedTriple (hyp.beta hVeq app a₁ a₂) A ∧ IsSignedTriple (hyp.beta hVeq app b₁ b₂) A' ∧
      (A ∩ A').card = 1 ∧ ∀ x ∈ A, -x ∉ A' := by
  obtain ⟨A, hA⟩ := hyp.exists_isSignedTriple_beta hVeq app ha₁ ha₂
  obtain ⟨A', hA'⟩ := hyp.exists_isSignedTriple_beta hVeq app hb₁ hb₂
  have hinner := hyp.beta_inner_eq_one_of_one_shared hVeq app ha₁ ha₂ hb₁ hb₂ hshared
  have hone : (hyp.beta hVeq app a₁ a₂) 1 = (hyp.beta hVeq app b₁ b₂) 1 := by
    rw [hyp.beta_apply_one, hyp.beta_apply_one]
  obtain ⟨hcard, hno⟩ := hA.L_of_inner_one hA' hinner hone
  exact ⟨A, A', hA, hA', hcard, hno⟩

open Classical in
/-- `⟨β_{ij}, β_{i'j'}⟩ = 0` when the two index pairs differ in **both** coordinates
(`i ≠ i'`, `j ≠ j'`).  Immediate from the Gram matrix `beta_inner`. -/
theorem beta_inner_eq_zero_of_both_diff (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ b₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ b₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) (hb₁ : b₁ ≠ 1) (hb₂ : b₂ ≠ 1)
    (hd₁ : a₁ ≠ b₁) (hd₂ : a₂ ≠ b₂) :
    ClassFunction.inner (hyp.beta hVeq app a₁ a₂) (hyp.beta hVeq app b₁ b₂) = 0 := by
  rw [hyp.beta_inner hVeq app ha₁ ha₂ hb₁ hb₂, if_neg hd₁, if_neg hd₂, if_neg (fun h => hd₁ h.1)]
  norm_num

open Classical in
/-- **Peterfalvi (3.5.2)** `O(ij, i'j')` for the `β_{ij}`: signed triples `A`, `A'` of two
orthogonal `β`-characters (index pairs differing in both coordinates) satisfy
`|A ∩ A'| = |{x ∈ A : -x ∈ A'}|`.  Combines `beta_inner_eq_zero_of_both_diff` and the abstract
`IsSignedTriple.O_card_inter_eq`. -/
theorem betaTriple_O (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ b₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ b₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) (hb₁ : b₁ ≠ 1) (hb₂ : b₂ ≠ 1)
    (hd₁ : a₁ ≠ b₁) (hd₂ : a₂ ≠ b₂) :
    ∃ A A' : Finset (ClassFunction G ℂ),
      IsSignedTriple (hyp.beta hVeq app a₁ a₂) A ∧ IsSignedTriple (hyp.beta hVeq app b₁ b₂) A' ∧
      (A ∩ A').card = (A.filter (fun x => -x ∈ A')).card := by
  obtain ⟨A, hA⟩ := hyp.exists_isSignedTriple_beta hVeq app ha₁ ha₂
  obtain ⟨A', hA'⟩ := hyp.exists_isSignedTriple_beta hVeq app hb₁ hb₂
  exact ⟨A, A', hA, hA',
    hA.O_card_inter_eq hA' (hyp.beta_inner_eq_zero_of_both_diff hVeq app ha₁ ha₂ hb₁ hb₂ hd₁ hd₂)⟩

/- 3.5.3: `sup(w₁, w₂) ≥ 5` -/

/-- **Peterfalvi (3.5.3)**: `sup(w₁, w₂) ≥ 5`.  Both `w₁ = |W₁|` and `w₂ = |W₂|` are odd (dividing
the odd `|W|`), greater than `1` (`W₁`, `W₂` nontrivial), and coprime (Hypothesis (3.1)).  Were
both `≤ 4`, each would equal `3` (the only odd number in `(1, 4]`), contradicting coprimality
(`gcd 3 3 = 3 ≠ 1`).  Peterfalvi then assumes `w₁ ≥ 5` by the `W₁ ↔ W₂` symmetry. -/
theorem sup_card_ge_five (hyp : TICyclicHypothesis G) :
    5 ≤ Nat.card hyp.W1 ∨ 5 ≤ Nat.card hyp.W2 := by
  haveI : Finite G := Finite.of_fintype G
  have h1odd : Odd (Nat.card hyp.W1) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W1_le_W)
  have h2odd : Odd (Nat.card hyp.W2) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W2_le_W)
  have h1gt : 1 < Nat.card hyp.W1 :=
    Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W1_nontrivial)
  have h2gt : 1 < Nat.card hyp.W2 :=
    Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W2_nontrivial)
  by_contra h
  obtain ⟨hlt1, hlt2⟩ := not_or.mp h
  rw [not_le] at hlt1 hlt2
  obtain ⟨k, hk⟩ := h1odd
  obtain ⟨l, hl⟩ := h2odd
  have hc1 : Nat.card hyp.W1 = 3 := by omega
  have hc2 : Nat.card hyp.W2 = 3 := by omega
  have hcop := hyp.W_card_coprime
  rw [hc1, hc2] at hcop
  exact absurd hcop (by decide)

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05
