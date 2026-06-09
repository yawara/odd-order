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

/- 3.5.4: the grid of signed triples and the sunflower lemma `|⋂_i A_{i1}| = 1` -/

/-- A 3-element finset containing two distinct elements `a, b` is `{a, b, c}` for a (unique)
third element `c ∉ {a, b}`.  Used to name "the third element" of each `A_{ij}` in (3.5.4). -/
theorem exists_third_of_card_three {α : Type*} [DecidableEq α] {s : Finset α} (hs : s.card = 3)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    ∃ c, c ∈ s ∧ c ≠ a ∧ c ≠ b ∧ s = {a, b, c} := by
  have hsub : ({a, b} : Finset α) ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    · rw [Finset.mem_singleton] at hx; exact hx ▸ hb
  have hcard2 : ({a, b} : Finset α).card = 2 := by
    rw [Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr hab), Finset.card_singleton]
  have hd : (s \ {a, b}).card = 1 := by rw [Finset.card_sdiff_of_subset hsub, hs, hcard2]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hd
  have hcmem : c ∈ s \ {a, b} := hc ▸ Finset.mem_singleton_self c
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcmem
  obtain ⟨hcs, hcab⟩ := hcmem
  refine ⟨c, hcs, hcab.1, hcab.2, ?_⟩
  apply Finset.ext
  intro x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    · by_cases hxb : x = b
      · exact Or.inr (Or.inl hxb)
      · refine Or.inr (Or.inr ?_)
        have : x ∈ s \ {a, b} := by
          rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨hx, fun h => h.elim hxa hxb⟩
        rw [hc, Finset.mem_singleton] at this; exact this
  · rintro (rfl | rfl | rfl)
    · exact ha
    · exact hb
    · exact hcs

/-- The number of a 3-element list `{a, b, c}` of distinct elements that lie in `s`, as a sum of
indicators.  Used to turn the `(3.5.4)` cardinality relations into a linear-arithmetic system. -/
theorem card_inter_triple {α : Type*} [DecidableEq α] (s : Finset α) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (s ∩ {a, b, c}).card =
      (if a ∈ s then 1 else 0) + (if b ∈ s then 1 else 0) + (if c ∈ s then 1 else 0) := by
  rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter,
    Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, add_assoc]

/-- The number of `x ∈ s` whose negative lies in a 3-element set `{a, b, c}` of distinct elements,
as a sum of indicators (`-x ∈ {a,b,c} ↔ x ∈ {-a,-b,-c}`).  The "negated" companion of
`card_inter_triple`, for the `filter` side of the `O`-relation. -/
theorem card_filter_neg_triple {α : Type*} [AddGroup α] [DecidableEq α] (s : Finset α)
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (s.filter (fun x => -x ∈ ({a, b, c} : Finset α))).card =
      (if -a ∈ s then 1 else 0) + (if -b ∈ s then 1 else 0) + (if -c ∈ s then 1 else 0) := by
  have heq : s.filter (fun x => -x ∈ ({a, b, c} : Finset α)) = s ∩ {-a, -b, -c} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      neg_eq_iff_eq_neg]
  rw [heq, card_inter_triple s (neg_injective.ne hab) (neg_injective.ne hac) (neg_injective.ne hbc)]

/-- From `card {a,b,c} = 3`, the three elements are pairwise distinct. -/
theorem triple_distinct {α : Type*} [DecidableEq α] {a b c : α}
    (h : ({a, b, c} : Finset α).card = 3) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have key : ∀ x y z : α, x ∈ ({y, z} : Finset α) → ({x, y, z} : Finset α).card ≠ 3 := by
    intro x y z hx
    rw [show ({x, y, z} : Finset α) = {y, z} from Finset.insert_eq_self.mpr hx]
    have := Finset.card_insert_le y ({z} : Finset α)
    rw [Finset.card_singleton] at this; omega
  refine ⟨fun hab => key a b c ?_ h, fun hac => key a b c ?_ h, fun hbc => ?_⟩
  · rw [hab]; exact Finset.mem_insert_self b {c}
  · rw [hac]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self c)
  · exact key b a c (by rw [hbc]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self c))
      (by rw [Finset.insert_comm]; exact h)

open scoped Classical in
/-- An abstract *grid of signed triples*: a family `A i j` (rows `i : ι`, columns `j : κ`) of
signed-triple sets satisfying the Peterfalvi relations.  `card_eq_three`/`signed`/`orthogonal` are
the per-cell `IsSignedTriple` data; `inter_L`/`noNeg_L` are `L(ij,i'j')` (index pairs sharing
exactly one coordinate) and `inter_O` is `O(ij,i'j')` (both coordinates differing).  This is the
data the (3.5.4) sunflower argument consumes; the concrete `β`-family `Afam` is an instance
(`Afam_isSignedTripleGrid`). -/
structure IsSignedTripleGrid [Invertible (Nat.card G : ℂ)] {ι κ : Type*}
    (A : ι → κ → Finset (ClassFunction G ℂ)) : Prop where
  card_eq_three : ∀ i j, (A i j).card = 3
  signed : ∀ i j, ∀ x ∈ A i j, IsSignedNontrivialIrr x
  orthogonal : ∀ i j, ∀ x ∈ A i j, ∀ y ∈ A i j, x ≠ y → ClassFunction.inner x y = 0
  inter_L : ∀ (i i' : ι) (j j' : κ), (i = i' ∧ j ≠ j') ∨ (i ≠ i' ∧ j = j') →
    (A i j ∩ A i' j').card = 1
  noNeg_L : ∀ (i i' : ι) (j j' : κ), (i = i' ∧ j ≠ j') ∨ (i ≠ i' ∧ j = j') →
    ∀ x ∈ A i j, -x ∉ A i' j'
  inter_O : ∀ (i i' : ι) (j j' : κ), i ≠ i' → j ≠ j' →
    (A i j ∩ A i' j').card = ((A i j).filter (fun x => -x ∈ A i' j')).card

namespace IsSignedTripleGrid

variable [Invertible (Nat.card G : ℂ)] {ι κ : Type*} {A : ι → κ → Finset (ClassFunction G ℂ)}

/-- In a single cell `A i j`, the negative of a member is not a member (it is a signed triple). -/
theorem neg_not_mem_self (hG : IsSignedTripleGrid A) {i : ι} {j : κ} {x : ClassFunction G ℂ}
    (hx : x ∈ A i j) : -x ∉ A i j := by
  intro hnx
  have hxsig := hG.signed i j x hx
  have h0 := hG.orthogonal i j x hx (-x) hnx (fun h => hxsig.ne_neg_self h)
  rw [ClassFunction.inner_neg_right, hxsig.inner_self] at h0
  exact one_ne_zero (neg_eq_zero.mp h0)

/-- **Uniqueness half of (3.5.4)**: for a fixed column `j₀`, at most one element lies in every
`A i j₀` (two such would both lie in `A i₁ j₀ ∩ A i₂ j₀`, a singleton by `L`). -/
theorem common_unique [Fintype ι] (hG : IsSignedTripleGrid A) (hι : 2 ≤ Fintype.card ι) {j₀ : κ}
    {z z' : ClassFunction G ℂ} (hz : ∀ i, z ∈ A i j₀) (hz' : ∀ i, z' ∈ A i j₀) : z = z' := by
  classical
  haveI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i₁, i₂, h12⟩ := exists_pair_ne ι
  have hcard : (A i₁ j₀ ∩ A i₂ j₀).card = 1 := hG.inter_L i₁ i₂ j₀ j₀ (Or.inr ⟨h12, rfl⟩)
  have hle := Finset.card_le_one.mp (le_of_eq hcard)
  exact hle z (Finset.mem_inter.mpr ⟨hz i₁, hz i₂⟩) z' (Finset.mem_inter.mpr ⟨hz' i₁, hz' i₂⟩)

/-- **(3.5.4) reduction**: if no element is common to every `A i j₀` (the negation of (3.5.4)),
then three rows `i₁, i₂, i₃` have *no* common element — a "triangle" (their three pairwise
intersection elements are then forced distinct).  Pick distinct `i₁, i₂` with common element `z`
(unique by `L`); since `z` is not common to all rows there is `i₃` with `z ∉ A i₃ j₀`; the triple
`{i₁, i₂, i₃}` then shares no element (a common `w` would equal `z ∉ A i₃ j₀`). -/
theorem exists_triangle_of_not_exists_common [Fintype ι] (hG : IsSignedTripleGrid A)
    (hι : 2 ≤ Fintype.card ι) (j₀ : κ) (hno : ¬ ∃ z, ∀ i, z ∈ A i j₀) :
    ∃ i₁ i₂ i₃ : ι, i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ ∧
      ¬ ∃ w, w ∈ A i₁ j₀ ∧ w ∈ A i₂ j₀ ∧ w ∈ A i₃ j₀ := by
  classical
  haveI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i₁, i₂, h12⟩ := exists_pair_ne ι
  have hcard : (A i₁ j₀ ∩ A i₂ j₀).card = 1 := hG.inter_L i₁ i₂ j₀ j₀ (Or.inr ⟨h12, rfl⟩)
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
  have hzmem : z ∈ A i₁ j₀ ∩ A i₂ j₀ := hz ▸ Finset.mem_singleton_self z
  obtain ⟨hz1, hz2⟩ := Finset.mem_inter.mp hzmem
  -- some row misses `z`, else `z` is common.
  obtain ⟨i₃, hz3⟩ : ∃ i₃, z ∉ A i₃ j₀ := by
    by_contra hcon
    exact hno ⟨z, fun i => not_not.mp (fun h => hcon ⟨i, h⟩)⟩
  refine ⟨i₁, i₂, i₃, h12, ?_, ?_, ?_⟩
  · rintro rfl; exact hz3 hz1
  · rintro rfl; exact hz3 hz2
  · rintro ⟨w, hw1, hw2, hw3⟩
    have hle := Finset.card_le_one.mp (le_of_eq hcard)
    exact hz3 ((hle w (Finset.mem_inter.mpr ⟨hw1, hw2⟩) z hzmem) ▸ hw3)

open scoped Classical in
/-- **(3.5.4) named triangle**: from three rows `i₁, i₂, i₃` with no common element, name their
three pairwise-intersection elements `e₁₂, e₁₃, e₂₃` (the "vertices", forced distinct) and the
three remaining "third" elements `t₁, t₂, t₃`, giving the explicit decompositions
`A i₁ j₀ = {e₁₂, e₁₃, t₁}`, `A i₂ j₀ = {e₁₂, e₂₃, t₂}`, `A i₃ j₀ = {e₁₃, e₂₃, t₃}`
(Peterfalvi's `β₁₁ = χ₁+χ₂+χ₃`, `β₂₁ = χ₁+χ₄+χ₅`, `β₃₁ = χ₂+χ₄+χ₆`).  Input to the Cases-I/II
argument that adds a fourth row. -/
theorem exists_namedTriangle (hG : IsSignedTripleGrid A) {i₁ i₂ i₃ : ι} {j₀ : κ}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    (hnoc : ¬ ∃ w, w ∈ A i₁ j₀ ∧ w ∈ A i₂ j₀ ∧ w ∈ A i₃ j₀) :
    ∃ e₁₂ e₁₃ e₂₃ t₁ t₂ t₃ : ClassFunction G ℂ,
      A i₁ j₀ = {e₁₂, e₁₃, t₁} ∧ A i₂ j₀ = {e₁₂, e₂₃, t₂} ∧ A i₃ j₀ = {e₁₃, e₂₃, t₃} ∧
      e₁₂ ≠ e₁₃ ∧ e₁₂ ≠ e₂₃ ∧ e₁₃ ≠ e₂₃ := by
  classical
  obtain ⟨e₁₂, he12⟩ := Finset.card_eq_one.mp (hG.inter_L i₁ i₂ j₀ j₀ (Or.inr ⟨h12, rfl⟩))
  obtain ⟨e₁₃, he13⟩ := Finset.card_eq_one.mp (hG.inter_L i₁ i₃ j₀ j₀ (Or.inr ⟨h13, rfl⟩))
  obtain ⟨e₂₃, he23⟩ := Finset.card_eq_one.mp (hG.inter_L i₂ i₃ j₀ j₀ (Or.inr ⟨h23, rfl⟩))
  obtain ⟨m12a, m12b⟩ := Finset.mem_inter.mp (he12 ▸ Finset.mem_singleton_self e₁₂)
  obtain ⟨m13a, m13b⟩ := Finset.mem_inter.mp (he13 ▸ Finset.mem_singleton_self e₁₃)
  obtain ⟨m23a, m23b⟩ := Finset.mem_inter.mp (he23 ▸ Finset.mem_singleton_self e₂₃)
  have d1213 : e₁₂ ≠ e₁₃ := by rintro rfl; exact hnoc ⟨e₁₂, m12a, m12b, m13b⟩
  have d1223 : e₁₂ ≠ e₂₃ := by rintro rfl; exact hnoc ⟨e₁₂, m12a, m12b, m23b⟩
  have d1323 : e₁₃ ≠ e₂₃ := by rintro rfl; exact hnoc ⟨e₁₃, m13a, m23a, m13b⟩
  obtain ⟨t₁, _, _, _, hset1⟩ :=
    exists_third_of_card_three (hG.card_eq_three i₁ j₀) m12a m13a d1213
  obtain ⟨t₂, _, _, _, hset2⟩ :=
    exists_third_of_card_three (hG.card_eq_three i₂ j₀) m12b m23a d1223
  obtain ⟨t₃, _, _, _, hset3⟩ :=
    exists_third_of_card_three (hG.card_eq_three i₃ j₀) m13b m23b d1323
  exact ⟨e₁₂, e₁₃, e₂₃, t₁, t₂, t₃, hset1, hset2, hset3, d1213, d1223, d1323⟩

open scoped Classical in
/-- **(3.5.4) Case II is impossible**: a fourth row `i₄` whose `j₀`-cell is exactly the three
"third" elements `{χ₃, χ₅, χ₆}` (the K₄ configuration, Peterfalvi's `β₄₁ = χ₃+χ₅+χ₆`) yields a
contradiction.  Look at the second-column cell `B = A i₁ j₁`: writing `n_k = [χ_k ∈ B]`,
`p_k = [-χ_k ∈ B]`, the relations `L(i₁j₁, i₁j₀)` (gives `n₁+n₂+n₃ = 1`, `p₁=p₂=p₃=0`) and
`O(i₁j₁, i_pj₀)` for `p = 2,3,4` (give `n₁+n₄+n₅ = p₁+p₄+p₅` etc.) sum to `1 + 2(n₄+n₅+n₆) =
2(p₄+p₅+p₆)` — an odd number equal to an even one.  (This single parity argument replaces
Peterfalvi's case-by-case (3.5.4.6).) -/
theorem caseII_false (hG : IsSignedTripleGrid A) {i₁ i₂ i₃ i₄ : ι} {j₀ j₁ : κ}
    {χ1 χ2 χ3 χ4 χ5 χ6 : ClassFunction G ℂ} (hj : j₁ ≠ j₀)
    (hi12 : i₁ ≠ i₂) (hi13 : i₁ ≠ i₃) (hi14 : i₁ ≠ i₄)
    (hset1 : A i₁ j₀ = {χ1, χ2, χ3}) (hset2 : A i₂ j₀ = {χ1, χ4, χ5})
    (hset3 : A i₃ j₀ = {χ2, χ4, χ6}) (hset4 : A i₄ j₀ = {χ3, χ5, χ6}) : False := by
  classical
  obtain ⟨d12, d13, d23⟩ := triple_distinct (hset1 ▸ hG.card_eq_three i₁ j₀)
  obtain ⟨d14, d15, d45⟩ := triple_distinct (hset2 ▸ hG.card_eq_three i₂ j₀)
  obtain ⟨d24, d26, d46⟩ := triple_distinct (hset3 ▸ hG.card_eq_three i₃ j₀)
  obtain ⟨d35, d36, d56⟩ := triple_distinct (hset4 ▸ hG.card_eq_three i₄ j₀)
  have hnoNeg : ∀ x ∈ A i₁ j₁, -x ∉ A i₁ j₀ := hG.noNeg_L i₁ i₁ j₁ j₀ (Or.inl ⟨rfl, hj⟩)
  have hL : (A i₁ j₁ ∩ ({χ1, χ2, χ3} : Finset _)).card = 1 := by
    have h := hG.inter_L i₁ i₁ j₁ j₀ (Or.inl ⟨rfl, hj⟩); rwa [hset1] at h
  have hO2 : (A i₁ j₁ ∩ ({χ1, χ4, χ5} : Finset _)).card =
      (A i₁ j₁ |>.filter (fun x => -x ∈ ({χ1, χ4, χ5} : Finset _))).card := by
    have h := hG.inter_O i₁ i₂ j₁ j₀ hi12 hj; rwa [hset2] at h
  have hO3 : (A i₁ j₁ ∩ ({χ2, χ4, χ6} : Finset _)).card =
      (A i₁ j₁ |>.filter (fun x => -x ∈ ({χ2, χ4, χ6} : Finset _))).card := by
    have h := hG.inter_O i₁ i₃ j₁ j₀ hi13 hj; rwa [hset3] at h
  have hO4 : (A i₁ j₁ ∩ ({χ3, χ5, χ6} : Finset _)).card =
      (A i₁ j₁ |>.filter (fun x => -x ∈ ({χ3, χ5, χ6} : Finset _))).card := by
    have h := hG.inter_O i₁ i₄ j₁ j₀ hi14 hj; rwa [hset4] at h
  rw [card_inter_triple _ d12 d13 d23] at hL
  rw [card_inter_triple _ d14 d15 d45, card_filter_neg_triple _ d14 d15 d45] at hO2
  rw [card_inter_triple _ d24 d26 d46, card_filter_neg_triple _ d24 d26 d46] at hO3
  rw [card_inter_triple _ d35 d36 d56, card_filter_neg_triple _ d35 d36 d56] at hO4
  -- `-χ₁, -χ₂, -χ₃ ∉ B` (the `noNeg` half of `L(i₁j₁, i₁j₀)`).
  have hp1 : -χ1 ∉ A i₁ j₁ := fun hm =>
    hnoNeg _ hm (by rw [neg_neg, hset1]; exact Finset.mem_insert_self _ _)
  have hp2 : -χ2 ∉ A i₁ j₁ := fun hm =>
    hnoNeg _ hm (by rw [neg_neg, hset1]
                    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hp3 : -χ3 ∉ A i₁ j₁ := fun hm =>
    hnoNeg _ hm (by rw [neg_neg, hset1]
                    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                      (Finset.mem_singleton_self _)))
  rw [if_neg hp1] at hO2
  rw [if_neg hp2] at hO3
  rw [if_neg hp3] at hO4
  -- Atomise the indicators and finish by parity (sum of the three `O`s is `odd = even`).
  set n1 := (if χ1 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set n2 := (if χ2 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set n3 := (if χ3 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set n4 := (if χ4 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set n5 := (if χ5 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set n6 := (if χ6 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set p4 := (if -χ4 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set p5 := (if -χ5 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set p6 := (if -χ6 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  omega

/- Helper layer for Case I (3.5.4.1)-(3.5.4.5): the `L`/`O` relations as membership deductions. -/

/-- For two `L`-linked cells, no member of one is the negative of a member of the other (the
`noNeg_L` field, read symmetrically). -/
theorem ne_neg_of_Llinked (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ}
    (h : (i = i' ∧ j ≠ j') ∨ (i ≠ i' ∧ j = j')) {x y : ClassFunction G ℂ}
    (hx : x ∈ A i j) (hy : y ∈ A i' j') : x ≠ -y := by
  have hsymm : (i' = i ∧ j' ≠ j) ∨ (i' ≠ i ∧ j' = j) := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h1.symm, h2.symm⟩
  intro hxy
  exact hG.noNeg_L i' i j' j hsymm y hy (hxy ▸ hx)

/-- For two `L`-linked cells sharing the element `z`, any common element equals `z`
(`|A ∩ A'| = 1`). -/
theorem eq_of_mem_Llinked (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ}
    (h : (i = i' ∧ j ≠ j') ∨ (i ≠ i' ∧ j = j')) {z w : ClassFunction G ℂ}
    (hz : z ∈ A i j) (hz' : z ∈ A i' j') (hw : w ∈ A i j) (hw' : w ∈ A i' j') : w = z := by
  classical
  have hcard := hG.inter_L i i' j j' h
  exact Finset.card_le_one.mp (le_of_eq hcard) w (Finset.mem_inter.mpr ⟨hw, hw'⟩) z
    (Finset.mem_inter.mpr ⟨hz, hz'⟩)

open scoped Classical in
/-- **(3.5.4) `L`-step**: if `B = A i j` and `A i' j' = {χ, u, v}` are `L`-linked cells with
`χ ∈ B` (so `χ` is *the* shared element), then `u, v ∉ B`, and none of `χ, u, v` has its negative
in `B`. -/
theorem lStep (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ}
    (h : (i = i' ∧ j ≠ j') ∨ (i ≠ i' ∧ j = j')) {χ u v : ClassFunction G ℂ}
    (hC : A i' j' = {χ, u, v}) (hχu : χ ≠ u) (hχv : χ ≠ v) (_huv : u ≠ v)
    (hχB : χ ∈ A i j) :
    u ∉ A i j ∧ v ∉ A i j ∧ -χ ∉ A i j ∧ -u ∉ A i j ∧ -v ∉ A i j := by
  have hsymm : (i' = i ∧ j' ≠ j) ∨ (i' ≠ i ∧ j' = j) := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h1.symm, h2.symm⟩
  have hχC : χ ∈ A i' j' := by rw [hC]; exact Finset.mem_insert_self _ _
  have huC : u ∈ A i' j' := by
    rw [hC]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hvC : v ∈ A i' j' := by
    rw [hC]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun h' => hχu (eq_of_mem_Llinked hG h hχB hχC h' huC).symm
  · exact fun h' => hχv (eq_of_mem_Llinked hG h hχB hχC h' hvC).symm
  · exact hG.noNeg_L i' i j' j hsymm χ hχC
  · exact hG.noNeg_L i' i j' j hsymm u huC
  · exact hG.noNeg_L i' i j' j hsymm v hvC

open scoped Classical in
/-- **(3.5.4) O-step**: if `B = A i j` and `A i' j' = {χ, u, v}` are `O`-related cells (`i ≠ i'`,
`j ≠ j'`) with `χ ∈ B` and `-χ ∉ B`, then `u, v ∉ B` and *exactly one* of `-u, -v` lies in `B`
(stated as `-u ∈ B ↔ -v ∉ B`).  This is the engine of (3.5.4.1). -/
theorem oStep (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ} (hii : i ≠ i') (hjj : j ≠ j')
    {χ u v : ClassFunction G ℂ} (hC : A i' j' = {χ, u, v})
    (hχu : χ ≠ u) (hχv : χ ≠ v) (huv : u ≠ v)
    (hχB : χ ∈ A i j) (hnegχ : -χ ∉ A i j) :
    u ∉ A i j ∧ v ∉ A i j ∧ (-u ∈ A i j ↔ -v ∉ A i j) := by
  classical
  have hO := hG.inter_O i i' j j' hii hjj
  rw [hC, card_inter_triple _ hχu hχv huv, card_filter_neg_triple _ hχu hχv huv,
    if_pos hχB, if_neg hnegχ] at hO
  set au := (if u ∈ A i j then (1 : ℕ) else 0) with hau
  set av := (if v ∈ A i j then (1 : ℕ) else 0) with hav
  set bu := (if -u ∈ A i j then (1 : ℕ) else 0) with hbu
  set bv := (if -v ∈ A i j then (1 : ℕ) else 0) with hbv
  have hau1 : au ≤ 1 := by rw [hau]; split <;> omega
  have hav1 : av ≤ 1 := by rw [hav]; split <;> omega
  have hbu1 : bu ≤ 1 := by rw [hbu]; split <;> omega
  have hbv1 : bv ≤ 1 := by rw [hbv]; split <;> omega
  have cu : au + bu ≤ 1 := by
    rw [hau, hbu]; by_cases h : u ∈ A i j
    · rw [if_pos h, if_neg (hG.neg_not_mem_self h)]
    · rw [if_neg h]; split <;> omega
  have cv : av + bv ≤ 1 := by
    rw [hav, hbv]; by_cases h : v ∈ A i j
    · rw [if_pos h, if_neg (hG.neg_not_mem_self h)]
    · rw [if_neg h]; split <;> omega
  obtain ⟨hau0, hav0, hsum⟩ : au = 0 ∧ av = 0 ∧ bu + bv = 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro h; rw [hau, if_pos h] at hau0; exact one_ne_zero hau0
  · intro h; rw [hav, if_pos h] at hav0; exact one_ne_zero hav0
  · constructor
    · intro h hnv'; rw [hbu, if_pos h, hbv, if_pos hnv'] at hsum; omega
    · intro h; by_contra h'; rw [hbu, if_neg h', hbv, if_neg h] at hsum; omega

open scoped Classical in
/-- **(3.5.4) O-step (all-out)**: if `B = A i j` and `A i' j' = {x, y, z}` are `O`-related and
none of `x, y, z` lies in `B`, then none of `-x, -y, -z` lies in `B`.  Used with the transversal
cell to kill the negated meet-points at once. -/
theorem oStep_out (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ} (hii : i ≠ i') (hjj : j ≠ j')
    {x y z : ClassFunction G ℂ} (hC : A i' j' = {x, y, z})
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x ∉ A i j) (hy : y ∉ A i j) (hz : z ∉ A i j) :
    -x ∉ A i j ∧ -y ∉ A i j ∧ -z ∉ A i j := by
  classical
  have hO := hG.inter_O i i' j j' hii hjj
  rw [hC, card_inter_triple _ hxy hxz hyz, card_filter_neg_triple _ hxy hxz hyz,
    if_neg hx, if_neg hy, if_neg hz] at hO
  refine ⟨?_, ?_, ?_⟩ <;> intro h
  · rw [if_pos h] at hO; omega
  · rw [if_pos h] at hO; omega
  · rw [if_pos h] at hO; omega

/-- Two members of the *same* cell are never negatives of each other. -/
theorem ne_neg_of_mem_same (hG : IsSignedTripleGrid A) {i : ι} {j : κ}
    {x y : ClassFunction G ℂ} (hx : x ∈ A i j) (hy : y ∈ A i j) : x ≠ -y :=
  fun h => hG.neg_not_mem_self hy (h ▸ hx)

open scoped Classical in
/-- **(3.5.4) O-step (force)**: if `B = A i j` and `A i' j' = {x, y, z}` are `O`-related with
`x, y ∉ B` but `-x ∈ B`, then `z ∈ B` (the lone negated member forces the third one in). -/
theorem oStep_force (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ} (hii : i ≠ i') (hjj : j ≠ j')
    {x y z : ClassFunction G ℂ} (hC : A i' j' = {x, y, z})
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x ∉ A i j) (hy : y ∉ A i j) (hnx : -x ∈ A i j) : z ∈ A i j := by
  classical
  have hO := hG.inter_O i i' j j' hii hjj
  rw [hC, card_inter_triple _ hxy hxz hyz, card_filter_neg_triple _ hxy hxz hyz,
    if_neg hx, if_neg hy, if_pos hnx] at hO
  by_contra hz
  rw [if_neg hz] at hO; omega

open scoped Classical in
/-- **(3.5.4) O-step (both-out)**: if `B = A i j` and `A i' j' = {x, y, z}` are `O`-related with
`x, y ∉ B` and `-x, -y ∉ B`, then neither `z` nor `-z` lies in `B`.  (The O-relation reduces to
`[z ∈ B] = [-z ∈ B]`, impossible for a `1` and forced `0` for a `0`.)  Yields newness of the
"third element" against a whole cell at once. -/
theorem oStep_both_out (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ}
    (hii : i ≠ i') (hjj : j ≠ j') {x y z : ClassFunction G ℂ} (hC : A i' j' = {x, y, z})
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x ∉ A i j) (hy : y ∉ A i j) (hnx : -x ∉ A i j) (hny : -y ∉ A i j) :
    z ∉ A i j ∧ -z ∉ A i j := by
  classical
  have hO := hG.inter_O i i' j j' hii hjj
  rw [hC, card_inter_triple _ hxy hxz hyz, card_filter_neg_triple _ hxy hxz hyz,
    if_neg hx, if_neg hy, if_neg hnx, if_neg hny] at hO
  refine ⟨?_, ?_⟩
  · intro hz; rw [if_pos hz, if_neg (hG.neg_not_mem_self hz)] at hO; omega
  · intro hnz
    rw [if_neg (fun hz => hG.neg_not_mem_self hz hnz), if_pos hnz] at hO; omega

open scoped Classical in
/-- **(3.5.4.1) pencil cell**: in the Case-I configuration, three pencil rows `ra, rb, rc` share
the apex `χ` (so `A ra j₀ = {χ, ma, fa}`, etc.) and a transversal row `rt` meets them at the
"meet-points" (`A rt j₀ = {ma, mb, mc}`).  If `χ ∈ A ra j₁` for a second column `j₁`, then the
whole cell is `A ra j₁ = {χ, -fb, -fc}` — the apex together with the *negated free-points* of the
other two pencil rows.  (Peterfalvi: `χ₁ ∈ A₁₂ ⟹ β₁₂ = χ₁ - χ₅ - χ₇`.)  The proof: `L(ra j₁, ra j₀)`
removes `ma, fa`; `O` against `Lb`, `Lc` forces "exactly one of the two negated others"; and the
`O` against the transversal `T` kills both negated meet-points at once, leaving the free ones. -/
theorem pencilCell (hG : IsSignedTripleGrid A) {ra rb rc rt : ι} {j₀ j₁ : κ}
    (hab : ra ≠ rb) (hac : ra ≠ rc) (hat : ra ≠ rt) (hbc : rb ≠ rc) (hj : j₀ ≠ j₁)
    {χ ma mb mc fa fb fc : ClassFunction G ℂ}
    (hLa : A ra j₀ = {χ, ma, fa}) (hLb : A rb j₀ = {χ, mb, fb})
    (hLc : A rc j₀ = {χ, mc, fc}) (hT : A rt j₀ = {ma, mb, mc})
    (hχB : χ ∈ A ra j₁) :
    A ra j₁ = {χ, -fb, -fc} := by
  classical
  obtain ⟨dχma, dχfa, dmafa⟩ := triple_distinct (hLa ▸ hG.card_eq_three ra j₀)
  obtain ⟨dχmb, dχfb, dmbfb⟩ := triple_distinct (hLb ▸ hG.card_eq_three rb j₀)
  obtain ⟨dχmc, dχfc, dmcfc⟩ := triple_distinct (hLc ▸ hG.card_eq_three rc j₀)
  obtain ⟨dmamb, dmamc, dmbmc⟩ := triple_distinct (hT ▸ hG.card_eq_three rt j₀)
  -- Step 1: `L(ra j₁, ra j₀)` — `χ` is the unique shared element; `ma, fa ∉ B`, `-χ ∉ B`.
  obtain ⟨hmaB, hfaB, hnegχB, _, _⟩ :=
    lStep hG (Or.inl ⟨rfl, hj.symm⟩) hLa dχma dχfa dmafa hχB
  -- Step 2/3: `O` against the other two pencil rows.
  obtain ⟨hmbB, _, hxorb⟩ := oStep hG hab hj.symm hLb dχmb dχfb dmbfb hχB hnegχB
  obtain ⟨hmcB, _, hxorc⟩ := oStep hG hac hj.symm hLc dχmc dχfc dmcfc hχB hnegχB
  -- Step 4: `O` against the transversal — `ma, mb, mc ∉ B`, so `-mb, -mc ∉ B`.
  obtain ⟨_, hnegmbB, hnegmcB⟩ :=
    oStep_out hG hat hj.symm hT dmamb dmamc dmbmc hmaB hmbB hmcB
  -- Step 5: hence `-fb, -fc ∈ B`.
  have hnegfbB : -fb ∈ A ra j₁ := not_not.mp (fun h => hnegmbB (hxorb.mpr h))
  have hnegfcB : -fc ∈ A ra j₁ := not_not.mp (fun h => hnegmcB (hxorc.mpr h))
  -- Distinctness for the final triple.
  have hχLa : χ ∈ A ra j₀ := by rw [hLa]; exact Finset.mem_insert_self _ _
  have hχLb : χ ∈ A rb j₀ := by rw [hLb]; exact Finset.mem_insert_self _ _
  have hχLc : χ ∈ A rc j₀ := by rw [hLc]; exact Finset.mem_insert_self _ _
  have hfbLb : fb ∈ A rb j₀ := by
    rw [hLb]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hfcLc : fc ∈ A rc j₀ := by
    rw [hLc]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have dχnfb : χ ≠ -fb := ne_neg_of_Llinked hG (Or.inr ⟨hab, rfl⟩) hχLa hfbLb
  have dχnfc : χ ≠ -fc := ne_neg_of_Llinked hG (Or.inr ⟨hac, rfl⟩) hχLa hfcLc
  have dnfbnfc : (-fb) ≠ -fc := by
    intro h
    exact dχfb (eq_of_mem_Llinked hG (Or.inr ⟨hbc, rfl⟩) hχLb hχLc hfbLb
      (neg_injective h ▸ hfcLc)).symm
  -- Conclude `B = {χ, -fb, -fc}` by cardinality.
  have hsub : ({χ, -fb, -fc} : Finset (ClassFunction G ℂ)) ⊆ A ra j₁ := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hχB
    · exact hnegfbB
    · exact hnegfcB
  have hcard3 : ({χ, -fb, -fc} : Finset (ClassFunction G ℂ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [dχnfb, dχnfc]),
      Finset.card_insert_of_notMem (by simp [dnfbnfc]), Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsub
    (le_of_eq (by rw [hG.card_eq_three ra j₁, hcard3]))).symm

open scoped Classical in
/-- **(3.5.4.2) transversal cell**: if the transversal row `rt`'s second-column cell shares the
meet-point `ma` (`= χ₂`) with its first-column cell `{ma, mb, mc}`, then `A rt j₁ = {ma, -fa, χ8}`
for a *new* element `χ8` (Peterfalvi `β₃₂ = χ₂ - χ₃ + χ₈`), distinct from the apex `χ` and from the
meets/frees `±mb, ±mc, fb, fc` of the other two pencil rows.  The shared half is an `L`-step; that
`-fa ∈ B` (rather than `-χ`) comes from excluding `-χ ∈ B`, which would force both free-points
`fb, fc ∈ B` (one O-step each), but `B` has room for only one element besides `ma, -χ`.  Newness of
`χ8` falls out of `oStep_both_out` against the two pencil cells. -/
theorem transversalCell (hG : IsSignedTripleGrid A) {ra rb rc rt : ι} {j₀ j₁ : κ}
    (hab : ra ≠ rb) (hac : ra ≠ rc) (hbc : rb ≠ rc)
    (hat : ra ≠ rt) (hbt : rb ≠ rt) (hct : rc ≠ rt) (hj : j₀ ≠ j₁)
    {χ ma mb mc fa fb fc : ClassFunction G ℂ}
    (hLa : A ra j₀ = {χ, ma, fa}) (hLb : A rb j₀ = {χ, mb, fb})
    (hLc : A rc j₀ = {χ, mc, fc}) (hT : A rt j₀ = {ma, mb, mc})
    (hmaB : ma ∈ A rt j₁) :
    ∃ χ8, A rt j₁ = {ma, -fa, χ8} ∧
      χ8 ≠ χ ∧ χ8 ≠ fb ∧ χ8 ≠ fc ∧ χ8 ≠ -fb ∧ χ8 ≠ -fc ∧ χ8 ≠ -mb ∧ χ8 ≠ -mc := by
  classical
  obtain ⟨_, _, dmafa⟩ := triple_distinct (hLa ▸ hG.card_eq_three ra j₀)
  obtain ⟨dχma, dχfa, _⟩ := triple_distinct (hLa ▸ hG.card_eq_three ra j₀)
  obtain ⟨dχmb, dχfb, dmbfb⟩ := triple_distinct (hLb ▸ hG.card_eq_three rb j₀)
  obtain ⟨dχmc, dχfc, dmcfc⟩ := triple_distinct (hLc ▸ hG.card_eq_three rc j₀)
  obtain ⟨dmamb, dmamc, dmbmc⟩ := triple_distinct (hT ▸ hG.card_eq_three rt j₀)
  -- column-`j₀` memberships
  have hχLa : χ ∈ A ra j₀ := by rw [hLa]; exact Finset.mem_insert_self _ _
  have hmaLa : ma ∈ A ra j₀ := by
    rw [hLa]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hfaLa : fa ∈ A ra j₀ := by
    rw [hLa]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hχLb : χ ∈ A rb j₀ := by rw [hLb]; exact Finset.mem_insert_self _ _
  have hmbLb : mb ∈ A rb j₀ := by
    rw [hLb]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hfbLb : fb ∈ A rb j₀ := by
    rw [hLb]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hχLc : χ ∈ A rc j₀ := by rw [hLc]; exact Finset.mem_insert_self _ _
  have hmcLc : mc ∈ A rc j₀ := by
    rw [hLc]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hfcLc : fc ∈ A rc j₀ := by
    rw [hLc]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hmaT : ma ∈ A rt j₀ := by rw [hT]; exact Finset.mem_insert_self _ _
  have hmbT : mb ∈ A rt j₀ := by
    rw [hT]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hmcT : mc ∈ A rt j₀ := by
    rw [hT]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  -- Step 1: `L(rt j₁, rt j₀)`, shared element `ma`.
  obtain ⟨hmb_nB, hmc_nB, hnegma_nB, hnegmb_nB, hnegmc_nB⟩ :=
    lStep hG (Or.inl ⟨rfl, hj.symm⟩) hT dmamb dmamc dmbmc hmaB
  -- Step 2: `O(rt j₁, ra j₀)`, reorder to `{ma, χ, fa}`.
  have hLa' : A ra j₀ = {ma, χ, fa} := by rw [hLa, Finset.insert_comm]
  obtain ⟨hχ_nB, _hfa_nB, hxor⟩ :=
    oStep hG hat.symm hj.symm hLa' dχma.symm dmafa dχfa hmaB hnegma_nB
  -- Step 3: exclude `-χ ∈ B`, hence `-fa ∈ B`.
  have hnegχ_nB : -χ ∉ A rt j₁ := by
    intro hnegχ
    have hfbB : fb ∈ A rt j₁ := oStep_force hG hbt.symm hj.symm hLb dχmb dχfb dmbfb hχ_nB hmb_nB hnegχ
    have hfcB : fc ∈ A rt j₁ := oStep_force hG hct.symm hj.symm hLc dχmc dχfc dmcfc hχ_nB hmc_nB hnegχ
    have hmanegχ : ma ≠ -χ := ne_neg_of_mem_same hG hmaLa hχLa
    obtain ⟨t, _, _, _, hBset⟩ :=
      exists_third_of_card_three (hG.card_eq_three rt j₁) hmaB hnegχ hmanegχ
    have hfbma : fb ≠ ma := fun h => dmbfb
      (eq_of_mem_Llinked hG (Or.inr ⟨hbt, rfl⟩) hmbLb hmbT hfbLb (by rw [h]; exact hmaT)).symm
    have hfcma : fc ≠ ma := fun h => dmcfc
      (eq_of_mem_Llinked hG (Or.inr ⟨hct, rfl⟩) hmcLc hmcT hfcLc (by rw [h]; exact hmaT)).symm
    have hfbnegχ : fb ≠ -χ := ne_neg_of_mem_same hG hfbLb hχLb
    have hfcnegχ : fc ≠ -χ := ne_neg_of_mem_same hG hfcLc hχLc
    have hfbfc : fb ≠ fc := fun h => dχfb
      (eq_of_mem_Llinked hG (Or.inr ⟨hbc, rfl⟩) hχLb hχLc hfbLb (by rw [h]; exact hfcLc)).symm
    have hfbt : fb = t := by
      have := hBset ▸ hfbB
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h
      · exact absurd h hfbma
      · exact absurd h hfbnegχ
      · exact h
    have hfct : fc = t := by
      have := hBset ▸ hfcB
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h
      · exact absurd h hfcma
      · exact absurd h hfcnegχ
      · exact h
    exact hfbfc (hfbt.trans hfct.symm)
  have hnegfaB : -fa ∈ A rt j₁ := not_not.mp (fun h => hnegχ_nB (hxor.mpr h))
  -- Step 4: name the third element `χ8`.
  have hmanegfa : ma ≠ -fa := ne_neg_of_mem_same hG hmaLa hfaLa
  obtain ⟨χ8, hχ8B, _, _, hBset⟩ :=
    exists_third_of_card_three (hG.card_eq_three rt j₁) hmaB hnegfaB hmanegfa
  -- Newness of `χ8`.
  obtain ⟨hfb_nB, hnegfb_nB⟩ :=
    oStep_both_out hG hbt.symm hj.symm hLb dχmb dχfb dmbfb hχ_nB hmb_nB hnegχ_nB hnegmb_nB
  obtain ⟨hfc_nB, hnegfc_nB⟩ :=
    oStep_both_out hG hct.symm hj.symm hLc dχmc dχfc dmcfc hχ_nB hmc_nB hnegχ_nB hnegmc_nB
  exact ⟨χ8, hBset, fun h => hχ_nB (h ▸ hχ8B), fun h => hfb_nB (h ▸ hχ8B),
    fun h => hfc_nB (h ▸ hχ8B), fun h => hnegfb_nB (h ▸ hχ8B), fun h => hnegfc_nB (h ▸ hχ8B),
    fun h => hnegmb_nB (h ▸ hχ8B), fun h => hnegmc_nB (h ▸ hχ8B)⟩

end IsSignedTripleGrid

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

/- 3.5.1 (cont.) / 3.5.2: the fixed family of signed triples `A_{ij}` -/

/-- **Peterfalvi (3.5.1)**, family form: a fixed choice of signed-triple set `A_{ij}` for each
`β_{ij}` (`i, j ≥ 1`), indexed by pairs of nontrivial linear characters of `W₁`, `W₂`.  This is
the family the `(3.5.4)`-`(3.5.5)` combinatorics reason about. -/
noncomputable def Afam (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    (p : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1})
    (q : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) : Finset (ClassFunction G ℂ) :=
  (hyp.exists_isSignedTriple_beta hVeq app p.2 q.2).choose

/-- `A_{ij}` is a signed triple for `β_{ij}`. -/
theorem Afam_isSignedTriple (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    (p : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1})
    (q : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) :
    IsSignedTriple (hyp.beta hVeq app p.1 q.1) (hyp.Afam hVeq app p q) :=
  (hyp.exists_isSignedTriple_beta hVeq app p.2 q.2).choose_spec

open Classical in
/-- **Peterfalvi (3.5.2)** `L(ij, i'j')`, family form: `A_{ij}` and `A_{i'j'}` with index pairs
sharing exactly one coordinate intersect in one element, with no negated common element. -/
theorem Afam_L (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {p p' : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}}
    {q q' : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}}
    (hshared : (p = p' ∧ q ≠ q') ∨ (p ≠ p' ∧ q = q')) :
    (hyp.Afam hVeq app p q ∩ hyp.Afam hVeq app p' q').card = 1 ∧
      ∀ x ∈ hyp.Afam hVeq app p q, -x ∉ hyp.Afam hVeq app p' q' := by
  refine (hyp.Afam_isSignedTriple hVeq app p q).L_of_inner_one
    (hyp.Afam_isSignedTriple hVeq app p' q') ?_ ?_
  · apply hyp.beta_inner_eq_one_of_one_shared hVeq app p.2 q.2 p'.2 q'.2
    rcases hshared with ⟨rfl, hq⟩ | ⟨hp, rfl⟩
    · exact Or.inl ⟨rfl, fun h => hq (Subtype.ext h)⟩
    · exact Or.inr ⟨fun h => hp (Subtype.ext h), rfl⟩
  · rw [hyp.beta_apply_one, hyp.beta_apply_one]

open Classical in
/-- **Peterfalvi (3.5.2)** `O(ij, i'j')`, family form: `A_{ij}` and `A_{i'j'}` with both indices
different satisfy `|A_{ij} ∩ A_{i'j'}| = |{x ∈ A_{ij} : -x ∈ A_{i'j'}}|`. -/
theorem Afam_O (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {p p' : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}}
    {q q' : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}}
    (hp : p ≠ p') (hq : q ≠ q') :
    (hyp.Afam hVeq app p q ∩ hyp.Afam hVeq app p' q').card =
      ((hyp.Afam hVeq app p q).filter (fun x => -x ∈ hyp.Afam hVeq app p' q')).card :=
  (hyp.Afam_isSignedTriple hVeq app p q).O_card_inter_eq (hyp.Afam_isSignedTriple hVeq app p' q')
    (hyp.beta_inner_eq_zero_of_both_diff hVeq app p.2 q.2 p'.2 q'.2
      (fun h => hp (Subtype.ext h)) (fun h => hq (Subtype.ext h)))

/-- The fixed family `Afam` is a signed-triple grid (`IsSignedTripleGrid`), indexed by nontrivial
linear characters of `W₁` (rows) and `W₂` (columns).  Bundles `Afam_isSignedTriple`/`Afam_L`/
`Afam_O` so the abstract (3.5.4) sunflower argument applies to the `β`-family. -/
theorem Afam_isSignedTripleGrid (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp) :
    IsSignedTripleGrid (fun (p : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1})
      (q : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) => hyp.Afam hVeq app p q) where
  card_eq_three p q := (hyp.Afam_isSignedTriple hVeq app p q).card_eq_three
  signed p q := (hyp.Afam_isSignedTriple hVeq app p q).signed
  orthogonal p q := (hyp.Afam_isSignedTriple hVeq app p q).pairwise_orthogonal
  inter_L _ _ _ _ hshared := (hyp.Afam_L hVeq app hshared).1
  noNeg_L _ _ _ _ hshared := (hyp.Afam_L hVeq app hshared).2
  inter_O _ _ _ _ hp hq := hyp.Afam_O hVeq app hp hq

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05
