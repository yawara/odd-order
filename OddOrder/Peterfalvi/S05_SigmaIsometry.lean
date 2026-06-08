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

namespace TICyclicHypothesis

/- 3.5.1 (cont.): the virtual characters `β_{ij} = Ind_W^G α_{ij} - 1_G` -/

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

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05
