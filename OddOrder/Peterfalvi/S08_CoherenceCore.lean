/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_RestrictExtensionDvd

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S08_CoherenceCore` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S08
open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis
variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]


/-- **(6.8.1) step-5 dichotomy** at the fixed witnesses (specialization of
`extension_eq_or_eq_neg_general`). -/
theorem extension_eq_or_eq_neg_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁
        = (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ₁
      ∨ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁
        = -(hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ₂ :=
  hyp.extension_eq_or_eq_neg_general hF
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁ hχ₂ hne ha hdeg2 hgood

/-- **(6.8.1) step-5 dichotomy** at the fixed witnesses, case (A) / c2 mirror of
`extension_eq_or_eq_neg_of_frobenius` (the `X`-coherence is
`Xset_centralCommutator_isCoherent_of_c2_caseA`; cert data `hK`/`hW1`/`hA`). -/
theorem extension_eq_or_eq_neg_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁
        = (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension χ₁
      ∨ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • hyp.coherentYset.extension η₁
        = -(hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension χ₂ :=
  hyp.extension_eq_or_eq_neg_general_c2_caseA hK hW1 hA
    (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁ hχ₂ hne ha hdeg2 hgood

open scoped Classical in
/-- **(6.8.1) crux `hDτ` (`n ≥ 3` case)** (mmd 04.8 L176).  Given a third equal-degree `X`-anchor
`χ₃` (distinct from `χ₁, χ₂`), the good-case crux holds:
`(χ₁−aη₁)^τ = χ₁^{τ₂} − a·η₁^{τ₁}`.

The step-5 dichotomy gives `X := (χ₁−aη₁)^τ + a·η₁^{τ₁} = χ₁^{τ₂} ∨ X = −χ₂^{τ₂}`; the second
disjunct is excluded by the step-5 relation for `χ₃` (`⟨X,χ₃^{τ₂}⟩ − ⟨X,χ₁^{τ₂}⟩ = −1`,
`inner_extension_Xset_sub_eq_neg_one`): under `X = −χ₂^{τ₂}` both `⟨χ₂^{τ₂},χ₃^{τ₂}⟩` and
`⟨χ₂^{τ₂},χ₁^{τ₂}⟩` vanish (distinct `X`-images), giving `0 = −1`.  Hence `X = χ₁^{τ₂}`, i.e. the
crux.  (The `n = 2` case — no third anchor — needs the relabel of `χ₁^{τ₂}, χ₂^{τ₂}`, deferred.) -/
theorem crux_of_third_anchor_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  set hXc := cX with hXc_def
  -- `X`-image orthonormality.
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (hXc.extension ψ) (hXc.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [hXc.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rcases hyp.extension_eq_or_eq_neg_general hF cX cY hη₁ hχ₁ hχ₂ hne₂ ha hdeg2
    hgood with h | h
  · -- left disjunct `X = χ₁^{τ₂}` ⟹ the crux by `eq_sub_of_add_eq`.
    rw [← hXc_def] at h
    exact eq_sub_of_add_eq h
  · -- right disjunct `X = −χ₂^{τ₂}` is excluded by the `χ₃` relation.
    exfalso
    rw [← hXc_def] at h
    have hrel3 := hyp.inner_extension_Xset_sub_eq_neg_one_general hF cX cY
      hη₁ hχ₁ hχ₃ hne₃₁ ha hdeg3
    rw [← hXc_def, h, ClassFunction.inner_neg_left, ClassFunction.inner_neg_left,
      hXon χ₂ χ₃ hχ₂ hχ₃, if_neg (Ne.symm hne₃₂), hXon χ₂ χ₁ hχ₂ hχ₁, if_neg hne₂] at hrel3
    norm_num at hrel3

open scoped Classical in
/-- **(6.8.1) crux `hDτ` (`n ≥ 3` case)**, case (A) / c2 mirror of `crux_of_third_anchor_general`.
The dichotomy/relation/`X`-irreducibility inputs use their case-(A) counterparts
(`extension_eq_or_eq_neg_general_c2_caseA`, `inner_extension_Xset_sub_eq_neg_one_general_c2_caseA`,
`isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem crux_of_third_anchor_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  set hXc := cX with hXc_def
  -- `X`-image orthonormality.
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (hXc.extension ψ) (hXc.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [hXc.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rcases hyp.extension_eq_or_eq_neg_general_c2_caseA hK hW1 hA cX cY hη₁ hχ₁ hχ₂ hne₂ ha hdeg2
    hgood with h | h
  · -- left disjunct `X = χ₁^{τ₂}` ⟹ the crux by `eq_sub_of_add_eq`.
    rw [← hXc_def] at h
    exact eq_sub_of_add_eq h
  · -- right disjunct `X = −χ₂^{τ₂}` is excluded by the `χ₃` relation.
    exfalso
    rw [← hXc_def] at h
    have hrel3 := hyp.inner_extension_Xset_sub_eq_neg_one_general_c2_caseA hK hW1 hA cX cY
      hη₁ hχ₁ hχ₃ hne₃₁ ha hdeg3
    rw [← hXc_def, h, ClassFunction.inner_neg_left, ClassFunction.inner_neg_left,
      hXon χ₂ χ₃ hχ₂ hχ₃, if_neg (Ne.symm hne₃₂), hXon χ₂ χ₁ hχ₂ hχ₁, if_neg hne₂] at hrel3
    norm_num at hrel3

/-- **(6.8.1) crux (`n ≥ 3` case)** at the fixed witnesses (specialization of
`crux_of_third_anchor_general`). -/
theorem crux_of_third_anchor_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁)
      = (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ₁
        - (a : ℂ) • hyp.coherentYset.extension η₁ :=
  hyp.crux_of_third_anchor_general hF
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁ hχ₂ hne₂ hχ₃ hne₃₁ hne₃₂ ha hdeg2 hdeg3 hgood

/-- **(6.8.1) crux (`n ≥ 3` case)** at the fixed witnesses, case (A) / c2 mirror of
`crux_of_third_anchor_of_frobenius` (the `X`-coherence is
`Xset_centralCommutator_isCoherent_of_c2_caseA`; cert data `hK`/`hW1`/`hA`). -/
theorem crux_of_third_anchor_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁)
      = (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension χ₁
        - (a : ℂ) • hyp.coherentYset.extension η₁ :=
  hyp.crux_of_third_anchor_general_c2_caseA hK hW1 hA
    (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁ hχ₂ hne₂ hχ₃ hne₃₁ hne₃₂ ha hdeg2 hdeg3 hgood

open scoped Classical in
/-- For `m = |Y| ≥ 3` the step-4 edge case (`m = 2`) is impossible, so the good case
`⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = −a` of `coeff_eq_neg_or_edge_of_frobenius` holds (no relabel needed). -/
theorem inner_tau_scaledDiff_extension_Yset_eq_neg_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hm3 : 3 ≤ hyp.Yset.ncard) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = -(a : ℂ) := by
  have ha_pos : 0 < a := by
    have := hyp.two_le_degreeRatio_of_mem_Xset_of_frobenius hχ₁ ha; omega
  rcases hyp.coeff_eq_neg_or_edge_of_frobenius hF hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos ha with
    h | ⟨hm2, _⟩
  · exact h
  · exfalso; omega

/-- case (A) / c2 mirror of `inner_tau_scaledDiff_extension_Yset_eq_neg_of_frobenius`.  The step-4
dichotomy input uses `coeff_eq_neg_or_edge_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem inner_tau_scaledDiff_extension_Yset_eq_neg_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hm3 : 3 ≤ hyp.Yset.ncard) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = -(a : ℂ) := by
  have ha_pos : 0 < a := by
    have := hyp.two_le_degreeRatio_of_mem_Xset_of_frobenius hχ₁ ha; omega
  rcases hyp.coeff_eq_neg_or_edge_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos ha with
    h | ⟨hm2, _⟩
  · exact h
  · exfalso; omega

open scoped Classical in
/-- **(6.8.1) crux `hDτ` (generic `m, n ≥ 3` case)** (mmd 04.8 L176).  When `|Y| ≥ 3` (so the step-4
edge `m = 2` is impossible, discharging the good case) and a third equal-degree `X`-anchor `χ₃`
exists (the `n ≥ 3` pinning), the crux `(χ₁−aη₁)^τ = χ₁^{τ₂} − a·η₁^{τ₁}` holds **unconditionally**
(no relabel).  This is the diagonal-shell hypothesis `hDτ` in the generic case. -/
theorem crux_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1)
    (hm3 : 3 ≤ hyp.Yset.ncard) :
    hyp.tau (χ₁ - a • η₁)
      = (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ₁
        - (a : ℂ) • hyp.coherentYset.extension η₁ :=
  hyp.crux_of_third_anchor_of_frobenius hF hHnonab hp hp3 hHp hη₁ hχ₁ hχ₂ hne₂ hχ₃ hne₃₁ hne₃₂
    ha hdeg2 hdeg3
    (hyp.inner_tau_scaledDiff_extension_Yset_eq_neg_of_frobenius hF hHnonab hp hp3 hHp hη₁ hχ₁ ha
      hm3)

open scoped Classical in
/-- **(6.8.1) crux `hDτ` (generic `m, n ≥ 3` case)**, case (A) / c2 mirror of `crux_of_frobenius`.
Delegates to `crux_of_third_anchor_c2_caseA` with the good case from
`inner_tau_scaledDiff_extension_Yset_eq_neg_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem crux_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1)
    (hm3 : 3 ≤ hyp.Yset.ncard) :
    hyp.tau (χ₁ - a • η₁)
      = (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension χ₁
        - (a : ℂ) • hyp.coherentYset.extension η₁ :=
  hyp.crux_of_third_anchor_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη₁ hχ₁ hχ₂ hne₂ hχ₃ hne₃₁ hne₃₂
    ha hdeg2 hdeg3
    (hyp.inner_tau_scaledDiff_extension_Yset_eq_neg_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη₁ hχ₁ ha
      hm3)

open scoped Classical in
/-- **(6.8.1) `hgen'` — the diagonal-aware generation hypothesis** (mmd 04.8 L176).  Every supported
`X(Zc) ∪ Y`-combination lies in the span of the supported `X(Zc)`-combinations, the supported
`Y`-combinations, and the single cross-diagonal `χ₁ − a·η₁`:
`ℤ[X(Zc) ∪ Y, A] ⊆ span(ℤ[X(Zc), A] ∪ ℤ[Y, A] ∪ {χ₁ − a·η₁})`.

For `φ = φ_X + φ_Y` (`X, Y` disjoint, `Submodule.span_union`), the degree-ratio integrality
(`exists_charValue_one_eq_mul_xBaseBlock_anchor`) gives `s ∈ ℤ` with `φ_X(1) = s·χ₁(1)` (span
induction); then `φ = (φ_X − s·χ₁) + (φ_Y + s·(a·η₁)) + s·(χ₁ − a·η₁)`, where the first two pieces
are degree-`0` (`φ(1) = 0` from support) hence supported
(`zSpan_S_support_subset_of_apply_one_eq_zero`) and the last is a multiple of the diagonal.  This is
the `hgen` field of `coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_frobenius` with
`D = {χ₁ − a·η₁}`. -/
theorem hgen_withDiagonal_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
      Submodule.span ℤ
        (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset hyp.centralCommutator)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
        OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
        {χ₁ - a • η₁}) := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  intro φ hφ
  obtain ⟨hφspan, hφsupp⟩ := hφ
  -- `φ(1) = 0`: `1 ∉ A = H^#`.
  have h1 : φ 1 = 0 := by
    by_contra h
    have hmem := hφsupp (ClassFunction.mem_support.mpr h)
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hmem
    simp only [sharpImage, Set.mem_sdiff, Set.mem_singleton_iff] at hmem
    exact hmem.2 (by simp)
  -- split `φ = φ_X + φ_Y`.
  rw [OddOrder.Peterfalvi.S07.zSpan, Submodule.span_union] at hφspan
  obtain ⟨φX, hφX, φY, hφY, hsum⟩ := Submodule.mem_sup.mp hφspan
  -- the integer `s` with `φ_X(1) = s·χ₁(1)` (span induction + degree-ratio integrality).
  have hsX : ∀ ψ ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator),
      ∃ s : ℤ, ψ 1 = (s : ℂ) * χ₁ 1 := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨d, -, hd⟩ := hyp.exists_charValue_one_eq_mul_xBaseBlock_anchor_of_irreducible_X
          hp hHp (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hx hχ₁base
        exact ⟨d, by rw [hd]; push_cast; ring⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
        obtain ⟨sx, hsx⟩ := hx; obtain ⟨sy, hsy⟩ := hy
        exact ⟨sx + sy, by rw [ClassFunction.add_apply, hsx, hsy]; push_cast; ring⟩
    | smul c x _ hx =>
        obtain ⟨sx, hsx⟩ := hx
        refine ⟨c * sx, ?_⟩
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hsx]; push_cast; ring
  obtain ⟨s, hφX1⟩ := hsX φX hφX
  -- `φ_Y(1) = −s·χ₁(1)`.
  have hφY1 : φY 1 = -((s : ℂ) * χ₁ 1) := by
    have haux : φX 1 + φY 1 = 0 := by
      have hc := congrArg (fun ψ : ClassFunction ↥L ℂ => ψ 1) hsum
      simpa [ClassFunction.add_apply, h1] using hc
    linear_combination haux - hφX1
  -- the smul degrees.
  have hsχ₁1 : (s • χ₁ : ClassFunction ↥L ℂ) 1 = (s : ℂ) * χ₁ 1 := by
    rw [← Int.cast_smul_eq_zsmul ℂ s χ₁, ClassFunction.smul_apply]
  have hsaη₁1 : (s • (a • η₁) : ClassFunction ↥L ℂ) 1 = (s : ℂ) * ((a : ℂ) * η₁ 1) := by
    rw [← Int.cast_smul_eq_zsmul ℂ s (a • η₁), ClassFunction.smul_apply,
      ← Nat.cast_smul_eq_nsmul ℂ a η₁, ClassFunction.smul_apply]
  -- the three pieces are degree 0 (for the supported ones) and span-members.
  have hp1deg : (φX - s • χ₁ : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.sub_apply, hφX1, hsχ₁1]; ring
  have hp2deg : (φY + s • (a • η₁) : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.add_apply, hφY1, hsaη₁1, ha, hyp.Yset_apply_one hη₁]; ring
  have hp1span : (φX - s • χ₁) ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) :=
    Submodule.sub_mem _ hφX (Submodule.smul_mem _ s (Submodule.subset_span hχ₁X))
  have hp2span : (φY + s • (a • η₁)) ∈ Submodule.span ℤ hyp.Yset :=
    Submodule.add_mem _ hφY
      (Submodule.smul_mem _ s (nsmul_mem (Submodule.subset_span hη₁) a))
  -- supports via the degree-0 ⟹ supported helper.
  have hp1supp : (φX - s • χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hyp.Xset_subset_S hp1span) hp1deg
  have hp2supp : (φY + s • (a • η₁)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hyp.Yset_subset_S hp2span) hp2deg
  -- assemble `φ = p1 + p2 + p3` (the `s·χ₁`, `s·(a·η₁)` terms cancel).
  have hφeq : φ = (φX - s • χ₁) + (φY + s • (a • η₁)) + s • (χ₁ - a • η₁) := by
    rw [smul_sub, ← hsum]; abel
  rw [hφeq]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_left _ ⟨hp1span, hp1supp⟩))
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_right _ ⟨hp2span, hp2supp⟩))
  · exact Submodule.smul_mem _ s
      (Submodule.subset_span (Set.mem_union_right _ (Set.mem_singleton _)))

open scoped Classical in
/-- **(6.8.1) `hgen'` — the diagonal-aware generation hypothesis**, case (A) / c2 mirror of
`hgen_withDiagonal_of_frobenius`.  `X`-irreducibility comes from the certain-type input
`isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem hgen_withDiagonal_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
      Submodule.span ℤ
        (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset hyp.centralCommutator)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
        OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
        {χ₁ - a • η₁}) := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  intro φ hφ
  obtain ⟨hφspan, hφsupp⟩ := hφ
  -- `φ(1) = 0`: `1 ∉ A = H^#`.
  have h1 : φ 1 = 0 := by
    by_contra h
    have hmem := hφsupp (ClassFunction.mem_support.mpr h)
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hmem
    simp only [sharpImage, Set.mem_sdiff, Set.mem_singleton_iff] at hmem
    exact hmem.2 (by simp)
  -- split `φ = φ_X + φ_Y`.
  rw [OddOrder.Peterfalvi.S07.zSpan, Submodule.span_union] at hφspan
  obtain ⟨φX, hφX, φY, hφY, hsum⟩ := Submodule.mem_sup.mp hφspan
  -- the integer `s` with `φ_X(1) = s·χ₁(1)` (span induction + degree-ratio integrality).
  have hsX : ∀ ψ ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator),
      ∃ s : ℤ, ψ 1 = (s : ℂ) * χ₁ 1 := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨d, -, hd⟩ := hyp.exists_charValue_one_eq_mul_xBaseBlock_anchor_of_irreducible_X
          hp hHp (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h) hx hχ₁base
        exact ⟨d, by rw [hd]; push_cast; ring⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
        obtain ⟨sx, hsx⟩ := hx; obtain ⟨sy, hsy⟩ := hy
        exact ⟨sx + sy, by rw [ClassFunction.add_apply, hsx, hsy]; push_cast; ring⟩
    | smul c x _ hx =>
        obtain ⟨sx, hsx⟩ := hx
        refine ⟨c * sx, ?_⟩
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hsx]; push_cast; ring
  obtain ⟨s, hφX1⟩ := hsX φX hφX
  -- `φ_Y(1) = −s·χ₁(1)`.
  have hφY1 : φY 1 = -((s : ℂ) * χ₁ 1) := by
    have haux : φX 1 + φY 1 = 0 := by
      have hc := congrArg (fun ψ : ClassFunction ↥L ℂ => ψ 1) hsum
      simpa [ClassFunction.add_apply, h1] using hc
    linear_combination haux - hφX1
  -- the smul degrees.
  have hsχ₁1 : (s • χ₁ : ClassFunction ↥L ℂ) 1 = (s : ℂ) * χ₁ 1 := by
    rw [← Int.cast_smul_eq_zsmul ℂ s χ₁, ClassFunction.smul_apply]
  have hsaη₁1 : (s • (a • η₁) : ClassFunction ↥L ℂ) 1 = (s : ℂ) * ((a : ℂ) * η₁ 1) := by
    rw [← Int.cast_smul_eq_zsmul ℂ s (a • η₁), ClassFunction.smul_apply,
      ← Nat.cast_smul_eq_nsmul ℂ a η₁, ClassFunction.smul_apply]
  -- the three pieces are degree 0 (for the supported ones) and span-members.
  have hp1deg : (φX - s • χ₁ : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.sub_apply, hφX1, hsχ₁1]; ring
  have hp2deg : (φY + s • (a • η₁) : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.add_apply, hφY1, hsaη₁1, ha, hyp.Yset_apply_one hη₁]; ring
  have hp1span : (φX - s • χ₁) ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) :=
    Submodule.sub_mem _ hφX (Submodule.smul_mem _ s (Submodule.subset_span hχ₁X))
  have hp2span : (φY + s • (a • η₁)) ∈ Submodule.span ℤ hyp.Yset :=
    Submodule.add_mem _ hφY
      (Submodule.smul_mem _ s (nsmul_mem (Submodule.subset_span hη₁) a))
  -- supports via the degree-0 ⟹ supported helper.
  have hp1supp : (φX - s • χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hyp.Xset_subset_S hp1span) hp1deg
  have hp2supp : (φY + s • (a • η₁)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hyp.Yset_subset_S hp2span) hp2deg
  -- assemble `φ = p1 + p2 + p3` (the `s·χ₁`, `s·(a·η₁)` terms cancel).
  have hφeq : φ = (φX - s • χ₁) + (φY + s • (a • η₁)) + s • (χ₁ - a • η₁) := by
    rw [smul_sub, ← hsum]; abel
  rw [hφeq]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_left _ ⟨hp1span, hp1supp⟩))
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_right _ ⟨hp2span, hp2supp⟩))
  · exact Submodule.smul_mem _ s
      (Submodule.subset_span (Set.mem_union_right _ (Set.mem_singleton _)))

open scoped Classical in
/-- **(6.8.1) `X`-difference isometry, degree-ratio form** (mmd 04.8 L176: the `n ≥ 3` exclusion uses
`(χ₃ − d₃χ₁)^τ` for ANY third `X`-member `χ₃`, of any degree).  For `η₁ ∈ Y`, `χ₁ ∈ X(Zc)` with
`χ₁(1) = a·|W₁|`, and a second member `χ₃ ∈ X(Zc)`, `χ₃ ≠ χ₁`, with degree ratio `d` (`χ₃(1) =
d·χ₁(1)`):  `⟨(χ₁−aη₁)^τ, (χ₃−d·χ₁)^τ⟩ = −d`.  Generalizes
`inner_tau_scaledDiff_tau_Xset_diff_of_frobenius` (the `d = 1` equal-degree case `= −1`); the
supported diff `χ₃ − d·χ₁` is degree-`0` (`sMember_scaledDiffSupport_of_charValue_eq`), so the Dade
isometry reduces to the source `⟨χ₁−aη₁, χ₃−d·χ₁⟩ = −d` (`X`-orthonormality + `X ⊥ Y`). -/
theorem inner_tau_scaledDiff_tau_Xset_scaledDiff_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₃ ≠ χ₁)
    {a d : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hd : χ₃ 1 = (d : ℂ) * χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₃ - d • χ₁)) = -(d : ℂ) := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hdegX : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
  have hsuppX : (χ₁ - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη₁)
      hdegX
  have hsuppX3 : (χ₃ - d • χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₃) (hyp.Xset_subset_S hχ₁) hd
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η₁, χ₃ - d • χ₁} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppX3)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hXirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hXirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hYXz : ∀ ψ ∈ hyp.Xset hyp.centralCommutator, ClassFunction.inner η₁ ψ = 0 := by
    intro ψ hψ
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ η₁,
      inner_eq_zero_of_mem_span_of_disjoint_irreducible (fun φ hφ => hXirr φ hφ)
        (fun φ hφ => hYirr φ hφ) hdisj ψ (Submodule.subset_span hψ) η₁ (Submodule.subset_span hη₁),
      star_zero]
  have e13 : ClassFunction.inner χ₁ χ₃ = 0 := by rw [hXon χ₁ χ₃ hχ₁ hχ₃, if_neg (Ne.symm hne)]
  have e11 : ClassFunction.inner χ₁ χ₁ = 1 := by rw [hXon χ₁ χ₁ hχ₁ hχ₁, if_pos rfl]
  have ey3 : ClassFunction.inner η₁ χ₃ = 0 := hYXz χ₃ hχ₃
  have ey1 : ClassFunction.inner η₁ χ₁ = 0 := hYXz χ₁ hχ₁
  rw [hiso, ← Nat.cast_smul_eq_nsmul ℂ a η₁, ← Nat.cast_smul_eq_nsmul ℂ d χ₁]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    e13, e11, ey3, ey1, star_natCast]
  ring

open scoped Classical in
/-- **(6.8.1) `X`-difference isometry, degree-ratio form**, case (A) / c2 mirror of
`inner_tau_scaledDiff_tau_Xset_scaledDiff_of_frobenius`.  `X`-irreducibility comes from the
certain-type input `isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`)
instead of `hF`. -/
theorem inner_tau_scaledDiff_tau_Xset_scaledDiff_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₃ ≠ χ₁)
    {a d : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hd : χ₃ 1 = (d : ℂ) * χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₃ - d • χ₁)) = -(d : ℂ) := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hdegX : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
  have hsuppX : (χ₁ - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη₁)
      hdegX
  have hsuppX3 : (χ₃ - d • χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₃) (hyp.Xset_subset_S hχ₁) hd
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η₁, χ₃ - d • χ₁} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppX3)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hXirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hXirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hYXz : ∀ ψ ∈ hyp.Xset hyp.centralCommutator, ClassFunction.inner η₁ ψ = 0 := by
    intro ψ hψ
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ η₁,
      inner_eq_zero_of_mem_span_of_disjoint_irreducible (fun φ hφ => hXirr φ hφ)
        (fun φ hφ => hYirr φ hφ) hdisj ψ (Submodule.subset_span hψ) η₁ (Submodule.subset_span hη₁),
      star_zero]
  have e13 : ClassFunction.inner χ₁ χ₃ = 0 := by rw [hXon χ₁ χ₃ hχ₁ hχ₃, if_neg (Ne.symm hne)]
  have e11 : ClassFunction.inner χ₁ χ₁ = 1 := by rw [hXon χ₁ χ₁ hχ₁ hχ₁, if_pos rfl]
  have ey3 : ClassFunction.inner η₁ χ₃ = 0 := hYXz χ₃ hχ₃
  have ey1 : ClassFunction.inner η₁ χ₁ = 0 := hYXz χ₁ hχ₁
  rw [hiso, ← Nat.cast_smul_eq_nsmul ℂ a η₁, ← Nat.cast_smul_eq_nsmul ℂ d χ₁]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    e13, e11, ey3, ey1, star_natCast]
  ring

open scoped Classical in
/-- **(6.8.1) step-5 relation, degree-ratio form.**  For the good-case element
`X := (χ₁−aη₁)^τ + a·η₁^{τ₁}` and a third `X`-member `χ₃` of degree ratio `d` (`χ₃(1) = d·χ₁(1)`):
`⟨X, χ₃^{τ₂}⟩ − d·⟨X, χ₁^{τ₂}⟩ = −d`.  himg_ortho (`η₁^{τ₁} ⊥ X^{τ₂}`) gives `⟨X,·⟩ = ⟨v,·⟩`; the
`X`-coherence `(χ₃−d·χ₁)^τ = χ₃^{τ₂} − d·χ₁^{τ₂}` and the degree-ratio isometry value
`⟨v, (χ₃−d·χ₁)^τ⟩ = −d` close it.  Generalizes `inner_extension_Xset_sub_eq_neg_one_general`
(the `d = 1` case). -/
theorem inner_extension_Xset_scaledSub_eq_neg_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₃ ≠ χ₁)
    {a d : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hd : χ₃ 1 = (d : ℂ) * χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁) (cX.extension χ₃)
      - (d : ℂ) * ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₁) = -(d : ℂ) := by
  classical
  set v := hyp.tau (χ₁ - a • η₁) with hv
  have hXv : ∀ χ ∈ hyp.Xset hyp.centralCommutator,
      ClassFunction.inner (v + (a : ℂ) • cY.extension η₁) (cX.extension χ)
        = ClassFunction.inner v (cX.extension χ) := by
    intro χ hχ
    have h := hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general hF cX cY hχ hη₁
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_conj_symm (cX.extension χ)
        (cY.extension η₁), h, star_zero, mul_zero, add_zero]
  have hsuppX3 : (χ₃ - d • χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₃) (hyp.Xset_subset_S hχ₁) hd
  have hXcoh : hyp.tau (χ₃ - d • χ₁) = cX.extension χ₃ - (d : ℂ) • cX.extension χ₁ := by
    have h := cX.extends_on_supported (χ₃ - d • χ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hχ₃)
        (nsmul_mem (Submodule.subset_span hχ₁) d), hsuppX3⟩
    rw [map_sub, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ d (cX.extension χ₁)] at h
    exact h.symm
  have hiso := hyp.inner_tau_scaledDiff_tau_Xset_scaledDiff_of_frobenius hF hη₁ hχ₁ hχ₃ hne ha hd
  rw [hXcoh, ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
    star_natCast] at hiso
  rw [hXv χ₃ hχ₃, hXv χ₁ hχ₁]
  exact hiso

open scoped Classical in
/-- **(6.8.1) step-5 relation, degree-ratio form**, case (A) / c2 mirror of
`inner_extension_Xset_scaledSub_eq_neg_general`.  The himg_ortho/isometry inputs use their case-(A)
counterparts (`inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA`,
`inner_tau_scaledDiff_tau_Xset_scaledDiff_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem inner_extension_Xset_scaledSub_eq_neg_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₃ ≠ χ₁)
    {a d : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hd : χ₃ 1 = (d : ℂ) * χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁) (cX.extension χ₃)
      - (d : ℂ) * ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₁) = -(d : ℂ) := by
  classical
  set v := hyp.tau (χ₁ - a • η₁) with hv
  have hXv : ∀ χ ∈ hyp.Xset hyp.centralCommutator,
      ClassFunction.inner (v + (a : ℂ) • cY.extension η₁) (cX.extension χ)
        = ClassFunction.inner v (cX.extension χ) := by
    intro χ hχ
    have h := hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA
      hK hW1 hA cX cY hχ hη₁
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_conj_symm (cX.extension χ)
        (cY.extension η₁), h, star_zero, mul_zero, add_zero]
  have hsuppX3 : (χ₃ - d • χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₃) (hyp.Xset_subset_S hχ₁) hd
  have hXcoh : hyp.tau (χ₃ - d • χ₁) = cX.extension χ₃ - (d : ℂ) • cX.extension χ₁ := by
    have h := cX.extends_on_supported (χ₃ - d • χ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hχ₃)
        (nsmul_mem (Submodule.subset_span hχ₁) d), hsuppX3⟩
    rw [map_sub, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ d (cX.extension χ₁)] at h
    exact h.symm
  have hiso := hyp.inner_tau_scaledDiff_tau_Xset_scaledDiff_c2_caseA hK hW1 hA hη₁ hχ₁ hχ₃ hne ha hd
  rw [hXcoh, ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
    star_natCast] at hiso
  rw [hXv χ₃ hχ₃, hXv χ₁ hχ₁]
  exact hiso

open scoped Classical in
/-- **(6.8.1) crux, general witnesses + ANY third anchor (`|X(Zc)| ≥ 3`)** — closes the
`|xBaseBlock| = 2 ∧ |X(Zc)| ≥ 3` gap that the equal-degree `crux_of_third_anchor_general` (which
needs a *third equal-degree* anchor, i.e. `|xBaseBlock| ≥ 3`) cannot reach.  Given the good case
`⟨(χ₁−aη₁)^τ, cY η₁⟩ = −a`, the dichotomy `X = cX χ₁ ∨ X = −cX χ₂` (equal-degree `χ₂`); the right
disjunct is excluded by ANY third `X`-member `χ₃` (any degree) via the degree-ratio relation
`⟨X, cX χ₃⟩ − d₃·⟨X, cX χ₁⟩ = −d₃` (`inner_extension_Xset_scaledSub_eq_neg_general`): under
`X = −cX χ₂` both inner products vanish (distinct `X`-images), giving `0 = −d₃`, impossible since
`d₃ > 0`.  Hence the crux `(χ₁−aη₁)^τ = cX χ₁ − a·cY η₁`. -/
theorem crux_general_of_higher_anchor
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  obtain ⟨d, hdpos, hd⟩ :=
    hyp.exists_charValue_one_eq_mul_xBaseBlock_anchor_of_irreducible_X hp hHp
      (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hχ₃ hχ₁base
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (cX.extension ψ) (cX.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [cX.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rcases hyp.extension_eq_or_eq_neg_general hF cX cY hη₁ hχ₁X hχ₂ hne₂ ha hdeg2 hgood with h | h
  · exact eq_sub_of_add_eq h
  · exfalso
    have hrel3 := hyp.inner_extension_Xset_scaledSub_eq_neg_general hF cX cY hη₁ hχ₁X hχ₃ hne₃₁ ha hd
    rw [h, ClassFunction.inner_neg_left, ClassFunction.inner_neg_left,
      hXon χ₂ χ₃ hχ₂ hχ₃, if_neg (Ne.symm hne₃₂), hXon χ₂ χ₁ hχ₂ hχ₁X, if_neg hne₂] at hrel3
    have hd0 : (d : ℂ) = 0 := by linear_combination hrel3
    rw [Nat.cast_eq_zero] at hd0
    omega

open scoped Classical in
/-- **(6.8.1) crux, general witnesses + ANY third anchor**, case (A) / c2 mirror of
`crux_general_of_higher_anchor`.  The dichotomy/relation/`X`-irreducibility inputs use their
case-(A) counterparts (`extension_eq_or_eq_neg_general_c2_caseA`,
`inner_extension_Xset_scaledSub_eq_neg_general_c2_caseA`,
`isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem crux_general_of_higher_anchor_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  obtain ⟨d, hdpos, hd⟩ :=
    hyp.exists_charValue_one_eq_mul_xBaseBlock_anchor_of_irreducible_X hp hHp
      (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h) hχ₃ hχ₁base
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (cX.extension ψ) (cX.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [cX.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rcases hyp.extension_eq_or_eq_neg_general_c2_caseA hK hW1 hA cX cY hη₁ hχ₁X hχ₂ hne₂ ha hdeg2
    hgood with h | h
  · exact eq_sub_of_add_eq h
  · exfalso
    have hrel3 := hyp.inner_extension_Xset_scaledSub_eq_neg_general_c2_caseA hK hW1 hA cX cY hη₁
      hχ₁X hχ₃ hne₃₁ ha hd
    rw [h, ClassFunction.inner_neg_left, ClassFunction.inner_neg_left,
      hXon χ₂ χ₃ hχ₂ hχ₃, if_neg (Ne.symm hne₃₂), hXon χ₂ χ₁ hχ₂ hχ₁X, if_neg hne₂] at hrel3
    have hd0 : (d : ℂ) = 0 := by linear_combination hrel3
    rw [Nat.cast_eq_zero] at hd0
    omega

open scoped Classical in
/-- **(6.8.1) E2: a `Y`-coherence witness in the good case** (the `m = 2` relabel, folded in).
Produces a `Y`-coherence witness `cY` with `⟨(χ₁−aη₁)^τ, cY η₁⟩ = −a` — the `hgood` that the crux
consumes.  Generic `|Y| ≥ 3`: `cY = coherentYset` (good branch of the step-4 dichotomy
`coeff_eq_neg_or_edge_of_frobenius`).  Edge `|Y| = 2`: `coherentYset` may give the bad value `0`;
then `Y = {η₁, η₂}` and the sign-swapped witness `cY'` (`coherentEqualDegree_swap_neg`,
`η₁ ↦ −η₂^{τ₁}`) gives `⟨v, cY' η₁⟩ = −⟨v, coherentYset η₂⟩ = −a`, since
`⟨v, coherentYset η₂⟩ = ⟨v, coherentYset η₁⟩ + a = 0 + a = a` (`inner_tau_scaledDiff_tau_Yset_diff`
+ `extends_on_supported`). -/
theorem exists_Ycoherence_hgood_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ) := by
  classical
  rcases hyp.coeff_eq_neg_or_edge_of_frobenius hF hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos ha with
    hgood | ⟨hm2, hbad⟩
  · exact ⟨hyp.coherentYset, hgood⟩
  · -- edge `|Y| = 2`: relabel.
    obtain ⟨η₂, hη₂Y, hη₂ne⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < hyp.Yset.ncard) η₁
    have hpairsub : ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Yset := by
      intro x hx; rcases hx with rfl | rfl
      · exact hη₁
      · exact hη₂Y
    have hYeq : hyp.Yset = ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) :=
      (Set.eq_of_subset_of_ncard_le hpairsub (hm2.le.trans_eq (Set.ncard_pair hη₂ne.symm).symm)
        hyp.Yset_finite).symm
    -- orthonormality of `η₁, η₂` (distinct irreducible `Y`-members).
    have hinner : ∀ φ ψ : ClassFunction ↥L ℂ, IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
        ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at h
      rw [h]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have hY1irr := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
    have hY2irr := hyp.isIrreducibleCharacter_of_mem_Yset hη₂Y
    have horth : ClassFunction.inner η₁ η₂ = 0 := by
      rw [hinner η₁ η₂ hY1irr hY2irr, if_neg (Ne.symm hη₂ne)]
    have hn1 : ClassFunction.inner η₁ η₁ = 1 := by rw [hinner η₁ η₁ hY1irr hY1irr, if_pos rfl]
    have hn2 : ClassFunction.inner η₂ η₂ = 1 := by rw [hinner η₂ η₂ hY2irr hY2irr, if_pos rfl]
    have hdeg : (η₂ : ↥L → ℂ) 1 = (η₁ : ↥L → ℂ) 1 :=
      (hyp.Yset_apply_one hη₂Y).trans (hyp.Yset_apply_one hη₁).symm
    have hdeg0 : (η₁ : ↥L → ℂ) 1 ≠ 0 := by
      rw [hyp.Yset_apply_one hη₁]; exact_mod_cast Nat.card_pos.ne'
    have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; intro hmem; exact hmem.2 (by simp)
    have hsupp : (η₂ - η₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη₂Y) (hyp.Yset_subset_S hη₁) hdeg
    -- transport `coherentYset` to the pair, build the swapped witness, transport back.
    have hcY0map : (hYeq ▸ hyp.coherentYset).extension = hyp.coherentYset.extension :=
      OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq hyp.coherentYset
    obtain ⟨cY', hcY'1, _⟩ := OddOrder.Peterfalvi.S07.coherentEqualDegree_swap_neg
      (hYeq ▸ hyp.coherentYset) horth hn1 hn2 hdeg hdeg0 h1A hsupp
    refine ⟨hYeq.symm ▸ cY', ?_⟩
    -- `⟨v, η₂^{τ₁}⟩ = a` from the constancy + the bad value `⟨v, η₁^{τ₁}⟩ = 0`.
    have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_of_frobenius hF hη₁ hη₂Y hη₂ne hχ₁ ha
    have htaud : hyp.tau (η₂ - η₁)
        = hyp.coherentYset.extension η₂ - hyp.coherentYset.extension η₁ := by
      rw [← hyp.coherentYset.extends_on_supported (η₂ - η₁)
        ⟨Submodule.sub_mem _ (Submodule.subset_span hη₂Y) (Submodule.subset_span hη₁), hsupp⟩,
        map_sub]
    rw [htaud, ClassFunction.inner_sub_right, hbad, sub_zero] at hconst
    -- assemble: `⟨v, (cY' η₁)⟩ = −⟨v, coherentYset η₂⟩ = −a`.
    rw [OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq.symm cY', hcY'1, hcY0map,
      ClassFunction.inner_neg_right, hconst]

open scoped Classical in
/-- **(6.8.1) E2: a `Y`-coherence witness in the good case**, case (A) / c2 mirror of
`exists_Ycoherence_hgood_of_frobenius`.  The step-4 dichotomy/constancy inputs use their case-(A)
counterparts (`coeff_eq_neg_or_edge_c2_caseA`, `inner_tau_scaledDiff_tau_Yset_diff_c2_caseA`)
instead of `hF` (cert data `hK`/`hW1`/`hA`); the non-`hF` `coherentEqualDegree_swap_neg` relabel is
copied verbatim. -/
theorem exists_Ycoherence_hgood_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ) := by
  classical
  rcases hyp.coeff_eq_neg_or_edge_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos ha with
    hgood | ⟨hm2, hbad⟩
  · exact ⟨hyp.coherentYset, hgood⟩
  · -- edge `|Y| = 2`: relabel.
    obtain ⟨η₂, hη₂Y, hη₂ne⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < hyp.Yset.ncard) η₁
    have hpairsub : ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Yset := by
      intro x hx; rcases hx with rfl | rfl
      · exact hη₁
      · exact hη₂Y
    have hYeq : hyp.Yset = ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) :=
      (Set.eq_of_subset_of_ncard_le hpairsub (hm2.le.trans_eq (Set.ncard_pair hη₂ne.symm).symm)
        hyp.Yset_finite).symm
    -- orthonormality of `η₁, η₂` (distinct irreducible `Y`-members).
    have hinner : ∀ φ ψ : ClassFunction ↥L ℂ, IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
        ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at h
      rw [h]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have hY1irr := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
    have hY2irr := hyp.isIrreducibleCharacter_of_mem_Yset hη₂Y
    have horth : ClassFunction.inner η₁ η₂ = 0 := by
      rw [hinner η₁ η₂ hY1irr hY2irr, if_neg (Ne.symm hη₂ne)]
    have hn1 : ClassFunction.inner η₁ η₁ = 1 := by rw [hinner η₁ η₁ hY1irr hY1irr, if_pos rfl]
    have hn2 : ClassFunction.inner η₂ η₂ = 1 := by rw [hinner η₂ η₂ hY2irr hY2irr, if_pos rfl]
    have hdeg : (η₂ : ↥L → ℂ) 1 = (η₁ : ↥L → ℂ) 1 :=
      (hyp.Yset_apply_one hη₂Y).trans (hyp.Yset_apply_one hη₁).symm
    have hdeg0 : (η₁ : ↥L → ℂ) 1 ≠ 0 := by
      rw [hyp.Yset_apply_one hη₁]; exact_mod_cast Nat.card_pos.ne'
    have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; intro hmem; exact hmem.2 (by simp)
    have hsupp : (η₂ - η₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη₂Y) (hyp.Yset_subset_S hη₁) hdeg
    -- transport `coherentYset` to the pair, build the swapped witness, transport back.
    have hcY0map : (hYeq ▸ hyp.coherentYset).extension = hyp.coherentYset.extension :=
      OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq hyp.coherentYset
    obtain ⟨cY', hcY'1, _⟩ := OddOrder.Peterfalvi.S07.coherentEqualDegree_swap_neg
      (hYeq ▸ hyp.coherentYset) horth hn1 hn2 hdeg hdeg0 h1A hsupp
    refine ⟨hYeq.symm ▸ cY', ?_⟩
    -- `⟨v, η₂^{τ₁}⟩ = a` from the constancy + the bad value `⟨v, η₁^{τ₁}⟩ = 0`.
    have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_c2_caseA hK hW1 hA hη₁ hη₂Y hη₂ne hχ₁ ha
    have htaud : hyp.tau (η₂ - η₁)
        = hyp.coherentYset.extension η₂ - hyp.coherentYset.extension η₁ := by
      rw [← hyp.coherentYset.extends_on_supported (η₂ - η₁)
        ⟨Submodule.sub_mem _ (Submodule.subset_span hη₂Y) (Submodule.subset_span hη₁), hsupp⟩,
        map_sub]
    rw [htaud, ClassFunction.inner_sub_right, hbad, sub_zero] at hconst
    -- assemble: `⟨v, (cY' η₁)⟩ = −⟨v, coherentYset η₂⟩ = −a`.
    rw [OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq.symm cY', hcY'1, hcY0map,
      ClassFunction.inner_neg_right, hconst]

open scoped Classical in
/-- **(6.8.1) E3: `X`-coherence witness + crux in the `|X(Zc)| = 2` edge** (the `n = 2` relabel).
When `X(Zc) = {χ₁, χ₂}` (a conjugate pair, equal degree), the step-5 dichotomy
`X = cX₀ χ₁ ∨ X = −cX₀ χ₂` (`extension_eq_or_eq_neg_general` at the fixed `cX₀`) has no third anchor
to exclude the right disjunct; instead, the right disjunct is *absorbed* by the sign-swapped witness
`cX'` (`coherentEqualDegree_swap_neg`, `χ₁ ↦ −χ₂^{τ₂}`, valid because `|X| = 2` is the whole set):
`cX' χ₁ = −cX₀ χ₂ = X`, giving the crux `(χ₁−aη₁)^τ = cX' χ₁ − a·cY η₁`.  Left disjunct uses `cX = cX₀`
directly.  Produces a witness + crux for *some* `cX`. -/
theorem exists_Xcoherence_crux_of_card_two_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hXeq : hyp.Xset hyp.centralCommutator = ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)))
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ)) :
    ∃ cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  set cX0 := hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp with hcX0def
  rcases hyp.extension_eq_or_eq_neg_general hF cX0 cY hη₁ hχ₁ hχ₂ hne ha hdeg2 hgood with h | h
  · -- left disjunct `X = cX₀ χ₁` ⟹ crux for `cX₀`.
    exact ⟨cX0, eq_sub_of_add_eq h⟩
  · -- right disjunct `X = −cX₀ χ₂` ⟹ relabel `cX' χ₁ = −cX₀ χ₂`.
    have hinner : ∀ φ ψ : ClassFunction ↥L ℂ, IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
        ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have hh := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at hh
      rw [hh]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have hX1irr := hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁
    have hX2irr := hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₂
    have horth : ClassFunction.inner χ₁ χ₂ = 0 := by
      rw [hinner χ₁ χ₂ hX1irr hX2irr, if_neg (Ne.symm hne)]
    have hn1 : ClassFunction.inner χ₁ χ₁ = 1 := by rw [hinner χ₁ χ₁ hX1irr hX1irr, if_pos rfl]
    have hn2 : ClassFunction.inner χ₂ χ₂ = 1 := by rw [hinner χ₂ χ₂ hX2irr hX2irr, if_pos rfl]
    have hdeg0 : (χ₁ : ↥L → ℂ) 1 ≠ 0 := by
      obtain ⟨d, hdpos, hdeq⟩ :=
        irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ₁, hX1irr⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at hdeq
      rw [hdeq]; exact_mod_cast hdpos.ne'
    have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; intro hmem; exact hmem.2 (by simp)
    have hsupp : (χ₂ - χ₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
    have hcX0map : (hXeq ▸ cX0).extension = cX0.extension :=
      OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hXeq cX0
    obtain ⟨cX', hcX'1, _⟩ := OddOrder.Peterfalvi.S07.coherentEqualDegree_swap_neg
      (hXeq ▸ cX0) horth hn1 hn2 hdeg2 hdeg0 h1A hsupp
    refine ⟨hXeq.symm ▸ cX', ?_⟩
    rw [OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hXeq.symm cX', hcX'1, hcX0map]
    exact eq_sub_of_add_eq h

open scoped Classical in
/-- **(6.8.1) E3: `X`-coherence witness + crux in the `|X(Zc)| = 2` edge**, case (A) / c2 mirror of
`exists_Xcoherence_crux_of_card_two_of_frobenius`.  The fixed `X`-coherence/dichotomy/`X`-irreducibility
inputs use their case-(A) counterparts (`Xset_centralCommutator_isCoherent_of_c2_caseA`,
`extension_eq_or_eq_neg_general_c2_caseA`, `isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of
`hF` (cert data `hK`/`hW1`/`hA`); the non-`hF` `coherentEqualDegree_swap_neg` relabel is copied
verbatim. -/
theorem exists_Xcoherence_crux_of_card_two_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hXeq : hyp.Xset hyp.centralCommutator = ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)))
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ)) :
    ∃ cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  set cX0 := hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp
    with hcX0def
  rcases hyp.extension_eq_or_eq_neg_general_c2_caseA hK hW1 hA cX0 cY hη₁ hχ₁ hχ₂ hne ha hdeg2
    hgood with h | h
  · -- left disjunct `X = cX₀ χ₁` ⟹ crux for `cX₀`.
    exact ⟨cX0, eq_sub_of_add_eq h⟩
  · -- right disjunct `X = −cX₀ χ₂` ⟹ relabel `cX' χ₁ = −cX₀ χ₂`.
    have hinner : ∀ φ ψ : ClassFunction ↥L ℂ, IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
        ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have hh := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at hh
      rw [hh]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have hX1irr := hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₁
    have hX2irr := hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₂
    have horth : ClassFunction.inner χ₁ χ₂ = 0 := by
      rw [hinner χ₁ χ₂ hX1irr hX2irr, if_neg (Ne.symm hne)]
    have hn1 : ClassFunction.inner χ₁ χ₁ = 1 := by rw [hinner χ₁ χ₁ hX1irr hX1irr, if_pos rfl]
    have hn2 : ClassFunction.inner χ₂ χ₂ = 1 := by rw [hinner χ₂ χ₂ hX2irr hX2irr, if_pos rfl]
    have hdeg0 : (χ₁ : ↥L → ℂ) 1 ≠ 0 := by
      obtain ⟨d, hdpos, hdeq⟩ :=
        irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ₁, hX1irr⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at hdeq
      rw [hdeq]; exact_mod_cast hdpos.ne'
    have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; intro hmem; exact hmem.2 (by simp)
    have hsupp : (χ₂ - χ₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
    have hcX0map : (hXeq ▸ cX0).extension = cX0.extension :=
      OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hXeq cX0
    obtain ⟨cX', hcX'1, _⟩ := OddOrder.Peterfalvi.S07.coherentEqualDegree_swap_neg
      (hXeq ▸ cX0) horth hn1 hn2 hdeg2 hdeg0 h1A hsupp
    refine ⟨hXeq.symm ▸ cX', ?_⟩
    rw [OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hXeq.symm cX', hcX'1, hcX0map]
    exact eq_sub_of_add_eq h

/-- **(6.8.1) capstone `X(Zc) ∪ Y` coherence from a witness-level crux** (general form).  Given
arbitrary coherence witnesses `cX` (for `X(Zc)`), `cY` (for `Y`), a base-block anchor `χ₁` with
`χ₁(1) = a·|W₁|`, an `η₁ ∈ Y`, and the **crux** `(χ₁−aη₁)^τ = cX χ₁ − a·cY η₁` (whichever way it is
established — the generic `n,m ≥ 3` argument or the `m=2`/`n=2` relabel), the union `X(Zc) ∪ Y` is
coherent.  `ν` is the `τ₃` glue of `cX`/`cY`; `hmixed = himg_ortho_general`, `hDτ = hcrux`,
`hgen = hgen_withDiagonal`.  This is the common assembly shared by the generic case and both edge
cases (which differ only in how `hcrux` is produced for the chosen witnesses). -/
noncomputable def coherentXunionYset_centralCommutator_diagonal_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hcrux : hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hXY : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner x y = 0 := fun x hx y hy => by
    rw [hinner x y (hXirr x hx) (hYirr y hy),
      if_neg (by intro h; exact Set.disjoint_left.mp hdisj hx (h ▸ hy))]
  have hglue :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthonormal
      (hyp.Xset_finite hyp.centralCommutator) hyp.Yset_finite
      (fun x hx x' hx' => hinner x x' (hXirr x hx) (hXirr x' hx'))
      (fun y hy y' hy' => hinner y y' (hYirr y hy) (hYirr y' hy')) hXY
      cX.extension cY.extension
  refine hyp.coherentXunionYset_centralCommutator_of_glued_withDiagonal_general
    hF cX cY hglue.choose hglue.choose_spec.1 hglue.choose_spec.2 (fun x hx y hy => ?_)
    {χ₁ - a • η₁} (fun d hd => ?_)
    (hyp.hgen_withDiagonal_of_frobenius hF hp hHp hη₁ hχ₁base ha)
  · -- `hmixed`: `⟨ν x, ν y⟩ = ⟨x, y⟩` (both `0`).
    rw [hglue.choose_spec.1 x hx, hglue.choose_spec.2 y hy,
      hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general hF cX cY hx hy, hXY x hx y hy]
  · -- `hDτ`: `ν(χ₁−aη₁) = (χ₁−aη₁)^τ` = the crux.
    rw [Set.mem_singleton_iff] at hd
    subst hd
    rw [map_sub, map_nsmul, hglue.choose_spec.1 χ₁ hχ₁X, hglue.choose_spec.2 η₁ hη₁,
      ← Nat.cast_smul_eq_nsmul ℂ a (cY.extension η₁)]
    exact hcrux.symm

/-- **(6.8.1) capstone `X(Zc) ∪ Y` coherence from a witness-level crux**, case (A) / c2 mirror of
`coherentXunionYset_centralCommutator_diagonal_general`.  The glue/`X ⊥ Y`/`hgen`/`X`-irreducibility
inputs use their case-(A) counterparts
(`coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_c2_caseA`,
`inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA`, `hgen_withDiagonal_c2_caseA`,
`isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
noncomputable def coherentXunionYset_centralCommutator_diagonal_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hcrux : hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hφ
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hXY : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner x y = 0 := fun x hx y hy => by
    rw [hinner x y (hXirr x hx) (hYirr y hy),
      if_neg (by intro h; exact Set.disjoint_left.mp hdisj hx (h ▸ hy))]
  have hglue :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthonormal
      (hyp.Xset_finite hyp.centralCommutator) hyp.Yset_finite
      (fun x hx x' hx' => hinner x x' (hXirr x hx) (hXirr x' hx'))
      (fun y hy y' hy' => hinner y y' (hYirr y hy) (hYirr y' hy')) hXY
      cX.extension cY.extension
  refine hyp.coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_c2_caseA
    hK hW1 hA cX cY hglue.choose hglue.choose_spec.1 hglue.choose_spec.2 (fun x hx y hy => ?_)
    {χ₁ - a • η₁} (fun d hd => ?_)
    (hyp.hgen_withDiagonal_c2_caseA hK hW1 hA hp hHp hη₁ hχ₁base ha)
  · -- `hmixed`: `⟨ν x, ν y⟩ = ⟨x, y⟩` (both `0`).
    rw [hglue.choose_spec.1 x hx, hglue.choose_spec.2 y hy,
      hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA hK hW1 hA cX cY hx hy,
      hXY x hx y hy]
  · -- `hDτ`: `ν(χ₁−aη₁) = (χ₁−aη₁)^τ` = the crux.
    rw [Set.mem_singleton_iff] at hd
    subst hd
    rw [map_sub, map_nsmul, hglue.choose_spec.1 χ₁ hχ₁X, hglue.choose_spec.2 η₁ hη₁,
      ← Nat.cast_smul_eq_nsmul ℂ a (cY.extension η₁)]
    exact hcrux.symm

/-- **(6.8.1) generic capstone Frobenius branch (`m, n ≥ 3`):** `X(Zc) ∪ Y` is coherent.

Given three distinct equal-degree `X(Zc)`-anchors `χ₁ ∈ xBaseBlock`, `χ₂, χ₃` (the `n ≥ 3`
pinning) with `χ₁(1) = a·|W₁|`, an `η₁ ∈ Y` and `|Y| ≥ 3` (the `m ≥ 3` good case), the union is
coherent.  Delegates to `coherentXunionYset_centralCommutator_diagonal_general` at the fixed
witnesses, with `hcrux = crux_of_frobenius`.  The `m = 2` / `n = 2` edge cases (relabel) are not
covered. -/
noncomputable def coherentXunionYset_centralCommutator_diagonal_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1) (hm3 : 3 ≤ hyp.Yset.ncard) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.coherentXunionYset_centralCommutator_diagonal_general hF hp hHp
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁base ha
    (hyp.crux_of_frobenius hF hHnonab hp hp3 hHp hη₁ (hyp.xBaseBlock_subset _ hχ₁base) hχ₂ hne₂
      hχ₃ hne₃₁ hne₃₂ ha hdeg2 hdeg3 hm3)

/-- **(6.8.1) generic capstone branch (`m, n ≥ 3`)**, case (A) / c2 mirror of
`coherentXunionYset_centralCommutator_diagonal_of_frobenius`.  Delegates to
`coherentXunionYset_centralCommutator_diagonal_general_c2_caseA` at the case-(A) `X`-coherence
(`Xset_centralCommutator_isCoherent_of_c2_caseA`) with `hcrux = crux_c2_caseA` (cert data
`hK`/`hW1`/`hA`) instead of `hF`. -/
noncomputable def coherentXunionYset_centralCommutator_diagonal_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1) (hm3 : 3 ≤ hyp.Yset.ncard) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.coherentXunionYset_centralCommutator_diagonal_general_c2_caseA hK hW1 hA hp hHp
    (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp)
    hyp.coherentYset hη₁ hχ₁base ha
    (hyp.crux_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη₁ (hyp.xBaseBlock_subset _ hχ₁base) hχ₂ hne₂
      hχ₃ hne₃₁ hne₃₂ ha hdeg2 hdeg3 hm3)

/-- **(6.8) capstone, case (A) (Frobenius, `m, n ≥ 3` with given anchors): `S` is coherent.**
Combines the generic capstone Frobenius branch
(`coherentXunionYset_centralCommutator_diagonal_of_frobenius`, giving `X(Zc) ∪ Y` coherent) with the
(6.8.3) extension `false_of_coherentXunionYset_of_not_coherentS` (`X ∪ Y` coherent ∧ `S` not
coherent ⟹ False): so `S` is coherent.  The anchors `χ₁ ∈ xBaseBlock, χ₂, χ₃` (distinct,
equal-degree, the `n ≥ 3` data) and `3 ≤ |Y|` (the `m ≥ 3` data) are taken as hypotheses; their
existence (vs the
`m = 2` / `n = 2` relabels) is a separate concern. -/
theorem nonempty_coherent_S_caseA_of_anchors_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hdeg2 : χ₂ 1 = χ₁ 1) (hdeg3 : χ₃ 1 = χ₁ 1) (hm3 : 3 ≤ hyp.Yset.ncard) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  by_contra hncoh
  exact hyp.false_of_coherentXunionYset_of_not_coherentS hF hHnonab
    ⟨hyp.coherentXunionYset_centralCommutator_diagonal_of_frobenius hF hHnonab hp hp3 hHp
      hη₁ hχ₁base hχ₂ hne₂ hχ₃ hne₃₁ hne₃₂ ha hdeg2 hdeg3 hm3⟩ hncoh

/-- **(6.8) capstone, case (A) under the `m, n ≥ 3` cardinality data: `S` is coherent.**
From `3 ≤ |xBaseBlock Zc|` (giving three distinct base-block anchors `χ₁, χ₂, χ₃`, all of equal
degree since the base block is equal-degree, `xBaseBlock_degree_re_eq`) and `3 ≤ |Y|`, the anchor
hypotheses of `nonempty_coherent_S_caseA_of_anchors_of_frobenius` are met (with `χ₁(1) = a·|W₁|`
extracted via a degree-`|W₁|` `Y`-anchor), so `S` is coherent.  This is the (6.8) capstone Frobenius
branch in the generic `m, n ≥ 3` case; the `m = 2` / `n = 2` edge cases (relabels) are not
covered. -/
theorem nonempty_coherent_S_caseA_of_card_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (h3X : 3 ≤ (hyp.xBaseBlock hyp.centralCommutator).ncard)
    (h3Y : 3 ≤ hyp.Yset.ncard) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ
  -- three distinct base-block anchors (from `3 ≤ |xBaseBlock|`).
  obtain ⟨χ₁, hχ₁base, χ₂, hχ₂base, χ₃, hχ₃base, hne12, hne13, hne23⟩ :
      ∃ a ∈ hyp.xBaseBlock hyp.centralCommutator, ∃ b ∈ hyp.xBaseBlock hyp.centralCommutator,
        ∃ c ∈ hyp.xBaseBlock hyp.centralCommutator, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    obtain ⟨a, ha⟩ : (hyp.xBaseBlock hyp.centralCommutator).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨b, hb, hba⟩ := Set.exists_ne_of_one_lt_ncard
      (s := hyp.xBaseBlock hyp.centralCommutator) (by omega) a
    have hpair : ({a, b} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.xBaseBlock hyp.centralCommutator := by
      intro x hx; rcases hx with rfl | rfl
      · exact ha
      · exact hb
    have hdc : (hyp.xBaseBlock hyp.centralCommutator \ {a, b}).ncard
        = (hyp.xBaseBlock hyp.centralCommutator).ncard - 2 := by
      rw [Set.ncard_sdiff hpair, Set.ncard_pair (Ne.symm hba)]
    have hcne : (hyp.xBaseBlock hyp.centralCommutator \ {a, b}).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]; intro he; rw [he, Set.ncard_empty] at hdc; omega
    obtain ⟨c, hcs, hcnp⟩ := hcne
    rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcnp
    exact ⟨a, ha, b, hb, c, hcs, Ne.symm hba, fun h => hcnp.1 h.symm, fun h => hcnp.2 h.symm⟩
  have hχ₁X := hyp.xBaseBlock_subset _ hχ₁base
  have hχ₂X := hyp.xBaseBlock_subset _ hχ₂base
  have hχ₃X := hyp.xBaseBlock_subset _ hχ₃base
  -- `η₁ ∈ Y` (degree `|W₁|`) and the degree ratio `a`.
  obtain ⟨η₁, hη₁⟩ := hyp.Yset_nonempty
  obtain ⟨a, _, ha⟩ := hyp.sMember_charValue_one_eq_mul_anchor (hyp.Xset_subset_S hχ₁X)
    (hyp.Yset_apply_one hη₁)
  rw [hyp.Yset_apply_one hη₁] at ha
  -- the base block is equal-degree.
  have hdegeq : ∀ χ' ∈ hyp.xBaseBlock hyp.centralCommutator, χ' 1 = χ₁ 1 := by
    intro χ' hχ'
    have hre := hyp.xBaseBlock_degree_re_eq hχ' hχ₁base
    rw [OddOrder.Peterfalvi.S03.characterDegree_def,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hre
    obtain ⟨d', _, hd'⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ', hXirr χ' (hyp.xBaseBlock_subset _ hχ')⟩ : IrreducibleCharacter ↥L)
    obtain ⟨d₁, _, hd₁⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ₁, hXirr χ₁ hχ₁X⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hd' hd₁
    rw [hd', hd₁] at hre ⊢
    exact_mod_cast hre
  exact hyp.nonempty_coherent_S_caseA_of_anchors_of_frobenius hF hHnonab hp hp3 hHp hη₁
    hχ₁base hχ₂X hne12.symm hχ₃X hne13.symm hne23.symm ha
    (hdegeq χ₂ hχ₂base) (hdegeq χ₃ hχ₃base) h3Y

open scoped Classical in
/-- **(6.8) capstone, case (A) (Frobenius): `S` is coherent — UNCONDITIONAL** (no `3 ≤` cardinality
hypotheses; the `m = 2` / `n = 2` edge relabels are handled internally).  This is the full case-(A)
result: only `2 ≤ |xBaseBlock|` (`two_le_xBaseBlock_ncard`) and `2 ≤ |Y|` (`two_le_Yset_ncard`),
both unconditionally available, are used.  E2 (`exists_Ycoherence_hgood_of_frobenius`) supplies the
`Y`-witness + good case (the `m = 2` relabel).  The `X`-side splits on `|X(Zc)|`: `≥ 3` uses the
degree-ratio crux E1 (`crux_general_of_higher_anchor`) at the fixed `X`-witness; `= 2` uses the
relabel crux E3 (`exists_Xcoherence_crux_of_card_two_of_frobenius`).  Either way the crux feeds the
shared assembly `coherentXunionYset_centralCommutator_diagonal_general`, giving `X(Zc) ∪ Y` coherent,
and the (6.8.3) extension `false_of_coherentXunionYset_of_not_coherentS` lifts it to `S`. -/
theorem nonempty_coherent_S_caseA_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  classical
  by_contra hncoh
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ
  have hXne : (hyp.Xset hyp.centralCommutator).Nonempty :=
    hyp.Xset_centralCommutator_nonempty hF hHnonab
  have hXfin : (hyp.Xset hyp.centralCommutator).Finite := hyp.Xset_finite hyp.centralCommutator
  have h2X : 2 ≤ (hyp.xBaseBlock hyp.centralCommutator).ncard :=
    hyp.two_le_xBaseBlock_ncard hF hyp.centralCommutator_le hXne
  -- two distinct base-block anchors.
  obtain ⟨χ₁, hχ₁base, χ₂, hχ₂base, hne⟩ : ∃ a ∈ hyp.xBaseBlock hyp.centralCommutator,
      ∃ b ∈ hyp.xBaseBlock hyp.centralCommutator, b ≠ a := by
    obtain ⟨a, ha⟩ : (hyp.xBaseBlock hyp.centralCommutator).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨b, hb, hba⟩ := Set.exists_ne_of_one_lt_ncard
      (s := hyp.xBaseBlock hyp.centralCommutator) (by omega) a
    exact ⟨a, ha, b, hb, hba⟩
  have hχ₁X := hyp.xBaseBlock_subset _ hχ₁base
  have hχ₂X := hyp.xBaseBlock_subset _ hχ₂base
  -- `η₁ ∈ Y` (degree `|W₁|`) and the degree ratio `a`.
  obtain ⟨η₁, hη₁⟩ := hyp.Yset_nonempty
  obtain ⟨a, ha_pos, ha⟩ := hyp.sMember_charValue_one_eq_mul_anchor (hyp.Xset_subset_S hχ₁X)
    (hyp.Yset_apply_one hη₁)
  rw [hyp.Yset_apply_one hη₁] at ha
  -- base block equal-degree.
  have hdegeq : ∀ χ' ∈ hyp.xBaseBlock hyp.centralCommutator, χ' 1 = χ₁ 1 := by
    intro χ' hχ'
    have hre := hyp.xBaseBlock_degree_re_eq hχ' hχ₁base
    rw [OddOrder.Peterfalvi.S03.characterDegree_def,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hre
    obtain ⟨d', _, hd'⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ', hXirr χ' (hyp.xBaseBlock_subset _ hχ')⟩ : IrreducibleCharacter ↥L)
    obtain ⟨d₁, _, hd₁⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ₁, hXirr χ₁ hχ₁X⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hd' hd₁
    rw [hd', hd₁] at hre ⊢
    exact_mod_cast hre
  have hdeg2 : χ₂ 1 = χ₁ 1 := hdegeq χ₂ hχ₂base
  -- E2: the `Y`-witness with the good case (m = 2 relabel folded in).
  obtain ⟨cY, hgood⟩ :=
    hyp.exists_Ycoherence_hgood_of_frobenius hF hHnonab hp hp3 hHp hη₁ hχ₁X ha_pos ha
  -- build `X(Zc) ∪ Y` coherent, splitting on `|X(Zc)|`.
  have hXYcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    by_cases h3X : 3 ≤ (hyp.Xset hyp.centralCommutator).ncard
    · -- `|X(Zc)| ≥ 3`: a third `X`-member of ANY degree (E1, degree-ratio exclusion).
      have hex : ∃ c ∈ hyp.Xset hyp.centralCommutator, c ≠ χ₁ ∧ c ≠ χ₂ := by
        have hpair : ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Xset hyp.centralCommutator := by
          intro x hx; rcases hx with rfl | rfl
          · exact hχ₁X
          · exact hχ₂X
        have hdc : (hyp.Xset hyp.centralCommutator \ {χ₁, χ₂}).ncard
            = (hyp.Xset hyp.centralCommutator).ncard - 2 := by
          rw [Set.ncard_sdiff hpair, Set.ncard_pair (Ne.symm hne)]
        have hcne : (hyp.Xset hyp.centralCommutator \ {χ₁, χ₂}).Nonempty := by
          rw [Set.nonempty_iff_ne_empty]; intro he; rw [he, Set.ncard_empty] at hdc; omega
        obtain ⟨c, hcs, hcnp⟩ := hcne
        rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcnp
        exact ⟨c, hcs, hcnp.1, hcnp.2⟩
      have cX0 := hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp
      exact hyp.coherentXunionYset_centralCommutator_diagonal_general hF hp hHp cX0 cY hη₁
        hχ₁base ha (hyp.crux_general_of_higher_anchor hF hp hHp cX0 cY hη₁ hχ₁base hχ₂X hne hdeg2
          hex.choose_spec.1 hex.choose_spec.2.1 hex.choose_spec.2.2 ha hgood)
    · -- `|X(Zc)| = 2`: relabel (E3).
      have h2Xle : 2 ≤ (hyp.Xset hyp.centralCommutator).ncard :=
        le_trans h2X (Set.ncard_le_ncard (hyp.xBaseBlock_subset _) hXfin)
      have h2Xeq : (hyp.Xset hyp.centralCommutator).ncard = 2 := by omega
      have hpairsub : ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Xset hyp.centralCommutator := by
        intro x hx; rcases hx with rfl | rfl
        · exact hχ₁X
        · exact hχ₂X
      have hXeq : hyp.Xset hyp.centralCommutator = ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)) :=
        (Set.eq_of_subset_of_ncard_le hpairsub
          (h2Xeq.le.trans_eq (Set.ncard_pair (Ne.symm hne)).symm) hXfin).symm
      have hexX := hyp.exists_Xcoherence_crux_of_card_two_of_frobenius hF hHnonab hp hp3 hHp
        cY hη₁ hχ₁X hχ₂X hne hdeg2 hXeq ha hgood
      exact hyp.coherentXunionYset_centralCommutator_diagonal_general hF hp hHp hexX.choose cY hη₁
        hχ₁base ha hexX.choose_spec
  exact hyp.false_of_coherentXunionYset_of_not_coherentS hF hHnonab ⟨hXYcoh⟩ hncoh

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08

