/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CoherenceBasic

/-!
# Peterfalvi (6.8) setting: `Y`-set extensions restricted to the central commutator

Orthogonality and constancy facts for the Sibley–Dade (6.8) setting, used by the coherence
constructions and the `(6.7)` congruence argument of `OddOrder.Peterfalvi.S08_XBlockCounting`:

* `two_le_xBaseBlock_ncard_c2_caseA` — the base `X`-block has at least two members (case (A)/c2);
* `inner_extension_Xset_centralCommutator_Yset_eq_zero_*` and their span versions — extensions of
  `X`-set characters are orthogonal to `Y`-set extensions on the central commutator;
* `inner_restrict_extension_Yset_*`, `restrict_extension_Yset_degree_value_eq_*`,
  `restrict_extension_Yset_const_on_centralCommutator_*` — the restriction of a `Y`-set extension
  to the central commutator is the constant degree character.

Each result comes in a Frobenius (`_of_frobenius`) form and a certain-type case-(A) (`_c2_caseA`)
mirror.  Split out of `S08_XBlockCounting` (issue 0189: the v4.34 bump left that file at 1490
lines, against the 1500-line limit).
-/
namespace OddOrder.Peterfalvi.S08
open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis
variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(T8 leaf 8) `2 ≤ |S₀|`**, case (A) / c2 form.  As `two_le_xBaseBlock_ncard`, but
`X`-irreducibility comes from the certain-type input `isIrreducibleCharacter_of_mem_Xset_c2_caseA`
(cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem two_le_xBaseBlock_ncard_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hXne : (hyp.Xset hyp.centralCommutator).Nonempty) :
    2 ≤ (hyp.xBaseBlock hyp.centralCommutator).ncard := by
  have := hyp.H_normal
  have := hyp.centralCommutator_normal
  exact hyp.two_le_xBaseBlock_ncard_of_irreducible_X hyp.centralCommutator_le
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h) hXne

/-- **Peterfalvi (6.8.1) image orthogonality `himg_ortho` via (4.1)** (Frobenius case, mmd 04.8
L166).
`X(Zc)^{τ₂} ⊥ Y^{τ₁}`: for `χ ∈ X(Zc)`, `η ∈ Y`, the coherent images are orthogonal,
`⟨χ^{τ₂}, η^{τ₁}⟩ = 0`.  This is the "by (4.1)" step, **independent** of the deep `b ≡ 0` argument.

Pick distinct references `χ' ≠ χ` in `X(Zc)` (`2 ≤ |X(Zc)|`, from `two_le_xBaseBlock_ncard` +
`xBaseBlock_subset`) and `η' ≠ η` in `Y` (`2 ≤ |Y|`, `two_le_Yset_ncard`), and apply
`pairwise_inner_eq_zero_of_orthogonal_signedDifference` with `α = η^{τ₁}, β = η'^{τ₁}, γ = χ^{τ₂},
δ = χ'^{τ₂}` and **degree coefficients** `u = χ'(1), v = χ(1)`.  Then `u•γ − v•δ =
(χ'(1)•χ − χ(1)•χ')^{τ₂}` is the τ₂-image of a *supported* (degree-`0`,
`sMember_smulDiffSupport_of_charValue_eq` — no divisibility needed) integer `X`-combination, and
`α − β = (η − η')^{τ₁}` the τ₁-image of a supported (equal-degree, `Yset_apply_one`) `Y`-difference;
the difference-orthogonality `inner_extension_eq_inner_of_supported` (`= 0` by `X ⊥ Y`) and
degree-`0`
`extension_apply_one_eq_zero_of_supported` discharge `hdiff`/`hα1`/`hγδ1`. The conclusion
`⟨α,γ⟩ = 0`
gives the claim by conjugate symmetry. -/
theorem inner_extension_Xset_centralCommutator_Yset_eq_zero_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner (cX.extension χ) (cY.extension η) = 0 := by
  classical
  have : (hyp.centralCommutator).Normal := hyp.centralCommutator_normal
  set hXc := cX with hXc_def
  set hYc := cY with hYc_def
  -- irreducibility of members
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  -- `if`-formula for inner products of irreducibles (orthonormality)
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [ite_eq_left (Subtype.ext hpq), ite_eq_left hpq]
    · rw [ite_eq_right (fun heq => hpq (Subtype.ext_iff.mp heq)), ite_eq_right hpq]
  -- distinct references (n, m ≥ 2)
  have hXne : (hyp.Xset hyp.centralCommutator).Nonempty := ⟨χ, hχ⟩
  have hXfin : (hyp.Xset hyp.centralCommutator).Finite := hyp.xSet_finite_of_irreducible_X hXirr
  have hX2 : 2 ≤ (hyp.Xset hyp.centralCommutator).ncard :=
    le_trans (hyp.two_le_xBaseBlock_ncard hF hyp.centralCommutator_le hXne)
      (Set.ncard_le_ncard (hyp.xBaseBlock_subset _) hXfin)
  obtain ⟨χ', hχ'X, hχ'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by omega : 1 < (hyp.Xset hyp.centralCommutator).ncard) χ
  obtain ⟨η', hη'Y, hη'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by have := hyp.two_le_Yset_ncard; omega : 1 < hyp.Yset.ncard) η
  -- positive natural degrees of `χ`, `χ'`
  obtain ⟨d, hd_pos, hd_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hXirr χ hχ⟩ : IrreducibleCharacter ↥L)
  obtain ⟨d', hd'_pos, hd'_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ', hXirr χ' hχ'X⟩ : IrreducibleCharacter ↥L)
  simp only [IrreducibleCharacter.coe_mk] at hd_eq hd'_eq
  -- membership in the integral spans (`subset_span`)
  have hχs : χ ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) := Submodule.subset_span hχ
  have hχ's : χ' ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) := Submodule.subset_span hχ'X
  have hηs : η ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη
  have hη's : η' ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη'Y
  -- the two supported difference inputs of (4.1)
  set xdiff : ClassFunction ↥L ℂ := d' • χ - d • χ' with hxdiff_def
  set ydiff : ClassFunction ↥L ℂ := η - η' with hydiff_def
  have hx_supp : xdiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ d' χ]; exact Submodule.smul_mem _ _ hχs
      · rw [← Nat.cast_smul_eq_nsmul ℤ d χ']; exact Submodule.smul_mem _ _ hχ's
    · exact hyp.sMember_smulDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ)
        (hyp.Xset_subset_S hχ'X) (by rw [hd_eq, hd'_eq]; ring)
  have hy_supp : ydiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨Submodule.sub_mem _ hηs hη's, ?_⟩
    exact hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη'Y)
      ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη'Y).symm)
  -- the image of `xdiff` is exactly the degree-weighted `u•γ − v•δ`
  have hXeq : ((d' : ℝ) : ℂ) • hXc.extension χ - ((d : ℝ) : ℂ) • hXc.extension χ'
      = hXc.extension xdiff := by
    rw [hxdiff_def, map_sub, map_nsmul, map_nsmul,
      ← Nat.cast_smul_eq_nsmul ℂ d' (hXc.extension χ),
      ← Nat.cast_smul_eq_nsmul ℂ d (hXc.extension χ')]
    push_cast
    ring_nf
  have hYeq : hYc.extension η - hYc.extension η' = hYc.extension ydiff := by
    rw [hydiff_def, map_sub]
  -- disjointness `X(Zc) ⊥ Y` and the source orthogonality `⟨xdiff, ydiff⟩ = 0`
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hsrc0 : ClassFunction.inner xdiff ydiff = 0 :=
    inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj xdiff hx_supp.1 ydiff hy_supp.1
  -- discharge the (4.1) hypotheses and read off `⟨α,γ⟩ = 0`
  have hconcl := OddOrder.RepresentationTheory.pairwise_inner_eq_zero_of_orthogonal_signedDifference
    (Γ := G) (α := hYc.extension η) (β := hYc.extension η')
    (γ := hXc.extension χ) (δ := hXc.extension χ')
    (u := (d' : ℝ)) (v := (d : ℝ))
    (by exact_mod_cast hd'_pos.ne') (by exact_mod_cast hd_pos.ne')
    (hYc.extension_mem_ZIrr η hηs)
    (by rw [hYc.extension_inner_eq η η hηs hηs, hinner η η (hYirr η hη) (hYirr η hη),
      ite_eq_left rfl])
    (hYc.extension_mem_ZIrr η' hη's)
    (by rw [hYc.extension_inner_eq η' η' hη's hη's, hinner η' η' (hYirr η' hη'Y) (hYirr η' hη'Y),
        ite_eq_left rfl])
    (hXc.extension_mem_ZIrr χ hχs)
    (by rw [hXc.extension_inner_eq χ χ hχs hχs, hinner χ χ (hXirr χ hχ) (hXirr χ hχ),
      ite_eq_left rfl])
    (hXc.extension_mem_ZIrr χ' hχ's)
    (by rw [hXc.extension_inner_eq χ' χ' hχ's hχ's, hinner χ' χ' (hXirr χ' hχ'X) (hXirr χ' hχ'X),
        ite_eq_left rfl])
    (by rw [hYc.extension_inner_eq η η' hηs hη's, hinner η η' (hYirr η hη) (hYirr η' hη'Y),
        ite_eq_right (fun h => hη'ne h.symm)])
    (by rw [hXc.extension_inner_eq χ χ' hχs hχ's, hinner χ χ' (hXirr χ hχ) (hXirr χ' hχ'X),
        ite_eq_right (fun h => hχ'ne h.symm)])
    (by -- hdiff
      rw [hXeq, hYeq, inner_conj_symm (hXc.extension xdiff) (hYc.extension ydiff),
        inner_extension_eq_inner_of_supported hyp.dade hXc hYc hx_supp hy_supp,
        hsrc0, star_zero])
    (by -- hα1
      rw [hYeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hYc hy_supp)
    (by -- hγδ1
      rw [hXeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hXc hx_supp)
  rw [inner_conj_symm (hYc.extension η) (hXc.extension χ), hconcl.1, star_zero]

/-- **Case-(A)/c2 mirror of `inner_extension_Xset_centralCommutator_Yset_eq_zero_general`.**  Same
proof as the Frobenius original, with the Frobenius hypothesis `hF` replaced by the certain-type
case-(A) data bundle `cert`/`hK`/`hW1`/`hA`, and the Frobenius `X`-irreducibility /
`two_le_xBaseBlock_ncard` adapters replaced by their `_c2_caseA` counterparts. -/
theorem inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner (cX.extension χ) (cY.extension η) = 0 := by
  classical
  have : (hyp.centralCommutator).Normal := hyp.centralCommutator_normal
  set hXc := cX with hXc_def
  set hYc := cY with hYc_def
  -- irreducibility of members
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  -- `if`-formula for inner products of irreducibles (orthonormality)
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [ite_eq_left (Subtype.ext hpq), ite_eq_left hpq]
    · rw [ite_eq_right (fun heq => hpq (Subtype.ext_iff.mp heq)), ite_eq_right hpq]
  -- distinct references (n, m ≥ 2)
  have hXne : (hyp.Xset hyp.centralCommutator).Nonempty := ⟨χ, hχ⟩
  have hXfin : (hyp.Xset hyp.centralCommutator).Finite := hyp.xSet_finite_of_irreducible_X hXirr
  have hX2 : 2 ≤ (hyp.Xset hyp.centralCommutator).ncard :=
    le_trans (hyp.two_le_xBaseBlock_ncard_c2_caseA hK hW1 hA hXne)
      (Set.ncard_le_ncard (hyp.xBaseBlock_subset _) hXfin)
  obtain ⟨χ', hχ'X, hχ'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by omega : 1 < (hyp.Xset hyp.centralCommutator).ncard) χ
  obtain ⟨η', hη'Y, hη'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by have := hyp.two_le_Yset_ncard; omega : 1 < hyp.Yset.ncard) η
  -- positive natural degrees of `χ`, `χ'`
  obtain ⟨d, hd_pos, hd_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hXirr χ hχ⟩ : IrreducibleCharacter ↥L)
  obtain ⟨d', hd'_pos, hd'_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ', hXirr χ' hχ'X⟩ : IrreducibleCharacter ↥L)
  simp only [IrreducibleCharacter.coe_mk] at hd_eq hd'_eq
  -- membership in the integral spans (`subset_span`)
  have hχs : χ ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) := Submodule.subset_span hχ
  have hχ's : χ' ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) := Submodule.subset_span hχ'X
  have hηs : η ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη
  have hη's : η' ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη'Y
  -- the two supported difference inputs of (4.1)
  set xdiff : ClassFunction ↥L ℂ := d' • χ - d • χ' with hxdiff_def
  set ydiff : ClassFunction ↥L ℂ := η - η' with hydiff_def
  have hx_supp : xdiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ d' χ]; exact Submodule.smul_mem _ _ hχs
      · rw [← Nat.cast_smul_eq_nsmul ℤ d χ']; exact Submodule.smul_mem _ _ hχ's
    · exact hyp.sMember_smulDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ)
        (hyp.Xset_subset_S hχ'X) (by rw [hd_eq, hd'_eq]; ring)
  have hy_supp : ydiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨Submodule.sub_mem _ hηs hη's, ?_⟩
    exact hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη'Y)
      ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη'Y).symm)
  -- the image of `xdiff` is exactly the degree-weighted `u•γ − v•δ`
  have hXeq : ((d' : ℝ) : ℂ) • hXc.extension χ - ((d : ℝ) : ℂ) • hXc.extension χ'
      = hXc.extension xdiff := by
    rw [hxdiff_def, map_sub, map_nsmul, map_nsmul,
      ← Nat.cast_smul_eq_nsmul ℂ d' (hXc.extension χ),
      ← Nat.cast_smul_eq_nsmul ℂ d (hXc.extension χ')]
    push_cast
    ring_nf
  have hYeq : hYc.extension η - hYc.extension η' = hYc.extension ydiff := by
    rw [hydiff_def, map_sub]
  -- disjointness `X(Zc) ⊥ Y` and the source orthogonality `⟨xdiff, ydiff⟩ = 0`
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hsrc0 : ClassFunction.inner xdiff ydiff = 0 :=
    inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj xdiff hx_supp.1 ydiff hy_supp.1
  -- discharge the (4.1) hypotheses and read off `⟨α,γ⟩ = 0`
  have hconcl := OddOrder.RepresentationTheory.pairwise_inner_eq_zero_of_orthogonal_signedDifference
    (Γ := G) (α := hYc.extension η) (β := hYc.extension η')
    (γ := hXc.extension χ) (δ := hXc.extension χ')
    (u := (d' : ℝ)) (v := (d : ℝ))
    (by exact_mod_cast hd'_pos.ne') (by exact_mod_cast hd_pos.ne')
    (hYc.extension_mem_ZIrr η hηs)
    (by rw [hYc.extension_inner_eq η η hηs hηs, hinner η η (hYirr η hη) (hYirr η hη),
      ite_eq_left rfl])
    (hYc.extension_mem_ZIrr η' hη's)
    (by rw [hYc.extension_inner_eq η' η' hη's hη's, hinner η' η' (hYirr η' hη'Y) (hYirr η' hη'Y),
        ite_eq_left rfl])
    (hXc.extension_mem_ZIrr χ hχs)
    (by rw [hXc.extension_inner_eq χ χ hχs hχs, hinner χ χ (hXirr χ hχ) (hXirr χ hχ),
      ite_eq_left rfl])
    (hXc.extension_mem_ZIrr χ' hχ's)
    (by rw [hXc.extension_inner_eq χ' χ' hχ's hχ's, hinner χ' χ' (hXirr χ' hχ'X) (hXirr χ' hχ'X),
        ite_eq_left rfl])
    (by rw [hYc.extension_inner_eq η η' hηs hη's, hinner η η' (hYirr η hη) (hYirr η' hη'Y),
        ite_eq_right (fun h => hη'ne h.symm)])
    (by rw [hXc.extension_inner_eq χ χ' hχs hχ's, hinner χ χ' (hXirr χ hχ) (hXirr χ' hχ'X),
        ite_eq_right (fun h => hχ'ne h.symm)])
    (by -- hdiff
      rw [hXeq, hYeq, inner_conj_symm (hXc.extension xdiff) (hYc.extension ydiff),
        inner_extension_eq_inner_of_supported hyp.dade hXc hYc hx_supp hy_supp,
        hsrc0, star_zero])
    (by -- hα1
      rw [hYeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hYc hy_supp)
    (by -- hγδ1
      rw [hXeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hXc hx_supp)
  rw [inner_conj_symm (hYc.extension η) (hXc.extension χ), hconcl.1, star_zero]

/-- **Peterfalvi (6.8.1) `himg_ortho`** at the fixed Frobenius-case witnesses `τ₂ =
`Xset_centralCommutator_isCoherent`, `τ₁ = coherentYset` (specialization of
`inner_extension_Xset_centralCommutator_Yset_eq_zero_general`). -/
theorem inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ)
      (hyp.coherentYset.extension η) = 0 :=
  hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general hF
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset hχ hη

/-- **Case-(A)/c2 mirror of `inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius`.**
Same as the Frobenius original, with `hF` replaced by the certain-type case-(A) bundle
`cert`/`hK`/`hW1`/`hA`, and the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem inner_extension_Xset_centralCommutator_Yset_eq_zero_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension χ)
      (hyp.coherentYset.extension η) = 0 :=
  hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA hK hW1 hA
    (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp)
    hyp.coherentYset hχ hη

/-- **Span form of `himg_ortho`:** `⟨x^{τ₂}, η^{τ₁}⟩ = 0` for any `x ∈ ℤ[X(Zc)]` and `η ∈ Y`
(by `ℤ`-linearity from the per-member
`inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius`). -/
theorem inner_extension_span_Xset_centralCommutator_Yset_eq_zero_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {x : ClassFunction ↥L ℂ} (hx : x ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator))
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x)
      (hyp.coherentYset.extension η) = 0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem χ hχ =>
      exact hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius
        hF hHnonab hp hp3 hHp hχ hη
  | zero => rw [map_zero, ClassFunction.inner_zero_left]
  | add a b _ _ iha ihb => rw [map_add, ClassFunction.inner_add_left, iha, ihb, add_zero]
  | smul c a _ ih =>
      rw [map_zsmul,
        ← Int.cast_smul_eq_zsmul ℂ c
          ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension a),
        ClassFunction.inner_smul_left, ih, mul_zero]

/-- **Case-(A)/c2 mirror of
`inner_extension_span_Xset_centralCommutator_Yset_eq_zero_of_frobenius`.**
Same as the Frobenius original, with `hF` replaced by the certain-type case-(A) bundle
`cert`/`hK`/`hW1`/`hA`, and the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem inner_extension_span_Xset_centralCommutator_Yset_eq_zero_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {x : ClassFunction ↥L ℂ} (hx : x ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator))
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension x)
      (hyp.coherentYset.extension η) = 0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem χ hχ =>
      exact hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_c2_caseA
        hK hW1 hA hHnonab hp hp3 hHp hχ hη
  | zero => rw [map_zero, ClassFunction.inner_zero_left]
  | add a b _ _ iha ihb => rw [map_add, ClassFunction.inner_add_left, iha, ihb, add_zero]
  | smul c a _ ih =>
      rw [map_zsmul,
        ← Int.cast_smul_eq_zsmul ℂ c
          ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp
            hp3 hHp).extension
            a),
        ClassFunction.inner_smul_left, ih, mul_zero]

/-- **(6.8.1) Res-decomposition orthogonality** (spine steps 1–2): `Res^G_L(η^{τ₁})` is orthogonal
to every *supported* `X(Zc)`-combination.  For `η ∈ Y` and `x ∈ ℤ[X(Zc), H^#]` (supported),
`⟨Res^G_L(η^{τ₁}), x⟩_L = 0`.  By Dade reciprocity (`inner_tau_eq_inner_restrict`,
`⟨x^τ, η^{τ₁}⟩_G = ⟨x, Res_L(η^{τ₁})⟩_L`) and `x^τ = x^{τ₂}` (supported), this reduces to the span
form of `himg_ortho` (`⟨x^{τ₂}, η^{τ₁}⟩_G = 0`).  Hence the `X`-components of `Res^G_L(η^{τ₁})` are
all proportional to `dᵢ`, i.e. `Res^G_L(η^{τ₁}) = c·∑dᵢχᵢ + χ′` with `χ′ ⊥ X(Zc)` (mmd 04.8
L170). -/
theorem inner_restrict_extension_Yset_mem_span_Xset_eq_zero_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {x : ClassFunction ↥L ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) :
    ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) x = 0 := by
  classical
  have hrec := hyp.inner_tau_eq_inner_restrict hx.2 (hyp.coherentYset.extension η)
  have hτ : hyp.tau x =
      (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x :=
    ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extends_on_supported
      x hx).symm
  have h0 : ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x)
      (hyp.coherentYset.extension η) = 0 :=
    hyp.inner_extension_span_Xset_centralCommutator_Yset_eq_zero_of_frobenius
      hF hHnonab hp hp3 hHp hx.1 hη
  have hxr : ClassFunction.inner x
      (ClassFunction.restrict L (hyp.coherentYset.extension η)) = 0 := by
    rw [← hrec, hτ, h0]
  rw [inner_conj_symm x (ClassFunction.restrict L (hyp.coherentYset.extension η)), hxr, star_zero]

/-- **Case-(A)/c2 mirror of `inner_restrict_extension_Yset_mem_span_Xset_eq_zero_of_frobenius`.**
Same as the Frobenius original, with `hF` replaced by the certain-type case-(A) bundle
`cert`/`hK`/`hW1`/`hA`, and the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem inner_restrict_extension_Yset_mem_span_Xset_eq_zero_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {x : ClassFunction ↥L ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) :
    ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) x = 0 := by
  classical
  have hrec := hyp.inner_tau_eq_inner_restrict hx.2 (hyp.coherentYset.extension η)
  have hτ : hyp.tau x =
      (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp
        hp3 hHp).extension x :=
    ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3
      hHp).extends_on_supported x hx).symm
  have h0 : ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension x)
      (hyp.coherentYset.extension η) = 0 :=
    hyp.inner_extension_span_Xset_centralCommutator_Yset_eq_zero_c2_caseA
      hK hW1 hA hHnonab hp hp3 hHp hx.1 hη
  have hxr : ClassFunction.inner x
      (ClassFunction.restrict L (hyp.coherentYset.extension η)) = 0 := by
    rw [← hrec, hτ, h0]
  rw [inner_conj_symm x (ClassFunction.restrict L (hyp.coherentYset.extension η)), hxr, star_zero]

/-- **(6.8.1) Res `X`-coefficient proportionality** (mmd 04.8 L170).  For `χ, χ' ∈ X(Zc)` and
`R = Res^G_L(η^{τ₁})` (`η ∈ Y`), `χ'(1)·⟨R, χ⟩ = χ(1)·⟨R, χ'⟩` — the `X`-Fourier coefficients of `R`
are proportional to the degrees (`⟨R,χᵢ⟩ ∝ dᵢ`, the `Res^G_L(η₁^{τ₁}) = c∑dᵢχᵢ + χ′` decomposition).
Apply Res-orthogonality (`inner_restrict_extension_Yset_mem_span_Xset_eq_zero`) to the supported
integer combination `χ'(1)•χ − χ(1)•χ'` (degree-`0`, `sMember_smulDiffSupport_of_charValue_eq`). -/
theorem inner_restrict_extension_Yset_mul_degree_eq_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    (hχ' : χ' ∈ hyp.Xset hyp.centralCommutator) :
    (χ' 1) * ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ
      = (χ 1) * ClassFunction.inner
        (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ' := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  obtain ⟨d, _hd_pos, hd_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hXirr χ hχ⟩ : IrreducibleCharacter ↥L)
  obtain ⟨d', _hd'_pos, hd'_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ', hXirr χ' hχ'⟩ : IrreducibleCharacter ↥L)
  simp only [IrreducibleCharacter.coe_mk] at hd_eq hd'_eq
  have hx_supp : (d' • χ - d • χ') ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ d' χ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hχ)
      · rw [← Nat.cast_smul_eq_nsmul ℤ d χ']
        exact Submodule.smul_mem _ _ (Submodule.subset_span hχ')
    · exact hyp.sMember_smulDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ)
        (hyp.Xset_subset_S hχ') (by rw [hd_eq, hd'_eq]; ring)
  have hortho := hyp.inner_restrict_extension_Yset_mem_span_Xset_eq_zero_of_frobenius
    hF hHnonab hp hp3 hHp hη hx_supp
  rw [ClassFunction.inner_sub_right,
    ← Nat.cast_smul_eq_nsmul ℂ d' χ, ← Nat.cast_smul_eq_nsmul ℂ d χ',
    OddOrder.RepresentationTheory.inner_smul_right, OddOrder.RepresentationTheory.inner_smul_right,
    star_natCast, star_natCast, ← hd'_eq, ← hd_eq] at hortho
  exact sub_eq_zero.mp hortho

/-- **Case-(A)/c2 mirror of `inner_restrict_extension_Yset_mul_degree_eq_of_frobenius`.**  Same as
the Frobenius original, with `hF` replaced by the certain-type case-(A) bundle
`cert`/`hK`/`hW1`/`hA`,
and the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem inner_restrict_extension_Yset_mul_degree_eq_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    (hχ' : χ' ∈ hyp.Xset hyp.centralCommutator) :
    (χ' 1) * ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ
      = (χ 1) * ClassFunction.inner
        (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ' := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h
  obtain ⟨d, _hd_pos, hd_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hXirr χ hχ⟩ : IrreducibleCharacter ↥L)
  obtain ⟨d', _hd'_pos, hd'_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ', hXirr χ' hχ'⟩ : IrreducibleCharacter ↥L)
  simp only [IrreducibleCharacter.coe_mk] at hd_eq hd'_eq
  have hx_supp : (d' • χ - d • χ') ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ d' χ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hχ)
      · rw [← Nat.cast_smul_eq_nsmul ℤ d χ']
        exact Submodule.smul_mem _ _ (Submodule.subset_span hχ')
    · exact hyp.sMember_smulDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ)
        (hyp.Xset_subset_S hχ') (by rw [hd_eq, hd'_eq]; ring)
  have hortho := hyp.inner_restrict_extension_Yset_mem_span_Xset_eq_zero_c2_caseA
    hK hW1 hA hHnonab hp hp3 hHp hη hx_supp
  rw [ClassFunction.inner_sub_right,
    ← Nat.cast_smul_eq_nsmul ℂ d' χ, ← Nat.cast_smul_eq_nsmul ℂ d χ',
    OddOrder.RepresentationTheory.inner_smul_right, OddOrder.RepresentationTheory.inner_smul_right,
    star_natCast, star_natCast, ← hd'_eq, ← hd_eq] at hortho
  exact sub_eq_zero.mp hortho

/-- **(6.8.1) `η^{τ₁}` constancy value on `Zc^#`** (mmd 04.8 L168, the key constant).  For `η ∈ Y`,
`χ₁ ∈ X(Zc)` and `z ∈ Zc^#`, with `R = Res^G_L(η^{τ₁})`,
`χ₁(1)·(R(z) − R(1)) = -⟨R, χ₁⟩·|L|`.  Since the right side is independent of `z`, this shows `R`
(hence `η^{τ₁}`) is **constant on `Zc^#`** (and gives the value `R(z) − R(1) = -c|H|/a` with
`c = ⟨R,χ₁⟩`, `χ₁(1) = a|W₁|`, after clearing the denominator).

Proof: Fourier-expand `R = ∑_{a∈Irr L} ⟨R,a⟩•a` (`classFunction_eq_sum_inner_smul`); split the sum
by `Zc ⊄ ker`.  On `Zc ⊆ ker` (the non-`X` part) `a(z) = a(1)`, so those terms vanish.  On `X(Zc)`
the coefficient relation `χ₁(1)⟨R,a⟩ = a(1)⟨R,χ₁⟩` (`inner_restrict_extension_Yset_mul_degree_eq`)
factors out `⟨R,χ₁⟩`, leaving `⟨R,χ₁⟩·∑_{a∈X} a(1)(a(z)−a(1)) = ⟨R,χ₁⟩·(-|L|)`
(`sum_filter_degree_mul_charValue_sub_eq`). -/
theorem restrict_extension_Yset_degree_value_eq_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    (χ₁ 1) * ((ClassFunction.restrict L (hyp.coherentYset.extension η)) z
        - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1)
      = -(ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ₁)
          * (Nat.card ↥L : ℂ) := by
  classical
  have : (hyp.centralCommutator).Normal := hyp.centralCommutator_normal
  set R := ClassFunction.restrict L (hyp.coherentYset.extension η) with hRdef
  have hval : R z - R 1 = ∑ a : IrreducibleCharacter ↥L,
      ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
        ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1) := by
    conv_lhs => rw [OddOrder.RepresentationTheory.classFunction_eq_sum_inner_smul R]
    rw [ClassFunction.finset_sum_apply, ClassFunction.finset_sum_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ClassFunction.smul_apply, ClassFunction.smul_apply]; ring
  rw [hval, Finset.mul_sum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun a : IrreducibleCharacter ↥L => ¬ ((hyp.centralCommutator : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ)))]
  have hnot : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
        ¬ ¬ ((hyp.centralCommutator : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
        (χ₁ 1) * (ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
          ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1))) = 0 := by
    refine Finset.sum_eq_zero (fun a ha => ?_)
    rw [Finset.mem_filter, not_not] at ha
    have haz : (a : ClassFunction ↥L ℂ) z = (a : ClassFunction ↥L ℂ) 1 := by
      have hmem := ha.2 hz
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hmem
      exact hmem
    rw [haz, sub_self, mul_zero, mul_zero]
  rw [hnot, add_zero]
  have hfilter : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
        ¬ ((hyp.centralCommutator : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
        (χ₁ 1) * (ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
          ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1)))
      = (ClassFunction.inner R χ₁) *
        (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
          ¬ ((hyp.centralCommutator : Set ↥L) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
          (a : ClassFunction ↥L ℂ) 1 *
            ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    have haX : (a : ClassFunction ↥L ℂ) ∈ hyp.Xset hyp.centralCommutator := by
      rw [hyp.Xset_eq_irreducible_not_subset_characterKernel hyp.centralCommutator_le
        (fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)]
      exact ⟨a.isIrreducible, ha.2⟩
    have hrel := hyp.inner_restrict_extension_Yset_mul_degree_eq_of_frobenius
      hF hHnonab hp hp3 hHp hη haX hχ₁
    rw [← hRdef] at hrel
    linear_combination ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1) * hrel
  rw [hfilter, OddOrder.RepresentationTheory.sum_filter_degree_mul_charValue_sub_eq
    (N := hyp.centralCommutator) hz hz1]
  ring

/-- **Case-(A)/c2 mirror of `restrict_extension_Yset_degree_value_eq_of_frobenius`.**  Same as the
Frobenius original, with `hF` replaced by the certain-type case-(A) bundle `cert`/`hK`/`hW1`/`hA`,
and
the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem restrict_extension_Yset_degree_value_eq_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    (χ₁ 1) * ((ClassFunction.restrict L (hyp.coherentYset.extension η)) z
        - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1)
      = -(ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ₁)
          * (Nat.card ↥L : ℂ) := by
  classical
  have : (hyp.centralCommutator).Normal := hyp.centralCommutator_normal
  set R := ClassFunction.restrict L (hyp.coherentYset.extension η) with hRdef
  have hval : R z - R 1 = ∑ a : IrreducibleCharacter ↥L,
      ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
        ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1) := by
    conv_lhs => rw [OddOrder.RepresentationTheory.classFunction_eq_sum_inner_smul R]
    rw [ClassFunction.finset_sum_apply, ClassFunction.finset_sum_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ClassFunction.smul_apply, ClassFunction.smul_apply]; ring
  rw [hval, Finset.mul_sum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun a : IrreducibleCharacter ↥L => ¬ ((hyp.centralCommutator : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ)))]
  have hnot : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
        ¬ ¬ ((hyp.centralCommutator : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
        (χ₁ 1) * (ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
          ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1))) = 0 := by
    refine Finset.sum_eq_zero (fun a ha => ?_)
    rw [Finset.mem_filter, not_not] at ha
    have haz : (a : ClassFunction ↥L ℂ) z = (a : ClassFunction ↥L ℂ) 1 := by
      have hmem := ha.2 hz
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hmem
      exact hmem
    rw [haz, sub_self, mul_zero, mul_zero]
  rw [hnot, add_zero]
  have hfilter : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
        ¬ ((hyp.centralCommutator : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
        (χ₁ 1) * (ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
          ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1)))
      = (ClassFunction.inner R χ₁) *
        (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
          ¬ ((hyp.centralCommutator : Set ↥L) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
          (a : ClassFunction ↥L ℂ) 1 *
            ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    have haX : (a : ClassFunction ↥L ℂ) ∈ hyp.Xset hyp.centralCommutator := by
      rw [hyp.Xset_eq_irreducible_not_subset_characterKernel hyp.centralCommutator_le
        (fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h)]
      exact ⟨a.isIrreducible, ha.2⟩
    have hrel := hyp.inner_restrict_extension_Yset_mul_degree_eq_c2_caseA
      hK hW1 hA hHnonab hp hp3 hHp hη haX hχ₁
    rw [← hRdef] at hrel
    linear_combination ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1) * hrel
  rw [hfilter, OddOrder.RepresentationTheory.sum_filter_degree_mul_charValue_sub_eq
    (N := hyp.centralCommutator) hz hz1]
  ring

/-- **(6.8.1) `η^{τ₁}` is constant on `Zc^#`** (mmd 04.8 L168 conclusion).  For `η ∈ Y`, the
restriction `Res^G_L(η^{τ₁})` takes the same value at any two points of `Zc^#`.  Immediate from the
value identity `restrict_extension_Yset_degree_value_eq_of_frobenius` (whose right side
`-⟨R,χ₁⟩·|L|`
is independent of the point) and `χ₁(1) ≠ 0` (any anchor `χ₁ ∈ X(Zc)`, nonempty).  This is the exact
"character constant on `Z^#`" hypothesis of the (6.7) adapter `peterfalvi_67_centralCommutator`. -/
theorem restrict_extension_Yset_const_on_centralCommutator_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z z' : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1)
    (hz' : z' ∈ hyp.centralCommutator) (hz'1 : z' ≠ 1) :
    (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      = (ClassFunction.restrict L (hyp.coherentYset.extension η)) z' := by
  obtain ⟨χ₁, hχ₁⟩ := hyp.Xset_centralCommutator_nonempty hF hHnonab
  have hd : χ₁ 1 ≠ 0 := by
    obtain ⟨d, hd_pos, hd_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ₁, hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hd_eq
    rw [hd_eq]; exact_mod_cast hd_pos.ne'
  have hv := hyp.restrict_extension_Yset_degree_value_eq_of_frobenius
    hF hHnonab hp hp3 hHp hη hχ₁ hz hz1
  have hv' := hyp.restrict_extension_Yset_degree_value_eq_of_frobenius
    hF hHnonab hp hp3 hHp hη hχ₁ hz' hz'1
  have hcancel : (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
      = (ClassFunction.restrict L (hyp.coherentYset.extension η)) z'
        - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1 :=
    mul_left_cancel₀ hd (hv.trans hv'.symm)
  linear_combination hcancel

/-- **Case-(A)/c2 mirror of `restrict_extension_Yset_const_on_centralCommutator_of_frobenius`.**
Same as the Frobenius original, with `hF` replaced by the certain-type case-(A) bundle
`cert`/`hK`/`hW1`/`hA`, and the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem restrict_extension_Yset_const_on_centralCommutator_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z z' : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1)
    (hz' : z' ∈ hyp.centralCommutator) (hz'1 : z' ≠ 1) :
    (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      = (ClassFunction.restrict L (hyp.coherentYset.extension η)) z' := by
  obtain ⟨χ₁, hχ₁⟩ := hyp.Xset_centralCommutator_nonempty_c2_caseA hK hW1 hA hHnonab
  have hd : χ₁ 1 ≠ 0 := by
    obtain ⟨d, hd_pos, hd_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ₁, hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₁⟩
        : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hd_eq
    rw [hd_eq]; exact_mod_cast hd_pos.ne'
  have hv := hyp.restrict_extension_Yset_degree_value_eq_c2_caseA
    hK hW1 hA hHnonab hp hp3 hHp hη hχ₁ hz hz1
  have hv' := hyp.restrict_extension_Yset_degree_value_eq_c2_caseA
    hK hW1 hA hHnonab hp hp3 hHp hη hχ₁ hz' hz'1
  have hcancel : (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
      = (ClassFunction.restrict L (hyp.coherentYset.extension η)) z'
        - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1 :=
    mul_left_cancel₀ hd (hv.trans hv'.symm)
  linear_combination hcancel

end SibleyDadeHypothesis
end OddOrder.Peterfalvi.S08
