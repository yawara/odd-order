/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S11_GaloisFieldModel
import OddOrder.Peterfalvi.S15_CaseAContradiction

/-!
# Peterfalvi (14.6) — the S-side Galois-field model

Peterfalvi (14.6) eliminates case (9.7.a) for the maximal subgroup `S`; the remaining
case (9.7.b) identifies the chief factor with the additive group of
`GF(p^q)`, with `U` acting through an injective subgroup of its unit group.

The §9 realization is initially stated for the abstract chief quotient `H/H₀`
and the complement in `TypesIIIIIIVSetup`.  Here `H₀ = ⊥`, `H = P`, and
the abstract complement is the named subgroup `U`, so the realization is
transported to the concrete S-side conjugation action.  The branch-independent
dispatcher combines this transport with the already proved case-A contradiction.

The conclusions `c = 1`, `q = 3`, and `u = (p - 1)² / 4`, and the
type-I maximal subgroup over `N_G(U)`, remain explicit inputs.  Thus this leaf
does not depend on the analytic producer currently being relayered.

Peterfalvi, *Character Theory for the Odd Order Theorem*, (14.6), pp. 87–88.
Coq reference: `coq/theories/PFsection14.v`, `typeP_Galois_P`.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

section /- (14.6): transport of the case-(9.7.b) model to the named S-instance (pp. 87–88) -/

/-! ## The named conjugation action -/

/-- The named complement `U` normalizes the Fitting kernel `P = S_F`.

Indeed `U ≤ S'`, while `S` normalizes its maximum nilpotent normal Hall subgroup. -/
theorem Hypothesis.U_le_normalizer_P (hyp : Hypothesis (G := G)) :
    hyp.U ≤ Subgroup.normalizer hyp.P := by
  have hU_le_deriv : hyp.U ≤ derivedInG hyp.S := by
    rw [hyp.S_deriv_eq_PU]
    exact le_sup_right
  have hderiv_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hS_le_norm : hyp.S ≤ Subgroup.normalizer hyp.P := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  exact (hU_le_deriv.trans hderiv_le_S).trans hS_le_norm

/-- Conjugation by the named complement `U` preserves the named kernel `P`. -/
theorem Hypothesis.conj_mem_P (hyp : Hypothesis (G := G))
    (v : ↥hyp.U) (x : ↥hyp.P) :
    (v : G) * (x : G) * (v : G)⁻¹ ∈ hyp.P := by
  have hv : (v : G) ∈ Subgroup.normalizer hyp.P := hyp.U_le_normalizer_P v.2
  exact (Subgroup.mem_normalizer_iff.mp hv (x : G)).mp x.2

private noncomputable def galoisFieldCongr
    {p p' q q' : ℕ} [Fact p.Prime] [Fact p'.Prime]
    (hp : p = p') (hq : q = q') :
    GaloisField p q ≃+* GaloisField p' q' := by
  subst p'
  subst q'
  exact RingEquiv.refl _

/-! ## Case (9.7.b) -/

/-- **Peterfalvi (9.7.b)/(14.6), the S-side Galois-field model.**

If the §9 Clifford dichotomy is in case (b) and `c = |C_U(P)| = 1`, then
there are an additive equivalence `P ≃+ GF(p^q)` and an injective homomorphism
`U → GF(p^q)ˣ` which linearize the actual conjugation action of `U` on `P`.

The proof transports `caseB_exists_galoisField_repr_of_cSub_eq_bot` along
`H₀ = ⊥`, `H = P`, the identification of the abstract and named complements,
and the equalities of the two field parameters. -/
theorem caseB_exists_sSide_galoisField_repr_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData
      (hyp.toTypesIIIIIIVSetupS hG)}
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataS hG chief))
    (hc : hyp.c = 1) :
    letI : Fact hyp.p.Prime := ⟨hyp.p_prime⟩
    ∃ (e : Additive ↥hyp.P ≃+ GaloisField hyp.p hyp.q)
      (μ : ↥hyp.U →* (GaloisField hyp.p hyp.q)ˣ),
      Function.Injective μ ∧
      ∀ (v : ↥hyp.U) (x : ↥hyp.P),
        e (Additive.ofMul
            (⟨(v : G) * (x : G) * (v : G)⁻¹, hyp.conj_mem_P v x⟩ : ↥hyp.P))
          = ((μ v : (GaloisField hyp.p hyp.q)ˣ) : GaloisField hyp.p hyp.q) *
            e (Additive.ofMul x) := by
  classical
  letI : Fact hyp.p.Prime := ⟨hyp.p_prime⟩
  letI : Fact chief.p.Prime := ⟨chief.p_prime⟩
  have hN : chief.N = ⊥ := hyp.toTypesIIIIIIVSetupS_chief_N_eq_bot hG chief
  have hC :
      OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief = ⊥ := by
    rw [hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief]
    apply Subgroup.eq_bot_of_card_eq
    rw [← hyp.c_eq_card_C, hc]
  have hp : chief.p = hyp.p := hyp.chiefFactorS_p_eq hG chief
  have hq : (hyp.toTypesIIIIIIVSetupS hG).q = hyp.q :=
    hyp.toTypesIIIIIIVSetupS_q_eq hG
  obtain ⟨e₀, μ₀, hμ₀, hcompat₀⟩ :=
    OddOrder.Peterfalvi.S11.caseB_exists_galoisField_repr_of_cSub_eq_bot
      (hyp.mkSection11CharacterDataS hG chief) caseB hC
  have hH : (hyp.toTypesIIIIIIVSetupS hG).H = hyp.P := by
    change hyp.Sdata.H = hyp.P
    rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hU : (hyp.toTypesIIIIIIVSetupS hG).typeP.U = hyp.U :=
    hyp.Sdata_U_eq
  let eHP : ↥(hyp.toTypesIIIIIIVSetupS hG).H ⧸ chief.N ≃* ↥hyp.P :=
    ((QuotientGroup.quotientMulEquivOfEq hN).trans
      (QuotientGroup.quotientBot
        (G := ↥(hyp.toTypesIIIIIIVSetupS hG).H))).trans
      (MulEquiv.subgroupCongr hH)
  let eU : ↥(hyp.toTypesIIIIIIVSetupS hG).typeP.U ≃* ↥hyp.U :=
    MulEquiv.subgroupCongr hU
  let eF : GaloisField chief.p (hyp.toTypesIIIIIIVSetupS hG).q ≃+*
      GaloisField hyp.p hyp.q := galoisFieldCongr hp hq
  let e : Additive ↥hyp.P ≃+ GaloisField hyp.p hyp.q :=
    (eHP.toAdditive.symm.trans e₀).trans eF.toAddEquiv
  let eFUnits :
      (GaloisField chief.p (hyp.toTypesIIIIIIVSetupS hG).q)ˣ ≃*
        (GaloisField hyp.p hyp.q)ˣ :=
    Units.mapEquiv eF.toMulEquiv
  let μ : ↥hyp.U →* (GaloisField hyp.p hyp.q)ˣ :=
    eFUnits.toMonoidHom.comp (μ₀.comp eU.symm.toMonoidHom)
  refine ⟨e, μ, eFUnits.injective.comp (hμ₀.comp eU.symm.injective), ?_⟩
  intro v x
  have h := hcompat₀ (eU.symm v) (eHP.symm x)
  have eHP_symm_apply (y : ↥hyp.P) :
      eHP.symm y = QuotientGroup.mk ((MulEquiv.subgroupCongr hH).symm y) := by
    apply eHP.injective
    simp [eHP]
  have hact :
      OddOrder.Peterfalvi.S11.uActionHom (hyp.toTypesIIIIIIVSetupS hG) chief
          ((Subgroup.subgroupOfEquivOfLe
            (le_sup_left : (hyp.toTypesIIIIIIVSetupS hG).typeP.U ≤
              (hyp.toTypesIIIIIIVSetupS hG).typeP.U ⊔
                (hyp.toTypesIIIIIIVSetupS hG).typeP.W1)).symm (eU.symm v))
          (eHP.symm x)
        = eHP.symm
          ⟨(v : G) * (x : G) * (v : G)⁻¹, hyp.conj_mem_P v x⟩ := by
    apply eHP.injective
    rw [eHP_symm_apply x, eHP_symm_apply]
    rw [OddOrder.Peterfalvi.S11.uActionHom, MonoidHom.comp_apply,
      OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply]
    simp only [eHP, MulEquiv.trans_apply,
      QuotientGroup.quotientMulEquivOfEq_mk]
    simp only [QuotientGroup.quotientBot]
    congr 1
  rw [hact] at h
  have h' := congrArg eF h
  simpa [e, μ, eFUnits, eF, eHP, eU,
    OddOrder.Peterfalvi.S11.uActionHom,
    OddOrder.Peterfalvi.S11.typeP_conjAction_apply] using h'

/-! ## The branch-independent (14.6) assembly -/

/-- **Peterfalvi (14.6), S-side case (9.7.b) with explicit sharp parameters.**

For the explicit conclusions `c = 1`, `q = 3`, and
`u = (p - 1)² / 4` of (13.12)/(13.13), and the type-I maximal subgroup over
`N_G(U)` constructed in (13.17)/(14.5), the named S-side Galois-field model
exists.  The Clifford case (a) is impossible by the prime contradiction; case
(b) is the transported model above.

The explicit inputs keep this theorem independent of the analytic producer of
the parameter equalities. -/
theorem sSide_galoisField_repr_of_parameters_and_typeIOverNormalizerData
    [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hc : hyp.c = 1) (hq : hyp.q = 3)
    (hu : hyp.u = (hyp.p - 1) ^ 2 / 4)
    (data : TypeIOverNormalizerData hyp) :
    letI : Fact hyp.p.Prime := ⟨hyp.p_prime⟩
    ∃ (e : Additive ↥hyp.P ≃+ GaloisField hyp.p hyp.q)
      (μ : ↥hyp.U →* (GaloisField hyp.p hyp.q)ˣ),
      Function.Injective μ ∧
      ∀ (v : ↥hyp.U) (x : ↥hyp.P),
        e (Additive.ofMul
            (⟨(v : G) * (x : G) * (v : G)⁻¹, hyp.conj_mem_P v x⟩ : ↥hyp.P))
          = ((μ v : (GaloisField hyp.p hyp.q)ˣ) : GaloisField hyp.p hyp.q) *
            e (Additive.ofMul x) := by
  classical
  letI : Fact hyp.p.Prime := ⟨hyp.p_prime⟩
  obtain ⟨chief, -⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
      (hyp.toTypesIIIIIIVSetupS hG)
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG
      (hyp.mkSection11CharacterDataS hG chief) with hA | hB
  · obtain ⟨caseA⟩ := hA
    exact
      (caseA_false_of_parameters_and_typeIOverNormalizerData
        hG hyp caseA hc hq hu data).elim
  · obtain ⟨caseB⟩ := hB
    exact caseB_exists_sSide_galoisField_repr_of_c_eq_one
      hG hyp caseB hc

end

end OddOrder.Peterfalvi.S15
