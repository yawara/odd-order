/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_NonExistenceG.TGapProjectionResidual
import OddOrder.Peterfalvi.S07_CoherenceGalois

/-!
# Peterfalvi (11.9)(a): Galois transport of the T-side bridge

The Galois transform of a Dade bridge differs from the original bridge by the
Dade image of the source-character correction.  This is Coq `FTtype34_structure`
lemma `aut_phi`, isolated before the cyclotomic transitivity argument.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The canonical prime-TI anchor `primeTIred 0 = Ind 1` is fixed by every
coefficient automorphism.  This is the source-side fixed point used in
Peterfalvi Galois transport identity. -/
theorem primeTIred_zero_mapRingEquiv
    {S : Type*} [Group S] [Fintype S]
    {PU : Subgroup S} [Fintype PU] [Invertible (Nat.card PU : Complex)]
    {q p : Nat} [NeZero q] [NeZero p]
    (D : PrimeTIResidueData S PU q p) (sigma : RingEquiv Complex Complex) :
    ClassFunction.mapRingEquiv sigma (D.primeTIred 0) = D.primeTIred 0 := by
  rw [(D.cfInd_prTIres 0).symm, D.prTIres0, ClassFunction.mapRingEquiv_induce]
  congr 1
  ext x
  simp [ClassFunction.mapRingEquiv_apply, trivialClassFunction_apply]

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), Galois bridge decomposition** (Coq `aut_phi`).
If the prime-TI anchor `ν₀` is fixed by a coefficient automorphism `σ`, then

`σ(τ_T(ν₀ - ζ)) = τ_T(ν₀ - ζ) + τ_T(ζ - σζ)`.

The only character-theoretic input is the supportedness of `ν₀ - ζ`: it lets
the explicit Dade map commute with `σ`.  The remaining identity is linearity. -/
theorem tSideDadeMap_mapRingEquiv_bridge [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (σc : ℂ ≃+* ℂ)
    {ν0 ζ : ClassFunction ↥hyp.base.T ℂ}
    (hν0 : ClassFunction.mapRingEquiv σc ν0 = ν0)
    (hbridgeSupp : (ν0 - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.mapRingEquiv σc (tSideDadeMap hyp hG (ν0 - ζ)) =
      tSideDadeMap hyp hG (ν0 - ζ) +
        tSideDadeMap hyp hG (ζ - ClassFunction.mapRingEquiv σc ζ) := by
  let side := (tSideDadeSupport_nonempty hG hyp).some
  change ClassFunction.mapRingEquiv σc
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap side.dade
        (side.dade.fullDadeIsometryData side.hconj) (ν0 - ζ)) = _
  rw [← OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mapRingEquiv_comm
    side.dade (side.dade.fullDadeIsometryData side.hconj) σc hbridgeSupp]
  change tSideDadeMap hyp hG (ClassFunction.mapRingEquiv σc (ν0 - ζ)) = _
  rw [← map_add]
  congr 1
  rw [ClassFunction.mapRingEquiv_sub, hν0]
  abel

end OddOrder.Peterfalvi.S16
