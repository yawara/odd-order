/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.FactorPairRelationDefinition
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Assembly

/-!
# Higman's Lemma 12: factor-pair dispatch over fixed coordinates

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 12, pp. 90–92.

This is the fixed-coordinate core of the prescribed-factor B/C/D dispatch.
The ambient actor generator, Frattini coordinate, primitive scalar, and both
factor coordinates are inputs.  Normalization may flip either factor model,
but it never replaces the common ambient coordinate.

This form is needed in Higman's Lemma 13, where the three pairwise joins must
all be analyzed over one ambient `Φ(P)` Singer datum.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

section /- Higman Lemma 12 (pp. 90–92) -/

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.RepresentationTheory
open OddOrder.Isaacs.Ch03
open Module
open scoped IsMulCommutative

noncomputable section

universe uP


namespace XiLengthThreeTypeAFactorData
/-- **Higman Lemma 12 (pp. 90–92), fixed-coordinate parameter dispatch.**

Normalize a supplied pair of factor coordinates and return the oriented
B/C/D parameter relation without choosing a new ambient Singer datum. -/
theorem exists_normalizedFactorPairRelation_with_witnesses_of_fixedCoordinates
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (factors : XiLengthThreeTypeAFactorData P Y) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    let hEA : IsElementaryAbelian 2 ↑(frattini P) :=
      frattini_isElementaryAbelian_of_xiLengthThree
        hP hncomm hmulti hxi hlen hprime
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) :=
      hEA.zmodModule
    ∀ {n : Nat} (c : Y)
      (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
      (nu : GaloisField 2 n),
      2 ≤ n →
      IsPrimitiveRoot nu (2 ^ n - 1) →
      ePhi.conj (elabRepresentation 2 hPhiInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
      ∀ (_left : FactorCoordinateData
          factors.left_invariant factors.frattini_lt_left.le c ePhi nu)
        (_right : FactorCoordinateData
          factors.right_invariant factors.frattini_lt_right.le c ePhi nu),
        ∃ (left' : FactorCoordinateData
            factors.left_invariant factors.frattini_lt_left.le c ePhi nu)
          (right' : FactorCoordinateData
            factors.right_invariant factors.frattini_lt_right.le c ePhi nu),
          nu = left'.lambda * left'.theta left'.lambda ∧
          nu = right'.lambda * right'.theta right'.lambda ∧
          (left'.theta = 1 ∨
            ∃ rL : ℕ, 0 < rL ∧ 2 * rL ≤ n ∧
              left'.theta =
                frobeniusEquiv (GaloisField 2 n) 2 ^ rL ∧
              Odd (orderOf left'.theta)) ∧
          (right'.theta = 1 ∨
            ∃ rR : ℕ, 0 < rR ∧ 2 * rR ≤ n ∧
              right'.theta =
                frobeniusEquiv (GaloisField 2 n) 2 ^ rR ∧
              Odd (orderOf right'.theta)) ∧
          NormalizedFactorPairRelation n left'.theta right'.theta := by
  classical
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  have hEA : IsElementaryAbelian 2 ↑(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  intro n c ePhi nu hnTwo hnuPrim hconj dataL0 dataR0
  have hK0 :=
    lowerCentralLayerKernel_zero_eq_frattini_subgroupOf_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hK1 := lowerCentralLayerKernel_one_eq_bot_of_xiLengthThree
    hP hncomm hmulti hxi hlen hprime
  have hterm := lowerCentralTerm_one_eq_frattini_of_xiLengthThree
    hP hncomm hmulti hxi hlen hprime
  have hSq := lowerCentralSquaresLieInSecond_of_xiLengthThree
    hP hncomm hmulti hxi hlen hprime
  have hAgemo := agemo_one_eq_frattini_of_xiLengthThree
    hP hncomm hmulti hxi hlen hprime
  have hPhiNeBot : frattini P ≠ (⊥ : Subgroup P) := by
    intro hPhiBot
    have hcommBot : _root_.commutator P = ⊥ :=
      le_bot_iff.mp
        ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
          (le_of_eq hPhiBot))
    exact hncomm ((commutator_eq_bot_iff P).mp hcommBot)
  have hinvPhi : involutions P ⊆ frattini P :=
    involutions_subset_of_nontrivial_invariant hP Y hxi.transitive
      (IsAInvariant.of_characteristic Y.subtype) hPhiNeBot
  have hn0 : n ≠ 0 := by omega
  have n_pos : 0 < n := by omega
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 n hn0
  have hordnu : orderOf nu = 2 ^ n - 1 := hnuPrim.eq_orderOf.symm
  have hNpos : 0 < 2 ^ n - 1 := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) n_pos
    omega
  have hnuNe : nu ≠ 0 := by
    intro h0
    have hone : nu ^ (2 ^ n - 1) = 1 := by
      rw [← hordnu]
      exact pow_orderOf_eq_one nu
    rw [h0, zero_pow (by omega)] at hone
    exact zero_ne_one hone
  have hpowcard : ∀ x : GaloisField 2 n, x ≠ 0 →
      x ^ (2 ^ n - 1) = 1 := by
    intro x hxne
    have hfin : Finite (GaloisField 2 n) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one x hxne
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  have horderF : orderOf (frobeniusEquiv (GaloisField 2 n) 2) = n :=
    orderOf_frobeniusEquiv_eq_of_card_eq_two_pow n
      (by simpa [Nat.card_eq_fintype_card] using hcard)
  have hfrobcong : ∀ a b : ℕ, (a : ZMod n) = (b : ZMod n) →
      (frobeniusEquiv (GaloisField 2 n) 2) ^ a =
        (frobeniusEquiv (GaloisField 2 n) 2) ^ b := by
    intro a b hab
    rw [pow_eq_pow_iff_modEq, horderF]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hab
  have normalize : ∀ {S : Subgroup P} {hSinv : IsAInvariant Y.subtype S}
      {hPhiS : frattini P ≤ S}
      (data : FactorCoordinateData hSinv hPhiS c ePhi nu),
      ∃ data' : FactorCoordinateData hSinv hPhiS c ePhi nu,
        nu = data'.lambda * data'.theta data'.lambda ∧
        (data'.theta = 1 ∨
          ∃ r : ℕ, 0 < r ∧ 2 * r ≤ n ∧
            data'.theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r ∧
            Odd (orderOf data'.theta)) := by
    intro S hSinv hPhiS data
    exact data.exists_normalized_frobenius_le_half hn0
  obtain ⟨dL, hnuL, hLcase⟩ := normalize dataL0
  obtain ⟨dR, hnuR, hRcase⟩ := normalize dataR0
  have hLnormal := hLcase
  have hRnormal := hRcase
  set L := dL.toInclusionData hEA ePhi hK1 hterm hSq hAgemo hK0
  set R := dR.toInclusionData hEA ePhi hK1 hterm hSq hAgemo hK0
  have hequivLR : ∀ α β : GaloisField 2 n,
      mixedTermBilinear L R (dL.lambda * α) (dR.lambda * β) =
        nu * mixedTermBilinear L R α β := fun α β =>
    mixedTermBilinear_lambda_equivariance hEA ePhi dL dR hK1 hterm hSq
      hAgemo hK0 hconj α β
  have hM0LR : ∃ α β : GaloisField 2 n,
      mixedTermBilinear L R α β ≠ 0 :=
    exists_mixedTermBilinear_ne_zero factors L R hxi hinvPhi
  have typeCDimension : ∀ {r : ℕ}
      (M : GaloisField 2 n →ₗ[ZMod 2]
        (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n))
      (lam mu : GaloisField 2 n),
      0 < r → 2 * r ≤ n →
      lam ^ (1 + 2 ^ r) = nu → mu ^ 2 = nu →
      (∀ α β, M (lam * α) (mu * β) = nu * M α β) →
      (∃ α β, M α β ≠ 0) →
      2 * r + 1 = n := by
    intro r M lam mu hr h2r hlamnu hmunu hequiv hM0
    have hlamne : lam ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by simp)] at hlamnu
      exact hnuNe hlamnu.symm
    have hmune : mu ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num)] at hmunu
      exact hnuNe hmunu.symm
    have hordlam : orderOf lam = 2 ^ n - 1 :=
      (orderOf_eq_and_coprime_of_pow_eq_orderOf hNpos
        (by simp : 1 + 2 ^ r ≠ 0) hordnu hlamnu
        (hpowcard lam hlamne)).1
    exact (mixedTerm_monomial_typeC hr h2r M lam mu nu hordlam
      hlamnu hmunu (hpowcard mu hmune) hequiv hM0).1
  rcases hLcase with hthetaL1 | ⟨rL, hrL0, hrLhalf, hthetaLfrob, -⟩
  · rcases hRcase with hthetaR1 | ⟨rR, hrR0, hrRhalf, hthetaRfrob, -⟩
    · exact ⟨dL, dR, hnuL, hnuR, hLnormal, hRnormal, .typeB (hthetaL1.trans hthetaR1.symm)⟩
    · have hleftSq : dL.lambda ^ 2 = nu := by
        have htheta : dL.theta dL.lambda = dL.lambda := by
          rw [hthetaL1, RingAut.one_apply]
        calc
          dL.lambda ^ 2 = dL.lambda * dL.lambda := pow_two _
          _ = dL.lambda * dL.theta dL.lambda := by rw [htheta]
          _ = nu := hnuL.symm
      have hrightNorm : dR.lambda ^ (1 + 2 ^ rR) = nu := by
        have htheta :
            dR.theta dR.lambda = dR.lambda ^ 2 ^ rR := by
          rw [hthetaRfrob, frobeniusEquiv_pow_apply]
        calc
          dR.lambda ^ (1 + 2 ^ rR)
              = dR.lambda * dR.lambda ^ 2 ^ rR := by
                rw [pow_add, pow_one]
          _ = dR.lambda * dR.theta dR.lambda := by rw [htheta]
          _ = nu := hnuR.symm
      have hequivRL : ∀ α β : GaloisField 2 n,
          mixedTermBilinear R L (dR.lambda * α) (dL.lambda * β) =
            nu * mixedTermBilinear R L α β := fun α β =>
        mixedTermBilinear_lambda_equivariance hEA ePhi dR dL hK1 hterm hSq
          hAgemo hK0 hconj α β
      have hM0RL : ∃ α β : GaloisField 2 n,
          mixedTermBilinear R L α β ≠ 0 := by
        obtain ⟨α, β, hne⟩ := hM0LR
        refine ⟨β, α, ?_⟩
        rw [mixedTermBilinear_swap L R α β]
        exact hne
      have hdim := typeCDimension (mixedTermBilinear R L)
        dR.lambda dL.lambda hrR0 hrRhalf hrightNorm hleftSq
        hequivRL hM0RL
      exact ⟨dL, dR, hnuL, hnuR, hLnormal, hRnormal,
        .typeCRight rR hrR0 hthetaL1 hthetaRfrob hdim⟩
  · rcases hRcase with hthetaR1 | ⟨rR, hrR0, hrRhalf, hthetaRfrob, -⟩
    · have hrightSq : dR.lambda ^ 2 = nu := by
        have htheta : dR.theta dR.lambda = dR.lambda := by
          rw [hthetaR1, RingAut.one_apply]
        calc
          dR.lambda ^ 2 = dR.lambda * dR.lambda := pow_two _
          _ = dR.lambda * dR.theta dR.lambda := by rw [htheta]
          _ = nu := hnuR.symm
      have hleftNorm : dL.lambda ^ (1 + 2 ^ rL) = nu := by
        have htheta :
            dL.theta dL.lambda = dL.lambda ^ 2 ^ rL := by
          rw [hthetaLfrob, frobeniusEquiv_pow_apply]
        calc
          dL.lambda ^ (1 + 2 ^ rL)
              = dL.lambda * dL.lambda ^ 2 ^ rL := by
                rw [pow_add, pow_one]
          _ = dL.lambda * dL.theta dL.lambda := by rw [htheta]
          _ = nu := hnuL.symm
      have hdim := typeCDimension (mixedTermBilinear L R)
        dL.lambda dR.lambda hrL0 hrLhalf hleftNorm hrightSq
        hequivLR hM0LR
      exact ⟨dL, dR, hnuL, hnuR, hLnormal, hRnormal,
        .typeCLeft rL hrL0 hthetaLfrob hthetaR1 hdim⟩
    · by_cases hre : rL = rR
      · have hthetaEq : dL.theta = dR.theta := by
          rw [hthetaLfrob, hthetaRfrob, hre]
        exact ⟨dL, dR, hnuL, hnuR, hLnormal, hRnormal, .typeB hthetaEq⟩
      · have hleftNorm : dL.lambda ^ (1 + 2 ^ rL) = nu := by
          have htheta :
              dL.theta dL.lambda = dL.lambda ^ 2 ^ rL := by
            rw [hthetaLfrob, frobeniusEquiv_pow_apply]
          calc
            dL.lambda ^ (1 + 2 ^ rL)
                = dL.lambda * dL.lambda ^ 2 ^ rL := by
                  rw [pow_add, pow_one]
            _ = dL.lambda * dL.theta dL.lambda := by rw [htheta]
            _ = nu := hnuL.symm
        have hrightNorm : dR.lambda ^ (1 + 2 ^ rR) = nu := by
          have htheta :
              dR.theta dR.lambda = dR.lambda ^ 2 ^ rR := by
            rw [hthetaRfrob, frobeniusEquiv_pow_apply]
          calc
            dR.lambda ^ (1 + 2 ^ rR)
                = dR.lambda * dR.lambda ^ 2 ^ rR := by
                  rw [pow_add, pow_one]
            _ = dR.lambda * dR.theta dR.lambda := by rw [htheta]
            _ = nu := hnuR.symm
        have hrLn : rL < n := by omega
        have hrRn : rR < n := by omega
        have hrLz : (rL : ZMod n) ≠ 0 := by
          rw [Ne, natCast_zmod_eq_zero_iff_mod_eq_zero,
            Nat.mod_eq_of_lt hrLn]
          omega
        have hrRz : (rR : ZMod n) ≠ 0 := by
          rw [Ne, natCast_zmod_eq_zero_iff_mod_eq_zero,
            Nat.mod_eq_of_lt hrRn]
          omega
        have hrszNe : (rL : ZMod n) ≠ (rR : ZMod n) := by
          intro h
          apply hre
          have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
          rwa [Nat.ModEq, Nat.mod_eq_of_lt hrLn, Nat.mod_eq_of_lt hrRn]
            at hmod
        have hsum : rL + rR < n := by omega
        have hrsz : (rL : ZMod n) + (rR : ZMod n) ≠ 0 := by
          rw [← Nat.cast_add, Ne, natCast_zmod_eq_zero_iff_mod_eq_zero,
            Nat.mod_eq_of_lt hsum]
          omega
        rcases mixedTerm_monomial_typeD n_pos hrLz hrRz hrsz hrszNe
            (mixedTermBilinear L R) dL.lambda dR.lambda nu hordnu
            hleftNorm hrightNorm hequivLR hM0LR with
          ⟨hs2r, h5r, -⟩ | ⟨hr2s, h5s, -⟩
        · have hthetaR2 : dR.theta = dL.theta ^ 2 := by
            rw [hthetaRfrob, hthetaLfrob, ← pow_mul]
            exact hfrobcong rR (rL * 2)
              (by push_cast; linear_combination hs2r)
          exact ⟨dL, dR, hnuL, hnuR, hLnormal, hRnormal,
            .typeDLeft rL hrL0 hrLhalf hthetaLfrob hthetaR2 h5r⟩
        · have hthetaL2 : dL.theta = dR.theta ^ 2 := by
            rw [hthetaLfrob, hthetaRfrob, ← pow_mul]
            exact hfrobcong rL (rR * 2)
              (by push_cast; linear_combination hr2s)
          exact ⟨dL, dR, hnuL, hnuR, hLnormal, hRnormal,
            .typeDRight rR hrR0 hrRhalf hthetaRfrob hthetaL2 h5s⟩

end XiLengthThreeTypeAFactorData

namespace XiLengthThreeTypeAFactorData

/-- **Higman Lemma 12 (pp. 90–92), fixed-coordinate parameter dispatch.**

Compatibility view of
`exists_normalizedFactorPairRelation_with_witnesses_of_fixedCoordinates`
that retains the original relation-only result. -/
theorem exists_normalizedFactorPairRelation_of_fixedCoordinates
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (factors : XiLengthThreeTypeAFactorData P Y) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    let hEA : IsElementaryAbelian 2 ↑(frattini P) :=
      frattini_isElementaryAbelian_of_xiLengthThree
        hP hncomm hmulti hxi hlen hprime
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) :=
      hEA.zmodModule
    ∀ {n : Nat} (c : Y)
      (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
      (nu : GaloisField 2 n),
      2 ≤ n →
      IsPrimitiveRoot nu (2 ^ n - 1) →
      ePhi.conj (elabRepresentation 2 hPhiInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
      ∀ (_left : FactorCoordinateData
          factors.left_invariant factors.frattini_lt_left.le c ePhi nu)
        (_right : FactorCoordinateData
          factors.right_invariant factors.frattini_lt_right.le c ePhi nu),
        ∃ (left' : FactorCoordinateData
            factors.left_invariant factors.frattini_lt_left.le c ePhi nu)
          (right' : FactorCoordinateData
            factors.right_invariant factors.frattini_lt_right.le c ePhi nu),
          NormalizedFactorPairRelation n left'.theta right'.theta := by
  classical
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  have hEA : IsElementaryAbelian 2 ↑(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  intro n c ePhi nu hnTwo hnuPrim hconj dataL0 dataR0
  obtain ⟨dL, dR, -, -, -, -, hrelation⟩ :=
    factors.exists_normalizedFactorPairRelation_with_witnesses_of_fixedCoordinates
      hP hncomm hmulti hxi hlen hprime
      c ePhi nu hnTwo hnuPrim hconj dataL0 dataR0
  exact ⟨dL, dR, hrelation⟩

end XiLengthThreeTypeAFactorData

end


end

end OddOrder.Higman.Suzuki2Groups
