/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.SummandIsomorphism
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.SupportPinning
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.NormalizedFactorParameterCoherence

/-!
# Higman Lemma 13: normalized factor-coordinate coherence

G. Higman, *Suzuki 2-groups*, pp. 90--94.  In the exponent-two branch of
Lemma 13, the same actual factor occurs in two pairwise joins.  Compatible
group-level and zeroth lower-central-layer identifications force the
normalized Frobenius automorphisms in the two coordinate systems to agree.

The noncommutative core first identifies the two quotient eigenvalues up to a
Frobenius power, then applies the arithmetic coherence theorem to their common
kernel eigenvalue.  The inclusive theorem also rules out a mixed
commutative/noncommutative pair because the factors are isomorphic as groups.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

local instance normalizedThetaLayerCommGroup
    (H : Type uP) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

local instance normalizedThetaLayerModule
    (H : Type uP) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 13, normalized factor-coordinate coherence
(noncommutative case).**  Normalized noncommutative factor parameters agree
across an equivariant identification of their zeroth lower-central layers. -/
theorem NoncommutativeFactorCoordinateData.theta_eq_of_normalized_equivariant
    {P Q : Type uP} [Group P] [Group Q]
    {Y : Subgroup (MulAut P)} {Z : Subgroup (MulAut Q)}
    [IsMulCommutative (frattini P)]
    [Module (ZMod 2) (Additive (frattini P))]
    [IsMulCommutative (frattini Q)]
    [Module (ZMod 2) (Additive (frattini Q))]
    {S : Subgroup P} {T : Subgroup Q}
    {hSinv : IsAInvariant Y.subtype S}
    {hTinv : IsAInvariant Z.subtype T}
    {hPhiS : frattini P ≤ S} {hPhiT : frattini Q ≤ T}
    {c : Y} {d : Z} {n : ℕ}
    {ePhiS : Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {ePhiT : Additive (frattini Q) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (dataS : NoncommutativeFactorCoordinateData
      hSinv hPhiS c ePhiS nu)
    (dataT : NoncommutativeFactorCoordinateData
      hTinv hPhiT d ePhiT nu)
    (hn : n ≠ 0)
    {r s : ℕ} (hr0 : 0 < r) (hrhalf : 2 * r ≤ n)
    (hthetaS : dataS.theta =
      frobeniusEquiv (GaloisField 2 n) 2 ^ r)
    (hs0 : 0 < s) (hshalf : 2 * s ≤ n)
    (hthetaT : dataT.theta =
      frobeniusEquiv (GaloisField 2 n) 2 ^ s)
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
    (e : Additive (lowerCentralLayer S 0) ≃ₗ[ZMod 2]
      Additive (lowerCentralLayer T 0))
    (hequiv : ∀ x, e
      (lowerCentralLayerRepresentation hSinv.restrict 0 c x) =
        lowerCentralLayerRepresentation hTinv.restrict 0 d (e x)) :
    dataS.theta = dataT.theta := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨i, hbridge⟩ :=
    exists_frobenius_conjugate_of_equivariant_linearEquiv
      hn dataS.eQuot dataT.eQuot dataS.lambda dataT.lambda
      (lowerCentralLayerRepresentation hSinv.restrict 0 c)
      (lowerCentralLayerRepresentation hTinv.restrict 0 d)
      dataS.quotient_compatible dataT.quotient_compatible e hequiv
  have hsourceS : dataS.lambda ^ (1 + 2 ^ r) = nu := by
    have htheta :
        dataS.theta dataS.lambda = dataS.lambda ^ 2 ^ r := by
      rw [hthetaS, frobeniusEquiv_pow_apply]
    calc
      dataS.lambda ^ (1 + 2 ^ r)
          = dataS.lambda * dataS.lambda ^ 2 ^ r := by
            rw [pow_add, pow_one]
      _ = dataS.lambda * dataS.theta dataS.lambda := by rw [htheta]
      _ = nu := dataS.kernel_eigenvalue_eq.symm
  have hsourceT : dataT.lambda ^ (1 + 2 ^ s) = nu := by
    have htheta :
        dataT.theta dataT.lambda = dataT.lambda ^ 2 ^ s := by
      rw [hthetaT, frobeniusEquiv_pow_apply]
    calc
      dataT.lambda ^ (1 + 2 ^ s)
          = dataT.lambda * dataT.lambda ^ 2 ^ s := by
            rw [pow_add, pow_one]
      _ = dataT.lambda * dataT.theta dataT.lambda := by rw [htheta]
      _ = nu := dataT.kernel_eigenvalue_eq.symm
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 n hn
  have hordnu : orderOf nu = 2 ^ n - 1 :=
    hnuPrimitive.eq_orderOf.symm
  have hNpos : 0 < 2 ^ n - 1 := by
    have : 2 ^ 1 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hnpos
    omega
  have hnuNe : nu ≠ 0 := by
    intro h0
    have hone : nu ^ (2 ^ n - 1) = 1 := by
      rw [← hordnu]
      exact pow_orderOf_eq_one nu
    rw [h0, zero_pow (by omega)] at hone
    exact zero_ne_one hone
  have hlamNe : dataS.lambda ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by simp)] at hsourceS
    exact hnuNe hsourceS.symm
  have hpowcard :
      dataS.lambda ^ (2 ^ n - 1) = 1 := by
    have hfin : Finite (GaloisField 2 n) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one dataS.lambda hlamNe
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  have hordlam : orderOf dataS.lambda = 2 ^ n - 1 :=
    (orderOf_eq_and_coprime_of_pow_eq_orderOf hNpos
      (by simp : 1 + 2 ^ r ≠ 0) hordnu hsourceS hpowcard).1
  have hrs : r = s :=
    normalized_frobenius_exponents_eq_of_power_bridge
      hnpos hr0 hs0 hrhalf hshalf hordlam
      hsourceS hsourceT hbridge
  rw [hthetaS, hthetaT, hrs]

/-- **Higman Lemma 13, normalized factor-coordinate coherence (inclusive
case).**  Normalized inclusive factor coordinates have the same square-law
automorphism across compatible group- and layer-level identifications. -/
theorem FactorCoordinateData.theta_eq_of_normalized_equivariant
    {P Q : Type uP} [Group P] [Finite P] [Group Q] [Finite Q]
    {Y : Subgroup (MulAut P)} {Z : Subgroup (MulAut Q)}
    [IsMulCommutative (frattini P)]
    [Module (ZMod 2) (Additive (frattini P))]
    [IsMulCommutative (frattini Q)]
    [Module (ZMod 2) (Additive (frattini Q))]
    {S : Subgroup P} {T : Subgroup Q}
    {hSinv : IsAInvariant Y.subtype S}
    {hTinv : IsAInvariant Z.subtype T}
    {hPhiS : frattini P ≤ S} {hPhiT : frattini Q ≤ T}
    {c : Y} {d : Z} {n : ℕ}
    {ePhiS : Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {ePhiT : Additive (frattini Q) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (dataS : FactorCoordinateData hSinv hPhiS c ePhiS nu)
    (dataT : FactorCoordinateData hTinv hPhiT d ePhiT nu)
    (hn : n ≠ 0)
    (hnormS : dataS.theta = 1 ∨
      ∃ r : ℕ, 0 < r ∧ 2 * r ≤ n ∧
        dataS.theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r ∧
        Odd (orderOf dataS.theta))
    (hnormT : dataT.theta = 1 ∨
      ∃ s : ℕ, 0 < s ∧ 2 * s ≤ n ∧
        dataT.theta = frobeniusEquiv (GaloisField 2 n) 2 ^ s ∧
        Odd (orderOf dataT.theta))
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
    (eMul : S ≃* T)
    (eLin : Additive (lowerCentralLayer S 0) ≃ₗ[ZMod 2]
      Additive (lowerCentralLayer T 0))
    (hequiv : ∀ x, eLin
      (lowerCentralLayerRepresentation hSinv.restrict 0 c x) =
        lowerCentralLayerRepresentation hTinv.restrict 0 d (eLin x)) :
    dataS.theta = dataT.theta := by
  cases dataS with
  | commutative dS =>
      cases dataT with
      | commutative dT => rfl
      | noncommutative hncommT dT =>
          have hcommT : IsMulCommutative T :=
            IsMulCommutative.of_comm fun x y => by
              apply eMul.symm.injective
              simpa only [map_mul] using
                dS.hcomm.is_comm.comm (eMul.symm x) (eMul.symm y)
          exact (hncommT hcommT).elim
  | noncommutative hncommS dS =>
      cases dataT with
      | commutative dT =>
          have hcommS : IsMulCommutative S :=
            IsMulCommutative.of_comm fun x y => by
              apply eMul.injective
              simpa only [map_mul] using dT.hcomm.is_comm.comm (eMul x) (eMul y)
          exact (hncommS hcommS).elim
      | noncommutative hncommT dT =>
          rcases hnormS with hSone | ⟨r, hr0, hrhalf, hthetaS, -⟩
          · exact (dS.theta_ne_one (by
              simpa [FactorCoordinateData.theta] using hSone)).elim
          rcases hnormT with hTone | ⟨s, hs0, hshalf, hthetaT, -⟩
          · exact (dT.theta_ne_one (by
              simpa [FactorCoordinateData.theta] using hTone)).elim
          have htheta := dS.theta_eq_of_normalized_equivariant
            dT hn hr0 hrhalf
            (by simpa [FactorCoordinateData.theta] using hthetaS)
            hs0 hshalf
            (by simpa [FactorCoordinateData.theta] using hthetaT)
            hnuPrimitive eLin hequiv
          simpa [FactorCoordinateData.theta] using htheta

end

end OddOrder.Higman.Suzuki2Groups
