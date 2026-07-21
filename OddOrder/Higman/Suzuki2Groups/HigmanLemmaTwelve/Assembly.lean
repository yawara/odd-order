/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.CaseDispatch
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Classification

/-!
# Higman Lemma 12: assembling the B/C/D classification

G. Higman, *Suzuki 2-groups*, pp. 90--92.  This file connects the actual
mixed term of the two complementary factors (`mixedTermBilinear`) to the
case-dispatch normalizations (`CaseDispatch`) and the per-case endpoint
engines (`Classification`), assembling `higmanLemmaTwelve`.

The pre-case-split state (`exists_mixedFrobeniusWeightEquation_of_xiLengthThree`)
supplies the complementary factors, their coordinate data over a common
ambient Singer datum, and the eigenvalue equations `ν = λθ(λ) = μφ(μ)`.  The
remaining steps are: coordinates for the noncommuting witness (so the mixed
term is a nonzero bilinear map), the Frobenius support extraction per case,
the shear normalization (case `θ = φ ≠ 1`), the `ε` conditions from
anisotropy, and the endpoint engines.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.RepresentationTheory
open OddOrder.Isaacs.Ch03
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups
open Module
open scoped IsMulCommutative

noncomputable section

universe uP

local instance assemblyLayerCommGroup
    (H : Type uP) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

local instance assemblyLayerModule
    (H : Type uP) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

local instance assemblyLayerIsMulComm
    (H : Type uP) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

variable {P : Type uP} [Group P] [Finite P] {Y : Subgroup (MulAut P)}

/-! ## Coordinates for the noncommuting witness -/

/-- **The actual mixed term is a nonzero bilinear map.**  The noncommuting
mixed-factor witness of the complementary factors has coordinates under the
packaged inclusions, and the ambient centre coordinate is injective, so the
bundled mixed term does not vanish identically.  This is the `hM0` input of
the Frobenius support extraction. -/
theorem exists_mixedTermBilinear_ne_zero
    {n : ℕ}
    (factors : XiLengthThreeTypeAFactorData P Y)
    {hEA : IsElementaryAbelian 2 ↑(frattini P)}
    {ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {hK1amb : lowerCentralLayerKernel P 1 = ⊥}
    {htermamb : lowerCentralTerm P 1 = frattini P}
    {hSqamb : LowerCentralSquaresLieInSecond P}
    {hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0)}
    (left : FactorInclusionData factors.left hEA ePhi hK1amb htermamb
      hSqamb hK0)
    (right : FactorInclusionData factors.right hEA ePhi hK1amb htermamb
      hSqamb hK0)
    (hxi : IsXiActor Y)
    (hinvPhi : involutions P ⊆ frattini P) :
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
    ∃ α β : GaloisField 2 n, mixedTermBilinear left right α β ≠ 0 := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  obtain ⟨x, y, hxL, hyR, hne⟩ :=
    factors.exists_mixed_lowerCentralCommutatorBilinear_ne_zero
      hxi hinvPhi hEA hK1amb
  obtain ⟨α, hα⟩ := left.exists_incl_eq x hxL
  obtain ⟨β, hβ⟩ := right.exists_incl_eq y hyR
  refine ⟨α, β, ?_⟩
  rw [mixedTermBilinear_apply, hα, hβ]
  intro hzero
  exact hne ((LinearEquiv.map_eq_zero_iff
    (ambientCenterCoordinate hEA hK1amb htermamb ePhi)).mp hzero)

/-! ## Case `θ = φ = 1` (Higman p. 90) -/

/-- **Higman p. 90, case `θ = φ = 1`: `G ≅ B(n, 1, ε)`.**  Both factors are
commutative; the mixed term is a single diagonal monomial `c₀αβ` by the
support pinning, and anisotropy makes `c₀` a permitted `ε`. -/
theorem isTypeB_of_mixedTerm_theta_one
    {Sl Sr : Subgroup P} {n : ℕ}
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hK1amb : lowerCentralLayerKernel P 1 = ⊥)
    (htermamb : lowerCentralTerm P 1 = frattini P)
    (hSqamb : LowerCentralSquaresLieInSecond P)
    (hAgemoamb : Agemo P 2 1 = frattini P)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (left : FactorInclusionData Sl hEA ePhi hK1amb htermamb hSqamb hK0)
    (right : FactorInclusionData Sr hEA ePhi hK1amb htermamb hSqamb hK0)
    (hRnormal : Sr.Normal) (hinf : Sl ⊓ Sr = frattini P)
    (hsup : Sl ⊔ Sr = ⊤) (hΦR : frattini P ≤ Sr)
    (lam nu : GaloisField 2 n)
    (hordnu : orderOf nu = 2 ^ n - 1)
    (hlam2 : lam ^ 2 = nu)
    (hθL : left.theta = 1) (hθR : right.theta = 1)
    (hequiv :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      ∀ α β : GaloisField 2 n,
        mixedTermBilinear left right (lam * α) (lam * β) =
          nu * mixedTermBilinear left right α β)
    (hM0 :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      ∃ α β : GaloisField 2 n, mixedTermBilinear left right α β ≠ 0)
    (hinv : ∀ x : P, x ^ 2 = 1 → x ∈ lowerCentralTerm P 1)
    (hcentral : frattini P ≤ Subgroup.center P)
    (n_pos : 0 < n)
    (hcard : Nat.card (GaloisField 2 n) = 2 ^ n) :
    IsTypeB.{uP, 0} P := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  have hNpos : 0 < 2 ^ n - 1 := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) n_pos
    omega
  have hνne : nu ≠ 0 := by
    intro h0
    have hone : nu ^ (2 ^ n - 1) = 1 := by
      rw [← hordnu]
      exact pow_orderOf_eq_one nu
    rw [h0, zero_pow (by omega)] at hone
    exact zero_ne_one hone
  have hlamne : lam ≠ 0 := by
    intro h0
    rw [h0] at hlam2
    exact hνne (by simpa using hlam2.symm)
  have hlampow : lam ^ (2 ^ n - 1) = 1 := by
    have hfin : Finite (GaloisField 2 n) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one lam hlamne
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  obtain ⟨hordlam, -⟩ :=
    orderOf_eq_and_coprime_of_pow_eq_orderOf hNpos (by norm_num : (2 : ℕ) ≠ 0)
      hordnu hlam2 hlampow
  obtain ⟨c0, hc0ne, hc0⟩ :=
    mixedTerm_monomial_of_theta_one n_pos (mixedTermBilinear left right)
      lam nu hordlam (by simpa using hlam2) hequiv hM0
  have hdecomp := fun (a b : GaloisField 2 n) (ha : a ≠ 0) (hb : b ≠ 0) =>
    ambientProductSquare_decomposed_ne_zero left right hRnormal hinf hsup
      hΦR hinv ha hb
  have hEps : OddOrder.Peterfalvi.Appendices.Suzuki2Groups.IsTypeBEpsilon
      (1 : RingAut (GaloisField 2 n)) c0 := by
    refine isTypeBEpsilon_of_decomposed_aniso 1 c0 fun a b ha hb => ?_
    have h := hdecomp a b ha hb
    rw [hθL, hθR, ← mixedTermBilinear_apply, hc0] at h
    simpa [RingAut.one_apply] using h
  refine isTypeB_of_mixedTerm hEA hK1amb htermamb hSqamb hAgemoamb hK0 ePhi
    left right hRnormal hinf hsup hΦR 1 hθL hθR
    (by simp : Odd (orderOf (1 : RingAut (GaloisField 2 n))))
    (Units.mk0 c0 hc0ne) hEps n_pos hcard ?_ ?_
  · rw [ambientProductExtension_inl_range]
    exact hcentral
  · intro α β
    have h := hc0 α β
    rw [mixedTermBilinear_apply] at h
    simpa [RingAut.one_apply] using h

/-! ## Case `θ = φ ≠ 1` (Higman p. 91) -/

/-- **Higman p. 91, case `θ = φ ≠ 1`: `G ≅ B(n, θ, ε)`.**  The mixed term
has the two monomials `c₁αθ(β) + c₂θ(α)β`; the shear-and-rescale coordinate
change removes the second and normalizes the third summand, and the engine
runs on the sheared coordinate. -/
theorem isTypeB_of_mixedTerm_theta_eq
    {Sl Sr : Subgroup P} {n r : ℕ}
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hK1amb : lowerCentralLayerKernel P 1 = ⊥)
    (htermamb : lowerCentralTerm P 1 = frattini P)
    (hSqamb : LowerCentralSquaresLieInSecond P)
    (hAgemoamb : Agemo P 2 1 = frattini P)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (left : FactorInclusionData Sl hEA ePhi hK1amb htermamb hSqamb hK0)
    (right : FactorInclusionData Sr hEA ePhi hK1amb htermamb hSqamb hK0)
    (hRnormal : Sr.Normal) (hinf : Sl ⊓ Sr = frattini P)
    (hsup : Sl ⊔ Sr = ⊤) (hΦR : frattini P ≤ Sr)
    (theta : RingAut (GaloisField 2 n))
    (htheta : theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r)
    (hr0 : r ≠ 0) (hrn : r < n)
    (hthetaodd : Odd (orderOf theta))
    (hθL : left.theta = theta) (hθR : right.theta = theta)
    (lam nu : GaloisField 2 n)
    (hordnu : orderOf nu = 2 ^ n - 1)
    (hlamnu : lam ^ (1 + 2 ^ r) = nu)
    (hequiv :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      ∀ α β : GaloisField 2 n,
        mixedTermBilinear left right (lam * α) (lam * β) =
          nu * mixedTermBilinear left right α β)
    (hM0 :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      ∃ α β : GaloisField 2 n, mixedTermBilinear left right α β ≠ 0)
    (hinv : ∀ x : P, x ^ 2 = 1 → x ∈ lowerCentralTerm P 1)
    (hcentral : frattini P ≤ Subgroup.center P)
    (n_pos : 0 < n)
    (hcard : Nat.card (GaloisField 2 n) = 2 ^ n) :
    IsTypeB.{uP, 0} P := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  have hNpos : 0 < 2 ^ n - 1 := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) n_pos
    omega
  have hνne : nu ≠ 0 := by
    intro h0
    have hone : nu ^ (2 ^ n - 1) = 1 := by
      rw [← hordnu]
      exact pow_orderOf_eq_one nu
    rw [h0, zero_pow (by omega)] at hone
    exact zero_ne_one hone
  have hlamne : lam ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by simp)] at hlamnu
    exact hνne hlamnu.symm
  have hlampow : lam ^ (2 ^ n - 1) = 1 := by
    have hfin : Finite (GaloisField 2 n) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one lam hlamne
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  obtain ⟨hordlam, -⟩ :=
    orderOf_eq_and_coprime_of_pow_eq_orderOf hNpos
      (by simp : 1 + 2 ^ r ≠ 0) hordnu hlamnu hlampow
  obtain ⟨c1, c2, hc12, hc⟩ :=
    mixedTerm_two_monomials_of_theta_eq hr0 hrn
      (mixedTermBilinear left right) lam nu hordlam hlamnu hequiv hM0
  have hθapp : ∀ x : GaloisField 2 n, theta x = x ^ 2 ^ r := by
    intro x
    rw [htheta, frobeniusEquiv_pow_apply]
  have haniso : ∀ α β : GaloisField 2 n, ¬(α = 0 ∧ β = 0) →
      α * theta α + β * theta β + mixedTermBilinear left right α β ≠ 0 := by
    intro a b hab
    by_cases ha : a = 0
    · have hb : b ≠ 0 := fun hb => hab ⟨ha, hb⟩
      have hθb : theta b ≠ 0 := fun h =>
        hb (theta.injective (h.trans (map_zero theta).symm))
      subst ha
      simpa using mul_ne_zero hb hθb
    · by_cases hb : b = 0
      · have hθa : theta a ≠ 0 := fun h =>
          ha (theta.injective (h.trans (map_zero theta).symm))
        subst hb
        simpa using mul_ne_zero ha hθa
      · have h := ambientProductSquare_decomposed_ne_zero left right
          hRnormal hinf hsup hΦR hinv ha hb
        rw [hθL, hθR, ← mixedTermBilinear_apply] at h
        exact h
  obtain ⟨ρ, t, ε, ht0, hε0, hEps, hfinal⟩ :=
    exists_typeB_shear_normalization theta hthetaodd c1 c2
      (fun a b => a * theta a + b * theta b + mixedTermBilinear left right a b)
      (fun α β => by
        simp only [hc]
        rw [hθapp α, hθapp β])
      haniso
  refine isTypeB_of_squareCoordinate hEA hK1amb htermamb hSqamb hAgemoamb hK0
    ePhi
    ((shearRescaleLinearEquiv ρ t ht0).trans
      (ambientProductEquivOfFactors left right hRnormal hinf hsup hΦR))
    theta hthetaodd (Units.mk0 ε hε0) hEps n_pos hcard ?_ ?_
  · rw [ambientProductExtension_inl_range]
    exact hcentral
  · rintro ⟨a, b⟩
    rw [LinearEquiv.trans_apply, shearRescaleLinearEquiv_apply,
      ambientProductSquare_eq left right hRnormal hinf hsup hΦR,
      hθL, hθR, typeBQuadraticMap_apply, ← mixedTermBilinear_apply]
    have h := hfinal a b
    simpa using h

/-! ## Case `θ ≠ 1`, `φ = 1` (Higman p. 91) -/

/-- **Higman p. 91, case `θ ≠ 1`, `φ = 1`: `G ≅ C(n, ε)`.**  The support
pinning forces `2r + 1 = n` and a single mixed monomial, which is the type-C
pairing `ε · (α^{1/2} · (2θ)(β))`. -/
theorem isTypeC_of_mixedTerm_right_theta_one
    {Sl Sr : Subgroup P} {n r : ℕ}
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hK1amb : lowerCentralLayerKernel P 1 = ⊥)
    (htermamb : lowerCentralTerm P 1 = frattini P)
    (hSqamb : LowerCentralSquaresLieInSecond P)
    (hAgemoamb : Agemo P 2 1 = frattini P)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (left : FactorInclusionData Sl hEA ePhi hK1amb htermamb hSqamb hK0)
    (right : FactorInclusionData Sr hEA ePhi hK1amb htermamb hSqamb hK0)
    (hRnormal : Sr.Normal) (hinf : Sl ⊓ Sr = frattini P)
    (hsup : Sl ⊔ Sr = ⊤) (hΦR : frattini P ≤ Sr)
    (theta : RingAut (GaloisField 2 n))
    (htheta : theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r)
    (hr : 0 < r) (h2r : 2 * r ≤ n)
    (hθL : left.theta = theta) (hθR : right.theta = 1)
    (lam mu nu : GaloisField 2 n)
    (hordnu : orderOf nu = 2 ^ n - 1)
    (hlamnu : lam ^ (1 + 2 ^ r) = nu)
    (hmunu : mu ^ 2 = nu)
    (hequiv :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      ∀ α β : GaloisField 2 n,
        mixedTermBilinear left right (lam * α) (mu * β) =
          nu * mixedTermBilinear left right α β)
    (hM0 :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      ∃ α β : GaloisField 2 n, mixedTermBilinear left right α β ≠ 0)
    (hinv : ∀ x : P, x ^ 2 = 1 → x ∈ lowerCentralTerm P 1)
    (hcentral : frattini P ≤ Subgroup.center P)
    (n_pos : 0 < n)
    (hcard : Nat.card (GaloisField 2 n) = 2 ^ n) :
    IsTypeC.{uP, 0} P := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  have hNpos : 0 < 2 ^ n - 1 := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) n_pos
    omega
  have hνne : nu ≠ 0 := by
    intro h0
    have hone : nu ^ (2 ^ n - 1) = 1 := by
      rw [← hordnu]
      exact pow_orderOf_eq_one nu
    rw [h0, zero_pow (by omega)] at hone
    exact zero_ne_one hone
  have hfin : Finite (GaloisField 2 n) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hlamne : lam ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by simp)] at hlamnu
    exact hνne hlamnu.symm
  have hmune : mu ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hmunu
    exact hνne hmunu.symm
  have hlampow : lam ^ (2 ^ n - 1) = 1 := by
    letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one lam hlamne
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  have hmupow : mu ^ (2 ^ n - 1) = 1 := by
    letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one mu hmune
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  obtain ⟨hordlam, -⟩ :=
    orderOf_eq_and_coprime_of_pow_eq_orderOf hNpos
      (by simp : 1 + 2 ^ r ≠ 0) hordnu hlamnu hlampow
  obtain ⟨h2r1, c0, hc0ne, hc0⟩ :=
    mixedTerm_monomial_typeC hr h2r (mixedTermBilinear left right)
      lam mu nu hordlam hlamnu hmunu hmupow hequiv hM0
  -- decomposed anisotropy in the type-C monomial shape
  have haniso : ∀ a b : GaloisField 2 n, a ≠ 0 → b ≠ 0 →
      a * theta a + b * b +
        c0 * (a ^ 2 ^ (n - 1) * b ^ 2 ^ (r + 1)) ≠ 0 := by
    intro a b ha hb
    have h := ambientProductSquare_decomposed_ne_zero left right
      hRnormal hinf hsup hΦR hinv ha hb
    rw [hθL, hθR, ← mixedTermBilinear_apply, hc0, RingAut.one_apply] at h
    exact h
  have hEps : IsTypeCEpsilon theta c0 :=
    isTypeCEpsilon_of_decomposed_aniso h2r1 theta htheta c0 haniso
  -- `2θ² = 1` from `2r + 1 = n`
  have hn0 : n ≠ 0 := by omega
  have hcard' : Nat.card (GaloisField 2 n) = 2 ^ n := hcard
  have horder : orderOf (frobeniusEquiv (GaloisField 2 n) 2) = n :=
    orderOf_frobeniusEquiv_eq_of_card_eq_two_pow n
      (by simpa [Nat.card_eq_fintype_card] using hcard')
  have hfrobn : (frobeniusEquiv (GaloisField 2 n) 2) ^ n = 1 := by
    calc (frobeniusEquiv (GaloisField 2 n) 2) ^ n
        = (frobeniusEquiv (GaloisField 2 n) 2)
            ^ orderOf (frobeniusEquiv (GaloisField 2 n) 2) := by rw [horder]
      _ = 1 := pow_orderOf_eq_one _
  have htwosq : frobeniusEquiv (GaloisField 2 n) 2 * theta ^ 2 = 1 := by
    rw [htheta, ← pow_mul, ← pow_succ', show r * 2 + 1 = n from by omega]
    exact hfrobn
  -- `Frob⁻¹` and `Frob·θ` as power maps
  have hinvfrob : (frobeniusEquiv (GaloisField 2 n) 2)⁻¹ =
      (frobeniusEquiv (GaloisField 2 n) 2) ^ (n - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', show n - 1 + 1 = n from by omega]
    exact hfrobn
  refine isTypeC_of_mixedTerm hEA hK1amb htermamb hSqamb hAgemoamb hK0 ePhi
    left right hRnormal hinf hsup hΦR theta hθL hθR htwosq
    (Units.mk0 c0 hc0ne) hEps n_pos hcard ?_ ?_
  · rw [ambientProductExtension_inl_range]
    exact hcentral
  · intro α β
    have h := hc0 α β
    rw [mixedTermBilinear_apply] at h
    rw [h]
    have hia : (frobeniusEquiv (GaloisField 2 n) 2)⁻¹ α =
        α ^ 2 ^ (n - 1) := by
      rw [hinvfrob, frobeniusEquiv_pow_apply]
    have hmb : (frobeniusEquiv (GaloisField 2 n) 2 * theta) β =
        β ^ 2 ^ (r + 1) := by
      rw [htheta, ← pow_succ', frobeniusEquiv_pow_apply]
    rw [hia, hmb]
    simp

end

end OddOrder.Higman.Suzuki2Groups
