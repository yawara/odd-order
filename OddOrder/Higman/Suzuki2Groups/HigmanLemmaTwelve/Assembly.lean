/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.CaseDispatch
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Classification
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.ModelCenters

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

/-! ## Symmetry of the mixed term -/

/-- The commutator pairing is symmetric in characteristic two: it is
alternating, and `-1 = 1` on the `ZMod 2`-module target. -/
theorem lowerCentralCommutatorBilinear_comm
    (H : Type uP) [Group H]
    (x y : Additive (lowerCentralLayer H 0)) :
    lowerCentralCommutatorBilinear H y x =
      lowerCentralCommutatorBilinear H x y := by
  have hself := lowerCentralCommutatorBilinear_self H (x + y)
  rw [map_add] at hself
  simp only [LinearMap.add_apply, map_add,
    lowerCentralCommutatorBilinear_self, zero_add, add_zero] at hself
  have h2 : lowerCentralCommutatorBilinear H x y +
      lowerCentralCommutatorBilinear H x y = 0 := by
    have h := two_smul (ZMod 2) (lowerCentralCommutatorBilinear H x y)
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
    exact h.symm
  exact add_right_cancel (hself.trans h2.symm)

/-- Swapping the two factors transposes the mixed term. -/
theorem mixedTermBilinear_swap
    {Sl Sr : Subgroup P} {n : ℕ}
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
    (left : FactorInclusionData Sl hEA ePhi hK1amb htermamb hSqamb hK0)
    (right : FactorInclusionData Sr hEA ePhi hK1amb htermamb hSqamb hK0)
    (α β : GaloisField 2 n) :
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
    mixedTermBilinear right left β α = mixedTermBilinear left right α β := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  rw [mixedTermBilinear_apply, mixedTermBilinear_apply]
  exact congrArg _
    (lowerCentralCommutatorBilinear_comm P (left.incl α) (right.incl β))

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

/-! ## Independent case (Higman pp. 91--92) -/

/-- **Higman pp. 91--92, the independent case: `G ≅ D(n, θ, ε)`.**  The
mixed term is the single monomial `c₀ · α^{2^{3r mod n}} · β^{2^{r mod n}}`
(the survivor branch of the type-D support pinning; the mirror branch enters
through the factor swap), which is the type-D pairing `ε · (θ³(α) · θ(β))`. -/
theorem isTypeD_of_mixedTerm_monomial
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
    (hrn : r < n) (hr0 : (r : ZMod n) ≠ 0)
    (h5r : 5 * (r : ZMod n) = 0)
    (hθL : left.theta = theta) (hθR : right.theta = theta ^ 2)
    (c0 : GaloisField 2 n) (hc0ne : c0 ≠ 0)
    (hc0 :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      ∀ α β : GaloisField 2 n,
        mixedTermBilinear left right α β =
          c0 * (α ^ 2 ^ (3 * r % n) * β ^ 2 ^ (r % n)))
    (hinv : ∀ x : P, x ^ 2 = 1 → x ∈ lowerCentralTerm P 1)
    (hcentral : frattini P ≤ Subgroup.center P)
    (n_pos : 0 < n)
    (hcard : Nat.card (GaloisField 2 n) = 2 ^ n) :
    IsTypeD.{uP, 0} P := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  have hn0 : n ≠ 0 := by omega
  have horder : orderOf (frobeniusEquiv (GaloisField 2 n) 2) = n :=
    orderOf_frobeniusEquiv_eq_of_card_eq_two_pow n
      (by simpa [Nat.card_eq_fintype_card] using hcard)
  have hfrobn : (frobeniusEquiv (GaloisField 2 n) 2) ^ n = 1 := by
    calc (frobeniusEquiv (GaloisField 2 n) 2) ^ n
        = (frobeniusEquiv (GaloisField 2 n) 2)
            ^ orderOf (frobeniusEquiv (GaloisField 2 n) 2) := by rw [horder]
      _ = 1 := pow_orderOf_eq_one _
  have hfrobcong : ∀ a b : ℕ, (a : ZMod n) = (b : ZMod n) →
      (frobeniusEquiv (GaloisField 2 n) 2) ^ a =
        (frobeniusEquiv (GaloisField 2 n) 2) ^ b := by
    intro a b hab
    rw [pow_eq_pow_iff_modEq, horder]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hab
  -- decomposed anisotropy in the type-D monomial shape
  have haniso : ∀ a b : GaloisField 2 n, a ≠ 0 → b ≠ 0 →
      a * theta a + b * (theta ^ 2) b +
        c0 * (a ^ 2 ^ (3 * r % n) * b ^ 2 ^ (r % n)) ≠ 0 := by
    intro a b ha hb
    have h := ambientProductSquare_decomposed_ne_zero left right
      hRnormal hinf hsup hΦR hinv ha hb
    rw [hθL, hθR, ← mixedTermBilinear_apply, hc0] at h
    exact h
  have hEps : IsTypeDEpsilon theta c0 :=
    isTypeDEpsilon_of_decomposed_aniso hn0 hrn theta htheta c0 haniso
  -- `θ⁵ = 1` from `5r ≡ 0 (mod n)`
  have hpow5 : theta ^ 5 = 1 := by
    rw [htheta, ← pow_mul]
    have h := hfrobcong (r * 5) 0 (by push_cast; linear_combination h5r)
    simpa using h
  -- `θ ≠ 1` from `r ≢ 0 (mod n)`
  have hne1 : theta ≠ 1 := by
    intro h1
    apply hr0
    have hdvd : orderOf (frobeniusEquiv (GaloisField 2 n) 2) ∣ r := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← htheta]
      exact h1
    rw [horder] at hdvd
    obtain ⟨k, rfl⟩ := hdvd
    exact natCast_zmod_eq_zero_iff_mod_eq_zero.mpr (Nat.mul_mod_right n k)
  -- the engine `hM` shape
  have hpow3 : theta ^ 3 =
      frobeniusEquiv (GaloisField 2 n) 2 ^ (3 * r % n) := by
    rw [htheta, ← pow_mul, Nat.mul_comm r 3,
      show 3 * r = n * (3 * r / n) + 3 * r % n from
        (Nat.div_add_mod (3 * r) n).symm,
      pow_add, pow_mul, hfrobn, one_pow, one_mul, Nat.div_add_mod]
  refine isTypeD_of_mixedTerm hEA hK1amb htermamb hSqamb hAgemoamb hK0 ePhi
    left right hRnormal hinf hsup hΦR theta hθL hθR hpow5 hne1
    (Units.mk0 c0 hc0ne) hEps n_pos hcard ?_ ?_
  · rw [ambientProductExtension_inl_range]
    exact hcentral
  · intro α β
    have h := hc0 α β
    rw [mixedTermBilinear_apply] at h
    rw [h]
    have h3 : (theta ^ 3) α = α ^ 2 ^ (3 * r % n) := by
      rw [hpow3, frobeniusEquiv_pow_apply]
    have h1 : theta β = β ^ 2 ^ (r % n) := by
      rw [htheta, frobeniusEquiv_pow_apply, Nat.mod_eq_of_lt hrn]
    rw [h3, h1]
    simp

/-! ## The classification endpoint -/

/-- **Higman, Lemma 12 (pp. 90--92): a Suzuki 2-group of ξ-length 3 is
isomorphic to some `B(n, θ, ε)`, `C(n, ε)`, or `D(n, θ, ε)`.**

The complementary invariant factors `X ≅ A(n, θ)`, `Y ≅ A(n, φ)` are
normalized by the `A(n, θ) ≅ A(n, θ⁻¹)` flip so that each factor
automorphism is `1` or `Frob^r` with `0 < r ≤ n/2`, and the four cases of
Higman's dispatch on `(θ, φ)` are closed by the per-case engines. -/
theorem higmanLemmaTwelve
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P, x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    IsTypeB.{uP, 0} P ∨ IsTypeC.{uP, 0} P ∨ IsTypeD.{uP, 0} P := by
  classical
  have hEA : IsElementaryAbelian 2 ↑(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  letI : IsMulCommutative ↑(frattini P) := IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  obtain ⟨factors, c, ePhi, nu, dataL0, dataR0, hn2, -, hnuPrim, hconj,
      hnuL0, hnuR0⟩ :=
    exists_complementaryFactorCoordinates_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  revert hnuL0 hnuR0 hconj hnuPrim hn2 dataR0 dataL0 nu ePhi
  generalize Module.finrank (ZMod 2) (Additive ↑(frattini P)) = n
  intro ePhi nu dataL0 dataR0 hn2 hnuPrim hconj hnuL0 hnuR0
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
  obtain ⟨-, hcentral⟩ :=
    commutator_eq_frattini_and_frattini_le_center_of_xiLengthThree
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
  have hinv : ∀ x : P, x ^ 2 = 1 → x ∈ lowerCentralTerm P 1 := by
    intro x hx
    rw [hterm]
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · exact hinvPhi ⟨hx, hx1⟩
  have hn0 : n ≠ 0 := by omega
  have n_pos : 0 < n := by omega
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 n hn0
  have hordnu : orderOf nu = 2 ^ n - 1 := hnuPrim.eq_orderOf.symm
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
  have hpowcard : ∀ x : GaloisField 2 n, x ≠ 0 → x ^ (2 ^ n - 1) = 1 := by
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
  -- normalize each factor by the `A(n, θ) ≅ A(n, θ⁻¹)` flip
  have normalize : ∀ {S : Subgroup P} {hSinv : IsAInvariant Y.subtype S}
      {hPhiS : frattini P ≤ S}
      (data : FactorCoordinateData hSinv hPhiS c ePhi nu),
      nu = data.lambda * data.theta data.lambda →
      ∃ data' : FactorCoordinateData hSinv hPhiS c ePhi nu,
        nu = data'.lambda * data'.theta data'.lambda ∧
        (data'.theta = 1 ∨
          ∃ r : ℕ, 0 < r ∧ 2 * r ≤ n ∧
            data'.theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r ∧
            Odd (orderOf data'.theta)) := by
    intro S hSinv hPhiS data hnu
    cases data with
    | commutative d => exact ⟨.commutative d, hnu, Or.inl rfl⟩
    | noncommutative hnc d =>
        obtain ⟨d', r, hr0, hrhalf, hθ'⟩ := d.exists_flip_frobenius_le_half hn0
        exact ⟨.noncommutative hnc d', d'.kernel_eigenvalue_eq,
          Or.inr ⟨r, hr0, hrhalf, hθ', d'.theta_order_odd⟩⟩
  obtain ⟨dL, hnuL, hLcase⟩ := normalize dataL0 hnuL0
  obtain ⟨dR, hnuR, hRcase⟩ := normalize dataR0 hnuR0
  -- packaged inclusions and their shared inputs
  set L := dL.toInclusionData hEA ePhi hK1 hterm hSq hAgemo hK0 with hLdef
  set R := dR.toInclusionData hEA ePhi hK1 hterm hSq hAgemo hK0 with hRdef
  have hθLpkg : L.theta = dL.theta :=
    FactorCoordinateData.toInclusionData_theta hEA ePhi dL hK1 hterm hSq
      hAgemo hK0
  have hθRpkg : R.theta = dR.theta :=
    FactorCoordinateData.toInclusionData_theta hEA ePhi dR hK1 hterm hSq
      hAgemo hK0
  have hequivLR : ∀ α β : GaloisField 2 n,
      mixedTermBilinear L R (dL.lambda * α) (dR.lambda * β) =
        nu * mixedTermBilinear L R α β := fun α β =>
    mixedTermBilinear_lambda_equivariance hEA ePhi dL dR hK1 hterm hSq
      hAgemo hK0 hconj α β
  have hequivRL : ∀ α β : GaloisField 2 n,
      mixedTermBilinear R L (dR.lambda * α) (dL.lambda * β) =
        nu * mixedTermBilinear R L α β := fun α β =>
    mixedTermBilinear_lambda_equivariance hEA ePhi dR dL hK1 hterm hSq
      hAgemo hK0 hconj α β
  have hM0LR : ∃ α β : GaloisField 2 n, mixedTermBilinear L R α β ≠ 0 :=
    exists_mixedTermBilinear_ne_zero factors L R hxi hinvPhi
  have hM0RL : ∃ α β : GaloisField 2 n, mixedTermBilinear R L α β ≠ 0 := by
    obtain ⟨α, β, hne⟩ := hM0LR
    refine ⟨β, α, ?_⟩
    rw [mixedTermBilinear_swap L R α β]
    exact hne
  have hinfRL : factors.right ⊓ factors.left = frattini P := by
    rw [inf_comm]
    exact factors.inf_eq_frattini
  have hsupRL : factors.right ⊔ factors.left = ⊤ := by
    rw [sup_comm]
    exact factors.sup_eq_top
  -- the dispatch on `(θ, φ)`
  rcases hLcase with hθL1 | ⟨rL, hrL0, hrLhalf, hθLfrob, hθLodd⟩
  · rcases hRcase with hθR1 | ⟨rR, hrR0, hrRhalf, hθRfrob, hθRodd⟩
    · -- `θ = φ = 1`
      left
      have hlam2 : dL.lambda ^ 2 = nu := by
        have h : dL.theta dL.lambda = dL.lambda := by
          rw [hθL1, RingAut.one_apply]
        calc dL.lambda ^ 2 = dL.lambda * dL.lambda := pow_two _
          _ = dL.lambda * dL.theta dL.lambda := by rw [h]
          _ = nu := hnuL.symm
      have hmu2 : dR.lambda ^ 2 = nu := by
        have h : dR.theta dR.lambda = dR.lambda := by
          rw [hθR1, RingAut.one_apply]
        calc dR.lambda ^ 2 = dR.lambda * dR.lambda := pow_two _
          _ = dR.lambda * dR.theta dR.lambda := by rw [h]
          _ = nu := hnuR.symm
      have heq : dR.lambda = dL.lambda :=
        CharTwo.sq_injective (hmu2.trans hlam2.symm)
      have hequiv' : ∀ α β : GaloisField 2 n,
          mixedTermBilinear L R (dL.lambda * α) (dL.lambda * β) =
            nu * mixedTermBilinear L R α β := by
        intro α β
        have h := hequivLR α β
        rwa [heq] at h
      exact isTypeB_of_mixedTerm_theta_one hEA hK1 hterm hSq hAgemo hK0 ePhi
        L R factors.right_normal factors.inf_eq_frattini factors.sup_eq_top
        factors.frattini_lt_right.le dL.lambda nu hordnu hlam2
        (hθLpkg.trans hθL1) (hθRpkg.trans hθR1) hequiv' hM0LR hinv hcentral
        n_pos hcard
    · -- `θ = 1`, `φ ≠ 1`: type C with the factors swapped
      right; left
      have hmu2 : dL.lambda ^ 2 = nu := by
        have h : dL.theta dL.lambda = dL.lambda := by
          rw [hθL1, RingAut.one_apply]
        calc dL.lambda ^ 2 = dL.lambda * dL.lambda := pow_two _
          _ = dL.lambda * dL.theta dL.lambda := by rw [h]
          _ = nu := hnuL.symm
      have hlamnuR : dR.lambda ^ (1 + 2 ^ rR) = nu := by
        have h : dR.theta dR.lambda = dR.lambda ^ 2 ^ rR := by
          rw [hθRfrob, frobeniusEquiv_pow_apply]
        calc dR.lambda ^ (1 + 2 ^ rR)
            = dR.lambda * dR.lambda ^ 2 ^ rR := by rw [pow_add, pow_one]
          _ = dR.lambda * dR.theta dR.lambda := by rw [h]
          _ = nu := hnuR.symm
      exact isTypeC_of_mixedTerm_right_theta_one hEA hK1 hterm hSq hAgemo
        hK0 ePhi R L factors.left_normal hinfRL hsupRL
        factors.frattini_lt_left.le dR.theta hθRfrob hrR0 hrRhalf hθRpkg
        (hθLpkg.trans hθL1) dR.lambda dL.lambda nu hordnu hlamnuR hmu2
        hequivRL hM0RL hinv hcentral n_pos hcard
  · rcases hRcase with hθR1 | ⟨rR, hrR0, hrRhalf, hθRfrob, hθRodd⟩
    · -- `θ ≠ 1`, `φ = 1`: type C directly
      right; left
      have hmu2 : dR.lambda ^ 2 = nu := by
        have h : dR.theta dR.lambda = dR.lambda := by
          rw [hθR1, RingAut.one_apply]
        calc dR.lambda ^ 2 = dR.lambda * dR.lambda := pow_two _
          _ = dR.lambda * dR.theta dR.lambda := by rw [h]
          _ = nu := hnuR.symm
      have hlamnuL : dL.lambda ^ (1 + 2 ^ rL) = nu := by
        have h : dL.theta dL.lambda = dL.lambda ^ 2 ^ rL := by
          rw [hθLfrob, frobeniusEquiv_pow_apply]
        calc dL.lambda ^ (1 + 2 ^ rL)
            = dL.lambda * dL.lambda ^ 2 ^ rL := by rw [pow_add, pow_one]
          _ = dL.lambda * dL.theta dL.lambda := by rw [h]
          _ = nu := hnuL.symm
      exact isTypeC_of_mixedTerm_right_theta_one hEA hK1 hterm hSq hAgemo
        hK0 ePhi L R factors.right_normal factors.inf_eq_frattini
        factors.sup_eq_top factors.frattini_lt_right.le dL.theta hθLfrob
        hrL0 hrLhalf hθLpkg (hθRpkg.trans hθR1) dL.lambda dR.lambda nu
        hordnu hlamnuL hmu2 hequivLR hM0LR hinv hcentral n_pos hcard
    · -- both `≠ 1`
      have hlamnuL : dL.lambda ^ (1 + 2 ^ rL) = nu := by
        have h : dL.theta dL.lambda = dL.lambda ^ 2 ^ rL := by
          rw [hθLfrob, frobeniusEquiv_pow_apply]
        calc dL.lambda ^ (1 + 2 ^ rL)
            = dL.lambda * dL.lambda ^ 2 ^ rL := by rw [pow_add, pow_one]
          _ = dL.lambda * dL.theta dL.lambda := by rw [h]
          _ = nu := hnuL.symm
      have hlamnuR : dR.lambda ^ (1 + 2 ^ rR) = nu := by
        have h : dR.theta dR.lambda = dR.lambda ^ 2 ^ rR := by
          rw [hθRfrob, frobeniusEquiv_pow_apply]
        calc dR.lambda ^ (1 + 2 ^ rR)
            = dR.lambda * dR.lambda ^ 2 ^ rR := by rw [pow_add, pow_one]
          _ = dR.lambda * dR.theta dR.lambda := by rw [h]
          _ = nu := hnuR.symm
      have hrLn : rL < n := by omega
      have hrRn : rR < n := by omega
      by_cases hrEq : rL = rR
      · -- `θ = φ ≠ 1`
        left
        subst hrEq
        have hlamLne : dL.lambda ≠ 0 := by
          intro h0
          rw [h0, zero_pow (by simp)] at hlamnuL
          exact hνne hlamnuL.symm
        have hlamRne : dR.lambda ≠ 0 := by
          intro h0
          rw [h0, zero_pow (by simp)] at hlamnuR
          exact hνne hlamnuR.symm
        have hmuEq : dR.lambda = dL.lambda :=
          eq_of_pow_eq_pow_orderOf hNpos (by simp) hordnu hlamnuL hlamnuR
            (hpowcard _ hlamLne) (hpowcard _ hlamRne)
        have hequiv' : ∀ α β : GaloisField 2 n,
            mixedTermBilinear L R (dL.lambda * α) (dL.lambda * β) =
              nu * mixedTermBilinear L R α β := by
          intro α β
          have h := hequivLR α β
          rwa [hmuEq] at h
        have hθeq : dR.theta = dL.theta := by
          rw [hθRfrob, hθLfrob]
        exact isTypeB_of_mixedTerm_theta_eq hEA hK1 hterm hSq hAgemo hK0
          ePhi L R factors.right_normal factors.inf_eq_frattini
          factors.sup_eq_top factors.frattini_lt_right.le dL.theta hθLfrob
          (by omega) hrLn hθLodd hθLpkg (hθRpkg.trans hθeq) dL.lambda nu
          hordnu hlamnuL hequiv' hM0LR hinv hcentral n_pos hcard
      · -- the independent case: type D
        right; right
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
          apply hrEq
          have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
          rwa [Nat.ModEq, Nat.mod_eq_of_lt hrLn, Nat.mod_eq_of_lt hrRn]
            at hmod
        have hsum : rL + rR < n := by omega
        have hrsz : (rL : ZMod n) + (rR : ZMod n) ≠ 0 := by
          rw [← Nat.cast_add, Ne, natCast_zmod_eq_zero_iff_mod_eq_zero,
            Nat.mod_eq_of_lt hsum]
          omega
        rcases mixedTerm_monomial_typeD n_pos hrLz hrRz hrsz hrszNe
            (mixedTermBilinear L R) dL.lambda dR.lambda nu hordnu hlamnuL
            hlamnuR hequivLR hM0LR with
          ⟨hs2r, h5r, c0, hc0ne, hc0⟩ | ⟨hr2s, h5s, c0, hc0ne, hc0⟩
        · -- survivor branch
          have hθR2 : R.theta = dL.theta ^ 2 := by
            rw [hθRpkg, hθRfrob, hθLfrob, ← pow_mul]
            exact hfrobcong rR (rL * 2) (by push_cast; linear_combination hs2r)
          exact isTypeD_of_mixedTerm_monomial hEA hK1 hterm hSq hAgemo hK0
            ePhi L R factors.right_normal factors.inf_eq_frattini
            factors.sup_eq_top factors.frattini_lt_right.le dL.theta hθLfrob
            hrLn hrLz h5r hθLpkg hθR2 c0 hc0ne hc0 hinv hcentral n_pos hcard
        · -- mirror branch, entered through the factor swap
          have hθL2 : L.theta = dR.theta ^ 2 := by
            rw [hθLpkg, hθLfrob, hθRfrob, ← pow_mul]
            exact hfrobcong rL (rR * 2) (by push_cast; linear_combination hr2s)
          have hc0' : ∀ α β : GaloisField 2 n,
              mixedTermBilinear R L α β =
                c0 * (α ^ 2 ^ (3 * rR % n) * β ^ 2 ^ (rR % n)) := by
            intro α β
            rw [mixedTermBilinear_swap L R β α, hc0 β α]
            ring
          exact isTypeD_of_mixedTerm_monomial hEA hK1 hterm hSq hAgemo hK0
            ePhi R L factors.left_normal hinfRL hsupRL
            factors.frattini_lt_left.le dR.theta hθRfrob hrRn hrRz h5s
            hθRpkg hθL2 c0 hc0ne hc0' hinv hcentral n_pos hcard

/-- **The center of a ξ-length-3 Suzuki 2-group has exponent two.**  The
classification sends `P` to one of the models `B/C/D`, whose centers have
exponent two by the trivial radical of the model polarizations.  This is the
source of "`Z(Q) = Q₀`" in Peterfalvi's Lemma I.3.5. -/
theorem center_sq_eq_one_of_xiLengthThree
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P, x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    {z : P} (hz : z ∈ Subgroup.center P) : z ^ 2 = 1 := by
  rcases higmanLemmaTwelve hP hncomm hmulti hxi hlen hprime with hB | hC | hD
  · obtain ⟨data⟩ := hB
    exact TypeBData.sq_eq_one_of_mem_center data hz
  · obtain ⟨data⟩ := hC
    exact TypeCData.sq_eq_one_of_mem_center data hz
  · obtain ⟨data⟩ := hD
    exact TypeDData.sq_eq_one_of_mem_center data hz

/-- **`Z(P) = Φ(P)` for a ξ-length-3 Suzuki 2-group**: the Frattini subgroup
is central, and every central element is an involution or the identity, hence
lies in `Φ(P)` with the other involutions. -/
theorem center_eq_frattini_of_xiLengthThree
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P, x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    Subgroup.center P = frattini P := by
  obtain ⟨-, hcentral⟩ :=
    commutator_eq_frattini_and_frattini_le_center_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  refine le_antisymm ?_ hcentral
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
  intro z hz
  have hsq := center_sq_eq_one_of_xiLengthThree hP hncomm hmulti hxi hlen
    hprime hz
  by_cases hz1 : z = 1
  · rw [hz1]
    exact Subgroup.one_mem _
  · exact hinvPhi ⟨hsq, hz1⟩

/-- **`℧₁(Z(P)) = ⊥` for a ξ-length-3 Suzuki 2-group** — the center is
elementary abelian.  This is the missing inclusion of Higman Lemma 1's layer
description of the center. -/
theorem agemo_center_eq_bot_of_xiLengthThree
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P, x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    Agemo ↥(Subgroup.center P) 2 1 = ⊥ := by
  rw [eq_bot_iff, Agemo, Subgroup.closure_le]
  rintro g ⟨z, rfl⟩
  have hsq := center_sq_eq_one_of_xiLengthThree hP hncomm hmulti hxi hlen
    hprime z.2
  have hz : z ^ 2 = 1 := Subtype.ext (by simpa using hsq)
  simp [hz]

end

end OddOrder.Higman.Suzuki2Groups
