/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoSupportCancellation
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.CaseSplitBCD

/-!
# Higman Lemma 13: two-support cancellation in the all-isomorphic case

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

In the exceptional exponent-two case, all three length-two factors have the
same nontrivial square-law automorphism `θ`.  A mixed bracket against the
third factor may then have both twisted supports

`A₁ (a θ(β)) + A₂ (θ(a) β)`.

The self-bracket of the third factor supplies the column
`a θ(β) + θ(a) β`.  Applying `θ⁻¹` to the second support turns the two
support equations into an ordinary two-by-three linear system whose last
column is `(1, 1)`.

This file records that coefficient calculation and derives the genuine
self-bracket coordinate of a factor inclusion by polarizing its ambient
square law.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open scoped IsMulCommutative

noncomputable section

universe uP

local instance allIsomorphicSupportLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

local instance allIsomorphicSupportLayerCommGroup
    (P : Type uP) [Group P] (i : Nat) :
    CommGroup (lowerCentralLayer P i) :=
  { (inferInstance : Group (lowerCentralLayer P i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian P i).comm }

noncomputable local instance allIsomorphicSupportLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- **Higman Lemma 13 (p. 93), simultaneous cancellation of two twisted
supports.**

The first support is already linear in `a,b,c`.  Applying `θ⁻¹` to the
coefficients of the second support makes it linear in the same three
variables.  The self-bracket column is `(1,1)`, so the first two variables
can be required not to vanish simultaneously. -/
theorem exists_nontrivial_first_pair_cancel_three_twisted_profiles
    {F : Type*} [Field F]
    (theta : F ≃+* F)
    (A₁ A₂ B₁ B₂ : F) :
    ∃ a b c : F,
      (a ≠ 0 ∨ b ≠ 0) ∧
        ∀ beta,
          (A₁ * (a * theta beta) +
              A₂ * (theta a * beta)) +
            (B₁ * (b * theta beta) +
              B₂ * (theta b * beta)) +
            (c * theta beta + theta c * beta) = 0 := by
  obtain ⟨a, b, c, hab, hfirst, hsecond⟩ :=
    exists_nontrivial_first_pair_cancel_two_linear_combinations
      A₁ B₁ 1 (theta.symm A₂) (theta.symm B₂) 1
        (Or.inl one_ne_zero)
  have hfirst' : A₁ * a + B₁ * b + c = 0 := by
    simpa only [mul_comm, mul_one] using hfirst
  have hsecond' :
      A₂ * theta a + B₂ * theta b + theta c = 0 := by
    have h := congrArg theta hsecond
    simp only [map_add, map_mul, RingEquiv.apply_symm_apply,
      mul_one, map_zero] at h
    simpa only [mul_comm] using h
  refine ⟨a, b, c, hab, fun beta => ?_⟩
  calc
    (A₁ * (a * theta beta) + A₂ * (theta a * beta)) +
          (B₁ * (b * theta beta) + B₂ * (theta b * beta)) +
          (c * theta beta + theta c * beta) =
        (A₁ * a + B₁ * b + c) * theta beta +
          (A₂ * theta a + B₂ * theta b + theta c) * beta := by
            ring
    _ = 0 := by rw [hfirst', hsecond']; simp

/-- Three genuine bilinear families with the two common twisted supports and
the self-bracket profile admit one simultaneous nontrivial cancellation.

This is the coordinate-level interface used after the two cross mixed terms
have been transported to one actual common factor. -/
theorem exists_nontrivial_first_pair_cancel_three_twisted_bilinear_profiles
    {n : Nat}
    (theta : (GaloisField 2 n) ≃+* (GaloisField 2 n))
    (M₁ M₂ M₃ :
      GaloisField 2 n →ₗ[ZMod 2]
        (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n))
    (A₁ A₂ B₁ B₂ : GaloisField 2 n)
    (hM₁ : ∀ alpha beta,
      M₁ alpha beta =
        A₁ * (alpha * theta beta) +
          A₂ * (theta alpha * beta))
    (hM₂ : ∀ alpha beta,
      M₂ alpha beta =
        B₁ * (alpha * theta beta) +
          B₂ * (theta alpha * beta))
    (hM₃ : ∀ alpha beta,
      M₃ alpha beta =
        alpha * theta beta + theta alpha * beta) :
    ∃ a b c : GaloisField 2 n,
      (a ≠ 0 ∨ b ≠ 0) ∧
        ∀ beta, M₁ a beta + M₂ b beta + M₃ c beta = 0 := by
  obtain ⟨a, b, c, hab, hcancel⟩ :=
    exists_nontrivial_first_pair_cancel_three_twisted_profiles
      theta A₁ A₂ B₁ B₂
  refine ⟨a, b, c, hab, fun beta => ?_⟩
  rw [hM₁ a beta, hM₂ b beta, hM₃ c beta]
  exact hcancel beta

/-- **Higman Lemma 13 (p. 93), self-bracket coordinate of an actual
factor inclusion.**

The square coordinate of a factor inclusion is `q(α) = α θ(α)`.
Polarizing this honest ambient square law gives the two-support
self-bracket

`[α, β] = α θ(β) + θ(α) β`.
-/
theorem FactorInclusionData.ambientCenterCoordinate_selfBracket_eq
    {P : Type uP} [Group P] [Finite P]
    {S : Subgroup P} {n : Nat}
    {hEA : IsElementaryAbelian 2 (frattini P)}
    {ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {hK1 : lowerCentralLayerKernel P 1 = ⊥}
    {hterm : lowerCentralTerm P 1 = frattini P}
    {hSq : LowerCentralSquaresLieInSecond P}
    {hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0)}
    (data : FactorInclusionData S hEA ePhi hK1 hterm hSq hK0)
    (alpha beta : GaloisField 2 n) :
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hEA.zmodModule
    ambientCenterCoordinate hEA hK1 hterm ePhi
        (lowerCentralCommutatorBilinear P
          (data.incl alpha) (data.incl beta)) =
      alpha * data.theta beta + data.theta alpha * beta := by
  let : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  let : CommGroup (frattini P) := inferInstance
  let : Module (ZMod 2) (Additive (frattini P)) :=
    hEA.zmodModule
  let center :=
    ambientCenterCoordinate hEA hK1 hterm ePhi
  have hpolar :=
    centerSquareMap_add hSq center (data.incl alpha) (data.incl beta)
  calc
    center
        (lowerCentralCommutatorBilinear P
          (data.incl alpha) (data.incl beta)) =
        (center
              (lowerCentralSquareMapAdditive P hSq
                (data.incl alpha)) +
            center
              (lowerCentralSquareMapAdditive P hSq
                (data.incl beta)) +
            center
              (lowerCentralCommutatorBilinear P
                (data.incl alpha) (data.incl beta))) -
          center
            (lowerCentralSquareMapAdditive P hSq
              (data.incl alpha)) -
          center
            (lowerCentralSquareMapAdditive P hSq
              (data.incl beta)) := by ring
    _ =
        center
            (lowerCentralSquareMapAdditive P hSq
              (data.incl alpha + data.incl beta)) -
          center
            (lowerCentralSquareMapAdditive P hSq
              (data.incl alpha)) -
          center
            (lowerCentralSquareMapAdditive P hSq
              (data.incl beta)) := by
                rw [← hpolar]
    _ =
        center
            (lowerCentralSquareMapAdditive P hSq
              (data.incl (alpha + beta))) -
          center
            (lowerCentralSquareMapAdditive P hSq
              (data.incl alpha)) -
          center
            (lowerCentralSquareMapAdditive P hSq
              (data.incl beta)) := by rw [map_add]
    _ =
        (alpha + beta) * data.theta (alpha + beta) -
          alpha * data.theta alpha -
          beta * data.theta beta := by
            rw [data.ambientSquare_incl,
              data.ambientSquare_incl, data.ambientSquare_incl]
    _ = alpha * data.theta beta + data.theta alpha * beta := by
      rw [map_add]
      ring

end

end OddOrder.Higman.Suzuki2Groups
