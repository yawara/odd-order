/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.LengthTwoModels
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoCommonFactorParameters

/-!
# Higman Lemma 13: quotient-eigenvalue coherence

G. Higman, *Suzuki 2-groups*, p. 93.  In the exponent-two branch of
Lemma 13, one actual factor occurs in two pairwise joins.  Once its normalized
square-law automorphisms have been identified, the two quotient eigenvalues
solve the same equation

`ν = λ θ(λ)`.

The odd order of `θ` makes the twisted norm `λ ↦ λ θ(λ)` injective on the
nonzero elements of the characteristic-two field.  Primitivity of `ν`
ensures that both source eigenvalues are nonzero, so they coincide exactly;
there is no residual Frobenius-orbit ambiguity.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

/-- **Higman Lemma 13 (printed p. 93), quotient-eigenvalue coherence.**

Two source eigenvalues over one finite field coincide when they have the same
odd-order square-law automorphism and the same primitive twisted norm. -/
theorem lambda_eq_of_common_primitive_twisted_norm
    {n : ℕ} (hn : n ≠ 0)
    (theta : RingAut (GaloisField 2 n))
    (lambdaJ lambdaK nu : GaloisField 2 n)
    (hthetaOdd : Odd (orderOf theta))
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
    (hsourceJ : nu = lambdaJ * theta lambdaJ)
    (hsourceK : nu = lambdaK * theta lambdaK) :
    lambdaJ = lambdaK := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have htwoPow : 2 ^ 1 ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num) hnpos
  have hNpos : 0 < 2 ^ n - 1 := by omega
  have hnuNe : nu ≠ 0 :=
    hnuPrimitive.ne_zero (Nat.ne_of_gt hNpos)
  have hlambdaJNe : lambdaJ ≠ 0 := by
    intro hzero
    apply hnuNe
    simpa [hzero] using hsourceJ
  have hlambdaKNe : lambdaK ≠ 0 := by
    intro hzero
    apply hnuNe
    simpa [hzero] using hsourceK
  let uJ : (GaloisField 2 n)ˣ := Units.mk0 lambdaJ hlambdaJNe
  let uK : (GaloisField 2 n)ˣ := Units.mk0 lambdaK hlambdaKNe
  have hnorm :
      lambdaJ * theta lambdaJ = lambdaK * theta lambdaK :=
    hsourceJ.symm.trans hsourceK
  have hnormUnits :
      uJ *
          OddOrder.Peterfalvi.Appendices.Suzuki.fieldRingAutOnUnits
            (GaloisField 2 n) theta uJ =
        uK *
          OddOrder.Peterfalvi.Appendices.Suzuki.fieldRingAutOnUnits
            (GaloisField 2 n) theta uK := by
    apply Units.ext
    simpa [uJ, uK,
      OddOrder.Peterfalvi.Appendices.Suzuki.fieldRingAutOnUnits_apply_val]
      using hnorm
  have huJK : uJ = uK :=
    (typeAUnitNorm_bijective theta hthetaOdd).1 hnormUnits
  have hval := congrArg
    (fun u : (GaloisField 2 n)ˣ => (u : GaloisField 2 n)) huJK
  simpa [uJ, uK] using hval

/-- A normalized common factor has a unique quotient eigenvalue over the
prescribed primitive kernel coordinate. -/
theorem lambda_eq_of_common_primitive_twisted_norm_of_normalized
    {n : ℕ} (hn : n ≠ 0)
    (theta : RingAut (GaloisField 2 n))
    (lambdaJ lambdaK nu : GaloisField 2 n)
    (hnorm : IsNormalizedFactorParameter n theta)
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
    (hsourceJ : nu = lambdaJ * theta lambdaJ)
    (hsourceK : nu = lambdaK * theta lambdaK) :
    lambdaJ = lambdaK := by
  have hthetaOdd : Odd (orderOf theta) := by
    rcases hnorm with hthetaOne | ⟨_r, _hr0, _hrhalf, _htheta, hodd⟩
    · simp [hthetaOne]
    · exact hodd
  exact lambda_eq_of_common_primitive_twisted_norm hn theta
    lambdaJ lambdaK nu hthetaOdd hnuPrimitive hsourceJ hsourceK

end OddOrder.Higman.Suzuki2Groups
