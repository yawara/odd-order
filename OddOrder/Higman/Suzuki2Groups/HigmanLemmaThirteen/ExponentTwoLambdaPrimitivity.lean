/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.SupportPinning
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoCommonFactorParameters

/-!
# Higman Lemma 13: primitivity of a factor eigenvalue

G. Higman, *Suzuki 2-groups*, p. 93.  A normalized factor source eigenvalue
`λ` satisfies

`ν = λ θ(λ)`

for the primitive kernel eigenvalue `ν`.  In the commutative case this is
`λ² = ν`; in the noncommutative case, normalized Frobenius coordinates turn
it into `λ^(1 + 2^r) = ν`.  Since every nonzero field element is killed by
`2^n - 1`, the full order of `ν` forces `λ` itself to have full order.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

/-- **Higman Lemma 13 (printed p. 93), source-eigenvalue order.**

A quotient eigenvalue with normalized square-law parameter and primitive
twisted norm has full multiplicative order `2 ^ n - 1`. -/
theorem orderOf_lambda_eq_of_normalized_twisted_norm
    {n : ℕ} (hn : n ≠ 0)
    (theta : RingAut (GaloisField 2 n))
    (lambda nu : GaloisField 2 n)
    (hnorm : IsNormalizedFactorParameter n theta)
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
    (hsource : nu = lambda * theta lambda) :
    orderOf lambda = 2 ^ n - 1 := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have htwoPow : 2 ^ 1 ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num) hnpos
  have hNpos : 0 < 2 ^ n - 1 := by omega
  have hordnu : orderOf nu = 2 ^ n - 1 :=
    hnuPrimitive.eq_orderOf.symm
  have hnuNe : nu ≠ 0 :=
    hnuPrimitive.ne_zero (Nat.ne_of_gt hNpos)
  have hlambdaNe : lambda ≠ 0 := by
    intro hzero
    apply hnuNe
    simpa [hzero] using hsource
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 n hn
  have hlambdaPow : lambda ^ (2 ^ n - 1) = 1 := by
    letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one lambda hlambdaNe
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  rcases hnorm with hthetaOne |
      ⟨r, _hr0, _hrhalf, hthetaFrobenius, _hthetaOdd⟩
  · have hlambdaSquare : lambda ^ 2 = nu := by
      calc
        lambda ^ 2 = lambda * lambda := pow_two lambda
        _ = lambda * theta lambda := by
          rw [hthetaOne, RingAut.one_apply]
        _ = nu := hsource.symm
    exact (orderOf_eq_and_coprime_of_pow_eq_orderOf
      hNpos (by norm_num : (2 : ℕ) ≠ 0)
      hordnu hlambdaSquare hlambdaPow).1
  · have hthetaApply :
        theta lambda = lambda ^ (2 ^ r) := by
      rw [hthetaFrobenius, frobeniusEquiv_pow_apply]
    have hlambdaPower : lambda ^ (1 + 2 ^ r) = nu := by
      calc
        lambda ^ (1 + 2 ^ r) =
            lambda * lambda ^ (2 ^ r) := by
          rw [pow_add, pow_one]
        _ = lambda * theta lambda := by rw [hthetaApply]
        _ = nu := hsource.symm
    exact (orderOf_eq_and_coprime_of_pow_eq_orderOf
      hNpos (by positivity : 1 + 2 ^ r ≠ 0)
      hordnu hlambdaPower hlambdaPow).1

/-- A normalized quotient eigenvalue whose twisted norm is primitive is
itself a primitive `(2 ^ n - 1)`-st root of unity. -/
theorem lambda_isPrimitiveRoot_of_normalized_twisted_norm
    {n : ℕ} (hn : n ≠ 0)
    (theta : RingAut (GaloisField 2 n))
    (lambda nu : GaloisField 2 n)
    (hnorm : IsNormalizedFactorParameter n theta)
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
    (hsource : nu = lambda * theta lambda) :
    IsPrimitiveRoot lambda (2 ^ n - 1) := by
  have hord := orderOf_lambda_eq_of_normalized_twisted_norm
    hn theta lambda nu hnorm hnuPrimitive hsource
  simpa [hord] using IsPrimitiveRoot.orderOf lambda

end OddOrder.Higman.Suzuki2Groups
