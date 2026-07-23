/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.CaseDispatch

/-!
# Higman's Lemma 12: normalized factor-pair relations

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 12, pp. 90–92.

This file records the five oriented parameter relations produced by the
B/C/D dispatch.  It contains only the relation type; the fixed-coordinate
proof and the coordinate-existence wrapper live in downstream leaves.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

section /- Higman Lemma 12 (pp. 90–92) -/

/-- The factor-parameter information retained from Higman's B/C/D dispatch.

The left/right orientation refers to the specified complementary factors,
not to a pair chosen internally by the classification theorem. -/
inductive NormalizedFactorPairRelation (n : ℕ)
    (theta phi : RingAut (GaloisField 2 n)) : Prop
  | typeB (same : theta = phi)
  | typeCLeft (r : ℕ) (r_pos : 0 < r)
      (left_frobenius :
        theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r)
      (right_one : phi = 1)
      (dimension : 2 * r + 1 = n)
  | typeCRight (r : ℕ) (r_pos : 0 < r)
      (left_one : theta = 1)
      (right_frobenius :
        phi = frobeniusEquiv (GaloisField 2 n) 2 ^ r)
      (dimension : 2 * r + 1 = n)
  | typeDLeft (r : ℕ) (r_pos : 0 < r) (r_half : 2 * r ≤ n)
      (left_frobenius :
        theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r)
      (right_square : phi = theta ^ 2)
      (order_five_congruence : 5 * (r : ZMod n) = 0)
  | typeDRight (r : ℕ) (r_pos : 0 < r) (r_half : 2 * r ≤ n)
      (right_frobenius :
        phi = frobeniusEquiv (GaloisField 2 n) 2 ^ r)
      (left_square : theta = phi ^ 2)
      (order_five_congruence : 5 * (r : ZMod n) = 0)

/-- Reversing the two prescribed factors reverses the orientation of a
normalized factor-pair relation. -/
theorem NormalizedFactorPairRelation.symm
    {n : ℕ} {theta phi : RingAut (GaloisField 2 n)}
    (h : NormalizedFactorPairRelation n theta phi) :
    NormalizedFactorPairRelation n phi theta := by
  cases h with
  | typeB same => exact .typeB same.symm
  | typeCLeft r hr0 htheta hphi hdim =>
      exact .typeCRight r hr0 hphi htheta hdim
  | typeCRight r hr0 htheta hphi hdim =>
      exact .typeCLeft r hr0 hphi htheta hdim
  | typeDLeft r hr0 hrhalf htheta hphi hfive =>
      exact .typeDRight r hr0 hrhalf htheta hphi hfive
  | typeDRight r hr0 hrhalf hphi htheta hfive =>
      exact .typeDLeft r hr0 hrhalf hphi htheta hfive

end

end OddOrder.Higman.Suzuki2Groups
