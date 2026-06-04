/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_FrobeniusClassSum

/-!
# BG Appendix C: Lemma C.2 Packaging

Bender--Glauberman Appendix C, Lemma C.2, pp. 145--152.

This file combines the finite-field cubic branch from `AppC_NormSet` with the
q >= 5 class-sum calculation from `AppC_FrobeniusClassSum`.  It is kept as a
small downstream wrapper to avoid making the finite-field norm-set leaf depend on
class-sum representation theory.
-/

namespace OddOrder.BG.AppC.NormSet

variable (p q : ℕ)

/-- **BG Appendix C, Lemma C.2** (mmd L4923): the norm set has at least two
elements when `p`, `q` are odd primes satisfying condition (A). -/
theorem lemmaC2 [Fact p.Prime] (hpodd : Odd p) (hq : q.Prime) (hqodd : Odd q)
    (_hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) :
    2 ≤ (normSetE p q).ncard := by
  rcases eq_or_ne q 3 with rfl | hq3
  · exact normSetE_ncard_ge_two_of_eq_three p hpodd
  · have hfive : 5 ≤ q := by
      rcases hqodd with ⟨k, hk⟩
      have hq2 : 2 ≤ q := hq.two_le
      omega
    exact normSetE_ncard_ge_two_of_five_le p q hpodd hq hfive

end OddOrder.BG.AppC.NormSet
