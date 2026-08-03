/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.Basic
import OddOrder.Algebra.CommutatorSpan
import OddOrder.GroupTheory.PRegularElement
import OddOrder.GroupTheory.RepresentationTheory.Modular.CommutatorQuotient
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Group elements and their `p'`-parts agree in the `p`-radical

A high enough `p`-power of a group element is its `p'`-part: raising to `p ^ m` kills the
`p`-part and, if `p ^ m ≡ 1` modulo the order of the `p'`-part, fixes the `p'`-part.  In the
group algebra this means `g - g_{p'}` lies in the `p`-radical `T'` of the commutator span, so
`kG ⧸ T'` is spanned by the `p`-regular classes.

## Main results

* `OddOrder.GroupTheory.exists_pow_prime_pow_eq_pRegularPart`
* `OddOrder.RepresentationTheory.Modular.single_sub_single_pRegularPart_mem`
-/

namespace OddOrder.GroupTheory

variable {p : ℕ} {G : Type*} [Group G]

/-- **A high `p`-power of `g` is its `p'`-part**, and it fixes the `p'`-part. -/
theorem exists_pow_prime_pow_eq_pRegularPart (hp : p.Prime) {g : G} (hg : IsOfFinOrder g) :
    ∃ m : ℕ, g ^ p ^ m = pRegularPart p g ∧ (pRegularPart p g) ^ p ^ m = pRegularPart p g := by
  set y := pRegularPart p g with hy
  set d := orderOf y with hd
  set a := (orderOf g).factorization p with ha
  have hcop : Nat.Coprime p d :=
    (isPRegular_iff_coprime hp).mp (isPRegular_pRegularPart hp hg)
  have hdpos : 0 < d := by
    rw [hd, hy]
    exact (isPRegular_pRegularPart hp hg).isOfFinOrder.orderOf_pos
  have hmodeq : p ^ (a * d.totient) ≡ 1 [MOD d] := by
    rw [mul_comm, pow_mul]
    simpa using (Nat.ModEq.pow_totient hcop).pow a
  have hmod : p ^ (a * d.totient) % d = 1 % d := hmodeq
  have hyfix : y ^ p ^ (a * d.totient) = y :=
    calc y ^ p ^ (a * d.totient) = y ^ (p ^ (a * d.totient) % orderOf y) :=
          (pow_mod_orderOf y _).symm
      _ = y ^ (1 % orderOf y) := by rw [← hd, hmod]
      _ = y ^ 1 := pow_mod_orderOf y 1
      _ = y := pow_one y
  refine ⟨a * d.totient, ?_, hyfix⟩
  have hcomm : Commute y (pPart p g) := commute_pRegularPart_pPart g
  have hfac : g = y * pPart p g := (pRegularPart_mul_pPart hp hg).symm
  have hple : (pPart p g) ^ p ^ (a * d.totient) = 1 := by
    have hord : (pPart p g) ^ p ^ a = 1 := pPart_pow_ordProj g
    obtain ⟨c, hc⟩ : p ^ a ∣ p ^ (a * d.totient) :=
      pow_dvd_pow p (Nat.le_mul_of_pos_right a (Nat.totient_pos.mpr hdpos))
    rw [hc, pow_mul, hord, one_pow]
  rw [hfac, hcomm.mul_pow, hple, hyfix, mul_one]

end OddOrder.GroupTheory

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {k G : Type*} [CommRing k] [Group G]

/-- **A group element and its `p'`-part are congruent modulo the `p`-radical.**  Hence the
`p`-regular classes span `kG ⧸ T'`. -/
theorem single_sub_single_pRegularPart_mem (hp : p.Prime) (hchar : (p : MonoidAlgebra k G) = 0)
    {g : G} (hg : IsOfFinOrder g) :
    single g (1 : k) - single (pRegularPart p g) 1
      ∈ OddOrder.commutatorRadical (k := k) (A := MonoidAlgebra k G) hp hchar := by
  obtain ⟨m, hgm, hym⟩ := exists_pow_prime_pow_eq_pRegularPart hp hg
  refine OddOrder.sub_mem_commutatorRadical_of_pow_eq hp hchar (m := m) ?_
  simp [single_pow, hgm, hym]

/-- The commutator subspace of a group algebra is the commutator span of the algebra. -/
theorem commutatorSubmodule_eq_commutatorSpan :
    commutatorSubmodule k G = OddOrder.commutatorSpan k (MonoidAlgebra k G) := rfl


end OddOrder.RepresentationTheory.Modular
