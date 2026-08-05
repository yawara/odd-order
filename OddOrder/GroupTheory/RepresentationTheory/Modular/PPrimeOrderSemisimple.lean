/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Maschke
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerCount

/-!
# `k[Q]` is split semisimple when `p ∤ |Q|`

Navarro (2.12) — the modular theory of a `p'`-group is its ordinary theory — starts from the fact
that `k[Q]` has no radical at all when `p` does not divide `|Q|`.  This file records that and the
splitting datum it produces.

* Maschke applies (`|Q|` is invertible in `k` because `char k = p ∤ |Q|`), so `k[Q]` is semisimple
  and `J(k[Q]) = ⊥`.
* Hence `BrauerCount`'s splitting datum, over an algebraically closed `k`, is an *injective*
  surjection: `k[Q] ≅ ∏_j M_{d_j}(k)`.  The count of blocks is the number of conjugacy classes,
  because every element of a `p'`-group is `p`-regular.

The consequence used downstream is dimensional: `∑_j d_j ^ 2 = |Q|`, which is what forces the
Cartan matrix of a `p'`-group to be the identity.

## Main results

* `OddOrder.RepresentationTheory.Modular.isSemisimpleRing_monoidAlgebra_of_not_dvd_card`
* `OddOrder.RepresentationTheory.Modular.exists_algEquiv_pi_matrix_of_not_dvd_card`
* `OddOrder.RepresentationTheory.Modular.sum_sq_eq_card_of_not_dvd_card` — `∑_j d_j ^ 2 = |Q|`

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (2.12) (p. 25).
-/

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra OddOrder.GroupTheory

variable {k Q : Type*} [Field k] [Group Q] [Finite Q] {p : ℕ}

/-- **Maschke for a `p'`-group.**  If `k` has characteristic `p` and `p ∤ |Q|`, then `|Q|` is
invertible in `k` and `k[Q]` is semisimple. -/
theorem isSemisimpleRing_monoidAlgebra_of_not_dvd_card (hp : p.Prime) (hk : (p : k) = 0)
    (hQ : ¬ p ∣ Nat.card Q) : IsSemisimpleRing (MonoidAlgebra k Q) := by
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).mpr hk
  haveI : NeZero (Nat.card Q : k) := ⟨fun h => hQ ((CharP.cast_eq_zero_iff k p _).mp h)⟩
  infer_instance

theorem jacobson_monoidAlgebra_eq_bot (hp : p.Prime) (hk : (p : k) = 0)
    (hQ : ¬ p ∣ Nat.card Q) : Ring.jacobson (MonoidAlgebra k Q) = ⊥ :=
  haveI := isSemisimpleRing_monoidAlgebra_of_not_dvd_card hp hk hQ
  IsSemisimpleRing.jacobson_eq_bot _

omit [Finite Q] in
/-- Every element of a `p'`-group is `p`-regular, so every conjugacy class is. -/
theorem isPRegularClass_of_not_dvd_card (hQ : ¬ p ∣ Nat.card Q) (C : ConjClasses Q) :
    IsPRegularClass p C := by
  induction C using Quotient.inductionOn with
  | h g => exact fun hdvd => hQ (hdvd.trans (orderOf_dvd_natCard g))

/-- **`k[Q] ≅ ∏_j M_{d_j}(k)` for a `p'`-group** over an algebraically closed `k` of
characteristic `p`, with as many blocks as conjugacy classes. -/
theorem exists_algEquiv_pi_matrix_of_not_dvd_card [IsAlgClosed k] (hp : p.Prime) (hk : (p : k) = 0)
    (hQ : ¬ p ∣ Nat.card Q) :
    ∃ (n : ℕ) (d : Fin n → ℕ) (_ : ∀ i, NeZero (d i))
      (π : MonoidAlgebra k Q →+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) k),
      Function.Bijective π ∧ n = Nat.card (ConjClasses Q) := by
  obtain ⟨n, d, hd, π, hsurj, hker, hn⟩ :=
    exists_surjective_blocks_card_eq (k := k) (G := Q) hp hk
  refine ⟨n, d, hd, π, ⟨?_, hsurj⟩, ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot, hker]
    exact jacobson_monoidAlgebra_eq_bot hp hk hQ
  · rw [hn]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv (isPRegularClass_of_not_dvd_card hQ))

/-- **`∑_j d_j ^ 2 = |Q|`** for a `p'`-group: comparing `k`-dimensions across
`k[Q] ≅ ∏_j M_{d_j}(k)`. -/
theorem sum_sq_eq_card_of_not_dvd_card {n : ℕ} {d : Fin n → ℕ}
    (π : MonoidAlgebra k Q →+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) k)
    (hπ : Function.Bijective π) (hlin : ∀ (c : k) (x : MonoidAlgebra k Q), π (c • x) = c • π x) :
    ∑ i, d i ^ 2 = Nat.card Q := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  let e : MonoidAlgebra k Q ≃ₗ[k] ∀ i, Matrix (Fin (d i)) (Fin (d i)) k :=
    { toFun := π, map_add' := π.map_add, map_smul' := hlin,
      invFun := Function.surjInv hπ.2,
      left_inv := fun x => hπ.1 (Function.surjInv_eq hπ.2 (π x)),
      right_inv := fun y => Function.surjInv_eq hπ.2 y }
  have hdim := LinearEquiv.finrank_eq e
  rw [Module.finrank_pi_fintype] at hdim
  have hleft : Module.finrank k (MonoidAlgebra k Q) = Nat.card Q := by
    rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis Q k), Nat.card_eq_fintype_card]
  rw [hleft] at hdim
  rw [hdim]
  exact Finset.sum_congr rfl fun i _ => by
    simp [Module.finrank_matrix, pow_two]

end OddOrder.RepresentationTheory.Modular
