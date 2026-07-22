import Mathlib.GroupTheory.Sylow

/-!
# Sylow intersect normal is Sylow (relative-index form)

If `P` is a Sylow `p`-subgroup of a finite group `M` and `N ⊴ M`, then `P ∩ N` is a
Sylow `p`-subgroup of `N` — stated in index form: `p ∤ [N : P ∩ N]`.

Hoisted from `BG/Ch1_Preliminary/S04_Prop44b.lean` (2026-07-22, issue 9318) so that
generic `GroupTheory` leaves (Brauer–Suzuki) can use it without importing the BG tree;
the statement is pure mathlib group theory.
-/

namespace OddOrder.GroupTheory

/-- **Sylow-in-normal-subgroup** (index form): if `P` is a Sylow `p`-subgroup of a finite
group `M` and `N ⊴ M`, then `P ∩ N` is a Sylow `p`-subgroup of `N`; concretely the index
`[N : P ∩ N] = P.relIndex N` is prime to `p`.

Proof: by the second isomorphism theorem `[N : P ∩ N] = [P N : P] = [P ⊔ N : P]`, which
divides `[M : P]`, and `[M : P]` is prime to `p` since `P` is Sylow. The equality
`P.relIndex (P ⊔ N) = P.relIndex N` is obtained by cancelling `(P ⊓ N).relIndex P` in the
two tower factorisations of `(P ⊓ N).relIndex (P ⊔ N)`. -/
theorem sylow_relIndex_normal_not_dvd {M : Type*} [Group M] [Finite M] {p : ℕ}
    [Fact p.Prime] (P : Sylow p M) (N : Subgroup M) [N.Normal] :
    ¬ p ∣ (P : Subgroup M).relIndex N := by
  set Q : Subgroup M := (P : Subgroup M) with hQ
  -- Two tower factorisations of `(Q ⊓ N).relIndex (Q ⊔ N)`.
  have e2 : (Q ⊓ N).relIndex Q * Q.relIndex (Q ⊔ N) = (Q ⊓ N).relIndex (Q ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (Q ⊓ N) Q (Q ⊔ N) inf_le_left le_sup_left
  have e3 : (Q ⊓ N).relIndex N * N.relIndex (Q ⊔ N) = (Q ⊓ N).relIndex (Q ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (Q ⊓ N) N (Q ⊔ N) inf_le_right le_sup_right
  rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_sup_right] at e3
  -- `e3 : Q.relIndex N * N.relIndex Q = (Q ⊓ N).relIndex (Q ⊔ N)`
  have hqn : (Q ⊓ N).relIndex Q = N.relIndex Q := by
    rw [inf_comm]; exact Subgroup.inf_relIndex_right N Q
  rw [hqn] at e2
  -- `e2 : N.relIndex Q * Q.relIndex (Q ⊔ N) = (Q ⊓ N).relIndex (Q ⊔ N)`
  have hpos : 0 < N.relIndex Q := by
    haveI : Finite ↥Q := inferInstance
    have h : (N.subgroupOf Q).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact Nat.pos_of_ne_zero h
  have hmul : N.relIndex Q * Q.relIndex (Q ⊔ N) = N.relIndex Q * Q.relIndex N := by
    rw [e2, ← e3]; ring
  have hkey : Q.relIndex (Q ⊔ N) = Q.relIndex N := Nat.eq_of_mul_eq_mul_left hpos hmul
  have hdvd : Q.relIndex N ∣ Q.index := by
    rw [← hkey]; exact Subgroup.relIndex_dvd_index_of_le le_sup_left
  intro hp
  exact Sylow.not_dvd_index P (hp.trans hdvd)

end OddOrder.GroupTheory
