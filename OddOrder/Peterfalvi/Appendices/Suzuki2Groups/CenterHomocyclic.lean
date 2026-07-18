/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.CenterInvolutions
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanAbelian

/-!
# The center of a Suzuki 2-group is homocyclic

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 1,
p. 83, applied to the characteristic center of the Suzuki group.

The defining actor preserves the center, and every involution already lies
in the center. Its regular action on ambient involutions therefore restricts
to a transitive action on the center involutions. Higman Lemma 1 then makes
the center homocyclic and classifies all of its actor-invariant subgroups as
Agemo layers. This is the first hard input toward the reverse inclusion in
Peterfalvi Appendix III theorem (a), `Z(P) ≤ Q₀`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03

/-- The defining Suzuki actor restricted to the characteristic center. -/
def centerAction
    {P : Type*} [Group P] (K : Subgroup (MulAut P)) :
    K →* MulAut ↥(Subgroup.center P) :=
  (IsAInvariant.of_characteristic K.subtype).restrict

@[simp] theorem centerAction_apply_val
    {P : Type*} [Group P] (K : Subgroup (MulAut P))
    (k : K) (z : Subgroup.center P) :
    ((centerAction K k z : Subgroup.center P) : P) =
      (k : MulAut P) (z : P) := by
  rfl

/-- Higman Lemma 1 applied to the center of a finite Suzuki `2`-group:
the center is homocyclic and its invariant subgroups are exactly its Agemo
layers. -/
theorem exists_center_homocyclic_and_invariant_eq_agemo
    {P : Type*} [Group P] [Finite P] (hP : IsSuzuki2Group P) :
    ∃ K : Subgroup (MulAut P), IsCyclic K ∧ ActsRegularlyOnInvolutions K ∧
      ∃ (ι : Type) (_ : Fintype ι) (e : ℕ), 0 < e ∧
        Nonempty (↥(Subgroup.center P) ≃*
          (ι → Multiplicative (ZMod (2 ^ e)))) ∧
        ∀ U : Subgroup ↥(Subgroup.center P),
          IsAInvariant (centerAction K) U →
            ∃ s ≤ e, U = Agemo ↥(Subgroup.center P) 2 s := by
  rcases hP with ⟨hP2, _, _, K, hKcyc, hreg⟩
  refine ⟨K, hKcyc, hreg, ?_⟩
  letI : CommGroup ↥(Subgroup.center P) :=
    { (inferInstance : Group ↥(Subgroup.center P)) with
      mul_comm := fun x y =>
        Subtype.ext ((Subgroup.mem_center_iff.mp x.2 y).symm) }
  have htrans : ∀ x ∈ involutions ↥(Subgroup.center P),
      ∀ y ∈ involutions ↥(Subgroup.center P),
        ∃ k : K, centerAction K k x = y := by
    intro x hx y hy
    have hxP : (x : P) ∈ involutions P := by
      refine ⟨congrArg Subtype.val hx.1, ?_⟩
      intro h
      exact hx.2 (Subtype.ext h)
    have hyP : (y : P) ∈ involutions P := by
      refine ⟨congrArg Subtype.val hy.1, ?_⟩
      intro h
      exact hy.2 (Subtype.ext h)
    obtain ⟨k, hk, _⟩ := hreg (x : P) hxP (y : P) hyP
    refine ⟨k, ?_⟩
    apply Subtype.ext
    exact hk
  simpa only using
    (exists_homocyclic_and_invariant_eq_agemo
      (hP2.to_subgroup (Subgroup.center P)) (centerAction K) htrans)

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
