import Mathlib.RepresentationTheory.Subrepresentation
import OddOrder.Mathlib.Subgroup

/-!
# Subrepresentation kernel helpers

Shared representation-theoretic kernel lemmas used by the odd-order formalization.
-/

namespace OddOrder.GroupTheory.RepresentationTheory

/-- If a prime-order subgroup acts fixed-point-freely on the ambient representation, then it
meets trivially the kernel of every nonzero subrepresentation. -/
theorem ker_subrepresentation_inf_prime_fixedFree_eq_bot
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (W : Subrepresentation ρ) (hWne : W ≠ ⊥)
    {R : Subgroup G} (hp : (Nat.card R).Prime)
    (hFix : ∀ v : V, (∀ r : R, ρ (r : G) v = v) → v = 0) :
    MonoidHom.ker W.toRepresentation.asGroupHom ⊓ R = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_inf] at hr
  obtain ⟨hrN, hrR⟩ := hr
  rw [Subgroup.mem_bot]
  by_contra hr1
  have hgen : Subgroup.zpowers r = R := Subgroup.zpowers_eq_of_prime_card hp hrR hr1
  have hRker : R ≤ MonoidHom.ker W.toRepresentation.asGroupHom := by
    rw [← hgen]
    exact (Subgroup.zpowers_le).mpr hrN
  have hWsub : W.toSubmodule ≠ ⊥ := by
    intro h
    exact hWne (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff _).mp hWsub
  have hfixed : ∀ r' : R, ρ (r' : G) w = w := by
    intro r'
    have hWr' : W.toRepresentation (r' : G) = 1 := by
      rw [← Representation.asGroupHom_apply, MonoidHom.mem_ker.mp (hRker r'.2), Units.val_one]
    have hval : W.toRepresentation (r' : G) ⟨w, hwW⟩ = ⟨w, hwW⟩ := by
      rw [hWr']
      rfl
    exact congrArg Subtype.val hval
  exact hw0 (hFix w hfixed)

end OddOrder.GroupTheory.RepresentationTheory
