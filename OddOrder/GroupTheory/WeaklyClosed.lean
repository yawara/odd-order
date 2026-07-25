/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow

/-!
# Weakly closed subgroups

I. M. Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 5C.6:

> Let `W ≤ H ≤ G`.  We say that `W` is **weakly closed** in `H` with respect to `G` if
> the only `G`-conjugate of `W` contained in `H` is `W` itself.

This file sets up the notion and proves the transport statement 5C.6(a): if `W` is
weakly closed in a Sylow subgroup `P`, then it is weakly closed in *every* Sylow
subgroup containing it.  (The statement is proved here for an arbitrary conjugate
`P^y` of `P`, which by Sylow's theorem covers all Sylow subgroups.)

Weak closure is the hypothesis of the Hall–Wielandt/Grün transfer theorems; see
issue 9503, where it is used for the Sylow `3`-subgroup of Peterfalvi Part II, Ch. II,
step (17).
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **Weakly closed subgroup** (Isaacs, Problem 5C.6): the only `G`-conjugate of `W`
contained in `P` is `W` itself.  (The containment `W ≤ P` is not part of the
definition; it is carried separately where needed.) -/
def IsWeaklyClosed (W P : Subgroup G) : Prop :=
  ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ P →
    W.map (MulAut.conj g).toMonoidHom = W

/-- Conjugating twice is conjugating by the product. -/
theorem map_conj_map_conj (W : Subgroup G) (g h : G) :
    (W.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom
      = W.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj, mul_assoc]

@[simp]
theorem map_conj_one (W : Subgroup G) :
    W.map (MulAut.conj (1 : G)).toMonoidHom = W := by
  ext x
  simp [MulAut.conj]

/-- Conjugation preserves containment. -/
theorem map_conj_le_map_conj {W P : Subgroup G} (g : G) (h : W ≤ P) :
    W.map (MulAut.conj g).toMonoidHom ≤ P.map (MulAut.conj g).toMonoidHom :=
  Subgroup.map_mono h

/-- Conjugation reflects containment. -/
theorem le_of_map_conj_le_map_conj {W P : Subgroup G} {g : G}
    (h : W.map (MulAut.conj g).toMonoidHom ≤ P.map (MulAut.conj g).toMonoidHom) :
    W ≤ P := by
  have h' := map_conj_le_map_conj g⁻¹ h
  rwa [map_conj_map_conj, map_conj_map_conj, inv_mul_cancel, map_conj_one,
    map_conj_one] at h'

/-- **Isaacs Problem 5C.6(a)**: weak closure transports to every conjugate containing
`W`.  If `W` is weakly closed in `P` and `W ≤ P^y`, then `W` is weakly closed in `P^y`.

Since any two Sylow `p`-subgroups are conjugate, this says that a subgroup weakly
closed in one Sylow subgroup is weakly closed in every Sylow subgroup containing it. -/
theorem IsWeaklyClosed.map_conj {W P : Subgroup G} (hwc : IsWeaklyClosed W P) {y : G}
    (hWQ : W ≤ P.map (MulAut.conj y).toMonoidHom) :
    IsWeaklyClosed W (P.map (MulAut.conj y).toMonoidHom) := by
  -- first, `W^{y⁻¹} = W`
  have hWy : W.map (MulAut.conj y⁻¹).toMonoidHom = W := by
    refine hwc y⁻¹ ?_
    have h := map_conj_le_map_conj y⁻¹ hWQ
    rwa [map_conj_map_conj, inv_mul_cancel, map_conj_one] at h
  have hWy' : W.map (MulAut.conj y).toMonoidHom = W := by
    conv_lhs => rw [← hWy]
    rw [map_conj_map_conj, mul_inv_cancel, map_conj_one]
  intro g hg
  -- `W^{y⁻¹g} ≤ P`, so it equals `W`
  have h1 : W.map (MulAut.conj (y⁻¹ * g)).toMonoidHom ≤ P := by
    have h := map_conj_le_map_conj y⁻¹ hg
    rw [map_conj_map_conj, map_conj_map_conj, inv_mul_cancel, map_conj_one] at h
    exact h
  have h2 := hwc _ h1
  -- conjugate back by `y`
  have h3 := congrArg (fun K : Subgroup G => K.map (MulAut.conj y).toMonoidHom) h2
  simp only [map_conj_map_conj] at h3
  rw [show y * (y⁻¹ * g) = g by group] at h3
  rw [h3, hWy']

end OddOrder.GroupTheory
