/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Fixed subgroup of an automorphic action

`fixedSubgroup φ K` — 作用 `φ : L →* MulAut H` の部分群 `K ≤ L` による固定点部分群
`C_H(K)`. `CoprimeAction.lean` から upstream 分割 (issue 9104): Isaacs Ch.3 §3E の
Tier-1 forward-dep leaf (`Ch04_Commutators/ForwardFromCh03.lean`) が `CoprimeAction`
本体 (Ch.6 経由の import 循環) を避けて `fixedSubgroup` を参照できるようにする.
-/

namespace OddOrder.GroupTheory

variable {L H : Type*} [Group L] [Group H]

/-- The subgroup `C_H(K)` of points of `H` fixed by every element of a subgroup `K ≤ L`,
under an action `φ : L →* MulAut H`.  This is a subgroup of `H` because each `φ l` is a
group automorphism. -/
def fixedSubgroup (φ : L →* MulAut H) (K : Subgroup L) : Subgroup H where
  carrier := {h | ∀ l ∈ K, φ l h = h}
  one_mem' l _ := map_one (φ l)
  mul_mem' ha hb l hl := by rw [map_mul, ha l hl, hb l hl]
  inv_mem' ha l hl := by rw [map_inv, ha l hl]

@[simp] theorem mem_fixedSubgroup {φ : L →* MulAut H} {K : Subgroup L} {x : H} :
    x ∈ fixedSubgroup φ K ↔ ∀ l ∈ K, φ l x = x := Iff.rfl

/-- Fixing the elements of a *larger* subgroup yields a *smaller* fixed subgroup. -/
theorem fixedSubgroup_antitone (φ : L →* MulAut H) {K K' : Subgroup L} (h : K ≤ K') :
    fixedSubgroup φ K' ≤ fixedSubgroup φ K :=
  fun _ hx l hl => hx l (h hl)

end OddOrder.GroupTheory
