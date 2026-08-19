/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.GroupAction.Basic

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

/-- Private helper: the elements of `L` fixing a given point `x ∈ H` form a subgroup
(the `φ`-stabilizer of `x`).  Kept private: publicly this is `MulAction.stabilizer` for
the action induced by `φ`, so a public duplicate would be wrapper debt. -/
private def fixerSubgroup (φ : L →* MulAut H) (x : H) : Subgroup L where
  carrier := {l | φ l x = x}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, MulAut.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_inv, MulAut.inv_def]
    exact (MulEquiv.symm_apply_eq (φ a)).mpr ha.symm

private theorem mem_fixedSubgroup_iff_le_fixerSubgroup {φ : L →* MulAut H} {K : Subgroup L}
    {x : H} : x ∈ fixedSubgroup φ K ↔ K ≤ fixerSubgroup φ x := Iff.rfl

@[simp] theorem fixedSubgroup_bot (φ : L →* MulAut H) : fixedSubgroup φ ⊥ = ⊤ :=
  top_le_iff.mp fun _ _ => mem_fixedSubgroup_iff_le_fixerSubgroup.mpr bot_le

/-- Membership in the fixed subgroup of a join: fixed by `K ⊔ K'` iff fixed by both. -/
theorem fixedSubgroup_sup (φ : L →* MulAut H) (K K' : Subgroup L) :
    fixedSubgroup φ (K ⊔ K') = fixedSubgroup φ K ⊓ fixedSubgroup φ K' :=
  le_antisymm
    (le_inf (fixedSubgroup_antitone φ le_sup_left) (fixedSubgroup_antitone φ le_sup_right))
    fun _ hx => mem_fixedSubgroup_iff_le_fixerSubgroup.mpr <|
      sup_le (mem_fixedSubgroup_iff_le_fixerSubgroup.mp hx.1)
        (mem_fixedSubgroup_iff_le_fixerSubgroup.mp hx.2)

/-- Membership in the fixed subgroup of a closure reduces to the generators. -/
theorem mem_fixedSubgroup_closure {φ : L →* MulAut H} {s : Set L} {x : H} :
    x ∈ fixedSubgroup φ (Subgroup.closure s) ↔ ∀ l ∈ s, φ l x = x := by
  rw [mem_fixedSubgroup_iff_le_fixerSubgroup, Subgroup.closure_le]
  exact Iff.rfl

/-- Membership in the fixed subgroup of a cyclic subgroup reduces to the generator:
the `a = 1` plug-and-play form for a single automorphism. -/
theorem mem_fixedSubgroup_zpowers {φ : L →* MulAut H} {l : L} {x : H} :
    x ∈ fixedSubgroup φ (Subgroup.zpowers l) ↔ φ l x = x := by
  rw [mem_fixedSubgroup_iff_le_fixerSubgroup, Subgroup.zpowers_le]
  exact Iff.rfl

/-- The fixed subgroup is everything iff `K` acts trivially (i.e. `K ≤ ker φ`). -/
theorem fixedSubgroup_eq_top_iff {φ : L →* MulAut H} {K : Subgroup L} :
    fixedSubgroup φ K = ⊤ ↔ K ≤ φ.ker := by
  constructor
  · intro h l hl
    rw [MonoidHom.mem_ker]
    ext x
    exact ((Subgroup.eq_top_iff' _).mp h x) l hl
  · intro h
    rw [Subgroup.eq_top_iff']
    intro x l hl
    rw [show φ l = 1 from MonoidHom.mem_ker.mp (h hl)]
    rfl

/-- `fixedSubgroup φ K` is, as a set, the fixed-point set `MulAction.fixedPoints ↥K H`
of the `↥K`-action on `H` induced by `φ` (bridging lemma to the mathlib vocabulary; the
action is not a global instance, hence the `letI`). -/
theorem coe_fixedSubgroup_eq_fixedPoints (φ : L →* MulAut H) (K : Subgroup L) :
    letI : MulAction K H := MulAction.compHom H (φ.comp K.subtype)
    (fixedSubgroup φ K : Set H) = MulAction.fixedPoints K H := by
  let : MulAction K H := MulAction.compHom H (φ.comp K.subtype)
  ext x
  constructor
  · intro hx ⟨l, hl⟩
    exact hx l hl
  · intro hx l hl
    exact hx ⟨l, hl⟩

end OddOrder.GroupTheory
