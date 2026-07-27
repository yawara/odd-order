/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Isaacs Problems 8A (pp. 235–236) — 1 次元アフィン群

**Problem 8A.11**: `AGL(1, F) = {x ↦ ax + b}` は `F` 上 sharply 2-transitive で,
metabelian ゆえ可解。有限体は各素数冪について存在するので, 次数 `q` の可解
sharply 2-transitive 群が得られる。

## Main results

- `affineLineGroup`, `existsUnique_affineLineGroup_of_ne`,
  `affineLineGroup_isSolvable` — **Problem 8A.11**。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

section /- Problems 8A (pp. 235-236) -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-! ### Problem 8A.11 — 1 次元アフィン群 `AGL(1, F)` -/

section AffineLine

variable {F : Type*} [Field F]

/-- `x ↦ a * x + b` (`a` は単元) が定める `F` の置換。 -/
def affineLinePerm (a : Fˣ) (b : F) : Equiv.Perm F :=
  (Equiv.mulLeft₀ (a : F) a.ne_zero).trans (Equiv.addRight b)

@[simp] lemma affineLinePerm_apply (a : Fˣ) (b x : F) :
    affineLinePerm a b x = (a : F) * x + b := rfl

/-- **1 次元アフィン群** `AGL(1, F) = {x ↦ a x + b : a ∈ Fˣ, b ∈ F}` — `Sym(F)` の部分群。

`q = |F|` のとき位数は `q(q - 1)` で, `F` 上 sharply 2-transitive
(`existsUnique_affineLineGroup_of_ne`)。 -/
def affineLineGroup (F : Type*) [Field F] : Subgroup (Equiv.Perm F) where
  carrier := {p | ∃ (a : Fˣ) (b : F), p = affineLinePerm a b}
  one_mem' := ⟨1, 0, by ext x; simp⟩
  mul_mem' := by
    rintro - - ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    refine ⟨a * a', (a : F) * b' + b, Equiv.ext fun x => ?_⟩
    simp only [Equiv.Perm.mul_apply, affineLinePerm_apply, Units.val_mul]
    ring
  inv_mem' := by
    rintro - ⟨a, b, rfl⟩
    refine ⟨a⁻¹, -(((a⁻¹ : Fˣ) : F) * b), inv_eq_of_mul_eq_one_right (Equiv.ext fun x => ?_)⟩
    simp only [Equiv.Perm.mul_apply, affineLinePerm_apply, Equiv.Perm.one_apply, mul_add,
      mul_neg, ← mul_assoc, Units.mul_inv, one_mul]
    ring

lemma mem_affineLineGroup_iff {p : Equiv.Perm F} :
    p ∈ affineLineGroup F ↔ ∃ (a : Fˣ) (b : F), p = affineLinePerm a b :=
  ⟨fun h => h, fun h => h⟩

/-- **Isaacs Problem 8A.11** (p. 236): `AGL(1, F)` は `F` 上 **sharply 2-transitive** —
相異なる 2 点の任意の組を相異なる 2 点の任意の組へ移す元がちょうど 1 つある。

`a = (y₁ - y₂)/(x₁ - x₂)`, `b = y₁ - a x₁` が唯一の解 (アフィン写像は 2 点での値で決まる)。
有限体は各素数冪 `q > 1` について存在するので, これで次数 `q` の可解 sharply 2-transitive
置換群の存在が言える (可解性は `affineLineGroup_isSolvable`)。 -/
theorem existsUnique_affineLineGroup_of_ne {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂) :
    ∃! p : ↥(affineLineGroup F),
      (p : Equiv.Perm F) x₁ = y₁ ∧ (p : Equiv.Perm F) x₂ = y₂ := by
  have hxsub : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hysub : y₁ - y₂ ≠ 0 := sub_ne_zero.mpr hy
  set a : Fˣ := Units.mk0 ((y₁ - y₂) / (x₁ - x₂)) (div_ne_zero hysub hxsub) with ha
  have hacoe : (a : F) = (y₁ - y₂) / (x₁ - x₂) := rfl
  have hax : (a : F) * (x₁ - x₂) = y₁ - y₂ := by
    rw [hacoe, div_mul_cancel₀ _ hxsub]
  refine ⟨⟨affineLinePerm a (y₁ - (a : F) * x₁),
    mem_affineLineGroup_iff.mpr ⟨a, _, rfl⟩⟩, ⟨by simp, ?_⟩, ?_⟩
  · simp only [affineLinePerm_apply]
    linear_combination -hax
  · rintro ⟨q, hq⟩ ⟨h1, h2⟩
    obtain ⟨a', b', rfl⟩ := mem_affineLineGroup_iff.mp hq
    simp only [affineLinePerm_apply] at h1 h2
    have hA : (a' : F) = (a : F) := by
      have hthis : (a' : F) * (x₁ - x₂) = y₁ - y₂ := by linear_combination h1 - h2
      rw [hacoe, eq_div_iff hxsub]
      exact hthis
    have hB : b' = y₁ - (a : F) * x₁ := by rw [← hA]; linear_combination h1
    refine Subtype.ext (Equiv.ext fun x => ?_)
    simp only [affineLinePerm_apply, hA, hB]

/-- `AGL(1,F)` の元の**線形部分** `a`。`p x = a x + b` から `a = p 1 - p 0` として取り出す。 -/
def affineLinearPart (p : ↥(affineLineGroup F)) : Fˣ :=
  Units.mk0 ((p : Equiv.Perm F) 1 - (p : Equiv.Perm F) 0) <| by
    obtain ⟨a, b, hab⟩ := mem_affineLineGroup_iff.mp p.2
    rw [show ((p : Equiv.Perm F)) = affineLinePerm a b from hab]
    simp

lemma affineLinearPart_affineLinePerm (a : Fˣ) (b : F)
    (h : affineLinePerm a b ∈ affineLineGroup F) :
    affineLinearPart ⟨affineLinePerm a b, h⟩ = a := by
  refine Units.ext ?_
  simp [affineLinearPart]

/-- 線形部分は準同型 `AGL(1,F) →* Fˣ`。 -/
def affineLinearPartHom : ↥(affineLineGroup F) →* Fˣ where
  toFun := affineLinearPart
  map_one' := by
    refine Units.ext ?_
    simp [affineLinearPart]
  map_mul' p q := by
    obtain ⟨a, b, hab⟩ := mem_affineLineGroup_iff.mp p.2
    obtain ⟨a', b', hab'⟩ := mem_affineLineGroup_iff.mp q.2
    refine Units.ext ?_
    simp only [affineLinearPart, Units.val_mk0, Units.val_mul, Subgroup.coe_mul,
      Equiv.Perm.mul_apply, hab, hab', affineLinePerm_apply]
    ring

/-- 平行移動群 (= 線形部分が `1`) は可換。 -/
instance affineLinearPartHom_ker_isSolvable :
    IsSolvable ↥(MonoidHom.ker (affineLinearPartHom (F := F))) := by
  refine isSolvable_of_comm fun p q => ?_
  obtain ⟨a, b, hab⟩ := mem_affineLineGroup_iff.mp (p : ↥(affineLineGroup F)).2
  obtain ⟨a', b', hab'⟩ := mem_affineLineGroup_iff.mp (q : ↥(affineLineGroup F)).2
  have hlin : ∀ (r : ↥(MonoidHom.ker (affineLinearPartHom (F := F)))) (c : Fˣ) (d : F),
      ((r : ↥(affineLineGroup F)) : Equiv.Perm F) = affineLinePerm c d → c = 1 := by
    intro r c d hr
    have hk : affineLinearPart (r : ↥(affineLineGroup F)) = 1 := MonoidHom.mem_ker.mp r.2
    rw [show (r : ↥(affineLineGroup F)) = ⟨affineLinePerm c d, hr ▸ (r : ↥(affineLineGroup F)).2⟩
      from Subtype.ext hr, affineLinearPart_affineLinePerm] at hk
    exact hk
  have ha : a = 1 := hlin p a b hab
  have ha' : a' = 1 := hlin q a' b' hab'
  refine Subtype.ext (Subtype.ext (Equiv.ext fun x => ?_))
  simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hab, hab', ha, ha',
    affineLinePerm_apply, Units.val_one, one_mul]
  ring

/-- **Isaacs Problem 8A.11** (p. 236) の可解性: `AGL(1,F)` は metabelian ゆえ**可解**。

線形部分 `p ↦ a` は `Fˣ` への準同型で, その核は平行移動群 `≅ F⁺` (可換)。 -/
instance affineLineGroup_isSolvable : IsSolvable ↥(affineLineGroup F) :=
  solvable_of_ker_le_range (MonoidHom.ker (affineLinearPartHom (F := F))).subtype
    affineLinearPartHom (le_of_eq (Subgroup.range_subtype _).symm)

end AffineLine

end

end OddOrder.Isaacs.Ch08
