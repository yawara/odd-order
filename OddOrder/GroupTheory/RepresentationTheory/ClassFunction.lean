/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Star.Basic

/-!
# Class functions on a group

A **class function** on a group `G` valued in a commutative ring `k` is a function
`G → k` that is constant on conjugacy classes: `f (h * g * h⁻¹) = f g`.

## mathlib v4.29.1 状況

mathlib に `ClassFunction G k` という型は **存在しない** (Peterfalvi audit 2026-05-23).
`Mathlib/RepresentationTheory/Character.lean` の `Representation.character` は単に関数
`G → k` で, conj-invariance は `Representation.char_conj` 補題として持つのみ.

本モジュールは **Peterfalvi Wave 1a 起点** として `ClassFunction G k` を新規定義し,
§3-§8 (Dade isometry / Coherence) で頻出する `CF(G) / CF(G, A) / ⟨α, β⟩_G` を統一的に
扱えるようにする.

## Main definitions

* `classFunctionSubmodule G k` — conj-invariant な `G → k` 全体 (`Submodule k (G → k)`).
* `ClassFunction G k` — 同 submodule の元の型. `AddCommGroup`, `Module k` instance 付き.
* `CoeFun` — `(φ : ClassFunction G k) (g : G) : k` を `φ g` で書ける.

## TODO (本 commit 範囲外)

- mathlib `Representation.character` からの coercion.

## References

* Peterfalvi §2 (notation).
* Audit: [`notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md`]
  (../../../notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md) §3.1, §6.1.

-/

namespace OddOrder.RepresentationTheory

/-- The submodule of class functions on `G` valued in `k`:
functions `f : G → k` satisfying `f (h * g * h⁻¹) = f g`. -/
def classFunctionSubmodule (G : Type*) [Group G] (k : Type*) [CommRing k] :
    Submodule k (G → k) where
  carrier := { f | ∀ g h : G, f (h * g * h⁻¹) = f g }
  add_mem' {f₁ f₂} h₁ h₂ g h := by
    simp only [Pi.add_apply]
    rw [h₁ g h, h₂ g h]
  zero_mem' _ _ := rfl
  smul_mem' c f hf g h := by
    simp only [Pi.smul_apply]
    rw [hf]

/-- A **class function** on `G` valued in `k`: a function `G → k` constant on
conjugacy classes. -/
def ClassFunction (G : Type*) [Group G] (k : Type*) [CommRing k] : Type _ :=
  ↥(classFunctionSubmodule G k)

namespace ClassFunction

variable {G : Type*} [Group G] {k : Type*} [CommRing k]

instance instAddCommGroup : AddCommGroup (ClassFunction G k) :=
  inferInstanceAs (AddCommGroup ↥(classFunctionSubmodule G k))

instance instModule : Module k (ClassFunction G k) :=
  inferInstanceAs (Module k ↥(classFunctionSubmodule G k))

instance : CoeFun (ClassFunction G k) (fun _ => G → k) :=
  ⟨fun φ => (φ.val : G → k)⟩

@[simp] theorem coe_mk (f : G → k) (hf) :
    ((⟨f, hf⟩ : ClassFunction G k) : G → k) = f := rfl

/-- Conjugation invariance: the defining property of a class function. -/
theorem conj_eq (φ : ClassFunction G k) (g h : G) : φ (h * g * h⁻¹) = φ g :=
  φ.property g h

/-- A class function is constant on conjugacy classes (`IsConj` form). -/
theorem of_isConj (φ : ClassFunction G k) {g₁ g₂ : G} (hg : IsConj g₁ g₂) :
    φ g₁ = φ g₂ := by
  obtain ⟨h, rfl⟩ := isConj_iff.mp hg
  exact (φ.conj_eq g₁ h).symm

@[ext]
theorem ext {φ ψ : ClassFunction G k} (h : ∀ g, φ g = ψ g) : φ = ψ :=
  Subtype.ext (funext h)

@[simp] theorem zero_apply (g : G) : (0 : ClassFunction G k) g = 0 := rfl

@[simp] theorem add_apply (φ ψ : ClassFunction G k) (g : G) :
    (φ + ψ) g = φ g + ψ g := rfl

@[simp] theorem neg_apply (φ : ClassFunction G k) (g : G) : (-φ) g = -φ g := rfl

@[simp] theorem sub_apply (φ ψ : ClassFunction G k) (g : G) :
    (φ - ψ) g = φ g - ψ g := rfl

@[simp] theorem smul_apply (c : k) (φ : ClassFunction G k) (g : G) :
    (c • φ) g = c * φ g := rfl

section Restrict

variable {G : Type*} [Group G] {k : Type*} [CommRing k]

/-- The **restriction** `Res^G_H φ : ClassFunction ↥H k` of a class function on `G`
to a subgroup `H ≤ G`. -/
def restrict (H : Subgroup G) (φ : ClassFunction G k) : ClassFunction ↥H k :=
  ⟨fun h => φ (h : G), fun h₁ h₂ => by
    change φ ((h₂ : G) * (h₁ : G) * ((h₂⁻¹ : H) : G)) = φ (h₁ : G)
    rw [show ((h₂⁻¹ : H) : G) = (h₂ : G)⁻¹ from rfl]
    exact φ.conj_eq h₁ h₂⟩

@[simp] theorem restrict_apply (H : Subgroup G) (φ : ClassFunction G k) (h : H) :
    (restrict H φ) h = φ (h : G) := rfl

@[simp] theorem restrict_zero (H : Subgroup G) :
    restrict H (0 : ClassFunction G k) = 0 := by
  ext h; simp

theorem restrict_add (H : Subgroup G) (φ ψ : ClassFunction G k) :
    restrict H (φ + ψ) = restrict H φ + restrict H ψ := by
  ext h; simp

theorem restrict_smul (H : Subgroup G) (c : k) (φ : ClassFunction G k) :
    restrict H (c • φ) = c • restrict H φ := by
  ext h; simp

end Restrict

section Support

variable {G : Type*} [Group G] {k : Type*} [CommRing k]

/-- The **support** of a class function: `{ g | φ g ≠ 0 }`. Closed under
conjugation by the defining property. -/
def support (φ : ClassFunction G k) : Set G := { g | φ g ≠ 0 }

@[simp] theorem mem_support {φ : ClassFunction G k} {g : G} :
    g ∈ φ.support ↔ φ g ≠ 0 := Iff.rfl

theorem support_conj_iff (φ : ClassFunction G k) (g h : G) :
    h * g * h⁻¹ ∈ φ.support ↔ g ∈ φ.support := by
  simp [mem_support, φ.conj_eq]

@[simp] theorem support_zero : (0 : ClassFunction G k).support = ∅ := by
  ext g; simp

theorem mem_support_of_isConj {φ : ClassFunction G k} {g₁ g₂ : G}
    (hg : IsConj g₁ g₂) (h : g₁ ∈ φ.support) : g₂ ∈ φ.support := by
  rw [mem_support, ← φ.of_isConj hg]
  exact h

/-- The support of a sum is contained in the union of the supports. -/
theorem support_add_subset (φ ψ : ClassFunction G k) :
    (φ + ψ).support ⊆ φ.support ∪ ψ.support := by
  intro g hg
  by_cases hφ : φ g = 0
  · right
    by_contra hψ
    have hψ_zero : ψ g = 0 := by simpa [mem_support] using hψ
    exact hg (by simp [hφ, hψ_zero])
  · left
    exact hφ

/-- The support of a scalar multiple is contained in the original support. -/
theorem support_smul_subset (c : k) (φ : ClassFunction G k) :
    (c • φ).support ⊆ φ.support := by
  intro g hg
  by_contra hφ
  have hφ_zero : φ g = 0 := by simpa [mem_support] using hφ
  exact hg (by simp [hφ_zero])

/-- The submodule of class functions supported on `A`.

This is Peterfalvi's `CF(G, A)`. -/
def supportedSubmodule (A : Set G) : Submodule k (ClassFunction G k) where
  carrier := { φ | φ.support ⊆ A }
  zero_mem' := by
    intro g hg
    simp [support] at hg
  add_mem' {φ ψ} hφ hψ := by
    intro g hg
    rcases support_add_subset φ ψ hg with h | h
    · exact hφ h
    · exact hψ h
  smul_mem' c φ hφ := by
    intro g hg
    exact hφ (support_smul_subset c φ hg)

@[simp] theorem mem_supportedSubmodule {A : Set G} {φ : ClassFunction G k} :
    φ ∈ supportedSubmodule (G := G) (k := k) A ↔ φ.support ⊆ A := Iff.rfl

end Support

section Inner

variable {G : Type*} [Group G] [Fintype G]
variable {k : Type*} [CommRing k] [StarRing k]

/-- The **unscaled inner sum** of two class functions: `Σ_g φ(g) * star(ψ(g))`.

Peterfalvi's `(α, β)_G = (1/|G|) Σ_g α(g) · β̄(g)` corresponds to this sum
divided by `Nat.card G`. We expose the bare sum here so that the user can
choose how to invert `|G|` (e.g. in a field of characteristic prime to `|G|`,
or formally as `Nat.card G : ℂ`). -/
def innerSum (φ ψ : ClassFunction G k) : k :=
  ∑ g : G, φ g * star (ψ g)

@[simp] theorem innerSum_zero_left (ψ : ClassFunction G k) :
    innerSum (0 : ClassFunction G k) ψ = 0 := by
  simp [innerSum]

@[simp] theorem innerSum_zero_right (φ : ClassFunction G k) :
    innerSum φ (0 : ClassFunction G k) = 0 := by
  simp [innerSum]

theorem innerSum_add_left (φ₁ φ₂ ψ : ClassFunction G k) :
    innerSum (φ₁ + φ₂) ψ = innerSum φ₁ ψ + innerSum φ₂ ψ := by
  simp [innerSum, add_mul, Finset.sum_add_distrib]

theorem innerSum_add_right (φ ψ₁ ψ₂ : ClassFunction G k) :
    innerSum φ (ψ₁ + ψ₂) = innerSum φ ψ₁ + innerSum φ ψ₂ := by
  simp [innerSum, star_add, mul_add, Finset.sum_add_distrib]

theorem innerSum_smul_left (c : k) (φ ψ : ClassFunction G k) :
    innerSum (c • φ) ψ = c * innerSum φ ψ := by
  rw [innerSum, innerSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [smul_apply, mul_assoc]

theorem innerSum_neg_left (φ ψ : ClassFunction G k) :
    innerSum (-φ) ψ = -innerSum φ ψ := by
  simp [innerSum, neg_mul, Finset.sum_neg_distrib]

theorem innerSum_neg_right (φ ψ : ClassFunction G k) :
    innerSum φ (-ψ) = -innerSum φ ψ := by
  simp [innerSum, mul_neg, Finset.sum_neg_distrib]

end Inner

end ClassFunction

end OddOrder.RepresentationTheory
