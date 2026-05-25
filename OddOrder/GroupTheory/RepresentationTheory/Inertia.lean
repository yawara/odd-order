/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Tactic.Group
import OddOrder.GroupTheory.RepresentationTheory.ClassFunction

/-!
# Conjugation action on class functions and the inertia group

For a normal subgroup `H ⊴ G` and a class function `θ : ClassFunction ↥H k`, the
**conjugate** `θ.conjBy g : ClassFunction ↥H k` (Peterfalvi's `θ^g`) is defined by

  `θ.conjBy g h = θ (g * h * g⁻¹)` for `h ∈ ↥H`.

This is well-defined because `H ⊴ G` ensures `g * h * g⁻¹ ∈ H`. The map
`g ↦ θ.conjBy g` is a `G`-action on `ClassFunction ↥H k`.

The **inertia group** of `θ` in `G` is the stabilizer:

  `inertia θ = { g ∈ G | θ.conjBy g = θ }`.

Peterfalvi notation `I_G(θ)`. Used heavily in §3 (1.5)/(1.7) (Clifford) and §4-§8.

## mathlib v4.29.1 状況

mathlib に「class function 上の G-action」「Inertia group」は不在 (Peterfalvi audit
2026-05-23 確認済). 本モジュールで新規定義.

## Main definitions

* `ClassFunction.conjBy g θ` — `θ` を `g ∈ G` で conjugate した class function (`H ⊴ G`).
* `ClassFunction.inertia θ : Subgroup G` — stabilizer subgroup.

## TODO (本 commit 範囲外)

- `H ≤ inertia θ` (∵ H 内部 conjugation で θ 不変).
- `inertia θ` の `H ⊴ inertia θ` (normal).
- `MulAction G (ClassFunction ↥H k)` instance (要 H ⊴ G 抽象化).

## References

* Peterfalvi §2 line 25 (`θ^g` notation), §3 (1.5) (Clifford suite), §3 (1.7).

-/

namespace OddOrder.RepresentationTheory

namespace ClassFunction

variable {G : Type*} [Group G] {H : Subgroup G} [hH : H.Normal]
variable {k : Type*} [CommRing k]

/-- The conjugate of `θ : ClassFunction ↥H k` by `g : G`. Defined by
`(θ.conjBy g) h = θ (g * h * g⁻¹)`. Well-defined since `H ⊴ G`. -/
def conjBy (g : G) (θ : ClassFunction ↥H k) : ClassFunction ↥H k where
  val h := θ ⟨g * (h : G) * g⁻¹, hH.conj_mem (h : G) h.property g⟩
  property h₁ h₂ := by
    have hy : g * (h₂ : G) * g⁻¹ ∈ H := hH.conj_mem (h₂ : G) h₂.property g
    let y : ↥H := ⟨g * (h₂ : G) * g⁻¹, hy⟩
    have key : (⟨g * ((h₂ * h₁ * h₂⁻¹ : ↥H) : G) * g⁻¹,
                  hH.conj_mem _ (h₂ * h₁ * h₂⁻¹ : ↥H).property g⟩ : ↥H)
             = y * ⟨g * (h₁ : G) * g⁻¹, hH.conj_mem _ h₁.property g⟩ * y⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      change g * ((h₂ : G) * (h₁ : G) * (h₂ : G)⁻¹) * g⁻¹
        = (g * (h₂ : G) * g⁻¹) * (g * (h₁ : G) * g⁻¹) * (g * (h₂ : G) * g⁻¹)⁻¹
      group
    change θ ⟨g * ((h₂ * h₁ * h₂⁻¹ : ↥H) : G) * g⁻¹, _⟩
         = θ ⟨g * (h₁ : G) * g⁻¹, _⟩
    rw [key]
    exact θ.conj_eq _ y

@[simp] theorem conjBy_apply (g : G) (θ : ClassFunction ↥H k) (h : ↥H) :
    (conjBy g θ) h = θ ⟨g * (h : G) * g⁻¹, hH.conj_mem (h : G) h.property g⟩ := rfl

@[simp] theorem conjBy_one (θ : ClassFunction ↥H k) : conjBy (1 : G) θ = θ := by
  ext h
  simp

theorem conjBy_mul (g₁ g₂ : G) (θ : ClassFunction ↥H k) :
    conjBy (g₁ * g₂) θ = conjBy g₂ (conjBy g₁ θ) := by
  ext h
  let h' : ↥H := ⟨g₂ * (h : G) * g₂⁻¹, hH.conj_mem _ h.property g₂⟩
  change θ ⟨(g₁ * g₂) * (h : G) * (g₁ * g₂)⁻¹, _⟩
      = θ ⟨g₁ * (h' : G) * g₁⁻¹, _⟩
  apply congrArg θ
  apply Subtype.ext
  change (g₁ * g₂) * (h : G) * (g₁ * g₂)⁻¹ = g₁ * (g₂ * (h : G) * g₂⁻¹) * g₁⁻¹
  group

/-- The **inertia group** of a class function `θ` under `G`-conjugation:
`I_G(θ) = { g ∈ G | θ^g = θ }`. -/
def inertia (θ : ClassFunction ↥H k) : Subgroup G where
  carrier := { g | conjBy g θ = θ }
  one_mem' := by
    change conjBy (1 : G) θ = θ
    exact conjBy_one θ
  mul_mem' {g₁ g₂} hg₁ hg₂ := by
    change conjBy g₁ θ = θ at hg₁
    change conjBy g₂ θ = θ at hg₂
    change conjBy (g₁ * g₂) θ = θ
    rw [conjBy_mul, hg₁, hg₂]
  inv_mem' {g} hg := by
    change conjBy g θ = θ at hg
    change conjBy g⁻¹ θ = θ
    have hprod : conjBy (g * g⁻¹) θ = θ := by
      simp
    rw [conjBy_mul, hg] at hprod
    simpa using hprod

@[simp] theorem mem_inertia {θ : ClassFunction ↥H k} {g : G} :
    g ∈ inertia θ ↔ conjBy g θ = θ := Iff.rfl

end ClassFunction

end OddOrder.RepresentationTheory
