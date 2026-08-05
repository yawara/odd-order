/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.PRegularCosetCount

/-!
# The linear character of `H = ⟨u⟩ P` with kernel `P`

Gorenstein's `ψ_i` in the proof of Lemma 7.6 (issue 9508, 段 E) are the irreducible characters of
`U × P` containing `P` in their kernel.  As noted in `UnitCharacter`, a single one of them and its
powers suffice, so all that is needed is **one** homomorphism

`λ : H →* Kˣ`  with  `λ u = ζ`  and  `P ≤ ker λ`,

for `ζ` a primitive `n`-th root of unity, `n = orderOf u`.

Every `h ∈ H` is `u ^ a * v` with `v ∈ P`, and `u ^ a` is then forced to be the `p'`-part of `h`
(`eq_pRegularPart_of_mem_leftCosetOf`-style uniqueness), so `a` is well defined modulo `n` and
`λ h := ζ ^ a` is a homomorphism.  No cyclic-group character theory is needed: the uniqueness of
the commuting `p'`-times-`p` decomposition does all the work.

## Main definitions

* `OddOrder.RepresentationTheory.cosetCharacter` — the homomorphism `λ`

## Main results

* `OddOrder.RepresentationTheory.pRegularPart_pow_mul` — `p'`-part of `u ^ a * v` is `u ^ a`
* `OddOrder.RepresentationTheory.cosetCharacter_apply_eq_iff` — `λ h = ζ ↔ h ∈ u P`

## References

* D. Gorenstein, *Finite Groups*, §4.7, Lemma 7.6 (`references/gorenstein/pages/`).
-/

namespace OddOrder.RepresentationTheory

open OddOrder.GroupTheory

variable {G K : Type*} [Group G] [Field K] {p : ℕ} {u : G} {P H : Subgroup G} {ζ : Kˣ}

/-- **The `p'`-part of `u ^ a * v` is `u ^ a`** when `u` is `p`-regular, `v` a `p`-element of `P`,
and the two commute. -/
theorem pRegularPart_pow_mul (hp : p.Prime) (hu : IsPRegular p u) (hPp : IsPGroup p ↥P)
    (hcomm : ∀ v ∈ P, Commute u v) (a : ℕ) {v : G} (hv : v ∈ P) :
    pRegularPart p (u ^ a * v) = u ^ a := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ((eq_pPart_of_commute hp ?_ (isPElement_of_mem_of_isPGroup hPp hv) (hu.pow a) rfl).2).symm
  exact ((hcomm v hv).pow_left a).symm

/-- Two decompositions `u ^ a * v = u ^ b * w` force `u ^ a = u ^ b`. -/
theorem pow_eq_pow_of_pow_mul_eq (hp : p.Prime) (hu : IsPRegular p u) (hPp : IsPGroup p ↥P)
    (hcomm : ∀ v ∈ P, Commute u v) {a b : ℕ} {v w : G} (hv : v ∈ P) (hw : w ∈ P)
    (h : u ^ a * v = u ^ b * w) : u ^ a = u ^ b := by
  rw [← pRegularPart_pow_mul hp hu hPp hcomm a hv, ← pRegularPart_pow_mul hp hu hPp hcomm b hw, h]

variable (hp : p.Prime) (hu : IsPRegular p u) (hPp : IsPGroup p ↥P)
  (hcomm : ∀ v ∈ P, Commute u v) (hord : orderOf ζ = orderOf u)
  (hgen : ∀ h : G, h ∈ H → ∃ (a : ℕ) (v : G), v ∈ P ∧ h = u ^ a * v)

include hp hu hPp hcomm hord in
/-- The exponent is well defined modulo `orderOf u`, hence `ζ ^ a` is well defined. -/
theorem zpow_eq_of_pow_mul_eq {a b : ℕ} {v w : G} (hv : v ∈ P) (hw : w ∈ P)
    (h : u ^ a * v = u ^ b * w) : ζ ^ a = ζ ^ b := by
  have hu' : u ^ a = u ^ b := pow_eq_pow_of_pow_mul_eq hp hu hPp hcomm hv hw h
  rw [pow_eq_pow_iff_modEq] at hu' ⊢
  rwa [hord]

include hp hu hPp hcomm hord hgen in
/-- The defining property of the character: on any decomposition it is `ζ ^ a`. -/
theorem exists_cosetCharacter_spec (h : ↥H) :
    ∃ c : Kˣ, ∀ (a : ℕ) (v : G), v ∈ P → (h : G) = u ^ a * v → c = ζ ^ a := by
  obtain ⟨a₀, v₀, hv₀, hh₀⟩ := hgen (h : G) h.2
  refine ⟨ζ ^ a₀, fun a v hv hh => ?_⟩
  exact zpow_eq_of_pow_mul_eq hp hu hPp hcomm hord hv₀ hv (hh₀ ▸ hh)

open scoped Classical in
include hp hu hPp hcomm hord hgen in
/-- **The linear character `λ` of `H = ⟨u⟩ P`** with `λ u = ζ` and `P` in its kernel. -/
noncomputable def cosetCharacter : ↥H →* Kˣ where
  toFun h := Classical.choose (exists_cosetCharacter_spec hp hu hPp hcomm hord hgen h)
  map_one' := by
    have hspec := Classical.choose_spec (exists_cosetCharacter_spec hp hu hPp hcomm hord hgen 1)
    simpa using hspec 0 1 P.one_mem (by simp)
  map_mul' h₁ h₂ := by
    obtain ⟨a₁, v₁, hv₁, hh₁⟩ := hgen (h₁ : G) h₁.2
    obtain ⟨a₂, v₂, hv₂, hh₂⟩ := hgen (h₂ : G) h₂.2
    have hs₁ := Classical.choose_spec
      (exists_cosetCharacter_spec hp hu hPp hcomm hord hgen h₁) a₁ v₁ hv₁ hh₁
    have hs₂ := Classical.choose_spec
      (exists_cosetCharacter_spec hp hu hPp hcomm hord hgen h₂) a₂ v₂ hv₂ hh₂
    have hprod : ((h₁ * h₂ : ↥H) : G) = u ^ (a₁ + a₂) * (v₁ * v₂) := by
      have : ((h₁ * h₂ : ↥H) : G) = (h₁ : G) * (h₂ : G) := rfl
      rw [this, hh₁, hh₂, pow_add]
      have hc : Commute v₁ (u ^ a₂) := ((hcomm v₁ hv₁).symm).pow_right a₂
      calc u ^ a₁ * v₁ * (u ^ a₂ * v₂) = u ^ a₁ * (v₁ * u ^ a₂) * v₂ := by
            simp only [mul_assoc]
        _ = u ^ a₁ * (u ^ a₂ * v₁) * v₂ := by rw [hc.eq]
        _ = u ^ a₁ * u ^ a₂ * (v₁ * v₂) := by simp only [mul_assoc]
    have hs := Classical.choose_spec
      (exists_cosetCharacter_spec hp hu hPp hcomm hord hgen (h₁ * h₂))
      (a₁ + a₂) (v₁ * v₂) (P.mul_mem hv₁ hv₂) hprod
    rw [hs, hs₁, hs₂, pow_add]

include hp hu hPp hcomm hord hgen in
theorem cosetCharacter_apply {h : ↥H} {a : ℕ} {v : G} (hv : v ∈ P) (hh : (h : G) = u ^ a * v) :
    cosetCharacter hp hu hPp hcomm hord hgen h = ζ ^ a :=
  Classical.choose_spec (exists_cosetCharacter_spec hp hu hPp hcomm hord hgen h) a v hv hh

include hp hu hPp hcomm hord hgen in
/-- **`λ h = ζ` exactly on the coset `u P`.** -/
theorem cosetCharacter_apply_eq_iff {h : ↥H} :
    cosetCharacter hp hu hPp hcomm hord hgen h = ζ ↔ (h : G) ∈ leftCosetOf u P := by
  obtain ⟨a, v, hv, hh⟩ := hgen (h : G) h.2
  rw [cosetCharacter_apply hp hu hPp hcomm hord hgen hv hh]
  constructor
  · intro hz
    have h1 : ζ ^ a = ζ ^ 1 := by rwa [pow_one]
    rw [pow_eq_pow_iff_modEq, hord] at h1
    have hua : u ^ a = u ^ 1 := by rw [pow_eq_pow_iff_modEq]; exact h1
    rw [mem_leftCosetOf, hh, hua, pow_one, inv_mul_cancel_left]
    exact hv
  · intro hmem
    rw [mem_leftCosetOf, hh] at hmem
    have heq : u ^ a * v = u ^ 1 * (u⁻¹ * (u ^ a * v)) := by
      rw [pow_one, mul_inv_cancel_left]
    have hkey : u ^ a = u ^ 1 := pow_eq_pow_of_pow_mul_eq hp hu hPp hcomm hv hmem heq
    rw [pow_eq_pow_iff_modEq, ← hord] at hkey
    rw [pow_eq_pow_iff_modEq.mpr hkey, pow_one]

end OddOrder.RepresentationTheory
