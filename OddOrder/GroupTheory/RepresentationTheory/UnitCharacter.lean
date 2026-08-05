/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerInductionDescent

/-!
# Linear characters over an arbitrary field, and the coset indicator

A group homomorphism `λ : H →* Kˣ` gives a one-dimensional representation `h ↦ λ h • id`, whose
character is `h ↦ (λ h : K)`.  Powers `λ ^ i` are again such homomorphisms, so the whole family
`{λ ^ i}` consists of genuine characters.

The point of the file is Gorenstein's function (7.12)–(7.13) in the proof of Lemma 7.6
(issue 9508, 段 E).  If `λ` has order `n` at `u` — that is, `λ u = ζ` is a primitive `n`-th root of
unity — and every `λ h` is an `n`-th root of unity, then

`∑_{i < n} ζ^{-i} (λ h)^i  =  n` if `λ h = ζ`, and `0` otherwise,

a bare geometric sum.  So that combination is the **indicator of the fibre `λ⁻¹(ζ)`, scaled by
`n`** — which for `λ` a character of `H = ⟨u⟩ × P` with kernel `P` is exactly `|U| · 1_{uP}`.
Being a `ℤ[ω]`-combination of characters it lies in `ch_R(H)`, which is what places the induced
function in `v_R(G)`.

## Main definitions

* `OddOrder.RepresentationTheory.unitRepresentation` — the one-dimensional representation

## Main results

* `OddOrder.RepresentationTheory.isRepCharacter_unitCharacter`
* `OddOrder.RepresentationTheory.sum_inv_pow_mul_pow` — the geometric sum
* `OddOrder.RepresentationTheory.fibreIndicator_mem_adjoinSpan` — the indicator lies in `ch_R(H)`

## References

* D. Gorenstein, *Finite Groups*, §4.7, Lemma 7.6 (`references/gorenstein/pages/`).
-/

namespace OddOrder.RepresentationTheory

variable {K H : Type*} [Field K] [Group H]

/-! ### One-dimensional representations -/

/-- **The one-dimensional representation** attached to `λ : H →* Kˣ`. -/
noncomputable def unitRepresentation (lam : H →* Kˣ) : Representation K H (Fin 1 → K) where
  toFun h := (lam h : K) • LinearMap.id
  map_one' := by rw [map_one, Units.val_one, one_smul, Module.End.one_eq_id]
  map_mul' g h := by
    rw [Module.End.mul_eq_comp, LinearMap.smul_comp, LinearMap.id_comp, smul_smul,
      ← Units.val_mul, ← map_mul]

@[simp]
theorem unitRepresentation_apply (lam : H →* Kˣ) (h : H) :
    unitRepresentation (K := K) lam h = (lam h : K) • LinearMap.id := rfl

@[simp]
theorem character_unitRepresentation (lam : H →* Kˣ) (h : H) :
    (unitRepresentation (K := K) lam).character h = (lam h : K) := by
  rw [Representation.character, unitRepresentation_apply, map_smul, LinearMap.trace_id]
  simp

/-- A homomorphism to the units is a genuine character. -/
theorem isRepCharacter_unitCharacter (lam : H →* Kˣ) :
    IsRepCharacter K (fun h => (lam h : K)) := by
  have := isRepCharacter_of_finite (unitRepresentation (K := K) lam)
  simpa [funext fun h => character_unitRepresentation (K := K) lam h] using this

theorem mem_virtualCharacters_unitCharacter (lam : H →* Kˣ) :
    (fun h => (lam h : K)) ∈ virtualCharacters K H :=
  (isRepCharacter_unitCharacter lam).mem_virtualCharacters

/-! ### The geometric sum -/

open scoped Classical in
/-- **The fibre indicator as a geometric sum.**  For `x` an `n`-th root of unity and `ζ` a
primitive one, `∑_{i < n} ζ^{-i} x^i` is `n` when `x = ζ` and `0` otherwise. -/
theorem sum_inv_pow_mul_pow {n : ℕ} (hn : 0 < n) {ζ x : K} (hζ : IsPrimitiveRoot ζ n)
    (hx : x ^ n = 1) :
    (∑ i ∈ Finset.range n, (ζ ^ i)⁻¹ * x ^ i) = if x = ζ then (n : K) else 0 := by
  have hζ0 : ζ ≠ 0 := by
    intro h
    exact absurd (h ▸ hζ.pow_eq_one) (by simp [zero_pow hn.ne'])
  have hrw : ∀ i ∈ Finset.range n, (ζ ^ i)⁻¹ * x ^ i = (ζ⁻¹ * x) ^ i := by
    intro i _
    rw [mul_pow, inv_pow]
  rw [Finset.sum_congr rfl hrw]
  by_cases h : x = ζ
  · subst h
    rw [inv_mul_cancel₀ hζ0]
    simp
  · have hne : ζ⁻¹ * x ≠ 1 := by
      intro hc
      exact h (by field_simp at hc; rw [← hc])
    have hpow : (ζ⁻¹ * x) ^ n = 1 := by
      rw [mul_pow, inv_pow, hζ.pow_eq_one, hx, inv_one, mul_one]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div, if_neg h]

/-! ### The indicator lies in `ch_R(H)` -/

open scoped Classical in
/-- **Gorenstein (7.12)–(7.13)**: `n · 1_{λ⁻¹(ζ)}` is a `ℤ[ω]`-combination of characters, hence
lies in `ch_R(H)`, provided `ζ` and the values of `λ` are powers of `ω`. -/
theorem fibreIndicator_mem_adjoinSpan [CharZero K] {ω : K} (hω : IsIntegral ℤ ω) {n : ℕ}
    (hn : 0 < n)
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (lam : H →* Kˣ) (hlam : ∀ h : H, (lam h : K) ^ n = 1)
    (hinv : ∀ i : ℕ, (ζ ^ i)⁻¹ ∈ Algebra.adjoin ℤ ({ω} : Set K)) :
    (fun h => if (lam h : K) = ζ then (n : K) else 0)
      ∈ adjoinSpan ω (virtualCharacters K H) := by
  have hsum : (fun h => if (lam h : K) = ζ then (n : K) else 0)
      = ∑ i ∈ Finset.range n, (fun h => (ζ ^ i)⁻¹ * ((lam ^ i) h : K)) := by
    funext h
    rw [Finset.sum_apply]
    exact (sum_inv_pow_mul_pow hn hζ (hlam h)).symm
  rw [hsum]
  refine sum_mem fun i _ => ?_
  have hmem : (fun h => ((lam ^ i) h : K)) ∈ virtualCharacters K H :=
    mem_virtualCharacters_unitCharacter (lam ^ i)
  have heq : (fun h => (ζ ^ i)⁻¹ * ((lam ^ i) h : K))
      = (ζ ^ i)⁻¹ • (fun h : H => ((lam ^ i) h : K)) := by
    funext h
    simp
  rw [heq]
  exact smul_mem_adjoinSpan_of_mem_adjoin hω (hinv i) hmem

end OddOrder.RepresentationTheory
