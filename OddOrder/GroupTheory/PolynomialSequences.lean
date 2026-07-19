/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.Main

/-!
# Polynomial sequences in a filtered group

A sequence `f : ℕ → G` is *polynomial* with respect to a descending filtration
`G = Γ₁ ⊇ Γ₂ ⊇ ⋯` with `⁅Γᵢ, Γⱼ⁆ ≤ Γ_{i+j}` when every `k`-fold iterated
multiplicative forward difference

`∂_{h_k} ⋯ ∂_{h_1} f`,   `∂_h f (n) = f (n + h) · (f n)⁻¹`,

takes values in `Γ_k`.  For `G` abelian and `Γ` trivial beyond `Γ₁` this is the
usual "`Δ^{k}f = 0`" notion of a degree-`< k` polynomial; in general it is the
Lazard–Leibman notion used for nilpotent groups.

The motivation here is P. Hall's collection formula (Bender–Glauberman,
Theorem E.1): the whole formula is the statement that

* `n ↦ aⁿ bⁿ` is a polynomial sequence for the lower central series, and
* every polynomial sequence has a binomial ("Taylor") expansion
  `f n = ∏ᵢ cᵢ^{C(n,i)}` with `cᵢ ∈ Γᵢ`.

This file proves the **first** item, in the sharp form of a closed formula for
the iterated differences of `n ↦ aⁿ bⁿ` (`mulFwdDiffList_cons_pow_mul_pow`).
That formula is short, and it is the only part of Hall's theorem that is about
`aⁿ bⁿ` rather than about polynomial sequences in general.

## Main definitions

* `OddOrder.GroupTheory.mulFwdDiff h f` — the multiplicative forward difference
  `n ↦ f (n + h) * (f n)⁻¹`.
* `OddOrder.GroupTheory.mulFwdDiffList hs f` — iterated differences, the head of
  `hs` being the *outermost* step.
* `OddOrder.GroupTheory.powCommWord a b hs h₁` — the iterated commutator
  `⁅a^{h_k}, ⁅…, ⁅a^{h_2}, b^{h_1}⁆…⁆⁆` for `hs = [h_k, …, h_2]`.

## Main results

* `mulFwdDiff_pow_mul_pow` — one difference:
  `∂_{h₁}(aᵐbᵐ)(n) = a^{n+h₁} · b^{h₁} · (a^{n+h₁})⁻¹ · a^{h₁}`.
* `mulFwdDiffList_cons_pow_mul_pow` — **the closed form**: for `k ≥ 2`,
  `∂_{h_k} ⋯ ∂_{h_1}(aᵐbᵐ)(n) = (powCommWord a b [h_k,…,h_2] h₁)^{a^{n+h₁}}`,
  a *conjugate of a fixed iterated commutator*, with no dependence on `n`
  except in the conjugator.
* `mulFwdDiffList_pow_mul_pow_mem` — consequently the `k`-fold difference lies
  in `γ_k` (the book's indexing; mathlib's `lowerCentralSeries (k - 1)`).
-/

namespace OddOrder.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ## Multiplicative forward differences -/

section Diff

/-- The multiplicative forward difference with step `h`:
`∂_h f (n) = f (n + h) · (f n)⁻¹`. -/
def mulFwdDiff (h : ℕ) (f : ℕ → G) : ℕ → G := fun n => f (n + h) * (f n)⁻¹

/-- Iterated multiplicative forward differences.  The **head** of the list is the
outermost step, so `mulFwdDiffList [h₂, h₁] f = ∂_{h₂} (∂_{h₁} f)`. -/
def mulFwdDiffList : List ℕ → (ℕ → G) → (ℕ → G)
  | [], f => f
  | h :: hs, f => mulFwdDiff h (mulFwdDiffList hs f)

@[simp] theorem mulFwdDiffList_nil (f : ℕ → G) : mulFwdDiffList [] f = f := rfl

@[simp] theorem mulFwdDiffList_cons (h : ℕ) (hs : List ℕ) (f : ℕ → G) :
    mulFwdDiffList (h :: hs) f = mulFwdDiff h (mulFwdDiffList hs f) := rfl

theorem mulFwdDiffList_append (l₁ l₂ : List ℕ) (f : ℕ → G) :
    mulFwdDiffList (l₁ ++ l₂) f = mulFwdDiffList l₁ (mulFwdDiffList l₂ f) := by
  induction l₁ with
  | nil => rfl
  | cons h t ih => rw [List.cons_append, mulFwdDiffList_cons, ih, mulFwdDiffList_cons]

/-- The engine of the closed formula: differencing a sequence of the shape
"fixed word conjugated by `a^{n+c}`, times a fixed tail" replaces the word by its
commutator with `a^h` and **kills the tail**. -/
theorem mulFwdDiff_conj_mul (a W z : G) (c h n : ℕ) :
    mulFwdDiff h (fun m => a ^ (m + c) * W * (a ^ (m + c))⁻¹ * z) n
      = a ^ (n + c) * ⁅a ^ h, W⁆ * (a ^ (n + c))⁻¹ := by
  simp only [mulFwdDiff, commutatorElement_def]
  rw [show n + h + c = n + c + h by omega, pow_add a (n + c) h]
  group

end Diff

/-! ## The closed form for `n ↦ aⁿ bⁿ` -/

section PowMulPow

/-- The iterated commutator `⁅a^{h_k}, ⁅…, ⁅a^{h_2}, b^{h_1}⁆…⁆⁆`, indexed by the
list `hs = [h_k, …, h_2]` of the *outer* steps together with the innermost step
`h₁`.  For `hs = []` it degenerates to `b^{h_1}`. -/
def powCommWord (a b : G) : List ℕ → ℕ → G
  | [], h₁ => b ^ h₁
  | h :: hs, h₁ => ⁅a ^ h, powCommWord a b hs h₁⁆

@[simp] theorem powCommWord_nil (a b : G) (h₁ : ℕ) : powCommWord a b [] h₁ = b ^ h₁ := rfl

@[simp] theorem powCommWord_cons (a b : G) (h : ℕ) (hs : List ℕ) (h₁ : ℕ) :
    powCommWord a b (h :: hs) h₁ = ⁅a ^ h, powCommWord a b hs h₁⁆ := rfl

/-- The word of `hs` outer steps is an `|hs|`-fold commutator, hence lies in
`lowerCentralSeries |hs|`. -/
theorem powCommWord_mem (a b : G) (hs : List ℕ) (h₁ : ℕ) :
    powCommWord a b hs h₁ ∈ (⊤ : Subgroup G).lowerCentralSeries hs.length := by
  induction hs with
  | nil => exact Subgroup.mem_top _
  | cons h t ih =>
      have htop : a ^ h ∈ (⊤ : Subgroup G).lowerCentralSeries 0 := Subgroup.mem_top _
      have hmem := OddOrder.Isaacs.Ch04.commutator_lowerCentralSeries_le (G := G) 0 t.length
        (Subgroup.commutator_mem_commutator htop ih)
      simpa using hmem

/-- One difference of `n ↦ aⁿ bⁿ`. -/
theorem mulFwdDiff_pow_mul_pow (a b : G) (h₁ n : ℕ) :
    mulFwdDiff h₁ (fun m => a ^ m * b ^ m) n
      = a ^ (n + h₁) * b ^ h₁ * (a ^ (n + h₁))⁻¹ * a ^ h₁ := by
  simp only [mulFwdDiff]
  rw [pow_add a n h₁, pow_add b n h₁]
  group

/-- **The closed form.**  For `k ≥ 2` the `k`-fold iterated difference of
`m ↦ aᵐ bᵐ` is a *conjugate of a fixed iterated commutator*:

`∂_{h_k} ⋯ ∂_{h_1} (aᵐbᵐ) (n) = a^{n+h₁} · ⁅a^{h_k}, ⁅…, ⁅a^{h_2}, b^{h_1}⁆…⁆⁆ · (a^{n+h₁})⁻¹`.

Everything depending on `n` sits in the conjugator, and the word itself is an
`|h :: hs|`-fold commutator.  Together with `powCommWord_mem` this is the whole
"`n ↦ aⁿbⁿ` is a polynomial sequence" statement. -/
theorem mulFwdDiffList_cons_pow_mul_pow (a b : G) (h : ℕ) (hs : List ℕ) (h₁ n : ℕ) :
    mulFwdDiffList (h :: hs) (mulFwdDiff h₁ fun m => a ^ m * b ^ m) n
      = a ^ (n + h₁) * powCommWord a b (h :: hs) h₁ * (a ^ (n + h₁))⁻¹ := by
  induction hs generalizing h n with
  | nil =>
      rw [mulFwdDiffList_cons, mulFwdDiffList_nil,
        show (mulFwdDiff h₁ fun m => a ^ m * b ^ m)
            = fun m => a ^ (m + h₁) * b ^ h₁ * (a ^ (m + h₁))⁻¹ * a ^ h₁ from
          funext fun m => mulFwdDiff_pow_mul_pow a b h₁ m,
        mulFwdDiff_conj_mul a (b ^ h₁) (a ^ h₁) h₁ h n]
      rfl
  | cons h' t ih =>
      rw [mulFwdDiffList_cons,
        show mulFwdDiffList (h' :: t) (mulFwdDiff h₁ fun m => a ^ m * b ^ m)
            = fun m => a ^ (m + h₁) * powCommWord a b (h' :: t) h₁ * (a ^ (m + h₁))⁻¹ * 1 from
          funext fun m => by rw [mul_one]; exact ih h' m,
        mulFwdDiff_conj_mul a (powCommWord a b (h' :: t) h₁) 1 h₁ h n]
      rfl

/-- **`n ↦ aⁿ bⁿ` is a polynomial sequence for the lower central series.**  The
`k`-fold iterated difference lies in the book's `γ_k`, i.e. mathlib's
`lowerCentralSeries (k - 1)`. -/
theorem mulFwdDiffList_pow_mul_pow_mem (a b : G) (hs : List ℕ) (n : ℕ) :
    mulFwdDiffList hs (fun m => a ^ m * b ^ m) n
      ∈ (⊤ : Subgroup G).lowerCentralSeries (hs.length - 1) := by
  induction hs using List.reverseRecOn with
  | nil => exact Subgroup.mem_top _
  | append_singleton t h₁ _ =>
      rw [mulFwdDiffList_append]
      rcases t with _ | ⟨h, hs'⟩
      · exact Subgroup.mem_top _
      · have hred : mulFwdDiffList [h₁] (fun m : ℕ => a ^ m * b ^ m)
            = mulFwdDiff h₁ (fun m : ℕ => a ^ m * b ^ m) := rfl
        rw [hred, mulFwdDiffList_cons_pow_mul_pow]
        have hlen : ((h :: hs') ++ [h₁]).length - 1 = (h :: hs').length := by simp
        rw [hlen]
        haveI hN : ((⊤ : Subgroup G).lowerCentralSeries (h :: hs').length).Normal :=
          inferInstance
        simpa [mul_assoc] using
          hN.conj_mem _ (powCommWord_mem a b (h :: hs') h₁) (a ^ (n + h₁))

end PowMulPow

end OddOrder.GroupTheory
