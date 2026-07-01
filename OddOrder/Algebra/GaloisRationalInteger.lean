/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import OddOrder.GroupTheory.RepresentationTheory.CyclotomicGaloisAction

/-!
# Algebraic integers fixed by all Galois automorphisms are rational integers

The arithmetic heart of **Isaacs, Lemma 3.14** (and Peterfalvi (13.9.b)): a nonzero algebraic
integer whose Galois conjugates are all accounted for has a field norm that is a nonzero rational
integer, hence of absolute value `≥ 1`.

This file isolates the reusable number-theoretic core:

* `exists_int_of_isIntegral_of_forall_complexRingEquiv_fixed` — an algebraic integer `α : ℂ`
  fixed by **every** ring automorphism `σ : ℂ ≃+* ℂ` is a rational integer.
* `exists_pow_of_complexRingEquiv` — every `σ : ℂ ≃+* ℂ` acts as a uniform power `(· ^ k)`
  (`k` coprime to `n`) on the `n`-th roots of unity (the converse of
  `exists_complexRingEquiv_pow_of_rootsOfUnity`).

The proof works inside the (finite, Galois) splitting field `K = ℚ(rootSet (minpoly ℚ α))`: `α` is
fixed by all `σ : K ≃ₐ[ℚ] K` (each extends to `ℂ` by `exists_complexRingEquiv_extends`, where the
hypothesis applies), so `α ∈ (⊥ : IntermediateField ℚ K)` by the Galois correspondence, i.e. `α ∈ ℚ`;
a rational algebraic integer lies in `ℤ` because `ℤ` is integrally closed in `ℚ`.

The consumer chain (Peterfalvi (13.9.b)) additionally uses the repository's
`OddOrder.RepresentationTheory.map_character_eq_character_pow` ((1.9): `σ (χ g) = χ (g ^ k)`) to see
that the product `∏_k χ(a^k)` over a cyclic class is fixed by every `σ : ℂ ≃+* ℂ` — any automorphism
of `ℂ` acts as a uniform power `(· ^ k)` on `m`-th roots of unity — and hence, being an algebraic
integer, is a rational integer.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Lemma 3.14.
* T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), (13.9.b).
-/

namespace OddOrder.Algebra

open Polynomial IntermediateField

/-- A rational algebraic integer is a rational integer: if `α : ℂ` is integral over `ℤ` and lies in
the image of `ℚ`, then `α` is the image of an integer. -/
theorem exists_int_of_isIntegral_of_mem_range_rat {α : ℂ} (hα : IsIntegral ℤ α)
    (hrat : ∃ q : ℚ, (q : ℂ) = α) : ∃ z : ℤ, (z : ℂ) = α := by
  obtain ⟨q, rfl⟩ := hrat
  -- `q` is integral over `ℤ` (the map `ℚ → ℂ` is injective, so integrality descends).
  have hqℚ : IsIntegral ℤ q := by
    have hinj : Function.Injective (algebraMap ℚ ℂ) := (algebraMap ℚ ℂ).injective
    exact (isIntegral_algebraMap_iff hinj).mp hα
  -- `ℤ` is integrally closed in `ℚ`, so `q ∈ ℤ`.
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff).mp hqℚ
  refine ⟨z, ?_⟩
  rw [← hz]
  simp

/-- **Isaacs 3.14 core.** An algebraic integer `α : ℂ` fixed by every ring automorphism of `ℂ`
is a rational integer. -/
theorem exists_int_of_isIntegral_of_forall_complexRingEquiv_fixed {α : ℂ}
    (hα : IsIntegral ℤ α) (hfix : ∀ σ : ℂ ≃+* ℂ, σ α = α) :
    ∃ z : ℤ, (z : ℂ) = α := by
  apply exists_int_of_isIntegral_of_mem_range_rat hα
  -- Work inside the splitting field `K = ℚ(rootSet (minpoly ℚ α)) ⊆ ℂ`.
  have hαℚ : IsIntegral ℚ α := hα.tower_top (A := ℚ)
  set p := minpoly ℚ α with hp
  have hp0 : p ≠ 0 := minpoly.ne_zero hαℚ
  have hsplits : (p.map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits _
  set K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (p.rootSet ℂ) with hK
  haveI hSF : IsSplittingField ℚ K p := IntermediateField.adjoin_rootSet_isSplittingField hsplits
  haveI : Normal ℚ K := Normal.of_isSplittingField p
  haveI : FiniteDimensional ℚ K := IsSplittingField.finiteDimensional K p
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  haveI : Algebra.IsSeparable ℚ K := inferInstance
  haveI : IsGalois ℚ K := ⟨⟩
  -- `α` lies in `K` (it is a root of its own minimal polynomial).
  have hαmem : α ∈ K := by
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    exact ⟨hp0, minpoly.aeval ℚ α⟩
  -- The element `⟨α, hαmem⟩ : K` is fixed by every `ℚ`-automorphism of `K`.
  have hfixedK : ∀ σ : K ≃ₐ[ℚ] K, σ ⟨α, hαmem⟩ = ⟨α, hαmem⟩ := by
    intro σ
    obtain ⟨τ, hτ⟩ := OddOrder.RepresentationTheory.exists_complexRingEquiv_extends K σ.toRingEquiv
    have hval : (σ ⟨α, hαmem⟩ : ℂ) = α := by
      have h1 : τ (α : ℂ) = ((σ ⟨α, hαmem⟩ : K) : ℂ) := hτ ⟨α, hαmem⟩
      have h2 : τ (α : ℂ) = α := hfix τ
      rw [h2] at h1
      exact h1.symm
    exact Subtype.ext hval
  -- By the Galois correspondence, `⟨α, hαmem⟩ ∈ ⊥`, i.e. `α` is rational.
  have hbot : (⟨α, hαmem⟩ : K) ∈ (⊥ : IntermediateField ℚ K) :=
    (IsGalois.mem_bot_iff_fixed _).mpr hfixedK
  rw [IntermediateField.mem_bot] at hbot
  obtain ⟨q, hq⟩ := hbot
  refine ⟨q, ?_⟩
  have : (algebraMap ℚ K q : ℂ) = ((⟨α, hαmem⟩ : K) : ℂ) := by rw [hq]
  simpa using this

/-- **Every ring automorphism of `ℂ` acts as a uniform power on `n`-th roots of unity.**
For `σ : ℂ ≃+* ℂ` and `n ≠ 0` there is a `k` coprime to `n` with `σ ζ = ζ ^ k` for every `n`-th root
of unity `ζ`.  This is the converse of `exists_complexRingEquiv_pow_of_rootsOfUnity` (which, given a
coprime `k`, produces such a `σ`): here we start from an arbitrary `σ` and *read off* its exponent.
The exponent is well defined because `σ` sends a fixed primitive root `μ` to another primitive root
`μ ^ k`, and every `n`-th root is a power of `μ`. -/
theorem exists_pow_of_complexRingEquiv (σ : ℂ ≃+* ℂ) {n : ℕ} (hn : n ≠ 0) :
    ∃ k : ℕ, k.Coprime n ∧ ∀ ζ : ℂ, ζ ^ n = 1 → σ ζ = ζ ^ k := by
  haveI : NeZero n := ⟨hn⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨μ, hμ⟩ : ∃ μ : ℂ, IsPrimitiveRoot μ n := ⟨_, Complex.isPrimitiveRoot_exp n hn⟩
  have hσμ : IsPrimitiveRoot (σ μ) n := hμ.map_of_injective σ.injective
  have hpow1 : (σ μ) ^ n = 1 := by rw [← map_pow, hμ.pow_eq_one, map_one]
  obtain ⟨k, -, hk_eq⟩ := hμ.eq_pow_of_pow_eq_one hpow1
  refine ⟨k, ?_, ?_⟩
  · have : IsPrimitiveRoot (μ ^ k) n := hk_eq ▸ hσμ
    exact (hμ.pow_iff_coprime hnpos k).mp this
  · intro ζ hζ
    obtain ⟨j, -, hj_eq⟩ := hμ.eq_pow_of_pow_eq_one hζ
    rw [← hj_eq, map_pow, ← hk_eq, ← pow_mul, ← pow_mul, Nat.mul_comm]

end OddOrder.Algebra
