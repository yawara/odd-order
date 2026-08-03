/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.CommutatorSpan

/-!
# The commutator span and its `p`-radical along algebra maps

Brauer's count reads `dim_k (A ⧸ T')` off the semisimple quotient `A ⧸ J(A)`, so one needs to
know how `T = [A, A]` and its `p`-radical `T' = {x : ∃ m, x ^ (p ^ m) ∈ T}` behave along an
algebra map.  For `T` this is formal: it is the image of `T` under any surjection.  For `T'` it
is *not* formal — the preimage of `T'(B)` can be bigger than `T'(A)` — but it is true as soon as
the kernel is nil with a uniform exponent, which is the case for the Jacobson radical of a
finite-dimensional algebra:

`x ^ (p ^ m) = t + y` with `t ∈ T(A)` and `y ^ N = 0` gives, after raising to `p ^ r ≥ N` and
using the iterated freshman's dream, `x ^ (p ^ (m + r)) ≡ t ^ (p ^ r) ∈ T(A)`.

## Main results

* `OddOrder.map_commutatorSpan` — `T` is the image of `T` under a surjection
* `OddOrder.map_mem_commutatorRadical` — `T'` maps into `T'`
* `OddOrder.mem_commutatorRadical_of_map_mem` — and conversely, for a nil kernel
-/

namespace OddOrder

variable {k A B : Type*} [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

/-- An algebra map sends commutators to commutators. -/
theorem map_commutatorSpan_le (f : A →ₐ[k] B) :
    (commutatorSpan k A).map f.toLinearMap ≤ commutatorSpan k B := by
  rw [Submodule.map_le_iff_le_comap, commutatorSpan, Submodule.span_le]
  rintro _ ⟨a, b, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, AlgHom.toLinearMap_apply, map_sub, map_mul]
  exact commutator_mem_commutatorSpan _ _

/-- Every commutator of the target is the image of a commutator. -/
theorem commutatorSpan_le_map (f : A →ₐ[k] B) (hf : Function.Surjective f) :
    commutatorSpan k B ≤ (commutatorSpan k A).map f.toLinearMap := by
  rw [commutatorSpan, Submodule.span_le]
  rintro _ ⟨a, b, rfl⟩
  obtain ⟨a', rfl⟩ := hf a
  obtain ⟨b', rfl⟩ := hf b
  exact ⟨a' * b' - b' * a', commutator_mem_commutatorSpan _ _, by simp⟩

/-- **The commutator span of a quotient is the image of the commutator span.** -/
theorem map_commutatorSpan (f : A →ₐ[k] B) (hf : Function.Surjective f) :
    (commutatorSpan k A).map f.toLinearMap = commutatorSpan k B :=
  le_antisymm (map_commutatorSpan_le f) (commutatorSpan_le_map f hf)

variable {p : ℕ}

/-- The `p`-radical maps into the `p`-radical. -/
theorem map_mem_commutatorRadical (f : A →ₐ[k] B) (hp : p.Prime) (hA : (p : A) = 0)
    (hB : (p : B) = 0) {x : A} (hx : x ∈ commutatorRadical (k := k) hp hA) :
    f x ∈ commutatorRadical (k := k) hp hB := by
  obtain ⟨m, hm⟩ := hx
  refine ⟨m, ?_⟩
  rw [← map_pow]
  exact map_commutatorSpan_le f ⟨_, hm, rfl⟩

/-- **A surjection with uniformly nilpotent kernel does not enlarge the `p`-radical.**  Together
with `map_mem_commutatorRadical` this says `T'(A)` is the preimage of `T'(B)`; applied to
`A ↠ A ⧸ J(A)` it turns the computation of `T'` into a computation in the semisimple quotient. -/
theorem mem_commutatorRadical_of_map_mem (f : A →ₐ[k] B) (hf : Function.Surjective f)
    (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
    {N : ℕ} (hker : ∀ y : A, f y = 0 → y ^ N = 0)
    {x : A} (hx : f x ∈ commutatorRadical (k := k) hp hB) :
    x ∈ commutatorRadical (k := k) hp hA := by
  obtain ⟨m, hm⟩ := hx
  rw [← map_pow] at hm
  obtain ⟨t, ht, hft⟩ := commutatorSpan_le_map f hf hm
  rw [AlgHom.toLinearMap_apply] at hft
  -- the error term lies in the kernel, hence dies after `p ^ r ≥ N` further powers
  set y := x ^ p ^ m - t with hy
  have hy0 : f y = 0 := by rw [hy, map_sub, hft, sub_self]
  obtain ⟨r, hr⟩ : ∃ r, N ≤ p ^ r := ⟨N, (Nat.lt_pow_self hp.one_lt).le⟩
  have hyp : y ^ p ^ r = 0 := by
    obtain ⟨c, hc⟩ : ∃ c, p ^ r = N + c := ⟨p ^ r - N, by omega⟩
    rw [hc, pow_add, hker y hy0, zero_mul]
  refine ⟨m + r, ?_⟩
  have hty : t + y = x ^ p ^ m := by rw [hy]; abel
  have hsplit : x ^ p ^ (m + r)
      = ((t + y) ^ p ^ r - t ^ p ^ r - y ^ p ^ r) + t ^ p ^ r + y ^ p ^ r := by
    rw [pow_add, pow_mul, hty]
    abel
  rw [hsplit]
  refine Submodule.add_mem _ (Submodule.add_mem _
    (add_pow_prime_pow_sub_sub_mem (k := k) hp hA r t y)
    (pow_pow_mem_commutatorSpan (k := k) hp hA r ht)) ?_
  rw [hyp]
  exact Submodule.zero_mem _

end OddOrder
