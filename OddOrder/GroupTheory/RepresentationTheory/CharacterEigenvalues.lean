/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.EigenspaceDecomposition
import OddOrder.GroupTheory.RepresentationTheory.VirtualCharacter

/-!
# Character values as sums of roots of unity

For a finite-dimensional representation `ρ` over a field `K` containing a primitive `m`-th root of
unity, and `g` with `g ^ m = 1`, the operator `ρ g` is diagonalisable with `m`-th roots of unity as
eigenvalues (`OddOrder.isInternal_eigenspace_of_pow`), so

`χ_ρ(g ^ k) = ∑_{ζ^m = 1} dim (eigenspace (ρ g) ζ) · ζ ^ k`

with the **same** multiplicities for every `k`.  Reading this at `k = 1` and at `k = p^s`
simultaneously is what gives the classical congruence `χ(g)^{p^s} ≡ χ(g^{p^s}) (mod p)`, which is
the analytic core of Gorenstein Lemma 7.5 (issue 9508, 段 D): the Frobenius endomorphism of a
ring of characteristic `p` turns the `k = 1` expression into the `k = p^s` one.

Working with the multiplicities of `ρ g` for *all* `k` at once avoids having to compare
eigenspaces of `ρ g` with eigenspaces of `ρ (g^k)`, which can merge.

## Main results

* `OddOrder.trace_pow_eq_sum_finrank_smul` — the trace of `A ^ k` from the eigenvalues of `A`
* `OddOrder.RepresentationTheory.character_pow_eq_sum_finrank_smul` — the character version
* `OddOrder.RepresentationTheory.character_mem_adjoin` — character values lie in `ℤ[ω]`

## References

* D. Gorenstein, *Finite Groups*, §4.7, Lemma 7.5 (`references/gorenstein/pages/`).
-/

namespace OddOrder

open Polynomial Module Module.End

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Eigenvectors of `A` are eigenvectors of `A ^ k`, with the eigenvalue raised to the `k`-th
power. -/
theorem pow_apply_of_mem_eigenspace {A : Module.End F V} {ζ : F} {v : V}
    (hv : v ∈ A.eigenspace ζ) (k : ℕ) : (A ^ k) v = ζ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, mem_eigenspace_iff.mp hv, map_smul, ih, smul_smul,
        ← pow_succ']

set_option backward.isDefEq.respectTransparency false in
/-- **The trace of a power, from the eigenvalues of the operator.**  Both sides use the
multiplicities of `A` itself, so the identity holds for every exponent at once. -/
theorem trace_pow_eq_sum_finrank_smul [FiniteDimensional F V] {A : Module.End F V} {m : ℕ}
    (hm : 0 < m) {ω : F} (hω : IsPrimitiveRoot ω m) (hA : A ^ m = 1) (k : ℕ) :
    LinearMap.trace F V (A ^ k)
      = ∑ ζ ∈ nthRootsFinset m (1 : F), Module.finrank F (A.eigenspace ζ) • ζ ^ k := by
  classical
  have hmaps : ∀ ζ : nthRootsFinset m (1 : F),
      Set.MapsTo (A ^ k) (A.eigenspace (ζ : F)) (A.eigenspace (ζ : F)) := by
    intro ζ v hv
    rw [SetLike.mem_coe, mem_eigenspace_iff] at hv ⊢
    rw [pow_apply_of_mem_eigenspace (mem_eigenspace_iff.mpr hv) k, map_smul, hv, smul_comm]
  have hrestrict : ∀ ζ : nthRootsFinset m (1 : F),
      LinearMap.trace F _ ((A ^ k).restrict (hmaps ζ))
        = Module.finrank F (A.eigenspace (ζ : F)) • (ζ : F) ^ k := by
    intro ζ
    have hid : (A ^ k).restrict (hmaps ζ) = ((ζ : F) ^ k) • LinearMap.id := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      simpa [LinearMap.restrict_apply] using pow_apply_of_mem_eigenspace v.2 k
    rw [hid, map_smul, LinearMap.trace_id, smul_eq_mul, nsmul_eq_mul]
    exact mul_comm _ _
  rw [LinearMap.trace_eq_sum_trace_restrict (isInternal_eigenspace_of_pow hm hω hA) hmaps]
  simp only [hrestrict, Finset.univ_eq_attach]
  exact Finset.sum_attach (nthRootsFinset m (1 : F))
    (fun ζ => Module.finrank F (A.eigenspace ζ) • ζ ^ k)

namespace RepresentationTheory

variable {K G : Type*} [Field K] [Group G] {W : Type*} [AddCommGroup W] [Module K W]

/-- **The character of a power, from the eigenvalues at `g`.**  The multiplicities are those of
`ρ g` and do not depend on `k`. -/
theorem character_pow_eq_sum_finrank_smul [FiniteDimensional K W] (ρ : Representation K G W)
    {m : ℕ} (hm : 0 < m) {ω : K} (hω : IsPrimitiveRoot ω m) {g : G} (hg : g ^ m = 1) (k : ℕ) :
    ρ.character (g ^ k)
      = ∑ ζ ∈ nthRootsFinset m (1 : K),
        Module.finrank K (Module.End.eigenspace (ρ g) ζ) • ζ ^ k := by
  have hA : (ρ g) ^ m = 1 := by rw [← map_pow, hg, map_one]
  rw [Representation.character, map_pow]
  exact trace_pow_eq_sum_finrank_smul hm hω hA k

/-- Every `m`-th root of unity is a power of a primitive one. -/
theorem mem_adjoin_of_mem_nthRootsFinset {m : ℕ} (hm : 0 < m) {ω : K} (hω : IsPrimitiveRoot ω m)
    {ζ : K} (hζ : ζ ∈ nthRootsFinset m (1 : K)) : ζ ∈ Algebra.adjoin ℤ ({ω} : Set K) := by
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨j, -, rfl⟩ := hω.eq_pow_of_pow_eq_one ((mem_nthRootsFinset hm _).mp hζ)
  exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ ω) j

/-- **Character values are cyclotomic integers**: they lie in `ℤ[ω]` as soon as `ω` is a primitive
`m`-th root of unity and `g ^ m = 1`. -/
theorem character_mem_adjoin [FiniteDimensional K W] (ρ : Representation K G W)
    {m : ℕ} (hm : 0 < m) {ω : K} (hω : IsPrimitiveRoot ω m) {g : G} (hg : g ^ m = 1) :
    ρ.character g ∈ Algebra.adjoin ℤ ({ω} : Set K) := by
  have hk := character_pow_eq_sum_finrank_smul ρ hm hω hg 1
  rw [pow_one] at hk
  rw [hk]
  refine Subalgebra.sum_mem _ fun ζ hζ => ?_
  rw [pow_one, nsmul_eq_mul]
  exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
    (mem_adjoin_of_mem_nthRootsFinset hm hω hζ)

end RepresentationTheory

end OddOrder
