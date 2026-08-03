/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.EigenspaceDecomposition
import OddOrder.GroupTheory.RepresentationTheory.Modular.SplittingSystem

/-!
# Eigen-decomposition over the coefficient ring of a `p`-modular system

Brauer characters compare a module over the residue field `k` with a lattice over `𝒪`.  The
comparison needs the eigen-decomposition of a finite-order operator *upstairs*, over `𝒪`, not
only downstairs over `k`.

`𝒪` is not a field, so mathlib's diagonalisation results do not apply; but the node set that
matters — the `n`-th roots of unity of `𝒪`, for `p ∤ n` — is *separated*: two of them that are
congruent modulo the maximal ideal are equal (`eq_of_pow_eq_one_of_sub_mem`), so their
difference is a unit.  That is exactly the hypothesis of
`OddOrder.iSup_eigenspace_eq_top_of_separated`.

## Main results

* `OddOrder.RepresentationTheory.Modular.separatedNodes_of_pow_eq_one` — roots of unity of
  order prime to `p` are separated nodes
* `OddOrder.RepresentationTheory.Modular.iSup_eigenspace_eq_top_of_pow` — the decomposition
* `OddOrder.RepresentationTheory.Modular.trace_eq_sum_finrank_smul_of_pow` — the trace of a
  finite-order lattice endomorphism, in Brauer-character shape
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Polynomial

/-- `X ^ n - 1` factors into the `n`-th roots of unity, so an operator of order dividing `n` is
annihilated by that product. -/
theorem prod_X_sub_C_nthRootsFinset_aeval_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (hn0 : 0 < n) {ω : R} (hω : IsPrimitiveRoot ω n)
    {M : Type*} [AddCommGroup M] [Module R M] {A : Module.End R M} (hA : A ^ n = 1) :
    aeval A (∏ η ∈ nthRootsFinset n (1 : R), (X - C η)) = 0 := by
  rw [← X_pow_sub_one_eq_prod hn0 hω]
  simp [hA]

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]

/-- **Roots of unity of order prime to `p` are separated nodes.**  Two `n`-th roots of unity of
`𝒪` with the same residue are equal, so distinct ones differ by a unit of the local ring `𝒪`. -/
theorem separatedNodes_of_pow_eq_one {n : ℕ} (hn : ¬ p ∣ n) {s : Finset 𝒪}
    (hs : ∀ a ∈ s, a ^ n = 1) : OddOrder.SeparatedNodes s := by
  intro ζ hζ η hη hne
  rw [isUnit_iff_residue_ne_zero]
  intro h0
  exact hne (eq_of_pow_eq_one_of_sub_mem (isUnit_natCast_of_not_dvd (p := p) hn)
    (hs ζ hζ) (hs η hη) ((residue_eq_zero_iff _).mp h0))

/-- **Eigen-decomposition over `𝒪`.**  An operator with `A ^ n = 1` and `p ∤ n` on any
`𝒪`-module is spanned by its eigen-submodules at the `n`-th roots of unity of `𝒪`.

Note that no finiteness or freeness of the module is needed; what replaces the usual
"the base is a field" is the separatedness of the roots of unity. -/
theorem iSup_eigenspace_eq_top_of_pow [IsDomain 𝒪] {n : ℕ} (hn : ¬ p ∣ n) (hn0 : 0 < n)
    {ω : 𝒪} (hω : IsPrimitiveRoot ω n) {M : Type*} [AddCommGroup M] [Module 𝒪 M]
    {A : Module.End 𝒪 M} (hA : A ^ n = 1) :
    ⨆ ζ ∈ nthRootsFinset n (1 : 𝒪), A.eigenspace ζ = ⊤ := by
  exact OddOrder.iSup_eigenspace_eq_top_of_separated
    (separatedNodes_of_pow_eq_one (p := p) hn fun _ ha => (mem_nthRootsFinset hn0 _).mp ha)
    (prod_X_sub_C_nthRootsFinset_aeval_eq_zero hn0 hω hA)

/-! ### Ranks and the trace of a lattice endomorphism -/

section Lattice

variable [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] {n : ℕ} (hn : ¬ p ∣ n) (hn0 : 0 < n)
  {ω : 𝒪} (hω : IsPrimitiveRoot ω n)
  {L : Type*} [AddCommGroup L] [Module 𝒪 L] [Module.Free 𝒪 L] [Module.Finite 𝒪 L]
  {A : Module.End 𝒪 L} (hA : A ^ n = 1)
include hn hn0 hω hA

/-- The ranks of the eigen-submodules of a finite-order lattice endomorphism add up to the rank
of the lattice. -/
theorem sum_finrank_eigenspace_of_pow :
    ∑ ζ ∈ nthRootsFinset n (1 : 𝒪), Module.finrank 𝒪 (A.eigenspace ζ) = Module.finrank 𝒪 L :=
  OddOrder.sum_finrank_eigenspace_of_separated
    (separatedNodes_of_pow_eq_one (p := p) hn fun _ ha => (mem_nthRootsFinset hn0 _).mp ha)
    (prod_X_sub_C_nthRootsFinset_aeval_eq_zero hn0 hω hA)

/-- **The trace of a finite-order lattice endomorphism is already the Brauer-character
expression**, computed upstairs in `𝒪`: the `n`-th roots of unity weighted by the ranks of the
eigen-submodules.

Comparing this with `brauerCharacter` — which is the same expression with the ranks replaced by
the dimensions of the eigenspaces of the reduction — is what makes the decomposition matrix an
identity between ordinary characters and Brauer characters. -/
theorem trace_eq_sum_finrank_smul_of_pow :
    LinearMap.trace 𝒪 L A
      = ∑ ζ ∈ nthRootsFinset n (1 : 𝒪), Module.finrank 𝒪 (A.eigenspace ζ) • ζ :=
  OddOrder.trace_eq_sum_finrank_smul
    (separatedNodes_of_pow_eq_one (p := p) hn fun _ ha => (mem_nthRootsFinset hn0 _).mp ha)
    (prod_X_sub_C_nthRootsFinset_aeval_eq_zero hn0 hω hA)

end Lattice


/-! ### The standard splitting system

For `SplittingSystem p n = 𝕎 (GF(p ^ φ(n)))` everything above is available unconditionally:
it is a domain, and it contains a primitive `n`-th root of unity by
`exists_isPrimitiveRoot_splittingSystem`. -/

section Splitting

variable (p n : ℕ) [Fact p.Prime]

instance : IsDomain (SplittingSystem p n) := inferInstance

/-- The eigen-decomposition over the standard splitting system, with no hypotheses beyond
`p ∤ n`. -/
theorem iSup_eigenspace_eq_top_splittingSystem (hp : ¬ p ∣ n) (hn : n ≠ 0)
    {M : Type*} [AddCommGroup M] [Module (SplittingSystem p n) M]
    {A : Module.End (SplittingSystem p n) M} (hA : A ^ n = 1) :
    ⨆ ζ ∈ nthRootsFinset n (1 : SplittingSystem p n), A.eigenspace ζ = ⊤ := by
  obtain ⟨ω, hω⟩ := exists_isPrimitiveRoot_splittingSystem p n hp hn
  exact iSup_eigenspace_eq_top_of_pow (p := p) hp (Nat.pos_of_ne_zero hn) hω hA

end Splitting

end OddOrder.RepresentationTheory.Modular
