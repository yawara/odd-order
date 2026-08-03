/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerDecomposition
import OddOrder.GroupTheory.RepresentationTheory.Modular.Reduction

/-!
# The decomposition matrix

`trace_eq_brauerCharacter_reduction` says the ordinary character of an `𝒪`-lattice
representation — its trace over `𝒪` — is the Brauer character of the reduction modulo the
maximal ideal.  `exists_decomposition` breaks that Brauer character into irreducible ones.  Put
together:

`χ(g) = ∑_φ d_{χφ} φ(g)` for `g` `p`-regular,

with `d_{χφ} ∈ ℕ` — the **decomposition numbers** of `χ`.  Ranging over the ordinary characters
this is the decomposition matrix `D`.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_decomposition_trace`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra TensorProduct OddOrder.GroupTheory

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable {L : Type*} [AddCommGroup L] [Module 𝒪 L] [Module.Free 𝒪 L] [Module.Finite 𝒪 L]

/-- **The decomposition of an ordinary character into irreducible Brauer characters.**

The two primitive roots of unity are the ones the two halves need: `hω` upstairs to write the
trace in Brauer-character shape (`trace_eq_brauerCharacter_reduction`), `hω'` downstairs to split
the reduction into composition factors (`exists_decomposition`).  Both are supplied by the
standard system `𝕎(𝔽̄_p)`. -/
theorem exists_decomposition_trace (hp : p.Prime)
    {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
    {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
    {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
    (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
    (ρ : Representation 𝒪 G L) :
    ∃ d : ι → ℕ, ∀ g : G, IsPRegular p g →
      LinearMap.trace 𝒪 L (ρ g)
        = ∑ i, (d i : 𝒪) * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π i g := by
  haveI : Module.Finite (ResidueField 𝒪) (ResidueField 𝒪 ⊗[𝒪] L) :=
    Module.Finite.of_basis
      (Module.Basis.baseChange (S := ResidueField 𝒪) (Module.Free.chooseBasis 𝒪 L))
  obtain ⟨d, hd⟩ := exists_decomposition (nn := nn) hp hω' hπ hlin hkerJ (reduction ρ)
  refine ⟨d, fun g hg => ?_⟩
  rw [trace_eq_brauerCharacter_reduction (not_dvd_pRegularExponent hp) pRegularExponent_pos hω ρ
    (rep_pow_pRegularExponent_eq_one' ρ hp hg)]
  exact hd g hg

end OddOrder.RepresentationTheory.Modular
