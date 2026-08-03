/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Nakayama
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerCharacterIndependence

/-!
# The irreducible Brauer characters are linearly independent

`mem_maximalIdeal_of_sum_irreducibleBrauerCharacter` says every relation among the `φ_i` on the
`p`-regular classes has all coefficients in `𝔪`.  Over a discrete valuation ring that upgrades to
`c = 0`: the relations form a submodule `S` of `ι → 𝒪`, and dividing a relation by a uniformiser
again gives a relation, so `S ≤ 𝔪 • S`.  Nakayama then forces `S = ⊥`.

No representation theory enters here — the input is exactly the one-step statement above.

The statement is independence over `𝒪`; independence over the fraction field follows by clearing
denominators, which is not recorded here.

## Main results

* `OddOrder.RepresentationTheory.Modular.eq_zero_of_sum_irreducibleBrauerCharacter`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]

/-- **The irreducible Brauer characters are linearly independent on the `p`-regular classes.**

Over a discrete valuation ring the one-step divisibility of
`mem_maximalIdeal_of_sum_irreducibleBrauerCharacter` becomes `S ≤ 𝔪 • S` for the module `S` of
relations, and Nakayama kills it. -/
theorem eq_zero_of_sum_irreducibleBrauerCharacter (hp : p.Prime)
    {ω : ResidueField 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
    {B : Type*} [Ring B] [Algebra (ResidueField 𝒪) B]
    {π : MonoidAlgebra (ResidueField 𝒪) G →ₐ[ResidueField 𝒪] B} (hπ : Function.Surjective π)
    {N : ℕ} (hker : ∀ y : MonoidAlgebra (ResidueField 𝒪) G, π y = 0 → y ^ N = 0)
    (e : B ≃ₐ[ResidueField 𝒪] ∀ i, Matrix (nn i) (nn i) (ResidueField 𝒪)) (c : ι → 𝒪)
    (h : ∀ g : G, IsPRegular p g →
      ∑ i, c i * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪)
        (e.toAlgHom.comp π).toRingHom i g = 0) :
    c = 0 := by
  classical
  -- the relations form a submodule of `ι → 𝒪`
  set Φ : (ι → 𝒪) →ₗ[𝒪] ({g : G // IsPRegular p g} → 𝒪) :=
    { toFun := fun d g => ∑ i, d i * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪)
        (e.toAlgHom.comp π).toRingHom i g.1
      map_add' := fun u v => by funext g; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun a u => by funext g; simp [Finset.mul_sum, mul_assoc] } with hΦ
  set S := LinearMap.ker Φ with hS
  have hmemS : ∀ d : ι → 𝒪, d ∈ S ↔ ∀ g : G, IsPRegular p g →
      ∑ i, d i * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪)
        (e.toAlgHom.comp π).toRingHom i g = 0 := by
    intro d
    constructor
    · intro hd g hg
      exact congrFun hd ⟨g, hg⟩
    · intro hd
      funext g
      exact hd g.1 g.2
  -- a relation divided by a uniformiser is again a relation
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  have hmax : maximalIdeal 𝒪 = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hstep : S ≤ maximalIdeal 𝒪 • S := by
    intro d hd
    have hmem : ∀ i, d i ∈ maximalIdeal 𝒪 := fun i =>
      mem_maximalIdeal_of_sum_irreducibleBrauerCharacter hp hω hπ hker e d
        ((hmemS d).mp hd) i
    choose d' hd' using fun i => Ideal.mem_span_singleton'.mp (hmax ▸ hmem i)
    have hd'S : d' ∈ S := by
      refine (hmemS d').mpr fun g hg => ?_
      have hrel := (hmemS d).mp hd g hg
      have hfac : ϖ * ∑ i, d' i * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪)
          (e.toAlgHom.comp π).toRingHom i g = 0 := by
        rw [Finset.mul_sum, ← hrel]
        exact Finset.sum_congr rfl fun i _ => by rw [← hd' i]; ring
      exact (mul_eq_zero.mp hfac).resolve_left hϖ.ne_zero
    have hdeq : d = ϖ • d' := by funext i; rw [← hd' i]; simp [mul_comm]
    rw [hdeq]
    exact Submodule.smul_mem_smul (hmax ▸ Ideal.mem_span_singleton_self ϖ) hd'S
  -- Nakayama
  have hSbot : S = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ S (IsNoetherian.noetherian S) hstep
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)
  exact (Submodule.mem_bot _).mp (hSbot ▸ (hmemS c).mpr h)

end OddOrder.RepresentationTheory.Modular
