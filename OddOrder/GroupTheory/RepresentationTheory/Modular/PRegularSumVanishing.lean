/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.PRegularSumBlock
import OddOrder.GroupTheory.RepresentationTheory.Modular.PairingZeroBlock

/-!
# `ω_χ(Ĝ⁰) = 0` outside the principal block

Navarro's Lemma (3.32) says `Ĝ⁰ f_{B_0} = Ĝ⁰`, hence `λ_B(Ĝ⁰) = 0` for `B ≠ B_0`.  Written on the
ordinary side this is

`ω_χ(Ĝ⁰) · χ(1) = ∑_{g ∈ G⁰} χ(g) = 0`  for `χ ∉ Irr(B_0)`,

the first equality being `centralScalar_pRegularSum_mul_character_one` and the second Navarro
(3.20) (`sum_pRegular_trace_eq_zero_of_centralCharacterAlg_ne`) paired against the trivial
character.  Since `χ(1)` is a positive integer and `K` has characteristic zero, `ω_χ(Ĝ⁰) = 0`.

## Main results

* `OddOrder.RepresentationTheory.Modular.centralScalar_pRegularSum_eq_zero`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [CharZero K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G ι : Type*} [Group G] [Fintype G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [DecidableEq ι]
  [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  [Invertible (Nat.card G : K)]
variable {L' : Type*} [AddCommGroup L'] [Module 𝒪 L'] [Module.Free 𝒪 L'] [Module.Finite 𝒪 L']
variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

set_option maxHeartbeats 800000 in
-- The character sum, its descent and the cancellation run under the same instance chains.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
include hp hω hω' hπ hlin hkerJ in
open scoped Classical in
/-- **`ω_χ(Ĝ⁰) = 0` for `χ` outside the block of the trivial character.**  This is Navarro (3.32)
on the ordinary side; reducing it gives `λ_B(Ĝ⁰) = 0` for `B ≠ B_0`. -/
theorem centralScalar_pRegularSum_eq_zero (i : ι') (σ : Representation 𝒪 G L')
    (hσ : ∀ g : G, LinearMap.trace 𝒪 L' (σ g) = 1)
    (hne : ∀ φ μ : ι,
      decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i φ ≠ 0 →
      decompositionNumber (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ σ μ ≠ 0 →
      MatrixModule.centralCharacterAlg π φ hπ hlin
        ≠ MatrixModule.centralCharacterAlg π μ hπ hlin) :
    MatrixModule.centralScalar e.toAlgHom.toRingHom i (pRegularSum p K) = 0 := by
  classical
  -- the character sum over `G⁰` vanishes, first over `𝒪` and then over `K`
  have hzero := sum_pRegular_trace_eq_zero_of_centralCharacterAlg_ne hp hω hω' hπ hlin hkerJ e
    (K := K) (wedderburnLatticeRepresentation (𝒪 := 𝒪) e i) σ hσ hne
  have hsum : ∑ g ∈ Finset.univ.filter (fun g : G => IsPRegular p g),
      (wedderburnRepresentation e i).character g = 0 := by
    have := congrArg (algebraMap 𝒪 K) hzero
    rw [map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun g _ => (algebraMap_ordinaryCharacter (𝒪 := 𝒪) e i g).symm
  -- `χ(1) ≠ 0`
  have hone : (wedderburnRepresentation e i).character 1 = (Fintype.card (m i) : K) := by
    rw [Representation.char_one, Module.finrank_fintype_fun_eq_card]
  have hone0 : (wedderburnRepresentation e i).character 1 ≠ 0 := by
    rw [hone]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine (mul_eq_zero.mp ?_).resolve_right hone0
  rw [centralScalar_pRegularSum_mul_character_one e i p, hsum]

end OddOrder.RepresentationTheory.Modular
