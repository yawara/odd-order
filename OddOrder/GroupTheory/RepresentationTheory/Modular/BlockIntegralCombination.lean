/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerFromOrdinary
import OddOrder.GroupTheory.RepresentationTheory.Modular.PRegularPartCharacter

/-!
# Navarro (3.16): `IBr(B)` is a `ℤ`-combination of `{χ⁰ : χ ∈ Irr(B)}`

Navarro (2.16) — `exists_int_sum_wedderburnRepresentation` — gives *some* family of rational
integers `a_i` with `φ_{μ_0} = ∑_i a_i χ_i⁰` on the `p`-regular classes.  This file localises it
to the block of `μ_0`: the truncated family

`a'_i = if blockOfIrr i = block(μ_0) then a_i else 0`

does the job just as well.

The verification is in the `IBr` coordinates.  Expanding `χ_i⁰ = ∑_μ d_{iμ} φ_μ` and using that
the `φ_μ` are linearly independent on the `p`-regular classes
(`eq_zero_of_sum_irreducibleBrauerCharacter_ringHom`), the relation says
`∑_i a_i d_{iμ} = δ_{μμ_0}` for every `μ`; and truncating changes nothing, because a nonzero
`d_{iμ}` forces `block(μ) = blockOfIrr i` (`blockOfIrr_eq_of_decompositionMatrix_ne_zero`):

* for `μ` in the block of `μ_0` the discarded terms have `d_{iμ} = 0`;
* for `μ` outside it the surviving terms have `d_{iμ} = 0`, and `δ_{μμ_0} = 0` as well.

⚠ **The coefficients cannot be taken to be `ordinaryCombinationCoeff`.**  Those are the entries of
`D C⁻¹` with `C = DᵀD`, a pseudo-inverse, which is not integral in general — already
`D = (1,1)ᵀ` gives `D C⁻¹ = (1/2, 1/2)ᵀ`.  Nor is the family here equal to them: the `χ_i⁰` are
*not* linearly independent on the `p`-regular classes (there are more of them than there are
`p`-regular classes), so the coefficients are not unique.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_int_block_sum_eq_irreducibleBrauerCharacter` —
  **Navarro (3.16)**

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (3.16).
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.RepresentationTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Fintype G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [DecidableEq ι]
  [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  [Invertible (Nat.card G : K)]
variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
variable [FaithfulSMul 𝒪 K] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]
  (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    MatrixModule.blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
variable {N : ℕ} {ωBT : K}

set_option maxHeartbeats 1000000 in
-- The block-diagonality and independence statements carry the full modular-datum chain; the
-- section's `Fintype`/`DecidableEq` instances are what make them elaborate.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open scoped Classical in
include hp hω hω' hπ hlin hkerJ e hnil in
/-- **Navarro (3.16)**: `μ_0 ∈ IBr(B)` is a `ℤ`-combination of `{χ⁰ : χ ∈ Irr(B)}`. -/
theorem exists_int_block_sum_eq_irreducibleBrauerCharacter (hN : N ≠ 0)
    (hgN : ∀ g : G, g ^ N = 1) (hωBT : IsPrimitiveRoot ωBT N) (μ₀ : ι)
    (hsub : ∀ Q : Subgroup G, ¬ p ∣ Nat.card ↥Q →
      (fun g => algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ₀ g)) ∘ Q.subtype
        ∈ virtualCharacters K ↥Q) :
    ∃ a : ι' → ℤ,
      (∀ i : ι', blockOfIrr e hπ hlin hnil i
        ≠ Quotient.mk (MatrixModule.blockSetoid π hπ hlin) μ₀ → a i = 0) ∧
      ∀ g : G, IsPRegular p g →
        algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ₀ g)
          = ∑ i : ι', (a i : K) * algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) e i g) := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  have hinj : Function.Injective (algebraMap 𝒪 K) := IsFractionRing.injective 𝒪 K
  -- (1) Navarro (2.16) gives integers; move the identity to `𝒪`
  obtain ⟨a, ha⟩ := exists_int_sum_wedderburnRepresentation e hN hgN hωBT hp
    (fun g h => congrArg (algebraMap 𝒪 K) (irreducibleBrauerCharacter_conj π μ₀ g h)) hsub
  have haO : ∀ g : G, IsPRegular p g →
      irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ₀ g
        = ∑ i : ι', (a i : 𝒪) * ordinaryCharacter (𝒪 := 𝒪) e i g := by
    intro g hg
    refine hinj ?_
    rw [ha g hg, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Representation.character, map_mul, map_intCast,
      algebraMap_ordinaryCharacter (𝒪 := 𝒪) e i g]
  -- (2) any integral combination of the `χ_i⁰`, in `IBr` coordinates
  have hswap : ∀ (c : ι' → ℤ) (g : G), IsPRegular p g →
      (∑ i : ι', (c i : 𝒪) * ordinaryCharacter (𝒪 := 𝒪) e i g)
        = ∑ μ : ι, ((∑ i : ι', c i *
              (decompositionMatrix hp hω hω' hπ hlin hkerJ e i μ : ℤ) : ℤ) : 𝒪)
            * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ g := by
    intro c g hg
    calc (∑ i : ι', (c i : 𝒪) * ordinaryCharacter (𝒪 := 𝒪) e i g)
        = ∑ i : ι', ∑ μ : ι, (c i : 𝒪)
            * ((decompositionMatrix hp hω hω' hπ hlin hkerJ e i μ : ℕ) : 𝒪)
            * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ g := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ordinaryCharacter, trace_eq_sum_decompositionMatrix hp hω hω' hπ hlin hkerJ e i g hg,
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun μ _ => by ring
      _ = ∑ μ : ι, ∑ i : ι', (c i : 𝒪)
            * ((decompositionMatrix hp hω hω' hπ hlin hkerJ e i μ : ℕ) : 𝒪)
            * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ g := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun μ _ => ?_
          push_cast
          rw [Finset.sum_mul]
  have hdelta : ∀ g : G, irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ₀ g
      = ∑ μ : ι, ((if μ = μ₀ then (1 : ℤ) else 0 : ℤ) : 𝒪)
          * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ g := fun g => by
    rw [Finset.sum_eq_single μ₀ (fun μ _ hμ => by rw [if_neg hμ, Int.cast_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ μ₀) h), if_pos rfl, Int.cast_one, one_mul]
  -- (3) linear independence of `IBr` pins the coordinates
  have hcoord : ∀ μ : ι,
      (∑ i : ι', a i * (decompositionMatrix hp hω hω' hπ hlin hkerJ e i μ : ℤ))
        = if μ = μ₀ then 1 else 0 := by
    have hzero := eq_zero_of_sum_irreducibleBrauerCharacter_ringHom (𝒪 := 𝒪) (nn := nn) hp hω' hπ
      hlin hkerJ (fun μ => ((∑ i : ι', a i *
            (decompositionMatrix hp hω hω' hπ hlin hkerJ e i μ : ℤ) : ℤ) : 𝒪)
          - ((if μ = μ₀ then (1 : ℤ) else 0 : ℤ) : 𝒪))
      (fun g hg => by
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [← hswap a g hg, ← hdelta g, ← haO g hg, sub_self])
    intro μ
    have hsub0 : ((∑ i : ι', a i *
          (decompositionMatrix hp hω hω' hπ hlin hkerJ e i μ : ℤ) : ℤ) : 𝒪)
        - ((if μ = μ₀ then (1 : ℤ) else 0 : ℤ) : 𝒪) = 0 := congrFun hzero μ
    exact_mod_cast sub_eq_zero.mp hsub0
  -- (4) truncating to the block does not change the coordinates
  refine ⟨fun i => if blockOfIrr e hπ hlin hnil i
      = Quotient.mk (MatrixModule.blockSetoid π hπ hlin) μ₀ then a i else 0,
    fun i hi => if_neg hi, fun g hg => ?_⟩
  have htrunc : ∀ μ : ι, (∑ i : ι', (if blockOfIrr e hπ hlin hnil i
        = Quotient.mk (MatrixModule.blockSetoid π hπ hlin) μ₀ then a i else 0) *
        (decompositionMatrix hp hω hω' hπ hlin hkerJ e i μ : ℤ))
      = if μ = μ₀ then 1 else 0 := by
    intro μ
    by_cases hμ : Quotient.mk (MatrixModule.blockSetoid π hπ hlin) μ
        = Quotient.mk (MatrixModule.blockSetoid π hπ hlin) μ₀
    · -- inside the block: the discarded terms had `d_{iμ} = 0` anyway
      rw [← hcoord μ]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hb : blockOfIrr e hπ hlin hnil i
          = Quotient.mk (MatrixModule.blockSetoid π hπ hlin) μ₀
      · rw [if_pos hb]
      · rw [if_neg hb, zero_mul]
        by_cases hd : decompositionMatrix hp hω hω' hπ hlin hkerJ e i μ = 0
        · rw [hd, Nat.cast_zero, mul_zero]
        · exact absurd ((blockOfIrr_eq_of_decompositionMatrix_ne_zero hp hω hω' hπ hlin hkerJ
            hnil e i hd).symm.trans hμ) hb
    · -- outside it: every surviving term has `d_{iμ} = 0`, and the right side is `0` too
      rw [if_neg (fun hcon => hμ (by rw [hcon]))]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hb : blockOfIrr e hπ hlin hnil i
          = Quotient.mk (MatrixModule.blockSetoid π hπ hlin) μ₀
      · rw [if_pos hb]
        by_cases hd : decompositionMatrix hp hω hω' hπ hlin hkerJ e i μ = 0
        · rw [hd, Nat.cast_zero, mul_zero]
        · exact absurd ((blockOfIrr_eq_of_decompositionMatrix_ne_zero hp hω hω' hπ hlin hkerJ
            hnil e i hd).trans hb) hμ
      · rw [if_neg hb, zero_mul]
  -- reassemble
  have hO : irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ₀ g
      = ∑ i : ι', ((if blockOfIrr e hπ hlin hnil i
          = Quotient.mk (MatrixModule.blockSetoid π hπ hlin) μ₀ then a i else 0 : ℤ) : 𝒪)
        * ordinaryCharacter (𝒪 := 𝒪) e i g := by
    rw [hswap (fun i => if blockOfIrr e hπ hlin hnil i
        = Quotient.mk (MatrixModule.blockSetoid π hπ hlin) μ₀ then a i else 0) g hg,
      Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) => by rw [htrunc μ], ← hdelta g]
  rw [hO, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, map_intCast]

end OddOrder.RepresentationTheory.Modular
