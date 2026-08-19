/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CentralSylowComplement
import OddOrder.GroupTheory.RepresentationTheory.Modular.DecompositionBlockDiagonal
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlockCartan

/-!
# Navarro (6.13): the Cartan matrix of `B_0` is the `1 × 1` matrix `(|G|_p)`

`PrincipalBlockCartan` produces the character-degree form of Navarro (6.13),

`|N| · ∑_{χ ∈ Irr(B_0)} χ(1)² = |G|`,

for `G` with a normal `p`-complement `N`.  What the Brauer–Suzuki argument cites is the *Cartan
matrix* form: `IBr(B_0) = {φ_0}` is a single Brauer character, so the Cartan matrix of `B_0` is
`1 × 1`, and its entry is `c_{φ_0 φ_0} = |G|_p`.

The two are the same statement once the column `φ_0` of the decomposition matrix is known:

* `d_{χ φ_0} = 0` for `χ ∉ Irr(B_0)` — block diagonality of `D`
  (`decompositionMatrix_eq_zero_of_blockOfIrr_ne`);
* `d_{χ φ_0} = χ(1)` for `χ ∈ Irr(B_0)` — expand `χ⁰` at `1`: block diagonality kills every
  column but `φ_0` (which is the *only* Brauer character of `B_0`,
  `eq_of_principalBlock_of_normalPComplement`), and `φ_0(1) = 1`
  (`subsingleton_of_principalBlock_of_normalPComplement`).

So `c_{φ_0 φ_0} = ∑_χ d_{χ φ_0}² = ∑_{χ ∈ Irr(B_0)} χ(1)²`.

## Main results

* `OddOrder.RepresentationTheory.Modular.decompositionMatrix_principalBlock_eq_card` —
  `d_{χ φ_0} = χ(1)` on `Irr(B_0)`
* `OddOrder.RepresentationTheory.Modular.card_mul_cartanMatrix_principalBlock` —
  `|N| · c_{φ_0 φ_0} = |G|`
* `OddOrder.RepresentationTheory.Modular.cartanMatrix_principalBlock_eq_card_sylow` —
  **`c_{φ_0 φ_0} = |G|_p`**, the form the Brauer–Suzuki argument cites (`hcart`)
* `…_eq_card_sylow_of_hasNormalPComplement` — the same with the complement packaged as
  `OddOrder.Isaacs.Ch05.HasNormalPComplement`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G ι : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
variable [Fact p.Prime] [CharP (ResidueField 𝒪) p]
  {N : Subgroup G} [N.Normal] (hNp : ¬ p ∣ Nat.card ↥N) (hquot : IsPGroup p (G ⧸ N))
  (S : Sylow p G) {φ₀ : ι}
  (hφ₀ : Quotient.mk (blockSetoid π hπ hlin) φ₀ = principalBlock π hπ hlin hnil)

/-! ### The column of `D` at the unique Brauer character of `B_0` -/

omit [Fintype ι'] [Fact p.Prime] [CharP (ResidueField 𝒪) p] in
include hp hω hω' hkerJ hφ₀ in
/-- **Off `Irr(B_0)` the column `φ_0` of the decomposition matrix vanishes.** -/
theorem decompositionMatrix_principalBlock_eq_zero {i : ι'}
    (hi : blockOfIrr e hπ hlin hnil i ≠ principalBlock π hπ hlin hnil) :
    decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i φ₀ = 0 :=
  decompositionMatrix_eq_zero_of_blockOfIrr_ne hp hω hω' hπ hlin hkerJ hnil e i
    (by rw [hφ₀]; exact fun hc => hi hc.symm)

set_option maxHeartbeats 800000 in
-- Both the `𝒪`-valued and the `K`-valued reading of `χ(1)` have to be unified through
-- `algebraMap_ordinaryCharacter`.
omit [Fintype ι'] in
include hp hω hω' hkerJ hNp hquot S hφ₀ in
/-- **On `Irr(B_0)` the column `φ_0` of the decomposition matrix is the degree**: `d_{χ φ_0} =
χ(1)`.  Expand `χ⁰` at `1`; every other column vanishes because `φ_0` is the only irreducible
Brauer character of `B_0`, and `φ_0(1) = 1`. -/
theorem decompositionMatrix_principalBlock_eq_card {i : ι'}
    (hi : blockOfIrr e hπ hlin hnil i = principalBlock π hπ hlin hnil) :
    ((decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i φ₀ : ℕ) : K)
      = (Fintype.card (m i) : K) := by
  classical
  -- `φ_0` has degree one
  have : Subsingleton (nn φ₀) :=
    subsingleton_of_principalBlock_of_normalPComplement π hπ hlin hnil hNp hquot S hφ₀
  have : Unique (nn φ₀) := uniqueOfSubsingleton (Classical.arbitrary (nn φ₀))
  -- only the column `φ_0` survives in `χ⁰`
  have hother : ∀ φ : ι, φ ≠ φ₀ →
      decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i φ = 0 := by
    intro φ hφ
    refine decompositionMatrix_eq_zero_of_blockOfIrr_ne hp hω hω' hπ hlin hkerJ hnil e i ?_
    rw [hi]
    exact fun hc =>
      hφ (eq_of_principalBlock_of_normalPComplement π hπ hlin hnil hNp hquot S hc hφ₀)
  have hexp := trace_eq_sum_decompositionMatrix hp hω hω' hπ hlin hkerJ e i 1 (isPRegular_one hp)
  rw [Finset.sum_eq_single φ₀
      (fun φ _ hne => by rw [hother φ hne, Nat.cast_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ φ₀) h),
    irreducibleBrauerCharacter_one π hp φ₀, Fintype.card_unique, Nat.cast_one, mul_one] at hexp
  -- read the same identity in `K`
  have hK : algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) e i 1) = (Fintype.card (m i) : K) := by
    rw [algebraMap_ordinaryCharacter (𝒪 := 𝒪) e i 1,
      show LinearMap.trace K _ (wedderburnRepresentation e i 1)
        = (wedderburnRepresentation e i).character 1 from rfl,
      Representation.char_one, Module.finrank_fintype_fun_eq_card]
  rw [show ordinaryCharacter (𝒪 := 𝒪) e i 1
      = ((decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i φ₀ : ℕ) : 𝒪) from
    hexp, map_natCast] at hK
  exact hK

/-! ### The single Cartan entry -/

set_option maxHeartbeats 800000 in
-- The filtered sum has to be matched against `card_mul_sum_sq_principalBlock` under the same
-- instance chains.
-- `Fintype G` and `Fintype (ConjClasses G)` are what make `principalBlock` and `subgroupSum`
-- elaborate; the section fixes them, so they cannot be replaced by `Finite` here.
set_option linter.unusedFintypeInType false in
omit [DecidableEq (ConjClasses G)] in
include hp hω hω' hkerJ hNp hquot S hφ₀ in
/-- **Navarro (6.13), Cartan form.**  For `G` with a normal `p`-complement `N` and `φ_0` the
unique irreducible Brauer character of `B_0`, `|N| · c_{φ_0 φ_0} = |G|`; that is, the Cartan
matrix of `B_0` is the `1 × 1` matrix `(|G|_p)`. -/
theorem card_mul_cartanMatrix_principalBlock :
    ((Nat.card ↥N : ℕ) : K)
        * ((cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀ : ℕ) : K)
      = ((Nat.card G : ℕ) : K) := by
  classical
  have hsum : ((cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀ : ℕ) : K)
      = ∑ i ∈ Finset.univ.filter
          (fun i => blockOfIrr e hπ hlin hnil i = principalBlock π hπ hlin hnil),
        (Fintype.card (m i) : K) ^ 2 := by
    simp only [cartanMatrix, Nat.cast_sum, Nat.cast_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : blockOfIrr e hπ hlin hnil i = principalBlock π hπ hlin hnil
    · rw [if_pos hi, decompositionMatrix_principalBlock_eq_card hp hω hω' hπ hlin hkerJ hnil e
        hNp hquot S hφ₀ hi, sq]
    · rw [if_neg hi, decompositionMatrix_principalBlock_eq_zero hp hω hω' hπ hlin hkerJ hnil e
        hφ₀ hi, Nat.cast_zero, mul_zero]
  rw [hsum]
  exact card_mul_sum_sq_principalBlock e hπ hlin hnil ‹N.Normal› hNp S.isPGroup'
    (by rw [sup_comm]; exact sylow_sup_eq_top_of_isPGroup_quotient hquot S)

-- `Fintype G` and `Fintype (ConjClasses G)` are what make `principalBlock` elaborate; the section
-- fixes them, so they cannot be replaced by `Finite` here.
set_option linter.unusedFintypeInType false in
omit [DecidableEq (ConjClasses G)] in
include hp hω hω' hkerJ hnil hNp hquot S hφ₀ in
/-- **Navarro (6.13) in the form the Brauer–Suzuki argument cites**: for `G` with a normal
`p`-complement, the single Cartan invariant of the principal block is `c_{φ_0 φ_0} = |G|_p`.

`K` has characteristic zero, so `|N| · c_{φ_0 φ_0} = |G|` may be read in `ℕ`; cancelling `|N|`
against `|N| · [G : N] = |G|` leaves `c_{φ_0 φ_0} = [G : N] = |S|`. -/
theorem cartanMatrix_principalBlock_eq_card_sylow :
    cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀
      = Nat.card ↥(S : Subgroup G) := by
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  have hK := card_mul_cartanMatrix_principalBlock hp hω hω' hπ hlin hkerJ hnil e hNp hquot S hφ₀
  have hN : Nat.card ↥N * cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀
      = Nat.card G := by exact_mod_cast hK
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥N)) ?_
  rw [hN, ← index_eq_card_sylow_of_isPGroup_quotient hNp hquot S, Subgroup.card_mul_index N]

set_option maxHeartbeats 800000 in
-- Same modular-datum chain as the theorem it repackages.
set_option linter.unusedFintypeInType false in
omit [DecidableEq (ConjClasses G)] in
include hp hω hω' hkerJ hnil in
/-- **Navarro (6.13), the form the Brauer–Suzuki proof cites on p. 132**: for a group with a
normal `p`-complement the Cartan invariant of the principal block is the order of a Sylow
`p`-subgroup.  The complement is unpacked from `HasNormalPComplement`
(`not_dvd_card_of_isComplement'`, `isPGroup_quotient_of_isComplement'`). -/
theorem cartanMatrix_principalBlock_eq_card_sylow_of_hasNormalPComplement
    (hcomp : OddOrder.Isaacs.Ch05.HasNormalPComplement p G) (S : Sylow p G) {φ₀ : ι}
    (hφ₀ : Quotient.mk (blockSetoid π hπ hlin) φ₀ = principalBlock π hπ hlin hnil) :
    cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀
      = Nat.card ↥(S : Subgroup G) := by
  obtain ⟨N, hN, hc⟩ := hcomp
  have := hN
  exact cartanMatrix_principalBlock_eq_card_sylow hp hω hω' hπ hlin hkerJ hnil e
    (not_dvd_card_of_isComplement' S (hc S)) (isPGroup_quotient_of_isComplement' S (hc S)) S hφ₀

end OddOrder.RepresentationTheory.Modular
