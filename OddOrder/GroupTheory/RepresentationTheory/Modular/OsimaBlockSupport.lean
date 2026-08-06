/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockIdempotentOrdinary
import OddOrder.GroupTheory.RepresentationTheory.Modular.DecompositionBlockDiagonal
import OddOrder.GroupTheory.RepresentationTheory.Modular.ProjectiveCharacterVanishing

/-!
# Osima's theorem: a block sees no `p`-singular element

For a block `B` and a `p`-singular `g`,

`∑_{χ ∈ Irr(B)} χ(1) χ(g) = 0`.

This is the vanishing half of **Navarro (3.8), Corollary (Osima)** — the half saying that the
block idempotent `f_B = ∑_{χ ∈ Irr(B)} e_χ` has zero coefficient at every `p`-singular element.
It is what lets Külshammer's route to the converse of the third main theorem cover *all* `g` and
not only the `p`-regular ones: Külshammer's formula itself is unavailable at a `p`-singular `g`,
because the hypothesis it carries (`hweak`, the block-wise column sum against a Sylow element)
is essentially equivalent to `g` being `p`-regular.

Navarro proves integrality and vanishing together and therefore works modulo `𝔪`; only vanishing
is needed here, and over `𝒪` — of characteristic `0` — it holds exactly, which collapses his
(3.6) and (3.8) into the single computation below.  Dickson's theorem, which his integrality half
needs, is not required.

The argument: expand `χ(1)` along its row of the decomposition matrix and exchange the sums.  The
inner sum `∑_{χ ∈ Irr(B)} d_{χφ} χ(g)` vanishes for *every* `φ`, by block diagonality of `D` —
either `φ` lies in `B`, in which case the terms outside `Irr(B)` already vanish and the sum is all
of `Φ_φ(g) = 0`, or it does not, in which case every term vanishes separately.

## Main results

* `OddOrder.RepresentationTheory.Modular.sum_ordinaryCharacter_one_mul_eq_zero_of_not_isPRegular`
* `OddOrder.RepresentationTheory.Modular.coeff_blockIdempotent_eq_zero_of_not_isPRegular` — the
  form the block theory consumes
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [CharZero K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G ι : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  [Invertible (Nat.card G : K)]
variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    MatrixModule.blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

omit [CharZero K] in
open scoped Classical in
include hp hω hω' hkerJ hnil in
/-- **The `D`-column of a block, weighted by `χ(g)`, vanishes at a `p`-singular `g`.**

For `φ` in the block `B` the sum extends to all of `Irr(G)` — the omitted `χ` have `d_{χφ} = 0`
by block diagonality — and is therefore `Φ_φ(g)`, which vanishes off the `p`-regular elements.
For `φ` outside `B` every term vanishes for the same reason. -/
theorem sum_decompositionMatrix_mul_ordinaryCharacter_eq_zero (B : MatrixModule.Block π hπ hlin)
    (φ : ι) {g : G} (hg : ¬ IsPRegular p g) :
    ∑ i ∈ Finset.univ.filter
        (fun i => blockOfIrr e hπ hlin hnil i = B),
      (decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ : 𝒪)
        * ordinaryCharacter (𝒪 := 𝒪) e i g = 0 := by
  classical
  by_cases hB : Quotient.mk (MatrixModule.blockSetoid π hπ hlin) φ = B
  · -- the terms outside `Irr(B)` are already zero, so the sum is all of `Φ_φ(g)`
    have hext : ∑ i ∈ Finset.univ.filter
          (fun i => blockOfIrr e hπ hlin hnil i = B),
        (decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ : 𝒪)
          * ordinaryCharacter (𝒪 := 𝒪) e i g
        = ∑ i : ι', (decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ : 𝒪)
          * ordinaryCharacter (𝒪 := 𝒪) e i g := by
      refine Finset.sum_subset (Finset.filter_subset _ _) fun i _ hi => ?_
      have hd : decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ = 0 := by
        by_contra hne
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i,
          (blockOfIrr_eq_of_decompositionMatrix_ne_zero hp hω hω' hπ hlin hkerJ hnil e i
            hne).symm.trans hB⟩)
      rw [hd, Nat.cast_zero, zero_mul]
    rw [hext]
    exact projectiveIndecomposableCharacter_eq_zero hp hω hω' hπ hlin hkerJ e φ hg
  · -- `φ` is outside the block, so no `χ ∈ Irr(B)` can see it
    refine Finset.sum_eq_zero fun i hi => ?_
    have hd : decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ = 0 := by
      by_contra hne
      exact hB ((blockOfIrr_eq_of_decompositionMatrix_ne_zero hp hω hω' hπ hlin hkerJ hnil e i
        hne).trans (Finset.mem_filter.mp hi).2)
    rw [hd, Nat.cast_zero, zero_mul]

-- `ι` indexes `IBr(G)`; it is summed over in the proof only, when `χ(1)` is expanded.
set_option linter.unusedFintypeInType false in
omit [CharZero K] in
open scoped Classical in
include hp hω hω' hkerJ hnil in
/-- **Osima's theorem, vanishing half** — Navarro (3.8): for `g` `p`-singular,

`∑_{χ ∈ Irr(B)} χ(1) χ(g) = 0`.

Expand `χ(1)` by its row of `D` (the identity is `p`-regular), exchange the sums, and apply
`sum_decompositionMatrix_mul_ordinaryCharacter_eq_zero` to each `φ`. -/
theorem sum_ordinaryCharacter_one_mul_eq_zero_of_not_isPRegular
    (B : MatrixModule.Block π hπ hlin) {g : G} (hg : ¬ IsPRegular p g) :
    ∑ i ∈ Finset.univ.filter
        (fun i => blockOfIrr e hπ hlin hnil i = B),
      ordinaryCharacter (𝒪 := 𝒪) e i 1 * ordinaryCharacter (𝒪 := 𝒪) e i g = 0 := by
  classical
  have hone : ∀ i : ι', ordinaryCharacter (𝒪 := 𝒪) e i 1
      = ∑ φ, (decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ : 𝒪)
        * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ 1 :=
    fun i => trace_eq_sum_decompositionMatrix hp hω hω' hπ hlin hkerJ e i 1 (isPRegular_one hp)
  calc ∑ i ∈ Finset.univ.filter
          (fun i => blockOfIrr e hπ hlin hnil i = B),
        ordinaryCharacter (𝒪 := 𝒪) e i 1 * ordinaryCharacter (𝒪 := 𝒪) e i g
      = ∑ i ∈ Finset.univ.filter
          (fun i => blockOfIrr e hπ hlin hnil i = B), ∑ φ,
        ((decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ : 𝒪)
            * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ 1)
          * ordinaryCharacter (𝒪 := 𝒪) e i g := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hone i, Finset.sum_mul]
    _ = ∑ φ, ∑ i ∈ Finset.univ.filter
          (fun i => blockOfIrr e hπ hlin hnil i = B),
        ((decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ : 𝒪)
            * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ 1)
          * ordinaryCharacter (𝒪 := 𝒪) e i g := Finset.sum_comm
    _ = ∑ φ, irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ 1 *
          ∑ i ∈ Finset.univ.filter
              (fun i => blockOfIrr e hπ hlin hnil i = B),
            (decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ : 𝒪)
              * ordinaryCharacter (𝒪 := 𝒪) e i g := by
        refine Finset.sum_congr rfl fun φ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by
        refine Finset.sum_eq_zero fun φ _ => ?_
        rw [sum_decompositionMatrix_mul_ordinaryCharacter_eq_zero hp hω hω' hπ hlin hkerJ hnil e
          B φ hg, mul_zero]

set_option maxHeartbeats 800000 in
-- The block idempotent is compared across `𝒪`, `K` and `k` at once; the class-sum
-- decidability is consumed by the block machinery in the proof.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open scoped Classical in
include hp hω hω' hkerJ hnil e in
/-- **Osima's theorem: a block idempotent vanishes at every `p`-singular element.**

Over `K` the lift of `e_B` is `∑_{χ ∈ Irr(B)} e_χ` (`mapRingHom_blockIdempotent_eq_sum`), whose
coefficient at `g` is `|G|⁻¹ ∑_{χ ∈ Irr(B)} χ(1) χ(g⁻¹)` — zero by the previous theorem, since
`g⁻¹` is `p`-singular exactly when `g` is.  The coefficient of the lift is therefore zero in `𝒪`
by injectivity, hence zero in `k` after reduction.

This is what supplies `hcoeff` at the `p`-singular elements, where Külshammer's formula is
unavailable. -/
theorem coeff_blockIdempotent_eq_zero_of_not_isPRegular
    {B : MatrixModule.Block π hπ hlin} {f : Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)}
    (hidem : IsIdempotentElem f)
    {f' : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)}
    (hf : MonoidAlgebra.mapRingHom G (residue 𝒪) (f : MonoidAlgebra 𝒪 G)
      = (f' : MonoidAlgebra (ResidueField 𝒪) G))
    (hB : MatrixModule.blockCharacterPi π hπ hlin f' = Pi.single B 1)
    {g : G} (hg : ¬ IsPRegular p g) :
    (f' : MonoidAlgebra (ResidueField 𝒪) G).coeff g = 0 := by
  classical
  have hginv : ¬ IsPRegular p g⁻¹ := by
    unfold IsPRegular at hg ⊢
    rwa [orderOf_inv]
  -- the coefficient of the lift, read in `K`
  have hK := mapRingHom_blockIdempotent_eq_sum e hπ hlin hnil hidem hf hB
  have hcoeffK : algebraMap 𝒪 K ((f : MonoidAlgebra 𝒪 G).coeff g) = 0 := by
    have hc := congrArg (fun x : MonoidAlgebra K G => x.coeff g) hK
    rw [MonoidAlgebra.coeff_mapRingHom] at hc
    rw [hc, MonoidAlgebra.coeff_finsetSum]
    have hterm : ∀ i ∈ Finset.univ.filter
          (fun i => blockOfIrr e hπ hlin hnil i = B),
        (ordinaryIdempotent e i).coeff g
          = ⅟(Nat.card G : K) * algebraMap 𝒪 K
            (ordinaryCharacter (𝒪 := 𝒪) e i 1 * ordinaryCharacter (𝒪 := 𝒪) e i g⁻¹) := by
      intro i _
      rw [coeff_ordinaryIdempotent, map_mul, algebraMap_ordinaryCharacter,
        algebraMap_ordinaryCharacter, mul_assoc]
      rfl
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum,
      sum_ordinaryCharacter_one_mul_eq_zero_of_not_isPRegular hp hω hω' hπ hlin hkerJ hnil e B
        hginv, map_zero, mul_zero]
  -- descend to `𝒪`, then reduce
  have hcoeff𝒪 : (f : MonoidAlgebra 𝒪 G).coeff g = 0 :=
    FaithfulSMul.algebraMap_injective 𝒪 K (by rw [hcoeffK, map_zero])
  rw [← hf, MonoidAlgebra.coeff_mapRingHom, hcoeff𝒪, map_zero]

end OddOrder.RepresentationTheory.Modular
