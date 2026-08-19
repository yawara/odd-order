/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.PPrimeSubgroupRestriction
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlockBasicSet

/-!
# The change-of-basis matrix `U` of Navarro (7.3) is integral

`PrincipalBlockBasicSet` builds `U` from an abstract family `a` expressing
`φ_μ = ∑_{χ ∈ Irr(B_0)} a_{μχ} χ⁰`, and proves Navarro (7.3)/(7.4) for any such family.  The
`K`-valued family of `BrauerFromOrdinary` is *not* integral — it is the pseudo-inverse `D C⁻¹` —
but Navarro (3.16) supplies an integral one, and that is what the Brauer–Suzuki argument on
pp. 141–142 needs: the columns of `D_𝓑 = D_B U` have to be columns of integers.

So this file
* collects the per-`μ` families of (3.16) into a single `A : IBr → Irr → ℤ` (`exists_intBlockCoeff`)
* writes `U` itself as an integer matrix (`intBasicSetMatrix`), using that the signs
  `ε_j = χ_j(t)` are `±1` and `K` has characteristic zero, so each `ε_j` is the image of an
  integer `basicSetSign j`
* descends Navarro (7.3)/(7.4) to `ℤ`, by injectivity of `ℤ → K`.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.basicSetSign` — `ε_j = ±1` as an integer
* `OddOrder.RepresentationTheory.Modular.intBasicSetMatrix` — `U` over `ℤ`

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_intBlockCoeff` — the integral family of (3.16)
* `OddOrder.RepresentationTheory.Modular.sum_decompositionMatrix_mul_intBasicSetMatrix` —
  `D_𝓑 = D_B U` over `ℤ`
* `OddOrder.RepresentationTheory.Modular.sum_intBasicSetMatrix_mul_cartanMatrix` —
  `UᵗCU = 1 + δ` over `ℤ`

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (3.16), (7.3), (7.4).
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule
open OddOrder.RepresentationTheory

/-! ### The integral coefficient family -/

section IntCoeff

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
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
variable {N : ℕ} {ωBT : K}

set_option maxHeartbeats 400000 in
-- The whole Brauer-characterization chain, once per index.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
open scoped Classical in
include hp hω hω' hπ hlin hkerJ e hnil in
/-- **Navarro (3.16) collected over all of `IBr(G)`**: a single integer matrix `A` with
`φ_ν = ∑_{χ ∈ Irr(block ν)} A_{νχ} χ⁰` on the `p`-regular classes, vanishing off the block.

This is exactly the pair of hypotheses `ha0` / `hasum` that `PrincipalBlockBasicSet` asks of a
coefficient family, so `U` may be built from it. -/
theorem exists_intBlockCoeff [IsAlgClosed (ResidueField 𝒪)] [IsAlgClosed K] (hN : N ≠ 0)
    (hgN : ∀ g : G, g ^ N = 1) (hωBT : IsPrimitiveRoot ωBT N) :
    ∃ A : ι → ι' → ℤ,
      (∀ (ν : ι) (l : ι'), blockOfIrr e hπ hlin hnil l
        ≠ Quotient.mk (blockSetoid π hπ hlin) ν → A ν l = 0) ∧
      ∀ (ν : ι) {y : G}, IsPRegular p y →
        (∑ l ∈ Finset.univ.filter (fun l => blockOfIrr e hπ hlin hnil l
            = Quotient.mk (blockSetoid π hπ hlin) ν),
          (A ν l : K) * algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) e l y))
          = algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π ν y) := by
  classical
  choose A hA0 hAsum using fun ν : ι =>
    exists_int_block_sum_eq_irreducibleBrauerCharacter_of_isAlgClosed (ι' := ι') (m := m) hp
      hω hω' hπ hlin hkerJ e hnil hN hgN hωBT ν
  refine ⟨A, hA0, fun ν y hy => ?_⟩
  have hfull : (∑ l ∈ Finset.univ.filter (fun l => blockOfIrr e hπ hlin hnil l
        = Quotient.mk (blockSetoid π hπ hlin) ν),
        (A ν l : K) * algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) e l y))
      = ∑ l : ι', (A ν l : K) * algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) e l y) :=
    Finset.sum_subset (Finset.subset_univ _) fun l _ hl => by
      rw [hA0 ν l fun hc => hl (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hc⟩), Int.cast_zero,
        zero_mul]
  rw [hfull]
  exact (hAsum ν y hy).symm

end IntCoeff

/-! ### `U` as an integer matrix -/

section IntMatrix

variable {K G κ ιG : Type*} [Field K] [CharZero K] [Group G] [DecidableEq κ]
  {mG : κ → Type*} [∀ i, Fintype (mG i)] [∀ i, DecidableEq (mG i)]
variable (eG : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (mG i) (mG i) K)

open scoped Classical in
/-- **The sign `ε_j = χ_j(u)` as an integer.**  Meaningful only where `ε_j² = 1`
(`intCast_basicSetSign`), which for `χ_j ∈ Irr(B_0)` is Navarro (7.2). -/
noncomputable def basicSetSign (u : G) (j : κ) : ℤ :=
  if (wedderburnRepresentation eG j).character u = 1 then 1 else -1

omit [DecidableEq κ] in
/-- Where `ε_j² = 1`, the integer `basicSetSign` really is `ε_j`.  Characteristic zero is what
tells `1` and `-1` apart. -/
theorem intCast_basicSetSign {u : G} {j : κ}
    (hj : (wedderburnRepresentation eG j).character u
      * (wedderburnRepresentation eG j).character u = 1) :
    ((basicSetSign eG u j : ℤ) : K) = (wedderburnRepresentation eG j).character u := by
  rcases mul_self_eq_one_iff.mp hj with h | h
  · rw [basicSetSign, if_pos h, Int.cast_one, h]
  · have hne : (wedderburnRepresentation eG j).character u ≠ 1 := fun hc => by
      rw [hc] at h; norm_num at h
    rw [basicSetSign, if_neg hne, Int.cast_neg, Int.cast_one, h]

/-- The row `(D_𝓑)_{i·}` over `ℤ` casts to the row over `K`. -/
theorem intCast_signRelationRow {u : G} {j₀ i j : κ}
    (hj : (wedderburnRepresentation eG j).character u
      * (wedderburnRepresentation eG j).character u = 1)
    (hj₀ : (wedderburnRepresentation eG j₀).character u
      * (wedderburnRepresentation eG j₀).character u = 1) :
    ((signRelationRow (basicSetSign eG u) j₀ i j : ℤ) : K)
      = signRelationRow (fun l => (wedderburnRepresentation eG l).character u) j₀ i j := by
  rw [signRelationRow, signRelationRow, Int.cast_sub, apply_ite ((Int.cast : ℤ → K)),
    apply_ite ((Int.cast : ℤ → K)), Int.cast_zero, intCast_basicSetSign eG hj,
    intCast_basicSetSign eG hj₀]

/-- **The change-of-basis matrix `U` over `ℤ`**, for an integral family `A` expressing
`φ_μ = ∑_{χ ∈ Irr(B_0)} A_{μχ} χ⁰`: the entries are `u_{μj} = A_{μj} ε_j - A_{μj₀} ε_{j₀}`. -/
noncomputable def intBasicSetMatrix (A : ιG → κ → ℤ) (u : G) (j₀ : κ) (μ : ιG) (j : κ) : ℤ :=
  A μ j * basicSetSign eG u j - A μ j₀ * basicSetSign eG u j₀

omit [DecidableEq κ] in
/-- The integer matrix casts to `basicSetMatrixOf` of the cast family — so all of Navarro
(7.3)/(7.4) applies to it. -/
theorem intCast_intBasicSetMatrix (A : ιG → κ → ℤ) {u : G} {j₀ : κ} (μ : ιG) {j : κ}
    (hj : (wedderburnRepresentation eG j).character u
      * (wedderburnRepresentation eG j).character u = 1)
    (hj₀ : (wedderburnRepresentation eG j₀).character u
      * (wedderburnRepresentation eG j₀).character u = 1) :
    ((intBasicSetMatrix eG A u j₀ μ j : ℤ) : K)
      = basicSetMatrixOf eG (fun ν l => (A ν l : K)) u j₀ μ j := by
  rw [intBasicSetMatrix, basicSetMatrixOf, Int.cast_sub, Int.cast_mul, Int.cast_mul,
    intCast_basicSetSign eG hj, intCast_basicSetSign eG hj₀]

end IntMatrix

/-! ### Navarro (7.3)/(7.4) over `ℤ` -/

section IntKleinFour

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsIntegrallyClosed 𝒪]
  [IsAlgClosed (FractionRing 𝒪)]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
  [Fact p.Prime] [CharP (ResidueField 𝒪) p]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] [Invertible (Nat.card G : K)] {t : G} [Fintype ↥(centralizerOf t)]
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [Fintype ι'] [∀ i, Nonempty (m i)]
variable {κ : Type*} {mG : κ → Type*} [∀ i, Fintype (mG i)] [∀ i, DecidableEq (mG i)]
  [Fintype κ] [DecidableEq κ] [∀ i, Nonempty (mG i)]
variable {ιG : Type*} {nnG : ιG → Type*} [∀ i, Fintype (nnG i)] [∀ i, DecidableEq (nnG i)]
  [Fintype ιG] [DecidableEq ιG] [∀ i, Nonempty (nnG i)]
variable (hp : p.Prime) (hx : IsPElement p t)
  {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf t)))
  (e : MonoidAlgebra K ↥(centralizerOf t) ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
  (eG : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (mG i) (mG i) K)
  {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t) →+*
    ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t)),
    π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t)))
  (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪)
      (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t)),
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf t)))
  {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
  (hconv : ∀ b : Block π hπ hlin,
    inducedBlockOfCentralizer t π hπ hlin πG hπG hlinG hnilG hp hx b
      = principalBlock πG hπG hlinG hnilG → b = principalBlock π hπ hlin hnil)
  {N : Subgroup ↥(centralizerOf t)} [N.Normal] (hNp : ¬ p ∣ Nat.card ↥N)
  (hquot : IsPGroup p (↥(centralizerOf t) ⧸ N)) (S : Sylow p ↥(centralizerOf t))
  {φ₀ : ι} (hφ₀ : Quotient.mk (blockSetoid π hπ hlin) φ₀
    = principalBlock π hπ hlin hnil)
  (ht : t * t = 1)
  {ωG : 𝒪} (hωG : IsPrimitiveRoot ωG (pRegularExponent p G))
  {ω'G : ResidueField 𝒪} (hω'G : IsPrimitiveRoot ω'G (pRegularExponent p G))
  (hkerJG : RingHom.ker πG = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))

set_option maxHeartbeats 1000000 in
-- Same chain as the `K`-valued statement it descends.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open scoped Classical in
include hp hx hω hω' e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ ht in
/-- **`D_𝓑 = D_B U` over `ℤ`.**  Both sides are integers, so the `K`-valued identity descends. -/
theorem sum_decompositionMatrix_mul_intBasicSetMatrix {A : ιG → κ → ℤ}
    (hasum : ∀ (ν : ιG) {y : G}, IsPRegular p y →
      (∑ l ∈ Finset.univ.filter (fun l => blockOfIrr eG hπG hlinG hnilG l
          = Quotient.mk (blockSetoid πG hπG hlinG) ν),
        (A ν l : K) * algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) eG l y))
        = algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) πG ν y))
    (hconjall : ∀ v : G, IsPElement p v → v ≠ 1 → IsConj t v) (ht1 : t ≠ 1)
    (hcart : cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀ = 4)
    {j₀ : κ} (hj₀ : blockOfIrr eG hπG hlinG hnilG j₀ = principalBlock πG hπG hlinG hnilG)
    {i : κ} (hi : blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG)
    {j : κ} (hjB : blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG)
    (hjne : j ≠ j₀) :
    (∑ μ : ιG, (decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i μ : ℤ)
        * intBasicSetMatrix eG A t j₀ μ j)
      = signRelationRow (basicSetSign eG t) j₀ i j := by
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  have hεj := character_involution_mul_self hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil hnilG hω'
    hζ hζk hζK hconv hNp hquot S hφ₀ ht hconjall ht1 hcart hjB
  have hεj₀ := character_involution_mul_self hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil hnilG hω'
    hζ hζk hζK hconv hNp hquot S hφ₀ ht hconjall ht1 hcart hj₀
  refine (Int.cast_injective (α := K)) ?_
  rw [Int.cast_sum, intCast_signRelationRow eG hεj hεj₀,
    ← sum_decompositionMatrix_mul_basicSetMatrixOf hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil
      hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ ht hωG hω'G hkerJG hasum hconjall ht1 hcart
      hj₀ hi hjB hjne]
  exact Finset.sum_congr rfl fun μ _ => by
    rw [Int.cast_mul, Int.cast_natCast, intCast_intBasicSetMatrix eG A μ hεj hεj₀]

set_option maxHeartbeats 1000000 in
-- Same chain as the `K`-valued statement it descends.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open scoped Classical in
include hp hx hω hω' e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ ht in
/-- **`C_𝓑 = UᵗCU = 1 + δ` over `ℤ`.**  This is the form the Brauer–Suzuki argument on
pp. 141–142 uses: the Gram matrix of the basic set is an *integer* matrix. -/
theorem sum_intBasicSetMatrix_mul_cartanMatrix {A : ιG → κ → ℤ}
    (ha0 : ∀ (ν : ιG) (l : κ), blockOfIrr eG hπG hlinG hnilG l
      ≠ Quotient.mk (blockSetoid πG hπG hlinG) ν → A ν l = 0)
    (hasum : ∀ (ν : ιG) {y : G}, IsPRegular p y →
      (∑ l ∈ Finset.univ.filter (fun l => blockOfIrr eG hπG hlinG hnilG l
          = Quotient.mk (blockSetoid πG hπG hlinG) ν),
        (A ν l : K) * algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) eG l y))
        = algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) πG ν y))
    (hconjall : ∀ v : G, IsPElement p v → v ≠ 1 → IsConj t v) (ht1 : t ≠ 1)
    (hcart : cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀ = 4)
    {j₀ : κ} (hj₀ : blockOfIrr eG hπG hlinG hnilG j₀ = principalBlock πG hπG hlinG hnilG)
    {j : κ} (hjB : blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG)
    (hjne : j ≠ j₀) {k : κ}
    (hkB : blockOfIrr eG hπG hlinG hnilG k = principalBlock πG hπG hlinG hnilG) (hkne : k ≠ j₀) :
    (∑ μ : ιG, ∑ τ : ιG, intBasicSetMatrix eG A t j₀ μ j
        * (cartanMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG μ τ : ℤ)
        * intBasicSetMatrix eG A t j₀ τ k)
      = 1 + (if j = k then 1 else 0) := by
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  have hεj := character_involution_mul_self hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil hnilG hω'
    hζ hζk hζK hconv hNp hquot S hφ₀ ht hconjall ht1 hcart hjB
  have hεk := character_involution_mul_self hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil hnilG hω'
    hζ hζk hζK hconv hNp hquot S hφ₀ ht hconjall ht1 hcart hkB
  have hεj₀ := character_involution_mul_self hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil hnilG hω'
    hζ hζk hζK hconv hNp hquot S hφ₀ ht hconjall ht1 hcart hj₀
  refine (Int.cast_injective (α := K)) ?_
  rw [Int.cast_sum, Int.cast_add, Int.cast_one, apply_ite ((Int.cast : ℤ → K)), Int.cast_one,
    Int.cast_zero,
    ← sum_basicSetMatrixOf_mul_cartanMatrix hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil hnilG hω'
      hζ hζk hζK hconv hNp hquot S hφ₀ ht hωG hω'G hkerJG
      (fun ν l hl => by rw [ha0 ν l hl, Int.cast_zero]) hasum hconjall ht1 hcart hj₀ hjB
      hjne hkB hkne]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Int.cast_sum]
  exact Finset.sum_congr rfl fun τ _ => by
    rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, intCast_intBasicSetMatrix eG A μ hεj hεj₀,
      intCast_intBasicSetMatrix eG A τ hεk hεj₀]

end IntKleinFour

end OddOrder.RepresentationTheory.Modular
