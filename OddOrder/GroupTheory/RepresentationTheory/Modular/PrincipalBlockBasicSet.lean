/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BasicSetDecomposition
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerFromOrdinary
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlockInvolution

/-!
# Navarro (7.4): a basic set for the principal block of a Klein four group

Let `G` have a Klein four Sylow `2`-subgroup and a single class of involutions, so that Navarro
(7.2) gives `Irr(B_0) = {χ_0, χ_1, χ_2, χ_3}` with `χ_i(t) = ε_i = ±1`, together with the single
relation

`∑_{i} ε_i χ_i(g) = 0`  (`g ∈ G⁰`)

(`sum_character_mul_character_involution_eq_zero`).  Fix an index `j₀` with `ε_{j₀} = -1`
(`exists_character_involution_eq_neg_one`).  Then

`𝓑 = {ε_j χ_j⁰ : j ≠ j₀}`

is a basic set of `B_0`: the three functions are independent on `G⁰`
(`eq_zero_of_vanishing_on_pRegular_of_apply_eq_zero`) and every `χ_i⁰` is the integer combination
of them recorded by the matrix

`(D_𝓑)_{ij} = δ_{ij} ε_j - δ_{i j₀} ε_{j₀}`,

whose Gram matrix is `C_𝓑 = D_𝓑ᵗ D_𝓑 = 1 + δ`.

The first half of the file is the underlying algebra, which needs nothing but the relation and
`ε_i² = 1`.  The second half puts it in the modular setting: the change-of-basis matrix `U` of
Navarro (7.3) — expressing `IBr(B_0)` in `𝓑` — is written down from the coefficients of
`sum_ordinaryCombination_block_eq_irreducibleBrauerCharacter`, and `UᵗCU = 1 + δ` follows.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.signRelationRow` — the row `(D_𝓑)_{i·}`
* `OddOrder.RepresentationTheory.Modular.principalBasicSet` — the basic set `𝓑`
* `OddOrder.RepresentationTheory.Modular.principalBasicSetMatrix` — the matrix `U` of (7.3)

## Main results

* `OddOrder.RepresentationTheory.Modular.sum_signRelationRow_mul` — `c_i = ∑_j (D_𝓑)_{ij} ε_j c_j`
* `OddOrder.RepresentationTheory.Modular.sum_signRelationRow_mul_signRelationRow` — `C_𝓑 = 1 + δ`
* `OddOrder.RepresentationTheory.Modular.character_eq_sum_signRelationRow_mul_principalBasicSet`
* `OddOrder.RepresentationTheory.Modular.sum_principalBasicSetMatrix_mul_principalBasicSet` —
  `φ_μ = ∑_j u_{μj} η_j`
* `OddOrder.RepresentationTheory.Modular.sum_decompositionMatrix_mul_principalBasicSetMatrix` —
  `D_𝓑 = D_B U`
* `OddOrder.RepresentationTheory.Modular.sum_principalBasicSetMatrix_mul_cartanMatrix` —
  `UᵗCU = 1 + δ`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule
open OddOrder.RepresentationTheory

/-! ### The algebra of a single sign relation -/

section SignRelation

variable {K κ : Type*} [CommRing K] [DecidableEq κ]

/-- **The decomposition matrix of `Irr(B_0)` in the basic set `𝓑 = {ε_j c_j : j ≠ j₀}`.**  If the
only relation among the `c_i` is `∑_{i ∈ S} ε_i c_i = 0` and `ε_i² = 1`, then dropping the index
`j₀` leaves a basis, in which `c_i` has coordinates

`(D_𝓑)_{ij} = δ_{ij} ε_j - δ_{i j₀} ε_{j₀}`

— the identity matrix bordered by the row `(-ε_{j₀}, …, -ε_{j₀})` at `i = j₀`.  (With Navarro's
normalisation `ε_{j₀} = -1` that row is all ones, as on p. 134.) -/
def signRelationRow (ε : κ → K) (j₀ i j : κ) : K :=
  (if i = j then ε j else 0) - (if i = j₀ then ε j₀ else 0)

private theorem sum_ite_eq_mul {S : Finset κ} (b : κ) (v : K) (f : κ → K) :
    (∑ i ∈ S, (if i = b then v else 0) * f i) = if b ∈ S then v * f b else 0 := by
  simp only [ite_mul, zero_mul]
  exact Finset.sum_ite_eq' S b fun i => v * f i

/-- **`c_i = ∑_{j ≠ j₀} (D_𝓑)_{ij} (ε_j c_j)`.**  Off `j₀` this is `ε_i² c_i = c_i`; at `i = j₀`
it is the relation `∑_{i ∈ S} ε_i c_i = 0` solved for `c_{j₀}`. -/
theorem sum_signRelationRow_mul {S : Finset κ} {ε c : κ → K} {j₀ : κ} (hj₀ : j₀ ∈ S)
    (hε : ∀ i ∈ S, ε i * ε i = 1) (hrel : (∑ i ∈ S, ε i * c i) = 0) {i : κ} (hi : i ∈ S) :
    (∑ j ∈ S.erase j₀, signRelationRow ε j₀ i j * (ε j * c j)) = c i := by
  classical
  have hsplit : (∑ j ∈ S.erase j₀, signRelationRow ε j₀ i j * (ε j * c j))
      = (∑ j ∈ S.erase j₀, (if i = j then ε j else 0) * (ε j * c j))
        - (if i = j₀ then ε j₀ else 0) * ∑ j ∈ S.erase j₀, ε j * c j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [signRelationRow]; ring
  have herase : (∑ j ∈ S.erase j₀, ε j * c j) = -(ε j₀ * c j₀) := by
    have h : ε j₀ * c j₀ + ∑ j ∈ S.erase j₀, ε j * c j = 0 := by
      rw [Finset.add_sum_erase S (fun j => ε j * c j) hj₀]
      exact hrel
    linear_combination h
  have hfirst : (∑ j ∈ S.erase j₀, (if i = j then ε j else 0) * (ε j * c j))
      = if i ∈ S.erase j₀ then c i else 0 := by
    rw [Finset.sum_congr rfl fun j _ => by
      rw [show (if i = j then ε j else 0) = (if j = i then ε i else 0) from by
        by_cases h : i = j
        · rw [if_pos h, if_pos h.symm, h]
        · rw [if_neg h, if_neg fun hc => h hc.symm]],
      sum_ite_eq_mul (S := S.erase j₀) i (ε i) (fun j => ε j * c j)]
    by_cases h : i ∈ S.erase j₀
    · rw [if_pos h, if_pos h, ← mul_assoc, hε i hi, one_mul]
    · rw [if_neg h, if_neg h]
  rw [hsplit, hfirst, herase]
  by_cases h : i = j₀
  · subst h
    rw [if_neg (Finset.notMem_erase i S), if_pos rfl, mul_neg, ← mul_assoc, hε i hi, one_mul,
      sub_neg_eq_add, zero_add]
  · rw [if_pos (Finset.mem_erase.mpr ⟨h, hi⟩), if_neg h, zero_mul, sub_zero]

/-- **The coordinates of `∑_{i ∈ S} a_i c_i` in the basic set** are `a_j ε_j - a_{j₀} ε_{j₀}`. -/
theorem sum_mul_signRelationRow {S : Finset κ} {ε a : κ → K} {j₀ : κ} (hj₀ : j₀ ∈ S) {j : κ}
    (hj : j ∈ S) : (∑ i ∈ S, a i * signRelationRow ε j₀ i j) = a j * ε j - a j₀ * ε j₀ := by
  classical
  have hsplit : (∑ i ∈ S, a i * signRelationRow ε j₀ i j)
      = (∑ i ∈ S, (if i = j then ε j else 0) * a i)
        - ∑ i ∈ S, (if i = j₀ then ε j₀ else 0) * a i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [signRelationRow]; ring
  rw [hsplit, sum_ite_eq_mul j (ε j) a, sum_ite_eq_mul j₀ (ε j₀) a, if_pos hj, if_pos hj₀,
    mul_comm (ε j), mul_comm (ε j₀)]

/-- **`C_𝓑 = D_𝓑ᵗ D_𝓑 = 1 + δ`.**  The `(j,k)` entry is `δ_{jk} ε_j ε_k` from the identity part
plus `ε_{j₀}²` from the row at `j₀`; the two cross terms vanish because neither `j` nor `k` is
`j₀`. -/
theorem sum_signRelationRow_mul_signRelationRow {S : Finset κ} {ε : κ → K} {j₀ : κ} (hj₀ : j₀ ∈ S)
    (hε : ∀ i ∈ S, ε i * ε i = 1) {j k : κ} (hjS : j ∈ S) (hj : j ≠ j₀) (hk : k ≠ j₀) :
    (∑ i ∈ S, signRelationRow ε j₀ i j * signRelationRow ε j₀ i k)
      = 1 + (if j = k then 1 else 0) := by
  classical
  have hexp : (∑ i ∈ S, signRelationRow ε j₀ i j * signRelationRow ε j₀ i k)
      = ((∑ i ∈ S, (if i = j then ε j else 0) * (if i = k then ε k else 0))
        - ∑ i ∈ S, (if i = j then ε j else 0) * (if i = j₀ then ε j₀ else 0))
        - (∑ i ∈ S, (if i = j₀ then ε j₀ else 0) * (if i = k then ε k else 0))
        + ∑ i ∈ S, (if i = j₀ then ε j₀ else 0) * (if i = j₀ then ε j₀ else 0) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [signRelationRow, signRelationRow]; ring
  have h1 : (∑ i ∈ S, (if i = j then ε j else 0) * (if i = k then ε k else 0))
      = if j = k then 1 else 0 := by
    rw [sum_ite_eq_mul j (ε j) (fun i => if i = k then ε k else 0), if_pos hjS]
    by_cases h : j = k
    · subst h; simp [hε j hjS]
    · rw [if_neg h, if_neg h, mul_zero]
  have h2 : (∑ i ∈ S, (if i = j then ε j else 0) * (if i = j₀ then ε j₀ else 0)) = 0 := by
    rw [sum_ite_eq_mul j (ε j) (fun i => if i = j₀ then ε j₀ else 0), if_pos hjS, if_neg hj,
      mul_zero]
  have h3 : (∑ i ∈ S, (if i = j₀ then ε j₀ else 0) * (if i = k then ε k else 0)) = 0 := by
    rw [sum_ite_eq_mul j₀ (ε j₀) (fun i => if i = k then ε k else 0), if_pos hj₀,
      if_neg (fun h : j₀ = k => hk h.symm), mul_zero]
  have h4 : (∑ i ∈ S, (if i = j₀ then ε j₀ else 0) * (if i = j₀ then ε j₀ else 0)) = 1 := by
    rw [sum_ite_eq_mul j₀ (ε j₀) (fun i => if i = j₀ then ε j₀ else 0), if_pos hj₀]
    simp [hε j₀ hj₀]
  rw [hexp, h1, h2, h3, h4, sub_zero, sub_zero, add_comm]

end SignRelation

/-! ### The basic set of the principal block -/

section KleinFour

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
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
  {φ₀ : ι} (hφ₀ : Quotient.mk (blockSetoid π hπ hlin) φ₀ = principalBlock π hπ hlin hnil)
  (ht : t * t = 1)
  {ωG : 𝒪} (hωG : IsPrimitiveRoot ωG (pRegularExponent p G))
  {ω'G : ResidueField 𝒪} (hω'G : IsPrimitiveRoot ω'G (pRegularExponent p G))
  (hkerJG : RingHom.ker πG = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))

open scoped Classical in
/-- **The basic set `𝓑 = {ε_j χ_j⁰ : j ∈ Irr(B_0), j ≠ j₀}` of Navarro (7.4)**, presented as a
family indexed by all of `Irr(G)` that vanishes outside `𝓑`.  Here `ε_j = χ_j(u)` for the
involution `u`. -/
noncomputable def principalBasicSet (u : G) (j₀ j : κ) (g : G) : K :=
  if blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG ∧ j ≠ j₀ then
    (wedderburnRepresentation eG j).character u * (wedderburnRepresentation eG j).character g
  else 0

/-- **The change-of-basis matrix `U` of Navarro (7.3)** for the basic set `𝓑`: writing
`φ_μ = ∑_{i ∈ Irr(B_0)} a_{μi} χ_i⁰`
(`sum_ordinaryCombination_block_eq_irreducibleBrauerCharacter`), the coordinates of `φ_μ` in `𝓑`
are `u_{μj} = a_{μj} ε_j - a_{μj₀} ε_{j₀}` (`sum_mul_signRelationRow`). -/
noncomputable def principalBasicSetMatrix (u : G) (j₀ : κ) (μ : ιG) (j : κ) : K :=
  ordinaryCombinationCoeff hp hωG hω'G hπG hlinG hkerJG eG μ j *
      (wedderburnRepresentation eG j).character u
    - ordinaryCombinationCoeff hp hωG hω'G hπG hlinG hkerJG eG μ j₀ *
      (wedderburnRepresentation eG j₀).character u

set_option maxHeartbeats 1000000 in
-- The sign is read off Navarro (7.2), which carries the full modular-datum chain.
set_option linter.unusedFintypeInType false in
omit [DecidableEq κ] [DecidableEq ιG] in
open scoped Classical in
include hp hx hω hω' e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ ht in
/-- **`ε_j² = 1`** for `χ_j ∈ Irr(B_0)`: Navarro (7.2) gives `χ_j(t) = ±1`. -/
theorem character_involution_mul_self
    (hconjall : ∀ v : G, IsPElement p v → v ≠ 1 → IsConj t v) (ht1 : t ≠ 1)
    (hcart : cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀ = 4)
    {j : κ} (hj : blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG) :
    (wedderburnRepresentation eG j).character t * (wedderburnRepresentation eG j).character t
      = 1 := by
  classical
  obtain ⟨-, hpm⟩ := card_blockOfIrr_principal_eq_four_and_character_involution hp hx hω e eG
    hπG hlinG hπ hlin hkerJ hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ ht hconjall ht1
    (sum_character_mul_character_involution_eq_zero hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil
      hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ ht1 (isPRegular_one hp)) hcart
  rcases hpm j hj with h | h <;> rw [h] <;> norm_num

set_option maxHeartbeats 1000000 in
-- Same chain as the sign statement it uses.
set_option linter.unusedFintypeInType false in
omit [DecidableEq ιG] in
open scoped Classical in
include hp hx hω hω' e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ ht in
/-- **Navarro (7.4), the decomposition matrix in the basic set.**  For `χ_i ∈ Irr(B_0)`,
`χ_i⁰ = ∑_j (D_𝓑)_{ij} η_j` with `(D_𝓑)_{ij} = δ_{ij} ε_j - δ_{i j₀} ε_{j₀}`: off `j₀` this is
just `ε_i² = 1`, and at `i = j₀` it is the relation `∑_{χ ∈ Irr(B_0)} ε_χ χ⁰ = 0` solved for
`χ_{j₀}⁰`. -/
theorem character_eq_sum_signRelationRow_mul_principalBasicSet
    (hconjall : ∀ v : G, IsPElement p v → v ≠ 1 → IsConj t v) (ht1 : t ≠ 1)
    (hcart : cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀ = 4)
    {j₀ : κ} (hj₀ : blockOfIrr eG hπG hlinG hnilG j₀ = principalBlock πG hπG hlinG hnilG)
    {i : κ} (hi : blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG)
    {g : G} (hg : IsPRegular p g) :
    (∑ j : κ, signRelationRow (fun l => (wedderburnRepresentation eG l).character t) j₀ i j
        * principalBasicSet eG hπG hlinG hnilG t j₀ j g)
      = (wedderburnRepresentation eG i).character g := by
  classical
  set Sirr : Finset κ := Finset.univ.filter
    (fun j => blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG) with hSirr
  have hmem : ∀ j : κ, j ∈ Sirr ↔
      blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG := by
    intro j
    rw [hSirr, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hout : ∀ j ∈ (Finset.univ : Finset κ), j ∉ Sirr.erase j₀ →
      signRelationRow (fun l => (wedderburnRepresentation eG l).character t) j₀ i j
        * principalBasicSet eG hπG hlinG hnilG t j₀ j g = 0 := by
    intro j _ hj
    rw [principalBasicSet, if_neg (fun hc => hj (Finset.mem_erase.mpr ⟨hc.2, (hmem j).mpr hc.1⟩)),
      mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ (Sirr.erase j₀)) hout,
    Finset.sum_congr rfl fun j hj => by
      rw [show principalBasicSet eG hπG hlinG hnilG t j₀ j g
          = (wedderburnRepresentation eG j).character t
              * (wedderburnRepresentation eG j).character g from by
        rw [principalBasicSet, if_pos ⟨(hmem j).mp (Finset.mem_of_mem_erase hj),
          Finset.ne_of_mem_erase hj⟩]]]
  exact sum_signRelationRow_mul (S := Sirr)
    (ε := fun l => (wedderburnRepresentation eG l).character t)
    (c := fun l => (wedderburnRepresentation eG l).character g) ((hmem j₀).mpr hj₀)
    (fun l hl => character_involution_mul_self hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil hnilG
      hω' hζ hζk hζK hconv hNp hquot S hφ₀ ht hconjall ht1 hcart ((hmem l).mp hl))
    (by
      rw [Finset.sum_congr rfl fun l _ =>
        mul_comm ((wedderburnRepresentation eG l).character t)
          ((wedderburnRepresentation eG l).character g)]
      exact sum_character_mul_character_involution_eq_zero hp hx hω e eG hπG hlinG hπ hlin hkerJ
        hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ ht1 hg)
    ((hmem i).mpr hi)

/-! ### The change-of-basis matrix `U` -/

set_option maxHeartbeats 800000 in
-- The coefficients carry the `G`-side modular datum; `DecidableEq ιG` is what makes the Cartan
-- inverse inside `ordinaryCombinationCoeff` elaborate.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
omit [DecidableEq κ] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Fact p.Prime] [CharP (ResidueField 𝒪) p]
  [Fintype ↥(centralizerOf t)] in
/-- **`u_{μj} = 0` for `μ ∉ IBr(B_0)` and `j ∈ Irr(B_0)`.**  Both coefficients of `u_{μj}` are
`ordinaryCombinationCoeff`s at indices in `Irr(B_0)`, and those vanish off the block of `μ`. -/
theorem principalBasicSetMatrix_eq_zero_of_ne_principalBlock
    {j₀ : κ} (hj₀ : blockOfIrr eG hπG hlinG hnilG j₀ = principalBlock πG hπG hlinG hnilG)
    {μ : ιG} (hμ : Quotient.mk (blockSetoid πG hπG hlinG) μ ≠ principalBlock πG hπG hlinG hnilG)
    {j : κ} (hj : blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG) :
    principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ j = 0 := by
  rw [principalBasicSetMatrix,
    ordinaryCombinationCoeff_eq_zero_of_blockOfIrr_ne hp hωG hω'G hπG hlinG hkerJG eG hnilG μ
      (by rw [hj]; exact fun hc => hμ hc.symm),
    ordinaryCombinationCoeff_eq_zero_of_blockOfIrr_ne hp hωG hω'G hπG hlinG hkerJG eG hnilG μ
      (by rw [hj₀]; exact fun hc => hμ hc.symm),
    zero_mul, zero_mul, sub_zero]

set_option maxHeartbeats 1000000 in
-- Both halves (the `G`-side coefficients and the `(7.2)` signs) carry their full chains.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open scoped Classical in
include hp hx hω hω' e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ ht in
/-- **`U` really expresses `IBr(B_0)` in the basic set**: `φ_μ = ∑_j u_{μj} η_j` on `G⁰`.

`φ_μ` is the combination `∑_{i ∈ Irr(B_0)} a_{μi} χ_i⁰`
(`sum_ordinaryCombination_block_eq_irreducibleBrauerCharacter`, the `K`-form of Navarro (3.16)),
and `∑_i a_{μi} (D_𝓑)_{ij} = a_{μj} ε_j - a_{μj₀} ε_{j₀} = u_{μj}` is precisely how `U` was
defined. -/
theorem sum_principalBasicSetMatrix_mul_principalBasicSet
    (hconjall : ∀ v : G, IsPElement p v → v ≠ 1 → IsConj t v) (ht1 : t ≠ 1)
    (hcart : cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀ = 4)
    {j₀ : κ} (hj₀ : blockOfIrr eG hπG hlinG hnilG j₀ = principalBlock πG hπG hlinG hnilG)
    {μ : ιG} (hμ : Quotient.mk (blockSetoid πG hπG hlinG) μ = principalBlock πG hπG hlinG hnilG)
    {g : G} (hg : IsPRegular p g) :
    (∑ j : κ, principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ j
        * principalBasicSet eG hπG hlinG hnilG t j₀ j g)
      = algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) πG μ g) := by
  classical
  set Sirr : Finset κ := Finset.univ.filter
    (fun j => blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG) with hSirr
  have hmem : ∀ j : κ, j ∈ Sirr ↔
      blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG := by
    intro j
    rw [hSirr, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hout : ∀ j ∈ (Finset.univ : Finset κ), j ∉ Sirr.erase j₀ →
      principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ j
        * principalBasicSet eG hπG hlinG hnilG t j₀ j g = 0 := by
    intro j _ hj
    rw [principalBasicSet, if_neg (fun hc => hj (Finset.mem_erase.mpr ⟨hc.2, (hmem j).mpr hc.1⟩)),
      mul_zero]
  have hεsq : ∀ l ∈ Sirr, (wedderburnRepresentation eG l).character t
      * (wedderburnRepresentation eG l).character t = 1 := fun l hl =>
    character_involution_mul_self hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil hnilG hω' hζ hζk hζK
      hconv hNp hquot S hφ₀ ht hconjall ht1 hcart ((hmem l).mp hl)
  have hrel : (∑ l ∈ Sirr, (wedderburnRepresentation eG l).character t
      * (wedderburnRepresentation eG l).character g) = 0 := by
    rw [Finset.sum_congr rfl fun l _ =>
      mul_comm ((wedderburnRepresentation eG l).character t)
        ((wedderburnRepresentation eG l).character g)]
    exact sum_character_mul_character_involution_eq_zero hp hx hω e eG hπG hlinG hπ hlin hkerJ
      hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ ht1 hg
  have hη : ∀ j ∈ Sirr.erase j₀, principalBasicSet eG hπG hlinG hnilG t j₀ j g
      = (wedderburnRepresentation eG j).character t
        * (wedderburnRepresentation eG j).character g := fun j hj => by
    rw [principalBasicSet, if_pos ⟨(hmem j).mp (Finset.mem_of_mem_erase hj),
      Finset.ne_of_mem_erase hj⟩]
  have hU : ∀ j ∈ Sirr.erase j₀,
      principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ j
        = ∑ i ∈ Sirr, ordinaryCombinationCoeff hp hωG hω'G hπG hlinG hkerJG eG μ i
            * signRelationRow (fun l => (wedderburnRepresentation eG l).character t) j₀ i j :=
    fun j hj => by
      rw [principalBasicSetMatrix]
      exact (sum_mul_signRelationRow (S := Sirr)
        (ε := fun l => (wedderburnRepresentation eG l).character t)
        (a := fun i => ordinaryCombinationCoeff hp hωG hω'G hπG hlinG hkerJG eG μ i)
        ((hmem j₀).mpr hj₀) (Finset.mem_of_mem_erase hj)).symm
  rw [← Finset.sum_subset (Finset.subset_univ (Sirr.erase j₀)) hout,
    Finset.sum_congr rfl fun j hj => by rw [hη j hj, hU j hj]]
  -- swap the two sums and collapse the inner one with the basic-set decomposition
  have hswap : (∑ j ∈ Sirr.erase j₀,
        (∑ i ∈ Sirr, ordinaryCombinationCoeff hp hωG hω'G hπG hlinG hkerJG eG μ i
          * signRelationRow (fun l => (wedderburnRepresentation eG l).character t) j₀ i j)
        * ((wedderburnRepresentation eG j).character t
            * (wedderburnRepresentation eG j).character g))
      = ∑ i ∈ Sirr, ordinaryCombinationCoeff hp hωG hω'G hπG hlinG hkerJG eG μ i
          * (wedderburnRepresentation eG i).character g := by
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_mul _ _ _, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← sum_signRelationRow_mul (S := Sirr)
      (ε := fun l => (wedderburnRepresentation eG l).character t)
      (c := fun l => (wedderburnRepresentation eG l).character g) ((hmem j₀).mpr hj₀) hεsq hrel
      hi, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hswap]
  -- and read the result off the `K`-form of Navarro (3.16)
  have h316 := sum_ordinaryCombination_block_eq_irreducibleBrauerCharacter hp hωG hω'G hπG hlinG
    hkerJG eG hnilG μ hg
  simp only [hμ] at h316
  rw [← hSirr] at h316
  rw [← h316]
  exact Finset.sum_congr rfl fun i _ => by
    rw [algebraMap_ordinaryCharacter (𝒪 := 𝒪) eG i g]; rfl

/-! ### `D_𝓑 = D_B U`, and the Gram matrix `UᵗCU = 1 + δ` -/

set_option maxHeartbeats 800000 in
-- Both factors carry the `G`-side modular datum.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
omit [DecidableEq κ] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Fact p.Prime] [CharP (ResidueField 𝒪) p]
  [Fintype ↥(centralizerOf t)] in
/-- **The row of `D_B U` at `χ_i ∉ Irr(B_0)` vanishes.**  A nonzero term needs `d_{iμ} ≠ 0`, which
puts `μ` in the block of `χ_i`, and `u_{μj} ≠ 0`, which puts `μ` in `B_0`. -/
theorem sum_decompositionMatrix_mul_principalBasicSetMatrix_eq_zero
    {j₀ : κ} (hj₀ : blockOfIrr eG hπG hlinG hnilG j₀ = principalBlock πG hπG hlinG hnilG)
    {i : κ} (hi : blockOfIrr eG hπG hlinG hnilG i ≠ principalBlock πG hπG hlinG hnilG)
    {j : κ} (hj : blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG) :
    (∑ μ : ιG, (decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i μ : K)
        * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ j) = 0 := by
  refine Finset.sum_eq_zero fun μ _ => ?_
  by_cases hμ : Quotient.mk (blockSetoid πG hπG hlinG) μ = principalBlock πG hπG hlinG hnilG
  · rw [decompositionMatrix_eq_zero_of_blockOfIrr_ne hp hωG hω'G hπG hlinG hkerJG hnilG eG i
      (by rw [hμ]; exact fun hc => hi hc.symm), Nat.cast_zero, zero_mul]
  · rw [principalBasicSetMatrix_eq_zero_of_ne_principalBlock hp eG hπG hlinG hnilG hωG hω'G
      hkerJG hj₀ hμ hj, mul_zero]

set_option maxHeartbeats 1000000 in
-- Both the `(7.2)` independence statement and the `G`-side datum carry their full chains.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open scoped Classical in
include hp hx hω hω' e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ ht in
/-- **`D_𝓑 = D_B U`.**  Both `∑_μ d_{iμ} u_{μ·}` and `(D_𝓑)_{i·}` express `χ_i⁰` in the basic set,
and the basic set is independent on `G⁰` (`eq_zero_of_vanishing_on_pRegular_of_apply_eq_zero`), so
the two coordinate vectors agree. -/
theorem sum_decompositionMatrix_mul_principalBasicSetMatrix
    (hconjall : ∀ v : G, IsPElement p v → v ≠ 1 → IsConj t v) (ht1 : t ≠ 1)
    (hcart : cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀ = 4)
    {j₀ : κ} (hj₀ : blockOfIrr eG hπG hlinG hnilG j₀ = principalBlock πG hπG hlinG hnilG)
    {i : κ} (hi : blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG)
    {j : κ} (hjB : blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG)
    (hjne : j ≠ j₀) :
    (∑ μ : ιG, (decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i μ : K)
        * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ j)
      = signRelationRow (fun l => (wedderburnRepresentation eG l).character t) j₀ i j := by
  classical
  set Sirr : Finset κ := Finset.univ.filter
    (fun j => blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG) with hSirr
  have hmem : ∀ j : κ, j ∈ Sirr ↔
      blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG := by
    intro j
    rw [hSirr, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  -- the difference between the two coordinate vectors, as a relation among `Irr(B_0)`
  set a : κ → K := fun l =>
    if l ∈ Sirr.erase j₀ then
      ((∑ μ : ιG, (decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i μ : K)
            * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ l)
          - signRelationRow (fun l => (wedderburnRepresentation eG l).character t) j₀ i l)
        * (wedderburnRepresentation eG l).character t
    else 0 with hadef
  have hsupp : ∀ l : κ,
      blockOfIrr eG hπG hlinG hnilG l ≠ principalBlock πG hπG hlinG hnilG → a l = 0 := fun l hl =>
    if_neg fun hc => hl ((hmem l).mp (Finset.mem_of_mem_erase hc))
  have ha₀ : a j₀ = 0 := if_neg (Finset.notMem_erase j₀ Sirr)
  have hvan : ∀ g : G, IsPRegular p g →
      (∑ l : κ, a l * (wedderburnRepresentation eG l).character g) = 0 := by
    intro g hg
    have hkey : ∀ l : κ, a l * (wedderburnRepresentation eG l).character g
        = ((∑ μ : ιG,
              (decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i μ : K)
                * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ l)
            - signRelationRow (fun l => (wedderburnRepresentation eG l).character t) j₀ i l)
          * principalBasicSet eG hπG hlinG hnilG t j₀ l g := by
      intro l
      by_cases hl : l ∈ Sirr.erase j₀
      · rw [hadef]
        simp only
        rw [if_pos hl, principalBasicSet, if_pos ⟨(hmem l).mp (Finset.mem_of_mem_erase hl),
          Finset.ne_of_mem_erase hl⟩]
        ring
      · rw [hadef]
        simp only
        rw [if_neg hl, principalBasicSet,
          if_neg fun hc => hl (Finset.mem_erase.mpr ⟨hc.2, (hmem l).mpr hc.1⟩), zero_mul, mul_zero]
    rw [Finset.sum_congr rfl fun l _ => (hkey l).trans (sub_mul _ _ _),
      Finset.sum_sub_distrib,
      character_eq_sum_signRelationRow_mul_principalBasicSet hp hx hω e eG hπG hlinG hπ hlin hkerJ
        hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ ht hconjall ht1 hcart hj₀ hi hg]
    -- the first sum is `∑_μ d_{iμ} φ_μ(g) = χ_i(g)`
    have hswap : (∑ l : κ, (∑ μ : ιG,
          (decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i μ : K)
            * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ l)
          * principalBasicSet eG hπG hlinG hnilG t j₀ l g)
        = ∑ μ : ιG,
            (decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i μ : K)
              * algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) πG μ g) := by
      rw [Finset.sum_congr rfl fun l _ => Finset.sum_mul _ _ _, Finset.sum_comm]
      refine Finset.sum_congr rfl fun μ _ => ?_
      by_cases hμ : Quotient.mk (blockSetoid πG hπG hlinG) μ = principalBlock πG hπG hlinG hnilG
      · rw [Finset.sum_congr rfl fun l _ => mul_assoc _ _ _, ← Finset.mul_sum,
          sum_principalBasicSetMatrix_mul_principalBasicSet hp hx hω e eG hπG hlinG hπ hlin
            hkerJ hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ ht hωG hω'G hkerJG hconjall ht1
            hcart hj₀ hμ hg]
      · rw [decompositionMatrix_eq_zero_of_blockOfIrr_ne hp hωG hω'G hπG hlinG hkerJG hnilG eG i
          (by rw [hi]; exact fun hc => hμ hc), Nat.cast_zero, zero_mul]
        exact Finset.sum_eq_zero fun l _ => by rw [zero_mul, zero_mul]
    rw [hswap]
    -- and that is exactly `χ_i(g)`
    have htr : (∑ μ : ιG,
          (decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i μ : K)
            * algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) πG μ g))
        = (wedderburnRepresentation eG i).character g := by
      have h0 : algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) eG i g)
          = (wedderburnRepresentation eG i).character g :=
        algebraMap_ordinaryCharacter (𝒪 := 𝒪) eG i g
      rw [← h0, ordinaryCharacter,
        trace_eq_sum_decompositionMatrix hp hωG hω'G hπG hlinG hkerJG eG i g hg, map_sum]
      exact Finset.sum_congr rfl fun μ _ => by rw [map_mul, map_natCast]
    rw [htr, sub_self]
  have hzero := eq_zero_of_vanishing_on_pRegular_of_apply_eq_zero hp hx hω e eG hπG hlinG hπ hlin
    hkerJ hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ hconjall ht1 hcart ht hsupp hvan hj₀ ha₀
  -- evaluate the relation at `j`, where the sign is a unit
  have hj := congrFun hzero j
  rw [hadef] at hj
  simp only [Pi.zero_apply] at hj
  rw [if_pos (Finset.mem_erase.mpr ⟨hjne, (hmem j).mpr hjB⟩)] at hj
  have hεj : (wedderburnRepresentation eG j).character t ≠ 0 := by
    intro hc
    have := character_involution_mul_self hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil hnilG hω' hζ
      hζk hζK hconv hNp hquot S hφ₀ ht hconjall ht1 hcart hjB
    rw [hc, mul_zero] at this
    exact zero_ne_one this
  exact sub_eq_zero.mp ((mul_eq_zero.mp hj).resolve_right hεj)

set_option maxHeartbeats 1000000 in
-- Same chain as the two row statements it combines.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open scoped Classical in
include hp hx hω hω' e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ ht in
/-- **Navarro (7.4): `C_𝓑 = UᵗCU = 1 + δ`.**  Expanding `C = D_BᵗD_B` and collecting by the
ordinary index turns `UᵗCU` into the Gram matrix of `D_𝓑 = D_B U`, whose rows are
`δ_{ij} ε_j - δ_{i j₀} ε_{j₀}` on `Irr(B_0)` and zero off it. -/
theorem sum_principalBasicSetMatrix_mul_cartanMatrix
    (hconjall : ∀ v : G, IsPElement p v → v ≠ 1 → IsConj t v) (ht1 : t ≠ 1)
    (hcart : cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀ = 4)
    {j₀ : κ} (hj₀ : blockOfIrr eG hπG hlinG hnilG j₀ = principalBlock πG hπG hlinG hnilG)
    {j : κ} (hjB : blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG)
    (hjne : j ≠ j₀) {k : κ}
    (hkB : blockOfIrr eG hπG hlinG hnilG k = principalBlock πG hπG hlinG hnilG) (hkne : k ≠ j₀) :
    (∑ μ : ιG, ∑ τ : ιG, principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ j
        * (cartanMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG μ τ : K)
        * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ τ k)
      = 1 + (if j = k then 1 else 0) := by
  classical
  set Sirr : Finset κ := Finset.univ.filter
    (fun j => blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG) with hSirr
  have hmem : ∀ j : κ, j ∈ Sirr ↔
      blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG := by
    intro j
    rw [hSirr, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  -- `UᵗCU` is the Gram matrix of `D_B U`
  have hstep : ∀ μ τ : ιG,
      principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ j
          * (cartanMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG μ τ : K)
          * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ τ k
        = ∑ i : κ,
            ((decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i μ : K)
              * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ j)
            * ((decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i τ : K)
              * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ τ k) := by
    intro μ τ
    rw [cartanMatrix, Nat.cast_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring
  have hgram : (∑ μ : ιG, ∑ τ : ιG,
        principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ j
          * (cartanMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG μ τ : K)
          * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ τ k)
      = ∑ i : κ,
          (∑ μ : ιG,
            (decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i μ : K)
              * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ j)
          * ∑ τ : ιG,
            (decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i τ : K)
              * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ τ k :=
    calc (∑ μ : ιG, ∑ τ : ιG,
          principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ j
            * (cartanMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG μ τ : K)
            * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ τ k)
        = ∑ μ : ιG, ∑ τ : ιG, ∑ i : κ,
            ((decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i μ : K)
              * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ j)
            * ((decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i τ : K)
              * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ τ k) :=
          Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun τ _ => hstep μ τ
      _ = ∑ i : κ, ∑ μ : ιG, ∑ τ : ιG,
            ((decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i μ : K)
              * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ μ j)
            * ((decompositionMatrix (𝒪 := 𝒪) (nn := nnG) hp hωG hω'G hπG hlinG hkerJG eG i τ : K)
              * principalBasicSetMatrix hp eG hπG hlinG hωG hω'G hkerJG t j₀ τ k) := by
          rw [Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) => Finset.sum_comm, Finset.sum_comm]
      _ = _ := Finset.sum_congr rfl fun i _ => (Finset.sum_mul_sum _ _ _ _).symm
  rw [hgram, ← Finset.sum_subset (Finset.subset_univ Sirr) fun i _ hi => by
    rw [sum_decompositionMatrix_mul_principalBasicSetMatrix_eq_zero hp eG hπG hlinG hnilG hωG hω'G
      hkerJG hj₀ (fun hc => hi ((hmem i).mpr hc)) hjB, zero_mul],
    Finset.sum_congr rfl fun i hi => by
      rw [sum_decompositionMatrix_mul_principalBasicSetMatrix hp hx hω e eG hπG hlinG hπ hlin
          hkerJ hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ ht hωG hω'G hkerJG hconjall ht1
          hcart hj₀ ((hmem i).mp hi) hjB hjne,
        sum_decompositionMatrix_mul_principalBasicSetMatrix hp hx hω e eG hπG hlinG hπ hlin
          hkerJ hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ ht hωG hω'G hkerJG hconjall ht1
          hcart hj₀ ((hmem i).mp hi) hkB hkne]]
  exact sum_signRelationRow_mul_signRelationRow ((hmem j₀).mpr hj₀)
    (fun l hl => character_involution_mul_self hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil hnilG
      hω' hζ hζk hζK hconv hNp hquot S hφ₀ ht hconjall ht1 hcart ((hmem l).mp hl))
    ((hmem j).mpr hjB) hjne hkne

end KleinFour

end OddOrder.RepresentationTheory.Modular
