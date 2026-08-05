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

## Main results

* `OddOrder.RepresentationTheory.Modular.sum_signRelationRow_mul` — `χ_i = ∑_j (D_𝓑)_{ij} η_j`
* `OddOrder.RepresentationTheory.Modular.sum_signRelationRow_mul_signRelationRow` — `C_𝓑 = 1 + δ`
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

end KleinFour

end OddOrder.RepresentationTheory.Modular
