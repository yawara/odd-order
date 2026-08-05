/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerCharacterKernel
import OddOrder.GroupTheory.RepresentationTheory.Modular.KulshammerThirdMain
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlockCartanEntry
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlockNonvanishing
import OddOrder.GroupTheory.RepresentationTheory.Modular.SecondMainBlockOfIrr
import OddOrder.GroupTheory.RepresentationTheory.Modular.ThirdMainEasy

/-!
# `χ(x y) = d^x_{χ φ_0}` when `C_G(x)` has a normal `p`-complement

This is the step Navarro's proof of (7.2) records as

`χ(t s) = d^t_{χ 1_{C^0}}`  for every `χ ∈ Irr(B_0)` and every `s ∈ C_G(t)^0`,

citing Corollary (5.8) and the third main theorem.  Three ingredients combine:

* the **second main theorem** (`generalizedDecompositionNumber_eq_zero_of_blockOfIrr_ne`):
  `d^x_{χ μ} = 0` unless the block of `μ` induces the block of `χ`;
* the **converse of the third main theorem** (Külshammer's route,
  `eq_principalBlock_of_inducedBlockOfNormalizer_eq_intermediate`): a block of `C_G(x)` inducing
  `B_0(G)` is `b_0(C_G(x))`;
* **Navarro (6.13)**: if `C_G(x)` has a normal `p`-complement then `IBr(b_0) = {1_{C^0}}` — a
  single Brauer character, and it is the constant `1` on the `p`-regular classes.

So the expansion `χ(x y) = ∑_μ d^x_{χ μ} μ(y)` collapses to its `φ_0` term, whose Brauer
character value is `1`.

## Main results

* `OddOrder.RepresentationTheory.Modular.irreducibleBrauerCharacter_principalBlock_eq_one` —
  (6.13): the unique Brauer character of `B_0` is the constant `1`
* `OddOrder.RepresentationTheory.Modular.eq_principalBlock_of_inducedBlockOfCentralizer_eq` —
  the converse third main theorem, phrased for `b^G` at a `p`-element
* `OddOrder.RepresentationTheory.Modular.generalizedDecompositionNumber_eq_zero_of_ne_principal`
* `OddOrder.RepresentationTheory.Modular.character_mul_eq_generalizedDecompositionNumber`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule
open OddOrder.RepresentationTheory

/-! ### Navarro (6.13): the unique Brauer character of `B_0` is the constant `1` -/

section BrauerCharacterOne

variable {p : ℕ} [Fact p.Prime] {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [HenselianLocalRing 𝒪]
  [IsPModularSystem p 𝒪] [CharP (ResidueField 𝒪) p]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Finite ι] [∀ i, Nonempty (nn i)]
variable {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)

/-- **Navarro (6.13): the unique irreducible Brauer character of `B_0` is the constant `1`.**
For a group with a normal `p`-complement the simple modules of `B_0` are trivial, so the block
representation is the identity and the Brauer character takes its degree — which is `1` — at
every `p`-regular element. -/
theorem irreducibleBrauerCharacter_principalBlock_eq_one (hp : p.Prime)
    {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
    {N : Subgroup G} [N.Normal] (hNp : ¬ p ∣ Nat.card ↥N) (hquot : IsPGroup p (G ⧸ N))
    (S : Sylow p G) {φ₀ : ι}
    (hφ₀ : Quotient.mk (blockSetoid π hπ hlin) φ₀ = principalBlock π hπ hlin hnil)
    {y : G} (hy : IsPRegular p y) :
    irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ₀ y = 1 := by
  classical
  haveI : Subsingleton (nn φ₀) :=
    subsingleton_of_principalBlock_of_normalPComplement π hπ hlin hnil hNp hquot S hφ₀
  haveI : Unique (nn φ₀) := uniqueOfSubsingleton (Classical.arbitrary (nn φ₀))
  have hrep : blockRepresentation π φ₀ y = 1 := by
    change Matrix.mulVecLin (π (single y (1 : ResidueField 𝒪)) φ₀) = 1
    rw [pi_single_eq_one_principalBlock_of_normalPComplement π hπ hlin hnil hNp hquot S hφ₀ y,
      Matrix.mulVecLin_one]
    rfl
  have hchar := (rep_eq_one_iff_brauerCharacter_eq (𝒪 := 𝒪) (blockRepresentation π φ₀) hp hω'
    hy).mp hrep
  rw [show irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ₀ y
      = brauerCharacter (𝒪 := 𝒪) (pRegularExponent p G) (blockRepresentation π φ₀) y from rfl,
    hchar,
    show brauerCharacter (𝒪 := 𝒪) (pRegularExponent p G) (blockRepresentation π φ₀) 1
      = irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ₀ 1 from rfl,
    irreducibleBrauerCharacter_one π hp φ₀, Fintype.card_unique, Nat.cast_one]

end BrauerCharacterOne

/-! ### The converse of the third main theorem at a `p`-element -/

section Converse

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] {p : ℕ} [Fact p.Prime] [CharP k p] {x : G}
  [Fintype ↥(centralizerOf x)] [DecidableEq (ConjClasses ↥(centralizerOf x))]
  [Fintype (ConjClasses ↥(centralizerOf x))]
variable {ι : Type*} [Finite ι] {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [∀ i, Nonempty (nn i)]
variable (π : MonoidAlgebra k ↥(centralizerOf x) →+* ∀ j, Matrix (nn j) (nn j) k)
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : k) (a : MonoidAlgebra k ↥(centralizerOf x)), π (c • a) = c • π a)
  (hnil : ∀ z : Subalgebra.center k (MonoidAlgebra k ↥(centralizerOf x)),
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable (πG : MonoidAlgebra k G →+* ∀ j, Matrix (nnG j) (nnG j) k) (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : k) (a : MonoidAlgebra k G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center k (MonoidAlgebra k G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)

-- as in (6.14) itself: the class-sum expansion of `Z(k C_G(x))` needs `cl(C_G(x))` finite and
-- decidable, which the statement does not mention
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
open scoped Classical in
/-- **The converse of Brauer's third main theorem at a `p`-element.**  A block of `C_G(x)`
inducing the principal block of `G` is the principal block of `C_G(x)`.

`inducedBlockOfCentralizer` is `inducedBlockOfNormalizer` for `Q = ⟨x⟩`, so this is Külshammer's
`eq_principalBlock_of_inducedBlockOfNormalizer_eq_intermediate` with the four side conditions of
`Q C_G(Q) ≤ C_G(x) ≤ N_G(Q)` discharged by `InducedBlockCentralizer`. -/
theorem eq_principalBlock_of_inducedBlockOfCentralizer_eq (hp : p.Prime) (hx : IsPElement p x)
    {F' : Block πG hπG hlinG → Subalgebra.center k (MonoidAlgebra k G)}
    {F'H : Block π hπ hlin → Subalgebra.center k (MonoidAlgebra k ↥(centralizerOf x))}
    (hB : ∀ B, blockCharacterPi πG hπG hlinG (F' B) = Pi.single B 1)
    (hBH : ∀ B, blockCharacterPi π hπ hlin (F'H B) = Pi.single B 1)
    (hcoeff : ∀ h : ↥(centralizerOf x),
      (h : G) ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) →
      ((F' (principalBlock πG hπG hlinG hnilG) : MonoidAlgebra k G)).coeff (h : G)
        = ((F'H (principalBlock π hπ hlin hnil) :
            MonoidAlgebra k ↥(centralizerOf x))).coeff h)
    (b : Block π hπ hlin)
    (hind : inducedBlockOfCentralizer x π hπ hlin πG hπG hlinG hnilG hp hx b
      = principalBlock πG hπG hlinG hnilG) :
    b = principalBlock π hπ hlin hnil := by
  refine eq_principalBlock_of_inducedBlockOfNormalizer_eq_intermediate π hπ hlin hnil πG hπG
    hlinG hnilG (OddOrder.GroupTheory.isPGroup_zpowers_of_isPElement hx)
    (zpowers_le_centralizerOf x) (centralizer_zpowers_le_centralizerOf x)
    (centralizerOf_le_normalizer_zpowers x) hB hBH hcoeff b ?_
  exact hind

omit [DecidableEq (ConjClasses ↥(centralizerOf x))] [Fintype (ConjClasses ↥(centralizerOf x))] in
open scoped Classical in
/-- **Brauer's third main theorem, easy half, at a `p`-element**: `b_0(C_G(x))^G = B_0(G)`.
`inducedBlockOfCentralizer` is `inducedBlockOfNormalizer` for `Q = ⟨x⟩`. -/
theorem inducedBlockOfCentralizer_principalBlock (hp : p.Prime) (hx : IsPElement p x) :
    inducedBlockOfCentralizer x π hπ hlin πG hπG hlinG hnilG hp hx
        (principalBlock π hπ hlin hnil)
      = principalBlock πG hπG hlinG hnilG :=
  inducedBlockOfNormalizer_principalBlock hπ hlin hnil hπG hlinG hnilG
    (OddOrder.GroupTheory.isPGroup_zpowers_of_isPElement hx) (zpowers_le_centralizerOf x)
    (centralizer_zpowers_le_centralizerOf x) (centralizerOf_le_normalizer_zpowers x)

end Converse

/-! ### The `p`-section of `x` sees only the column `φ_0` -/

section Section

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
  [Fact p.Prime] [CharP (ResidueField 𝒪) p]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] {x : G} [Fintype ↥(centralizerOf x)]
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [Finite ι'] [∀ i, Nonempty (m i)]
variable {κ : Type*} {mG : κ → Type*} [∀ i, Fintype (mG i)] [∀ i, DecidableEq (mG i)]
  [Finite κ] [∀ i, Nonempty (mG i)]
variable {ιG : Type*} {nnG : ιG → Type*} [∀ i, Fintype (nnG i)] [∀ i, DecidableEq (nnG i)]
  [Finite ιG] [∀ i, Nonempty (nnG i)]
variable (hp : p.Prime) (hx : IsPElement p x)
  {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
  (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
  (eG : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (mG i) (mG i) K)
  {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
    ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
    π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))
  (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪)
      (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
  {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
  (hconv : ∀ b : Block π hπ hlin,
    inducedBlockOfCentralizer x π hπ hlin πG hπG hlinG hnilG hp hx b
      = principalBlock πG hπG hlinG hnilG → b = principalBlock π hπ hlin hnil)
  {N : Subgroup ↥(centralizerOf x)} [N.Normal] (hNp : ¬ p ∣ Nat.card ↥N)
  (hquot : IsPGroup p (↥(centralizerOf x) ⧸ N)) (S : Sylow p ↥(centralizerOf x))
  {φ₀ : ι} (hφ₀ : Quotient.mk (blockSetoid π hπ hlin) φ₀ = principalBlock π hπ hlin hnil)

set_option maxHeartbeats 1000000 in
-- Same cost as the (5.8) specialisation it invokes: two block index sets and three incarnations
-- of the block idempotent have to be unified.
omit [Finite κ] in
include hp hx hω e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ in
/-- **Only the column `φ_0` survives on the `p`-section of `x`.**  If `χ_i ∈ Irr(B_0(G))` and
`C_G(x)` has a normal `p`-complement, the generalized decomposition numbers `d^x_{χ_i μ}` vanish
for every `μ ≠ φ_0`.

Second main theorem: a nonzero `d^x_{χ_i μ}` forces the block of `μ` to induce `B_0(G)`; the
converse third main theorem then makes that block `b_0(C_G(x))`, and (6.13) makes `μ = φ_0`. -/
theorem generalizedDecompositionNumber_eq_zero_of_ne_principal {i : κ}
    (hi : blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG)
    {μ : ι} (hμ : μ ≠ φ₀) :
    generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
        ((wedderburnRepresentation eG i).character)
        (fun _ _ hgh => character_eq_of_isConj _ hgh) μ = 0 := by
  refine generalizedDecompositionNumber_eq_zero_of_blockOfIrr_ne hp hx e eG hπG hlinG hπ hlin
    hkerJ hnil hnilG hω hω' hζ hζk hζK ?_
  rw [hi]
  intro hc
  exact hμ (eq_of_principalBlock_of_normalPComplement π hπ hlin hnil hNp hquot S
    (hconv _ hc) hφ₀)

set_option maxHeartbeats 1000000 in
-- The `p`-section expansion is elaborated under the same chains as the vanishing above.
omit [Finite κ] in
include hp hx hω e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ in
/-- **Navarro's `χ(x y) = d^x_{χ φ_0}`.**  For `χ_i ∈ Irr(B_0(G))` and `y` a `p`-regular element
of `C_G(x)` whose group has a normal `p`-complement, the defining expansion
`χ(x y) = ∑_μ d^x_{χ μ} μ(y)` has only the term `μ = φ_0`, and `φ_0(y) = 1`. -/
theorem character_mul_eq_generalizedDecompositionNumber {i : κ}
    (hi : blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG)
    {y : ↥(centralizerOf x)} (hy : IsPRegular p y) :
    (wedderburnRepresentation eG i).character (x * (y : G))
      = generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
          ((wedderburnRepresentation eG i).character)
          (fun _ _ hgh => character_eq_of_isConj _ hgh) φ₀ := by
  classical
  rw [← sum_generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
    ((wedderburnRepresentation eG i).character)
    (fun _ _ hgh => character_eq_of_isConj _ hgh) hy]
  rw [Finset.sum_eq_single φ₀
    (fun μ _ hne => by
      rw [generalizedDecompositionNumber_eq_zero_of_ne_principal hp hx hω e eG hπG hlinG hπ hlin
        hkerJ hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ hi hne, zero_mul])
    (fun h => absurd (Finset.mem_univ φ₀) h)]
  rw [irreducibleBrauerCharacter_principalBlock_eq_one hπ hlin hnil hp hω' hNp hquot S hφ₀ hy,
    map_one, mul_one]

set_option maxHeartbeats 1000000 in
-- Same cost as the (5.8) specialisation it invokes; `Fintype ↥(centralizerOf x)` is what makes
-- the induced block in that specialisation elaborate, and the section fixes it.
set_option linter.unusedFintypeInType false in
omit [Finite κ] in
include hp hx hω e hπG hlinG hkerJ hnil hζ hζk hζK hφ₀ in
/-- **Off `Irr(B_0(G))` the column `φ_0` vanishes.**  The block of `φ_0` is `b_0(C_G(x))`, which
induces `B_0(G)` by the easy half of the third main theorem, so the second main theorem kills
`d^x_{χ_i φ_0}` whenever `χ_i` is outside `B_0(G)`. -/
theorem generalizedDecompositionNumber_principalBlock_eq_zero_of_blockOfIrr_ne {i : κ}
    (hi : blockOfIrr eG hπG hlinG hnilG i ≠ principalBlock πG hπG hlinG hnilG) :
    generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
        ((wedderburnRepresentation eG i).character)
        (fun _ _ hgh => character_eq_of_isConj _ hgh) φ₀ = 0 := by
  classical
  refine generalizedDecompositionNumber_eq_zero_of_blockOfIrr_ne hp hx e eG hπG hlinG hπ hlin
    hkerJ hnil hnilG hω hω' hζ hζk hζK ?_
  rw [hφ₀, inducedBlockOfCentralizer_principalBlock π hπ hlin hnil πG hπG hlinG hnilG hp hx]
  exact fun h => hi h.symm

set_option maxHeartbeats 1000000 in
-- The `p`-section expansion is elaborated under the same chains as the results above.
omit [Finite κ] in
include hp hx hω e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ in
/-- **`χ` is constant on the `p`-singular elements**, with value `d^x_{χ φ_0}`, as soon as every
nontrivial `p`-element is conjugate to `x`.

Write `u = u_p u_{p'}`.  The `p`-part is nontrivial (that is what `p`-singular means), so
`u_p = c x c⁻¹`, and conjugating back puts `u` in the `p`-section of `x`:
`c⁻¹ u c = x (c⁻¹ u_{p'} c)` with `c⁻¹ u_{p'} c` a `p`-regular element of `C_G(x)`.  Characters
are class functions, so `character_mul_eq_generalizedDecompositionNumber` applies. -/
theorem character_eq_generalizedDecompositionNumber_of_not_isPRegular
    (hconjall : ∀ v : G, IsPElement p v → v ≠ 1 → IsConj x v) {i : κ}
    (hi : blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG)
    {u : G} (hu : ¬ IsPRegular p u) :
    (wedderburnRepresentation eG i).character u
      = generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
          ((wedderburnRepresentation eG i).character)
          (fun _ _ hgh => character_eq_of_isConj _ hgh) φ₀ := by
  classical
  have hufin : IsOfFinOrder u := isOfFinOrder_of_finite u
  have hane : pPart p u ≠ 1 := fun h => hu (isPRegular_of_pPart_eq_one hp hufin h)
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconjall (pPart p u) (isPElement_pPart hp u) hane)
  have hx' : x = c⁻¹ * pPart p u * c := by rw [← hc]; group
  have hcomm : Commute (pRegularPart p u) (pPart p u) := commute_pRegularPart_pPart u
  have hmem : c⁻¹ * pRegularPart p u * c ∈ centralizerOf x := by
    simp only [centralizerOf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    rw [hx']
    calc c⁻¹ * pPart p u * c * (c⁻¹ * pRegularPart p u * c)
        = c⁻¹ * (pPart p u * pRegularPart p u) * c := by group
      _ = c⁻¹ * (pRegularPart p u * pPart p u) * c := by rw [hcomm.eq]
      _ = c⁻¹ * pRegularPart p u * c * (c⁻¹ * pPart p u * c) := by group
  have hyreg : IsPRegular p (⟨c⁻¹ * pRegularPart p u * c, hmem⟩ : ↥(centralizerOf x)) := by
    refine isPRegular_coe_iff.mp ?_
    have h := (isPRegular_pRegularPart hp hufin).conj c⁻¹
    rwa [inv_inv] at h
  have hconjeq : IsConj u
      (x * ((⟨c⁻¹ * pRegularPart p u * c, hmem⟩ : ↥(centralizerOf x)) : G)) := by
    refine isConj_iff.mpr ⟨c⁻¹, ?_⟩
    change c⁻¹ * u * c⁻¹⁻¹ = x * (c⁻¹ * pRegularPart p u * c)
    rw [hx']
    calc c⁻¹ * u * c⁻¹⁻¹
        = c⁻¹ * (pPart p u * pRegularPart p u) * c := by
          rw [pPart_mul_pRegularPart hp hufin]; group
      _ = c⁻¹ * pPart p u * c * (c⁻¹ * pRegularPart p u * c) := by group
  rw [character_eq_of_isConj _ hconjeq,
    character_mul_eq_generalizedDecompositionNumber hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil
      hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ hi hyreg]

set_option maxHeartbeats 1000000 in
-- Same chains as the constancy statement it contraposes.
omit [Finite κ] in
include hp hx hω e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ in
/-- **`d^x_{χ φ_0} ≠ 0` for `χ ∈ Irr(B_0)`.**  Otherwise `χ` vanishes on every `p`-singular
element by the previous result, and Navarro (3.18)
(`not_dvd_card_of_character_eq_zero_of_pSingular`) makes `p ∤ |G|` — impossible, since `x` is a
nontrivial `p`-element. -/
theorem generalizedDecompositionNumber_ne_zero_of_blockOfIrr_principal
    (hconjall : ∀ v : G, IsPElement p v → v ≠ 1 → IsConj x v) (hx1 : x ≠ 1) {i : κ}
    (hi : blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG) :
    generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
        ((wedderburnRepresentation eG i).character)
        (fun _ _ hgh => character_eq_of_isConj _ hgh) φ₀ ≠ 0 := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  intro hzero
  refine not_dvd_card_of_character_eq_zero_of_pSingular eG hπG hlinG hnilG i hi
    (fun u hu => by
      rw [character_eq_generalizedDecompositionNumber_of_not_isPRegular hp hx hω e eG hπG hlinG
        hπ hlin hkerJ hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ hconjall hi hu, hzero]) ?_
  -- `x` is a nontrivial `p`-element, so `p` divides `|G|`
  obtain ⟨k, hk⟩ := id hx
  have hord : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.mp (by simpa using hk))
  exact dvd_trans (by rw [hk]; exact dvd_pow_self p hk0) hord

end Section

end OddOrder.RepresentationTheory.Modular
