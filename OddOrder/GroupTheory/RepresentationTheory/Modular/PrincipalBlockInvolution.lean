/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.SumSquaresFour
import OddOrder.GroupTheory.RepresentationTheory.CharacterInvolution
import OddOrder.GroupTheory.RepresentationTheory.Modular.GeneralizedDecompositionInvolution
import OddOrder.GroupTheory.RepresentationTheory.Modular.SecondMainPrincipalBlock

/-!
# Navarro (7.2), character side: `Irr(B_0) = {1_G, χ_1, χ_2, χ_3}` and `χ_i(t) = ±1`

Let `t` be an involution such that every nontrivial `2`-element of `G` is conjugate to `t` — the
situation of Navarro (7.2), where the Sylow `2`-subgroup is a Klein four group and `G` has a
single class of involutions — and suppose `C = C_G(t)` has a normal `2`-complement.  Then

`∑_{χ ∈ Irr(B_0)} χ(t)² = c_{φ_0 φ_0} = |C|_2 = 4`.

The left-hand side is (5.13.b) at an involution
(`sum_sq_generalizedDecompositionNumber_of_involution`) with the columns outside `Irr(B_0)`
removed (`generalizedDecompositionNumber_principalBlock_eq_zero_of_blockOfIrr_ne`) and
`d^t_{χ φ_0}` read as `χ(t)` (`character_mul_eq_generalizedDecompositionNumber` at `y = 1`).

Every `χ(t)` is a rational integer (`exists_intCast_character_of_mul_self_eq_one`) and nonzero
(`generalizedDecompositionNumber_ne_zero_of_blockOfIrr_principal`), and weak block orthogonality
`∑_{χ ∈ Irr(B_0)} χ(1) χ(t) = 0` forbids `|Irr(B_0)| = 1`.  `OddOrder.Algebra.SumSquaresFour`
then forces four characters, each with `χ(t) = ±1`.

## Main results

* `OddOrder.RepresentationTheory.Modular.sum_sq_character_involution_eq_cartanMatrix`
* `OddOrder.RepresentationTheory.Modular.nontrivial_blockOfIrr_principal`
* `OddOrder.RepresentationTheory.Modular.card_blockOfIrr_principal_eq_four_and_character_involution`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule
open OddOrder.RepresentationTheory

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
  [Fintype κ] [∀ i, Nonempty (mG i)]
variable {ιG : Type*} {nnG : ιG → Type*} [∀ i, Fintype (nnG i)] [∀ i, DecidableEq (nnG i)]
  [Finite ιG] [∀ i, Nonempty (nnG i)]
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

/-! ### `∑_{χ ∈ Irr(B_0)} χ(t)² = c_{φ_0 φ_0}` -/

set_option maxHeartbeats 1000000 in
-- The three inputs (the involution form of (5.13.b), the vanishing off `Irr(B_0)` and the
-- `p`-section value) are all elaborated under the full modular-datum chain.
open scoped Classical in
include hp hx hω e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ ht in
/-- **`∑_{χ ∈ Irr(B_0)} χ(t)² = c_{φ_0 φ_0}`.**  (5.13.b) at the involution `t` gives the sum of
squares of the whole column `φ_0`; the entries outside `Irr(B_0)` vanish, and inside `Irr(B_0)`
the entry is `χ(t)`. -/
theorem sum_sq_character_involution_eq_cartanMatrix :
    (∑ j ∈ Finset.univ.filter
        (fun j => blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG),
      ((wedderburnRepresentation eG j).character t) ^ 2)
      = (cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀ : K) := by
  classical
  have hres : (∑ j ∈ Finset.univ.filter
        (fun j => blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG),
      (generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) t hp hω' hπ hlin hkerJ
        ((wedderburnRepresentation eG j).character)
        (fun _ _ hgh => character_eq_of_isConj _ hgh) φ₀) ^ 2)
      = ∑ j : κ, (generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) t hp hω' hπ hlin hkerJ
        ((wedderburnRepresentation eG j).character)
        (fun _ _ hgh => character_eq_of_isConj _ hgh) φ₀) ^ 2 := by
    refine Finset.sum_subset (Finset.filter_subset _ Finset.univ) fun j _ hj => ?_
    rw [generalizedDecompositionNumber_principalBlock_eq_zero_of_blockOfIrr_ne hp hx hω e eG
      hπG hlinG hπ hlin hkerJ hnil hnilG hω' hζ hζk hζK hφ₀
      (fun hcon => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)), sq, mul_zero]
  rw [← sum_sq_generalizedDecompositionNumber_of_involution hp hω hω' hπ hlin hkerJ e eG ht hx φ₀,
    ← hres]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hi := (Finset.mem_filter.mp hj).2
  have hval := character_mul_eq_generalizedDecompositionNumber hp hx hω e eG hπG hlinG hπ hlin
    hkerJ hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ hi
    (y := (1 : ↥(centralizerOf t))) (isPRegular_one hp)
  rw [show ((1 : ↥(centralizerOf t)) : G) = 1 from rfl, mul_one] at hval
  rw [hval]

/-! ### The arithmetic conclusion -/

set_option maxHeartbeats 1000000 in
-- Same chain as above; the weak-orthogonality hypothesis is read on the same filtered sum.
-- `Fintype ι` / `Fintype ι'` are what make the generalized decomposition numbers and the
-- splitting of `C_G(t)` elaborate; the section fixes them.
set_option linter.unusedFintypeInType false in
omit [Invertible (Nat.card G : K)] ht in
open scoped Classical in
include hp hx hω hω' e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ in
/-- **`Irr(B_0)` has more than one element.**  Weak block orthogonality
`∑_{χ ∈ Irr(B_0)} χ(1) χ(t) = 0` (Navarro (5.11) at `h = 1`) would otherwise read
`χ(1) χ(t) = 0` for the unique `χ ∈ Irr(B_0)`, forcing `χ(t) = 0`. -/
theorem nontrivial_blockOfIrr_principal
    (hconjall : ∀ v : G, IsPElement p v → v ≠ 1 → IsConj t v) (ht1 : t ≠ 1)
    (hweak : (∑ j ∈ Finset.univ.filter
        (fun j => blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG),
      (wedderburnRepresentation eG j).character 1 *
        (wedderburnRepresentation eG j).character t) = 0)
    {j₀ : κ} (hj₀ : blockOfIrr eG hπG hlinG hnilG j₀ = principalBlock πG hπG hlinG hnilG) :
    ∃ j₁, blockOfIrr eG hπG hlinG hnilG j₁ = principalBlock πG hπG hlinG hnilG ∧ j₁ ≠ j₀ := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  by_contra hcon
  push Not at hcon
  -- the filtered set is `{j₀}`
  have hfil : (Finset.univ.filter
      (fun j => blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG))
      = {j₀} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₀⟩, fun j hj => ?_⟩
    exact hcon j (Finset.mem_filter.mp hj).2
  rw [hfil, Finset.sum_singleton] at hweak
  -- `χ(1) ≠ 0`
  have hone : (wedderburnRepresentation eG j₀).character 1 = (Fintype.card (mG j₀) : K) := by
    rw [Representation.char_one, Module.finrank_fintype_fun_eq_card]
  have hone0 : (wedderburnRepresentation eG j₀).character 1 ≠ 0 := by
    rw [hone]; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- so `χ(t) = 0`, contradicting the nonvanishing of the generalized decomposition number
  have hzero := (mul_eq_zero.mp hweak).resolve_left hone0
  refine generalizedDecompositionNumber_ne_zero_of_blockOfIrr_principal hp hx hω e eG hπG hlinG
    hπ hlin hkerJ hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ hconjall ht1 hj₀ ?_
  have hval := character_mul_eq_generalizedDecompositionNumber hp hx hω e eG hπG hlinG hπ hlin
    hkerJ hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ hj₀
    (y := (1 : ↥(centralizerOf t))) (isPRegular_one hp)
  rw [show ((1 : ↥(centralizerOf t)) : G) = 1 from rfl, mul_one] at hval
  rw [← hval, hzero]

set_option maxHeartbeats 1000000 in
-- The integer chosen for each `χ(t)` is threaded through the same modular-datum chain.
open scoped Classical in
include hp hx hω hω' e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ ht in
/-- **Navarro (7.2), character side.**  `|Irr(B_0)| = 4` and `χ(t) = ±1` for every
`χ ∈ Irr(B_0)`.

`∑_{χ ∈ Irr(B_0)} χ(t)² = c_{φ_0 φ_0} = 4` with every `χ(t)` a nonzero rational integer, and
`|Irr(B_0)| ≠ 1` by weak block orthogonality; `OddOrder.Algebra.SumSquaresFour` closes it. -/
theorem card_blockOfIrr_principal_eq_four_and_character_involution
    (hconjall : ∀ v : G, IsPElement p v → v ≠ 1 → IsConj t v) (ht1 : t ≠ 1)
    (hweak : (∑ j ∈ Finset.univ.filter
        (fun j => blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG),
      (wedderburnRepresentation eG j).character 1 *
        (wedderburnRepresentation eG j).character t) = 0)
    (hcart : cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀ = 4) :
    (Finset.univ.filter
        (fun j => blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG)).card = 4
      ∧ ∀ j : κ, blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG →
          (wedderburnRepresentation eG j).character t = 1
            ∨ (wedderburnRepresentation eG j).character t = -1 := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  set P : κ → Prop :=
    fun j => blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG with hP
  have hmem : ∀ j : κ, j ∈ Finset.univ.filter P ↔ P j := fun j =>
    ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  -- the integer value of `χ(t)`
  obtain ⟨a, hav⟩ : ∃ a : κ → ℤ,
      ∀ j : κ, (wedderburnRepresentation eG j).character t = ((a j : ℤ) : K) := by
    choose a ha using fun j : κ =>
      exists_intCast_character_of_mul_self_eq_one (wedderburnRepresentation eG j) h2 ht
    exact ⟨a, ha⟩
  -- the sum of squares is `4`, over `ℤ`
  have hsumZ : (∑ j : Subtype P, a (j : κ) ^ 2) = 4 := by
    have hK : (∑ j ∈ Finset.univ.filter P, ((a j : ℤ) : K) ^ 2) = ((4 : ℤ) : K) := by
      rw [Finset.sum_congr rfl fun j _ => by rw [← hav j],
        sum_sq_character_involution_eq_cartanMatrix hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil
          hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ ht, hcart]
      norm_num
    rw [← Finset.sum_subtype (Finset.univ.filter P) hmem (fun j => a j ^ 2)]
    have : (((∑ j ∈ Finset.univ.filter P, a j ^ 2 : ℤ)) : K) = ((4 : ℤ) : K) := by
      push_cast
      push_cast at hK
      exact hK
    exact_mod_cast this
  -- every term is nonzero
  have hane : ∀ j : Subtype P, a (j : κ) ≠ 0 := by
    intro j hzero
    refine generalizedDecompositionNumber_ne_zero_of_blockOfIrr_principal hp hx hω e eG hπG hlinG
      hπ hlin hkerJ hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ hconjall ht1 j.2 ?_
    have hval := character_mul_eq_generalizedDecompositionNumber hp hx hω e eG hπG hlinG hπ hlin
      hkerJ hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ j.2
      (y := (1 : ↥(centralizerOf t))) (isPRegular_one hp)
    rw [show ((1 : ↥(centralizerOf t)) : G) = 1 from rfl, mul_one] at hval
    rw [← hval, hav (j : κ), hzero, Int.cast_zero]
  -- there are at least two of them
  haveI : Nontrivial (Subtype P) := by
    have hne : (Finset.univ.filter P).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [← Finset.sum_subtype (Finset.univ.filter P) hmem (fun j => a j ^ 2), hemp,
        Finset.sum_empty] at hsumZ
      exact absurd hsumZ (by norm_num)
    obtain ⟨j₀, hj₀⟩ := hne
    obtain ⟨j₁, hj₁, hne'⟩ := nontrivial_blockOfIrr_principal hp hx hω e eG hπG hlinG hπ hlin
      hkerJ hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ hconjall ht1 hweak
      ((hmem j₀).mp hj₀)
    exact ⟨⟨⟨j₁, hj₁⟩, ⟨j₀, (hmem j₀).mp hj₀⟩, fun h => hne' (congrArg Subtype.val h)⟩⟩
  refine ⟨?_, fun j hj => ?_⟩
  · rw [← Fintype.card_subtype]
    exact OddOrder.Algebra.card_eq_four_of_sum_sq_eq_four hsumZ hane
  · rcases OddOrder.Algebra.eq_one_or_neg_one_of_sum_sq_eq_four hsumZ hane ⟨j, hj⟩ with h | h
    · left; rw [hav j, h, Int.cast_one]
    · right; rw [hav j, h]; norm_num

end OddOrder.RepresentationTheory.Modular
