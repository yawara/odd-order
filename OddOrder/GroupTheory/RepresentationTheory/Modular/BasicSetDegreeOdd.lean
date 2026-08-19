/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BrauerSuzukiEndgame
import OddOrder.GroupTheory.RepresentationTheory.Modular.IntegralBasicSetMatrix

/-!
# The degrees in the basic set of Navarro (7.4) are odd integers

The endgame of Brauer–Suzuki uses the expansion
`χ(t) = D^t_0 + ψ_1(1) D^t_1 + ψ_2(1) D^t_2` only through the *parity* of `ψ_1(1)`, `ψ_2(1)`
(`OddOrder.Algebra.two_dvd_sum_of_odd_degrees`).  This file produces those two degrees as odd
integers.

A member of the basic set is `ψ_j = ε_j χ_j⁰` with `ε_j = χ_j(t) = ±1` (Navarro (7.2)), so
`ψ_j(1) = ε_j χ_j(1)`; and `χ_j(1) ≡ ε_j mod 4` (`card_modEq_character_involution`, the count of
the fixed points of a Klein four subgroup) makes `χ_j(1)` odd.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_odd_intCast_principalBasicSet`

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (7.2), (7.4), p. 141.
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule

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
  [Fintype ιG] [∀ i, Nonempty (nnG i)]
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

set_option maxHeartbeats 1000000 in
-- Navarro (7.2) is invoked twice (for the sign and for the congruence), with its whole chain.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open scoped Classical in
include hp hx hω hω' e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ ht in
/-- **`ψ_j(1)` is an odd integer** for every member `ψ_j` of the basic set of Navarro (7.4).

`ψ_j(1) = ε_j χ_j(1)` with `ε_j = ±1` (`basicSetSign`, legitimate by `ε_j² = 1`), and `χ_j(1)` is
odd because `χ_j(1) ≡ ε_j mod 4`: the fixed-point count of the Klein four subgroup `P` on the
module of `χ_j` is an integer, and `χ_j(1) + 3 ε_j = 4 dim V^P`.

This is the source of the endgame's `hs₁`, `hs₂`. -/
theorem exists_odd_intCast_principalBasicSet
    (hconjall : ∀ v : G, IsPElement p v → v ≠ 1 → IsConj t v) (ht1 : t ≠ 1)
    (hcart : cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀ = 4)
    (P : Subgroup G) [Fintype ↥P] (hPcard : Fintype.card ↥P = 4)
    (hPsing : ∀ h : ↥P, (h : G) ≠ 1 → ¬ IsPRegular p (h : G))
    {j₀ j : κ} (hjB : blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG)
    (hjne : j ≠ j₀) :
    ∃ s : ℤ, ((s : ℤ) : K) = principalBasicSet eG hπG hlinG hnilG t j₀ j 1 ∧ Odd s := by
  classical
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  -- `ε_j = ±1` as an integer
  have hεsq := character_involution_mul_self hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil hnilG hω'
    hζ hζk hζK hconv hNp hquot S hφ₀ ht hconjall ht1 hcart hjB
  have hε : ((basicSetSign eG t j : ℤ) : K) = (wedderburnRepresentation eG j).character t :=
    intCast_basicSetSign eG hεsq
  have hsign : basicSetSign eG t j = 1 ∨ basicSetSign eG t j = -1 := by
    rw [basicSetSign]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- `χ_j(1) = dim` and it is odd, by `χ_j(1) ≡ ε_j mod 4`
  have hone : (wedderburnRepresentation eG j).character 1 = ((Fintype.card (mG j) : ℤ) : K) := by
    rw [Representation.char_one, Module.finrank_fintype_fun_eq_card]
    push_cast
    rfl
  have hodd : Odd (Fintype.card (mG j) : ℤ) :=
    OddOrder.Algebra.odd_of_modEq_four
      (card_modEq_character_involution hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil hnilG hω' hζ
        hζk hζK hconv hNp hquot S hφ₀ hconjall hjB P hPcard hPsing hε.symm) hsign
  refine ⟨basicSetSign eG t j * (Fintype.card (mG j) : ℤ), ?_,
    OddOrder.Algebra.odd_mul_of_eq_one_or_neg_one hsign hodd⟩
  rw [principalBasicSet, if_pos ⟨hjB, hjne⟩, Int.cast_mul, hε, hone]

end OddOrder.RepresentationTheory.Modular
