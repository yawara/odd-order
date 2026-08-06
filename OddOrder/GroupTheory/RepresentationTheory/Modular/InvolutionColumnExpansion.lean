/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BasicSetTriple
import OddOrder.GroupTheory.RepresentationTheory.Modular.ColumnsAtInvolution
import OddOrder.GroupTheory.RepresentationTheory.Modular.QuotientBlockBijection
import OddOrder.GroupTheory.RepresentationTheory.Modular.SupportOfGeneralizedDecomposition
import OddOrder.GroupTheory.RepresentationTheory.Modular.TrivialCharacterBasicSet

/-!
# `χ(t) = D^t_0 + ψ_1(1) D^t_1 + ψ_2(1) D^t_2` — Navarro p. 141 at `u = 1`

This is the hypothesis `hT` of
`OddOrder.RepresentationTheory.Modular.exists_proper_normal_of_columns`, assembled from the four
pieces that were built for it:

* the display on p. 141 collapses to three terms because the basic set of (7.4) has three members
  (`basicDecompositionNumber_add_add_eq_character`);
* the basic set of `C_G(t)/⟨t⟩`, pulled back, expresses `IBr(C_G(t))` on the principal block
  (`algebraMap_irreducibleBrauerCharacter_eq_sum_intBasicSetMatrix`) — this supplies `hu`;
* the column `d^t_{χ ·}` of `χ ∈ Irr(B_0(G))` is supported there
  (`generalizedDecompositionNumber_eq_zero_of_quotient_ne` through Navarro (7.6),
  `mk_eq_principalBlock_quotientPi_of_mem`) — this supplies `hd`;
* the member of the basic set coming from the trivial character is the constant `1`
  (`principalBasicSet_eq_one_of_trivial`) — this is why the first term has no coefficient.

Evaluating at `u = 1` is legitimate because `1` is `p`-regular, and `x * 1 = x`.

## Main results

* `OddOrder.RepresentationTheory.Modular.character_eq_add_add_basicDecompositionNumber`

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (7.4), (7.5), (7.6), p. 141.
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule

section ThreeTermExpansion

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsIntegrallyClosed 𝒪]
  [IsAlgClosed (FractionRing 𝒪)]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
  [Fact p.Prime] [CharP (ResidueField 𝒪) p]
-- the ambient group `G` and its involution `x`; the columns are indexed by `Irr(G)`
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] {x : G} [Invertible (Nat.card G : K)]
  [Fintype ↥(centralizerOf x)] [Invertible (Nat.card ↥(centralizerOf x) : K)]
-- the central subgroup `⟨x⟩ ⊴ C_G(x)` and the quotient
variable {N : Subgroup ↥(centralizerOf x)} [N.Normal] [Fintype (↥(centralizerOf x) ⧸ N)]
  [DecidableEq (ConjClasses (↥(centralizerOf x) ⧸ N))]
  [Fintype (ConjClasses (↥(centralizerOf x) ⧸ N))]
  [Invertible (Nat.card (↥(centralizerOf x) ⧸ N) : K)]
-- the involution `ȳ` of `C_G(x)/⟨x⟩` and its centraliser there
variable {yb : ↥(centralizerOf x) ⧸ N} [Fintype ↥(centralizerOf yb)]
-- `IBr(C_G(x)) = IBr(C_G(x)/⟨x⟩)`
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [DecidableEq ι] [∀ i, Nonempty (nn i)]
-- `Irr(C_G(x))`
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [Fintype ι'] [∀ i, Nonempty (m i)]
-- `Irr(C_G(x)/⟨x⟩)`, the index of the basic set
variable {κ : Type*} {mQ : κ → Type*} [∀ i, Fintype (mQ i)] [∀ i, DecidableEq (mQ i)]
  [Fintype κ] [DecidableEq κ] [∀ i, Nonempty (mQ i)]
-- `IBr(C_{C_G(x)/⟨x⟩}(ȳ))` and `Irr` of the same group
variable {ιC : Type*} {nnC : ιC → Type*} [∀ i, Fintype (nnC i)] [∀ i, DecidableEq (nnC i)]
  [Fintype ιC] [∀ i, Nonempty (nnC i)]
variable {ι'C : Type*} {mC : ι'C → Type*} [∀ i, Fintype (mC i)] [∀ i, DecidableEq (mC i)]
  [Fintype ι'C] [∀ i, Nonempty (mC i)]
-- `Irr(G)` and `IBr(G)`
variable {J : Type*} [Fintype J] {mG : J → Type*} [∀ j, Fintype (mG j)]
  [∀ j, DecidableEq (mG j)] [∀ j, Nonempty (mG j)]
variable {ιG : Type*} {nnG : ιG → Type*} [∀ i, Fintype (nnG i)] [∀ i, DecidableEq (nnG i)]
  [Fintype ιG] [∀ i, Nonempty (nnG i)]
-- the datum of `C_G(x)`, shared by the two chains
variable (hp : p.Prime) (hx : IsPElement p x)
  {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
  {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
    ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
    π (c • a) = c • π a)
  (hkerJ : RingHom.ker π
    = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))
  (hnilH : ∀ z : Subalgebra.center (ResidueField 𝒪)
      (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
  (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
-- the datum of `G`
variable (eG : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (mG j) (mG j) K)
  {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
-- the datum of the quotient `C_G(x)/⟨x⟩`
variable (eQ : MonoidAlgebra K (↥(centralizerOf x) ⧸ N) ≃ₐ[K] ∀ j, Matrix (mQ j) (mQ j) K)
  (hN : IsPGroup p ↥N)
  (hcent : ∀ z : ↥(centralizerOf x), IsPRegular p z → ∀ w ∈ N, Commute z w)
  {ϖ : 𝒪} (hϖ : IsPrimitiveRoot ϖ (pRegularExponent p (↥(centralizerOf x) ⧸ N)))
  {ϖ' : ResidueField 𝒪} (hϖ' : IsPrimitiveRoot ϖ' (pRegularExponent p (↥(centralizerOf x) ⧸ N)))
-- the (7.2) datum of `C_G(x)/⟨x⟩` at its involution `ȳ`
variable (hyb : IsPElement p yb)
  {ωC : 𝒪} (hωC : IsPrimitiveRoot ωC (pRegularExponent p ↥(centralizerOf yb)))
  {ω'C : ResidueField 𝒪} (hω'C : IsPrimitiveRoot ω'C (pRegularExponent p ↥(centralizerOf yb)))
  (eC : MonoidAlgebra K ↥(centralizerOf yb) ≃ₐ[K] ∀ i, Matrix (mC i) (mC i) K)
  {πC : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf yb) →+*
    ∀ j, Matrix (nnC j) (nnC j) (ResidueField 𝒪)}
  (hπC : Function.Surjective πC)
  (hlinC : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf yb)),
    πC (c • a) = c • πC a)
  (hkerJC : RingHom.ker πC
    = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf yb)))
  (hnilC : ∀ z : Subalgebra.center (ResidueField 𝒪)
      (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf yb)),
    blockCharacterPi πC hπC hlinC z = 0 → IsNilpotent z)
  (hnilQ : ∀ z : Subalgebra.center (ResidueField 𝒪)
      (MonoidAlgebra (ResidueField 𝒪) (↥(centralizerOf x) ⧸ N)),
    blockCharacterPi (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) z = 0 → IsNilpotent z)
  {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
  (hconvC : ∀ b : Block πC hπC hlinC,
    inducedBlockOfCentralizer yb πC hπC hlinC (quotientPi π hπ hlin hN).toRingHom
        (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN) hnilQ hp hyb b
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ →
    b = principalBlock πC hπC hlinC hnilC)
  (hconvG : ∀ b : Block π hπ hlin,
    inducedBlockOfCentralizer x π hπ hlin πG hπG hlinG hnilG hp hx b
        = principalBlock πG hπG hlinG hnilG →
      b = principalBlock π hπ hlin hnilH)
  {M : Subgroup ↥(centralizerOf yb)} [M.Normal] (hMp : ¬ p ∣ Nat.card ↥M)
  (hquot : IsPGroup p (↥(centralizerOf yb) ⧸ M)) (Syl : Sylow p ↥(centralizerOf yb))
  {φ₀ : ιC} (hφ₀ : Quotient.mk (blockSetoid πC hπC hlinC) φ₀
    = principalBlock πC hπC hlinC hnilC)
  (hyb2 : yb * yb = 1)

set_option maxHeartbeats 1600000 in
-- The three chains (the display, the pull-back of the basic set, the second main theorem) meet.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
omit [Invertible (Nat.card G : K)] [DecidableEq ι] [Fintype J] in
open scoped Classical in
include hp hx hω hω' hkerJ hnilH e eG hπG hlinG hnilG eQ hN hcent hϖ hϖ' hyb hωC hω'C eC hkerJC
  hnilC hnilQ hζ hζk hζK hconvC hconvG hMp hquot Syl hφ₀ hyb2 in
/-- **Navarro p. 141 at `u = 1`**: `χ(t) = D^t_0 + ψ_1(1) D^t_1 + ψ_2(1) D^t_2` for
`χ ∈ Irr(B_0(G))`.

This is `hT` of `exists_proper_normal_of_columns`.  The first coefficient is absent because the
member of the basic set indexed by the trivial character of `C_G(t)/⟨t⟩` *is* the constant
function `1` (`principalBasicSet_eq_one_of_trivial`), so `ψ_0(1) = 1`.

The other two coefficients are `ψ_i(1) = ε_i χ_i(1)`, odd by Navarro (7.2)
(`OddOrder.Algebra.odd_mul_of_eq_one_or_neg_one` on top of `card_modEq_character_involution`);
that is what the endgame consumes as `hs₁`, `hs₂`. -/
theorem character_eq_add_add_basicDecompositionNumber {A : ι → κ → ℤ}
    (hasum : ∀ (ν : ι) {z : ↥(centralizerOf x) ⧸ N}, IsPRegular p z →
      (∑ l ∈ Finset.univ.filter (fun l => blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ l
          = Quotient.mk (blockSetoid (quotientPi π hπ hlin hN).toRingHom
              (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)) ν),
        (A ν l : K) * algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) eQ l z))
        = algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪)
            (quotientPi π hπ hlin hN).toRingHom ν z))
    (hconjall : ∀ v : ↥(centralizerOf x) ⧸ N, IsPElement p v → v ≠ 1 → IsConj yb v)
    (hyb1 : yb ≠ 1)
    (hcart : cartanMatrix (𝒪 := 𝒪) (nn := nnC) hp hωC hω'C hπC hlinC hkerJC eC φ₀ φ₀ = 4)
    {j₀ l₀ ψ₁ ψ₂ : κ}
    (hj₀ : blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) hnilQ j₀
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ)
    (hl₀B : blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) hnilQ l₀
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ)
    (hl₀ : ∀ g : ↥(centralizerOf x) ⧸ N, (wedderburnRepresentation eQ l₀).character g = 1)
    (hl₀ne : l₀ ≠ j₀)
    (henum : ∀ φ : κ, blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
        (quotientPi_smul π hπ hlin hN) hnilQ φ
        = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
            (quotientPi_smul π hπ hlin hN) hnilQ →
      φ ≠ j₀ → φ = l₀ ∨ φ = ψ₁ ∨ φ = ψ₂)
    (h01 : l₀ ≠ ψ₁) (h02 : l₀ ≠ ψ₂) (h12 : ψ₁ ≠ ψ₂)
    {i : J} (hi : blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG) :
    (wedderburnRepresentation eG i).character x
      = basicDecompositionNumber
          (generalizedDecompositionNumber x hp hω' hπ hlin hkerJ
            ((wedderburnRepresentation eG i).character)
            (fun _ _ h => character_eq_of_isConj _ h))
          (fun μ l => ((intBasicSetMatrix eQ A yb j₀ μ l : ℤ) : K)) l₀
        + principalBasicSet eQ (quotientPi_surjective π hπ hlin hN)
            (quotientPi_smul π hπ hlin hN) hnilQ yb j₀ ψ₁ 1
          * basicDecompositionNumber
              (generalizedDecompositionNumber x hp hω' hπ hlin hkerJ
                ((wedderburnRepresentation eG i).character)
                (fun _ _ h => character_eq_of_isConj _ h))
              (fun μ l => ((intBasicSetMatrix eQ A yb j₀ μ l : ℤ) : K)) ψ₁
        + principalBasicSet eQ (quotientPi_surjective π hπ hlin hN)
            (quotientPi_smul π hπ hlin hN) hnilQ yb j₀ ψ₂ 1
          * basicDecompositionNumber
              (generalizedDecompositionNumber x hp hω' hπ hlin hkerJ
                ((wedderburnRepresentation eG i).character)
                (fun _ _ h => character_eq_of_isConj _ h))
              (fun μ l => ((intBasicSetMatrix eQ A yb j₀ μ l : ℤ) : K)) ψ₂ := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  have key := basicDecompositionNumber_add_add_eq_character (𝒪 := 𝒪) (nn := nn) hp hω' hπ hlin
    hkerJ (fun μ l => ((intBasicSetMatrix eQ A yb j₀ μ l : ℤ) : K))
    (fun φ w => principalBasicSet eQ (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) hnilQ yb j₀ φ (QuotientGroup.mk w))
    ((wedderburnRepresentation eG i).character) (fun _ _ h => character_eq_of_isConj _ h)
    (P := fun ν => Quotient.mk (blockSetoid (quotientPi π hπ hlin hN).toRingHom
        (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)) ν
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ)
    (fun μ hμ => generalizedDecompositionNumber_eq_zero_of_quotient_ne hp hx e eG hπG hlinG hπ hlin
      hkerJ hnilH hnilG hω hω' hζ hζk hζK hconvG
      (fun ν hν => mk_eq_principalBlock_quotientPi_of_mem (hω := hω) (hω' := hω') (hϖ := hϖ)
        (hϖ' := hϖ') (hπ := hπ) (hlin := hlin) (hkerJ := hkerJ) (hN := hN) (hnil := hnilH)
        (hnilQ := hnilQ) (e := e) (e' := eQ) (hcent := hcent) (hμ := hν)) hi hμ)
    (fun μ hμ w hw => algebraMap_irreducibleBrauerCharacter_eq_sum_intBasicSetMatrix
      (hp := hp) (hπ := hπ) (hlin := hlin) (eQ := eQ) (hN := hN) (hyb := hyb) (hωC := hωC)
      (hω'C := hω'C) (eC := eC) (hπC := hπC) (hlinC := hlinC) (hkerJC := hkerJC) (hnilC := hnilC)
      (hnilQ := hnilQ) (hζ := hζ) (hζk := hζk) (hζK := hζK) (hconv := hconvC) (hMp := hMp)
      (hquot := hquot) (S := Syl) (hφ₀ := hφ₀) (hyb2 := hyb2) (hasum := hasum)
      (hconjall := hconjall) (hyb1 := hyb1) (hcart := hcart) (hj₀ := hj₀) (hμ := hμ) (hw := hw))
    (isPRegular_one hp)
    (B := fun φ => blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
        (quotientPi_smul π hπ hlin hN) hnilQ φ
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ)
    (fun φ hφ => by rw [principalBasicSet, if_neg hφ]) henum h01 h02 h12
  rw [show ((1 : ↥(centralizerOf x)) : G) = 1 from rfl, mul_one] at key
  rw [show (QuotientGroup.mk (1 : ↥(centralizerOf x)) : ↥(centralizerOf x) ⧸ N) = 1 from rfl,
    principalBasicSet_eq_one_of_trivial eQ (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) hnilQ hl₀B hl₀ hl₀ne 1, mul_one] at key
  rw [← key]
  ring

set_option maxHeartbeats 1000000 in
-- The second main theorem it specialises carries the whole block chain.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
omit [Invertible (Nat.card G : K)] [DecidableEq ι] [Fintype J]
  [Invertible (Nat.card ↥(centralizerOf x) : K)]
  [Invertible (Nat.card (↥(centralizerOf x) ⧸ N) : K)] [Fintype ↥(centralizerOf yb)]
  [Fintype κ] [DecidableEq κ] in
open scoped Classical in
include hp hx hω hω' hkerJ hnilH e eG hπG hlinG hnilG eQ hN hζ hζk hζK in
/-- **Off `Irr(B_0(G))` the basic-set columns at `x` vanish** — the hypothesis `hzero` of
`exists_proper_normal_of_columns`.

`U` is supported on `IBr(B_0(C_G(x)/N))`: its entries are differences `A_{μl} ε_l - A_{μj₀}
ε_{j₀}` with `l`, `j₀` in the principal block of the quotient, and `A` is block-diagonal.  So a
nonzero entry puts `μ` in `IBr(B_0(C_G(x)/N))`, hence in `IBr(B_0(C_G(x)))` by the easy half of
Navarro (7.6) (`mk_eq_principalBlock_of_quotientPi`); and there the second main theorem kills
`d^x_{χμ}` for `χ` outside `B_0(G)`. -/
theorem basicDecompositionNumber_eq_zero_of_blockOfIrr_ne {A : ι → κ → ℤ}
    (ha0 : ∀ (ν : ι) (l : κ), blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
        (quotientPi_smul π hπ hlin hN) hnilQ l
      ≠ Quotient.mk (blockSetoid (quotientPi π hπ hlin hN).toRingHom
          (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)) ν → A ν l = 0)
    {j₀ φ : κ}
    (hj₀ : blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) hnilQ j₀
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ)
    (hφ : blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) hnilQ φ
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ)
    {i : J} (hi : blockOfIrr eG hπG hlinG hnilG i ≠ principalBlock πG hπG hlinG hnilG) :
    basicDecompositionNumber
        (generalizedDecompositionNumber x hp hω' hπ hlin hkerJ
          ((wedderburnRepresentation eG i).character)
          (fun _ _ h => character_eq_of_isConj _ h))
        (fun μ l => ((intBasicSetMatrix eQ A yb j₀ μ l : ℤ) : K)) φ = 0 := by
  classical
  refine basicDecompositionNumber_eq_zero fun μ hU => ?_
  -- a nonzero entry of `U` needs a nonzero entry of `A` in the principal block of the quotient
  have hmk : Quotient.mk (blockSetoid (quotientPi π hπ hlin hN).toRingHom
      (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)) μ
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ := by
    by_cases hAφ : A μ φ = 0
    · by_cases hAj : A μ j₀ = 0
      · exact absurd (by rw [intBasicSetMatrix, hAφ, hAj, zero_mul, zero_mul, sub_zero,
          Int.cast_zero]) hU
      · have hbj : blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
            (quotientPi_smul π hπ hlin hN) hnilQ j₀
            = Quotient.mk (blockSetoid (quotientPi π hπ hlin hN).toRingHom
              (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)) μ := by
          by_contra hne
          exact hAj (ha0 μ j₀ hne)
        exact hbj.symm.trans hj₀
    · have hbφ : blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ φ
          = Quotient.mk (blockSetoid (quotientPi π hπ hlin hN).toRingHom
            (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)) μ := by
        by_contra hne
        exact hAφ (ha0 μ φ hne)
      exact hbφ.symm.trans hφ
  exact generalizedDecompositionNumber_principalBlock_eq_zero_of_blockOfIrr_ne
    (hp := hp) (hx := hx) (hω := hω) (e := e) (eG := eG) (hπG := hπG) (hlinG := hlinG)
    (hπ := hπ) (hlin := hlin) (hkerJ := hkerJ) (hnil := hnilH) (hnilG := hnilG) (hω' := hω')
    (hζ := hζ) (hζk := hζk) (hζK := hζK)
    (hφ₀ := mk_eq_principalBlock_of_quotientPi hπ hlin hN hnilH hnilQ hmk) (hi := hi)

set_option maxHeartbeats 1600000 in
-- The display, the pull-back of the basic set and the independence of `𝓑` meet here.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
omit [Invertible (Nat.card G : K)] [DecidableEq ι] [Fintype J] in
open scoped Classical in
include hp hx hω hω' hkerJ hnilH e eG hπG hlinG hnilG eQ hN hcent hϖ hϖ' hyb hωC hω'C eC hkerJC
  hnilC hnilQ hζ hζk hζK hconvC hconvG hMp hquot Syl hφ₀ hyb2 in
/-- **Navarro p. 141: `d^t_{00} = 1` and `d^t_{0j} = 0` for `j ≠ 0`** — the hypotheses `hb0`,
`hc0`, `hd0` of `exists_proper_normal_of_columns` at once.

The basic-set column of the *trivial* character of `G` expands the constant function `1`: the
display on p. 141 reads `1 = 1_G(t u) = ∑_j d^t_{1_G j} ψ_j(u)` on the `p`-regular classes.  Since
`𝓑` contains the constant function `1` and is independent there
(`eq_ite_of_sum_principalBasicSet_eq_one`), that column is `Pi.single l₀ 1`.

Every `p`-regular class of `C_G(t)/⟨t⟩` is hit by a `p`-regular element of `C_G(t)`
(`exists_isPRegular_mk_eq`), so the display covers all of them. -/
theorem basicDecompositionNumber_trivial_eq_ite {A : ι → κ → ℤ}
    (hasum : ∀ (ν : ι) {z : ↥(centralizerOf x) ⧸ N}, IsPRegular p z →
      (∑ l ∈ Finset.univ.filter (fun l => blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ l
          = Quotient.mk (blockSetoid (quotientPi π hπ hlin hN).toRingHom
              (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)) ν),
        (A ν l : K) * algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) eQ l z))
        = algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪)
            (quotientPi π hπ hlin hN).toRingHom ν z))
    (hconjall : ∀ v : ↥(centralizerOf x) ⧸ N, IsPElement p v → v ≠ 1 → IsConj yb v)
    (hyb1 : yb ≠ 1)
    (hcart : cartanMatrix (𝒪 := 𝒪) (nn := nnC) hp hωC hω'C hπC hlinC hkerJC eC φ₀ φ₀ = 4)
    {i₀ : J} (hi₀B : blockOfIrr eG hπG hlinG hnilG i₀ = principalBlock πG hπG hlinG hnilG)
    (hi₀ : ∀ g : G, (wedderburnRepresentation eG i₀).character g = 1)
    {j₀ l₀ : κ}
    (hj₀ : blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) hnilQ j₀
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ)
    (hl₀B : blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) hnilQ l₀
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ)
    (hl₀ : ∀ g : ↥(centralizerOf x) ⧸ N, (wedderburnRepresentation eQ l₀).character g = 1)
    (hl₀ne : l₀ ≠ j₀)
    {j : κ} (hjB : blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) hnilQ j
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ)
    (hjne : j ≠ j₀) :
    basicDecompositionNumber
        (generalizedDecompositionNumber x hp hω' hπ hlin hkerJ
          ((wedderburnRepresentation eG i₀).character)
          (fun _ _ h => character_eq_of_isConj _ h))
        (fun μ l => ((intBasicSetMatrix eQ A yb j₀ μ l : ℤ) : K)) j
      = if j = l₀ then 1 else 0 := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  refine eq_ite_of_sum_principalBasicSet_eq_one (hp := hp) (hx := hyb) (hω := hωC) (e := eC)
    (eG := eQ) (hπG := quotientPi_surjective π hπ hlin hN)
    (hlinG := quotientPi_smul π hπ hlin hN) (hπ := hπC) (hlin := hlinC) (hkerJ := hkerJC)
    (hnil := hnilC) (hnilG := hnilQ) (hω' := hω'C) (hζ := hζ) (hζk := hζk) (hζK := hζK)
    (hconv := hconvC) (hNp := hMp) (hquot := hquot) (S := Syl) (hφ₀ := hφ₀)
    (hconjall := hconjall) (ht1 := hyb1) (hcart := hcart) (ht := hyb2) (hj₀ := hj₀)
    (hone := ?_) (hi₀B := hl₀B) (hi₀ := hl₀) (hi₀ne := hl₀ne) (hjB := hjB) (hjne := hjne)
  intro g hg
  obtain ⟨w, hw, rfl⟩ := exists_isPRegular_mk_eq (N := N) hp hg
  rw [← hi₀ (x * (w : G))]
  exact sum_basicDecompositionNumber_eq_character_of_support (𝒪 := 𝒪) (nn := nn) hp hω' hπ hlin
    hkerJ
    (fun μ l => ((intBasicSetMatrix eQ A yb j₀ μ l : ℤ) : K))
    (fun φ v => principalBasicSet eQ (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) hnilQ yb j₀ φ (QuotientGroup.mk v))
    ((wedderburnRepresentation eG i₀).character) (fun _ _ h => character_eq_of_isConj _ h)
    (fun μ hμ => generalizedDecompositionNumber_eq_zero_of_quotient_ne hp hx e eG hπG hlinG hπ hlin
      hkerJ hnilH hnilG hω hω' hζ hζk hζK hconvG
      (fun ν hν => mk_eq_principalBlock_quotientPi_of_mem (hω := hω) (hω' := hω') (hϖ := hϖ)
        (hϖ' := hϖ') (hπ := hπ) (hlin := hlin) (hkerJ := hkerJ) (hN := hN) (hnil := hnilH)
        (hnilQ := hnilQ) (e := e) (e' := eQ) (hcent := hcent) (hμ := hν)) hi₀B hμ)
    (fun μ hμ v hv => algebraMap_irreducibleBrauerCharacter_eq_sum_intBasicSetMatrix
      (hp := hp) (hπ := hπ) (hlin := hlin) (eQ := eQ) (hN := hN) (hyb := hyb) (hωC := hωC)
      (hω'C := hω'C) (eC := eC) (hπC := hπC) (hlinC := hlinC) (hkerJC := hkerJC) (hnilC := hnilC)
      (hnilQ := hnilQ) (hζ := hζ) (hζk := hζk) (hζK := hζK) (hconv := hconvC) (hMp := hMp)
      (hquot := hquot) (S := Syl) (hφ₀ := hφ₀) (hyb2 := hyb2) (hasum := hasum)
      (hconjall := hconjall) (hyb1 := hyb1) (hcart := hcart) (hj₀ := hj₀) (hμ := hμ) (hw := hv))
    hw

end ThreeTermExpansion

end OddOrder.RepresentationTheory.Modular
