/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.GeneralizedDecompositionInvolution
import OddOrder.GroupTheory.RepresentationTheory.Modular.QuotientBasicSetCartan

/-!
# The columns `D^t_j` of the "analysis at `t`": Navarro p. 141, equation (3)

Two chains meet here.

* Navarro (7.5)(c) at an involution
  (`sum_mul_basicDecompositionNumber_eq_cartanMatrix_of_involution`) says that the pairing of two
  basic-set columns at `t` is `Uᵗ C_{C_G(t)} U`.
* Navarro (7.4) + (7.6) (`sum_intBasicSetMatrix_mul_cartanMatrix_quotientPi`) say that for the
  basic set of the principal block of `C_G(t)/⟨t⟩`, that matrix is `|⟨t⟩| (1 + δ) = 2(1 + δ)`.

Composing them is Navarro's equation (3),

`(D^t_i, D^t_j) = 2 (1 + δ_ij)`,

the pairing table the endgame consumes as `hbb`, `hcc`, `hdd`, `hbc`, `hbd`, `hcd`
(`OddOrder.RepresentationTheory.Modular.exists_proper_normal_of_columns`).

The two sides fit because the Cartan matrix appearing on the right of (7.5)(c) is *literally* the
one on the left of (7.4)+(7.6): both are `cartanMatrix … e` for the ordinary splitting `e` of
`C_G(t)`, with the `IBr` index type shared through `quotientPi`.

## Main results

* `OddOrder.RepresentationTheory.Modular.sum_mul_basicDecompositionNumber_quotientPi` — equation
  (3) over `K`

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (7.4), (7.5), (7.6), p. 141.
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule

section AnalysisAtInvolution

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsIntegrallyClosed 𝒪]
  [IsAlgClosed (FractionRing 𝒪)]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
  [Fact p.Prime] [CharP (ResidueField 𝒪) p]
-- the ambient group `G` and its involution `x`; the columns are indexed by `Irr(G)`
variable {G : Type*} [Group G] [Finite G] {x : G} [Invertible (Nat.card G : K)]
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
-- `Irr(G)`
variable {J : Type*} [Fintype J] {mG : J → Type*} [∀ j, Fintype (mG j)]
  [∀ j, DecidableEq (mG j)] [∀ j, Nonempty (mG j)]
-- the datum of `C_G(x)`, shared by the two chains
variable (hp : p.Prime)
  {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
  {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
    ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
    π (c • a) = c • π a)
  (hkerJ : RingHom.ker π
    = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))
  (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
  (eG : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (mG j) (mG j) K)
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
  (hconv : ∀ b : Block πC hπC hlinC,
    inducedBlockOfCentralizer yb πC hπC hlinC (quotientPi π hπ hlin hN).toRingHom
        (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN) hnilQ hp hyb b
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ →
    b = principalBlock πC hπC hlinC hnilC)
  {M : Subgroup ↥(centralizerOf yb)} [M.Normal] (hMp : ¬ p ∣ Nat.card ↥M)
  (hquot : IsPGroup p (↥(centralizerOf yb) ⧸ M)) (S : Sylow p ↥(centralizerOf yb))
  {φ₀ : ιC} (hφ₀ : Quotient.mk (blockSetoid πC hπC hlinC) φ₀
    = principalBlock πC hπC hlinC hnilC)
  (hyb2 : yb * yb = 1)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open scoped Classical in
include hp hω hω' hkerJ e eG eQ hN hcent hϖ hϖ' hyb hωC hω'C eC hkerJC hnilC hζ hζk hζK hconv
  hMp hquot S hφ₀ hyb2 in
/-- **Navarro p. 141, equation (3): `(D^t_i, D^t_j) = 2 (1 + δ_ij)`.**

The left side is the pairing of two basic-set columns of the generalized decomposition matrix of
`G` at the involution `x`; (7.5)(c) turns it into `Uᵗ C_{C_G(x)} U`, and (7.4) composed with (7.6)
evaluates that as `|N| (1 + δ)`.  For `N = ⟨x⟩` the factor is `2`. -/
theorem sum_mul_basicDecompositionNumber_quotientPi {A : ι → κ → ℤ} (ht : x * x = 1)
    (hx : IsPElement p x)
    (ha0 : ∀ (ν : ι) (l : κ), blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
        (quotientPi_smul π hπ hlin hN) hnilQ l
      ≠ Quotient.mk (blockSetoid (quotientPi π hπ hlin hN).toRingHom
          (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)) ν → A ν l = 0)
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
    {j₀ : κ} (hj₀ : blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) hnilQ j₀
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ)
    {j : κ} (hjB : blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) hnilQ j
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ)
    (hjne : j ≠ j₀)
    {k : κ} (hkB : blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) hnilQ k
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ)
    (hkne : k ≠ j₀) :
    (∑ i : J, basicDecompositionNumber
        (generalizedDecompositionNumber x hp hω' hπ hlin hkerJ
          ((wedderburnRepresentation eG i).character)
          (fun _ _ h => character_eq_of_isConj _ h))
        (fun μ l => ((intBasicSetMatrix eQ A yb j₀ μ l : ℤ) : K)) j *
      basicDecompositionNumber
        (generalizedDecompositionNumber x hp hω' hπ hlin hkerJ
          ((wedderburnRepresentation eG i).character)
          (fun _ _ h => character_eq_of_isConj _ h))
        (fun μ l => ((intBasicSetMatrix eQ A yb j₀ μ l : ℤ) : K)) k)
      = (Nat.card ↥N : K) * (1 + if j = k then 1 else 0) := by
  have h1 := sum_mul_basicDecompositionNumber_eq_cartanMatrix_of_involution hp hω hω' hπ hlin hkerJ
    e eG (fun μ l => ((intBasicSetMatrix eQ A yb j₀ μ l : ℤ) : K)) ht hx j k
  have h2 := sum_intBasicSetMatrix_mul_cartanMatrix_quotientPi hp hπ hlin hkerJ e eQ hN hcent hω
    hω' hϖ hϖ' hyb hωC hω'C eC hπC hlinC hkerJC hnilC hnilQ hζ hζk hζK hconv hMp hquot S hφ₀ hyb2
    ha0 hasum hconjall hyb1 hcart hj₀ hjB hjne hkB hkne
  exact h1.trans h2

end AnalysisAtInvolution

end OddOrder.RepresentationTheory.Modular
