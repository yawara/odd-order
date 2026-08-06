/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.IntegralBasicSetMatrix
import OddOrder.GroupTheory.RepresentationTheory.Modular.QuotientCartan

/-!
# The basic set of `G` read through a central `p`-subgroup: `C_𝓑 = |N| (1 + δ)`

Navarro's "analysis at `t`" (p. 141) uses the basic set of the principal block twice over: once on
`C_G(t)/⟨t⟩`, where the Sylow `2`-subgroup is a Klein four group so that (7.4) applies, and once
on `C_G(t)` itself, where the same basic set survives (7.6) but the Cartan invariants are doubled.

This file is that composite.  With `N ⊴ G` a `p`-subgroup centralised by the `p`-regular elements
and `G ⧸ N` in the situation of Navarro (7.2):

* (7.4) `sum_intBasicSetMatrix_mul_cartanMatrix` gives `Uᵗ C_{G/N} U = 1 + δ` over `ℤ`;
* (7.6) `sum_sum_mul_cartanMatrix_quotientPi` gives `Uᵗ C_G U = |N| · Uᵗ C_{G/N} U`.

The two compose because `quotientPi` keeps the *same* index set `ι` and the same matrix sizes for
`IBr(G)` and `IBr(G/N)` — that is the formal content of Navarro's "`IBr(B̄) = IBr(B)`" — so a
single change-of-basis matrix `U` is meaningful on both sides.

## Main results

* `OddOrder.RepresentationTheory.Modular.sum_intBasicSetMatrix_mul_cartanMatrix_quotientPi`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule

section QuotientKleinFour

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsIntegrallyClosed 𝒪]
  [IsAlgClosed (FractionRing 𝒪)]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
  [Fact p.Prime] [CharP (ResidueField 𝒪) p]
-- the group `G` and the central `p`-subgroup `N`
variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : K)]
  {N : Subgroup G} [N.Normal] [Fintype (G ⧸ N)] [DecidableEq (ConjClasses (G ⧸ N))]
  [Fintype (ConjClasses (G ⧸ N))] [Invertible (Nat.card (G ⧸ N) : K)]
-- the involution of `G ⧸ N` and its centraliser
variable {t : G ⧸ N} [Fintype ↥(centralizerOf t)]
-- `IBr(G) = IBr(G/N)`, then `Irr(G)`, `Irr(G/N)`, `IBr(C_{G/N}(t))`, `Irr(C_{G/N}(t))`
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [DecidableEq ι] [∀ i, Nonempty (nn i)]
variable {ι'' : Type*} {mQ : ι'' → Type*} [∀ i, Fintype (mQ i)] [∀ i, DecidableEq (mQ i)]
  [Fintype ι''] [∀ i, Nonempty (mQ i)]
variable {κ : Type*} {mG : κ → Type*} [∀ i, Fintype (mG i)] [∀ i, DecidableEq (mG i)]
  [Fintype κ] [DecidableEq κ] [∀ i, Nonempty (mG i)]
variable {ιC : Type*} {nnC : ιC → Type*} [∀ i, Fintype (nnC i)] [∀ i, DecidableEq (nnC i)]
  [Fintype ιC] [∀ i, Nonempty (nnC i)]
variable {ι'C : Type*} {mC : ι'C → Type*} [∀ i, Fintype (mC i)] [∀ i, DecidableEq (mC i)]
  [Fintype ι'C] [∀ i, Nonempty (mC i)]
-- the modular datum of `G`; the one on `G ⧸ N` is *induced* from it (Navarro (7.6))
variable (hp : p.Prime)
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (eG : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (mQ j) (mQ j) K)
  (eQ : MonoidAlgebra K (G ⧸ N) ≃ₐ[K] ∀ j, Matrix (mG j) (mG j) K)
  (hN : IsPGroup p ↥N) (hcent : ∀ x : G, IsPRegular p x → ∀ z ∈ N, Commute x z)
  {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {ϖ : 𝒪} (hϖ : IsPrimitiveRoot ϖ (pRegularExponent p (G ⧸ N)))
  {ϖ' : ResidueField 𝒪} (hϖ' : IsPrimitiveRoot ϖ' (pRegularExponent p (G ⧸ N)))
-- the Navarro (7.2) datum of `G ⧸ N` at the involution `t`
variable (hx : IsPElement p t)
  {ωC : 𝒪} (hωC : IsPrimitiveRoot ωC (pRegularExponent p ↥(centralizerOf t)))
  {ω'C : ResidueField 𝒪} (hω'C : IsPrimitiveRoot ω'C (pRegularExponent p ↥(centralizerOf t)))
  (eC : MonoidAlgebra K ↥(centralizerOf t) ≃ₐ[K] ∀ i, Matrix (mC i) (mC i) K)
  {πC : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t) →+*
    ∀ j, Matrix (nnC j) (nnC j) (ResidueField 𝒪)}
  (hπC : Function.Surjective πC)
  (hlinC : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t)),
    πC (c • a) = c • πC a)
  (hkerJC : RingHom.ker πC
    = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t)))
  (hnilC : ∀ z : Subalgebra.center (ResidueField 𝒪)
      (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t)),
    blockCharacterPi πC hπC hlinC z = 0 → IsNilpotent z)
  (hnilQ : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) (G ⧸ N)),
    blockCharacterPi (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
      (quotientPi_smul π hπ hlin hN) z = 0 → IsNilpotent z)
  {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
  (hconv : ∀ b : Block πC hπC hlinC,
    inducedBlockOfCentralizer t πC hπC hlinC (quotientPi π hπ hlin hN).toRingHom
        (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN) hnilQ hp hx b
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ →
    b = principalBlock πC hπC hlinC hnilC)
  {M : Subgroup ↥(centralizerOf t)} [M.Normal] (hMp : ¬ p ∣ Nat.card ↥M)
  (hquot : IsPGroup p (↥(centralizerOf t) ⧸ M)) (S : Sylow p ↥(centralizerOf t))
  {φ₀ : ιC} (hφ₀ : Quotient.mk (blockSetoid πC hπC hlinC) φ₀
    = principalBlock πC hπC hlinC hnilC)
  (ht : t * t = 1)

set_option maxHeartbeats 1600000 in
-- Two chains meet here: the Klein-four datum of `G ⧸ N` and the quotient datum of `G`.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open scoped Classical in
include hp hx hωC hω'C eC hkerJC hnilC hζ hζk hζK hconv hMp hquot S hφ₀ ht
  hω hω' hϖ hϖ' hkerJ eG hcent in
/-- **The Cartan invariants of the basic set double under `G ↠ G ⧸ N`** (Navarro p. 141).

`U` is the integral change-of-basis matrix of the basic set `𝓑` of the principal block of
`G ⧸ N`, from Navarro (7.4).  Because `IBr(G) = IBr(G ⧸ N)` under `quotientPi`, the same `U`
expresses the basic set of `B_0(G)`, and (7.6) multiplies its Gram matrix by `|N|`:

`Uᵗ C_{B_0(G)} U = |N| (1 + δ)`.

For `G = C_G(t)` and `N = ⟨t⟩` this is the `2(1 + δ)` that the Brauer–Suzuki argument reads off
the "analysis at `t`". -/
theorem sum_intBasicSetMatrix_mul_cartanMatrix_quotientPi {A : ι → κ → ℤ}
    (ha0 : ∀ (ν : ι) (l : κ), blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
        (quotientPi_smul π hπ hlin hN) hnilQ l
      ≠ Quotient.mk (blockSetoid (quotientPi π hπ hlin hN).toRingHom
          (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)) ν → A ν l = 0)
    (hasum : ∀ (ν : ι) {y : G ⧸ N}, IsPRegular p y →
      (∑ l ∈ Finset.univ.filter (fun l => blockOfIrr eQ (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ l
          = Quotient.mk (blockSetoid (quotientPi π hπ hlin hN).toRingHom
              (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)) ν),
        (A ν l : K) * algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) eQ l y))
        = algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪)
            (quotientPi π hπ hlin hN).toRingHom ν y))
    (hconjall : ∀ v : G ⧸ N, IsPElement p v → v ≠ 1 → IsConj t v) (ht1 : t ≠ 1)
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
    (∑ μ : ι, ∑ τ : ι, (intBasicSetMatrix eQ A t j₀ μ j : K)
        * (cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ eG μ τ : K)
        * (intBasicSetMatrix eQ A t j₀ τ k : K))
      = (Nat.card ↥N : K) * (1 + if j = k then 1 else 0) := by
  classical
  rw [sum_sum_mul_cartanMatrix_quotientPi hω hω' hϖ hϖ' hπ hlin hkerJ eG eQ hN hcent
    (fun μ l => ((intBasicSetMatrix eQ A t j₀ μ l : ℤ) : K)) j k]
  congr 1
  have hint := sum_intBasicSetMatrix_mul_cartanMatrix hp hx hωC eC eQ
    (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN) hπC hlinC hkerJC hnilC
    hnilQ hω'C hζ hζk hζK hconv hMp hquot S hφ₀ ht hϖ hϖ'
    (ker_quotientPi π hπ hlin hN hkerJ) ha0 hasum hconjall ht1 hcart hj₀ hjB hjne hkB hkne
  have := congrArg (fun z : ℤ => (z : K)) hint
  push_cast at this ⊢
  exact this

end QuotientKleinFour

end OddOrder.RepresentationTheory.Modular
