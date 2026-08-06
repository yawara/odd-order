/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockConnected
import OddOrder.GroupTheory.RepresentationTheory.Modular.QuotientCartan
import OddOrder.GroupTheory.RepresentationTheory.Modular.QuotientPrincipalBlock

/-!
# Navarro (7.6): the principal blocks of `G` and `G/N` have the same `IBr`

`QuotientPrincipalBlock` proves the easy inclusion `IBr(B_0(Ḡ)) ⊆ IBr(B_0(G))`.  This file is the
converse, which is the content of Navarro's (7.6) — and it is exactly the argument on p. 138:

> if the block `B` of `G` contained more than one block of `Ḡ`, then since `c_{φθ} = |P| c_{φ̄θ̄}`
> the Cartan matrix of `B` would have the form `(* 0; 0 *)`, contradicting Problem (3.4).

Problem (3.4) is `not_cartanMatrix_separated` (`BlockConnected`), and `c = |P| c̄` is
`cartanMatrix_quotientPi` (`QuotientCartan`), which holds for *every* pair of indices — the two
splittings share the index set `ι`, that being Navarro's `IBr(Ḡ) = IBr(G)`.

## Main results

* `OddOrder.RepresentationTheory.Modular.mk_eq_principalBlock_quotientPi_of_mem`

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (7.6), Problem (3.4).
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [CharZero K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
  [CharP (ResidueField 𝒪) p]
variable {G ι : Type*} [Group G] [Fintype G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)]
variable {ι'' : Type*} [Fintype ι''] {m' : ι'' → Type*} [∀ i, Fintype (m' i)]
  [∀ i, DecidableEq (m' i)] [∀ i, Nonempty (m' i)]
variable {N : Subgroup G} [N.Normal] [hpF : Fact p.Prime]
  [Invertible (Nat.card G : K)] [Invertible (Nat.card (G ⧸ N) : K)]
variable {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {ϖ : 𝒪} (hϖ : IsPrimitiveRoot ϖ (pRegularExponent p (G ⧸ N)))
  {ϖ' : ResidueField 𝒪} (hϖ' : IsPrimitiveRoot ϖ' (pRegularExponent p (G ⧸ N)))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (hN : IsPGroup p ↥N)
  (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    MatrixModule.blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
  (hnilQ : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) (G ⧸ N)),
    MatrixModule.blockCharacterPi (quotientPi π hπ hlin hN).toRingHom
      (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN) z = 0 → IsNilpotent z)
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
  (e' : MonoidAlgebra K (G ⧸ N) ≃ₐ[K] ∀ i, Matrix (m' i) (m' i) K)
  (hcent : ∀ z : G, IsPRegular p z → ∀ w ∈ N, Commute z w)

set_option maxHeartbeats 1600000 in
-- Problem (3.4), the doubled Cartan matrix and the quotient block machinery meet here.
set_option linter.unusedFintypeInType false in
open scoped Classical in
include hω hω' hϖ hϖ' hkerJ hnil hnilQ e e' hcent in
/-- **Navarro (7.6), the hard inclusion**: `IBr(B_0(G)) ⊆ IBr(B_0(Ḡ))`.

If some `μ ∈ IBr(B_0(G))` were outside `IBr(B_0(Ḡ))`, then `S = IBr(B_0(Ḡ))` and
`T = IBr(B_0(G)) \ S` would split `IBr(B_0(G))` with `c_{φθ} = |N| c̄_{φθ} = 0` across the split
(different `Ḡ`-blocks have vanishing `Ḡ`-Cartan entries), contradicting Problem (3.4). -/
theorem mk_eq_principalBlock_quotientPi_of_mem {μ : ι}
    (hμ : Quotient.mk (MatrixModule.blockSetoid π hπ hlin) μ = principalBlock π hπ hlin hnil) :
    Quotient.mk (MatrixModule.blockSetoid (quotientPi π hπ hlin hN).toRingHom
        (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)) μ
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ := by
  classical
  by_contra hSμ
  set S : ι → Prop := fun ν =>
    Quotient.mk (MatrixModule.blockSetoid (quotientPi π hπ hlin hN).toRingHom
        (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)) ν
      = principalBlock (quotientPi π hπ hlin hN).toRingHom (quotientPi_surjective π hπ hlin hN)
          (quotientPi_smul π hπ hlin hN) hnilQ with hSdef
  set T : ι → Prop := fun ν =>
    Quotient.mk (MatrixModule.blockSetoid π hπ hlin) ν = principalBlock π hπ hlin hnil ∧ ¬ S ν
    with hTdef
  obtain ⟨φ, hφ⟩ := Quotient.exists_rep (principalBlock (quotientPi π hπ hlin hN).toRingHom
    (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN) hnilQ)
  refine not_cartanMatrix_separated hpF.out hω hω' hπ hlin hkerJ hnil e
    (S := S) (T := T) (B := principalBlock π hπ hlin hnil) (fun φ' θ' hS hT => ?_)
    (fun ν hν => mk_eq_principalBlock_of_quotientPi hπ hlin hN hnil hnilQ hν)
    (fun ν hν => hν.1) (fun ν hν => ?_) hφ ⟨hμ, hSμ⟩
  · -- the `Ḡ`-Cartan entry vanishes across the split, and `c = |N| c̄`
    rw [cartanMatrix_quotientPi hω hω' hϖ hϖ' hπ hlin hkerJ e e' hN hcent φ' θ',
      cartanMatrix_eq_zero_of_centralCharacterAlg_ne hpF.out hϖ hϖ'
        (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)
        (ker_quotientPi π hπ hlin hN hkerJ) e' (fun hc => hT.2 ?_), mul_zero]
    rw [hSdef]
    rw [hSdef] at hS
    exact (Quotient.sound hc).symm.trans hS
  · by_cases hS : S ν
    · exact Or.inl hS
    · exact Or.inr ⟨hν, hS⟩

end OddOrder.RepresentationTheory.Modular
