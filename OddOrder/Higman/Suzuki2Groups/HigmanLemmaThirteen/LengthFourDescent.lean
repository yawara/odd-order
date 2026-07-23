/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.LengthFourReduction
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.QuotientTwoStep

/-!
# Higman's Lemma 13: descent and the abelian length-four obstruction

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

The opening reduction of Lemma 13 says that a group of `ξ`-length greater
than four contains a normal `ξ`-subgroup of length four, and that Lemma 9
rules out this subgroup being abelian.  This leaf supplies the two local
ingredients used by that reduction:

* a descent-specific construction sending an ambient normal invariant term
  contained in a subgroup to the corresponding term under the restricted
  range actor, with strictness preserved;
* the direct Agemo obstruction showing that an abelian finite `2`-group of
  exponent at most four cannot carry a four-step `ξ`-chain.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uA uX

/-! ## Descent of normal invariant terms -/

/-- The restricted term used in Higman's length descent.

An ambient normal actor-invariant subgroup is intersected with the
restricted carrier through `subgroupOf`; the actor is then replaced by the
faithful range of its restriction.  This definition is intentionally local
to the Lemma 13 descent. -/
def xiLengthDescentSubgroupOf
    {A : Type uA} [Group A] {X : Type uX} [Group X]
    {act : X →* MulAut A} {S : Subgroup A}
    (hSinv : IsAInvariant act S)
    (K : NormalInvariantSubgroup act) :
    NormalInvariantSubgroup hSinv.restrict.range.subtype :=
  ⟨K.1.subgroupOf S,
    ⟨K.2.1.subgroupOf S,
      (isAInvariant_range_subtype_iff hSinv.restrict
        (K.1.subgroupOf S)).2 (hSinv.subgroupOf K.2.2)⟩⟩

/-- Strict inclusions between ambient descent terms remain strict after
passing to `subgroupOf` inside a common containing subgroup. -/
theorem xiLengthDescentSubgroupOf_lt
    {A : Type uA} [Group A] {X : Type uX} [Group X]
    {act : X →* MulAut A} {S : Subgroup A}
    (hSinv : IsAInvariant act S)
    {K L : NormalInvariantSubgroup act}
    (hKS : K.1 ≤ S) (hLS : L.1 ≤ S) (hKL : K < L) :
    xiLengthDescentSubgroupOf hSinv K <
      xiLengthDescentSubgroupOf hSinv L := by
  change K.1.subgroupOf S < L.1.subgroupOf S
  rw [← Subgroup.map_lt_map_iff_of_injective S.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hKS,
    Subgroup.map_subgroupOf_eq_of_le hLS]
  exact hKL

/-! ## The abelian obstruction -/

/-- **Higman Lemma 13 (p. 92), abelian case of the opening descent.**

In the source line “a group of length greater than 4 contains a normal
`ξ`-subgroup of length 4, which cannot be abelian, by Lemma 9,” Lemma 9
provides exponent at most four for the abelian subgroup.  The homocyclic
Agemo classification then sends every proper nontrivial term of the
four-step chain to `Agemo A 2 1`; the first two middle terms are therefore
equal, contradicting their strict inclusion. -/
theorem not_hasXiLengthAtLeastFour_of_isMulCommutative_of_pow_four
    {A : Type uA} [Group A] [Finite A]
    {Y : Subgroup (MulAut A)}
    (hA : IsPGroup 2 A)
    (htrans : ActsTransitivelyOnInvolutions Y)
    (hcomm : IsMulCommutative A)
    (hfour : ∀ a : A, a ^ 4 = 1) :
    ¬ HasXiLengthAtLeastFour Y.subtype := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hcomm.is_comm.comm }
  intro hlen
  obtain ⟨ι, hι, e, _he, _hε, classify⟩ :=
    exists_homocyclic_and_invariant_eq_agemo hA Y.subtype htrans
  letI : Fintype ι := hι
  have hAgemoTwo : Agemo A 2 2 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := mem_agemo_iff_of_comm.mp hx
    simpa using hfour y
  have proper_invariant_index_eq_one :
      ∀ (K : NormalInvariantSubgroup Y.subtype),
        K ≠ normalInvariantBot Y.subtype →
        K ≠ normalInvariantTop Y.subtype →
        ∀ s : ℕ, K.1 = Agemo A 2 s → s = 1 := by
    intro K hKbot hKtop s hKs
    have hKvalNeBot : K.1 ≠ (⊥ : Subgroup A) := by
      intro h
      apply hKbot
      apply Subtype.ext
      exact h
    have hKvalNeTop : K.1 ≠ (⊤ : Subgroup A) := by
      intro h
      apply hKtop
      apply Subtype.ext
      exact h
    have hs0 : s ≠ 0 := by
      intro hs
      subst s
      apply hKvalNeTop
      simpa [agemo_zero_eq_top] using hKs
    have hslt : s < 2 := by
      by_contra hnot
      have htwo : 2 ≤ s := by omega
      apply hKvalNeBot
      rw [hKs, eq_bot_iff]
      exact (Agemo.anti htwo).trans (le_of_eq hAgemoTwo)
    omega
  obtain ⟨U, V, W, hbotU, hUV, hVW, hWtop⟩ := hlen.exists_chain
  obtain ⟨s, _hs, hUs⟩ := classify U.1 U.2.2
  obtain ⟨t, _ht, hVt⟩ := classify V.1 V.2.2
  have hs : s = 1 := proper_invariant_index_eq_one U hbotU.ne'
    ((hUV.trans hVW).trans hWtop).ne s hUs
  have ht : t = 1 := proper_invariant_index_eq_one V
    (hbotU.trans hUV).ne' (hVW.trans hWtop).ne t hVt
  apply hUV.ne
  apply Subtype.ext
  rw [hUs, hVt, hs, ht]

end OddOrder.Higman.Suzuki2Groups
