/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults.Notation

/-!
# BG Theorem C(5) — maximal-overgroup uniqueness for prime-order subgroups of the pair

BG *Local Analysis for the Odd Order Theorem* (LMS LNS 188), **Theorem C(5)** (mmd L4396):
in the type-`P` situation (`K ≠ 1`), with `K* = M_σ ⊓ C_G(K)` and the paired maximal `M*`,
`𝓜(C_G(X)) = {M}` for every subgroup `X ⊆ K*` of prime order, and `𝓜(C_G(Y)) = {M*}` for
every subgroup `Y ⊆ K` of prime order.

This is the one conjunct of Theorem C that `theoremC_paired_structure`
(`…S16_MainResults.TheoremsAE`, which carries C(1)–(4),(6)–(11)) omits.  The schematic proof
(mmd L4450) cites "Theorem 10.1(b), Theorem 14.7(a)(b)(c), Proposition 14.2(c) → (4)(5)".
Both halves reduce to **Proposition 14.2(c)** (`S14.typeP_structure`, conjunct 6,
`𝓜(C_G(X)) = {M}` for `X ∈ ℰ¹(K*)`):

* the first half directly, applied to `M`;
* the second half applied to the dual partner `M*` (**Theorem 14.7** / `S14.typeP_duality`),
  whose `κ(M*)`-Hall factor is `K*` and whose "`K*`-datum" is `K = M*_σ ⊓ C_G(K*)`; hence
  conjunct 6 of `typeP_structure` for `M*` reads `𝓜(C_G(Y)) = {M*}` for `Y ∈ ℰ¹(K)`.

The partner `M*` is exposed via the *same* `∃!` predicate as `theoremC_paired_structure`'s
C(4) block (Theorem 14.7), so the `M*` of C(5) is definitionally the `M*` of C(4).
-/

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch4.S14
open OddOrder.BG.Ch4.S15
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Theorem C(5)** (mmd L4396): in the type-`P` situation (`K ≠ ⊥`), with
`K* = M_σ ⊓ C_G(K)`,

* `𝓜(C_G(X)) = {M}` for every prime-order `X ≤ K*`, and
* for the unique paired maximal `M*` (Theorem 14.7 / C(4)), `𝓜(C_G(Y)) = {M*}` for every
  prime-order `Y ≤ K`.

The `∃!` block reproduces `theoremC_paired_structure`'s C(4) predicate verbatim and augments it
with the second-half conclusion, so `M*` is pinned by exactly the Theorem-14.7 datum; uniqueness
carries over from `typeP_duality` (the second-half conjunct is an extra property of the same
witness, not a second selector).

Proof: `S14.typeP_structure`'s conjunct 6 is Proposition 14.2(c), `𝓜(C_G(X)) = {M}` for
`X ∈ ℰ¹(K*)`.  The first half applies it to `M`; the second half applies it to the dual partner
`M*` from `S14.typeP_duality`, whose Hall datum `K* ≤ M*`, `K*` Hall-`κ(M*)`, `K = M*_σ ⊓ C_G(K*)`
turns conjunct 6 into `𝓜(C_G(Y)) = {M*}` for `Y ∈ ℰ¹(K)`.  A prime-order subgroup is elementary
abelian of rank one (`Subgroup.IsElementaryAbelian.of_card_prime`). -/
theorem theoremC_5_overgroup_unique [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKne : K ≠ ⊥)
    (hKM : K ≤ M) (_hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    (∀ X : Subgroup G, X ≤ Kstar → (∃ p : ℕ, p.Prime ∧ Nat.card ↥X = p) →
        maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) ∧
      ∃! Mstar : Subgroup G,
        (Mstar ∈ maximalSubgroups G ∧ S14.IsTypeP Mstar ∧
          ¬ S14.IsConjugateSubgroup M Mstar ∧
          (Kstar ≤ Mstar ∧ Ch03.IsHallSubgroup (S14.kappa Mstar) (Kstar.subgroupOf Mstar) ∧
            K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G)) ∧
          IsCyclic ↥(K ⊔ Kstar) ∧ IsTISubset (S14.zTilde K Kstar) (K ⊔ Kstar) ∧
          (S14.IsTypeP2 M ∨ S14.IsTypeP2 Mstar) ∧
          (∀ H : Subgroup G, H ∈ maximalSubgroups G → S14.IsTypeP H →
            S14.IsConjugateSubgroup H M ∨ S14.IsConjugateSubgroup H Mstar)) ∧
          (∀ Y : Subgroup G, Y ≤ K → (∃ p : ℕ, p.Prime ∧ Nat.card ↥Y = p) →
            maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {Mstar}) := by
  classical
  -- `M` is type-`P` from the nonempty `κ`-Hall factor `K` (as in `theoremC_paired_structure`).
  have hKofne : K.subgroupOf M ≠ ⊥ := by
    rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hKne (hd.eq_bot_of_le hKM)
  have hP : S14.IsTypeP M := isTypeP_of_isHall_kappa_subgroupOf_ne_bot hK hKofne
  refine ⟨?_, ?_⟩
  · -- **First half** (Proposition 14.2(c) for `M`): `𝓜(C_G(X)) = {M}` for prime-order `X ≤ K*`.
    rintro X hXle ⟨p, hp, hXcard⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have hXelem : X ∈ elemAbelianOfRank G p 1 :=
      mem_elemAbelianOfRank.mpr
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
    exact (S14.typeP_structure hG hM hP hKM hK hKstar hU).2.2.2.2.2.1 p hp X hXelem hXle
  · -- **Second half**: the partner `M*` (Theorem 14.7 / `typeP_duality`); Prop 14.2(c) for `M*`.
    obtain ⟨Mstar, hP0, huniq⟩ := (S14.typeP_duality hG hM hP hKM hK hKstar).2.2
    -- Uniqueness is inherited from `typeP_duality`: the second-half conjunct is an extra property
    -- of the same witness, so the base predicate `hN.1` already pins `N = Mstar`.
    refine ⟨Mstar, ⟨hP0, ?_⟩, fun N hN => huniq N hN.1⟩
    obtain ⟨hMstmax, hMstP, _hMnc, hpair, _rest⟩ := hP0
    -- Prop 14.2(c) applied to `M*` with `(K*, K)` in the role of `(K, K*)`.
    rintro Y hYle ⟨p, hp, hYcard⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have hYelem : Y ∈ elemAbelianOfRank G p 1 :=
      mem_elemAbelianOfRank.mpr
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hYcard, by rw [hYcard, pow_one]⟩
    -- A Hall `(κ(M*) ∪ σ(M*))'`-subgroup of `M*` (solvable ⟹ Hall's theorem; `typeP_structure`
    -- does not use it, but requires it as an argument).
    haveI hMstsol : IsSolvable ↥Mstar := hG.solvable_of_mem_maximalSubgroups hMstmax
    obtain ⟨UMst, hUMsthall⟩ : ∃ UMst : Subgroup G, Ch03.IsHallSubgroup
        ((S14.kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ) (UMst.subgroupOf Mstar) := by
      obtain ⟨U', hU'hall, -⟩ := Ch03.hall_D (G := ↥Mstar)
        (π := (S14.kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ) (U := (⊥ : Subgroup ↥Mstar))
        (fun q hq => by simp at hq)
      have hUeq : (U'.map Mstar.subtype).subgroupOf Mstar = U' :=
        Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective U'
      exact ⟨U'.map Mstar.subtype, by rw [hUeq]; exact hU'hall⟩
    -- For `M*`, `typeP_structure`'s `Kstar`-argument is `K = M*_σ ⊓ C_G(K*)` (`hpair.2.2`), so its
    -- conjunct 6 is exactly `𝓜(C_G(Y)) = {M*}` for `Y ∈ ℰ¹(K)`.
    exact (S14.typeP_structure hG hMstmax hMstP hpair.1 hpair.2.1 hpair.2.2
      hUMsthall).2.2.2.2.2.1 p hp Y hYelem hYle

end OddOrder.BG.Ch4.S16
