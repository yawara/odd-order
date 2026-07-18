/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Huppert.TransitiveInvariant
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.AgemoLayers

/-!
# Higman's abelian invariant-subgroup lemma

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 1,
p. 83; used in Peterfalvi, Appendix III.

An abelian `2`-group carrying an action transitive on its involutions is
homocyclic.  Moreover, its only invariant subgroups are the terms of its
Agemo filtration.  The proof follows Higman's original two sentences:

1. involutions of different heights would contradict transitivity, so all
   cyclic direct factors have one common order;
2. power maps identify the successive quotients with the last involution
   layer, hence each quotient is irreducible and Agemo--Nakayama lifts this
   irreducibility to the complete invariant-subgroup classification.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03

/-- If a subgroup surjects onto `G/N`, then together with `N` it generates
`G`. -/
private theorem sup_eq_top_of_map_mk'_eq_top
    {G : Type*} [Group G] (N U : Subgroup G) [N.Normal]
    (hmap : U.map (QuotientGroup.mk' N) = ⊤) :
    U ⊔ N = ⊤ := by
  have hcomap := congrArg
    (fun K : Subgroup (G ⧸ N) => K.comap (QuotientGroup.mk' N)) hmap
  rw [QuotientGroup.comap_map_mk', Subgroup.comap_top] at hcomap
  simpa [sup_comm] using hcomap

/-- Ambient Agemo form of `sup_eq_top_of_map_mk'_eq_top`. -/
private theorem sup_agemo_succ_eq_of_map_quotient_eq_top
    {A : Type*} [CommGroup A] {p s : ℕ} {U : Subgroup A}
    (hU : U ≤ Agemo A p s)
    (hmap : (U.subgroupOf (Agemo A p s)).map
      (QuotientGroup.mk'
        ((Agemo A p (s + 1)).subgroupOf (Agemo A p s))) = ⊤) :
    U ⊔ Agemo A p (s + 1) = Agemo A p s := by
  have htop : U.subgroupOf (Agemo A p s) ⊔
      (Agemo A p (s + 1)).subgroupOf (Agemo A p s) = ⊤ :=
    sup_eq_top_of_map_mk'_eq_top _ _ hmap
  apply le_antisymm (sup_le hU (Agemo.anti (Nat.le_succ s)))
  apply Subgroup.subgroupOf_eq_top.mp
  rw [Subgroup.subgroupOf_sup hU (Agemo.anti (Nat.le_succ s)), htop]

/-- **Higman, Suzuki 2-groups, Lemma 1 — invariant-subgroup part**: once the
homocyclic model is fixed, every invariant subgroup is one of the Agemo
layers `A^(2^s)`, with `0 ≤ s ≤ e`. -/
theorem exists_eq_agemo_of_invariant
    {A X : Type*} [CommGroup A] [Finite A] [Group X]
    (hA : IsPGroup 2 A) (φ : X →* MulAut A)
    (htrans : ∀ x ∈ involutions A, ∀ y ∈ involutions A,
      ∃ g : X, (φ g) x = y)
    {ι : Type*} {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    {U : Subgroup A} (hU : IsAInvariant φ U) :
    ∃ s ≤ e, U = Agemo A 2 s := by
  have classify : ∀ n s : ℕ, s + n = e → U ≤ Agemo A 2 s →
      ∃ t ≤ e, U = Agemo A 2 t := by
    intro n
    induction n with
    | zero =>
        intro s hse hUle
        have hs : s = e := by omega
        subst s
        refine ⟨e, le_rfl, (eq_bot_iff.mpr ?_).trans
          (agemo_two_eq_bot_of_equiv_pi_zmod ε).symm⟩
        simpa [agemo_two_eq_bot_of_equiv_pi_zmod ε] using hUle
    | succ n ih =>
        intro s hse hUle
        by_cases hnext : U ≤ Agemo A 2 (s + 1)
        · exact ih (s + 1) (by omega) hnext
        · have hs : s < e := by omega
          let M := Agemo A 2 s
          let N := (Agemo A 2 (s + 1)).subgroupOf M
          let Ubar := (U.subgroupOf M).map (QuotientGroup.mk' N)
          have hM : IsAInvariant φ M := IsAInvariant.of_characteristic φ
          have hNext : IsAInvariant φ (Agemo A 2 (s + 1)) :=
            IsAInvariant.of_characteristic φ
          have hUM : IsAInvariant (agemoRestrictAction φ s) (U.subgroupOf M) := by
            simpa [M, agemoRestrictAction] using hM.subgroupOf hU
          have hN : IsAInvariant (agemoRestrictAction φ s) N := by
            simpa [M, N, agemoRestrictAction] using hM.subgroupOf hNext
          have hUbar : IsAInvariant (agemoSuccQuotientAction φ s) Ubar := by
            simpa [M, N, Ubar, agemoSuccQuotientAction, agemoRestrictAction] using
              hN.map_quotient hUM
          have hUbar_ne : Ubar ≠ ⊥ := by
            intro hbot
            apply hnext
            have hle : U.subgroupOf M ≤ N := by
              have hker := (Subgroup.map_eq_bot_iff (U.subgroupOf M)).mp hbot
              simpa [N] using hker
            intro u hu
            have huM : u ∈ M := hUle hu
            exact hle (show (⟨u, huM⟩ : M) ∈ U.subgroupOf M from hu)
          have hUbar_top : Ubar = ⊤ :=
            (OddOrder.Peterfalvi.Appendices.Huppert.isAInvariant_eq_bot_or_top_of_transitive
                (agemoSuccQuotientAction φ s)
                (fun q r hq hr =>
                  agemoSuccQuotientAction_transitive_on_nonidentity
                    φ ε htrans hs q r hq hr)
                hUbar).resolve_left hUbar_ne
          refine ⟨s, by omega, eq_agemo_of_sup_succ_eq hA hUle ?_⟩
          exact sup_agemo_succ_eq_of_map_quotient_eq_top hUle
            (by simpa [M, N, Ubar] using hUbar_top)
  apply classify e 0 (by simp)
  rw [agemo_zero_eq_top]
  exact le_top

/-- **Higman, Suzuki 2-groups, Lemma 1**: an abelian finite `2`-group with an
automorphism action transitive on involutions is a direct product of cyclic
groups of one common order `2^e`, and its invariant subgroups are exactly the
Agemo layers `A^(2^s)` for `0 ≤ s ≤ e`. -/
theorem exists_homocyclic_and_invariant_eq_agemo
    {A X : Type*} [CommGroup A] [Finite A] [Group X]
    (hA : IsPGroup 2 A) (φ : X →* MulAut A)
    (htrans : ∀ x ∈ involutions A, ∀ y ∈ involutions A,
      ∃ g : X, (φ g) x = y) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ℕ), 0 < e ∧
      Nonempty (A ≃* (ι → Multiplicative (ZMod (2 ^ e)))) ∧
        ∀ U : Subgroup A, IsAInvariant φ U →
          ∃ s ≤ e, U = Agemo A 2 s := by
  have htransOrder : ∀ {x y : A}, orderOf x = 2 → orderOf y = 2 →
      ∃ g : X, φ g x = y := by
    intro x y hx hy
    exact htrans x (orderOf_eq_prime_iff.mp hx) y (orderOf_eq_prime_iff.mp hy)
  obtain ⟨ι, hι, e, he, ⟨ε⟩⟩ :=
    exists_homocyclic_decomposition_of_transitive_involutions hA φ htransOrder
  exact ⟨ι, hι, e, he, ⟨ε⟩, fun _ hU =>
    exists_eq_agemo_of_invariant hA φ htrans ε hU⟩

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
