/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7C_ThompsonPComplementFinal

/-!
# Isaacs Thm 6.23: Thompson's normal `p`-complement theorem, characteristic-subgroup form (p. 198)

**Isaacs, _Finite Group Theory_ (AMS GSM 92), §6C, Theorem 6.23 (p. 198).**

**Theorem 6.23** (Thompson): let `P ∈ Syl_p(G)` with `G` finite and `p ≠ 2`, and assume
`N_G(X)` has a normal `p`-complement for every nonidentity characteristic subgroup `X`
of `P`.  Then `G` has a normal `p`-complement.

Isaacs states this in §6C only as "a partial statement of this improved theorem" and defers
the proof to Chapter 7, where the sharper Thm 7.1 replaces the quantifier over *all*
nonidentity characteristic subgroups by the two specific ones `Z(P)` and `J(P)`.  This leaf
therefore derives 6.23 from Thm 7.1 (`thompson_normal_p_complement_of_local_hypotheses`),
which is exactly the book's logical order.

## Proof

Both `Z(P)` and `J(P)` are nonidentity characteristic subgroups of a nontrivial `P`
(`Subgroup.center_characteristic` + `IsPGroup.center_nontrivial`, and
`Subgroup.thompsonJ_subgroupOf_characteristic` + `Subgroup.thompsonJ_ne_bot`), so the
hypothesis applies to both.  For `Z(P)` it yields a normal `p`-complement in `N_G(Z(P))`,
which descends to the subgroup `C_G(Z(P)) ≤ N_G(Z(P))`
(`Subgroup.centralizer_le_normalizer` + `hasNormalPComplement_of_le`).  Thm 7.1 then
applies.  The degenerate case `P = ⊥` is `hasNormalPComplement_of_sylow_eq_bot`.

## Main results

- `OddOrder.Isaacs.Ch06.hasNormalPComplement_of_forall_characteristic_normalizer`:
  **Isaacs Thm 6.23**.
-/

namespace OddOrder.Isaacs.Ch06

section /- 6C: Thm 6.23 (p. 198) -/

/-- **Isaacs Thm 6.23** (Thompson, p. 198).

`P ∈ Syl_p(G)`, `G` finite, `p ≠ 2`, and `N_G(X)` has a normal `p`-complement for every
nonidentity characteristic subgroup `X` of `P`.  Then `G` has a normal `p`-complement.

The characteristic subgroups of `P` are quantified in their intrinsic form, as subgroups
`X : Subgroup ↥P` carrying `Subgroup.Characteristic`; `X.map P.subtype` is the
corresponding subgroup of `G` whose normalizer is taken.

Isaacs remarks (p. 198) that `p ≠ 2` is essential: for `G = S₄` and `P ∈ Syl₂(G)` the three
nonidentity characteristic subgroups of `P ≅ D₈` are self-normalizing in `G`, hence have
normal `2`-complements, while `G` has none. -/
theorem hasNormalPComplement_of_forall_characteristic_normalizer.{u}
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (hchar : ∀ X : Subgroup ↥(P : Subgroup G), X.Characteristic → X ≠ ⊥ →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p
        ↥(Subgroup.normalizer ((X.map (P : Subgroup G).subtype : Subgroup G) : Set G))) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  classical
  -- Degenerate case: a trivial Sylow `p`-subgroup means `p ∤ |G|`.
  rcases eq_or_ne (P : Subgroup G) ⊥ with hP | hP
  · exact OddOrder.Isaacs.Ch07.hasNormalPComplement_of_sylow_eq_bot P hP
  -- `P` is a nontrivial finite `p`-group.
  have hPnt : Nontrivial ↥(P : Subgroup G) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hP
  -- `Z(P)` is a nonidentity characteristic subgroup of `P`.
  have hZnt : Nontrivial ↥(Subgroup.center ↥(P : Subgroup G)) :=
    P.isPGroup'.center_nontrivial
  have hZne : Subgroup.center ↥(P : Subgroup G) ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp hZnt
  have hNZ := hchar (Subgroup.center ↥(P : Subgroup G)) inferInstance hZne
  -- The normal `p`-complement of `N_G(Z(P))` descends to `C_G(Z(P))`.
  have hCZ : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.centralizer
        (((Subgroup.center (P : Subgroup G)).map
          (P : Subgroup G).subtype : Subgroup G) : Set G)) :=
    OddOrder.Isaacs.Ch07.hasNormalPComplement_of_le
      (Subgroup.centralizer_le_normalizer _) hNZ
  -- `J(P)` is a nonidentity characteristic subgroup of `P`.
  have hJne : (Subgroup.thompsonJ (P : Subgroup G) p).subgroupOf (P : Subgroup G) ≠ ⊥ := by
    intro hbot
    refine Subgroup.thompsonJ_ne_bot P.isPGroup' hP ?_
    have := congrArg (fun K => Subgroup.map (P : Subgroup G).subtype K) hbot
    rwa [Subgroup.map_subgroupOf_eq_of_le (Subgroup.thompsonJ_le (P : Subgroup G) p),
      Subgroup.map_bot] at this
  have hNJ := hchar _ (Subgroup.thompsonJ_subgroupOf_characteristic _ p) hJne
  rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.thompsonJ_le (P : Subgroup G) p)] at hNJ
  exact OddOrder.Isaacs.Ch07.thompson_normal_p_complement_of_local_hypotheses P hp2 hCZ hNJ

end

end OddOrder.Isaacs.Ch06
