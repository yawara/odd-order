/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.GroupTheory.ElementaryAbelian
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Minimal `L`-invariant normal subgroups are elementary abelian

`OddOrder.GroupTheory.MinimalInvariantNormal`: for a finite solvable group `H` carrying an action
`φ : L →* MulAut H`, a nontrivial `H` has a nontrivial `L`-invariant normal subgroup `N ◁ H` that
is *elementary abelian* (`exists_aInvariant_normal_isElementaryAbelian`).

This is the existence input driving the chief-series induction of **Peterfalvi (9.1)** (Wielandt's
fixed-point formula, assembled from `OddOrder.GroupTheory.wielandt_step`): the induction peels off
such an `N`, applies the per-chief-factor identity on the elementary-abelian `N`, and recurses on
`H/N`.  It is also the minimal-invariant-normal input for the corollary (i) argument in
`OddOrder.GroupTheory.CoprimeFrobeniusKernel`.

The proof takes a minimal element `N` of the finite poset of nontrivial `L`-invariant normal
subgroups.  Both the derived subgroup `commutator ↥N` and, once `N` is abelian, the subgroup of
`p`-th powers `(powMonoidHom p).range` are characteristic in `↥N`, hence map to `L`-invariant normal
subgroups of `H` contained in `N` (`ConjAct.normal_of_characteristic_of_normal` +
`IsAInvariant.of_characteristic` on the restricted action).  Minimality forces each to be trivial:
`commutator ↥N = ⊥` makes `↥N` abelian, and `(powMonoidHom p).range = ⊥` makes `↥N` have exponent
`p`.

`notes/peterfalvi/s11_wielandt_91_design.md` (assembly piece A), issue 2014.
-/

namespace OddOrder.GroupTheory

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)
open scoped commutatorElement

variable {L H : Type*} [Group L] [Group H] {φ : L →* MulAut H}

/-- A subgroup `K ≤ ↥N` invariant under the restricted action `hN.restrict` maps, via `N.subtype`,
to an `L`-invariant subgroup of `H`. -/
theorem aInvariant_map_subtype_of_restrict {N : Subgroup H} (hN : IsAInvariant φ N)
    {K : Subgroup ↥N} (hK : IsAInvariant hN.restrict K) :
    IsAInvariant φ (K.map N.subtype) := by
  rw [isAInvariant_iff_smul_mem]
  rintro l _ ⟨k, hk, rfl⟩
  exact ⟨(hN.restrict l) k, hK.smul_mem l hk, IsAInvariant.restrict_apply_val hN l k⟩

/-- A *characteristic* subgroup `K` of an `L`-invariant normal subgroup `N ◁ H` maps to a subgroup
of `H` that is simultaneously `L`-invariant, normal in `H`, and contained in `N`. -/
theorem aInvariant_normal_map_of_characteristic {N : Subgroup H} [N.Normal]
    (hN : IsAInvariant φ N) (K : Subgroup ↥N) [K.Characteristic] :
    IsAInvariant φ (K.map N.subtype) ∧ (K.map N.subtype).Normal ∧ K.map N.subtype ≤ N :=
  ⟨aInvariant_map_subtype_of_restrict hN (IsAInvariant.of_characteristic hN.restrict),
    ConjAct.normal_of_characteristic_of_normal, Subgroup.map_subtype_le K⟩

/-- **Existence of an elementary-abelian `L`-invariant normal subgroup.**  A nontrivial finite
solvable group `H` carrying an action `φ : L →* MulAut H` has a nontrivial `L`-invariant normal
subgroup `N ◁ H` that is elementary abelian (of some prime exponent `p`). -/
theorem exists_aInvariant_normal_isElementaryAbelian [Finite H] [IsSolvable H]
    [Nontrivial H] :
    ∃ (N : Subgroup H) (p : ℕ), p.Prime ∧ N ≠ ⊥ ∧ N.Normal ∧ IsAInvariant φ N ∧
      IsElementaryAbelian p ↥N := by
  classical
  -- A minimal element of the finite poset of nontrivial `L`-invariant normal subgroups.
  set S : Set (Subgroup H) := {N | N ≠ ⊥ ∧ N.Normal ∧ IsAInvariant φ N} with hS_def
  have hS_ne : S.Nonempty := ⟨⊤, top_ne_bot, inferInstance, IsAInvariant.top φ⟩
  obtain ⟨N, ⟨hN_ne, hN_normal, hN_inv⟩, hN_min⟩ := (Set.toFinite S).exists_minimal hS_ne
  -- Minimality kill: an `L`-invariant normal subgroup `≤ N` is either trivial or all of `N`.
  have hkill : ∀ M : Subgroup H, M.Normal → IsAInvariant φ M → M ≤ N → M = ⊥ ∨ M = N := by
    intro M hMnorm hMinv hMle
    by_cases hM0 : M = ⊥
    · exact Or.inl hM0
    · exact Or.inr (le_antisymm hMle (hN_min ⟨hM0, hMnorm, hMinv⟩ hMle))
  haveI : N.Normal := hN_normal
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN_ne
  haveI : IsSolvable ↥N := inferInstance
  -- Step 1: `↥N` is abelian (`commutator ↥N = ⊥`).
  have hcomm_bot : commutator ↥N = ⊥ := by
    obtain ⟨hinv, hnorm, hle⟩ := aInvariant_normal_map_of_characteristic hN_inv (commutator ↥N)
    rcases hkill _ hnorm hinv hle with h | h
    · exact Subgroup.map_injective N.subtype_injective (by rw [h, Subgroup.map_bot])
    · -- `(commutator ↥N).map = N` would force `commutator ↥N = ⊤`, contradicting solvability.
      have htop : commutator ↥N = ⊤ := by
        apply Subgroup.map_injective N.subtype_injective
        rw [h, ← MonoidHom.range_eq_map, N.range_subtype]
      exact absurd htop (IsSolvable.commutator_lt_top_of_nontrivial (G := ↥N)).ne
  have hab : ∀ x y : ↥N, x * y = y * x := by
    intro x y
    rw [← commutatorElement_eq_one_iff_mul_comm]
    have hmem : ⁅x, y⁆ ∈ commutator ↥N :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [hcomm_bot, Subgroup.mem_bot] at hmem
    exact hmem
  -- Step 2: `↥N` has prime exponent `p` (the subgroup of `p`-th powers is trivial).
  letI : CommGroup ↥N := { (inferInstance : Group ↥N) with mul_comm := hab }
  obtain ⟨p, hp, hpdvd⟩ :=
    Nat.exists_prime_and_dvd (Finite.one_lt_card (α := ↥N)).ne'
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨N, p, hp, hN_ne, hN_normal, hN_inv, hab, fun x => ?_⟩
  -- The subgroup of `p`-th powers `(powMonoidHom p).range` is characteristic.
  have hPchar : ((powMonoidHom p).range : Subgroup ↥N).Characteristic := by
    rw [Subgroup.characteristic_iff_map_le]
    rintro ϕ _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨ϕ z, by simp only [powMonoidHom_apply, map_pow, MulEquiv.coe_toMonoidHom]⟩
  haveI := hPchar
  obtain ⟨hinv, hnorm, hle⟩ :=
    aInvariant_normal_map_of_characteristic hN_inv ((powMonoidHom p).range)
  rcases hkill _ hnorm hinv hle with h | h
  · -- `(p`-th powers`).map = ⊥` ⟹ `p`-th powers trivial ⟹ `x ^ p = 1`.
    have hbot : ((powMonoidHom p).range : Subgroup ↥N) = ⊥ :=
      Subgroup.map_injective N.subtype_injective (by rw [h, Subgroup.map_bot])
    have hxp : x ^ p ∈ ((powMonoidHom p).range : Subgroup ↥N) := ⟨x, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hxp
    exact hxp
  · -- `(p`-th powers`).map = N` ⟹ powering is surjective, hence injective, contradicting Cauchy.
    exfalso
    have htop : ((powMonoidHom p).range : Subgroup ↥N) = ⊤ :=
      Subgroup.map_injective N.subtype_injective
        (by rw [h, ← MonoidHom.range_eq_map, N.range_subtype])
    have hsurj : Function.Surjective (powMonoidHom p : ↥N →* ↥N) :=
      MonoidHom.range_eq_top.mp htop
    have hinj : Function.Injective (powMonoidHom p : ↥N →* ↥N) :=
      Finite.injective_iff_surjective.mpr hsurj
    haveI : Fintype ↥N := Fintype.ofFinite _
    obtain ⟨g, hg⟩ :=
      exists_prime_orderOf_dvd_card p (by rwa [Nat.card_eq_fintype_card] at hpdvd)
    have hgp : (powMonoidHom p : ↥N →* ↥N) g = (powMonoidHom p : ↥N →* ↥N) 1 := by
      simp only [powMonoidHom_apply, one_pow]
      rw [← hg]; exact pow_orderOf_eq_one g
    have hg1 : g = 1 := hinj hgp
    rw [hg1, orderOf_one] at hg
    exact hp.ne_one hg.symm

end OddOrder.GroupTheory
