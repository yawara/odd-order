/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_RegularOperator

/-!
# BG Appendix E, Theorem E.3, Step 3: `Ω₁(R)` has exponent `p`

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, p. 161 — Step 3 of the proof of Theorem E.3.

Step 2 (`OddOrder/BG/AppE_RegularOperator.lean` and its upstream neighbour) proves BG's
`(E.13)` — `R₀ ⊄ S'`, `|S| ≤ p^q`, `|S/S'| = p²` — for *every* `A`-invariant subgroup `S`
of exponent `p` containing `R₀`.  Step 3 turns that into a statement about `Ω₁(R)` itself:

> Take an `A`-invariant subgroup `S` of `R` of exponent `p` that is maximal subject to
> containing `R₀ × Ω₁(R₁)`.  Then `S ⊆ Ω₁(R)`.  … Let `P = Ω₁(R)` and `T = N_P(S)`.  If
> `S = Ω₁(T)`, then `N_P(T) ⊆ N_P(Ω₁(T)) = N_P(S) = T`, whence `T = P` and
> `S = Ω₁(P) = Ω₁(Ω₁(R)) = Ω₁(R)`, which by `(E.13)` yields (b) and (c).

The remaining branch — `S ≠ Ω₁(T)` — is BG's `(E.14)`–`(E.16)` counting argument, which
ends by contradicting the maximality of `S`.

## BG's seed

BG writes the seed as `R₀ × Ω₁(R₁)`.  Here it is spelled `Ω₁(C_R(R₀))` instead: the two are
equal because `C_R(R₀) = R₀ × R₁` with `R₀` of order `p`, and the centralizer form is the
one that is visibly `A`-invariant (`R₀` is `A`-invariant, hence so is its centralizer) —
`R₁` on its own carries no invariance hypothesis in the setup.
-/

namespace OddOrder.BG.AppE

open OddOrder.GroupTheory OddOrder.Isaacs.Ch03
open scoped commutatorElement

variable {R B : Type*} [Group R] [Group B] {p q : ℕ}

/-- `C_R(R₀)` is commutative, in the pointwise form `omega1OfAbelian` consumes.

`isMulCommutative_centralizer_R₀` states it for the subtype; this is the same fact with the
membership proofs kept explicit. -/
theorem RegularOperatorSetup.centralizer_R₀_mul_comm [Finite R]
    (hyp : RegularOperatorSetup R B p q) :
    ∀ x ∈ Subgroup.centralizer (hyp.R₀ : Set R), ∀ y ∈ Subgroup.centralizer (hyp.R₀ : Set R),
      x * y = y * x := by
  haveI := hyp.isMulCommutative_centralizer_R₀
  intro x hx y hy
  exact congrArg Subtype.val
    (‹IsMulCommutative ↥(Subgroup.centralizer (hyp.R₀ : Set R))›.is_comm.comm
      (⟨x, hx⟩ : ↥(Subgroup.centralizer (hyp.R₀ : Set R))) ⟨y, hy⟩)

/-- **BG's seed `R₀ × Ω₁(R₁)`**, spelled as `Ω₁(C_R(R₀))`.

Step 3 maximises among `A`-invariant exponent-`p` subgroups *containing this one*.  Its two
jobs are to force `R₀ ≤ S` (which everything in Step 2 needs) and `R₀ < S` proper (which
`(E.7)` needs). -/
def RegularOperatorSetup.seed [Finite R] (hyp : RegularOperatorSetup R B p q) : Subgroup R :=
  omega1OfAbelian R (Subgroup.centralizer (hyp.R₀ : Set R)) p hyp.centralizer_R₀_mul_comm

theorem RegularOperatorSetup.mem_seed [Finite R] (hyp : RegularOperatorSetup R B p q) {g : R} :
    g ∈ hyp.seed ↔ g ∈ Subgroup.centralizer (hyp.R₀ : Set R) ∧ g ^ p = 1 := Iff.rfl

/-- The seed has exponent `p`. -/
theorem RegularOperatorSetup.seed_pow_eq_one [Finite R] (hyp : RegularOperatorSetup R B p q)
    {g : R} (hg : g ∈ hyp.seed) : g ^ p = 1 := hg.2

/-- `R₀ ≤ Ω₁(C_R(R₀))`: `R₀` is central in its own centralizer and has exponent `p`. -/
theorem RegularOperatorSetup.R₀_le_seed [Finite R] (hyp : RegularOperatorSetup R B p q) :
    hyp.R₀ ≤ hyp.seed := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  intro g hg
  refine ⟨?_, ?_⟩
  · -- `R₀` has prime order, hence is cyclic, hence commutative: it centralizes itself
    haveI : IsCyclic ↥hyp.R₀ := isCyclic_of_prime_card hyp.R₀_card
    letI : CommGroup ↥hyp.R₀ := IsCyclic.commGroup
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (mul_comm (⟨h, hh⟩ : ↥hyp.R₀) ⟨g, hg⟩)
  · -- every element of a group of order `p` satisfies `x ^ p = 1`
    have h := pow_card_eq_one' (G := ↥hyp.R₀) (x := ⟨g, hg⟩)
    rw [hyp.R₀_card] at h
    simpa using congrArg Subtype.val h

/-- The seed is `A`-invariant.

`C_R(R₀)` is `A`-invariant because `R₀` is (`IsAInvariant.centralizer`), and the defining
equation `x ^ p = 1` is preserved by any automorphism.  ⚠ This is exactly why the seed is
written as `Ω₁(C_R(R₀))` and not as `R₀ × Ω₁(R₁)`: the setup grants no invariance for `R₁`
itself. -/
theorem RegularOperatorSetup.isAInvariant_seed [Finite R]
    (hyp : RegularOperatorSetup R B p q) :
    IsAInvariant (hyp.act.comp hyp.A.subtype) hyp.seed := by
  rw [isAInvariant_iff_smul_mem]
  intro a g hg
  refine ⟨hyp.isAInvariant_R₀.centralizer.smul_mem a hg.1, ?_⟩
  rw [← map_pow, hg.2, map_one]

/-- `R₀ < Ω₁(C_R(R₀))` **properly**.

`R₁ ≠ 1` is a `p`-group, so it has an element of order `p`; that element lies in
`C_R(R₀)` (because `R₁ ≤ R₀ ⊔ R₁ = C_R(R₀)`) and satisfies `x ^ p = 1`, hence lies in the
seed — but not in `R₀`, the two being disjoint. -/
theorem RegularOperatorSetup.R₀_lt_seed [Finite R] (hyp : RegularOperatorSetup R B p q) :
    hyp.R₀ < hyp.seed := by
  refine lt_of_le_of_ne hyp.R₀_le_seed fun heq => ?_
  obtain ⟨z, hzR₁, hzR₀, hzp⟩ := hyp.exists_mem_R₁_pow_eq_one
  refine hzR₀ ?_
  rw [heq]
  -- `z ∈ R₁ ≤ R₀ ⊔ R₁ = C_R(R₀)` and `z ^ p = 1`, so `z` lies in the seed
  exact ⟨by rw [hyp.centralizer_eq]; exact Subgroup.mem_sup_right hzR₁, hzp⟩

/-! ### BG's maximal choice -/

/-- The family Step 3 maximises over: `A`-invariant subgroups of exponent `p` containing the
seed `Ω₁(C_R(R₀))`. -/
def RegularOperatorSetup.ExpPFamily [Finite R] (hyp : RegularOperatorSetup R B p q)
    (S : Subgroup R) : Prop :=
  IsAInvariant (hyp.act.comp hyp.A.subtype) S ∧ (∀ x ∈ S, x ^ p = 1) ∧ hyp.seed ≤ S

theorem RegularOperatorSetup.expPFamily_seed [Finite R] (hyp : RegularOperatorSetup R B p q) :
    hyp.ExpPFamily hyp.seed :=
  ⟨hyp.isAInvariant_seed, fun _ hx => hyp.seed_pow_eq_one hx, le_refl _⟩

/-- **BG's maximal choice**: *"Take an `A`-invariant subgroup `S` of `R` of exponent `p` that
is maximal subject to containing `R₀ × Ω₁(R₁)`."*

The family is nonempty (it contains the seed) and `Subgroup R` is finite, so a maximal
element exists. -/
theorem RegularOperatorSetup.exists_maximal_expP [Finite R]
    (hyp : RegularOperatorSetup R B p q) :
    ∃ S, hyp.ExpPFamily S ∧ ∀ S', hyp.ExpPFamily S' → S ≤ S' → S' = S := by
  obtain ⟨S, hS, hmax⟩ :=
    Set.Finite.exists_maximal (s := {S : Subgroup R | hyp.ExpPFamily S}) (Set.toFinite _)
      ⟨hyp.seed, hyp.expPFamily_seed⟩
  exact ⟨S, hS, fun S' hS' hle => le_antisymm (hmax hS' hle) hle⟩

/-- Every member of the family lies inside `Ω₁(R)`: BG's *"Then `S ⊆ Ω₁(R)`"*. -/
theorem RegularOperatorSetup.expPFamily_le_omega [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hS : hyp.ExpPFamily S) :
    S ≤ Omega R p 1 :=
  fun x hx => Omega.mem_of_pow_eq_one (by simpa using hS.2.1 x hx)

/-- `R₀ < S` for every member of the family, and in particular `R₀ ≤ S` — the two hypotheses
that all of Step 2 runs on. -/
theorem RegularOperatorSetup.R₀_lt_of_expPFamily [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hS : hyp.ExpPFamily S) :
    hyp.R₀ < S :=
  lt_of_lt_of_le hyp.R₀_lt_seed hS.2.2

/-- The exponent hypothesis in the subtype form Step 2 consumes. -/
theorem RegularOperatorSetup.expPFamily_pow_eq_one [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hS : hyp.ExpPFamily S)
    (x : ↥S) : x ^ p = 1 :=
  Subtype.ext (by simpa using hS.2.1 (x : R) x.2)

/-! ### `Ω_n(H)` for a subgroup `H`, viewed in the ambient group

BG's `Ω₁(T)` for `T = N_P(S)` is `Ω₁` of the *group* `T`.  Stating it ambiently — as the
closure of `{x ∈ T | x^p = 1}` inside `R` — keeps BG's `N_P(T) ⊆ N_P(Ω₁(T))` free of
`subgroupOf` round trips.  Compare `frattiniInG`, which plays the same role for `Φ`. -/

/-- `Ω_n(H)` transported back into the ambient group.

Equal to `(Omega ↥H p n).map H.subtype` (`omegaInG_eq_map`); the closure form is the
definition because `Ω_n` *is* a closure and `MonoidHom.map_closure` turns the image of the
closure into the closure of the image.

⚠ Kept here rather than in `OddOrder/GroupTheory/OmegaSubgroup.lean` for the same reason as
`frattiniInG`: Appendix E is so far the only consumer.  Promote on a second one. -/
def omegaInG {G : Type*} [Group G] (H : Subgroup G) (p n : ℕ) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ H ∧ x ^ (p ^ n) = 1}

theorem omegaInG_eq_map {G : Type*} [Group G] (H : Subgroup G) (p n : ℕ) :
    omegaInG H p n = (Omega ↥H p n).map H.subtype := by
  rw [omegaInG, Omega, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Subgroup.coe_subtype]
  constructor
  · rintro ⟨hxH, hxp⟩
    exact ⟨⟨x, hxH⟩, Subtype.ext (by simpa using hxp), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using congrArg Subtype.val hy⟩

theorem omegaInG_le {G : Type*} [Group G] {H : Subgroup G} {p n : ℕ} :
    omegaInG H p n ≤ H :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem mem_omegaInG {G : Type*} [Group G] {H : Subgroup G} {p n : ℕ} {x : G}
    (hxH : x ∈ H) (hxp : x ^ (p ^ n) = 1) : x ∈ omegaInG H p n :=
  Subgroup.subset_closure ⟨hxH, hxp⟩

/-- **`Ω₁(Ω₁(G)) = Ω₁(G)`**, BG's last step in the easy branch.

The two generating sets coincide: an element with `x^{pⁿ} = 1` lies in `Ω_n(G)` already, so
the side condition `x ∈ Ω_n(G)` is vacuous. -/
theorem omegaInG_omega {G : Type*} [Group G] (p n : ℕ) :
    omegaInG (Omega G p n) p n = Omega G p n := by
  rw [omegaInG, Omega]
  congr 1
  ext x
  exact ⟨fun hx => hx.2, fun hx => ⟨Subgroup.subset_closure hx, hx⟩⟩

/-- **`N_G(H) ≤ N_G(Ω_n(H))`**, BG's *"`N_P(T) ⊆ N_P(Ω₁(T))`"*.

Conjugation by an element normalizing `H` preserves both defining conditions of the
generating set, hence its closure. -/
theorem normalizer_le_normalizer_omegaInG {G : Type*} [Group G] (H : Subgroup G) (p n : ℕ) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer ((omegaInG H p n : Subgroup G) : Set G) := by
  -- conjugation by `g ∈ N_G(H)` maps the generating set into itself
  have hsub : ∀ g ∈ Subgroup.normalizer (H : Set G), ∀ h ∈ omegaInG H p n,
      g * h * g⁻¹ ∈ omegaInG H p n := by
    intro g hg h hh
    have hle : omegaInG H p n ≤ (omegaInG H p n).comap (MulAut.conj g).toMonoidHom := by
      show Subgroup.closure {x : G | x ∈ H ∧ x ^ (p ^ n) = 1} ≤ _
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hxH, hxp⟩
      refine Subgroup.mem_comap.mpr (mem_omegaInG ?_ ?_)
      · exact (Subgroup.mem_normalizer_iff.mp hg x).mp hxH
      · show (g * x * g⁻¹) ^ (p ^ n) = 1
        have : ((MulAut.conj g) x) ^ (p ^ n) = 1 := by rw [← map_pow, hxp, map_one]
        simpa using this
    exact hle hh
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  refine fun h => ⟨hsub g hg h, fun hh => ?_⟩
  have h2 := hsub g⁻¹ (Subgroup.inv_mem _ hg) _ hh
  have heq : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [heq] at h2

/-! ### BG's easy branch -/

/-- **BG's easy branch of Step 3**: if `S = Ω₁(N_P(S))` for `P = Ω₁(R)`, then `S = Ω₁(R)`.

BG: *"Let `P = Ω₁(R)` and `T = N_P(S)`.  If `S = Ω₁(T)`, then
`N_P(T) ⊆ N_P(Ω₁(T)) = N_P(S) = T`, whence `T = P` and
`S = Ω₁(P) = Ω₁(Ω₁(R)) = Ω₁(R)`."*

Three ingredients: `N_G(T) ≤ N_G(Ω₁(T))` (`normalizer_le_normalizer_omegaInG`), the
normalizer condition in the `p`-group `P` (Isaacs Thm 1.22 — a proper subgroup of a
nilpotent group is properly contained in its normalizer), and the idempotence
`Ω₁(Ω₁(R)) = Ω₁(R)` (`omegaInG_omega`).

⚠ Nothing about `A` or the setup's `R₀`, `R₁` enters — only that `R` is a `p`-group.  BG's
hypotheses are used in the *other* branch. -/
theorem RegularOperatorSetup.eq_omega_of_omegaInG_normalizer_eq [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R}
    (h : omegaInG (Subgroup.normalizer (S : Set R) ⊓ Omega R p 1) p 1 = S) :
    S = Omega R p 1 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set P := Omega R p 1 with hP
  set T := Subgroup.normalizer (S : Set R) ⊓ P with hT
  have hTP : T ≤ P := inf_le_right
  -- `N_P(T) ≤ T`, i.e. `T` is self-normalizing in `P`
  have hself : ∀ g ∈ P, g ∈ Subgroup.normalizer (T : Set R) → g ∈ T := by
    intro g hgP hgN
    have h1 : g ∈ Subgroup.normalizer ((omegaInG T p 1 : Subgroup R) : Set R) :=
      normalizer_le_normalizer_omegaInG T p 1 hgN
    rw [h] at h1
    exact ⟨h1, hgP⟩
  -- so `T = P`, by the normalizer condition in the `p`-group `P`
  haveI hPp : IsPGroup p ↥P := hyp.R_pGroup.to_subgroup P
  haveI : Group.IsNilpotent ↥P := hPp.isNilpotent
  have hTtop : T.subgroupOf P = ⊤ := by
    by_contra hne
    obtain ⟨x, hxN, hxT⟩ := SetLike.exists_of_lt
      (OddOrder.Isaacs.Ch01.lt_normalizer_of_isNilpotent_of_lt_top
        (H := T.subgroupOf P) (lt_of_le_of_ne le_top hne))
    rw [← Subgroup.subgroupOf_normalizer_eq hTP] at hxN
    exact hxT (Subgroup.mem_subgroupOf.mpr
      (hself (x : R) x.2 (Subgroup.mem_subgroupOf.mp hxN)))
  have hTeq : T = P := le_antisymm hTP (Subgroup.subgroupOf_eq_top.mp hTtop)
  rw [← h, hTeq, hP, omegaInG_omega]

end OddOrder.BG.AppE
