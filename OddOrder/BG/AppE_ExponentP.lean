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
open scoped commutatorElement Pointwise

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

/-! ### BG's hard branch, `(E.15)`: the conjugacy class of `v ∈ R₀^#` in `S` -/

/-- Centralizing a generator is centralizing the whole cyclic group it generates. -/
theorem centralizer_singleton_eq_of_zpowers_eq {G : Type*} [Group G] {v : G} {H : Subgroup G}
    (hv : Subgroup.zpowers v = H) :
    Subgroup.centralizer ({v} : Set G) = Subgroup.centralizer (H : Set G) := by
  subst hv
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  refine ⟨fun h g hg => ?_, fun h g hg => ?_⟩
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (h v rfl) k)
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact h g (Subgroup.mem_zpowers g)

/-- **BG (E.15), the centralizer half**: `|C_S(v)| = |C_S(R₀)| = p²` for a generator `v`
of `R₀`.

BG writes `|S : C_S(v)| = |S : C_S(R₀)|`; the two centralizers are literally equal
(`centralizer_singleton_eq_of_zpowers_eq`), and the order `p²` is Step 2's `(E.4)`. -/
theorem RegularOperatorSetup.card_centralizer_generator [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p)
    {v : ↥S} (hv : Subgroup.zpowers v = hyp.R₀.subgroupOf S) :
    Nat.card ↥(Subgroup.centralizer ({v} : Set ↥S)) = p ^ 2 := by
  rw [centralizer_singleton_eq_of_zpowers_eq hv, hyp.centralizer_subgroupOf_eq hR₀S,
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : S ⊓ Subgroup.centralizer (hyp.R₀ : Set R) ≤ S)).toEquiv]
  exact (hyp.centralizer_inf_eq_sup_omega1Center hR₀S hexp hS).2

/-- **BG (E.15)**: the `S`-conjugacy class of `v ∈ R₀^#` has `|S|/p²` elements.

Stated as `p² · |K| = |S|` to keep it division-free.  Orbit--stabilizer for the conjugation
action of `S` on itself, with the stabilizer identified as `C_S(v)` by
`ConjAct.stabilizer_eq_centralizer` and its order supplied by
`card_centralizer_generator`. -/
theorem RegularOperatorSetup.card_conjClass_generator [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p)
    {v : ↥S} (hv : Subgroup.zpowers v = hyp.R₀.subgroupOf S) :
    p ^ 2 * Nat.card (MulAction.orbit (ConjAct ↥S) v) = Nat.card ↥S := by
  have horb : Nat.card (MulAction.orbit (ConjAct ↥S) v) =
      (MulAction.stabilizer (ConjAct ↥S) v).index := by
    rw [Subgroup.index]
    exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct ↥S) v)
  have hstab : Nat.card ↥(MulAction.stabilizer (ConjAct ↥S) v) = p ^ 2 := by
    rw [ConjAct.stabilizer_eq_centralizer]
    exact hyp.card_centralizer_generator hR₀S hexp hS hv
  rw [horb, ← hstab]
  exact (MulAction.stabilizer (ConjAct ↥S) v).card_mul_index

/-! ### BG's Frattini variation

BG introduces `T₁` as the normalizer in `T` of the `S`-class `K` of `v`, then computes
`T₁ = S(T₁ ∩ R₀R₁) = S R₀ (T₁ ∩ R₁) = S(T₁ ∩ R₁)`.

The first equality is a Frattini argument (`S ⊴ T₁` is transitive on `K`, so
`T₁ = S · Stab_{T₁}(v) = S · C_{T₁}(v)`), and its outcome `T₁ = S · C_T(v)` can be taken as
the *definition* of `T₁` — nothing downstream uses "normalizer of `K`" directly.  That is
what is done here: it removes the need for an action on sets of subsets entirely. -/

/-- **BG's Frattini variation**: `S ⊔ C_T(v) = S ⊔ (T ⊓ R₁)` for `R₀ ≤ S ≤ T` and a
generator `v` of `R₀`.

`C_R(v) = C_R(R₀) = R₀ × R₁` by the setup, and `R₀ ≤ S`; so the `R₀`-component of an element
of `C_T(v)` is absorbed into `S`, and the `R₁`-component is left inside `T`.  This is the
step that makes `T₁/S` a section of the **cyclic** `R₁`. -/
theorem RegularOperatorSetup.sup_centralizer_eq_sup_inf_R₁ [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S T : Subgroup R} (hR₀S : hyp.R₀ ≤ S) (hST : S ≤ T)
    {v : R} (hv : Subgroup.zpowers v = hyp.R₀) :
    S ⊔ (T ⊓ Subgroup.centralizer ({v} : Set R)) = S ⊔ (T ⊓ hyp.R₁) := by
  have hcv : Subgroup.centralizer ({v} : Set R) = hyp.R₀ ⊔ hyp.R₁ := by
    rw [centralizer_singleton_eq_of_zpowers_eq hv, hyp.centralizer_eq]
  refine le_antisymm (sup_le le_sup_left fun x hx => ?_) ?_
  · obtain ⟨hxT, hxC⟩ := hx
    rw [hcv] at hxC
    -- `x = r₀ r₁` with `r₀ ∈ R₀`, `r₁ ∈ R₁`
    have hnorm : hyp.R₀ ≤ Subgroup.normalizer (hyp.R₁ : Set R) :=
      hyp.R₀_le_centralizer_R₁.trans (Subgroup.centralizer_le_normalizer _)
    have hcoe : (↑(hyp.R₀ ⊔ hyp.R₁) : Set R) = (hyp.R₀ : Set R) * (hyp.R₁ : Set R) :=
      Subgroup.coe_mul_of_left_le_normalizer_right hyp.R₀ hyp.R₁ hnorm
    have hxmem : x ∈ (hyp.R₀ : Set R) * (hyp.R₁ : Set R) := by rw [← hcoe]; exact hxC
    obtain ⟨r₀, hr₀, r₁, hr₁, rfl⟩ := hxmem
    have hr₀T : r₀ ∈ T := hST (hR₀S hr₀)
    have hr₁T : r₁ ∈ T := by
      have hrw : r₁ = r₀⁻¹ * (r₀ * r₁) := by group
      rw [hrw]
      exact T.mul_mem (T.inv_mem hr₀T) hxT
    exact Subgroup.mul_mem_sup (hR₀S hr₀) ⟨hr₁T, hr₁⟩
  · refine sup_le le_sup_left ((inf_le_inf_left T ?_).trans le_sup_right)
    rw [hcv]
    exact le_sup_right

/-- The image of a cyclic subgroup, in generator form: `K.map f = ⟨f g⟩` for a generator `g`
of `K`.

Generator form rather than `IsCyclic ↥(K.map f)` because BG Lemma 4.5(b)
(`Ch1.S04.card_omega1_le_prime_sq_of_cyclic_index_prime`) consumes a generator and the
index of its `zpowers`. -/
theorem exists_zpowers_eq_map_of_isCyclic {G H : Type*} [Group G] [Group H]
    (f : G →* H) {K : Subgroup G} (hK : IsCyclic ↥K) :
    ∃ x : H, Subgroup.zpowers x = K.map f := by
  obtain ⟨g, hg⟩ := hK.exists_generator
  have hKg : Subgroup.zpowers (g : G) = K :=
    le_antisymm (Subgroup.zpowers_le.mpr g.2) fun y hy => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
      exact ⟨k, congrArg Subtype.val hk⟩
  refine ⟨f (g : G), le_antisymm ?_ ?_⟩
  · rw [Subgroup.zpowers_le]
    exact ⟨(g : G), g.2, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Subgroup.zpowers (g : G) := by rw [hKg]; exact hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    exact ⟨k, (map_zpow f _ k).symm⟩

/-- `T ⊓ R₁` is cyclic, being a subgroup of the cyclic `R₁`. -/
theorem RegularOperatorSetup.isCyclic_inf_R₁ (hyp : RegularOperatorSetup R B p q)
    (T : Subgroup R) : IsCyclic ↥(T ⊓ hyp.R₁) := by
  haveI := hyp.R₁_cyclic
  haveI : IsCyclic ↥((T ⊓ hyp.R₁).subgroupOf hyp.R₁) := inferInstance
  exact isCyclic_of_surjective
    (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ hyp.R₁ ≤ hyp.R₁)).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe _).surjective

/-- **BG's "As `R₁` is cyclic, so is `T₁/S`"**, in generator form.

`T₁ = S ⊔ (T ⊓ R₁)` (`sup_centralizer_eq_sup_inf_R₁`), and `S` dies in `T/S`, so the image
of `T₁` is the image of the cyclic `T ⊓ R₁` — generated by the image of any generator. -/
theorem RegularOperatorSetup.exists_zpowers_eq_map_sup_inf_R₁ [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S T : Subgroup R} (hST : S ≤ T)
    [hn : (S.subgroupOf T).Normal] :
    ∃ x : ↥T ⧸ S.subgroupOf T,
      Subgroup.zpowers x =
        ((S ⊔ (T ⊓ hyp.R₁)).subgroupOf T).map (QuotientGroup.mk' (S.subgroupOf T)) := by
  -- the image of `T ⊓ R₁`, which is cyclic
  haveI : IsCyclic ↥((T ⊓ hyp.R₁).subgroupOf T) := by
    haveI := hyp.isCyclic_inf_R₁ T
    exact isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : T ⊓ hyp.R₁ ≤ T)).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe _).symm.surjective
  obtain ⟨x, hx⟩ := exists_zpowers_eq_map_of_isCyclic
    (QuotientGroup.mk' (S.subgroupOf T)) ‹IsCyclic ↥((T ⊓ hyp.R₁).subgroupOf T)›
  refine ⟨x, hx.trans ?_⟩
  -- the two images agree because `S` maps to `1`
  have hbot : (S.subgroupOf T).map (QuotientGroup.mk' (S.subgroupOf T)) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff y).mpr hy)
  rw [Subgroup.subgroupOf_sup hST (inf_le_left : T ⊓ hyp.R₁ ≤ T), Subgroup.map_sup,
    hbot, bot_sup_eq]

end OddOrder.BG.AppE
