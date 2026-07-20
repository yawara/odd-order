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

/-- **The order of BG's `T₁ = S · C_T(v)`**: `|T₁| · p² = |S| · |C_T(v)|`.

The product formula `|HK| · |H ∩ K| = |H| · |K|` for `H = C_T(v)` and `K = S`.  It computes
a *subgroup* order because `C_T(v) ≤ T ≤ N_R(S)`, so the product set is the subgroup `T₁`;
and the intersection is `C_S(v)`, of order `p²` by `(E.4)`.

This is the arithmetic behind BG's `(E.16)`: dividing `|T : C_T(v)| = |T : T₁|·|T₁ : C_T(v)|`
by it turns the `T`-class bound into the bound `|T : T₁| < p²`. -/
theorem RegularOperatorSetup.card_sup_centralizer [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S T : Subgroup R} (hR₀S : hyp.R₀ ≤ S) (hST : S ≤ T)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p)
    (hTN : T ≤ Subgroup.normalizer (S : Set R)) {v : R} (hv : Subgroup.zpowers v = hyp.R₀) :
    Nat.card ↥(S ⊔ (T ⊓ Subgroup.centralizer ({v} : Set R))) * p ^ 2 =
      Nat.card ↥S * Nat.card ↥(T ⊓ Subgroup.centralizer ({v} : Set R)) := by
  set C : Subgroup R := T ⊓ Subgroup.centralizer ({v} : Set R) with hC
  have hCN : C ≤ Subgroup.normalizer (S : Set R) := inf_le_left.trans hTN
  have hcoe : (↑(C ⊔ S) : Set R) = (C : Set R) * (S : Set R) :=
    Subgroup.coe_mul_of_left_le_normalizer_right C S hCN
  have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card C S
  -- `C ⊓ S = C_S(v)`, of order `p²`
  have hinf : C ⊓ S = S ⊓ Subgroup.centralizer (hyp.R₀ : Set R) := by
    rw [hC, centralizer_singleton_eq_of_zpowers_eq hv]
    exact le_antisymm (le_inf inf_le_right (inf_le_left.trans inf_le_right))
      (le_inf (le_inf (inf_le_left.trans hST) inf_le_right) inf_le_left)
  rw [hinf, (hyp.centralizer_inf_eq_sup_omega1Center hR₀S hexp hS).2] at hprod
  have hcard : Nat.card ↥(C ⊔ S) = Nat.card ↑((C : Set R) * (S : Set R)) :=
    Nat.card_congr (Equiv.setCongr hcoe)
  rw [sup_comm, hcard, hprod, mul_comm]

/-- `C_T(v)` computed inside `↥T`: it is `(T ⊓ C_R(v)).subgroupOf T`. -/
theorem centralizer_singleton_subgroupOf {G : Type*} [Group G] (T : Subgroup G) {v : G}
    (hvT : v ∈ T) :
    Subgroup.centralizer ({(⟨v, hvT⟩ : ↥T)} : Set ↥T)
      = (T ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf T := by
  ext y
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨y.2, fun g hg => ?_⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact congrArg Subtype.val (h _ rfl)
  · rintro ⟨-, h⟩ g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact Subtype.ext (h v rfl)


/-- **BG (E.16)**: `|T : T₁| < p²`, where `T₁ = S ⊔ C_T(v)`.

BG: *"the conjugacy class of `v` in `T` is the union of `|T : T₁|` conjugacy classes of `S`,
each having `|S|/p²` elements.  Since none contains the identity element,
`|T : T₁|·|S|/p² ≤ |S| − 1 < |S|` and `|T : T₁| < p²`."*

⚠ **The fusion of `S`-classes never has to be formalised.**  One application of
orbit--stabilizer in `T` suffices: `|K_T|·|C_T(v)| = |T|`, `|T| = |T:T₁|·|T₁|` and
`|T₁|·p² = |S|·|C_T(v)|` (`card_sup_centralizer`) already combine to
`p²·|K_T| = |T:T₁|·|S|`.  The `T`-class `K_T` is a *proper* subset of `S` — inside it
because `S ⊴ T`, proper because it misses `1`. -/
theorem RegularOperatorSetup.index_sup_centralizer_lt [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S T : Subgroup R} (hR₀S : hyp.R₀ ≤ S) (hST : S ≤ T)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p)
    (hTN : T ≤ Subgroup.normalizer (S : Set R)) {v : R} (hv : Subgroup.zpowers v = hyp.R₀)
    (hvS : v ∈ S) (hv1 : v ≠ 1) :
    ((S ⊔ (T ⊓ Subgroup.centralizer ({v} : Set R))).subgroupOf T).index < p ^ 2 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set C : Subgroup R := T ⊓ Subgroup.centralizer ({v} : Set R) with hC
  set T₁ : Subgroup R := S ⊔ C with hT₁
  have hT₁T : T₁ ≤ T := sup_le hST inf_le_left
  set v' : ↥T := ⟨v, hST hvS⟩ with hv'
  set O := MulAction.orbit (ConjAct ↥T) v' with hO
  -- (1) orbit--stabilizer in `↥T`
  have hstab : MulAction.stabilizer (ConjAct ↥T) v' = C.subgroupOf T := by
    rw [ConjAct.stabilizer_eq_centralizer]
    exact centralizer_singleton_subgroupOf T (hST hvS)
  have h1 : Nat.card O * Nat.card ↥(C.subgroupOf T) = Nat.card ↥T := by
    have hidx : (MulAction.stabilizer (ConjAct ↥T) v').index = Nat.card O :=
      (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct ↥T) v')).symm
    have h := (MulAction.stabilizer (ConjAct ↥T) v').card_mul_index
    rw [hidx, hstab] at h
    rw [mul_comm]
    exact h
  -- (2) `|T| = |T₁|·|T : T₁|`
  have h2 := (T₁.subgroupOf T).card_mul_index
  have hcT₁ : Nat.card ↥(T₁.subgroupOf T) = Nat.card ↥T₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₁T).toEquiv
  have hcC : Nat.card ↥(C.subgroupOf T) = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ T)).toEquiv
  rw [hcT₁] at h2
  rw [hcC] at h1
  -- (3) the product formula
  have h3 := hyp.card_sup_centralizer hR₀S hST hexp hS hTN hv
  -- (5) the `T`-class is a proper subset of `S`
  have hOsub : O ⊆ ((S.subgroupOf T : Subgroup ↥T) : Set ↥T) := by
    rintro y ⟨t, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, ConjAct.smul_def]
    have ht := hTN (ConjAct.ofConjAct t).2
    simpa using (Subgroup.mem_normalizer_iff.mp ht v).mp hvS
  have hOne : (1 : ↥T) ∉ O := by
    rintro ⟨t, ht⟩
    have ht' : ConjAct.ofConjAct t * v' * (ConjAct.ofConjAct t)⁻¹ = 1 := by
      rw [← ConjAct.smul_def]; exact ht
    refine hv1 (congrArg Subtype.val (?_ : v' = 1))
    calc v'
        = (ConjAct.ofConjAct t)⁻¹ * (ConjAct.ofConjAct t * v' * (ConjAct.ofConjAct t)⁻¹) *
            ConjAct.ofConjAct t := by group
      _ = (ConjAct.ofConjAct t)⁻¹ * 1 * ConjAct.ofConjAct t := by rw [ht']
      _ = 1 := by group
  have hOlt : Nat.card O < Nat.card ↥S := by
    have hssub : O ⊂ ((S.subgroupOf T : Subgroup ↥T) : Set ↥T) :=
      ⟨hOsub, fun h => hOne (by rw [Set.eq_of_subset_of_subset hOsub h]; exact Subgroup.one_mem _)⟩
    have hlt := Set.ncard_lt_ncard hssub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at hlt
    calc Nat.card O < Nat.card ↥(S.subgroupOf T) := hlt
      _ = Nat.card ↥S := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hST).toEquiv
  -- (4)+(6): `p²·|K_T| = |T:T₁|·|S|`, then compare with `p²·|S|`
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have hSpos : 0 < Nat.card ↥S := Nat.card_pos
  have hkey : Nat.card O * p ^ 2 = (T₁.subgroupOf T).index * Nat.card ↥S := by
    refine Nat.eq_of_mul_eq_mul_right hCpos ?_
    calc Nat.card O * p ^ 2 * Nat.card ↥C
        = (Nat.card O * Nat.card ↥C) * p ^ 2 := by ring
      _ = (Nat.card ↥T₁ * (T₁.subgroupOf T).index) * p ^ 2 := by rw [h1, h2]
      _ = (Nat.card ↥T₁ * p ^ 2) * (T₁.subgroupOf T).index := by ring
      _ = (Nat.card ↥S * Nat.card ↥C) * (T₁.subgroupOf T).index := by rw [h3]
      _ = (T₁.subgroupOf T).index * Nat.card ↥S * Nat.card ↥C := by ring
  have : (T₁.subgroupOf T).index * Nat.card ↥S < p ^ 2 * Nat.card ↥S := by
    rw [← hkey, mul_comm (Nat.card O) (p ^ 2)]
    exact mul_lt_mul_of_pos_left hOlt (pow_pos hyp.p_prime.pos 2)
  exact Nat.lt_of_mul_lt_mul_right this


/-- `(H/N).index` in `G/N` equals `H.index` in `G`, for `N ≤ H` normal.

The bridge from `(E.16)`'s `|T : T₁|` to the index of `T₁/S` inside `T/S`, which is the
form BG Lemma 4.5(b) consumes. -/
theorem index_map_mk' {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {H : Subgroup G}
    (hNH : N ≤ H) : (H.map (QuotientGroup.mk' N)).index = H.index := by
  rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N),
    Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])]

/-- **BG (E.16), in the form Lemma 4.5(b) consumes**: the cyclic subgroup `T₁/S` of `T/S`
has index `< p²`.

`(E.16)` bounds `|T : T₁|` for `T₁ = S ⊔ C_T(v)`; the Frattini variation rewrites that
`T₁` as `S ⊔ (T ⊓ R₁)`, whose image in `T/S` is the cyclic `⟨x⟩` of
`exists_zpowers_eq_map_sup_inf_R₁`; and `index_map_mk'` says passing to `T/S` does not
change the index. -/
theorem RegularOperatorSetup.exists_zpowers_index_lt [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S T : Subgroup R} (hR₀S : hyp.R₀ ≤ S) (hST : S ≤ T)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p)
    (hTN : T ≤ Subgroup.normalizer (S : Set R)) {v : R} (hv : Subgroup.zpowers v = hyp.R₀)
    (hvS : v ∈ S) (hv1 : v ≠ 1) [hn : (S.subgroupOf T).Normal] :
    ∃ x : ↥T ⧸ S.subgroupOf T, (Subgroup.zpowers x).index < p ^ 2 := by
  obtain ⟨x, hx⟩ := hyp.exists_zpowers_eq_map_sup_inf_R₁ hST
  refine ⟨x, ?_⟩
  rw [hx, index_map_mk' _ (Subgroup.subgroupOf_mono T le_sup_left),
    ← hyp.sup_centralizer_eq_sup_inf_R₁ hR₀S hST hv]
  exact hyp.index_sup_centralizer_lt hR₀S hST hexp hS hTN hv hvS hv1


/-- **In a finite cyclic group, `|Ω₁(G)| ≤ p`.**

BG's Step 3 applies Lemma 4.5(b) to `T/S`, which needs a cyclic subgroup of index exactly
`p`; `(E.16)` only gives index `< p²`, i.e. index `1` or `p` in a `p`-group.  This closes
the index-`1` case: there `T/S` is itself cyclic, and a cyclic group has at most `p`
solutions of `x^p = 1` (`IsCyclic.card_pow_eq_one_le`), which — the group being abelian —
already form the subgroup `Ω₁`. -/
theorem card_omega_le_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G] {p : ℕ}
    (hp : 0 < p) : Nat.card ↥(Omega G p 1) ≤ p := by
  classical
  letI := Fintype.ofFinite G
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hcomm : ∀ x ∈ (⊤ : Subgroup G), ∀ y ∈ (⊤ : Subgroup G), x * y = y * x := by
    intro x _ y _
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
    rw [← zpow_add, ← zpow_add, add_comm]
  have hOK : Omega G p 1 = omega1OfAbelian G ⊤ p hcomm := by
    refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => ?_) fun x hx => ?_
    · exact ⟨Subgroup.mem_top x, by simpa using hx⟩
    · exact Omega.mem_of_pow_eq_one (by simpa using hx.2)
  rw [hOK]
  have hcard : Nat.card ↥(omega1OfAbelian G ⊤ p hcomm) = Fintype.card {x : G // x ^ p = 1} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr
      (Equiv.subtypeEquivRight fun x => ⟨fun h => h.2, fun h => ⟨Subgroup.mem_top x, h⟩⟩)
  rw [hcard, Fintype.card_subtype]
  exact IsCyclic.card_pow_eq_one_le hp


/-- **BG's "Hence, by Lemma 4.5, `|Ω₁(T/S)| ≤ p²`"**: for a finite `p`-group with a cyclic
subgroup of index `< p²`, `|Ω₁| ≤ p²`.

In a `p`-group every index is a power of `p`, so `< p²` means index `1` or `p`.  Index `p`
is BG Lemma 4.5(b) (`Ch1.S04.card_omega1_le_prime_sq_of_cyclic_index_prime`); index `1`
means the group is itself cyclic, and then `card_omega_le_of_isCyclic` gives the sharper
`≤ p`. -/
theorem card_omega_le_prime_sq_of_index_lt {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hG : IsPGroup p G) (hp_odd : Odd p) {x : G}
    (hidx : (Subgroup.zpowers x).index < p ^ 2) :
    Nat.card ↥(Omega G p 1) ≤ p ^ 2 := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, hk⟩ := hG.exists_card_eq
  have hdvd : (Subgroup.zpowers x).index ∣ Nat.card G := Subgroup.index_dvd_card _
  rw [hk] at hdvd
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hjlt : j < 2 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (hjeq ▸ hidx)
  interval_cases j
  · -- index `1`: the group is cyclic
    rw [pow_zero] at hjeq
    have htop : Subgroup.zpowers x = ⊤ := Subgroup.index_eq_one.mp hjeq
    haveI : IsCyclic G := ⟨⟨x, fun y => by
      have hy : y ∈ (⊤ : Subgroup G) := Subgroup.mem_top y
      rwa [← htop] at hy⟩⟩
    exact (card_omega_le_of_isCyclic hp.pos).trans (Nat.le_self_pow two_ne_zero p)
  · -- index `p`: BG Lemma 4.5(b)
    rw [pow_one] at hjeq
    exact OddOrder.BG.Ch1.S04.card_omega1_le_prime_sq_of_cyclic_index_prime hG hp_odd hjeq


/-- **BG's `|Ω₁(T)/S| ≤ |Ω₁(T/S)|`**, in the division-free form
`|Ω₁(T)| ≤ |Ω₁(T/S)| · |S|`.

`S` has exponent `p`, so `S ≤ Ω₁(T)`; and `Ω₁` is a *closure*, so the image of `Ω₁(T)` in
`T/S` is the closure of the images of the generators — each killed by `p` — hence lies in
`Ω₁(T/S)`.  The first isomorphism theorem turns the index of `S` inside `Ω₁(T)` into the
order of that image. -/
theorem card_omegaInG_le_mul {G : Type*} [Group G] [Finite G] {p : ℕ} {S T : Subgroup G}
    (hST : S ≤ T) (hexp : ∀ x ∈ S, x ^ p = 1) [hn : (S.subgroupOf T).Normal] :
    Nat.card ↥(omegaInG T p 1) ≤
      Nat.card ↥(Omega (↥T ⧸ S.subgroupOf T) p 1) * Nat.card ↥S := by
  set N : Subgroup ↥T := S.subgroupOf T with hN
  set W : Subgroup ↥T := Omega (↥T) p 1 with hW
  set g : ↥T →* (↥T ⧸ N) := QuotientGroup.mk' N with hg
  set f : ↥W →* (↥T ⧸ N) := g.comp W.subtype with hf
  have hcardW : Nat.card ↥(omegaInG T p 1) = Nat.card ↥W := by
    rw [omegaInG_eq_map]
    exact Subgroup.card_map_of_injective T.subtype_injective
  have hNW : N ≤ W := by
    intro x hx
    refine Omega.mem_of_pow_eq_one ?_
    have h : ((x : G)) ^ p = 1 := hexp (x : G) (Subgroup.mem_subgroupOf.mp hx)
    have hx1 : (x : ↥T) ^ p = 1 := by
      refine Subtype.ext ?_
      push_cast
      simpa using h
    simpa using hx1
  have hcardN : Nat.card ↥N = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hST).toEquiv
  have hker : f.ker = N.subgroupOf W := by
    ext x
    simp [hf, hg, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrangeW : f.range = W.map g := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hidx : (N.subgroupOf W).index = Nat.card ↥(W.map g) := by
    rw [Subgroup.index, ← hker, ← hrangeW]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hcardNW : Nat.card ↥(N.subgroupOf W) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNW).toEquiv
  -- the image lands in `Ω₁(T/S)`, via the generators
  have hle : W.map g ≤ Omega (↥T ⧸ N) p 1 := by
    rw [hW, Omega, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    exact Omega.mem_of_pow_eq_one (by rw [← map_pow, hy, map_one])
  have hsplit : Nat.card ↥(N.subgroupOf W) * (N.subgroupOf W).index = Nat.card ↥W :=
    (N.subgroupOf W).card_mul_index
  rw [hcardW, ← hsplit, hcardNW, hcardN, hidx, mul_comm]
  exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle))



/-- **`Ω₁(Ω₁(T)) = Ω₁(T)`** for a subgroup `T` — BG's *"Since `Ω₁(Ω₁(T)) = Ω₁(T)`"*.

The two generating sets literally coincide: `x ∈ T` with `x^{pⁿ} = 1` already lies in
`Ω_n(T)`, and conversely `Ω_n(T) ≤ T`. -/
theorem omegaInG_idem {G : Type*} [Group G] (T : Subgroup G) (p n : ℕ) :
    omegaInG (omegaInG T p n) p n = omegaInG T p n := by
  rw [omegaInG, omegaInG]
  congr 1
  ext x
  exact ⟨fun h => ⟨omegaInG_le h.1, h.2⟩, fun h => ⟨mem_omegaInG h.1 h.2, h.2⟩⟩

/-- `Ω₁` of the *group* `Ω₁(T)` is everything.

The subtype form of `omegaInG_idem`, which is what BG Proposition E.2(a) — stated for a
whole group — consumes. -/
theorem omega_eq_top_of_omegaInG {G : Type*} [Group G] (T : Subgroup G) (p n : ℕ) :
    Omega ↥(omegaInG T p n) p n = ⊤ := by
  refine Subgroup.map_injective (omegaInG T p n).subtype_injective ?_
  rw [← omegaInG_eq_map, omegaInG_idem, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- **BG Proposition E.2(a) applied to `Ω₁(T)`**: if `Ω₁(T)` has nilpotence class at most
`p − 1`, then it has exponent `p`.

BG: *"Therefore `Ω₁(T)` has nilpotence class at most `p − 1`.  By Proposition E.2,
`Ω₁(Ω₁(T))` has exponent `p`.  Since `Ω₁(Ω₁(T)) = Ω₁(T)`, this contradicts the maximal
choice of `S`."* -/
theorem pow_eq_one_of_omegaInG {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T : Subgroup G}
    (hgamma : (⊤ : Subgroup ↥(omegaInG T p 1)).lowerCentralSeries (p - 1) = ⊥)
    {x : G} (hx : x ∈ omegaInG T p 1) : x ^ p = 1 := by
  have hy : (⟨x, hx⟩ : ↥(omegaInG T p 1)) ∈ Omega ↥(omegaInG T p 1) p 1 := by
    rw [omega_eq_top_of_omegaInG]
    trivial
  have := omega_pow_eq_one_of_lowerCentralSeries_eq_bot hgamma hy
  simpa using congrArg (Subtype.val (p := fun z => z ∈ omegaInG T p 1)) this


/-- **BG's class bound**: `|Ω₁(T)| ≤ p^{q+2}` forces `Ω₁(T)` to have exponent `p`.

BG: *"Since `p ≥ 7` and `q ≤ (p−1)/2`, by Step 1 … therefore `Ω₁(T)` has nilpotence class
at most `p − 1`.  By Proposition E.2, `Ω₁(Ω₁(T))` has exponent `p`."*

The chain: a `p`-group of order `≤ p^{q+2}` has class `≤ q+1`
(`Ch1.S04.nilpotencyClass_le_of_card_le_pow`); Step 1 (`card_A_dvd_half_p_sub_one`) gives
`q ≤ (p−1)/2`, and `q` odd prime forces `p ≥ 7`, so `q + 1 ≤ p − 1`; then
`pow_eq_one_of_omegaInG` applies Proposition E.2(a). -/
theorem RegularOperatorSetup.pow_eq_one_of_card_omegaInG_le [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) {T : Subgroup R}
    (hcard : Nat.card ↥(omegaInG T p 1) ≤ p ^ (q + 2))
    {x : R} (hx : x ∈ omegaInG T p 1) : x ^ p = 1 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  have hpg : IsPGroup p ↥(omegaInG T p 1) := hyp.R_pGroup.to_subgroup _
  haveI : Group.IsNilpotent ↥(omegaInG T p 1) := hpg.isNilpotent
  have hcl : Group.nilpotencyClass ↥(omegaInG T p 1) ≤ q + 1 :=
    OddOrder.BG.Ch1.S04.nilpotencyClass_le_of_card_le_pow hpg (by omega) hcard
  -- `q + 1 ≤ p − 1`, from Step 1 and the oddness of `p`, `q`
  have hq3 : 3 ≤ q := by
    obtain ⟨k, hk⟩ := hyp.q_odd
    have := hyp.q_prime.two_le
    omega
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := hyp.p_odd
    have := hyp.p_prime.two_le
    omega
  have hqle : q ≤ (p - 1) / 2 :=
    Nat.le_of_dvd (by omega) hyp.card_A_dvd_half_p_sub_one
  have hqp : q + 1 ≤ p - 1 := by omega
  exact pow_eq_one_of_omegaInG
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (hcl.trans hqp)) hx


/-- `Ω_n` of an `A`-invariant subgroup is `A`-invariant.

Via the generating set: an automorphism preserves both `x ∈ H` and `x^{pⁿ} = 1`. -/
theorem isAInvariant_omegaInG {G A : Type*} [Group G] [Group A] {φ : A →* MulAut G}
    {H : Subgroup G} (hH : IsAInvariant φ H) (p n : ℕ) :
    IsAInvariant φ (omegaInG H p n) := fun a => by
  change (omegaInG H p n).map (φ a).toMonoidHom = omegaInG H p n
  rw [omegaInG, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, ⟨hyH, hyp⟩, rfl⟩
    exact ⟨hH.smul_mem a hyH, by rw [← map_pow, hyp, map_one]⟩
  · rintro ⟨hxH, hxp⟩
    exact ⟨(φ a)⁻¹ x, ⟨hH.inv_smul_mem a hxH, by rw [← map_pow, hxp, map_one]⟩,
      MulAut.apply_inv_self G (φ a) x⟩

/-- BG's `v ∈ R₀^#` in the ambient group: a generator of `R₀`, which is nontrivial. -/
theorem RegularOperatorSetup.exists_zpowers_eq_R₀ [Finite R]
    (hyp : RegularOperatorSetup R B p q) :
    ∃ v : R, Subgroup.zpowers v = hyp.R₀ ∧ v ≠ 1 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  have hcard := hyp.R₀_card
  haveI : Nontrivial ↥hyp.R₀ := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro h
    rw [h, Subgroup.card_bot] at hcard
    exact hyp.p_prime.one_lt.ne hcard
  obtain ⟨v, hv⟩ := exists_ne (1 : ↥hyp.R₀)
  have hord : orderOf (v : R) = p := by
    have h1 : orderOf v ∣ Nat.card ↥hyp.R₀ := orderOf_dvd_natCard v
    rw [hyp.R₀_card] at h1
    have h2 : orderOf (v : R) = orderOf v := Subgroup.orderOf_coe v
    rcases (Nat.dvd_prime hyp.p_prime).mp h1 with h | h
    · exact absurd (Subtype.ext (orderOf_eq_one_iff.mp (h2.trans h))) hv
    · exact h2.trans h
  refine ⟨(v : R), Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr v.2)
    (by rw [hyp.R₀_card, Nat.card_zpowers, hord]), fun h1 => hv (Subtype.ext ?_)⟩
  simpa using h1


/-- **BG (E.14)**: `C_S(R₀) = S ∩ (R₀ × R₁) = R₀ × Ω₁(R₁)`, i.e. `S ⊓ C_R(R₀) = seed`.

⚠ This is the route by which BG gets `|C_S(R₀)| = p²` in Step 3 — from `S` **containing the
seed**, not from `r(S) ≥ 3` (which Step 3 never establishes).  Step 2's `(E.4)`
(`centralizer_inf_eq_sup_omega1Center`) reaches the same conclusion under the rank
hypothesis; the two are alternative suppliers.

Both inclusions are immediate: `seed ≤ S` is the family condition and `seed ≤ C_R(R₀)` is
`omega1OfAbelian_le`; conversely an element of `S ⊓ C_R(R₀)` centralizes `R₀` and is killed
by `p` (exponent of `S`), which is exactly membership in the seed. -/
theorem RegularOperatorSetup.inf_centralizer_eq_seed [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hseed : hyp.seed ≤ S)
    (hexp : ∀ x ∈ S, x ^ p = 1) :
    S ⊓ Subgroup.centralizer (hyp.R₀ : Set R) = hyp.seed := by
  refine le_antisymm (fun x hx => ⟨hx.2, hexp x hx.1⟩) (le_inf hseed fun x hx => hx.1)


end OddOrder.BG.AppE
