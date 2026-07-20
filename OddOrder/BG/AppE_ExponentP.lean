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

end OddOrder.BG.AppE
