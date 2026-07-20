/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_SemidirectFrattini

/-!
# BG Appendix E, Proposition E.4: `C_S(Z₂(S))` is abelian of index `p`

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, pp. 162–164.

> **Proposition E.4.**  Assume the situation of Theorem E.3 and let `S = Ω₁(R)`.  Suppose
> `|S| ≥ p⁴`, `B` acts regularly on `R`, and `B` does not fix `R₀`.  Then `C_S(Z₂(S))` is
> abelian and has index `p` in `S`.

BG's proof opens by collecting, from Theorem E.3,

> `S` has exponent `p`, `|S/S'| = p²`, `|S| ≤ p^q`, and `B` does not fix `R₀Φ(S)`  (E.18)

— the last clause being exactly the **contrapositive of E.3(d)**, which is why the
proposition is gated on Step 4.  The index clause is then Step 2's `|S : T| = p`; the hard
half is that `T = C_S(Z₂(S))` is abelian, proved by contradiction inside the two-dimensional
`𝔽_p`-space `S/S'`, comparing the eigenvalues `r, r₀` of `α` on `R₀S'/S'` and `T/S'` with
the eigenvalues `t, t₀` of `β` on a `B`-invariant complement `Q/S'` and on `T/S'`.

## Naming

Step 2 spells BG's `T = C_S(Z₂(S))` as `C_S(Ω₁(Z₂(S)))`, because Lemma 5.2 (which supplies
`|S : T| = p`) is stated for the narrow-`p`-group subgroup `W = Ω₁(Z₂(S))`.  The two agree
here since `S` has exponent `p`; `omega1UpperCentralTwo_eq_upperCentralSeries` is that
bridge, and it is what lets the proposition be *stated* with BG's `Z₂(S)`.
-/

namespace OddOrder.BG.AppE

open OddOrder.GroupTheory OddOrder.Isaacs.Ch03
open scoped commutatorElement Pointwise

variable {R B : Type*} [Group R] [Group B] {p q : ℕ}

/-! ## `Ω₁(Z₂(S)) = Z₂(S)` for exponent-`p` `S` -/

/-- In a group of exponent `p`, `Ω₁(Z₂(S))` is all of `Z₂(S)`.

Step 2 works with `C_S(Ω₁(Z₂(S)))` because Lemma 5.2 is phrased for the narrow-group
subgroup `W = Ω₁(Z₂(S))`; BG's Proposition E.4 says `C_S(Z₂(S))`.  Under the exponent-`p`
hypothesis carried by `S = Ω₁(R)` (E.3(b), first clause) the two subgroups coincide, so the
two names describe the same `T`. -/
theorem omega1UpperCentralTwo_eq_upperCentralSeries {G : Type*} [Group G] {p : ℕ}
    (hexp : ∀ x : G, x ^ p = 1) :
    omega1UpperCentralTwo G p = Subgroup.upperCentralSeries G 2 := by
  refine le_antisymm (omega1UpperCentralTwo_le G p) fun x hx => ?_
  refine ⟨⟨x, hx⟩, Omega.mem_of_pow_eq_one ?_, rfl⟩
  exact Subtype.ext (by simpa using hexp x)

/-- `C_S(Z₂(S)) = C_S(Ω₁(Z₂(S)))` for `S` of exponent `p` — the centralizer form of
`omega1UpperCentralTwo_eq_upperCentralSeries`, which is how Step 2's `T` enters. -/
theorem centralizer_upperCentralSeries_eq_centralizer_omega1 {G : Type*} [Group G] {p : ℕ}
    (hexp : ∀ x : G, x ^ p = 1) :
    Subgroup.centralizer ((Subgroup.upperCentralSeries G 2 : Subgroup G) : Set G) =
      Subgroup.centralizer (omega1UpperCentralTwo G p : Set G) := by
  rw [omega1UpperCentralTwo_eq_upperCentralSeries hexp]

/-! ## `(E.18)`: `B` does not fix `R₀Φ(S)` -/

/-- **BG `(E.18)`, last clause**: if `B` does not fix `R₀` then `B` does not fix `R₀Φ(Ω₁(R))`.

This is the contrapositive of Theorem E.3(d) (`B_fixes_R₀_of_fixes_frattini`), and it is the
only place Proposition E.4 uses Step 4. -/
theorem RegularOperatorSetup.not_fixes_sup_frattini_of_not_fixes_R₀ [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q)
    (hB : ¬ ∀ b : B, (hyp.act b) • hyp.R₀ = hyp.R₀) :
    ¬ ∀ b : B, (hyp.act b) • (hyp.R₀ ⊔ frattiniInG (Omega R p 1)) =
      hyp.R₀ ⊔ frattiniInG (Omega R p 1) :=
  fun h => hB (hyp.B_fixes_R₀_of_fixes_frattini h)

/-! ## The index clause of Proposition E.4 -/

/-- `3 ≤ r(Ω₁(R))` under BG's `|S| ≥ p⁴`.

Step 2's results are all conditioned on `p`-rank at least `3`; Proposition E.4 supplies that
through its cardinality hypothesis, since an exponent-`p` group of `p`-rank `≤ 2` has order
at most `p³` (`three_le_pRank_of_prime_cube_lt_card`). -/
theorem RegularOperatorSetup.three_le_pRank_omega [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) (hcard : p ^ 4 ≤ Nat.card ↥(Omega R p 1)) :
    3 ≤ pRank ↥(Omega R p 1) p := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  refine three_le_pRank_of_prime_cube_lt_card (hyp.R_pGroup.to_subgroup _)
    hyp.omega_pow_eq_one' (lt_of_lt_of_le ?_ hcard)
  exact Nat.pow_lt_pow_right hyp.p_prime.one_lt (by omega)

/-- **BG Proposition E.4, index clause**: `|S : C_S(Z₂(S))| = p`.

Step 2's `|S : T| = p` (`card_omega1Center_and_index_centralizer`, out of Lemma 5.2 applied
inside the narrow group `S`), transported along
`centralizer_upperCentralSeries_eq_centralizer_omega1`.

⚠ Only `|S| ≥ p⁴` is used — neither the regularity of `B` nor `B ⊄ N(R₀)` enters.  BG lists
all three hypotheses for the proposition as a whole; the abelianness clause is what consumes
the other two. -/
theorem RegularOperatorSetup.index_centralizer_upperCentralSeries [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) (hcard : p ^ 4 ≤ Nat.card ↥(Omega R p 1)) :
    (Subgroup.centralizer
        ((Subgroup.upperCentralSeries ↥(Omega R p 1) 2 : Subgroup ↥(Omega R p 1)) :
          Set ↥(Omega R p 1))).index = p := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  rw [centralizer_upperCentralSeries_eq_centralizer_omega1 (p := p) hyp.omega_pow_eq_one']
  exact (hyp.card_omega1Center_and_index_centralizer hyp.R₀_le_omega
    (hyp.three_le_pRank_omega hcard)).2

end OddOrder.BG.AppE
