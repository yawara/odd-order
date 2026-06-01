/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.BG.Ch1_Preliminary.S04c_Prop411
import OddOrder.BG.Ch1_Preliminary.S04d_GorThm415
import OddOrder.BG.Ch1_Preliminary.S04e_GorThm37
import OddOrder.GroupTheory.CentralProduct

/-!
# BG §4F — Blackburn rank-two classification

This downstream leaf hosts the BG §4 endpoint declarations that must see both
`S04_PGroupsSmallRank` and the later Gorenstein precursor files:

* `S04d_GorThm415`: `SCN₃(R)=∅ ⇒ pRank R p ≤ 2`.
* `S04e_GorThm37`: the minimal `p′`-operator subgroup is special of exponent `p`.
* `S04c_Prop411`: Huppert's metacyclic criterion.

Keeping the Blackburn apex here avoids an import cycle: `S04e_GorThm37` imports
`S04_PGroupsSmallRank`, so the final Theorem 4.16 proof cannot live in S04 itself.
-/

open scoped Pointwise commutatorElement

namespace OddOrder.BG.Ch1.S04

open OddOrder.GroupTheory

section AutOrderConstraints

/-! ## §4E: automorphism-order constraints (Lemmas 4.13 and 4.14) -/

/-- **BG Lemma 4.13** (via Gorenstein Theorem 4.15(ii)). Suppose `p` is an odd
prime, `R` is a finite `p`-group, and `q` is a prime divisor of `|Aut R|`. If
`SCN₃(R)` is empty and `q ≠ p`, then `q ∣ p^2 - 1` and `q < p`.

The proof is the remaining assembly of `pRank_le_two_of_scn3_empty`,
`exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction`, and the existing
rank-`≤ 2` linear automorphism bounds in `PRank.lean`. -/
theorem dvd_prime_sq_sub_one_and_lt_of_prime_dvd_aut_of_scn3_empty
    {R : Type*} [Group R] [Finite R] {p q : ℕ} [Fact p.Prime]
    (hp_odd : Odd p) (hR : IsPGroup p R)
    (hSCN : ∀ A : Subgroup R, ¬ IsSCN₃ p A)
    (hq : q.Prime) (hqp : q ≠ p) (hq_dvd : q ∣ Nat.card (MulAut R)) :
    q ∣ p ^ 2 - 1 ∧ q < p := by
  sorry

/-- **BG Lemma 4.14.** Under the hypotheses of Lemma 4.13, `q` divides one of the
half-factors `(p + 1) / 2` or `(p - 1) / 2`.

BG derives this from Lemma 4.13 and the factorization
`p^2 - 1 = 4 * ((p - 1) / 2) * ((p + 1) / 2)` for odd `p`; the `q = 2` case is
absorbed by the same parity split. -/
theorem dvd_half_prime_add_or_sub_of_prime_dvd_aut_of_scn3_empty
    {R : Type*} [Group R] [Finite R] {p q : ℕ} [Fact p.Prime]
    (hp_odd : Odd p) (hR : IsPGroup p R)
    (hSCN : ∀ A : Subgroup R, ¬ IsSCN₃ p A)
    (hq : q.Prime) (hqp : q ≠ p) (hq_dvd : q ∣ Nat.card (MulAut R)) :
    q ∣ (p + 1) / 2 ∨ q ∣ (p - 1) / 2 := by
  sorry

end AutOrderConstraints

section BlackburnClassification

/-! ## §4F: Blackburn rank-two classification (Theorem 4.16)

The current declaration makes the BG Theorem 4.16 endpoint visible in Lean.
Its proof is the remaining Blackburn apex of issue 0051; the statement is kept
close to the printed theorem:

* `A` is represented by an operator action `φ : A →* MulAut R`.
* "`A` is a `p'`-group of automorphisms" is represented in the repo's standard
  coprime-action form `Nat.Coprime (Nat.card A) (Nat.card R)`.
* `[R,A]=R` is `OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤`.
* `R = R₁ ∘ R₂` is the internal central product
  `IsCentralProduct (⊤ : Subgroup R) R₁ R₂`.
-/

/-- **BG Theorem 4.16, case (2)** (Blackburn): `R` is the central product
`R₁ ∘ R₂`, where `R₁` is nonabelian of order `p^3` and exponent `p`, `R₂` is
cyclic, and `Ω₁(R₂) = R₁'`.

The equality `Ω₁(R₂) = R₁'` is stated after mapping both subgroups into the
ambient group `R`: `Ω₁(R₂)` is `(Omega R₂ p 1).map R₂.subtype`, and `R₁'` is
`(commutator R₁).map R₁.subtype`. -/
def BlackburnCentralProductCase (p : ℕ) (R : Type*) [Group R] : Prop :=
  ∃ R₁ R₂ : Subgroup R,
    IsCentralProduct (⊤ : Subgroup R) R₁ R₂ ∧
      ¬ IsMulCommutative ↥R₁ ∧
      Nat.card ↥R₁ = p ^ 3 ∧
      Monoid.exponent ↥R₁ = p ∧
      IsCyclic ↥R₂ ∧
      (Omega ↥R₂ p 1).map R₂.subtype =
        (_root_.commutator ↥R₁).map R₁.subtype

/-- **BG Theorem 4.16** (Blackburn rank-two classification).

Let `p` be an odd prime, `R` a nonidentity finite `p`-group, and `A` a
`p'`-group of automorphisms of `R`.  If `r(R) ≤ 2`, `[R,A]=R`, and `|A|` is odd,
then `p > 3` and either `R` is abelian, or `R` is a central product
`R₁ ∘ R₂` where `R₁` is nonabelian of order `p^3` and exponent `p`, `R₂` is
cyclic, and `Ω₁(R₂)=R₁'`.

In Lean, because `R` is a `p`-group, BG's rank hypothesis `r(R) ≤ 2` is represented
as `pRank R p ≤ 2`; see the §4C comments above `scn3_empty_of_pRank_le_two`.
The proof is intentionally still `sorry`: this declaration makes the missing
Blackburn apex visible to the mainline `sorry` census and downstream dependencies. -/
theorem blackburnRankTwoClassification
    {R : Type*} [Group R] [Finite R] [Nontrivial R]
    {p : ℕ} [Fact p.Prime] (hp_odd : Odd p) (hR : IsPGroup p R)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    (hrank : pRank R p ≤ 2)
    (hRA : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤)
    (hAodd : Odd (Nat.card A)) :
    3 < p ∧ (IsMulCommutative R ∨ BlackburnCentralProductCase p R) := by
  sorry

end BlackburnClassification

end OddOrder.BG.Ch1.S04
