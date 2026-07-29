/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.Trichotomy
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.PSUCentre
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.WielandtOnQ
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.HilbertNinetyOnQ

/-!
# Case (3) of the Ch. III §1 Proposition: `W ≠ 1`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §1, Proposition, p. 117, end of case (3):

> Suppose that `W = 1`.  Then, as in case (2), `C_V(C_{Q₀}(P)) = P`, `F/Z(F)` is
> not isomorphic to `PSU(3, ℓ)` and the case in which `C_S(P)` is elementary
> abelian holds since `st` has order `3`.  But `[K, P] ⋊ P` is a Frobenius group
> acting on `S/Q₀` and `[K, P]` acts without fixed points on `S/Q₀`, whence
> `C_{S/Q₀}(P) ≠ 1` and we obtain a contradiction.  Thus, `W ≠ 1`.

Assuming `W = 1`, the three alternatives of Ch. I §3 Proposition 1(c) at a
prime-order `P ≤ V` are all refuted:

* `Sz(ℓ)` carries `orderOf (st) = 5`, while case (3) has `orderOf (st) = 3`
  (`orderOf_st_eq_three_of_card_cube`);
* `PSU(3, ℓ)` is refuted by the book's deferred computation, discharged in
  `PSUCentre.lean` (`CentralizerPSUData.false_of_W_eq_bot`);
* `PSL(2, ℓ)` splits on whether `p` divides `q₀ − 1` (`q₀ = |C_{Q₀}(P)|`, and
  `|Q₀| = q₀ ^ p` by Artin).  If it does not, the book's Frobenius route is
  available and Wielandt's formula gives `|Q| = |Q₀|`
  (`false_of_natCard_cQ_eq_cQ0_of_card_cube`).  If it does, then `p ∤ q + 1`,
  and Hilbert 90 on a `K`-orbit of `S/Q₀` produces an element of `C_Q(P)`
  outside `Q₀` (`exists_mem_inf_centralizer_not_mem_Q0_of_card_cube`), against
  `C_Q(P) = C_{Q₀}(P)`.

⚠ The book asserts the Frobenius property of `[K, P] ⋊ P` unconditionally;
that is equivalent to `p ∤ q₀ − 1` and genuinely fails otherwise (issue 0164).

## Main results

* `SecondCaseHypothesis.W_ne_bot_of_card_cube` — case (3) forces `W ≠ 1`.
* `SecondCaseHypothesis.trichotomy` — the Proposition itself, now with no
  hypothesis left over.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

universe uG uΩ

namespace SecondCaseHypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (sc : SecondCaseHypothesis G Ω)

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (3): `W ≠ 1`**
(p. 117).

The three alternatives of Ch. I §3 Proposition 1(c) at a prime-order `P ≤ V`
are refuted one by one under `W = 1`; see the module docstring. -/
theorem W_ne_bot_of_card_cube
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥sc.toHypothesis.Q)
    {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥sc.toHypothesis.Q0 = 2 ^ m)
    (hcardQ : Nat.card ↥sc.toHypothesis.Q = Nat.card ↥sc.toHypothesis.Q0 ^ 3) :
    sc.toHypothesis.W ≠ ⊥ := by
  classical
  intro hW
  obtain ⟨P, p, hp, hPcard, hPV⟩ := exists_le_card_eq_prime sc.V_ne_bot
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact hp.one_lt.ne hPcard
  have hst := sc.orderOf_st_eq_three_of_card_cube ind hQsuz hm hQ0card hcardQ
    hp hPcard hPV
  have hQ2 : IsPGroup 2 ↥sc.toHypothesis.Q := sc.isPGroup_two_Q ind
  -- `p` is odd: `P ≤ V ≤ D` and `D` has odd order
  have hpodd : p ≠ 2 := by
    intro h
    have hdvd : Nat.card ↥P ∣ Nat.card ↥sc.toHypothesis.D :=
      Subgroup.card_dvd_of_le (hPV.trans sc.toHypothesis.V_le_D)
    have hodd : Odd (Nat.card ↥P) := sc.toHypothesis.D_odd.of_dvd_nat hdvd
    rw [hPcard, h] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd
  letI := sc.toHypothesis.centralizerQuotientMulAction hPV
  obtain ⟨data⟩ := sc.toHypothesis.centralizer_trichotomy_of_induction hPV hPne
    (sc.twoRank_centralizer_ge_two P hPV p hp hPcard) ind
  rcases data.branch with ⟨d, -, det⟩ | ⟨d, -, det⟩ | ⟨d, -, det⟩
  · -- `PSL(2, ℓ)`
    set C : Subgroup G := Subgroup.centralizer (P : Set G) with hCdef
    -- `|C_Q(P)| = |C_{Q₀}(P)|`
    have hsub : ∀ N : Subgroup G, Nat.card ↥(N.subgroupOf C) = Nat.card ↥(N ⊓ C) := by
      intro N
      rw [← Subgroup.inf_subgroupOf_right]
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ C ≤ C)).toEquiv
    have heq : Nat.card ↥(sc.toHypothesis.Q ⊓ C)
        = Nat.card ↥(sc.toHypothesis.Q0 ⊓ C) := by
      rw [← hsub, ← hsub, det.natCard_cQ_eq_field, det.natCard_cQ0_eq_field]
    -- Artin: `|Q₀| = q₀ ^ p`
    set q₀ : ℕ := Nat.card ↥(sc.toHypothesis.Q0 ⊓ C) with hq₀def
    have hQ0pow : Nat.card ↥sc.toHypothesis.Q0 = q₀ ^ p := by
      have h := sc.toHypothesis.natCard_Q0_eq_pow_of_W_eq_bot hW hPV
      rwa [hPcard] at h
    by_cases hdvd : p ∣ q₀ - 1
    · -- `p ∣ q₀ − 1`: then `p ∤ q + 1`, and Hilbert 90 on a `K`-orbit applies
      have hq₀pos : 0 < q₀ := Nat.card_pos
      have hQ0pos : 0 < Nat.card ↥sc.toHypothesis.Q0 := Nat.card_pos
      have hdvd' : p ∣ Nat.card ↥sc.toHypothesis.Q0 - 1 := by
        rw [hQ0pow]
        exact hdvd.trans (Nat.sub_one_dvd_pow_sub_one q₀ p)
      have hnd : ¬ p ∣ Nat.card ↥sc.toHypothesis.Q0 + 1 := by
        intro hd2
        have h2 : p ∣ 2 := by
          have := Nat.dvd_sub hd2 hdvd'
          rwa [show Nat.card ↥sc.toHypothesis.Q0 + 1 -
            (Nat.card ↥sc.toHypothesis.Q0 - 1) = 2 by omega] at this
        exact hpodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      obtain ⟨y, hyQC, hyQ0⟩ :=
        sc.toHypothesis.exists_mem_inf_centralizer_not_mem_Q0_of_card_cube hQsuz hm
          hQ0card hcardQ hW hPV hp hPcard hnd
      -- `C_Q(P) = C_{Q₀}(P)` in this branch, so `y` cannot avoid `Q₀`
      refine hyQ0 ?_
      have hEq : sc.toHypothesis.Q0 ⊓ C = sc.toHypothesis.Q ⊓ C :=
        Subgroup.eq_of_le_of_card_ge
          (inf_le_inf_right C sc.toHypothesis.Q0_le_Q) heq.le
      have hy0 : y ∈ sc.toHypothesis.Q0 ⊓ C := by rw [hEq]; exact hyQC
      exact hy0.1
    · -- `p ∤ q₀ − 1`: the book's Frobenius route, via Wielandt's formula
      have hcop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥sc.toHypothesis.K) := by
        rw [hPcard]
        exact sc.toHypothesis.coprime_natCard_K_of_not_dvd hp Nat.card_pos hQ0pow hdvd
      exact sc.toHypothesis.false_of_natCard_cQ_eq_cQ0_of_card_cube hW hPV hPne
        (by rw [hPcard]; exact hp) hcop hQ2 hcardQ heq
  · -- `Sz(ℓ)`: `orderOf (st) = 5` against `orderOf (st) = 3`
    rw [det.distinguishedProduct_order] at hst
    omega
  · -- `PSU(3, ℓ)`: the book's deferred computation
    exact det.false_of_W_eq_bot hPV hW data.common

/-- **Peterfalvi Part II, Ch. III §1, Proposition** (pp. 116–117).

> One of the following three cases holds.
> (a) `S = Q₀` and `st` has order `3`.
> (b) `S` is a Suzuki `2`-group of type A, `st` has order `5` and `W = 1`.
> (c) `S` is a Suzuki `2`-group of type B, `st` has order `3` and `W ≠ 1`.

`S = Q` after Theorem C (`sylowTwoOfQ_eq_Q`).  The case split is Ch. I §2's
"either `S` is abelian or `S` is a Suzuki `2`-group"
(`isMulCommutative_or_isSuzuki2Group_Q`) refined by Appendix III's two possible
orders `|Q₀|²` and `|Q₀|³` (`natCard_Q_eq_sq_or_cube`).

The `W ≠ 1` clause of case (c) is `W_ne_bot_of_card_cube`; it subsumes both the
book's deferred `PSU(3, ℓ)` computation ("as can be checked") and the repair of
its `PSL(2, ℓ)` argument (issue 0164). -/
theorem trichotomy (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    (sc.toHypothesis.Q = sc.toHypothesis.Q0 ∧
        orderOf (sc.toHypothesis.distinguishedInvolution * sc.toHypothesis.t) = 3)
      ∨ (Suzuki2Groups.IsTypeA.{uG, 0} ↥sc.toHypothesis.Q ∧
        orderOf (sc.toHypothesis.distinguishedInvolution * sc.toHypothesis.t) = 5 ∧
        sc.toHypothesis.W = ⊥)
      ∨ (Suzuki2Groups.IsTypeB.{uG, 0} ↥sc.toHypothesis.Q ∧
        orderOf (sc.toHypothesis.distinguishedInvolution * sc.toHypothesis.t) = 3 ∧
        sc.toHypothesis.W ≠ ⊥) := by
  classical
  have hQ2 : IsPGroup 2 ↥sc.toHypothesis.Q := sc.isPGroup_two_Q ind
  obtain ⟨m, hQ0card⟩ := (hQ2.to_le sc.toHypothesis.Q0_le_Q).exists_card_eq
  have hm : m ≠ 0 := by
    intro h
    have h2 := sc.toHypothesis.two_le_card_Q0
    rw [hQ0card, h, pow_zero] at h2
    omega
  rcases sc.isMulCommutative_or_isSuzuki2Group_Q ind with hcomm | hQsuz
  · -- (1) `S` abelian
    have hc : ∀ a ∈ sc.toHypothesis.Q, ∀ b ∈ sc.toHypothesis.Q, Commute a b := by
      intro a ha b hb
      exact congrArg (Subtype.val (p := fun z => z ∈ sc.toHypothesis.Q))
        (hcomm.1.comm (⟨a, ha⟩ : ↥sc.toHypothesis.Q) ⟨b, hb⟩)
    exact Or.inl (sc.Q_eq_Q0_and_orderOf_st_of_commute ind hQ2 hc)
  · obtain ⟨P, p, hp, hPcard, hPV⟩ := exists_le_card_eq_prime sc.V_ne_bot
    rcases sc.toHypothesis.natCard_Q_eq_sq_or_cube hQsuz with hsq | hcube
    · -- (2) `S` non-abelian of order `q²`
      exact Or.inr (Or.inl ⟨sc.toHypothesis.isTypeA_of_natCard_eq_sq hQsuz hsq,
        sc.orderOf_st_eq_five_of_isSuzuki2Group ind hQsuz hsq hp hPcard hPV,
        sc.W_eq_bot_of_isSuzuki2Group hQsuz hsq⟩)
    · -- (3) `S` non-abelian of order `q³`
      have hst := sc.orderOf_st_eq_three_of_card_cube ind hQsuz hm hQ0card hcube
        hp hPcard hPV
      have hW := sc.W_ne_bot_of_card_cube ind hQsuz hm hQ0card hcube
      obtain ⟨-, -, hB⟩ := sc.toHypothesis.lemmaFive_of_orderThree hst hQsuz hm
        hQ0card hcube ind
      exact Or.inr (Or.inr ⟨hB hW, hst, hW⟩)

end SecondCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
