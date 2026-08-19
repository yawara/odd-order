/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerTrichotomy
import OddOrder.Peterfalvi.Appendices.Suzuki.Q1MinimalInvariant

/-!
# Peterfalvi Part II, Ch. III: hypothesis (C1) and the action of `D` on `Q₁`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III, §1, p. 115.

Chapter III assumes, on top of the Chapter I axioms (A1)–(A3):

**(C1)** the subgroup `V` is non-trivial, and `C_G(P)` has 2-rank `≥ 2`
for every subgroup `P` of `V` of prime order.

(The excluded configurations are covered elsewhere: `V = 1` makes `G` a
Zassenhaus group, and a prime-order `P ≤ V` with `C_G(P)` of 2-rank one
is hypothesis (B1) of Chapter II, settled by Theorem B.)

This leaf derives the opening step of the proof of Theorem C: **`D` acts
fixed-point-freely on `Q₁`**.  For a prime-order `P ≤ D` the book splits on
the number of fixed points of `P` on `Ω`; since `|Ω_P| = |C_Q(P)| + 1`
(Ch. I §1, Proposition 6), that split is exactly whether `C_Q(P)` is
trivial:

* `|Ω_P| = 2`, i.e. `C_Q(P) = 1` — then a fortiori `C_{Q₁}(P) = 1`;
* `|Ω_P| ≥ 3` — then `P` is conjugate in `D` to a subgroup of `V`
  (Ch. I §1, Proposition 6(c)), where (C1) feeds the 2-rank input of
  Ch. I §3, Proposition 1(c) and yields `C_{Q₁}(P) = 1`.

Fixed-point-freeness for arbitrary `g ∈ D^#` follows by passing to a
subgroup of prime order of `⟨g⟩`, which centralizes whatever `g`
centralizes.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open MulAction

universe uG uΩ

/-- **Peterfalvi Part II, Ch. III, hypothesis (C1)** (p. 115): the Chapter I
axioms together with `V ≠ 1` and the requirement that `C_G(P)` have 2-rank at
least two for every prime-order subgroup `P` of `V`.

"2-rank at least two" is recorded in the form consumed by Ch. I §3,
Proposition 1(c): the centralizer contains a four-subgroup. -/
structure SecondCaseHypothesis (G : Type uG) (Ω : Type uΩ) [Group G]
    [MulAction G Ω] [Finite G] extends Hypothesis G Ω where
  /-- (C1), first clause: `V ≠ 1` -/
  V_ne_bot : toHypothesis.V ≠ ⊥
  /-- (C1), second clause: `C_G(P)` has 2-rank `≥ 2` for prime-order `P ≤ V` -/
  twoRank_centralizer_ge_two : ∀ P : Subgroup G, P ≤ toHypothesis.V →
    ∀ p : ℕ, p.Prime → Nat.card ↥P = p →
      ∃ E : Subgroup ↥(Subgroup.centralizer (P : Set G)),
        Nat.card ↥E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1

namespace Hypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- **Peterfalvi Part II, Ch. I §3, Proposition 1(c)**, in the single form used
by Chapter III: for a non-trivial `X ≤ V` whose centralizer has 2-rank at least
two, `C_{Q₁}(X) = 1`.

This is the `q1_inf_centralizer_eq_bot` field of the trichotomy data, extracted
so that callers need not carry the centralizer-quotient action instance. -/
theorem Q1_inf_centralizer_eq_bot_of_le_V {X : Subgroup G} (hXV : X ≤ hyp.V)
    (hX : X ≠ ⊥)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer (X : Set G)),
      Nat.card ↥E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (ind : TheoremAInductionBelow G Ω) :
    hyp.Q1 ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  let := hyp.centralizerQuotientMulAction hXV
  obtain ⟨data⟩ := hyp.centralizer_trichotomy_of_induction hXV hX hA3 ind
  exact data.common.q1_inf_centralizer_eq_bot

/-- **Peterfalvi Part II, Ch. III, Theorem C, step 2** (p. 115): `Q ∩ Q^x = 1` for
`x ∈ G − H`, i.e. `Q` has trivial intersections in `G`.

The book's one-line argument: `Q ∩ Q^x ⊆ Q ∩ (H ∩ H^x) = 1`, because `H ∩ H^x` is
conjugate to `D` in `H` (Ch. I §1, Proposition 1(a)) and `Q ∩ D = 1`.  Conjugating
by the element `h ∈ H` that realises `(H^x ∩ H)^h = D` keeps the element inside `Q`
(`Q ⊴ H`) and lands it in `D`, so it is trivial. -/
theorem Q_inf_map_conj_eq_bot {x : G} (hx : x ∉ hyp.H) :
    hyp.Q ⊓ hyp.Q.map (MulAut.conj x).toMonoidHom = ⊥ := by
  obtain ⟨h, hhH, heq⟩ := hyp.exists_mem_H_conj_inf_eq_D hx
  refine le_bot_iff.mp fun y hy => ?_
  obtain ⟨hyQ, hyQx⟩ := Subgroup.mem_inf.mp hy
  have hyH : y ∈ hyp.H := hyp.Q_le_H hyQ
  have hyHx : y ∈ hyp.H.map (MulAut.conj x).toMonoidHom := by
    obtain ⟨z, hz, rfl⟩ := hyQx
    exact ⟨z, hyp.Q_le_H hz, rfl⟩
  have hmemD : h * y * h⁻¹ ∈ hyp.D := by
    rw [← heq]
    exact ⟨y, Subgroup.mem_inf.mpr ⟨hyHx, hyH⟩, rfl⟩
  have hmemQ : h * y * h⁻¹ ∈ hyp.Q := hyp.Q_normal_in_H h hhH y hyQ
  have hmem : h * y * h⁻¹ ∈ hyp.Q ⊓ hyp.D := Subgroup.mem_inf.mpr ⟨hmemQ, hmemD⟩
  rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  calc y = h⁻¹ * (h * y * h⁻¹) * h := by group
    _ = h⁻¹ * 1 * h := by rw [hmem]
    _ = 1 := by group

end Hypothesis

namespace SecondCaseHypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (sc : SecondCaseHypothesis G Ω)

/-- A prime-order subgroup of `D` with a non-trivial fixed-point set on `Q`
has at least three fixed points on `Ω`, by `|Ω_X| = |C_Q(X)| + 1`. -/
theorem three_le_ncard_fixedPoints_of_cQ_ne_bot {P : Subgroup G}
    (hPD : P ≤ sc.toHypothesis.D)
    (hcQ : sc.toHypothesis.Q ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥) :
    3 ≤ (fixedPoints P Ω).ncard := by
  rw [sc.toHypothesis.ncard_fixedPoints hPD]
  have h2 : 2 ≤ Nat.card ↥(sc.toHypothesis.Q ⊓ Subgroup.centralizer (P : Set G)) := by
    rcases Nat.lt_or_ge (Nat.card ↥(sc.toHypothesis.Q ⊓
      Subgroup.centralizer (P : Set G))) 2 with hlt | hge
    · exact absurd (Subgroup.eq_bot_of_card_le _ (by omega)) hcQ
    · exact hge
  omega

/-- **Peterfalvi Part II, Ch. III, Theorem C, step 1** (p. 115): for a subgroup
`P ≤ D` of prime order, `C_{Q₁}(P) = 1`.

If `C_Q(P) = 1` there is nothing to prove.  Otherwise `P` has at least three
fixed points on `Ω`, hence is conjugate in `D` to a subgroup `X ≤ V`
(Ch. I §1, Proposition 6(c)); (C1) supplies the 2-rank input for `X` and
Ch. I §3, Proposition 1(c) gives `C_{Q₁}(X) = 1`, which transports back along
the conjugation (`Q₁` is normalized by `D ≤ H`). -/
theorem Q1_inf_centralizer_eq_bot_of_prime_le_D (ind : Hypothesis.TheoremAInductionBelow G Ω)
    {P : Subgroup G} (hPD : P ≤ sc.toHypothesis.D) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card ↥P = p) :
    sc.toHypothesis.Q1 ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  set hyp := sc.toHypothesis with hhyp
  by_cases hcQ : hyp.Q ⊓ Subgroup.centralizer (P : Set G) = ⊥
  · -- `|Ω_P| = 2`: already `C_Q(P) = 1`
    refine le_bot_iff.mp ?_
    rw [← hcQ]
    exact inf_le_inf_right _ hyp.Q1_le_Q
  -- `|Ω_P| ≥ 3`: conjugate `P` into `V`
  obtain ⟨k, hkD, hkV⟩ :=
    hyp.exists_conj_mem_D_map_le_V hPD (sc.three_le_ncard_fixedPoints_of_cQ_ne_bot hPD hcQ)
  set X : Subgroup G := P.map (MulAut.conj k).toMonoidHom with hX
  have hcardX : Nat.card ↥X = p := by
    rw [hX, ← hcard]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective P _ (MulAut.conj k).injective).toEquiv.symm
  have hXne : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardX
    exact hp.one_lt.ne' hcardX.symm
  have hbot := hyp.Q1_inf_centralizer_eq_bot_of_le_V hkV hXne
    (sc.twoRank_centralizer_ge_two X hkV p hp hcardX) ind
  -- transport: conjugation by `k ∈ D ≤ H` preserves `Q₁` and moves `C_G(P)` to `C_G(X)`
  refine le_bot_iff.mp fun x hx => ?_
  obtain ⟨hxQ1, hxc⟩ := Subgroup.mem_inf.mp hx
  have hkH : k ∈ hyp.H := hyp.D_le_H hkD
  have hconjQ1 : k * x * k⁻¹ ∈ hyp.Q1 := hyp.conj_mem_Q1_of_mem_H hkH hxQ1
  have hconjc : k * x * k⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨z, hz, rfl⟩
    have hcomm : z * x = x * z := Subgroup.mem_centralizer_iff.mp hxc z hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k * z * k⁻¹ * (k * x * k⁻¹) = k * (z * x) * k⁻¹ := by group
      _ = k * (x * z) * k⁻¹ := by rw [hcomm]
      _ = k * x * k⁻¹ * (k * z * k⁻¹) := by group
  have hmem : k * x * k⁻¹ ∈ hyp.Q1 ⊓ Subgroup.centralizer (X : Set G) :=
    Subgroup.mem_inf.mpr ⟨hconjQ1, hconjc⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have hx1 : x = 1 := by
    have h2 : k⁻¹ * (k * x * k⁻¹) * k = k⁻¹ * 1 * k := by rw [hmem]
    calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
      _ = k⁻¹ * 1 * k := h2
      _ = 1 := by group
  rw [Subgroup.mem_bot]
  exact hx1

/-- **Peterfalvi Part II, Ch. III, Theorem C, step 1** (p. 115), the form fed to
the Feit–Sibley hypothesis: `D` acts on `Q₁` without fixed points.

A non-trivial `g ∈ D` has a power of prime order generating a subgroup `P ≤ D`
that centralizes everything `g` centralizes, so the prime-order case applies. -/
theorem D_fixedPointFree_on_Q1 (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    ∀ g ∈ sc.toHypothesis.D, g ≠ 1 →
      ∀ x ∈ sc.toHypothesis.Q1, g * x * g⁻¹ = x → x = 1 := by
  intro g hgD hg1 x hxQ1 hfix
  have hord : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hord
  have hpos : 0 < orderOf g := orderOf_pos g
  have hmpos : 0 < orderOf g / p := Nat.div_pos (Nat.le_of_dvd hpos hpdvd) hp.pos
  have hmdvd : (orderOf g / p) ∣ orderOf g := Nat.div_dvd_of_dvd hpdvd
  have hyord : orderOf (g ^ (orderOf g / p)) = p := by
    rw [orderOf_pow_of_dvd hmpos.ne' hmdvd]
    exact Nat.div_div_self hpdvd hpos.ne'
  have hcardP : Nat.card ↥(Subgroup.zpowers (g ^ (orderOf g / p))) = p := by
    rw [Nat.card_zpowers, hyord]
  have hPD : Subgroup.zpowers (g ^ (orderOf g / p)) ≤ sc.toHypothesis.D := by
    rw [Subgroup.zpowers_le]
    exact pow_mem hgD _
  have hcomm : Commute (g ^ (orderOf g / p)) x := by
    refine Commute.pow_left ?_ _
    calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [hfix]
  have hxc : x ∈ Subgroup.centralizer
      ((Subgroup.zpowers (g ^ (orderOf g / p)) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact hcomm.zpow_left n
  have hmem : x ∈ sc.toHypothesis.Q1 ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (g ^ (orderOf g / p)) : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨hxQ1, hxc⟩
  rw [sc.Q1_inf_centralizer_eq_bot_of_prime_le_D ind hPD hp hcardP,
    Subgroup.mem_bot] at hmem
  exact hmem

end SecondCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
