/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.SemilinearRealization
import OddOrder.Peterfalvi.Appendices.Suzuki.OrderThreeSuzukiCentralizer

/-!
# Peterfalvi Part II, Ch. II: hypothesis (B1) and first consequences

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, p. 108.

Chapter II assumes, on top of the Chapter I axioms (A1)–(A3):

**(B1)** the subgroup `V` contains a subgroup `P` of prime order `p` such
that `C_G(P)` has 2-rank 1.

This leaf defines the hypothesis carrier and derives the first
consequences used throughout the chapter: `p` is odd, `P` meets `W`
trivially (else `Q₀ ⊆ C_G(P)` would contain a four-subgroup), and the
fixed points of `P` on `Q₀` form an elementary abelian group of order at
most `2`.

Since `t ∈ C_G(P)` is an involution, the 2-rank of `C_G(P)` is at least
one; hypothesis (B1) is therefore recorded in the usable direction: every
elementary abelian `2`-subgroup of `C_G(P)` has order at most `2`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

universe uG uΩ

/-- **Peterfalvi Part II, Ch. II, hypothesis (B1)** (p. 108): the Chapter I
axioms together with a subgroup `P ≤ V` of prime order `p` whose centralizer
has 2-rank one. -/
structure FirstCaseHypothesis (G : Type uG) (Ω : Type uΩ) [Group G]
    [MulAction G Ω] [Finite G] extends Hypothesis G Ω where
  /-- the distinguished subgroup of prime order -/
  P : Subgroup G
  /-- the prime `p` -/
  p : ℕ
  p_prime : p.Prime
  P_le_V : P ≤ toHypothesis.V
  card_P : Nat.card ↥P = p
  /-- `C_G(P)` has 2-rank one: every elementary abelian `2`-subgroup of the
  centralizer has order at most `2`. -/
  twoRank_centralizer_le_one : ∀ E : Subgroup G,
    E ≤ Subgroup.centralizer (P : Set G) → (∀ x ∈ E, x ^ 2 = 1) →
    Nat.card ↥E ≤ 2

namespace FirstCaseHypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- The prime `p` is odd: `P ≤ V ≤ D` and `D` has odd order. -/
theorem p_odd : Odd fc.p := by
  rw [← fc.card_P]
  exact fc.toHypothesis.D_odd.of_dvd_nat
    (Subgroup.card_dvd_of_le
      (fc.P_le_V.trans fc.toHypothesis.V_le_D))

theorem p_ne_two : fc.p ≠ 2 := by
  intro h
  have := fc.p_odd
  rw [h] at this
  exact (Nat.not_odd_iff_even.mpr even_two) this

/-- Elements of `W` centralize `Q₀` elementwise. -/
theorem W_mem_centralizes_Q0 {w : G} (hw : w ∈ fc.toHypothesis.W)
    {x : G} (hx : x ∈ fc.toHypothesis.Q0) : w * x = x * w := by
  set hyp := fc.toHypothesis
  have hwD : w ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hw)
  have hker : (⟨w, hwD⟩ : ↥hyp.D) ∈ hyp.conjQ0.ker := by
    rw [hyp.ker_conjQ0]
    exact hw
  rw [MonoidHom.mem_ker] at hker
  have happ : hyp.conjQ0 ⟨w, hwD⟩ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    rw [hker]
    rfl
  have hval := congrArg (fun y : ↥hyp.Q0 => (y : G)) happ
  have hconj : w * x * w⁻¹ = x := hval
  calc w * x = (w * x * w⁻¹) * w := by group
    _ = x * w := by rw [hconj]

/-- **Peterfalvi Part II, Ch. II, step (1) opening** (p. 108): `P ∩ W = 1`.
If `P ≤ W` then `P` would centralize `Q₀`, so the four-subgroup of `Q₀`
would land in `C_G(P)`, contradicting (B1). -/
theorem P_inf_W_eq_bot : fc.P ⊓ fc.toHypothesis.W = ⊥ := by
  set hyp := fc.toHypothesis
  have hle : fc.P ⊓ hyp.W ≤ fc.P := inf_le_left
  have hdvd : Nat.card ↥(fc.P ⊓ hyp.W) ∣ fc.p := by
    rw [← fc.card_P]
    exact Subgroup.card_dvd_of_le hle
  rcases (Nat.Prime.eq_one_or_self_of_dvd fc.p_prime _ hdvd) with hone | hp
  · exact Subgroup.eq_bot_of_card_eq _ hone
  · -- then `P ≤ W`, so `Q₀ ⊆ C_G(P)`, contradicting (B1)
    exfalso
    have hPW : fc.P ≤ hyp.W := by
      have heq : fc.P ⊓ hyp.W = fc.P := by
        apply Subgroup.eq_of_le_of_card_ge hle
        rw [hp, fc.card_P]
      rw [← heq]
      exact inf_le_right
    have hQ0C : hyp.Q0 ≤ Subgroup.centralizer (fc.P : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact fc.W_mem_centralizes_Q0 (hPW hg) hx
    obtain ⟨E, hEQ0, hE4, hEsq⟩ := hyp.exists_four_subgroup_le_Q0
    have hcard := fc.twoRank_centralizer_le_one E (hEQ0.trans hQ0C) hEsq
    rw [hE4] at hcard
    omega

/-- The fixed points of `P` on `Q₀` form a group of order at most `2`:
they are an elementary abelian `2`-subgroup of `C_G(P)`. -/
theorem card_Q0_inf_centralizer_le_two :
    Nat.card ↥(fc.toHypothesis.Q0 ⊓ Subgroup.centralizer (fc.P : Set G)) ≤
      2 := by
  set hyp := fc.toHypothesis
  apply fc.twoRank_centralizer_le_one _ inf_le_right
  intro x hx
  exact (hyp.mem_Q0_iff.mp hx.1).1

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
