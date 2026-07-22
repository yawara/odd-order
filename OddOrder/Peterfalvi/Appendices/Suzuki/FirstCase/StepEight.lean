/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepSeven

/-!
# Peterfalvi Part II, Ch. II, step (8): the case `Q₁ ≠ 1`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (8), p. 110.

Assume `Q₁ ≠ 1`.  Let `ℓ = |Σ|`.  If `ℓ ≠ 1`, then `ℓ` is prime and `F` is a
field of order `3^ℓ`, `5^ℓ`, or `9^ℓ`.

The first step of the argument is that `F` is a *field*: by step (5) the model's
near-field is either commutative or `≅ F_{9,2}`, and the exceptional near-field
`F_{9,2}` occurs only with `Q₁ = 1`.  So `Q₁ ≠ 1` forces `F` commutative.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

/-- **The fixed set of a ring automorphism of a finite field is a subfield**
(step (8), p. 110): for a finite field `F` of characteristic `f` and a ring
automorphism `σ`, the fixed set `{x : σ x = x}` is a subfield, hence has order
`f^a`.

The fixed set is the kernel of the additive endomorphism `σ − id` of `F`, hence
an additive subgroup, so its order divides `|F| = f^n` (additive Lagrange) and
is therefore a power of `f`. -/
theorem exists_card_fixedSet_eq_char_pow {F : Type*} [Field F] [Finite F]
    {f : ℕ} (hf : f.Prime) [CharP F f] (σ : F ≃+* F) :
    ∃ a : ℕ, Nat.card {x : F // σ x = x} = f ^ a := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact f.Prime := ⟨hf⟩
  let A : AddSubgroup F :=
    { carrier := {x | σ x = x}
      add_mem' := fun {a b} ha hb => by
        have ha' : σ a = a := ha
        have hb' : σ b = b := hb
        change σ (a + b) = a + b
        rw [map_add, ha', hb']
      zero_mem' := show σ 0 = 0 from map_zero σ
      neg_mem' := fun {a} ha => by
        have ha' : σ a = a := ha
        change σ (-a) = -a
        rw [map_neg, ha'] }
  obtain ⟨n, -, hn⟩ := FiniteField.card F f
  have hdvd : Nat.card ↥A ∣ f ^ (n : ℕ) := by
    have hcard : Nat.card ↥A ∣ Nat.card F := AddSubgroup.card_addSubgroup_dvd_card A
    have hNF : Nat.card F = f ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
    rwa [hNF] at hcard
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hf).mp hdvd
  exact ⟨a, ha⟩

/-- **Step (8), the fixed-field order dichotomy** (p. 110): if the fixed *units*
of a ring automorphism `σ` of a finite field `F` (characteristic `f`) form a
group of order `2^b` with `b ≥ 1`, then the fixed field has order `f` or `9`.

The fixed field has order `f^a` (`exists_card_fixedSet_eq_char_pow`); its unit
group has order `f^a − 1 = 2^b`, so `f^a = 2^b + 1`, and the arithmetic lemma
`eq_one_or_pow_eq_nine_of_pow_eq_two_pow_add_one` gives `f^a ∈ {f, 9}`. -/
theorem card_fixedSet_mem_of_units_two_pow {F : Type*} [Field F] [Finite F]
    {f : ℕ} (hf : f.Prime) [CharP F f] (σ : F ≃+* F) {b : ℕ} (hb : 1 ≤ b)
    (hunits : Nat.card {x : F // σ x = x} = 2 ^ b + 1) :
    Nat.card {x : F // σ x = x} = f ∨ Nat.card {x : F // σ x = x} = 9 := by
  obtain ⟨a, ha⟩ := exists_card_fixedSet_eq_char_pow hf σ
  have heq : f ^ a = 2 ^ b + 1 := by rw [← ha]; exact hunits
  -- `f` is odd (else `f^a = 2^b + 1` odd would be even)
  have hfodd : Odd f := by
    rcases hf.eq_two_or_odd' with rfl | hodd
    · exfalso
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · simp only [pow_zero] at heq
        have hb1 : 1 ≤ (2 : ℕ) ^ b := Nat.one_le_two_pow
        omega
      · have h1 : (2 : ℕ) ∣ 2 ^ a := dvd_pow_self 2 hapos.ne'
        have h2 : (2 : ℕ) ∣ 2 ^ b := dvd_pow_self 2 (by omega : b ≠ 0)
        omega
    · exact hodd
  rcases eq_one_or_pow_eq_nine_of_pow_eq_two_pow_add_one hfodd hb heq with ha1 | hf9
  · left; rw [ha, ha1, pow_one]
  · right; rw [ha]; exact hf9

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- **Peterfalvi Part II, Ch. II, step (8), `F` is a field** (p. 110, "By (5),
`F` is a field"): if `Q₁ ≠ 1` then the model's near-field `F` is commutative.

Step (5) (`card_nearField_eq_nine_and_Q1_eq_bot`) gives the dichotomy `F`
commutative, or `F ≅ F_{9,2}` with `Q₁ = 1`; the second alternative asserts
`Q₁ = 1`, so `Q₁ ≠ 1` leaves `F` commutative.

Inherits the step (2)(b) `sorry` (issue 9318) only through a model-supplying
caller, and the Higman `sorry` (step (5)). -/
theorem comm_of_Q1_ne_bot :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    ∀ {F : Type uG} [NearFields.NearField F]
      (_model : NearFields.AffineNearFieldModel fc.rankOneQuotient F),
      fc.toHypothesis.Q1 ≠ ⊥ → ∀ x y : F, x * y = y * x := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  intro F instF _model hQ1 x y
  rcases fc.card_nearField_eq_nine_and_Q1_eq_bot _model with hcomm | ⟨_, _, hbot⟩
  · exact hcomm x y
  · exact absurd hbot hQ1

/-- **Peterfalvi Part II, Ch. II, step (8), the per-`w` induction facts**
(p. 110, "It follows from the induction hypothesis that `f = 3` or `5` and that
`C_Q(w)` is a `2`-group"): for a nonidentity `w ∈ C_W(P)`, applying §3
Proposition 1(c) to `X = ⟨w⟩` yields that the global product order
`f = |s·t|` is `3` or `5`, and `C_Q(w)` is a `2`-group.

`⟨w⟩ ≤ W ≤ V` is nontrivial, and `w` centralizes `Q₀` (so the four-subgroup of
`Q₀` lies in `C_G(w)`); the trichotomy reading
(`cQ_card_and_pGroup_of_trichotomy`) supplies both conclusions.

Inherits the step (2)(b) `sorry` (issue 9318) — none directly, this is a clean
application of the axiom-clean trichotomy reading. -/
theorem st_mem_and_cQ_isPGroup_of_mem_centralizer_W
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    {w : G} (hwW : w ∈ fc.toHypothesis.W)
    (_hwP : w ∈ Subgroup.centralizer (fc.P : Set G)) (hw1 : w ≠ 1) :
    (orderOf (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t) = 3 ∨
        orderOf (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t) = 5) ∧
      IsPGroup 2 ↥(fc.toHypothesis.Q.subgroupOf
        (Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G))) := by
  set X : Subgroup G := Subgroup.zpowers w with hXdef
  have hwV : w ∈ fc.toHypothesis.V := fc.toHypothesis.W_le_V hwW
  have hXV : X ≤ fc.toHypothesis.V := (Subgroup.zpowers_le).mpr hwV
  have hX : X ≠ ⊥ := fun h => hw1 (Subgroup.zpowers_eq_bot.mp h)
  -- four-subgroup of `Q₀` sits in `C_G(⟨w⟩)`
  obtain ⟨E0, hE0Q0, hE04, hE0sq⟩ := fc.toHypothesis.exists_four_subgroup_le_Q0
  have hE0C : E0 ≤ Subgroup.centralizer (X : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcw : Commute w e := fc.W_mem_centralizes_Q0 hwW (hE0Q0 he)
    exact (hcw.zpow_left n).eq
  have hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
    refine ⟨E0.subgroupOf (Subgroup.centralizer (X : Set G)), ?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE0C).toEquiv]; exact hE04
    · intro x hx
      exact Subtype.ext (by
        rw [Subgroup.coe_pow, hE0sq (x : G) (Subgroup.mem_subgroupOf.mp hx),
          Subgroup.coe_one])
  obtain ⟨hpg, hcases⟩ :=
    fc.toHypothesis.cQ_card_and_pGroup_of_trichotomy hXV hX hA3 ind
  refine ⟨?_, hpg⟩
  rcases hcases with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
