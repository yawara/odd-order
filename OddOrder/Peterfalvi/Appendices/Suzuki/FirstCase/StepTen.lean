/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepNine
import Mathlib.NumberTheory.Multiplicity

/-!
# Peterfalvi Part II, Ch. II, step (10): the two cases

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (10), p. 111.

Step (10) fixes `|F| = p^m` and proves the dichotomy

* (10.1) `p ∤ |Σ|` and `|G|_p = p^{m+2}`, or
* (10.2) `p = |Σ| = 3`, `F ≅ F_{9,2}`, `W` is cyclic of order `3` or `9` and
  `|G|_3 = 3^4 |W|`.

The proof opens with the arithmetic computation

`|Q| + 1 = 1 + (-1 + p^m)^p ≡ p^{m+1} (mod p^{m+2})`,

so that `(|Q|+1)_p = p^{m+1}`.  This file formalizes that **arithmetic core**:

* `padicValNat_pow_sub_one_add_one` — the pure lifting-the-exponent computation
  `v_p((N-1)^p + 1) = v_p(N) + 1` for an odd prime `p ∣ N` (model-free,
  axiom-clean).
* `card_field_eq_prime_pow` — `|F| = p^m` with `m ≥ 1` (the additive group of the
  near-field is an elementary abelian `p`-group, `p = char = f`).
* `padicValNat_card_Q_add_one` — the step (10) opening `v_p(|Q|+1) = m+1`.

The structural `|G|_p` computation and the case split are built on top of these
in later sections.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

/-! ## Pure lifting-the-exponent core -/

/-- **Lifting the exponent** (odd prime): for an odd prime `p` dividing `N ≥ 1`,
`v_p((N-1)^p + 1) = v_p(N) + 1`.

Direct application of `padicValNat.pow_add_pow` with `x = N-1`, `y = 1`, `n = p`:
`(N-1) + 1 = N`, `p ∤ N-1` (as `p ∣ N`), and `v_p(p) = 1`. -/
theorem padicValNat_pow_sub_one_add_one {p N : ℕ} [Fact p.Prime] (hp : Odd p)
    (hpN : p ∣ N) (hN : 1 ≤ N) :
    padicValNat p ((N - 1) ^ p + 1) = padicValNat p N + 1 := by
  have hx : ¬ p ∣ (N - 1) := by
    intro h
    have h1 : p ∣ 1 := Nat.sub_sub_self hN ▸ Nat.dvd_sub hpN h
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h1)
  have hxy : p ∣ (N - 1) + 1 := by rwa [Nat.sub_add_cancel hN]
  have key := padicValNat.pow_add_pow (p := p) (x := N - 1) (y := 1) (n := p) hp hxy hx hp
  rw [one_pow, Nat.sub_add_cancel hN, padicValNat_self] at key
  exact key

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- The near-field `F` supplied by a model is finite (it embeds into `Q`). -/
theorem finite_of_model {F : Type uG} [NearFields.NearField F]
    (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      NearFields.AffineNearFieldModel fc.rankOneQuotient F) :
    Finite F := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  have hinj : Function.Injective (fun x : F => model.emb (Multiplicative.ofAdd x)) :=
    fun a b hab => Multiplicative.ofAdd.injective (model.emb_injective hab)
  exact Finite.of_injective _ hinj

/-- **Peterfalvi Part II, Ch. II, step (10) opening** (p. 111): `|F| = p^m` with
`m ≥ 1`.

The characteristic of `F` equals `p` (step (9), needs (B2)); `char • a = 0` for all
`a` (`char_spec`), so the additive group of `F` is an elementary abelian `p`-group.
Every prime dividing `|F|` therefore equals `p` (Cauchy), whence `|F|` is a power of
`p`; it is nontrivial (`0 ≠ 1`) so `m ≥ 1`. -/
theorem card_field_eq_prime_pow {F : Type uG} [NearFields.NearField F]
    (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      NearFields.AffineNearFieldModel fc.rankOneQuotient F)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    ∃ m, 1 ≤ m ∧ Nat.card F = fc.p ^ m := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  haveI : Finite F := fc.finite_of_model model
  haveI : Fintype F := Fintype.ofFinite F
  have hcharp : model.char = fc.p := fc.char_eq_p model hB2
  have hchar : ∀ a : F, fc.p • a = 0 := by
    intro a; rw [← hcharp]; exact model.char_spec a
  -- every prime dividing `|F|` equals `p`
  have huniq : ∀ {d : ℕ}, Nat.Prime d → d ∣ Nat.card F → d = fc.p := by
    intro d hd hdvd
    haveI : Fact d.Prime := ⟨hd⟩
    obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card d
      (Nat.card_eq_fintype_card (α := F) ▸ hdvd)
    have hdp : d ∣ fc.p := ha ▸ addOrderOf_dvd_of_nsmul_eq_zero (hchar a)
    exact (Nat.prime_dvd_prime_iff_eq hd fc.p_prime).mp hdp
  haveI : Nonempty F := ⟨0⟩
  have hne : Nat.card F ≠ 0 := Nat.card_pos.ne'
  refine ⟨(Nat.card F).primeFactorsList.length,
    ?_, Nat.eq_prime_pow_of_unique_prime_dvd hne huniq⟩
  -- `m ≥ 1`: `|F| > 1` (nontrivial), so its prime-factor list is nonempty
  rcases Nat.eq_zero_or_pos (Nat.card F).primeFactorsList.length with hk | hk
  · exfalso
    have hcard1 : Nat.card F = 1 := by
      rw [Nat.eq_prime_pow_of_unique_prime_dvd hne huniq, hk, pow_zero]
    have h1lt : 1 < Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    omega
  · exact hk

/-- **Peterfalvi Part II, Ch. II, step (10) opening** (p. 111): `(|Q|+1)_p = p^{m+1}`,
i.e. `v_p(|Q| + 1) = m + 1` where `|F| = p^m`.

By (4) `|Q| = |C_Q(P)|^p = (|F| - 1)^p`, and `p ∣ |F|` (as `p = char`), so
lifting the exponent gives `v_p((|F|-1)^p + 1) = v_p(|F|) + 1 = m + 1`. -/
theorem padicValNat_card_Q_add_one {F : Type uG} [NearFields.NearField F]
    (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      NearFields.AffineNearFieldModel fc.rankOneQuotient F)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    padicValNat fc.p (Nat.card fc.toHypothesis.Q + 1) = m + 1 := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  haveI : Finite F := fc.finite_of_model model
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Nonempty F := ⟨0⟩
  -- `|Q| = (|F| − 1)^p`
  obtain ⟨e⟩ := fc.centralizer_inf_mulEquiv_units model
  have hCQ : Nat.card ↥(fc.toHypothesis.Q ⊓ Subgroup.centralizer (fc.P : Set G)) =
      Nat.card F - 1 := by rw [Nat.card_congr e.toEquiv, Nat.card_units]
  have hQ : Nat.card ↥fc.toHypothesis.Q = (Nat.card F - 1) ^ fc.p := by
    rw [fc.card_Q_eq_card_inf_centralizer_pow, hCQ]
  -- `p ∣ |F|`: the additive order of `1 ∈ F` is `char = p` and divides `|F|`
  have hpF : fc.p ∣ Nat.card F := by
    have hcharp : model.char = fc.p := fc.char_eq_p model hB2
    have hord : addOrderOf (1 : F) = model.char := by
      have hdvd : addOrderOf (1 : F) ∣ model.char :=
        addOrderOf_dvd_of_nsmul_eq_zero (model.char_spec 1)
      rcases (Nat.dvd_prime model.char_prime).mp hdvd with h | h
      · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) one_ne_zero
      · exact h
    rw [← hcharp, ← hord]
    exact addOrderOf_dvd_natCard _
  have hFpos : 1 ≤ Nat.card F := Nat.card_pos
  rw [hQ, padicValNat_pow_sub_one_add_one fc.p_odd hpF hFpos, hm,
    padicValNat.prime_pow]

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
