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

/-! ## Structural `|G|_p` decomposition

`|G| = |Q| · |D| · (|Q|+1)` (`card_G_eq`), and `|D| = |D̄| · |W|`,
`|D̄| = |K̄| · |V̄|` (`D̄ = K̄ ⋊ V̄`).  The `p`-parts are `|Q|_p = 1`
(`not_p_dvd_card_Q`), `|K̄|_p = 1` (`|K̄| = 2^p − 1`), `|V̄| = p`, giving
`|D|_p = p · |W|_p` and `|G|_p = p^{m+2} · |W|_p`. -/

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G] (hyp : Hypothesis G Ω)

/-- `|D| = |D̄| · |W|` where `D̄ = D/W`. -/
theorem card_D_eq_card_Dbar_mul_card_W :
    Nat.card ↥hyp.D = Nat.card hyp.Dbar * Nat.card ↥hyp.W := by
  have hW : Nat.card ↥(hyp.W.subgroupOf hyp.D) = Nat.card ↥hyp.W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hyp.W_le_V.trans hyp.V_le_D)).toEquiv
  calc Nat.card ↥hyp.D
      = Nat.card (↥hyp.D ⧸ hyp.W.subgroupOf hyp.D) *
          Nat.card ↥(hyp.W.subgroupOf hyp.D) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
    _ = Nat.card hyp.Dbar * Nat.card ↥hyp.W := by rw [hW]

/-- `|K̄| · |V̄| = |D̄|` (`D̄ = K̄ ⋊ V̄`, from `Kbar_isComplement_Vbar`). -/
theorem card_Kbar_mul_card_Vbar :
    Nat.card ↥hyp.Kbar * Nat.card ↥hyp.Vbar = Nat.card hyp.Dbar := by
  simpa using Subgroup.IsComplement.card_mul_card hyp.Kbar_isComplement_Vbar

end Hypothesis

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

/-- **Step (10)** structural: `|K̄| = 2^p − 1` (First Case).  `K̄ = F(D̄)`, and
Proposition 2 gives `|F(D̄)| = |KSet| = |K| = |Q₀| − 1 = 2^p − 1`. -/
theorem card_Kbar_eq_two_pow_sub_one :
    Nat.card ↥fc.toHypothesis.Kbar = 2 ^ fc.p - 1 := by
  have hK : Nat.card ↥fc.toHypothesis.K = fc.toHypothesis.KSet.ncard :=
    (Nat.card_coe_set_eq _).trans (by rw [fc.toHypothesis.coe_K])
  have hKbar := congrArg (fun s : Subgroup fc.toHypothesis.Dbar => Nat.card ↥s)
    fc.toHypothesis.Kbar_eq_fitting
  rw [hKbar, fc.toHypothesis.card_fitting_Dbar_eq_ncard_KSet, ← hK,
    fc.toHypothesis.card_K_eq_card_Q0_sub_one, fc.card_Q0_eq_two_pow]

/-- **Step (10)** structural: `p ∤ |K̄|` (First Case).  `|K̄| = 2^p − 1 ≡ 1 (mod p)`
by Fermat (`2^p ≡ 2`), so `p ∤ |K̄|`. -/
theorem not_p_dvd_card_Kbar :
    ¬ fc.p ∣ Nat.card ↥fc.toHypothesis.Kbar := by
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  rw [fc.card_Kbar_eq_two_pow_sub_one]
  intro hdvd
  have h1le : 1 ≤ 2 ^ fc.p := Nat.one_le_two_pow
  have h1 : ((2 ^ fc.p - 1 : ℕ) : ZMod fc.p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have hval : ((2 ^ fc.p - 1 : ℕ) : ZMod fc.p) = 1 := by
    rw [Nat.cast_sub h1le, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat, ZMod.pow_card]
    ring
  rw [hval] at h1
  exact one_ne_zero h1

/-- **Step (10)** structural: `|V̄| = p` (First Case).  `V = W ⋊ P`, so
`V̄ = V/W = (W̄ ⊔ P̄)` collapses to the image of `P`; `P ∩ W = 1` makes the
quotient map injective on `P`, so `|V̄| = |P| = p`. -/
theorem card_Vbar_eq_p :
    Nat.card ↥fc.toHypothesis.Vbar = fc.p := by
  have hWD : fc.toHypothesis.W ≤ fc.toHypothesis.D :=
    fc.toHypothesis.W_le_V.trans fc.toHypothesis.V_le_D
  have hPD : fc.P ≤ fc.toHypothesis.D := fc.P_le_V.trans fc.toHypothesis.V_le_D
  set ψ : ↥fc.P →* fc.toHypothesis.Dbar :=
    (QuotientGroup.mk' (fc.toHypothesis.W.subgroupOf fc.toHypothesis.D)).comp
      (Subgroup.inclusion hPD) with hψ
  -- `ψ` is injective: its kernel is `P ∩ W = 1`
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hx
    have hmem : (x : G) ∈ fc.P ⊓ fc.toHypothesis.W := ⟨x.2, hx⟩
    rw [fc.P_inf_W_eq_bot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hbot : (fc.toHypothesis.W.subgroupOf fc.toHypothesis.D).map
      (QuotientGroup.mk' (fc.toHypothesis.W.subgroupOf fc.toHypothesis.D)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact le_of_eq (QuotientGroup.ker_mk' _).symm
  -- `ψ.range = V̄`: both equal `(P.subgroupOf D).map (mk' W)`
  have hψrange : ψ.range = (fc.P.subgroupOf fc.toHypothesis.D).map
      (QuotientGroup.mk' (fc.toHypothesis.W.subgroupOf fc.toHypothesis.D)) := by
    rw [hψ, MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
      Subgroup.inclusion_range]
  have hVbarP : fc.toHypothesis.Vbar = (fc.P.subgroupOf fc.toHypothesis.D).map
      (QuotientGroup.mk' (fc.toHypothesis.W.subgroupOf fc.toHypothesis.D)) := by
    rw [show fc.toHypothesis.Vbar = (fc.toHypothesis.V.subgroupOf fc.toHypothesis.D).map
        (QuotientGroup.mk' (fc.toHypothesis.W.subgroupOf fc.toHypothesis.D)) from rfl,
      ← fc.W_join_P_eq_V, Subgroup.subgroupOf_sup hWD hPD, Subgroup.map_sup, hbot, bot_sup_eq]
  have hrange : ψ.range = fc.toHypothesis.Vbar := hψrange.trans hVbarP.symm
  rw [← hrange, ← fc.card_P]
  exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm

/-- **Step (10)** structural: `|D̄|_p = p`.  `|D̄| = |K̄| · |V̄|`, `p ∤ |K̄|`,
`|V̄| = p`. -/
theorem factorization_card_Dbar_eq_one :
    (Nat.card fc.toHypothesis.Dbar).factorization fc.p = 1 := by
  rw [← fc.toHypothesis.card_Kbar_mul_card_Vbar,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd fc.not_p_dvd_card_Kbar, fc.card_Vbar_eq_p,
    Nat.Prime.factorization_self fc.p_prime, zero_add]

/-- **Step (10)** structural: `|D|_p = p · |W|_p`, i.e.
`v_p(|D|) = 1 + v_p(|W|)`. -/
theorem factorization_card_D_eq :
    (Nat.card ↥fc.toHypothesis.D).factorization fc.p =
      1 + (Nat.card ↥fc.toHypothesis.W).factorization fc.p := by
  rw [fc.toHypothesis.card_D_eq_card_Dbar_mul_card_W,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    fc.factorization_card_Dbar_eq_one]

/-- **Peterfalvi Part II, Ch. II, step (10)** (p. 111): `|G|_p = p^{m+2} · |W|_p`,
i.e. `v_p(|G|) = (m+2) + v_p(|W|)` where `|F| = p^m`.

`|G| = |Q| · |D| · (|Q|+1)`; `|Q|_p = 1` (`not_p_dvd_card_Q`), `|D|_p = p · |W|_p`
(`factorization_card_D_eq`), and `(|Q|+1)_p = p^{m+1}`
(`padicValNat_card_Q_add_one`).  Inherits the step (2)(b) `sorry` (issue 9318)
through the model. -/
theorem factorization_card_G_eq {F : Type uG} [NearFields.NearField F]
    (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      NearFields.AffineNearFieldModel fc.rankOneQuotient F)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    (Nat.card G).factorization fc.p =
      (m + 2) + (Nat.card ↥fc.toHypothesis.W).factorization fc.p := by
  have hQ1 : (Nat.card ↥fc.toHypothesis.Q + 1).factorization fc.p = m + 1 := by
    rw [Nat.factorization_def _ fc.p_prime, fc.padicValNat_card_Q_add_one model hB2 hm]
  have hQ0 : (Nat.card ↥fc.toHypothesis.Q).factorization fc.p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fc.not_p_dvd_card_Q
  rw [fc.toHypothesis.card_G_eq,
    Nat.factorization_mul (mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne') (by omega),
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Finsupp.add_apply, hQ0, hQ1, fc.factorization_card_D_eq]
  ring

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
