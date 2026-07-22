/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepEight

/-!
# Peterfalvi Part II, Ch. II, step (9): `p = f`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (9), pp. 110–111.

Step (9) asserts `p = f` (the prime `p = |P|` equals the characteristic `f` of
the near-field `F`).

The book's argument is a transfer computation: the transfer `T : G → H/(QKW)`
sends `x ∈ P^#` to `x^{|Q|+1}` (using the canonical coset representatives `1`
and `{ty : y ∈ Q}` of §1 Proposition 4(a) and `tyx = xty^x`); by hypothesis
`(B2)` (no normal subgroup of index `p`) `T(x) = 1`, and `P ∩ (QKW) = 1` forces
`x^{|Q|+1} = 1`, so `p ∣ |Q| + 1`.  The arithmetic finish is then

`|F| = (|F| − 1) + 1 ≡ (|F| − 1)^p + 1 = |Q| + 1 ≡ 0 (mod p)`,

so `p ∣ |F|`, and since `|F|` is a power of the characteristic `f`, `p = f`.

This file formalizes the **arithmetic finish** as `char_eq_p_of_p_dvd_card_Q_add_one`
(from `p ∣ |Q| + 1`, conclude `f = p`).  The transfer computation producing
`p ∣ |Q| + 1` is the remaining frontier of step (9).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- **Peterfalvi Part II, Ch. II, step (9), arithmetic finish** (p. 111): if
`p ∣ |Q| + 1`, then the characteristic `f` of the near-field equals `p`.

By (4) `|Q| = |C_Q(P)|^p` and the standing identification `|C_Q(P)| = |F| − 1`,
so `|Q| + 1 = (|F| − 1)^p + 1 ≡ |F| (mod p)` (Fermat: `a^p ≡ a`).  Hence
`p ∣ |F|`; the additive group of `F` has exponent dividing the prime `f`
(`char_spec`), so Cauchy produces an element of additive order `p`, forcing
`p ∣ f` and thus `p = f`.

Inherits the step (2)(b) `sorry` (issue 9318) through a model-supplying caller
(via `centralizer_inf_mulEquiv_units`). -/
theorem char_eq_p_of_p_dvd_card_Q_add_one
    {F : Type uG} [NearFields.NearField F]
    (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      NearFields.AffineNearFieldModel fc.rankOneQuotient F)
    (hp : fc.p ∣ Nat.card ↥fc.toHypothesis.Q + 1) :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    model.char = fc.p := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  haveI : Finite F := by
    have hinj : Function.Injective (fun x : F => model.emb (Multiplicative.ofAdd x)) :=
      fun a b hab => Multiplicative.ofAdd.injective (model.emb_injective hab)
    exact Finite.of_injective _ hinj
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  haveI : Nonempty F := ⟨0⟩
  -- `|Q| = (|F| − 1)^p`
  obtain ⟨e⟩ := fc.centralizer_inf_mulEquiv_units model
  have hCQ : Nat.card ↥(fc.toHypothesis.Q ⊓ Subgroup.centralizer (fc.P : Set G)) =
      Nat.card F - 1 := by rw [Nat.card_congr e.toEquiv, Nat.card_units]
  have hQ : Nat.card ↥fc.toHypothesis.Q = (Nat.card F - 1) ^ fc.p := by
    rw [fc.card_Q_eq_card_inf_centralizer_pow, hCQ]
  rw [hQ] at hp
  have hFpos : 1 ≤ Nat.card F := Nat.card_pos
  -- Fermat: `p ∣ |F|`
  have hpF : fc.p ∣ Nat.card F := by
    have hz : ((Nat.card F : ZMod fc.p)) = 0 := by
      have h0 : (((Nat.card F - 1) ^ fc.p + 1 : ℕ) : ZMod fc.p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hp
      push_cast [Nat.cast_sub hFpos] at h0
      rw [ZMod.pow_card, sub_add_cancel] at h0
      exact h0
    exact (ZMod.natCast_eq_zero_iff _ _).mp hz
  -- Cauchy in `(F, +)`: `p ∣ f`
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card fc.p
    (Nat.card_eq_fintype_card (α := F) ▸ hpF)
  have hdvd : fc.p ∣ model.char := ha ▸ addOrderOf_dvd_of_nsmul_eq_zero (model.char_spec a)
  exact ((Nat.prime_dvd_prime_iff_eq fc.p_prime model.char_prime).mp hdvd).symm

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
