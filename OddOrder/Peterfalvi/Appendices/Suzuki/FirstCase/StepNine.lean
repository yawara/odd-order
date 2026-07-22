/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepEight
import OddOrder.Peterfalvi.Appendices.Suzuki.CanonicalForm
import OddOrder.GroupTheory.TransferInvariantTransversal

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

open scoped Pointwise in
/-- **Peterfalvi Part II, Ch. II, step (9), transversal invariance**: the right
transversal `{1} ∪ {t y : y ∈ Q}` of `H` is invariant under conjugation by `x ∈ P`.
Since `P ≤ V = C_D(t)`, `x` centralises `t`, and `x ∈ H` normalises `Q`, so
`x⁻¹ (t y) x = t (x⁻¹ y x)` with `x⁻¹ y x ∈ Q`. -/
theorem rightTransversalTQ_conj_invariant {x : G} (hxP : x ∈ fc.P) :
    ∀ r ∈ fc.toHypothesis.rightTransversalTQ,
      x⁻¹ * r * x ∈ fc.toHypothesis.rightTransversalTQ := by
  set hyp := fc.toHypothesis with hhyp
  have hxH : x ∈ hyp.H := hyp.D_le_H (hyp.V_le_D (fc.P_le_V hxP))
  have hxt : Commute x hyp.t := hyp.commute_t_of_mem_V (fc.P_le_V hxP)
  intro r hr
  rw [Hypothesis.mem_rightTransversalTQ] at hr ⊢
  rcases hr with rfl | ⟨y, hyQ, rfl⟩
  · left; group
  · right
    refine ⟨x⁻¹ * y * x, ?_, ?_⟩
    · simpa using hyp.Q_normal_in_H x⁻¹ (inv_mem hxH) y hyQ
    · calc hyp.t * (x⁻¹ * y * x)
          = hyp.t * x⁻¹ * y * x := by group
        _ = x⁻¹ * hyp.t * y * x := by rw [← hxt.inv_left.eq]
        _ = x⁻¹ * (hyp.t * y) * x := by group

/-- **Peterfalvi Part II, Ch. II, step (9), the transfer computation** (p. 111):
for any homomorphism `ϕ : H →* A` to a commutative group and `x ∈ P`, the transfer
of `x` is `T(x) = ϕ(x) ^ (|Q| + 1)`.

By Prop 4 (a) the identity and the elements `t y` (`y ∈ Q`) represent the right
cosets of `H`, so `[G : H] = |Q| + 1`; this transversal is invariant under
conjugation by `x ∈ P` (`rightTransversalTQ_conj_invariant`), whence every transfer
factor equals `x` (`transfer_eq_pow_of_conj_invariant_rightTransversal`). -/
theorem transfer_eq_pow_card_Q_add_one {A : Type*} [CommGroup A]
    (ϕ : fc.toHypothesis.H →* A) {x : G} (hxP : x ∈ fc.P) :
    MonoidHom.transfer ϕ x
      = ϕ ⟨x, fc.toHypothesis.D_le_H (fc.toHypothesis.V_le_D (fc.P_le_V hxP))⟩
          ^ (Nat.card fc.toHypothesis.Q + 1) := by
  have hxH : x ∈ fc.toHypothesis.H :=
    fc.toHypothesis.D_le_H (fc.toHypothesis.V_le_D (fc.P_le_V hxP))
  have hindex : fc.toHypothesis.H.index = Nat.card fc.toHypothesis.Q + 1 := by
    haveI := fc.toHypothesis.doubly_transitive
    haveI : MulAction.IsPretransitive G Ω :=
      MulAction.isPretransitive_of_is_two_pretransitive
    rw [fc.toHypothesis.H_def,
      MulAction.index_stabilizer_of_transitive G fc.toHypothesis.basept,
      fc.toHypothesis.card_Omega]
  haveI : fc.toHypothesis.H.FiniteIndex := ⟨by rw [hindex]; exact Nat.succ_ne_zero _⟩
  rw [OddOrder.GroupTheory.transfer_eq_pow_of_conj_invariant_rightTransversal ϕ
      fc.toHypothesis.isComplement_H_rightTransversalTQ hxH
      (fc.rightTransversalTQ_conj_invariant hxP),
    hindex]

/-- **Peterfalvi Part II, Ch. II, step (9)** (p. 111): `p ∣ |Q| + 1`.

Take `ϕ = Abelianization.of : H → H^{ab}` and `x ∈ P` of order `p`.  The transfer
`T = transfer ϕ : G → H^{ab}` maps into an abelian group, so `⁅G,G⁆ ≤ ker T`; by
`hB2` (no normal subgroup of index `p`, equivalently `p ∤ |G^{ab}|`) the `p`-element
`x` lies in `⁅G,G⁆`, so `T(x) = 1`.  But `T(x) = ϕ(x)^{|Q|+1}`
(`transfer_eq_pow_card_Q_add_one`), and `hPinj` (`P ∩ ⁅H,H⁆ = 1`, i.e. `P` injects
into `H^{ab}`; the book's `P ∩ QKW = 1`, as `⁅H,H⁆ ≤ QKW`) makes `ϕ(x)` of order `p`.
Hence `ϕ(x)^{|Q|+1} = 1` forces `p ∣ |Q| + 1`. -/
theorem p_dvd_card_Q_add_one
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hPinj : Disjoint fc.P
      ((commutator ↥fc.toHypothesis.H).map fc.toHypothesis.H.subtype)) :
    fc.p ∣ Nat.card fc.toHypothesis.Q + 1 := by
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  -- pick a nonidentity `x ∈ P`; it has order `p`
  obtain ⟨x, hxP, hx1⟩ : ∃ x, x ∈ fc.P ∧ x ≠ 1 := by
    haveI : Nontrivial ↥fc.P :=
      (Finite.one_lt_card_iff_nontrivial).mp (by rw [fc.card_P]; exact fc.p_prime.one_lt)
    obtain ⟨⟨y, hyP⟩, hy1⟩ := exists_ne (1 : ↥fc.P)
    exact ⟨y, hyP, fun h => hy1 (Subtype.ext h)⟩
  have hxH : x ∈ fc.toHypothesis.H :=
    fc.toHypothesis.D_le_H (fc.toHypothesis.V_le_D (fc.P_le_V hxP))
  have hxpow : x ^ fc.p = 1 := by
    have h0 : (⟨x, hxP⟩ : ↥fc.P) ^ fc.p = 1 := by
      rw [← fc.card_P]; exact pow_card_eq_one'
    have := congrArg (Subgroup.subtype fc.P) h0
    simpa using this
  -- `ϕ = Abelianization.of : H → H^{ab}` and the transfer identity
  set ϕ := Abelianization.of (G := ↥fc.toHypothesis.H) with hϕ
  have htrans : MonoidHom.transfer ϕ x = ϕ ⟨x, hxH⟩ ^ (Nat.card fc.toHypothesis.Q + 1) :=
    fc.transfer_eq_pow_card_Q_add_one ϕ hxP
  -- `x ∈ ⁅G,G⁆`, hence `T(x) = 1`
  have hx0comm : x ∈ commutator G := by
    have hof1 : Abelianization.of x = 1 := by
      by_contra h
      apply hB2
      have h1 : orderOf (Abelianization.of x) ∣ fc.p :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxpow, map_one])
      have h2 : orderOf (Abelianization.of x) = fc.p :=
        (fc.p_prime.eq_one_or_self_of_dvd _ h1).resolve_left
          (fun he => h (orderOf_eq_one_iff.mp he))
      exact h2 ▸ orderOf_dvd_natCard _
    exact (QuotientGroup.eq_one_iff x).mp hof1
  have htrans1 : MonoidHom.transfer ϕ x = 1 :=
    MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker _ hx0comm)
  -- `ϕ ⟨x, hxH⟩` has order `p`
  have hxHpow : (⟨x, hxH⟩ : ↥fc.toHypothesis.H) ^ fc.p = 1 :=
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hxpow)
  have hϕne : ϕ ⟨x, hxH⟩ ≠ 1 := by
    intro hcon
    have hmem : (⟨x, hxH⟩ : ↥fc.toHypothesis.H) ∈ commutator ↥fc.toHypothesis.H :=
      (QuotientGroup.eq_one_iff _).mp hcon
    have hxM : x ∈ (commutator ↥fc.toHypothesis.H).map fc.toHypothesis.H.subtype :=
      ⟨⟨x, hxH⟩, hmem, rfl⟩
    exact hx1 (Subgroup.mem_bot.mp (hPinj.le_bot ⟨hxP, hxM⟩))
  have hordϕ : orderOf (ϕ ⟨x, hxH⟩) = fc.p := by
    have h1 : orderOf (ϕ ⟨x, hxH⟩) ∣ fc.p :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxHpow, map_one])
    exact (fc.p_prime.eq_one_or_self_of_dvd _ h1).resolve_left
      (fun he => hϕne (orderOf_eq_one_iff.mp he))
  -- conclude `p ∣ |Q| + 1`
  rw [htrans1] at htrans
  rw [← hordϕ]
  exact orderOf_dvd_of_pow_eq_one htrans.symm

/-- **Peterfalvi Part II, Ch. II, step (9): `p = f`** (p. 111).  Under (B2)
(`p ∤ |G^{ab}|`, equivalently no normal subgroup of index `p`) and `P ∩ ⁅H,H⁆ = 1`
(the book's `P ∩ QKW = 1`), the characteristic `f` of the near-field equals `p`.

Combines the transfer half (`p_dvd_card_Q_add_one`) with the arithmetic finish
(`char_eq_p_of_p_dvd_card_Q_add_one`).  Inherits the step (2)(b) `sorry` (issue 9318)
through the supplied model. -/
theorem char_eq_p {F : Type uG} [NearFields.NearField F]
    (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      NearFields.AffineNearFieldModel fc.rankOneQuotient F)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hPinj : Disjoint fc.P
      ((commutator ↥fc.toHypothesis.H).map fc.toHypothesis.H.subtype)) :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    model.char = fc.p :=
  fc.char_eq_p_of_p_dvd_card_Q_add_one model (fc.p_dvd_card_Q_add_one hB2 hPinj)

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
