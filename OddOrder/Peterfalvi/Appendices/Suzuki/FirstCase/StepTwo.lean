/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepOne
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerQuotient
import OddOrder.Peterfalvi.Appendices.NearFields

/-!
# Peterfalvi Part II, Ch. II, step (2): the rank-one centralizer quotient

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (2), p. 108.

By §3 Proposition 1(a), `L = C_G(P)` acts on the fixed points `Ω_P` with
kernel `N = C_{D_L}(Q_L)`, and the faithful quotient `L/N` satisfies (A1)
and (A2).  Under (B1) the quotient has 2-rank one — a four-subgroup of the
quotient would lift along the odd kernel to a four-subgroup of `C_G(P)` —
so Appendix C, Proposition 1 applies to `L/N`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open MulAction
open scoped Pointwise

/-- **Lifting a four-subgroup along an odd kernel**: if `A ⧸ N` contains an
elementary abelian subgroup of order `4` and `N` has odd order, so does
`A` — the Sylow `2`-subgroup of the preimage maps isomorphically. -/
theorem exists_four_subgroup_of_quotient {A : Type*} [Group A] [Finite A]
    (N : Subgroup A) [N.Normal] (hNodd : Odd (Nat.card ↥N))
    (hbar : ∃ Ebar : Subgroup (A ⧸ N),
      Nat.card ↥Ebar = 4 ∧ ∀ x ∈ Ebar, x ^ 2 = 1) :
    ∃ E : Subgroup A, Nat.card ↥E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
  classical
  obtain ⟨Ebar, hEcard, hEsq⟩ := hbar
  set E' : Subgroup A := Ebar.comap (QuotientGroup.mk' N) with hE'def
  -- `|E'| = 4 * |N|`
  have h1 : Nat.card ↥E' * E'.index = Nat.card A :=
    E'.card_mul_index
  have h2 : Nat.card ↥Ebar * Ebar.index = Nat.card (A ⧸ N) :=
    Ebar.card_mul_index
  have h3 : Nat.card A = Nat.card (A ⧸ N) * Nat.card ↥N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hidx : E'.index = Ebar.index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)
  have hipos : E'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hE'card : Nat.card ↥E' = 4 * Nat.card ↥N := by
    have hmul : Nat.card ↥E' * E'.index =
        (4 * Nat.card ↥N) * E'.index := by
      rw [h1, h3, ← h2, hidx, hEcard]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hipos) hmul
  -- the Sylow `2`-subgroup of `E'` has order `4`
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥E') := inferInstance
  have hfact : (Nat.card ↥E').factorization 2 = 2 := by
    rw [hE'card, Nat.factorization_mul (by norm_num) Nat.card_pos.ne']
    have h4 : (4 : ℕ).factorization 2 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.factorization_pow_self Nat.prime_two
    have hodd : (Nat.card ↥N).factorization 2 = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro h2dvd
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2dvd)
    simp [h4, hodd]
  have hScard : Nat.card ↥(S : Subgroup ↥E') = 4 := by
    rw [S.card_eq_multiplicity, hfact]
    norm_num
  -- elements of `S` square into `S ∩ N = 1`
  have hSsq : ∀ y : ↥E', y ∈ (S : Subgroup ↥E') → y ^ 2 = 1 := by
    intro y hyS
    have hmemN : ((y : A)) ^ 2 ∈ N := by
      have hEb : QuotientGroup.mk' N (y : A) ∈ Ebar := y.2
      have hsq := hEsq _ hEb
      rw [← map_pow] at hsq
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      exact hsq
    have hyS2 : y ^ 2 ∈ (S : Subgroup ↥E') :=
      Subgroup.pow_mem _ hyS 2
    have hdvd4 : orderOf (y ^ 2) ∣ 4 := by
      have h : orderOf (y ^ 2) =
          orderOf (⟨y ^ 2, hyS2⟩ : ↥(S : Subgroup ↥E')) :=
        orderOf_injective ((S : Subgroup ↥E').subtype)
          (Subgroup.subtype_injective _) ⟨y ^ 2, hyS2⟩
      rw [h, ← hScard]
      exact orderOf_dvd_natCard _
    have hdvdN : orderOf (y ^ 2) ∣ Nat.card ↥N := by
      have hcoe : orderOf (((y : A)) ^ 2) = orderOf (y ^ 2) :=
        orderOf_injective E'.subtype
          (Subgroup.subtype_injective _) (y ^ 2)
      have h : orderOf (((y : A)) ^ 2) =
          orderOf (⟨((y : A)) ^ 2, hmemN⟩ : ↥N) :=
        orderOf_injective N.subtype
          (Subgroup.subtype_injective _) ⟨((y : A)) ^ 2, hmemN⟩
      rw [← hcoe, h]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime 4 (Nat.card ↥N) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (Nat.coprime_two_left.mpr hNodd).pow_left 2
    have hone : orderOf (y ^ 2) = 1 :=
      Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd4 hdvdN)
    rwa [orderOf_eq_one_iff] at hone
  -- push forward to `A`
  refine ⟨(S : Subgroup ↥E').map E'.subtype, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (Subgroup.subtype_injective _)).toEquiv.symm]
    exact hScard
  · rintro x ⟨y, hyS, rfl⟩
    have hy2 := hSsq y hyS
    calc (E'.subtype y) ^ 2 = E'.subtype (y ^ 2) := (map_pow _ _ _).symm
      _ = 1 := by rw [hy2, map_one]

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- **Peterfalvi Part II, Ch. II, step (2)(a)** (p. 108): the faithful
centralizer quotient `C_G(P)/N` is a doubly transitive rank-one group —
the input of Appendix C, Proposition 1.  All of (A1) comes from §3
Proposition 1(a)/(c); faithfulness is the quotient construction; and a
four-subgroup of the quotient would lift along the odd kernel to a
four-subgroup of `C_G(P)`, contradicting (B1). -/
noncomputable def rankOneQuotient :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    NearFields.RankOneHypothesis
      (fc.toHypothesis.centralizerActionQuotient fc.P)
      ↥(MulAction.fixedPoints fc.P Ω) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  let h1 := fc.toHypothesis.centralizerQuotientHypothesisA1 fc.P_le_V
  refine
    { basept := h1.basept
      doubly_transitive := h1.doubly_transitive
      faithful := fc.toHypothesis.centralizerQuotient_faithful fc.P_le_V
      H := h1.H
      Q := h1.Q
      D := h1.D
      H_def := h1.H_def
      t := h1.t
      t_sq := h1.t_sq
      t_ne_one := h1.t_ne_one
      t_not_mem_H := h1.t_not_mem_H
      D_def := h1.D_def
      Q_le_H := h1.Q_le_H
      Q_normal_in_H := h1.Q_normal_in_H
      Q_inf_D_eq_bot := h1.Q_inf_D_eq_bot
      Q_mul_D_eq_H := h1.Q_mul_D_eq_H
      Q_even := h1.Q_even
      D_odd := h1.D_odd
      two_rank_one := ?_ }
  intro hbar
  set L : Subgroup G := Subgroup.centralizer ((fc.P : Set G)) with hLdef
  set N : Subgroup ↥L :=
    (fc.toHypothesis.H.subgroupOf L).normalCore with hNdef
  have hNodd : Odd (Nat.card ↥N) := by
    have hle : N ≤ fc.toHypothesis.D.subgroupOf L := by
      rw [hNdef, fc.toHypothesis.normalCore_cH_eq_centralizer_cQ fc.P_le_V]
      exact inf_le_left
    have hDodd : Odd (Nat.card ↥(fc.toHypothesis.D.subgroupOf L)) :=
      (fc.toHypothesis.centralizerHypothesisA1 fc.P_le_V).D_odd
    exact hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  obtain ⟨E, hEcard, hEsq⟩ := exists_four_subgroup_of_quotient N hNodd hbar
  have hEC : E.map L.subtype ≤ Subgroup.centralizer (fc.P : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hcard' : Nat.card ↥(E.map L.subtype) = 4 := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (Subgroup.subtype_injective _)).toEquiv.symm]
    exact hEcard
  have hsq' : ∀ x ∈ E.map L.subtype, x ^ 2 = 1 := by
    rintro x ⟨y, hy, rfl⟩
    have hy2 := hEsq y hy
    calc (L.subtype y) ^ 2 = L.subtype (y ^ 2) := (map_pow _ _ _).symm
      _ = 1 := by rw [hy2, map_one]
  have hle2 := fc.twoRank_centralizer_le_one _ hEC hsq'
  rw [hcard'] at hle2
  omega

/-- **Peterfalvi Part II, Ch. II, step (2)(b)** (p. 108): the faithful
rank-one quotient `C_G(P)/N` is the affine group of a finite near-field
extended by automorphisms.

This cites Appendix C, Proposition 1 (`rankOne_affine_nearField`), which is
honestly stated but currently sorried behind the Brauer–Suzuki theorem
(issue 9318); downstream consumers of this theorem inherit that `sorry`
until 9318 closes. -/
theorem exists_affineNearFieldModel :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    ∃ (F : Type uG) (_ : NearFields.NearField F),
      Nonempty (NearFields.AffineNearFieldModel fc.rankOneQuotient F) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  exact NearFields.rankOne_affine_nearField fc.rankOneQuotient

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
