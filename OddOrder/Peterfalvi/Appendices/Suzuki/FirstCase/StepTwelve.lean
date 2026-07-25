/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepElevenComplement

/-!
# Peterfalvi Part II, Ch. II, step (12): case (10.2) holds

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (12), pp. 112–113.

Step (12) rules out case (10.1).  This leaf starts from the orbit count
`[N_G(R) : N_G(P)] = p^m` (`StepElevenComplement`) and derives `m = 1`
(so `|G|_p = p³`), heading for the Hall–Wielandt/transfer contradiction
with hypothesis (B2).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)
  {F : Type uG} [NearFields.NearField F]
  (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    NearFields.AffineNearFieldModel fc.rankOneQuotient F)

include model in
/-- **`m = 1` in case (10.1)** (step (12), p. 112): `|N_G(R)| = |N_G(P)|·p^m` with
`p^{m+1} ∣ |N_G(P)| = |C_G(P)|`, so `p^{2m+1}` divides `|G|`, while `|G|_p = p^{m+2}` —
forcing `2m + 1 ≤ m + 2`, i.e. `m ≤ 1`; and `m ≥ 1` since `F` is nontrivial. -/
theorem m_eq_one_of_factorization
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m)
    (hfact : (Nat.card G).factorization fc.p = m + 2)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) :
    m = 1 := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  haveI : Finite F := Nat.finite_of_card_ne_zero
    (by rw [hm]; exact (Nat.pow_pos fc.p_prime.pos).ne')
  have hGp : fc.p ^ (m + 2) ∣ Nat.card G := by
    have h1 : fc.p ^ (m + 2) = fc.p ^ ((Nat.card G).factorization fc.p) := by rw [hfact]
    rw [h1]
    exact (Nat.Prime.pow_dvd_iff_le_factorization fc.p_prime Nat.card_pos.ne').mpr le_rfl
  have hidx := fc.index_normalizer_P_subgroupOf_normalizer_invImageF model ind hB2 hm
    hGp hSigma
  set NR : Subgroup G :=
    Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) with hNRdef
  have hle : Subgroup.normalizer (fc.P : Set G) ≤ NR :=
    (fc.normalizer_P_lt_normalizer_invImageF model ind hm hGp hSigma).le
  -- `|NR| = |N_G(P)|·p^m`.
  have hlag := ((Subgroup.normalizer (fc.P : Set G)).subgroupOf NR).card_mul_index
  rw [hidx] at hlag
  have hcNP : Nat.card ↥((Subgroup.normalizer (fc.P : Set G)).subgroupOf NR)
      = Nat.card ↥(Subgroup.normalizer (fc.P : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [hcNP] at hlag
  -- `p^{m+1} ∣ |N_G(P)| = |C_G(P)|`.
  have hNPeq : Nat.card ↥(Subgroup.normalizer (fc.P : Set G))
      = Nat.card ↥(Subgroup.centralizer (fc.P : Set G)) := by
    rw [fc.normalizer_P_eq_centralizer]
  have hCeq : Nat.card ↥(Subgroup.centralizer (fc.P : Set G))
      = fc.p ^ (m + 1) * (Nat.card ↥(fc.rankOneQuotient).Q
        * Nat.card ↥(fc.rankOneQuotient).D) := by
    rw [fc.card_centralizer_P model ind, fc.card_P, hm]; ring
  -- assemble: `p^{2m+1} ∣ |NR| ∣ |G|`.
  have hdvd1 : fc.p ^ (2 * m + 1) ∣ Nat.card ↥NR := by
    have h1 : fc.p ^ (2 * m + 1) = fc.p ^ (m + 1) * fc.p ^ m := by
      rw [← pow_add]
      congr 1
      ring
    rw [← hlag, hNPeq, hCeq, h1]
    exact mul_dvd_mul (Dvd.intro _ rfl) dvd_rfl
  have hdvd2 : Nat.card ↥NR ∣ Nat.card G := Subgroup.card_subgroup_dvd_card NR
  have hdvd3 : fc.p ^ (2 * m + 1) ∣ Nat.card G := hdvd1.trans hdvd2
  have hle2 : 2 * m + 1 ≤ m + 2 := by
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization fc.p_prime
      Nat.card_pos.ne').mp hdvd3
    rwa [hfact] at h1
  have hm1 : 1 ≤ m := by
    by_contra hm0
    push Not at hm0
    interval_cases m
    have h2 : 1 < Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [hm] at h2
    simp at h2
  omega

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
