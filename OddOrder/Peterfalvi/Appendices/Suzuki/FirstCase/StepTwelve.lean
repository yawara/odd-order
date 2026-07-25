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

open scoped Pointwise

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

include model in
/-- **The `N_G(R)`-orbit of `P` is exactly `𝒜`** (step (12) tail input): the orbit sits
inside `𝒜` (conjugates stay in `R`, keep order `p`, and stay outside `T` by the
strongly-real exclusion), and the orbit count `p^m` (index theorem) matches `|𝒜|`. -/
theorem orbit_eq_setOf_prime_order
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m)
    (hGp : fc.p ^ (m + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) :
    letI act : MulAction
        ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)) (Subgroup G) :=
      MulAction.compHom _ ((MulAut.conj : G →* MulAut G).comp
        (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)).subtype)
    MulAction.orbit
        ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)) fc.P
      = {P₁ : Subgroup G | P₁ ≤ fc.invImageF model ∧ Nat.card ↥P₁ = fc.p ∧
          ¬ P₁ ≤ fc.sInvertedT model} := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  set NR : Subgroup G :=
    Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) with hNRdef
  letI act : MulAction ↥NR (Subgroup G) :=
    MulAction.compHom _ ((MulAut.conj : G →* MulAut G).comp NR.subtype)
  -- subset (same argument as in the index theorem).
  have hsub : MulAction.orbit ↥NR fc.P ⊆ {P₁ : Subgroup G |
      P₁ ≤ fc.invImageF model ∧ Nat.card ↥P₁ = fc.p ∧
        ¬ P₁ ≤ fc.sInvertedT model} := by
    rintro Q ⟨n, rfl⟩
    change MulAut.conj (n : G) • fc.P ≤ fc.invImageF model ∧ _ ∧ _
    have hcard : Nat.card ↥(MulAut.conj (n : G) • fc.P) = fc.p := by
      rw [← fc.card_P]
      exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj (n : G)) fc.P).toEquiv).symm
    refine ⟨?_, hcard, ?_⟩
    · intro x hx
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
      have h2 : ((MulAut.conj (n : G))⁻¹ • x : G) = (n : G)⁻¹ * x * (n : G) := by
        have h3 : ((MulAut.conj (n : G))⁻¹ • x : G) = (MulAut.conj (n : G))⁻¹ x := rfl
        rw [h3, ← map_inv, MulAut.conj_apply]
        group
      rw [h2] at hx
      have h4 : (n : G)⁻¹ * x * (n : G) ∈ fc.invImageF model :=
        fc.P_le_invImageF model hx
      have h5 := (Subgroup.mem_set_normalizer_iff.mp n.2 ((n : G)⁻¹ * x * (n : G))).mp h4
      have h6 : (n : G) * ((n : G)⁻¹ * x * (n : G)) * (n : G)⁻¹ = x := by group
      rwa [h6] at h5
    · intro hleT
      have hbot := fc.conj_P_inf_sInvertedT_eq_bot model ind hB2 hm (n : G)
      have h1 : MulAut.conj (n : G) • fc.P
          = (MulAut.conj (n : G) • fc.P) ⊓ fc.sInvertedT model :=
        (inf_of_le_left hleT).symm
      rw [h1, hbot, Subgroup.card_bot] at hcard
      exact fc.p_prime.one_lt.ne hcard
  -- cardinality match via the index theorem.
  obtain ⟨x₀, hx₀P, hx₀1⟩ : ∃ x₀ ∈ fc.P, x₀ ≠ (1 : G) := by
    by_contra hall
    push Not at hall
    have h1 : fc.P = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      exact hall x hx
    have h2 := fc.card_P
    rw [h1, Subgroup.card_bot] at h2
    exact fc.p_prime.one_lt.ne h2
  have hAcard := fc.ncard_prime_order_not_le_sInvertedT model ind hB2 hm hx₀P hx₀1
  have hidx := fc.index_normalizer_P_subgroupOf_normalizer_invImageF model ind hB2 hm
    hGp hSigma
  have horbcard : (MulAction.orbit ↥NR fc.P).ncard = fc.p ^ m := by
    rw [← Nat.card_coe_set_eq,
      Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥NR fc.P)]
    have hstab : MulAction.stabilizer ↥NR fc.P
        = (Subgroup.normalizer (fc.P : Set G)).subgroupOf NR := by
      ext n
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      change (MulAut.conj (n : G) • fc.P = fc.P) ↔ _
      exact conj_smul_eq_iff_mem_normalizer
    rw [hstab]
    exact hidx ▸ rfl
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [hAcard, horbcard]

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
