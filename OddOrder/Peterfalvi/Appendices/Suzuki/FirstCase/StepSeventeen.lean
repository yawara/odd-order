/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepSeventeenWeakClosure

/-!
# Peterfalvi Part II, Ch. II, step (17): the final contradiction

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (17), p. 114.

Given the weak closure of `Z₁PΣ` in `R₂` (`StepSeventeenWeakClosure.lean`), the
Hall–Wielandt theorem transports hypothesis (B2) from `G` to `N_G(Z₁PΣ) = R₂⟨s⟩`.
This file shows that `R₂⟨s⟩` nevertheless has a quotient of order `3` — in both the
`|W| = 9` and the `|W| = 3` case — and assembles the contradiction, parameterised by
the transfer-control input (issue 9503).
-/

set_option autoImplicit false

open scoped Pointwise commutatorElement

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)
  {F : Type uG} [NearFields.NearField F]
  (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    NearFields.AffineNearFieldModel fc.rankOneQuotient F)

include model in
/-- **`W ⊄ R₁` when `|W| = 9`** ((17), p. 114, last paragraph).

Peterfalvi argues through `C_{R₁}(s) = PΣ`; here it is quicker to compare centres:
if `W ≤ R₁` then `LV ≤ R₁`, and `|LV| = 27·|W| = 3⁵ = |R₁|` forces `LV = R₁`, whence
`Z₁Σ = Z(LV) = Z(R₁) = Z₁` — impossible since `|Z₁Σ| = 9` and `|Z₁| = 3`. -/
theorem not_W_le_sylowThree_of_card_W_eq_nine
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hW9 : Nat.card ↥fc.toHypothesis.W = 9) :
    ¬ fc.toHypothesis.W ≤ fc.sylowThreeNormalizerRSigma model := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  intro hWR₁
  have hR₁card := fc.card_sylowThreeNormalizerRSigma model ind hB2
  have hLVcard : Nat.card ↥(fc.nonsplitTorus ⊔ fc.toHypothesis.V) = 3 ^ 5 := by
    rw [fc.card_sup_nonsplitTorus_V model ind hB2, hW9]
    norm_num
  have hPR₁ : fc.P ≤ fc.sylowThreeNormalizerRSigma model :=
    ((fc.P_le_invImageF model).trans le_sup_left).trans
      (fc.sup_le_sylowThreeNormalizerRSigma model ind hB2)
  have hLVle : fc.nonsplitTorus ⊔ fc.toHypothesis.V
      ≤ fc.sylowThreeNormalizerRSigma model := by
    refine sup_le (fc.nonsplitTorus_le_sylowThreeNormalizerRSigma model ind hB2) ?_
    rw [← fc.W_join_P_eq_V]
    exact sup_le hWR₁ hPR₁
  have hLVeq : fc.nonsplitTorus ⊔ fc.toHypothesis.V
      = fc.sylowThreeNormalizerRSigma model :=
    Subgroup.eq_of_le_of_card_ge hLVle (by rw [hLVcard, hR₁card])
  -- the two centres disagree
  have hZLV := fc.inf_centralizer_sup_nonsplitTorus_V_eq model ind hB2
  have hZR₁ := fc.inf_centralizer_sylowThree_eq_zpowers model ind hB2
  rw [hLVeq, hZR₁] at hZLV
  have h9 := fc.card_zpowers_sup_sigma model ind hB2
  obtain ⟨-, hp3, -, -, -, -⟩ := fc.step_twelve model ind hB2
  have hstord : orderOf (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = 3 := by
    rw [fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  rw [← hZLV, Nat.card_zpowers, hstord] at h9
  omega

include model in
/-- **`R₂⟨s⟩` has a quotient of order `3` when `|W| = 9`** ((17), p. 114, last
paragraph): `R₂ = R₁W` with `R₁` of index `3`, and `s` centralizes `W`, so `R₁⟨s⟩` is
normal of index `3` in `R₂⟨s⟩`. -/
theorem three_dvd_card_abelianization_of_card_W_eq_nine
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G)
    (hR₁S : fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G))
    (hW9 : Nat.card ↥fc.toHypothesis.W = 9) :
    (3 : ℕ) ∣ Nat.card (Abelianization ↥((S : Subgroup G)
      ⊔ Subgroup.zpowers fc.toHypothesis.distinguishedInvolution)) := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set s : G := fc.toHypothesis.distinguishedInvolution with hs_def
  have hsord : orderOf s = 2 :=
    orderOf_eq_prime fc.toHypothesis.distinguishedInvolution_sq
      fc.toHypothesis.distinguishedInvolution_ne_one
  have hR₁card := fc.card_sylowThreeNormalizerRSigma model ind hB2
  obtain ⟨-, -, -, -, -, hGp⟩ := fc.step_twelve model ind hB2
  have hScard : Nat.card ↥(S : Subgroup G) = 3 ^ 6 := by
    rw [Sylow.card_eq_multiplicity, hGp, hW9]
    norm_num
  -- `R₁` is normal of index `3` in `R₂`
  have hR₁idx : ((fc.sylowThreeNormalizerRSigma model).subgroupOf
      (S : Subgroup G)).index = 3 := by
    have h := ((fc.sylowThreeNormalizerRSigma model).subgroupOf
      (S : Subgroup G)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₁S).toEquiv, hR₁card,
      hScard] at h
    omega
  have hR₁norm : ((fc.sylowThreeNormalizerRSigma model).subgroupOf
      (S : Subgroup G)).Normal :=
    Subgroup.normal_of_index_eq_minFac_card (by rw [hR₁idx, hScard]; norm_num)
  have hconjR₁ : ∀ g ∈ (S : Subgroup G), ∀ a ∈ fc.sylowThreeNormalizerRSigma model,
      g * a * g⁻¹ ∈ fc.sylowThreeNormalizerRSigma model := by
    intro g hg a ha
    have h := hR₁norm.conj_mem ⟨a, hR₁S ha⟩ (by rwa [Subgroup.mem_subgroupOf])
      ⟨g, hg⟩
    rwa [Subgroup.mem_subgroupOf] at h
  -- `s` normalizes `R₁` and `R₂`
  have hsR₁ : ∀ a ∈ fc.sylowThreeNormalizerRSigma model,
      s * a * s⁻¹ ∈ fc.sylowThreeNormalizerRSigma model := fun a ha =>
    fc.conj_mem_sylowThreeNormalizerRSigma model
      (fc.distinguishedInvolution_mem_normalizerRSigma model) ha
  have hsS : s ∈ Subgroup.normalizer (((S : Subgroup G)) : Set G) := by
    rw [fc.normalizer_sylow_eq model ind hB2 S hR₁S]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  -- `R₂ = R₁W`
  have hWS : fc.toHypothesis.W ≤ (S : Subgroup G) :=
    ((fc.toHypothesis.W_le_V.trans le_sup_right).trans
      (fc.sup_nonsplitTorus_V_le_sylow model ind hB2 S hR₁S))
  have hR₂eq : fc.sylowThreeNormalizerRSigma model ⊔ fc.toHypothesis.W
      = (S : Subgroup G) := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hR₁S hWS) ?_
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le
      (le_sup_left : fc.sylowThreeNormalizerRSigma model ≤ _ ⊔ fc.toHypothesis.W)
    have hdvd : Nat.card ↥(fc.sylowThreeNormalizerRSigma model
        ⊔ fc.toHypothesis.W) ∣ Nat.card ↥(S : Subgroup G) :=
      Subgroup.card_dvd_of_le (sup_le hR₁S hWS)
    have hm3 : m ∣ 3 := by
      rw [hm, hR₁card, hScard] at hdvd
      refine (Nat.mul_dvd_mul_iff_left (show 0 < 3 ^ 5 by norm_num)).mp ?_
      calc 3 ^ 5 * m ∣ 3 ^ 6 := hdvd
        _ = 3 ^ 5 * 3 := by norm_num
    rcases (Nat.dvd_prime (by norm_num)).mp hm3 with h1 | h3
    · exfalso
      refine fc.not_W_le_sylowThree_of_card_W_eq_nine model ind hB2 hW9 ?_
      have heq : fc.sylowThreeNormalizerRSigma model ⊔ fc.toHypothesis.W
          = fc.sylowThreeNormalizerRSigma model :=
        (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hm, h1, mul_one])).symm
      rw [← heq]
      exact le_sup_right
    · rw [hm, h3, hR₁card, hScard]
      norm_num
  -- every element of `R₂` sends `s` into `R₁⟨s⟩`
  have hcoeR₂ : ((S : Subgroup G) : Set G)
      = ((fc.sylowThreeNormalizerRSigma model : Subgroup G) : Set G)
        * (fc.toHypothesis.W : Set G) := by
    rw [← hR₂eq]
    refine Subgroup.coe_mul_of_right_le_normalizer_left _ _ ?_
    intro w hw
    rw [Subgroup.mem_set_normalizer_iff]
    intro y
    refine ⟨fun hy => hconjR₁ w (hWS hw) y hy, fun hy => ?_⟩
    have h1 : w⁻¹ * (w * y * w⁻¹) * w⁻¹⁻¹ = y := by group
    rw [← h1]
    exact hconjR₁ w⁻¹ (Subgroup.inv_mem _ (hWS hw)) _ hy
  have hconjS : ∀ g ∈ (S : Subgroup G),
      g * s * g⁻¹ ∈ fc.sylowThreeNormalizerRSigma model ⊔ Subgroup.zpowers s := by
    intro g hg
    have hg' : g ∈ ((fc.sylowThreeNormalizerRSigma model : Subgroup G) : Set G)
        * (fc.toHypothesis.W : Set G) := by rw [← hcoeR₂]; exact hg
    obtain ⟨a, ha, w, hw, hawg⟩ := hg'
    have haw : a * w = g := hawg
    have hws : w * s = s * w := Subgroup.mem_centralizer_singleton_iff.mp
      (fc.toHypothesis.V_le_centralizer_distinguishedInvolution
        (fc.toHypothesis.W_le_V hw)).2
    have hcalc : g * s * g⁻¹ = (a * (s * a⁻¹ * s⁻¹)) * s := by
      calc g * s * g⁻¹ = a * (w * s * w⁻¹) * a⁻¹ := by rw [← haw]; group
        _ = a * s * a⁻¹ := by rw [hws]; group
        _ = (a * (s * a⁻¹ * s⁻¹)) * s := by group
    rw [hcalc]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    exact Subgroup.mul_mem _ ha (hsR₁ a⁻¹ (Subgroup.inv_mem _ ha))
  -- `R₁⟨s⟩` is normal in `R₂⟨s⟩`
  have hnorm : ∀ g ∈ (S : Subgroup G) ⊔ Subgroup.zpowers s,
      ∀ y ∈ fc.sylowThreeNormalizerRSigma model ⊔ Subgroup.zpowers s,
      g * y * g⁻¹ ∈ fc.sylowThreeNormalizerRSigma model ⊔ Subgroup.zpowers s := by
    have hgen : ((S : Subgroup G) ⊔ Subgroup.zpowers s)
        ≤ Subgroup.normalizer (((fc.sylowThreeNormalizerRSigma model
          ⊔ Subgroup.zpowers s : Subgroup G)) : Set G) := by
      refine sup_le ?_ ?_
      · intro g hg
        have hconj : ∀ h : G, (∀ a ∈ fc.sylowThreeNormalizerRSigma model,
              h * a * h⁻¹ ∈ fc.sylowThreeNormalizerRSigma model) →
            (h * s * h⁻¹ ∈ fc.sylowThreeNormalizerRSigma model ⊔ Subgroup.zpowers s) →
            ∀ y ∈ fc.sylowThreeNormalizerRSigma model ⊔ Subgroup.zpowers s,
              h * y * h⁻¹ ∈ fc.sylowThreeNormalizerRSigma model
                ⊔ Subgroup.zpowers s := by
          intro h hR hs y hy
          have hsub : fc.sylowThreeNormalizerRSigma model ⊔ Subgroup.zpowers s
              ≤ Subgroup.comap (MulAut.conj h).toMonoidHom
                (fc.sylowThreeNormalizerRSigma model ⊔ Subgroup.zpowers s) := by
            refine sup_le (fun a ha => Subgroup.mem_sup_left (hR a ha))
              (Subgroup.zpowers_le.mpr hs)
          exact hsub hy
        rw [Subgroup.mem_set_normalizer_iff]
        intro y
        refine ⟨fun hy => hconj g (fun a ha => hconjR₁ g hg a ha) (hconjS g hg) y hy,
          fun hy => ?_⟩
        have h1 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
        rw [← h1]
        refine hconj g⁻¹ (fun a ha => hconjR₁ g⁻¹ (Subgroup.inv_mem _ hg) a ha) ?_ _ hy
        exact hconjS g⁻¹ (Subgroup.inv_mem _ hg)
      · rw [Subgroup.zpowers_le, Subgroup.mem_set_normalizer_iff]
        have hs2 : s * s = 1 := by
          rw [← pow_two]; exact fc.toHypothesis.distinguishedInvolution_sq
        have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
        have hconj : ∀ y ∈ fc.sylowThreeNormalizerRSigma model ⊔ Subgroup.zpowers s,
            s * y * s⁻¹ ∈ fc.sylowThreeNormalizerRSigma model
              ⊔ Subgroup.zpowers s := by
          have hsub : fc.sylowThreeNormalizerRSigma model ⊔ Subgroup.zpowers s
              ≤ Subgroup.comap (MulAut.conj s).toMonoidHom
                (fc.sylowThreeNormalizerRSigma model ⊔ Subgroup.zpowers s) := by
            refine sup_le (fun a ha => Subgroup.mem_sup_left (hsR₁ a ha))
              (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right ?_))
            have hss : (MulAut.conj s).toMonoidHom s = s := by
              change s * s * s⁻¹ = s
              group
            rw [hss]
            exact Subgroup.mem_zpowers _
          intro y hy
          exact hsub hy
        intro y
        refine ⟨fun hy => hconj y hy, fun hy => ?_⟩
        have h1 : y = s * (s * y * s⁻¹) * s⁻¹ := by
          rw [hsinv]
          calc y = (s * s) * y * (s * s) := by rw [hs2]; group
            _ = s * (s * y * s) * s := by group
        rw [h1]
        exact hconj _ hy
    intro g hg y hy
    have h := Subgroup.mem_set_normalizer_iff.mp (hgen hg) y
    exact h.mp hy
  -- cardinalities and the index
  have hR₁inf : fc.sylowThreeNormalizerRSigma model ⊓ Subgroup.zpowers s = ⊥ :=
    (fc.sylowThree_sup_zpowers_distinguishedInvolution model ind hB2).2
  have hSinf : (S : Subgroup G) ⊓ Subgroup.zpowers s = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have h2 : orderOf y ∣ 2 := by
      have h := Subgroup.orderOf_dvd_natCard _ hy.2
      rwa [Nat.card_zpowers, hsord] at h
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp S.isPGroup' ⟨y, hy.1⟩
    rw [Subgroup.orderOf_mk] at hk
    have h3 : orderOf y ∣ 3 ^ k := by rw [hk]
    have h1 : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right k (by norm_num)) h2 h3
    exact orderOf_eq_one_iff.mp h1
  have hcardR₁s : Nat.card ↥(fc.sylowThreeNormalizerRSigma model
      ⊔ Subgroup.zpowers s) = 3 ^ 5 * 2 := by
    rw [card_sup_eq_mul_of_le_normalizer (fun b hb => ?_) hR₁inf, hR₁card,
      Nat.card_zpowers, hsord]
    rw [Subgroup.mem_set_normalizer_iff]
    obtain ⟨k, rfl⟩ := hb
    intro y
    have hsk : ∀ a ∈ fc.sylowThreeNormalizerRSigma model,
        s ^ k * a * (s ^ k)⁻¹ ∈ fc.sylowThreeNormalizerRSigma model := by
      intro a ha
      exact fc.conj_mem_sylowThreeNormalizerRSigma model
        (Subgroup.zpow_mem _ (fc.distinguishedInvolution_mem_normalizerRSigma model) k)
        ha
    refine ⟨fun hy => hsk y hy, fun hy => ?_⟩
    have h1 : (s ^ k)⁻¹ * (s ^ k * y * (s ^ k)⁻¹) * ((s ^ k)⁻¹)⁻¹ = y := by group
    rw [← h1]
    have hsk' : ∀ a ∈ fc.sylowThreeNormalizerRSigma model,
        (s ^ k)⁻¹ * a * ((s ^ k)⁻¹)⁻¹ ∈ fc.sylowThreeNormalizerRSigma model := by
      intro a ha
      exact fc.conj_mem_sylowThreeNormalizerRSigma model
        (Subgroup.inv_mem _ (Subgroup.zpow_mem _
          (fc.distinguishedInvolution_mem_normalizerRSigma model) k)) ha
    exact hsk' _ hy
  have hcardSs : Nat.card ↥((S : Subgroup G) ⊔ Subgroup.zpowers s)
      = 3 ^ 6 * 2 := by
    rw [card_sup_eq_mul_of_le_normalizer (fun b hb => ?_) hSinf, hScard,
      Nat.card_zpowers, hsord]
    obtain ⟨k, rfl⟩ := hb
    exact Subgroup.zpow_mem _ hsS k
  have hleSs : fc.sylowThreeNormalizerRSigma model ⊔ Subgroup.zpowers s
      ≤ (S : Subgroup G) ⊔ Subgroup.zpowers s :=
    sup_le (hR₁S.trans le_sup_left) le_sup_right
  have hnormSub : ((fc.sylowThreeNormalizerRSigma model
      ⊔ Subgroup.zpowers s).subgroupOf
        ((S : Subgroup G) ⊔ Subgroup.zpowers s)).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm g g.2 n hn
  have hidx : ((fc.sylowThreeNormalizerRSigma model ⊔ Subgroup.zpowers s).subgroupOf
      ((S : Subgroup G) ⊔ Subgroup.zpowers s)).index = 3 := by
    have h := ((fc.sylowThreeNormalizerRSigma model ⊔ Subgroup.zpowers s).subgroupOf
      ((S : Subgroup G) ⊔ Subgroup.zpowers s)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hleSs).toEquiv, hcardR₁s,
      hcardSs] at h
    omega
  exact dvd_card_abelianization_of_index_eq_prime (by norm_num) hidx

/-! ## Towards the `|W| = 3` branch -/

include model in
/-- `Z₁ ⊓ ΣP = 1`: the elements of `Z₁` are strongly real ((16)) while those of
`(ΣP)^#` are not. -/
theorem zpowers_inf_sigma_sup_P_eq_bot
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
      ⊓ ((fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) ⊔ fc.P) = ⊥ := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  by_contra hy1
  exact fc.not_isStronglyReal_of_mem_P_sup_sigma model ind hB2 hy.2 hy1
    (fc.forall_isStronglyReal_mem_zpowers_st model ind hB2 hy.1)

include model in
/-- `Z₁ ≤ ⁅R₁, R₁⁆`, since `Z₁ = ⁅RΣ, RΣ⁆` by (14) and `RΣ ≤ R₁`. -/
theorem zpowers_le_commutator_sylowThree
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
      ≤ ⁅fc.sylowThreeNormalizerRSigma model, fc.sylowThreeNormalizerRSigma model⁆ := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  rw [← fc.commutator_sup_eq_zpowers model ind hB2]
  exact Subgroup.commutator_mono (fc.sup_le_sylowThreeNormalizerRSigma model ind hB2)
    (fc.sup_le_sylowThreeNormalizerRSigma model ind hB2)

include model in
/-- **`ΣP ⊄ ⁅R₁, R₁⁆`**, given the commutator bound `|⁅R₁, R₁⁆| ≤ 9` ((17), p. 114:
"`⁅R̄₁, R̄₁⁆` has order `1` or `3`").

Indeed `Z₁ ≤ ⁅R₁, R₁⁆` and `Z₁ ⊓ ΣP = 1`, so `ΣP ≤ ⁅R₁, R₁⁆` would force
`27 = |Z₁ΣP| ≤ |⁅R₁, R₁⁆| ≤ 9`. -/
theorem not_sigma_sup_P_le_commutator_sylowThree
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hbound : Nat.card ↥(⁅fc.sylowThreeNormalizerRSigma model,
      fc.sylowThreeNormalizerRSigma model⁆ : Subgroup G) ≤ 9) :
    ¬ ((fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) ⊔ fc.P)
      ≤ ⁅fc.sylowThreeNormalizerRSigma model,
        fc.sylowThreeNormalizerRSigma model⁆ := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  intro hle
  obtain ⟨-, hp3, -, -, -, -⟩ := fc.step_twelve model ind hB2
  obtain ⟨hpSig, -, -, -, -, -⟩ := fc.step_twelve model ind hB2
  obtain ⟨-, -, -, hSig3, -⟩ :=
    fc.card_field_eq_nine_of_p_dvd_card_centralizer_W ind model hB2 hpSig
  have hstord : orderOf (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = 3 := by
    rw [fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  -- `|ΣP| = 9`
  have hSPcard : Nat.card ↥((fc.toHypothesis.W
      ⊓ Subgroup.centralizer (fc.P : Set G)) ⊔ fc.P) = 9 := by
    have hinf : (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) ⊓ fc.P
        = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hmem : x ∈ (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
          ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊓ fc.P :=
        ⟨Subgroup.mem_sup_right hx.1, hx.2⟩
      rwa [fc.zpowers_sup_sigma_inf_P_eq_bot model ind hB2] at hmem
    rw [card_sup_eq_mul_of_commute
        (fun a (ha : a ∈ fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))
          b (hb : b ∈ fc.P) =>
          (Subgroup.mem_centralizer_iff.mp ha.2 b hb).symm) hinf,
      hSig3, fc.card_P, hp3]
  -- `Z₁ΣP ≤ ⁅R₁, R₁⁆` has order `27`
  have hSPle : ((fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) ⊔ fc.P)
      ≤ (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hZle := fc.zpowers_le_commutator_sylowThree model ind hB2
  have hZSPle : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t)
      ⊔ ((fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) ⊔ fc.P)
      ≤ ⁅fc.sylowThreeNormalizerRSigma model,
        fc.sylowThreeNormalizerRSigma model⁆ := sup_le hZle hle
  have hcard27 : Nat.card ↥(Subgroup.zpowers
      (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
      ⊔ ((fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) ⊔ fc.P)) = 27 := by
    rw [card_sup_eq_mul_of_commute
        (fun a (ha : a ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
            * fc.toHypothesis.t)) b
          (hb : b ∈ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))
            ⊔ fc.P) =>
          fc.mul_comm_of_mem_zpowers_sup_sigma_sup_P model ind hB2
            (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
            (hSPle hb))
        (fc.zpowers_inf_sigma_sup_P_eq_bot model ind hB2),
      Nat.card_zpowers, hstord, hSPcard]
  have hdvd := Subgroup.card_dvd_of_le hZSPle
  rw [hcard27] at hdvd
  have := Nat.le_of_dvd (by
    have : 0 < Nat.card ↥(⁅fc.sylowThreeNormalizerRSigma model,
      fc.sylowThreeNormalizerRSigma model⁆ : Subgroup G) := Nat.card_pos
    omega) hdvd
  omega

include model in
/-- **`|⁅R₁, R₁⁆| ≤ 9`** ((17), p. 114: "`⁅R̄₁, R̄₁⁆` has order `1` or `3`").

`R₁` is generated by `N = Z₁ΣP` together with one element `u ∈ R ∖ Z₁P` and a generator
`v` of `L`, while `⁅N, R₁⁆ ≤ Z₁` by (16) and `⁅R₁, R₁⁆ ≤ N`; so
`commutator_le_of_two_generators` bounds `⁅R₁, R₁⁆` by `Z₁⟨⁅u,v⁆⟩`, of order at most
`9`. -/
theorem card_commutator_sylowThree_le
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hcommN : ⁅fc.sylowThreeNormalizerRSigma model,
        fc.sylowThreeNormalizerRSigma model⁆
      ≤ (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P) :
    Nat.card ↥(⁅fc.sylowThreeNormalizerRSigma model,
      fc.sylowThreeNormalizerRSigma model⁆ : Subgroup G) ≤ 9 := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨-, hp3, hF9, -, -, -⟩ := fc.step_twelve model ind hB2
  have hm : Nat.card F = fc.p ^ 2 := by rw [hF9, hp3]; norm_num
  have hPcard : Nat.card ↥fc.P = 3 := by rw [fc.card_P, hp3]
  have hstord : orderOf (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = 3 := by
    rw [fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  have hZ₁card : Nat.card ↥(Subgroup.zpowers
      (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)) = 3 := by
    rw [Nat.card_zpowers, hstord]
  -- basic containments
  have hZ₁R : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ≤ fc.invImageF model :=
    (fc.zpowers_distinguishedInvolution_mul_t_le_sInvertedT model ind hB2 hm).trans
      (fc.sInvertedT_spec model ind hB2 hm).1
  have hPR : fc.P ≤ fc.invImageF model := fc.P_le_invImageF model
  have habR := fc.invImageF_mul_comm model ind hB2 hm
  have hRcard : Nat.card ↥(fc.invImageF model) = 27 := by
    rw [fc.card_invImageF model ind, hF9, hPcard]
  have hZPcard := fc.card_zpowers_sup_P_eq_nine model ind hB2
  have hZPR : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ⊔ fc.P ≤ fc.invImageF model := sup_le hZ₁R hPR
  -- pick `u ∈ R ∖ Z₁P`
  obtain ⟨u, huR, huZP⟩ : ∃ u ∈ fc.invImageF model,
      u ∉ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) ⊔ fc.P := by
    by_contra hcon
    push Not at hcon
    have hle : fc.invImageF model ≤ Subgroup.zpowers
        (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t) ⊔ fc.P := hcon
    have := Nat.le_of_dvd (by norm_num) (Subgroup.card_dvd_of_le hle)
    rw [hRcard, hZPcard] at this
    omega
  have hu3 : u ^ 3 = 1 := by
    have h := fc.pow_p_eq_one_of_mem_invImageF model ind hB2 hm huR
    rwa [hp3] at h
  have hR_eq : (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ⊔ fc.P) ⊔ Subgroup.zpowers u = fc.invImageF model := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hZPR (Subgroup.zpowers_le.mpr huR)) ?_
    have huord : orderOf u = 3 := by
      have hdvd : orderOf u ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hu3
      rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h3
      · exact absurd (by rw [orderOf_eq_one_iff.mp h1]; exact Subgroup.one_mem _) huZP
      · exact h3
    have hinf : (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) ⊔ fc.P) ⊓ Subgroup.zpowers u = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      by_contra hy1
      refine huZP ?_
      have hyord : orderOf y = 3 := by
        have hdvd : orderOf y ∣ 3 := by
          have h := Subgroup.orderOf_dvd_natCard _ hy.2
          rwa [Nat.card_zpowers, huord] at h
        rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h3
        · exact absurd (orderOf_eq_one_iff.mp h1) hy1
        · exact h3
      have heq : Subgroup.zpowers y = Subgroup.zpowers u :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy.2)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, huord, hyord])
      have hu : u ∈ Subgroup.zpowers y := by rw [heq]; exact Subgroup.mem_zpowers _
      obtain ⟨k, hk⟩ := hu
      rw [← hk]
      exact Subgroup.zpow_mem _ hy.1 k
    have hzuR : Subgroup.zpowers u ≤ fc.invImageF model :=
      Subgroup.zpowers_le.mpr huR
    rw [card_sup_eq_mul_of_commute
        (fun a (ha : a ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
            * fc.toHypothesis.t) ⊔ fc.P) b (hb : b ∈ Subgroup.zpowers u) =>
          habR a (hZPR ha) b (hzuR hb))
        hinf, hZPcard, Nat.card_zpowers, huord, hRcard]
  -- pick a generator `v` of `L`
  obtain ⟨hLcyc, hLcard⟩ := fc.isCyclic_and_card_nonsplitTorus model ind hB2
  obtain ⟨g, hg⟩ := hLcyc.exists_generator
  have hLgen : Subgroup.zpowers ((g : G)) = fc.nonsplitTorus := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr g.2) ?_
    have hgtop : Subgroup.zpowers g = ⊤ := eq_top_iff.mpr fun x _ => hg x
    have hgord : orderOf ((g : G)) = 9 := by
      rw [Subgroup.orderOf_coe, ← Nat.card_zpowers, hgtop, Subgroup.card_top, hLcard]
    rw [hLcard, Nat.card_zpowers, hgord]
  -- `R₁` is generated by `N` together with `u` and `v`
  have hgen : Subgroup.closure ((((Subgroup.zpowers
        (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P)
        : Subgroup G) ∪ {u, (g : G)})
      = fc.sylowThreeNormalizerRSigma model := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      rintro y (hy | hy)
      · exact (fc.sup_le_sylowThreeNormalizerRSigma model ind hB2)
          (sup_le (sup_le (hZ₁R.trans le_sup_left) le_sup_right)
            (hPR.trans le_sup_left) hy)
      · rcases hy with rfl | rfl
        · exact (fc.sup_le_sylowThreeNormalizerRSigma model ind hB2)
            (Subgroup.mem_sup_left huR)
        · exact fc.nonsplitTorus_le_sylowThreeNormalizerRSigma model ind hB2 g.2
    · rw [← fc.sup_invImageF_centralizer_W_sup_nonsplitTorus_eq model ind hB2]
      refine sup_le (sup_le ?_ ?_) ?_
      · refine le_trans (le_of_eq hR_eq.symm) ?_
        refine sup_le (sup_le ?_ ?_) ?_
        · exact fun y hy => Subgroup.subset_closure
            (Or.inl (Subgroup.mem_sup_left (Subgroup.mem_sup_left hy)))
        · exact fun y hy => Subgroup.subset_closure
            (Or.inl (Subgroup.mem_sup_right hy))
        · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Or.inr (by simp)))
      · exact fun y hy => Subgroup.subset_closure
          (Or.inl (Subgroup.mem_sup_left (Subgroup.mem_sup_right hy)))
      · refine le_trans (le_of_eq hLgen.symm) ?_
        exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Or.inr (by simp)))
  -- apply the generic bound
  have hbound := commutator_le_of_two_generators
    (X := fc.sylowThreeNormalizerRSigma model)
    (N := (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t)
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P)
    (Z := Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t))
    (u := u) (v := (g : G))
    (fun z hz x hx => by
      have hmem : z ∈ fc.sylowThreeNormalizerRSigma model ⊓ Subgroup.centralizer
          ((fc.sylowThreeNormalizerRSigma model : Subgroup G) : Set G) := by
        rw [fc.inf_centralizer_sylowThree_eq_zpowers model ind hB2]
        exact hz
      exact (Subgroup.mem_centralizer_iff.mp hmem.2 x hx).symm)
    (fc.commutator_zpowers_sup_sigma_sup_P_sylowThree_le model ind hB2) hcommN
    ((fc.sup_le_sylowThreeNormalizerRSigma model ind hB2)
      (Subgroup.mem_sup_left huR))
    (fc.nonsplitTorus_le_sylowThreeNormalizerRSigma model ind hB2 g.2) hgen
  -- the bounding subgroup has order at most `9`
  set c : G := ⁅u, (g : G)⁆ with hc_def
  have hc3 : c ^ 3 = 1 := by
    have hcN : c ∈ (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P :=
      hcommN (Subgroup.commutator_mem_commutator
        ((fc.sup_le_sylowThreeNormalizerRSigma model ind hB2)
          (Subgroup.mem_sup_left huR))
        (fc.nonsplitTorus_le_sylowThreeNormalizerRSigma model ind hB2 g.2))
    exact (fc.pow_three_eq_one_iff_mem_zpowers_sup_sigma_sup_P model ind hB2
      (by
        refine sup_le (sup_le (fc.zpowers_le_nonsplitTorus.trans le_sup_left)
          ((inf_le_left.trans fc.toHypothesis.W_le_V).trans le_sup_right))
          (fc.P_le_V.trans le_sup_right) hcN)).mpr hcN
  have hMcard : Nat.card ↥(Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ⊔ Subgroup.zpowers c) ≤ 9 := by
    by_cases hcZ : c ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t)
    · have heq : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t) ⊔ Subgroup.zpowers c
          = Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
            * fc.toHypothesis.t) :=
        sup_eq_left.mpr (Subgroup.zpowers_le.mpr hcZ)
      rw [heq, hZ₁card]
      norm_num
    · have hcord : Nat.card ↥(Subgroup.zpowers c) ≤ 3 := by
        have hdvd : orderOf c ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hc3
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num) hdvd
      have hinf : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t) ⊓ Subgroup.zpowers c = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        rw [Subgroup.mem_bot]
        by_contra hy1
        refine hcZ ?_
        have hyord : orderOf y = 3 := by
          have hdvd : orderOf y ∣ 3 := by
            have h := Subgroup.orderOf_dvd_natCard _ hy.1
            rwa [hZ₁card] at h
          rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h3
          · exact absurd (orderOf_eq_one_iff.mp h1) hy1
          · exact h3
        have hccard : Nat.card ↥(Subgroup.zpowers c) = 3 := by
          refine le_antisymm hcord ?_
          rw [← hyord, ← Nat.card_zpowers]
          exact Nat.le_of_dvd Nat.card_pos
            (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hy.2))
        have heq : Subgroup.zpowers y = Subgroup.zpowers c :=
          Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy.2)
            (by rw [hccard, Nat.card_zpowers, hyord])
        obtain ⟨k, hk⟩ : c ∈ Subgroup.zpowers y := by
          rw [heq]; exact Subgroup.mem_zpowers _
        rw [← hk]
        exact Subgroup.zpow_mem _ hy.1 k
      have hcomm : ∀ a ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t), ∀ b ∈ Subgroup.zpowers c, a * b = b * a := by
        intro a ha b hb
        have hmem : a ∈ fc.sylowThreeNormalizerRSigma model ⊓ Subgroup.centralizer
            ((fc.sylowThreeNormalizerRSigma model : Subgroup G) : Set G) := by
          rw [fc.inf_centralizer_sylowThree_eq_zpowers model ind hB2]
          exact ha
        obtain ⟨k, rfl⟩ := hb
        have huR₁ : u ∈ fc.sylowThreeNormalizerRSigma model :=
          (fc.sup_le_sylowThreeNormalizerRSigma model ind hB2)
            (Subgroup.mem_sup_left huR)
        have hgR₁ : (g : G) ∈ fc.sylowThreeNormalizerRSigma model :=
          fc.nonsplitTorus_le_sylowThreeNormalizerRSigma model ind hB2 g.2
        have hcR₁ : c ∈ fc.sylowThreeNormalizerRSigma model := by
          rw [hc_def, commutatorElement_def]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _
            (Subgroup.mul_mem _ huR₁ hgR₁) (Subgroup.inv_mem _ huR₁))
            (Subgroup.inv_mem _ hgR₁)
        exact (Commute.zpow_right
          (Subgroup.mem_centralizer_iff.mp hmem.2 c hcR₁).symm k).eq
      rw [card_sup_eq_mul_of_commute hcomm hinf, hZ₁card]
      omega
  exact le_trans (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hbound)) hMcard

include model in
/-- **`⁅R₁, R₁⁆ ≤ Z₁ΣP`**: `Z₁ΣP` is normal in `R₁` by (16), and the quotient has
order `3⁵/27 = 9 = 3²`, hence is abelian. -/
theorem commutator_sylowThree_le_zpowers_sup_sigma_sup_P
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    ⁅fc.sylowThreeNormalizerRSigma model, fc.sylowThreeNormalizerRSigma model⁆
      ≤ (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨-, hp3, hF9, -, -, -⟩ := fc.step_twelve model ind hB2
  have hm : Nat.card F = fc.p ^ 2 := by rw [hF9, hp3]; norm_num
  have hZ₁R : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ≤ fc.invImageF model :=
    (fc.zpowers_distinguishedInvolution_mul_t_le_sInvertedT model ind hB2 hm).trans
      (fc.sInvertedT_spec model ind hB2 hm).1
  have hZSP_R₁ : ((Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P)
      ≤ fc.sylowThreeNormalizerRSigma model :=
    (sup_le (sup_le (hZ₁R.trans le_sup_left) le_sup_right)
      ((fc.P_le_invImageF model).trans le_sup_left)).trans
      (fc.sup_le_sylowThreeNormalizerRSigma model ind hB2)
  have hcommZ := fc.commutator_zpowers_sup_sigma_sup_P_sylowThree_le model ind hB2
  -- `Z₁ΣP` is normal in `R₁`
  have hnorm : (((Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t)
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P).subgroupOf
        (fc.sylowThreeNormalizerRSigma model)).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : ⁅(n : G), (g : G)⁆ ∈ Subgroup.zpowers
        (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t) :=
      hcommZ (Subgroup.commutator_mem_commutator hn g.2)
    have h1 : ((g : G) * (n : G) * (g : G)⁻¹) = ⁅(n : G), (g : G)⁆⁻¹ * (n : G) := by
      rw [commutatorElement_def]; group
    change ((g : G) * (n : G) * (g : G)⁻¹) ∈ _
    rw [h1]
    exact Subgroup.mul_mem _
      (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hc))) hn
  -- the quotient has order `9`
  have hZSPcard := fc.card_zpowers_sup_sigma_sup_P model ind hB2
  have hR₁card := fc.card_sylowThreeNormalizerRSigma model ind hB2
  have hcardQ : Nat.card (↥(fc.sylowThreeNormalizerRSigma model)
      ⧸ ((Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P).subgroupOf
          (fc.sylowThreeNormalizerRSigma model)) = 3 ^ 2 := by
    rw [← Subgroup.index_eq_card]
    have h := (((Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t)
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P).subgroupOf
        (fc.sylowThreeNormalizerRSigma model)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZSP_R₁).toEquiv, hZSPcard,
      hR₁card] at h
    omega
  have : IsMulCommutative (↥(fc.sylowThreeNormalizerRSigma model)
      ⧸ ((Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P).subgroupOf
          (fc.sylowThreeNormalizerRSigma model)) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcardQ
  -- commutators die in the quotient
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have hq := ‹IsMulCommutative _›.is_comm.comm
    (QuotientGroup.mk (⟨a, ha⟩ : ↥(fc.sylowThreeNormalizerRSigma model)))
    (QuotientGroup.mk (⟨b, hb⟩ : ↥(fc.sylowThreeNormalizerRSigma model)))
  set N₀ : Subgroup ↥(fc.sylowThreeNormalizerRSigma model) :=
    ((Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t)
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P).subgroupOf
        (fc.sylowThreeNormalizerRSigma model) with hN₀_def
  have hone : ⁅(⟨a, ha⟩ : ↥(fc.sylowThreeNormalizerRSigma model)),
      (⟨b, hb⟩ : ↥(fc.sylowThreeNormalizerRSigma model))⁆ ∈ N₀ := by
    have h1 : (QuotientGroup.mk' N₀)
        ⁅(⟨a, ha⟩ : ↥(fc.sylowThreeNormalizerRSigma model)),
          (⟨b, hb⟩ : ↥(fc.sylowThreeNormalizerRSigma model))⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr hq
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  rw [hN₀_def, Subgroup.mem_subgroupOf] at hone
  have hcoe : ((⁅(⟨a, ha⟩ : ↥(fc.sylowThreeNormalizerRSigma model)),
      (⟨b, hb⟩ : ↥(fc.sylowThreeNormalizerRSigma model))⁆ : _) : G) = ⁅a, b⁆ :=
    map_commutatorElement (fc.sylowThreeNormalizerRSigma model).subtype _ _
  rwa [hcoe] at hone

include model in
/-- **`ΣP ⊄ ⁅R₁, R₁⁆`** ((17), p. 114), with all hypotheses discharged: the commutator
subgroup has order at most `9` (alternating-form bound) while `Z₁ΣP ≤ ⁅R₁,R₁⁆` would
have order `27`. -/
theorem not_sigma_sup_P_le_commutator
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    ¬ ((fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) ⊔ fc.P)
      ≤ ⁅fc.sylowThreeNormalizerRSigma model,
        fc.sylowThreeNormalizerRSigma model⁆ :=
  fc.not_sigma_sup_P_le_commutator_sylowThree model ind hB2
    (fc.card_commutator_sylowThree_le model ind hB2
      (fc.commutator_sylowThree_le_zpowers_sup_sigma_sup_P model ind hB2))

include model in
/-- **`3 ∣ |Ab(R₂⟨s⟩)|` when `|W| = 3`** ((17), p. 114, last paragraph).

Here `R₂ = R₁`.  With `A = R₁^{ab}`, `π : R₁ → A`, `σ` induced by conjugation by `s`
and `φ : x ↦ x⁻¹·σ(x)`, the subgroup `F = π⁻¹(range φ)` is normalized by `R₁⟨s⟩` and
contains all commutators of the generators (`⁅a, s⁆` maps to `φ(π a)⁻¹`), so
`⁅R₁⟨s⟩, R₁⟨s⟩⁆ ≤ F`.  Since `ker φ` contains the nontrivial image of `ΣP`, the index
of `range φ` — hence of `F` in `R₁` — is at least `3`. -/
theorem three_dvd_card_abelianization_of_card_W_eq_three
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G)
    (hR₁S : fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G))
    (hW3 : Nat.card ↥fc.toHypothesis.W = 3) :
    (3 : ℕ) ∣ Nat.card (Abelianization ↥((S : Subgroup G)
      ⊔ Subgroup.zpowers fc.toHypothesis.distinguishedInvolution)) := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨-, hp3, hF9, -, -, hGp⟩ := fc.step_twelve model ind hB2
  set s : G := fc.toHypothesis.distinguishedInvolution with hs_def
  set R₁ : Subgroup G := fc.sylowThreeNormalizerRSigma model with hR₁_def
  have hR₁card : Nat.card ↥R₁ = 3 ^ 5 :=
    fc.card_sylowThreeNormalizerRSigma model ind hB2
  have hScard : Nat.card ↥(S : Subgroup G) = 3 ^ 5 := by
    rw [Sylow.card_eq_multiplicity, hGp, hW3]; norm_num
  have hSeq : (S : Subgroup G) = R₁ :=
    (Subgroup.eq_of_le_of_card_ge hR₁S (by rw [hScard, hR₁card])).symm
  rw [hSeq]
  have hsR₁ : ∀ a ∈ R₁, s * a * s⁻¹ ∈ R₁ := fun a ha =>
    fc.conj_mem_sylowThreeNormalizerRSigma model
      (fc.distinguishedInvolution_mem_normalizerRSigma model) ha
  have hs2 : s * s = 1 := by
    rw [← pow_two]; exact fc.toHypothesis.distinguishedInvolution_sq
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  -- the conjugation automorphism of `R₁` and the induced maps on the abelianisation
  let cs : ↥R₁ →* ↥R₁ :=
    { toFun := fun a => ⟨s * (a : G) * s⁻¹, hsR₁ (a : G) a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        change s * ((a : G) * (b : G)) * s⁻¹
          = (s * (a : G) * s⁻¹) * (s * (b : G) * s⁻¹)
        group }
  let σ : Abelianization ↥R₁ →* Abelianization ↥R₁ := Abelianization.map cs
  let φ : Abelianization ↥R₁ →* Abelianization ↥R₁ :=
    σ / MonoidHom.id (Abelianization ↥R₁)
  set Fsub : Subgroup G := (φ.range.comap (Abelianization.of (G := ↥R₁))).map R₁.subtype
    with hF_def
  have hmemF : ∀ (y : G) (hy : y ∈ R₁),
      Abelianization.of (⟨y, hy⟩ : ↥R₁) ∈ φ.range → y ∈ Fsub := fun y hy hmem =>
    ⟨⟨y, hy⟩, hmem, rfl⟩
  have hFmem : ∀ y ∈ Fsub, ∃ hy : y ∈ R₁,
      Abelianization.of (⟨y, hy⟩ : ↥R₁) ∈ φ.range := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z.2, by simpa using hz⟩
  have hFR₁ : Fsub ≤ R₁ := by rintro y ⟨z, -, rfl⟩; exact z.2
  -- conjugation by the generators preserves `Fsub`
  have hconjR₁F : ∀ x ∈ R₁, ∀ f ∈ Fsub, x * f * x⁻¹ ∈ Fsub := by
    intro x hx f hf
    obtain ⟨hfR₁, hfrange⟩ := hFmem f hf
    refine hmemF _ (R₁.mul_mem (R₁.mul_mem hx hfR₁) (R₁.inv_mem hx)) ?_
    have heq : (⟨x * f * x⁻¹, R₁.mul_mem (R₁.mul_mem hx hfR₁) (R₁.inv_mem hx)⟩ : ↥R₁)
        = ⟨x, hx⟩ * ⟨f, hfR₁⟩ * (⟨x, hx⟩ : ↥R₁)⁻¹ := rfl
    rw [heq, map_mul, map_mul, map_inv]
    have hcomm : Abelianization.of (⟨x, hx⟩ : ↥R₁)
        * Abelianization.of (⟨f, hfR₁⟩ : ↥R₁)
        * (Abelianization.of (⟨x, hx⟩ : ↥R₁))⁻¹
        = Abelianization.of (⟨f, hfR₁⟩ : ↥R₁) := by
      simp
    rw [hcomm]
    exact hfrange
  have hconjsF : ∀ f ∈ Fsub, s * f * s⁻¹ ∈ Fsub := by
    intro f hf
    obtain ⟨hfR₁, hfrange⟩ := hFmem f hf
    refine hmemF _ (hsR₁ f hfR₁) ?_
    obtain ⟨w, hw⟩ := hfrange
    have heq : (⟨s * f * s⁻¹, hsR₁ f hfR₁⟩ : ↥R₁) = cs ⟨f, hfR₁⟩ := rfl
    rw [heq, show Abelianization.of (cs (⟨f, hfR₁⟩ : ↥R₁))
      = σ (Abelianization.of (⟨f, hfR₁⟩ : ↥R₁)) from rfl, ← hw]
    refine ⟨σ w, ?_⟩
    change σ (σ w) / σ w = σ (σ w / w)
    rw [map_div]
  -- `Fsub` is normalized by `H = R₁⟨s⟩`
  set H : Subgroup G := R₁ ⊔ Subgroup.zpowers s with hH_def
  have hgenH : Subgroup.closure ((R₁ : Set G) ∪ {s}) = H := by
    rw [hH_def, Subgroup.closure_union, Subgroup.closure_eq,
      ← Subgroup.zpowers_eq_closure]
  have hHnorm : H ≤ Subgroup.normalizer (Fsub : Set G) := by
    have hbasic : ∀ x ∈ (R₁ : Set G) ∪ {s},
        x ∈ Subgroup.normalizer (Fsub : Set G) := by
      rintro x (hx | rfl)
      · rw [Subgroup.mem_set_normalizer_iff]
        intro y
        refine ⟨fun hy => hconjR₁F x hx y hy, fun hy => ?_⟩
        have h1 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
        rw [← h1]
        exact hconjR₁F x⁻¹ (R₁.inv_mem hx) _ hy
      · rw [Subgroup.mem_set_normalizer_iff]
        intro y
        refine ⟨fun hy => hconjsF y hy, fun hy => ?_⟩
        have h1 : y = s * (s * y * s⁻¹) * s⁻¹ := by
          rw [hsinv]
          calc y = (s * s) * y * (s * s) := by rw [hs2]; group
            _ = s * (s * y * s) * s := by group
        rw [h1]
        exact hconjsF _ hy
    rw [← hgenH, Subgroup.closure_le]
    exact hbasic
  have hFconj : ∀ x ∈ H, ∀ f ∈ Fsub, x * f * x⁻¹ ∈ Fsub := fun x hx f hf =>
    (Subgroup.mem_set_normalizer_iff.mp (hHnorm hx) f).mp hf
  -- the commutator of the generators lands in `Fsub`
  have hKF : ⁅H, H⁆ ≤ Fsub := by
    refine commutator_le_of_generators (T := (R₁ : Set G) ∪ {s}) hgenH hFconj ?_
    rintro a (haR₁ | rfl) b (hbR₁ | rfl)
    · refine hmemF _ (R₁.mul_mem (R₁.mul_mem (R₁.mul_mem haR₁ hbR₁)
        (R₁.inv_mem haR₁)) (R₁.inv_mem hbR₁)) ?_
      have heq : (⟨⁅a, b⁆, R₁.mul_mem (R₁.mul_mem (R₁.mul_mem haR₁ hbR₁)
            (R₁.inv_mem haR₁)) (R₁.inv_mem hbR₁)⟩ : ↥R₁)
          = ⁅(⟨a, haR₁⟩ : ↥R₁), (⟨b, hbR₁⟩ : ↥R₁)⁆ := rfl
      rw [heq, map_commutatorElement,
        show ⁅Abelianization.of (⟨a, haR₁⟩ : ↥R₁),
            Abelianization.of (⟨b, hbR₁⟩ : ↥R₁)⁆ = 1 from
          commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)]
      exact one_mem _
    · -- `⁅a, s⁆ = a·(s a⁻¹ s⁻¹)` maps to `φ(π a)⁻¹`
      have hmem : ⁅a, s⁆ ∈ R₁ := by
        have heq : ⁅a, s⁆ = a * (s * a⁻¹ * s⁻¹) := by
          rw [commutatorElement_def]; group
        rw [heq]
        exact R₁.mul_mem haR₁ (hsR₁ a⁻¹ (R₁.inv_mem haR₁))
      refine hmemF _ hmem ?_
      have heq : (⟨⁅a, s⁆, hmem⟩ : ↥R₁)
          = (⟨a, haR₁⟩ : ↥R₁) * (cs (⟨a, haR₁⟩ : ↥R₁))⁻¹ := by
        ext
        change ⁅a, s⁆ = a * (s * a * s⁻¹)⁻¹
        rw [commutatorElement_def]
        group
      rw [heq, map_mul, map_inv,
        show Abelianization.of (cs (⟨a, haR₁⟩ : ↥R₁))
          = σ (Abelianization.of (⟨a, haR₁⟩ : ↥R₁)) from rfl]
      have hinv : Abelianization.of (⟨a, haR₁⟩ : ↥R₁)
          * (σ (Abelianization.of (⟨a, haR₁⟩ : ↥R₁)))⁻¹
          = (φ (Abelianization.of (⟨a, haR₁⟩ : ↥R₁)))⁻¹ := by
        change Abelianization.of (⟨a, haR₁⟩ : ↥R₁)
            * (σ (Abelianization.of (⟨a, haR₁⟩ : ↥R₁)))⁻¹
          = (σ (Abelianization.of (⟨a, haR₁⟩ : ↥R₁))
              / Abelianization.of (⟨a, haR₁⟩ : ↥R₁))⁻¹
        rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
      rw [hinv]
      exact Subgroup.inv_mem _ ⟨_, rfl⟩
    · -- `⁅s, b⁆ = ⁅b, s⁆⁻¹`
      have hmem : ⁅b, s⁆ ∈ R₁ := by
        have heq : ⁅b, s⁆ = b * (s * b⁻¹ * s⁻¹) := by
          rw [commutatorElement_def]; group
        rw [heq]
        exact R₁.mul_mem hbR₁ (hsR₁ b⁻¹ (R₁.inv_mem hbR₁))
      have hbs : ⁅b, s⁆ ∈ Fsub := by
        refine hmemF _ hmem ?_
        have heq : (⟨⁅b, s⁆, hmem⟩ : ↥R₁)
            = (⟨b, hbR₁⟩ : ↥R₁) * (cs (⟨b, hbR₁⟩ : ↥R₁))⁻¹ := by
          ext
          change ⁅b, s⁆ = b * (s * b * s⁻¹)⁻¹
          rw [commutatorElement_def]
          group
        rw [heq, map_mul, map_inv,
          show Abelianization.of (cs (⟨b, hbR₁⟩ : ↥R₁))
            = σ (Abelianization.of (⟨b, hbR₁⟩ : ↥R₁)) from rfl]
        have hinv : Abelianization.of (⟨b, hbR₁⟩ : ↥R₁)
            * (σ (Abelianization.of (⟨b, hbR₁⟩ : ↥R₁)))⁻¹
            = (φ (Abelianization.of (⟨b, hbR₁⟩ : ↥R₁)))⁻¹ := by
          change Abelianization.of (⟨b, hbR₁⟩ : ↥R₁)
              * (σ (Abelianization.of (⟨b, hbR₁⟩ : ↥R₁)))⁻¹
            = (σ (Abelianization.of (⟨b, hbR₁⟩ : ↥R₁))
                / Abelianization.of (⟨b, hbR₁⟩ : ↥R₁))⁻¹
          rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
        rw [hinv]
        exact Subgroup.inv_mem _ ⟨_, rfl⟩
      have heq : ⁅s, b⁆ = ⁅b, s⁆⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]; group
      rw [heq]
      exact Fsub.inv_mem hbs
    · rw [show ⁅s, s⁆ = 1 by rw [commutatorElement_def]; group]
      exact Fsub.one_mem
  -- `ker φ` is nontrivial: the image of `ΣP` survives
  have hSigPR₁ : ((fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) ⊔ fc.P)
      ≤ R₁ := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact (fc.sup_le_sylowThreeNormalizerRSigma model ind hB2)
        (Subgroup.mem_sup_right hy)
    · exact (fc.sup_le_sylowThreeNormalizerRSigma model ind hB2)
        (Subgroup.mem_sup_left ((fc.P_le_invImageF model) hy))
  obtain ⟨x₀, hx₀SigP, hx₀comm⟩ : ∃ x₀ ∈ ((fc.toHypothesis.W
      ⊓ Subgroup.centralizer (fc.P : Set G)) ⊔ fc.P), x₀ ∉ ⁅R₁, R₁⁆ := by
    by_contra hcon
    push Not at hcon
    exact fc.not_sigma_sup_P_le_commutator model ind hB2 hcon
  have hx₀R₁ : x₀ ∈ R₁ := hSigPR₁ hx₀SigP
  have hkerne : φ.ker ≠ ⊥ := by
    intro hbot
    refine hx₀comm ?_
    have hfix : s * x₀ * s⁻¹ = x₀ := by
      have hcen : x₀ * s = s * x₀ := Subgroup.mem_centralizer_singleton_iff.mp
        (fc.toHypothesis.V_le_centralizer_distinguishedInvolution
          (sup_le (inf_le_left.trans fc.toHypothesis.W_le_V) fc.P_le_V hx₀SigP)).2
      rw [← hcen]; group
    have hcs : cs (⟨x₀, hx₀R₁⟩ : ↥R₁) = ⟨x₀, hx₀R₁⟩ := by ext; exact hfix
    have hker : φ (Abelianization.of (⟨x₀, hx₀R₁⟩ : ↥R₁)) = 1 := by
      change σ (Abelianization.of (⟨x₀, hx₀R₁⟩ : ↥R₁))
        / Abelianization.of (⟨x₀, hx₀R₁⟩ : ↥R₁) = 1
      rw [show σ (Abelianization.of (⟨x₀, hx₀R₁⟩ : ↥R₁))
        = Abelianization.of (cs (⟨x₀, hx₀R₁⟩ : ↥R₁)) from rfl, hcs, div_self']
    have hmem : Abelianization.of (⟨x₀, hx₀R₁⟩ : ↥R₁) ∈ φ.ker :=
      MonoidHom.mem_ker.mpr hker
    rw [hbot, Subgroup.mem_bot] at hmem
    have hmem2 : (⟨x₀, hx₀R₁⟩ : ↥R₁) ∈ commutator ↥R₁ := by
      rwa [← Abelianization.ker_of, MonoidHom.mem_ker]
    have hmap : (commutator ↥R₁).map R₁.subtype = ⁅R₁, R₁⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    rw [← hmap]
    exact ⟨_, hmem2, rfl⟩
  -- hence `Fsub` has index at least `3` in `R₁`
  have hπsurj : Function.Surjective (Abelianization.of (G := ↥R₁)) := by
    intro y
    obtain ⟨g, rfl⟩ := Quot.exists_rep y
    exact ⟨g, rfl⟩
  have hFindex : 3 ≤ (φ.range.comap (Abelianization.of (G := ↥R₁))).index := by
    rw [Subgroup.index_comap_of_surjective _ hπsurj, index_range_eq_card_ker]
    have hAdvd : Nat.card (Abelianization ↥R₁) ∣ 3 ^ 5 := by
      rw [← hR₁card]
      have h := (commutator ↥R₁).index_dvd_card
      rwa [Subgroup.index_eq_card] at h
    have h1 : Nat.card ↥φ.ker ∣ 3 ^ 5 :=
      dvd_trans (Subgroup.card_dvd_of_le (le_top : φ.ker ≤ ⊤))
        (by rw [Subgroup.card_top]; exact hAdvd)
    have h2 : Nat.card ↥φ.ker ≠ 1 := fun h => hkerne (Subgroup.card_eq_one.mp h)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num)).mp h1
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact absurd (by rw [hj]; norm_num) h2
    · rw [hj]
      calc (3 : ℕ) = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hjpos
  -- `|Fsub| ≤ 3⁴`
  have hFcard : Nat.card ↥Fsub ≤ 3 ^ 4 := by
    have hFeq : Nat.card ↥Fsub
        = Nat.card ↥(φ.range.comap (Abelianization.of (G := ↥R₁))) := by
      rw [hF_def, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    have hmul := (φ.range.comap (Abelianization.of (G := ↥R₁))).card_mul_index
    have hcardA : Nat.card (Abelianization ↥R₁) ≤ 3 ^ 5 := by
      have hAdvd : Nat.card (Abelianization ↥R₁) ∣ 3 ^ 5 := by
        rw [← hR₁card]
        have h := (commutator ↥R₁).index_dvd_card
        rwa [Subgroup.index_eq_card] at h
      exact Nat.le_of_dvd (by norm_num) hAdvd
    nlinarith [hmul, hFeq, hFindex, hcardA, Nat.card_pos (α := ↥Fsub)]
  -- conclude: `|⁅H,H⁆| ≤ 3⁴` and `|H| = 2·3⁵`
  have hFsubR₁ : Fsub ≤ R₁ := hFR₁
  have hKcard_le : Nat.card ↥(⁅H, H⁆ : Subgroup G) ≤ 3 ^ 4 :=
    le_trans (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hKF)) hFcard
  have hKdvd : Nat.card ↥(⁅H, H⁆ : Subgroup G) ∣ 3 ^ 5 := by
    rw [← hR₁card]
    exact Subgroup.card_dvd_of_le (hKF.trans hFsubR₁)
  have hsord : orderOf s = 2 :=
    orderOf_eq_prime fc.toHypothesis.distinguishedInvolution_sq
      fc.toHypothesis.distinguishedInvolution_ne_one
  have hHcard : Nat.card ↥H = 3 ^ 5 * 2 := by
    rw [hH_def, card_sup_eq_mul_of_le_normalizer (fun b hb => ?_)
        (fc.sylowThree_sup_zpowers_distinguishedInvolution model ind hB2).2,
      hR₁card, Nat.card_zpowers, hsord]
    obtain ⟨k, rfl⟩ := hb
    rw [Subgroup.mem_set_normalizer_iff]
    intro y
    have hsk : ∀ a ∈ R₁, s ^ k * a * (s ^ k)⁻¹ ∈ R₁ := fun a ha =>
      fc.conj_mem_sylowThreeNormalizerRSigma model
        (Subgroup.zpow_mem _ (fc.distinguishedInvolution_mem_normalizerRSigma model) k)
        ha
    refine ⟨fun hy => hsk y hy, fun hy => ?_⟩
    have h1 : (s ^ k)⁻¹ * (s ^ k * y * (s ^ k)⁻¹) * ((s ^ k)⁻¹)⁻¹ = y := by group
    rw [← h1]
    exact fc.conj_mem_sylowThreeNormalizerRSigma model
      (Subgroup.inv_mem _ (Subgroup.zpow_mem _
        (fc.distinguishedInvolution_mem_normalizerRSigma model) k)) hy
  -- the commutator subgroup of `↥H` has the same order as `⁅H, H⁆`
  have hcommmap : (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hcommcard : Nat.card ↥(commutator ↥H) = Nat.card ↥(⁅H, H⁆ : Subgroup G) := by
    rw [← hcommmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hmul := (commutator ↥H).card_mul_index
  rw [hcommcard, hHcard] at hmul
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num)).mp hKdvd
  have hj4 : j ≤ 4 := by
    by_contra hcon
    push Not at hcon
    have h1 : (3 : ℕ) ^ 5 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hcon
    rw [hj] at hKcard_le
    have h2 : (3 : ℕ) ^ 5 ≤ 3 ^ 4 := le_trans h1 hKcard_le
    norm_num at h2
  rw [hj] at hmul
  have hidxeq : Nat.card (Abelianization ↥H) = (commutator ↥H).index :=
    (Subgroup.index_eq_card _).symm
  rw [hidxeq]
  refine ⟨2 * 3 ^ (4 - j), ?_⟩
  have hpow : (3 : ℕ) ^ j * (3 * (2 * 3 ^ (4 - j))) = 3 ^ 5 * 2 := by
    have hsplit : (3 : ℕ) ^ j * 3 ^ (4 - j) = 3 ^ 4 := by
      rw [← pow_add]
      congr 1
      omega
    calc (3 : ℕ) ^ j * (3 * (2 * 3 ^ (4 - j)))
        = 6 * (3 ^ j * 3 ^ (4 - j)) := by ring
      _ = 6 * 3 ^ 4 := by rw [hsplit]
      _ = 3 ^ 5 * 2 := by norm_num
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by norm_num : 0 < 3))
    (by rw [hmul, ← hpow])

/-! ## The endpoint of (17) -/

include model in
/-- **The final contradiction of (17)** (p. 114), as an engine parameterised by its two
remaining inputs.

* `hcontrol` is the transfer-control conclusion: by the weak closure of the abelian
  `Z₁PΣ` in `R₂` (`map_conj_eq_of_le_sylow`), the Hall–Wielandt theorem gives
  `G/O³(G) ≅ N_G(Z₁PΣ)/O³(N_G(Z₁PΣ))`, so hypothesis (B2) (`p ∤ |G^{ab}|`) transports
  to `N_G(Z₁PΣ)`.  See issue 9503.
* `hW3` is the `|W| = 3` branch, where `R₂ = R₁` and the structure of `R̄₁ = R₁/Z₁`
  produces the quotient of order `3`; the `|W| = 9` branch is
  `three_dvd_card_abelianization_of_card_W_eq_nine`, proved above. -/
theorem false_of_transfer_control
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G)
    (hR₁S : fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G))
    (hcontrol : ¬ (3 : ℕ) ∣ Nat.card (Abelianization
      ↥(Subgroup.normalizer ((((Subgroup.zpowers
            (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
          ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P)
            : Subgroup G) : Set G))))
    (hW3 : Nat.card ↥fc.toHypothesis.W = 3 →
      (3 : ℕ) ∣ Nat.card (Abelianization ↥((S : Subgroup G)
        ⊔ Subgroup.zpowers fc.toHypothesis.distinguishedInvolution))) :
    False := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  obtain ⟨-, -, -, -, hW, -⟩ := fc.step_twelve model ind hB2
  have hNeq : Subgroup.normalizer ((((Subgroup.zpowers
        (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P)
        : Subgroup G) : Set G)
      = (S : Subgroup G)
        ⊔ Subgroup.zpowers fc.toHypothesis.distinguishedInvolution := by
    rw [← fc.normalizer_zpowers_eq_normalizer_zpowers_sup_sigma_sup_P model ind hB2
      S hR₁S]
    exact fc.normalizer_zpowers_eq_sylow_sup_zpowers model ind hB2 S hR₁S
  rw [hNeq] at hcontrol
  rcases hW with h3 | h9
  · exact hcontrol (hW3 h3)
  · exact hcontrol
      (fc.three_dvd_card_abelianization_of_card_W_eq_nine model ind hB2 S hR₁S h9)

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
