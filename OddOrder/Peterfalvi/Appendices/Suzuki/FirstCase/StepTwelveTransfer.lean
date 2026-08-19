/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch10_MoreTransfer.Yoshida
import OddOrder.GroupTheory.TransferInvariantTransversal
import OddOrder.GroupTheory.TransferTransitivity
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepTwelveConclusion

/-!
# Peterfalvi Part II, Ch. II, step (12): the transfer contradiction

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (12), p. 113 (end of the first case).

If `|G|_p = p³` then `R₁` is a Sylow `p`-subgroup of `G` of nilpotence class
`2 < p`, so `N := N_G(R₁) = N_G(R)` controls `p`-transfer (Isaacs Cor 10.2,
the Hall–Wielandt strengthening via Yoshida).  Hypothesis (B2)
(`p ∤ |G^{ab}|`) makes the `G`-transfer into `R₁^{ab}` trivial, hence the
`N`-level transfer is trivial as well.  But `[N_G(R), R₁] ≤ T₁` forces the
`N`-level transfer to agree with `x ↦ x^{[N : R₁]}` modulo `T₁`, and
`p ∤ [N : R₁]`, which would push all of `R₁` into the index-`p` subgroup
`T₁` — absurd.  Consequently `(Nat.card G).factorization p ≠ 3` under the
standing hypotheses of the first case.
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
/-- **`R₁` has nilpotence class at most `2`** ((12) tail, ε2 preparation):
`⁅R₁, R₁⁆ = T` (the commutator computation) is central in `R₁` (δ4a), so the
lower central series of `R₁` reaches `⊥` at step `2`. -/
theorem nilpotencyClass_overgroup_le_two
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hRle : fc.invImageF model ≤ R₁)
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3) :
    Group.nilpotencyClass ↥R₁ ≤ 2 := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  have : Fact fc.p.Prime := ⟨fc.p_prime⟩
  have : Group.IsNilpotent ↥R₁ := (IsPGroup.of_card hcard).isNilpotent
  have hcommT := fc.commutator_eq_sInvertedT model ind hB2 hm hGp hSigma hRle
    hR₁le hcard
  have hcomm := fc.sInvertedT_mul_comm_of_mem model ind hB2 hm hGp hSigma
    hR₁le hcard
  rw [← Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.lowerCentralSeries_succ,
    Subgroup.top_lowerCentralSeries_one,
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  -- every commutator of `R₁` is central: it lies in `T` (via `⁅R₁,R₁⁆ = T`).
  intro c hc
  have hcG : (c : G) ∈ fc.sInvertedT model := by
    rw [← hcommT, ← Subgroup.map_subtype_commutator]
    exact Subgroup.mem_map_of_mem _ hc
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact Subtype.ext (hcomm (c : G) hcG (b : G) b.2)

include model in
/-- **Step (12), conclusion of the first case — `|G|_p ≠ p³`** (ε2/ε3, the
transfer contradiction, p. 113): if `|G|_p = p³` then `R₁` is a Sylow
`p`-subgroup of class `2 < p`, so `N_G(R₁)` controls `p`-transfer
(Isaacs Cor 10.2); by (B2) the `G`-transfer into `R₁^{ab}` is trivial, hence so
is the `N_G(R₁)`-level transfer; but modulo `T₁` the latter evaluates on
`x ∈ R₁` as `x^{[N_G(R₁) : R₁]}` (its factors are conjugates `s⁻¹xs ≡ x mod
⁅N_G(R), R₁⁆ ≤ T₁`), and `p ∤ [N_G(R₁) : R₁]`, so all of `R₁` would collapse
into the index-`p` subgroup `T₁` — contradicting `|T₁| = p² < p³ = |R₁|`. -/
theorem factorization_ne_three
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) :
    (Nat.card G).factorization fc.p ≠ 3 := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  have : Fact fc.p.Prime := ⟨fc.p_prime⟩
  intro hfact
  obtain ⟨R₁, hRle, hR₁le, hcard, hR₁n⟩ :=
    fc.exists_normal_overgroup_cube model ind hB2 hm hGp hSigma
  obtain ⟨hT₁card, hTsubT₁, -⟩ := fc.card_sInvertedOvergroup model ind hB2 hm
    hGp hSigma hRle hR₁le hcard hR₁n
  have hcommT := fc.commutator_eq_sInvertedT model ind hB2 hm hGp hSigma hRle
    hR₁le hcard
  have hδ4 := fc.normalizer_overgroup_eq_normalizer_invImageF model ind hB2 hm
    hGp hfact hSigma hRle hR₁le hcard hR₁n
  -- `R₁` is a Sylow `p`-subgroup carrying the full `p`-part `p³`.
  have hcard' : Nat.card ↥R₁ = fc.p ^ (Nat.card G).factorization fc.p := by
    rw [hcard, hfact]
  set P₁ : Sylow fc.p G := Sylow.ofCard R₁ hcard' with hP₁_def
  -- nilpotence class `2 < p` (`p` is an odd prime).
  have hclass : Group.nilpotencyClass ↥((P₁ : Subgroup G)) < fc.p := by
    have h1 : Group.nilpotencyClass ↥R₁ ≤ 2 :=
      fc.nilpotencyClass_overgroup_le_two model ind hB2 hm hGp hSigma hRle
        hR₁le hcard
    have h2 : 3 ≤ fc.p := by
      obtain ⟨j, hj⟩ := fc.p_odd
      have h3 := fc.p_prime.two_le
      omega
    have h4 : Group.nilpotencyClass ↥((P₁ : Subgroup G)) ≤ 2 := h1
    omega
  -- Isaacs Cor 10.2: the `G`- and `N`-level transfer images agree.
  have hrange := OddOrder.Isaacs.Ch10.transfer_range_eq_of_nilpotencyClass_lt
    P₁ hclass
  -- (B2): the `G`-transfer into `R₁^{ab}` is trivial.
  have hvbot : (MonoidHom.transfer
      (Abelianization.of (G := ↥((P₁ : Subgroup G))))).range = ⊥ :=
    OddOrder.GroupTheory.transfer_abelianization_range_eq_bot
      (IsPGroup.of_card
        (show Nat.card ↥((P₁ : Subgroup G)) = fc.p ^ 3 from hcard)) hB2
  rw [hvbot] at hrange
  -- hence every `N`-level transfer value is trivial.
  have hwzero : ∀ n : ↥(Subgroup.normalizer ((P₁ : Subgroup G) : Set G)),
      MonoidHom.transfer (OddOrder.GroupTheory.transferRes Subgroup.le_normalizer
        (Abelianization.of (G := ↥((P₁ : Subgroup G))))) n = 1 := by
    intro n
    have h1 : MonoidHom.transfer (OddOrder.GroupTheory.transferRes
        Subgroup.le_normalizer (Abelianization.of (G := ↥((P₁ : Subgroup G))))) n
        ∈ (MonoidHom.transfer (OddOrder.GroupTheory.transferRes
          Subgroup.le_normalizer
          (Abelianization.of (G := ↥((P₁ : Subgroup G)))))).range :=
      ⟨n, rfl⟩
    rw [← hrange] at h1
    exact Subgroup.mem_bot.mp h1
  -- the image of `T₁` in the abelianisation, and the quotient by it.
  set Tbar : Subgroup (Abelianization ↥((P₁ : Subgroup G))) :=
    Subgroup.map (Abelianization.of)
      ((fc.sInvertedOvergroup R₁).subgroupOf ((P₁ : Subgroup G))) with hTbar_def
  have hTbarN : Tbar.Normal := ⟨fun n hn g => by
    rw [mul_comm g n, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
  set π := QuotientGroup.mk' Tbar with hπ_def
  -- membership transport: the normalizer of `R₁` is `N_G(R)` (δ4).
  have hKNR : ∀ s : G, s ∈ Subgroup.normalizer ((P₁ : Subgroup G) : Set G) →
      s ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) := by
    intro s hs
    rw [← hδ4]
    exact hs
  -- the transfer computation pushes every `x ∈ R₁` into `T₁`.
  have hkey : ∀ x ∈ R₁, x ∈ fc.sInvertedOvergroup R₁ := by
    intro x hx
    set K : Subgroup G := Subgroup.normalizer ((P₁ : Subgroup G) : Set G)
      with hK_def
    have hR₁K : R₁ ≤ K := Subgroup.le_normalizer
    set xhat : ↥K := ⟨x, hR₁K hx⟩ with hxhat_def
    have hxhatH : xhat ∈ ((P₁ : Subgroup G)).subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    set xbar : ↥((P₁ : Subgroup G)) := ⟨x, hx⟩ with hxbar_def
    have hψ₀ : (OddOrder.GroupTheory.transferRes Subgroup.le_normalizer
        (Abelianization.of (G := ↥((P₁ : Subgroup G))))) ⟨xhat, hxhatH⟩
        = Abelianization.of xbar := by
      rw [OddOrder.GroupTheory.transferRes_apply]
    -- conjugates of `xhat` stay in `R₁` …
    have hmem : ∀ s : ↥K, s⁻¹ * xhat * s ∈ ((P₁ : Subgroup G)).subgroupOf K := by
      intro s
      rw [Subgroup.mem_subgroupOf]
      have h2 := hR₁n (s : G)⁻¹
        (Subgroup.inv_mem _ (hKNR (s : G) s.2)) x hx
      rw [inv_inv] at h2
      exact h2
    -- … with constant value modulo `T₁` (`⁅N_G(R), R₁⁆ ≤ T₁`, ε1).
    have hϕinv : ∀ s : ↥K,
        (π.comp (OddOrder.GroupTheory.transferRes Subgroup.le_normalizer
          (Abelianization.of (G := ↥((P₁ : Subgroup G))))))
          ⟨s⁻¹ * xhat * s, hmem s⟩
          = (π.comp (OddOrder.GroupTheory.transferRes Subgroup.le_normalizer
            (Abelianization.of (G := ↥((P₁ : Subgroup G))))))
            ⟨xhat, hxhatH⟩ := by
      intro s
      simp only [MonoidHom.comp_apply, OddOrder.GroupTheory.transferRes_apply,
        hπ_def, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      rw [← map_inv, ← map_mul]
      refine Subgroup.mem_map_of_mem _ ?_
      rw [Subgroup.mem_subgroupOf]
      have hcomm := fc.commutator_mem_sInvertedOvergroup model ind hB2 hm hGp
        hSigma hRle hR₁le hcard hR₁n (k := (s : G)⁻¹) (y := x⁻¹)
        (Subgroup.inv_mem _ (hKNR (s : G) s.2)) (Subgroup.inv_mem _ hx)
      have heq2 : ((s : G)⁻¹ * x * (s : G))⁻¹ * x = ⁅(s : G)⁻¹, x⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [← heq2] at hcomm
      exact hcomm
    -- transfer evaluation: `π(of x) ^ [K : R₁] = π(w xhat) = 1`.
    have htrans := OddOrder.GroupTheory.transfer_eq_pow_of_map_conj_eq
      (π.comp (OddOrder.GroupTheory.transferRes Subgroup.le_normalizer
        (Abelianization.of (G := ↥((P₁ : Subgroup G)))))) hxhatH hmem hϕinv
    rw [OddOrder.GroupTheory.transfer_comp_left, MonoidHom.comp_apply,
      hwzero xhat, map_one] at htrans
    -- the exponent is prime to `p` while the base lives in a `p`-group.
    set a := (π.comp (OddOrder.GroupTheory.transferRes Subgroup.le_normalizer
      (Abelianization.of (G := ↥((P₁ : Subgroup G)))))) ⟨xhat, hxhatH⟩
      with ha_def
    have hpm : ¬ fc.p ∣ (((P₁ : Subgroup G)).subgroupOf K).index :=
      fc.not_p_dvd_index_subgroupOf_normalizer_overgroup hfact hcard hR₁K
    have hAb : IsPGroup fc.p (Abelianization ↥((P₁ : Subgroup G))) :=
      (IsPGroup.of_card
        (show Nat.card ↥((P₁ : Subgroup G)) = fc.p ^ 3 from hcard)).to_quotient
          (_root_.commutator ↥((P₁ : Subgroup G)))
    have hQp : IsPGroup fc.p
        (Abelianization ↥((P₁ : Subgroup G)) ⧸ Tbar) := hAb.to_quotient Tbar
    have : Finite (Abelianization ↥((P₁ : Subgroup G))) := Quotient.finite _
    have : Finite (Abelianization ↥((P₁ : Subgroup G)) ⧸ Tbar) :=
      Quotient.finite _
    obtain ⟨k, hk⟩ := hQp.exists_card_eq
    have h_am : a ^ (((P₁ : Subgroup G)).subgroupOf K).index = 1 := htrans.symm
    have h_apk : a ^ (fc.p ^ k) = 1 := by
      rw [← hk]
      exact pow_card_eq_one'
    have hord1 : orderOf a ∣ (((P₁ : Subgroup G)).subgroupOf K).index :=
      orderOf_dvd_of_pow_eq_one h_am
    have hord2 : orderOf a ∣ fc.p ^ k := orderOf_dvd_of_pow_eq_one h_apk
    have hcop : Nat.Coprime (fc.p ^ k) (((P₁ : Subgroup G)).subgroupOf K).index :=
      ((Nat.Prime.coprime_iff_not_dvd fc.p_prime).mpr hpm).pow_left k
    have ha1 : a = 1 := by
      have h5 := Nat.dvd_gcd hord2 hord1
      rw [Nat.Coprime.gcd_eq_one hcop] at h5
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)
    -- unfold `a`: `of x ∈ T̄₁`, hence `x ∈ T·T₁ = T₁`.
    rw [ha_def, MonoidHom.comp_apply, hψ₀, hπ_def, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha1
    obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.mp ha1
    have hker : xbar * t⁻¹ ∈ _root_.commutator ↥((P₁ : Subgroup G)) := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_inv, hteq,
        mul_inv_cancel]
    have h6 : ((xbar * t⁻¹ : ↥((P₁ : Subgroup G))) : G) ∈ fc.sInvertedT model := by
      rw [← hcommT, ← Subgroup.map_subtype_commutator]
      exact Subgroup.mem_map_of_mem _ hker
    have h7 : (t : G) ∈ fc.sInvertedOvergroup R₁ := Subgroup.mem_subgroupOf.mp ht
    have h12 : ((xbar * t⁻¹ * t : ↥((P₁ : Subgroup G))) : G)
        ∈ fc.sInvertedOvergroup R₁ :=
      mul_mem (hTsubT₁ h6) h7
    have h11 : xbar * t⁻¹ * t = xbar := by group
    rw [h11] at h12
    exact h12
  -- `R₁ ≤ T₁` is absurd: `p³ ≤ p²`.
  have hcardle := Subgroup.card_le_of_le hkey
  rw [hcard, hT₁card] at hcardle
  have hlt := Nat.pow_lt_pow_right fc.p_prime.one_lt (show 2 < 3 by omega)
  omega

include model in
/-- **Peterfalvi Part II, Ch. II, step (12)** (p. 112): *Case (10.2) holds.*

Assume case (10.1).  The index theorem `[N_G(R) : R] = p^m·|Q̄|·|Σ|` gives
`p^{2m+1} ∣ |N_G(R)| ∣ |G|` (the cofactor `|Q̄|·|Σ|` is prime to `p`), so
`2m + 1 ≤ m + 2`, i.e. `m = 1`; but `m = 1` with `|G|_p = p³` is killed by the
transfer contradiction (`factorization_ne_three`).  Hence the dichotomy of
step (10) lands in case (10.2). -/
theorem step_twelve
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    fc.p ∣ Nat.card ↥(fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) ∧
      fc.p = 3 ∧ Nat.card F = 9 ∧ IsCyclic ↥fc.toHypothesis.W ∧
      (Nat.card ↥fc.toHypothesis.W = 3 ∨ Nat.card ↥fc.toHypothesis.W = 9) ∧
      3 ^ (Nat.card G).factorization 3 = 3 ^ 4 * Nat.card ↥fc.toHypothesis.W := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  have : Fact fc.p.Prime := ⟨fc.p_prime⟩
  obtain ⟨m, hm1, hm⟩ := fc.card_field_eq_prime_pow model hB2
  rcases fc.step_ten_dichotomy ind model hB2 hm with ⟨hnSig, hfact⟩ | h102
  · -- case (10.1): first `m = 1`, then the transfer contradiction.
    exfalso
    obtain ⟨e⟩ := fc.sigma_mulEquiv_centralizer_W ind
    have hSigma : ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D := by
      rw [Nat.card_congr e.toEquiv]
      exact hnSig
    have hGp : fc.p ^ (m + 2) ∣ Nat.card G := by
      rw [← hfact]
      exact Nat.ordProj_dvd _ _
    have hidx := fc.index_invImageF_subgroupOf_normalizer model ind hB2 hm hGp
      hSigma
    set NR : Subgroup G :=
      Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) with hNRdef
    have hleR : fc.invImageF model ≤ NR := Subgroup.le_normalizer
    have hlagR := ((fc.invImageF model).subgroupOf NR).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hleR).toEquiv,
      fc.card_invImageF model ind, hidx] at hlagR
    -- `p^{2m+1} ∣ |N_G(R)| ∣ |G|`.
    have h2m1 : fc.p ^ (2 * m + 1) ∣ Nat.card G := by
      refine dvd_trans ⟨Nat.card ↥(fc.rankOneQuotient).Q
        * Nat.card ↥(fc.rankOneQuotient).D, ?_⟩
        (Subgroup.card_subgroup_dvd_card NR)
      rw [← hlagR, hm, fc.card_P]
      ring
    have hle : 2 * m + 1 ≤ m + 2 := by
      have h3 := (Nat.Prime.pow_dvd_iff_le_factorization fc.p_prime
        Nat.card_pos.ne').mp h2m1
      rw [hfact] at h3
      exact h3
    have hmeq : m = 1 := by omega
    subst hmeq
    exact fc.factorization_ne_three model ind hB2 hm hGp hSigma hfact
  · exact h102

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
