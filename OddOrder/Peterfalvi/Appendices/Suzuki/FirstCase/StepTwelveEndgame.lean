/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepTwelve

/-!
# Peterfalvi Part II, Ch. II, step (12): the endgame

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (12), pp. 112–113 (conclusion).

The `s`-inverted complement `T₁ ≤ R₁` (order `p²`, all of whose nonidentity
elements are strongly real), the identification `N_G(R₁) = N_G(R)`, and the
final Hall–Wielandt/transfer contradiction with hypothesis (B2).
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

/-- **`T₁`: the `s`-inverted part of `R₁`** ((12), p. 112).  Defined as a closure so
that it is a subgroup unconditionally; under the step-(12) hypotheses the generating
set is itself closed under multiplication (`mul_comm_of_conj_eq_inv`), see
`sInvertedOvergroup_spec`. -/
def sInvertedOvergroup (R₁ : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ R₁ ∧ fc.toHypothesis.distinguishedInvolution * x
    * fc.toHypothesis.distinguishedInvolution⁻¹ = x⁻¹}

include model in
/-- **Membership in `T₁`** collapses to the generating set: the `s`-inverted elements
of `R₁` form a subgroup (they commute pairwise). -/
theorem mem_sInvertedOvergroup_iff
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hRle : fc.invImageF model ≤ R₁)
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3) {x : G} :
    x ∈ fc.sInvertedOvergroup R₁ ↔ x ∈ R₁ ∧
      fc.toHypothesis.distinguishedInvolution * x
        * fc.toHypothesis.distinguishedInvolution⁻¹ = x⁻¹ := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  set s : G := fc.toHypothesis.distinguishedInvolution with hsdef
  have hs2 : s * s = 1 := by
    have h := fc.toHypothesis.distinguishedInvolution_sq
    rwa [pow_two] at h
  set S₁ : Set G := {y : G | y ∈ R₁ ∧ s * y * s⁻¹ = y⁻¹} with hS₁def
  have hsub : ∃ H : Subgroup G, (H : Set G) = S₁ := by
    refine ⟨⟨⟨⟨S₁, ?_⟩, ?_⟩, ?_⟩, rfl⟩
    · -- mul_mem
      rintro a b ⟨haR, hai⟩ ⟨hbR, hbi⟩
      refine ⟨mul_mem haR hbR, ?_⟩
      have hcomm := fc.mul_comm_of_conj_eq_inv model ind hB2 hm hGp hSigma hRle
        hR₁le hcard haR hbR hai hbi
      calc s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
        _ = a⁻¹ * b⁻¹ := by rw [hai, hbi]
        _ = (b * a)⁻¹ := by rw [mul_inv_rev]
        _ = (a * b)⁻¹ := by rw [hcomm]
    · -- one_mem
      exact ⟨one_mem _, by simp⟩
    · -- inv_mem
      rintro a ⟨haR, hai⟩
      refine ⟨inv_mem haR, ?_⟩
      calc s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ := by group
        _ = (a⁻¹)⁻¹ := by rw [hai]
  obtain ⟨H, hH⟩ := hsub
  have h1 : fc.sInvertedOvergroup R₁ = H := by
    have h2 : fc.sInvertedOvergroup R₁ = Subgroup.closure S₁ := rfl
    rw [h2, ← hH, Subgroup.closure_eq]
  rw [h1, ← SetLike.mem_coe, hH]
  exact Iff.rfl

include model in
/-- **`|T₁| = p²`, `T ≤ T₁`, and `T₁ ⊓ P = ⊥`** ((12), p. 112): the twisted-cocycle
map `g ↦ (s g s⁻¹)·g⁻¹` has fibers the cosets of `C_{R₁}(s) = P`, so its image —
inside `T₁` — has `p²` elements; conversely `T₁ ∩ P = 1` keeps `|T₁| ∣ p³` at `p²`. -/
theorem card_sInvertedOvergroup
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hRle : fc.invImageF model ≤ R₁)
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3)
    (hR₁n : ∀ n ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G),
      ∀ x ∈ R₁, n * x * n⁻¹ ∈ R₁) :
    Nat.card ↥(fc.sInvertedOvergroup R₁) = fc.p ^ 2 ∧
      fc.sInvertedT model ≤ fc.sInvertedOvergroup R₁ ∧
      fc.sInvertedOvergroup R₁ ⊓ fc.P = ⊥ := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  have : Fact fc.p.Prime := ⟨fc.p_prime⟩
  set s : G := fc.toHypothesis.distinguishedInvolution with hsdef
  have hs2 : s * s = 1 := by
    have h := fc.toHypothesis.distinguishedInvolution_sq
    rwa [pow_two] at h
  have hmemiff := fun (x : G) =>
    fc.mem_sInvertedOvergroup_iff model ind hB2 hm hGp hSigma hRle hR₁le hcard (x := x)
  obtain ⟨hTle, hTinv, -, -⟩ := fc.sInvertedT_spec model ind hB2 hm
  have hsNR : s ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) :=
    fc.distinguishedInvolution_mem_normalizer_invImageF model ind hB2 hm
  -- `T ≤ T₁`.
  have hTsub : fc.sInvertedT model ≤ fc.sInvertedOvergroup R₁ := by
    intro t ht
    rw [hmemiff]
    exact ⟨hRle (hTle ht), hTinv t ht⟩
  -- `T₁ ⊓ P = ⊥`.
  have hinfP : fc.sInvertedOvergroup R₁ ⊓ fc.P = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Subgroup.mem_bot]
    rw [hmemiff] at hx1
    have h1 : s * x * s⁻¹ = x := by
      have h2 := Subgroup.mem_centralizer_iff.mp
        (fc.toHypothesis.distinguishedInvolution_mem_centralizer_of_le_V fc.P_le_V) x hx2
      rw [← hsdef] at h2
      rw [← h2]
      group
    have h3 : x = x⁻¹ := by rw [← hx1.2, h1]
    have h4 : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [h3]
      group
    have h5 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h4
    have h6 : x ^ fc.p = 1 := fc.pow_p_eq_one_of_mem_invImageF model ind hB2 hm
      (fc.P_le_invImageF model hx2)
    have h7 : orderOf x ∣ fc.p := orderOf_dvd_of_pow_eq_one h6
    obtain ⟨j, hj⟩ := fc.p_odd
    have h8 := Nat.dvd_gcd h5 h7
    have h9 : Nat.gcd 2 fc.p = 1 :=
      (Nat.coprime_primes Nat.prime_two fc.p_prime).mpr (by omega)
    rw [h9, Nat.dvd_one] at h8
    exact orderOf_eq_one_iff.mp h8
  -- lower bound `p²` via the twisted-cocycle map on `R₁ ⧸ P`.
  have hPle : fc.P ≤ R₁ := (fc.P_le_invImageF model).trans hRle
  set C' : Subgroup ↥R₁ := fc.P.subgroupOf R₁ with hC'def
  have hFwd : ∀ g : ↥R₁, (s * (g : G) * s⁻¹) * (g : G)⁻¹ ∈ fc.sInvertedOvergroup R₁ := by
    intro g
    rw [hmemiff]
    constructor
    · exact mul_mem (hR₁n s hsNR _ g.2) (inv_mem g.2)
    · have hss : s⁻¹ = s := by
        rw [← mul_one s⁻¹, ← hs2, ← mul_assoc, inv_mul_cancel, one_mul]
      have hexp : ((s * (g : G) * s⁻¹) * (g : G)⁻¹)⁻¹
          = (g : G) * s * (g : G)⁻¹ * s⁻¹ := by group
      rw [hexp, hss]
      calc s * (s * (g : G) * s * (g : G)⁻¹) * s
          = (s * s) * ((g : G) * s * (g : G)⁻¹ * s) := by group
        _ = (g : G) * s * (g : G)⁻¹ * s := by rw [hs2, one_mul]
  have hSound : ∀ a b : ↥R₁, (a : G)⁻¹ * (b : G) ∈ fc.P →
      (s * (a : G) * s⁻¹) * (a : G)⁻¹ = (s * (b : G) * s⁻¹) * (b : G)⁻¹ := by
    intro a b hab
    have h1 : s * ((a : G)⁻¹ * (b : G)) * s⁻¹ = (a : G)⁻¹ * (b : G) := by
      have h2 := Subgroup.mem_centralizer_iff.mp
        (fc.toHypothesis.distinguishedInvolution_mem_centralizer_of_le_V fc.P_le_V)
        _ hab
      rw [← hsdef] at h2
      rw [← h2]
      group
    -- `s b s⁻¹ = s a s⁻¹ · a⁻¹ b`.
    have h3 : s * (b : G) * s⁻¹ = (s * (a : G) * s⁻¹) * ((a : G)⁻¹ * (b : G)) := by
      calc s * (b : G) * s⁻¹
          = (s * (a : G) * s⁻¹) * (s * ((a : G)⁻¹ * (b : G)) * s⁻¹) := by group
        _ = (s * (a : G) * s⁻¹) * ((a : G)⁻¹ * (b : G)) := by rw [h1]
    rw [h3]
    group
  -- descend to the quotient and inject into `T₁`.
  let Fbar : (↥R₁ ⧸ C') → ↥(fc.sInvertedOvergroup R₁) :=
    Quotient.lift (fun g : ↥R₁ => (⟨(s * (g : G) * s⁻¹) * (g : G)⁻¹, hFwd g⟩ :
        ↥(fc.sInvertedOvergroup R₁)))
      (by
        intro a b hab
        have h1 : a⁻¹ * b ∈ C' := (QuotientGroup.leftRel_apply).mp hab
        have h2 : (a : G)⁻¹ * (b : G) ∈ fc.P := by
          have h3 : ((a⁻¹ * b : ↥R₁) : G) ∈ fc.P := Subgroup.mem_subgroupOf.mp h1
          simpa using h3
        exact Subtype.ext (hSound a b h2))
  have hFinj : Function.Injective Fbar := by
    intro qa qb h
    obtain ⟨a, rfl⟩ := Quotient.exists_rep qa
    obtain ⟨b, rfl⟩ := Quotient.exists_rep qb
    have h1 : (s * (a : G) * s⁻¹) * (a : G)⁻¹ = (s * (b : G) * s⁻¹) * (b : G)⁻¹ :=
      congrArg Subtype.val h
    -- reverse the fiber computation: `a⁻¹ b` is `s`-fixed, hence in `P`.
    have h2 : s * ((a : G)⁻¹ * (b : G)) * s⁻¹ = (a : G)⁻¹ * (b : G) := by
      have h3 : s * (b : G) * s⁻¹ = (s * (a : G) * s⁻¹) * ((a : G)⁻¹ * (b : G)) := by
        calc s * (b : G) * s⁻¹
            = ((s * (a : G) * s⁻¹) * (a : G)⁻¹) * (b : G) := by rw [h1]; group
          _ = (s * (a : G) * s⁻¹) * ((a : G)⁻¹ * (b : G)) := by group
      calc s * ((a : G)⁻¹ * (b : G)) * s⁻¹
          = (s * (a : G) * s⁻¹)⁻¹ * (s * (b : G) * s⁻¹) := by group
        _ = (a : G)⁻¹ * (b : G) := by rw [h3]; group
    have h4 : (a : G)⁻¹ * (b : G) ∈ fc.P := by
      have h5 : (a : G)⁻¹ * (b : G) ∈ R₁ := mul_mem (inv_mem a.2) b.2
      exact fc.mem_P_of_mem_of_distinguishedInvolution_conj_eq model ind hB2 hm hGp
        hSigma hR₁le hcard h5 h2
    apply Quotient.sound
    have h6 : a⁻¹ * b ∈ C' := by
      rw [Subgroup.mem_subgroupOf]
      simpa using h4
    exact QuotientGroup.leftRel_apply.mpr h6
  -- cardinalities.
  have hC'card : Nat.card ↥C' = fc.p := by
    rw [hC'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv, fc.card_P]
  have hQcard : Nat.card (↥R₁ ⧸ C') = fc.p ^ 2 := by
    have h1 := C'.card_mul_index
    rw [hC'card, hcard] at h1
    apply Nat.eq_of_mul_eq_mul_left fc.p_prime.pos
    calc fc.p * Nat.card (↥R₁ ⧸ C') = fc.p ^ 3 := h1
      _ = fc.p * fc.p ^ 2 := by ring
  have hlower : fc.p ^ 2 ≤ Nat.card ↥(fc.sInvertedOvergroup R₁) := by
    rw [← hQcard]
    exact Nat.card_le_card_of_injective Fbar hFinj
  -- upper bound: `|T₁| ∣ p³` and `T₁ ≠ R₁`.
  have hT₁le : fc.sInvertedOvergroup R₁ ≤ R₁ := by
    intro x hx
    exact ((hmemiff x).mp hx).1
  have hdvd : Nat.card ↥(fc.sInvertedOvergroup R₁) ∣ fc.p ^ 3 := by
    have h1 := Subgroup.card_dvd_of_le hT₁le
    rwa [hcard] at h1
  obtain ⟨i, hi3, hicard⟩ := (Nat.dvd_prime_pow fc.p_prime).mp hdvd
  have hine : fc.sInvertedOvergroup R₁ ≠ R₁ := by
    intro h0
    have h1 : fc.P ≤ fc.sInvertedOvergroup R₁ := by
      rw [h0]
      exact hPle
    have h2 : fc.P = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h3 : x ∈ fc.sInvertedOvergroup R₁ ⊓ fc.P := ⟨h1 hx, hx⟩
      rwa [hinfP] at h3
    have h4 := fc.card_P
    rw [h2, Subgroup.card_bot] at h4
    exact fc.p_prime.one_lt.ne h4
  have hi2 : i = 2 := by
    rcases Nat.lt_or_ge i 2 with h | h
    · exfalso
      have h1 : Nat.card ↥(fc.sInvertedOvergroup R₁) < fc.p ^ 2 := by
        rw [hicard]
        exact Nat.pow_lt_pow_right fc.p_prime.one_lt h
      omega
    · rcases Nat.lt_or_ge i 3 with h' | h'
      · omega
      · exfalso
        have h1 : i = 3 := by omega
        have h2 : Nat.card ↥(fc.sInvertedOvergroup R₁) = Nat.card ↥R₁ := by
          rw [hicard, h1, hcard]
        exact hine (Subgroup.eq_of_le_of_card_ge hT₁le (le_of_eq h2.symm))
  exact ⟨by rw [hicard, hi2], hTsub, hinfP⟩

include model in
/-- **Nonidentity elements of `T₁` are strongly real** ((12), p. 112): `x = s·(s x)`
with both factors nonidentity involutions. -/
theorem isStronglyReal_of_mem_sInvertedOvergroup
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hRle : fc.invImageF model ≤ R₁)
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3) {x : G}
    (hx : x ∈ fc.sInvertedOvergroup R₁) : IsStronglyReal x := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  rw [fc.mem_sInvertedOvergroup_iff model ind hB2 hm hGp hSigma hRle hR₁le hcard] at hx
  set s : G := fc.toHypothesis.distinguishedInvolution with hsdef
  have hs2 : s * s = 1 := by
    have h := fc.toHypothesis.distinguishedInvolution_sq
    rwa [pow_two] at h
  have hsinv : s⁻¹ = s := by
    rw [← mul_one s⁻¹, ← hs2, ← mul_assoc, inv_mul_cancel, one_mul]
  have hsx2 : (s * x) * (s * x) = 1 := by
    have h1 : (s * x) * (s * x) = (s * x * s⁻¹) * ((s * s) * x) := by
      group
    rw [h1, hx.2, hs2, one_mul, inv_mul_cancel]
  have hxo : Odd (orderOf x) := by
    have h1 : orderOf x ∣ Nat.card ↥R₁ := by
      have h2 : orderOf (⟨x, hx.1⟩ : ↥R₁) ∣ Nat.card ↥R₁ := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk] at h2
    rw [hcard] at h1
    have hodd : Odd (fc.p ^ 3) := Odd.pow fc.p_odd
    exact hodd.of_dvd_nat h1
  have hsx1 : s * x ≠ 1 := by
    intro h
    have hxs : x = s := by
      have h1 : x = s⁻¹ := by
        have h2 := congrArg (fun z => s⁻¹ * z) h
        simpa [mul_assoc] using h2
      rw [h1, hsinv]
    rw [hxs] at hxo
    have h2 : orderOf s = 2 := by
      have h3 : s ^ 2 = 1 := fc.toHypothesis.distinguishedInvolution_sq
      have h4 : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one h3
      rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h)
          fc.toHypothesis.distinguishedInvolution_ne_one
      · exact h
    rw [h2] at hxo
    rcases hxo with ⟨k, hk⟩
    omega
  refine ⟨s, ⟨?_, fc.toHypothesis.distinguishedInvolution_ne_one⟩, s * x,
    ⟨by rw [pow_two]; exact hsx2, hsx1⟩, ?_⟩
  · rw [pow_two]
    exact hs2
  · rw [← mul_assoc, hs2, one_mul]

include model in
/-- **A conjugate of `P` meets `T₁` trivially** ((12) tail, δ4-v input): nonidentity
elements of `g·P·g⁻¹` are not strongly real, but those of `T₁` are. -/
theorem conj_P_inf_sInvertedOvergroup_eq_bot
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hRle : fc.invImageF model ≤ R₁)
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3) (g : G) :
    (MulAut.conj g • fc.P) ⊓ fc.sInvertedOvergroup R₁ = ⊥ := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxP, hxT⟩ := hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hsr : IsStronglyReal x :=
    fc.isStronglyReal_of_mem_sInvertedOvergroup model ind hB2 hm hGp hSigma hRle
      hR₁le hcard hxT
  obtain ⟨y, hyP, hyx⟩ := hxP
  have hy1 : y ≠ 1 := by
    intro h
    apply hx1
    rw [← hyx, h]
    simp
  obtain ⟨u, hu, v, hv, huv⟩ := hsr
  have hysr : IsStronglyReal y := by
    refine ⟨g⁻¹ * u * g, ⟨?_, ?_⟩, g⁻¹ * v * g, ⟨?_, ?_⟩, ?_⟩
    · rw [pow_two]
      have h1 := hu.1
      rw [pow_two] at h1
      calc (g⁻¹ * u * g) * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
        _ = 1 := by rw [h1]; group
    · intro h
      apply hu.2
      have h2 := congrArg (fun z => g * z * g⁻¹) h
      simpa [mul_assoc] using h2
    · rw [pow_two]
      have h1 := hv.1
      rw [pow_two] at h1
      calc (g⁻¹ * v * g) * (g⁻¹ * v * g) = g⁻¹ * (v * v) * g := by group
        _ = 1 := by rw [h1]; group
    · intro h
      apply hv.2
      have h2 := congrArg (fun z => g * z * g⁻¹) h
      simpa [mul_assoc] using h2
    · have h1 : y = g⁻¹ * x * g := by
        rw [← hyx]
        change y = g⁻¹ * (g * y * g⁻¹) * g
        group
      rw [h1, huv]
      group
  exact fc.not_isStronglyReal_of_mem_P hyP hy1 hysr

include model in
/-- **No conjugate of `R` equals `T₁`** ((12) tail, δ4-v): it would contain a
conjugate of `P`, which meets `T₁` trivially. -/
theorem conj_invImageF_ne_sInvertedOvergroup
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hRle : fc.invImageF model ≤ R₁)
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3) (g : G) :
    MulAut.conj g • fc.invImageF model ≠ fc.sInvertedOvergroup R₁ := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  intro h0
  have h1 : MulAut.conj g • fc.P ≤ fc.sInvertedOvergroup R₁ := by
    rw [← h0]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (fc.P_le_invImageF model)
  have h2 : MulAut.conj g • fc.P
      = (MulAut.conj g • fc.P) ⊓ fc.sInvertedOvergroup R₁ :=
    (inf_of_le_left h1).symm
  have h3 := fc.conj_P_inf_sInvertedOvergroup_eq_bot model ind hB2 hm hGp hSigma hRle
    hR₁le hcard g
  have h4 : Nat.card ↥(MulAut.conj g • fc.P) = fc.p := by
    rw [← fc.card_P]
    exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) fc.P).toEquiv).symm
  rw [h2, h3, Subgroup.card_bot] at h4
  exact fc.p_prime.one_lt.ne h4

include model in
/-- **An element of `N_G(R)/R` commuting with the normal order-`p` subgroup lies in
it** ((12) tail, δ4-iii core): the faithful degree-`p` action on `𝒜` makes the
centralizer of the regular normal subgroup collapse into it. -/
theorem quotient_mem_zpowers_of_mul_comm
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D)
    {σ q : ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
      ⧸ (fc.invImageF model).subgroupOf
        (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))}
    (hσ : orderOf σ = fc.p) (hσn : (Subgroup.zpowers σ).Normal)
    (hq : q * σ = σ * q) :
    q ∈ Subgroup.zpowers σ := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  have : Fact fc.p.Prime := ⟨fc.p_prime⟩
  revert σ q
  set NR : Subgroup G :=
    Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) with hNRdef
  set R' : Subgroup ↥NR := (fc.invImageF model).subgroupOf NR with hR'def
  intro σ q hσ hσn hq
  have horb := fc.orbit_eq_setOf_prime_order model ind hB2 hm hGp hSigma
  let actNR : MulAction ↥NR (Subgroup G) :=
    MulAction.compHom _ ((MulAut.conj : G →* MulAut G).comp NR.subtype)
  set A : Set (Subgroup G) := {P₁ : Subgroup G | P₁ ≤ fc.invImageF model ∧
    Nat.card ↥P₁ = fc.p ∧ ¬ P₁ ≤ fc.sInvertedT model} with hAdef
  have hpres : ∀ (n : ↥NR) (X : Subgroup G), X ∈ A →
      MulAut.conj (n : G) • X ∈ A := by
    intro n X hX
    rw [← horb] at hX ⊢
    obtain ⟨k, hk⟩ := hX
    refine ⟨n * k, ?_⟩
    have hk' : k • fc.P = X := hk
    change (n * k) • fc.P = MulAut.conj (n : G) • X
    rw [mul_smul, hk']
    rfl
  let actA : MulAction ↥NR ↥A :=
    { smul := fun n X => ⟨MulAut.conj (n : G) • (X : Subgroup G), hpres n X X.2⟩
      one_smul := fun X => Subtype.ext (by
        change MulAut.conj ((1 : ↥NR) : G) • (X : Subgroup G) = X
        rw [OneMemClass.coe_one, map_one, one_smul])
      mul_smul := fun n k X => Subtype.ext (by
        change MulAut.conj ((n * k : ↥NR) : G) • (X : Subgroup G)
          = MulAut.conj (n : G) • MulAut.conj (k : G) • (X : Subgroup G)
        rw [Subgroup.coe_mul, map_mul, mul_smul]) }
  have hsmulA : ∀ (n : ↥NR) (X : ↥A),
      ((n • X : ↥A) : Subgroup G) = MulAut.conj (n : G) • (X : Subgroup G) :=
    fun n X => rfl
  set φ : ↥NR →* Equiv.Perm ↥A := MulAction.toPermHom ↥NR ↥A with hφdef
  have hker : R' ≤ φ.ker := by
    intro x hx
    have hxR : (x : G) ∈ fc.invImageF model := Subgroup.mem_subgroupOf.mp hx
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro X
    have h2 := (fc.mem_invImageF_iff_forall_conj_smul_eq model ind hB2 hm).mp hxR
      X.1 X.2.1 X.2.2.1 X.2.2.2
    have h3 : x • X = X := Subtype.ext (by rw [hsmulA]; exact h2)
    have h4 : (φ x) X = X := h3
    simpa using h4
  set ψ : (↥NR ⧸ R') →* Equiv.Perm ↥A := QuotientGroup.lift R' φ hker with hψdef
  let actQ : MulAction (↥NR ⧸ R') ↥A := MulAction.compHom _ ψ
  have hsmulQ : ∀ (n : ↥NR) (X : ↥A),
      (QuotientGroup.mk' R' n) • X = n • X := fun n X => rfl
  have hfaith : FaithfulSMul (↥NR ⧸ R') ↥A := by
    constructor
    intro m₁ m₂ h
    have h1 : ∀ X : ↥A, (m₂⁻¹ * m₁) • X = X := by
      intro X
      rw [mul_smul, h X, inv_smul_smul]
    obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective R' (m₂⁻¹ * m₁)
    have h2 : (n : G) ∈ fc.invImageF model := by
      rw [fc.mem_invImageF_iff_forall_conj_smul_eq model ind hB2 hm]
      intro P₁ hP₁le hP₁card hP₁T
      have h3 := h1 ⟨P₁, hP₁le, hP₁card, hP₁T⟩
      rw [← hn, hsmulQ] at h3
      exact congrArg Subtype.val h3
    have h4 : m₂⁻¹ * m₁ = 1 := by
      rw [← hn, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h2
    exact (inv_mul_eq_one.mp h4).symm
  have htrans : MulAction.IsPretransitive (↥NR ⧸ R') ↥A := by
    constructor
    intro X Y
    have hX : (X : Subgroup G) ∈ MulAction.orbit ↥NR fc.P := by
      rw [horb]; exact X.2
    have hY : (Y : Subgroup G) ∈ MulAction.orbit ↥NR fc.P := by
      rw [horb]; exact Y.2
    obtain ⟨kX, hkX⟩ := hX
    obtain ⟨kY, hkY⟩ := hY
    have hkX' : kX • fc.P = (X : Subgroup G) := hkX
    have hkY' : kY • fc.P = (Y : Subgroup G) := hkY
    refine ⟨QuotientGroup.mk' R' (kY * kX⁻¹), ?_⟩
    rw [hsmulQ]
    apply Subtype.ext
    rw [hsmulA]
    change ((kY * kX⁻¹) • (X : Subgroup G) : Subgroup G) = Y
    rw [← hkX', mul_smul, inv_smul_smul, hkY']
  have hΩcard : Nat.card ↥A = fc.p := by
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
    have hA := fc.ncard_prime_order_not_le_sInvertedT model ind hB2 hm hx₀P hx₀1
    rw [Nat.card_coe_set_eq, hA, pow_one]
  obtain ⟨a⟩ : Nonempty ↥A :=
    (Nat.card_ne_zero.mp (by rw [hΩcard]; exact fc.p_prime.pos.ne')).1
  have hsurjAll : ∀ y : ↥A,
      Function.Surjective (fun i : ZMod fc.p => σ ^ (i.val) • y) :=
    fun y => OddOrder.GroupTheory.surjective_zpow_smul fc.p_prime hΩcard hσ hσn y
  have hcen : ∀ n ∈ Subgroup.zpowers σ, q * n * q⁻¹ = n := by
    intro n hn
    obtain ⟨w, hw⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hq' : q * σ * q⁻¹ = σ := by
      rw [hq]
      group
    calc q * n * q⁻¹ = q * σ ^ w * q⁻¹ := by rw [hw]
      _ = (q * σ * q⁻¹) ^ w := by simp
      _ = σ ^ w := by rw [hq']
      _ = n := hw
  exact OddOrder.GroupTheory.mem_zpowers_of_centralizes hsurjAll a hcen

include model in
/-- **An element of `N_G(R)` acting trivially on `R₁/T` lies in `R₁`** ((12) tail,
δ4-iii): its class in `N_G(R)/R` commutes with the class of any `x₁ ∈ R₁ ∖ R`
(commutators land in `T ≤ R`), hence lies in `R₁/R` by
`quotient_mem_zpowers_of_mul_comm`. -/
theorem mem_of_forall_conj_mul_inv_mem_sInvertedT
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hRle : fc.invImageF model ≤ R₁)
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3) {k : G}
    (hk : k ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcen : ∀ x ∈ R₁, k * x * k⁻¹ * x⁻¹ ∈ fc.sInvertedT model) :
    k ∈ R₁ := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  have : Fact fc.p.Prime := ⟨fc.p_prime⟩
  obtain ⟨hTle, -, -, -⟩ := fc.sInvertedT_spec model ind hB2 hm
  have hcardQ := fc.card_quotient_invImageF_eq model ind hB2 hm hGp hSigma
  -- an element of `R₁` outside `R`.
  have hnle : ¬ R₁ ≤ fc.invImageF model := by
    intro h
    have h2 := Subgroup.card_le_of_le h
    rw [hcard, fc.card_invImageF model ind, hm, pow_one, fc.card_P] at h2
    have h3 := fc.p_prime.two_le
    have h4 : fc.p ^ 3 = (fc.p * fc.p) * fc.p := by ring
    rw [h4] at h2
    have h5 : (fc.p * fc.p) * fc.p ≤ (fc.p * fc.p) * 1 := by rwa [mul_one]
    have h6 : fc.p ≤ 1 :=
      Nat.le_of_mul_le_mul_left h5 (Nat.mul_pos fc.p_prime.pos fc.p_prime.pos)
    omega
  obtain ⟨x₁, hx₁R₁, hx₁nR⟩ := SetLike.not_le_iff_exists.mp hnle
  -- its class has order `p` and generates the normal Sylow of `N/R`.
  have hx₁NR : x₁ ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) :=
    hR₁le hx₁R₁
  set R' : Subgroup
      ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)) :=
    (fc.invImageF model).subgroupOf
      (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)) with hR'def
  have hξ1 : QuotientGroup.mk' R' ⟨x₁, hx₁NR⟩ ≠ 1 := by
    intro h0
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h0
    exact hx₁nR (Subgroup.mem_subgroupOf.mp h0)
  have hordx : orderOf x₁ ∣ fc.p ^ 3 := by
    have h1 : orderOf (R₁.subtype ⟨x₁, hx₁R₁⟩) = orderOf (⟨x₁, hx₁R₁⟩ : ↥R₁) :=
      orderOf_injective R₁.subtype R₁.subtype_injective _
    have h2 : orderOf (⟨x₁, hx₁R₁⟩ : ↥R₁) ∣ Nat.card ↥R₁ := orderOf_dvd_natCard _
    rw [hcard] at h2
    exact h1 ▸ h2
  have hordxNR : orderOf
      ((Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)).subtype
        ⟨x₁, hx₁NR⟩)
      = orderOf (⟨x₁, hx₁NR⟩ :
        ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))) :=
    orderOf_injective _ (Subgroup.subtype_injective _) _
  have hordξ3 : orderOf (QuotientGroup.mk' R' ⟨x₁, hx₁NR⟩) ∣ fc.p ^ 3 := by
    refine (orderOf_map_dvd (QuotientGroup.mk' R') _).trans ?_
    have h9 : orderOf (⟨x₁, hx₁NR⟩ :
        ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))
        = orderOf x₁ := by
      rw [← hordxNR, Subgroup.subtype_apply]
    rw [h9]
    exact hordx
  have hordξQ : orderOf (QuotientGroup.mk' R' ⟨x₁, hx₁NR⟩)
      ∣ fc.p * (fc.p - 1) := by
    have h1 : orderOf (QuotientGroup.mk' R' ⟨x₁, hx₁NR⟩)
        ∣ Nat.card (_ ⧸ R') := orderOf_dvd_natCard _
    rwa [hcardQ] at h1
  have hordξ : orderOf (QuotientGroup.mk' R' ⟨x₁, hx₁NR⟩) = fc.p := by
    have hcopP : Nat.Coprime fc.p (fc.p - 1) :=
      (Nat.Prime.coprime_iff_not_dvd fc.p_prime).mpr (fun h => by
        have h1 := Nat.le_of_dvd (by have := fc.p_prime.two_le; omega) h
        have := fc.p_prime.two_le
        omega)
    have h5 : orderOf (QuotientGroup.mk' R' ⟨x₁, hx₁NR⟩) ∣ fc.p :=
      (Nat.Coprime.coprime_dvd_left hordξ3 (hcopP.pow_left 3)).dvd_of_dvd_mul_right
        hordξQ
    rcases (fc.p_prime.eq_one_or_self_of_dvd _ h5).symm with heq | heq
    · exact heq
    · exact absurd (orderOf_eq_one_iff.mp heq) hξ1
  have hσn := OddOrder.GroupTheory.zpowers_normal_of_orderOf_eq fc.p_prime hcardQ hordξ
  -- the class of `k` commutes with the class of `x₁`.
  have hcomm : QuotientGroup.mk' R' ⟨k, hk⟩ * QuotientGroup.mk' R' ⟨x₁, hx₁NR⟩
      = QuotientGroup.mk' R' ⟨x₁, hx₁NR⟩ * QuotientGroup.mk' R' ⟨k, hk⟩ := by
    have h1 : k * x₁ * k⁻¹ * x₁⁻¹ ∈ fc.invImageF model := hTle (hcen x₁ hx₁R₁)
    have h2 : (⟨k, hk⟩ * ⟨x₁, hx₁NR⟩ * (⟨k, hk⟩ :
        ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))⁻¹
        * (⟨x₁, hx₁NR⟩ :
          ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))⁻¹)
        ∈ R' := by
      rw [Subgroup.mem_subgroupOf]
      exact h1
    have h3 : QuotientGroup.mk' R' (⟨k, hk⟩ * ⟨x₁, hx₁NR⟩ * (⟨k, hk⟩ :
        ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))⁻¹
        * (⟨x₁, hx₁NR⟩ :
          ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))⁻¹)
        = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    have h4 := congrArg (fun z => z * (QuotientGroup.mk' R' ⟨x₁, hx₁NR⟩)
      * (QuotientGroup.mk' R' ⟨k, hk⟩)) h3
    simpa [mul_assoc] using h4
  -- conclude via the centralizer collapse.
  have hkmem := fc.quotient_mem_zpowers_of_mul_comm model ind hB2 hm hGp hSigma
    hordξ hσn hcomm
  obtain ⟨w, hw⟩ := Subgroup.mem_zpowers_iff.mp hkmem
  have h5 : QuotientGroup.mk' R' ((⟨x₁, hx₁NR⟩ :
      ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))) ^ w)
      = QuotientGroup.mk' R' ⟨k, hk⟩ := by
    rw [map_zpow]
    exact hw
  have h6 : (⟨x₁, hx₁NR⟩ :
      ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))) ^ w
      * (⟨k, hk⟩ :
        ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))⁻¹
      ∈ R' := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, h5]
    group
  rw [Subgroup.mem_subgroupOf] at h6
  have h7 : x₁ ^ w * k⁻¹ ∈ fc.invImageF model := by
    simpa using h6
  have h9 : k = (x₁ ^ w * k⁻¹)⁻¹ * x₁ ^ w := by group
  rw [h9]
  exact mul_mem (inv_mem (hRle h7)) (Subgroup.zpow_mem R₁ hx₁R₁ w)

include model in
/-- **`R ⊓ T₁ = T`** ((12) tail, coordinate block): an `s`-inverted element of
`R = T·P` has trivial `P`-component. -/
theorem invImageF_inf_sInvertedOvergroup
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hRle : fc.invImageF model ≤ R₁)
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3) :
    fc.invImageF model ⊓ fc.sInvertedOvergroup R₁ = fc.sInvertedT model := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  set s : G := fc.toHypothesis.distinguishedInvolution with hsdef
  obtain ⟨hTle, hTinv, -, -⟩ := fc.sInvertedT_spec model ind hB2 hm
  have hab := fc.invImageF_mul_comm model ind hB2 hm
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxR, hxT₁⟩ := hx
    rw [fc.mem_sInvertedOvergroup_iff model ind hB2 hm hGp hSigma hRle hR₁le hcard]
      at hxT₁
    have hxTP : x ∈ (fc.sInvertedT model : Set G) * (fc.P : Set G) := by
      rw [← fc.coe_invImageF_eq_sInvertedT_mul_P model ind hB2 hm]
      exact hxR
    obtain ⟨t, ht, y, hy, rfl⟩ := hxTP
    have hsy : s * y * s⁻¹ = y := by
      have h1 := Subgroup.mem_centralizer_iff.mp
        (fc.toHypothesis.distinguishedInvolution_mem_centralizer_of_le_V fc.P_le_V) y hy
      rw [← hsdef] at h1
      rw [← h1]
      group
    have h1 : s * (t * y) * s⁻¹ = t⁻¹ * y := by
      calc s * (t * y) * s⁻¹ = (s * t * s⁻¹) * (s * y * s⁻¹) := by group
        _ = t⁻¹ * y := by rw [hTinv t ht, hsy]
    have h2 : t⁻¹ * y = t⁻¹ * y⁻¹ := by
      rw [← h1, hxT₁.2, mul_inv_rev]
      have h3 : y * t = t * y := hab y (fc.P_le_invImageF model hy) t
        ((fc.sInvertedT_spec model ind hB2 hm).1 ht)
      calc y⁻¹ * t⁻¹ = (t * y)⁻¹ := by rw [mul_inv_rev]
        _ = (y * t)⁻¹ := by rw [h3]
        _ = t⁻¹ * y⁻¹ := by rw [mul_inv_rev]
    have h4 : y = y⁻¹ := mul_left_cancel h2
    have h5 : y = 1 := by
      have h6 : y ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 1 [h4]
        group
      have h7 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one h6
      have h8 : y ^ fc.p = 1 := fc.pow_p_eq_one_of_mem_invImageF model ind hB2 hm
        (fc.P_le_invImageF model hy)
      have h9 : orderOf y ∣ fc.p := orderOf_dvd_of_pow_eq_one h8
      obtain ⟨j, hj⟩ := fc.p_odd
      have h10 := Nat.dvd_gcd h7 h9
      have h11 : Nat.gcd 2 fc.p = 1 :=
        (Nat.coprime_primes Nat.prime_two fc.p_prime).mpr (by omega)
      rw [h11, Nat.dvd_one] at h10
      exact orderOf_eq_one_iff.mp h10
    rw [h5]
    simpa using ht
  · intro t ht
    rw [Subgroup.mem_inf]
    refine ⟨hTle ht, ?_⟩
    rw [fc.mem_sInvertedOvergroup_iff model ind hB2 hm hGp hSigma hRle hR₁le hcard]
    exact ⟨hRle (hTle ht), hTinv t ht⟩

include model in
/-- A generator class for `R₁/R` inside `N_G(R)/R`: any `x₁ ∈ R₁ ∖ R` has class of
order `p` generating the unique (normal) Sylow `p`-subgroup. -/
private theorem exists_quotient_generator
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3) :
    ∃ x₁ : G, ∃ hx₁NR : x₁ ∈ Subgroup.normalizer
        ((fc.invImageF model : Subgroup G) : Set G), x₁ ∈ R₁ ∧
      orderOf (QuotientGroup.mk' ((fc.invImageF model).subgroupOf
        (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))
        ⟨x₁, hx₁NR⟩) = fc.p ∧
      (Subgroup.zpowers (QuotientGroup.mk' ((fc.invImageF model).subgroupOf
        (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))
        ⟨x₁, hx₁NR⟩)).Normal := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  have : Fact fc.p.Prime := ⟨fc.p_prime⟩
  have hcardQ := fc.card_quotient_invImageF_eq model ind hB2 hm hGp hSigma
  have hnle : ¬ R₁ ≤ fc.invImageF model := by
    intro h
    have h2 := Subgroup.card_le_of_le h
    rw [hcard, fc.card_invImageF model ind, hm, pow_one, fc.card_P] at h2
    have h3 := fc.p_prime.two_le
    have h4 : fc.p ^ 3 = (fc.p * fc.p) * fc.p := by ring
    rw [h4] at h2
    have h5 : (fc.p * fc.p) * fc.p ≤ (fc.p * fc.p) * 1 := by rwa [mul_one]
    have h6 : fc.p ≤ 1 :=
      Nat.le_of_mul_le_mul_left h5 (Nat.mul_pos fc.p_prime.pos fc.p_prime.pos)
    omega
  obtain ⟨x₁, hx₁R₁, hx₁nR⟩ := SetLike.not_le_iff_exists.mp hnle
  have hx₁NR : x₁ ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) :=
    hR₁le hx₁R₁
  have hξ1 : QuotientGroup.mk' ((fc.invImageF model).subgroupOf
      (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))
      ⟨x₁, hx₁NR⟩ ≠ 1 := by
    intro h0
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h0
    exact hx₁nR (Subgroup.mem_subgroupOf.mp h0)
  have hordx : orderOf x₁ ∣ fc.p ^ 3 := by
    have h1 : orderOf (R₁.subtype ⟨x₁, hx₁R₁⟩) = orderOf (⟨x₁, hx₁R₁⟩ : ↥R₁) :=
      orderOf_injective R₁.subtype R₁.subtype_injective _
    have h2 : orderOf (⟨x₁, hx₁R₁⟩ : ↥R₁) ∣ Nat.card ↥R₁ := orderOf_dvd_natCard _
    rw [hcard] at h2
    exact h1 ▸ h2
  have hordxNR : orderOf
      ((Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)).subtype
        ⟨x₁, hx₁NR⟩)
      = orderOf (⟨x₁, hx₁NR⟩ :
        ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))) :=
    orderOf_injective _ (Subgroup.subtype_injective _) _
  have hordξ3 : orderOf (QuotientGroup.mk' ((fc.invImageF model).subgroupOf
      (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))
      ⟨x₁, hx₁NR⟩) ∣ fc.p ^ 3 := by
    refine (orderOf_map_dvd (QuotientGroup.mk' _) _).trans ?_
    have h9 : orderOf (⟨x₁, hx₁NR⟩ :
        ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))
        = orderOf x₁ := by
      rw [← hordxNR, Subgroup.subtype_apply]
    rw [h9]
    exact hordx
  have hordξQ : orderOf (QuotientGroup.mk' ((fc.invImageF model).subgroupOf
      (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))
      ⟨x₁, hx₁NR⟩) ∣ fc.p * (fc.p - 1) := by
    have h1 := orderOf_dvd_natCard (QuotientGroup.mk' ((fc.invImageF model).subgroupOf
      (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))
      ⟨x₁, hx₁NR⟩)
    rwa [hcardQ] at h1
  have hcopP : Nat.Coprime fc.p (fc.p - 1) :=
    (Nat.Prime.coprime_iff_not_dvd fc.p_prime).mpr (fun h => by
      have h1 := Nat.le_of_dvd (by have := fc.p_prime.two_le; omega) h
      have := fc.p_prime.two_le
      omega)
  have h5 : orderOf (QuotientGroup.mk' ((fc.invImageF model).subgroupOf
      (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))
      ⟨x₁, hx₁NR⟩) ∣ fc.p :=
    (Nat.Coprime.coprime_dvd_left hordξ3 (hcopP.pow_left 3)).dvd_of_dvd_mul_right
      hordξQ
  have hord : orderOf (QuotientGroup.mk' ((fc.invImageF model).subgroupOf
      (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))
      ⟨x₁, hx₁NR⟩) = fc.p := by
    rcases (fc.p_prime.eq_one_or_self_of_dvd _ h5).symm with heq | heq
    · exact heq
    · exact absurd (orderOf_eq_one_iff.mp heq) hξ1
  exact ⟨x₁, hx₁NR, hx₁R₁, hord,
    OddOrder.GroupTheory.zpowers_normal_of_orderOf_eq fc.p_prime hcardQ hord⟩

include model in
/-- **`[N_G(R), N_G(R)] ≤ R₁`** ((12) tail, δ4-B core): commutator classes centralize
the normal Sylow `p`-subgroup of `N_G(R)/R` (`commutatorElement_mul_comm_of_zpowers_normal`),
hence lie in it, hence pull back into `R₁`. -/
theorem commutator_mem_of_mem_normalizer
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hRle : fc.invImageF model ≤ R₁)
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3) {k l : G}
    (hk : k ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hl : l ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)) :
    ⁅k, l⁆ ∈ R₁ := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  have : Fact fc.p.Prime := ⟨fc.p_prime⟩
  obtain ⟨x₁, hx₁NR, hx₁R₁, hord, hσn⟩ :=
    fc.exists_quotient_generator model ind hB2 hm hGp hSigma hR₁le hcard
  set R' : Subgroup
      ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)) :=
    (fc.invImageF model).subgroupOf
      (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)) with hR'def
  -- the commutator class commutes with the generator class.
  have hcomm := OddOrder.GroupTheory.commutatorElement_mul_comm_of_zpowers_normal
    (p := fc.p) hord hσn (QuotientGroup.mk' R' ⟨k, hk⟩) (QuotientGroup.mk' R' ⟨l, hl⟩)
  have hcommξ : ⁅QuotientGroup.mk' R' ⟨k, hk⟩, QuotientGroup.mk' R' ⟨l, hl⟩⁆
      = QuotientGroup.mk' R' ⁅(⟨k, hk⟩ :
        ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))),
        ⟨l, hl⟩⁆ :=
    (map_commutatorElement _ _ _).symm
  rw [hcommξ] at hcomm
  have hmem := fc.quotient_mem_zpowers_of_mul_comm model ind hB2 hm hGp hSigma
    hord hσn hcomm
  -- pull back.
  obtain ⟨w, hw⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h5 : QuotientGroup.mk' R' ((⟨x₁, hx₁NR⟩ :
      ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))) ^ w)
      = QuotientGroup.mk' R' ⁅(⟨k, hk⟩ :
        ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))), ⟨l, hl⟩⁆ := by
    rw [map_zpow]
    exact hw
  have h6 : (⟨x₁, hx₁NR⟩ :
      ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))) ^ w
      * (⁅(⟨k, hk⟩ :
        ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))), ⟨l, hl⟩⁆)⁻¹
      ∈ R' := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, h5]
    group
  rw [Subgroup.mem_subgroupOf] at h6
  have h7 : x₁ ^ w * ⁅k, l⁆⁻¹ ∈ fc.invImageF model := by
    simpa [commutatorElement_def] using h6
  have h9 : ⁅k, l⁆ = (x₁ ^ w * ⁅k, l⁆⁻¹)⁻¹ * x₁ ^ w := by group
  rw [h9]
  exact mul_mem (inv_mem (hRle h7)) (Subgroup.zpow_mem R₁ hx₁R₁ w)

include model in
/-- **`R₁ ⊓ C_G(P) = R`** ((12) tail, δ4-A2): a centralizing element of `R₁` outside
`R` would have class of order `p` in `N_G(R)/R`, yet `x^{p-1} ∈ R` since
`|C_G(P)/R| = p - 1`. -/
theorem inf_centralizer_eq_invImageF
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hRle : fc.invImageF model ≤ R₁)
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3) :
    R₁ ⊓ Subgroup.centralizer (fc.P : Set G) = fc.invImageF model := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  have : Fact fc.p.Prime := ⟨fc.p_prime⟩
  set C : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hCdef
  have hCle : C ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) := by
    have h1 := (fc.normalizer_P_lt_normalizer_invImageF model ind hm hGp hSigma).le
    rw [fc.normalizer_P_eq_centralizer] at h1
    exact h1
  have hRleC : fc.invImageF model ≤ C := fc.invImageF_le_centralizer model
  -- `R ⊴ C` and the quotient has order `p - 1`.
  have hnorm : ((fc.invImageF model).subgroupOf C).Normal := by
    constructor
    intro t ht n
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    have h1 := (Subgroup.mem_set_normalizer_iff.mp (hCle n.2) (t : G)).mp ht
    exact h1
  have hqcard : Nat.card (↥C ⧸ (fc.invImageF model).subgroupOf C) = fc.p - 1 := by
    have h1 := ((fc.invImageF model).subgroupOf C).card_mul_index
    have h2 : Nat.card ↥((fc.invImageF model).subgroupOf C)
        = Nat.card ↥(fc.invImageF model) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRleC).toEquiv
    have hCcard : Nat.card ↥C = (fc.p * fc.p) * (fc.p - 1) := by
      rw [hCdef, fc.card_centralizer_P model ind, fc.card_P, hm, pow_one,
        fc.card_rankOneQ_eq_pred_card_F model hm, hm, pow_one]
      have hD1 : Nat.card ↥(fc.rankOneQuotient).D = 1 := by
        have hall := fc.sigmaComponent_eq_one_of_card_F_eq_p model
          (by rw [hm, pow_one])
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun a b => by rw [hall a, hall b]⟩, ⟨1⟩⟩
      rw [hD1, mul_one]
      ring
    rw [h2, fc.card_invImageF model ind, hm, pow_one, fc.card_P, hCcard] at h1
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos fc.p_prime.pos fc.p_prime.pos)
    calc (fc.p * fc.p) * Nat.card (↥C ⧸ (fc.invImageF model).subgroupOf C)
        = (fc.p * fc.p) * (fc.p - 1) := h1
      _ = (fc.p * fc.p) * (fc.p - 1) := rfl
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    by_contra hxnR
    -- `x^{p-1} ∈ R`.
    have hxpow : x ^ (fc.p - 1) ∈ fc.invImageF model := by
      have h1 : orderOf (QuotientGroup.mk' ((fc.invImageF model).subgroupOf C)
          ⟨x, hx2⟩) ∣ fc.p - 1 := by
        have h2 := orderOf_dvd_natCard (QuotientGroup.mk'
          ((fc.invImageF model).subgroupOf C) ⟨x, hx2⟩)
        rwa [hqcard] at h2
      have h3 : (QuotientGroup.mk' ((fc.invImageF model).subgroupOf C)
          ⟨x, hx2⟩) ^ (fc.p - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
      exact Subgroup.mem_subgroupOf.mp h3
    -- but the class of `x` in `N_G(R)/R` has order `p`.
    have hxNR : x ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) :=
      hR₁le hx1
    set R' : Subgroup
        ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)) :=
      (fc.invImageF model).subgroupOf
        (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)) with hR'def
    have hcardQ := fc.card_quotient_invImageF_eq model ind hB2 hm hGp hSigma
    have hξ1 : QuotientGroup.mk' R' ⟨x, hxNR⟩ ≠ 1 := by
      intro h0
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h0
      exact hxnR (Subgroup.mem_subgroupOf.mp h0)
    have hordx : orderOf x ∣ fc.p ^ 3 := by
      have h1 : orderOf (R₁.subtype ⟨x, hx1⟩) = orderOf (⟨x, hx1⟩ : ↥R₁) :=
        orderOf_injective R₁.subtype R₁.subtype_injective _
      have h2 : orderOf (⟨x, hx1⟩ : ↥R₁) ∣ Nat.card ↥R₁ := orderOf_dvd_natCard _
      rw [hcard] at h2
      exact h1 ▸ h2
    have hordxNR : orderOf
        ((Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)).subtype
          ⟨x, hxNR⟩)
        = orderOf (⟨x, hxNR⟩ :
          ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))) :=
      orderOf_injective _ (Subgroup.subtype_injective _) _
    have hordξ3 : orderOf (QuotientGroup.mk' R' ⟨x, hxNR⟩) ∣ fc.p ^ 3 := by
      refine (orderOf_map_dvd (QuotientGroup.mk' R') _).trans ?_
      have h9 : orderOf (⟨x, hxNR⟩ :
          ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))
          = orderOf x := by
        rw [← hordxNR, Subgroup.subtype_apply]
      rw [h9]
      exact hordx
    have hordξQ : orderOf (QuotientGroup.mk' R' ⟨x, hxNR⟩) ∣ fc.p * (fc.p - 1) := by
      have h1 := orderOf_dvd_natCard (QuotientGroup.mk' R' ⟨x, hxNR⟩)
      rwa [hcardQ] at h1
    have hcopP : Nat.Coprime fc.p (fc.p - 1) :=
      (Nat.Prime.coprime_iff_not_dvd fc.p_prime).mpr (fun h => by
        have h1 := Nat.le_of_dvd (by have := fc.p_prime.two_le; omega) h
        have := fc.p_prime.two_le
        omega)
    have h5 : orderOf (QuotientGroup.mk' R' ⟨x, hxNR⟩) ∣ fc.p :=
      (Nat.Coprime.coprime_dvd_left hordξ3 (hcopP.pow_left 3)).dvd_of_dvd_mul_right
        hordξQ
    have hordξ : orderOf (QuotientGroup.mk' R' ⟨x, hxNR⟩) = fc.p := by
      rcases (fc.p_prime.eq_one_or_self_of_dvd _ h5).symm with heq | heq
      · exact heq
      · exact absurd (orderOf_eq_one_iff.mp heq) hξ1
    -- contradiction: `[x]^{p-1} = 1` forces `p ∣ p - 1`.
    have h6 : (QuotientGroup.mk' R' ⟨x, hxNR⟩) ^ (fc.p - 1) = 1 := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rw [Subgroup.mem_subgroupOf]
      simpa using hxpow
    have h8 : fc.p ∣ fc.p - 1 := by
      have h8' := orderOf_dvd_of_pow_eq_one h6
      rwa [hordξ] at h8'
    have h10 := Nat.le_of_dvd (by have := fc.p_prime.two_le; omega) h8
    have := fc.p_prime.two_le
    omega
  · exact le_inf hRle hRleC

include model in
/-- **`N_G(R) = R₁ · C_G(P)`** ((12) tail, δ4-A2): the quotient `C_G(P)/R` of order
`p - 1` embeds into `(R₁ ⊔ C_G(P))/R₁`, so the join has full order `p³(p-1)`, and the
join is a product since `C_G(P)` normalizes `R₁`. -/
theorem exists_mul_eq_of_mem_normalizer
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hRle : fc.invImageF model ≤ R₁)
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3)
    (hR₁n : ∀ n ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G),
      ∀ x ∈ R₁, n * x * n⁻¹ ∈ R₁) {k : G}
    (hk : k ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)) :
    ∃ r ∈ R₁, ∃ c ∈ Subgroup.centralizer (fc.P : Set G), k = r * c := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  have : Fact fc.p.Prime := ⟨fc.p_prime⟩
  set C : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hCdef
  have hCle : C ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) := by
    have h1 := (fc.normalizer_P_lt_normalizer_invImageF model ind hm hGp hSigma).le
    rw [fc.normalizer_P_eq_centralizer] at h1
    exact h1
  have hRleC : fc.invImageF model ≤ C := fc.invImageF_le_centralizer model
  have hinf := fc.inf_centralizer_eq_invImageF model ind hB2 hm hGp hSigma hRle
    hR₁le hcard
  set S : Subgroup G := R₁ ⊔ C with hSdef
  have hSle : S ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) :=
    sup_le hR₁le hCle
  have hR₁S : R₁ ≤ S := le_sup_left
  have hCS : C ≤ S := le_sup_right
  -- the `C/R`-quotient embeds into `S/R₁`.
  have hnormR₁S : (R₁.subgroupOf S).Normal := by
    constructor
    intro t ht n
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    exact hR₁n (↑n) (hSle n.2) _ ht
  have hnormR : ((fc.invImageF model).subgroupOf C).Normal := by
    constructor
    intro t ht n
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    exact (Subgroup.mem_set_normalizer_iff.mp (hCle n.2) (t : G)).mp ht
  have hqcard : Nat.card (↥C ⧸ (fc.invImageF model).subgroupOf C) = fc.p - 1 := by
    have h1 := ((fc.invImageF model).subgroupOf C).card_mul_index
    have h2 : Nat.card ↥((fc.invImageF model).subgroupOf C)
        = Nat.card ↥(fc.invImageF model) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRleC).toEquiv
    have hCcard : Nat.card ↥C = (fc.p * fc.p) * (fc.p - 1) := by
      rw [hCdef, fc.card_centralizer_P model ind, fc.card_P, hm, pow_one,
        fc.card_rankOneQ_eq_pred_card_F model hm, hm, pow_one]
      have hD1 : Nat.card ↥(fc.rankOneQuotient).D = 1 := by
        have hall := fc.sigmaComponent_eq_one_of_card_F_eq_p model
          (by rw [hm, pow_one])
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun a b => by rw [hall a, hall b]⟩, ⟨1⟩⟩
      rw [hD1, mul_one]
      ring
    rw [h2, fc.card_invImageF model ind, hm, pow_one, fc.card_P, hCcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos fc.p_prime.pos fc.p_prime.pos) h1
  -- the embedding.
  let ι : (↥C ⧸ (fc.invImageF model).subgroupOf C) → (↥S ⧸ R₁.subgroupOf S) :=
    Quotient.lift (fun c : ↥C => QuotientGroup.mk' (R₁.subgroupOf S)
        ⟨(c : G), hCS c.2⟩)
      (by
        intro a b hab
        have h1 : (a : G)⁻¹ * (b : G) ∈ fc.invImageF model := by
          have h2 := (QuotientGroup.leftRel_apply).mp hab
          have h3 := Subgroup.mem_subgroupOf.mp h2
          simpa using h3
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        rw [Subgroup.mem_subgroupOf]
        have h4 : ((⟨(a : G), hCS a.2⟩ : ↥S)⁻¹ * ⟨(b : G), hCS b.2⟩ : ↥S)
            = (⟨(a : G)⁻¹ * (b : G), mul_mem (inv_mem (hCS a.2)) (hCS b.2)⟩ : ↥S) :=
          rfl
        rw [h4]
        exact hRle h1)
  have hι : Function.Injective ι := by
    intro qa qb h
    obtain ⟨a, rfl⟩ := Quotient.exists_rep qa
    obtain ⟨b, rfl⟩ := Quotient.exists_rep qb
    have h1 : QuotientGroup.mk' (R₁.subgroupOf S) ⟨(a : G), hCS a.2⟩
        = QuotientGroup.mk' (R₁.subgroupOf S) ⟨(b : G), hCS b.2⟩ := h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : (a : G)⁻¹ * (b : G) ∈ R₁ := by simpa using h1
    have h3 : (a : G)⁻¹ * (b : G) ∈ fc.invImageF model := by
      rw [← hinf]
      exact ⟨h2, mul_mem (C.inv_mem a.2) b.2⟩
    apply Quotient.sound
    refine QuotientGroup.leftRel_apply.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    simpa using h3
  -- cardinalities force `S = N_G(R)`.
  have hidxS : fc.p - 1 ≤ Nat.card (↥S ⧸ R₁.subgroupOf S) := by
    rw [← hqcard]
    exact Nat.card_le_card_of_injective ι hι
  have hScard : Nat.card ↥S = fc.p ^ 3 * Nat.card (↥S ⧸ R₁.subgroupOf S) := by
    have h1 := (R₁.subgroupOf S).card_mul_index
    have h2 : Nat.card ↥(R₁.subgroupOf S) = Nat.card ↥R₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₁S).toEquiv
    rw [h2, hcard] at h1
    exact h1.symm
  have hNRcard : Nat.card
      ↥(Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
      = fc.p ^ 3 * (fc.p - 1) := by
    have h1 := ((fc.invImageF model).subgroupOf
      (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))).card_mul_index
    have h2 : Nat.card ↥((fc.invImageF model).subgroupOf
        (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)))
        = Nat.card ↥(fc.invImageF model) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
    have h3 : ((fc.invImageF model).subgroupOf
        (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))).index
        = fc.p * (fc.p - 1) :=
      fc.card_quotient_invImageF_eq model ind hB2 hm hGp hSigma
    rw [h2, h3, fc.card_invImageF model ind, hm, pow_one, fc.card_P] at h1
    rw [← h1]
    ring
  have hSeq : S = Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) := by
    apply Subgroup.eq_of_le_of_card_ge hSle
    rw [hNRcard, hScard]
    calc fc.p ^ 3 * (fc.p - 1)
        ≤ fc.p ^ 3 * Nat.card (↥S ⧸ R₁.subgroupOf S) := by
          exact Nat.mul_le_mul_left _ hidxS
      _ = fc.p ^ 3 * Nat.card (↥S ⧸ R₁.subgroupOf S) := rfl
  -- the join is a product.
  have hprod : ((S : Subgroup G) : Set G) = (R₁ : Set G) * (C : Set G) := by
    rw [hSdef]
    refine Subgroup.coe_mul_of_right_le_normalizer_left _ _ ?_
    intro c hc
    rw [Subgroup.mem_set_normalizer_iff]
    intro r
    constructor
    · intro hr
      exact hR₁n c (hCle hc) r hr
    · intro hr
      have h1 := hR₁n c⁻¹ (Subgroup.inv_mem _ (hCle hc)) _ hr
      simpa [mul_assoc] using h1
  have hkS : k ∈ ((S : Subgroup G) : Set G) := by
    rw [hSeq]
    exact hk
  rw [hprod] at hkS
  obtain ⟨r, hr, c, hc, rfl⟩ := hkS
  exact ⟨r, hr, c, hc, rfl⟩

include model in
/-- **`T₁ ⊴ N_G(R)`** ((12) tail, δ4-B): the set `X₁` of mod-`T` inverted elements of
`R₁` is a subgroup (commutators land in the central `T`) squeezed to `T₁` by
cardinality, and conjugation twists exact inversion only by central `T`-elements
(`⁅k⁻¹, s⁆ ∈ R₁`). -/
theorem conj_sInvertedOvergroup_eq
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hRle : fc.invImageF model ≤ R₁)
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3)
    (hR₁n : ∀ n ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G),
      ∀ x ∈ R₁, n * x * n⁻¹ ∈ R₁) {k : G}
    (hk : k ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G)) :
    MulAut.conj k • fc.sInvertedOvergroup R₁ = fc.sInvertedOvergroup R₁ := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  have : Fact fc.p.Prime := ⟨fc.p_prime⟩
  set s : G := fc.toHypothesis.distinguishedInvolution with hsdef
  obtain ⟨hTle, hTinv, -, hTinfP⟩ := fc.sInvertedT_spec model ind hB2 hm
  have hTcard : Nat.card ↥(fc.sInvertedT model) = fc.p := by
    rw [fc.card_sInvertedT model ind hB2 hm, hm, pow_one]
  have hcen := fc.sInvertedT_mul_comm_of_mem model ind hB2 hm hGp hSigma hR₁le hcard
  have hcommT := fc.commutator_eq_sInvertedT model ind hB2 hm hGp hSigma hRle
    hR₁le hcard
  obtain ⟨hT₁card, hTsubT₁, hT₁infP⟩ := fc.card_sInvertedOvergroup model ind hB2 hm
    hGp hSigma hRle hR₁le hcard hR₁n
  have hmemiff := fun (x : G) =>
    fc.mem_sInvertedOvergroup_iff model ind hB2 hm hGp hSigma hRle hR₁le hcard (x := x)
  have hab := fc.invImageF_mul_comm model ind hB2 hm
  -- the mod-`T` inverted subgroup `X₁`.
  set S₁ : Set G := {x : G | x ∈ R₁ ∧
    s * x * s⁻¹ * x ∈ fc.sInvertedT model} with hS₁def
  have hsub : ∃ H : Subgroup G, (H : Set G) = S₁ := by
    refine ⟨⟨⟨⟨S₁, ?_⟩, ?_⟩, ?_⟩, rfl⟩
    · -- mul_mem
      rintro a b ⟨haR, hai⟩ ⟨hbR, hbi⟩
      refine ⟨mul_mem haR hbR, ?_⟩
      have hcm : ⁅a⁻¹, b⁻¹⁆ ∈ fc.sInvertedT model := by
        rw [← hcommT]
        exact Subgroup.commutator_mem_commutator (inv_mem haR) (inv_mem hbR)
      have hfinal : s * (a * b) * s⁻¹ * (a * b)
          = (s * a * s⁻¹ * a) * ((s * b * s⁻¹ * b) * ⁅a⁻¹, b⁻¹⁆) := by
        have hswap := hcen _ hbi a⁻¹ (inv_mem haR)
        calc s * (a * b) * s⁻¹ * (a * b)
            = ((s * a * s⁻¹ * a) * (a⁻¹ * (s * b * s⁻¹ * b))) * (b⁻¹ * a * b) := by
              group
          _ = ((s * a * s⁻¹ * a) * ((s * b * s⁻¹ * b) * a⁻¹)) * (b⁻¹ * a * b) := by
              rw [hswap]
          _ = (s * a * s⁻¹ * a) * ((s * b * s⁻¹ * b) * ⁅a⁻¹, b⁻¹⁆) := by
              rw [commutatorElement_def, inv_inv, inv_inv]
              group
      rw [hfinal]
      exact mul_mem hai (mul_mem hbi hcm)
    · -- one_mem
      refine ⟨one_mem _, ?_⟩
      have h1 : s * 1 * s⁻¹ * 1 = 1 := by group
      rw [h1]
      exact one_mem _
    · -- inv_mem
      rintro a ⟨haR, hai⟩
      refine ⟨inv_mem haR, ?_⟩
      have h1 : s * a⁻¹ * s⁻¹ * a⁻¹ = a * (s * a * s⁻¹ * a)⁻¹ * a⁻¹ := by group
      rw [h1]
      have h3 := hcen _ ((fc.sInvertedT model).inv_mem hai) a haR
      rw [h3]
      have h4 : (s * a * s⁻¹ * a)⁻¹ * a * a⁻¹ = (s * a * s⁻¹ * a)⁻¹ := by group
      rw [h4]
      exact (fc.sInvertedT model).inv_mem hai
  obtain ⟨X₁, hX₁⟩ := hsub
  have hX₁mem : ∀ x : G, x ∈ X₁ ↔ (x ∈ R₁ ∧
      s * x * s⁻¹ * x ∈ fc.sInvertedT model) := by
    intro x
    rw [← SetLike.mem_coe, hX₁]
    exact Iff.rfl
  have hT₁X₁ : fc.sInvertedOvergroup R₁ ≤ X₁ := by
    intro x hx
    rw [hmemiff] at hx
    rw [hX₁mem]
    refine ⟨hx.1, ?_⟩
    rw [hx.2, inv_mul_cancel]
    exact one_mem _
  -- `X₁ ⊓ R = T`.
  have hX₁R : X₁ ⊓ fc.invImageF model = fc.sInvertedT model := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [hX₁mem] at hx1
      have hxTP : x ∈ (fc.sInvertedT model : Set G) * (fc.P : Set G) := by
        rw [← fc.coe_invImageF_eq_sInvertedT_mul_P model ind hB2 hm]
        exact hx2
      obtain ⟨t, ht, y, hy, rfl⟩ := hxTP
      have hsy : s * y * s⁻¹ = y := by
        have h1 := Subgroup.mem_centralizer_iff.mp
          (fc.toHypothesis.distinguishedInvolution_mem_centralizer_of_le_V
            fc.P_le_V) y hy
        rw [← hsdef] at h1
        rw [← h1]
        group
      have hty : t * y = y * t := hab t (hTle ht) y (fc.P_le_invImageF model hy)
      have hd : s * (t * y) * s⁻¹ * (t * y) = y * y := by
        calc s * (t * y) * s⁻¹ * (t * y)
            = ((s * t * s⁻¹) * (s * y * s⁻¹)) * (t * y) := by group
          _ = (t⁻¹ * y) * (t * y) := by rw [hTinv t ht, hsy]
          _ = (t⁻¹ * (y * t)) * y := by group
          _ = (t⁻¹ * (t * y)) * y := by rw [hty]
          _ = y * y := by group
      rw [hd] at hx1
      have hyy : y * y ∈ fc.sInvertedT model ⊓ fc.P :=
        ⟨hx1.2, mul_mem hy hy⟩
      rw [hTinfP, Subgroup.mem_bot] at hyy
      have hy1 : y = 1 := by
        have h6 : y ^ 2 = 1 := by rw [pow_two]; exact hyy
        have h7 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one h6
        have h8 : y ^ fc.p = 1 := fc.pow_p_eq_one_of_mem_invImageF model ind hB2 hm
          (fc.P_le_invImageF model hy)
        have h9 : orderOf y ∣ fc.p := orderOf_dvd_of_pow_eq_one h8
        obtain ⟨j, hj⟩ := fc.p_odd
        have h10 := Nat.dvd_gcd h7 h9
        have h11 : Nat.gcd 2 fc.p = 1 :=
          (Nat.coprime_primes Nat.prime_two fc.p_prime).mpr (by omega)
        rw [h11, Nat.dvd_one] at h10
        exact orderOf_eq_one_iff.mp h10
      rw [hy1]
      simpa using ht
    · intro t ht
      rw [Subgroup.mem_inf]
      refine ⟨?_, hTle ht⟩
      rw [hX₁mem]
      refine ⟨hRle (hTle ht), ?_⟩
      rw [hTinv t ht, inv_mul_cancel]
      exact one_mem _
  -- the cardinality squeeze `X₁ = T₁`.
  have hX₁le : X₁ ≤ R₁ := fun x hx => ((hX₁mem x).mp hx).1
  have hX₁eq : X₁ = fc.sInvertedOvergroup R₁ := by
    have hdvd : Nat.card ↥X₁ ∣ fc.p ^ 3 := by
      have h1 := Subgroup.card_dvd_of_le hX₁le
      rwa [hcard] at h1
    obtain ⟨i, hi3, hicard⟩ := (Nat.dvd_prime_pow fc.p_prime).mp hdvd
    have hge : fc.p ^ 2 ≤ Nat.card ↥X₁ := by
      rw [← hT₁card]
      exact Subgroup.card_le_of_le hT₁X₁
    have hne : X₁ ≠ R₁ := by
      intro h0
      have h1 : fc.invImageF model ≤ X₁ := h0 ▸ hRle
      have h2 : X₁ ⊓ fc.invImageF model = fc.invImageF model :=
        inf_eq_right.mpr h1
      rw [hX₁R] at h2
      have h3 : Nat.card ↥(fc.invImageF model) = fc.p := by rw [← h2, hTcard]
      rw [fc.card_invImageF model ind, hm, pow_one, fc.card_P] at h3
      have h4 := fc.p_prime.one_lt
      nlinarith
    have hi2 : i = 2 := by
      rcases Nat.lt_or_ge i 2 with h | h
      · exfalso
        have h1 : Nat.card ↥X₁ < fc.p ^ 2 := by
          rw [hicard]
          exact Nat.pow_lt_pow_right fc.p_prime.one_lt h
        omega
      · rcases Nat.lt_or_ge i 3 with h' | h'
        · omega
        · exfalso
          have h1 : i = 3 := by omega
          have h2 : Nat.card ↥X₁ = Nat.card ↥R₁ := by
            rw [hicard, h1, hcard]
          exact hne (Subgroup.eq_of_le_of_card_ge hX₁le (le_of_eq h2.symm))
    exact (Subgroup.eq_of_le_of_card_ge hT₁X₁
      (by rw [hicard, hi2, hT₁card])).symm
  -- conjugates stay mod-`T` inverted.
  have hsNR : s ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) :=
    fc.distinguishedInvolution_mem_normalizer_invImageF model ind hB2 hm
  have hconjle : MulAut.conj k • fc.sInvertedOvergroup R₁ ≤ X₁ := by
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have h2 : ((MulAut.conj k)⁻¹ • x : G) = k⁻¹ * x * k := by
      have h3 : ((MulAut.conj k)⁻¹ • x : G) = (MulAut.conj k)⁻¹ x := rfl
      rw [h3, ← map_inv, MulAut.conj_apply]
      group
    rw [h2] at hx
    rw [hmemiff] at hx
    have hxR₁ : x ∈ R₁ := by
      have h3 : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
      rw [h3]
      exact hR₁n k hk _ hx.1
    rw [hX₁mem]
    refine ⟨hxR₁, ?_⟩
    have hr₂ : ⁅k⁻¹, s⁆ ∈ R₁ :=
      fc.commutator_mem_of_mem_normalizer model ind hB2 hm hGp hSigma hRle hR₁le
        hcard (Subgroup.inv_mem _ hk) hsNR
    have hc : ⁅⁅k⁻¹, s⁆, (k⁻¹ * x * k)⁻¹⁆ ∈ fc.sInvertedT model := by
      rw [← hcommT]
      exact Subgroup.commutator_mem_commutator hr₂ (inv_mem hx.1)
    have hkey : s * x * s⁻¹ * x = k * ⁅⁅k⁻¹, s⁆, (k⁻¹ * x * k)⁻¹⁆ * k⁻¹ := by
      have hs' : k⁻¹ * s * k = ⁅k⁻¹, s⁆ * s := by
        rw [commutatorElement_def]
        group
      have hinvx₀ : s * (k⁻¹ * x * k) * s⁻¹ = (k⁻¹ * x * k)⁻¹ := hx.2
      calc s * x * s⁻¹ * x
          = k * ((k⁻¹ * s * k) * (k⁻¹ * x * k) * (k⁻¹ * s * k)⁻¹ * (k⁻¹ * x * k))
            * k⁻¹ := by group
        _ = k * ((⁅k⁻¹, s⁆ * s) * (k⁻¹ * x * k) * (⁅k⁻¹, s⁆ * s)⁻¹ * (k⁻¹ * x * k))
            * k⁻¹ := by rw [hs']
        _ = k * (⁅k⁻¹, s⁆ * (s * (k⁻¹ * x * k) * s⁻¹) * ⁅k⁻¹, s⁆⁻¹ * (k⁻¹ * x * k))
            * k⁻¹ := by group
        _ = k * (⁅k⁻¹, s⁆ * (k⁻¹ * x * k)⁻¹ * ⁅k⁻¹, s⁆⁻¹ * (k⁻¹ * x * k)) * k⁻¹ := by
            rw [hinvx₀]
        _ = k * ⁅⁅k⁻¹, s⁆, (k⁻¹ * x * k)⁻¹⁆ * k⁻¹ := by
            rw [commutatorElement_def, commutatorElement_def, inv_inv]
            group
    rw [hkey]
    have h6 := fc.conj_sInvertedT_eq_of_mem_normalizer model ind hB2 hm hGp hSigma hk
    have h7 := Subgroup.smul_mem_pointwise_smul ⁅⁅k⁻¹, s⁆, (k⁻¹ * x * k)⁻¹⁆
      (MulAut.conj k) (fc.sInvertedT model) hc
    rwa [h6] at h7
  -- conclude by cardinality.
  rw [hX₁eq] at hconjle
  apply Subgroup.eq_of_le_of_card_ge hconjle
  have h8 : Nat.card ↥(MulAut.conj k • fc.sInvertedOvergroup R₁)
      = Nat.card ↥(fc.sInvertedOvergroup R₁) :=
    (Nat.card_congr (Subgroup.equivSMul (MulAut.conj k) _).toEquiv).symm
  rw [h8]

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
