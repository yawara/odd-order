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
    letI : MulAction
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

include model in
/-- **`R` is self-centralizing: `C_G(R) = R`** ((12) tail, faithfulness input).  A
centralizing element lies in `C_G(P)` (as `P ≤ R`), its class in the affine quotient
decomposes as `translation · q̄ · d̄`, and centralizing all translations forces
`dAut d̄ x · u_q̄ = x` for every `x : F`; evaluating at `x = 1` kills the `Q̄`-component
(`dAut` is multiplicative, so `dAut d̄ 1 = 1`), and then `dAut` faithfulness kills the
`Σ`-component, leaving a translation class — i.e. membership in `R`.  Conversely `R`
is abelian. -/
theorem centralizer_invImageF_eq
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    Subgroup.centralizer ((fc.invImageF model : Subgroup G) : Set G)
      = fc.invImageF model := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N' : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hN'def
  apply le_antisymm
  · intro c hc
    have hcL : c ∈ L := by
      rw [hLdef, Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_iff.mp hc x (fc.P_le_invImageF model hx)
    -- the class of `c` centralizes every translation.
    have hcen : ∀ x : F,
        QuotientGroup.mk' N' ⟨c, hcL⟩ * model.emb (Multiplicative.ofAdd x)
          * (QuotientGroup.mk' N' ⟨c, hcL⟩)⁻¹ = model.emb (Multiplicative.ofAdd x) := by
      intro x
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N'
        (model.emb (Multiplicative.ofAdd x))
      have hyR : (y : G) ∈ fc.invImageF model :=
        ⟨y, Subgroup.mem_comap.mpr (by rw [hy]; exact ⟨Multiplicative.ofAdd x, rfl⟩), rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hc _ hyR
      have hcyG : c * (y : G) * c⁻¹ = (y : G) := by
        rw [← h1]; group
      have hpush : QuotientGroup.mk' N' ⟨c, hcL⟩ * QuotientGroup.mk' N' y
            * (QuotientGroup.mk' N' ⟨c, hcL⟩)⁻¹
          = QuotientGroup.mk' N' y := by
        rw [← map_inv, ← map_mul, ← map_mul]
        exact congrArg _ (Subtype.ext hcyG)
      rw [← hy]
      exact hpush
    -- decompose the class along `quotient = emb(F) ⋊ H̄`, then split `H̄ = Q̄·D̄`.
    obtain ⟨⟨a, hbar⟩, hprod, -⟩ :=
      model.isComplement.existsUnique (QuotientGroup.mk' N' ⟨c, hcL⟩)
    have hhH : (hbar : ↥L ⧸ N') ∈ ((fc.rankOneQuotient).Q : Set (↥L ⧸ N'))
        * ((fc.rankOneQuotient).D : Set (↥L ⧸ N')) := by
      rw [(fc.rankOneQuotient).Q_mul_D_eq_H]
      exact hbar.2
    obtain ⟨qb, hqb, db, hdb, hqd⟩ := hhH
    obtain ⟨za, hza⟩ := MonoidHom.mem_range.mp a.2
    have hacomm : ∀ w : Multiplicative F,
        (a : ↥L ⧸ N') * model.emb w = model.emb w * (a : ↥L ⧸ N') := by
      intro w
      rw [← hza, ← map_mul, ← map_mul, mul_comm]
    -- the affine part of conjugation by `[c]` is trivial: `dAut d̄ x · u = x`.
    have hkey : ∀ x : F,
        model.dAut ⟨db, hdb⟩ x
            * ((model.qEquiv (⟨qb, hqb⟩ : ↥(fc.rankOneQuotient).Q)⁻¹ : Fˣ) : F) = x := by
      intro x
      have hd' : db * model.emb (Multiplicative.ofAdd x) * db⁻¹
          = model.emb (Multiplicative.ofAdd (model.dAut ⟨db, hdb⟩ x)) :=
        model.dAut_conj ⟨db, hdb⟩ x
      have hq' : qb * model.emb (Multiplicative.ofAdd (model.dAut ⟨db, hdb⟩ x)) * qb⁻¹
          = model.emb (Multiplicative.ofAdd (model.dAut ⟨db, hdb⟩ x
              * ((model.qEquiv (⟨qb, hqb⟩ : ↥(fc.rankOneQuotient).Q)⁻¹ : Fˣ) : F))) :=
        model.qEquiv_conj ⟨qb, hqb⟩ (model.dAut ⟨db, hdb⟩ x)
      have h1 := hcen x
      rw [← hprod, ← hqd] at h1
      have h4 : (a : ↥L ⧸ N')
            * (qb * (db * model.emb (Multiplicative.ofAdd x) * db⁻¹) * qb⁻¹)
            * (a : ↥L ⧸ N')⁻¹
          = model.emb (Multiplicative.ofAdd x) := by
        calc (a : ↥L ⧸ N')
              * (qb * (db * model.emb (Multiplicative.ofAdd x) * db⁻¹) * qb⁻¹)
              * (a : ↥L ⧸ N')⁻¹
            = (a : ↥L ⧸ N') * (qb * db) * model.emb (Multiplicative.ofAdd x)
              * ((a : ↥L ⧸ N') * (qb * db))⁻¹ := by
              rw [mul_inv_rev, mul_inv_rev]; group
          _ = model.emb (Multiplicative.ofAdd x) := h1
      rw [hd', hq', hacomm] at h4
      have h5 : model.emb (Multiplicative.ofAdd (model.dAut ⟨db, hdb⟩ x
            * ((model.qEquiv (⟨qb, hqb⟩ : ↥(fc.rankOneQuotient).Q)⁻¹ : Fˣ) : F)))
          = model.emb (Multiplicative.ofAdd x) := by
        rwa [mul_assoc, mul_inv_cancel, mul_one] at h4
      exact Multiplicative.ofAdd.injective (model.emb_injective h5)
    -- `x = 1` kills the `Q̄`-component …
    have hd1 : model.dAut ⟨db, hdb⟩ 1 = 1 := by
      have hmul := model.dAut_mul ⟨db, hdb⟩ 1 1
      rw [one_mul] at hmul
      have hne : model.dAut ⟨db, hdb⟩ 1 ≠ 0 := by
        intro h0
        have h00 : model.dAut ⟨db, hdb⟩ 0 = 0 := map_zero _
        exact one_ne_zero ((model.dAut ⟨db, hdb⟩).injective (h0.trans h00.symm))
      have hc' : model.dAut ⟨db, hdb⟩ 1 * 1
          = model.dAut ⟨db, hdb⟩ 1 * model.dAut ⟨db, hdb⟩ 1 := by
        rw [mul_one]; exact hmul
      exact (mul_left_cancel₀ hne hc').symm
    have hu1 : ((model.qEquiv (⟨qb, hqb⟩ : ↥(fc.rankOneQuotient).Q)⁻¹ : Fˣ) : F) = 1 := by
      have h := hkey 1
      rwa [hd1, one_mul] at h
    have hq1 : qb = 1 := by
      have h1 : model.qEquiv (⟨qb, hqb⟩ : ↥(fc.rankOneQuotient).Q)⁻¹ = 1 :=
        Units.ext (hu1.trans Units.val_one.symm)
      have h2 : (⟨qb, hqb⟩ : ↥(fc.rankOneQuotient).Q)⁻¹ = 1 := by
        apply model.qEquiv.injective
        rw [h1, map_one]
      have h3 : (⟨qb, hqb⟩ : ↥(fc.rankOneQuotient).Q) = 1 := by
        rw [← inv_inv (⟨qb, hqb⟩ : ↥(fc.rankOneQuotient).Q), h2, inv_one]
      have h4 := congrArg Subtype.val h3
      simpa using h4
    -- … and then `dAut` faithfulness kills the `Σ`-component.
    have hdx : ∀ x : F, model.dAut ⟨db, hdb⟩ x = x := by
      intro x
      have h := hkey x
      rwa [hu1, mul_one] at h
    have hdone : ∀ x : F, model.dAut 1 x = x := by
      intro x
      have h := model.dAut_conj 1 x
      simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h
      exact (model.emb_injective h).symm ▸ rfl
    have hd_eq : (⟨db, hdb⟩ : ↥(fc.rankOneQuotient).D) = 1 := by
      apply model.dAut_injective
      ext x
      rw [hdx x]
      exact (hdone x).symm
    have hdb1 : db = 1 := by
      have h := congrArg Subtype.val hd_eq
      simpa using h
    -- the class is a translation, i.e. `c ∈ R`.
    have hfin : QuotientGroup.mk' N' ⟨c, hcL⟩ ∈ MonoidHom.range model.emb := by
      rw [← hprod, ← hqd, hq1, hdb1]
      simp
    exact ⟨⟨c, hcL⟩, Subgroup.mem_comap.mpr hfin, rfl⟩
  · intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact fc.invImageF_mul_comm model ind hB2 hm y hy r hr

include model in
/-- **An element fixing every member of `𝒜` (setwise) centralizes `R`** ((12) tail,
faithfulness input).  Such an `n` fixes `P ∈ 𝒜`, hence centralizes `P` (step (1):
`N_G(P) = C_G(P)`).  For `t ∈ T`, `t ≠ 1`, both `⟨x₀·t⟩` and `⟨x₀²·t⟩` lie in `𝒜`
(`x₀` a nonidentity element of `P`, `x₀² ≠ 1` as `p` is odd); matching the unique
`T·P`-decompositions of the two conjugation relations pins the conjugation exponent
to `k ≡ 1 (mod p)`, so `n` centralizes `T` — no projective geometry needed.
`R = T·P` finishes. -/
theorem mul_comm_invImageF_of_forall_conj_smul_eq
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) {n : G}
    (hfix : ∀ P₁ : Subgroup G, P₁ ≤ fc.invImageF model → Nat.card ↥P₁ = fc.p →
      ¬ P₁ ≤ fc.sInvertedT model → MulAut.conj n • P₁ = P₁) :
    ∀ r ∈ fc.invImageF model, n * r = r * n := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  obtain ⟨hTle, -, -, hTinf⟩ := fc.sInvertedT_spec model ind hB2 hm
  have hab := fc.invImageF_mul_comm model ind hB2 hm
  -- `n` centralizes `P`.
  have hPnotT : ¬ fc.P ≤ fc.sInvertedT model := by
    intro hle
    have h1 : fc.P = ⊥ := by rw [← inf_eq_right.mpr hle, hTinf]
    have h2 := fc.card_P
    rw [h1, Subgroup.card_bot] at h2
    exact fc.p_prime.one_lt.ne h2
  have hnP : ∀ x ∈ fc.P, n * x * n⁻¹ = x := by
    have hPfix := hfix fc.P (fc.P_le_invImageF model) fc.card_P hPnotT
    have hnC : n ∈ Subgroup.centralizer (fc.P : Set G) := by
      rw [← fc.normalizer_P_eq_centralizer]
      exact conj_smul_eq_iff_mem_normalizer.mp hPfix
    intro x hx
    have h1 := Subgroup.mem_centralizer_iff.mp hnC x hx
    rw [← h1]; group
  -- a nonidentity element of `P`, of order `p`.
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
  have hx₀R : x₀ ∈ fc.invImageF model := fc.P_le_invImageF model hx₀P
  have hordx : orderOf x₀ = fc.p := orderOf_eq_prime
    (fc.pow_p_eq_one_of_mem_invImageF model ind hB2 hm hx₀R) hx₀1
  -- generic brick: `⟨z·t⟩ ∈ 𝒜` is fixed, for `z ∈ P`, `t ∈ T`, both nonidentity.
  have hAgen : ∀ z ∈ fc.P, ∀ t ∈ fc.sInvertedT model, z ≠ 1 → t ≠ 1 →
      MulAut.conj n • Subgroup.zpowers (z * t) = Subgroup.zpowers (z * t) := by
    intro z hz t ht hz1 ht1
    have hzR : z ∈ fc.invImageF model := fc.P_le_invImageF model hz
    have htR : t ∈ fc.invImageF model := hTle ht
    have hzt1 : z * t ≠ 1 := by
      intro h0
      have h1 : t = z⁻¹ := eq_inv_of_mul_eq_one_right h0
      have h2 : t ∈ fc.sInvertedT model ⊓ fc.P := ⟨ht, by rw [h1]; exact fc.P.inv_mem hz⟩
      rw [hTinf, Subgroup.mem_bot] at h2
      exact ht1 h2
    have hord : orderOf (z * t) = fc.p := orderOf_eq_prime
      (fc.pow_p_eq_one_of_mem_invImageF model ind hB2 hm (mul_mem hzR htR)) hzt1
    refine hfix _ ?_ ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact mul_mem hzR htR
    · rw [Nat.card_zpowers, hord]
    · intro hle
      have h1 : z * t ∈ fc.sInvertedT model := hle (Subgroup.mem_zpowers _)
      have h2 : z ∈ fc.sInvertedT model := by
        have h3 : z = (z * t) * t⁻¹ := by group
        rw [h3]
        exact mul_mem h1 ((fc.sInvertedT model).inv_mem ht)
      have h4 : z ∈ fc.sInvertedT model ⊓ fc.P := ⟨h2, hz⟩
      rw [hTinf, Subgroup.mem_bot] at h4
      exact hz1 h4
  -- `n` centralizes `T`.
  have hnT : ∀ t ∈ fc.sInvertedT model, n * t * n⁻¹ = t := by
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1]; group
    have htR : t ∈ fc.invImageF model := hTle ht
    have hordt : orderOf t = fc.p := orderOf_eq_prime
      (fc.pow_p_eq_one_of_mem_invImageF model ind hB2 hm htR) ht1
    have hcomm : Commute x₀ t := hab x₀ hx₀R t htR
    -- `x₀² ≠ 1` since `p` is odd.
    have hx₀2 : x₀ * x₀ ≠ 1 := by
      intro h0
      have h1 : orderOf x₀ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h0)
      rw [hordx] at h1
      have h2 := (Nat.prime_dvd_prime_iff_eq fc.p_prime Nat.prime_two).mp h1
      obtain ⟨j, hj⟩ := fc.p_odd
      omega
    have hx₀2P : x₀ * x₀ ∈ fc.P := mul_mem hx₀P hx₀P
    have hcomm2 : Commute (x₀ * x₀) t := hab _ (fc.P_le_invImageF model hx₀2P) t htR
    -- first relation: `n t n⁻¹ = x₀^(k-1)·t^k` from `⟨x₀·t⟩` fixed.
    have hmem1 : n * (x₀ * t) * n⁻¹ ∈ Subgroup.zpowers (x₀ * t) := by
      have h1 := Subgroup.smul_mem_pointwise_smul (x₀ * t) (MulAut.conj n)
        (Subgroup.zpowers (x₀ * t)) (Subgroup.mem_zpowers _)
      rw [hAgen x₀ hx₀P t ht hx₀1 ht1] at h1
      have h2 : MulAut.conj n • (x₀ * t) = n * (x₀ * t) * n⁻¹ := rfl
      rwa [h2] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem1
    have hntn : n * t * n⁻¹ = x₀ ^ (k - 1) * t ^ k := by
      have h1 : n * (x₀ * t) * n⁻¹ = (n * x₀ * n⁻¹) * (n * t * n⁻¹) := by group
      rw [hnP x₀ hx₀P] at h1
      have h3 : x₀ * (n * t * n⁻¹) = x₀ ^ k * t ^ k := by
        rw [← h1, ← hcomm.mul_zpow, hk]
      have h4 : n * t * n⁻¹ = x₀⁻¹ * (x₀ ^ k * t ^ k) := by
        rw [← h3]; group
      rw [h4, ← mul_assoc]
      congr 1
      rw [← zpow_neg_one, ← zpow_add]
      congr 1
      ring
    -- second relation from `⟨x₀²·t⟩` pins `k ≡ 1 (mod p)`.
    have hmem2 : n * ((x₀ * x₀) * t) * n⁻¹ ∈ Subgroup.zpowers ((x₀ * x₀) * t) := by
      have h1 := Subgroup.smul_mem_pointwise_smul ((x₀ * x₀) * t) (MulAut.conj n)
        (Subgroup.zpowers ((x₀ * x₀) * t)) (Subgroup.mem_zpowers _)
      rw [hAgen (x₀ * x₀) hx₀2P t ht hx₀2 ht1] at h1
      have h2 : MulAut.conj n • ((x₀ * x₀) * t) = n * ((x₀ * x₀) * t) * n⁻¹ := rfl
      rwa [h2] at h1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem2
    have hL : n * ((x₀ * x₀) * t) * n⁻¹ = x₀ ^ (k + 1) * t ^ k := by
      have h1 : n * ((x₀ * x₀) * t) * n⁻¹
          = (n * x₀ * n⁻¹) * (n * x₀ * n⁻¹) * (n * t * n⁻¹) := by group
      rw [hnP x₀ hx₀P, hntn] at h1
      rw [h1]
      group
    have hR : ((x₀ * x₀) * t) ^ j = x₀ ^ (2 * j) * t ^ j := by
      rw [hcomm2.mul_zpow]
      congr 1
      rw [← zpow_two, ← zpow_mul]
    have hmatch : x₀ ^ (k + 1) * t ^ k = x₀ ^ (2 * j) * t ^ j := by
      rw [← hL, ← hj, hR]
    have hsep : x₀ ^ (k + 1 - 2 * j) = t ^ (j - k) := by
      calc x₀ ^ (k + 1 - 2 * j)
          = x₀ ^ (-(2 * j)) * x₀ ^ (k + 1) := by
            rw [← zpow_add]
            congr 1
            ring
        _ = x₀ ^ (-(2 * j)) * ((x₀ ^ (k + 1) * t ^ k) * t ^ (-k)) := by
            rw [mul_assoc (x₀ ^ (k + 1)), ← zpow_add t k (-k), add_neg_cancel, zpow_zero,
              mul_one]
        _ = x₀ ^ (-(2 * j)) * ((x₀ ^ (2 * j) * t ^ j) * t ^ (-k)) := by rw [hmatch]
        _ = t ^ (j - k) := by
            rw [← mul_assoc, ← mul_assoc, ← zpow_add x₀ (-(2 * j)) (2 * j), neg_add_cancel,
              zpow_zero, one_mul, ← zpow_add t j (-k), sub_eq_add_neg]
    have hsep1 : x₀ ^ (k + 1 - 2 * j) = 1 := by
      have h4 : x₀ ^ (k + 1 - 2 * j) ∈ fc.sInvertedT model ⊓ fc.P :=
        ⟨hsep ▸ zpow_mem ht _, zpow_mem hx₀P _⟩
      rwa [hTinf, Subgroup.mem_bot] at h4
    have hdvd1 : (fc.p : ℤ) ∣ (k + 1 - 2 * j) := by
      rw [← hordx]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hsep1
    have hdvd2 : (fc.p : ℤ) ∣ (j - k) := by
      rw [← hordt]
      exact orderOf_dvd_iff_zpow_eq_one.mpr (hsep ▸ hsep1)
    have hdvd3 : (fc.p : ℤ) ∣ (k - 1) := by
      have h1 : k - 1 = -(k + 1 - 2 * j) - 2 * (j - k) := by ring
      rw [h1]
      exact dvd_sub (dvd_neg.mpr hdvd1) (hdvd2.mul_left 2)
    rw [hntn]
    have h1 : x₀ ^ (k - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hordx]; exact hdvd3)
    have h2 : t ^ k = t := by
      have h4 : t ^ (k - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hordt]; exact hdvd3)
      calc t ^ k = t ^ (k - 1 + 1) := by congr 1; ring
        _ = t ^ (k - 1) * t := zpow_add_one t (k - 1)
        _ = t := by rw [h4, one_mul]
    rw [h1, h2, one_mul]
  -- assemble via `R = T·P`.
  intro r hr
  have hrmem : r ∈ (fc.sInvertedT model : Set G) * (fc.P : Set G) := by
    rw [← fc.coe_invImageF_eq_sInvertedT_mul_P model ind hB2 hm]
    exact hr
  obtain ⟨t, ht, x, hx, rfl⟩ := hrmem
  have h1 : n * (t * x) * n⁻¹ = t * x := by
    have h2 : n * (t * x) * n⁻¹ = (n * t * n⁻¹) * (n * x * n⁻¹) := by group
    rw [h2, hnT t ht, hnP x hx]
  calc n * (t * x) = (n * (t * x) * n⁻¹) * n := by group
    _ = (t * x) * n := by rw [h1]

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
