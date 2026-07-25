/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepFourteen

/-!
# Peterfalvi Part II, Ch. II, step (14): the action of `N_G(RΣ)` on `𝒜₂`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (14), p. 113.

Step (14) states that `N_G(RΣ)/RΣ ≅ S₃`.  The isomorphism is realised by the
action of `N_G(RΣ)` on the three-element set `𝒜₂` of order-`3` subgroups of
`Z₁P` other than `Z₁` (`lineSetTwo`, whose cardinality was computed in
`ncard_lineSetTwo`).  This file builds that permutation representation:

* `normalizerRSigma` — the subgroup `N_G(RΣ)`;
* `smul_mem_lineSetTwo_iff` — conjugation by an element of `N_G(RΣ)` preserves
  `𝒜₂` (it preserves `Z₁P = Z(RΣ)` and `Z₁ = ⁅RΣ, RΣ⁆`, and subgroup orders);
* `lineSetTwoPermHom` — the resulting homomorphism `N_G(RΣ) →* Sym(𝒜₂)`.

Conjugation is written with the pointwise action of `MulAut G` on `Subgroup G`,
which is the mathlib idiom; `smul_eq_map_conj` bridges it to the `Subgroup.map`
form used in `StepFourteen`.
-/

set_option autoImplicit false

open scoped Pointwise

namespace OddOrder.Peterfalvi.Appendices.Suzuki

section ConjSmul

variable {G' : Type*} [Group G']

/-- The pointwise action of `MulAut G'` on subgroups, written as a `Subgroup.map`. -/
theorem smul_eq_map_conj (g : G') (A : Subgroup G') :
    (MulAut.conj g) • A = A.map (MulAut.conj g).toMonoidHom := rfl

/-- Membership in a conjugated subgroup. -/
theorem mem_conj_smul_iff {g x : G'} {A : Subgroup G'} :
    x ∈ (MulAut.conj g) • A ↔ g⁻¹ * x * g ∈ A := by
  rw [smul_eq_map_conj, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [show (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ from rfl, h]
    exact hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

/-- Conjugation transports membership along a fixed subgroup. -/
theorem conj_mem_of_conj_smul_eq {g x : G'} {A : Subgroup G'}
    (h : (MulAut.conj g) • A = A) (hx : x ∈ A) : g * x * g⁻¹ ∈ A := by
  rw [← h, mem_conj_smul_iff]
  have h1 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [h1]
  exact hx

/-- An element centralizing a subgroup elementwise fixes it under conjugation. -/
theorem conj_smul_eq_of_forall_comm {g : G'} {A : Subgroup G'}
    (h : ∀ x ∈ A, g * x = x * g) : (MulAut.conj g) • A = A := by
  ext x
  rw [mem_conj_smul_iff]
  constructor
  · intro hx
    have h1 : g * (g⁻¹ * x * g) = (g⁻¹ * x * g) * g := h _ hx
    have h2 : x = g⁻¹ * x * g := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = ((g⁻¹ * x * g) * g) * g⁻¹ := by rw [h1]
        _ = g⁻¹ * x * g := by group
    rw [h2]
    exact hx
  · intro hx
    have h1 : g⁻¹ * x * g = x := by
      calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
        _ = g⁻¹ * (g * x) := by rw [← h x hx]
        _ = x := by group
    rw [h1]
    exact hx

end ConjSmul

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)
  {F : Type uG} [NearFields.NearField F]
  (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    NearFields.AffineNearFieldModel fc.rankOneQuotient F)

/-- **`N_G(RΣ)`** ((14), p. 113), with `RΣ = R ⊔ Σ` in the notation of (11). -/
noncomputable def normalizerRSigma : Subgroup G :=
  Subgroup.normalizer ((fc.invImageF model
    ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G) : Set G)

include model in
theorem mem_normalizerRSigma_iff {g : G} :
    g ∈ fc.normalizerRSigma model ↔ ∀ y : G,
      y ∈ (fc.invImageF model
          ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G)
        ↔ g * y * g⁻¹ ∈ (fc.invImageF model
          ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G) :=
  Subgroup.mem_set_normalizer_iff

include model in
/-- **`N_G(RΣ)` fixes `Z₁`** ((14), p. 113): `Z₁ = ⁅RΣ, RΣ⁆` is a characteristic
subgroup of `RΣ`, so conjugation by a normalizing element maps it onto itself. -/
theorem conj_smul_zpowers_eq
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {g : G}
    (hg : g ∈ fc.normalizerRSigma model) :
    (MulAut.conj g) • Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t)
      = Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) := by
  classical
  set Z₁ : Subgroup G := Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
    * fc.toHypothesis.t) with hZ₁_def
  have hle : (MulAut.conj g) • Z₁ ≤ Z₁ := by
    intro x hx
    rw [mem_conj_smul_iff] at hx
    have h := fc.conj_mem_zpowers_of_mem_normalizer_sup model ind hB2 hg hx
    have h1 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [h1] at h
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  rw [smul_eq_map_conj,
    Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective]

include model in
/-- **Conjugation by `N_G(RΣ)` preserves `𝒜₂`** ((14), p. 113): it preserves
`Z₁P = Z(RΣ)` and `Z₁ = ⁅RΣ, RΣ⁆`, and it preserves the order of a subgroup. -/
theorem smul_mem_lineSetTwo
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {g : G}
    (hg : g ∈ fc.normalizerRSigma model) {A : Subgroup G} (hA : A ∈ fc.lineSetTwo) :
    (MulAut.conj g) • A ∈ fc.lineSetTwo := by
  classical
  obtain ⟨hle, hcard, hne⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_conj_smul_iff] at hx
    have h := fc.conj_mem_zpowers_sup_P_of_mem_normalizer_sup model ind hB2 hg
      (hle hx)
    have h1 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [h1] at h
  · rw [smul_eq_map_conj,
      Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective]
    exact hcard
  · intro hEq
    refine hne ?_
    have hZ := fc.conj_smul_zpowers_eq model ind hB2 hg
    rw [smul_eq_map_conj] at hEq hZ
    exact Subgroup.map_injective (MulAut.conj g).injective (hEq.trans hZ.symm)

include model in
/-- Conjugation by an element of `N_G(RΣ)` restricts to a bijection of `𝒜₂`. -/
theorem smul_mem_lineSetTwo_iff
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {g : G}
    (hg : g ∈ fc.normalizerRSigma model) (A : Subgroup G) :
    (MulAut.conj g) • A ∈ fc.lineSetTwo ↔ A ∈ fc.lineSetTwo := by
  refine ⟨fun h => ?_, fun h => fc.smul_mem_lineSetTwo model ind hB2 hg h⟩
  have h' := fc.smul_mem_lineSetTwo model ind hB2 (inv_mem hg) h
  rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h'

include model in
/-- **`C_G(Z₁P) = C_G(P) ⊓ C_G(st) = RΣ`** (quoted in (15), p. 113).

`RΣ` centralizes `Z₁P`: `R` is abelian and contains both `st` and `P`, while
`Σ = C_W(P)` centralizes `P` by definition and `st` because `Σ ≤ V = C_D(s) = C_D(t)`.
Conversely `|C_G(P)| = 3⁴·8` by the order accounting of (11) in case (10.2), and `st`
lies in `T`, so it is a strongly real element of order `3` and `|C_G(st)|` is odd
(Ch. I §3, Lemma 3).  Hence `|C_G(P) ⊓ C_G(st)|` is an odd divisor of `3⁴·8`, so it
divides `3⁴ = 81 = |RΣ|`. -/
theorem centralizer_P_inf_centralizer_mul_t_eq_sup
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    Subgroup.centralizer (fc.P : Set G)
        ⊓ Subgroup.centralizer ({fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t} : Set G)
      = fc.invImageF model
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨hpSig, hp3, hF9, -, -, -⟩ := fc.step_twelve model ind hB2
  obtain ⟨-, -, -, hSig3, -⟩ :=
    fc.card_field_eq_nine_of_p_dvd_card_centralizer_W ind model hB2 hpSig
  obtain ⟨e⟩ := fc.sigma_mulEquiv_centralizer_W ind
  have hm : Nat.card F = fc.p ^ 2 := by rw [hF9, hp3]; norm_num
  have hPcard : Nat.card ↥fc.P = 3 := by rw [fc.card_P, hp3]
  -- `|C_G(P)| = 3⁴·8` (order accounting of (11) in case (10.2))
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF9]; norm_num)
  have hQ8 : Nat.card ↥(fc.rankOneQuotient).Q = 8 := by
    haveI := Fintype.ofFinite F
    haveI := Classical.decEq F
    rw [Nat.card_congr model.qEquiv.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_units, ← Nat.card_eq_fintype_card, hF9]
  have hD3 : Nat.card ↥(fc.rankOneQuotient).D = 3 := by
    rw [Nat.card_congr e.toEquiv, hSig3]
  have hCPcard : Nat.card ↥(Subgroup.centralizer (fc.P : Set G)) = 81 * 8 := by
    rw [fc.card_centralizer_P model ind, hPcard, hF9, hQ8, hD3]
  set R : Subgroup G := fc.invImageF model with hR_def
  set Sg : Subgroup G :=
    fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G) with hSg_def
  have hRcard : Nat.card ↥R = 27 := by
    rw [hR_def, fc.card_invImageF model ind, hF9, hPcard]
  have hRScard : Nat.card ↥(R ⊔ Sg) = 81 := by
    rw [hR_def, hSg_def, fc.card_sup_invImageF_centralizer_W model ind]
    rw [← hR_def, ← hSg_def, hRcard, hSig3]
  -- `RΣ` centralizes both `P` and `st`
  have habR := fc.invImageF_mul_comm model ind hB2 hm
  have hPR : fc.P ≤ R := fc.P_le_invImageF model
  have hstR : fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t ∈ R :=
    fc.distinguishedInvolution_mul_t_mem_invImageF model
  have hle : R ⊔ Sg ≤ Subgroup.centralizer (fc.P : Set G)
      ⊓ Subgroup.centralizer ({fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t} : Set G) := by
    refine sup_le (le_inf ?_ ?_)
      (le_inf inf_le_right
        fc.centralizer_W_le_centralizer_distinguishedInvolution_mul_t)
    · intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (habR r hr y (hPR hy)).symm
    · intro r hr
      exact Subgroup.mem_centralizer_singleton_iff.mpr (habR r hr _ hstR)
  -- `|C_G(st)|` is odd: `st ∈ T` is strongly real of order `3`
  have hstord : orderOf (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = 3 := by
    rw [fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  have hst2 : (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ^ 2 ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hstord] at h1
    omega
  have hoddC := fc.toHypothesis.centralizer_natCard_odd_of_stronglyReal
    (fc.isStronglyReal_of_mem_sInvertedT model ind hB2 hm
      (fc.distinguishedInvolution_mul_t_mem_sInvertedT model ind hB2 hm)) hst2
  -- an odd divisor of `3⁴·8` divides `3⁴`
  have hodd' : Odd (Nat.card ↥(Subgroup.centralizer (fc.P : Set G)
      ⊓ Subgroup.centralizer ({fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t} : Set G))) :=
    hoddC.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hdvd648 : Nat.card ↥(Subgroup.centralizer (fc.P : Set G)
      ⊓ Subgroup.centralizer ({fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t} : Set G)) ∣ 81 * 8 := by
    rw [← hCPcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hdvd81 := (hodd'.coprime_two_right.pow_right 3).dvd_of_dvd_mul_right hdvd648
  have hge : 81 ∣ Nat.card ↥(Subgroup.centralizer (fc.P : Set G)
      ⊓ Subgroup.centralizer ({fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t} : Set G)) := by
    rw [← hRScard]
    exact Subgroup.card_dvd_of_le hle
  exact (Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (by rw [Nat.dvd_antisymm hdvd81 hge, hRScard]))).symm

include model in
/-- **The permutation representation of `N_G(RΣ)` on `𝒜₂`** ((14), p. 113).
Step (14) asserts that this map is onto `Sym(𝒜₂) ≅ S₃` with kernel `RΣ`. -/
noncomputable def lineSetTwoPermHom
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    ↥(fc.normalizerRSigma model) →* Equiv.Perm ↥fc.lineSetTwo where
  toFun g := (MulAction.toPerm (MulAut.conj (g : G))).subtypePerm
    (fun A => fc.smul_mem_lineSetTwo_iff model ind hB2 g.2 A)
  map_one' := by
    refine Equiv.ext fun A => Subtype.ext ?_
    change (MulAut.conj ((1 : ↥(fc.normalizerRSigma model)) : G)) • (A : Subgroup G)
      = (A : Subgroup G)
    rw [Subgroup.coe_one, map_one, one_smul]
  map_mul' g h := by
    refine Equiv.ext fun A => Subtype.ext ?_
    change (MulAut.conj ((g * h : ↥(fc.normalizerRSigma model)) : G)) • (A : Subgroup G)
      = (MulAut.conj ((g : G))) • ((MulAut.conj ((h : G))) • (A : Subgroup G))
    rw [Subgroup.coe_mul, map_mul, mul_smul]

include model in
/-- `Z₁ ⊓ P = 1`: `Z₁ ≤ T` by the "`Z₁ ⊂ T`" remark of (14), and `T ⊓ P = 1` by (11). -/
theorem zpowers_inf_P_eq_bot
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
      ⊓ fc.P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ fc.sInvertedT model ⊓ fc.P :=
    ⟨fc.zpowers_distinguishedInvolution_mul_t_le_sInvertedT model ind hB2 hm hx.1,
      hx.2⟩
  rwa [(fc.sInvertedT_spec model ind hB2 hm).2.2.2] at hx'

include model in
/-- `P ∈ 𝒜₂` (it has order `3` and meets `Z₁` trivially). -/
theorem P_mem_lineSetTwo
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) : fc.P ∈ fc.lineSetTwo := by
  obtain ⟨-, hp3, hF9, -, -, -⟩ := fc.step_twelve model ind hB2
  have hm : Nat.card F = fc.p ^ 2 := by rw [hF9, hp3]; norm_num
  have hPcard : Nat.card ↥fc.P = 3 := by rw [fc.card_P, hp3]
  refine ⟨le_sup_right, hPcard, fun hEq => ?_⟩
  have hbot := fc.zpowers_inf_P_eq_bot model ind hB2 hm
  rw [← hEq, inf_idem] at hbot
  rw [hbot, Subgroup.card_bot] at hPcard
  omega

include model in
/-- `⟨(st)·y⟩ ∈ 𝒜₂` for a nonidentity `y ∈ P`: the two commuting order-`3` elements
`st` and `y` generate distinct lines of `Z₁P`. -/
theorem zpowers_mul_mem_lineSetTwo
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {y : G} (hyP : y ∈ fc.P)
    (hy1 : y ≠ 1) :
    Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t * y) ∈ fc.lineSetTwo := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨-, hp3, hF9, -, -, -⟩ := fc.step_twelve model ind hB2
  have hm : Nat.card F = fc.p ^ 2 := by rw [hF9, hp3]; norm_num
  set z : G := fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t with hz_def
  have hbot := fc.zpowers_inf_P_eq_bot model ind hB2 hm
  have hzZ : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
  have hstord : orderOf z = 3 := by
    rw [hz_def, fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  -- `z` and `y` commute inside the abelian `R`
  have habR := fc.invImageF_mul_comm model ind hB2 hm
  have hcomm : Commute z y :=
    habR z (fc.distinguishedInvolution_mul_t_mem_invImageF model) y
      (fc.P_le_invImageF model hyP)
  have hy3 : y ^ 3 = 1 := by
    have h := fc.P.orderOf_dvd_natCard hyP
    rw [fc.card_P, hp3] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hz3 : z ^ 3 = 1 := by rw [← hstord]; exact pow_orderOf_eq_one z
  -- `z·y ≠ 1`
  have hzy1 : z * y ≠ 1 := by
    intro h
    have hz' : z ∈ Subgroup.zpowers z ⊓ fc.P := by
      refine ⟨hzZ, ?_⟩
      have : z = y⁻¹ := by rw [← mul_one z, ← mul_inv_cancel y, ← mul_assoc, h, one_mul]
      rw [this]
      exact fc.P.inv_mem hyP
    rw [hbot, Subgroup.mem_bot] at hz'
    rw [hz'] at hstord
    simp at hstord
  refine ⟨Subgroup.zpowers_le.mpr (Subgroup.mul_mem_sup hzZ hyP), ?_, ?_⟩
  · rw [Nat.card_zpowers]
    have hdvd : orderOf (z * y) ∣ 3 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [hcomm.mul_pow, hy3, hz3, one_mul])
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hzy1
    · exact h3
  · intro hEq
    have hyZ : y ∈ Subgroup.zpowers z ⊓ fc.P := by
      refine ⟨?_, hyP⟩
      have h1 : y = z⁻¹ * (z * y) := by group
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzZ)
        (hEq ▸ Subgroup.mem_zpowers (z * y))
    rw [hbot, Subgroup.mem_bot] at hyZ
    exact hy1 hyZ

@[simp]
theorem lineSetTwoPermHom_apply
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (g : ↥(fc.normalizerRSigma model)) (A : ↥fc.lineSetTwo) :
    (fc.lineSetTwoPermHom model ind hB2 g A : Subgroup G)
      = (MulAut.conj ((g : G))) • (A : Subgroup G) := rfl

include model in
/-- **The kernel of the action of `N_G(RΣ)` on `𝒜₂` is `RΣ`** ((14), p. 113).

`RΣ` acts trivially because `Z₁P = Z(RΣ)`, so it centralizes every member of `𝒜₂`
elementwise.  Conversely an element `g` of the kernel fixes `P ∈ 𝒜₂`, hence
centralizes `P` (step (1): `N_G(P) = C_G(P)`); it also fixes `Z₁` and the line
`⟨(st)·y⟩` for a generator `y` of `P`, and matching the unique `Z₁ × P`
decomposition of `g·(st·y)·g⁻¹ = (g·st·g⁻¹)·y` pins the exponent to `k ≡ 1 (mod 3)`,
so `g` centralizes `st` as well.  Thus `g ∈ C_G(P) ⊓ C_G(st) = RΣ`.

Peterfalvi instead argues that the kernel lies in `N_G(P) = R·C_Q(P)·Σ` and that
`C_Q(P)^#` is fixed-point-free on `𝒜 − {P}`; the route taken here replaces the
structure of `N_G(P)` by the order of `C_G(P)` together with the oddness of
`|C_G(st)|` (`centralizer_P_inf_centralizer_mul_t_eq_sup`). -/
theorem mem_ker_lineSetTwoPermHom_iff
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    {g : ↥(fc.normalizerRSigma model)} :
    g ∈ (fc.lineSetTwoPermHom model ind hB2).ker ↔
      (g : G) ∈ fc.invImageF model
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨-, hp3, hF9, -, -, -⟩ := fc.step_twelve model ind hB2
  have hm : Nat.card F = fc.p ^ 2 := by rw [hF9, hp3]; norm_num
  set z : G := fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t with hz_def
  have hstord : orderOf z = 3 := by
    rw [hz_def, fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  have hcentre := fc.inf_centralizer_sup_eq_zpowers_sup_P model ind hB2
  constructor
  · intro hker
    have hfix : ∀ A ∈ fc.lineSetTwo, (MulAut.conj (g : G)) • A = A := by
      intro A hA
      have h1 : fc.lineSetTwoPermHom model ind hB2 g ⟨A, hA⟩ = ⟨A, hA⟩ := by
        rw [MonoidHom.mem_ker.mp hker]; rfl
      simpa using congrArg Subtype.val h1
    -- `g` fixes `P`, hence centralizes it (step (1): `N_G(P) = C_G(P)`)
    have hgC : (g : G) ∈ Subgroup.centralizer (fc.P : Set G) := by
      rw [← fc.normalizer_P_eq_centralizer]
      exact conj_smul_eq_iff_mem_normalizer.mp
        (hfix fc.P (fc.P_mem_lineSetTwo model ind hB2))
    obtain ⟨y, hyP, hy1⟩ : ∃ y ∈ fc.P, y ≠ (1 : G) := by
      by_contra hcon
      push Not at hcon
      have hbot : fc.P = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_bot]
        exact hcon x hx
      have h2 := fc.card_P
      rw [hbot, Subgroup.card_bot, hp3] at h2
      omega
    have hyord : orderOf y = 3 := by
      have h := fc.P.orderOf_dvd_natCard hyP
      rw [fc.card_P, hp3] at h
      rcases (Nat.dvd_prime (by norm_num)).mp h with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hy1
      · exact h3
    have hgy : (g : G) * y * (g : G)⁻¹ = y := by
      have h1 := Subgroup.mem_centralizer_iff.mp hgC y hyP
      calc (g : G) * y * (g : G)⁻¹ = (y * (g : G)) * (g : G)⁻¹ := by rw [← h1]
        _ = y := by group
    -- `g` fixes the line `⟨z·y⟩`
    have hcomm : Commute z y :=
      fc.invImageF_mul_comm model ind hB2 hm z
        (fc.distinguishedInvolution_mul_t_mem_invImageF model) y
        (fc.P_le_invImageF model hyP)
    have hmem := conj_mem_of_conj_smul_eq
      (hfix _ (fc.zpowers_mul_mem_lineSetTwo model ind hB2 hyP hy1))
      (Subgroup.mem_zpowers (z * y))
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    have hu : (g : G) * z * (g : G)⁻¹ ∈ Subgroup.zpowers z :=
      conj_mem_of_conj_smul_eq (fc.conj_smul_zpowers_eq model ind hB2 g.2)
        (Subgroup.mem_zpowers z)
    have hsplit : (g : G) * (z * y) * (g : G)⁻¹
        = ((g : G) * z * (g : G)⁻¹) * y := by
      calc (g : G) * (z * y) * (g : G)⁻¹
          = ((g : G) * z * (g : G)⁻¹) * ((g : G) * y * (g : G)⁻¹) := by group
        _ = ((g : G) * z * (g : G)⁻¹) * y := by rw [hgy]
    have heq : z ^ k * y ^ k = ((g : G) * z * (g : G)⁻¹) * y := by
      rw [← hcomm.mul_zpow, hk, hsplit]
    -- unique `Z₁ × P` decomposition
    have hab : (z ^ k)⁻¹ * ((g : G) * z * (g : G)⁻¹) = y ^ k * y⁻¹ := by
      have h1 : y ^ k = (z ^ k)⁻¹ * (((g : G) * z * (g : G)⁻¹) * y) := by
        rw [← heq]; group
      calc (z ^ k)⁻¹ * ((g : G) * z * (g : G)⁻¹)
          = ((z ^ k)⁻¹ * (((g : G) * z * (g : G)⁻¹) * y)) * y⁻¹ := by group
        _ = y ^ k * y⁻¹ := by rw [← h1]
    have hone : (z ^ k)⁻¹ * ((g : G) * z * (g : G)⁻¹) = 1 := by
      have hmemboth : (z ^ k)⁻¹ * ((g : G) * z * (g : G)⁻¹)
          ∈ Subgroup.zpowers z ⊓ fc.P := by
        refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _
          (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k)) hu, ?_⟩
        rw [hab]
        exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hyP k)
          (Subgroup.inv_mem _ hyP)
      rwa [fc.zpowers_inf_P_eq_bot model ind hB2 hm, Subgroup.mem_bot] at hmemboth
    have hyk : y ^ k = y := by
      have h1 : y ^ k * y⁻¹ = 1 := by rw [← hab, hone]
      calc y ^ k = (y ^ k * y⁻¹) * y := by group
        _ = y := by rw [h1, one_mul]
    -- `k ≡ 1 (mod 3)`, so `g` centralizes `z` too
    have hzk : z ^ k = z := by
      have hk1 : y ^ (k - 1) = 1 := by
        rw [zpow_sub, zpow_one, hyk, mul_inv_cancel]
      have hdvd : ((3 : ℕ) : ℤ) ∣ k - 1 := by
        rw [← hyord]
        exact orderOf_dvd_iff_zpow_eq_one.mpr hk1
      have hz1 : z ^ (k - 1) = 1 :=
        orderOf_dvd_iff_zpow_eq_one.mp (by rw [hstord]; exact hdvd)
      rw [zpow_sub, zpow_one] at hz1
      calc z ^ k = (z ^ k * z⁻¹) * z := by group
        _ = z := by rw [hz1, one_mul]
    have hgz : (g : G) * z = z * (g : G) := by
      have h1 : (g : G) * z * (g : G)⁻¹ = z := by
        calc (g : G) * z * (g : G)⁻¹
            = z ^ k * ((z ^ k)⁻¹ * ((g : G) * z * (g : G)⁻¹)) := by group
          _ = z ^ k := by rw [hone, mul_one]
          _ = z := hzk
      calc (g : G) * z = ((g : G) * z * (g : G)⁻¹) * (g : G) := by group
        _ = z * (g : G) := by rw [h1]
    rw [← fc.centralizer_P_inf_centralizer_mul_t_eq_sup model ind hB2]
    exact ⟨hgC, Subgroup.mem_centralizer_singleton_iff.mpr hgz⟩
  · intro hg
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun A => Subtype.ext ?_
    change (MulAut.conj ((g : G))) • (A : Subgroup G) = (A : Subgroup G)
    refine conj_smul_eq_of_forall_comm fun x hx => ?_
    have hxZ : x ∈ Subgroup.zpowers z ⊔ fc.P := (fc.mem_lineSetTwo.mp A.2).1 hx
    rw [← hcentre] at hxZ
    exact Subgroup.mem_centralizer_iff.mp hxZ.2 (g : G) hg

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
