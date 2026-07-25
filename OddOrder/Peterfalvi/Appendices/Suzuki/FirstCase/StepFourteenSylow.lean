/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepFourteenAction

/-!
# Peterfalvi Part II, Ch. II, step (14): the `3`-subgroup `R₁`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (14), p. 113.

Step (14) asserts the existence of a `3`-subgroup `R₁` of `G` with
`N_G(RΣ)/RΣ = (R₁/RΣ) ⋊ ⟨s⟩ ≅ S₃`.  Since `|N_G(RΣ)| = 2·3⁵`
(`card_normalizerRSigma`), its Sylow `3`-subgroup has index `2`, hence is normal
and unique, and so consists of all the `3`-elements of `N_G(RΣ)`; that is the
choice-free description taken as the definition of `R₁` here.

The file then proves the assertions of (14) about `R₁`: `|R₁| = 3⁵`,
`C_{R₁}(P) = RΣ` and `Z(R₁) = Z₁`.
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

/-- **`R₁`** ((14), p. 113): the unique Sylow `3`-subgroup of `N_G(RΣ)`.

Since `|N_G(RΣ)| = 2·3⁵`, its Sylow `3`-subgroup has index `2`, hence is normal and
unique, and therefore consists of all the `3`-elements of `N_G(RΣ)`.  That is the
choice-free description used as the definition here. -/
noncomputable def sylowThreeNormalizerRSigma : Subgroup G :=
  Subgroup.closure {g : G | g ∈ fc.normalizerRSigma model ∧ ∃ j : ℕ, orderOf g = 3 ^ j}

include model in
theorem sylowThreeNormalizerRSigma_def :
    fc.sylowThreeNormalizerRSigma model
      = Subgroup.closure {g : G | g ∈ fc.normalizerRSigma model
        ∧ ∃ j : ℕ, orderOf g = 3 ^ j} := rfl

include model in
/-- **`R₁` is the image of any Sylow `3`-subgroup of `N_G(RΣ)`** ((14), p. 113): the
Sylow `3`-subgroup has index `2` in `N_G(RΣ)`, hence is normal and unique, so it
absorbs every `3`-element. -/
theorem sylowThreeNormalizerRSigma_eq_map
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (S : Sylow 3 ↥(fc.normalizerRSigma model)) :
    fc.sylowThreeNormalizerRSigma model
      = (S : Subgroup ↥(fc.normalizerRSigma model)).map
        (fc.normalizerRSigma model).subtype
      ∧ Nat.card ↥(S : Subgroup ↥(fc.normalizerRSigma model)) = 3 ^ 5 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hNcard := fc.card_normalizerRSigma model ind hB2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp S.isPGroup'
  have hmul := (S : Subgroup ↥(fc.normalizerRSigma model)).card_mul_index
  rw [hk, hNcard] at hmul
  have hnd := S.not_dvd_index
  have hcop : Nat.Coprime (3 ^ 5)
      ((S : Subgroup ↥(fc.normalizerRSigma model)).index) :=
    Nat.Coprime.pow_left 5 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hnd)
  have h1 : (3 : ℕ) ^ 5 ∣ 3 ^ k := by
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [hmul]
    exact ⟨2, by ring⟩
  have h2 : (3 : ℕ) ^ k ∣ 3 ^ 5 :=
    (Nat.Coprime.pow_left k (by norm_num)).dvd_of_dvd_mul_left ⟨_, hmul.symm⟩
  have hkeq : k = 5 :=
    le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2)
      ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1)
  have hScard : Nat.card ↥(S : Subgroup ↥(fc.normalizerRSigma model)) = 3 ^ 5 := by
    rw [hk, hkeq]
  have hSidx : (S : Subgroup ↥(fc.normalizerRSigma model)).index = 2 := by
    rw [hkeq] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : (0 : ℕ) < 3 ^ 5)
      (by rw [hmul]; ring)
  haveI hSn : (S : Subgroup ↥(fc.normalizerRSigma model)).Normal :=
    Subgroup.normal_of_index_eq_two hSidx
  letI := Sylow.unique_of_normal S hSn
  refine ⟨le_antisymm ?_ ?_, hScard⟩
  · rw [fc.sylowThreeNormalizerRSigma_def model, Subgroup.closure_le]
    rintro g ⟨hgN, j, hj⟩
    have hz : IsPGroup 3
        ↥(Subgroup.zpowers (⟨g, hgN⟩ : ↥(fc.normalizerRSigma model))) :=
      IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hj])
    obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
    have hmemQ : (⟨g, hgN⟩ : ↥(fc.normalizerRSigma model))
        ∈ (Q : Subgroup ↥(fc.normalizerRSigma model)) := hQ (Subgroup.mem_zpowers _)
    rw [Subsingleton.elim Q S] at hmemQ
    exact ⟨⟨g, hgN⟩, hmemQ, rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    rw [fc.sylowThreeNormalizerRSigma_def model]
    refine Subgroup.subset_closure ⟨y.2, ?_⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf).mp S.isPGroup' ⟨y, hy⟩
    refine ⟨j, ?_⟩
    change orderOf ((y : G)) = 3 ^ j
    rw [Subgroup.orderOf_coe]
    rwa [Subgroup.orderOf_mk] at hj

include model in
/-- **`|R₁| = 3⁵`** ((14), p. 113). -/
theorem card_sylowThreeNormalizerRSigma
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    Nat.card ↥(fc.sylowThreeNormalizerRSigma model) = 3 ^ 5 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 ↥(fc.normalizerRSigma model)) := inferInstance
  obtain ⟨hEq, hScard⟩ := fc.sylowThreeNormalizerRSigma_eq_map model ind hB2 S
  rw [hEq, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact hScard

include model in
theorem sylowThreeNormalizerRSigma_le :
    fc.sylowThreeNormalizerRSigma model ≤ fc.normalizerRSigma model := by
  rw [fc.sylowThreeNormalizerRSigma_def model, Subgroup.closure_le]
  rintro y ⟨hyN, -⟩
  exact hyN

include model in
/-- **`RΣ ≤ R₁`**: every element of `RΣ` is a `3`-element of `N_G(RΣ)` (`|RΣ| = 3⁴`). -/
theorem sup_le_sylowThreeNormalizerRSigma
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    (fc.invImageF model
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G)
      ≤ fc.sylowThreeNormalizerRSigma model := by
  have hRScard := fc.card_sup_invImageF_centralizer_W_eq model ind hB2
  intro x hx
  rw [fc.sylowThreeNormalizerRSigma_def model]
  refine Subgroup.subset_closure ⟨Subgroup.le_normalizer hx, ?_⟩
  have hdvd := Subgroup.orderOf_dvd_natCard _ hx
  rw [hRScard] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num)).mp hdvd
  exact ⟨j, hj⟩

include model in
/-- The set of `3`-elements of `N_G(RΣ)` is invariant under conjugation by
`N_G(RΣ)`. -/
theorem conj_image_threeElements_eq {g : G} (hg : g ∈ fc.normalizerRSigma model) :
    (fun y => g * y * g⁻¹) ''
        {y : G | y ∈ fc.normalizerRSigma model ∧ ∃ j : ℕ, orderOf y = 3 ^ j}
      = {y : G | y ∈ fc.normalizerRSigma model ∧ ∃ j : ℕ, orderOf y = 3 ^ j} := by
  have horder : ∀ a b : G, orderOf (a * b * a⁻¹) = orderOf b := fun a b =>
    orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective b
  ext z
  constructor
  · rintro ⟨y, ⟨hyN, j, hj⟩, rfl⟩
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hyN) (Subgroup.inv_mem _ hg),
      j, by rw [horder]; exact hj⟩
  · rintro ⟨hzN, j, hj⟩
    refine ⟨g⁻¹ * z * g, ⟨Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hzN) hg, j, ?_⟩, by group⟩
    have h1 : g⁻¹ * z * g = g⁻¹ * z * (g⁻¹)⁻¹ := by rw [inv_inv]
    rw [h1, horder]
    exact hj

include model in
/-- **`R₁ ⊴ N_G(RΣ)`** ((14), p. 113): `R₁` is generated by the `3`-elements of
`N_G(RΣ)`, a conjugation-invariant set. -/
theorem conj_mem_sylowThreeNormalizerRSigma {g : G}
    (hg : g ∈ fc.normalizerRSigma model) {x : G}
    (hx : x ∈ fc.sylowThreeNormalizerRSigma model) :
    g * x * g⁻¹ ∈ fc.sylowThreeNormalizerRSigma model := by
  have hmap : (fc.sylowThreeNormalizerRSigma model).map (MulAut.conj g).toMonoidHom
      = fc.sylowThreeNormalizerRSigma model := by
    rw [fc.sylowThreeNormalizerRSigma_def model, MonoidHom.map_closure]
    congr 1
    exact fc.conj_image_threeElements_eq model hg
  rw [← hmap]
  exact Subgroup.mem_map_of_mem _ hx

include model in
/-- `R₁` is a `3`-group (`|R₁| = 3⁵`). -/
theorem isPGroup_sylowThreeNormalizerRSigma
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    IsPGroup 3 ↥(fc.sylowThreeNormalizerRSigma model) :=
  IsPGroup.of_card (fc.card_sylowThreeNormalizerRSigma model ind hB2)

include model in
/-- **`C_K(P) = RΣ` for every `3`-subgroup `K ⊇ RΣ`** ((14), p. 113): `RΣ`
centralizes `P`, and `K ⊓ C_G(P)` is a `3`-group inside `C_G(P)`, whose order `3⁴·8`
has `3`-part `3⁴ = |RΣ|`. -/
theorem inf_centralizer_P_eq_of_isPGroup
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {K : Subgroup G}
    (hKp : IsPGroup 3 ↥K)
    (hRSK : (fc.invImageF model
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G) ≤ K) :
    K ⊓ Subgroup.centralizer (fc.P : Set G)
      = fc.invImageF model
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hRSC : (fc.invImageF model
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G)
      ≤ Subgroup.centralizer (fc.P : Set G) := by
    rw [← fc.centralizer_P_inf_centralizer_mul_t_eq_sup model ind hB2]
    exact inf_le_left
  have hle : (fc.invImageF model
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G)
      ≤ K ⊓ Subgroup.centralizer (fc.P : Set G) :=
    le_inf hRSK hRSC
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  -- the intersection is a `3`-group of order dividing the `3`-part of `|C_G(P)|`
  obtain ⟨i, hi⟩ := (IsPGroup.iff_card).mp (hKp.to_le inf_le_left)
  have hdvd : (3 : ℕ) ^ i ∣ 81 * 8 := by
    rw [← hi, ← fc.card_centralizer_P_eq model ind hB2]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime ((3 : ℕ) ^ i) 8 :=
    Nat.Coprime.pow_left i (by decide)
  have hdvd' : (3 : ℕ) ^ i ∣ 3 ^ 4 := by
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [show (3 : ℕ) ^ 4 * 8 = 81 * 8 by norm_num]
    exact hdvd
  rw [hi, fc.card_sup_invImageF_centralizer_W_eq model ind hB2]
  exact Nat.le_of_dvd (by norm_num) hdvd'

include model in
/-- **`C_{R₁}(P) = RΣ`** ((14), p. 113). -/
theorem inf_centralizer_P_sylowThree_eq
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    fc.sylowThreeNormalizerRSigma model ⊓ Subgroup.centralizer (fc.P : Set G)
      = fc.invImageF model
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) :=
  fc.inf_centralizer_P_eq_of_isPGroup model ind hB2
    (fc.isPGroup_sylowThreeNormalizerRSigma model ind hB2)
    (fc.sup_le_sylowThreeNormalizerRSigma model ind hB2)

include model in
/-- **`Z(R₁) = Z₁`** ((14), p. 113), the centre taken inside `G` as
`R₁ ⊓ C_G(R₁)`.

`Z₁ ≤ Z(R₁)` because `R₁` normalizes `Z₁ = ⁅RΣ, RΣ⁆` and consists of odd-order
elements, so it centralizes the order-`3` group `Z₁`.  Conversely `Z(R₁)` centralizes
`P ≤ R₁`, hence lies in `C_{R₁}(P) = RΣ`, and it centralizes `RΣ`, hence lies in
`Z(RΣ) = Z₁P`.  It cannot be all of `Z₁P`, for then `R₁` would centralize `Z₁P` and so
`R₁ ≤ C_G(Z₁P) = RΣ`, contradicting `3⁵ > 3⁴`.  As `|Z₁P| = 9` and `|Z₁| = 3`, this
leaves `Z(R₁) = Z₁`. -/
theorem inf_centralizer_sylowThree_eq_zpowers
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    fc.sylowThreeNormalizerRSigma model
        ⊓ Subgroup.centralizer
          ((fc.sylowThreeNormalizerRSigma model : Subgroup G) : Set G)
      = Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨-, hp3, hF9, -, -, -⟩ := fc.step_twelve model ind hB2
  have hm : Nat.card F = fc.p ^ 2 := by rw [hF9, hp3]; norm_num
  have hstord : orderOf (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = 3 := by
    rw [fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  have hR₁p := fc.isPGroup_sylowThreeNormalizerRSigma model ind hB2
  have hRSle := fc.sup_le_sylowThreeNormalizerRSigma model ind hB2
  have hZ₁RS : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ≤ (fc.invImageF model
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G) :=
    ((fc.zpowers_distinguishedInvolution_mul_t_le_sInvertedT model ind hB2 hm).trans
      (fc.sInvertedT_spec model ind hB2 hm).1).trans le_sup_left
  -- `R₁` centralizes `Z₁`: its elements have odd order and normalize `Z₁`
  have hcomm : ∀ g ∈ fc.sylowThreeNormalizerRSigma model,
      g * (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
        = (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t) * g := by
    intro g hg
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf).mp hR₁p ⟨g, hg⟩
    rw [Subgroup.orderOf_mk] at hj
    have hoddg : Odd (orderOf g) := by
      rw [hj]
      exact Odd.pow (Nat.odd_iff.mpr (by norm_num))
    refine commute_of_odd_orderOf_of_conj_mem_zpowers hoddg hstord ?_
    exact conj_mem_of_conj_smul_eq
      (fc.conj_smul_zpowers_eq model ind hB2
        (fc.sylowThreeNormalizerRSigma_le model hg)) (Subgroup.mem_zpowers _)
  have hZ₁le : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t)
      ≤ fc.sylowThreeNormalizerRSigma model ⊓ Subgroup.centralizer
        ((fc.sylowThreeNormalizerRSigma model : Subgroup G) : Set G) := by
    refine le_inf (hZ₁RS.trans hRSle) ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    exact fun h hh => hcomm h hh
  -- `Z(R₁) ≤ Z₁P`
  have hPR₁ : fc.P ≤ fc.sylowThreeNormalizerRSigma model :=
    (le_sup_left.trans' (fc.P_le_invImageF model)).trans hRSle
  have hupper : fc.sylowThreeNormalizerRSigma model ⊓ Subgroup.centralizer
      ((fc.sylowThreeNormalizerRSigma model : Subgroup G) : Set G)
      ≤ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) ⊔ fc.P := by
    intro x hx
    have hxP : x ∈ Subgroup.centralizer (fc.P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      exact fun y hy => Subgroup.mem_centralizer_iff.mp hx.2 y (hPR₁ hy)
    have hxRS : x ∈ (fc.invImageF model
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G) := by
      rw [← fc.inf_centralizer_P_sylowThree_eq model ind hB2]
      exact ⟨hx.1, hxP⟩
    rw [← fc.inf_centralizer_sup_eq_zpowers_sup_P model ind hB2]
    exact ⟨hxRS, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp hx.2 y (hRSle hy)⟩
  -- `Z(R₁) ≠ Z₁P`
  have hne : fc.sylowThreeNormalizerRSigma model ⊓ Subgroup.centralizer
      ((fc.sylowThreeNormalizerRSigma model : Subgroup G) : Set G)
      ≠ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) ⊔ fc.P := by
    intro hEq
    have hR₁le : fc.sylowThreeNormalizerRSigma model
        ≤ Subgroup.centralizer (fc.P : Set G)
          ⊓ Subgroup.centralizer ({fc.toHypothesis.distinguishedInvolution
            * fc.toHypothesis.t} : Set G) := by
      have hZP : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t) ⊔ fc.P
          ≤ Subgroup.centralizer
            ((fc.sylowThreeNormalizerRSigma model : Subgroup G) : Set G) := by
        rw [← hEq]; exact inf_le_right
      refine fun g hg => ⟨Subgroup.mem_centralizer_iff.mpr fun y hy =>
          (Subgroup.mem_centralizer_iff.mp (hZP (Subgroup.mem_sup_right hy))
            g hg).symm,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp
            (hZP (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))) g hg)⟩
    rw [fc.centralizer_P_inf_centralizer_mul_t_eq_sup model ind hB2] at hR₁le
    have hcard := Subgroup.card_dvd_of_le hR₁le
    rw [fc.card_sylowThreeNormalizerRSigma model ind hB2,
      fc.card_sup_invImageF_centralizer_W_eq model ind hB2] at hcard
    have := Nat.le_of_dvd (by norm_num) hcard
    norm_num at this
  -- squeeze
  have hZ₁card : Nat.card ↥(Subgroup.zpowers
      (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)) = 3 := by
    rw [Nat.card_zpowers, hstord]
  have hZPcard := fc.card_zpowers_sup_P_eq_nine model ind hB2
  have hdvd := Subgroup.card_dvd_of_le hupper
  rw [hZPcard] at hdvd
  have hdvd2 := Subgroup.card_dvd_of_le hZ₁le
  rw [hZ₁card] at hdvd2
  refine (Subgroup.eq_of_le_of_card_ge hZ₁le ?_).symm
  rw [hZ₁card]
  have hdvd9 : Nat.card ↥(fc.sylowThreeNormalizerRSigma model ⊓ Subgroup.centralizer
      ((fc.sylowThreeNormalizerRSigma model : Subgroup G) : Set G)) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
    exact hdvd
  obtain ⟨i, hi2, hie⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd9
  interval_cases i
  · rw [pow_zero] at hie; omega
  · rw [pow_one] at hie; omega
  · exfalso
    refine hne (Subgroup.eq_of_le_of_card_ge hupper ?_)
    rw [hZPcard, hie]
    norm_num

include model in
/-- `s ∉ R₁`: `R₁` is a `3`-group and `s` is an involution. -/
theorem distinguishedInvolution_notMem_sylowThree
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    fc.toHypothesis.distinguishedInvolution
      ∉ fc.sylowThreeNormalizerRSigma model := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  intro hmem
  have hord : orderOf fc.toHypothesis.distinguishedInvolution = 2 :=
    orderOf_eq_prime fc.toHypothesis.distinguishedInvolution_sq
      fc.toHypothesis.distinguishedInvolution_ne_one
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  rw [hord, fc.card_sylowThreeNormalizerRSigma model ind hB2] at hdvd
  norm_num at hdvd

include model in
/-- **`N_G(RΣ) = R₁ ⋊ ⟨s⟩`** ((14), p. 113): `R₁` is normal of order `3⁵`
(`conj_mem_sylowThreeNormalizerRSigma`) and `⟨s⟩` has order `2`, while
`|N_G(RΣ)| = 2·3⁵`; so they meet trivially and together fill up `N_G(RΣ)`. -/
theorem sylowThree_sup_zpowers_distinguishedInvolution
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    fc.sylowThreeNormalizerRSigma model
        ⊔ Subgroup.zpowers fc.toHypothesis.distinguishedInvolution
      = fc.normalizerRSigma model
    ∧ fc.sylowThreeNormalizerRSigma model
        ⊓ Subgroup.zpowers fc.toHypothesis.distinguishedInvolution = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hord : orderOf fc.toHypothesis.distinguishedInvolution = 2 :=
    orderOf_eq_prime fc.toHypothesis.distinguishedInvolution_sq
      fc.toHypothesis.distinguishedInvolution_ne_one
  have hscard : Nat.card ↥(Subgroup.zpowers
      fc.toHypothesis.distinguishedInvolution) = 2 := by
    rw [Nat.card_zpowers, hord]
  have hR₁card := fc.card_sylowThreeNormalizerRSigma model ind hB2
  have hNcard := fc.card_normalizerRSigma model ind hB2
  have hsN : Subgroup.zpowers fc.toHypothesis.distinguishedInvolution
      ≤ fc.normalizerRSigma model :=
    Subgroup.zpowers_le.mpr (fc.distinguishedInvolution_mem_normalizerRSigma model)
  have hR₁N := fc.sylowThreeNormalizerRSigma_le model
  refine ⟨?_, ?_⟩
  · refine Subgroup.eq_of_le_of_card_ge (sup_le hR₁N hsN) ?_
    have h3 : (3 : ℕ) ^ 5 ∣ Nat.card ↥(fc.sylowThreeNormalizerRSigma model
        ⊔ Subgroup.zpowers fc.toHypothesis.distinguishedInvolution) := by
      rw [← hR₁card]
      exact Subgroup.card_dvd_of_le le_sup_left
    have h2 : (2 : ℕ) ∣ Nat.card ↥(fc.sylowThreeNormalizerRSigma model
        ⊔ Subgroup.zpowers fc.toHypothesis.distinguishedInvolution) := by
      rw [← hscard]
      exact Subgroup.card_dvd_of_le le_sup_right
    have h6 : 2 * 3 ^ 5 ∣ Nat.card ↥(fc.sylowThreeNormalizerRSigma model
        ⊔ Subgroup.zpowers fc.toHypothesis.distinguishedInvolution) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h2 h3
    rw [hNcard]
    exact Nat.le_of_dvd Nat.card_pos h6
  · have hdvd3 : Nat.card ↥(fc.sylowThreeNormalizerRSigma model
        ⊓ Subgroup.zpowers fc.toHypothesis.distinguishedInvolution) ∣ 3 ^ 5 := by
      rw [← hR₁card]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hdvd2 : Nat.card ↥(fc.sylowThreeNormalizerRSigma model
        ⊓ Subgroup.zpowers fc.toHypothesis.distinguishedInvolution) ∣ 2 := by
      rw [← hscard]
      exact Subgroup.card_dvd_of_le inf_le_right
    refine Subgroup.card_eq_one.mp ?_
    exact Nat.eq_one_of_dvd_coprimes (by decide) hdvd2 hdvd3

include model in
/-- **`|R₂| = 3⁵` or `3⁶`** ((14), p. 113: `|R₂ : R₁| = 1` or `3`): by (10.2) the
`3`-part of `|G|` is `3⁴·|W|` with `|W| ∈ {3, 9}`. -/
theorem card_sylow_eq
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G) :
    Nat.card ↥(S : Subgroup G) = 3 ^ 5 ∨ Nat.card ↥(S : Subgroup G) = 3 ^ 6 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨-, -, -, -, hW, hGp⟩ := fc.step_twelve model ind hB2
  have hXcard : Nat.card ↥(S : Subgroup G) = 3 ^ 4 * Nat.card ↥fc.toHypothesis.W := by
    rw [Sylow.card_eq_multiplicity]
    exact hGp
  rcases hW with h | h
  · left; rw [hXcard, h]; norm_num
  · right; rw [hXcard, h]; norm_num

include model in
/-- **`Z(R₂) = Z₁` for a Sylow `3`-subgroup `R₂ ⊇ R₁`** ((14), p. 113).

`Z(R₂)` centralizes `P ≤ R₂`, hence lies in `R₂ ⊓ C_G(P) = RΣ ≤ R₁`; centralizing
`R₁ ≤ R₂` as well, it lies in `Z(R₁) = Z₁`.  It is nontrivial because `R₂` is a
nontrivial `3`-group, and `|Z₁| = 3` is prime. -/
theorem inf_centralizer_sylow_eq_zpowers
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G)
    (hR₁S : fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G)) :
    (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G)) : Set G)
      = Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨-, hp3, -, -, -, -⟩ := fc.step_twelve model ind hB2
  have hstord : orderOf (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = 3 := by
    rw [fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  have hZ₁card : Nat.card ↥(Subgroup.zpowers
      (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)) = 3 := by
    rw [Nat.card_zpowers, hstord]
  have hRSle := fc.sup_le_sylowThreeNormalizerRSigma model ind hB2
  have hPR₁ : fc.P ≤ fc.sylowThreeNormalizerRSigma model :=
    (le_sup_left.trans' (fc.P_le_invImageF model)).trans hRSle
  have hSCP := fc.inf_centralizer_P_eq_of_isPGroup model ind hB2 S.isPGroup'
    (hRSle.trans hR₁S)
  -- `Z(R₂) ≤ Z(R₁) = Z₁`
  have hle : (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G)) : Set G)
      ≤ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) := by
    rw [← fc.inf_centralizer_sylowThree_eq_zpowers model ind hB2]
    intro x hx
    have hxP : x ∈ Subgroup.centralizer (fc.P : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp hx.2 y (hR₁S (hPR₁ hy))
    have hxR₁ : x ∈ fc.sylowThreeNormalizerRSigma model := by
      have : x ∈ (fc.invImageF model
          ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G) := by
        rw [← hSCP]; exact ⟨hx.1, hxP⟩
      exact hRSle this
    exact ⟨hxR₁, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp hx.2 y (hR₁S hy)⟩
  -- `Z(R₂) ≠ 1`
  have hSbig : 3 ^ 5 ≤ Nat.card ↥(S : Subgroup G) := by
    rw [← fc.card_sylowThreeNormalizerRSigma model ind hB2]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hR₁S)
  haveI : Nontrivial ↥(S : Subgroup G) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have h243 : (3 : ℕ) ^ 5 = 243 := by norm_num
    omega
  have hcentre : Nat.card ↥(Subgroup.center ↥(S : Subgroup G))
      = Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer
        (((S : Subgroup G)) : Set G)) := by
    rw [center_eq_inf_centralizer_subgroupOf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  haveI := S.isPGroup'.center_nontrivial
  have hne : Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer
      (((S : Subgroup G)) : Set G)) ≠ 1 := by
    rw [← hcentre]
    intro h
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' h
  -- conclude
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hZ₁card] at hdvd
  rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h3
  · exact absurd h1 hne
  · rw [hZ₁card, h3]

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
