/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepSixteen

/-!
# Peterfalvi Part II, Ch. II, step (17): the conclusion

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (17), p. 114.

The final contradiction runs as follows.  If `x ∈ G` is such that `(Z₁PΣ)^x ⊆ R₂`
then `Z₁^x ⊆ LV` (otherwise `R₂ = LV ⋊ Z₁^x` and one finds `Z₁Σ ⊆ Z(R₂)`, contrary
to (14)), and then `Z₁^x ⊆ Ω₁(LV) = Z₁PΣ`, so `Z₁^x = Z₁` by the uniqueness of the
strongly real line (16) and `x ∈ N_G(Z₁) = N_G(Z₁PΣ)`.  Thus `Z₁PΣ` is an abelian
subgroup weakly closed in `R₂`, and the Hall–Wielandt theorem gives
`G/O³(G) ≅ R₂⟨s⟩/O³(R₂⟨s⟩)`; the structure of `R̄₁ = R₁/Z₁` then produces a quotient
of order `3`, contradicting hypothesis (B2).

This file develops the weak-closure half.  (The Hall–Wielandt input itself is the one
piece of genuinely new shared infrastructure; see issue 2053.)
-/

set_option autoImplicit false

open scoped Pointwise commutatorElement

namespace OddOrder.Peterfalvi.Appendices.Suzuki

section GenericStronglyReal

variable {G' : Type*} [Group G']

/-- The inverse of a strongly real element is strongly real. -/
theorem isStronglyReal_inv {x : G'} (hx : IsStronglyReal x) : IsStronglyReal x⁻¹ := by
  obtain ⟨u, ⟨hu2, hu1⟩, v, ⟨hv2, hv1⟩, rfl⟩ := hx
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hu2)
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hv2)
  exact ⟨v, ⟨hv2, hv1⟩, u, ⟨hu2, hu1⟩, by rw [mul_inv_rev, huinv, hvinv]⟩

end GenericStronglyReal

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)
  {F : Type uG} [NearFields.NearField F]
  (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    NearFields.AffineNearFieldModel fc.rankOneQuotient F)

include model in
/-- **The strongly real elements of `Z₁PΣ` are exactly those of `Z₁`** ((16), p. 114):
a strongly real `y ∈ Z₁PΣ` generates a subgroup of order `3` all of whose elements are
strongly real (the inverse of a strongly real element is strongly real), so that
subgroup is `Z₁`. -/
theorem mem_zpowers_of_isStronglyReal_of_mem
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {y : G}
    (hy : y ∈ (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P)
    (hsr : IsStronglyReal y) :
    y ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  rcases eq_or_ne y 1 with rfl | hy1
  · exact Subgroup.one_mem _
  -- `y` has order `3`
  have hZSP_LV : ((Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P)
      ≤ fc.nonsplitTorus ⊔ fc.toHypothesis.V :=
    sup_le (sup_le (fc.zpowers_le_nonsplitTorus.trans le_sup_left)
      ((inf_le_left.trans fc.toHypothesis.W_le_V).trans le_sup_right))
      (fc.P_le_V.trans le_sup_right)
  have hy3 : y ^ 3 = 1 :=
    (fc.pow_three_eq_one_iff_mem_zpowers_sup_sigma_sup_P model ind hB2
      (hZSP_LV hy)).mpr hy
  have hyord : orderOf y = 3 := by
    have h := orderOf_dvd_of_pow_eq_one hy3
    rcases (Nat.dvd_prime (by norm_num)).mp h with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hy1
    · exact h3
  have hXeq := fc.eq_zpowers_of_card_three_of_forall_isStronglyReal model ind hB2
    (X := Subgroup.zpowers y) (Subgroup.zpowers_le.mpr hy)
    (by rw [Nat.card_zpowers, hyord])
    (by
      intro z hz hz1
      rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three hyord hz
        with h | h | h
      · exact absurd h hz1
      · rw [h]; exact hsr
      · rw [h]; exact isStronglyReal_inv hsr)
  rw [← hXeq]
  exact Subgroup.mem_zpowers _

include model in
/-- **`Z₁PΣ` is weakly closed in `R₂`, once `Z₁^x ≤ LV`** ((17), p. 114): then
`Z₁^x ≤ Ω₁(LV) = Z₁PΣ` consists of strongly real elements, so `Z₁^x = Z₁` by (16) and
`x ∈ N_G(Z₁) = N_G(Z₁PΣ)`. -/
theorem map_conj_eq_of_map_conj_zpowers_le
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G)
    (hR₁S : fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G)) {x : G}
    (hxLV : (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)).map (MulAut.conj x).toMonoidHom
      ≤ fc.nonsplitTorus ⊔ fc.toHypothesis.V) :
    (((Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P)
          : Subgroup G).map (MulAut.conj x).toMonoidHom
      = (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨-, hp3, -, -, -, -⟩ := fc.step_twelve model ind hB2
  have hstord : orderOf (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = 3 := by
    rw [fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  -- `Z₁^x` lies in `Ω₁(LV) = Z₁PΣ`
  have hle : (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t)).map (MulAut.conj x).toMonoidHom
      ≤ (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P := by
    intro y hy
    refine (fc.pow_three_eq_one_iff_mem_zpowers_sup_sigma_sup_P model ind hB2
      (hxLV hy)).mp ?_
    obtain ⟨z, hz, rfl⟩ := hy
    have hz3 : z ^ 3 = 1 := by
      have h := Subgroup.orderOf_dvd_natCard _ hz
      rw [Nat.card_zpowers, hstord] at h
      exact orderOf_dvd_iff_pow_eq_one.mp h
    change (x * z * x⁻¹) ^ 3 = 1
    rw [conj_pow, hz3]
    group
  -- `Z₁^x = Z₁` by the uniqueness of the strongly real line
  have hZeq : (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t)).map (MulAut.conj x).toMonoidHom
      = Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) := by
    refine fc.eq_zpowers_of_card_three_of_forall_isStronglyReal model ind hB2 hle ?_ ?_
    · rw [Subgroup.card_map_of_injective, Nat.card_zpowers, hstord]
      exact fun a b h => by
        simpa using congrArg (fun y => (MulAut.conj x).symm y) h
    · rintro y ⟨z, hz, rfl⟩ -
      exact isStronglyReal_conj
        (fc.forall_isStronglyReal_mem_zpowers_st model ind hB2 hz) x
  -- hence `x` normalizes `Z₁`, so also `Z₁PΣ`
  have hxN : x ∈ Subgroup.normalizer ((Subgroup.zpowers
      (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t) : Subgroup G)
        : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hZeq
  rw [fc.normalizer_zpowers_eq_normalizer_zpowers_sup_sigma_sup_P model ind hB2
    S hR₁S] at hxN
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
