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

include model in
/-- **`Z₁^x ≤ LV`** ((17), p. 114, first paragraph), for `x` with `(Z₁PΣ)^x ≤ R₂`.

Otherwise `R₂ = LV·Z₁^x`, and `A = (Z₁PΣ)^x ⊓ LV` has order `9` and lies in
`Ω₁(LV) = Z₁PΣ`.  Its nonidentity elements are not strongly real: the strongly real
elements of `(Z₁PΣ)^x` are those of `Z₁^x`, which meets `LV` trivially in this case.
Hence `A ⊓ Z₁ = 1` and `Z₁A = Z₁PΣ`, so `Z₁^x` — which centralizes the abelian
`(Z₁PΣ)^x ⊇ A` and the central `Z₁ = Z(R₂)` — centralizes `Z₁PΣ`.  Then `Z₁Σ = Z(LV)`
is centralized by `LV` and by `Z₁^x`, i.e. `Z₁Σ ≤ Z(R₂) = Z₁`, contradicting
`|Z₁Σ| = 9`. -/
theorem map_conj_zpowers_le_sup_nonsplitTorus_V
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G)
    (hR₁S : fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G)) {x : G}
    (hx : (((Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
            * fc.toHypothesis.t)
          ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P)
            : Subgroup G).map (MulAut.conj x).toMonoidHom ≤ (S : Subgroup G)) :
    (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t)).map (MulAut.conj x).toMonoidHom
      ≤ fc.nonsplitTorus ⊔ fc.toHypothesis.V := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨-, hp3, -, -, -, -⟩ := fc.step_twelve model ind hB2
  have hstord : orderOf (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = 3 := by
    rw [fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  have hZ₁card : Nat.card ↥(Subgroup.zpowers
      (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)) = 3 := by
    rw [Nat.card_zpowers, hstord]
  have hconjInj : Function.Injective (MulAut.conj x).toMonoidHom := fun a b h => by
    simpa using congrArg (fun y => (MulAut.conj x).symm y) h
  set B : Subgroup G := (((Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t)
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P)
        : Subgroup G).map (MulAut.conj x).toMonoidHom with hB_def
  set Zx : Subgroup G := (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t)).map (MulAut.conj x).toMonoidHom with hZx_def
  have hZxB : Zx ≤ B := Subgroup.map_mono (le_sup_left.trans le_sup_left)
  have hBcard : Nat.card ↥B = 27 := by
    rw [hB_def, Subgroup.card_map_of_injective hconjInj]
    exact fc.card_zpowers_sup_sigma_sup_P model ind hB2
  have hZxcard : Nat.card ↥Zx = 3 := by
    rw [hZx_def, Subgroup.card_map_of_injective hconjInj, hZ₁card]
  by_contra hcon
  have hBnotLV : ¬ B ≤ fc.nonsplitTorus ⊔ fc.toHypothesis.V :=
    fun h => hcon (hZxB.trans h)
  -- `A = B ⊓ LV` has order `9`
  have hBS : B ≤ (S : Subgroup G) := hx
  have hLVS := fc.sup_nonsplitTorus_V_le_sylow model ind hB2 S hR₁S
  have hidx := fc.index_subgroupOf_sup_nonsplitTorus_V_eq_three model ind hB2 S hR₁S
  have hminFac : (Nat.card ↥(S : Subgroup G)).minFac = 3 := by
    rcases fc.card_sylow_eq model ind hB2 S with h | h <;> rw [h] <;> norm_num
  haveI hLVnorm : ((fc.nonsplitTorus ⊔ fc.toHypothesis.V).subgroupOf
      (S : Subgroup G)).Normal :=
    Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hminFac])
  have hrel : (fc.nonsplitTorus ⊔ fc.toHypothesis.V).relIndex B ∣ 3 := by
    have h := Subgroup.relIndex_dvd_index_of_normal
      (H := (fc.nonsplitTorus ⊔ fc.toHypothesis.V).subgroupOf (S : Subgroup G))
      (K := B.subgroupOf (S : Subgroup G))
    rw [Subgroup.relIndex_subgroupOf hBS, hidx] at h
    exact h
  have hmul : Nat.card ↥((fc.nonsplitTorus ⊔ fc.toHypothesis.V) ⊓ B)
      * (fc.nonsplitTorus ⊔ fc.toHypothesis.V).relIndex B = Nat.card ↥B := by
    have hcard1 : Nat.card ↥(((fc.nonsplitTorus ⊔ fc.toHypothesis.V) ⊓ B).subgroupOf B)
        = Nat.card ↥((fc.nonsplitTorus ⊔ fc.toHypothesis.V) ⊓ B) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have h := (((fc.nonsplitTorus ⊔ fc.toHypothesis.V) ⊓ B).subgroupOf B).card_mul_index
    rwa [hcard1, Subgroup.inf_subgroupOf_right] at h
  have hAcard : Nat.card ↥((fc.nonsplitTorus ⊔ fc.toHypothesis.V) ⊓ B) = 9 := by
    rw [hBcard] at hmul
    rcases (Nat.dvd_prime (by norm_num)).mp hrel with h1 | h3
    · exfalso
      rw [h1, mul_one] at hmul
      exact hBnotLV (le_trans (le_of_eq (Subgroup.eq_of_le_of_card_ge inf_le_right
        (by rw [hmul, hBcard])).symm) inf_le_left)
    · rw [h3] at hmul; omega
  -- `A ≤ Z₁ΣP`
  have hAZSP : (fc.nonsplitTorus ⊔ fc.toHypothesis.V) ⊓ B
      ≤ (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P := by
    intro y hy
    refine (fc.pow_three_eq_one_iff_mem_zpowers_sup_sigma_sup_P model ind hB2
      hy.1).mp ?_
    obtain ⟨z, hz, hzy⟩ := hy.2
    have hz3 : z ^ 3 = 1 :=
      (fc.pow_three_eq_one_iff_mem_zpowers_sup_sigma_sup_P model ind hB2
        (by
          refine sup_le (sup_le (fc.zpowers_le_nonsplitTorus.trans le_sup_left)
            ((inf_le_left.trans fc.toHypothesis.W_le_V).trans le_sup_right))
            (fc.P_le_V.trans le_sup_right) hz)).mpr hz
    have hyz : y = x * z * x⁻¹ := hzy.symm
    rw [hyz, conj_pow, hz3]
    group
  -- `A ⊓ Z₁ = 1`
  have hAZ₁ : ((fc.nonsplitTorus ⊔ fc.toHypothesis.V) ⊓ B)
      ⊓ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    by_contra hy1
    -- `y ∈ Z₁^#` is strongly real and lies in `B`, hence in `Z₁^x`
    refine hcon ?_
    have hyB : y ∈ B := hy.1.2
    have hysr : IsStronglyReal y :=
      fc.forall_isStronglyReal_mem_zpowers_st model ind hB2 hy.2
    have hyZx : y ∈ Zx := by
      obtain ⟨w, hwB, hwy⟩ : ∃ w ∈ ((Subgroup.zpowers
          (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
          ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P),
          x * w * x⁻¹ = y := by
        obtain ⟨w, hw, hwy⟩ := hyB
        exact ⟨w, hw, hwy⟩
      have hwsr : IsStronglyReal w := by
        have h := isStronglyReal_conj hysr x⁻¹
        rwa [show x⁻¹ * y * x⁻¹⁻¹ = w by rw [← hwy]; group] at h
      have hwZ := fc.mem_zpowers_of_isStronglyReal_of_mem model ind hB2 hwB hwsr
      exact ⟨w, hwZ, hwy⟩
    -- so `Z₁^x = ⟨y⟩ = Z₁ ≤ LV`
    have hyord : orderOf y = 3 := by
      have h := Subgroup.orderOf_dvd_natCard _ hy.2
      rw [hZ₁card] at h
      rcases (Nat.dvd_prime (by norm_num)).mp h with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hy1
      · exact h3
    have h1 : Subgroup.zpowers y = Zx :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyZx)
        (by rw [hZxcard, Nat.card_zpowers, hyord])
    rw [← h1]
    exact Subgroup.zpowers_le.mpr
      (Subgroup.mem_sup_left (fc.zpowers_le_nonsplitTorus hy.2))
  -- `Z₁A = Z₁ΣP`
  have hprod : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t)
      ⊔ ((fc.nonsplitTorus ⊔ fc.toHypothesis.V) ⊓ B)
      = (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P := by
    refine Subgroup.eq_of_le_of_card_ge
      (sup_le (le_sup_left.trans le_sup_left) hAZSP) ?_
    rw [card_sup_eq_mul_of_commute
        (fun a ha b hb => fc.mul_comm_of_mem_zpowers_sup_sigma_sup_P model ind hB2
          (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha)) (hAZSP hb))
        (by rw [← hAZ₁]; exact inf_comm _ _),
      hZ₁card, hAcard, fc.card_zpowers_sup_sigma_sup_P model ind hB2]
  -- `B` is abelian, being a conjugate of `Z₁ΣP`
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro a ⟨c, hc, rfl⟩ b ⟨d, hd, rfl⟩
    have hcd := fc.mul_comm_of_mem_zpowers_sup_sigma_sup_P model ind hB2 hc hd
    change (x * c * x⁻¹) * (x * d * x⁻¹) = (x * d * x⁻¹) * (x * c * x⁻¹)
    calc (x * c * x⁻¹) * (x * d * x⁻¹) = x * (c * d) * x⁻¹ := by group
      _ = x * (d * c) * x⁻¹ := by rw [hcd]
      _ = (x * d * x⁻¹) * (x * c * x⁻¹) := by group
  -- `Z₁ = Z(R₂)` is central in `R₂`
  have hZ₁cen : ∀ z ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t), ∀ u ∈ (S : Subgroup G), z * u = u * z := by
    intro z hz u hu
    have hmem : z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer
        (((S : Subgroup G)) : Set G) := by
      rw [fc.inf_centralizer_sylow_eq_zpowers model ind hB2 S hR₁S]
      exact hz
    exact (Subgroup.mem_centralizer_iff.mp hmem.2 u hu).symm
  -- `Z₁^x` centralizes `Z₁ΣP = Z₁A`
  have hZxcen : ∀ u ∈ Zx, ∀ v ∈ ((Subgroup.zpowers
        (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P),
      u * v = v * u := by
    intro u hu v hv
    rw [← hprod] at hv
    have hcoe := coe_sup_eq_mul_of_commute
      (fun _ (ha : _ ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)) _
        (hb : _ ∈ (fc.nonsplitTorus ⊔ fc.toHypothesis.V) ⊓ B) =>
        fc.mul_comm_of_mem_zpowers_sup_sigma_sup_P model ind hB2
          (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha)) (hAZSP hb))
    have hv' : v ∈ ((Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) : Subgroup G) : Set G)
        * (((fc.nonsplitTorus ⊔ fc.toHypothesis.V) ⊓ B : Subgroup G) : Set G) := by
      rw [← hcoe]; exact hv
    obtain ⟨z, hz, a, ha, hza⟩ := hv'
    have hzav : z * a = v := hza
    have h1 : u * z = z * u := (hZ₁cen z hz u (hBS (hZxB hu))).symm
    have h2 : u * a = a * u := hBcomm u (hZxB hu) a ha.2
    calc u * v = u * (z * a) := by rw [hzav]
      _ = z * (u * a) := by rw [← mul_assoc, h1, mul_assoc]
      _ = z * (a * u) := by rw [h2]
      _ = v * u := by rw [← mul_assoc, hzav]
  -- `R₂ = LV·Z₁^x`
  have hLVcardS : Nat.card ↥(fc.nonsplitTorus ⊔ fc.toHypothesis.V) * 3
      = Nat.card ↥(S : Subgroup G) := by
    have h := ((fc.nonsplitTorus ⊔ fc.toHypothesis.V).subgroupOf
      (S : Subgroup G)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLVS).toEquiv, hidx] at h
    exact h
  have hR₂eq : (fc.nonsplitTorus ⊔ fc.toHypothesis.V) ⊔ Zx = (S : Subgroup G) := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hLVS (hZxB.trans hBS)) ?_
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le
      (le_sup_left : fc.nonsplitTorus ⊔ fc.toHypothesis.V ≤ _ ⊔ Zx)
    have hdvd : Nat.card ↥((fc.nonsplitTorus ⊔ fc.toHypothesis.V) ⊔ Zx)
        ∣ Nat.card ↥(S : Subgroup G) :=
      Subgroup.card_dvd_of_le (sup_le hLVS (hZxB.trans hBS))
    have hpos : 0 < Nat.card ↥(fc.nonsplitTorus ⊔ fc.toHypothesis.V) := Nat.card_pos
    have hm3 : m ∣ 3 := by
      rw [hm, ← hLVcardS] at hdvd
      exact (Nat.mul_dvd_mul_iff_left hpos).mp hdvd
    rcases (Nat.dvd_prime (by norm_num)).mp hm3 with h1 | h3
    · exfalso
      refine hcon (le_trans ?_ (le_refl _))
      have heq : (fc.nonsplitTorus ⊔ fc.toHypothesis.V) ⊔ Zx
          = fc.nonsplitTorus ⊔ fc.toHypothesis.V :=
        (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hm, h1, mul_one])).symm
      rw [← heq]
      exact le_sup_right
    · rw [hm, h3, hLVcardS]
  -- `Z₁Σ ≤ Z(R₂) = Z₁`, contradicting `|Z₁Σ| = 9`
  have hm : Nat.card F = fc.p ^ 2 := by
    obtain ⟨-, -, hF9, -, -, -⟩ := fc.step_twelve model ind hB2
    rw [hF9, hp3]; norm_num
  have hZ₁R : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ≤ fc.invImageF model :=
    (fc.zpowers_distinguishedInvolution_mul_t_le_sInvertedT model ind hB2 hm).trans
      (fc.sInvertedT_spec model ind hB2 hm).1
  have hZSP_S : ((Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P)
      ≤ (S : Subgroup G) := by
    refine le_trans (le_trans ?_ (fc.sup_le_sylowThreeNormalizerRSigma model ind hB2))
      hR₁S
    exact sup_le (sup_le (hZ₁R.trans le_sup_left) le_sup_right)
      ((fc.P_le_invImageF model).trans le_sup_left)
  have hZSle' : (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t)
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)))
      ≤ (S : Subgroup G)
        ⊓ Subgroup.centralizer (((S : Subgroup G)) : Set G) := by
    intro y hy
    refine ⟨hZSP_S (Subgroup.mem_sup_left hy), ?_⟩
    rw [← hR₂eq, centralizer_sup]
    refine ⟨?_, ?_⟩
    · have heq := fc.inf_centralizer_sup_nonsplitTorus_V_eq model ind hB2
      rw [← heq] at hy
      exact hy.2
    · refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
      exact hZxcen u hu y (Subgroup.mem_sup_left hy)
  have hZSle : (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t)
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)))
      ≤ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) :=
    le_trans hZSle'
      (le_of_eq (fc.inf_centralizer_sylow_eq_zpowers model ind hB2 S hR₁S))
  have hcard9 := fc.card_zpowers_sup_sigma model ind hB2
  have hdvd := Subgroup.card_dvd_of_le hZSle
  rw [hcard9, hZ₁card] at hdvd
  exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)

include model in
/-- **`Z₁PΣ` is weakly closed in `R₂`** ((17), p. 114): every `G`-conjugate of `Z₁PΣ`
that is contained in the Sylow `3`-subgroup `R₂` equals `Z₁PΣ`.

This is the hypothesis of the Hall–Wielandt theorem, which then yields
`G/O³(G) ≅ N_G(Z₁PΣ)/O³(N_G(Z₁PΣ)) = R₂⟨s⟩/O³(R₂⟨s⟩)` (`Z₁PΣ` is abelian and
`p = 3 > 2`). -/
theorem map_conj_eq_of_le_sylow
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G)
    (hR₁S : fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G)) {x : G}
    (hx : (((Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
            * fc.toHypothesis.t)
          ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P)
            : Subgroup G).map (MulAut.conj x).toMonoidHom ≤ (S : Subgroup G)) :
    (((Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P)
          : Subgroup G).map (MulAut.conj x).toMonoidHom
      = (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P :=
  fc.map_conj_eq_of_map_conj_zpowers_le model ind hB2 S hR₁S
    (fc.map_conj_zpowers_le_sup_nonsplitTorus_V model ind hB2 S hR₁S hx)

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
