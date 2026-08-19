/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepElevenComplement

/-!
# Peterfalvi Part II, Ch. II, step (11): `T ⋊ C_Q(P) ≅ F ⋊ F^*`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (11), p. 111 — the third clause.

Step (11) reads

> Let `R` be the inverse image of `F` in `G`.  Then `R = T ⋊ P`, where `T` is a
> subgroup normalized by `C_Q(P)C_W(P)`, and **`T ⋊ C_Q(P) ≅ F ⋊ F^*`**.
> Furthermore, `C_Q(P)` acts regularly on `𝒜 − {P}` …

`StepEleven`/`StepElevenComplement` prove the decomposition, the normalization and
the regular action.  This file supplies the remaining clause, in the form that makes
it a genuine assertion rather than a slogan:

* `fieldCoord` — the coordinate map `T → (F, +)`, namely "read off the translation
  that `x` induces on the faithful quotient `C_G(P)/N`";
* `sInvertedTEquivField` — it is a group isomorphism `T ≃* (F, +)`
  (injective because `T ∩ N = T ∩ P = 1`, surjective because `|T| = |F|`);
* `fieldCoord_conj` — it is `C_Q(P)`-equivariant: conjugation by `q` on `T`
  corresponds to right multiplication by `qEquiv q⁻¹` on `F`.

Together the last two say exactly that the conjugation action of `C_Q(P)` on `T` is
the multiplication action of `F^*` on `F` — which is the content of
`T ⋊ C_Q(P) ≅ F ⋊ F^*`.
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

/-- `T ≤ C_G(P)`: `T ≤ R` (step (11)) and `R ≤ C_G(P)`. -/
theorem sInvertedT_le_centralizer
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    fc.sInvertedT model ≤ Subgroup.centralizer (fc.P : Set G) :=
  (fc.sInvertedT_spec model ind hB2 hm).1.trans (fc.invImageF_le_centralizer model)

/-- For `x ∈ T` the image of `x` in the faithful quotient `C_G(P)/N` is a translation. -/
theorem mk_mem_range_emb_of_mem_sInvertedT
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m)
    (x : ↥(fc.sInvertedT model)) :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    QuotientGroup.mk'
      ((fc.toHypothesis.H.subgroupOf
        (Subgroup.centralizer (fc.P : Set G))).normalCore)
      ⟨(x : G), fc.sInvertedT_le_centralizer model ind hB2 hm x.2⟩ ∈
      MonoidHom.range model.emb :=
  (fc.mem_invImageF_iff model (fc.sInvertedT_le_centralizer model ind hB2 hm x.2)).mp
    ((fc.sInvertedT_spec model ind hB2 hm).1 x.2)

/-- **Step (11), the coordinate map** — `T → (F, +)`: send `x ∈ T` to the unique
`a ∈ F` whose translation is the image of `x` in `C_G(P)/N`. -/
noncomputable def fieldCoord
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    ↥(fc.sInvertedT model) →* Multiplicative F :=
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  (MonoidHom.ofInjective model.emb_injective).symm.toMonoidHom.comp
    (MonoidHom.codRestrict
      ((QuotientGroup.mk'
        ((fc.toHypothesis.H.subgroupOf
          (Subgroup.centralizer (fc.P : Set G))).normalCore)).comp
        (Subgroup.inclusion (fc.sInvertedT_le_centralizer model ind hB2 hm)))
      (MonoidHom.range model.emb)
      (fc.mk_mem_range_emb_of_mem_sInvertedT model ind hB2 hm))

/-- Defining property of `fieldCoord`: `emb (fieldCoord x)` is the class of `x`. -/
theorem emb_fieldCoord
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m)
    (x : ↥(fc.sInvertedT model)) :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    model.emb (fc.fieldCoord model ind hB2 hm x) =
      QuotientGroup.mk'
        ((fc.toHypothesis.H.subgroupOf
          (Subgroup.centralizer (fc.P : Set G))).normalCore)
        ⟨(x : G), fc.sInvertedT_le_centralizer model ind hB2 hm x.2⟩ := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  exact congrArg Subtype.val
    ((MonoidHom.ofInjective model.emb_injective).apply_symm_apply
      ⟨_, fc.mk_mem_range_emb_of_mem_sInvertedT model ind hB2 hm x⟩)

/-- **Step (11)**: the coordinate map is injective.  `fieldCoord x = 1` says the class of
`x` in `C_G(P)/N` is trivial, i.e. `x ∈ N = P` (step (7)); but `T ∩ P = 1`. -/
theorem fieldCoord_injective
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    Function.Injective (fc.fieldCoord model ind hB2 hm) := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N' : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hN'def
  have hNP : fc.kernelN = fc.P :=
    (fc.N_eq_P_and_sigma_mulEquiv_centralizer_W ind).1
  obtain ⟨-, -, -, hTinf⟩ := fc.sInvertedT_spec model ind hB2 hm
  rw [injective_iff_map_eq_one]
  intro x hx
  -- the class of `x` is trivial, so `x ∈ N = P`
  have hclass : QuotientGroup.mk' N'
      ⟨(x : G), fc.sInvertedT_le_centralizer model ind hB2 hm x.2⟩ = 1 := by
    have h := fc.emb_fieldCoord model ind hB2 hm x
    rw [hx, map_one] at h
    exact h.symm
  have hxN : (x : G) ∈ fc.kernelN :=
    ⟨⟨(x : G), fc.sInvertedT_le_centralizer model ind hB2 hm x.2⟩,
      (QuotientGroup.eq_one_iff _).mp hclass, rfl⟩
  have hxP : (x : G) ∈ fc.P := by rwa [hNP] at hxN
  have : (x : G) ∈ fc.sInvertedT model ⊓ fc.P := ⟨x.2, hxP⟩
  rw [hTinf, Subgroup.mem_bot] at this
  exact Subtype.ext this

/-- **Step (11), third clause (group part)** — `T ≅ (F, +)`.

Injective by `fieldCoord_injective`, surjective because `|T| = |F|`
(`card_sInvertedT`). -/
noncomputable def sInvertedTEquivField
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    ↥(fc.sInvertedT model) ≃* Multiplicative F := by
  classical
  refine MulEquiv.ofBijective (fc.fieldCoord model ind hB2 hm)
    ⟨fc.fieldCoord_injective model ind hB2 hm, ?_⟩
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hm]; exact pow_ne_zero _ fc.p_prime.pos.ne')
  have hcard : Nat.card ↥(fc.sInvertedT model) = Nat.card (Multiplicative F) := by
    rw [fc.card_sInvertedT model ind hB2 hm]
    rfl
  exact ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨fc.fieldCoord_injective model ind hB2 hm, hcard⟩).2

@[simp] theorem sInvertedTEquivField_apply
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) (x : ↥(fc.sInvertedT model)) :
    fc.sInvertedTEquivField model ind hB2 hm x = fc.fieldCoord model ind hB2 hm x :=
  rfl

/-- The class of an element of `C_Q(P)` lands in the quotient's `Q`. -/
theorem mk_mem_rankOneQuotient_Q {a : G} (haQ : a ∈ fc.toHypothesis.Q)
    (haL : a ∈ Subgroup.centralizer (fc.P : Set G)) :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    QuotientGroup.mk'
      ((fc.toHypothesis.H.subgroupOf
        (Subgroup.centralizer (fc.P : Set G))).normalCore) ⟨a, haL⟩ ∈
      fc.rankOneQuotient.Q :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr haQ)

/-- **Step (11), third clause (equivariance)** — the coordinate map intertwines the
conjugation action of `C_Q(P)` on `T` with the right multiplication action of `F^*`
on `F`.

Together with `sInvertedTEquivField` this is the book's `T ⋊ C_Q(P) ≅ F ⋊ F^*`: the
group `T` *is* `(F, +)` and the group `C_Q(P)` *is* `F^*` (`model.qEquiv`) acting in
its natural manner.  (The inverse on `qEquiv` is the one forced by the right-near-field
convention, exactly as in `model.qEquiv_conj`.) -/
theorem fieldCoord_conj
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) {a : G} (haQ : a ∈ fc.toHypothesis.Q)
    (haL : a ∈ Subgroup.centralizer (fc.P : Set G))
    (x : ↥(fc.sInvertedT model)) :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    fc.fieldCoord model ind hB2 hm
        ⟨a * (x : G) * a⁻¹,
          fc.conj_mem_sInvertedT_of_mem_Q model ind hB2 hm haQ haL x.2⟩ =
      Multiplicative.ofAdd
        (Multiplicative.toAdd (fc.fieldCoord model ind hB2 hm x) *
          ((model.qEquiv
              ⟨_, fc.mk_mem_rankOneQuotient_Q haQ haL⟩⁻¹ : Fˣ) : F)) := by
  let := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N' : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hN'def
  set π := QuotientGroup.mk' N' with hπ
  set q : ↥fc.rankOneQuotient.Q :=
    ⟨π ⟨a, haL⟩, fc.mk_mem_rankOneQuotient_Q haQ haL⟩ with hq
  -- `emb` is injective, so it suffices to compare images of the two sides.
  apply model.emb_injective
  rw [fc.emb_fieldCoord model ind hB2 hm]
  -- the class of `a x a⁻¹` is the conjugate of the class of `x` by `q`
  have hmemL : a * (x : G) * a⁻¹ ∈ L :=
    fc.sInvertedT_le_centralizer model ind hB2 hm
      (fc.conj_mem_sInvertedT_of_mem_Q model ind hB2 hm haQ haL x.2)
  have hclass : π ⟨a * (x : G) * a⁻¹, hmemL⟩ =
      (q : fc.toHypothesis.centralizerActionQuotient fc.P) *
        π ⟨(x : G), fc.sInvertedT_le_centralizer model ind hB2 hm x.2⟩ *
        (q : fc.toHypothesis.centralizerActionQuotient fc.P)⁻¹ := by
    rw [hq]
    simp only [← map_mul, ← map_inv]
    rfl
  rw [hclass, ← fc.emb_fieldCoord model ind hB2 hm x]
  exact model.qEquiv_conj q _

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
