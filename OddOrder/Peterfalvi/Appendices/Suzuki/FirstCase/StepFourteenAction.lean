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

@[simp]
theorem lineSetTwoPermHom_apply
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (g : ↥(fc.normalizerRSigma model)) (A : ↥fc.lineSetTwo) :
    (fc.lineSetTwoPermHom model ind hB2 g A : Subgroup G)
      = (MulAut.conj ((g : G))) • (A : Subgroup G) := rfl

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
