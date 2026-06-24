/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S07_Coherence

/-!
# Peterfalvi (5.7): the *standalone* constant-degree coherence theorem

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §5, (5.7).

> **(5.7)** Assume Hypothesis (5.2) and that `χ(1)` is independent of `χ` for `χ ∈ S`.  Then `S` is
> coherent.  (`references/peterfalvi/04.7_pp_25_29_Coherence.mmd:107`)

The §11/§13 maximal-subgroup analysis (Peterfalvi (11.5), repo `S13_MaximalIII_IV.HC_le_secondDerived`)
needs this: since `M'/M''` is abelian, the constituents of `S(M'')` all have equal degree, so (5.7)
makes `S(M'')` coherent — the coherence content of `M'' = HC`.

**Status (lane-c relane #8, issue 4012): scoping + signature skeleton.**  All the proof ingredients
already live in `S07_Coherence`: the (5.2) hypothesis carrier `S07.Hypothesis`, the (5.4)
decomposition `CharacterPsiDecomposition`, the (5.4.b)/(5.5) norm lemmas
(`norm_eq_and_X_eq_sum_of_norm_Y_ge` / `eq_sum_of_psi_eq_zero`), and the coherence constructor
`retarget_isCoherent_of_decompositions`.  So (5.7) is an *assembly*, not a missing-machinery gap
(unlike lane-h's (6.2) which needed the `h62` index oracle).  The proof (base case `|S| = 2` from
(5.2.d); inductive build of the auxiliary isometry `τ₁` via per-member `ψ = 0` decompositions, then
`retarget_isCoherent_of_decompositions`) is the next session's work; design + framework mapping are
in `notes/peterfalvi/s05_57_constant_degree_coherence_producer.md`.
-/

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]
variable [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
variable {S : Set (ClassFunction L ℂ)} {A : Set L}

/-! ### (5.7) base case: coherence of a single conjugate pair `{χ, χ̄}` -/

/-- The base-case coherent extension for an orthonormal break pair `{χ, χ̄}`: the projection
`φ ↦ ⟨φ,χ⟩·(ε·μ) + ⟨φ,χ̄⟩·(ε·ν)` onto the orthonormal image pair `{μ, ν}` of (5.2.d) (with
`ε = sign`).  A `ℤ`-linear map since `⟨·,χ⟩` is (`IntegralCharacterMap.innerLeftℤ`). -/
noncomputable def pairExtension {τ : IntegralCharacterMap L G} {χ : ClassFunction L ℂ}
    (hχ : CharacterDifferenceImage (L := L) (G := G) τ χ) : IntegralCharacterMap L G :=
  (IntegralCharacterMap.innerLeftℤ χ).smulRight (hχ.sign • (hχ.mu : ClassFunction G ℂ))
    + (IntegralCharacterMap.innerLeftℤ χ.conj).smulRight (hχ.sign • (hχ.nu : ClassFunction G ℂ))

@[simp] theorem pairExtension_apply {τ : IntegralCharacterMap L G} {χ : ClassFunction L ℂ}
    (hχ : CharacterDifferenceImage (L := L) (G := G) τ χ) (φ : ClassFunction L ℂ) :
    pairExtension hχ φ =
      ClassFunction.inner φ χ • (hχ.sign • (hχ.mu : ClassFunction G ℂ))
        + ClassFunction.inner φ χ.conj • (hχ.sign • (hχ.nu : ClassFunction G ℂ)) := by
  simp [pairExtension]

/-- `χ ↦ ε·μ` (uses `‖χ‖² = 1`, `χ ⊥ χ̄`). -/
theorem pairExtension_chi {τ : IntegralCharacterMap L G} {χ : ClassFunction L ℂ}
    (hχ : CharacterDifferenceImage (L := L) (G := G) τ χ)
    (hχχ : ClassFunction.inner χ χ = 1) (hortho : ClassFunction.inner χ χ.conj = 0) :
    pairExtension hχ χ = hχ.sign • (hχ.mu : ClassFunction G ℂ) := by
  rw [pairExtension_apply, hχχ, hortho, one_smul, zero_smul, add_zero]

/-- `χ̄ ↦ ε·ν` (uses `‖χ̄‖² = 1`, `χ̄ ⊥ χ`). -/
theorem pairExtension_chiConj {τ : IntegralCharacterMap L G} {χ : ClassFunction L ℂ}
    (hχ : CharacterDifferenceImage (L := L) (G := G) τ χ)
    (hχbar : ClassFunction.inner χ.conj χ.conj = 1)
    (hortho' : ClassFunction.inner χ.conj χ = 0) :
    pairExtension hχ χ.conj = hχ.sign • (hχ.nu : ClassFunction G ℂ) := by
  rw [pairExtension_apply, hχbar, hortho', one_smul, zero_smul, zero_add]

/-- `χ - χ̄ ↦ τ(χ - χ̄)` (`= ε·(μ - ν)`, `image_eq`). -/
theorem pairExtension_diff {τ : IntegralCharacterMap L G} {χ : ClassFunction L ℂ}
    (hχ : CharacterDifferenceImage (L := L) (G := G) τ χ)
    (hχχ : ClassFunction.inner χ χ = 1) (hχbar : ClassFunction.inner χ.conj χ.conj = 1)
    (hortho : ClassFunction.inner χ χ.conj = 0) (hortho' : ClassFunction.inner χ.conj χ = 0) :
    pairExtension hχ (χ - χ.conj) = τ (χ - χ.conj) := by
  rw [map_sub, pairExtension_chi hχ hχχ hortho, pairExtension_chiConj hχ hχbar hortho',
    hχ.image_eq, smul_sub]

/-- **Peterfalvi (5.7), base case**: a single orthonormal conjugate pair `{χ, χ̄}` is coherent.

`χ` and `χ̄` are orthonormal (`hχχ`/`hχbar`/`hortho`/`hortho'`), distinct (`hne`), the difference
`χ - χ̄` is `A`-supported (`hdiff_supp`), and the only `A`-supported elements of `ℤ[{χ,χ̄}]` are
multiples of `χ - χ̄` (`hsupp`; in Peterfalvi `A = L^#` and `χ(1) ≠ 0` force this).  The coherent
extension is `pairExtension hχ`. -/
noncomputable def isCoherent_pair_of_differenceImage
    {τ : IntegralCharacterMap L G} {χ : ClassFunction L ℂ} {A : Set L}
    (hχ : CharacterDifferenceImage (L := L) (G := G) τ χ)
    (hχχ : ClassFunction.inner χ χ = 1) (hχbar : ClassFunction.inner χ.conj χ.conj = 1)
    (hortho : ClassFunction.inner χ χ.conj = 0) (hortho' : ClassFunction.inner χ.conj χ = 0)
    (hne : χ ≠ χ.conj) (hdiff_supp : (χ - χ.conj).support ⊆ A)
    (hsupp : zSupportedSpan (L := L) {χ, χ.conj} A ⊆ Submodule.span ℤ {χ - χ.conj}) :
    IsCoherent τ ({χ, χ.conj} : Set (ClassFunction L ℂ)) A := by
  have hχmem : χ ∈ Submodule.span ℤ ({χ, χ.conj} : Set (ClassFunction L ℂ)) :=
    Submodule.subset_span (by simp)
  have hχbarmem : χ.conj ∈ Submodule.span ℤ ({χ, χ.conj} : Set (ClassFunction L ℂ)) :=
    Submodule.subset_span (by simp)
  have hdiffmem : χ - χ.conj ∈ zSpan (L := L) ({χ, χ.conj} : Set (ClassFunction L ℂ)) :=
    Submodule.sub_mem _ hχmem hχbarmem
  -- value of the extension at `μ`, `ν` ∈ ZIrr; the ε·μ, ε·ν are in ZIrr.
  have hεμ : hχ.sign • (hχ.mu : ClassFunction G ℂ) ∈ ZIrr G :=
    Submodule.smul_mem _ _ hχ.mu.mem_ZIrr
  have hεν : hχ.sign • (hχ.nu : ClassFunction G ℂ) ∈ ZIrr G :=
    Submodule.smul_mem _ _ hχ.nu.mem_ZIrr
  refine
    { nonzero := ⟨χ - χ.conj, ⟨hdiffmem, hdiff_supp⟩, sub_ne_zero.mpr hne⟩
      extension := pairExtension hχ
      extension_inner_eq := ?_
      extends_on_supported := ?_
      extension_mem_ZIrr := ?_ }
  · -- isometry on `ℤ[{χ,χ̄}]`: orthonormal-basis Parseval.  For `φ = a•χ+b•χ̄`, `ψ = c•χ+d•χ̄`, both
    -- `⟨ext φ, ext ψ⟩` and `⟨φ, ψ⟩` reduce to `a·c + b·d` via the orthonormalities
    -- `⟨εμ,εμ⟩=⟨χ,χ⟩=1`, `⟨εμ,εν⟩=⟨χ,χ̄⟩=0`.
    intro φ ψ hφ hψ
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hφ
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hψ
    have hextφ : pairExtension hχ (a • χ + b • χ.conj)
        = a • (hχ.sign • (hχ.mu : ClassFunction G ℂ)) + b • (hχ.sign • (hχ.nu : ClassFunction G ℂ)) := by
      rw [map_add, map_zsmul, map_zsmul, pairExtension_chi hχ hχχ hortho,
        pairExtension_chiConj hχ hχbar hortho']
    have hextψ : pairExtension hχ (c • χ + d • χ.conj)
        = c • (hχ.sign • (hχ.mu : ClassFunction G ℂ)) + d • (hχ.sign • (hχ.nu : ClassFunction G ℂ)) := by
      rw [map_add, map_zsmul, map_zsmul, pairExtension_chi hχ hχχ hortho,
        pairExtension_chiConj hχ hχbar hortho']
    have hμμ0 : ClassFunction.inner (hχ.mu : ClassFunction G ℂ) (hχ.mu : ClassFunction G ℂ) = 1 := by
      rw [irreducibleCharacter_inner, if_pos rfl]
    have hμν0 : ClassFunction.inner (hχ.mu : ClassFunction G ℂ) (hχ.nu : ClassFunction G ℂ) = 0 := by
      rw [irreducibleCharacter_inner, if_neg hχ.distinct]
    have hνμ0 : ClassFunction.inner (hχ.nu : ClassFunction G ℂ) (hχ.mu : ClassFunction G ℂ) = 0 := by
      rw [irreducibleCharacter_inner, if_neg (Ne.symm hχ.distinct)]
    have hνν0 : ClassFunction.inner (hχ.nu : ClassFunction G ℂ) (hχ.nu : ClassFunction G ℂ) = 1 := by
      rw [irreducibleCharacter_inner, if_pos rfl]
    rw [hextφ, hextψ]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ← Int.cast_smul_eq_zsmul ℂ, ClassFunction.inner_smul_left, ClassFunction.inner_smul_right,
      star_intCast, hμμ0, hμν0, hνμ0, hνν0, hχχ, hortho, hortho', hχbar]
    rcases hχ.sign_eq with hs | hs <;> rw [hs] <;> push_cast <;> ring
  · -- agreement with `τ` on the `A`-supported lattice (= multiples of `χ - χ̄`).
    intro φ hφ
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp (hsupp hφ)
    rw [map_zsmul, map_zsmul, pairExtension_diff hχ hχχ hχbar hortho hortho']
  · -- ZIrr-codomain: `ext` of a lattice element is a `ℤ`-combination of `ε·μ, ε·ν ∈ ZIrr`.
    intro φ hφ
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hφ
    rw [map_add, map_zsmul, map_zsmul, pairExtension_chi hχ hχχ hortho,
      pairExtension_chiConj hχ hχbar hortho']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hεμ) (Submodule.smul_mem _ _ hεν)

/-! ### (5.7) inductive case: the common projection `β` and its two facts

Following Peterfalvi (5.7) directly: fix a distinguished member `χ₀ ∈ S`, build the auxiliary
isometry `τ₁` in **one shot** with `χ₀^{τ₁} = β` (a single element of `R(χ₀)`) and
`ζ^{τ₁} = β − (χ₀ − ζ)^τ` for every other member `ζ`.  Because all members share a degree, the
differences `χ₀ − ζ` are supported, so the auxiliary isometry needed by the (5.4) decompositions is
just the fixed Dade map `τ` itself (`tau1 := τ`) — no running-extension/Gram–Schmidt residual.  The
orthonormal target family `X = {β} ∪ {β − (χ₀ − ζ)^τ}` then feeds `coherentEqualDegree`.

The only genuinely new content is the (5.4.b) **two-sided** norm argument forcing `‖β‖² = 1` and the
independence of `β` from the auxiliary member, packaged in `pairDecomp_X_norm_one` /
`pairDecomp_Y_eq` below.  Everything ZIrr/Dade-specific is abstracted into explicit hypotheses
(`τ(χ − ζ) ∈ ℤ[Irr G]` for supported differences), discharged by the §13 consumer. -/

open OddOrder.RepresentationTheory

/-- The orthonormal image family `R(χ) = {ε·μ, −ε·ν}` of a member `χ ∈ S`, from the (5.2.d)
difference image carried by the hypothesis. -/
noncomputable abbrev imageFam (hyp : Hypothesis (L := L) (G := G) S A)
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    OrthonormalCharacterImageFamily (L := L) (G := G) hyp.tau χ :=
  (hyp.difference_image hχ).toOrthonormalImage

/-- **(5.7) per-pair decomposition.**  For members `χ, ζ ∈ S` with `⟨χ,ζ⟩ = ⟨χ̄,ζ⟩ = 0` and the
supported-difference virtual-character fact `(χ − ζ)^τ ∈ ℤ[Irr G]`, the (5.4) decomposition of
`(χ − ζ)^τ` against `R(χ)`, built against the fixed Dade isometry `τ` (`tau1 := τ`, whose isometry
and `χ − χ̄` agreement are immediate from `hyp.tau_isometry`). -/
noncomputable def pairDecomp (hyp : Hypothesis (L := L) (G := G) S A)
    {χ ζ : ClassFunction L ℂ} (hχ : χ ∈ S)
    (hχζ : ClassFunction.inner χ ζ = 0) (hχbarζ : ClassFunction.inner χ.conj ζ = 0)
    (hZ : hyp.tau (χ - ζ) ∈ ZIrr G) :
    CharacterPsiDecomposition (L := L) (G := G) hyp.tau χ ζ :=
  CharacterPsiDecomposition.ofProjection (imageFam hyp hχ) hyp.tau
    (fun φ ψ _ _ => hyp.tau_isometry.inner_eq φ ψ)
    rfl hZ hχζ hχbarζ
    (hyp.pairwise_orthogonal hχ (hyp.conjugate_mem hχ) (hyp.ne_conj hχ))

/-- `⟨D.X, D'.X⟩ = 0` when the image families are orthogonal (`R(χ) ⊥ R(χ')`, the (5.2.e) input):
lift the per-element orthogonality `⟨D.X, α⟩ = 0` (`α ∈ R(χ')`) to the `ℤ`-combination
`D'.X = ∑_{α ∈ R(χ')} coeff α • α`. -/
theorem inner_X_X'_eq_zero {τ : IntegralCharacterMap L G}
    {χ χ' ψ ψ' : ClassFunction L ℂ}
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    (D' : CharacterPsiDecomposition (L := L) (G := G) τ χ' ψ')
    (hortho : D.imageFamily.Orthogonal D'.imageFamily) :
    ClassFunction.inner D.X D'.X = 0 := by
  rw [D'.X_eq, inner_sum_right]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [OddOrder.RepresentationTheory.inner_smul_right,
    D.inner_X_orthogonal_imageSet_of_orthogonal D'.imageFamily hortho hα, mul_zero]

/-- Inner-self products are real: `⟨φ,φ⟩ = (⟨φ,φ⟩.re : ℂ)`. -/
theorem inner_self_re_cast (φ : ClassFunction G ℂ) :
    ClassFunction.inner φ φ = ((ClassFunction.inner φ φ).re : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
  · rw [Complex.ofReal_im, inner_self_eq_realCast, Complex.ofReal_im]

/-- **Peterfalvi (5.7) two-sided norm core.**  For two members `χ, ζ` in *different* conjugate
pairs (so `R(χ) ⊥ R(ζ)`, both norm-one, both differences supported and virtual), the (5.4)
decomposition `D` of `(χ − ζ)^τ` against `R(χ)` and the symmetric `D'` of `(ζ − χ)^τ` against `R(ζ)`
satisfy `‖D.X‖² = 1` and `D.Y = D'.X`.

This is Peterfalvi's "`‖X‖² = ‖χ‖²`" and "`Y = 0`" combined: the (5.4.b) hypothesis `‖Y‖² ≥ ‖ζ‖²`
is supplied by the symmetric `D'` through `‖D.Y − D'.X‖² ≥ 0` together with the identity
`⟨D.Y, D'.X⟩ = ‖D'.X‖² ≥ ‖ζ‖²` (which holds because `D.Y = D.X − (χ − ζ)^τ`, `(χ − ζ)^τ = D'.Y − D'.X`,
`⟨D.X, D'.X⟩ = 0` and `⟨D'.X, D'.Y⟩ = 0`).  Once `‖D.Y‖² = ‖ζ‖²` is forced, `‖D.Y − D'.X‖² = 0`. -/
theorem pairDecomp_two_sided
    {τ : IntegralCharacterMap L G} {χ ζ : ClassFunction L ℂ}
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ζ)
    (D' : CharacterPsiDecomposition (L := L) (G := G) τ ζ χ)
    (hχχ : ClassFunction.inner χ χ = 1) (hζζ : ClassFunction.inner ζ ζ = 1)
    (hortho : D.imageFamily.Orthogonal D'.imageFamily)
    (himgD : τ (χ - ζ) = D.X - D.Y) (himgD' : τ (ζ - χ) = D'.X - D'.Y) :
    ClassFunction.inner D.X D.X = 1 ∧ D.Y = D'.X := by
  -- `⟨D.X, D'.X⟩ = 0` (cross-family) and `⟨D'.Y, D'.X⟩ = 0` (image ⊥ residual).
  have hXX' : ClassFunction.inner D.X D'.X = 0 := inner_X_X'_eq_zero D D' hortho
  have hYX' : ClassFunction.inner D'.Y D'.X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, D'.inner_X_Y, star_zero]
  -- `D.Y = D.X − (χ−ζ)^τ`, and `(χ−ζ)^τ = D'.Y − D'.X`.
  have hDYval : D.Y = D.X - τ (χ - ζ) := by rw [himgD]; abel
  have hτχζ : τ (χ - ζ) = D'.Y - D'.X := by
    have hneg : χ - ζ = -(ζ - χ) := by abel
    rw [hneg, map_neg, himgD']; abel
  -- `⟨D.Y, D'.X⟩ = ‖D'.X‖²`.
  have hYX'_eq : ClassFunction.inner D.Y D'.X = ClassFunction.inner D'.X D'.X := by
    rw [hDYval, ClassFunction.inner_sub_left, hXX', hτχζ, ClassFunction.inner_sub_left, hYX']
    ring
  -- `‖D'.X‖².re ≥ ‖ζ‖².re = 1` from (5.4.a) on `D'`.
  have hD'Xge : (1 : ℝ) ≤ (ClassFunction.inner D'.X D'.X).re := by
    have h := D'.inner_self_chi_re_le_inner_self_X
    rw [hζζ] at h; simpa using h
  -- `‖D.Y − D'.X‖².re = ‖D.Y‖².re − ‖D'.X‖².re`.
  have hdiffre : (ClassFunction.inner (D.Y - D'.X) (D.Y - D'.X)).re
      = (ClassFunction.inner D.Y D.Y).re - (ClassFunction.inner D'.X D'.X).re := by
    have hexp : ClassFunction.inner (D.Y - D'.X) (D.Y - D'.X)
        = ClassFunction.inner D.Y D.Y - ClassFunction.inner D.Y D'.X
          - ClassFunction.inner D'.X D.Y + ClassFunction.inner D'.X D'.X := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right]; ring
    rw [hexp, hYX'_eq, OddOrder.RepresentationTheory.inner_conj_symm D.Y D'.X, hYX'_eq]
    simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re]; ring
  have hDYge : (1 : ℝ) ≤ (ClassFunction.inner D.Y D.Y).re := by
    have hnn := inner_self_re_nonneg (D.Y - D'.X)
    rw [hdiffre] at hnn; linarith
  -- (5.4.b) on `D` with `‖ζ‖².re ≤ ‖D.Y‖².re`.
  have hY : (ClassFunction.inner ζ ζ).re ≤ (ClassFunction.inner D.Y D.Y).re := by
    rw [hζζ]; simpa using hDYge
  obtain ⟨hXnorm, hYnorm, _⟩ := D.norm_eq_and_X_eq_sum_of_norm_Y_ge hY
  refine ⟨?_, ?_⟩
  · -- `‖D.X‖² = 1` (ℂ): `‖χ‖².re = ‖D.X‖².re` and `‖χ‖² = 1`.
    have hXre : (ClassFunction.inner D.X D.X).re = 1 := by rw [← hXnorm, hχχ]; simp
    rw [inner_self_re_cast D.X, hXre]; exact Complex.ofReal_one
  · -- `D.Y = D'.X`: both norm `1`, and `‖D.Y − D'.X‖².re = 0`.
    have hDY1 : (ClassFunction.inner D.Y D.Y).re = 1 := by rw [← hYnorm, hζζ]; simp
    have hDX'1 : (ClassFunction.inner D'.X D'.X).re = 1 := by
      have hnn := inner_self_re_nonneg (D.Y - D'.X)
      rw [hdiffre] at hnn; linarith
    have hdz : D.Y - D'.X = 0 := by
      apply eq_zero_of_inner_self_re_eq_zero
      rw [hdiffre, hDY1, hDX'1]; ring
    exact sub_eq_zero.mp hdz

/-- `⟨D.X, w⟩ = 0` when `w ⊥ R(χ)` (`w` orthogonal to every member of the image family).  The
`X`-side companion of `Y_orthogonal`. -/
theorem inner_X_perp {τ : IntegralCharacterMap L G} {χ ψ : ClassFunction L ℂ}
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) {w : ClassFunction G ℂ}
    (hw : ∀ α ∈ D.imageFamily.imageSet, ClassFunction.inner w α = 0) :
    ClassFunction.inner D.X w = 0 := by
  rw [D.X_eq, inner_sum_left]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_conj_symm, hw α hα,
    star_zero, mul_zero]

/-- `χ`, `ζ` lie in *different* conjugate pairs: `χ ∉ {ζ, ζ̄}`.  (Then also `χ̄ ∉ {ζ, ζ̄}`, and the
relation is symmetric.) -/
def DiffPair (χ ζ : ClassFunction L ℂ) : Prop := χ ≠ ζ ∧ χ ≠ ζ.conj

theorem DiffPair.conj_ne {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) : χ.conj ≠ ζ :=
  fun he => h.2 (by rw [← ClassFunction.conj_conj χ, he])

theorem DiffPair.symm {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) : DiffPair ζ χ :=
  ⟨h.1.symm, fun he => h.2 (by rw [he, ClassFunction.conj_conj])⟩

theorem DiffPair.inner_eq_zero (hyp : Hypothesis (L := L) (G := G) S A)
    {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) (hχ : χ ∈ S) (hζ : ζ ∈ S) :
    ClassFunction.inner χ ζ = 0 :=
  hyp.pairwise_orthogonal hχ hζ h.1

theorem DiffPair.inner_conj_eq_zero (hyp : Hypothesis (L := L) (G := G) S A)
    {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) (hχ : χ ∈ S) (hζ : ζ ∈ S) :
    ClassFunction.inner χ ζ.conj = 0 :=
  hyp.pairwise_orthogonal hχ (hyp.conjugate_mem hζ) h.2

/-- The image families of two members in different conjugate pairs are orthogonal (the (5.2.e) input
lifted through `toOrthonormalImage`). -/
theorem DiffPair.imageFam_orthogonal (hyp : Hypothesis (L := L) (G := G) S A)
    {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) (hχ : χ ∈ S) (hζ : ζ ∈ S) :
    (imageFam hyp hχ).Orthogonal (imageFam hyp hζ) :=
  CharacterDifferenceImage.toOrthonormalImage_orthogonal
    (hyp.difference_image hχ) (hyp.difference_image hζ)
    (hyp.difference_images_orthogonal hχ hζ
      (h.inner_eq_zero hyp hχ hζ) (h.inner_conj_eq_zero hyp hχ hζ))

/-- The per-pair decomposition `pairDecomp` for two members `χ, ζ` in *different* conjugate pairs. -/
noncomputable def pairDecomp' (hyp : Hypothesis (L := L) (G := G) S A)
    {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) (hχ : χ ∈ S) (hζ : ζ ∈ S)
    (hZ : hyp.tau (χ - ζ) ∈ ZIrr G) :
    CharacterPsiDecomposition (L := L) (G := G) hyp.tau χ ζ :=
  pairDecomp hyp hχ (hyp.pairwise_orthogonal hχ hζ h.1)
    (hyp.pairwise_orthogonal (hyp.conjugate_mem hχ) hζ h.conj_ne) hZ

/-- The defining image equation `(χ − ζ)^τ = D.X − D.Y` for `D = pairDecomp' …` (the `tau1_image`
field of `ofProjection`, with the fixed `tau1 = τ`). -/
theorem pairDecomp'_image (hyp : Hypothesis (L := L) (G := G) S A)
    {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) (hχ : χ ∈ S) (hζ : ζ ∈ S)
    (hZ : hyp.tau (χ - ζ) ∈ ZIrr G) :
    hyp.tau (χ - ζ) = (pairDecomp' hyp h hχ hζ hZ).X - (pairDecomp' hyp h hχ hζ hZ).Y :=
  (pairDecomp' hyp h hχ hζ hZ).tau1_image

/-- `⟨D.X, ∑_{β ∈ R'} β⟩ = 0` for an orthogonal second family `R'` (`R(χ) ⊥ R'`). -/
theorem inner_X_sum_imageFam_eq_zero {τ : IntegralCharacterMap L G} {χ χ' ψ : ClassFunction L ℂ}
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    (R' : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ')
    (hortho : D.imageFamily.Orthogonal R') :
    ClassFunction.inner D.X (∑ β ∈ R'.imageSet, β) = 0 := by
  refine inner_X_perp D fun α hα => ?_
  rw [inner_sum_left]
  refine Finset.sum_eq_zero fun β hβ => ?_
  rw [OddOrder.RepresentationTheory.inner_conj_symm, hortho α hα β hβ, star_zero]

/-- **Peterfalvi (5.7) common image `β = χ₀^{τ₁}`.**  The `R(χ₀)`-projection of `(χ₀ − ζ₀)^τ` for a
fixed reference member `ζ₀` in a different conjugate pair from `χ₀`.  By `pairDecomp_two_sided` this
is a single element of `R(χ₀)` of norm one; Peterfalvi (5.7) shows it is *independent* of `ζ₀`. -/
noncomputable def commonImage (hyp : Hypothesis (L := L) (G := G) S A)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    {χ₀ ζ₀ : ClassFunction L ℂ} (hdp : DiffPair χ₀ ζ₀) (hχ₀ : χ₀ ∈ S) (hζ₀ : ζ₀ ∈ S) :
    ClassFunction G ℂ :=
  (pairDecomp' hyp hdp hχ₀ hζ₀ (hZIrr χ₀ hχ₀ ζ₀ hζ₀)).X

/-- The two-sided norm facts for `pairDecomp'`: `‖D.X‖² = 1` and `D.Y = D'.X` (the symmetric
decomposition), from `pairDecomp_two_sided`. -/
theorem pairDecomp'_two_sided (hyp : Hypothesis (L := L) (G := G) S A)
    (hirr : ∀ ζ ∈ S, ClassFunction.inner ζ ζ = 1)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) (hχ : χ ∈ S) (hζ : ζ ∈ S) :
    ClassFunction.inner (pairDecomp' hyp h hχ hζ (hZIrr χ hχ ζ hζ)).X
        (pairDecomp' hyp h hχ hζ (hZIrr χ hχ ζ hζ)).X = 1 ∧
      (pairDecomp' hyp h hχ hζ (hZIrr χ hχ ζ hζ)).Y =
        (pairDecomp' hyp h.symm hζ hχ (hZIrr ζ hζ χ hχ)).X :=
  pairDecomp_two_sided (pairDecomp' hyp h hχ hζ (hZIrr χ hχ ζ hζ))
    (pairDecomp' hyp h.symm hζ hχ (hZIrr ζ hζ χ hχ))
    (hirr χ hχ) (hirr ζ hζ) (h.imageFam_orthogonal hyp hχ hζ)
    (pairDecomp'_image hyp h hχ hζ (hZIrr χ hχ ζ hζ))
    (pairDecomp'_image hyp h.symm hζ hχ (hZIrr ζ hζ χ hχ))

/-- **(5.7) fact (A): `‖β‖² = 1`.** -/
theorem commonImage_self (hyp : Hypothesis (L := L) (G := G) S A)
    (hirr : ∀ ζ ∈ S, ClassFunction.inner ζ ζ = 1)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    {χ₀ ζ₀ : ClassFunction L ℂ} (hdp : DiffPair χ₀ ζ₀) (hχ₀ : χ₀ ∈ S) (hζ₀ : ζ₀ ∈ S) :
    ClassFunction.inner (commonImage hyp hZIrr hdp hχ₀ hζ₀)
      (commonImage hyp hZIrr hdp hχ₀ hζ₀) = 1 :=
  (pairDecomp'_two_sided hyp hirr hZIrr hdp hχ₀ hζ₀).1

/-- **(5.7) fact (B) at the reference `ζ₀`: `⟨β, (χ₀ − ζ₀)^τ⟩ = 1`.**  `= ⟨D₀.X, D₀.X − D₀.Y⟩ =
‖D₀.X‖² − 0`. -/
theorem commonImage_inner_ref (hyp : Hypothesis (L := L) (G := G) S A)
    (hirr : ∀ ζ ∈ S, ClassFunction.inner ζ ζ = 1)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    {χ₀ ζ₀ : ClassFunction L ℂ} (hdp : DiffPair χ₀ ζ₀) (hχ₀ : χ₀ ∈ S) (hζ₀ : ζ₀ ∈ S) :
    ClassFunction.inner (commonImage hyp hZIrr hdp hχ₀ hζ₀) (hyp.tau (χ₀ - ζ₀)) = 1 := by
  rw [commonImage, pairDecomp'_image hyp hdp hχ₀ hζ₀ (hZIrr χ₀ hχ₀ ζ₀ hζ₀),
    ClassFunction.inner_sub_right, (pairDecomp' hyp hdp hχ₀ hζ₀ (hZIrr χ₀ hχ₀ ζ₀ hζ₀)).inner_X_Y,
    sub_zero, (pairDecomp'_two_sided hyp hirr hZIrr hdp hχ₀ hζ₀).1]

/-- **(5.7) fact (B) at `χ̄₀`: `⟨β, (χ₀ − χ̄₀)^τ⟩ = 1`.**  `(χ₀ − χ̄₀)^τ = ∑_{R(χ₀)} α`, and
`⟨β, ∑ α⟩ = ∑ coeff = ‖χ₀‖² = 1` (the keystone). -/
theorem commonImage_inner_conj (hyp : Hypothesis (L := L) (G := G) S A)
    (hirr : ∀ ζ ∈ S, ClassFunction.inner ζ ζ = 1)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    {χ₀ ζ₀ : ClassFunction L ℂ} (hdp : DiffPair χ₀ ζ₀) (hχ₀ : χ₀ ∈ S) (hζ₀ : ζ₀ ∈ S) :
    ClassFunction.inner (commonImage hyp hZIrr hdp hχ₀ hζ₀) (hyp.tau (χ₀ - χ₀.conj)) = 1 := by
  rw [commonImage]
  set D₀ := pairDecomp' hyp hdp hχ₀ hζ₀ (hZIrr χ₀ hχ₀ ζ₀ hζ₀) with hD₀
  rw [D₀.imageFamily.image_eq, D₀.inner_X_sum, ← D₀.inner_self_chi_eq_sum_coeff, hirr χ₀ hχ₀]

/-- **(5.7) fact (B) at `ζ̄₀`: `⟨β, (χ₀ − ζ̄₀)^τ⟩ = 1`.**  `(χ₀ − ζ̄₀)^τ = (χ₀ − ζ₀)^τ + (ζ₀ − ζ̄₀)^τ`;
the first gives `1` (reference), the second is `∑_{R(ζ₀)} α ⊥ R(χ₀)`. -/
theorem commonImage_inner_refconj (hyp : Hypothesis (L := L) (G := G) S A)
    (hirr : ∀ ζ ∈ S, ClassFunction.inner ζ ζ = 1)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    {χ₀ ζ₀ : ClassFunction L ℂ} (hdp : DiffPair χ₀ ζ₀) (hχ₀ : χ₀ ∈ S) (hζ₀ : ζ₀ ∈ S) :
    ClassFunction.inner (commonImage hyp hZIrr hdp hχ₀ hζ₀) (hyp.tau (χ₀ - ζ₀.conj)) = 1 := by
  have hsplit : χ₀ - ζ₀.conj = (χ₀ - ζ₀) + (ζ₀ - ζ₀.conj) := by abel
  rw [hsplit, map_add, ClassFunction.inner_add_right,
    commonImage_inner_ref hyp hirr hZIrr hdp hχ₀ hζ₀, commonImage,
    (imageFam hyp hζ₀).image_eq,
    inner_X_sum_imageFam_eq_zero (pairDecomp' hyp hdp hχ₀ hζ₀ (hZIrr χ₀ hχ₀ ζ₀ hζ₀))
      (imageFam hyp hζ₀) (hdp.imageFam_orthogonal hyp hχ₀ hζ₀), add_zero]

/-- **(5.7) fact (B) at a member `ζ` in a *third* pair: `⟨β, (χ₀ − ζ)^τ⟩ = 1`.**  The independence
of `β` from the auxiliary member: `⟨β, (χ₀−ζ)^τ⟩ = ⟨D₀.X, Dζ.X⟩ = ⟨χ₀−ζ₀, χ₀−ζ⟩ = 1`, the cross terms
vanishing because `R(χ₀) ⊥ R(ζ)`, `R(χ₀) ⊥ R(ζ₀)` and `D₀.Y, Dζ.Y` lie in `R(ζ₀)`, `R(ζ)` (different
pairs, `pairDecomp_two_sided`). -/
theorem commonImage_inner_other (hyp : Hypothesis (L := L) (G := G) S A)
    (hirr : ∀ ζ ∈ S, ClassFunction.inner ζ ζ = 1)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    {χ₀ ζ₀ ζ : ClassFunction L ℂ} (hdp : DiffPair χ₀ ζ₀) (hχ₀ : χ₀ ∈ S) (hζ₀ : ζ₀ ∈ S)
    (hζ : ζ ∈ S) (hdpχ : DiffPair χ₀ ζ) (hdpζ : DiffPair ζ₀ ζ) :
    ClassFunction.inner (commonImage hyp hZIrr hdp hχ₀ hζ₀) (hyp.tau (χ₀ - ζ)) = 1 := by
  rw [commonImage, pairDecomp'_image hyp hdpχ hχ₀ hζ (hZIrr χ₀ hχ₀ ζ hζ),
    ClassFunction.inner_sub_right]
  set D₀ := pairDecomp' hyp hdp hχ₀ hζ₀ (hZIrr χ₀ hχ₀ ζ₀ hζ₀) with hD₀
  set Dζ := pairDecomp' hyp hdpχ hχ₀ hζ (hZIrr χ₀ hχ₀ ζ hζ) with hDζ
  -- `⟨D₀.X, Dζ.Y⟩ = 0` (`Dζ.Y ⊥ R(χ₀)`), so the goal is `⟨D₀.X, Dζ.X⟩ = 1`.
  rw [inner_X_perp D₀ Dζ.Y_orthogonal, sub_zero]
  -- isometry: `⟨(χ₀−ζ₀)^τ, (χ₀−ζ)^τ⟩ = ⟨χ₀−ζ₀, χ₀−ζ⟩`.
  have hiso : ClassFunction.inner (hyp.tau (χ₀ - ζ₀)) (hyp.tau (χ₀ - ζ))
      = ClassFunction.inner (χ₀ - ζ₀) (χ₀ - ζ) := hyp.tau_isometry.inner_eq _ _
  rw [pairDecomp'_image hyp hdp hχ₀ hζ₀ (hZIrr χ₀ hχ₀ ζ₀ hζ₀),
    pairDecomp'_image hyp hdpχ hχ₀ hζ (hZIrr χ₀ hχ₀ ζ hζ)] at hiso
  -- the cross terms.
  have hXY : ClassFunction.inner D₀.X Dζ.Y = 0 := inner_X_perp D₀ Dζ.Y_orthogonal
  have hYX : ClassFunction.inner D₀.Y Dζ.X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, inner_X_perp Dζ D₀.Y_orthogonal, star_zero]
  have hYY : ClassFunction.inner D₀.Y Dζ.Y = 0 := by
    rw [(pairDecomp'_two_sided hyp hirr hZIrr hdp hχ₀ hζ₀).2,
      (pairDecomp'_two_sided hyp hirr hZIrr hdpχ hχ₀ hζ).2]
    exact inner_X_X'_eq_zero _ _ (hdpζ.imageFam_orthogonal hyp hζ₀ hζ)
  -- the right-hand side `⟨χ₀−ζ₀, χ₀−ζ⟩ = 1`.
  have hLHS : ClassFunction.inner (χ₀ - ζ₀) (χ₀ - ζ) = 1 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
      hirr χ₀ hχ₀, hdpχ.inner_eq_zero hyp hχ₀ hζ, hdp.symm.inner_eq_zero hyp hζ₀ hχ₀,
      hdpζ.inner_eq_zero hyp hζ₀ hζ]
    ring
  rw [hLHS, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, hXY, hYX, hYY] at hiso
  linear_combination hiso

/-- **Peterfalvi (5.7) fact (B), dispatcher: `⟨β, (χ₀ − ζ)^τ⟩ = 1` for every member `ζ ≠ χ₀`.** -/
theorem commonImage_inner (hyp : Hypothesis (L := L) (G := G) S A)
    (hirr : ∀ ζ ∈ S, ClassFunction.inner ζ ζ = 1)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    {χ₀ ζ₀ : ClassFunction L ℂ} (hdp : DiffPair χ₀ ζ₀) (hχ₀ : χ₀ ∈ S) (hζ₀ : ζ₀ ∈ S)
    {ζ : ClassFunction L ℂ} (hζ : ζ ∈ S) (hζne : ζ ≠ χ₀) :
    ClassFunction.inner (commonImage hyp hZIrr hdp hχ₀ hζ₀) (hyp.tau (χ₀ - ζ)) = 1 := by
  by_cases hc1 : ζ = χ₀.conj
  · rw [hc1]; exact commonImage_inner_conj hyp hirr hZIrr hdp hχ₀ hζ₀
  have hdpχ : DiffPair χ₀ ζ :=
    ⟨hζne.symm, fun h => hc1 (by rw [← ClassFunction.conj_conj ζ, ← h])⟩
  by_cases hc2 : ζ = ζ₀
  · rw [hc2]; exact commonImage_inner_ref hyp hirr hZIrr hdp hχ₀ hζ₀
  by_cases hc3 : ζ = ζ₀.conj
  · rw [hc3]; exact commonImage_inner_refconj hyp hirr hZIrr hdp hχ₀ hζ₀
  have hdpζ : DiffPair ζ₀ ζ :=
    ⟨fun h => hc2 h.symm, fun h => hc3 (by rw [h, ClassFunction.conj_conj] : ζ₀.conj = ζ).symm⟩
  exact commonImage_inner_other hyp hirr hZIrr hdp hχ₀ hζ₀ hζ hdpχ hdpζ

/-- **Peterfalvi (5.7), standalone form**: under the (5.2) coherence hypotheses, if every member of
`S` has the same degree `χ(1)`, then `(S, A, τ)` is coherent.

The constant-degree hypothesis `hconst` is stated faithfully (Peterfalvi assumes it); pinning down
exactly which step of the assembly consumes it — versus its being needed only for the equal-degree
*application* — is part of the implementation (see the design note).  `hne` is the nondegeneracy
witness of the (5.1) coherence predicate (an `A`-supported nonzero element of `ℤ[S]`).

This is the producer that `S13_MaximalIII_IV.HC_le_secondDerived` (Peterfalvi (11.5)) will cite, once
a `Hypothesis (5.2)` instance for `S(M'')` is constructed on the §13 Dade side. -/
theorem coherent_of_constant_degree
    (hyp : Hypothesis (L := L) (G := G) S A)
    (hconst : ∀ χ ∈ S, ∀ ψ ∈ S, χ 1 = ψ 1)
    (hne : ∃ φ : ClassFunction L ℂ, φ ∈ zSupportedSpan (L := L) S A ∧ φ ≠ 0) :
    Nonempty (IsCoherent hyp.tau S A) := by
  -- Assembly over `S07_Coherence`: base case `|S| = 2` from (5.2.d); inductive build of the
  -- auxiliary isometry via `eq_sum_of_psi_eq_zero` (5.5) per member, then
  -- `retarget_isCoherent_of_decompositions`.  See the design note.
  sorry

end OddOrder.Peterfalvi.S07
