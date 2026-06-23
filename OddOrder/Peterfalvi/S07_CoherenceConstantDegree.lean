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
