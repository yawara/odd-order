import OddOrder.Peterfalvi.S07_Coherence.DifferenceImage

/-!
# Peterfalvi (5.4)-(5.6)/(6.6) 前半 — norm inequalities, ψ-decomposition, IsCoherent, degree gap

Split from the former monolithic `OddOrder.Peterfalvi.S07_Coherence` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S07
open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]


/-! ### Peterfalvi (5.4): the norm inequalities for `X` and `Y`

Setup: `χ ∈ S`, `ψ ∈ ℤ[S]` with `(χ,ψ) = (χ̄,ψ) = 0`; an isometry `τ₁` on
`ℤ[χ-ψ, χ-χ̄]` coinciding with `τ` on `ℤ[χ-χ̄]`; `(χ-ψ)^{τ₁} = X - Y` with
`X ∈ ℤ[R(χ)]` and `Y ⊥ R(χ)`.  The conclusions are:

* (5.4.a) `‖X‖² ≥ ‖χ‖²`;
* (5.4.b) if also `‖Y‖² ≥ ‖ψ‖²`, then `‖X‖² = ‖χ‖²`, `‖Y‖² = ‖ψ‖²` and
  `X = ∑_{α ∈ E} α` for some `E ⊆ R(χ)`.

The whole argument is the integer Cauchy–Schwarz `∑ c_α ≤ ∑ c_α²` against the
orthonormal `R(χ)`, run through the Parseval identities of `ZIrrFourier`. -/

open OddOrder.RepresentationTheory in
/-- **Peterfalvi (5.4) setup.**  Bundles the hypotheses of (5.4): the orthonormal
image family `R(χ)`, the auxiliary isometry `τ₁` agreeing with `τ` on `χ - χ̄`, the
decomposition `(χ - ψ)^{τ₁} = X - Y` with `X ∈ ℤ[R(χ)]` (recorded via integer
coefficients `coeff`) and `Y ⊥ R(χ)`, and the orthogonality relations
`(χ,ψ) = (χ̄,ψ) = (χ,χ̄) = 0`. -/
structure CharacterPsiDecomposition (τ : IntegralCharacterMap L G)
    (χ ψ : ClassFunction L ℂ)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  /-- The orthonormal image family `R(χ)` with `(χ - χ̄)^τ = ∑_{α ∈ R(χ)} α`. -/
  imageFamily : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ
  /-- The auxiliary isometry `τ₁` on `ℤ[χ - ψ, χ - χ̄]`. -/
  tau1 : IntegralCharacterMap L G
  /-- `τ₁` preserves the inner product on the sponsoring lattice `ℤ[χ, χ̄, ψ]`.

  This is **lattice-relative**, not a global `IsIntegralIsometry` on all of `CF(L)`:
  it is the same Round-13 weakening already applied to `IsCoherent.extension_inner_eq`.
  In Feit–Thompson `dim CF(L) > dim CF(G)`, so a global isometry of the
  character-difference lattice into `CF(G)` generically does not exist, but the Dade
  isometry / running extension *does* preserve the inner product on the supported
  sublattice `ℤ[χ, χ̄, ψ]` — which is all the (5.4.b)/(5.5)/(5.6.2) proofs use (every
  access is on `χ - ψ` or `χ - χ̄`, both in `ℤ[χ, χ̄, ψ]`). -/
  tau1_inner_eq_on_support :
    ∀ φ ζ : ClassFunction L ℂ,
      φ ∈ zSpan (L := L) {χ - χ.conj, χ - ψ} → ζ ∈ zSpan (L := L) {χ - χ.conj, χ - ψ} →
      ClassFunction.inner (tau1 φ) (tau1 ζ) = ClassFunction.inner φ ζ
  /-- `τ₁` coincides with `τ` on `χ - χ̄`. -/
  tau1_agrees : tau1 (χ - χ.conj) = τ (χ - χ.conj)
  /-- The image side `X` of `(χ - ψ)^{τ₁} = X - Y`. -/
  X : ClassFunction G ℂ
  /-- The orthogonal side `Y` of `(χ - ψ)^{τ₁} = X - Y`. -/
  Y : ClassFunction G ℂ
  /-- The decomposition `(χ - ψ)^{τ₁} = X - Y`. -/
  tau1_image : tau1 (χ - ψ) = X - Y
  /-- The integer coefficients of `X ∈ ℤ[R(χ)]`. -/
  coeff : ClassFunction G ℂ → ℤ
  /-- `X = ∑_{α ∈ R(χ)} (coeff α) • α`, i.e. `X ∈ ℤ[R(χ)]`. -/
  X_eq : X = ∑ α ∈ imageFamily.imageSet, (coeff α : ℂ) • α
  /-- `Y` is orthogonal to `R(χ)`. -/
  Y_orthogonal : ∀ α ∈ imageFamily.imageSet, ClassFunction.inner Y α = 0
  /-- `(χ, ψ) = 0`. -/
  chi_psi_orthogonal : ClassFunction.inner χ ψ = 0
  /-- `(χ̄, ψ) = 0`. -/
  chiConj_psi_orthogonal : ClassFunction.inner χ.conj ψ = 0
  /-- `(χ, χ̄) = 0` (the distinct elements `χ`, `χ̄ ∈ S` are orthogonal by (5.2.c)). -/
  chi_chiConj_orthogonal : ClassFunction.inner χ χ.conj = 0

namespace CharacterPsiDecomposition

open OddOrder.RepresentationTheory

variable {τ : IntegralCharacterMap L G} {χ ψ : ClassFunction L ℂ}
variable [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

open scoped Classical in
/-- **Smart constructor for `CharacterPsiDecomposition` via integral projection.**

The hard `X`/`Y`/`coeff` content of the (5.4) decomposition `(χ − ψ)^{τ₁} = X − Y` — the
integral `R(χ)`-projection `X = ∑_{α ∈ R(χ)} (coeff α)•α ∈ ℤ[R(χ)]` and the orthogonal residual
`Y ⊥ R(χ)` — is *computed*, not posited, from the single number-theoretic input
`htau1_mem : (χ − ψ)^{τ₁} ∈ ZIrr G` (the τ₁-image is a virtual character of `G`).  This is the
orthogonal projection of `(χ − ψ)^{τ₁}` onto the ZIrr-orthonormal family `R(χ)`
(`exists_intProjection_of_orthonormal_ZIrr`, integer coefficients because `R(χ) ⊆ ZIrr G`); the
residual `Y` is its orthogonal complement.

The remaining inputs are exactly the *structural* data a per-step (5.4)/(5.5)/(5.6.1) construction
must still supply:
* `imageFamily` — the signed-irreducible family `R(χ)` with `(χ − χ̄)^τ = ∑_{α} α` (from the Dade
  data / §3 keystone, `OrthonormalCharacterImageFamily`);
* `tau1`, `htau1_inner_eq`, `htau1_agrees` — the (5.4) auxiliary isometry `τ₁`, supplied as
  **lattice-relative** inner-preservation on the sponsoring lattice `ℤ[χ, χ̄, ψ]` (the Round-13
  weakening: the Dade isometry / running extension preserves `⟨·,·⟩` only on the supported
  sublattice, *not* globally on `CF(L)`), agreeing with `τ` on `χ − χ̄`;
* the three (5.2.c)/(5.4) orthogonality scalars `⟨χ, ψ⟩ = ⟨χ̄, ψ⟩ = ⟨χ, χ̄⟩ = 0`.

This isolates the genuinely missing primitives (the Dade `R(χ)` extractor and the `τ₁`
isometry-extension) as the only residual: once those are built, this constructor delivers the full
`CharacterPsiDecomposition` with its `X`/`Y`/`coeff`/`X_eq`/`Y_orthogonal` fields populated by the
projection. -/
noncomputable def ofProjection
    (imageFamily : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ)
    (tau1 : IntegralCharacterMap L G)
    (htau1_inner_eq : ∀ φ ζ : ClassFunction L ℂ,
      φ ∈ zSpan (L := L) {χ - χ.conj, χ - ψ} → ζ ∈ zSpan (L := L) {χ - χ.conj, χ - ψ} →
      ClassFunction.inner (tau1 φ) (tau1 ζ) = ClassFunction.inner φ ζ)
    (htau1_agrees : tau1 (χ - χ.conj) = τ (χ - χ.conj))
    (htau1_mem : tau1 (χ - ψ) ∈ ZIrr G)
    (hχψ : ClassFunction.inner χ ψ = 0)
    (hχbarψ : ClassFunction.inner χ.conj ψ = 0)
    (hχχbar : ClassFunction.inner χ χ.conj = 0) :
    CharacterPsiDecomposition (L := L) (G := G) τ χ ψ :=
  let proj := ClassFunction.exists_intProjection_of_orthonormal_ZIrr htau1_mem
    imageFamily.mem_ZIrr imageFamily.orthonormal
  { imageFamily := imageFamily
    tau1 := tau1
    tau1_inner_eq_on_support := htau1_inner_eq
    tau1_agrees := htau1_agrees
    X := ∑ α ∈ imageFamily.imageSet, (proj.choose α : ℂ) • α
    Y := -(tau1 (χ - ψ) - ∑ α ∈ imageFamily.imageSet, (proj.choose α : ℂ) • α)
    tau1_image := by
      -- `X − Y = X − (−(τ₁(χ−ψ) − X)) = τ₁(χ−ψ)`, pure algebra.
      rw [sub_neg_eq_add]; abel
    coeff := proj.choose
    X_eq := rfl
    Y_orthogonal := by
      -- `⟨Y, α⟩ = −⟨τ₁(χ−ψ) − X, α⟩ = −(⟨τ₁(χ−ψ), α⟩ − coeff α) = −(coeff α − coeff α) = 0`.
      intro α hα
      have hcoeff : ClassFunction.inner (tau1 (χ - ψ)) α = (proj.choose α : ℂ) :=
        proj.choose_spec.choose_spec.1 α hα
      rw [ClassFunction.inner_neg_left, ClassFunction.inner_sub_left,
        inner_orthonormalSum_eq_coeff imageFamily.orthonormal hα, hcoeff, sub_self, neg_zero]
    chi_psi_orthogonal := hχψ
    chiConj_psi_orthogonal := hχbarψ
    chi_chiConj_orthogonal := hχχbar }

open scoped Classical in
/-- **Peterfalvi (5.6.3) per-step decomposition pair: shared auxiliary isometry.**
`(D₀, Da)` for the *same* `χ` built against the *same* auxiliary isometry `τ₁`, so that the
projection identity `Da.tau1 χ = D₀.tau1 χ` (the honest τ₁-agreement input of
`retarget_isCoherent_of_decompositions`) holds by `rfl`.

This packages the PASS 2 (ii) per-step production: from a single shared `(imageFamily, τ₁,
isometry, agreement)` plus the two number-theoretic `ZIrr`-membership facts
`(χ − 0)^{τ₁} ∈ ℤ[Irr G]` and `(χ − a·χ₁)^{τ₁} ∈ ℤ[Irr G]`, both `ofProjection` calls produce
`CharacterPsiDecomposition`s with the *same* `tau1` field, so the two `R(χ)`-projections are
evaluated against one running isometry — exactly Peterfalvi's "`τ₂` extends `τ₁`".  The
distinguishing data are only the two `ψ`-values (`0` and `a·χ₁`); everything geometric (`R(χ)`, the
isometry, the agreement) is shared, and the `Da.tau1 χ = D₀.tau1 χ` agreement is *structural*.

The orthogonalities for `ψ = a·χ₁` are derived from the bare `⟨χ, χ₁⟩ = ⟨χ̄, χ₁⟩ = 0` (the
`χ ⊥ S₁` hypothesis); for `ψ = 0` they are automatic (`inner_zero_right`). -/
noncomputable def decompositionPair {a : ℕ} {chi1 : ClassFunction L ℂ}
    (imageFamily : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ)
    (tau1 : IntegralCharacterMap L G)
    (htau1_inner_eq : ∀ φ ζ : ClassFunction L ℂ,
      φ ∈ zSpan (L := L) {χ, χ.conj, 0, a • chi1} →
      ζ ∈ zSpan (L := L) {χ, χ.conj, 0, a • chi1} →
      ClassFunction.inner (tau1 φ) (tau1 ζ) = ClassFunction.inner φ ζ)
    (htau1_agrees : tau1 (χ - χ.conj) = τ (χ - χ.conj))
    (htau1_mem0 : tau1 (χ - 0) ∈ ZIrr G)
    (htau1_mema : tau1 (χ - a • chi1) ∈ ZIrr G)
    (hχχ1 : ClassFunction.inner χ chi1 = 0)
    (hχbarχ1 : ClassFunction.inner χ.conj chi1 = 0)
    (hχχbar : ClassFunction.inner χ χ.conj = 0) :
    CharacterPsiDecomposition (L := L) (G := G) τ χ 0 ×
      CharacterPsiDecomposition (L := L) (G := G) τ χ (a • chi1) :=
  -- `⟨χ, a·χ₁⟩ = a·⟨χ, χ₁⟩ = 0` (nsmul pulls out of the second slot, conjugate of a real `a`).
  have hχaχ1 : ClassFunction.inner χ (a • chi1 : ClassFunction L ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a chi1, OddOrder.RepresentationTheory.inner_smul_right,
      hχχ1, mul_zero]
  have hχbaraχ1 : ClassFunction.inner χ.conj (a • chi1 : ClassFunction L ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a chi1, OddOrder.RepresentationTheory.inner_smul_right,
      hχbarχ1, mul_zero]
  -- The two per-`ψ` sponsoring lattices `{χ, χ̄, ψ}` (`ψ = 0` resp. `a·χ₁`) both sit inside the
  -- shared lattice `{χ, χ̄, 0, a·χ₁}`, so the lattice-relative inner-preservation specializes by
  -- `Submodule.span_mono`.  This is exactly how the Dade isometry supplies both decompositions:
  -- one preservation fact on the supported span covers every difference generator.
  -- Each per-`ψ` *difference* sublattice `ℤ[χ−χ̄, χ−ψ]` sits inside the shared (supported) span
  -- `ℤ[χ, χ̄, 0, a·χ₁]` (its generators `χ−χ̄`, `χ−ψ` are differences of the shared generators), so
  -- the full inner-preservation restricts to it.
  have hle0 : zSpan (L := L) ({χ - χ.conj, χ - 0} : Set (ClassFunction L ℂ)) ≤
      zSpan (L := L) ({χ, χ.conj, 0, a • chi1} : Set (ClassFunction L ℂ)) :=
    Submodule.span_le.mpr (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;>
        exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp)))
  have hlea : zSpan (L := L) ({χ - χ.conj, χ - a • chi1} : Set (ClassFunction L ℂ)) ≤
      zSpan (L := L) ({χ, χ.conj, 0, a • chi1} : Set (ClassFunction L ℂ)) :=
    Submodule.span_le.mpr (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;>
        exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp)))
  (ofProjection imageFamily tau1
      (fun φ ζ hφ hζ => htau1_inner_eq φ ζ (hle0 hφ) (hle0 hζ))
      htau1_agrees htau1_mem0
      (by rw [ClassFunction.inner_zero_right]) (by rw [ClassFunction.inner_zero_right]) hχχbar,
    ofProjection imageFamily tau1
      (fun φ ζ hφ hζ => htau1_inner_eq φ ζ (hlea hφ) (hlea hζ))
      htau1_agrees htau1_mema hχaχ1 hχbaraχ1 hχχbar)

/-- The two decompositions produced by `decompositionPair` share their auxiliary isometry: their
`tau1` fields are literally the same `tau1`, so `Da.tau1 χ = D₀.tau1 χ` is `rfl`.  This is the
honest τ₁-agreement `htau1_chi` input of `retarget_isCoherent_of_decompositions`, discharged
structurally rather than posited. -/
theorem decompositionPair_tau1_agree {a : ℕ} {chi1 : ClassFunction L ℂ}
    (imageFamily : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ)
    (tau1 : IntegralCharacterMap L G)
    (htau1_inner_eq : ∀ φ ζ : ClassFunction L ℂ,
      φ ∈ zSpan (L := L) {χ, χ.conj, 0, a • chi1} →
      ζ ∈ zSpan (L := L) {χ, χ.conj, 0, a • chi1} →
      ClassFunction.inner (tau1 φ) (tau1 ζ) = ClassFunction.inner φ ζ)
    (htau1_agrees : tau1 (χ - χ.conj) = τ (χ - χ.conj))
    (htau1_mem0 : tau1 (χ - 0) ∈ ZIrr G)
    (htau1_mema : tau1 (χ - a • chi1) ∈ ZIrr G)
    (hχχ1 : ClassFunction.inner χ chi1 = 0)
    (hχbarχ1 : ClassFunction.inner χ.conj chi1 = 0)
    (hχχbar : ClassFunction.inner χ χ.conj = 0) :
    ((decompositionPair imageFamily tau1 htau1_inner_eq htau1_agrees htau1_mem0 htau1_mema
        hχχ1 hχbarχ1 hχχbar).2).tau1 χ =
      ((decompositionPair imageFamily tau1 htau1_inner_eq htau1_agrees htau1_mem0 htau1_mema
        hχχ1 hχbarχ1 hχχbar).1).tau1 χ :=
  rfl

omit [Fintype L] in
/-- `χ - χ̄ ∈ ℤ[χ−χ̄, χ−ψ]`: the difference sublattice contains the conjugate difference (it is a
generator). -/
theorem chi_sub_conj_mem_zSpan_support :
    χ - χ.conj ∈ zSpan (L := L) {χ - χ.conj, χ - ψ} :=
  Submodule.subset_span (by simp)

omit [Fintype L] in
/-- `χ - ψ ∈ ℤ[χ−χ̄, χ−ψ]`: the difference sublattice contains the `ψ`-difference (it is a
generator). -/
theorem chi_sub_psi_mem_zSpan_support :
    χ - ψ ∈ zSpan (L := L) {χ - χ.conj, χ - ψ} :=
  Submodule.subset_span (by simp)

/-- `⟨X, α⟩ = coeff α` for `α ∈ R(χ)` (orthonormal coefficient recovery). -/
theorem inner_X_eq_coeff (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    {α : ClassFunction G ℂ} (hα : α ∈ D.imageFamily.imageSet) :
    ClassFunction.inner D.X α = (D.coeff α : ℂ) := by
  rw [D.X_eq]
  exact inner_orthonormalSum_eq_coeff D.imageFamily.orthonormal hα

/-- `‖X‖² = ∑_{α ∈ R(χ)} (coeff α)²` (Parseval). -/
theorem inner_self_X (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner D.X D.X = ∑ α ∈ D.imageFamily.imageSet, (D.coeff α : ℂ) ^ 2 := by
  rw [D.X_eq]
  exact inner_self_orthonormalSum_eq_sum_sq D.imageFamily.orthonormal

/-- `⟨X, ∑_{α ∈ R(χ)} α⟩ = ∑_{α ∈ R(χ)} coeff α`. -/
theorem inner_X_sum (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner D.X (∑ α ∈ D.imageFamily.imageSet, α) =
      ∑ α ∈ D.imageFamily.imageSet, (D.coeff α : ℂ) := by
  rw [D.X_eq]
  exact inner_orthonormalSum_sum_eq_sum_coeff D.imageFamily.orthonormal

/-- `Y ⊥ R(χ)` extends to the sum: `⟨Y, ∑_{α ∈ R(χ)} α⟩ = 0`. -/
theorem inner_Y_sum (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner D.Y (∑ α ∈ D.imageFamily.imageSet, α) = 0 := by
  rw [inner_sum_right]
  exact Finset.sum_eq_zero fun α hα => D.Y_orthogonal α hα

/-- **The keystone identity of (5.4.a).**  `‖χ‖² = ∑_{α ∈ R(χ)} coeff α`.

`‖χ‖² = ⟨χ - ψ, χ - χ̄⟩` (using the three orthogonality relations), `= ⟨X - Y, ∑ α⟩`
(by the isometry of `τ₁` and `τ₁ = τ` on `χ - χ̄`), `= ⟨X, ∑ α⟩` (since `Y ⊥ R(χ)`),
`= ∑ coeff α`. -/
theorem inner_self_chi_eq_sum_coeff
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner χ χ = ∑ α ∈ D.imageFamily.imageSet, (D.coeff α : ℂ) := by
  -- Step 1: `⟨χ, χ⟩ = ⟨χ - ψ, χ - χ̄⟩`.
  have hpsi_chi : ClassFunction.inner ψ χ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, D.chi_psi_orthogonal, star_zero]
  have hpsi_chiConj : ClassFunction.inner ψ χ.conj = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, D.chiConj_psi_orthogonal, star_zero]
  have hsrc : ClassFunction.inner χ χ =
      ClassFunction.inner (χ - ψ) (χ - χ.conj) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, D.chi_chiConj_orthogonal, hpsi_chi, hpsi_chiConj]
    ring
  -- Step 2: transport across `τ₁` (isometry, agreeing with `τ` on `χ - χ̄`).
  have himg : ClassFunction.inner (χ - ψ) (χ - χ.conj) =
      ClassFunction.inner (D.X - D.Y) (∑ α ∈ D.imageFamily.imageSet, α) := by
    rw [← D.tau1_inner_eq_on_support (χ - ψ) (χ - χ.conj)
        chi_sub_psi_mem_zSpan_support chi_sub_conj_mem_zSpan_support,
      D.tau1_image, D.tau1_agrees, D.imageFamily.image_eq]
  -- Step 3: `Y ⊥ R(χ)` drops `Y`; coefficient recovery finishes.
  rw [hsrc, himg, ClassFunction.inner_sub_left, D.inner_Y_sum, sub_zero, D.inner_X_sum]

/-- **Peterfalvi (5.4.a):** `‖X‖² ≥ ‖χ‖²`.

By the keystone identity `‖χ‖² = ∑ coeff α` and Parseval `‖X‖² = ∑ (coeff α)²`, the
integer Cauchy–Schwarz `∑ coeff α ≤ ∑ (coeff α)²` gives the inequality. -/
theorem inner_self_chi_re_le_inner_self_X
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    (ClassFunction.inner χ χ).re ≤ (ClassFunction.inner D.X D.X).re := by
  classical
  have hχ : ClassFunction.inner χ χ =
      ((∑ α ∈ D.imageFamily.imageSet, D.coeff α : ℤ) : ℂ) := by
    rw [D.inner_self_chi_eq_sum_coeff]; push_cast; ring
  have hX : ClassFunction.inner D.X D.X =
      ((∑ α ∈ D.imageFamily.imageSet, (D.coeff α) ^ 2 : ℤ) : ℂ) := by
    rw [D.inner_self_X]; push_cast; ring
  rw [hχ, hX, Complex.intCast_re, Complex.intCast_re]
  exact_mod_cast finset_sum_le_sum_sq D.imageFamily.imageSet D.coeff

/-- `⟨χ, χ⟩` is the integer cast `(∑ coeff α : ℤ)`. -/
theorem inner_self_chi_eq_intCast
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner χ χ = ((∑ α ∈ D.imageFamily.imageSet, D.coeff α : ℤ) : ℂ) := by
  rw [D.inner_self_chi_eq_sum_coeff]; push_cast; ring

/-- `⟨X, X⟩` is the integer cast `(∑ (coeff α)² : ℤ)`. -/
theorem inner_self_X_eq_intCast
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner D.X D.X = ((∑ α ∈ D.imageFamily.imageSet, (D.coeff α) ^ 2 : ℤ) : ℂ) := by
  rw [D.inner_self_X]; push_cast; ring

/-- `X ⊥ Y`: `⟨X, Y⟩ = 0` (since `X ∈ ℤ[R(χ)]` and `Y ⊥ R(χ)`). -/
theorem inner_X_Y (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner D.X D.Y = 0 := by
  rw [D.X_eq, inner_sum_left]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [ClassFunction.inner_smul_left,
    OddOrder.RepresentationTheory.inner_conj_symm, D.Y_orthogonal α hα, star_zero, mul_zero]

/-- `‖X - Y‖² = ‖X‖² + ‖Y‖²` (Pythagoras, since `X ⊥ Y`). -/
theorem inner_self_X_sub_Y (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner (D.X - D.Y) (D.X - D.Y) =
      ClassFunction.inner D.X D.X + ClassFunction.inner D.Y D.Y := by
  have hYX : ClassFunction.inner D.Y D.X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, D.inner_X_Y, star_zero]
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, D.inner_X_Y, hYX]
  ring

/-- `‖χ - ψ‖² = ‖χ‖² + ‖ψ‖²` (Pythagoras, since `(χ, ψ) = (ψ, χ) = 0`). -/
theorem inner_self_chi_sub_psi (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner (χ - ψ) (χ - ψ) =
      ClassFunction.inner χ χ + ClassFunction.inner ψ ψ := by
  have hpsi_chi : ClassFunction.inner ψ χ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, D.chi_psi_orthogonal, star_zero]
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, D.chi_psi_orthogonal, hpsi_chi]
  ring

/-- The total-norm identity `‖χ‖² + ‖ψ‖² = ‖X‖² + ‖Y‖²` from the isometry of `τ₁`. -/
theorem inner_self_chi_add_psi_eq
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner χ χ + ClassFunction.inner ψ ψ =
      ClassFunction.inner D.X D.X + ClassFunction.inner D.Y D.Y := by
  rw [← D.inner_self_chi_sub_psi, ← D.inner_self_X_sub_Y, ← D.tau1_image,
    D.tau1_inner_eq_on_support (χ - ψ) (χ - ψ)
      chi_sub_psi_mem_zSpan_support chi_sub_psi_mem_zSpan_support]

/-- **Peterfalvi (5.6.2) opening bound:** `‖Y‖² ≤ ‖ψ‖²`.

This is the first step of (5.6.2) ("We note first that `‖χ‖² + a²‖χ₁‖² = ‖X‖² + ‖Y‖²`;
by (5.4.a) `‖X‖² ≥ ‖χ‖²`, so `‖Y‖² ≤ a²‖χ₁‖²`").  It follows directly from the total-norm
identity `‖χ‖² + ‖ψ‖² = ‖X‖² + ‖Y‖²` and (5.4.a) `‖χ‖² ≤ ‖X‖²`, with `ψ = a·χ₁` in the
application.  Stated for the general `ψ` of the (5.4) decomposition. -/
theorem inner_self_Y_re_le_inner_self_psi
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    (ClassFunction.inner D.Y D.Y).re ≤ (ClassFunction.inner ψ ψ).re := by
  have htotal : (ClassFunction.inner χ χ).re + (ClassFunction.inner ψ ψ).re =
      (ClassFunction.inner D.X D.X).re + (ClassFunction.inner D.Y D.Y).re := by
    have := congrArg Complex.re D.inner_self_chi_add_psi_eq
    simpa [Complex.add_re] using this
  have hXge := D.inner_self_chi_re_le_inner_self_X
  linarith

/-- **Peterfalvi (5.4.b).**  If `‖Y‖² ≥ ‖ψ‖²`, then `‖X‖² = ‖χ‖²`, `‖Y‖² = ‖ψ‖²`
and `X = ∑_{α ∈ E} α` for some `E ⊆ R(χ)` with `|E| = ‖χ‖²`.

The total-norm identity `‖χ‖² + ‖ψ‖² = ‖X‖² + ‖Y‖²` together with `‖X‖² ≥ ‖χ‖²`
(5.4.a) and the hypothesis `‖Y‖² ≥ ‖ψ‖²` forces both inequalities to be equalities.
The norm equality `‖χ‖² = ‖X‖²` reads `∑ coeff α = ∑ (coeff α)²`, so by the tightness
of integer Cauchy–Schwarz each `coeff α ∈ {0, 1}`; then `E = {α | coeff α = 1}` and
`X = ∑_{α ∈ E} α`.  The cardinality `|E| = ∑ coeff α = ‖χ‖²` is the form used in
(5.6.3) to compute `‖χ̄^{τ₂}‖² = |R(χ)| - |E| = ‖χ - χ̄‖² - ‖χ‖² = ‖χ̄‖²`. -/
theorem norm_eq_and_X_eq_sum_of_norm_Y_ge
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    (hY : (ClassFunction.inner ψ ψ).re ≤ (ClassFunction.inner D.Y D.Y).re) :
    (ClassFunction.inner χ χ).re = (ClassFunction.inner D.X D.X).re ∧
      (ClassFunction.inner ψ ψ).re = (ClassFunction.inner D.Y D.Y).re ∧
      ∃ E ⊆ D.imageFamily.imageSet, D.X = ∑ α ∈ E, α ∧
        (E.card : ℂ) = ClassFunction.inner χ χ := by
  classical
  -- The `.re` total-norm identity.
  have htotal : (ClassFunction.inner χ χ).re + (ClassFunction.inner ψ ψ).re =
      (ClassFunction.inner D.X D.X).re + (ClassFunction.inner D.Y D.Y).re := by
    have := congrArg Complex.re D.inner_self_chi_add_psi_eq
    simpa [Complex.add_re] using this
  have hXge := D.inner_self_chi_re_le_inner_self_X
  -- Both inequalities are forced to equalities.
  have hχX : (ClassFunction.inner χ χ).re = (ClassFunction.inner D.X D.X).re := by linarith
  have hψY : (ClassFunction.inner ψ ψ).re = (ClassFunction.inner D.Y D.Y).re := by linarith
  refine ⟨hχX, hψY, ?_⟩
  -- Tightness: `∑ coeff = ∑ coeff²` as integers.
  have hsum_eq : (∑ α ∈ D.imageFamily.imageSet, D.coeff α) =
      ∑ α ∈ D.imageFamily.imageSet, (D.coeff α) ^ 2 := by
    have h1 := hχX
    rw [D.inner_self_chi_eq_intCast, D.inner_self_X_eq_intCast,
      Complex.intCast_re, Complex.intCast_re] at h1
    exact_mod_cast h1
  have hcoeff01 : ∀ α ∈ D.imageFamily.imageSet, D.coeff α = 0 ∨ D.coeff α = 1 :=
    (finset_sum_eq_sum_sq_iff D.imageFamily.imageSet D.coeff).mp hsum_eq
  -- `E = {α | coeff α = 1}`.
  set E := D.imageFamily.imageSet.filter (fun α => D.coeff α = 1) with hE
  refine ⟨E, Finset.filter_subset _ _, ?_, ?_⟩
  · -- `X = ∑_{α ∈ E} α`.
    rw [D.X_eq, hE, Finset.sum_filter]
    refine Finset.sum_congr rfl fun α hα => ?_
    rcases hcoeff01 α hα with h0 | h1
    · rw [h0, if_neg (by norm_num), Int.cast_zero, zero_smul]
    · rw [h1, if_pos rfl, Int.cast_one, one_smul]
  · -- `|E| = ∑ coeff α = ‖χ‖²`: on `R(χ)`, `coeff α = (if coeff α = 1 then 1 else 0)`.
    have hcard : (E.card : ℤ) = ∑ α ∈ D.imageFamily.imageSet, D.coeff α := by
      rw [hE, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      rcases hcoeff01 α hα with h0 | h1
      · rw [h0, if_neg (by norm_num), Nat.cast_zero]
      · rw [h1, if_pos rfl, Nat.cast_one]
    rw [D.inner_self_chi_eq_intCast]
    exact_mod_cast hcard

/-- **Peterfalvi (5.5).**  Applying (5.4) with `ψ = 0`: the hypothesis `‖Y‖² ≥ ‖ψ‖² = 0`
of (5.4.b) holds automatically (the inner product is positive semidefinite), so `Y = 0`
and `χ^{τ₁} = X = ∑_{α ∈ E} α` for some `E ⊆ R(χ)` with `|E| = ‖χ‖²`.

`‖ψ‖² = ⟨0, 0⟩ = 0 ≤ ‖Y‖²` feeds (5.4.b), whose norm equality `‖Y‖² = ‖ψ‖² = 0` forces
`Y = 0` by positive definiteness of `ClassFunction.inner`.  Then
`χ^{τ₁} = (χ - 0)^{τ₁} = X - Y = X`. -/
theorem eq_sum_of_psi_eq_zero
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ 0) :
    D.Y = 0 ∧ D.tau1 χ = D.X ∧
      ∃ E ⊆ D.imageFamily.imageSet, D.X = ∑ α ∈ E, α ∧
        (E.card : ℂ) = ClassFunction.inner χ χ := by
  -- `‖ψ‖² = ‖0‖² = 0 ≤ ‖Y‖²` by positive semidefiniteness.
  have hψY : (ClassFunction.inner (0 : ClassFunction L ℂ) 0).re ≤
      (ClassFunction.inner D.Y D.Y).re := by
    rw [ClassFunction.inner_zero_left, Complex.zero_re]
    exact inner_self_re_nonneg D.Y
  obtain ⟨_, hYnorm, E, hEsub, hXsum, hEcard⟩ := D.norm_eq_and_X_eq_sum_of_norm_Y_ge hψY
  -- `‖Y‖² = ‖0‖² = 0`, so `Y = 0` by positive definiteness.
  have hY0 : D.Y = 0 := by
    apply eq_zero_of_inner_self_re_eq_zero
    rw [← hYnorm, ClassFunction.inner_zero_left, Complex.zero_re]
  -- `χ^{τ₁} = (χ - 0)^{τ₁} = X - Y = X`.
  have hτ1χ : D.tau1 χ = D.X := by
    have := D.tau1_image
    rw [sub_zero] at this
    rw [this, hY0, sub_zero]
  exact ⟨hY0, hτ1χ, E, hEsub, hXsum, hEcard⟩

end CharacterPsiDecomposition

/-- Peterfalvi (5.1): `τ` is coherent for `(S,A)` if it admits an integral
extension on `Z[S]` that is **isometric on the lattice `Z[S]`** and agrees with
`τ` on `Z[S,A]`.

The isometry hypothesis is **lattice-relative** (`extension_inner_eq`, restricted
to `φ, ψ ∈ Z[S] = zSpan S`), not a global `IsIntegralIsometry` on all of `CF(L)`.
This is the object Peterfalvi actually constructs in (5.6): in Feit–Thompson
`dim CF(L) > dim CF(G)`, so a global isometry of the character-difference lattice
into `CF(G)` generically does not exist, but the lattice-relative one
(`retarget_inner_eq_on`) does.  Every downstream consumer uses only the
inner-product preservation on lattice elements `ζ ∈ S ⊆ Z[S]`. -/
structure IsCoherent (τ : IntegralCharacterMap L G)
    (S : Set (ClassFunction L ℂ)) (A : Set L)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  nonzero : ∃ φ : ClassFunction L ℂ, φ ∈ zSupportedSpan (L := L) S A ∧ φ ≠ 0
  extension : IntegralCharacterMap L G
  extension_inner_eq :
    ∀ φ ψ : ClassFunction L ℂ, φ ∈ zSpan (L := L) S → ψ ∈ zSpan (L := L) S →
      ClassFunction.inner (extension φ) (extension ψ) = ClassFunction.inner φ ψ
  extends_on_supported :
    ∀ φ : ClassFunction L ℂ, φ ∈ zSupportedSpan (L := L) S A → extension φ = τ φ
  /-- The coherent extension sends the **coherent lattice** `ℤ[S]` into `ℤ[Irr G]`.

  Peterfalvi's coherent isometries are genuine virtual-character maps *on the coherent set*: the
  (5.6.3) running extension is built by `retarget` from virtual-character target pairs
  `{X, X̄} ⊂ ℤ[Irr G]`, sending each member of `S` to a virtual character.  (It is *not* claimed on
  all of `ℤ[Irr L]` — the base Dade map is only an isometry on the supported lattice, not a global
  `ℤ[Irr]`-endomorphism.)  This is the **ZIrr-codomain** the (6.6)/(6.8) `X`-chain needs: for an
  irreducible member `χⱼ ∈ S`, `χⱼ ∈ ℤ[S]` gives `ν χⱼ ∈ ZIrr`, the load-bearing input of
  `crux1_of_memberFamily`. -/
  extension_mem_ZIrr : ∀ φ : ClassFunction L ℂ, φ ∈ zSpan (L := L) S → extension φ ∈ ZIrr G

namespace IsCoherent

variable {τ : IntegralCharacterMap L G} {S : Set (ClassFunction L ℂ)} {A : Set L}
variable [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

theorem exists_nonzero_supported (hτ : IsCoherent τ S A) :
    ∃ φ : ClassFunction L ℂ, φ ∈ zSupportedSpan (L := L) S A ∧ φ ≠ 0 :=
  hτ.nonzero

theorem extension_agrees (hτ : IsCoherent τ S A)
    {φ : ClassFunction L ℂ} (hφ : φ ∈ zSupportedSpan (L := L) S A) :
    hτ.extension φ = τ φ :=
  hτ.extends_on_supported φ hφ

theorem inner_eq_on_supported (hτ : IsCoherent τ S A)
    {φ ψ : ClassFunction L ℂ}
    (hφ : φ ∈ zSupportedSpan (L := L) S A)
    (hψ : ψ ∈ zSupportedSpan (L := L) S A) :
    ClassFunction.inner (τ φ) (τ ψ) = ClassFunction.inner φ ψ := by
  rw [← hτ.extension_agrees hφ, ← hτ.extension_agrees hψ]
  exact hτ.extension_inner_eq φ ψ hφ.1 hψ.1

/-- Coherence is invariant under coefficientwise automorphisms that commute with `star`.

The coherent set is transported to `σS`, and the base map is conjugated as
`σ ∘ τ ∘ σ⁻¹`.  This is the reusable Galois-coherence transport needed by Peterfalvi
(5.9.a)-style arguments; it does not assume a capstone-specific theorem about which
irreducible characters form the set. -/
def galoisTransport (hτ : IsCoherent τ S A) (σ : ℂ ≃+* ℂ)
    (hσ : ∀ z : ℂ, σ (star z) = star (σ z)) :
    IsCoherent (IntegralCharacterMap.galoisTransport (L := L) (G := G) σ τ)
      (ClassFunction.mapRingEquiv σ '' S) A := by
  classical
  have hσsymm : ∀ z : ℂ, σ.symm (star z) = star (σ.symm z) := by
    intro z
    apply σ.injective
    rw [RingEquiv.apply_symm_apply, hσ, RingEquiv.apply_symm_apply]
  refine
    { nonzero := ?_
      extension := IntegralCharacterMap.galoisTransport (L := L) (G := G) σ hτ.extension
      extension_inner_eq := ?_
      extends_on_supported := ?_
      extension_mem_ZIrr := ?_ }
  · rcases hτ.nonzero with ⟨φ, hφ, hφne⟩
    exact ⟨ClassFunction.mapRingEquiv σ φ,
      ClassFunction.mapRingEquiv_mem_zSupportedSpan_image σ hφ,
      (ClassFunction.mapRingEquiv_ne_zero_iff σ φ).mpr hφne⟩
  · intro φ ψ hφ hψ
    have hφ' : ClassFunction.mapRingEquiv σ.symm φ ∈ zSpan (L := L) S :=
      ClassFunction.mapRingEquiv_symm_mem_zSpan_of_mem_image σ hφ
    have hψ' : ClassFunction.mapRingEquiv σ.symm ψ ∈ zSpan (L := L) S :=
      ClassFunction.mapRingEquiv_symm_mem_zSpan_of_mem_image σ hψ
    calc
      ClassFunction.inner
          (IntegralCharacterMap.galoisTransport (L := L) (G := G) σ hτ.extension φ)
          (IntegralCharacterMap.galoisTransport (L := L) (G := G) σ hτ.extension ψ)
          = σ (ClassFunction.inner
              (hτ.extension (ClassFunction.mapRingEquiv σ.symm φ))
              (hτ.extension (ClassFunction.mapRingEquiv σ.symm ψ))) := by
            rw [IntegralCharacterMap.galoisTransport_apply,
              IntegralCharacterMap.galoisTransport_apply,
              ClassFunction.mapRingEquiv_inner σ hσ]
      _ = σ (ClassFunction.inner (ClassFunction.mapRingEquiv σ.symm φ)
              (ClassFunction.mapRingEquiv σ.symm ψ)) := by
            rw [hτ.extension_inner_eq _ _ hφ' hψ']
      _ = ClassFunction.inner φ ψ := by
            rw [← ClassFunction.mapRingEquiv_inner (G := L) σ hσ
              (ClassFunction.mapRingEquiv σ.symm φ) (ClassFunction.mapRingEquiv σ.symm ψ)]
            simp
  · intro φ hφ
    have hφ' : ClassFunction.mapRingEquiv σ.symm φ ∈ zSupportedSpan (L := L) S A :=
      ClassFunction.mapRingEquiv_symm_mem_zSupportedSpan_of_mem_image σ hφ
    rw [IntegralCharacterMap.galoisTransport_apply, IntegralCharacterMap.galoisTransport_apply,
      hτ.extends_on_supported _ hφ']
  · -- extension_mem_ZIrr: `σ` carries `ℤ[σS] →[σ⁻¹] ℤ[S] →[ν] ℤ[Irr G] →[σ] ℤ[Irr G]`.
    intro φ hφ
    rw [IntegralCharacterMap.galoisTransport_apply]
    exact ClassFunction.mapRingEquiv_mem_ZIrr σ
      (hτ.extension_mem_ZIrr _ (ClassFunction.mapRingEquiv_symm_mem_zSpan_of_mem_image σ hφ))

end IsCoherent

/-- Peterfalvi (5.2)-style hypotheses for coherence applications.  This is a
carrier for later theorems, not a proof that the hypotheses hold in any
particular Dade situation. -/
structure Hypothesis (S : Set (ClassFunction L ℂ)) (A : Set L)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  tau : IntegralCharacterMap L G
  /-- **Lattice-relative (5.2)(b) isometry on the `A`-supported sublattice** (issues 9001, 0099):
  `τ` preserves inner products on `ℤ[S, A] = {f ∈ ℤ[S] | supp f ⊆ A}` — Coq `subcoherent`
  clause (b) `{in 'Z[S, L^#], isometry tau}` (`PFsection5.v:488`).  A *global* `IsIntegralIsometry`
  does **not** exist for the Feit–Thompson Dade map (`dim CF(L) > dim CF(G)`), and the pre-0099
  all-member-difference form is **false** for mixed-degree families (`a − b` with `a(1) ≠ b(1)` is
  not `A`-supported) — while every extension mechanism ((5.4)/(5.6)/(5.7)/(5.9a)) only ever
  consumes `A`-supported `ℤ`-combinations.  The Dade witnesses supply this field *unconditionally*
  (any family, mixed degrees included) via `dadeIntegralCharacterMap_inner_eq_of_supported`;
  member-difference consumers use the derived `tau_isometry_memberDiff`. -/
  tau_isometry_diff : ∀ ⦃φ ψ : ClassFunction L ℂ⦄,
    φ ∈ zSupportedSpan (L := L) S A → ψ ∈ zSupportedSpan (L := L) S A →
    ClassFunction.inner (tau φ) (tau ψ) = ClassFunction.inner φ ψ
  conjugate_closed : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S
  no_real_characters : OddOrder.Peterfalvi.S03.HasNoRealCharacters S
  pairwise_orthogonal : OddOrder.Peterfalvi.S03.PairwiseOrthogonal S
  difference_image :
    ∀ ⦃χ : ClassFunction L ℂ⦄, χ ∈ S → CharacterDifferenceImage (L := L) (G := G) tau χ
  difference_images_orthogonal :
    ∀ ⦃φ χ : ClassFunction L ℂ⦄ (hφ : φ ∈ S) (hχ : χ ∈ S),
      ClassFunction.inner φ χ = 0 → ClassFunction.inner φ χ.conj = 0 →
        (difference_image hφ).Orthogonal (difference_image hχ)

namespace Hypothesis

variable {S : Set (ClassFunction L ℂ)} {A : Set L}
variable [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- The map carried by a §7 hypothesis, as a coherence predicate target. -/
abbrev IsCoherentTarget (hyp : Hypothesis (L := L) (G := G) S A) :=
  IsCoherent hyp.tau S A

/-- **Member-difference form of the (5.2)(b) lattice isometry** (the pre-0099 field shape, now
derived).  For members `a, b, c, d ∈ S` whose differences are `A`-supported, `τ` preserves
`⟨a − b, c − d⟩`: such differences lie in `ℤ[S, A]`, where `tau_isometry_diff` applies.
Equal-degree consumers discharge the support inputs from `a(1) = b(1)` (the difference vanishes at
`1` and off the family support). -/
theorem tau_isometry_memberDiff (hyp : Hypothesis (L := L) (G := G) S A)
    ⦃a b c d : ClassFunction L ℂ⦄ (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : ((a - b : ClassFunction L ℂ)).support ⊆ A)
    (hcd : ((c - d : ClassFunction L ℂ)).support ⊆ A) :
    ClassFunction.inner (hyp.tau (a - b)) (hyp.tau (c - d))
      = ClassFunction.inner (a - b) (c - d) :=
  hyp.tau_isometry_diff
    ⟨Submodule.sub_mem _ (Submodule.subset_span ha) (Submodule.subset_span hb), hab⟩
    ⟨Submodule.sub_mem _ (Submodule.subset_span hc) (Submodule.subset_span hd), hcd⟩

/-- The signed irreducible-difference image of `χ - χ̄` supplied by a §7
hypothesis. -/
theorem difference_image_eq {hyp : Hypothesis (L := L) (G := G) S A}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    hyp.tau (OddOrder.Peterfalvi.S03.conjugateDifference χ) =
      (hyp.difference_image hχ).sign •
        ((hyp.difference_image hχ).muClassFunction -
          (hyp.difference_image hχ).nuClassFunction) :=
  (hyp.difference_image hχ).image_conjugateDifference

theorem difference_image_ne_zero {hyp : Hypothesis (L := L) (G := G) S A}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    hyp.tau (OddOrder.Peterfalvi.S03.conjugateDifference χ) ≠ 0 :=
  (hyp.difference_image hχ).image_conjugateDifference_ne_zero

theorem signed_difference_image_ne_zero {hyp : Hypothesis (L := L) (G := G) S A}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    (hyp.difference_image hχ).sign •
        ((hyp.difference_image hχ).muClassFunction -
          (hyp.difference_image hχ).nuClassFunction) ≠ 0 :=
  (hyp.difference_image hχ).signed_image_ne_zero

theorem conjugate_mem {hyp : Hypothesis (L := L) (G := G) S A}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    χ.conj ∈ S :=
  hyp.conjugate_closed hχ

theorem not_isReal {hyp : Hypothesis (L := L) (G := G) S A}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    ¬ χ.IsReal :=
  hyp.no_real_characters hχ

theorem ne_conj {hyp : Hypothesis (L := L) (G := G) S A}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    χ ≠ χ.conj := by
  intro hχ_eq
  exact hyp.not_isReal hχ hχ_eq.symm

theorem conjugateDifference_ne_zero {hyp : Hypothesis (L := L) (G := G) S A}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    OddOrder.Peterfalvi.S03.conjugateDifference χ ≠ 0 :=
  (OddOrder.Peterfalvi.S03.conjugateDifference_ne_zero_iff_not_isReal χ).mpr
    (hyp.not_isReal hχ)

theorem difference_images_orthogonal_of_inner_pair
    {hyp : Hypothesis (L := L) (G := G) S A}
    {φ χ : ClassFunction L ℂ} (hφ : φ ∈ S) (hχ : χ ∈ S)
    (hφχ : ClassFunction.inner φ χ = 0)
    (hφχ_conj : ClassFunction.inner φ χ.conj = 0) :
    (hyp.difference_image hφ).Orthogonal (hyp.difference_image hχ) :=
  hyp.difference_images_orthogonal hφ hχ hφχ hφχ_conj

theorem difference_image_inner_self
    {hyp : Hypothesis (L := L) (G := G) S A}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    ClassFunction.inner
        (hyp.tau (OddOrder.Peterfalvi.S03.conjugateDifference χ))
        (hyp.tau (OddOrder.Peterfalvi.S03.conjugateDifference χ)) = 2 :=
  (hyp.difference_image hχ).image_conjugateDifference_inner_self

theorem difference_images_inner_eq_zero_of_inner_pair
    {hyp : Hypothesis (L := L) (G := G) S A}
    {φ χ : ClassFunction L ℂ} (hφ : φ ∈ S) (hχ : χ ∈ S)
    (hφχ : ClassFunction.inner φ χ = 0)
    (hφχ_conj : ClassFunction.inner φ χ.conj = 0) :
    ClassFunction.inner
        (hyp.tau (OddOrder.Peterfalvi.S03.conjugateDifference φ))
        (hyp.tau (OddOrder.Peterfalvi.S03.conjugateDifference χ)) = 0 :=
  CharacterDifferenceImage.Orthogonal.image_conjugateDifference_inner_eq_zero
    (hyp.difference_images_orthogonal_of_inner_pair hφ hχ hφχ hφχ_conj)

end Hypothesis

/-! ### Peterfalvi (5.6): the coherence-union theorem

`S₁ = {χ₁,…,χₙ}` is a conjugation-closed coherent subset of `S` and `{χ, χ̄}` is disjoint
from `S₁` with `χ₁(1) ∣ χ(1)` (write `χ(1) = a·χ₁(1)`).  Under the degree-ratio inequality
`2·χ(1)·χ₁(1) < ∑ᵢ χᵢ(1)²/‖χᵢ‖²`, the union `S₁ ∪ {χ, χ̄}` is coherent.

The proof runs through the (5.4)/(5.5) decomposition machinery: writing
`(χ - a·χ₁)^τ = X - Y` against the orthonormal `R(χ)`, the inequality forces the integer
coefficient `λ` of the orthogonal part `Y` to vanish (5.6.2), so `Y = a·χ₁^{τ₁}` (5.6.1) and
`X = ∑_{α ∈ E} α` for some `E ⊆ R(χ)` with `|E| = ‖χ‖²` (5.5/5.4.b); the extension `τ₂` with
`χ^{τ₂} = X`, `χ̄^{τ₂} = X - (χ - χ̄)^τ` is then the coherence witness. -/

/-- **Peterfalvi (5.6.2): the integer-forcing core.**

The quadratic inequality produced by the (5.6.2) norm computation forces `λ = 0`.  Concretely:
if `D` is a positive rational, `z ≥ 0`, `0 ≤ a`, the strict degree-ratio bound `2·a < D` holds,
and the integer `λ` satisfies `λ²·D - 2·λ·a + z ≤ 0`, then `λ = 0`.

This is exactly the step `λ² - bλ ≤ 0`, `0 < b < 1` (with `b = 2a/D`) `⟹ λ = 0` of the text,
kept division-free: the strict bound `2a < D` is the `b < 1` hypothesis and `0 ≤ a`, `0 < D`
give `0 < b`.  The slack term `z = ‖Z‖² ≥ 0` is carried so the caller need not drop it first. -/
theorem int_eq_zero_of_sq_mul_le_of_two_mul_lt
    {lam : ℤ} {D a z : ℚ}
    (hD : 0 < D) (hz : 0 ≤ z) (ha : 0 ≤ a) (hbnd : 2 * a < D)
    (hquad : (lam : ℚ) ^ 2 * D - 2 * (lam : ℚ) * a + z ≤ 0) :
    lam = 0 := by
  -- From `λ²·D - 2λa + z ≤ 0` and `z ≥ 0`: `λ²·D ≤ 2λa`.
  have hcore : (lam : ℚ) ^ 2 * D ≤ 2 * (lam : ℚ) * a := by linarith
  -- `λ ≠ 0` is impossible.
  by_contra hne
  have hne' : lam ≠ 0 := hne
  -- WLOG via cases on the sign of `λ`.
  rcases lt_trichotomy lam 0 with hneg | hzero | hpos
  · -- `λ < 0`: then `2λa ≤ 0 ≤ λ²·D` with `λ²·D > 0`, contradiction.
    have hlamR : (lam : ℚ) < 0 := by exact_mod_cast hneg
    have hsq_pos : 0 < (lam : ℚ) ^ 2 := by positivity
    have hlhs_pos : 0 < (lam : ℚ) ^ 2 * D := mul_pos hsq_pos hD
    have hrhs_nonpos : 2 * (lam : ℚ) * a ≤ 0 := by nlinarith [hlamR, ha]
    linarith
  · exact hne' hzero
  · -- `λ > 0`: divide `λ²·D ≤ 2λa` by `λ > 0` to get `λ·D ≤ 2a < D`, so `λ < 1`, contradiction.
    have hlamR : (0 : ℚ) < (lam : ℚ) := by exact_mod_cast hpos
    have hlam1 : (1 : ℚ) ≤ (lam : ℚ) := by
      have : (1 : ℤ) ≤ lam := hpos
      exact_mod_cast this
    -- `λ²·D = λ·(λ·D)` and `2λa = λ·(2a)`, cancel one `λ`.
    have hcancel : (lam : ℚ) * D ≤ 2 * a := by
      have h2 : (lam : ℚ) * ((lam : ℚ) * D) ≤ (lam : ℚ) * (2 * a) := by nlinarith [hcore]
      exact le_of_mul_le_mul_left h2 hlamR
    -- But `λ ≥ 1` gives `D ≤ λ·D ≤ 2a < D`, contradiction.
    have hDle : D ≤ (lam : ℚ) * D := by nlinarith [hlam1, hD]
    linarith

/-! ### Peterfalvi (6.6): the prime-power degree gap

(6.6) builds coherence of `X = {χ₁,…,χₙ}` (sorted, `χ₁(1) ≤ ⋯ ≤ χₙ(1)`) by *repeated use* of
(5.6) (the `coherentPairChain` engine).  Each step adjoins one degree class and needs the strict
degree-ratio bound `2·χᵢ(1)·χ₁(1) < ∑_{j<i} χⱼ(1)²` — exactly the `2·a < D` precondition of
`int_eq_zero_of_sq_mul_le_of_two_mul_lt`.

The mmd derives it (L80-82) from the prime-power structure: every `χⱼ(1) = |L:K|·θⱼ(1)` with
`θⱼ(1)` a power of `p`, so for `i` past the maximal same-degree index, `χᵢ(1) = q·χ₁(1)` with
`q = p^m` a non-trivial power of `p`; coprimality `(|L:K|, p) = 1` plus the sum identity force
`χᵢ(1)² ∣ ∑_{j<i} χⱼ(1)²`.  Since `|L|` is odd, `p ≥ 3`, whence

`2·χᵢ(1)·χ₁(1) < p·χᵢ(1)·χ₁(1) ≤ χᵢ(1)² ≤ ∑_{j<i} χⱼ(1)²`.

The three lemmas below isolate this number-theoretic content (over `ℕ`, then cast to `ℚ` for the
(5.6) core).  They are honest consequences of (6.6)'s data, not posited hypotheses: the prime-power
gap and the square-divisibility both come from the character-degree structure of `K` a `p`-group. -/

/-- **Peterfalvi (6.6): the prime-power degree gap (ℕ).**

If two character degrees `d₁ ≤ dᵢ` differ by a non-trivial power of an odd prime — `dᵢ = q·d₁`
with `q = p^m`, `p ≥ 3`, `d₁ < dᵢ` — then the doubled cross term `2·dᵢ·d₁` is strictly below the
square `dᵢ²`.

The text's chain (mmd L82) is `2·dᵢ·d₁ < p·dᵢ·d₁ ≤ dᵢ²`.  We extract the load-bearing fact that
`q > 1` is a power of `p`, hence `q ≥ p ≥ 3`, so `dᵢ = q·d₁ ≥ 3·d₁`; the strict inequality then
follows from `2·dᵢ·d₁ < 3·dᵢ·d₁ ≤ dᵢ²` (using `d₁ ≥ 1`). -/
theorem two_mul_lt_sq_of_primePow_gap
    {p d₁ dᵢ q m : ℕ} (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dᵢ = q * d₁) (hlt : d₁ < dᵢ) :
    2 * (dᵢ * d₁) < dᵢ * dᵢ := by
  -- `q > 1`: otherwise `dᵢ = q·d₁ ≤ d₁`, contradicting `d₁ < dᵢ`.
  have hq1 : 1 < q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · interval_cases q <;> simp_all
    · omega
  -- `q = p^m` with `q > 1` forces `m ≥ 1`, hence `p ≤ q`.
  have hpq : p ≤ q := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp at hq; omega
    · calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ m := Nat.pow_le_pow_right (by omega) hm
        _ = q := hq.symm
  -- `dᵢ = q·d₁ ≥ p·d₁ ≥ 3·d₁`.
  have hgap : 3 * d₁ ≤ dᵢ := by
    have h1 : 3 * d₁ ≤ p * d₁ := Nat.mul_le_mul_right _ hp
    have h2 : p * d₁ ≤ q * d₁ := Nat.mul_le_mul_right _ hpq
    omega
  nlinarith [hgap, hpos₁]

/-- **Peterfalvi (6.6): the common-index p-power degree gap (ℕ).**

This is the same strict gap as `two_mul_lt_sq_of_primePow_gap`, but in the exact
common-index form used in the §8 Sibley X-chain.  If
`d₁ = idx * p^m₁` and `dᵢ = idx * p^mᵢ` with `idx > 0`, `p ≥ 3`, and
`d₁ < dᵢ`, then the p-power residual of `dᵢ` is at least one factor of `p`
larger than the residual of `d₁`; hence `dᵢ ≥ 3 * d₁` and
`2 * dᵢ * d₁ < dᵢ^2`.

This removes the need to name a separate quotient `q = dᵢ / d₁` in the
consumer-facing §8 constructors. -/
theorem two_mul_lt_sq_of_commonIndex_primePower_gap
    {p idx θ₁ θᵢ d₁ dᵢ m₁ mᵢ : ℕ} (hp : 3 ≤ p) (hidx : 0 < idx)
    (hd₁ : d₁ = idx * θ₁) (hdᵢ : dᵢ = idx * θᵢ)
    (hθ₁ : θ₁ = p ^ m₁) (hθᵢ : θᵢ = p ^ mᵢ) (hlt : d₁ < dᵢ) :
    2 * (dᵢ * d₁) < dᵢ * dᵢ := by
  have hθlt : θ₁ < θᵢ := by
    rw [hd₁, hdᵢ] at hlt
    exact (Nat.mul_lt_mul_left hidx).mp hlt
  have hm_lt : m₁ < mᵢ := by
    rw [hθ₁, hθᵢ] at hθlt
    exact (Nat.pow_lt_pow_iff_right (show 1 < p by omega)).mp hθlt
  have hpθ : p * θ₁ ≤ θᵢ := by
    rw [hθ₁, hθᵢ]
    have hm_succ : m₁ + 1 ≤ mᵢ := Nat.succ_le_of_lt hm_lt
    calc
      p * p ^ m₁ = p ^ (m₁ + 1) := by
        rw [pow_succ']
      _ ≤ p ^ mᵢ := Nat.pow_le_pow_right (by omega) hm_succ
  have hgap : 3 * d₁ ≤ dᵢ := by
    rw [hd₁, hdᵢ]
    have h3θ : 3 * θ₁ ≤ θᵢ :=
      (Nat.mul_le_mul_right θ₁ hp).trans hpθ
    calc
      3 * (idx * θ₁) = idx * (3 * θ₁) := by ring
      _ ≤ idx * θᵢ := Nat.mul_le_mul_left idx h3θ
  have hd₁pos : 0 < d₁ := by
    rw [hd₁, hθ₁]
    exact Nat.mul_pos hidx (pow_pos (by omega) m₁)
  nlinarith [hgap, hd₁pos]

/-- **Peterfalvi (6.6): chaining the gap to the partial degree sum (ℕ).**

The gap `2·dᵢ·d₁ < dᵢ²` together with `dᵢ² ∣ D` (the square-divisibility `χᵢ(1)² ∣ ∑_{j<i}χⱼ(1)²`)
and `0 < D` gives `2·dᵢ·d₁ < D`: positivity upgrades the divisibility to `dᵢ² ≤ D`. -/
theorem two_mul_lt_of_sq_dvd_of_gap
    {d₁ dᵢ D : ℕ} (hgap : 2 * (dᵢ * d₁) < dᵢ * dᵢ)
    (hdvd : dᵢ * dᵢ ∣ D) (hDpos : 0 < D) :
    2 * (dᵢ * d₁) < D := by
  have : dᵢ * dᵢ ≤ D := Nat.le_of_dvd hDpos hdvd
  omega

/-- **Peterfalvi (6.6): the degree-ratio bound feeding (5.6) (ℚ).**

The consumer-facing form: from the prime-power gap data (`dᵢ = q·d₁`, `q = p^m`, `p ≥ 3`,
`d₁ < dᵢ`) and the square-divisibility `dᵢ² ∣ D` with `0 < D`, the strict bound
`2·(dᵢ·d₁) < D` holds in `ℚ`.  This is exactly the `2·a < D` precondition (`a = dᵢ·d₁`,
`D = ∑_{j<i}χⱼ(1)²`) of `int_eq_zero_of_sq_mul_le_of_two_mul_lt`, so each `coherentPairChain`
step's (5.6.2) integer-forcing has its degree hypothesis discharged from `ℕ` degree data. -/
theorem two_mul_degree_lt_sum_ratCast
    {p d₁ dᵢ q m D : ℕ} (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dᵢ = q * d₁) (hlt : d₁ < dᵢ)
    (hdvd : dᵢ * dᵢ ∣ D) (hDpos : 0 < D) :
    2 * ((dᵢ : ℚ) * (d₁ : ℚ)) < (D : ℚ) := by
  have hℕ : 2 * (dᵢ * d₁) < D :=
    two_mul_lt_of_sq_dvd_of_gap
      (two_mul_lt_sq_of_primePow_gap hp hpos₁ hq hdiv hlt) hdvd hDpos
  exact_mod_cast hℕ

/-! ### Peterfalvi (6.6): producing the square-divisibility `χᵢ(1)² ∣ ∑_{j<i}χⱼ(1)²`

The `hdvd` hypothesis of `two_mul_degree_lt_sum_ratCast` (`dᵢ² ∣ D`, i.e.
`χᵢ(1)² ∣ ∑_{j<i}χⱼ(1)²`) is itself produced by the number-theoretic chain of mmd L78-80:

* (L78, sum identity)  `∑_{j<i}χⱼ(1)² + ∑_{j≥i}χⱼ(1)² = |L| - |L:Z|`;
* (L80, p-power)       `θᵢ(1)²` (smallest among `j ≥ i`) divides `∑_{j≥i}χⱼ(1)²`, and by
                        [Is] Cor 2.30 `θᵢ(1)² ≤ |K:Z|` so `θᵢ(1)² ∣ |L| - |L:Z|`;
* (L80, combine)       hence `θᵢ(1)² ∣ ∑_{j<i}χⱼ(1)²` (the additive complement);
* (L80, coprime)       `(|L:K|, p) = 1` and `χᵢ(1) = |L:K|·θᵢ(1)` give `χᵢ(1)² ∣ ∑_{j<i}χⱼ(1)²`.

The arithmetic load-bearing steps below isolate the additive complement, coprimality forcing,
tail-sum divisibility, and total-side p-power divisibility.  They take honest divisibility data
(consequences of the character-degree structure; the sum identity is an *additive* equation,
sidestepping `ℕ` truncated subtraction) and are not posited. -/

/-- **Peterfalvi (6.6): additive complement of a divisor (ℕ).**

If `a` divides both the `tail` and the `total`, and `head + tail = total`, then `a ∣ head`.
This is the combination step of mmd L78+L80: with `head = ∑_{j<i}χⱼ(1)²`,
`tail = ∑_{j≥i}χⱼ(1)²`, `total = |L| - |L:Z|`, the divisibilities `θᵢ(1)² ∣ tail` and
`θᵢ(1)² ∣ total` give `θᵢ(1)² ∣ head`.  Stated additively to avoid `ℕ` subtraction. -/
theorem dvd_of_add_eq_of_dvd_dvd
    {a head tail total : ℕ} (hsum : head + tail = total)
    (htail : a ∣ tail) (htot : a ∣ total) :
    a ∣ head := by
  have h : a ∣ total - tail := Nat.dvd_sub htot htail
  rwa [show total - tail = head from by omega] at h

/-- **Peterfalvi (6.6): coprimality forcing of the full degree square (ℕ).**

The induced degree factors as `χᵢ(1) = idx·θ` (`idx = |L:K|`, `θ = θᵢ(1)`).  Given that both
`θ²` and `idx²` divide `D` and that `idx` is coprime to `θ` (mmd L80: `(|L:K|, p) = 1` with
`θ` a power of `p`), the full square `χᵢ(1)² = idx²·θ²` divides `D`.

`Coprime idx θ ⟹ Coprime idx² θ²`, and coprime divisors multiply: `idx²·θ² ∣ D`. -/
theorem sq_dvd_of_factored_coprime
    {idx θ chi D : ℕ} (hchi : chi = idx * θ)
    (hθ : θ * θ ∣ D) (hidx : idx * idx ∣ D) (hcop : Nat.Coprime idx θ) :
    chi * chi ∣ D := by
  subst hchi
  have hsq : Nat.Coprime (idx * idx) (θ * θ) := by
    simpa [sq] using Nat.Coprime.pow 2 2 hcop
  have h : (idx * idx) * (θ * θ) ∣ D := hsq.mul_dvd_of_dvd_of_dvd hidx hθ
  calc idx * θ * (idx * θ) = (idx * idx) * (θ * θ) := by ring
    _ ∣ D := h

/-- **Peterfalvi (6.6): full square-divisibility from the additive complement.**

This is the consumer-facing form of mmd L78-80 for the prefix sum `head = ∑_{j<i}χⱼ(1)²`.
If `θ²` divides the complementary tail and the total degree sum, it divides `head`; combined with
`idx² ∣ head`, `χᵢ(1) = idx·θ`, and `Coprime idx θ`, the full square `χᵢ(1)²` divides `head`.

It packages the two arithmetic steps above so the (6.6) coherence step can pass the square
divisibility `hdvd` to `two_mul_degree_lt_sum_ratCast` directly from the character-theoretic
sum identity and coprimality data. -/
theorem sq_dvd_of_factored_coprime_add_complement
    {idx θ chi head tail total : ℕ} (hsum : head + tail = total)
    (hθtail : θ * θ ∣ tail) (hθtotal : θ * θ ∣ total)
    (hidx : idx * idx ∣ head) (hchi : chi = idx * θ)
    (hcop : Nat.Coprime idx θ) :
    chi * chi ∣ head :=
  sq_dvd_of_factored_coprime hchi
    (dvd_of_add_eq_of_dvd_dvd hsum hθtail hθtotal) hidx hcop

/-- **Peterfalvi (6.6): square-divisibility of the complementary tail sum.**

If the anchor p-power degree `θ` divides every tail p-power degree `θdeg j`, then `θ²` divides
the tail sum of the induced degrees `(idx j * θdeg j)²`.  This isolates the `Finset.dvd_sum`
part of mmd L80: once the degree sort gives the divisibility of the p-power factors, every
summand carries a factor `θ²`. -/
theorem sq_dvd_sum_sq_mul_of_dvd
    {ι : Type*} (s : Finset ι) {θ : ℕ} {idx θdeg : ι → ℕ}
    (hθ : ∀ j ∈ s, θ ∣ θdeg j) :
    θ * θ ∣ ∑ j ∈ s, (idx j * θdeg j) * (idx j * θdeg j) := by
  apply Finset.dvd_sum
  intro j hj
  obtain ⟨a, ha⟩ := hθ j hj
  refine ⟨(idx j * a) * (idx j * a), ?_⟩
  rw [ha]
  ring

/-- **Peterfalvi (6.6): divisibility of p-power degrees from monotonicity (ℕ).**

If two p-power degree factors use the same base `p ≥ 2`, then the weak degree order
`θ ≤ θ'` implies `θ ∣ θ'`.  This is the arithmetic core behind the tail assertion
`θᵢ(1) ∣ θⱼ(1)` after the (6.6) degree sort. -/
theorem dvd_primePow_of_le
    {p θ θ' m n : ℕ} (hp : 2 ≤ p)
    (hθ : θ = p ^ m) (hθ' : θ' = p ^ n) (hle : θ ≤ θ') :
    θ ∣ θ' := by
  rw [hθ, hθ'] at hle ⊢
  have hexp : m ≤ n :=
    (Nat.pow_le_pow_iff_right (show 1 < p by omega)).mp hle
  exact Nat.pow_dvd_pow p hexp

/-- **Peterfalvi (6.6): cancelling the common induction index in p-power degrees (ℕ).**

The (6.6) sort compares induced degrees `idx·θ`.  Since `idx = |L:K|` is positive and fixed,
`idx·θ ≤ idx·θ'` reduces to `θ ≤ θ'`, and p-power comparison gives `θ ∣ θ'`. -/
theorem dvd_primePow_of_mul_le_mul
    {p idx θ θ' m n : ℕ} (hp : 2 ≤ p) (hidx : 0 < idx)
    (hθ : θ = p ^ m) (hθ' : θ' = p ^ n) (hle : idx * θ ≤ idx * θ') :
    θ ∣ θ' :=
  dvd_primePow_of_le hp hθ hθ' (Nat.le_of_mul_le_mul_left hle hidx)

/-- **Peterfalvi (6.6): full induced-degree divisibility from sorted p-power factors (ℕ).**

If `d = idx·θ` and `d' = idx·θ'` share the same positive induction index and the factors
are powers of the same base `p ≥ 2`, then `d ≤ d'` forces `d ∣ d'`.  This is the full-degree
version of `dvd_primePow_of_mul_le_mul`, feeding the §8 degree-ratio constructors from the
(6.6) sorted induced degrees. -/
theorem mul_primePow_dvd_mul_primePow_of_le
    {p idx θ θ' d d' m n : ℕ} (hp : 2 ≤ p) (hidx : 0 < idx)
    (hd : d = idx * θ) (hd' : d' = idx * θ')
    (hθ : θ = p ^ m) (hθ' : θ' = p ^ n) (hle : d ≤ d') :
    d ∣ d' := by
  subst d
  subst d'
  exact Nat.mul_dvd_mul_left idx
    (dvd_primePow_of_mul_le_mul hp hidx hθ hθ' hle)

/-- **Peterfalvi (6.6): tail square-divisibility from sorted p-power degrees (ℕ).**

A consumer-facing form of the tail step: if every tail degree factor `θdeg j` is a p-power
and the sorted induced degrees satisfy `idx·θ ≤ idx·θdeg j`, then `θ²` divides the tail sum
`∑ (idx·θdeg j)²`. -/
theorem sq_dvd_sum_sq_mul_const_of_primePow_mul_le
    {ι : Type*} (s : Finset ι) {p idx θ : ℕ} {θdeg : ι → ℕ}
    {m : ℕ} {n : ι → ℕ} (hp : 2 ≤ p) (hidx : 0 < idx)
    (hθ : θ = p ^ m) (hθdeg : ∀ j ∈ s, θdeg j = p ^ n j)
    (hle : ∀ j ∈ s, idx * θ ≤ idx * θdeg j) :
    θ * θ ∣ ∑ j ∈ s, (idx * θdeg j) * (idx * θdeg j) := by
  exact sq_dvd_sum_sq_mul_of_dvd s (θ := θ) (idx := fun _ ↦ idx) (θdeg := θdeg)
    (fun j hj ↦ dvd_primePow_of_mul_le_mul hp hidx hθ (hθdeg j hj) (hle j hj))

/-- **Peterfalvi (6.6): p-power square divisibility from a square bound (ℕ).**

If `θ` and `q` are powers of the same base `p ≥ 2`, then `θ² ≤ q` forces
`θ² ∣ q`.  In the (6.6) tail/total divisibility chain, this turns the Schur-center
bound `θᵢ(1)² ≤ |K:Z|` into the p-power divisibility input needed for the total sum. -/
theorem sq_dvd_primePow_of_sq_le
    {p θ q m n : ℕ} (hp : 2 ≤ p)
    (hθ : θ = p ^ m) (hq : q = p ^ n) (hle : θ * θ ≤ q) :
    θ * θ ∣ q := by
  rw [hθ, hq] at hle ⊢
  have hpow : p ^ (m + m) ≤ p ^ n := by
    simpa [pow_add] using hle
  have hexp : m + m ≤ n :=
    (Nat.pow_le_pow_iff_right (show 1 < p by omega)).mp hpow
  simpa [pow_add] using Nat.pow_dvd_pow p hexp

/-- **Peterfalvi (6.6): p-power square divisibility through a multiplicative factor (ℕ).**

A factored version of `sq_dvd_primePow_of_sq_le`: once `θ²` divides the p-power factor `q`,
it divides any product `q * c`. -/
theorem sq_dvd_primePow_mul_of_sq_le
    {p θ q c m n : ℕ} (hp : 2 ≤ p)
    (hθ : θ = p ^ m) (hq : q = p ^ n) (hle : θ * θ ≤ q) :
    θ * θ ∣ q * c :=
  dvd_mul_of_dvd_left (sq_dvd_primePow_of_sq_le hp hθ hq hle) c

/-- **Peterfalvi (6.6): head square-divisibility from tail and total p-power data (ℕ).**

This packages the full mmd L78-80 arithmetic chain.  The complementary tail divisibility is derived
from the sorted p-power degrees, the total divisibility from the p-power square bound, and the
additive identity then moves the `θ²` divisor to the head.  Finally the coprime fixed-index factor
upgrades `θ² ∣ head` and `idx² ∣ head` to `(idx·θ)² ∣ head`. -/
theorem sq_dvd_head_of_commonIndex_primePower_sums
    {ι : Type*} (tailSet : Finset ι)
    {p idx θ chi q c head total : ℕ} {θdeg : ι → ℕ}
    {m n : ℕ} {ntail : ι → ℕ} (hp : 2 ≤ p) (hidxpos : 0 < idx)
    (hθ : θ = p ^ m) (hθdeg : ∀ j ∈ tailSet, θdeg j = p ^ ntail j)
    (htail_le : ∀ j ∈ tailSet, idx * θ ≤ idx * θdeg j)
    (hsum : head + (∑ j ∈ tailSet, (idx * θdeg j) * (idx * θdeg j)) = total)
    (hq : q = p ^ n) (hθsq_le_q : θ * θ ≤ q) (htotal : total = q * c)
    (hidx_head : idx * idx ∣ head) (hchi : chi = idx * θ) (hcop : Nat.Coprime idx θ) :
    chi * chi ∣ head := by
  have hθtail : θ * θ ∣ ∑ j ∈ tailSet, (idx * θdeg j) * (idx * θdeg j) :=
    sq_dvd_sum_sq_mul_const_of_primePow_mul_le tailSet hp hidxpos hθ hθdeg htail_le
  have hθtotal : θ * θ ∣ total := by
    rw [htotal]
    exact sq_dvd_primePow_mul_of_sq_le hp hθ hq hθsq_le_q
  exact sq_dvd_of_factored_coprime_add_complement
    hsum hθtail hθtotal hidx_head hchi hcop

end OddOrder.Peterfalvi.S07
