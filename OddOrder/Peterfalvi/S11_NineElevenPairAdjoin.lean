/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S11_NineElevenAlphaBound

/-!
# Peterfalvi (9.11.7)–(9.11.8): the coherent-pair adjunction and the case-(a) endgame

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §9, p. 57,
(9.11.7)–(9.11.8) (mmd `04.11`, lines ~176–199); Coq mirror `PFsection9.v:2048-2227`.

## What this file provides

The **final piece of the (9.11) case-(a) refutation** (issue 9083, Phase E-final): the
discharge of the single residual `NineElevenSevenEightRefutation`, and with it the
unconditional Peterfalvi (9.11) (`coherent_sOf_H0Cprime`, Coq `Ptype_core_coherence`).

* **The union-pair coherent extension** (`isCoherent_union_pair_of_bridge`): the Lean form of
  Coq's `extend_coherent_with` + `bridge_coherent` (Peterfalvi (5.6.3), reused in (9.11.8)).
  Given a coherent extension `τ₁` of an orthonormal family `S`, a conjugate pair
  `{λ, λ̄}` orthogonal to `S`, orthonormal targets `X, Xc ∈ ℤ[Irr G]` orthogonal to `τ₁S` with
  `(λ − λ̄)^τ = X − Xc`, and the **bridge identity** `(λ − E·ψ₀)^τ = X − E·τ₁ψ₀` for some
  `ψ₀ ∈ S` with `λ − E·ψ₀` supported, the Fourier-projection map
  `φ ↦ ∑_{ψ∈S} ⟨φ,ψ⟩·τ₁ψ + ⟨φ,λ⟩·X + ⟨φ,λ̄⟩·Xc` is a coherent extension of `S ∪ {λ, λ̄}`.
  Agreement with `τ` on the supported lattice follows by rewriting a supported
  `φ = φ' + (a+b)·(λ − E·ψ₀) + b·(λ̄ − λ)` with `φ' ∈ ℤ[S]` supported — Coq's
  `bridge_coherent` bookkeeping without the degree computation.

* **Peterfalvi (5.5) for coherent extensions** (`coherent_extension_eq_sum_memberRFamily`,
  Coq `mem_coherent_sum_subseq`): a coherent extension evaluates each member as a partial sum
  `∑_{α ∈ E} α` of its dispatched `R`-family — the `CharacterPsiDecomposition.ofProjection` +
  `eq_sum_of_psi_eq_zero` machinery at `ψ = 0`.

* **Cross-orthogonality of coherent images** (`coherent_extension_cross_orthogonal`, Coq
  `coherent_ortho`): for members of two coherent subfamilies with `⟨ψ, λ⟩ = ⟨ψ, λ̄⟩ = 0`, the
  images are orthogonal — (5.5) on both sides plus the (5.2.e) `R`-family cross-orthogonality
  `sOf_H0Cprime_memberRFamily_orthogonal`.

* **The (9.11.7)–(9.11.8) discharge** (`nineElevenSevenEightRefutation`): in the orthogonal
  branch `α^τ ⊥ 𝒮₃^{τ₃}` of the (9.11.6) dichotomy, pick `λ₁ ∈ 𝒮₄` (nonempty since
  `|𝒮₄| > N = ‖α‖²` — the arithmetic spine refutes `|𝒮₄| ≤ N`), set `e = u/a ≥ 2` and
  `β = λ₁ − e·ψ₁`.  Project `β^τ` on `𝒮₄^{τ₃}` (giving `Γ`) and on `𝒮₂^{τ₁}` (coefficients
  constant off `ψ₁` by `⟨β, ψ − ψ₁⟩ = e`); the norm budget `‖β‖² = e² + 1` with `|𝒮₂| = 2e`
  forces `‖Γ‖² = 1`, `Δ = 0`, and the common coefficient `b ∈ {0, 1}` **(9.11.7)**; pairing
  with `⟨α^τ, β^τ⟩ = e` and `α^τ ⊥ Γ` forces `e ∣ b`, so `b = 0` **(9.11.8)**, leaving the
  bridge `β^τ = Γ − e·τ₁ψ₁`; the union-pair extension then adjoins `{λ₁, λ̄₁}` coherently to
  `𝒮₂`, contradicting the maximality pair clause.

Reference note: `issues/closed/9083-lane-a-1007-decomp-moot-revised-frontier.md` (Phase E-final).
-/

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Peterfalvi.S11
open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

/-! ### The union-pair coherent extension (Coq `extend_coherent_with` + `bridge_coherent`) -/

section UnionPair

variable {L Γ' : Type*} [Group L] [Group Γ']
variable [Fintype L] [Fintype Γ'] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card Γ' : ℂ)]

/-- The Fourier-projection extension of the union family `S ∪ {λ, λ̄}`: on the orthonormal
basis it sends `ψ ∈ S ↦ τ₁ψ`, `λ ↦ X`, `λ̄ ↦ Xc`.  A `ℤ`-linear map since each coefficient
functional `⟨·, η⟩` is (`IntegralCharacterMap.innerLeftℤ`). -/
noncomputable def unionPairExtension {S : Set (ClassFunction L ℂ)} (hSfin : S.Finite)
    (τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L Γ')
    (lam : ClassFunction L ℂ) (X Xc : ClassFunction Γ' ℂ) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap L Γ' :=
  (∑ ψ ∈ hSfin.toFinset,
      (OddOrder.Peterfalvi.S07.IntegralCharacterMap.innerLeftℤ ψ).smulRight (τ₁ ψ))
    + (OddOrder.Peterfalvi.S07.IntegralCharacterMap.innerLeftℤ lam).smulRight X
    + (OddOrder.Peterfalvi.S07.IntegralCharacterMap.innerLeftℤ lam.conj).smulRight Xc

omit [Fintype Γ'] [Invertible (Nat.card Γ' : ℂ)] in
theorem unionPairExtension_apply {S : Set (ClassFunction L ℂ)} (hSfin : S.Finite)
    (τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L Γ')
    (lam : ClassFunction L ℂ) (X Xc : ClassFunction Γ' ℂ) (φ : ClassFunction L ℂ) :
    unionPairExtension hSfin τ₁ lam X Xc φ
      = (∑ ψ ∈ hSfin.toFinset, ClassFunction.inner φ ψ • τ₁ ψ)
        + ClassFunction.inner φ lam • X + ClassFunction.inner φ lam.conj • Xc := by
  simp [unionPairExtension, LinearMap.sum_apply, LinearMap.smulRight_apply]

set_option maxHeartbeats 800000 in
-- the four structure fields each run `Submodule.span_induction` over the union lattice with
-- inner-product rewriting per generator pair
/-- **The union-pair coherent extension** (Peterfalvi (5.6.3); Coq `extend_coherent_with`
`PFsection5.v:1059` + `bridge_coherent` `PFsection5.v:1000`, the shape reused in (9.11.8)).

Inputs: an orthonormal finite family `S` with a coherent-extension-style map `τ₁` (isometric
on pairs of members, agreeing with `τ` on the `A`-supported lattice, `ℤ[Irr]`-valued on
members); a conjugate pair `{λ, λ̄}` of orthonormal members orthogonal to `S`; orthonormal
targets `X, Xc ∈ ℤ[Irr Γ']` orthogonal to the `τ₁`-images with `(λ − λ̄)^τ = X − Xc`; and the
**bridge** `(λ − E·ψ₀)^τ = X − E·τ₁ψ₀` for a member `ψ₀ ∈ S`, with `λ − E·ψ₀`
`A`-supported.  Conclusion: `S ∪ {λ, λ̄}` is coherent via the Fourier-projection extension.

Agreement on the supported lattice: a supported `φ = y + a·λ + b·λ̄` rewrites as
`φ' + (a+b)·(λ − E·ψ₀) + b·(λ̄ − λ)` with `φ' = y + (a+b)E·ψ₀ ∈ ℤ[S]` supported (difference
of supported elements), and `τ` agrees with the extension on all three pieces. -/
noncomputable def isCoherent_union_pair_of_bridge
    {τ τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L Γ'}
    {S : Set (ClassFunction L ℂ)} {A : Set L} (hSfin : S.Finite)
    (hON1 : ∀ φ ∈ S, ClassFunction.inner φ φ = 1)
    (hON2 : ∀ φ ∈ S, ∀ ξ ∈ S, φ ≠ ξ → ClassFunction.inner φ ξ = 0)
    (hτ₁pair : ∀ φ ∈ S, ∀ ξ ∈ S,
      ClassFunction.inner (τ₁ φ) (τ₁ ξ) = ClassFunction.inner φ ξ)
    (hτ₁agrees : ∀ φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A, τ₁ φ = τ φ)
    (hτ₁Z : ∀ φ ∈ S, τ₁ φ ∈ ZIrr Γ')
    {lam : ClassFunction L ℂ}
    (hlamne : lam ≠ lam.conj)
    (hlam1 : ClassFunction.inner lam lam = 1)
    (hlamc1 : ClassFunction.inner lam.conj lam.conj = 1)
    (hlamlamc : ClassFunction.inner lam lam.conj = 0)
    (hSlam : ∀ φ ∈ S, ClassFunction.inner φ lam = 0)
    (hSlamc : ∀ φ ∈ S, ClassFunction.inner φ lam.conj = 0)
    {X Xc : ClassFunction Γ' ℂ}
    (hXX : ClassFunction.inner X X = 1)
    (hXcXc : ClassFunction.inner Xc Xc = 1)
    (hXXc : ClassFunction.inner X Xc = 0)
    (hXZ : X ∈ ZIrr Γ') (hXcZ : Xc ∈ ZIrr Γ')
    (hextX : ∀ φ ∈ S, ClassFunction.inner (τ₁ φ) X = 0)
    (hextXc : ∀ φ ∈ S, ClassFunction.inner (τ₁ φ) Xc = 0)
    (hdiff : τ (lam - lam.conj) = X - Xc)
    (hdiffsupp : ((lam - lam.conj : ClassFunction L ℂ)).support ⊆ A)
    {ψ₀ : ClassFunction L ℂ} (hψ₀S : ψ₀ ∈ S) {E : ℤ}
    (hbridge : τ (lam - E • ψ₀) = X - E • τ₁ ψ₀)
    (hbridgesupp : ((lam - E • ψ₀ : ClassFunction L ℂ)).support ⊆ A) :
    OddOrder.Peterfalvi.S07.IsCoherent τ (S ∪ {lam, lam.conj}) A := by
  classical
  -- generator membership dichotomy
  have hUmem : ∀ x, x ∈ S ∪ ({lam, lam.conj} : Set (ClassFunction L ℂ)) →
      x ∈ S ∨ x = lam ∨ x = lam.conj := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · rcases Set.mem_insert_iff.mp hx with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Set.mem_singleton_iff.mp h))
  -- reversed-slot orthogonalities
  have hlamS : ∀ φ ∈ S, ClassFunction.inner lam φ = 0 := fun φ hφ => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm φ lam, hSlam φ hφ, star_zero]
  have hlamcS : ∀ φ ∈ S, ClassFunction.inner lam.conj φ = 0 := fun φ hφ => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm φ lam.conj, hSlamc φ hφ, star_zero]
  have hlamclam : ClassFunction.inner lam.conj lam = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm lam lam.conj, hlamlamc, star_zero]
  have hXcX : ClassFunction.inner Xc X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm X Xc, hXXc, star_zero]
  have hXext : ∀ φ ∈ S, ClassFunction.inner X (τ₁ φ) = 0 := fun φ hφ => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (τ₁ φ) X, hextX φ hφ, star_zero]
  have hXcext : ∀ φ ∈ S, ClassFunction.inner Xc (τ₁ φ) = 0 := fun φ hφ => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (τ₁ φ) Xc, hextXc φ hφ, star_zero]
  -- generator values of the extension
  have hval_mem : ∀ ψ' ∈ S, unionPairExtension hSfin τ₁ lam X Xc ψ' = τ₁ ψ' := by
    intro ψ' hψ'
    rw [unionPairExtension_apply, hSlam ψ' hψ', hSlamc ψ' hψ', zero_smul, zero_smul,
      add_zero, add_zero,
      Finset.sum_eq_single ψ'
        (fun ψ hψ hne => by
          rw [hON2 ψ' hψ' ψ (hSfin.mem_toFinset.mp hψ) (Ne.symm hne), zero_smul])
        (fun h => absurd (hSfin.mem_toFinset.mpr hψ') h),
      hON1 ψ' hψ', one_smul]
  have hval_lam : unionPairExtension hSfin τ₁ lam X Xc lam = X := by
    rw [unionPairExtension_apply, hlam1, hlamlamc, one_smul, zero_smul, add_zero,
      Finset.sum_eq_zero
        (fun ψ hψ => by rw [hlamS ψ (hSfin.mem_toFinset.mp hψ), zero_smul]),
      zero_add]
  have hval_lamc : unionPairExtension hSfin τ₁ lam X Xc lam.conj = Xc := by
    rw [unionPairExtension_apply, hlamc1, hlamclam, one_smul, zero_smul, add_zero,
      Finset.sum_eq_zero
        (fun ψ hψ => by rw [hlamcS ψ (hSfin.mem_toFinset.mp hψ), zero_smul]),
      zero_add]
  -- the extension agrees with `τ₁` on `ℤ[S]`
  have hext_span : ∀ φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := L) S,
      unionPairExtension hSfin τ₁ lam X Xc φ = τ₁ φ := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hval_mem x hx
    | zero => rw [map_zero, map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul n x _ hx => rw [map_smul, map_smul, hx]
  -- inner products on generator pairs
  have hgen : ∀ x, (x ∈ S ∨ x = lam ∨ x = lam.conj) →
      ∀ y, (y ∈ S ∨ y = lam ∨ y = lam.conj) →
      ClassFunction.inner (unionPairExtension hSfin τ₁ lam X Xc x)
          (unionPairExtension hSfin τ₁ lam X Xc y)
        = ClassFunction.inner x y := by
    intro x hx y hy
    rcases hx with hx | rfl | rfl <;> rcases hy with hy | rfl | rfl
    · rw [hval_mem x hx, hval_mem y hy]; exact hτ₁pair x hx y hy
    · rw [hval_mem x hx, hval_lam, hextX x hx, hSlam x hx]
    · rw [hval_mem x hx, hval_lamc, hextXc x hx, hSlamc x hx]
    · rw [hval_lam, hval_mem y hy, hXext y hy, hlamS y hy]
    · rw [hval_lam, hXX, hlam1]
    · rw [hval_lam, hval_lamc, hXXc, hlamlamc]
    · rw [hval_lamc, hval_mem y hy, hXcext y hy, hlamcS y hy]
    · rw [hval_lamc, hval_lam, hXcX, hlamclam]
    · rw [hval_lamc, hXcXc, hlamc1]
  -- inner products, one slot span-general
  have hrow : ∀ y, (y ∈ S ∨ y = lam ∨ y = lam.conj) →
      ∀ φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := L) (S ∪ {lam, lam.conj}),
      ClassFunction.inner (unionPairExtension hSfin τ₁ lam X Xc φ)
          (unionPairExtension hSfin τ₁ lam X Xc y)
        = ClassFunction.inner φ y := by
    intro y hy φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hgen x (hUmem x hx) y hy
    | zero => rw [map_zero, ClassFunction.inner_zero_left, ClassFunction.inner_zero_left]
    | add x z _ _ hx hz =>
        rw [map_add, ClassFunction.inner_add_left, ClassFunction.inner_add_left, hx, hz]
    | smul n x _ hx =>
        rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ n (unionPairExtension hSfin τ₁ lam X Xc x),
          ← Int.cast_smul_eq_zsmul ℂ n x, ClassFunction.inner_smul_left,
          ClassFunction.inner_smul_left, hx]
  refine
    { nonzero := ⟨lam - lam.conj,
        ⟨Submodule.sub_mem _
          (Submodule.subset_span (Or.inr (Set.mem_insert _ _)))
          (Submodule.subset_span (Or.inr (Set.mem_insert_of_mem _ rfl))),
          hdiffsupp⟩,
        sub_ne_zero.mpr hlamne⟩
      extension := unionPairExtension hSfin τ₁ lam X Xc
      extension_inner_eq := ?_
      extends_on_supported := ?_
      extension_mem_ZIrr := ?_ }
  · -- isometry on the union lattice: span-induct the right slot over `hrow`
    intro φ ψ hφ hψ
    induction hψ using Submodule.span_induction with
    | mem y hy => exact hrow y (hUmem y hy) φ hφ
    | zero => rw [map_zero, ClassFunction.inner_zero_right, ClassFunction.inner_zero_right]
    | add x z _ _ hx hz =>
        rw [map_add, ClassFunction.inner_add_right, ClassFunction.inner_add_right, hx, hz]
    | smul n x _ hx =>
        rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ n (unionPairExtension hSfin τ₁ lam X Xc x),
          ← Int.cast_smul_eq_zsmul ℂ n x,
          OddOrder.RepresentationTheory.inner_smul_right,
          OddOrder.RepresentationTheory.inner_smul_right, hx]
  · -- agreement with `τ` on the supported union lattice
    intro φ hφ
    obtain ⟨hφspan, hφsupp⟩ := hφ
    have hφsup : φ ∈ Submodule.span ℤ (S : Set (ClassFunction L ℂ)) ⊔
        Submodule.span ℤ ({lam, lam.conj} : Set (ClassFunction L ℂ)) := by
      rw [← Submodule.span_union]
      exact hφspan
    obtain ⟨y, hy, z, hz, hφeq⟩ := Submodule.mem_sup.mp hφsup
    obtain ⟨a, b, hzeq⟩ := Submodule.mem_span_pair.mp hz
    -- the recentered element `φ' = y + (a+b)E·ψ₀ ∈ ℤ[S]`
    set φ' : ClassFunction L ℂ :=
      φ - (a + b) • (lam - E • ψ₀) - b • (lam.conj - lam) with hφ'def
    have hφ'eq : φ' = y + ((a + b) * E) • ψ₀ := by
      rw [hφ'def, ← hφeq, ← hzeq]
      module
    have hφ'span : φ' ∈ OddOrder.Peterfalvi.S07.zSpan (L := L) S := by
      rw [hφ'eq]
      exact Submodule.add_mem _ hy
        (Submodule.smul_mem _ _ (Submodule.subset_span hψ₀S))
    have hφ'supp : φ'.support ⊆ A := by
      intro x hx
      rw [ClassFunction.mem_support] at hx
      by_contra hxA
      have h1 : φ x = 0 := by
        by_contra h
        exact hxA (hφsupp (ClassFunction.mem_support.mpr h))
      have h2 : (lam - E • ψ₀ : ClassFunction L ℂ) x = 0 := by
        by_contra h
        exact hxA (hbridgesupp (ClassFunction.mem_support.mpr h))
      have h3 : (lam - lam.conj : ClassFunction L ℂ) x = 0 := by
        by_contra h
        exact hxA (hdiffsupp (ClassFunction.mem_support.mpr h))
      apply hx
      have hval : φ' x
          = φ x - ((a + b : ℤ) : ℂ) * (lam - E • ψ₀ : ClassFunction L ℂ) x
            + ((b : ℤ) : ℂ) * (lam - lam.conj : ClassFunction L ℂ) x := by
        rw [hφ'def, ClassFunction.sub_apply, ClassFunction.sub_apply,
          ← Int.cast_smul_eq_zsmul ℂ (a + b) (lam - E • ψ₀ : ClassFunction L ℂ),
          ← Int.cast_smul_eq_zsmul ℂ b (lam.conj - lam : ClassFunction L ℂ),
          ClassFunction.smul_apply, ClassFunction.smul_apply]
        have hneg : (lam.conj - lam : ClassFunction L ℂ) x
            = -((lam - lam.conj : ClassFunction L ℂ) x) := by
          rw [ClassFunction.sub_apply, ClassFunction.sub_apply]
          ring
        rw [hneg]
        ring
      rw [hval, h1, h2, h3, mul_zero, mul_zero, sub_zero, add_zero]
    -- decompose and transport piecewise
    have hφdecomp : φ = φ' + (a + b) • (lam - E • ψ₀) + b • (lam.conj - lam) := by
      rw [hφ'def]
      abel
    have hextβ : unionPairExtension hSfin τ₁ lam X Xc (lam - E • ψ₀)
        = τ (lam - E • ψ₀) := by
      rw [map_sub, map_smul, hval_lam, hval_mem ψ₀ hψ₀S, hbridge]
    have hextD : unionPairExtension hSfin τ₁ lam X Xc (lam.conj - lam)
        = τ (lam.conj - lam) := by
      have hτD : τ (lam.conj - lam) = Xc - X := by
        rw [show (lam.conj - lam : ClassFunction L ℂ) = -(lam - lam.conj) from by abel,
          map_neg, hdiff]
        abel
      rw [hτD, map_sub, hval_lamc, hval_lam]
    calc unionPairExtension hSfin τ₁ lam X Xc φ
        = unionPairExtension hSfin τ₁ lam X Xc φ'
            + (a + b) • unionPairExtension hSfin τ₁ lam X Xc (lam - E • ψ₀)
            + b • unionPairExtension hSfin τ₁ lam X Xc (lam.conj - lam) := by
          conv_lhs => rw [hφdecomp]
          rw [map_add, map_add, map_smul, map_smul]
      _ = τ φ' + (a + b) • τ (lam - E • ψ₀) + b • τ (lam.conj - lam) := by
          rw [hext_span φ' hφ'span, hτ₁agrees φ' ⟨hφ'span, hφ'supp⟩, hextβ, hextD]
      _ = τ φ := by
          conv_rhs => rw [hφdecomp]
          rw [map_add, map_add, map_smul, map_smul]
  · -- `ℤ[Irr Γ']`-valued on the union lattice
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
        rcases hUmem x hx with hxS | rfl | rfl
        · rw [hval_mem x hxS]; exact hτ₁Z x hxS
        · rw [hval_lam]; exact hXZ
        · rw [hval_lamc]; exact hXcZ
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x z _ _ hx hz => rw [map_add]; exact Submodule.add_mem _ hx hz
    | smul n x _ hx => rw [map_smul]; exact Submodule.smul_mem _ n hx

end UnionPair

/-! ### Peterfalvi (5.5) for coherent extensions, and the `coherent_ortho` cross-orthogonality -/

section CoherentOrtho

variable [Finite G]

/-- **Peterfalvi (5.5) for a coherent subfamily of `𝒮(H₀C′)`** (Coq `mem_coherent_sum_subseq`,
`PFsection5.v:957`): a coherent extension of `T ⊆ 𝒮(H₀C′)` evaluates a member `ψ` (whose
conjugate is also in `T`) as a partial sum `∑_{α ∈ E} α` over the dispatched `R(ψ)`-family.
This is `CharacterPsiDecomposition.ofProjection` at `ψ = 0` (the auxiliary isometry is the
coherent extension itself, its lattice-relative isometry restricted from `ℤ[T]`, the
agreement on `ψ − ψ̄` from `extends_on_supported`), closed by `eq_sum_of_psi_eq_zero`. -/
theorem coherent_extension_eq_sum_memberRFamily
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {T : Set (ClassFunction ↥M ℂ)}
    (hTsub : T ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (c' : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau T hyp.base.A0)
    {ψ : ClassFunction ↥M ℂ} (hψT : ψ ∈ T) (hψcT : ψ.conj ∈ T) :
    ∃ E ⊆ (sOf_H0Cprime_memberRFamily hG hyp (hTsub hψT)).imageSet,
      c'.extension ψ = ∑ α ∈ E, α := by
  haveI := hyp.base.finiteG
  classical
  have hψsOf := hTsub hψT
  have hψcsOf := hTsub hψcT
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun x hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hne : ψ ≠ ψ.conj := fun h =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd _
      (hIKF hψsOf) h.symm
  have hχχbar : ClassFunction.inner ψ ψ.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF hψsOf) (hIKF hψcsOf) hne
  have hdiffsupp : ((ψ - ψ.conj : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := by
    rw [show (ψ - ψ.conj : ClassFunction ↥M ℂ) = -(ψ.conj - ψ) from by abel,
      ClassFunction.support_neg]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 (hIKF hψsOf)
  have hle : OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
      ({ψ - ψ.conj, ψ - 0} : Set (ClassFunction ↥M ℂ))
      ≤ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) T :=
    Submodule.span_le.mpr (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.subset_span hψcT)
      · exact Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.zero_mem _))
  obtain ⟨-, hτ1ψ, E, hEsub, hXsum, -⟩ :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.eq_sum_of_psi_eq_zero
      (OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
        (sOf_H0Cprime_memberRFamily hG hyp hψsOf) c'.extension
        (fun φ ζ hφ hζ => c'.extension_inner_eq φ ζ (hle hφ) (hle hζ))
        (c'.extends_on_supported (ψ - ψ.conj)
          ⟨Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.subset_span hψcT),
            hdiffsupp⟩)
        (by rw [sub_zero]; exact c'.extension_mem_ZIrr ψ (Submodule.subset_span hψT))
        (by rw [ClassFunction.inner_zero_right])
        (by rw [ClassFunction.inner_zero_right])
        hχχbar)
  exact ⟨E, hEsub, hτ1ψ.trans hXsum⟩

set_option maxHeartbeats 1600000 in
-- the two (5.5) projections and the (5.2.e) dispatch thread the
-- `hyp.base.tau = dadeIntegralCharacterMap` defeq (as in `sOf_H0Cprime_memberRFamily_orthogonal`)
/-- **Cross-orthogonality of coherent images** (Coq `coherent_ortho`, `PFsection5.v:986`):
for coherent subfamilies `T₁, T₂ ⊆ 𝒮(H₀C′)` and members `ψ ∈ T₁`, `λ ∈ T₂` with
`ψ ∉ {λ, λ̄}` (so `⟨ψ, λ⟩ = ⟨ψ, λ̄⟩ = 0` by the family's pairwise orthogonality), the
coherent images are orthogonal: both are partial `R`-family sums by (5.5), and the
`R`-families are cross-orthogonal by (5.2.e). -/
theorem coherent_extension_cross_orthogonal
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {T₁ T₂ : Set (ClassFunction ↥M ℂ)}
    (hT₁sub : T₁ ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hT₂sub : T₂ ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (c₁ : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau T₁ hyp.base.A0)
    (c₂ : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau T₂ hyp.base.A0)
    {ψ lam : ClassFunction ↥M ℂ}
    (hψT : ψ ∈ T₁) (hψcT : ψ.conj ∈ T₁) (hlamT : lam ∈ T₂) (hlamcT : lam.conj ∈ T₂)
    (hne1 : ψ ≠ lam) (hne2 : ψ ≠ lam.conj) :
    ClassFunction.inner (c₁.extension ψ) (c₂.extension lam) = 0 := by
  haveI := hyp.base.finiteG
  classical
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun x hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  have h1 : ClassFunction.inner ψ lam = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF (hT₁sub hψT)) (hIKF (hT₂sub hlamT)) hne1
  have h2 : ClassFunction.inner ψ lam.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF (hT₁sub hψT)) (hIKF (hT₂sub hlamcT)) hne2
  obtain ⟨E₁, hE₁sub, hE₁⟩ :=
    coherent_extension_eq_sum_memberRFamily hG hyp hT₁sub c₁ hψT hψcT
  obtain ⟨E₂, hE₂sub, hE₂⟩ :=
    coherent_extension_eq_sum_memberRFamily hG hyp hT₂sub c₂ hlamT hlamcT
  have horth := sOf_H0Cprime_memberRFamily_orthogonal hG hyp
    (hT₁sub hψT) (hT₂sub hlamT) h1 h2
  rw [hE₁, hE₂, OddOrder.RepresentationTheory.inner_sum_left]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [OddOrder.RepresentationTheory.inner_sum_right]
  exact Finset.sum_eq_zero fun β hβ => horth α (hE₁sub hα) β (hE₂sub hβ)

/-- **Peterfalvi (5.5) for a coherent subfamily of any stratum `S(N)`** (stratum-generic
`coherent_extension_eq_sum_memberRFamily`, issue 1023): a coherent extension of `T ⊆ S(N)`
evaluates a member `ψ` (whose conjugate is also in `T`) as a partial sum over the dispatched
`SOf_memberRFamily`. -/
theorem SOf_coherent_extension_eq_sum_memberRFamily
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {N : Subgroup G} {T : Set (ClassFunction ↥M ℂ)} (hTsub : T ⊆ hyp.SOf N)
    (c' : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau T hyp.base.A0)
    {ψ : ClassFunction ↥M ℂ} (hψT : ψ ∈ T) (hψcT : ψ.conj ∈ T) :
    ∃ E ⊆ (SOf_memberRFamily hG hyp (hTsub hψT)).imageSet,
      c'.extension ψ = ∑ α ∈ E, α := by
  haveI := hyp.base.finiteG
  classical
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄, x ∈ hyp.SOf N →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun x hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hx)
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hne : ψ ≠ ψ.conj := fun h =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd _
      (hIKF (hTsub hψT)) h.symm
  have hχχbar : ClassFunction.inner ψ ψ.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF (hTsub hψT)) (hIKF (hTsub hψcT)) hne
  have hdiffsupp : ((ψ - ψ.conj : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := by
    rw [show (ψ - ψ.conj : ClassFunction ↥M ℂ) = -(ψ.conj - ψ) from by abel,
      ClassFunction.support_neg]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 (hIKF (hTsub hψT))
  have hle : OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
      ({ψ - ψ.conj, ψ - 0} : Set (ClassFunction ↥M ℂ))
      ≤ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) T :=
    Submodule.span_le.mpr (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.subset_span hψcT)
      · exact Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.zero_mem _))
  obtain ⟨-, hτ1ψ, E, hEsub, hXsum, -⟩ :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.eq_sum_of_psi_eq_zero
      (OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
        (SOf_memberRFamily hG hyp (hTsub hψT)) c'.extension
        (fun φ ζ hφ hζ => c'.extension_inner_eq φ ζ (hle hφ) (hle hζ))
        (c'.extends_on_supported (ψ - ψ.conj)
          ⟨Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.subset_span hψcT),
            hdiffsupp⟩)
        (by rw [sub_zero]; exact c'.extension_mem_ZIrr ψ (Submodule.subset_span hψT))
        (by rw [ClassFunction.inner_zero_right])
        (by rw [ClassFunction.inner_zero_right])
        hχχbar)
  exact ⟨E, hEsub, hτ1ψ.trans hXsum⟩

set_option maxHeartbeats 1600000 in
-- the two (5.5) projections and the (5.2.e) dispatch thread the
-- `hyp.base.tau = dadeIntegralCharacterMap` defeq (as in `SOf_memberRFamily_orthogonal`)
/-- **Cross-orthogonality of coherent images across two strata** (the Coq `coherent_ortho`,
`PFsection5.v:986`, at two kernel-filter strata — issue 1023, the `hmixed` core of (11.8.6)):
for coherent subfamilies `T₁ ⊆ S(N₁)`, `T₂ ⊆ S(N₂)` and members `ψ ∈ T₁`, `λ ∈ T₂` with
`ψ ∉ {λ, λ̄}`, the coherent images are orthogonal: both are partial `R`-family sums by (5.5),
and the `R`-families are cross-orthogonal by (5.2.e). -/
theorem SOf_coherent_extension_cross_orthogonal
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {N₁ N₂ : Subgroup G} {T₁ T₂ : Set (ClassFunction ↥M ℂ)}
    (hT₁sub : T₁ ⊆ hyp.SOf N₁) (hT₂sub : T₂ ⊆ hyp.SOf N₂)
    (c₁ : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau T₁ hyp.base.A0)
    (c₂ : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau T₂ hyp.base.A0)
    {ψ lam : ClassFunction ↥M ℂ}
    (hψT : ψ ∈ T₁) (hψcT : ψ.conj ∈ T₁) (hlamT : lam ∈ T₂) (hlamcT : lam.conj ∈ T₂)
    (hne1 : ψ ≠ lam) (hne2 : ψ ≠ lam.conj) :
    ClassFunction.inner (c₁.extension ψ) (c₂.extension lam) = 0 := by
  haveI := hyp.base.finiteG
  classical
  have hIKF : ∀ ⦃Nz : Subgroup G⦄ ⦃x : ClassFunction ↥M ℂ⦄, x ∈ hyp.SOf Nz →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun Nz x hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hx)
  have h1 : ClassFunction.inner ψ lam = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF (hT₁sub hψT)) (hIKF (hT₂sub hlamT)) hne1
  have h2 : ClassFunction.inner ψ lam.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF (hT₁sub hψT)) (hIKF (hT₂sub hlamcT)) hne2
  obtain ⟨E₁, hE₁sub, hE₁⟩ :=
    SOf_coherent_extension_eq_sum_memberRFamily hG hyp hT₁sub c₁ hψT hψcT
  obtain ⟨E₂, hE₂sub, hE₂⟩ :=
    SOf_coherent_extension_eq_sum_memberRFamily hG hyp hT₂sub c₂ hlamT hlamcT
  have horth := SOf_memberRFamily_orthogonal hG hyp
    (hT₁sub hψT) (hT₂sub hlamT) h1 h2
  rw [hE₁, hE₂, OddOrder.RepresentationTheory.inner_sum_left]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [OddOrder.RepresentationTheory.inner_sum_right]
  exact Finset.sum_eq_zero fun β hβ => horth α (hE₁sub hα) β (hE₂sub hβ)

end CoherentOrtho

/-! ### The (9.11.7)–(9.11.8) projection budget -/

section ProjectionBudget

variable {Γ' : Type*} [Group Γ'] [Fintype Γ'] [Invertible (Nat.card Γ' : ℂ)]

set_option maxHeartbeats 1600000 in
-- orthonormal-projection bookkeeping: repeated `Finset` sum collapses and a final
-- integer-cast budget analysis
/-- **Peterfalvi (9.11.7)–(9.11.8), the projection budget** (Coq `PFsection9.v:2090-2172`
for (9.11.7) and `:2173-2220` for the `b`-elimination of (9.11.8)).

Abstract data: two orthonormal families `θ₁` (indexed by `SF`, `|SF| = 2e`, the
`𝒮₁^{τ₁}`-side) and `θ₃` (indexed by `S4F`, the `𝒮₄^{τ₃}`-side), mutually orthogonal;
`TB = β^τ` of norm `e² + 1` with integer coefficients, `θ₁`-coefficients constant off `ψ₁`
with offset `e` ((9.11.7): `⟨β, ψ − ψ₁⟩ = e`), and `θ₃ l₁/l₂`-coefficient difference `1`
(`⟨β, λ₁ − λ̄₁⟩ = 1`); `TA = α^τ` with `⟨TA, TB⟩ = e`, `TA ⊥ θ₃` ((9.11.6)), and
`θ₁`-coefficients constant off `ψ₁` with offset `1` (`⟨α, ψ − ψ₁⟩ = 1`).

Projecting `TB = Γ + B + Δ` on the two families, the norm budget
`‖Γ‖² + (b−e)² + (2e−1)b² + ‖Δ‖² = e² + 1` with `‖Γ‖² ≥ 1` (the `l₁/l₂` coefficients cannot
both vanish) forces `‖Γ‖² = 1`, `Δ = 0`, `b ∈ {0,1}` **(9.11.7)**; then
`e = ⟨TA, TB⟩ = (b−e)x + (2e−1)b(x+1)` forces `e·(x+1) = 1` if `b = 1` — impossible for
`e ≥ 2` — so `b = 0` **(9.11.8)** and `TB = Γ − e·θ₁ψ₁`. -/
theorem exists_bridge_target_of_budget {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {SF : Finset ι} {S4F : Finset κ}
    (θ₁ : ι → ClassFunction Γ' ℂ) (θ₃ : κ → ClassFunction Γ' ℂ)
    {TB TA : ClassFunction Γ' ℂ} {ψ₁ : ι} {l₁ l₂ : κ} {e : ℕ}
    (hψ₁SF : ψ₁ ∈ SF) (hl₁ : l₁ ∈ S4F) (hl₂ : l₂ ∈ S4F)
    (he2 : 2 ≤ e) (hcard : SF.card = 2 * e)
    (hON₁ : ∀ i ∈ SF, ∀ j ∈ SF,
      ClassFunction.inner (θ₁ i) (θ₁ j) = if i = j then 1 else 0)
    (hON₃ : ∀ i ∈ S4F, ∀ j ∈ S4F,
      ClassFunction.inner (θ₃ i) (θ₃ j) = if i = j then 1 else 0)
    (hcross : ∀ i ∈ SF, ∀ j ∈ S4F, ClassFunction.inner (θ₁ i) (θ₃ j) = 0)
    (hθ₃Z : ∀ j ∈ S4F, θ₃ j ∈ ZIrr Γ') (hθ₁Z : ∀ i ∈ SF, θ₁ i ∈ ZIrr Γ')
    (hTBZ : TB ∈ ZIrr Γ')
    (hTBnorm : ClassFunction.inner TB TB = ((e : ℂ)) ^ 2 + 1)
    (hTBconst : ∀ i ∈ SF, i ≠ ψ₁ →
      ClassFunction.inner TB (θ₁ i) = ClassFunction.inner TB (θ₁ ψ₁) + (e : ℂ))
    (hTBD : ClassFunction.inner TB (θ₃ l₁) - ClassFunction.inner TB (θ₃ l₂) = 1)
    (hTATB : ClassFunction.inner TA TB = (e : ℂ))
    (hTAθ₃ : ∀ j ∈ S4F, ClassFunction.inner TA (θ₃ j) = 0)
    (hTAconst : ∀ i ∈ SF, i ≠ ψ₁ →
      ClassFunction.inner TA (θ₁ i) = ClassFunction.inner TA (θ₁ ψ₁) + 1)
    (hTAψ₁int : ∃ m : ℤ, ClassFunction.inner TA (θ₁ ψ₁) = (m : ℂ))
    (hTBψ₁int : ∃ m : ℤ, ClassFunction.inner TB (θ₁ ψ₁) = (m : ℂ))
    (hTBθ₃int : ∀ j ∈ S4F, ∃ m : ℤ, ClassFunction.inner TB (θ₃ j) = (m : ℂ)) :
    ∃ X : ClassFunction Γ' ℂ, X ∈ ZIrr Γ' ∧
      ClassFunction.inner X X = 1 ∧
      (∀ i ∈ SF, ClassFunction.inner (θ₁ i) X = 0) ∧
      ClassFunction.inner X (θ₃ l₁) - ClassFunction.inner X (θ₃ l₂) = 1 ∧
      TB = X - (e : ℂ) • θ₁ ψ₁ := by
  classical
  choose! mΓ hmΓ using hTBθ₃int
  obtain ⟨mψ, hmψ⟩ := hTBψ₁int
  -- the three projection components
  set Γ0 : ClassFunction Γ' ℂ :=
    ∑ j ∈ S4F, ClassFunction.inner TB (θ₃ j) • θ₃ j with hΓ0
  set B0 : ClassFunction Γ' ℂ :=
    ∑ i ∈ SF, ClassFunction.inner TB (θ₁ i) • θ₁ i with hB0
  set Δ0 : ClassFunction Γ' ℂ := TB - Γ0 - B0 with hΔ0
  -- sum expansions
  have hΓ0L : ∀ ψ : ClassFunction Γ' ℂ, ClassFunction.inner Γ0 ψ
      = ∑ j ∈ S4F, ClassFunction.inner TB (θ₃ j) * ClassFunction.inner (θ₃ j) ψ := by
    intro ψ
    rw [hΓ0, OddOrder.RepresentationTheory.inner_sum_left]
    exact Finset.sum_congr rfl fun j _ => by rw [ClassFunction.inner_smul_left]
  have hΓ0R : ∀ ψ : ClassFunction Γ' ℂ, ClassFunction.inner ψ Γ0
      = ∑ j ∈ S4F, star (ClassFunction.inner TB (θ₃ j)) * ClassFunction.inner ψ (θ₃ j) := by
    intro ψ
    rw [hΓ0, OddOrder.RepresentationTheory.inner_sum_right]
    exact Finset.sum_congr rfl fun j _ => by
      rw [OddOrder.RepresentationTheory.inner_smul_right]
  have hB0L : ∀ ψ : ClassFunction Γ' ℂ, ClassFunction.inner B0 ψ
      = ∑ i ∈ SF, ClassFunction.inner TB (θ₁ i) * ClassFunction.inner (θ₁ i) ψ := by
    intro ψ
    rw [hB0, OddOrder.RepresentationTheory.inner_sum_left]
    exact Finset.sum_congr rfl fun i _ => by rw [ClassFunction.inner_smul_left]
  have hB0R : ∀ ψ : ClassFunction Γ' ℂ, ClassFunction.inner ψ B0
      = ∑ i ∈ SF, star (ClassFunction.inner TB (θ₁ i)) * ClassFunction.inner ψ (θ₁ i) := by
    intro ψ
    rw [hB0, OddOrder.RepresentationTheory.inner_sum_right]
    exact Finset.sum_congr rfl fun i _ => by
      rw [OddOrder.RepresentationTheory.inner_smul_right]
  -- projections onto the two families
  have hΓ0proj : ∀ j₀ ∈ S4F, ClassFunction.inner Γ0 (θ₃ j₀)
      = ClassFunction.inner TB (θ₃ j₀) := by
    intro j₀ hj₀
    rw [hΓ0L (θ₃ j₀),
      Finset.sum_eq_single j₀
        (fun j hj hne => by rw [hON₃ j hj j₀ hj₀, if_neg hne, mul_zero])
        (fun h => absurd hj₀ h),
      hON₃ j₀ hj₀ j₀ hj₀, if_pos rfl, mul_one]
  have hB0proj : ∀ i₀ ∈ SF, ClassFunction.inner B0 (θ₁ i₀)
      = ClassFunction.inner TB (θ₁ i₀) := by
    intro i₀ hi₀
    rw [hB0L (θ₁ i₀),
      Finset.sum_eq_single i₀
        (fun i hi hne => by rw [hON₁ i hi i₀ hi₀, if_neg hne, mul_zero])
        (fun h => absurd hi₀ h),
      hON₁ i₀ hi₀ i₀ hi₀, if_pos rfl, mul_one]
  have hB0θ₃ : ∀ j ∈ S4F, ClassFunction.inner B0 (θ₃ j) = 0 := by
    intro j hj
    rw [hB0L (θ₃ j)]
    exact Finset.sum_eq_zero fun i hi => by rw [hcross i hi j hj, mul_zero]
  have hΓ0θ₁ : ∀ i ∈ SF, ClassFunction.inner Γ0 (θ₁ i) = 0 := by
    intro i hi
    rw [hΓ0L (θ₁ i)]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [OddOrder.RepresentationTheory.inner_conj_symm (θ₁ i) (θ₃ j), hcross i hi j hj,
      star_zero, mul_zero]
  have hθ₁Γ0 : ∀ i ∈ SF, ClassFunction.inner (θ₁ i) Γ0 = 0 := by
    intro i hi
    rw [hΓ0R (θ₁ i)]
    exact Finset.sum_eq_zero fun j hj => by rw [hcross i hi j hj, mul_zero]
  -- the residual is orthogonal to both families
  have hΔθ₃ : ∀ j ∈ S4F, ClassFunction.inner Δ0 (θ₃ j) = 0 := by
    intro j hj
    rw [hΔ0, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
      hΓ0proj j hj, hB0θ₃ j hj, sub_zero, sub_self]
  have hΔθ₁ : ∀ i ∈ SF, ClassFunction.inner Δ0 (θ₁ i) = 0 := by
    intro i hi
    rw [hΔ0, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
      hΓ0θ₁ i hi, hB0proj i hi, sub_zero, sub_self]
  -- the split `TB = Γ0 + B0 + Δ0`
  have hTBsplit : TB = Γ0 + B0 + Δ0 := by rw [hΔ0]; abel
  -- cross inner products vanish
  have hΓ0B0 : ClassFunction.inner Γ0 B0 = 0 := by
    rw [hB0R Γ0]
    exact Finset.sum_eq_zero fun i hi => by rw [hΓ0θ₁ i hi, mul_zero]
  have hB0Γ0 : ClassFunction.inner B0 Γ0 = 0 := by
    rw [hΓ0R B0]
    exact Finset.sum_eq_zero fun j hj => by rw [hB0θ₃ j hj, mul_zero]
  have hΔ0Γ0 : ClassFunction.inner Δ0 Γ0 = 0 := by
    rw [hΓ0R Δ0]
    exact Finset.sum_eq_zero fun j hj => by rw [hΔθ₃ j hj, mul_zero]
  have hΓ0Δ0 : ClassFunction.inner Γ0 Δ0 = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm Δ0 Γ0, hΔ0Γ0, star_zero]
  have hΔ0B0 : ClassFunction.inner Δ0 B0 = 0 := by
    rw [hB0R Δ0]
    exact Finset.sum_eq_zero fun i hi => by rw [hΔθ₁ i hi, mul_zero]
  have hB0Δ0 : ClassFunction.inner B0 Δ0 = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm Δ0 B0, hΔ0B0, star_zero]
  -- Pythagoras
  have hPyth : ClassFunction.inner TB TB
      = ClassFunction.inner Γ0 Γ0 + ClassFunction.inner B0 B0
        + ClassFunction.inner Δ0 Δ0 := by
    conv_lhs => rw [hTBsplit]
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_left,
      ClassFunction.inner_add_right, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right, ClassFunction.inner_add_right,
      hΓ0B0, hB0Γ0, hΔ0Γ0, hΓ0Δ0, hΔ0B0, hB0Δ0]
    ring
  -- `‖Γ0‖² = ∑ mΓ²`
  have hΓ0norm : ClassFunction.inner Γ0 Γ0 = ((∑ j ∈ S4F, mΓ j ^ 2 : ℤ) : ℂ) := by
    rw [hΓ0R Γ0, Int.cast_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hΓ0proj j hj, hmΓ j hj, star_intCast]
    push_cast
    ring
  -- `‖B0‖² = mψ² + (2e−1)(mψ+e)²`
  have hbval : ∀ i ∈ SF, i ≠ ψ₁ →
      ClassFunction.inner TB (θ₁ i) = ((mψ + (e : ℤ) : ℤ) : ℂ) := by
    intro i hi hne
    rw [hTBconst i hi hne, hmψ]
    push_cast
    ring
  have hB0norm : ClassFunction.inner B0 B0
      = ((mψ ^ 2 + (2 * (e : ℤ) - 1) * (mψ + (e : ℤ)) ^ 2 : ℤ) : ℂ) := by
    rw [hB0R B0, ← Finset.add_sum_erase SF _ hψ₁SF]
    have herase : ∀ i ∈ SF.erase ψ₁,
        star (ClassFunction.inner TB (θ₁ i)) * ClassFunction.inner B0 (θ₁ i)
          = (((mψ + (e : ℤ)) ^ 2 : ℤ) : ℂ) := by
      intro i hi
      have hiSF := Finset.mem_of_mem_erase hi
      have hine := Finset.ne_of_mem_erase hi
      rw [hB0proj i hiSF, hbval i hiSF hine, star_intCast]
      push_cast
      ring
    rw [Finset.sum_congr rfl herase, Finset.sum_const, Finset.card_erase_of_mem hψ₁SF,
      hcard, hB0proj ψ₁ hψ₁SF, hmψ, star_intCast, nsmul_eq_mul,
      Nat.cast_sub (show 1 ≤ 2 * e from by omega)]
    push_cast
    ring
  -- `‖Δ0‖²` is a nonnegative integer
  have hΔ0Z : Δ0 ∈ ZIrr Γ' := by
    rw [hΔ0]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ hTBZ ?_) ?_
    · rw [hΓ0]
      refine Submodule.sum_mem _ fun j hj => ?_
      rw [hmΓ j hj, Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ (hθ₃Z j hj)
    · rw [hB0]
      refine Submodule.sum_mem _ fun i hi => ?_
      by_cases hne : i = ψ₁
      · subst hne
        rw [hmψ, Int.cast_smul_eq_zsmul]
        exact Submodule.smul_mem _ _ (hθ₁Z i hi)
      · rw [hbval i hi hne, Int.cast_smul_eq_zsmul]
        exact Submodule.smul_mem _ _ (hθ₁Z i hi)
  obtain ⟨cΔ, -, -, hcΔsum⟩ :=
    OddOrder.RepresentationTheory.mem_ZIrr_inner_self_eq_sum_sq hΔ0Z
  have hΔval : ClassFunction.inner Δ0 Δ0
      = ((∑ x ∈ cΔ.support, cΔ x ^ 2 : ℤ) : ℂ) := by
    rw [hcΔsum]
    push_cast
    rfl
  have hsΔ0 : 0 ≤ ∑ x ∈ cΔ.support, cΔ x ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- `‖Γ0‖² ≥ 1`: the `l₁`/`l₂` coefficients differ by `1`
  have hmΓD : mΓ l₁ - mΓ l₂ = 1 := by
    have h : ((mΓ l₁ - mΓ l₂ : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by
      push_cast
      rw [← hmΓ l₁ hl₁, ← hmΓ l₂ hl₂]
      exact_mod_cast hTBD
    exact_mod_cast h
  have hsq1 : ∀ m : ℤ, m ≠ 0 → 1 ≤ m ^ 2 := by
    intro m hm
    rcases lt_or_gt_of_ne hm with h | h <;> nlinarith
  have hsΓ1 : 1 ≤ ∑ j ∈ S4F, mΓ j ^ 2 := by
    rcases eq_or_ne (mΓ l₁) 0 with h1 | h1
    · have h2 : mΓ l₂ ≠ 0 := by omega
      exact le_trans (hsq1 _ h2)
        (Finset.single_le_sum (fun j _ => sq_nonneg (mΓ j)) hl₂)
    · exact le_trans (hsq1 _ h1)
        (Finset.single_le_sum (fun j _ => sq_nonneg (mΓ j)) hl₁)
  -- the integer budget
  have hbudget : (e : ℤ) ^ 2 + 1
      = (∑ j ∈ S4F, mΓ j ^ 2) + (mψ ^ 2 + (2 * (e : ℤ) - 1) * (mψ + (e : ℤ)) ^ 2)
        + ∑ x ∈ cΔ.support, cΔ x ^ 2 := by
    have h : (((e : ℤ) ^ 2 + 1 : ℤ) : ℂ)
        = (((∑ j ∈ S4F, mΓ j ^ 2) + (mψ ^ 2 + (2 * (e : ℤ) - 1) * (mψ + (e : ℤ)) ^ 2)
            + ∑ x ∈ cΔ.support, cΔ x ^ 2 : ℤ) : ℂ) := by
      push_cast
      rw [show ((e : ℂ)) ^ 2 + 1 = ClassFunction.inner TB TB from hTBnorm.symm, hPyth,
        hΓ0norm, hB0norm, hΔval]
      push_cast
      ring
    exact_mod_cast h
  -- pin the budget: `‖Γ0‖² = 1`, `mb(mb−1) = 0`, `‖Δ0‖² = 0`
  have hmb4 : -1 ≤ 4 * ((mψ + (e : ℤ)) * ((mψ + (e : ℤ)) - 1)) := by
    nlinarith [sq_nonneg (2 * (mψ + (e : ℤ)) - 1)]
  have hmbnn : 0 ≤ (mψ + (e : ℤ)) * ((mψ + (e : ℤ)) - 1) := by omega
  have hbudget' : 1 = (∑ j ∈ S4F, mΓ j ^ 2)
      + 2 * (e : ℤ) * ((mψ + (e : ℤ)) * ((mψ + (e : ℤ)) - 1))
      + ∑ x ∈ cΔ.support, cΔ x ^ 2 := by linear_combination hbudget
  have heZ2 : (2 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he2
  have h2emb : 0 ≤ 2 * (e : ℤ) * ((mψ + (e : ℤ)) * ((mψ + (e : ℤ)) - 1)) := by positivity
  have hsΓeq : ∑ j ∈ S4F, mΓ j ^ 2 = 1 := by linarith
  have h2emb0 : 2 * (e : ℤ) * ((mψ + (e : ℤ)) * ((mψ + (e : ℤ)) - 1)) = 0 := by linarith
  have hsΔeq : ∑ x ∈ cΔ.support, cΔ x ^ 2 = 0 := by linarith
  have hmb01 : mψ + (e : ℤ) = 0 ∨ mψ + (e : ℤ) = 1 := by
    have h := mul_eq_zero.mp
      ((mul_eq_zero.mp h2emb0).resolve_left (by omega : ¬ 2 * (e : ℤ) = 0))
    omega
  -- `Δ0 = 0`
  have hΔzero : Δ0 = 0 := by
    apply OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero
    rw [hΔval, hsΔeq]
    simp
  -- (9.11.8): the `⟨TA, TB⟩ = e` pairing eliminates `mb = 1`
  obtain ⟨mx, hmx⟩ := hTAψ₁int
  have hTAB0 : ClassFunction.inner TA B0
      = ((mψ * mx + (2 * (e : ℤ) - 1) * (mψ + (e : ℤ)) * (mx + 1) : ℤ) : ℂ) := by
    rw [hB0R TA, ← Finset.add_sum_erase SF _ hψ₁SF]
    have herase : ∀ i ∈ SF.erase ψ₁,
        star (ClassFunction.inner TB (θ₁ i)) * ClassFunction.inner TA (θ₁ i)
          = (((mψ + (e : ℤ)) * (mx + 1) : ℤ) : ℂ) := by
      intro i hi
      have hiSF := Finset.mem_of_mem_erase hi
      have hine := Finset.ne_of_mem_erase hi
      rw [hbval i hiSF hine, hTAconst i hiSF hine, hmx, star_intCast]
      push_cast
      ring
    rw [Finset.sum_congr rfl herase, Finset.sum_const, Finset.card_erase_of_mem hψ₁SF,
      hcard, hmψ, hmx, star_intCast, nsmul_eq_mul,
      Nat.cast_sub (show 1 ≤ 2 * e from by omega)]
    push_cast
    ring
  have hTAΓ0 : ClassFunction.inner TA Γ0 = 0 := by
    rw [hΓ0R TA]
    exact Finset.sum_eq_zero fun j hj => by rw [hTAθ₃ j hj, mul_zero]
  have hpairing : (e : ℤ) = mψ * mx + (2 * (e : ℤ) - 1) * (mψ + (e : ℤ)) * (mx + 1) := by
    have h : ((e : ℤ) : ℂ)
        = ((mψ * mx + (2 * (e : ℤ) - 1) * (mψ + (e : ℤ)) * (mx + 1) : ℤ) : ℂ) := by
      rw [show ((e : ℤ) : ℂ) = (e : ℂ) from by push_cast; rfl, ← hTATB]
      conv_lhs => rw [hTBsplit]
      rw [ClassFunction.inner_add_right, ClassFunction.inner_add_right, hTAΓ0,
        hΔzero, ClassFunction.inner_zero_right, add_zero, zero_add, hTAB0]
    exact_mod_cast h
  have hmb0 : mψ + (e : ℤ) = 0 := by
    rcases hmb01 with h | h
    · exact h
    · exfalso
      -- `mb = 1` forces `e·(mx+1) = 1`, impossible for `e ≥ 2`
      have hmψe : mψ = 1 - (e : ℤ) := by omega
      have hkey : (e : ℤ) * (mx + 1) = 1 := by
        rw [hmψe] at hpairing
        linear_combination -hpairing
      have hdvd : (e : ℤ) ∣ 1 := ⟨mx + 1, hkey.symm⟩
      have := Int.le_of_dvd one_pos hdvd
      omega
  -- the `b = 0` bridge: `B0 = −e·θ₁ψ₁` and `TB = Γ0 − e·θ₁ψ₁`
  have hB0eq : B0 = -(e : ℂ) • θ₁ ψ₁ := by
    rw [hB0,
      Finset.sum_eq_single ψ₁
        (fun i hi hne => by
          rw [hbval i hi hne, show mψ + (e : ℤ) = 0 from hmb0, Int.cast_zero, zero_smul])
        (fun h => absurd hψ₁SF h),
      hmψ, show mψ = -(e : ℤ) from by omega]
    push_cast
    ring_nf
  have hTBfinal : TB = Γ0 - (e : ℂ) • θ₁ ψ₁ := by
    rw [hTBsplit, hΔzero, hB0eq]
    module
  -- assemble the output
  refine ⟨Γ0, ?_, ?_, hθ₁Γ0, ?_, hTBfinal⟩
  · rw [hΓ0]
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [hmΓ j hj, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (hθ₃Z j hj)
  · rw [hΓ0norm, hsΓeq]
    simp
  · rw [hΓ0proj l₁ hl₁, hΓ0proj l₂ hl₂]
    exact hTBD

end ProjectionBudget

/-! ### The (9.11.7)–(9.11.8) discharge -/

section Discharge

variable [Finite G]

set_option maxHeartbeats 3200000 in
-- threads the `hyp.base.tau = dadeIntegralCharacterMap` defeq through the ZIrr/isometry
-- layers while assembling the ~20 scalar inputs of the projection budget
/-- **Peterfalvi (9.11.7)–(9.11.8), discharged** (issue 9083 Phase E-final; Coq
`PFsection9.v:2048-2227`, the tail of `Ptype_core_coherence`).

In the orthogonal branch `α^τ ⊥ 𝒮₃^{τ₃}` of the (9.11.6) dichotomy: `𝒮₄ ≠ ∅` (else the
(9.11.2)–(9.11.5) arithmetic spine already refutes, since `|𝒮₄| = 0 ≤ N`); pick `λ₁ ∈ 𝒮₄`,
put `e = u/a = [U₁ : C] ≥ 2` (`a ∣ u` by the `C ≤ U₁ ≤ U` index chain; `u ≠ a` since a
degree-`qa` irreducible member would lie in `𝒮₁ ⊆ 𝒮₂`) and `β = λ₁ − e·ψ₁`.  The projection
budget (`exists_bridge_target_of_budget`) applied to `β^τ` and `α^τ` over the orthonormal
families `𝒮₂^{τ₁}` (`|𝒮₂| = 2e` by the (9.8.d) count at the equality configuration) and
`𝒮₄^{τ₃}` — cross-orthogonal by `coherent_extension_cross_orthogonal` — produces
`Γ ∈ ℤ[Irr G]` with `‖Γ‖² = 1`, `Γ ⊥ 𝒮₂^{τ₁}`, `⟨Γ, λ₁^{τ₃}⟩ − ⟨Γ, λ̄₁^{τ₃}⟩ = 1` and the
bridge `β^τ = Γ − e·τ₁ψ₁`.  The union-pair extension (`isCoherent_union_pair_of_bridge`,
with `X = Γ`, `Xc = Γ − (λ₁ − λ̄₁)^τ`) then adjoins `{λ₁, λ̄₁}` coherently to `𝒮₂`,
contradicting the maximality pair clause `hpairs`. -/
theorem nineElevenSevenEightRefutation
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    (hncH0C : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    NineElevenSevenEightRefutation hyp caseA := by
  haveI := hyp.base.finiteG
  classical
  intro S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs h2a hCUprime hS3deg hcount hFbound hS2deg
    c₃ γ ψ₁ hψ₁S₂ hψ₁irr hψ₁deg hγZIrr hγ1 hγorth hαsupp hc
  obtain ⟨c₁⟩ := hS₂coh
  -- ── ambient family facts
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun x hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hSfin : (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime).Finite :=
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_finite
        (K := (derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M)).subset
      (fun x hx => by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  have hS₂fin : S₂.Finite := hSfin.subset hS₂sub
  have hS₂cut := caseA_sTwo_subset_degreeQaCut hG hyp caseA hS₁sub hS₂sub h2a hCUprime
    hcount hFbound
  have hψ₁sOf : ψ₁ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime := hS₂sub hψ₁S₂
  have hselfone : ∀ {χ : ClassFunction ↥M ℂ}, IsIrreducibleCharacter χ →
      ClassFunction.inner χ χ = 1 := by
    intro χ hχ
    have h := irreducibleCharacter_inner_eq_ite
      (⟨χ, hχ⟩ : IrreducibleCharacter ↥M) ⟨χ, hχ⟩
    rwa [if_pos rfl] at h
  -- ── the (9.11.2) TI-witness supplies `U₁` with `C ≤ U₁ ≤ U`, `[U:U₁] = a`
  obtain ⟨U₁, hCU₁, hU₁U, hU₁a, -⟩ :=
    caseA_nineElevenTwo_tiWitness hG hyp caseA hS3deg hS2deg hncH0C htype
  obtain ⟨e, hedef⟩ : ∃ e : ℕ,
      e = (OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief).relIndex U₁ := ⟨_, rfl⟩
  have hue : e * caseA.a
      = (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u := by
    rw [hedef]
    have h := Subgroup.relIndex_mul_relIndex
      (OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief) U₁ hyp.s11Setup.U hCU₁ hU₁U
    rwa [hU₁a, OddOrder.Peterfalvi.S11.relIndex_cSub_U_eq_u
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)] at h
  -- ── the arithmetic spine refutes `|𝒮₄| ≤ N`, so `𝒮₄ ≠ ∅`
  obtain ⟨K₁, K₂, hK₁, hK₂, hCinf⟩ :=
    caseA_two_summand_inertia_inputs hG hyp caseA hS3deg hS2deg hncH0C htype
  have hclass := caseA_nineElevenThree_count_inputs hG hyp caseA hS₁sub hS3deg hS2deg
    hCUprime hcount hncH0C htype
  obtain ⟨N, hnorm, -⟩ := caseA_nineElevenFour_norm_inputs hyp caseA
    (caseA_nineElevenTwo_tiWitness hG hyp caseA hS3deg hS2deg hncH0C htype) hCUprime hcount
  have hqp : (hyp.s11Setup.q).Prime := hyp.s11Setup.nontrivial.2.1
  have hqodd : Odd hyp.s11Setup.q :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.s11Setup.typeP.W1)
  have hq3 : 3 ≤ hyp.s11Setup.q := by
    obtain ⟨k, hk⟩ := hqodd
    have h2 := hqp.two_le
    omega
  have hu1 : 1 ≤ (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u :=
    (OddOrder.Peterfalvi.S11.u_odd hG
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)).pos
  have hp1 : 1 < hyp.chief.p := hyp.chief.p_prime.one_lt
  have hpeq : hyp.chief.p = 2 * caseA.a + 1 := by omega
  have hS4ne : (nineElevenSFour hyp S₂).Nonempty := by
    rcases Set.eq_empty_or_nonempty (nineElevenSFour hyp S₂) with hemp | hne
    · exact absurd
        (OddOrder.Peterfalvi.S11.nineElevenCaseA_equality_refutation caseA hq3 hu1 hpeq
          hK₁ hK₂ hCinf hclass rfl hnorm
          (by rw [hemp, Set.ncard_empty]; exact Nat.zero_le N))
        not_false
    · exact hne
  obtain ⟨lam₁, hlam₁S₄⟩ := hS4ne
  obtain ⟨hlam₁sOfC, hlam₁irr, hlam₁nS₂⟩ := hlam₁S₄
  -- ── `𝒮₄ ⊆ 𝒮₃` along `H₀C′ ≤ H₀C`; the pair `{λ₁, λ̄₁}` lives in `𝒮₄`
  have hleC : hyp.H0Cprime
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief := by
    change hyp.chief.H0 ⊔ derivedInG hyp.C ≤ _
    refine sup_le_sup_left ?_ hyp.chief.H0
    rw [C_eq_cSub_of_noncoherent hG hyp hncH0C htype]
    exact OddOrder.Peterfalvi.S11.cprimeSub_le_C hyp.s11Setup hyp.chief
  have hS4sub : nineElevenSFour hyp S₂
      ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂ := fun ξ hξ =>
    ⟨OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup hleC hξ.1, hξ.2.2⟩
  have hlam₁S₃ : lam₁ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂ :=
    hS4sub ⟨hlam₁sOfC, hlam₁irr, hlam₁nS₂⟩
  have hlam₁c_S₄ : lam₁.conj ∈ nineElevenSFour hyp S₂ := by
    refine ⟨OddOrder.Peterfalvi.S11.sOf_closedUnderConjugate hyp.s11Setup _ hlam₁sOfC,
      hlam₁irr.conj, ?_⟩
    intro hmem
    apply hlam₁nS₂
    have h := hS₂conj hmem
    rwa [ClassFunction.conj_conj] at h
  have hlam₁cS₃ : lam₁.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂ :=
    hS4sub hlam₁c_S₄
  have hlam₁ne : lam₁ ≠ lam₁.conj := fun h =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd _
      (hIKF hlam₁S₃.1) h.symm
  have hlam₁deg : (lam₁ : ↥M → ℂ) 1 = ((hyp.s11Setup.q
      * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℂ) :=
    hS3deg lam₁ hlam₁S₃
  -- ── `e ≥ 2`: `u ≠ a` since a degree-`qa` irreducible member would lie in `𝒮₁ ⊆ 𝒮₂`
  have hune : (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u ≠ caseA.a := by
    intro huea
    apply hlam₁nS₂
    apply hS₁sub
    refine ⟨hlam₁S₃.1, hlam₁irr, ?_⟩
    rw [hlam₁deg, huea]
  have he2 : 2 ≤ e := by
    have ha1 : 1 ≤ caseA.a := caseA.a_pos
    rcases Nat.lt_or_ge e 2 with h | h
    · exfalso
      interval_cases e
      · rw [zero_mul] at hue
        omega
      · rw [one_mul] at hue
        exact hune hue.symm
    · exact h
  -- ── `|𝒮₂| = 2e` from the (9.8.d) count at the equality configuration
  have hS₂eq : S₂ = {φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
      (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
      IsIrreducibleCharacter φ ∧
      φ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)} := by
    refine Set.Subset.antisymm hS₂cut ?_
    have hCUle : hyp.C ≤ hyp.s11Setup.U := by
      change hyp.C ≤ hyp.s11Setup.typeP.U
      rw [hyp.setup_typeP_eq]; exact hyp.C_le_U
    have hleU' : hyp.H0Cprime
        ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup := by
      change hyp.chief.H0 ⊔ derivedInG hyp.C
        ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup
      refine sup_le_sup_left ?_ hyp.chief.H0
      change derivedInG hyp.C ≤ derivedInG hyp.s11Setup.U
      rw [OddOrder.Peterfalvi.S11.derivedInG_eq_commutator hyp.C,
        OddOrder.Peterfalvi.S11.derivedInG_eq_commutator hyp.s11Setup.U]
      exact Subgroup.commutator_mono hCUle hCUle
    exact fun φ hφ =>
      hS₁sub ⟨OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup hleU' hφ.1, hφ.2.1, hφ.2.2⟩
  have hcardS₂ : hS₂fin.toFinset.card = 2 * e := by
    have hrelu : (OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U
        = (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u := by
      have hUpC : OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief
          = OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup := hCUprime
      rw [← hUpC]
      exact OddOrder.Peterfalvi.S11.relIndex_cSub_U_eq_u _
    have hcount' : S₂.ncard * (caseA.a * caseA.a) = 2 * e * (caseA.a * caseA.a) := by
      rw [hS₂eq, hcount, hrelu, ← h2a, ← hue]
      ring
    have ha0 : 0 < caseA.a * caseA.a := Nat.mul_pos caseA.a_pos caseA.a_pos
    have hncard : S₂.ncard = 2 * e := Nat.eq_of_mul_eq_mul_right ha0 hcount'
    rw [← Set.ncard_eq_toFinset_card _ hS₂fin]
    exact hncard
  -- ── orthonormality of the source families
  have hON1 : ∀ φ ∈ S₂, ClassFunction.inner φ φ = 1 := fun φ hφ =>
    hselfone (hS₂cut hφ).2.1
  have hON2 : ∀ φ ∈ S₂, ∀ ξ ∈ S₂, φ ≠ ξ → ClassFunction.inner φ ξ = 0 :=
    fun φ hφ ξ hξ hne =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF (hS₂sub hφ)) (hIKF (hS₂sub hξ)) hne
  -- ── `𝒮₃` is conjugation-closed; cross-orthogonality of the coherent images
  have hS₃sub : OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂
      ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime := Set.sdiff_subset
  have hS₃conj : ∀ x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      x.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂ := by
    intro x hx
    refine ⟨OddOrder.Peterfalvi.S11.sOf_closedUnderConjugate hyp.s11Setup hyp.H0Cprime hx.1, ?_⟩
    intro hcmem
    apply hx.2
    have h := hS₂conj hcmem
    rwa [ClassFunction.conj_conj] at h
  have hcross : ∀ φ ∈ S₂,
      ∀ lam ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      ClassFunction.inner (c₁.extension φ) (c₃.extension lam) = 0 := by
    intro φ hφ lam hlam
    exact coherent_extension_cross_orthogonal hG hyp hS₂sub hS₃sub c₁ c₃
      hφ (hS₂conj hφ) hlam (hS₃conj lam hlam)
      (fun h => hlam.2 (h ▸ hφ)) (fun h => (hS₃conj lam hlam).2 (h ▸ hφ))
  -- ── `β = λ₁ − e·ψ₁`: support, integrality, `τ`-image
  have hβdegℂ : (lam₁ : ↥M → ℂ) 1 = ((e : ℕ) : ℂ) * (ψ₁ : ↥M → ℂ) 1 := by
    rw [hlam₁deg, hψ₁deg, ← hue]
    push_cast
    ring
  have hβsupp : ((lam₁ - e • ψ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support
      hyp.base.mderivSharp_subset_A0 (hIKF hlam₁S₃.1) (hIKF hψ₁sOf) hβdegℂ
  have hβsmul : (lam₁ - e • ψ₁ : ClassFunction ↥M ℂ) = lam₁ - ((e : ℕ) : ℂ) • ψ₁ := by
    rw [Nat.cast_smul_eq_nsmul]
  have hβZIrr : (lam₁ - e • ψ₁ : ClassFunction ↥M ℂ) ∈ ZIrr ↥M :=
    Submodule.sub_mem _
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hlam₁S₃.1))
      (nsmul_mem (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hψ₁sOf)) e)
  have hτβZ : hyp.base.tau (lam₁ - e • ψ₁) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.base.dadeData.dade hyp.base.hconj hβsupp hβZIrr
  have hαZIrr : (γ - ψ₁ : ClassFunction ↥M ℂ) ∈ ZIrr ↥M :=
    Submodule.sub_mem _ hγZIrr
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hψ₁sOf))
  have hταZ : hyp.base.tau (γ - ψ₁) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.base.dadeData.dade hyp.base.hconj hαsupp hαZIrr
  -- ── supported differences and their `τ₁`/`τ₃` images
  have hψdiffsupp : ∀ φ ∈ S₂,
      ((φ - ψ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := by
    intro φ hφ
    have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support
      hyp.base.mderivSharp_subset_A0 (hIKF (hS₂sub hφ)) (hIKF hψ₁sOf) (d := 1)
      (by rw [Nat.cast_one, one_mul, hS2deg φ hφ, hψ₁deg])
    rwa [one_smul] at h
  have hτ₁diff : ∀ φ ∈ S₂,
      hyp.base.tau (φ - ψ₁) = c₁.extension φ - c₁.extension ψ₁ := by
    intro φ hφ
    rw [← map_sub]
    exact (c₁.extends_on_supported (φ - ψ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hφ) (Submodule.subset_span hψ₁S₂),
        hψdiffsupp φ hφ⟩).symm
  have hDsupp : ((lam₁ - lam₁.conj : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := by
    rw [show (lam₁ - lam₁.conj : ClassFunction ↥M ℂ) = -(lam₁.conj - lam₁) from by abel,
      ClassFunction.support_neg]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 (hIKF hlam₁S₃.1)
  have hτD : hyp.base.tau (lam₁ - lam₁.conj)
      = c₃.extension lam₁ - c₃.extension lam₁.conj := by
    rw [← map_sub]
    exact (c₃.extends_on_supported (lam₁ - lam₁.conj)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hlam₁S₃)
        (Submodule.subset_span hlam₁cS₃), hDsupp⟩).symm
  -- ── scalar values at the source
  have hll1 : ClassFunction.inner lam₁ lam₁ = 1 := hselfone hlam₁irr
  have hlclc : ClassFunction.inner lam₁.conj lam₁.conj = 1 := hselfone hlam₁irr.conj
  have hllc : ClassFunction.inner lam₁ lam₁.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF hlam₁S₃.1) (hIKF hlam₁cS₃.1) hlam₁ne
  have hψψ : ClassFunction.inner ψ₁ ψ₁ = 1 := hON1 ψ₁ hψ₁S₂
  have hψl : ClassFunction.inner ψ₁ lam₁ = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF hψ₁sOf) (hIKF hlam₁S₃.1) (fun h => hlam₁nS₂ (h ▸ hψ₁S₂))
  have hψlc : ClassFunction.inner ψ₁ lam₁.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF hψ₁sOf) (hIKF hlam₁cS₃.1) (fun h => hlam₁cS₃.2 (h ▸ hψ₁S₂))
  have hlψ : ClassFunction.inner lam₁ ψ₁ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ₁ lam₁, hψl, star_zero]
  have hlcψ : ClassFunction.inner lam₁.conj ψ₁ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ₁ lam₁.conj, hψlc, star_zero]
  have hlcl : ClassFunction.inner lam₁.conj lam₁ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm lam₁ lam₁.conj, hllc, star_zero]
  -- ── the budget inputs
  have hS4fin : (nineElevenSFour hyp S₂).Finite :=
    hSfin.subset (fun ξ hξ => (hS4sub hξ).1)
  have hτβnorm : ClassFunction.inner (hyp.base.tau (lam₁ - e • ψ₁))
      (hyp.base.tau (lam₁ - e • ψ₁)) = ((e : ℕ) : ℂ) ^ 2 + 1 := by
    rw [hyp.base.tau_inner_eq_of_supported hβsupp hβsupp, hβsmul]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hll1, hlψ, hψl, hψψ, star_natCast, mul_zero, mul_one, sub_zero, zero_sub]
    ring
  have hτβconst : ∀ φ ∈ hS₂fin.toFinset, φ ≠ ψ₁ →
      ClassFunction.inner (hyp.base.tau (lam₁ - e • ψ₁)) (c₁.extension φ)
        = ClassFunction.inner (hyp.base.tau (lam₁ - e • ψ₁)) (c₁.extension ψ₁)
          + ((e : ℕ) : ℂ) := by
    intro φ hφF hφne
    have hφ := hS₂fin.mem_toFinset.mp hφF
    have hβφ : ClassFunction.inner (lam₁ - e • ψ₁ : ClassFunction ↥M ℂ) (φ - ψ₁)
        = ((e : ℕ) : ℂ) := by
      rw [hβsmul]
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, hlψ, hψψ,
        hON2 ψ₁ hψ₁S₂ φ hφ (fun h => hφne h.symm),
        show ClassFunction.inner lam₁ φ = 0 from by
          rw [OddOrder.RepresentationTheory.inner_conj_symm φ lam₁,
            OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
              (hIKF (hS₂sub hφ)) (hIKF hlam₁S₃.1) (fun h => hlam₁nS₂ (h ▸ hφ)),
            star_zero],
        mul_zero, mul_one, sub_zero, zero_sub, sub_neg_eq_add, zero_add]
    have hiso := hyp.base.tau_inner_eq_of_supported hβsupp (hψdiffsupp φ hφ)
    rw [hτ₁diff φ hφ, ClassFunction.inner_sub_right, hβφ] at hiso
    linear_combination hiso
  have hτβD : ClassFunction.inner (hyp.base.tau (lam₁ - e • ψ₁)) (c₃.extension lam₁)
      - ClassFunction.inner (hyp.base.tau (lam₁ - e • ψ₁)) (c₃.extension lam₁.conj)
        = 1 := by
    have hβD : ClassFunction.inner (lam₁ - e • ψ₁ : ClassFunction ↥M ℂ)
        (lam₁ - lam₁.conj) = 1 := by
      rw [hβsmul]
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, hll1, hllc, hψl, hψlc, mul_zero, sub_zero]
    have hiso := hyp.base.tau_inner_eq_of_supported hβsupp hDsupp
    rw [hτD, ClassFunction.inner_sub_right, hβD] at hiso
    exact hiso
  have hτατβ : ClassFunction.inner (hyp.base.tau (γ - ψ₁))
      (hyp.base.tau (lam₁ - e • ψ₁)) = ((e : ℕ) : ℂ) := by
    rw [hyp.base.tau_inner_eq_of_supported hαsupp hβsupp, hβsmul]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      OddOrder.RepresentationTheory.inner_smul_right, hγorth lam₁ hlam₁S₃.1,
      hγorth ψ₁ hψ₁sOf, hψl, hψψ, star_natCast, mul_zero, mul_one, zero_sub, sub_zero,
      sub_neg_eq_add, zero_add]
  have hταconst : ∀ φ ∈ hS₂fin.toFinset, φ ≠ ψ₁ →
      ClassFunction.inner (hyp.base.tau (γ - ψ₁)) (c₁.extension φ)
        = ClassFunction.inner (hyp.base.tau (γ - ψ₁)) (c₁.extension ψ₁) + 1 := by
    intro φ hφF hφne
    have hφ := hS₂fin.mem_toFinset.mp hφF
    have hαφ : ClassFunction.inner (γ - ψ₁ : ClassFunction ↥M ℂ) (φ - ψ₁) = 1 := by
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        hγorth φ (hS₂sub hφ), hγorth ψ₁ hψ₁sOf, hψψ,
        hON2 ψ₁ hψ₁S₂ φ hφ (fun h => hφne h.symm), zero_sub, sub_neg_eq_add,
        zero_add, sub_self]
    have hiso := hyp.base.tau_inner_eq_of_supported hαsupp (hψdiffsupp φ hφ)
    rw [hτ₁diff φ hφ, ClassFunction.inner_sub_right, hαφ] at hiso
    linear_combination hiso
  -- ── run the projection budget
  obtain ⟨Γ0, hΓZ, hΓ1, hθ₁Γ, hΓD, hTBeq⟩ :=
    exists_bridge_target_of_budget (Γ' := G)
      (SF := hS₂fin.toFinset) (S4F := hS4fin.toFinset)
      (fun φ => c₁.extension φ) (fun ξ => c₃.extension ξ)
      (TB := hyp.base.tau (lam₁ - e • ψ₁)) (TA := hyp.base.tau (γ - ψ₁))
      (ψ₁ := ψ₁) (l₁ := lam₁) (l₂ := lam₁.conj) (e := e)
      (hS₂fin.mem_toFinset.mpr hψ₁S₂)
      (hS4fin.mem_toFinset.mpr ⟨hlam₁sOfC, hlam₁irr, hlam₁nS₂⟩)
      (hS4fin.mem_toFinset.mpr hlam₁c_S₄)
      he2 hcardS₂
      (by
        intro φ hφF ξ hξF
        have hφ := hS₂fin.mem_toFinset.mp hφF
        have hξ := hS₂fin.mem_toFinset.mp hξF
        rw [c₁.extension_inner_eq φ ξ (Submodule.subset_span hφ)
          (Submodule.subset_span hξ)]
        by_cases h : φ = ξ
        · subst h; rw [if_pos rfl]; exact hON1 φ hφ
        · rw [if_neg h]; exact hON2 φ hφ ξ hξ h)
      (by
        intro ξ hξF ξ' hξ'F
        have hξ := hS4sub (hS4fin.mem_toFinset.mp hξF)
        have hξ' := hS4sub (hS4fin.mem_toFinset.mp hξ'F)
        rw [c₃.extension_inner_eq ξ ξ' (Submodule.subset_span hξ)
          (Submodule.subset_span hξ')]
        by_cases h : ξ = ξ'
        · subst h
          rw [if_pos rfl]
          exact hselfone (hS4fin.mem_toFinset.mp hξF).2.1
        · rw [if_neg h]
          exact OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
            (hIKF hξ.1) (hIKF hξ'.1) h)
      (fun φ hφF ξ hξF => hcross φ (hS₂fin.mem_toFinset.mp hφF)
        ξ (hS4sub (hS4fin.mem_toFinset.mp hξF)))
      (fun ξ hξF => c₃.extension_mem_ZIrr ξ
        (Submodule.subset_span (hS4sub (hS4fin.mem_toFinset.mp hξF))))
      (fun φ hφF => c₁.extension_mem_ZIrr φ
        (Submodule.subset_span (hS₂fin.mem_toFinset.mp hφF)))
      hτβZ hτβnorm hτβconst hτβD hτατβ
      (fun ξ hξF => hc ξ (hS4sub (hS4fin.mem_toFinset.mp hξF)))
      hταconst
      (ClassFunction.inner_mem_ZIrr_int hταZ
        (c₁.extension_mem_ZIrr ψ₁ (Submodule.subset_span hψ₁S₂)))
      (ClassFunction.inner_mem_ZIrr_int hτβZ
        (c₁.extension_mem_ZIrr ψ₁ (Submodule.subset_span hψ₁S₂)))
      (fun ξ hξF => ClassFunction.inner_mem_ZIrr_int hτβZ
        (c₃.extension_mem_ZIrr ξ
          (Submodule.subset_span (hS4sub (hS4fin.mem_toFinset.mp hξF)))))
  -- ── the pair targets `X = Γ0`, `Xc = Γ0 − (λ₁ − λ̄₁)^τ`
  have hΓτD : ClassFunction.inner Γ0 (hyp.base.tau (lam₁ - lam₁.conj)) = 1 := by
    rw [hτD, ClassFunction.inner_sub_right, hΓD]
  have hτDΓ : ClassFunction.inner (hyp.base.tau (lam₁ - lam₁.conj)) Γ0 = 1 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm Γ0
      (hyp.base.tau (lam₁ - lam₁.conj)), hΓτD, star_one]
  have hτDτD : ClassFunction.inner (hyp.base.tau (lam₁ - lam₁.conj))
      (hyp.base.tau (lam₁ - lam₁.conj)) = 2 := by
    rw [hyp.base.tau_inner_eq_of_supported hDsupp hDsupp]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      hll1, hllc, hlcl, hlclc, sub_zero, zero_sub, sub_neg_eq_add]
    norm_num
  have hτDZ : hyp.base.tau (lam₁ - lam₁.conj) ∈ ZIrr G := by
    rw [hτD]
    exact Submodule.sub_mem _
      (c₃.extension_mem_ZIrr lam₁ (Submodule.subset_span hlam₁S₃))
      (c₃.extension_mem_ZIrr lam₁.conj (Submodule.subset_span hlam₁cS₃))
  -- ── adjoin the pair `{λ₁, λ̄₁}` coherently to `𝒮₂` (the (5.6.3) union-pair extension)
  have hunion : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (S₂ ∪ {lam₁, lam₁.conj}) hyp.base.A0 := by
    refine isCoherent_union_pair_of_bridge (E := ((e : ℕ) : ℤ)) hS₂fin hON1 hON2
      (fun φ hφ ξ hξ => c₁.extension_inner_eq φ ξ (Submodule.subset_span hφ)
        (Submodule.subset_span hξ))
      (fun φ hφ => c₁.extends_on_supported φ hφ)
      (fun φ hφ => c₁.extension_mem_ZIrr φ (Submodule.subset_span hφ))
      hlam₁ne hll1 hlclc hllc
      (fun φ hφ => OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF (hS₂sub hφ)) (hIKF hlam₁S₃.1) (fun h => hlam₁nS₂ (h ▸ hφ)))
      (fun φ hφ => OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF (hS₂sub hφ)) (hIKF hlam₁cS₃.1) (fun h => hlam₁cS₃.2 (h ▸ hφ)))
      hΓ1 ?_ ?_ hΓZ
      (Submodule.sub_mem _ hΓZ hτDZ)
      (fun φ hφ => hθ₁Γ φ (hS₂fin.mem_toFinset.mpr hφ)) ?_ ?_ hDsupp hψ₁S₂ ?_ ?_
    · -- `‖Xc‖² = 1`
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, hΓ1, hΓτD, hτDΓ, hτDτD]
      norm_num
    · -- `⟨X, Xc⟩ = 0`
      rw [ClassFunction.inner_sub_right, hΓ1, hΓτD]
      norm_num
    · -- `τ₁𝒮₂ ⊥ Xc`
      intro φ hφ
      rw [ClassFunction.inner_sub_right, hθ₁Γ φ (hS₂fin.mem_toFinset.mpr hφ), hτD,
        ClassFunction.inner_sub_right,
        hcross φ hφ lam₁ hlam₁S₃, hcross φ hφ lam₁.conj hlam₁cS₃]
      norm_num
    · -- `(λ₁ − λ̄₁)^τ = X − Xc`
      exact (sub_sub_cancel Γ0 (hyp.base.tau (lam₁ - lam₁.conj))).symm
    · -- the bridge `(λ₁ − e·ψ₁)^τ = X − e·τ₁ψ₁` (`ℤ`-scalar form)
      show hyp.base.tau (lam₁ - ((e : ℕ) : ℤ) • ψ₁)
        = Γ0 - ((e : ℕ) : ℤ) • c₁.extension ψ₁
      simp only [natCast_zsmul]
      rw [← Nat.cast_smul_eq_nsmul ℂ e (c₁.extension ψ₁)]
      exact hTBeq
    · -- the bridge support (`ℤ`-scalar form)
      show ((lam₁ - ((e : ℕ) : ℤ) • ψ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0
      simp only [natCast_zsmul]
      exact hβsupp
  exact hpairs lam₁ hlam₁S₃ ⟨hunion⟩

end Discharge

end OddOrder.Peterfalvi.S13
