import OddOrder.Peterfalvi.S07_Coherence.PsiDecomposition

/-!
# Peterfalvi (5.6.3)/(5.6.2)/(5.5) — the coherence-union extension `τ₂` and its images

The `τ₂` extension, the image-equation supplier `himg`, and the orthogonality of the
running images to `R(χ)`.

Split from the parent file (issue 0149, the longFile-1500 campaign); the parent
imports this leaf, so downstream imports are unchanged.
-/

namespace OddOrder.Peterfalvi.S07
open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]


/-! ### Peterfalvi (5.6.3): the coherence-union extension `τ₂`

The keystone `IntegralCharacterMap.retarget_isIntegralIsometry` builds the global isometry `τ₂`;
this section assembles it into the actual `IsCoherent (S₁ ∪ {χ, χ̄}) A` witness.  The data threaded
in are the honest outputs of (5.4)/(5.5)/(5.6.2): the coherent `τ₁` (= `hS₁.extension`), the
orthonormal pairs `{χ, χ̄}`, `{X, X̄}` (with `‖χ‖² = ‖χ̄‖² = 1` for irreducibles, hence
`‖X‖² = ‖X̄‖² = 1`), the conjugate-image definition `X̄ = X − (χ − χ̄)^τ`, the (5.5)+(5.2.e)
orthogonality `X, X̄ ⊥ τ₁ ξ` for `ξ ⊥ {χ, χ̄}`, the (5.6.2) image equation
`(χ − aχ₁)^τ = X − aχ₁^{τ₁}`,
and the (5.1)-type generation `Z[S₁∪S₂, L^#] ⊆ ℤ[Z[S₁,L^#] ∪ {χ−χ̄, χ−aχ₁}]`.  No hypothesis
assumes the extension itself: `τ₂` is *constructed* as `retarget τ₁ χ χ̄ X X̄`. -/

open IntegralCharacterMap in
/-- **Peterfalvi (5.6.3): coherence of `S₁ ∪ {χ, χ̄}`.**

Given a coherent `τ` on `S₁` (witness `hS₁`, with `τ₁ := hS₁.extension`), an orthonormal pair
`{χ, χ̄}` disjoint from and orthogonal to `S₁`, and the (5.4)/(5.5)/(5.6.2) target data `{X, X̄}`
— orthonormal in `ℤ[Irr G]`, with `X̄ = X − (χ − χ̄)^τ`, both orthogonal to `τ₁ ξ` for every `ξ`
orthogonal to `{χ, χ̄}` (the (5.5)+(5.2.e) input), and with the (5.6.2) image equation
`(χ − a·χ₁)^τ = X − a·χ₁^{τ₁}` — the union `S₁ ∪ {χ, χ̄}` is coherent.

The constructed extension is `τ₂ := retarget τ₁ χ χ̄ X X̄`: it is a global integral isometry by the
keystone `retarget_isIntegralIsometry`, sends `χ ↦ X`, `χ̄ ↦ X̄`, keeps `τ₁` off `{χ, χ̄}`, and
agrees with `τ` on the supported span — checked on the three difference generators
`{χ − χ̄, χ − a·χ₁} ∪ Z[S₁, L^#]` via `eq_on_zSpan_of_eq_on`, using the generation hypothesis
`hgen`.  The degree ratio `a : ℕ` (`χ(1) = a·χ₁(1)` from hypothesis (b) divisibility,
`exists_pos_natDegreeRatio_of_dvd`) enters as a *natural* scalar, so the difference `χ − a·χ₁`
is preserved by the `ℤ`-linear `τ₂`. -/
noncomputable def retarget_isCoherent
    {τ : IntegralCharacterMap L G} {S₁ : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hS₁ : IsCoherent τ S₁ A)
    {χ chibar chi1 : ClassFunction L ℂ} {a : ℕ} {X Xbar : ClassFunction G ℂ}
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hXX : ClassFunction.inner X X = 1) (hXbarXbar : ClassFunction.inner Xbar Xbar = 1)
    (hXXbar : ClassFunction.inner X Xbar = 0) (hXbarX : ClassFunction.inner Xbar X = 0)
    (hXZ : X ∈ ZIrr G) (hXbarZ : Xbar ∈ ZIrr G)
    (hX_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (hS₁.extension ξ) X = 0)
    (hXbar_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (hS₁.extension ξ) Xbar = 0)
    (hXbar_def : Xbar = X - τ (χ - chibar))
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner chibar x = 0)
    (hchi1 : chi1 ∈ S₁)
    (himg : τ (χ - a • chi1) = X - a • hS₁.extension chi1)
    (hgen : zSupportedSpan (L := L) (S₁ ∪ {χ, chibar}) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χ - chibar, χ - a • chi1})) :
    IsCoherent τ (S₁ ∪ {χ, chibar}) A := by
  classical
  set τ₁ := hS₁.extension with hτ₁def
  set τ₂ := retarget τ₁ χ chibar X Xbar with hτ₂def
  -- χ, χ̄ are orthogonal to all of ℤ[S₁].
  have hχ_zspan : ∀ φ : ClassFunction L ℂ, φ ∈ Submodule.span ℤ S₁ →
      ClassFunction.inner χ φ = 0 := fun φ hφ =>
    IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχ_S1 hφ
  have hχbar_zspan : ∀ φ : ClassFunction L ℂ, φ ∈ Submodule.span ℤ S₁ →
      ClassFunction.inner chibar φ = 0 := fun φ hφ =>
    IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχbar_S1 hφ
  -- (1) τ₂ preserves `⟨·,·⟩` on the *lattice* `ℤ[S₁ ∪ {χ, χ̄}]` (the genuine (5.6.3) isometry).
  -- This uses only the `ℤ[S₁]`-isometry of `τ₁ = hS₁.extension` (the coherence of `S₁`) and the
  -- honest lattice orthogonality `X, X̄ ⊥ τ₁ ξ` for `ξ ∈ ℤ[S₁]`; *not* a global isometry.
  have hτ₂_inner : ∀ φ ψ : ClassFunction L ℂ,
      φ ∈ zSpan (L := L) (S₁ ∪ {χ, chibar}) → ψ ∈ zSpan (L := L) (S₁ ∪ {χ, chibar}) →
      ClassFunction.inner (τ₂ φ) (τ₂ ψ) = ClassFunction.inner φ ψ := by
    intro φ ψ hφ hψ
    rw [hτ₂def]
    exact retarget_inner_eq_on_zSpan_union hS₁.extension_inner_eq hχχ hχbarχbar hχχbar hχbarχ
      hXX hXbarXbar hXXbar hXbarX hχ_S1 hχbar_S1 hX_ortho hXbar_ortho hφ hψ
  -- (2) Agreement of τ₂ with τ on the three difference generators.
  -- (2a) On χ - χ̄: τ₂(χ-χ̄) = X - X̄ = X - (X - τ(χ-χ̄)) = τ(χ-χ̄).
  have hagree_diff : τ₂ (χ - chibar) = τ (χ - chibar) := by
    rw [hτ₂def, map_sub, retarget_apply_left hχχ hχχbar, retarget_apply_right hχbarχ hχbarχbar,
      hXbar_def]; abel
  -- (2b) On χ - a·χ₁: τ₂(χ - a•χ₁) = X - a•τ₁χ₁ = τ(χ - a•χ₁).
  have hagree_ratio : τ₂ (χ - a • chi1) = τ (χ - a • chi1) := by
    have hχ₁ : τ₂ chi1 = τ₁ chi1 :=
      retarget_eq_of_orthogonal
        (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 chi1 hchi1, star_zero])
        (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 chi1 hchi1, star_zero])
    rw [hτ₂def, map_sub, map_nsmul, retarget_apply_left hχχ hχχbar, ← hτ₂def, hχ₁,
      himg, hτ₁def]
  -- (2c) On Z[S₁, L^#]: τ₂ φ = τ₁ φ = τ φ.
  have hagree_S1 : ∀ x ∈ zSupportedSpan (L := L) S₁ A, τ₂ x = τ x := by
    intro x hx
    have hxspan : x ∈ Submodule.span ℤ S₁ := hx.1
    have hτ₂x : τ₂ x = τ₁ x := by
      rw [hτ₂def]
      exact retarget_eq_of_orthogonal
        (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_zspan x hxspan, star_zero])
        (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_zspan x hxspan, star_zero])
    rw [hτ₂x, hτ₁def, hS₁.extends_on_supported x hx]
  -- (3) τ₂ = τ on the generating set T, hence on its span (eq_on_zSpan_of_eq_on).
  have hagree_T : ∀ y ∈ zSupportedSpan (L := L) S₁ A ∪ {χ - chibar, χ - a • chi1},
      τ₂ y = τ y := by
    intro y hy
    rcases hy with hyS1 | hypair
    · exact hagree_S1 y hyS1
    · rcases hypair with hy1 | hy2
      · rw [hy1]; exact hagree_diff
      · rw [hy2]; exact hagree_ratio
  -- (4) Assemble the IsCoherent witness.
  refine ⟨?_, τ₂, hτ₂_inner, ?_, ?_⟩
  · -- nonzero: inherited from S₁ ⊆ S₁ ∪ {χ, χ̄}.
    obtain ⟨φ, hφmem, hφne⟩ := hS₁.nonzero
    exact ⟨φ, zSupportedSpan_mono_left (Set.subset_union_left) hφmem, hφne⟩
  · -- extends_on_supported via span generation + generator agreement.
    intro φ hφ
    exact IntegralCharacterMap.eq_on_zSpan_of_eq_on hagree_T (hgen hφ)
  · -- extension_mem_ZIrr: `τ₂ = retarget τ₁ χ χ̄ X X̄` sends each generator of `ℤ[S₁ ∪ {χ, χ̄}]` to
    -- a virtual character (`S₁`-members via `τ₁` and its inductive ZIrr-codomain; `χ ↦ X`,
    -- `χ̄ ↦ X̄`).
    intro φ hφ
    rw [hτ₂def]
    induction hφ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hyS1 | hyχ
        · rw [retarget_eq_of_orthogonal
              (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 y hyS1, star_zero])
              (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 y hyS1, star_zero]),
            hτ₁def]
          exact hS₁.extension_mem_ZIrr y (Submodule.subset_span hyS1)
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hyχ
          rcases hyχ with rfl | rfl
          · rw [retarget_apply_left hχχ hχχbar]; exact hXZ
          · rw [retarget_apply_right hχbarχ hχbarχbar]; exact hXbarZ
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
    | smul c y _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ c ih

/-- **The supported part of `Z[{χ, χ̄}]` is generated by the difference `χ − χ̄`.**

If `χ` and `χ̄` have the same value at `1` (e.g. equal degree, `χ̄(1) = χ(1) ≠ 0`) and the support
set `A` excludes `1`, then every supported `ℤ`-combination `m·χ + n·χ̄` vanishes at `1`, forcing
`m + n = 0`, so it is a multiple of `χ − χ̄`.  This is the generation hypothesis the (5.2.d) base
coherence `coherentPair` needs (the `S₁ = ∅` analogue of `zSupportedSpan_adjoinPair_subset_span`,
where no `χ₁` is available to reconstruct `χ`). -/
theorem zSupportedSpan_pair_subset_span
    {χ chibar : ClassFunction L ℂ} {A : Set L}
    (hχ1 : (χ : L → ℂ) 1 ≠ 0)
    (hbar1 : (chibar : L → ℂ) 1 = (χ : L → ℂ) 1)
    (h1 : (1 : L) ∉ A) :
    zSupportedSpan (L := L) {χ, chibar} A ⊆ Submodule.span ℤ ({χ - chibar} : Set _) := by
  intro φ hφ
  obtain ⟨m, n, hmn⟩ := Submodule.mem_span_pair.mp hφ.1
  -- `φ(1) = 0`: `1 ∉ A ⊇ support φ`.
  have hφ1 : φ (1 : L) = 0 := by
    by_contra h
    exact h1 (hφ.2 (ClassFunction.mem_support.mpr h))
  -- evaluate `m·χ + n·χ̄ = φ` at `1`.
  have heval : (m : ℂ) * χ (1 : L) + (n : ℂ) * chibar (1 : L) = 0 := by
    have h := congrArg (fun ψ : ClassFunction L ℂ => ψ (1 : L)) hmn
    simp only [← Int.cast_smul_eq_zsmul ℂ m χ, ← Int.cast_smul_eq_zsmul ℂ n chibar,
      ClassFunction.add_apply, ClassFunction.smul_apply, hφ1] at h
    simpa [smul_eq_mul] using h
  -- `m + n = 0` since `χ(1) ≠ 0`.
  have hmn0 : m + n = 0 := by
    rw [hbar1, ← add_mul] at heval
    have hc : (m : ℂ) + n = 0 := (mul_eq_zero.mp heval).resolve_right hχ1
    exact_mod_cast hc
  -- `φ = m·χ + n·χ̄ = m·(χ − χ̄)`.
  rw [SetLike.mem_coe, Submodule.mem_span_singleton]
  refine ⟨m, ?_⟩
  have hn : n = -m := by omega
  subst hn
  rw [← hmn]; module

open IntegralCharacterMap in
open scoped Classical in
/-- **Peterfalvi (5.2.d) base coherence: a single conjugate pair `{χ, χ̄}` is coherent.**

The seed of every coherence chain — the `h0`/`hS₁` base that `coherentPairChain`,
`retarget_isCoherent[_fromDade]` and `coherentUnion_of_glued` all consume but never construct.
Given an orthonormal source pair `{χ, χ̄}`, an orthonormal target pair `{X, X̄}` in `ℤ[Irr G]` with
`X̄ = X − τ(χ − χ̄)` (the (5.2.d) image data — for an irreducible `χ`, supplied by
`retargetTargetPair` from `R(χ)`), and the generation `Z[{χ,χ̄}, A] ⊆ Z[χ − χ̄]` (every supported
combination of `χ, χ̄` is a multiple of the difference `χ − χ̄`, as both have the same degree),
the extension `ν := retarget τ χ χ̄ X X̄` realizes `IsCoherent τ {χ, χ̄} A`.

This is the `S₁ = ∅` degenerate case of the (5.6.3) re-targeting: with no prior lattice the
Gram–Schmidt residual of any `φ ∈ Z[{χ,χ̄}]` vanishes, so the isometry
(`retarget_inner_eq_on_zSpan_union`) and the agreement on the supported difference reduce to the
target-pair orthonormality and `ν(χ − χ̄) = X − X̄ = τ(χ − χ̄)`. -/
noncomputable def coherentPair
    {τ : IntegralCharacterMap L G} {χ chibar : ClassFunction L ℂ} {A : Set L}
    {X Xbar : ClassFunction G ℂ}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hXX : ClassFunction.inner X X = 1) (hXbarXbar : ClassFunction.inner Xbar Xbar = 1)
    (hXXbar : ClassFunction.inner X Xbar = 0) (hXbarX : ClassFunction.inner Xbar X = 0)
    (hXZ : X ∈ ZIrr G) (hXbarZ : Xbar ∈ ZIrr G)
    (hXbar_def : Xbar = X - τ (χ - chibar))
    (hne : χ - chibar ≠ 0)
    (hsupp : (χ - chibar).support ⊆ A)
    (hgen : zSupportedSpan (L := L) {χ, chibar} A ⊆ Submodule.span ℤ ({χ - chibar} : Set _)) :
    IsCoherent τ {χ, chibar} A := by
  classical
  set ν := retarget τ χ chibar X Xbar with hνdef
  have hνdiff : ν (χ - chibar) = τ (χ - chibar) := by
    rw [hνdef, map_sub, retarget_apply_left hχχ hχχbar, retarget_apply_right hχbarχ hχbarχbar,
      hXbar_def]; abel
  have hχ_mem : χ ∈ zSpan (L := L) {χ, chibar} := Submodule.subset_span (by simp)
  have hχbar_mem : chibar ∈ zSpan (L := L) {χ, chibar} := Submodule.subset_span (by simp)
  refine ⟨⟨χ - chibar, ⟨Submodule.sub_mem _ hχ_mem hχbar_mem, hsupp⟩, hne⟩, ν, ?_, ?_, ?_⟩
  · -- isometry on `zSpan {χ, χ̄}` (the `S₁ = ∅` case of `retarget_inner_eq_on_zSpan_union`).
    intro φ ψ hφ hψ
    rw [hνdef]
    refine retarget_inner_eq_on_zSpan_union (S₁ := ∅) (fun u v hu hv => ?_) hχχ hχbarχbar hχχbar
      hχbarχ hXX hXbarXbar hXXbar hXbarX (fun x hx => hx.elim)
      (fun x hx => hx.elim) (fun ξ hξ => ?_) (fun ξ hξ => ?_)
      ?_ ?_
    · rw [Submodule.span_empty, Submodule.mem_bot] at hu hv; rw [hu, hv]; simp
    · rw [Submodule.span_empty, Submodule.mem_bot] at hξ
      rw [hξ, map_zero, ClassFunction.inner_zero_left]
    · rw [Submodule.span_empty, Submodule.mem_bot] at hξ
      rw [hξ, map_zero, ClassFunction.inner_zero_left]
    · rw [Set.empty_union]; exact hφ
    · rw [Set.empty_union]; exact hψ
  · -- extends_on_supported: `ν = τ` on `χ − χ̄`, hence on `Z[χ − χ̄] ⊇ Z[{χ,χ̄}, A]` (`hgen`).
    intro φ hφ
    rw [hνdef]
    refine IntegralCharacterMap.eq_on_zSpan_of_eq_on (T := ({χ - chibar} : Set _)) ?_ (hgen hφ)
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx, ← hνdef]; exact hνdiff
  · -- extension_mem_ZIrr: `χ ↦ X`, `χ̄ ↦ X̄`, so `ℤ[{χ, χ̄}]` maps into `ℤ[Irr G]`.
    intro φ hφ
    rw [hνdef]
    induction hφ using Submodule.span_induction with
    | mem y hy =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · rw [retarget_apply_left hχχ hχχbar]; exact hXZ
        · rw [retarget_apply_right hχbarχ hχbarχbar]; exact hXbarZ
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
    | smul c y _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ c ih

/-- **Equal-degree generation:** every supported `φ ∈ ℤ[range χ, A]` is an integer combination of
the differences `χⱼ − χ₀`.  Since all `χⱼ` share the value `d ≠ 0` at `1 ∉ A`, a supported
combination `∑ⱼ cⱼ χⱼ` vanishes at `1`, forcing `∑ⱼ cⱼ = 0`, so it equals `∑ⱼ cⱼ (χⱼ − χ₀)`.  This
is the `n`-element analogue of `zSupportedSpan_pair_subset_span` (the base of (6.6)/(6.8)). -/
theorem zSupportedSpan_range_subset_span_sub_zero {n : ℕ} [NeZero n]
    {χ : Fin n → ClassFunction L ℂ} {A : Set L}
    (hdeg : ∀ j, ((χ j : ClassFunction L ℂ) : L → ℂ) 1 = ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1)
    (hdeg0 : ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0)
    (h1A : (1 : L) ∉ A) :
    zSupportedSpan (L := L) (Set.range χ) A ⊆
      Submodule.span ℤ (Set.range (fun j => χ j - χ 0)) := by
  classical
  intro φ hφ
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).mp hφ.1
  have hφ1 : φ (1 : L) = 0 := by
    by_contra h
    exact h1A (hφ.2 (ClassFunction.mem_support.mpr h))
  have hc' : ∑ j : Fin n, (c j : ℂ) • χ j = φ := by
    rw [← hc]
    exact Finset.sum_congr rfl fun j _ => Int.cast_smul_eq_zsmul ℂ (c j) (χ j)
  have heval : ∑ j : Fin n, (c j : ℂ) * ((χ j : ClassFunction L ℂ) : L → ℂ) 1 = 0 := by
    have h := congrArg (fun ψ : ClassFunction L ℂ => ψ (1 : L)) hc'
    simpa [classFunction_sum_apply, ClassFunction.smul_apply, hφ1] using h
  have hsum0 : ∑ j : Fin n, c j = 0 := by
    have hrw : ∑ j : Fin n, (c j : ℂ) * ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1
        = ∑ j : Fin n, (c j : ℂ) * ((χ j : ClassFunction L ℂ) : L → ℂ) 1 :=
      Finset.sum_congr rfl fun j _ => by rw [hdeg j]
    have key : (∑ j : Fin n, (c j : ℂ)) * ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1 = 0 := by
      rw [Finset.sum_mul, hrw, heval]
    have hsum0ℂ : (∑ j : Fin n, (c j : ℂ)) = 0 := (mul_eq_zero.mp key).resolve_right hdeg0
    have hcast : ((∑ j : Fin n, c j : ℤ) : ℂ) = ∑ j : Fin n, (c j : ℂ) := by push_cast; ring
    exact_mod_cast hcast.trans hsum0ℂ
  rw [← hc]
  have heq : ∑ j : Fin n, c j • χ j = ∑ j : Fin n, c j • (χ j - χ 0) := by
    have hexp : ∑ j : Fin n, c j • (χ j - χ 0)
        = (∑ j : Fin n, c j • χ j) - (∑ j : Fin n, c j) • χ 0 := by
      rw [Finset.sum_smul]
      simp only [smul_sub]
      rw [Finset.sum_sub_distrib]
    rw [hexp, hsum0, zero_smul, sub_zero]
  rw [heq]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

open IntegralCharacterMap in
/-- **Peterfalvi (1.1)+(1.4): an equal-degree set is coherent.**

If `χ : Fin n → CF(L)` (`n ≥ 2`) is an orthonormal family with all members of equal degree `d ≠ 0`,
whose differences `χⱼ − χ₀` are supported in `A` (`1 ∉ A`), and `X : Fin n → CF(G)` is an
orthonormal
family in the target with `τ (χⱼ − χ₀) = Xⱼ − X₀` (the (1.4) signed-difference image equation), then
`{χ₀, …, χₙ₋₁} = range χ` is coherent, with extension `ν φ = ∑ⱼ ⟨φ, χⱼ⟩ • Xⱼ` (`coherentImageMap`).

This is the seed for both the equal-minimal-degree base prefix of (6.6) and the set `Y = S(H')` of
(6.8), where coherence holds *directly* by (1.1)+(1.4) (the (5.6) degree induction is unavailable at
equal degree).  The construction needs no `τ₁`-residual: on the lattice `ℤ[range χ]` the residual
vanishes, so `extension_inner_eq` is pure Parseval (`coherentImageMap_inner_eq`) and `τ` enters only
through `extends_on_supported`, where `ℤ[range χ, A]` is generated by the differences `χⱼ − χ₀`
(`zSupportedSpan_range_subset_span_sub_zero`), on which `ν` and `τ` agree by `himg`. -/
noncomputable def coherentEqualDegree
    {τ : IntegralCharacterMap L G} {A : Set L} {n : ℕ} [NeZero n]
    {χ : Fin n → ClassFunction L ℂ} {X : Fin n → ClassFunction G ℂ}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hn : 2 ≤ n)
    (horthχ : ∀ i j, ClassFunction.inner (χ i) (χ j) = if i = j then (1 : ℂ) else 0)
    (horthX : ∀ i j, ClassFunction.inner (X i) (X j) = if i = j then (1 : ℂ) else 0)
    (himg : ∀ j, τ (χ j - χ 0) = X j - X 0)
    (hXZ : ∀ j, X j ∈ ZIrr G)
    (hdeg : ∀ j, ((χ j : ClassFunction L ℂ) : L → ℂ) 1 = ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1)
    (hdeg0 : ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0)
    (h1A : (1 : L) ∉ A)
    (hsuppdiff : ∀ j, (χ j - χ 0).support ⊆ A) :
    IsCoherent τ (Set.range χ) A := by
  classical
  have h1n : 1 < n := by omega
  have hi1 : (⟨1, h1n⟩ : Fin n) ≠ 0 := by
    intro h; exact absurd (congrArg Fin.val h) (by simp)
  refine ⟨⟨χ ⟨1, h1n⟩ - χ 0,
      ⟨Submodule.sub_mem _ (Submodule.subset_span (Set.mem_range_self _))
        (Submodule.subset_span (Set.mem_range_self _)), hsuppdiff ⟨1, h1n⟩⟩, ?_⟩,
    coherentImageMap (L := L) (G := G) χ X, ?_, ?_, ?_⟩
  · -- nonzero: `χ₁ − χ₀ ≠ 0` from orthonormality.
    rw [sub_ne_zero]
    intro h
    have hcontra : (0 : ℂ) = 1 :=
      calc (0 : ℂ) = ClassFunction.inner (χ (⟨1, h1n⟩ : Fin n)) (χ 0) := by
            rw [horthχ, if_neg hi1]
        _ = ClassFunction.inner (χ 0) (χ 0) := by rw [h]
        _ = 1 := by rw [horthχ, if_pos rfl]
    exact zero_ne_one hcontra
  · -- extension_inner_eq: pure Parseval on `ℤ[range χ]`.
    intro φ ψ hφ hψ
    exact coherentImageMap_inner_eq horthχ horthX hφ hψ
  · -- extends_on_supported: agreement on the difference generators of `ℤ[range χ, A]`.
    intro φ hφ
    refine eq_on_zSpan_of_eq_on (T := Set.range (fun j => χ j - χ 0)) ?_
      (zSupportedSpan_range_subset_span_sub_zero hdeg hdeg0 h1A hφ)
    rintro x ⟨j, rfl⟩
    rw [map_sub, coherentImageMap_apply_eq horthχ j, coherentImageMap_apply_eq horthχ 0, himg j]
  · -- extension_mem_ZIrr: each member maps to `Xⱼ ∈ ℤ[Irr G]` (`coherentImageMap_apply_eq`), so
    -- `ℤ[range χ]` maps into `ℤ[Irr G]`.
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        rw [coherentImageMap_apply_eq horthχ j]; exact hXZ j
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
    | smul c y _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ c ih

open IntegralCharacterMap in
/-- **Peterfalvi (5.7) core: an equal-degree set with *arbitrary* member norms is coherent.**

The weighted form of `coherentEqualDegree`.  Hypothesis (5.2) gives the members of `𝒮` only
*pairwise orthogonality* — a reducible member has `‖χ‖² > 1` — so the book's (5.7) may not assume
unit norm, and neither does this builder (issue 0157).

Inputs: `χ : Fin n → CF(L)` (`n ≥ 2`) pairwise orthogonal with nonzero norms, all of equal degree
`d ≠ 0`, differences supported in `A` (`1 ∉ A`); and a target family `X : Fin n → CF(G)` of virtual
characters matching the **Gram matrix** of `χ` (`⟨Xᵢ, Xⱼ⟩ = ⟨χᵢ, χⱼ⟩` — the orthonormal builder's
`horthX` is the `⟨χᵢ, χⱼ⟩ = δᵢⱼ` case), with `τ (χⱼ − χ₀) = Xⱼ − X₀`.

The extension is the **norm-rescaled** reconstruction `ν φ = ∑ⱼ ⟨φ, χⱼ⟩ · ‖χⱼ‖⁻² • Xⱼ`, which
sends `χₖ ↦ Xₖ` (`coherentImageMap_apply_eq_of_orthogonal`) and is an isometry on `ℤ[range χ]` by
weighted Parseval (`coherentImageMapW_inner_eq`).  `IsCoherent` asks for an isometry, not for
orthonormal images, so nothing else changes.

`coherentEqualDegree` is kept as the unit-norm construction because its `extension` is
`coherentImageMap χ X` *definitionally* (`coherentEqualDegree_extension`), an API several
downstream consumers rely on; here the extension carries the `‖χⱼ‖⁻²` rescaling. -/
noncomputable def coherentEqualDegreeW
    {τ : IntegralCharacterMap L G} {A : Set L} {n : ℕ} [NeZero n]
    {χ : Fin n → ClassFunction L ℂ} {X : Fin n → ClassFunction G ℂ}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hn : 2 ≤ n)
    (horthχ : ∀ i j, i ≠ j → ClassFunction.inner (χ i) (χ j) = 0)
    (hnorm : ∀ j, ClassFunction.inner (χ j) (χ j) ≠ 0)
    (hgram : ∀ i j, ClassFunction.inner (X i) (X j) = ClassFunction.inner (χ i) (χ j))
    (himg : ∀ j, τ (χ j - χ 0) = X j - X 0)
    (hXZ : ∀ j, X j ∈ ZIrr G)
    (hdeg : ∀ j, ((χ j : ClassFunction L ℂ) : L → ℂ) 1 = ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1)
    (hdeg0 : ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0)
    (h1A : (1 : L) ∉ A)
    (hsuppdiff : ∀ j, (χ j - χ 0).support ⊆ A) :
    IsCoherent τ (Set.range χ) A := by
  classical
  have h1n : 1 < n := by omega
  have hi1 : (⟨1, h1n⟩ : Fin n) ≠ 0 := by
    intro h; exact absurd (congrArg Fin.val h) (by simp)
  refine ⟨⟨χ ⟨1, h1n⟩ - χ 0,
      ⟨Submodule.sub_mem _ (Submodule.subset_span (Set.mem_range_self _))
        (Submodule.subset_span (Set.mem_range_self _)), hsuppdiff ⟨1, h1n⟩⟩, ?_⟩,
    coherentImageMap (L := L) (G := G) χ
      (fun j => (ClassFunction.inner (χ j) (χ j))⁻¹ • X j), ?_, ?_, ?_⟩
  · -- nonzero: `χ₁ = χ₀` would make the nonzero norm `⟨χ₀, χ₀⟩` an off-diagonal `0`.
    rw [sub_ne_zero]
    intro h
    have hoff := horthχ ⟨1, h1n⟩ 0 hi1
    rw [h] at hoff
    exact hnorm 0 hoff
  · -- extension_inner_eq: weighted Parseval on `ℤ[range χ]`.
    intro φ ψ hφ hψ
    exact coherentImageMapW_inner_eq horthχ hnorm hgram hφ hψ
  · -- extends_on_supported: agreement on the difference generators of `ℤ[range χ, A]`.
    intro φ hφ
    refine eq_on_zSpan_of_eq_on (T := Set.range (fun j => χ j - χ 0)) ?_
      (zSupportedSpan_range_subset_span_sub_zero hdeg hdeg0 h1A hφ)
    rintro x ⟨j, rfl⟩
    rw [map_sub, coherentImageMap_apply_eq_of_orthogonal horthχ hnorm j,
      coherentImageMap_apply_eq_of_orthogonal horthχ hnorm 0, himg j]
  · -- extension_mem_ZIrr: each member maps to `Xⱼ ∈ ℤ[Irr G]`.
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        rw [coherentImageMap_apply_eq_of_orthogonal horthχ hnorm j]; exact hXZ j
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
    | smul c y _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ c ih

open IntegralCharacterMap in
/-- The `extension` field of `coherentEqualDegree` is the Fourier image map `coherentImageMap χ X`.
-/
theorem coherentEqualDegree_extension
    {τ : IntegralCharacterMap L G} {A : Set L} {n : ℕ} [NeZero n]
    {χ : Fin n → ClassFunction L ℂ} {X : Fin n → ClassFunction G ℂ}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hn : 2 ≤ n)
    (horthχ : ∀ i j, ClassFunction.inner (χ i) (χ j) = if i = j then (1 : ℂ) else 0)
    (horthX : ∀ i j, ClassFunction.inner (X i) (X j) = if i = j then (1 : ℂ) else 0)
    (himg : ∀ j, τ (χ j - χ 0) = X j - X 0)
    (hXZ : ∀ j, X j ∈ ZIrr G)
    (hdeg : ∀ j, ((χ j : ClassFunction L ℂ) : L → ℂ) 1 = ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1)
    (hdeg0 : ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0)
    (h1A : (1 : L) ∉ A)
    (hsuppdiff : ∀ j, (χ j - χ 0).support ⊆ A) :
    (coherentEqualDegree hn horthχ horthX himg hXZ hdeg hdeg0 h1A hsuppdiff).extension
      = coherentImageMap (L := L) (G := G) χ X := rfl

/-- Transport the `extension` of a coherence witness across an equality of the coherent set: the
`extension` field is set-independent data, so it is unchanged by `▸`-rewriting the set. -/
theorem IsCoherent.extension_eqRec {τ : IntegralCharacterMap L G} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {S₁ S₂ : Set (ClassFunction L ℂ)} (h : S₁ = S₂) (c : IsCoherent τ S₁ A) :
    (h ▸ c).extension = c.extension := by subst h; rfl

open scoped Classical in
open IntegralCharacterMap in
/-- **Sign-swap relabel of a coherence witness on a 2-element equal-degree set** (Peterfalvi (6.8.1)
relabel, mmd 04.8 L176: "replacing `η₁^{τ₁}, η₂^{τ₁}` by `-η₂^{τ₁}, -η₁^{τ₁}`", and the `X`-analogue
for `n = 2`).

Given a coherence witness `c` for the orthonormal equal-degree pair `{φ₀, φ₁}` (`φ₀ ≠ φ₁`,
`φ₁(1) = φ₀(1) ≠ 0`, difference supported in `A`, `1 ∉ A`), there is a second coherence witness `c'`
for the *same set* whose extension sends `φ₀ ↦ -c.extension φ₁` and `φ₁ ↦ -c.extension φ₀` — the
"swap-and-negate" of the two images.  The swapped images `-c.extension φ₁, -c.extension φ₀` are
still orthonormal and in `ℤ[Irr G]` (signs square out), and the supported difference is preserved:
`φ₁ - φ₀ ↦ (-c.extension φ₀) - (-c.extension φ₁) = c.extension φ₁ - c.extension φ₀ = τ(φ₁ - φ₀)`,
which is *exactly* why `extends_on_supported` survives the swap (it would fail for an unequal-degree
pair, where the supported lattice is generated by a degree-ratio difference instead).  Built via
`coherentEqualDegree` with source `![φ₀, φ₁]` and target `![-c.extension φ₁, -c.extension φ₀]`. -/
theorem coherentEqualDegree_swap_neg
    {τ : IntegralCharacterMap L G} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {φ₀ φ₁ : ClassFunction L ℂ}
    (c : IsCoherent τ ({φ₀, φ₁} : Set (ClassFunction L ℂ)) A)
    (horth : ClassFunction.inner φ₀ φ₁ = 0)
    (hn0 : ClassFunction.inner φ₀ φ₀ = 1) (hn1 : ClassFunction.inner φ₁ φ₁ = 1)
    (hdeg : (φ₁ : L → ℂ) 1 = (φ₀ : L → ℂ) 1) (hdeg0 : (φ₀ : L → ℂ) 1 ≠ 0)
    (h1A : (1 : L) ∉ A) (hsupp : (φ₁ - φ₀).support ⊆ A) :
    ∃ c' : IsCoherent τ ({φ₀, φ₁} : Set (ClassFunction L ℂ)) A,
      c'.extension φ₀ = -c.extension φ₁ ∧ c'.extension φ₁ = -c.extension φ₀ := by
  classical
  -- membership in `{φ₀, φ₁}` and its `ℤ`-span.
  have hmem0 : φ₀ ∈ ({φ₀, φ₁} : Set (ClassFunction L ℂ)) := Set.mem_insert _ _
  have hmem1 : φ₁ ∈ ({φ₀, φ₁} : Set (ClassFunction L ℂ)) := Set.mem_insert_of_mem _ rfl
  have hsp0 : φ₀ ∈ zSpan (L := L) ({φ₀, φ₁} : Set _) := Submodule.subset_span hmem0
  have hsp1 : φ₁ ∈ zSpan (L := L) ({φ₀, φ₁} : Set _) := Submodule.subset_span hmem1
  -- target images are orthonormal (from `c.extension_inner_eq` + source orthonormality).
  have hψ00 : ClassFunction.inner (c.extension φ₀) (c.extension φ₀) = 1 := by
    rw [c.extension_inner_eq φ₀ φ₀ hsp0 hsp0, hn0]
  have hψ11 : ClassFunction.inner (c.extension φ₁) (c.extension φ₁) = 1 := by
    rw [c.extension_inner_eq φ₁ φ₁ hsp1 hsp1, hn1]
  have hψ01 : ClassFunction.inner (c.extension φ₀) (c.extension φ₁) = 0 := by
    rw [c.extension_inner_eq φ₀ φ₁ hsp0 hsp1, horth]
  have hψ10 : ClassFunction.inner (c.extension φ₁) (c.extension φ₀) = 0 := by
    rw [c.extension_inner_eq φ₁ φ₀ hsp1 hsp0,
      OddOrder.RepresentationTheory.inner_conj_symm φ₀ φ₁, horth, star_zero]
  -- ZIrr membership of the target images.
  have hZ0 : c.extension φ₀ ∈ ZIrr G := c.extension_mem_ZIrr φ₀ hsp0
  have hZ1 : c.extension φ₁ ∈ ZIrr G := c.extension_mem_ZIrr φ₁ hsp1
  -- `coherentEqualDegree` inputs for `χ = ![φ₀, φ₁]`, `X = ![-c.extension φ₁, -c.extension φ₀]`.
  have horthχ : ∀ i j : Fin 2, ClassFunction.inner ((![φ₀, φ₁] : Fin 2 → _) i)
      ((![φ₀, φ₁] : Fin 2 → _) j) = if i = j then (1 : ℂ) else 0 := by
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
      Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · simpa using hn0
    · simpa using horth
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
        Fin.reduceEq, ↓reduceIte]
      rw [OddOrder.RepresentationTheory.inner_conj_symm φ₀ φ₁, horth, star_zero]
    · simpa using hn1
  have horthX : ∀ i j : Fin 2,
      ClassFunction.inner ((![-c.extension φ₁, -c.extension φ₀] : Fin 2 → _) i)
      ((![-c.extension φ₁, -c.extension φ₀] : Fin 2 → _) j) = if i = j then (1 : ℂ) else 0 := by
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
      Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
        Fin.reduceEq, ↓reduceIte, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
        neg_neg]
    · exact hψ11
    · exact hψ10
    · exact hψ01
    · exact hψ00
  have himg : ∀ j : Fin 2, τ ((![φ₀, φ₁] : Fin 2 → _) j - (![φ₀, φ₁] : Fin 2 → _) 0)
      = (![-c.extension φ₁, -c.extension φ₀] : Fin 2 → _) j
        - (![-c.extension φ₁, -c.extension φ₀] : Fin 2 → _) 0 := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · simp
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
      have hsuppmem : (φ₁ - φ₀) ∈ zSupportedSpan (L := L) ({φ₀, φ₁} : Set _) A :=
        ⟨Submodule.sub_mem _ hsp1 hsp0, hsupp⟩
      have hext := c.extends_on_supported (φ₁ - φ₀) hsuppmem
      rw [map_sub] at hext
      rw [← hext, neg_sub_neg]
  have hXZ : ∀ j : Fin 2, (![-c.extension φ₁, -c.extension φ₀] : Fin 2 → _) j ∈ ZIrr G := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · simpa using Submodule.neg_mem _ hZ1
    · simpa using Submodule.neg_mem _ hZ0
  have hdeg' : ∀ j : Fin 2, (((![φ₀, φ₁] : Fin 2 → _) j : ClassFunction L ℂ) : L → ℂ) 1
      = (((![φ₀, φ₁] : Fin 2 → _) 0 : ClassFunction L ℂ) : L → ℂ) 1 := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rfl
    · simpa using hdeg
  have hdeg0' : (((![φ₀, φ₁] : Fin 2 → _) 0 : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0 := by
    simpa using hdeg0
  have hsuppdiff : ∀ j : Fin 2,
      ((![φ₀, φ₁] : Fin 2 → _) j - (![φ₀, φ₁] : Fin 2 → _) 0).support ⊆ A := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · simp
    · simpa using hsupp
  -- the swapped witness over `range ![φ₀,φ₁]`, transported to `{φ₀,φ₁}`.
  have hr : Set.range (![φ₀, φ₁] : Fin 2 → ClassFunction L ℂ) = ({φ₀, φ₁} : Set _) := by
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  refine ⟨hr ▸ coherentEqualDegree (by norm_num : (2 : ℕ) ≤ 2) horthχ horthX himg hXZ hdeg'
      hdeg0' h1A hsuppdiff, ?_, ?_⟩
  · rw [IsCoherent.extension_eqRec hr, coherentEqualDegree_extension]
    have h0 := coherentImageMap_apply_eq (L := L) (G := G)
      (χ := (![φ₀, φ₁] : Fin 2 → _)) (X := (![-c.extension φ₁, -c.extension φ₀] : Fin 2 → _))
      horthχ 0
    simpa using h0
  · rw [IsCoherent.extension_eqRec hr, coherentEqualDegree_extension]
    have h1 := coherentImageMap_apply_eq (L := L) (G := G)
      (χ := (![φ₀, φ₁] : Fin 2 → _)) (X := (![-c.extension φ₁, -c.extension φ₀] : Fin 2 → _))
      horthχ 1
    simpa using h1

open scoped Classical in
open IntegralCharacterMap in
/-- **Peterfalvi (5.6.3) per-step coherence, with the target pair constructed from (5.5).**

The (5.6.3) adjoining of `{χ, χ̄}` to a coherent `S₁`, where the orthonormal target pair
`{X, X̄}` is *not* taken as data but **constructed** from a (5.5) decomposition
`D : CharacterPsiDecomposition τ χ 0` of the irreducible `χ` (`X := D.X`,
`X̄ := D.X − (χ − χ̄)^τ`, orthonormal by `retargetTargetPair`).  This isolates exactly the part
of `retarget_isCoherent` that genuinely couples to the running `τ₁ = hS₁.extension`:

* `hX_ortho`/`hXbar_ortho` — the (5.2.e) cross-orthogonality `D.X, X̄ ⊥ τ₁ ξ` (`ξ ∈ ℤ[S₁]`);
* `himg` — the (5.6.2) image equation `(χ − a·χ₁)^τ = D.X − a·τ₁ χ₁`.

These two — and these alone — depend on how `D.tau1` relates to the *prior-step* coherence
extension `hS₁.extension`; everything else (the orthonormality of `{D.X, X̄}` and their virtual-
character membership) is supplied by `D` through `retargetTargetPair`.  The Round-20 "missing
Gram–Schmidt / basis-extension primitive" is thereby shown to be unnecessary: for irreducible `χ`
the target pair is forced, and the real residual is the running-`τ₁` coupling above. -/
noncomputable def retarget_isCoherent_of_decomposition
    {τ : IntegralCharacterMap L G} {S₁ : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hS₁ : IsCoherent τ S₁ A)
    {χ chibar chi1 : ClassFunction L ℂ} {a : ℕ}
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ 0)
    (hχbar_eq : chibar = χ.conj)
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hX_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (hS₁.extension ξ) D.X = 0)
    (hXbar_ortho : ∀ ξ ∈ Submodule.span ℤ S₁,
      ClassFunction.inner (hS₁.extension ξ) (D.X - τ (χ - chibar)) = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner chibar x = 0)
    (hchi1 : chi1 ∈ S₁)
    (himg : τ (χ - a • chi1) = D.X - a • hS₁.extension chi1)
    (hgen : zSupportedSpan (L := L) (S₁ ∪ {χ, chibar}) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χ - chibar, χ - a • chi1})) :
    IsCoherent τ (S₁ ∪ {χ, chibar}) A := by
  classical
  subst hχbar_eq
  -- The orthonormal `{X, X̄}` block, constructed from `D` (no Gram–Schmidt).
  set P := D.retargetTargetPair hχχ hχbarχbar hχχbar hχbarχ with hP
  exact retarget_isCoherent hS₁ hχχ hχbarχbar hχχbar hχbarχ
    P.inner_self_X P.inner_self_conjImage P.inner_X_conjImage P.inner_conjImage_X
    P.X_mem_ZIrr P.conjImage_mem_ZIrr
    hX_ortho hXbar_ortho rfl hχ_S1 hχbar_S1 hchi1 himg hgen

/-! ### Peterfalvi (5.6.2): the image-equation supplier `himg`

`retarget_isCoherent` / `retarget_isCoherent_of_decomposition` consume, as their single genuinely
running-`τ₁`-coupled hypothesis, the (5.6.2) **image equation**

`himg : (χ − a·χ₁)^τ = X − a·χ₁^{τ₁}`   (`τ₁ := hS₁.extension`).

This is *not* a free wiring fact — it is exactly Peterfalvi (5.6.1)+(5.6.2): writing the (5.4)
decomposition `(χ − a·χ₁)^{τ₁'} = X − Y` against `R(χ)` (where `τ₁'` is the (5.4) auxiliary isometry
agreeing with `τ` on the supported difference), the integer-forcing capstone
`lambda_eq_zero_and_Z_eq_zero`
collapses `Y` to `a·χ₁^{τ₁}`.  The producer below assembles `himg` from the three honest textbook
facts, *constructing* it rather than positing it:

* `htau1_diff` — the (5.4) agreement `(χ − a·χ₁)^{τ₁'} = (χ − a·χ₁)^τ` (`τ₁'` coincides with `τ` on
  `ℤ[χ − a·χ₁, χ − χ̄]`, the (5.4) hypothesis); written via the decomposition's `tau1`;
* `hY` — the (5.6.2) output `Y = a·χ₁^{τ₁'}` (the `lambda_eq_zero_and_Z_eq_zero` conclusion fed back
  into `(5.6.1)`'s `Y = a·χ₁^{τ₁} − λ·(…) + Z` at `λ = 0`, `Z = 0`);
* `htau1_chi1` — the coherence compatibility `χ₁^{τ₁'} = χ₁^{τ₁}` of the (5.4) auxiliary isometry
  with the running coherence extension `τ₁ = hS₁.extension` at the family member `χ₁ ∈ S₁`.

The chain `(χ − a·χ₁)^τ = (χ − a·χ₁)^{τ₁'} = X − Y = X − a·χ₁^{τ₁'} = X − a·χ₁^{τ₁}` then delivers
`himg`.  This is the precise §4↔§7 connection point: the Dade-isometry side enters as `τ` in
`htau1_diff` (the LHS `(χ − a·χ₁)^τ`), and the running coherence side as `hS₁.extension` in the
conclusion. -/

open OddOrder.RepresentationTheory in
/-- **Peterfalvi (5.6.2) image equation.**

Assembles the `himg : τ(χ − a·χ₁) = X − a·(hS₁.extension χ₁)` hypothesis of `retarget_isCoherent`
from the (5.4)/(5.6.2) decomposition `D : CharacterPsiDecomposition τ χ (a·χ₁)` and the three
honest facts:

* `htau1_diff : D.tau1 (χ − a·χ₁) = τ (χ − a·χ₁)` — the (5.4) auxiliary isometry `D.tau1` coincides
  with `τ` on the supported difference `χ − a·χ₁` (the (5.4) hypothesis "τ₁ coincides with τ on
  `ℤ[χ − ψ, χ − χ̄]`");
* `hY : D.Y = a • D.tau1 χ₁` — the (5.6.2) conclusion `Y = a·χ₁^{τ₁}` (after `λ = 0`, `Z = 0`);
* `htau1_chi1 : D.tau1 χ₁ = hS₁.extension χ₁` — `D.tau1` agrees with the running coherence extension
  at `χ₁ ∈ S₁`.

The output `himg` is *constructed* by chaining
`τ(χ − a·χ₁) = D.tau1(χ − a·χ₁) = D.X − D.Y = D.X − a·D.tau1 χ₁ = D.X − a·hS₁.extension χ₁`,
using `D.tau1_image` for the middle step. -/
theorem image_eq_of_decomposition
    {τ : IntegralCharacterMap L G} {S₁ : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hS₁ : IsCoherent τ S₁ A)
    {χ chi1 : ClassFunction L ℂ} {a : ℕ}
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ (a • chi1))
    (htau1_diff : D.tau1 (χ - a • chi1) = τ (χ - a • chi1))
    (hY : D.Y = a • D.tau1 chi1)
    (htau1_chi1 : D.tau1 chi1 = hS₁.extension chi1) :
    τ (χ - a • chi1) = D.X - a • hS₁.extension chi1 := by
  rw [← htau1_diff, D.tau1_image, hY, htau1_chi1]

/-! ### Peterfalvi (5.5)+(5.2.e): the running images `S₁^{τ₁}` are orthogonal to `R(χ)`

`retarget_isCoherent_of_decompositions` consumes, as its single still-opaque hypothesis,
`hperElem : ∀ ξ ∈ ℤ[S₁], ∀ α ∈ R(χ), ⟨τ₁ ξ, α⟩ = 0` (`τ₁ := hS₁.extension`).  In Peterfalvi this is
the one-line remark "`χᵢ^{τ₁}` is orthogonal to `R(χ)` by (5.5) and (5.2.e)" (mmd L77), lifted from
the family members `χᵢ ∈ S₁` to the whole lattice `ℤ[S₁]`.  The two lemmas below *construct* it:

* per family member `χ' ∈ S₁`, the `ψ = 0` decomposition `D'` gives `χ'^{τ₁} = D'.X ∈ ℤ[R(χ')]` (by
  (5.5), `eq_sum_of_psi_eq_zero`), which is orthogonal to `R(χ)` by (5.2.e) (`R(χ') ⊥ R(χ)`,
  `inner_X_orthogonal_imageSet_of_orthogonal`).  The running agreement `D'.tau1 χ' = τ₁ χ'`
  identifies `χ'^{τ₁}` with `D'.tau1 χ' = D'.X`;
* the lattice lift to `ℤ[S₁]` is span induction on `ξ`, using `ℤ`-linearity of `τ₁` and of
  `⟨·, α⟩` (`inner_extension_orthogonal_imageSet_of_members`).

These supply `hperElem` from the honest per-member (5.5)/(5.2.e) data, removing it as a posited
hypothesis. -/

open OddOrder.RepresentationTheory in
/-- **Per-member (5.5)+(5.2.e) orthogonality `χ'^{τ₁} ⊥ R(χ)`.**  For a family member `χ' ∈ S₁`
with its `ψ = 0` decomposition `D'` (so `χ'^{τ₁'} = D'.X ∈ ℤ[R(χ')]` by (5.5),
`eq_sum_of_psi_eq_zero`), whose image family `R(χ')` is orthogonal to the distinguished `R(χ) :=
R₀` (the (5.2.e) input `D'.imageFamily.Orthogonal R₀`), and whose auxiliary isometry agrees with the
running extension at `χ'` (`htau1 : D'.tau1 χ' = hS₁.extension χ'`), the running image
`χ'^{τ₁} = hS₁.extension χ'` is orthogonal to every `α ∈ R(χ)`:
`⟨hS₁.extension χ', α⟩ = ⟨D'.tau1 χ', α⟩ = ⟨D'.X, α⟩ = 0`.  This is the per-character content of
mmd L77, the building block of `hperElem`. -/
theorem inner_extension_member_orthogonal_imageSet
    {τ : IntegralCharacterMap L G} {S₁ : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hS₁ : IsCoherent τ S₁ A)
    {χ χ' : ClassFunction L ℂ}
    (R₀ : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ)
    (D' : CharacterPsiDecomposition (L := L) (G := G) τ χ' 0)
    (hortho : D'.imageFamily.Orthogonal R₀)
    (htau1 : D'.tau1 χ' = hS₁.extension χ')
    {α : ClassFunction G ℂ} (hα : α ∈ R₀.imageSet) :
    ClassFunction.inner (hS₁.extension χ') α = 0 := by
  rw [← htau1, (D'.eq_sum_of_psi_eq_zero).2.1,
    D'.inner_X_orthogonal_imageSet_of_orthogonal R₀ hortho hα]

open OddOrder.RepresentationTheory in
/-- **Lattice lift of the (5.5)+(5.2.e) orthogonality to `ℤ[S₁]`.**  If the running image of every
*member* `x ∈ S₁` is orthogonal to `α` (`hmem : ∀ x ∈ S₁, ⟨e x, α⟩ = 0`, supplied per-member by
`inner_extension_member_orthogonal_imageSet`), then the running image of every *lattice element*
`ξ ∈ ℤ[S₁]` is orthogonal to `α`.

Span induction on `ξ`: the base case is `hmem`; the `0`, `+` and `ℤ•` cases follow from the
`ℤ`-linearity of the extension `e` (`map_zero`/`map_add`/`map_zsmul`) and of `⟨·, α⟩`
(`inner_zero_left`/`inner_add_left`/`inner_smul_left`).  This is exactly the lift of the per-member
remark "`χᵢ^{τ₁}` is orthogonal to `R(χ)`" (mmd L77) to `ℤ[S₁]`. -/
theorem inner_extension_orthogonal_imageSet_of_members
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (e : IntegralCharacterMap L G) {S₁ : Set (ClassFunction L ℂ)} {α : ClassFunction G ℂ}
    (hmem : ∀ x ∈ S₁, ClassFunction.inner (e x) α = 0)
    {ξ : ClassFunction L ℂ} (hξ : ξ ∈ Submodule.span ℤ S₁) :
    ClassFunction.inner (e ξ) α = 0 := by
  induction hξ using Submodule.span_induction with
  | mem x hx => exact hmem x hx
  | zero => rw [map_zero, ClassFunction.inner_zero_left]
  | add x y _ _ ihx ihy => rw [map_add, ClassFunction.inner_add_left, ihx, ihy, add_zero]
  | smul c x _ ih =>
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ c (e x), ClassFunction.inner_smul_left, ih,
          mul_zero]

open scoped Classical in
open OddOrder.RepresentationTheory in
/-- **Peterfalvi (5.6.3) per-step coherence, `himg` discharged internally.**

The complete (5.6) adjoining step `IsCoherent τ S₁ A → IsCoherent τ (S₁ ∪ {χ, χ̄}) A`, with **both**
the orthonormal target pair `{X, X̄}` (from the (5.5) decomposition `D₀ : CharacterPsiDecomposition
τ χ 0`) **and** the (5.6.2) image equation `himg` *constructed*, not posited.  This is the single
clean entry point a (6.6)/(6.8) instantiation calls per `coherentPairChain` step: it consumes the
two honest decompositions and the (5.6.2)/(5.2.e) facts, and discharges `retarget_isCoherent`'s
`himg` via `image_eq_of_decomposition`.

The two decompositions and their common projection are exactly Peterfalvi's (5.6.3) data:
* `D₀ : CharacterPsiDecomposition τ χ 0` — the (5.5) decomposition giving `X = D₀.X = ∑_{α∈E}α` and
  the orthonormal pair `{X, X̄ := X − (χ−χ̄)^τ}` (`retargetTargetPair`);
* `Da : CharacterPsiDecomposition τ χ (a·χ₁)` — the (5.6.1) decomposition `(χ−a·χ₁)^τ = X − Y` whose
  `R(χ)`-projection feeds the (5.6.2) integer-forcing;
* `htau1_chi : Da.tau1 χ = D₀.tau1 χ` — both decompositions evaluate the *same* running `τ₁` at `χ`.
  This is the honest τ₁-agreement input; the (5.6.2) identification `Da.X = D₀.X` (the two `R(χ)`
  projections coincide, both `∑_{α∈E}α`) is then **derived** here via `X_eq_of_tau1_eq_on_chi`
  (`Da.X = Da.tau1 χ` from the (5.6.2) collapse `hY`, `= D₀.tau1 χ = D₀.X` from (5.5)), *not*
  posited;
* `hperElem : ∀ ξ ∈ ℤ[S₁], ∀ α ∈ R(χ), ⟨τ₁ ξ, α⟩ = 0` — the (5.5)+(5.2.e) **per-element**
  `R(χ)`-orthogonality of the running images.  The sum-level lattice orthogonalities
  `hX_ortho`/`hXbar_ortho` (`⟨τ₁ ξ, X⟩ = ⟨τ₁ ξ, X̄⟩ = 0`) consumed by
  `retarget_isCoherent_of_decomposition`
  are **derived** here via `inner_X_eq_zero_of_orthogonal_imageSet` /
  `inner_conjImage_eq_zero_of_orthogonal_imageSet` (using `X = ∑ coeff•α` and
  `(χ−χ̄)^τ = ∑_{α∈R(χ)}α`
  both in `ℤ[R(χ)]`), *not* posited.

The `himg` facts (`htau1_diff`, `hY`, `htau1_chi1`) are the (5.4)/(5.6.2)/(coherence-compat) inputs
of `image_eq_of_decomposition`. -/
noncomputable def retarget_isCoherent_of_decompositions
    {τ : IntegralCharacterMap L G} {S₁ : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hS₁ : IsCoherent τ S₁ A)
    {χ chibar chi1 : ClassFunction L ℂ} {a : ℕ}
    (D₀ : CharacterPsiDecomposition (L := L) (G := G) τ χ 0)
    (Da : CharacterPsiDecomposition (L := L) (G := G) τ χ (a • chi1))
    (htau1_chi : Da.tau1 χ = D₀.tau1 χ)
    (hχbar_eq : chibar = χ.conj)
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hperElem : ∀ ξ ∈ Submodule.span ℤ S₁,
      ∀ α ∈ D₀.imageFamily.imageSet, ClassFunction.inner (hS₁.extension ξ) α = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner chibar x = 0)
    (hchi1 : chi1 ∈ S₁)
    (htau1_diff : Da.tau1 (χ - a • chi1) = τ (χ - a • chi1))
    (hY : Da.Y = a • Da.tau1 chi1)
    (htau1_chi1 : Da.tau1 chi1 = hS₁.extension chi1)
    (hgen : zSupportedSpan (L := L) (S₁ ∪ {χ, chibar}) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χ - chibar, χ - a • chi1})) :
    IsCoherent τ (S₁ ∪ {χ, chibar}) A := by
  classical
  -- (5.6.3) projection identity `Da.X = D₀.X`, *constructed* from the (5.6.2) collapse `hY` and the
  -- τ₁-agreement `htau1_chi` (no longer posited).
  have hX_eq : Da.X = D₀.X :=
    CharacterPsiDecomposition.X_eq_of_tau1_eq_on_chi (a := a) D₀ Da hY htau1_chi
  -- (5.5)+(5.2.e) image-side orthogonalities `⟨τ₁ ξ, X⟩ = ⟨τ₁ ξ, X̄⟩ = 0`, *constructed* from the
  -- per-element `R(χ)`-orthogonality `hperElem` (no longer posited).
  have hX_ortho : ∀ ξ ∈ Submodule.span ℤ S₁,
      ClassFunction.inner (hS₁.extension ξ) D₀.X = 0 := fun ξ hξ =>
    D₀.inner_X_eq_zero_of_orthogonal_imageSet (hperElem ξ hξ)
  have hXbar_ortho : ∀ ξ ∈ Submodule.span ℤ S₁,
      ClassFunction.inner (hS₁.extension ξ) (D₀.X - τ (χ - chibar)) = 0 := by
    intro ξ hξ
    rw [hχbar_eq]
    exact D₀.inner_conjImage_eq_zero_of_orthogonal_imageSet (hperElem ξ hξ)
  -- `himg` for `D₀.X`, constructed from the (5.6.1) decomposition `Da` via the supplier, then
  -- rewritten through `hX_eq : Da.X = D₀.X`.
  have himg : τ (χ - a • chi1) = D₀.X - a • hS₁.extension chi1 := by
    rw [← hX_eq]
    exact image_eq_of_decomposition hS₁ Da htau1_diff hY htau1_chi1
  exact retarget_isCoherent_of_decomposition hS₁ D₀ hχbar_eq hχχ hχbarχbar hχχbar hχbarχ
    hX_ortho hXbar_ortho hχ_S1 hχbar_S1 hchi1 himg hgen

open scoped Classical in
open OddOrder.RepresentationTheory in
/-- **Peterfalvi (5.6.3) per-step coherence, `hperElem` *also* discharged internally.**

The completed (5.6) adjoining step where the last opaque hypothesis of
`retarget_isCoherent_of_decompositions` — the lattice orthogonality `hperElem : ∀ ξ ∈ ℤ[S₁], ∀ α ∈
R(χ), ⟨τ₁ ξ, α⟩ = 0` — is *constructed*, not posited, from the honest per-member (5.5)+(5.2.e) data.
Every (5.6.3) input now reduces to genuine textbook facts about the Dade map `τ` and the running
extension `τ₁ = hS₁.extension`; nothing about the *image-side* coupling remains assumed.

The extra data over `retarget_isCoherent_of_decompositions`, replacing `hperElem`, is the family of
per-member `ψ = 0` decompositions of `S₁` (mmd L77 "`χᵢ^{τ₁}` is orthogonal to `R(χ)` by (5.5) and
(5.2.e)"):
* `Dmem x hx : CharacterPsiDecomposition τ x 0` — the (5.5) decomposition of each member `x ∈ S₁`,
  giving `x^{τ₁'} = (Dmem x hx).X ∈ ℤ[R(x)]`;
* `hmemOrtho` — the (5.2.e) orthogonality `R(x) ⊥ R(χ)` (`(Dmem x hx).imageFamily.Orthogonal
  D₀.imageFamily`);
* `hmemTau1` — the running agreement `(Dmem x hx).tau1 x = hS₁.extension x` (each member's auxiliary
  isometry coincides with the running extension at `x`).

`hperElem` is then `inner_extension_orthogonal_imageSet_of_members` applied to the per-member
`inner_extension_member_orthogonal_imageSet` (which chains `⟨τ₁ x, α⟩ = ⟨(Dmem x hx).X, α⟩ = 0`).
The remaining hypotheses are identical to `retarget_isCoherent_of_decompositions`. -/
noncomputable def retarget_isCoherent_of_decompositions_and_memberFamily
    {τ : IntegralCharacterMap L G} {S₁ : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hS₁ : IsCoherent τ S₁ A)
    {χ chibar chi1 : ClassFunction L ℂ} {a : ℕ}
    (D₀ : CharacterPsiDecomposition (L := L) (G := G) τ χ 0)
    (Da : CharacterPsiDecomposition (L := L) (G := G) τ χ (a • chi1))
    (htau1_chi : Da.tau1 χ = D₀.tau1 χ)
    (hχbar_eq : chibar = χ.conj)
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (Dmem : (x : ClassFunction L ℂ) → x ∈ S₁ →
      CharacterPsiDecomposition (L := L) (G := G) τ x 0)
    (hmemOrtho : ∀ (x : ClassFunction L ℂ) (hx : x ∈ S₁),
      (Dmem x hx).imageFamily.Orthogonal D₀.imageFamily)
    (hmemTau1 : ∀ (x : ClassFunction L ℂ) (hx : x ∈ S₁),
      (Dmem x hx).tau1 x = hS₁.extension x)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner chibar x = 0)
    (hchi1 : chi1 ∈ S₁)
    (htau1_diff : Da.tau1 (χ - a • chi1) = τ (χ - a • chi1))
    (hY : Da.Y = a • Da.tau1 chi1)
    (htau1_chi1 : Da.tau1 chi1 = hS₁.extension chi1)
    (hgen : zSupportedSpan (L := L) (S₁ ∪ {χ, chibar}) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χ - chibar, χ - a • chi1})) :
    IsCoherent τ (S₁ ∪ {χ, chibar}) A := by
  classical
  -- The per-element `R(χ)`-orthogonality `hperElem`, *constructed* from the per-member
  -- (5.5)/(5.2.e)
  -- data: each member's running image `x^{τ₁} = (Dmem x hx).X ⊥ R(χ)`, lifted to `ℤ[S₁]`.
  have hperElem : ∀ ξ ∈ Submodule.span ℤ S₁,
      ∀ α ∈ D₀.imageFamily.imageSet, ClassFunction.inner (hS₁.extension ξ) α = 0 := by
    intro ξ hξ α hα
    refine inner_extension_orthogonal_imageSet_of_members hS₁.extension ?_ hξ
    intro x hx
    exact inner_extension_member_orthogonal_imageSet hS₁ D₀.imageFamily (Dmem x hx)
      (hmemOrtho x hx) (hmemTau1 x hx) hα
  exact retarget_isCoherent_of_decompositions hS₁ D₀ Da htau1_chi hχbar_eq hχχ hχbarχbar hχχbar
    hχbarχ hperElem hχ_S1 hχbar_S1 hchi1 htau1_diff hY htau1_chi1 hgen

open scoped Classical in
open OddOrder.RepresentationTheory in
/-- **Peterfalvi (5.6.3) per-step coherence from the SUPPORTED decomposition alone (X-family).**

The `ψ = 0` decomposition `D₀` of `retarget_isCoherent_of_decomposition[s]` requires
`τ₁χ ∈ ℤ[Irr G]`,
which fails for an *unsupported* induced `χ = Ind θ` (there `τ` is an off-support arbitrary
extension, so `τχ ∉ ℤ[Irr G]`).  This variant routes coherence entirely through the **supported**
decomposition `Da` of `χ − a·χ₁` (built from `(χ − a·χ₁)^{τ₁} ∈ ℤ[Irr G]`, which holds because the
degree-matched difference `χ − a·χ₁` vanishes at `1` and is supported on `A`): the target image is
`X := Da.X`, and the `{X, X̄}` orthonormality is *derived* from `Da` via the (5.4.a) keystone
`inner_self_chi_eq_sum_coeff` and the total-norm identity `inner_self_chi_add_psi_eq` — **never**
`τχ ∈ ZIrr`.  The remaining inputs are those of `retarget_isCoherent_of_decompositions` minus the
`ψ = 0` decomposition `D₀` and the `τ₁`-agreement, plus the member norm `‖χ₁‖² = 1`. -/
noncomputable def retarget_isCoherent_of_supportedDecomposition
    {τ : IntegralCharacterMap L G} {S₁ : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hS₁ : IsCoherent τ S₁ A)
    {χ chibar chi1 : ClassFunction L ℂ} {a : ℕ}
    (Da : CharacterPsiDecomposition (L := L) (G := G) τ χ (a • chi1))
    (hχbar_eq : chibar = χ.conj)
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hchi1chi1 : ClassFunction.inner chi1 chi1 = 1)
    (hperElem : ∀ ξ ∈ Submodule.span ℤ S₁,
      ∀ α ∈ Da.imageFamily.imageSet, ClassFunction.inner (hS₁.extension ξ) α = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner chibar x = 0)
    (hchi1 : chi1 ∈ S₁)
    (htau1_diff : Da.tau1 (χ - a • chi1) = τ (χ - a • chi1))
    (hY : Da.Y = a • Da.tau1 chi1)
    (htau1_chi1 : Da.tau1 chi1 = hS₁.extension chi1)
    (hgen : zSupportedSpan (L := L) (S₁ ∪ {χ, chibar}) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χ - chibar, χ - a • chi1})) :
    IsCoherent τ (S₁ ∪ {χ, chibar}) A := by
  classical
  subst hχbar_eq
  -- `himg` from the supported decomposition (the (5.6.2) image equation).
  have himg : τ (χ - a • chi1) = Da.X - a • hS₁.extension chi1 :=
    image_eq_of_decomposition hS₁ Da htau1_diff hY htau1_chi1
  -- `⟨a•χ₁, a•χ₁⟩ = a²`, `⟨τ₁χ₁, τ₁χ₁⟩ = ⟨χ₁,χ₁⟩ = 1`, hence `⟨Y, Y⟩ = a²`.
  have hpsipsi : ClassFunction.inner (a • chi1 : ClassFunction L ℂ) (a • chi1) = (a : ℂ) ^ 2 := by
    simp only [← Nat.cast_smul_eq_nsmul ℂ a chi1]
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hchi1chi1,
      star_natCast]
    ring
  have hextchi1 : ClassFunction.inner (hS₁.extension chi1) (hS₁.extension chi1) = 1 := by
    rw [hS₁.extension_inner_eq chi1 chi1 (Submodule.subset_span hchi1)
      (Submodule.subset_span hchi1), hchi1chi1]
  have hYY : ClassFunction.inner Da.Y Da.Y = (a : ℂ) ^ 2 := by
    rw [hY]
    simp only [← Nat.cast_smul_eq_nsmul ℂ a (Da.tau1 chi1)]
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, htau1_chi1,
      hextchi1, star_natCast]
    ring
  -- `‖X‖² = 1` from the total-norm identity `‖χ‖² + ‖a•χ₁‖² = ‖X‖² + ‖Y‖²`.
  have hXX : ClassFunction.inner Da.X Da.X = 1 := by
    have h := Da.inner_self_chi_add_psi_eq
    rw [hχχ, hpsipsi, hYY] at h
    linear_combination -h
  -- `⟨X, (χ−χ̄)^τ⟩ = ∑ coeff = ⟨χ,χ⟩ = 1` (the (5.4.a) keystone, supported route).
  have hXtau : ClassFunction.inner Da.X (τ (χ - χ.conj)) = 1 := by
    rw [Da.imageFamily.image_eq, Da.inner_X_sum, ← Da.inner_self_chi_eq_sum_coeff, hχχ]
  have hXtau' : ClassFunction.inner (τ (χ - χ.conj)) Da.X = 1 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXtau, star_one]
  -- `‖(χ−χ̄)^τ‖² = ‖χ−χ̄‖² = 2` (isometry of `τ₁` on the supported difference).
  have htautau : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - χ.conj)) = 2 := by
    rw [← Da.tau1_agrees, Da.tau1_inner_eq_on_support (χ - χ.conj) (χ - χ.conj)
        (CharacterPsiDecomposition.chi_sub_conj_mem_zSpan_support (χ := χ) (ψ := a • chi1))
        (CharacterPsiDecomposition.chi_sub_conj_mem_zSpan_support (χ := χ) (ψ := a • chi1)),
      ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
      hχχ, hχbarχbar, hχχbar, hχbarχ]
    ring
  -- `{X, X̄}` orthonormality, `X̄ := X − (χ−χ̄)^τ`.
  have hXbarXbar : ClassFunction.inner (Da.X - τ (χ - χ.conj)) (Da.X - τ (χ - χ.conj)) = 1 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
      hXX, hXtau, hXtau', htautau]; ring
  have hXXbar : ClassFunction.inner Da.X (Da.X - τ (χ - χ.conj)) = 0 := by
    rw [ClassFunction.inner_sub_right, hXX, hXtau]; ring
  have hXbarX : ClassFunction.inner (Da.X - τ (χ - χ.conj)) Da.X = 0 := by
    rw [ClassFunction.inner_sub_left, hXX, hXtau']; ring
  -- The running images `τ₁ ξ` (`ξ ∈ ℤ[S₁]`) are orthogonal to `X` and `X̄` (from `hperElem`).
  have hX_ortho : ∀ ξ ∈ Submodule.span ℤ S₁,
      ClassFunction.inner (hS₁.extension ξ) Da.X = 0 := fun ξ hξ =>
    Da.inner_X_eq_zero_of_orthogonal_imageSet (hperElem ξ hξ)
  have hXbar_ortho : ∀ ξ ∈ Submodule.span ℤ S₁,
      ClassFunction.inner (hS₁.extension ξ) (Da.X - τ (χ - χ.conj)) = 0 := fun ξ hξ =>
    Da.inner_conjImage_eq_zero_of_orthogonal_imageSet (hperElem ξ hξ)
  -- `X = Da.X ∈ ℤ[R(χ)] ⊂ ℤ[Irr G]` and `X̄ = Da.X − (χ − χ̄)^τ ∈ ℤ[Irr G]` (both
  -- `R(χ)`-combinations).
  have hXZ : Da.X ∈ ZIrr G := by
    rw [Da.X_eq]
    exact Submodule.sum_mem _ (fun α hα => by
      rw [Int.cast_smul_eq_zsmul ℂ (Da.coeff α) α]
      exact Submodule.smul_mem _ (Da.coeff α) (Da.imageFamily.mem_ZIrr α hα))
  have hXbarZ : Da.X - τ (χ - χ.conj) ∈ ZIrr G :=
    Submodule.sub_mem _ hXZ (by
      rw [Da.imageFamily.image_eq]
      exact Submodule.sum_mem _ (fun α hα => Da.imageFamily.mem_ZIrr α hα))
  exact retarget_isCoherent hS₁ hχχ hχbarχbar hχχbar hχbarχ hXX hXbarXbar hXXbar hXbarX
    hXZ hXbarZ hX_ortho hXbar_ortho rfl hχ_S1 hχbar_S1 hchi1 himg hgen

open scoped Classical in
open OddOrder.RepresentationTheory in
/-- **(5.6.3) supported per-step coherence, `hperElem` discharged from the member family
(X-family).**

The X-family analogue of `retarget_isCoherent_of_decompositions_and_memberFamily`: routes through
the
supported decomposition `Da` only (no `ψ=0` `D₀`, no `τχ ∈ ZIrr`), discharging the per-element
`R(χ)`-orthogonality `hperElem` from the per-member `ψ = 0` decompositions `Dmem` of `S₁` (mmd L77,
"`χᵢ^{τ₁}` is orthogonal to `R(χ)` by (5.5) and (5.2.e)"). -/
noncomputable def retarget_isCoherent_of_supportedDecomposition_and_memberFamily
    {τ : IntegralCharacterMap L G} {S₁ : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hS₁ : IsCoherent τ S₁ A)
    {χ chibar chi1 : ClassFunction L ℂ} {a : ℕ}
    (Da : CharacterPsiDecomposition (L := L) (G := G) τ χ (a • chi1))
    (hχbar_eq : chibar = χ.conj)
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hchi1chi1 : ClassFunction.inner chi1 chi1 = 1)
    (Dmem : (x : ClassFunction L ℂ) → x ∈ S₁ →
      CharacterPsiDecomposition (L := L) (G := G) τ x 0)
    (hmemOrtho : ∀ (x : ClassFunction L ℂ) (hx : x ∈ S₁),
      (Dmem x hx).imageFamily.Orthogonal Da.imageFamily)
    (hmemTau1 : ∀ (x : ClassFunction L ℂ) (hx : x ∈ S₁),
      (Dmem x hx).tau1 x = hS₁.extension x)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner chibar x = 0)
    (hchi1 : chi1 ∈ S₁)
    (htau1_diff : Da.tau1 (χ - a • chi1) = τ (χ - a • chi1))
    (hY : Da.Y = a • Da.tau1 chi1)
    (htau1_chi1 : Da.tau1 chi1 = hS₁.extension chi1)
    (hgen : zSupportedSpan (L := L) (S₁ ∪ {χ, chibar}) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χ - chibar, χ - a • chi1})) :
    IsCoherent τ (S₁ ∪ {χ, chibar}) A := by
  classical
  have hperElem : ∀ ξ ∈ Submodule.span ℤ S₁,
      ∀ α ∈ Da.imageFamily.imageSet, ClassFunction.inner (hS₁.extension ξ) α = 0 := by
    intro ξ hξ α hα
    refine inner_extension_orthogonal_imageSet_of_members hS₁.extension ?_ hξ
    intro x hx
    exact inner_extension_member_orthogonal_imageSet hS₁ Da.imageFamily (Dmem x hx)
      (hmemOrtho x hx) (hmemTau1 x hx) hα
  exact retarget_isCoherent_of_supportedDecomposition hS₁ Da hχbar_eq hχχ hχbarχbar hχχbar hχbarχ
    hchi1chi1 hperElem hχ_S1 hχbar_S1 hchi1 htau1_diff hY htau1_chi1 hgen

open scoped Classical in
open OddOrder.RepresentationTheory in
/-- **Peterfalvi (5.6.3) per-step coherence from a shared-isometry decomposition pair.**

The full (5.6) adjoining step `IsCoherent τ S₁ A → IsCoherent τ (S₁ ∪ {χ, χ̄}) A` with the two
distinguished decompositions `D₀`, `Da` *produced together* by
`CharacterPsiDecomposition.decompositionPair`
from a single shared auxiliary isometry `τ₁` — so the τ₁-agreement input `htau1_chi : Da.tau1 χ =
D₀.tau1
χ` of `retarget_isCoherent_of_decompositions_and_memberFamily` is discharged **structurally**
(`decompositionPair_tau1_agree`, by `rfl`), never posited.

This is the precise PASS 2 (ii) entry point for a (6.6) `hstep`: instead of supplying two ad-hoc
decompositions and *asserting* they evaluate the same running `τ₁` at `χ`, the caller supplies the
shared `(R(χ), τ₁, isometry, agreement)` and the two number-theoretic membership facts
`(χ − 0)^{τ₁}, (χ − a·χ₁)^{τ₁} ∈ ℤ[Irr G]`; both decompositions are then built against one isometry
by `decompositionPair`, and the projection identity `Da.X = D₀.X` ((5.6.3)) follows from the
*structural* agreement via the already-landed `X_eq_of_tau1_eq_on_chi`.

The remaining inputs are exactly those of `retarget_isCoherent_of_decompositions_and_memberFamily`,
restated for the produced `Da = (decompositionPair …).2`:
* the per-member `ψ = 0` family `Dmem`/`hmemOrtho`/`hmemTau1` (the (5.5)+(5.2.e) image-side data);
* the orthonormality of `{χ, χ̄}` and the `χ, χ̄ ⊥ S₁` relations;
* the (5.6.2) collapse `hY : Da.Y = a·χ₁^{τ₁}` (produced by `Y_eq_nsmul_tau1_of_lambdaForm`), the
  (5.4) agreement `htau1_diff`, and the coherence compatibility `htau1_chi1`. -/
noncomputable def retarget_isCoherent_of_sharedDecomposition
    {τ : IntegralCharacterMap L G} {S₁ : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hS₁ : IsCoherent τ S₁ A)
    {χ chibar chi1 : ClassFunction L ℂ} {a : ℕ}
    (imageFamily : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ)
    (tau1 : IntegralCharacterMap L G)
    (htau1_inner_eq : ∀ φ ζ : ClassFunction L ℂ,
      φ ∈ zSpan (L := L) {χ, χ.conj, 0, a • chi1} →
      ζ ∈ zSpan (L := L) {χ, χ.conj, 0, a • chi1} →
      ClassFunction.inner (tau1 φ) (tau1 ζ) = ClassFunction.inner φ ζ)
    (htau1_agrees : tau1 (χ - χ.conj) = τ (χ - χ.conj))
    (htau1_mem0 : tau1 (χ - 0) ∈ ZIrr G)
    (htau1_mema : tau1 (χ - a • chi1) ∈ ZIrr G)
    (hχbar_eq : chibar = χ.conj)
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hχχ1 : ClassFunction.inner χ chi1 = 0)
    (hχbarχ1 : ClassFunction.inner χ.conj chi1 = 0)
    (hχχbar' : ClassFunction.inner χ χ.conj = 0)
    (Dmem : (x : ClassFunction L ℂ) → x ∈ S₁ →
      CharacterPsiDecomposition (L := L) (G := G) τ x 0)
    (hmemOrtho : ∀ (x : ClassFunction L ℂ) (hx : x ∈ S₁),
      (Dmem x hx).imageFamily.Orthogonal imageFamily)
    (hmemTau1 : ∀ (x : ClassFunction L ℂ) (hx : x ∈ S₁),
      (Dmem x hx).tau1 x = hS₁.extension x)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner chibar x = 0)
    (hchi1 : chi1 ∈ S₁)
    (htau1_diff :
      ((CharacterPsiDecomposition.decompositionPair imageFamily tau1 htau1_inner_eq htau1_agrees
        htau1_mem0 htau1_mema hχχ1 hχbarχ1 hχχbar').2).tau1 (χ - a • chi1) = τ (χ - a • chi1))
    (hY :
      ((CharacterPsiDecomposition.decompositionPair imageFamily tau1 htau1_inner_eq htau1_agrees
        htau1_mem0 htau1_mema hχχ1 hχbarχ1 hχχbar').2).Y =
        a • ((CharacterPsiDecomposition.decompositionPair imageFamily tau1 htau1_inner_eq
            htau1_agrees
          htau1_mem0 htau1_mema hχχ1 hχbarχ1 hχχbar').2).tau1 chi1)
    (htau1_chi1 :
      ((CharacterPsiDecomposition.decompositionPair imageFamily tau1 htau1_inner_eq htau1_agrees
        htau1_mem0 htau1_mema hχχ1 hχbarχ1 hχχbar').2).tau1 chi1 = hS₁.extension chi1)
    (hgen : zSupportedSpan (L := L) (S₁ ∪ {χ, chibar}) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χ - chibar, χ - a • chi1})) :
    IsCoherent τ (S₁ ∪ {χ, chibar}) A :=
  -- The two decompositions are produced together against the *same* `τ₁`, so the τ₁-agreement
  -- `Da.tau1 χ = D₀.tau1 χ` is structural (`rfl`).
  retarget_isCoherent_of_decompositions_and_memberFamily hS₁
    (CharacterPsiDecomposition.decompositionPair imageFamily tau1 htau1_inner_eq htau1_agrees
      htau1_mem0 htau1_mema hχχ1 hχbarχ1 hχχbar').1
    (CharacterPsiDecomposition.decompositionPair imageFamily tau1 htau1_inner_eq htau1_agrees
      htau1_mem0 htau1_mema hχχ1 hχbarχ1 hχχbar').2
    (CharacterPsiDecomposition.decompositionPair_tau1_agree imageFamily tau1 htau1_inner_eq
      htau1_agrees htau1_mem0 htau1_mema hχχ1 hχbarχ1 hχχbar')
    hχbar_eq hχχ hχbarχbar hχχbar hχbarχ Dmem hmemOrtho hmemTau1 hχ_S1 hχbar_S1 hchi1
    htau1_diff hY htau1_chi1 hgen


end OddOrder.Peterfalvi.S07
