/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S08_CaseBAnchoredSeed
import OddOrder.Peterfalvi.S08_CaseBWeightedEndgame

/-!
# Peterfalvi §6.8.2 — case-(B) full `X(W₂) ∪ Y` coherence seed (the `(P4)` glue)

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §6, (6.8.2).

This leaf assembles the case-(B) **seed** `IsCoherent hyp.tau (X(W₂) ∪ Y)` from the full
`X`-coherence `caseBXset_isCoherent` (`S08_CaseBAnchoredSeed`, the anchored-image dichotomy
extension) and the `Y`-coherence `coherentYset`, via the §7 diagonal-aware glue engine.  It is the
full-`X(W₂)` analogue of the single-class `coherentCertainTypeSet_union_Yset_caseB`.

* `caseBXimg_seam_all_Yset` — the all-`Y` seam `⟨caseBXimg χ, η^{τ₁}⟩ = 0` for a *general*
  `X`-member `χ ∈ X(W₂)` (column or irreducible), generalizing the column-only
  `caseB_anchoredImage_seam_all_Yset`.
* `exists_glue_nu_Xset_Yset_via_map` — the full-source glue map: glues an arbitrary `X`-target map
  `νX` (on the orthonormal source `grid ∪ {irreducible X-members}`) with the `Y`-coherence map into
  a single `ν` agreeing with `νX` on all of `X(W₂)` (columns by linearity over the grid,
  irreducibles directly) and with `coherentYset.extension` on `Y`.
* `coherentXunionYset_caseB` — the (6.8.2) case-(B) seed producer: `IsCoherent hyp.tau (X(W₂) ∪ Y)`.

The seed feeds `nonempty_coherent_S_caseB` ((6.8.3) bootstrap) to give `IsCoherent hyp.tau S`.
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **Full-source glue map for the case-(B) `X(W₂) ∪ Y` coherence.**  The full-`X(W₂)` analogue of
`exists_glue_nu_columnSum_Yset_via_map`: from the orthonormal source `grid ∪ {irreducible
X-members}` (every member an irreducible character of `L`, so orthonormality is automatic) and the
orthonormal `Y`-family, glue *any* `X`-target map `νX` with `coherentYset.extension` into a single
`ν` agreeing with `νX` on **all** of `X(W₂)` and with `coherentYset.extension` on `Y`.

The agreement on `X(W₂)` splits via `caseB_S_member_column_or_irreducible`: a certain-type column
`μ_j = columnSum χ₂` matches by linearity over its grid constituents (each in the source), an
irreducible `X`-member is itself in the source.  The source-`⊥`-`Y` input is
`inner_columnFamily_mu_Yset_eq_zero` (grid) and `caseB_Xset_orthogonal_Yset` (irreducibles). -/
theorem exists_glue_nu_Xset_Yset_via_map
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (νX : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G) :
    ∃ ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G,
      (∀ x ∈ hyp.Xset h46.W2, ν x = νX x)
      ∧ (∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y) := by
  classical
  haveI : Finite ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :=
    SibleyDadeHypothesis.finite_linearCharacters_of_finite
  -- generic irreducible inner product (orthonormality of any two irreducibles)
  have hinner : ∀ φ ψ : ClassFunction ↥L ℂ, IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
  -- the source: grid constituents `{μ_{ij}}` together with the irreducible `X`-members.
  set grid : Set (ClassFunction ↥L ℂ) :=
    Set.range (fun p : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) × Fin (Nat.card h46.W1) =>
      ((h46.columnFamily p.1).mu p.2 : ClassFunction ↥L ℂ)) with hgrid
  set irrX : Set (ClassFunction ↥L ℂ) :=
    {x | x ∈ hyp.Xset h46.W2 ∧ IsIrreducibleCharacter x} with hirrX
  -- every source member is an irreducible character of `L`.
  have hsrc_irr : ∀ z ∈ grid ∪ irrX, IsIrreducibleCharacter z := by
    rintro z (⟨p, rfl⟩ | ⟨-, hirr⟩)
    · exact ((h46.columnFamily p.1).mu p.2).property
    · exact hirr
  have hirrXfin : irrX.Finite := hyp.S_finite.subset (fun x hx => hyp.Xset_subset_S hx.1)
  have hsrcfin : (grid ∪ irrX).Finite := (Set.finite_range _).union hirrXfin
  have hsrcorth : ∀ x ∈ grid ∪ irrX, ∀ x' ∈ grid ∪ irrX,
      ClassFunction.inner x x' = if x = x' then (1 : ℂ) else 0 :=
    fun x hx x' hx' => hinner x x' (hsrc_irr x hx) (hsrc_irr x' hx')
  have hYorth : ∀ y ∈ hyp.Yset, ∀ y' ∈ hyp.Yset,
      ClassFunction.inner y y' = if y = y' then (1 : ℂ) else 0 :=
    fun y hy y' hy' => hinner _ _ (hyp.isIrreducibleCharacter_of_mem_Yset hy)
      (hyp.isIrreducibleCharacter_of_mem_Yset hy')
  have hsrcY : ∀ x ∈ grid ∪ irrX, ∀ y ∈ hyp.Yset, ClassFunction.inner x y = 0 := by
    rintro x (⟨p, rfl⟩ | ⟨hxX, -⟩) y hy
    · exact inner_columnFamily_mu_Yset_eq_zero hyp h46 hW1 hy p.1 p.2
    · exact caseB_Xset_orthogonal_Yset hyp h46 hHK hW1 hW2comm x hxX y hy
  obtain ⟨ν, hνsrc, hνY⟩ :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthonormal
      hsrcfin hyp.Yset_finite hsrcorth hYorth hsrcY νX hyp.coherentYset.extension
  refine ⟨ν, fun x hx => ?_, hνY⟩
  rcases caseB_S_member_column_or_irreducible hyp h46 hHK (hyp.Xset_subset_S hx) with
    ⟨χ₂, -, hcol⟩ | hirr
  · -- column: `ν(columnSum) = νX(columnSum)` by linearity over the grid constituents.
    rw [← hcol, OddOrder.Peterfalvi.S06.columnSum_def]
    simp only [map_sum]
    exact Finset.sum_congr rfl fun i _ => hνsrc _ (Or.inl ⟨(χ₂, i), rfl⟩)
  · -- irreducible: `x` is itself in the source.
    exact hνsrc x (Or.inr ⟨hx, hirr⟩)

/-- **(6.8.2.3) all-`Y` seam for a general `X`-member.**  The full-`X(W₂)` analogue of the
column-only `caseB_anchoredImage_seam_all_Yset`: for *any* `χ ∈ X(W₂)` with anchored image
`τ(χ − a₀·η₁) = X − a₀·η₁^{τ₁}`, anchor seam `⟨X, η₁^{τ₁}⟩ = 0` and `H^#`-support, the image `X`
is orthogonal to `η^{τ₁}` for **every** `η ∈ Y`.

The proof is the column proof verbatim, with the column-`⊥`-`Y` orthogonality
`inner_columnSum_Yset_eq_zero` replaced by the member-`⊥`-`Y` orthogonality
`caseB_Xset_orthogonal_Yset` (valid for columns *and* irreducibles). -/
theorem caseB_member_seam_all_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) {a₀ : ℕ} {X : ClassFunction G ℂ}
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset h46.W2)
    (hanc : hyp.tau (χ - a₀ • η₁) = X - (a₀ : ℂ) • hyp.coherentYset.extension η₁)
    (hmix : ClassFunction.inner X (hyp.coherentYset.extension η₁) = 0)
    (hsupp : (χ - a₀ • η₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    {y : ClassFunction ↥L ℂ} (hy : y ∈ hyp.Yset) :
    ClassFunction.inner X (hyp.coherentYset.extension y) = 0 := by
  classical
  -- `y − η₁` is `H^#`-supported (equal degree `|W₁|`) and lies in the `Y`-span.
  have hydeg : y (1 : ↥L) = η₁ (1 : ↥L) :=
    (hyp.Yset_apply_one hy).trans (hyp.Yset_apply_one hη₁).symm
  have hysupp : (y - η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hy) (hyp.Yset_subset_S hη₁) hydeg
  have hymemZ : y - η₁ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥L) hyp.Yset :=
    Submodule.sub_mem _ (Submodule.subset_span hy) (Submodule.subset_span hη₁)
  have hη₁memZ : η₁ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥L) hyp.Yset :=
    Submodule.subset_span hη₁
  have hcYext : hyp.coherentYset.extension (y - η₁) = hyp.tau (y - η₁) :=
    hyp.coherentYset.extends_on_supported (y - η₁) ⟨hymemZ, hysupp⟩
  -- `X = τ(χ − a₀η₁) + a₀·ν₁`.
  have hX : X = hyp.tau (χ - a₀ • η₁) + (a₀ : ℂ) • hyp.coherentYset.extension η₁ := by
    rw [hanc]; abel
  -- split `⟨X, ν_y⟩ = ⟨X, cY(y − η₁)⟩ + ⟨X, ν₁⟩` and discharge the anchor term by `hmix`.
  have hsplit : ClassFunction.inner X (hyp.coherentYset.extension y)
      = ClassFunction.inner X (hyp.coherentYset.extension (y - η₁))
        + ClassFunction.inner X (hyp.coherentYset.extension η₁) := by
    rw [map_sub, ClassFunction.inner_sub_right]; ring
  rw [hsplit, hmix, add_zero, hcYext]
  -- the Dade isometry of `τ` on the supported pair `{χ − a₀η₁, y − η₁}`.
  have hiso : ClassFunction.inner (hyp.tau (χ - a₀ • η₁)) (hyp.tau (y - η₁))
      = ClassFunction.inner (χ - a₀ • η₁) (y - η₁) :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp.dade hyp.hconj
      (S := ({χ - a₀ • η₁, y - η₁} : Set (ClassFunction ↥L ℂ)))
      (by intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
          rcases hs with rfl | rfl; exacts [hsupp, hysupp])
      (Submodule.subset_span (Set.mem_insert _ _))
      (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  -- the `Y`-isometry of `cY`: `⟨ν₁, τ(y − η₁)⟩ = ⟨η₁, y − η₁⟩`.
  have hcYiso : ClassFunction.inner (hyp.coherentYset.extension η₁) (hyp.tau (y - η₁))
      = ClassFunction.inner η₁ (y - η₁) := by
    rw [← hcYext, hyp.coherentYset.extension_inner_eq η₁ (y - η₁) hη₁memZ hymemZ]
  -- the member is orthogonal to `Y` (columns and irreducibles alike).
  have hμy : ClassFunction.inner χ y = 0 :=
    caseB_Xset_orthogonal_Yset hyp h46 hHK hW1 hW2comm χ hχ y hy
  have hμη : ClassFunction.inner χ η₁ = 0 :=
    caseB_Xset_orthogonal_Yset hyp h46 hHK hW1 hW2comm χ hχ η₁ hη₁
  have hηirr : IsIrreducibleCharacter η₁ := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  have hηη : ClassFunction.inner η₁ η₁ = 1 := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L)
      (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L)
    rwa [if_pos rfl] at h
  -- assemble: the `c = ⟨η₁, y⟩` terms cancel.
  rw [hX, ClassFunction.inner_add_left, hiso, ClassFunction.inner_smul_left, hcYiso]
  simp only [← Nat.cast_smul_eq_nsmul ℂ a₀ η₁, ClassFunction.inner_sub_left,
    ClassFunction.inner_sub_right, ClassFunction.inner_smul_left, hμy, hμη, hηη]
  ring

/-- **Degree ratio of an `Xset W₂`-span element against the anchor `χ₁`** (varying-degree analogue
of `certainTypeSet_span_apply_one_eq_intMul`).  Every `ψ ∈ ℤ[X(W₂)]` has degree an integer multiple
of the anchor degree `χ₁(1)`.  Unlike the certain-type single-class set (where the ratio comes from
*equal degree*), here the per-member integrality is the `p`-power divisibility `hdvd`
(`χ(1) = d·χ₁(1)`, `d ∈ ℕ`, available since `H` is a `p`-group and `χ₁` has minimal degree); span
induction lifts it to integer combinations. -/
theorem Xset_span_apply_one_eq_intMul
    (hyp : SibleyDadeHypothesis G L H) {W2 : Subgroup ↥L}
    {χ₁ : ClassFunction ↥L ℂ}
    (hdvd : ∀ f ∈ hyp.Xset W2, ∃ d : ℕ, (f : ClassFunction ↥L ℂ) 1 = (d : ℂ) * χ₁ 1)
    {ψ : ClassFunction ↥L ℂ} (hψ : ψ ∈ Submodule.span ℤ (hyp.Xset W2)) :
    ∃ s : ℤ, ψ 1 = (s : ℂ) * χ₁ 1 := by
  classical
  induction hψ using Submodule.span_induction with
  | mem x hx => obtain ⟨d, hd⟩ := hdvd x hx; exact ⟨d, by rw [hd]; push_cast; ring⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨sx, hsx⟩ := hx; obtain ⟨sy, hsy⟩ := hy
      exact ⟨sx + sy, by rw [ClassFunction.add_apply, hsx, hsy]; push_cast; ring⟩
  | smul c x _ hx =>
      obtain ⟨sx, hsx⟩ := hx
      exact ⟨c * sx, by
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hsx]; push_cast; ring⟩

/-- **(6.8.1) generation hypothesis for the full case-(B) `X(W₂) ∪ Y` union.**  The varying-degree
analogue of `hgen_withDiagonal_certainTypeSet`: with anchor `χ₁ ∈ X(W₂)` (`χ₁(1) = a₁·η₁(1)`,
`η₁ ∈ Y` of degree `|W₁|`) and the `p`-power divisibility `hdvd`, the single cross-diagonal
`χ₁ − a₁·η₁` makes the supported lattice of `X(W₂) ∪ Y` generated by the supported sublattices of
`X(W₂)` and `Y` together with that diagonal.  Same `φ = (φ_X − s·χ₁) + (φ_Y + s·a₁·η₁) +
s·(χ₁ − a₁·η₁)` split as the certain-type proof, with the integer ratio `s` from
`Xset_span_apply_one_eq_intMul`. -/
theorem hgen_withDiagonal_Xset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {W2 : Subgroup ↥L}
    {χ₁ : ClassFunction ↥L ℂ} (hanchor : χ₁ ∈ hyp.Xset W2)
    (hdvd : ∀ f ∈ hyp.Xset W2, ∃ d : ℕ, (f : ClassFunction ↥L ℂ) 1 = (d : ℂ) * χ₁ 1)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) {a₁ : ℕ}
    (ha₁ : χ₁ 1 = (a₁ : ℂ) * η₁ 1) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset W2 ∪ hyp.Yset)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
      Submodule.span ℤ
        (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset W2)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          {χ₁ - a₁ • η₁}) := by
  classical
  intro φ hφ
  obtain ⟨hφspan, hφsupp⟩ := hφ
  -- `φ(1) = 0`: `1 ∉ A = H^#`.
  have h1 : φ 1 = 0 := by
    by_contra h
    have hmem := hφsupp (ClassFunction.mem_support.mpr h)
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hmem
    simp only [sharpImage, Set.mem_diff, Set.mem_singleton_iff] at hmem
    exact hmem.2 (by simp)
  -- split `φ = φ_X + φ_Y`.
  rw [OddOrder.Peterfalvi.S07.zSpan, Submodule.span_union] at hφspan
  obtain ⟨φX, hφX, φY, hφY, hsum⟩ := Submodule.mem_sup.mp hφspan
  -- the integer `s` with `φ_X(1) = s·χ₁(1)` (degree-ratio integrality from `hdvd`).
  obtain ⟨s, hφX1⟩ := Xset_span_apply_one_eq_intMul hyp hdvd hφX
  rw [ha₁] at hφX1
  -- `φ_Y(1) = −s·(a₁·η₁(1))`.
  have hφY1 : φY 1 = -((s : ℂ) * ((a₁ : ℂ) * η₁ 1)) := by
    have haux : φX 1 + φY 1 = 0 := by
      have hc := congrArg (fun ψ : ClassFunction ↥L ℂ => ψ 1) hsum
      simpa [ClassFunction.add_apply, h1] using hc
    linear_combination haux - hφX1
  -- the smul degrees.
  have hsχ₁1 : (s • χ₁ : ClassFunction ↥L ℂ) 1 = (s : ℂ) * ((a₁ : ℂ) * η₁ 1) := by
    rw [← Int.cast_smul_eq_zsmul ℂ s χ₁, ClassFunction.smul_apply, ha₁]
  have hsaη₁1 : (s • (a₁ • η₁) : ClassFunction ↥L ℂ) 1 = (s : ℂ) * ((a₁ : ℂ) * η₁ 1) := by
    rw [← Int.cast_smul_eq_zsmul ℂ s (a₁ • η₁), ClassFunction.smul_apply,
      ← Nat.cast_smul_eq_nsmul ℂ a₁ η₁, ClassFunction.smul_apply]
  -- the three pieces are degree 0 and span-members.
  have hp1deg : (φX - s • χ₁ : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.sub_apply, hφX1, hsχ₁1]; ring
  have hp2deg : (φY + s • (a₁ • η₁) : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.add_apply, hφY1, hsaη₁1]; ring
  have hp1span : (φX - s • χ₁) ∈ Submodule.span ℤ (hyp.Xset W2) :=
    Submodule.sub_mem _ hφX (Submodule.smul_mem _ s (Submodule.subset_span hanchor))
  have hp2span : (φY + s • (a₁ • η₁)) ∈ Submodule.span ℤ hyp.Yset :=
    Submodule.add_mem _ hφY
      (Submodule.smul_mem _ s (nsmul_mem (Submodule.subset_span hη₁) a₁))
  have hp1supp : (φX - s • χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hyp.Xset_subset_S hp1span) hp1deg
  have hp2supp : (φY + s • (a₁ • η₁)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hyp.Yset_subset_S hp2span) hp2deg
  -- assemble `φ = p1 + p2 + p3` (the `s·χ₁`, `s·(a₁·η₁)` terms cancel).
  have hφeq : φ = (φX - s • χ₁) + (φY + s • (a₁ • η₁)) + s • (χ₁ - a₁ • η₁) := by
    rw [smul_sub, ← hsum]; abel
  rw [hφeq]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_left _ ⟨hp1span, hp1supp⟩))
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_right _ ⟨hp2span, hp2supp⟩))
  · exact Submodule.smul_mem _ s
      (Submodule.subset_span (Set.mem_union_right _ (Set.mem_singleton _)))

/-- **Peterfalvi (6.8.2) case-(B) `X(W₂) ∪ Y` coherence seed.**  The full-`X(W₂)` analogue of
`coherentCertainTypeSet_union_Yset_caseB`: under the case-(B) structural data (with anchor
`χ₁ ∈ X(W₂)` of minimal degree dividing every `X`-member, `hdvd`), `hyp.tau` is coherent on
`X(W₂) ∪ Y`.

The `X`-coherence is the anchored-image dichotomy `caseBXset_isCoherent`; it is glued with the
`Y`-coherence through the §7 diagonal-aware engine `coherentXunionYset_caseB_of_glued`:
* `ν` (`exists_glue_nu_Xset_Yset_via_map`) agrees with the dichotomy extension on `X(W₂)` and with
  `coherentYset` on `Y`;
* `hmixed` is the all-`Y` seam `caseB_member_seam_all_Yset` applied to each member's anchored image
  (`caseBXimg_spec`), both sides vanishing;
* the cross-diagonal `χ₁ − a₁·η₁` (anchor degree `χ₁(1) = a₁·η₁(1)`) gives `hDτ` by construction
  (the anchored image identity) and `hgen` via `hgen_withDiagonal_Xset`.

This is the seed consumed by `nonempty_coherent_S_caseB` ((6.8.3) bootstrap) to coherence of `S`. -/
noncomputable def coherentXunionYset_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Fintype ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
    (hW2H : h46.W2 ≤ H) (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hderiv : h46.W2.subgroupOf H ≤ commutator ↥H)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (hprime : (Nat.card h46.W2).Prime) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (hW2cenL : h46.W2 ≤ Subgroup.center ↥L)
    (hc2 : 2 ≤ (h46.W2.subgroupOf H).index)
    (hFPF : (h46.W2.index : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) ^ 2)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) (hYcard : hyp.Yset.ncard ≠ 2)
    (hη₁1 : η₁ (1 : ↥L) ≠ 0)
    {χ₁ : ClassFunction ↥L ℂ} (hanchor : χ₁ ∈ hyp.Xset h46.W2) (hχ₁1 : χ₁ (1 : ↥L) ≠ 0)
    (hdvd : ∀ f ∈ hyp.Xset h46.W2, ∃ d : ℕ, (f : ClassFunction ↥L ℂ) 1 = (d : ℂ) * χ₁ 1)
    (hnonzero : ∃ φ : ClassFunction ↥L ℂ, φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.Xset h46.W2) (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧ φ ≠ 0) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset h46.W2 ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  -- the full `X(W₂)`-coherence `cX` (anchored-image dichotomy extension).
  set cX := caseBXset_isCoherent hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm
    hW2cenL hc2 hFPF hη₁ hYcard hη₁1 hanchor hχ₁1 hdvd hnonzero with hcXdef
  -- on every `X`-member, `cX.extension = caseBXimg` (the anchored image).
  have hcXext : ∀ x ∈ hyp.Xset h46.W2, cX.extension x =
      caseBXimg hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2 hFPF
        hη₁ hYcard x := by
    intro x hx
    rw [hcXdef]
    exact caseBXsetExtension_eq hyp h46 hHK hW1 _ hx
  -- the glue map `ν` agreeing with `cX.extension` on `X(W₂)` and `cY` on `Y` (extracted via
  -- `Exists.choose` since the eventual goal `IsCoherent` lives in `Type`).
  have hglue := exists_glue_nu_Xset_Yset_via_map hyp h46 hHK hW1 hW2comm cX.extension
  set ν := hglue.choose with hνdef
  have hagreeX : ∀ x ∈ hyp.Xset h46.W2, ν x = cX.extension x := hglue.choose_spec.1
  have hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y := hglue.choose_spec.2
  -- `X(W₂) ⊥ Y`.
  have hpair := caseB_Xset_orthogonal_Yset hyp h46 hHK hW1 hW2comm (W2 := h46.W2)
  -- `hmixed`: both sides vanish (`X ⊥ Y` and the image seam `caseBXimg ⊥ Y^{τ₁}`).
  have hmixed : ∀ x ∈ hyp.Xset h46.W2, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y := by
    intro x hx y hy
    rw [hagreeX x hx, hagreeY y hy, hpair x hx y hy, hcXext x hx]
    obtain ⟨a, -, hanc, hmix, -, hsupp⟩ := caseBXimg_spec hyp h46 hHK hW1 hW2H hcen hderiv hcop
      hp hHp hprime hW2comm hW2cenL hc2 hFPF hη₁ hYcard hx
    exact caseB_member_seam_all_Yset hyp h46 hHK hW1 hW2comm hη₁ hx hanc hmix hsupp hy
  -- the cross-diagonal `χ₁ − a₁·η₁` (`a₁` = anchor weight from `caseBXimg_spec`; extracted via
  -- `Exists.choose` since the eventual goal `IsCoherent` lives in `Type`).
  have hanchorSpec := caseBXimg_spec hyp h46 hHK hW1 hW2H hcen hderiv hcop
    hp hHp hprime hW2comm hW2cenL hc2 hFPF hη₁ hYcard hanchor
  set a₁ : ℕ := hanchorSpec.choose with ha₁def
  have ha₁deg : χ₁ 1 = (a₁ : ℂ) * η₁ 1 := hanchorSpec.choose_spec.1
  have ha₁anc : hyp.tau (χ₁ - a₁ • η₁)
      = caseBXimg hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2 hFPF
          hη₁ hYcard χ₁ - (a₁ : ℂ) • hyp.coherentYset.extension η₁ :=
    hanchorSpec.choose_spec.2.1
  -- `hDτ`: ν agrees with τ on the diagonal (by the anchored image identity).
  have hDτ : ∀ d ∈ ({χ₁ - a₁ • η₁} : Set (ClassFunction ↥L ℂ)), ν d = hyp.tau d := by
    intro d hd
    rw [Set.mem_singleton_iff] at hd; subst hd
    rw [map_sub, map_nsmul, hagreeX χ₁ hanchor, hagreeY η₁ hη₁, hcXext χ₁ hanchor, ha₁anc,
      Nat.cast_smul_eq_nsmul]
  exact hyp.coherentXunionYset_caseB_of_glued cX ν hagreeX hagreeY hpair hmixed
    {χ₁ - a₁ • η₁} hDτ (hgen_withDiagonal_Xset hyp hanchor hdvd hη₁ ha₁deg)

/-- **Peterfalvi (6.8) case-(B): `S` is coherent (from the anchor data).**  The case-(B) analogue of
`nonempty_coherent_S_caseA_of_frobenius`, with the seed *constructed* (not hypothesized): the
`X(W₂) ∪ Y` coherence seed `coherentXunionYset_caseB` is fed to the (6.8.3) bootstrap
`nonempty_coherent_S_caseB`.

This reduces the case-(B) branch of `sibleySetup_is_coherent` to the case-(B) structural data
together with the three anchor obligations — a minimal-degree anchor `χ₁ ∈ X(W₂)` (`hanchor`,
`hχ₁1`), its `p`-power divisibility `hdvd`, and a nonzero supported witness `hnonzero` — all
constructible from the `p`-group structure at the dispatch. -/
theorem nonempty_coherent_S_caseB_of_anchor
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Fintype ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
    (hW2H : h46.W2 ≤ H) (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hderiv : h46.W2.subgroupOf H ≤ commutator ↥H)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (hprime : (Nat.card h46.W2).Prime) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (hW2cenL : h46.W2 ≤ Subgroup.center ↥L)
    (hc2 : 2 ≤ (h46.W2.subgroupOf H).index)
    (hFPF : (h46.W2.index : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) ^ 2)
    (hcZ : 2 ≤ Nat.card ↥(h46.W2.subgroupOf H))
    (hfpf : (2 * Nat.card hyp.W1 + 1) ^ 2 ≤ Nat.card (↥H ⧸ h46.W2.subgroupOf H))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) (hYcard : hyp.Yset.ncard ≠ 2)
    (hη₁1 : η₁ (1 : ↥L) ≠ 0)
    {χ₁ : ClassFunction ↥L ℂ} (hanchor : χ₁ ∈ hyp.Xset h46.W2) (hχ₁1 : χ₁ (1 : ↥L) ≠ 0)
    (hdvd : ∀ f ∈ hyp.Xset h46.W2, ∃ d : ℕ, (f : ClassFunction ↥L ℂ) 1 = (d : ℂ) * χ₁ 1)
    (hnonzero : ∃ φ : ClassFunction ↥L ℂ, φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.Xset h46.W2) (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧ φ ≠ 0) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) :=
  nonempty_coherent_S_caseB hyp h46 hHK hW1 hcen hcZ hfpf
    ⟨coherentXunionYset_caseB hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL
      hc2 hFPF hη₁ hYcard hη₁1 hanchor hχ₁1 hdvd hnonzero⟩

end OddOrder.Peterfalvi.S08
