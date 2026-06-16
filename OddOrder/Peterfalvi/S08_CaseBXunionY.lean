/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CaseBAssembly

/-!
# Peterfalvi §8: case-(B) `X ∪ Y` base union (generation hypothesis)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, pp. 30-37 (mmd `references/peterfalvi/04.8` L156-244).

This leaf assembles the **base** of the case-(B) `(6.8.2)` coherence construction.  Following the
settled session-44 architecture (`notes/peterfalvi/s08_6_8_assembly_plan.md`), the coherent set
`X ∪ Y` is built starting from the base `certainTypeSet h46 k ⊔ Y` (which already contains the
`Y`-anchor `η₁` and all the reducible certain-type columns `μ_j`), and the irreducible `X`-members
are adjoined later by the standard retarget engine.

The **generation hypothesis** `hgen` of the glue engine
`coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` (S07) is the `(6.8.1)`
degree-bookkeeping fact: with `μ_{j₀} = columnSum k0` a reference column *member*
(degree `μ_{j₀}(1) = a₀·|W₁|`) and `η₁ ∈ Y` (degree `|W₁|`), the cross-diagonal
`μ_{j₀} − a₀·η₁` is supported and generates (together with the supported sublattices of
`certainTypeSet` and `Y`) the whole supported lattice of the union.  This is the column
analogue of `hgen_withDiagonal_of_frobenius`
(`S08_CoherenceCore`); the Frobenius degree-ratio input
`exists_charValue_one_eq_mul_xBaseBlock_anchor` is replaced here by the **equal-degree** property
*built into* `certainTypeSet h46 k` (every member shares the reference degree, hence equals the
anchor member degree `μ_{j₀}(1)`), so the per-`X` degree ratio is always an integer.

Reference note: `notes/peterfalvi/s08_6_8_assembly_plan.md` (session 44).
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **Degree ratio of a `certainTypeSet`-span element against any reference column member.**

Every `ψ ∈ ℤ[certainTypeSet h46 k]` has degree an integer multiple of `μ_{j₀}(1)` for any
anchor member `μ_{j₀} = columnSum h46 k0 ∈ certainTypeSet h46 k`.  The single-member case is
*ratio 1* — the *defining* property of `certainTypeSet h46 k`: every member
`μ_{χ₂} = columnSum χ₂` shares the reference degree `∑_i μ_{ik}(1)` (`columnSum_apply_one`),
and so does the anchor member `μ_{j₀}`, so `μ_{χ₂}(1) = μ_{j₀}(1)`.  Span induction lifts to
integer combinations.

This is the column analogue of the Frobenius `hsX` step of `hgen_withDiagonal_of_frobenius`, with the
degree-ratio integrality coming from the equal-degree condition built into `certainTypeSet` rather
than from `exists_charValue_one_eq_mul_xBaseBlock_anchor`. -/
theorem certainTypeSet_span_apply_one_eq_intMul
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {k k0 : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ}
    (hk0mem : OddOrder.Peterfalvi.S06.columnSum h46 k0
      ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k)
    {ψ : ClassFunction ↥L ℂ}
    (hψ : ψ ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S06.certainTypeSet h46 k)) :
    ∃ s : ℤ,
      ψ 1 = (s : ℂ) * (OddOrder.Peterfalvi.S06.columnSum h46 k0 : ClassFunction ↥L ℂ) 1 := by
  classical
  -- The reference-column-member degree equals the certain-type reference degree.
  obtain ⟨k0', _hk0'ne, hk0deg, hk0eq⟩ := hk0mem
  have hanchor1 : (OddOrder.Peterfalvi.S06.columnSum h46 k0 : ClassFunction ↥L ℂ) 1
      = (∑ i, ((h46.columnFamily k).mu i : ClassFunction ↥L ℂ) 1) := by
    rw [hk0eq, OddOrder.Peterfalvi.S06.columnSum_apply_one, hk0deg]
  induction hψ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨χ₂, _hχ₂, hdeg, rfl⟩ := hx
      refine ⟨1, ?_⟩
      rw [OddOrder.Peterfalvi.S06.columnSum_apply_one, hdeg, hanchor1]
      push_cast; ring
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨sx, hsx⟩ := hx; obtain ⟨sy, hsy⟩ := hy
      exact ⟨sx + sy, by rw [ClassFunction.add_apply, hsx, hsy]; push_cast; ring⟩
  | smul c x _ hx =>
      obtain ⟨sx, hsx⟩ := hx
      refine ⟨c * sx, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hsx]; push_cast; ring

/-- **(6.8.1) generation hypothesis for the case-(B) `certainTypeSet ⊔ Y` base union.**

The cross-diagonal-aware generation hypothesis `hgen` consumed by the §7 glue engine
`coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`, instantiated for the base
`X := certainTypeSet h46 k`, `Y := Yset`, with the single cross-diagonal
`D := {columnSum h46 k0 − a₀·η₁}` (`μ_{j₀} = columnSum k0` a chosen reference column *member*).

The plain generation (without `D`) is **false** here — the `(6.8.1)` phenomenon: a column degree is
`a₀·|W₁|` (with `a₀ > 1` in the non-degenerate case) while `η₁(1) = |W₁|`, so the supported
combination `μ_{j₀} − a₀·η₁ ∈ ℤ[certainTypeSet ∪ Y]` is *not* a sum of a supported
`certainTypeSet`-combination and a supported `Y`-combination.  Adjoining the single cross-diagonal
makes `hgen` hold: any supported `φ` splits `φ = φ_X + φ_Y` with `φ_X(1) = s·μ_{j₀}(1)`
(the integer ratio `s` from the equal-degree property
`certainTypeSet_span_apply_one_eq_intMul`); then the three pieces `(φ_X − s·μ_{j₀})`,
`(φ_Y + s·(a₀·η₁))`, `s·(μ_{j₀} − a₀·η₁)` are each supported and lie in the right submodule.

This mirrors `hgen_withDiagonal_of_frobenius` (`S08_CoherenceCore`) with the certain-type
equal-degree replacing the Frobenius anchor-degree-ratio. -/
theorem hgen_withDiagonal_certainTypeSet
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hHK : h46.K = H)
    {k k0 : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ}
    (hk0mem : OddOrder.Peterfalvi.S06.columnSum h46 k0
      ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {a₀ : ℕ}
    (ha₀ : (OddOrder.Peterfalvi.S06.columnSum h46 k0 : ClassFunction ↥L ℂ) 1
      = (a₀ : ℂ) * η₁ 1) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (OddOrder.Peterfalvi.S06.certainTypeSet h46 k ∪ hyp.Yset)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
      Submodule.span ℤ
        (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
            (OddOrder.Peterfalvi.S06.certainTypeSet h46 k)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          {OddOrder.Peterfalvi.S06.columnSum h46 k0 - a₀ • η₁}) := by
  classical
  -- `certainTypeSet ⊆ S` (via `Xset`) and `Yset ⊆ S` for the support helper.
  have hXS : OddOrder.Peterfalvi.S06.certainTypeSet h46 k ⊆ hyp.S :=
    (hyp.certainTypeSet_subset_Xset h46 hHK k).trans hyp.Xset_subset_S
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
  -- the integer `s` with `φ_X(1) = s·μ_{j₀}(1)` (degree-ratio integrality from equal degree).
  obtain ⟨s, hφX1⟩ := certainTypeSet_span_apply_one_eq_intMul h46 hk0mem hφX
  rw [ha₀] at hφX1
  -- `φ_Y(1) = −s·(a₀·η₁(1))`.
  have hφY1 : φY 1 = -((s : ℂ) * ((a₀ : ℂ) * η₁ 1)) := by
    have haux : φX 1 + φY 1 = 0 := by
      have hc := congrArg (fun ψ : ClassFunction ↥L ℂ => ψ 1) hsum
      simpa [ClassFunction.add_apply, h1] using hc
    linear_combination haux - hφX1
  -- the smul degrees.
  have hsχ₁1 :
      (s • OddOrder.Peterfalvi.S06.columnSum h46 k0 : ClassFunction ↥L ℂ) 1
        = (s : ℂ) * ((a₀ : ℂ) * η₁ 1) := by
    rw [← Int.cast_smul_eq_zsmul ℂ s (OddOrder.Peterfalvi.S06.columnSum h46 k0),
      ClassFunction.smul_apply, ha₀]
  have hsaη₁1 : (s • (a₀ • η₁) : ClassFunction ↥L ℂ) 1 = (s : ℂ) * ((a₀ : ℂ) * η₁ 1) := by
    rw [← Int.cast_smul_eq_zsmul ℂ s (a₀ • η₁), ClassFunction.smul_apply,
      ← Nat.cast_smul_eq_nsmul ℂ a₀ η₁, ClassFunction.smul_apply]
  -- the three pieces are degree 0 (for the supported ones) and span-members.
  have hp1deg :
      (φX - s • OddOrder.Peterfalvi.S06.columnSum h46 k0 : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.sub_apply, hφX1, hsχ₁1]; ring
  have hp2deg : (φY + s • (a₀ • η₁) : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.add_apply, hφY1, hsaη₁1]; ring
  have hp1span : (φX - s • OddOrder.Peterfalvi.S06.columnSum h46 k0) ∈
      Submodule.span ℤ (OddOrder.Peterfalvi.S06.certainTypeSet h46 k) :=
    Submodule.sub_mem _ hφX (Submodule.smul_mem _ s (Submodule.subset_span hk0mem))
  have hp2span : (φY + s • (a₀ • η₁)) ∈ Submodule.span ℤ hyp.Yset :=
    Submodule.add_mem _ hφY
      (Submodule.smul_mem _ s (nsmul_mem (Submodule.subset_span hη₁) a₀))
  -- supports via the degree-0 ⟹ supported helper (members in `ℤ[S]`).
  have hp1supp : (φX - s • OddOrder.Peterfalvi.S06.columnSum h46 k0).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hXS hp1span) hp1deg
  have hp2supp : (φY + s • (a₀ • η₁)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hyp.Yset_subset_S hp2span) hp2deg
  -- assemble `φ = p1 + p2 + p3` (the `s·μ_{j₀}`, `s·(a₀·η₁)` terms cancel).
  have hφeq : φ = (φX - s • OddOrder.Peterfalvi.S06.columnSum h46 k0)
      + (φY + s • (a₀ • η₁))
      + s • (OddOrder.Peterfalvi.S06.columnSum h46 k0 - a₀ • η₁) := by
    rw [smul_sub, ← hsum]; abel
  rw [hφeq]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_left _ ⟨hp1span, hp1supp⟩))
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_right _ ⟨hp2span, hp2supp⟩))
  · exact Submodule.smul_mem _ s
      (Submodule.subset_span (Set.mem_union_right _ (Set.mem_singleton _)))

/-- **The certain-type set `𝒯 = certainTypeSet h46 k` is finite.**

Every member is a column character `columnSum h46 χ₂` for some `W₂`-dual
`χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ`, so `𝒯 ⊆ range (columnSum h46)`.  The index type
of `W₂`-duals — linear characters of a *finite* group — is finite
(`SibleyDadeHypothesis.finite_linearCharacters_of_finite`), hence the range, hence `𝒯`.

This is the `hXfin` input of the `(6.8.2)` `ν`-glue `exists_integralCharacterMap_glue_of_orthonormal`
(via the column-sum-to-grid source reduction) and of any finite-enumeration of the column base. -/
theorem certainTypeSet_finite
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (k : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    (OddOrder.Peterfalvi.S06.certainTypeSet h46 k).Finite := by
  haveI : Finite ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :=
    SibleyDadeHypothesis.finite_linearCharacters_of_finite
  refine Set.Finite.subset (Set.finite_range (OddOrder.Peterfalvi.S06.columnSum h46)) ?_
  rintro f ⟨χ₂, -, -, rfl⟩
  exact ⟨χ₂, rfl⟩

/-- **(6.8.2) case-(B), the glue map `ν` (`τ₂`) for the `certainTypeSet ⊔ Y` base union.**

The combined `IntegralCharacterMap (↥L) G` of the case-(B) `(6.8.2)` glue: it agrees with the
certain-type coherent extension `certainTypeExtension h46` on **every** column character
`μ_j = columnSum h46 χ₂`, and with the `Y`-coherent extension `coherentYset.extension` on every
`η ∈ Y`.

Built by `exists_integralCharacterMap_glue_of_orthonormal` from the **grid** source family
`{μ_{ij}}` (`p ↦ (h46.columnFamily p.1).mu p.2`, orthonormal irreducibles — the
`SignedIrreducibleDifferenceFamily.mu` are `IrreducibleCharacter`) and `Y` (orthonormal irreducibles),
which are mutually orthogonal by `inner_columnFamily_mu_Yset_eq_zero` (the source-level `(4.1)`
`X ⊥ Y`).  The column-character agreement is recovered from the grid agreement *by linearity*
(`columnSum = ∑_i μ_{ij}` via `columnSum_def`, `map_sum`), since `columnSum` is itself **not**
orthonormal (norm `|W₁|`) and cannot serve as a glue source directly.

This supplies the `ν`/`hagreeX`/`hagreeY` inputs of `coherentXunionYset_caseB_of_glued` (instantiated
with the column base `X := certainTypeSet h46 k`); the column agreement specialises to the
certain-type members `columnSum h46 χ₂ ∈ 𝒯`. -/
theorem exists_glue_nu_columnSum_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)] :
    ∃ ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G,
      (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ,
        ν (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
          = OddOrder.Peterfalvi.S06.certainTypeExtension h46
              (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)) ∧
      (∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y) := by
  classical
  haveI : Finite ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :=
    SibleyDadeHypothesis.finite_linearCharacters_of_finite
  -- CF-level orthonormality of irreducibles (`⟨φ,ψ⟩ = δ` for irreducible `φ,ψ`).
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
  -- the orthonormal grid source family `{μ_{ij}}`, indexed by `(χ₂, i)`.
  set grid : Set (ClassFunction ↥L ℂ) :=
    Set.range (fun p : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) × Fin (Nat.card h46.W1) =>
      ((h46.columnFamily p.1).mu p.2 : ClassFunction ↥L ℂ)) with hgrid
  have hXfin : grid.Finite := Set.finite_range _
  have hXorth : ∀ x ∈ grid, ∀ x' ∈ grid,
      ClassFunction.inner x x' = if x = x' then (1 : ℂ) else 0 := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact hinner _ _ ((h46.columnFamily p.1).mu p.2).property
      ((h46.columnFamily q.1).mu q.2).property
  have hYorth : ∀ y ∈ hyp.Yset, ∀ y' ∈ hyp.Yset,
      ClassFunction.inner y y' = if y = y' then (1 : ℂ) else 0 :=
    fun y hy y' hy' => hinner _ _ (hyp.isIrreducibleCharacter_of_mem_Yset hy)
      (hyp.isIrreducibleCharacter_of_mem_Yset hy')
  have hXY : ∀ x ∈ grid, ∀ y ∈ hyp.Yset, ClassFunction.inner x y = 0 := by
    rintro _ ⟨p, rfl⟩ y hy
    exact inner_columnFamily_mu_Yset_eq_zero hyp h46 hW1 hy p.1 p.2
  -- glue the two orthonormal source families through the two coherent extensions.
  obtain ⟨ν, hνgrid, hνY⟩ :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthonormal
    hXfin hyp.Yset_finite hXorth hYorth hXY
    (OddOrder.Peterfalvi.S06.certainTypeExtension h46) hyp.coherentYset.extension
  refine ⟨ν, fun χ₂ => ?_, hνY⟩
  -- column agreement by linearity: `ν(∑ μ_{ij}) = ∑ ν μ_{ij} = ∑ certainTypeExtension μ_{ij}`.
  rw [OddOrder.Peterfalvi.S06.columnSum_def]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun i _ => hνgrid _ ⟨(χ₂, i), rfl⟩

/-- **(6.8.2) case-(B), the `certainTypeSet ⊔ Y` base union is coherent** — assembly.

Glues the column base `certainTypeSet h46 k` (coherent via `certainTypeSet_isCoherent_tau_canonical`)
with `Y` (coherent via `coherentYset`) into `IsCoherent hyp.tau (certainTypeSet ∪ Y)` through the §7
diagonal-aware engine `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`.  Every
mechanical engine input is discharged here from established facts:

* `ν`/`hagreeX`/`hagreeY` — the grid-glue map `exists_glue_nu_columnSum_Yset` (its column agreement
  *is* `certainTypeExtension`, which is the canonical coherence extension because `IsCoherent.congrMap`
  preserves `.extension`);
* `hsrc_ortho` — `inner_eq_zero_of_mem_span_of_pairwise_orthogonal` over the column-`Y` orthogonality
  `inner_columnSum_Yset_eq_zero`;
* `hmixed` — `inner_certainTypeExtension_columnSum_coherentYset_extension_eq_zero` (both the image and
  the source inner products vanish);
* `hgen` — `hgen_withDiagonal_certainTypeSet` (the `(6.8.1)` generation, session 45);
* `hDτ` — reduces by `ν`-linearity to the **single** `(6.8.2.3)` obligation `hanchored`.

`hanchored` is the faithful `(6.8.2.3)` anchored-image identity for the reference column `μ_{k0}`:
`(μ_{k0} − a₀·η₁)^τ = ν(μ_{k0}) − a₀·η₁^{τ₁}` (with `ν(μ_{k0}) = certainTypeExtension(μ_{k0})` and
`η₁^{τ₁} = coherentYset.extension η₁`).  It is the certain-type per-constituent decomposition +
pinning content (`columnDecompositionTau` / `per_constituent_Y_eq_smul`), to be discharged separately;
this lemma isolates it as the lone remaining input of the case-(B) base glue. -/
noncomputable def coherentCertainTypeSet_union_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    (hHK : h46.K = H) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {k : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hk : k ≠ 1)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {k0 : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ}
    (hk0mem : OddOrder.Peterfalvi.S06.columnSum h46 k0
      ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k)
    {a₀ : ℕ}
    (ha₀ : (OddOrder.Peterfalvi.S06.columnSum h46 k0 : ClassFunction ↥L ℂ) 1
      = (a₀ : ℂ) * η₁ 1)
    (hanchored : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 k0 - a₀ • η₁)
      = OddOrder.Peterfalvi.S06.certainTypeExtension h46
          (OddOrder.Peterfalvi.S06.columnSum h46 k0)
        - a₀ • hyp.coherentYset.extension η₁) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S06.certainTypeSet h46 k ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  -- `ν` is data (an `IntegralCharacterMap`); extract it via choice (the `∃` cannot be destructured
  -- into the `IsCoherent` data goal), keeping its agreement spec as `hνcol`/`hνY`.
  have hspec := (exists_glue_nu_columnSum_Yset hyp h46 hW1).choose_spec
  set ν := (exists_glue_nu_columnSum_Yset hyp h46 hW1).choose with hνdef
  have hνcol := hspec.1
  have hνY := hspec.2
  -- `hagreeX`: column agreement is `certainTypeExtension = canonical coherence extension`.
  have hagreeX : ∀ x ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k,
      ν x = (hyp.certainTypeSet_isCoherent_tau_canonical h46 hk).extension x := by
    rintro x ⟨χ₂, -, -, rfl⟩
    exact hνcol χ₂
  -- `hsrc_ortho`: column ⊥ `Y` (source level) spread to the spans.
  have hpair : ∀ χ ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k, ∀ η ∈ hyp.Yset,
      ClassFunction.inner χ η = 0 := by
    rintro χ ⟨χ₂, -, -, rfl⟩ η hη
    exact inner_columnSum_Yset_eq_zero hyp h46 hW1 hη χ₂
  -- `hmixed`: both `⟨ν x, ν y⟩` (image side) and `⟨x, y⟩` (source side) vanish.
  have hmixed : ∀ x ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y := by
    rintro x ⟨χ₂, -, -, rfl⟩ y hy
    rw [hνcol χ₂, hνY y hy,
      inner_certainTypeExtension_columnSum_coherentYset_extension_eq_zero hyp h46 hHK hy χ₂,
      inner_columnSum_Yset_eq_zero hyp h46 hW1 hy χ₂]
  -- `hDτ`: `ν`-linearity reduces the cross-diagonal image to `hanchored`.
  have hDτ : ∀ d ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 k0 - a₀ • η₁} :
        Set (ClassFunction ↥L ℂ)), ν d = hyp.tau d := by
    intro d hd
    rw [Set.mem_singleton_iff] at hd
    subst hd
    rw [hanchored, map_sub, map_nsmul, hνcol k0, hνY η₁ hη₁]
  exact OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal
    (hyp.certainTypeSet_isCoherent_tau_canonical h46 hk) hyp.coherentYset
    ν hagreeX hνY
    (inner_eq_zero_of_mem_span_of_pairwise_orthogonal hpair) hmixed
    {OddOrder.Peterfalvi.S06.columnSum h46 k0 - a₀ • η₁} hDτ
    (hgen_withDiagonal_certainTypeSet hyp h46 hHK hk0mem hη₁ ha₀)

end OddOrder.Peterfalvi.S08
