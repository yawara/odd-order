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

omit [Invertible (Nat.card ↥H : ℂ)] in
/-- **Degree ratio of a `certainTypeSet`-span element against any reference column member.**

Every `ψ ∈ ℤ[certainTypeSet h46 k]` has degree an integer multiple of `μ_{j₀}(1)` for any
anchor member `μ_{j₀} = columnSum h46 k0 ∈ certainTypeSet h46 k`.  The single-member case is
*ratio 1* — the *defining* property of `certainTypeSet h46 k`: every member
`μ_{χ₂} = columnSum χ₂` shares the reference degree `∑_i μ_{ik}(1)` (`columnSum_apply_one`),
and so does the anchor member `μ_{j₀}`, so `μ_{χ₂}(1) = μ_{j₀}(1)`.  Span induction lifts to
integer combinations.

This is the column analogue of the Frobenius `hsX` step of `hgen_withDiagonal_of_frobenius`, with
the
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
    simp only [sharpImage, Set.mem_sdiff, Set.mem_singleton_iff] at hmem
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

omit [Invertible (Nat.card ↥H : ℂ)] in
/-- **The certain-type set `𝒯 = certainTypeSet h46 k` is finite.**

Every member is a column character `columnSum h46 χ₂` for some `W₂`-dual
`χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ`, so `𝒯 ⊆ range (columnSum h46)`.  The index type
of `W₂`-duals — linear characters of a *finite* group — is finite
(`SibleyDadeHypothesis.finite_linearCharacters_of_finite`), hence the range, hence `𝒯`.

This is the `hXfin` input of the `(6.8.2)` `ν`-glue
`exists_integralCharacterMap_glue_of_orthonormal`
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

end OddOrder.Peterfalvi.S08
