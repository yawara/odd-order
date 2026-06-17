/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S08_CaseBAssembly
import OddOrder.Peterfalvi.S08_CaseBHortho
import OddOrder.Peterfalvi.S08_CoherenceWeighted

/-!
# Peterfalvi §6.8.2 — case-(B) conjugate-pair cover of the `X`-set

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §6, (6.8.2).

This leaf produces the **case-(B) conjugate-pair cover** of the `X`-set `hyp.Xset W₂` with base the
certain-type column set `certainTypeSet h46 k`, in the four-conjunct form
(`hpair0`/`hpair1`/`hpairs`/`hcover`) consumed by the norm-weighted X-chain fold
`xChainCoherentW` (`S08_CoherenceWeighted`).

The cover is assembled from the Γ-generic engine `exists_conjugatePairCover_general`
(`S08_CoherenceCorePart1`), which — unlike `exists_conjugatePairCover` — does **not** require the
ambient `X`-irreducibility hypothesis `hX : ∀ φ ∈ X, IsIrreducible`.  The certain-type set is the
reducible column base on which case (B) lives: its members `columnSum h46 χ₂` are genuinely
reducible, so the unweighted chain cannot be used.

The four inputs of `exists_conjugatePairCover_general` for case (B):

* **`hXfin`** = `hyp.Xset_finite` (unconditional);
* **`hXconj`** = `hyp.Xset_closedUnderConjugate_unconditional` (unconditional);
* **`hXreal`** = `Xset_hasNoRealCharacters_caseB` (proved here): an `X`-member is either a
  certain-type column (whose conjugate is the *inverse* column `columnSum χ₂⁻¹ ≠ columnSum χ₂`,
  distinct by the column Gram matrix `columnFamily_mu_sum_inner`) or an irreducible
  `Ind^L_H θ`, non-real because `L` has odd order (`caseB_irr_nonreal`);
* **`hS₀conj`** = `certainTypeSet_closedUnderConjugate` (proved here): the conjugate of a column is
  the inverse column, still a member (equal degree by `columnSum_inv_apply_one`).

The pair members `(pair i).1` are the **non-`S₀`** `X`-members.  These must be irreducible to build
`χs : ℕ → IrreducibleCharacter ↥L` for `xChainCoherentW`.  A non-`S₀` `X`-member is, by
`caseB_S_member_column_or_irreducible`, either a nontrivial column or irreducible; but a column of a
degree class *other* than `k` is reducible and is *not* in `certainTypeSet h46 k`, so the per-member
irreducibility of the non-`S₀` part is supplied as the explicit hypothesis `hnonS₀_irr` (it holds in
the regime where `certainTypeSet h46 k` captures every reducible `X`-member, e.g. when the fold is
applied to the single degree class `k`).  See REPORT note (d).
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory
open scoped Classical

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **The certain-type column set is closed under conjugation** (`hS₀conj` for the case-(B) cover).
A member of `certainTypeSet h46 k` is a column `columnSum h46 χ₂` (`χ₂ ≠ 1`, degree-matched); its
conjugate is the *inverse* column `columnSum h46 χ₂⁻¹` (`columnSum_conj_eq`), which is again a member
of the set: `χ₂⁻¹ ≠ 1` (since `χ₂ ≠ 1`), and the degree condition is preserved because the inverse
column has the same degree as the original (`columnSum_inv_apply_one`). -/
theorem certainTypeSet_closedUnderConjugate
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (k : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate
      (OddOrder.Peterfalvi.S06.certainTypeSet h46 k) := by
  classical
  intro f hf
  obtain ⟨χ₂, hχ₂, hdeg, rfl⟩ := hf
  refine ⟨χ₂⁻¹, ?_, ?_, ?_⟩
  · simpa using hχ₂
  · -- the inverse column has the original column's degree (`columnSum_inv_apply_one`), so still `= k`.
    rw [OddOrder.Peterfalvi.S06.columnSum_inv_apply_one, hdeg]
  · exact OddOrder.Peterfalvi.S06.columnSum_conj_eq h46 χ₂

/-- **The case-(B) `X`-set contains no real characters** (`hXreal` for the case-(B) cover).  By the
`S`-level cover (`caseB_induce_column_or_irreducible`) each `X(W₂)`-member is either a certain-type
column or an irreducible `Ind^L_H θ`:

* **column** `χ = columnSum h46 χ₂` (`χ₂ ≠ 1`): its conjugate is the inverse column
  `columnSum h46 χ₂⁻¹` (`columnSum_conj_eq`) with `χ₂⁻¹ ≠ χ₂` (`column_inv_ne_self`), so the
  conjugate differs by the column Gram matrix (`⟨χ, χ⟩ = w₁ ≠ 0 = ⟨χ, χ̄⟩`,
  `columnFamily_mu_sum_inner`, `w₁ = Nat.card W₁ ≠ 0`);
* **irreducible** `Ind^L_H θ`: non-real because `L` has odd order (`caseB_irr_nonreal`). -/
theorem Xset_hasNoRealCharacters_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)] :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset h46.W2) := by
  classical
  intro χ hχX
  -- An `X(W₂)`-member is an induced character `Ind^L_H θ` with `θ ≠ 1`.
  have hχS : χ ∈ hyp.S := hyp.Xset_subset_S hχX
  rw [hyp.S_eq, Set.mem_setOf_eq] at hχS
  obtain ⟨θ, hθne, rfl⟩ := hχS
  have hθne' : (θ : ClassFunction ↥H ℂ) ≠ trivialClassFunction ↥H := fun heq =>
    hθne (Subtype.ext (heq.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter).symm))
  rcases caseB_induce_column_or_irreducible h46 hHK hθne' with ⟨χ₂, hχ₂, hcol⟩ | hirr
  · -- column branch: distinct from its inverse column by the Gram matrix.
    intro hreal
    rw [ClassFunction.IsReal, ← hcol, OddOrder.Peterfalvi.S06.columnSum_conj_eq] at hreal
    -- `columnSum χ₂⁻¹ = columnSum χ₂` would force `w₁ = 0` via the Gram entries.
    have hgram_self := OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner h46 χ₂ χ₂
    have hgram_cross := OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner h46 χ₂ χ₂⁻¹
    rw [if_pos rfl] at hgram_self
    rw [if_neg (OddOrder.Peterfalvi.S06.column_inv_ne_self h46 hχ₂).symm] at hgram_cross
    -- `⟨columnSum χ₂, columnSum χ₂⟩ = ⟨columnSum χ₂, columnSum χ₂⁻¹⟩`, i.e. `w₁ = 0`.
    simp only [← OddOrder.Peterfalvi.S06.columnSum_def] at hgram_self hgram_cross
    rw [hreal] at hgram_cross
    have hcontra : (Nat.card h46.W1 : ℂ) = 0 := hgram_self.symm.trans hgram_cross
    have hne : Nat.card h46.W1 ≠ 0 := NeZero.ne _
    exact hne (by exact_mod_cast hcontra)
  · -- irreducible branch: non-real by odd order.
    exact caseB_irr_nonreal hyp hirr

/-- **Peterfalvi (6.8.2) case-(B) conjugate-pair cover of `X(W₂)`** with base the certain-type column
set `certainTypeSet h46 k`.

Produces the four conjuncts `hpair0`/`hpair1`/`hpairs`/`hcover` of the norm-weighted X-chain fold
`xChainCoherentW` (with `S₀ = certainTypeSet h46 k`, `X = hyp.Xset h46.W2`), packaged with an
irreducible-character sequence `χs` witnessing the pair members.  Assembled from the Γ-generic engine
`exists_conjugatePairCover_general` (no `X`-irreducibility hypothesis needed); the pair members are
the **non-`S₀`** `X`-members.

Explicit hypotheses beyond the ambient instances:

* `hbase : certainTypeSet h46 k ⊆ hyp.Xset h46.W2` — the certain-type columns lie in
  `X(W₂) = S − S(W₂)`; discharging it requires the column-`= Ind^L_H θ` structure
  (`columnSum_mem_S`) and the `S(W₂)`-membership characterisation, deferred to the caller.
* `hnonS₀_irr : ∀ χ ∈ X(W₂), χ ∉ certainTypeSet h46 k → IsIrreducibleCharacter χ` — the non-`S₀`
  `X`-members are irreducible (so they can be paired).  This is genuinely needed: a column of a
  degree class other than `k` is reducible and not in `certainTypeSet h46 k`, so it is *not*
  irreducible; the hypothesis pins the regime where `certainTypeSet h46 k` captures every reducible
  `X`-member. -/
theorem caseB_Xset_conjugatePairCover
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {k : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ}
    (hbase : OddOrder.Peterfalvi.S06.certainTypeSet h46 k ⊆ hyp.Xset h46.W2)
    (hnonS₀_irr : ∀ χ ∈ hyp.Xset h46.W2,
      χ ∉ OddOrder.Peterfalvi.S06.certainTypeSet h46 k → IsIrreducibleCharacter χ) :
    ∃ (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
        (χs : ℕ → IrreducibleCharacter ↥L),
        (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) ∧
        (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) ∧
        (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset h46.W2) ∧
        (∀ χ ∈ hyp.Xset h46.W2, χ ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k ∨
          ∃ j, j < N ∧ χ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j) := by
  classical
  -- the four inputs of `exists_conjugatePairCover_general`.
  have hXfin : (hyp.Xset h46.W2).Finite := hyp.Xset_finite h46.W2
  have hXconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset h46.W2) :=
    hyp.Xset_closedUnderConjugate_unconditional h46.W2
  have hXreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset h46.W2) :=
    Xset_hasNoRealCharacters_caseB hyp h46 hHK
  have hS₀conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate
      (OddOrder.Peterfalvi.S06.certainTypeSet h46 k) :=
    certainTypeSet_closedUnderConjugate h46 k
  obtain ⟨e, pair, N, hsurj, hpairs, hcoverIdx, hpair1Raw, hdisj, _hmono⟩ :=
    exists_conjugatePairCover_general (X := hyp.Xset h46.W2)
      (S₀ := OddOrder.Peterfalvi.S06.certainTypeSet h46 k) hXfin hXconj hXreal hS₀conj
  -- each pair member `(pair i).1` (i < N) is irreducible: it is a non-`S₀` `X`-member.
  -- `(pair i).1 ∈ X` from `hpairs`; `(pair i).1 ∉ S₀` from the `Disjoint` conjunct (since `S₀`
  -- sits inside `pairUnion S₀ pair i`).
  have hpairIrr : ∀ i, i < N → IsIrreducibleCharacter (pair i).1 := by
    intro i hi
    have hmemX : (pair i).1 ∈ hyp.Xset h46.W2 := by
      apply hpairs i hi
      simp [OddOrder.Peterfalvi.S07.pairSet]
    have hnotS₀ : (pair i).1 ∉ OddOrder.Peterfalvi.S06.certainTypeSet h46 k := by
      intro hS₀
      have hmem : (pair i).1 ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
        simp [OddOrder.Peterfalvi.S07.pairSet]
      have hu : (pair i).1 ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L)
          (OddOrder.Peterfalvi.S06.certainTypeSet h46 k) pair i := by
        rw [OddOrder.Peterfalvi.S07.mem_pairUnion]; exact Or.inl hS₀
      exact Set.disjoint_left.mp (hdisj i hi) hmem hu
    exact hnonS₀_irr (pair i).1 hmemX hnotS₀
  -- assemble the irreducible-character sequence; junk default for indices `≥ N`.
  let χ0 : IrreducibleCharacter ↥L := trivialIrreducibleCharacter ↥L
  let χs : ℕ → IrreducibleCharacter ↥L := fun i =>
    if hi : i < N then ⟨(pair i).1, hpairIrr i hi⟩ else χ0
  refine ⟨pair, N, χs, ?_, ?_, ?_, ?_⟩
  · -- `hpair0`: `(pair i).1 = (χs i : ClassFunction)`.
    intro i hi; simp [χs, hi]
  · -- `hpair1`: `(pair i).2 = (χs i : ClassFunction).conj`.
    intro i hi
    rw [hpair1Raw i hi]; simp [χs, hi]
  · -- `hpairs`: each pair set is inside `X`.
    exact hpairs
  · -- `hcover`: every `X`-member is in `S₀` or some pair set.
    intro χ hχ
    obtain ⟨i, hi⟩ := hsurj χ hχ
    have hci := hcoverIdx i
    rw [hi] at hci
    exact hci

/-- **General finite enumeration of a set of class functions** (the case-(B) analogue of
`exists_finEnum_irreducible`, dropping the irreducibility requirement).

For a finite set `S : Set (ClassFunction Γ ℂ)` produces an injective `Fin k`-indexed family whose
range is `S` — **without** requiring its members to be irreducible.  This is the enumeration
primitive for the case-(B) norm-weighted member family, whose coherent set `X ∪ Y` contains the
*reducible* certain-type columns `μ_j = columnSum h46 χ₂` (so the `IrreducibleCharacter`-typed
`exists_finEnum_irreducible` does not apply).  Pure formalization (no character theory): the `Fin`
enumeration of a `Fintype` via `Fintype.equivFin`. -/
theorem exists_finEnum_general {Γ : Type*} [Group Γ] {S : Set (ClassFunction Γ ℂ)}
    (hSfin : S.Finite) :
    ∃ (k : ℕ) (f : Fin k → ClassFunction Γ ℂ),
      Function.Injective f ∧ Set.range f = S := by
  classical
  haveI : Fintype S := hSfin.fintype
  refine ⟨Fintype.card S, fun j => ((Fintype.equivFin S).symm j : ClassFunction Γ ℂ), ?_, ?_⟩
  · intro i j hij
    exact (Fintype.equivFin S).symm.injective (Subtype.ext hij)
  · ext φ
    constructor
    · rintro ⟨j, rfl⟩
      exact ((Fintype.equivFin S).symm j).2
    · intro hφ
      exact ⟨Fintype.equivFin S ⟨φ, hφ⟩, by simp⟩

/-- **Peterfalvi (6.8.2) case-(B) per-member `(5.4)` decomposition** (brick 1 of the norm-weighted
member-family bound).

For a member `x` of a conjugation-closed coherent set `S₁ ⊆ S` (the `X ∪ Y` coherent seed of case
(B)), produces the `ψ = 0` decomposition `CharacterPsiDecomposition hyp.tau x 0` — the `Dmem` datum
of the norm-weighted (5.6) member-family bound `coherentDegreeSqNormBound_of_not_coherentW`.

Dispatches on the `S`-member dichotomy `caseB_induce_column_or_irreducible` (`x = Ind^L_H θ`):

* **reducible certain-type column** `x = columnSum h46 χ₂` (`χ₂ ≠ 1`): the reducible `R(μ_j)`
  decomposition `certainTypeMemberDecomposition`, with the conjugate-column degree equality
  (`columnSum_inv_apply_one`), the map agreement `caseB_column_mapagree` (`hyp.tau` equals the
  certain-type Dade map on `μ_j − μ̄_j`), and the `H^#`-supported difference
  (`columnDiff_support_subset`);
* **irreducible** `x = Ind^L_H θ`: the irreducible `R(χ)` decomposition
  `memberExtensionDecomposition`, with the odd-order non-realness `caseB_irr_nonreal`, the conjugate
  difference support `caseB_irr_conj_diff_support`, and the self-conjugate orthogonality
  `caseB_irr_conj_inner`.

In both branches the auxiliary isometry `τ₁` is the running coherence extension
`ν = hS₁coh.extension` (so the weighted engine's `htau1Dmem` field holds by `rfl`), and the image
family `R(·)` is orthonormal in `ZIrr G`. -/
noncomputable def caseB_member_psiDecomposition
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    {x : ClassFunction ↥L ℂ} (hxS₁ : x ∈ S₁)
    (hνZ : hS₁coh.extension x ∈ ZIrr G) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau x 0 := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hxS : x ∈ hyp.S := hS₁sub hxS₁
  -- The goal is `Type`-valued (`CharacterPsiDecomposition` carries data), so the column index `χ₂`
  -- must be extracted via `Exists.choose` rather than `obtain`/`rcases` (a `Prop`-valued `∃`/`∨`
  -- cannot be eliminated into a `Type`).  The inducing source `θ` is recovered only inside the
  -- `Prop`-valued sub-`have`s of the irreducible branch.
  by_cases hcolumn : ∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = x
  · -- reducible certain-type column branch
    set χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ := hcolumn.choose with hχ₂def
    have hχ₂ : χ₂ ≠ 1 := hcolumn.choose_spec.1
    have hcol : OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = x := hcolumn.choose_spec.2
    have hμ_S1 : OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∈ S₁ := by rw [hcol]; exact hxS₁
    have hμbar_S1 : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj ∈ S₁ :=
      hS₁conj.conj_mem hμ_S1
    have hνZ' : hS₁coh.extension (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) ∈ ZIrr G := by
      rw [hcol]; exact hνZ
    have hsupp : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq]
      exact OddOrder.Peterfalvi.S06.columnDiff_support_subset h46 hχ₂ (inv_ne_one.mpr hχ₂)
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm
    -- transport the `columnSum χ₂`-decomposition to `x` along `hcol` (term-level `▸`, no dependency
    -- cycle, unlike `rw [← hcol]` which would try to abstract `x` under the `x`-dependent `χ₂`).
    exact hcol ▸ OddOrder.Peterfalvi.S06.certainTypeMemberDecomposition h46 hχ₂
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm
      (caseB_column_mapagree hyp h46 hχ₂) hS₁coh hμ_S1 hμbar_S1 hνZ'
      (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
        ⟨Submodule.sub_mem _ (Submodule.subset_span hμ_S1) (Submodule.subset_span hμbar_S1),
          hsupp⟩)
  · -- irreducible branch (`x` is not a nontrivial column, so the `S`-member dichotomy forces it)
    have hirrx : IsIrreducibleCharacter x :=
      (caseB_S_member_column_or_irreducible hyp h46 hHK hxS).resolve_left hcolumn
    have hreal : ¬ ClassFunction.IsReal x := by
      have h := hxS; rw [hyp.S_eq, Set.mem_setOf_eq] at h
      obtain ⟨θ, hθne, hxeq⟩ := h
      rw [hxeq]; exact caseB_irr_nonreal hyp (hxeq ▸ hirrx)
    have hdiffsupp : (x.conj - x).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      have h := hxS; rw [hyp.S_eq, Set.mem_setOf_eq] at h
      obtain ⟨θ, hθne, hxeq⟩ := h
      rw [hxeq]; exact caseB_irr_conj_diff_support hyp θ
    have hχχbar : ClassFunction.inner x x.conj = 0 := by
      have h := hxS; rw [hyp.S_eq, Set.mem_setOf_eq] at h
      obtain ⟨θ, hθne, hxeq⟩ := h
      rw [hxeq]; exact caseB_irr_conj_inner hyp (hxeq ▸ hirrx)
    exact memberExtensionDecomposition hyp.dade hyp.hconj hS₁coh ⟨x, hirrx⟩
      hreal hdiffsupp hxS₁ (hS₁conj.conj_mem hxS₁) hνZ hχχbar

/-- **Peterfalvi (6.8.2) case-(B) per-member `(5.4)` decomposition bundled with its (5.2.e)
cross-orthogonality and `τ₁`-agreement** (the coupled brick-1 datum for the norm-weighted member
family).

For a member `x` of a conjugation-closed coherent set `S₁ ⊆ S` and a fixed **break character**
`χ : Irr L` (the irreducible pair `{χ, χ̄}` being adjoined), produces the per-member `Dmem`
together with the two engine fields that must be *coupled* to it:

* `hortho` — the (5.2.e) cross-family orthogonality `R(x) ⊥ R(χ)`
  (`(Dmem).imageFamily.Orthogonal (dadeOrthonormalCharacterImageFamilyOfDiff … χ …)`), and
* `htau1` — the running-extension agreement `(Dmem).tau1 x = ν x` (`ν = hS₁coh.extension`).

This is the brick-1 dispatcher `caseB_member_psiDecomposition` enriched with the two
χ-dependent fields the norm-weighted engine `coherentDegreeSqNormBound_of_not_coherentW` demands.
Crucially the three outputs are produced in **one** transparent `by_cases` so they stay coupled:
proving `hortho`/`htau1` about the *opaque* black-box output of `caseB_member_psiDecomposition`
fails, because that output threads through the term-level transport `hcol ▸ …` (column branch),
which blocks the `rfl` shape of `htau1` and the imageSet identity `hortho` needs.

Dispatches on the `S`-member dichotomy `caseB_induce_column_or_irreducible`:

* **reducible certain-type column** `x = columnSum h46 χ₂` (`χ₂ ≠ 1`): `Dmem` is the
  reducible `R(μ_j)` decomposition `certainTypeMemberDecomposition`; `hortho` is the V-vanishing
  cross-orthogonality `certainTypeR_imageSet_orthogonal_dadeOfDiff` (needs only `χ`'s realness and
  `H^#`-support, *not* the member⊥break facts); `htau1` is `rfl` (`ofProjection`'s `τ₁` is `ν`);
* **irreducible** `x = Ind^L_H θ`: `Dmem` is `memberExtensionDecomposition`; `hortho` is the Dade
  difference-family orthogonality `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`, which
  consumes the member⊥break facts `hxχ`/`hxχbar`/`hxbarχ`/`hxbarχbar` (supplied by the caller
  from the break pair's orthogonality to `S₁`); `htau1` is `rfl`. -/
noncomputable def caseB_member_orthoDatum
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    {x : ClassFunction ↥L ℂ} (hxS₁ : x ∈ S₁)
    (hνZ : hS₁coh.extension x ∈ ZIrr G)
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hxχ : ClassFunction.inner x (χ : ClassFunction ↥L ℂ) = 0)
    (hxχbar : ClassFunction.inner x (χ : ClassFunction ↥L ℂ).conj = 0)
    (hxbarχ : ClassFunction.inner x.conj (χ : ClassFunction ↥L ℂ) = 0)
    (hxbarχbar : ClassFunction.inner x.conj (χ : ClassFunction ↥L ℂ).conj = 0) :
    { D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau x 0 //
      D.imageFamily.Orthogonal (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          hyp.dade hyp.hconj χ hrealχ hdiffsuppχ) ∧
        D.tau1 x = hS₁coh.extension x } := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hxS : x ∈ hyp.S := hS₁sub hxS₁
  by_cases hcolumn : ∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = x
  · -- reducible certain-type column branch
    set χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ := hcolumn.choose with hχ₂def
    have hχ₂ : χ₂ ≠ 1 := hcolumn.choose_spec.1
    have hcol : OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = x := hcolumn.choose_spec.2
    have hμ_S1 : OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∈ S₁ := by rw [hcol]; exact hxS₁
    have hμbar_S1 : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj ∈ S₁ :=
      hS₁conj.conj_mem hμ_S1
    have hνZ' : hS₁coh.extension (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) ∈ ZIrr G := by
      rw [hcol]; exact hνZ
    have hsupp : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq]
      exact OddOrder.Peterfalvi.S06.columnDiff_support_subset h46 hχ₂ (inv_ne_one.mpr hχ₂)
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm
    -- the coupled datum at `columnSum χ₂`, transported to `x` along `hcol`.
    exact hcol ▸ (⟨OddOrder.Peterfalvi.S06.certainTypeMemberDecomposition h46 hχ₂
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm
        (caseB_column_mapagree hyp h46 hχ₂) hS₁coh hμ_S1 hμbar_S1 hνZ'
        (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
          ⟨Submodule.sub_mem _ (Submodule.subset_span hμ_S1) (Submodule.subset_span hμbar_S1),
            hsupp⟩),
      certainTypeR_imageSet_orthogonal_dadeOfDiff hyp h46 hHK hχ₂
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm χ hrealχ hdiffsuppχ,
      rfl⟩ :
      { D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
          (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) 0 //
        D.imageFamily.Orthogonal (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
            hyp.dade hyp.hconj χ hrealχ hdiffsuppχ) ∧
          D.tau1 (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
            = hS₁coh.extension (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) })
  · -- irreducible branch
    have hirrx : IsIrreducibleCharacter x :=
      (caseB_S_member_column_or_irreducible hyp h46 hHK hxS).resolve_left hcolumn
    have hreal : ¬ ClassFunction.IsReal x := by
      have h := hxS; rw [hyp.S_eq, Set.mem_setOf_eq] at h
      obtain ⟨θ, hθne, hxeq⟩ := h
      rw [hxeq]; exact caseB_irr_nonreal hyp (hxeq ▸ hirrx)
    have hdiffsupp : (x.conj - x).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      have h := hxS; rw [hyp.S_eq, Set.mem_setOf_eq] at h
      obtain ⟨θ, hθne, hxeq⟩ := h
      rw [hxeq]; exact caseB_irr_conj_diff_support hyp θ
    have hχχbar : ClassFunction.inner x x.conj = 0 := by
      have h := hxS; rw [hyp.S_eq, Set.mem_setOf_eq] at h
      obtain ⟨θ, hθne, hxeq⟩ := h
      rw [hxeq]; exact caseB_irr_conj_inner hyp (hxeq ▸ hirrx)
    refine ⟨memberExtensionDecomposition hyp.dade hyp.hconj hS₁coh ⟨x, hirrx⟩
      hreal hdiffsupp hxS₁ (hS₁conj.conj_mem hxS₁) hνZ hχχbar, ?_, rfl⟩
    -- `(Dmem).imageFamily = R(x)` (the Dade difference family), `⊥ R(χ)` by the (5.2.e) lemma.
    exact dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal hyp.dade hyp.hconj
      hreal hdiffsupp hrealχ hdiffsuppχ hxχ hxχbar hxbarχ hxbarχbar

/-- **Peterfalvi (6.8.2) case-(B): the `X(W₂) ∪ Y` coherent set is pairwise orthogonal.**

For distinct members `x ≠ y` of `X(W₂) ∪ Y` (the case-(B) `X ∪ Y` coherent seed), `⟨x, y⟩ = 0`.
This is the off-diagonal of the weighted Gram matrix `hmemortho` that the norm-weighted (5.6) engine
consumes — the genuinely new structural fact case (B) needs, because the members are no longer all
irreducible: `X(W₂)` contains the reducible certain-type columns `columnSum h46 χ₂`.

The four membership cases (each `X`-member splits, by `caseB_S_member_column_or_irreducible`, into a
nontrivial column or an irreducible):

* **column vs column** — distinct columns (`χ₂ ≠ χ₂'`, forced by `x ≠ y`) are orthogonal by
  `inner_columnSum_cross_eq_zero` (Peterfalvi (4.1) grid cross-orthogonality);
* **column vs irreducible** / **irreducible vs column** — a column `columnSum h46 χ₂` and an
  irreducible `Ind^L_H θ` are orthogonal by `caseB_inner_irr_columnSum_eq_zero` (the degree-`mod |W₁|`
  argument: grid degrees are `≡ ±1`, induced degrees `≡ 0`), one order via conjugate symmetry;
* **irreducible vs irreducible** — distinct irreducibles are orthogonal (`irreducibleCharacter_inner_
  eq_ite`);
* **`X` vs `Y`** / **`Y` vs `X`** — `caseB_Xset_orthogonal_Yset` (one order via conjugate symmetry);
* **`Y` vs `Y`** — distinct irreducible `Y`-members (`isIrreducibleCharacter_of_mem_Yset`). -/
theorem caseB_Sunion_pairwise_orthogonal
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {W2 : Subgroup ↥L} (hW2comm : W2 ≤ ⁅H, H⁆) :
    ∀ x ∈ hyp.Xset W2 ∪ hyp.Yset, ∀ y ∈ hyp.Xset W2 ∪ hyp.Yset, x ≠ y →
      ClassFunction.inner x y = 0 := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  -- helper: an irreducible `S`-member is orthogonal to every certain-type column.
  have hirr_col : ∀ z, IsIrreducibleCharacter z → z ∈ hyp.S →
      ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ,
      ClassFunction.inner z (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) = 0 := by
    intro z hzirr hzS χ₂
    rw [hyp.S_eq, Set.mem_setOf_eq] at hzS
    obtain ⟨θ, hθne, rfl⟩ := hzS
    exact caseB_inner_irr_columnSum_eq_zero hyp h46 hW1 hzirr χ₂
  intro x hx y hy hxy
  rcases hx with hxX | hxY
  · rcases hy with hyX | hyY
    · -- both in `X(W₂)`
      rcases caseB_S_member_column_or_irreducible hyp h46 hHK (hyp.Xset_subset_S hxX) with
        ⟨χ₂, hχ₂, hcolx⟩ | hirrx
      · rcases caseB_S_member_column_or_irreducible hyp h46 hHK (hyp.Xset_subset_S hyX) with
          ⟨χ₂', hχ₂', hcoly⟩ | hirry
        · -- column vs column
          have hne : χ₂ ≠ χ₂' := fun h => hxy (by subst h; exact hcolx.symm.trans hcoly)
          exact hcolx ▸ hcoly ▸ inner_columnSum_cross_eq_zero h46 hne
        · -- column vs irreducible (conjugate symmetry of irreducible vs column)
          refine hcolx ▸ ?_
          rw [inner_conj_symm y (OddOrder.Peterfalvi.S06.columnSum h46 χ₂),
            hirr_col y hirry (hyp.Xset_subset_S hyX) χ₂, star_zero]
      · rcases caseB_S_member_column_or_irreducible hyp h46 hHK (hyp.Xset_subset_S hyX) with
          ⟨χ₂', hχ₂', hcoly⟩ | hirry
        · -- irreducible vs column
          exact hcoly ▸ hirr_col x hirrx (hyp.Xset_subset_S hxX) χ₂'
        · -- irreducible vs irreducible
          have h := irreducibleCharacter_inner_eq_ite
            (⟨x, hirrx⟩ : IrreducibleCharacter ↥L) ⟨y, hirry⟩
          rwa [if_neg (fun he => hxy (congrArg Subtype.val he))] at h
    · -- `X(W₂)` vs `Y`
      exact caseB_Xset_orthogonal_Yset hyp h46 hHK hW1 hW2comm x hxX y hyY
  · rcases hy with hyX | hyY
    · -- `Y` vs `X(W₂)` (conjugate symmetry)
      rw [inner_conj_symm y x, caseB_Xset_orthogonal_Yset hyp h46 hHK hW1 hW2comm y hyX x hxY,
        star_zero]
    · -- both in `Y`: distinct irreducibles
      have h := irreducibleCharacter_inner_eq_ite
        (⟨x, hyp.isIrreducibleCharacter_of_mem_Yset hxY⟩ : IrreducibleCharacter ↥L)
        ⟨y, hyp.isIrreducibleCharacter_of_mem_Yset hyY⟩
      rwa [if_neg (fun he => hxy (congrArg Subtype.val he))] at h

/-- **Peterfalvi (6.8.2) case-(B) norm-weighted member-family enumerator** (brick 2): the
ψ-independent data of the norm-weighted (5.6) member family for the `X(W₂) ∪ Y` coherent seed.

Enumerates `S₁ = X(W₂) ∪ Y` (finite, by `exists_finEnum_general` — *not*
`exists_finEnum_irreducible`, since case (B) members include the reducible certain-type columns) as
an injective `Fin k`-family `χmem : Fin k → ClassFunction ↥L ℂ`, together with:

* the per-member squared norms `mc j = (⟨χmem j, χmem j⟩).re`, all positive (`|W₁|` for the columns,
  `1` for the irreducibles);
* the **weighted Gram identity** `⟨χmem i, χmem j⟩ = if i = j then (mc i : ℂ) else 0` — diagonal the
  real squared norm (`inner_self_eq_realCast`), off-diagonal `0` by the pairwise orthogonality
  `caseB_Sunion_pairwise_orthogonal`.

This is exactly the `χmem`/`mc`/`hmempos`/`hmemortho` block the engine
`coherentDegreeSqNormBound_of_not_coherentW` consumes; the χ-dependent per-member data
(`Dmem`/`hortho_mem`/`htau1Dmem`, supplied by `caseB_member_orthoDatum`) and the degree data are
layered on in the (6.8.3) bound (brick 3). -/
theorem exists_sMemberOrthogonalFamilyW
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {W2 : Subgroup ↥L} (hW2comm : W2 ≤ ⁅H, H⁆) :
    ∃ (k : ℕ) (χmem : Fin k → ClassFunction ↥L ℂ) (mc : Fin k → ℝ),
      Function.Injective χmem ∧
      Set.range χmem = hyp.Xset W2 ∪ hyp.Yset ∧
      (∀ j, χmem j ∈ hyp.Xset W2 ∪ hyp.Yset) ∧
      (∀ j, 0 < mc j) ∧
      (∀ i j, ClassFunction.inner (χmem i) (χmem j) = if i = j then (mc i : ℂ) else 0) := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hfin : (hyp.Xset W2 ∪ hyp.Yset).Finite := (hyp.Xset_finite W2).union hyp.Yset_finite
  obtain ⟨k, χmem, hinj, hrange⟩ := exists_finEnum_general hfin
  have hmemS1 : ∀ j, χmem j ∈ hyp.Xset W2 ∪ hyp.Yset := fun j => hrange ▸ Set.mem_range_self j
  refine ⟨k, χmem, fun j => (ClassFunction.inner (χmem j) (χmem j)).re,
    hinj, hrange, hmemS1, ?_, ?_⟩
  · -- `mc j > 0`: column members have `‖μ_j‖² = |W₁|`, irreducibles have `‖χ‖² = 1`.
    intro j
    show (0 : ℝ) < (ClassFunction.inner (χmem j) (χmem j)).re
    rcases hmemS1 j with hX | hY
    · rcases caseB_S_member_column_or_irreducible hyp h46 hHK (hyp.Xset_subset_S hX) with
        ⟨χ₂, hχ₂, hcol⟩ | hirr
      · have hval := OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner h46 χ₂ χ₂
        rw [if_pos rfl] at hval
        simp only [← OddOrder.Peterfalvi.S06.columnSum_def] at hval
        rw [hcol] at hval
        rw [hval, Complex.natCast_re]
        exact_mod_cast Nat.card_pos
      · have hval : ClassFunction.inner (χmem j) (χmem j) = 1 := by
          have h := irreducibleCharacter_inner_eq_ite
            (⟨χmem j, hirr⟩ : IrreducibleCharacter ↥L) ⟨χmem j, hirr⟩
          rwa [if_pos rfl] at h
        rw [hval]; norm_num
    · have hirr := hyp.isIrreducibleCharacter_of_mem_Yset hY
      have hval : ClassFunction.inner (χmem j) (χmem j) = 1 := by
        have h := irreducibleCharacter_inner_eq_ite
          (⟨χmem j, hirr⟩ : IrreducibleCharacter ↥L) ⟨χmem j, hirr⟩
        rwa [if_pos rfl] at h
      rw [hval]; norm_num
  · -- weighted Gram: diagonal the real squared norm, off-diagonal `0`.
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      show ClassFunction.inner (χmem i) (χmem i)
        = (((ClassFunction.inner (χmem i) (χmem i)).re : ℝ) : ℂ)
      rw [inner_self_eq_realCast (χmem i), Complex.ofReal_re]
    · rw [if_neg hij]
      exact caseB_Sunion_pairwise_orthogonal hyp h46 hHK hW1 hW2comm
        (χmem i) (hmemS1 i) (χmem j) (hmemS1 j) (fun h => hij (hinj h))

end OddOrder.Peterfalvi.S08
