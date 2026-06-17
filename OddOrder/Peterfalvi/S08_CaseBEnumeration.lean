/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S08_CaseBAssembly
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

end OddOrder.Peterfalvi.S08
