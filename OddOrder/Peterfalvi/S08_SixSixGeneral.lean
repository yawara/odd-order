/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_SixFiveGeneral
import OddOrder.GroupTheory.RepresentationTheory.SchurCenterBound

/-!
# Peterfalvi (6.6) for a general kernel: the `X`-set and its degree data

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §6, (6.6)
(pp. 31–32).

> **(6.6)** Suppose that Hypothesis (6.4) holds with `M = 1`.  Let `Z` be a normal subgroup of `L`
> such that `1 ≠ Z ⊆ Z(K)` and let `𝒳 = 𝒮 − 𝒮(Z)`.  Suppose that `𝒳 ⊆ Irr L`.  Then
> `𝒳 = {χ ∈ Irr L | Z ⊄ Ker χ}` and `𝒳` is coherent.

The **set identity** is already available for an arbitrary kernel
(`inducedKernelFamily_sdiff_eq_irreducible_not_subset_characterKernel`, `S08_InducedKernelFamily`).
This leaf starts the general-kernel form of the **coherence** half, whose `K = H` (Sibley)
instance is `S08_CoherenceBasic.Xset_isCoherent_of_irreducible_X`.

## Why a port rather than a re-proof

Measuring the Sibley chain shows that its per-member arithmetic uses the `SibleyDadeHypothesis`
only through the family shape `𝒮 = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1}` (`S_eq`) and the normality of
`H` — never the Dade datum, the split `L = H ⋊ W₁`, the TI condition, or the (6.8)(c)
alternative.  So the right move is to restate the arithmetic over `inducedKernelFamily K` and let
the Sibley layer read it off, exactly as was done for the (6.6) `X`-characterization.

The book's proof of the coherence half (p. 32) runs on three numeric facts about
`𝒳 = 𝒮 − 𝒮(Z)` once `K` is a `p`-group (which (6.5) supplies):

* every member has degree `|L:K|·p^k` (`exists_index_primePow_degree_of_mem_inducedKernelFamily`);
* the source degree obeys [Is] Corollary 2.30 against the **central** `Z`:
  `θ(1)² ≤ |K:Z|` (`exists_source_primePow_centralBound_of_mem_xSet`) — this is where `Z ⊆ Z(K)`
  enters, and it is what fails at `Z = [K,K]`;
* the degree-square sum over `𝒳` (Peterfalvi's `∑ χᵢ(1)² = |L|·|L:Z| − ∑_{χ>i} χⱼ(1)²`).
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

/-! ### The `(6.6)` set `𝒳 = 𝒮 − 𝒮(Z)` for a general kernel -/

/-- **Peterfalvi (6.6)'s `𝒳 = 𝒮 − 𝒮(Z)` for a general kernel `K`**: the members of the (6.1)
family `𝒮 = 𝒮(⊥)` whose source is *not* trivial on `Z`.  The Sibley `K = H` instance is
`SibleyDadeHypothesis.Xset` (`Xset_eq_inducedKernelFamily_sdiff`). -/
def xSet (K : Subgroup ↥L) [Invertible (Nat.card ↥K : ℂ)] (Z : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  inducedKernelFamily K ⊥ \ inducedKernelFamily K Z

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
theorem mem_xSet {Z : Subgroup ↥L} {φ : ClassFunction ↥L ℂ} :
    φ ∈ xSet K Z ↔ φ ∈ inducedKernelFamily K ⊥ ∧ φ ∉ inducedKernelFamily K Z :=
  Iff.rfl

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
theorem xSet_subset (Z : Subgroup ↥L) : xSet K Z ⊆ inducedKernelFamily K ⊥ :=
  fun _ h => h.1

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
theorem xSet_finite (Z : Subgroup ↥L) : (xSet K Z).Finite :=
  (inducedKernelFamily_finite (K := K) ⊥).subset (xSet_subset Z)

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- `𝒳` is closed under complex conjugation (inherited from both `𝒮` and `𝒮(Z)`). -/
theorem xSet_closedUnderConjugate (Z : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (xSet K Z) := by
  intro φ hφ
  refine ⟨inducedKernelFamily_closedUnderConjugate (K := K) ⊥ hφ.1, fun hcon => hφ.2 ?_⟩
  have := inducedKernelFamily_closedUnderConjugate (K := K) Z hcon
  rwa [ClassFunction.conj_conj] at this

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- `𝒳` has no real members (Peterfalvi (1.1), `|L|` odd). -/
theorem xSet_hasNoRealCharacters (hodd : Odd (Nat.card ↥L)) (Z : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (xSet K Z) :=
  (inducedKernelFamily_hasNoRealCharacters (K := K) hodd ⊥).mono (xSet_subset Z)

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- Two distinct members of `𝒳` are orthogonal (Hypothesis (5.2.c)). -/
theorem xSet_pairwise_orthogonal (Z : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.PairwiseOrthogonal (xSet K Z) :=
  fun _ _ hφ hφ' hne => inducedKernelFamily_pairwise_orthogonal hφ.1 hφ'.1 hne

/-! ### `p`-power degree data (the `(6.6)` arithmetic, general kernel) -/

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- **(6.6) per-member degree shape, general kernel.**  Every member `χ = Ind_K^L θ` of `𝒮(X)` has
degree `|L:K|·θ(1)`; when `K` is a `p`-group, `θ(1) = p^k`, so `χ(1) = |L:K|·p^k`.

The Sibley instance is `exists_index_primePow_degree_of_mem_S`; its proof uses the
`SibleyDadeHypothesis` only through `S_eq`, i.e. the family shape, so nothing is lost here. -/
theorem exists_index_primePow_degree_of_mem_inducedKernelFamily
    {p : ℕ} (hp : p.Prime) (hKp : IsPGroup p ↥K) {X : Subgroup ↥L}
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ inducedKernelFamily K X) :
    ∃ k : ℕ, χ 1 = ((K.index * p ^ k : ℕ) : ℂ) := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  obtain ⟨θ, -, -, rfl⟩ := hχ
  obtain ⟨k, hk⟩ := exists_primePow_natDegree_of_isPGroup hp hKp θ
  exact ⟨k, by rw [ClassFunction.induce_apply_one, hk]; push_cast; ring⟩

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- **(6.6) central degree bound, general kernel.**  For `χ = Ind_K^L θ ∈ 𝒳(Z)` with `K` a
`p`-group and `Z` **central in `K`** (`Z.subgroupOf K ≤ Z(K)`, the book's `Z ⊆ Z(K)`), the source
`θ` satisfies `θ(1) = p^k` and, by [Is] Corollary 2.30 (`exists_degree_sq_le_index`, which is
exactly where centrality is needed), `(p^k)² ≤ |K:Z|`.

This is the `θχ`/`hθsq_le_qtot` datum of every X-chain step.  Centrality is essential: the bound
fails at `Z = [K,K]`. -/
theorem exists_source_primePow_centralBound_of_mem_xSet
    {p : ℕ} (hp : p.Prime) (hKp : IsPGroup p ↥K)
    {Z : Subgroup ↥L} (hZcentral : Z.subgroupOf K ≤ Subgroup.center ↥K)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ xSet K Z) :
    ∃ k : ℕ, χ 1 = ((K.index * p ^ k : ℕ) : ℂ)
      ∧ (p ^ k) ^ 2 ≤ Nat.card (↥K ⧸ Z.subgroupOf K) := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  obtain ⟨θ, -, -, rfl⟩ := hχ.1
  obtain ⟨k, hk⟩ := exists_primePow_natDegree_of_isPGroup hp hKp θ
  refine ⟨k, by rw [ClassFunction.induce_apply_one, hk]; push_cast; ring, ?_⟩
  obtain ⟨d, hd, hdsq⟩ := θ.isIrreducible.exists_degree_sq_le_index (Z.subgroupOf K) hZcentral
  have hdpk : d = p ^ k := by
    have hcast : (d : ℂ) = ((p ^ k : ℕ) : ℂ) := by rw [← hd, hk]
    exact_mod_cast hcast
  rw [← hdpk, ← Subgroup.index_eq_card]
  exact hdsq

/-! ### Hypothesis (5.2) for `𝒳` -/

/-- **Hypothesis (5.2) for the `(6.6)` set `𝒳 = 𝒮 − 𝒮(Z)`.**  `𝒳` is a conjugation-closed,
real-free, pairwise-orthogonal subset of `𝒮`, so every clause restricts from
`InducedFamilyImageData.hypothesis` at `X = ⊥` — with the same (5.3.a) two-element `R(χ)` for the
(irreducible) members and the same derived (5.2.e). -/
noncomputable def InducedFamilyImageData.xSetHypothesis {A₀ : Set ↥L}
    (RD : InducedFamilyImageData A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {Z : Subgroup ↥L} (hirr : ∀ φ ∈ xSet K Z, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥L) (G := G) (xSet K Z) A₀ :=
  RD.hypothesisOfSubfamily hodd hKsupp (xSet_subset Z) (xSet_closedUnderConjugate Z) hirr

@[simp] theorem InducedFamilyImageData.xSetHypothesis_tau {A₀ : Set ↥L}
    (RD : InducedFamilyImageData A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {Z : Subgroup ↥L} (hirr : ∀ φ ∈ xSet K Z, IsIrreducibleCharacter φ) :
    (RD.xSetHypothesis hodd hKsupp hirr).tau = RD.tau := rfl

/-! ### The `(6.6)` degree-square sum over `𝒳`, general kernel -/

open scoped Classical in
/-- The `Finset` enumerating `𝒳 = 𝒮 − 𝒮(Z)` — the difference of the two kernel-filter images that
`sum_re_div_normSq_inducedKernelFamily_eq` sums over. -/
noncomputable def xSetFinset (K : Subgroup ↥L) [Invertible (Nat.card ↥K : ℂ)]
    (Z : Subgroup ↥L) : Finset (ClassFunction ↥L ℂ) :=
  (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
        (↑((⊥ : Subgroup ↥L).subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥K ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥K)).image
      (fun θ => ClassFunction.induce K θ.toClassFunction) \
    (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
        (↑(Z.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥K ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥K)).image
      (fun θ => ClassFunction.induce K θ.toClassFunction)

omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
open scoped Classical in
theorem coe_xSetFinset (Z : Subgroup ↥L) : ↑(xSetFinset K Z) = xSet K Z := by
  rw [xSetFinset, Finset.coe_sdiff, coe_kernelFilter_image_eq_inducedKernelFamily,
    coe_kernelFilter_image_eq_inducedKernelFamily]
  rfl

omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
open scoped Classical in
theorem mem_xSetFinset {Z : Subgroup ↥L} {φ : ClassFunction ↥L ℂ} :
    φ ∈ xSetFinset K Z ↔ φ ∈ xSet K Z := by
  rw [← Finset.mem_coe, coe_xSetFinset]

omit [Invertible (Nat.card G : ℂ)] in
open scoped Classical in
/-- **Peterfalvi (6.6) degree-square sum, general kernel**:
`∑_{χ ∈ 𝒳} χ(1)² = |L:K| · (|K| − |K:Z|)`.

Since `𝒮(Z) ⊆ 𝒮` and `𝒳 = 𝒮 − 𝒮(Z)`, this is the difference of two instances of the general
`S(X)` weighted identity `sum_re_div_normSq_inducedKernelFamily_eq` (at `X = ⊥`, using
`|K ⧸ ⊥| = |K|`, and at `X = Z`), extracted by `Finset.sum_sdiff`.  The weights `‖χ‖²` cancel on
the `𝒳` side because its members are irreducible (`hX` — the book's `𝒳 ⊆ Irr L`), which is exactly
the case-B situation of the Sibley `sum_re_sq_Xset_eq_of_irreducible_X`: reducible members of `𝒮`
are allowed, as long as they lie in `𝒮(Z)`.

This is the `total` of the `X`-chain step data; the book's divisibility argument (p. 32) shows the
source degree `θ(1)²` divides it. -/
theorem sum_re_sq_xSet_eq (Z : Subgroup ↥L) [Z.Normal]
    (hX : ∀ χ ∈ xSet K Z, IsIrreducibleCharacter χ) :
    ∑ χ ∈ xSetFinset K Z, ((χ 1).re) ^ 2
      = (K.index : ℝ) * ((Nat.card ↥K : ℝ) - (Nat.card (↥K ⧸ Z.subgroupOf K) : ℝ)) := by
  set f : ClassFunction ↥L ℂ → ℝ :=
    fun χ => ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re with hf
  set A := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
        (↑((⊥ : Subgroup ↥L).subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥K ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥K)).image
      (fun θ => ClassFunction.induce K θ.toClassFunction) with hA
  set B := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
        (↑(Z.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥K ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥K)).image
      (fun θ => ClassFunction.induce K θ.toClassFunction) with hB
  -- `𝒮(Z) ⊆ 𝒮` at the `Finset` level: `⊥ ≤ ker θ` always.
  have hsub : B ⊆ A := by
    refine Finset.image_subset_image ?_
    intro θ hθ
    rw [Finset.mem_filter] at hθ ⊢
    refine ⟨hθ.1, ?_, hθ.2.2⟩
    intro x hx
    rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
    subst hx
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  have hsd := Finset.sum_sdiff (f := f) hsub
  have h0 := sum_re_div_normSq_inducedKernelFamily_eq (K := K) (⊥ : Subgroup ↥L)
  have hZ := sum_re_div_normSq_inducedKernelFamily_eq (K := K) Z
  have hbotcard : Nat.card (↥K ⧸ (⊥ : Subgroup ↥L).subgroupOf K) = Nat.card ↥K := by
    rw [Subgroup.bot_subgroupOf]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := ↥K)).toEquiv
  rw [hbotcard] at h0
  -- on `𝒳` the weight is `1`, so `f` is the plain degree square there
  have hconv : ∀ χ ∈ A \ B, f χ = ((χ 1).re) ^ 2 := by
    intro χ hχ
    have hirr : IsIrreducibleCharacter χ := hX χ (mem_xSetFinset.mp hχ)
    simp only [hf, hirr.inner_self_eq_one, Complex.one_re, div_one]
  rw [xSetFinset, ← hA, ← hB, ← Finset.sum_congr rfl hconv, eq_sub_of_add_eq hsd, h0, hZ]
  ring

end OddOrder.Peterfalvi.S08
