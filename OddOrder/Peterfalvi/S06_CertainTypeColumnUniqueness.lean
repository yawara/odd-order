/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S06_CertainTypeCoherence

/-!
# Peterfalvi (5.8), the uniqueness rider: a third equal-degree column forces the first case

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §5, p. 29
(page image: `references/peterfalvi/pages/peterfalvi-p029.png`).

The last sentence of (5.8) reads

> In the second case, `j` and `k` are the only indices `ℓ` such that `ℓ ≥ 1`, `μ_ℓ ∈ 𝒮` and
> `μ_ℓ(1) = μ_k(1)`.

and its proof is the contrapositive statement proved here:

> Suppose that there is an index `ℓ ≥ 1` such that `ℓ ≠ j`, `ℓ ≠ k`, `μ_ℓ ∈ 𝒮` and
> `μ_ℓ(1) = μ_k(1)`.  By Theorem (4.9), `μ_k^{τ₁} − μ_ℓ^{τ₁} = δ_k ∑_i (ω_{ik}^σ − ω_{iℓ}^σ)`.
> Since `μ_ℓ^{τ₁}` is a sum of elements of `R(μ_ℓ)`, it follows that
> `μ_k^{τ₁} = δ_k ∑_i ω_{ik}^σ` — the **first** case of the dichotomy.

## The argument, as formalized

Write `ψ_k`, `ψ_ℓ` for the `τ₁`-images, each a sub-sum of its `R`-family (`hEksub`/`hElsub`), with
`|E_ℓ| = w₁`; the (4.9) difference identity `dadeICM_columnDiff_eq_sum` is the input `hdiff`
(`τ₁` agrees with `τ` on the `A`-supported difference `μ_k − μ_ℓ`, which is where the equal-degree
hypothesis is used).

1. Every member of `R(μ_k)` is a signed `σ`-image at a column in `{k, j}`, so it is orthogonal to
   the whole `χ_ℓ`-column of the grid — hence `⟨ψ_k, ω_{iℓ}^σ⟩ = 0` for every row `i`.
2. Pairing the difference identity with `ω_{iℓ}^σ` therefore gives `⟨ψ_ℓ, ω_{iℓ}^σ⟩ = δ`.
3. But `ψ_ℓ` is a sub-sum of `R(μ_ℓ)`, whose only member meeting `ω_{iℓ}^σ` is `δ·ω_{iℓ}^σ`
   itself; so every one of the `w₁` elements `δ·ω_{iℓ}^σ` lies in `E_ℓ`, and `|E_ℓ| = w₁` forces
   `E_ℓ` to be exactly that column.  Thus `ψ_ℓ = δ ∑_i ω_{iℓ}^σ`.
4. Adding back the difference identity collapses the `χ_ℓ`-column: `ψ_k = δ ∑_i ω_{ik}^σ`.

The signs of the two columns agree (`certainType_columnSign_eq`) precisely because the degrees do.

Reference: issue 0161.
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory
open OddOrder.GroupTheory

variable {G : Type*} [Group G] {A : Set G} {L : Subgroup G}

open scoped Classical in
/-- **Peterfalvi (5.8), uniqueness rider** (p. 29): if a third column `χ_ℓ` — distinct from the
column `χ_k` and from its conjugate `χ_k⁻¹` — carries a family member of the same degree, then the
`τ₁`-image of `μ_k` is the *positive* full `σ`-grid column `δ_k ∑_i ω_{ik}^σ`, i.e. the **first**
case of the (5.8) dichotomy.  The book's rider is the contrapositive: in the second case, `j` and
`k` are the only such indices.

See the module docstring for the four steps. -/
theorem subsum_eq_column_of_third_column [Fintype G] [Fintype ↥L]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]
    (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χk χl : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hk1 : χk ≠ 1) (hl1 : χl ≠ 1)
    (hlk : χl ≠ χk) (hlj : χl ≠ χk⁻¹)
    (hdeg : (∑ i, ((h.columnFamily χk).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily χl).mu i : ClassFunction ↥L ℂ) 1))
    {ψk ψl : ClassFunction G ℂ} {Ek El : Finset (ClassFunction G ℂ)}
    (hEksub : Ek ⊆ (certainTypeR h hk1 (columnSum_inv_apply_one h χk).symm).imageSet)
    (hEksum : ψk = ∑ α ∈ Ek, α)
    (hElsub : El ⊆ (certainTypeR h hl1 (columnSum_inv_apply_one h χl).symm).imageSet)
    (hElsum : ψl = ∑ α ∈ El, α)
    (hElcard : (El.card : ℂ) = (Nat.card h.W1 : ℂ))
    (hdiff : ψk - ψl = S07.dadeIntegralCharacterMap h.dade0 h.tau
      (columnSum h χk - columnSum h χl)) :
    ψk = ((h.columnFamily χk).sign : ℂ) • ∑ i, certainTypeOmegaSigma h χk i := by
  classical
  set δ : ℂ := ((h.columnFamily χk).sign : ℂ) with hδdef
  have hδpm : δ = 1 ∨ δ = -1 := by
    rcases (h.columnFamily χk).sign_eq with hs | hs <;> rw [hδdef, hs] <;> norm_num
  have hδne : δ ≠ 0 := by rcases hδpm with hs | hs <;> rw [hs] <;> norm_num
  have hsignl : ((h.columnFamily χl).sign : ℂ) = δ := by
    rw [hδdef, ← certainType_columnSign_eq h hdeg]
  -- the (4.9) difference identity
  have hdiff' : ψk - ψl
      = ∑ p : Bool × Fin (Nat.card h.W1), certainTypeRImage h χk χl p := by
    rw [hdiff, dadeICM_columnDiff_eq_sum h hk1 hl1 hdeg]
  -- Step B: members of `R(μ_k)` are orthogonal to the `χl`-column of the grid
  have hBk : ∀ α ∈ Ek, ∀ i, ClassFunction.inner α (certainTypeOmegaSigma h χl i) = 0 := by
    intro α hα i
    have := hEksub hα
    simp only [certainTypeR, Finset.mem_image, Finset.mem_univ, true_and] at this
    obtain ⟨⟨b, i'⟩, rfl⟩ := this
    cases b <;>
      simp only [certainTypeRImage, ClassFunction.inner_smul_left, certainTypeOmegaSigma_inner]
    · rw [if_neg (fun hc => hlk hc.1.symm), mul_zero]
    · rw [if_neg (fun hc => hlj hc.1.symm), mul_zero]
  have hBksum : ∀ i, ClassFunction.inner ψk (certainTypeOmegaSigma h χl i) = 0 := by
    intro i
    rw [hEksum, inner_sum_left]
    exact Finset.sum_eq_zero fun α hα => hBk α hα i
  -- Step B′: the RHS of the difference identity against the `χl`-column is `−δ`
  have hδstar : star δ = δ := by rcases hδpm with hs | hs <;> rw [hs] <;> norm_num
  have hRHS : ∀ i, ClassFunction.inner
      (∑ p : Bool × Fin (Nat.card h.W1), certainTypeRImage h χk χl p)
      (certainTypeOmegaSigma h χl i) = -δ := by
    intro i
    have key : ∀ i' : Fin (Nat.card h.W1), ClassFunction.inner
        (certainTypeOmegaSigma h χk i' - certainTypeOmegaSigma h χl i')
        (certainTypeOmegaSigma h χl i) = -(if i' = i then (1 : ℂ) else 0) := by
      intro i'
      rw [ClassFunction.inner_sub_left, certainTypeOmegaSigma_inner, certainTypeOmegaSigma_inner,
        if_neg (fun hc => hlk hc.1.symm)]
      by_cases hii : i' = i
      · rw [if_pos ⟨rfl, hii⟩, if_pos hii]; ring
      · rw [if_neg (fun hc => hii hc.2), if_neg hii]; ring
    rw [certainTypeRImage_sum, ClassFunction.inner_smul_left, ← hδdef, inner_sum_left,
      Finset.sum_congr rfl (fun i' _ => key i')]
    simp
  -- Step C: the `χl`-column coefficient of `ψl` is `δ` at every row
  have hlinv : χl⁻¹ ≠ χl := column_inv_ne_self h hl1
  set a : Fin (Nat.card h.W1) → ClassFunction G ℂ :=
    fun i => certainTypeRImage h χl χl⁻¹ (false, i) with hadef
  have hCl : ∀ i, ClassFunction.inner ψl (certainTypeOmegaSigma h χl i)
      = if a i ∈ El then δ else 0 := by
    intro i
    rw [hElsum, inner_sum_left]
    have hterm : ∀ α ∈ El, ClassFunction.inner α (certainTypeOmegaSigma h χl i)
        = if α = a i then δ else 0 := by
      intro α hα
      have := hElsub hα
      simp only [certainTypeR, Finset.mem_image, Finset.mem_univ, true_and] at this
      obtain ⟨⟨b, i'⟩, rfl⟩ := this
      by_cases hbi : (b, i') = ((false, i) : Bool × Fin (Nat.card h.W1))
      · rw [hbi, if_pos rfl]
        change ClassFunction.inner (((h.columnFamily χl).sign : ℂ) • certainTypeOmegaSigma h χl i)
          (certainTypeOmegaSigma h χl i) = δ
        rw [ClassFunction.inner_smul_left, certainTypeOmegaSigma_inner, if_pos ⟨rfl, rfl⟩,
          hsignl, mul_one]
      · rw [if_neg (fun hc => hbi (certainTypeRImage_injective h hlinv.symm hc))]
        cases b <;>
          simp only [certainTypeRImage, ClassFunction.inner_smul_left,
            certainTypeOmegaSigma_inner, hsignl]
        · rw [if_neg (fun hc => hbi (Prod.ext rfl hc.2)), mul_zero]
        · rw [if_neg (fun hc => hlinv hc.1), mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' El (a i) (fun _ => δ)]
  -- combine: `⟨ψl, ω_{χl,i}⟩ = δ`, so every `a i` lies in `El`
  have hmem : ∀ i, a i ∈ El := by
    intro i
    by_contra hno
    have h1 : ClassFunction.inner ψl (certainTypeOmegaSigma h χl i) = 0 := by
      rw [hCl i, if_neg hno]
    have h2 : ClassFunction.inner ψk (certainTypeOmegaSigma h χl i)
        - ClassFunction.inner ψl (certainTypeOmegaSigma h χl i) = -δ := by
      rw [← ClassFunction.inner_sub_left, hdiff']
      exact hRHS i
    rw [hBksum i, h1, sub_zero] at h2
    exact hδne (by rw [eq_comm, neg_eq_zero] at h2; exact h2)
  -- Step C′: `El` is exactly the `χl`-column, so `ψl = δ ∑_i ω_{χl,i}`
  have hainj : Function.Injective a := by
    intro i i' hii
    have := certainTypeRImage_injective h hlinv.symm hii
    simpa using this
  have hElcardN : El.card = Nat.card h.W1 := Nat.cast_injective hElcard
  have hEleq : El = Finset.univ.image a := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact hmem i
    · rw [Finset.card_image_of_injective _ hainj, hElcardN, Finset.card_univ,
        Fintype.card_fin]
  have hψl : ψl = δ • ∑ i, certainTypeOmegaSigma h χl i := by
    rw [hElsum, hEleq, Finset.sum_image (fun i _ i' _ hii => hainj hii), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [hadef, certainTypeRImage, hsignl]
  -- Step D: `ψk = ψl + (ψk − ψl)` collapses the `χl`-column
  have hD : ψk = ψl + ∑ p : Bool × Fin (Nat.card h.W1), certainTypeRImage h χk χl p := by
    rw [← hdiff']; abel
  rw [hD, hψl, certainTypeRImage_sum, ← hδdef, ← smul_add, Finset.sum_sub_distrib]
  congr 1
  abel

end OddOrder.Peterfalvi.S06
