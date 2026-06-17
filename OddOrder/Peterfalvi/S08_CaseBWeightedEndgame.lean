/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S08_CaseBEnumeration
import OddOrder.Peterfalvi.S08_CaseBEndgame

/-!
# Peterfalvi §6.8.3 — case-(B) norm-weighted endgame

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §6, (6.8.3).

This leaf assembles the **case-(B) (6.8.3) contradiction** from the norm-weighted member-family
bound (brick 3, `S08_CaseBEnumeration`) and the FPF arithmetic spine (`S08_CaseBEndgame`):

* `sum_re_div_normSq_Xset_eq` — the norm-weighted `X`-set degree-square identity
  `∑_{χ∈X(Z)} χ(1).re²/‖χ‖² = |L:H|·(|H| − |H:Z|)` (the genuinely weighted form, valid with the
  reducible certain-type columns of case (B), via the complex orbit count
  `sum_div_normSq_induce_kernelFilter_eq`);
* `xSum_le_two_psi_caseB` — the norm-weighted (5.6) `X`-sum bound
  `|L:H|·(|H| − |H:W₂|) ≤ 2·ψ(1).re·η(1).re`, bridging brick 3 to the identity;
* `false_of_coherentXunionYset_caseB_of_not_coherentS` — the (6.8.3) contradiction: a coherent
  `X(W₂) ∪ Y` but non-coherent `S` forces the break-pair bound, which the FPF arithmetic core
  `false_of_caseB_break_of_bounds` refutes.

The final `S08_CoherenceTheorems` c2-math-B dispatch — which *constructs* the `X(W₂) ∪ Y` coherence
seed (`coherentXunionYset_caseB_of_glued`) and thereby requires the §6 certain-type structure-theory
input `hXanchored` — is **not** in this leaf; the endgame here takes that seed as a hypothesis.
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory
open scoped Classical

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(6.6) norm-weighted `X` degree-square identity** (case-(B) form).

The norm-weighted degree-square sum over `X = S − S(Z)` is `|L:H|·(|H| − |H:Z|)`.  Unlike the
Frobenius `sum_re_sq_Xset_eq` (which uses `χ(1)²/‖χ‖² = χ(1).re²` from irreducibility of every
member), this keeps the `/‖χ‖²` weights and so is valid even when `X` contains the **reducible**
certain-type columns of case (B): it routes through the complex orbit-count
`sum_div_normSq_induce_kernelFilter_eq` (in the `χ(1)²/⟨χ,χ⟩` form, valid for reducibles), taking
the difference of the `A = ⊥` and `A = Z` filter sums via `Finset.sum_sdiff`.  The per-summand real
conversion `χ(1)²/⟨χ,χ⟩ = (χ(1).re²/⟨χ,χ⟩.re : ℂ)` uses that `χ(1)` is a (real) degree
(`induce_apply_one`) and `⟨χ,χ⟩` is real (`inner_self_eq_realCast`). -/
theorem sum_re_div_normSq_Xset_eq (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L} [Z.Normal] :
    ∑ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
        ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re
      = (H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ)) := by
  letI : H.Normal := hyp.H_normal
  have hbotker : ∀ θ : IrreducibleCharacter ↥H,
      (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro θ x hx
    rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
    subst hx
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  have hsub : (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) ⊆
      (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) := by
    apply Finset.image_subset_image
    intro θ hθ
    rw [Finset.mem_filter] at hθ ⊢
    exact ⟨hθ.1, hbotker θ, hθ.2.2⟩
  have hsd := Finset.sum_sdiff
    (f := fun χ : ClassFunction ↥L ℂ => χ 1 ^ 2 / ClassFunction.inner χ χ) hsub
  have hB2bot := @sum_div_normSq_induce_kernelFilter_eq ↥L _ _ _ H _ _ (⊥ : Subgroup ↥L) _
  have hB2Z := @sum_div_normSq_induce_kernelFilter_eq ↥L _ _ _ H _ _ Z _
  have hbotcard : Nat.card (↥H ⧸ (⊥ : Subgroup ↥L).subgroupOf H) = Nat.card ↥H := by
    rw [Subgroup.bot_subgroupOf]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := ↥H)).toEquiv
  rw [hbotcard] at hB2bot
  -- the complex weighted `X`-set identity.
  have hcomplex : ∑ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
              (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                  (θ : ClassFunction ↥H ℂ) ∧
                θ ≠ trivialIrreducibleCharacter ↥H)).image
            (fun θ => ClassFunction.induce H θ.toClassFunction) \
          (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
              (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                  (θ : ClassFunction ↥H ℂ) ∧
                θ ≠ trivialIrreducibleCharacter ↥H)).image
            (fun θ => ClassFunction.induce H θ.toClassFunction)),
          χ 1 ^ 2 / ClassFunction.inner χ χ
        = (H.index : ℂ) * ((Nat.card ↥H : ℂ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℂ)) := by
    rw [eq_sub_of_add_eq hsd, hB2bot, hB2Z]; ring
  -- per-summand real conversion `χ(1)²/⟨χ,χ⟩ = (χ(1).re²/⟨χ,χ⟩.re : ℂ)`.
  have hconv : ∀ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
      χ 1 ^ 2 / ClassFunction.inner χ χ
        = (((χ 1).re ^ 2 / (ClassFunction.inner χ χ).re : ℝ) : ℂ) := by
    intro χ hχ
    rw [Finset.mem_sdiff] at hχ
    obtain ⟨θ, -, rfl⟩ := Finset.mem_image.mp hχ.1
    obtain ⟨d, -, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    have hχ1 : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) (1 : ↥L)
        = ((H.index * d : ℕ) : ℂ) := by
      rw [ClassFunction.induce_apply_one, hd]; push_cast; ring
    have hr : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) (1 : ↥L)).re
        = ((H.index * d : ℕ) : ℝ) := by
      rw [hχ1, Complex.natCast_re]
    rw [hr, hχ1, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    congr 1
    rw [inner_self_eq_realCast (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)), Complex.ofReal_re]
  -- combine: cast the real sum to `ℂ`, rewrite each summand, identify with `hcomplex`.
  have key : (((∑ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
              (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                  (θ : ClassFunction ↥H ℂ) ∧
                θ ≠ trivialIrreducibleCharacter ↥H)).image
            (fun θ => ClassFunction.induce H θ.toClassFunction) \
          (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
              (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                  (θ : ClassFunction ↥H ℂ) ∧
                θ ≠ trivialIrreducibleCharacter ↥H)).image
            (fun θ => ClassFunction.induce H θ.toClassFunction)),
          ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re : ℝ)) : ℂ)
      = (((H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ))) : ℝ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun χ hχ => (hconv χ hχ).symm), hcomplex]
    push_cast; ring
  exact Complex.ofReal_inj.mp key

/-- **(6.2) norm-weighted `X`-sum bound** (case-(B) form).

The norm-weighted Peterfalvi (5.6) inequality for case (B): if `X(W₂) ∪ Y` is coherent but adding
the break pair `{ψ, ψ̄}` (`ψ ∈ S`, `{ψ, ψ̄}` disjoint from `X(W₂) ∪ Y`) is **not** coherent, then
the degree-square count over `X(W₂)` is bounded by `|L:H|·(|H| − |H:W₂|) ≤ 2·ψ(1).re·η(1).re`.

This is the weighted analogue of `xSum_le_two_psi` (`S08_CoherenceCorePart2`): the brick-3 family
bound `∑ⱼ χⱼ(1).re²/mcⱼ ≤ 2ψ(1).re·η(1).re` (`sMember_degreeSqNormReBound_of_not_coherent`) bounds
the sum over the enumerated `X(W₂) ∪ Y` family, into which the norm-weighted `X`-set identity
`sum_re_div_normSq_Xset_eq` injects `∑_{χ∈X(W₂)} χ(1).re²/‖χ‖²` (`X(W₂) ⊆ X(W₂) ∪ Y`, with
nonnegative weighted summands `inner_self_re_nonneg`). -/
theorem xSum_le_two_psi_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} [W2.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hXsub : hyp.Xset W2 ⊆ S₁)
    {η : ClassFunction ↥L ℂ} (hηY : η ∈ hyp.Yset) (hηS₁ : η ∈ S₁)
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ W2.subgroupOf H) : ℝ))
      ≤ 2 * (ψ 1).re * (η 1).re := by
  classical
  obtain ⟨k, χmem, mc, hinj, hrange, hmemS1, hmcpos, hmcnorm, hfambound⟩ :=
    sMember_degreeSqNormReBound_of_not_coherent hyp h46 hHK hW1 hS₁sub hS₁conj hS₁fin hS₁coh hηY hηS₁
      hψS hψirr hψnotS1 hψcnotS1 hnc
  have hXsum := sum_re_div_normSq_Xset_eq hyp (Z := W2)
  set Xdiff := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(W2.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXdiffdef
  have hsub : Xdiff ⊆ (Set.range χmem).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hXdiffdef, Finset.mem_sdiff] at hχ
    obtain ⟨hχbot, hχnotZ⟩ := hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχbot
    obtain ⟨-, -, hne⟩ := Finset.mem_filter.mp hθ
    have hχS : ClassFunction.induce H θ.toClassFunction ∈ hyp.S := by
      rw [hyp.S_eq]; exact ⟨θ, hne, rfl⟩
    have hχnotSZ : ClassFunction.induce H θ.toClassFunction ∉ hyp.SsubFiltration W2 := by
      intro hmem
      rw [hyp.mem_SsubFiltration] at hmem
      obtain ⟨θ', hne', hker', heq'⟩ := hmem
      exact hχnotZ (Finset.mem_image.mpr
        ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
    exact hXsub (hyp.mem_Xset.mpr ⟨hχS, hχnotSZ⟩)
  rw [← hXsum]
  calc ∑ χ ∈ Xdiff, ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re
      ≤ ∑ χ ∈ (Set.range χmem).toFinset, ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun χ _ _ => div_nonneg (sq_nonneg _) (inner_self_re_nonneg χ))
    _ = ∑ j : Fin k, ((χmem j 1).re) ^ 2 / (ClassFunction.inner (χmem j) (χmem j)).re :=
        sum_toFinset_range_eq hinj (fun χ => ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re)
    _ = ∑ j : Fin k, ((χmem j 1).re) ^ 2 / mc j := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hmcnorm j, Complex.ofReal_re]
    _ ≤ 2 * (ψ 1).re * (η 1).re := hfambound

end OddOrder.Peterfalvi.S08
