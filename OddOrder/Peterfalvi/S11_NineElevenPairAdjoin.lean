/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S07_UnionPairBridge
import OddOrder.Peterfalvi.S11_NineElevenAlphaBound

/-!
# Peterfalvi (9.11.7)–(9.11.8): the coherent-pair adjunction and the case-(a) endgame

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §9, p. 57,
(9.11.7)–(9.11.8) (mmd `04.11`, lines ~176–199); Coq mirror `PFsection9.v:2048-2227`.

## What this file provides

The **final piece of the (9.11) case-(a) refutation** (issue 9083, Phase E-final): the
discharge of the single residual `NineElevenSevenEightRefutation`, and with it the
unconditional Peterfalvi (9.11) (`coherent_sOf_H0Cprime`, Coq `Ptype_core_coherence`).

⚠ The two structure-free ingredients — the union-pair coherent extension
(`S07.isCoherent_union_pair_of_bridge`, Peterfalvi (5.6.3)) and the projection budget
(`S07.exists_bridge_target_of_budget`, (9.11.7)–(9.11.8)) — were moved to
`OddOrder/Peterfalvi/S07_UnionPairBridge.lean` (issue 1045): neither mentions §9 or §13 data, and
the §9-level (9.11) chain needs them without importing this file's §11/§13 closure.

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

end OddOrder.Peterfalvi.S13
