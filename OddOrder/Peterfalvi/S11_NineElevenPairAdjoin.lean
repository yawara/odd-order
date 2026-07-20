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

set_option maxHeartbeats 1600000 in
-- the two (5.5) projections and the (5.2.e) dispatch thread the
-- `hyp.base.tau = dadeIntegralCharacterMap` defeq (as in `sOf_H0Cprime_memberRFamily_orthogonal`)
/-- **Cross-orthogonality of coherent images** (Coq `coherent_ortho`, `PFsection5.v:986`):
for coherent subfamilies `T₁, T₂ ⊆ 𝒮(H₀C′)` and members `ψ ∈ T₁`, `λ ∈ T₂` with
`ψ ∉ {λ, λ̄}` (so `⟨ψ, λ⟩ = ⟨ψ, λ̄⟩ = 0` by the family's pairwise orthogonality), the
coherent images are orthogonal: both are partial `R`-family sums by (5.5), and the
`R`-families are cross-orthogonal by (5.2.e). -/
theorem coherent_extension_cross_orthogonal
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {T₁ T₂ : Set (ClassFunction ↥M ℂ)}
    (hT₁sub : T₁ ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hT₂sub : T₂ ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (c₁ : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau T₁ hyp.base.A0)
    (c₂ : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau T₂ hyp.base.A0)
    {ψ lam : ClassFunction ↥M ℂ}
    (hψT : ψ ∈ T₁) (hψcT : ψ.conj ∈ T₁) (hlamT : lam ∈ T₂) (hlamcT : lam.conj ∈ T₂)
    (hne1 : ψ ≠ lam) (hne2 : ψ ≠ lam.conj) :
    ClassFunction.inner (c₁.extension ψ) (c₂.extension lam) = 0 := by
  haveI := hyp.base.finiteG
  classical
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun x hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  have h1 : ClassFunction.inner ψ lam = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF (hT₁sub hψT)) (hIKF (hT₂sub hlamT)) hne1
  have h2 : ClassFunction.inner ψ lam.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF (hT₁sub hψT)) (hIKF (hT₂sub hlamcT)) hne2
  obtain ⟨E₁, hE₁sub, hE₁⟩ :=
    coherent_extension_eq_sum_memberRFamily hG hyp hT₁sub c₁ hψT hψcT
  obtain ⟨E₂, hE₂sub, hE₂⟩ :=
    coherent_extension_eq_sum_memberRFamily hG hyp hT₂sub c₂ hlamT hlamcT
  have horth := sOf_H0Cprime_memberRFamily_orthogonal hG hyp
    (hT₁sub hψT) (hT₂sub hlamT) h1 h2
  rw [hE₁, hE₂, OddOrder.RepresentationTheory.inner_sum_left]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [OddOrder.RepresentationTheory.inner_sum_right]
  exact Finset.sum_eq_zero fun β hβ => horth α (hE₁sub hα) β (hE₂sub hβ)

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

/-! ### The (9.11.7)–(9.11.8) discharge -/

section Discharge

variable [Finite G]

set_option maxHeartbeats 3200000 in
-- threads the `hyp.base.tau = dadeIntegralCharacterMap` defeq through the ZIrr/isometry
-- layers while assembling the ~20 scalar inputs of the projection budget
/-- **Peterfalvi (9.11.7)–(9.11.8), discharged** (issue 9083 Phase E-final; Coq
`PFsection9.v:2048-2227`, the tail of `Ptype_core_coherence`).

In the orthogonal branch `α^τ ⊥ 𝒮₃^{τ₃}` of the (9.11.6) dichotomy: `𝒮₄ ≠ ∅` (else the
(9.11.2)–(9.11.5) arithmetic spine already refutes, since `|𝒮₄| = 0 ≤ N`); pick `λ₁ ∈ 𝒮₄`,
put `e = u/a = [U₁ : C] ≥ 2` (`a ∣ u` by the `C ≤ U₁ ≤ U` index chain; `u ≠ a` since a
degree-`qa` irreducible member would lie in `𝒮₁ ⊆ 𝒮₂`) and `β = λ₁ − e·ψ₁`.  The projection
budget (`exists_bridge_target_of_budget`) applied to `β^τ` and `α^τ` over the orthonormal
families `𝒮₂^{τ₁}` (`|𝒮₂| = 2e` by the (9.8.d) count at the equality configuration) and
`𝒮₄^{τ₃}` — cross-orthogonal by `coherent_extension_cross_orthogonal` — produces
`Γ ∈ ℤ[Irr G]` with `‖Γ‖² = 1`, `Γ ⊥ 𝒮₂^{τ₁}`, `⟨Γ, λ₁^{τ₃}⟩ − ⟨Γ, λ̄₁^{τ₃}⟩ = 1` and the
bridge `β^τ = Γ − e·τ₁ψ₁`.  The union-pair extension (`isCoherent_union_pair_of_bridge`,
with `X = Γ`, `Xc = Γ − (λ₁ − λ̄₁)^τ`) then adjoins `{λ₁, λ̄₁}` coherently to `𝒮₂`,
contradicting the maximality pair clause `hpairs`. -/
theorem nineElevenSevenEightRefutation
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    (hncH0C : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    NineElevenSevenEightRefutation hyp caseA := by
  haveI := hyp.base.finiteG
  classical
  intro S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs h2a hCUprime hS3deg hcount hFbound hS2deg
    c₃ γ ψ₁ hψ₁S₂ hψ₁irr hψ₁deg hγZIrr hγ1 hγorth hαsupp hc
  obtain ⟨c₁⟩ := hS₂coh
  -- ── ambient family facts
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun x hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hSfin : (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime).Finite :=
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_finite
        (K := (derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M)).subset
      (fun x hx => by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  have hS₂fin : S₂.Finite := hSfin.subset hS₂sub
  have hS₂cut := caseA_sTwo_subset_degreeQaCut hG hyp caseA hS₁sub hS₂sub h2a hCUprime
    hcount hFbound
  have hψ₁sOf : ψ₁ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime := hS₂sub hψ₁S₂
  have hselfone : ∀ {χ : ClassFunction ↥M ℂ}, IsIrreducibleCharacter χ →
      ClassFunction.inner χ χ = 1 := by
    intro χ hχ
    have h := irreducibleCharacter_inner_eq_ite
      (⟨χ, hχ⟩ : IrreducibleCharacter ↥M) ⟨χ, hχ⟩
    rwa [if_pos rfl] at h
  -- ── the (9.11.2) TI-witness supplies `U₁` with `C ≤ U₁ ≤ U`, `[U:U₁] = a`
  obtain ⟨U₁, hCU₁, hU₁U, hU₁a, -⟩ :=
    caseA_nineElevenTwo_tiWitness hG hyp caseA hS3deg hS2deg hncH0C htype
  obtain ⟨e, hedef⟩ : ∃ e : ℕ,
      e = (OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief).relIndex U₁ := ⟨_, rfl⟩
  have hue : e * caseA.a
      = (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u := by
    rw [hedef]
    have h := Subgroup.relIndex_mul_relIndex
      (OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief) U₁ hyp.s11Setup.U hCU₁ hU₁U
    rwa [hU₁a, OddOrder.Peterfalvi.S11.relIndex_cSub_U_eq_u
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)] at h
  -- ── the arithmetic spine refutes `|𝒮₄| ≤ N`, so `𝒮₄ ≠ ∅`
  obtain ⟨K₁, K₂, hK₁, hK₂, hCinf⟩ :=
    caseA_two_summand_inertia_inputs hG hyp caseA hS3deg hS2deg hncH0C htype
  have hclass := caseA_nineElevenThree_count_inputs hG hyp caseA hS₁sub hS3deg hS2deg
    hCUprime hcount hncH0C htype
  obtain ⟨N, hnorm, -⟩ := caseA_nineElevenFour_norm_inputs hyp caseA
    (caseA_nineElevenTwo_tiWitness hG hyp caseA hS3deg hS2deg hncH0C htype) hCUprime hcount
  have hqp : (hyp.s11Setup.q).Prime := hyp.s11Setup.nontrivial.2.1
  have hqodd : Odd hyp.s11Setup.q :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.s11Setup.typeP.W1)
  have hq3 : 3 ≤ hyp.s11Setup.q := by
    obtain ⟨k, hk⟩ := hqodd
    have h2 := hqp.two_le
    omega
  have hu1 : 1 ≤ (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u :=
    (OddOrder.Peterfalvi.S11.u_odd hG
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)).pos
  have hp1 : 1 < hyp.chief.p := hyp.chief.p_prime.one_lt
  have hpeq : hyp.chief.p = 2 * caseA.a + 1 := by omega
  have hS4ne : (nineElevenSFour hyp S₂).Nonempty := by
    rcases Set.eq_empty_or_nonempty (nineElevenSFour hyp S₂) with hemp | hne
    · exact absurd
        (OddOrder.Peterfalvi.S11.nineElevenCaseA_equality_refutation caseA hq3 hu1 hpeq
          hK₁ hK₂ hCinf hclass rfl hnorm
          (by rw [hemp, Set.ncard_empty]; exact Nat.zero_le N))
        not_false
    · exact hne
  obtain ⟨lam₁, hlam₁S₄⟩ := hS4ne
  obtain ⟨hlam₁sOfC, hlam₁irr, hlam₁nS₂⟩ := hlam₁S₄
  -- ── `𝒮₄ ⊆ 𝒮₃` along `H₀C′ ≤ H₀C`; the pair `{λ₁, λ̄₁}` lives in `𝒮₄`
  have hleC : hyp.H0Cprime
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief := by
    change hyp.chief.H0 ⊔ derivedInG hyp.C ≤ _
    refine sup_le_sup_left ?_ hyp.chief.H0
    rw [C_eq_cSub_of_noncoherent hG hyp hncH0C htype]
    exact OddOrder.Peterfalvi.S11.cprimeSub_le_C hyp.s11Setup hyp.chief
  have hS4sub : nineElevenSFour hyp S₂
      ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂ := fun ξ hξ =>
    ⟨OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup hleC hξ.1, hξ.2.2⟩
  have hlam₁S₃ : lam₁ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂ :=
    hS4sub ⟨hlam₁sOfC, hlam₁irr, hlam₁nS₂⟩
  have hlam₁c_S₄ : lam₁.conj ∈ nineElevenSFour hyp S₂ := by
    refine ⟨OddOrder.Peterfalvi.S11.sOf_closedUnderConjugate hyp.s11Setup _ hlam₁sOfC,
      hlam₁irr.conj, ?_⟩
    intro hmem
    apply hlam₁nS₂
    have h := hS₂conj hmem
    rwa [ClassFunction.conj_conj] at h
  have hlam₁cS₃ : lam₁.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂ :=
    hS4sub hlam₁c_S₄
  have hlam₁ne : lam₁ ≠ lam₁.conj := fun h =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd _
      (hIKF hlam₁S₃.1) h.symm
  have hlam₁deg : (lam₁ : ↥M → ℂ) 1 = ((hyp.s11Setup.q
      * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℂ) :=
    hS3deg lam₁ hlam₁S₃
  -- ── `e ≥ 2`: `u ≠ a` since a degree-`qa` irreducible member would lie in `𝒮₁ ⊆ 𝒮₂`
  have hune : (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u ≠ caseA.a := by
    intro huea
    apply hlam₁nS₂
    apply hS₁sub
    refine ⟨hlam₁S₃.1, hlam₁irr, ?_⟩
    rw [hlam₁deg, huea]
  have he2 : 2 ≤ e := by
    have ha1 : 1 ≤ caseA.a := caseA.a_pos
    rcases Nat.lt_or_ge e 2 with h | h
    · exfalso
      interval_cases e
      · rw [zero_mul] at hue
        omega
      · rw [one_mul] at hue
        exact hune hue.symm
    · exact h
  -- ── `|𝒮₂| = 2e` from the (9.8.d) count at the equality configuration
  have hS₂eq : S₂ = {φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
      (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
      IsIrreducibleCharacter φ ∧
      φ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)} := by
    refine Set.Subset.antisymm hS₂cut ?_
    have hCUle : hyp.C ≤ hyp.s11Setup.U := by
      change hyp.C ≤ hyp.s11Setup.typeP.U
      rw [hyp.setup_typeP_eq]; exact hyp.C_le_U
    have hleU' : hyp.H0Cprime
        ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup := by
      change hyp.chief.H0 ⊔ derivedInG hyp.C
        ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup
      refine sup_le_sup_left ?_ hyp.chief.H0
      change derivedInG hyp.C ≤ derivedInG hyp.s11Setup.U
      rw [OddOrder.Peterfalvi.S11.derivedInG_eq_commutator hyp.C,
        OddOrder.Peterfalvi.S11.derivedInG_eq_commutator hyp.s11Setup.U]
      exact Subgroup.commutator_mono hCUle hCUle
    exact fun φ hφ =>
      hS₁sub ⟨OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup hleU' hφ.1, hφ.2.1, hφ.2.2⟩
  have hcardS₂ : hS₂fin.toFinset.card = 2 * e := by
    have hrelu : (OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U
        = (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u := by
      have hUpC : OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief
          = OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup := hCUprime
      rw [← hUpC]
      exact OddOrder.Peterfalvi.S11.relIndex_cSub_U_eq_u _
    have hcount' : S₂.ncard * (caseA.a * caseA.a) = 2 * e * (caseA.a * caseA.a) := by
      rw [hS₂eq, hcount, hrelu, ← h2a, ← hue]
      ring
    have ha0 : 0 < caseA.a * caseA.a := Nat.mul_pos caseA.a_pos caseA.a_pos
    have hncard : S₂.ncard = 2 * e := Nat.eq_of_mul_eq_mul_right ha0 hcount'
    rw [← Set.ncard_eq_toFinset_card _ hS₂fin]
    exact hncard
  -- ── orthonormality of the source families
  have hON1 : ∀ φ ∈ S₂, ClassFunction.inner φ φ = 1 := fun φ hφ =>
    hselfone (hS₂cut hφ).2.1
  have hON2 : ∀ φ ∈ S₂, ∀ ξ ∈ S₂, φ ≠ ξ → ClassFunction.inner φ ξ = 0 :=
    fun φ hφ ξ hξ hne =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF (hS₂sub hφ)) (hIKF (hS₂sub hξ)) hne
  -- ── `𝒮₃` is conjugation-closed; cross-orthogonality of the coherent images
  have hS₃sub : OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂
      ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime := Set.sdiff_subset
  have hS₃conj : ∀ x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      x.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂ := by
    intro x hx
    refine ⟨OddOrder.Peterfalvi.S11.sOf_closedUnderConjugate hyp.s11Setup hyp.H0Cprime hx.1, ?_⟩
    intro hcmem
    apply hx.2
    have h := hS₂conj hcmem
    rwa [ClassFunction.conj_conj] at h
  have hcross : ∀ φ ∈ S₂,
      ∀ lam ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      ClassFunction.inner (c₁.extension φ) (c₃.extension lam) = 0 := by
    intro φ hφ lam hlam
    exact coherent_extension_cross_orthogonal hG hyp hS₂sub hS₃sub c₁ c₃
      hφ (hS₂conj hφ) hlam (hS₃conj lam hlam)
      (fun h => hlam.2 (h ▸ hφ)) (fun h => (hS₃conj lam hlam).2 (h ▸ hφ))
  -- ── `β = λ₁ − e·ψ₁`: support, integrality, `τ`-image
  have hβdegℂ : (lam₁ : ↥M → ℂ) 1 = ((e : ℕ) : ℂ) * (ψ₁ : ↥M → ℂ) 1 := by
    rw [hlam₁deg, hψ₁deg, ← hue]
    push_cast
    ring
  have hβsupp : ((lam₁ - e • ψ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support
      hyp.base.mderivSharp_subset_A0 (hIKF hlam₁S₃.1) (hIKF hψ₁sOf) hβdegℂ
  have hβsmul : (lam₁ - e • ψ₁ : ClassFunction ↥M ℂ) = lam₁ - ((e : ℕ) : ℂ) • ψ₁ := by
    rw [Nat.cast_smul_eq_nsmul]
  have hβZIrr : (lam₁ - e • ψ₁ : ClassFunction ↥M ℂ) ∈ ZIrr ↥M :=
    Submodule.sub_mem _
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hlam₁S₃.1))
      (nsmul_mem (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hψ₁sOf)) e)
  have hτβZ : hyp.base.tau (lam₁ - e • ψ₁) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.base.dadeData.dade hyp.base.hconj hβsupp hβZIrr
  have hαZIrr : (γ - ψ₁ : ClassFunction ↥M ℂ) ∈ ZIrr ↥M :=
    Submodule.sub_mem _ hγZIrr
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hψ₁sOf))
  have hταZ : hyp.base.tau (γ - ψ₁) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.base.dadeData.dade hyp.base.hconj hαsupp hαZIrr
  -- ── supported differences and their `τ₁`/`τ₃` images
  have hψdiffsupp : ∀ φ ∈ S₂,
      ((φ - ψ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := by
    intro φ hφ
    have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support
      hyp.base.mderivSharp_subset_A0 (hIKF (hS₂sub hφ)) (hIKF hψ₁sOf) (d := 1)
      (by rw [Nat.cast_one, one_mul, hS2deg φ hφ, hψ₁deg])
    rwa [one_smul] at h
  have hτ₁diff : ∀ φ ∈ S₂,
      hyp.base.tau (φ - ψ₁) = c₁.extension φ - c₁.extension ψ₁ := by
    intro φ hφ
    rw [← map_sub]
    exact (c₁.extends_on_supported (φ - ψ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hφ) (Submodule.subset_span hψ₁S₂),
        hψdiffsupp φ hφ⟩).symm
  have hDsupp : ((lam₁ - lam₁.conj : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := by
    rw [show (lam₁ - lam₁.conj : ClassFunction ↥M ℂ) = -(lam₁.conj - lam₁) from by abel,
      ClassFunction.support_neg]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 (hIKF hlam₁S₃.1)
  have hτD : hyp.base.tau (lam₁ - lam₁.conj)
      = c₃.extension lam₁ - c₃.extension lam₁.conj := by
    rw [← map_sub]
    exact (c₃.extends_on_supported (lam₁ - lam₁.conj)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hlam₁S₃)
        (Submodule.subset_span hlam₁cS₃), hDsupp⟩).symm
  -- ── scalar values at the source
  have hll1 : ClassFunction.inner lam₁ lam₁ = 1 := hselfone hlam₁irr
  have hlclc : ClassFunction.inner lam₁.conj lam₁.conj = 1 := hselfone hlam₁irr.conj
  have hllc : ClassFunction.inner lam₁ lam₁.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF hlam₁S₃.1) (hIKF hlam₁cS₃.1) hlam₁ne
  have hψψ : ClassFunction.inner ψ₁ ψ₁ = 1 := hON1 ψ₁ hψ₁S₂
  have hψl : ClassFunction.inner ψ₁ lam₁ = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF hψ₁sOf) (hIKF hlam₁S₃.1) (fun h => hlam₁nS₂ (h ▸ hψ₁S₂))
  have hψlc : ClassFunction.inner ψ₁ lam₁.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF hψ₁sOf) (hIKF hlam₁cS₃.1) (fun h => hlam₁cS₃.2 (h ▸ hψ₁S₂))
  have hlψ : ClassFunction.inner lam₁ ψ₁ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ₁ lam₁, hψl, star_zero]
  have hlcψ : ClassFunction.inner lam₁.conj ψ₁ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ₁ lam₁.conj, hψlc, star_zero]
  have hlcl : ClassFunction.inner lam₁.conj lam₁ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm lam₁ lam₁.conj, hllc, star_zero]
  -- ── the budget inputs
  have hS4fin : (nineElevenSFour hyp S₂).Finite :=
    hSfin.subset (fun ξ hξ => (hS4sub hξ).1)
  have hτβnorm : ClassFunction.inner (hyp.base.tau (lam₁ - e • ψ₁))
      (hyp.base.tau (lam₁ - e • ψ₁)) = ((e : ℕ) : ℂ) ^ 2 + 1 := by
    rw [hyp.base.tau_inner_eq_of_supported hβsupp hβsupp, hβsmul]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hll1, hlψ, hψl, hψψ, star_natCast, mul_zero, mul_one, sub_zero, zero_sub]
    ring
  have hτβconst : ∀ φ ∈ hS₂fin.toFinset, φ ≠ ψ₁ →
      ClassFunction.inner (hyp.base.tau (lam₁ - e • ψ₁)) (c₁.extension φ)
        = ClassFunction.inner (hyp.base.tau (lam₁ - e • ψ₁)) (c₁.extension ψ₁)
          + ((e : ℕ) : ℂ) := by
    intro φ hφF hφne
    have hφ := hS₂fin.mem_toFinset.mp hφF
    have hβφ : ClassFunction.inner (lam₁ - e • ψ₁ : ClassFunction ↥M ℂ) (φ - ψ₁)
        = ((e : ℕ) : ℂ) := by
      rw [hβsmul]
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, hlψ, hψψ,
        hON2 ψ₁ hψ₁S₂ φ hφ (fun h => hφne h.symm),
        show ClassFunction.inner lam₁ φ = 0 from by
          rw [OddOrder.RepresentationTheory.inner_conj_symm φ lam₁,
            OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
              (hIKF (hS₂sub hφ)) (hIKF hlam₁S₃.1) (fun h => hlam₁nS₂ (h ▸ hφ)),
            star_zero],
        mul_zero, mul_one, sub_zero, zero_sub, sub_neg_eq_add, zero_add]
    have hiso := hyp.base.tau_inner_eq_of_supported hβsupp (hψdiffsupp φ hφ)
    rw [hτ₁diff φ hφ, ClassFunction.inner_sub_right, hβφ] at hiso
    linear_combination hiso
  have hτβD : ClassFunction.inner (hyp.base.tau (lam₁ - e • ψ₁)) (c₃.extension lam₁)
      - ClassFunction.inner (hyp.base.tau (lam₁ - e • ψ₁)) (c₃.extension lam₁.conj)
        = 1 := by
    have hβD : ClassFunction.inner (lam₁ - e • ψ₁ : ClassFunction ↥M ℂ)
        (lam₁ - lam₁.conj) = 1 := by
      rw [hβsmul]
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, hll1, hllc, hψl, hψlc, mul_zero, sub_zero]
    have hiso := hyp.base.tau_inner_eq_of_supported hβsupp hDsupp
    rw [hτD, ClassFunction.inner_sub_right, hβD] at hiso
    exact hiso
  have hτατβ : ClassFunction.inner (hyp.base.tau (γ - ψ₁))
      (hyp.base.tau (lam₁ - e • ψ₁)) = ((e : ℕ) : ℂ) := by
    rw [hyp.base.tau_inner_eq_of_supported hαsupp hβsupp, hβsmul]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      OddOrder.RepresentationTheory.inner_smul_right, hγorth lam₁ hlam₁S₃.1,
      hγorth ψ₁ hψ₁sOf, hψl, hψψ, star_natCast, mul_zero, mul_one, zero_sub, sub_zero,
      sub_neg_eq_add, zero_add]
  have hταconst : ∀ φ ∈ hS₂fin.toFinset, φ ≠ ψ₁ →
      ClassFunction.inner (hyp.base.tau (γ - ψ₁)) (c₁.extension φ)
        = ClassFunction.inner (hyp.base.tau (γ - ψ₁)) (c₁.extension ψ₁) + 1 := by
    intro φ hφF hφne
    have hφ := hS₂fin.mem_toFinset.mp hφF
    have hαφ : ClassFunction.inner (γ - ψ₁ : ClassFunction ↥M ℂ) (φ - ψ₁) = 1 := by
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        hγorth φ (hS₂sub hφ), hγorth ψ₁ hψ₁sOf, hψψ,
        hON2 ψ₁ hψ₁S₂ φ hφ (fun h => hφne h.symm), zero_sub, sub_neg_eq_add,
        zero_add, sub_self]
    have hiso := hyp.base.tau_inner_eq_of_supported hαsupp (hψdiffsupp φ hφ)
    rw [hτ₁diff φ hφ, ClassFunction.inner_sub_right, hαφ] at hiso
    linear_combination hiso
  -- ── run the projection budget
  obtain ⟨Γ0, hΓZ, hΓ1, hθ₁Γ, hΓD, hTBeq⟩ :=
    OddOrder.Peterfalvi.S07.exists_bridge_target_of_budget (Γ' := G)
      (SF := hS₂fin.toFinset) (S4F := hS4fin.toFinset)
      (fun φ => c₁.extension φ) (fun ξ => c₃.extension ξ)
      (TB := hyp.base.tau (lam₁ - e • ψ₁)) (TA := hyp.base.tau (γ - ψ₁))
      (ψ₁ := ψ₁) (l₁ := lam₁) (l₂ := lam₁.conj) (e := e)
      (hS₂fin.mem_toFinset.mpr hψ₁S₂)
      (hS4fin.mem_toFinset.mpr ⟨hlam₁sOfC, hlam₁irr, hlam₁nS₂⟩)
      (hS4fin.mem_toFinset.mpr hlam₁c_S₄)
      he2 hcardS₂
      (by
        intro φ hφF ξ hξF
        have hφ := hS₂fin.mem_toFinset.mp hφF
        have hξ := hS₂fin.mem_toFinset.mp hξF
        rw [c₁.extension_inner_eq φ ξ (Submodule.subset_span hφ)
          (Submodule.subset_span hξ)]
        by_cases h : φ = ξ
        · subst h; rw [if_pos rfl]; exact hON1 φ hφ
        · rw [if_neg h]; exact hON2 φ hφ ξ hξ h)
      (by
        intro ξ hξF ξ' hξ'F
        have hξ := hS4sub (hS4fin.mem_toFinset.mp hξF)
        have hξ' := hS4sub (hS4fin.mem_toFinset.mp hξ'F)
        rw [c₃.extension_inner_eq ξ ξ' (Submodule.subset_span hξ)
          (Submodule.subset_span hξ')]
        by_cases h : ξ = ξ'
        · subst h
          rw [if_pos rfl]
          exact hselfone (hS4fin.mem_toFinset.mp hξF).2.1
        · rw [if_neg h]
          exact OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
            (hIKF hξ.1) (hIKF hξ'.1) h)
      (fun φ hφF ξ hξF => hcross φ (hS₂fin.mem_toFinset.mp hφF)
        ξ (hS4sub (hS4fin.mem_toFinset.mp hξF)))
      (fun ξ hξF => c₃.extension_mem_ZIrr ξ
        (Submodule.subset_span (hS4sub (hS4fin.mem_toFinset.mp hξF))))
      (fun φ hφF => c₁.extension_mem_ZIrr φ
        (Submodule.subset_span (hS₂fin.mem_toFinset.mp hφF)))
      hτβZ hτβnorm hτβconst hτβD hτατβ
      (fun ξ hξF => hc ξ (hS4sub (hS4fin.mem_toFinset.mp hξF)))
      hταconst
      (ClassFunction.inner_mem_ZIrr_int hταZ
        (c₁.extension_mem_ZIrr ψ₁ (Submodule.subset_span hψ₁S₂)))
      (ClassFunction.inner_mem_ZIrr_int hτβZ
        (c₁.extension_mem_ZIrr ψ₁ (Submodule.subset_span hψ₁S₂)))
      (fun ξ hξF => ClassFunction.inner_mem_ZIrr_int hτβZ
        (c₃.extension_mem_ZIrr ξ
          (Submodule.subset_span (hS4sub (hS4fin.mem_toFinset.mp hξF)))))
  -- ── the pair targets `X = Γ0`, `Xc = Γ0 − (λ₁ − λ̄₁)^τ`
  have hΓτD : ClassFunction.inner Γ0 (hyp.base.tau (lam₁ - lam₁.conj)) = 1 := by
    rw [hτD, ClassFunction.inner_sub_right, hΓD]
  have hτDΓ : ClassFunction.inner (hyp.base.tau (lam₁ - lam₁.conj)) Γ0 = 1 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm Γ0
      (hyp.base.tau (lam₁ - lam₁.conj)), hΓτD, star_one]
  have hτDτD : ClassFunction.inner (hyp.base.tau (lam₁ - lam₁.conj))
      (hyp.base.tau (lam₁ - lam₁.conj)) = 2 := by
    rw [hyp.base.tau_inner_eq_of_supported hDsupp hDsupp]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      hll1, hllc, hlcl, hlclc, sub_zero, zero_sub, sub_neg_eq_add]
    norm_num
  have hτDZ : hyp.base.tau (lam₁ - lam₁.conj) ∈ ZIrr G := by
    rw [hτD]
    exact Submodule.sub_mem _
      (c₃.extension_mem_ZIrr lam₁ (Submodule.subset_span hlam₁S₃))
      (c₃.extension_mem_ZIrr lam₁.conj (Submodule.subset_span hlam₁cS₃))
  -- ── adjoin the pair `{λ₁, λ̄₁}` coherently to `𝒮₂` (the (5.6.3) union-pair extension)
  have hunion : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (S₂ ∪ {lam₁, lam₁.conj}) hyp.base.A0 := by
    refine OddOrder.Peterfalvi.S07.isCoherent_union_pair_of_bridge (E := ((e : ℕ) : ℤ))
      hS₂fin hON1 hON2
      (fun φ hφ ξ hξ => c₁.extension_inner_eq φ ξ (Submodule.subset_span hφ)
        (Submodule.subset_span hξ))
      (fun φ hφ => c₁.extends_on_supported φ hφ)
      (fun φ hφ => c₁.extension_mem_ZIrr φ (Submodule.subset_span hφ))
      hlam₁ne hll1 hlclc hllc
      (fun φ hφ => OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF (hS₂sub hφ)) (hIKF hlam₁S₃.1) (fun h => hlam₁nS₂ (h ▸ hφ)))
      (fun φ hφ => OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF (hS₂sub hφ)) (hIKF hlam₁cS₃.1) (fun h => hlam₁cS₃.2 (h ▸ hφ)))
      hΓ1 ?_ ?_ hΓZ
      (Submodule.sub_mem _ hΓZ hτDZ)
      (fun φ hφ => hθ₁Γ φ (hS₂fin.mem_toFinset.mpr hφ)) ?_ ?_ hDsupp hψ₁S₂ ?_ ?_
    · -- `‖Xc‖² = 1`
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, hΓ1, hΓτD, hτDΓ, hτDτD]
      norm_num
    · -- `⟨X, Xc⟩ = 0`
      rw [ClassFunction.inner_sub_right, hΓ1, hΓτD]
      norm_num
    · -- `τ₁𝒮₂ ⊥ Xc`
      intro φ hφ
      rw [ClassFunction.inner_sub_right, hθ₁Γ φ (hS₂fin.mem_toFinset.mpr hφ), hτD,
        ClassFunction.inner_sub_right,
        hcross φ hφ lam₁ hlam₁S₃, hcross φ hφ lam₁.conj hlam₁cS₃]
      norm_num
    · -- `(λ₁ − λ̄₁)^τ = X − Xc`
      exact (sub_sub_cancel Γ0 (hyp.base.tau (lam₁ - lam₁.conj))).symm
    · -- the bridge `(λ₁ − e·ψ₁)^τ = X − e·τ₁ψ₁` (`ℤ`-scalar form)
      show hyp.base.tau (lam₁ - ((e : ℕ) : ℤ) • ψ₁)
        = Γ0 - ((e : ℕ) : ℤ) • c₁.extension ψ₁
      simp only [natCast_zsmul]
      rw [← Nat.cast_smul_eq_nsmul ℂ e (c₁.extension ψ₁)]
      exact hTBeq
    · -- the bridge support (`ℤ`-scalar form)
      show ((lam₁ - ((e : ℕ) : ℤ) • ψ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0
      simp only [natCast_zsmul]
      exact hβsupp
  exact hpairs lam₁ hlam₁S₃ ⟨hunion⟩

end Discharge

end OddOrder.Peterfalvi.S13
