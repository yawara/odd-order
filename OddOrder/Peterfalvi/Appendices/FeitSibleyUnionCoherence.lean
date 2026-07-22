/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyEndgame

/-!
# Peterfalvi Appendix IV: the (6) union coherence assembly (p. 148)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix IV, p. 148 (campaign issue 1054, step (6)).  With the endgame notation
`(4)` set up — two disjoint coherent families `X = 𝒳` (anchor `χ₁`, `p`-power
degree ratios) and `Y = 𝒴 = 𝒮(Q')` (anchor `η₁`, uniform degree `d`) inside
`𝒮`, and the keystone difference `χ₁ − a·η₁` supported — Peterfalvi's step (6)
shows that **`a ∣ λ` implies `X ∪ Y` is coherent**.

This file assembles the three witness constructions of the endgame into the
single member-assignment coherence `isCoherent_of_memberAssignment`:

* `exists_lambda_norm_identity` produces the coefficient `λ` and the norm
  identity `1 + a² = (v,v) + (λ−a)² + (m−1)λ²`;
* `exists_normalized_witness_of_dvd` (consuming `a ∣ λ`) produces the
  `𝒴`-witnesses `w` with `w η − w η₁ = τ(η − η₁)` (P1-Y), orthonormal `±Irr`
  values (P2), and the keystone pairings `(u, w η) = 0`, `(u, w η₁) = −a` (P3);
* `exists_X_witness_assignment` (consuming P2/P3 of `w`) produces the
  `𝒳`-witnesses `wX` with `wX χ' − a'·wX χ₁ = τ(χ' − a'·χ₁)` (P1-X) and the
  keystone `wX χ₁ − a·w η₁ = τ(χ₁ − a·η₁)` (P4).

The combined assignment `W = wX` on `X`, `= w` on `Y` is orthonormal `ℤ[Irr G]`-
valued, and every member has a supported difference to the common anchor `η₁`
(`η` for `η ∈ Y`; `χ − a_χ·a·η₁ = (χ − a_χ·χ₁) + a_χ·(χ₁ − a·η₁)` for `χ ∈ X`)
on which `W` matches `τ` — exactly the input of `isCoherent_of_memberAssignment`.
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

open scoped commutatorElement

namespace Hypothesis

variable {G : Type*} [Group G] (hyp : Hypothesis G)

section Coherence

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
variable [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]

/-- **Peterfalvi (6): `a ∣ λ ⟹ 𝒳 ∪ 𝒴 coherent`** (p. 148).

Given the endgame `(4)` data — disjoint coherent families `X, Y ⊆ 𝒮` with
anchors `χ₁ ∈ X`, `η₁ ∈ Y`, integral degree differences `φ − a_φ·χ₁` (`X`) and
`ψ − η₁` (`Y`) supported, the supported keystone `χ₁ − a·η₁` (`a ≥ 2`), and the
`(6)` norm-identity coefficient `λ` — the divisibility `a ∣ λ` (proved in (8))
makes `X ∪ Y` coherent.  The three witness families are stitched into a single
orthonormal `ℤ[Irr G]`-valued assignment and fed to
`isCoherent_of_memberAssignment`. -/
noncomputable def union_coherent_of_lambda_dvd [Finite G]
    {X Y : Set (ClassFunction ↥hyp.H ℂ)}
    (hXS : X ⊆ hyp.Sset) (hYS : Y ⊆ hyp.Sset) (hdisj : ∀ φ ∈ X, φ ∉ Y)
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau X hyp.A)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ₁ : ClassFunction ↥hyp.H ℂ} (hχ₁X : χ₁ ∈ X)
    (hXdiff : ∀ φ ∈ X, ∃ b : ℕ, 0 < b ∧
      φ - b • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A)
    {χ₂ : ClassFunction ↥hyp.H ℂ} (hχ₂X : χ₂ ∈ X) (hχ₂ne : χ₂ ≠ χ₁)
    {η₁ : ClassFunction ↥hyp.H ℂ} (hη₁Y : η₁ ∈ Y)
    (hYdiff : ∀ ψ ∈ Y, ψ - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      Y hyp.A)
    {η₂ : ClassFunction ↥hyp.H ℂ} (hη₂Y : η₂ ∈ Y) (hη₂ne : η₂ ≠ η₁)
    {a : ℕ} (ha : 2 ≤ a) (hm : 2 ≤ Y.ncard)
    (hsupp : χ₁ - a • η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      hyp.Sset hyp.A)
    {lam : ℤ}
    (hlam_ne : ∀ η ∈ Y, η ≠ η₁ →
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hcohY.extension η) = (lam : ℂ))
    (hlam_1 : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hcohY.extension η₁) =
      (lam : ℂ) - a)
    {nvv : ℤ} (hnvv : 0 ≤ nvv)
    (hident : 1 + (a : ℤ) ^ 2 = nvv + (lam - a) ^ 2 + ((Y.ncard : ℤ) - 1) * lam ^ 2)
    (hdvd : (a : ℤ) ∣ lam) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (X ∪ Y) hyp.A := by
  classical
  -- **the two witness families** — `IsCoherent` is data-valued, so the existential
  -- witnesses are pulled out by `Classical.choose` (their `Prop` specs may still be
  -- `obtain`-destructured, since `And` eliminates into `Type`).
  have hwex := hyp.exists_normalized_witness_of_dvd hYS hcohY hη₁Y hYdiff ha hm hlam_ne hlam_1
    hnvv hident hdvd
  have hwspec := hwex.choose_spec
  set w : ClassFunction ↥hyp.H ℂ → ClassFunction G ℂ := hwex.choose with hwdef
  obtain ⟨hwP1, hwP2a, hwnorm, hworth, hwu_ne, hwu_1⟩ := hwspec
  have hwXex := hyp.exists_X_witness_assignment hXS hYS hdisj hcohX hcohY hχ₁X hXdiff hχ₂X hχ₂ne
    hη₁Y hYdiff hη₂Y hη₂ne hsupp hwP2a hwnorm hworth hwu_ne hwu_1
  have hwXspec := hwXex.choose_spec
  set wX : ClassFunction ↥hyp.H ℂ → ClassFunction G ℂ := hwXex.choose with hwXdef
  obtain ⟨hwXZIrr, hwXnorm, hwXorth, hwXcross, hwXdiff, hwXkey⟩ := hwXspec
  -- **the combined assignment** `W`
  set W : ClassFunction ↥hyp.H ℂ → ClassFunction G ℂ :=
    fun μ => if μ ∈ X then wX μ else w μ with hWdef
  have hWX : ∀ μ ∈ X, W μ = wX μ := fun μ hμ => if_pos hμ
  have hWY : ∀ μ ∈ Y, W μ = w μ := fun μ hμ => if_neg (fun h => hdisj μ h hμ)
  have hWanchor : W η₁ = w η₁ := hWY η₁ hη₁Y
  -- membership and orthonormality of the members
  have hSset : ∀ μ ∈ X ∪ Y, μ ∈ hyp.Sset := by
    intro μ hμ
    rcases hμ with h | h
    · exact hXS h
    · exact hYS h
  have hnorm : ∀ μ ∈ X ∪ Y, ClassFunction.inner μ μ = 1 :=
    fun μ hμ => ((hSset μ hμ).1).inner_self_eq_one
  have horth : ∀ μ ∈ X ∪ Y, ∀ ν ∈ X ∪ Y, μ ≠ ν → ClassFunction.inner μ ν = 0 :=
    fun μ hμ ν hν hne => hyp.Sset_pairwiseOrthogonal (hSset μ hμ) (hSset ν hν) hne
  -- orthonormality and `ZIrr` of `W`
  have hWZIrr : ∀ μ ∈ X ∪ Y, W μ ∈ ZIrr G := by
    intro μ hμ
    rcases hμ with hμX | hμY
    · rw [hWX μ hμX]; exact hwXZIrr μ hμX
    · rw [hWY μ hμY]
      obtain ⟨η', hη'Y, sgn, -, hws⟩ := hwP2a μ hμY
      rw [hws]
      exact Submodule.smul_mem _ _
        (hcohY.extension_mem_ZIrr η' (Submodule.subset_span hη'Y))
  have hWnorm : ∀ μ ∈ X ∪ Y, ClassFunction.inner (W μ) (W μ) = 1 := by
    intro μ hμ
    rcases hμ with hμX | hμY
    · rw [hWX μ hμX]; exact hwXnorm μ hμX
    · rw [hWY μ hμY]; exact hwnorm μ hμY
  have hWorth : ∀ μ ∈ X ∪ Y, ∀ ν ∈ X ∪ Y, μ ≠ ν →
      ClassFunction.inner (W μ) (W ν) = 0 := by
    intro μ hμ ν hν hne
    rcases hμ with hμX | hμY <;> rcases hν with hνX | hνY
    · rw [hWX μ hμX, hWX ν hνX]; exact hwXorth μ hμX ν hνX hne
    · rw [hWX μ hμX, hWY ν hνY]; exact hwXcross μ hμX ν hνY
    · rw [hWY μ hμY, hWX ν hνX, OddOrder.RepresentationTheory.inner_conj_symm,
        hwXcross ν hνX μ hμY, star_zero]
    · rw [hWY μ hμY, hWY ν hνY]; exact hworth μ hμY ν hνY hne
  -- the anchor `η₁` is nonzero at `1`
  have hanchor_one : η₁ (1 : ↥hyp.H) ≠ 0 := by
    obtain ⟨d, hdpos, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨η₁, (hYS hη₁Y).1⟩ : IrreducibleCharacter ↥hyp.H)
    rw [show ((⟨η₁, (hYS hη₁Y).1⟩ : IrreducibleCharacter ↥hyp.H) :
      ClassFunction ↥hyp.H ℂ) = η₁ from rfl] at hd
    rw [hd]; exact_mod_cast hdpos.ne'
  -- the keystone difference lives in the union lattice
  have hkey_supp : χ₁ - a • η₁ ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) (X ∪ Y) hyp.A := by
    refine ⟨Submodule.sub_mem _ (Submodule.subset_span (Set.mem_union_left _ hχ₁X)) ?_,
      hsupp.2⟩
    rw [← Nat.cast_smul_eq_nsmul ℤ a η₁]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_union_right _ hη₁Y))
  -- **the supported differences to the common anchor** `η₁`
  have hdiff : ∀ μ ∈ X ∪ Y, ∃ b : ℕ,
      μ - b • η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) (X ∪ Y) hyp.A ∧
      W μ - (b : ℂ) • W η₁ = hyp.tau (μ - b • η₁) := by
    intro μ hμ
    rcases hμ with hμX | hμY
    · -- `μ ∈ X`: `b = a_μ · a`
      obtain ⟨aμ, haμpos, haμsupp⟩ := hXdiff μ hμX
      have heq : μ - (aμ * a) • η₁ = (μ - aμ • χ₁) + aμ • (χ₁ - a • η₁) := by
        rw [smul_sub, ← smul_smul]; abel
      refine ⟨aμ * a, ?_, ?_⟩
      · rw [heq]
        refine OddOrder.Peterfalvi.S07.add_mem_zSupportedSpan
          (OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left Set.subset_union_left haμsupp) ?_
        rw [← Nat.cast_smul_eq_nsmul ℤ aμ (χ₁ - a • η₁)]
        exact zsmul_mem_zSupportedSpan hkey_supp (aμ : ℤ)
      · rw [hWX μ hμX, hWanchor, heq, map_add, map_nsmul, ← hwXdiff μ hμX aμ haμsupp, ← hwXkey,
          ← Nat.cast_smul_eq_nsmul ℂ aμ (wX χ₁ - (a : ℂ) • w η₁)]
        push_cast
        module
    · -- `μ ∈ Y`: `b = 1`
      refine ⟨1, ?_, ?_⟩
      · rw [one_nsmul]
        exact OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left Set.subset_union_right
          (hYdiff μ hμY)
      · rw [hWY μ hμY, hWanchor, Nat.cast_one, one_smul, one_nsmul, hwP1 μ hμY]
  -- **assemble**
  have hUfin : (X ∪ Y).Finite := hyp.Sset_finite.subset (Set.union_subset hXS hYS)
  exact isCoherent_of_memberAssignment (W := W) (s := hUfin.toFinset)
    (fun {μ} => Set.Finite.mem_toFinset hUfin) hnorm horth hWnorm hWorth hWZIrr
    (Set.mem_union_right _ hη₁Y) hanchor_one hyp.one_notMem_A hdiff
    ⟨η₂ - η₁, OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left Set.subset_union_right
      (hYdiff η₂ hη₂Y), sub_ne_zero.mpr hη₂ne⟩

end Coherence

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
