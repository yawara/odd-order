/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_DegreeSums

/-!
# Peterfalvi §8: Sibley bounds and X-set coherence

Sibley arithmetic bounds and the X-set coherence construction split under issue 0073.
-/
namespace OddOrder.Peterfalvi.S08
open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis
variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]


open scoped Classical in
/-- **(6.8.1) regular-character difference value over `X(Z)`** (mmd 04.8 L168, combined form).  For
the central `(6.6)` set `X(Z)` and `z ∈ Z^#`, `∑_{χ ∈ X(Z)} χ(1)·(χ(z) − χ(1)) = -|L|`.  This is
`(ρ_L − ρ_{L/Z})(z) − (ρ_L − ρ_{L/Z})(1) = -|L:Z| − (|L| − |L:Z|) = -|L|` (the off-identity minus
the
degree value), which divided by `a|W₁| = χ₁(1)` gives `∑dᵢχᵢ(z) − ∑dᵢχᵢ(1) = -|H|/a` — the key
constant in showing `η₁^{τ₁}` is constant on `Z^#`. -/
theorem sum_degree_mul_charValue_sub_Xset_eq_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    {T : Finset (ClassFunction ↥L ℂ)} (hT : ∀ φ, φ ∈ T ↔ φ ∈ hyp.Xset Z)
    {z : ↥L} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    ∑ φ ∈ T, (φ 1) * (φ z - φ 1) = -(Nat.card ↥L : ℂ) := by
  have hexpand : ∑ φ ∈ T, (φ 1) * (φ z - φ 1)
      = (∑ φ ∈ T, (φ 1) * φ z) - (∑ φ ∈ T, (φ 1) * φ 1) := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun φ _ => ?_); ring
  rw [hexpand, hyp.sum_degree_mul_charValue_Xset_eq_of_frobenius hF hZH hT hz hz1,
    hyp.sum_degree_sq_Xset_eq_of_frobenius hF hZH hT]
  ring

/-- **(6.6) `htotal` factorization.**  `|L:H|·(|H| − |H:Z|) = |H:Z| · (|L:H|·(|Z| − 1))` (Lagrange
`|H| = |H:Z|·|Z|`).  With the X degree-sum `total = |L:H|·(|H| − |H:Z|)` (`sum_re_sq_Xset_eq`), this
is the `total = qtot · c` of the X-chain step data with `qtot = |H:Z|`, `c = |L:H|·(|Z| − 1)`. -/
theorem index_mul_card_sub_factor (_hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L} [Z.Normal] :
    H.index * (Nat.card ↥H - Nat.card (↥H ⧸ Z.subgroupOf H))
      = Nat.card (↥H ⧸ Z.subgroupOf H) * (H.index * (Nat.card ↥(Z.subgroupOf H) - 1)) := by
  have hlag : Nat.card ↥H
      = Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf H)
  have hz : 1 ≤ Nat.card ↥(Z.subgroupOf H) := Nat.card_pos
  obtain ⟨w, hw⟩ : ∃ w, Nat.card ↥(Z.subgroupOf H) = w + 1 := ⟨_, (Nat.sub_add_cancel hz).symm⟩
  rw [hlag, hw]
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
  ring

/-- **(6.8.3) arithmetic core.**  The numeric contradiction closing the (6.8.3) extension in case
(A).  From the break-pair (5.6) bound `∑_{χ∈X} χ(1)² < 2ψ(1)η₁(1)` — i.e.
`|W₁|·|H:Z|·(|Z|−1) < 2·|W₁|²·d` with `ψ(1) = |W₁|d`, `η₁(1) = |W₁|` — together with [Is] Cor 2.30
`d² ≤ |H:Z|` (valid since `Z` is central) and the fixed-point-free bound `|Z|−1 ≥ 2|W₁|`
(`W₁` acts FPF on the odd-order `Z`), one derives `|H:Z| < d ≤ d² ≤ |H:Z|`, a contradiction.

Here `w1 = |W₁|`, `d = θ(1)` (the degree of the `H`-source of `ψ`), `hZ = |H:Z|`, `cZ = |Z|`.
The hypothesis `2 ≤ hZ` holds because `Z ⊆ H′ ⊊ H` (`H` non-abelian), so `|H:Z| ≥ |H:H′| ≥ 2`. -/
theorem false_of_centralCommutator_break_arith {w1 d hZ cZ : ℕ}
    (hw1 : 1 ≤ w1) (hd : 1 ≤ d) (hdsq : d ^ 2 ≤ hZ) (hZ2 : 2 ≤ hZ)
    (hfpf : 2 * w1 ≤ cZ - 1)
    (hbreak : w1 * hZ * (cZ - 1) ≤ 2 * w1 ^ 2 * d) : False := by
  set m := cZ - 1 with hm
  have hge : 2 * w1 ^ 2 * hZ ≤ w1 * hZ * m := by
    calc 2 * w1 ^ 2 * hZ = w1 * hZ * (2 * w1) := by ring
      _ ≤ w1 * hZ * m := mul_le_mul_right hfpf (w1 * hZ)
  have hle : 2 * w1 ^ 2 * hZ ≤ 2 * w1 ^ 2 * d := le_trans hge hbreak
  have hZd : hZ ≤ d := Nat.le_of_mul_le_mul_left hle (by positivity)
  have h2d : 2 ≤ d := le_trans hZ2 hZd
  have hdd : 2 * d ≤ d ^ 2 := by nlinarith [h2d]
  omega

/-- **(6.6) per-member degree shape.**  Every member `χ = Ind_H^L θ` of `S` (`θ ∈ Irr H`) has degree
`χ(1) = |L:H| · θ(1)`; when `H` is a `p`-group `θ(1) = p^k`, so `χ(1) = |L:H| · p^k`.  This is the
common-index `p`-power degree shape (`idx = |L:H|`) of every X-chain member. -/
theorem exists_index_primePow_degree_of_mem_S (hyp : SibleyDadeHypothesis G L H)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H) {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.S) :
    ∃ k : ℕ, χ 1 = ((H.index * p ^ k : ℕ) : ℂ) := by
  rw [hyp.S_eq, Set.mem_setOf_eq] at hχ
  obtain ⟨θ, _hθ, rfl⟩ := hχ
  obtain ⟨k, hk⟩ := exists_primePow_natDegree_of_isPGroup hp hHp θ
  refine ⟨k, ?_⟩
  rw [ClassFunction.induce_apply_one, hk]
  push_cast; ring

/-- **(6.6) per-member degree data for an X-member family.**  Vectorizes
`exists_index_primePow_degree_of_mem_S` over a finite family `χmem : Fin k → Irr L` of `S`-members:
there are exponents `mmem j` with `χmem j (1) = |L:H| · p^(mmem j)`. Supplies the
`dmem`/`θmem`/`mmem`
fields of the X-chain step data (`dmem j = |L:H|·θmem j`, `θmem j = p^(mmem j)`). -/
theorem exists_memberDegreeData (hyp : SibleyDadeHypothesis G L H)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {k : ℕ} {χmem : Fin k → IrreducibleCharacter ↥L}
    (hmemS : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.S) :
    ∃ mmem : Fin k → ℕ,
      ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = ((H.index * p ^ mmem j : ℕ) : ℂ) := by
  choose mmem hmmem using fun j => hyp.exists_index_primePow_degree_of_mem_S hp hHp (hmemS j)
  exact ⟨mmem, hmmem⟩

/-- **(6.6)/(6.8) central degree bound for an X-member (the redesign linchpin).**  For
`χ = Ind_H^L θ ∈ X(Z) = S − S(Z)` with `H` a `p`-group and `Z` **central in `H`**
(`Z.subgroupOf H ≤ Z(↥H)`), the source `θ` has `θ(1) = p^k` and — crucially — by [Is] Cor 2.30
(`exists_degree_sq_le_index`, which needs `Z` central) `θ(1)² = (p^k)² ≤ |H:Z|`, while
`χ(1) = |L:H|·p^k`.  This is exactly the `θχ`/`hθχ`/`hθsq_le_qtot` data the per-step X-chain
producer
needs (with `qtot = |H:Z|`); it is fillable at the central `Z = Z(H)∩H′` but **not** at `Z = ⁅H,H⁆`
(see `notes/peterfalvi/s08_6_8_blocker_central_Z.md`). -/
theorem exists_source_primePow_centralBound_of_mem_Xset (hyp : SibleyDadeHypothesis G L H)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {Z : Subgroup ↥L} (hZcentral : Z.subgroupOf H ≤ Subgroup.center ↥H)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset Z) :
    ∃ k : ℕ, χ 1 = ((H.index * p ^ k : ℕ) : ℂ)
      ∧ (p ^ k) ^ 2 ≤ Nat.card (↥H ⧸ Z.subgroupOf H) := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hχS : χ ∈ hyp.S := hyp.Xset_subset_S hχ
  rw [hyp.S_eq, Set.mem_setOf_eq] at hχS
  obtain ⟨θ, _hθne, rfl⟩ := hχS
  obtain ⟨k, hk⟩ := exists_primePow_natDegree_of_isPGroup hp hHp θ
  refine ⟨k, ?_, ?_⟩
  · rw [ClassFunction.induce_apply_one, hk]; push_cast; ring
  · obtain ⟨d, hd, hdsq⟩ := θ.isIrreducible.exists_degree_sq_le_index (Z.subgroupOf H) hZcentral
    have hdpk : d = p ^ k := by
      have hcast : (d : ℂ) = ((p ^ k : ℕ) : ℂ) := by rw [← hd, hk]
      exact_mod_cast hcast
    rw [← hdpk, ← Subgroup.index_eq_card]; exact hdsq

open scoped Classical in
/-- **(6.2) core inequality** `|K:A| − 1 ≤ 2ψ(1)` (Frobenius case).

Combines the member-family degree-square bound `sMember_degreeSqReBound_of_not_coherent`
(`∑_{χ∈S₁} χ(1).re² ≤ 2ψ(1).re·χ₁(1).re`) with the real B2 identity
`sum_re_sq_induce_kernelFilter_eq`
(`∑_{χ∈S(A)} χ(1).re² = |L:H|·(|H:A| − 1)`).  Since `S(A) ⊆ S₁`, the `S(A)`-sum is bounded by the
`S₁`-sum, and with `χ₁(1) = |W₁| = |L:H|` (cancelling the positive index `|L:H|`) this gives
`|H:A| − 1 ≤ 2ψ(1)`.  This is the (6.2) bound `2ψ(1) ≥ |K:A| − 1` (with `K = H`); composing with the
θ-bound `ψ(1) ≤ |L:C|√|C:D|` yields the full (6.2) `2|L:C|√|C:D| ≥ |K:A| − 1`. -/
theorem sMember_index_le_two_psi (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {A : Subgroup ↥L} [A.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁sub : S₁ ⊆ hyp.S) (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁fin : S₁.Finite) (hSA_S1 : hyp.SsubFiltration A ⊆ S₁)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤ 2 * (ψ 1).re := by
  obtain ⟨k, χmem, hχinj, hrange, hmemS1, hfambound⟩ :=
    hyp.sMember_degreeSqReBound_of_not_coherent hF hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁ hχ₁deg
      hψS hψirr hψnotS1 hψcnotS1 hnc
  have hcfinj : Function.Injective (fun j => (χmem j : ClassFunction ↥L ℂ)) :=
    fun a b h => hχinj (Subtype.ext h)
  have hB2 := hyp.sum_re_sq_induce_kernelFilter_eq hF (A := A)
  set SA := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) with hSAdef
  -- the `S(A)` Finset is contained in the enumerated `S₁`-range Finset
  have hsub : SA ⊆ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hSAdef] at hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨-, hker, hne⟩ := Finset.mem_filter.mp hθ
    exact hSA_S1 (by rw [hyp.mem_SsubFiltration]; exact ⟨θ, hne, hker, rfl⟩)
  have hchain : (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1) ≤
      2 * (ψ 1).re * (χ₁ 1).re := by
    rw [← hB2]
    calc ∑ χ ∈ SA, ((χ 1).re) ^ 2
        ≤ ∑ χ ∈ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset, ((χ 1).re) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ = ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 :=
          sum_toFinset_range_eq hcfinj (fun χ => (χ 1).re ^ 2)
      _ ≤ 2 * (ψ 1).re * (χ₁ 1).re := hfambound
  have hχ₁re : (χ₁ 1).re = (H.index : ℝ) := by
    rw [hχ₁deg, Complex.natCast_re, hyp.index_H_eq_card_W1]
  rw [hχ₁re] at hchain
  have hidx_pos : (0 : ℝ) < (H.index : ℝ) := by
    rw [hyp.index_H_eq_card_W1]; exact_mod_cast Nat.card_pos
  have key : (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1) ≤
      (H.index : ℝ) * (2 * (ψ 1).re) := by
    calc (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1)
        ≤ 2 * (ψ 1).re * (H.index : ℝ) := hchain
      _ = (H.index : ℝ) * (2 * (ψ 1).re) := by ring
  exact le_of_mul_le_mul_left key hidx_pos

open scoped Classical in
/-- **(6.8.3) X-sum break bound.**  The (5.6)/B1 bound applied to the breaking coherent set `S₁ ⊇ X`:
`∑_{χ∈X} χ(1)² ≤ 2ψ(1)·χ₁(1)`.  Since `X ⊆ S₁` and `S₁` enumerates as a member family bounded by
`sMember_degreeSqReBound_of_not_coherent`, the `X`-sum `(H.index)·(|H| − |H:Z|)`
(`sum_re_sq_Xset_eq`) is dominated by the full family sum, which the (5.6) break bounds by
`2ψ(1)χ₁(1)`.  This is the `(6.8.3)` inequality with `χ₁ = η₁ ∈ Y` of degree `|W₁|`. -/
theorem xSum_le_two_psi (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {Z : Subgroup ↥L} [Z.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁sub : S₁ ⊆ hyp.S) (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁fin : S₁.Finite) (hXS1 : hyp.Xset Z ⊆ S₁)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ))
      ≤ 2 * (ψ 1).re * (χ₁ 1).re := by
  obtain ⟨k, χmem, hχinj, hrange, hmemS1, hfambound⟩ :=
    hyp.sMember_degreeSqReBound_of_not_coherent hF hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁ hχ₁deg
      hψS hψirr hψnotS1 hψcnotS1 hnc
  have hcfinj : Function.Injective (fun j => (χmem j : ClassFunction ↥L ℂ)) :=
    fun a b h => hχinj (Subtype.ext h)
  have hXsum := hyp.sum_re_sq_Xset_eq hF (Z := Z)
  set Xdiff := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXdiffdef
  have hsub : Xdiff ⊆ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hXdiffdef, Finset.mem_sdiff] at hχ
    obtain ⟨hχbot, hχnotZ⟩ := hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχbot
    obtain ⟨-, -, hne⟩ := Finset.mem_filter.mp hθ
    have hχS : ClassFunction.induce H θ.toClassFunction ∈ hyp.S := by
      rw [hyp.S_eq]; exact ⟨θ, hne, rfl⟩
    have hχnotSZ : ClassFunction.induce H θ.toClassFunction ∉ hyp.SsubFiltration Z := by
      intro hmem
      rw [hyp.mem_SsubFiltration] at hmem
      obtain ⟨θ', hne', hker', heq'⟩ := hmem
      exact hχnotZ (Finset.mem_image.mpr
        ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
    exact hXS1 ⟨hχS, hχnotSZ⟩
  rw [← hXsum]
  calc ∑ χ ∈ Xdiff, ((χ 1).re) ^ 2
      ≤ ∑ χ ∈ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset, ((χ 1).re) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ = ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 :=
        sum_toFinset_range_eq hcfinj (fun χ => (χ 1).re ^ 2)
    _ ≤ 2 * (ψ 1).re * (χ₁ 1).re := hfambound

open scoped Classical in
/-- **(6.6) X-set nonemptiness from a nontrivial trace.**  If `Z ⊴ L` and `Z.subgroupOf H ≠ ⊥`,
then `X(Z) = S − S(Z)` is nonempty.  The (6.6) degree-square sum
`∑_{χ∈X(Z)} χ(1).re² = |L:H|·(|H| − |H:Z|)` (`sum_re_sq_Xset_eq`) is strictly positive because
`|H:Z| < |H|` whenever `Z.subgroupOf H` is nontrivial, and a positive sum of squares forces its
index Finset — hence `X(Z)` — to be nonempty.  (Note `Xset` is *antitone* in `Z` (`Xset_mono`), so
`X(Zc)` nonemptiness does **not** follow from `X(⁅H,H⁆)` nonemptiness; this degree-sum route is the
honest argument, and it avoids any Clifford-conjugacy reasoning about `Ind`.) -/
theorem Xset_nonempty_of_subgroupOf_ne_bot (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} [Z.Normal] (hZbot : Z.subgroupOf H ≠ ⊥) :
    (hyp.Xset Z).Nonempty := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hXsum := hyp.sum_re_sq_Xset_eq hF (Z := Z)
  set Xdiff := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXdiffdef
  -- `|H:Z| < |H|`, since `Z.subgroupOf H` is nontrivial
  have hlt : Nat.card (↥H ⧸ Z.subgroupOf H) < Nat.card ↥H := by
    have h2 : 1 < Nat.card ↥(Z.subgroupOf H) := (Z.subgroupOf H).one_lt_card_iff_ne_bot.mpr hZbot
    have hcard : Nat.card ↥H
        = Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf H)
    calc Nat.card (↥H ⧸ Z.subgroupOf H)
        < Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
          lt_mul_of_one_lt_right Nat.card_pos h2
      _ = Nat.card ↥H := hcard.symm
  -- the degree-square sum is strictly positive
  have hidxpos : 0 < H.index := by rw [hyp.index_H_eq_card_W1]; exact Nat.card_pos
  have hpos : (0 : ℝ) < (H.index : ℝ) *
      ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ)) := by
    refine mul_pos (by exact_mod_cast hidxpos) ?_
    have : (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ) < (Nat.card ↥H : ℝ) := by exact_mod_cast hlt
    linarith
  rw [← hXsum] at hpos
  have hne : Xdiff.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨χ, hχ⟩ := hne
  refine ⟨χ, ?_⟩
  rw [hXdiffdef, Finset.mem_sdiff] at hχ
  obtain ⟨hχbot, hχnotZ⟩ := hχ
  obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχbot
  obtain ⟨-, -, hθne⟩ := Finset.mem_filter.mp hθ
  have hχS : ClassFunction.induce H θ.toClassFunction ∈ hyp.S := by
    rw [hyp.S_eq]; exact ⟨θ, hθne, rfl⟩
  have hχnotSZ : ClassFunction.induce H θ.toClassFunction ∉ hyp.SsubFiltration Z := by
    intro hmem
    rw [hyp.mem_SsubFiltration] at hmem
    obtain ⟨θ', hne', hker', heq'⟩ := hmem
    exact hχnotZ (Finset.mem_image.mpr
      ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
  exact hyp.mem_Xset.mpr ⟨hχS, hχnotSZ⟩

open scoped Classical in
/-- **(6.6)/(6.8) X-set nonemptiness, CertainType (case B) form.**  As
`Xset_nonempty_of_subgroupOf_ne_bot` but the strictly-positive degree-square sum is supplied by the
case-B identity `sum_re_sq_Xset_eq_of_irreducible_X` (which needs only `X`-irreducibility, valid in
case B) instead of the Frobenius `sum_re_sq_Xset_eq`. The `hX` hypothesis is the
`X = S − S(Z) ⊆ Irr L`
fact (Peterfalvi (6.8.1) for (c2), discharged by `isIrreducibleCharacter_of_mem_Xset_c2_caseA`). -/
theorem Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} [Z.Normal] (hZbot : Z.subgroupOf H ≠ ⊥)
    (hX : ∀ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
        IsIrreducibleCharacter χ) :
    (hyp.Xset Z).Nonempty := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hXsum := hyp.sum_re_sq_Xset_eq_of_irreducible_X (Z := Z) hX
  set Xdiff := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXdiffdef
  have hlt : Nat.card (↥H ⧸ Z.subgroupOf H) < Nat.card ↥H := by
    have h2 : 1 < Nat.card ↥(Z.subgroupOf H) := (Z.subgroupOf H).one_lt_card_iff_ne_bot.mpr hZbot
    have hcard : Nat.card ↥H
        = Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf H)
    calc Nat.card (↥H ⧸ Z.subgroupOf H)
        < Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
          lt_mul_of_one_lt_right Nat.card_pos h2
      _ = Nat.card ↥H := hcard.symm
  have hidxpos : 0 < H.index := by rw [hyp.index_H_eq_card_W1]; exact Nat.card_pos
  have hpos : (0 : ℝ) < (H.index : ℝ) *
      ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ)) := by
    refine mul_pos (by exact_mod_cast hidxpos) ?_
    have : (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ) < (Nat.card ↥H : ℝ) := by exact_mod_cast hlt
    linarith
  rw [← hXsum] at hpos
  have hne : Xdiff.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨χ, hχ⟩ := hne
  refine ⟨χ, ?_⟩
  rw [hXdiffdef, Finset.mem_sdiff] at hχ
  obtain ⟨hχbot, hχnotZ⟩ := hχ
  obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχbot
  obtain ⟨-, -, hθne⟩ := Finset.mem_filter.mp hθ
  have hχS : ClassFunction.induce H θ.toClassFunction ∈ hyp.S := by
    rw [hyp.S_eq]; exact ⟨θ, hθne, rfl⟩
  have hχnotSZ : ClassFunction.induce H θ.toClassFunction ∉ hyp.SsubFiltration Z := by
    intro hmem
    rw [hyp.mem_SsubFiltration] at hmem
    obtain ⟨θ', hne', hker', heq'⟩ := hmem
    exact hχnotZ (Finset.mem_image.mpr
      ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
  exact hyp.mem_Xset.mpr ⟨hχS, hχnotSZ⟩

/-- **(6.6)/(6.8) X-set nonemptiness at the central commutator** (the redesign's `hXne`).
`X(Zc)` with `Zc = Z(H) ∩ H′` is nonempty whenever `H` is non-abelian (`commutator ↥H ≠ ⊥`),
since then `Zc ≠ ⊥` (`centralCommutator_ne_bot`), hence `Zc.subgroupOf H ≠ ⊥` (`Zc ≤ H`). -/
theorem Xset_centralCommutator_nonempty (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥) :
    (hyp.Xset hyp.centralCommutator).Nonempty := by
  haveI := hyp.centralCommutator_normal
  refine hyp.Xset_nonempty_of_subgroupOf_ne_bot hF ?_
  intro hbot
  apply hyp.centralCommutator_ne_bot hHnonab
  rw [eq_bot_iff]
  intro z hz
  have hzH : z ∈ H := hyp.centralCommutator_le hz
  have hmem : (⟨z, hzH⟩ : ↥H) ∈ hyp.centralCommutator.subgroupOf H :=
    (Subgroup.mem_subgroupOf).mpr hz
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hmem

/-- **(6.8.3) extension, case (A): non-coherence of `S` is impossible.**
If `X ∪ Y` (with `X = S − S(Z)`, `Z = Z(H)∩H′` central) is coherent but `S` is not, the
break-pair `{ψ, ψ̄}` (`exists_coherentBreakPair`) gives a coherent `S₁ ⊇ X∪Y` whose extension by
`{ψ,ψ̄}` fails; the (5.6)/B1 bound (`xSum_le_two_psi`) then forces
`|W₁|·|H:Z|·(|Z|−1) = ∑_X χ(1)² ≤ 2ψ(1)·η₁(1) = 2|W₁|²d` with `d = θ(1)`, `ψ = Ind θ`.  Combined
with Cor 2.30 `d² ≤ |H:Z|` (central `Z`) and the FPF bound `|Z|−1 ≥ 2|W₁|`
(`centralCommutator_card_subgroupOf_lower`), the arithmetic core
`false_of_centralCommutator_break_arith` yields a contradiction.  This is the heart of
Peterfalvi (6.8.3) — the step the old `Xset ⁅H,H⁆ ∪ Yset = S` shortcut elided. -/
theorem false_of_coherentXunionYset_of_not_coherentS (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    (hXYcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) : False := by
  classical
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have hcommlt : (⁅H, H⁆ : Subgroup ↥L) < H := by
    have h1 : _root_.commutator ↥H < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial ↥H
    rw [← commutator_subgroupOf_self] at h1
    refine lt_of_le_of_ne (Subgroup.commutator_le_left H H) (fun heq => ?_)
    rw [heq, Subgroup.subgroupOf_self] at h1
    exact lt_irrefl _ h1
  -- break pair on `Sa = X ∪ Y`, `Sb = S`
  have hSaSb : hyp.Xset hyp.centralCommutator ∪ hyp.Yset ⊆ hyp.S := by
    rintro φ (hX | hY)
    · exact hyp.Xset_subset_S hX
    · exact hyp.Yset_subset_S hY
  have hSaconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset) := by
    intro φ hφ
    rcases hφ with hX | hY
    · exact Or.inl (hyp.Xset_closedUnderConjugate_unconditional hyp.centralCommutator hX)
    · exact Or.inr (hyp.SsubFiltration_closedUnderConjugate ⁅H, H⁆ hY)
  obtain ⟨S₁, ψ, hS₁conj, hSaS₁, hS₁Sb, hψSb, hψnS₁, hψcnS₁, hS₁cohN, hncN⟩ :=
    exists_coherentBreakPair hyp.tau hSaSb hyp.S_finite hyp.S_closedUnderConjugate
      (hyp.S_hasNoRealCharacters hF)
      (fun χ hχ => hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hχ)
      hSaconj hXYcoh hncoh
  -- anchor `η ∈ Y` of degree `|W₁|`
  obtain ⟨η, hηY⟩ := hyp.Yset_nonempty
  have hηS₁ : η ∈ S₁ := hSaS₁ (Or.inr hηY)
  have hηdeg : η 1 = (Nat.card hyp.W1 : ℂ) := by
    obtain ⟨χ, -, rfl⟩ := hyp.exists_linear_source_of_mem_Yset hηY
    exact hyp.induce_apply_one_eq_card_W1_of_degree_one _
      (OddOrder.RepresentationTheory.linearIrreducibleCharacter_apply_one χ)
  -- `ψ ∈ S` irreducible, `ψ = Ind θ`
  have hψS : ψ ∈ hyp.S := hψSb
  have hψirr : IsIrreducibleCharacter ψ := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hψS
  rw [hyp.S_eq, Set.mem_setOf_eq] at hψS
  obtain ⟨θ, hθne, hψeq⟩ := hψS
  obtain ⟨d, hdpos, hθd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  have hdsq : d ^ 2 ≤ Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) := by
    obtain ⟨d', hθd', hd'sq⟩ := θ.isIrreducible.exists_degree_sq_le_index
      (hyp.centralCommutator.subgroupOf H) hyp.centralCommutator_subgroupOf_le_center
    have hdd' : d = d' := by
      have hcast : (d : ℂ) = (d' : ℂ) := by rw [← hθd, hθd']
      exact_mod_cast hcast
    rw [hdd', ← Subgroup.index_eq_card]; exact hd'sq
  -- the (5.6) X-sum bound
  have hxb := hyp.xSum_le_two_psi hF (Z := hyp.centralCommutator) hS₁Sb hS₁conj
    (hyp.S_finite.subset hS₁Sb) (fun φ hφ => hSaS₁ (Or.inl hφ)) hS₁cohN.some
    hηS₁ hηdeg hψSb hψirr hψnS₁ hψcnS₁ hncN
  have hψre : (ψ 1).re = (H.index : ℝ) * (d : ℝ) := by
    rw [hψeq, ClassFunction.induce_apply_one, hθd]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
  have hηre : (η 1).re = (Nat.card hyp.W1 : ℝ) := by rw [hηdeg, Complex.natCast_re]
  rw [hψre, hηre] at hxb
  -- cast the real inequality to ℕ
  have hZle : Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) ≤ Nat.card ↥H :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hxbN : H.index * (Nat.card ↥H - Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H))
      ≤ 2 * (H.index * d) * Nat.card hyp.W1 := by
    rw [← Nat.cast_le (α := ℝ)]
    push_cast [Nat.cast_sub hZle]
    nlinarith [hxb]
  rw [hyp.index_mul_card_sub_factor (Z := hyp.centralCommutator), hyp.index_H_eq_card_W1] at hxbN
  -- discharge the arithmetic core
  refine false_of_centralCommutator_break_arith (w1 := Nat.card hyp.W1) (d := d)
    (hZ := Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H))
    (cZ := Nat.card ↥(hyp.centralCommutator.subgroupOf H))
    Nat.card_pos hdpos hdsq ?_ ?_ ?_
  · -- `2 ≤ |H:Z|`
    have hZcnotle : ¬ H ≤ hyp.centralCommutator := by
      intro h
      exact (ne_of_lt hcommlt)
        (le_antisymm (Subgroup.commutator_le_left H H)
          (le_trans h hyp.centralCommutator_le_commutator))
    have hne : hyp.centralCommutator.subgroupOf H ≠ ⊤ := fun heq =>
      hZcnotle (Subgroup.subgroupOf_eq_top.mp heq)
    have hcard1 : Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) ≠ 1 := by
      rw [← Subgroup.index_eq_card]; exact mt Subgroup.index_eq_one.mp hne
    have hcardpos : 0 < Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) := Nat.card_pos
    omega
  · -- `2|W₁| ≤ |Z| − 1`
    have he := hyp.centralCommutator_card_subgroupOf_lower hF hHnonab
    omega
  · -- the break inequality, reassociated
    calc Nat.card hyp.W1 * Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H)
            * (Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1)
        = Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H)
            * (Nat.card hyp.W1 * (Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1)) := by ring
      _ ≤ 2 * (Nat.card hyp.W1 * d) * Nat.card hyp.W1 := hxbN
      _ = 2 * Nat.card hyp.W1 ^ 2 * d := by ring

/-- **(6.2) θ-bound for an induced member `ψ = Ind_H^L θ`.**

For `θ ∈ Irr H` and a section `N ◁ C` with `N ≤ D ≤ C ≤ H`, `θ` trivial on `N` (after restriction
to `C`) and `D ⧸ N` central in `C ⧸ N`, the degree of the induced character `ψ = Ind_H^L θ` is
bounded by `ψ(1) = |L:H|·θ(1) ≤ |L:H|·|H:C|·√|C:D|`, combining `induce_apply_one`
(`ψ(1) = |L:H|·θ(1)`) with the §6 `θ`-bound `theta_degree_le_index_mul_sqrt_index`
(`θ(1) ≤ |H:C|·√|C:D|`).  This is the (6.2) step `ψ(1) ≤ |L:C|·√|C:D|`. -/
theorem psi_degree_le_of_source (_hyp : SibleyDadeHypothesis G L H)
    (θ : IrreducibleCharacter ↥H) (C : Subgroup ↥H) [Finite ↥C]
    [Invertible (Nat.card ↥C : ℂ)] {N : Subgroup ↥C} [N.Normal] (D : Subgroup ↥C) (hND : N ≤ D)
    (hθN : (↑N : Set ↥C) ⊆ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.restrict C (θ : ClassFunction ↥H ℂ)))
    (hcentral : D.map (QuotientGroup.mk' N) ≤ Subgroup.center (↥C ⧸ N)) :
    (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re ≤
      (H.index : ℝ) * (C.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  haveI : Fintype ↥C := Fintype.ofFinite ↥C
  letI : H.Normal := _hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hind : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re
      = (H.index : ℝ) * ((θ : ClassFunction ↥H ℂ) 1).re := by
    rw [ClassFunction.induce_apply_one, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  rw [hind]
  have hθbound := theta_degree_le_index_mul_sqrt_index (K := ↥H) θ C D hND hθN hcentral
  calc (H.index : ℝ) * ((θ : ClassFunction ↥H ℂ) 1).re
      ≤ (H.index : ℝ) * ((C.index : ℝ) * Real.sqrt (D.index : ℝ)) :=
        mul_le_mul_of_nonneg_left hθbound (Nat.cast_nonneg _)
    _ = (H.index : ℝ) * (C.index : ℝ) * Real.sqrt (D.index : ℝ) := by ring

open scoped Classical in
/-- **(6.2) first-obstruction + core wiring** `|K:A| − 1 ≤ 2ψ(1)`.

From `S(A)` coherent and `S(B)` not coherent (with `S(A) ⊆ S(B)`), the first-obstruction
`exists_coherentBreakPair` produces a breaking pair `{ψ, ψ̄}` with `ψ ∈ S(B)` (`ψ, ψ̄ ∉ S₁`), and
the
(6.2) core `sMember_index_le_two_psi` — with the degree-`|W₁|` anchor `χ₁ ∈ S(A) ⊆ S₁`
(`exists_mem_SsubFiltration_degree_W1`, valid since `H/(A.subgroupOf H)` has a proper commutator
subgroup) — gives `|H:A| − 1 ≤ 2ψ(1)`.  The structural inputs (`S(B)` finite / conjugation-closed /
real-free / irreducible, `S(A)` conjugation-closed) come from the landed `SsubFiltration_*`
helpers. -/
theorem six_two_index_bound (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {A B : Subgroup ↥L} [A.Normal]
    (hAB : hyp.SsubFiltration A ⊆ hyp.SsubFiltration B)
    (hAcomm : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤)
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ ψ, ψ ∈ hyp.SsubFiltration B ∧
      (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤ 2 * (ψ 1).re := by
  letI : H.Normal := hyp.H_normal
  obtain ⟨S₁, ψ, hS₁conj, hAS₁, hS₁B, hψB, hψnotS1, hψcnotS1, hS₁coh, hncoh⟩ :=
    exists_coherentBreakPair hyp.tau hAB (hyp.SsubFiltration_finite B)
      (hyp.SsubFiltration_closedUnderConjugate B) (hyp.SsubFiltration_hasNoRealCharacters hF B)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF
        (hyp.SsubFiltration_subset_S hφ))
      (hyp.SsubFiltration_closedUnderConjugate A) hSAcoh hSBncoh
  obtain ⟨χ₁, hχ₁SA, hχ₁deg⟩ := hyp.exists_mem_SsubFiltration_degree_W1 hAcomm
  have hψS : ψ ∈ hyp.S := hyp.SsubFiltration_subset_S hψB
  exact ⟨ψ, hψB, hyp.sMember_index_le_two_psi hF
    (hS₁B.trans hyp.SsubFiltration_subset_S) hS₁conj
    ((hyp.SsubFiltration_finite B).subset hS₁B) hAS₁ hS₁coh.some
    (hAS₁ hχ₁SA) hχ₁deg hψS (hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hψS)
    hψnotS1 hψcnotS1 hncoh⟩

/-- **Peterfalvi (6.2)** (Frobenius case, `K = H`).

Under the (6.2) section hypotheses — `B ⊆ D ⊆ C ⊆ H` with `D ⧸ B` central in `C ⧸ B` (here `B`
appears as `N = (B.subgroupOf H).subgroupOf C`), `S(A)` coherent, `S(B)` not — the index bound
`2|L:C|·√|C:D| ≥ |K:A| − 1` holds (with `K = H`, so `|L:C| = |L:H|·|H:C|` and `|C:D| = D.index`).

Proof: `six_two_index_bound` gives a breaking pair `ψ ∈ S(B)` with `|H:A| − 1 ≤ 2ψ(1)`; writing
`ψ = Ind_H^L θ` with `θ` trivial on `B` (`ψ ∈ S(B)`), `characterKernel_restrict_subgroupOf`
discharges the θ-bound's kernel hypothesis, and `psi_degree_le_of_source` gives
`ψ(1) ≤ |L:H|·|H:C|·√|C:D|`. -/
theorem six_two (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {A B : Subgroup ↥L} [A.Normal] [B.Normal]
    (hAB : hyp.SsubFiltration A ⊆ hyp.SsubFiltration B)
    (hAcomm : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤)
    (C : Subgroup ↥H) [Finite ↥C] [Invertible (Nat.card ↥C : ℂ)] (D : Subgroup ↥C)
    (hND : ((B.subgroupOf H).subgroupOf C) ≤ D)
    (hcentral : D.map (QuotientGroup.mk' ((B.subgroupOf H).subgroupOf C)) ≤
      Subgroup.center (↥C ⧸ (B.subgroupOf H).subgroupOf C))
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤
      2 * (H.index : ℝ) * (C.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  letI : H.Normal := hyp.H_normal
  obtain ⟨ψ, hψB, hψbound⟩ := hyp.six_two_index_bound hF hAB hAcomm hSAcoh hSBncoh
  rw [hyp.mem_SsubFiltration] at hψB
  obtain ⟨θ, _hθne, hθkerB, hψeq⟩ := hψB
  have hθN := characterKernel_restrict_subgroupOf C hθkerB
  have hψdeg := hyp.psi_degree_le_of_source θ C D hND hθN hcentral
  rw [hψeq] at hψbound
  calc (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1
      ≤ 2 * (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re := hψbound
    _ ≤ 2 * ((H.index : ℝ) * (C.index : ℝ) * Real.sqrt (D.index : ℝ)) := by linarith [hψdeg]
    _ = 2 * (H.index : ℝ) * (C.index : ℝ) * Real.sqrt (D.index : ℝ) := by ring

/-- **(6.2) θ-bound for an induced member, central (`C = H`) case.**

When the section is `N ◁ D ≤ H` with `θ` trivial on `N` and `D ⧸ N` central in `H ⧸ N`, the b-half
`degree_sq_le_index_of_central_quotient` gives `θ(1)² ≤ |H:D|` directly (no Clifford restriction),
so `ψ = Ind_H^L θ` has `ψ(1) = |L:H|·θ(1) ≤ |L:H|·√|H:D|`.  This is the form (6.3) consumes (it
applies (6.2) with `C = H`). -/
theorem psi_degree_le_of_source_central (_hyp : SibleyDadeHypothesis G L H)
    (θ : IrreducibleCharacter ↥H) {N : Subgroup ↥H} [N.Normal] (D : Subgroup ↥H) (hND : N ≤ D)
    (hθN : (↑N : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ))
    (hcentral : D.map (QuotientGroup.mk' N) ≤ Subgroup.center (↥H ⧸ N)) :
    (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re ≤
      (H.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  letI : H.Normal := _hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  obtain ⟨d, hd1, hd2⟩ :=
    degree_sq_le_index_of_central_quotient N θ D hND hθN hcentral
  have hind : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re
      = (H.index : ℝ) * ((θ : ClassFunction ↥H ℂ) 1).re := by
    rw [ClassFunction.induce_apply_one, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  rw [hind, hd1, Complex.natCast_re]
  exact mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (by exact_mod_cast hd2))
    (Nat.cast_nonneg _)

/-- **Peterfalvi (6.2), central case `C = H`** (the form consumed by (6.3)).

With the section `B ⊆ D ≤ H` (`B` as `N = B.subgroupOf H`), `D/B` central in `H/B`, `S(A)`
coherent, `S(B)` not: `|K:A| − 1 ≤ 2|L:H|·√|H:D|`.  Specializes `six_two` to `C = H`, where the
θ-bound is the direct b-half (`psi_degree_le_of_source_central`), so the source `θ` of the breaking
pair `ψ ∈ S(B)` is trivial on `N = B.subgroupOf H` (no restriction step needed). -/
theorem six_two_central (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {A B : Subgroup ↥L} [A.Normal] [B.Normal]
    (hAB : hyp.SsubFiltration A ⊆ hyp.SsubFiltration B)
    (hAcomm : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤)
    (D : Subgroup ↥H) (hND : B.subgroupOf H ≤ D)
    (hcentral : D.map (QuotientGroup.mk' (B.subgroupOf H)) ≤
      Subgroup.center (↥H ⧸ B.subgroupOf H))
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤ 2 * (H.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  letI : H.Normal := hyp.H_normal
  obtain ⟨ψ, hψB, hψbound⟩ := hyp.six_two_index_bound hF hAB hAcomm hSAcoh hSBncoh
  rw [hyp.mem_SsubFiltration] at hψB
  obtain ⟨θ, _hθne, hθkerB, hψeq⟩ := hψB
  have hψdeg := hyp.psi_degree_le_of_source_central θ D hND hθkerB hcentral
  rw [hψeq] at hψbound
  calc (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1
      ≤ 2 * (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re := hψbound
    _ ≤ 2 * ((H.index : ℝ) * Real.sqrt (D.index : ℝ)) := by linarith [hψdeg]
    _ = 2 * (H.index : ℝ) * Real.sqrt (D.index : ℝ) := by ring

/-- **(6.3) per-step index bound.**

The per-step of Peterfalvi (6.3): for a section `B ⊆ A ⊆ H₁` with `A/B` central in `H/B`, `S(A)`
coherent and `S(B)` not, the (6.2) central bound `six_two_central` (`|H:A| − 1 ≤ 2|L:H|√|H:A|`)
combines with the arithmetic core `six_three_HH1_le` to give `|H:H₁| ≤ 4|L:K|² + 1` (`K = H`).
The minimal-`A` / maximal-`B` induction of (6.3) repeatedly applies this step. -/
theorem six_three_index_bound (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {A B H₁ : Subgroup ↥L} [A.Normal] [B.Normal] (hBA : B ≤ A) (hAH₁ : A ≤ H₁)
    (hAcomm : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤)
    (hcentral : (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) ≤
      Subgroup.center (↥H ⧸ B.subgroupOf H))
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    Nat.card (↥H ⧸ H₁.subgroupOf H) ≤ 4 * H.index ^ 2 + 1 := by
  letI : H.Normal := hyp.H_normal
  have hsixtwo := hyp.six_two_central hF (hyp.SsubFiltration_antitone hBA) hAcomm
    (A.subgroupOf H) (Subgroup.subgroupOf_mono H hBA) hcentral hSAcoh hSBncoh
  have hHH1le : Nat.card (↥H ⧸ H₁.subgroupOf H) ≤ Nat.card (↥H ⧸ A.subgroupOf H) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono H hAH₁))
  refine six_three_HH1_le (LK := H.index) (KH := 1) (HA := Nat.card (↥H ⧸ A.subgroupOf H))
    (HH1 := Nat.card (↥H ⧸ H₁.subgroupOf H)) (by norm_num) hHH1le ?_
  simpa [Subgroup.index_eq_card] using hsixtwo

/-- **`hAcomm` from nilpotency of `H`.**

In the Sibley setup `H` is nilpotent, so for a normal `A ⊊ H` the quotient `H/A` is a nontrivial
nilpotent (hence solvable) group, whence its commutator subgroup is proper: `[H/A, H/A] ≠ ⊤`.  This
supplies the `hAcomm` hypothesis of `six_two_index_bound` / `six_three_index_bound` (which need a
degree-`|W₁|` anchor in `S(A)`). -/
theorem commutator_subgroupOf_quotient_ne_top (hyp : SibleyDadeHypothesis G L H)
    {A : Subgroup ↥L} [A.Normal] (hAH : A < H) :
    _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤ := by
  letI : H.Normal := hyp.H_normal
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  haveI : (A.subgroupOf H).Normal := (‹A.Normal›).subgroupOf H
  haveI : Nontrivial (↥H ⧸ A.subgroupOf H) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hAH.ne (le_antisymm hAH.le htop)
  exact (IsSolvable.commutator_lt_top_of_nontrivial (G := ↥H ⧸ A.subgroupOf H)).ne

/-- **Peterfalvi (6.3)** (Frobenius case `K = H`).

With `M ≤ H₁ ⊊ H` normal subgroups of `L`, `S(H₁)` coherent and `|H:H₁| > 4|L:H|² + 1`, the set
`S(M)` is coherent.

Minimal-`A` induction (Peterfalvi's argument): pick a normal `A ∈ [M, H₁]` with `S(A)` coherent that
is minimal for `⊆` (exists since `H₁` qualifies).  If `A ≠ M` then `M < A`; take a maximal normal
`B` with `M ≤ B ⊊ A` (`exists_maximal_normal_between`).  Then `A/B ⊆ Z(H/B)`
(`normal_central_of_maximal_normal_below`, using `H` nilpotent), and `S(B)` is *not* coherent (else
`B ∈ [M, H₁]` would beat the minimality of `A`).  So `six_three_index_bound` gives
`|H:H₁| ≤ 4|L:H|² + 1`, contradicting the hypothesis.  Hence `A = M` and `S(M) = S(A)` is
coherent. -/
theorem six_three (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {M H₁ : Subgroup ↥L} [M.Normal] [H₁.Normal] (hMH₁ : M ≤ H₁) (hH₁H : H₁ < H)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration H₁)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hbound : 4 * H.index ^ 2 + 1 < Nat.card (↥H ⧸ H₁.subgroupOf H)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration M)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  classical
  letI : H.Normal := hyp.H_normal
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  haveI : Finite (Subgroup ↥L) := Finite.of_injective (fun K : Subgroup ↥L => (K : Set ↥L))
    (fun _ _ h => SetLike.coe_injective h)
  set s : Set (Subgroup ↥L) := {A | A.Normal ∧ M ≤ A ∧ A ≤ H₁ ∧
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))} with hs_def
  have hH₁s : H₁ ∈ s := by
    simp only [hs_def, Set.mem_setOf_eq]; exact ⟨‹H₁.Normal›, hMH₁, le_refl _, hcoh⟩
  obtain ⟨A, hAmem, hAmin⟩ :=
    Set.Finite.exists_minimalFor (id : Subgroup ↥L → Subgroup ↥L) s (Set.toFinite _) ⟨H₁, hH₁s⟩
  simp only [hs_def, Set.mem_setOf_eq] at hAmem
  obtain ⟨hAnorm, hMA, hAH₁, hAcoh⟩ := hAmem
  haveI : A.Normal := hAnorm
  have hAeqM : A = M := by
    by_contra hne
    have hMltA : M < A := lt_of_le_of_ne hMA (Ne.symm hne)
    obtain ⟨B, hBnorm, hMB, hBltA, hBmaxl⟩ := exists_maximal_normal_between hMltA
    haveI : B.Normal := hBnorm
    have hAltH : A < H := lt_of_le_of_lt hAH₁ hH₁H
    have hAcomm := hyp.commutator_subgroupOf_quotient_ne_top hAltH
    have hcentral := normal_central_of_maximal_normal_below (H := H) (A := A) (B := B)
      ‹H.Normal› hAltH.le hBltA hBmaxl
    have hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
      intro hBcoh
      have hBs : B ∈ s := by
        simp only [hs_def, Set.mem_setOf_eq]
        exact ⟨hBnorm, hMB, hBltA.le.trans hAH₁, hBcoh⟩
      exact lt_irrefl _ (hBltA.trans_le (hAmin hBs hBltA.le))
    have hbnd := hyp.six_three_index_bound hF hBltA.le hAH₁ hAcomm hcentral hAcoh hSBncoh
    omega
  rw [← hAeqM]
  exact hAcoh

/-- **Peterfalvi (6.5) consequence (Frobenius case): `H` is a `p`-group.**

If the full set `S` is *not* coherent, then `H` is a `p`-group for some prime `p`.  Apply
`six_three`
with `M = ⊥`, `H₁ = ⁅H,H⁆`: `S(⁅H,H⁆) = Y` is coherent (`coherentYset`), `⊥ ≤ ⁅H,H⁆` and `⁅H,H⁆ ⊊ H`
(`H` nilpotent nontrivial ⟹ not perfect), so if `|H:⁅H,H⁆| > 4|L:H|²+1` then `S(⊥) = S` would be
coherent — contradiction.  Hence `|Abelianization H| = |H:⁅H,H⁆| ≤ 4|W₁|²+1`
(`commutator_subgroupOf_self`, `index_H_eq_card_W1`), and as everything has odd order
`isPGroup_of_isFrobeniusGroup_of_card_le` produces the prime.  This is the (6.5)/(6.6) reduction
"`H` is a `p`-group" that feeds the (6.8) capstone. -/
theorem isPGroup_of_not_coherent (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hSncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p ↥H := by
  letI : H.Normal := hyp.H_normal
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  -- `⁅H,H⁆ ⊊ H` from nilpotency (nontrivial nilpotent is not perfect)
  have hcommlt : (⁅H, H⁆ : Subgroup ↥L) < H := by
    have h1 : _root_.commutator ↥H < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial ↥H
    rw [← commutator_subgroupOf_self] at h1
    refine lt_of_le_of_ne (Subgroup.commutator_le_left H H) (fun heq => ?_)
    rw [heq, Subgroup.subgroupOf_self] at h1
    exact lt_irrefl _ h1
  -- the index bound, by the contrapositive of `six_three`
  have hidx : Nat.card (↥H ⧸ (⁅H, H⁆ : Subgroup ↥L).subgroupOf H) ≤ 4 * H.index ^ 2 + 1 := by
    by_contra hgt
    rw [not_le] at hgt
    have hYcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration ⁅H, H⁆)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := ⟨hyp.coherentYset⟩
    have hMcoh := hyp.six_three hF (M := ⊥) (H₁ := ⁅H, H⁆) bot_le hcommlt hYcoh hgt
    rw [hyp.SsubFiltration_bot] at hMcoh
    exact hSncoh hMcoh
  -- convert the index bound to the abelianization-card bound
  have hbound : Nat.card (Abelianization ↥H) ≤ 4 * Nat.card hyp.W1 ^ 2 + 1 := by
    rw [commutator_subgroupOf_self, hyp.index_H_eq_card_W1] at hidx
    exact hidx
  -- odd orders
  have hLodd : Odd (Nat.card ↥L) := hyp.card_L_odd
  have hHodd : Odd (Nat.card (Abelianization ↥H)) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hLodd H.card_subgroup_dvd_card)
      (Subgroup.card_quotient_dvd_card (_root_.commutator ↥H))
  have hW1odd : Odd (Nat.card hyp.W1) := Odd.of_dvd_nat hLodd hyp.W1.card_subgroup_dvd_card
  exact isPGroup_of_isFrobeniusGroup_of_card_le hF hHodd hW1odd hbound

/-- **(T8 leaf 8) `2 ≤ |S₀|`**, from the abstract input `X ⊆ Irr L`.

If `X` is nonempty, its base block `S₀` (minimal-degree members) contains a minimal-degree `χ`
together with its conjugate `χ̄ ≠ χ` (`Xset_hasNoRealCharacters_of_irreducible_X`,
`xBaseBlock_closedUnderConjugate_of_irreducible_X`), so `2 ≤ |S₀|`. -/
theorem two_le_xBaseBlock_ncard_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty) :
    2 ≤ (hyp.xBaseBlock Z).ncard := by
  have hXfin := hyp.xSet_finite_of_irreducible_X hX
  obtain ⟨χ, hχX, hχmin⟩ := Set.exists_min_image (hyp.Xset Z)
    (fun ψ => (OddOrder.Peterfalvi.S03.characterDegree ψ).re) hXfin hXne
  have hχS₀ : χ ∈ hyp.xBaseBlock Z := ⟨hχX, hχmin⟩
  have hconjS₀ : χ.conj ∈ hyp.xBaseBlock Z :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX hχS₀
  have hne : χ.conj ≠ χ := hyp.Xset_hasNoRealCharacters_of_irreducible_X hZH hX hχX
  have hS₀fin : (hyp.xBaseBlock Z).Finite := hXfin.subset (hyp.xBaseBlock_subset Z)
  have h1 : 1 < (hyp.xBaseBlock Z).ncard :=
    (Set.one_lt_ncard hS₀fin).mpr ⟨χ.conj, hconjS₀, χ, hχS₀, hne⟩
  omega

/-- **(T8 leaf 8) `2 ≤ |S₀|`** (Frobenius case). -/
theorem two_le_xBaseBlock_ncard (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] (hXne : (hyp.Xset Z).Nonempty) :
    2 ≤ (hyp.xBaseBlock Z).ncard :=
  hyp.two_le_xBaseBlock_ncard_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hXne

/-- **(T8 leaf 9) base coherence `IsCoherent τ S₀`**, from the abstract input
`X ⊆ Irr L`.

The minimal-degree base block `S₀ = xBaseBlock Z` is coherent for the real Dade map `tau`.  It is a
finite, equal-degree family of `≥ 2` irreducible characters of `L`
(`exists_finEnum_irreducible`, `xBaseBlock_degree_re_eq` with the integer degrees
`irreducibleCharacter_apply_one_eq_pos_natCast`, `two_le_xBaseBlock_ncard_of_irreducible_X`) whose
pairwise differences `χⱼ − χ₀` vanish off `H^# = sharpImage H`
(`sMember_diffSupport_of_charValue_eq`), so the §7 base engine `coherentEqualDegree_fromDade`
((6.6) base case, via (1.1)+(1.4)) applies with `A = H^#` — matching
`tau = dadeIntegralCharacterMap hyp.dade …`.

`noncomputable def` (not `theorem`): `IsCoherent` carries the isometric extension map as data
(it lives in `Type`, not `Prop`), exactly like `sibleySetup_is_coherent`/`CoherenceTarget`. -/
noncomputable def xBaseBlock_isCoherent_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.xBaseBlock Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  -- Enumerate the finite irreducible base block `S₀` as `χ : Fin k → Irr L`.  The conclusion
  -- `IsCoherent` is `Type`-valued (carries the extension map), so the enumeration data must be
  -- extracted with `choose` (via choice), not `obtain` (which would large-eliminate a `Prop ∃`).
  have hS₀fin : (hyp.xBaseBlock Z).Finite :=
    (hyp.xSet_finite_of_irreducible_X hX).subset (hyp.xBaseBlock_subset Z)
  have hS₀irr : ∀ φ ∈ hyp.xBaseBlock Z, IsIrreducibleCharacter φ :=
    fun φ hφ => hX φ (hyp.xBaseBlock_subset Z hφ)
  choose k χ hχinj hrange using exists_finEnum_irreducible hS₀fin hS₀irr
  have hmemS₀ : ∀ j, (χ j : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z :=
    fun j => hrange ▸ Set.mem_range_self j
  -- `2 ≤ k`: the coerced enumeration is injective, so `|S₀| = k`.
  have hcoeinj : Function.Injective (fun j => (χ j : ClassFunction ↥L ℂ)) := by
    intro i j hij
    exact hχinj (IrreducibleCharacter.ext hij)
  have hk2 : 2 ≤ k := by
    have hcard : (hyp.xBaseBlock Z).ncard = k := by
      rw [← hrange, Set.ncard_range_of_injective hcoeinj, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have h2 := hyp.two_le_xBaseBlock_ncard_of_irreducible_X hZH hX hXne
    omega
  haveI : NeZero k := ⟨by omega⟩
  -- `S₀ ⊆ S`.
  have hmemS : ∀ j, (χ j : ClassFunction ↥L ℂ) ∈ hyp.S :=
    fun j => (hyp.mem_Xset.mp (hyp.xBaseBlock_subset Z (hmemS₀ j))).1
  -- Equal degree: real parts equal (base block) and the degrees are positive integers.
  have hdeg : ∀ j, ((χ j : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
      = ((χ 0 : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := by
    intro j
    obtain ⟨dj, _, hdj⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (χ j)
    obtain ⟨d0, _, hd0⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (χ 0)
    have hre := hyp.xBaseBlock_degree_re_eq (hmemS₀ j) (hmemS₀ 0)
    rw [OddOrder.Peterfalvi.S03.characterDegree_def,
      OddOrder.Peterfalvi.S03.characterDegree_def, hdj, hd0] at hre
    rw [hdj, hd0]
    have hdd : dj = d0 := by exact_mod_cast hre
    rw [hdd]
  -- Difference support: `χⱼ − χ₀` vanishes off `H^#` (equal degree, both supported on `H`).
  have hsuppdiff : ∀ j, (irreducibleCharacterDifference χ j).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    fun j => hyp.sMember_diffSupport_of_charValue_eq (hmemS j) (hmemS 0) (hdeg j)
  -- `1 ∉ A = H^#`.
  have h1notA : (1 : G) ∉ sharpImage H := by simp [sharpImage]
  -- Apply the §7 base engine; its `range χ = S₀` and Dade map `= hyp.tau`.
  have hcoh := OddOrder.Peterfalvi.S07.coherentEqualDegree_fromDade hyp.dade hyp.hconj
    hk2 χ hχinj hdeg hsuppdiff h1notA
  rw [hrange] at hcoh
  exact hcoh

/-- **(T8 leaf 9) base coherence `IsCoherent τ S₀`** (Frobenius case). -/
noncomputable def xBaseBlock_isCoherent (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] (hXne : (hyp.Xset Z).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.xBaseBlock Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.xBaseBlock_isCoherent_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hXne

/-- **(T8 leaf 9, case A) base coherence `IsCoherent τ S₀`.**

This specializes the abstract `X ⊆ Irr L` base-block engine using the case-A irreducibility bridge
`isIrreducibleCharacter_of_mem_Xset_caseA`. -/
noncomputable def xBaseBlock_isCoherent_caseA (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hZcentral : Z.subgroupOf H ≤ Subgroup.center ↥H)
    (hZnorm : ∀ w ∈ hyp.W1, w ∈ Subgroup.normalizer Z)
    (hZfpf : ∀ w ∈ hyp.W1, w ≠ 1 → Subgroup.centralizer ({w} : Set ↥L) ⊓ Z = ⊥)
    (hXne : (hyp.Xset Z).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.xBaseBlock Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.xBaseBlock_isCoherent_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_caseA hZH hZcentral hZnorm hZfpf h)
    hXne


/-- **(T8.11b) X-pair step core facts.**

For a pair supplied by `exists_conjugatePairCover`, the first eight fields of
`XAdjoinStepInput` are forced by membership in `X` and the disjoint-prefix property: the new
character is non-real, has the required difference support, is orthonormal to its conjugate, and is
orthogonal to the accumulated prefix. -/
theorem xPair_stepCoreFacts_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N) :
    ¬ ClassFunction.IsReal (χs i : ClassFunction ↥L ℂ) ∧
      (((χs i : ClassFunction ↥L ℂ).conj - (χs i : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ) (χs i : ClassFunction ↥L ℂ) = 1 ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ).conj
        (χs i : ClassFunction ↥L ℂ).conj = 1 ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ)
        (χs i : ClassFunction ↥L ℂ).conj = 0 ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ).conj
        (χs i : ClassFunction ↥L ℂ) = 0 ∧
      (∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
        ClassFunction.inner (χs i : ClassFunction ↥L ℂ) x = 0) ∧
      (∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
        ClassFunction.inner (χs i : ClassFunction ↥L ℂ).conj x = 0) := by
  classical
  have hχpair : (χs i : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0 i hi]
  have hχX : (χs i : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := hpairs i hi hχpair
  rcases hyp.xMember_characterFacts_of_irreducible_X hZH hX hχX with
    ⟨hrealχ, hχχ, hχbarχbar, hχbarχ, hχχbar⟩
  have hdiffsuppχ := hyp.xMember_diffSupport_of_irreducible_X hX hχX
  have hortho := pairCover_orthogonal_to_prefix
    (X := hyp.Xset Z) (S₀ := hyp.xBaseBlock Z) (pair := pair) (N := N)
    (i := i) (χ := χs i) hX (hyp.xBaseBlock_subset Z) hpairs
    (hpair0 i hi) (hpair1 i hi) (hdisj i hi) hi
  exact ⟨hrealχ, hdiffsuppχ, hχχ, hχbarχbar, hχχbar, hχbarχ, hortho.1, hortho.2⟩

/-- **(T8.11c) Accumulator member-family enumeration.**

Every prefix accumulator `pairUnion (xBaseBlock Z) pair i` in the X-chain is a finite family of
irreducible characters, closed under conjugation.  This packages the `Fin k` enumeration and the
member facts needed by the member-family half of `XAdjoinStepInput`.  The remaining
degree-ratio and lattice-generation fields stay separate. -/
theorem exists_pairUnion_memberFamily_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hi : i < N) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) =
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i ∧
      (∀ j : Fin k, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ)) ∧
      (∀ j : Fin k,
        ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      (∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i) ∧
      (∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ).conj ∈
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i) ∧
      (∀ j : Fin k, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ).conj = 0) ∧
      (∀ j l : Fin k,
        ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
          (χmem l : ClassFunction ↥L ℂ) = if j = l then (1 : ℂ) else 0) := by
  classical
  let S₁ : Set (ClassFunction ↥L ℂ) :=
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  have hS₁X : S₁ ⊆ hyp.Xset Z := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact hyp.xBaseBlock_subset Z hbase
    · exact hpairs j (hji.trans hi) hjpair
  have hS₁irr : ∀ φ ∈ S₁, IsIrreducibleCharacter φ := fun φ hφ => hX φ (hS₁X hφ)
  have hS₁fin : S₁.Finite := (hyp.xSet_finite_of_irreducible_X hX).subset hS₁X
  have hS₀conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX
  have hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl (hS₀conj hbase))
    · have hjN : j < N := hji.trans hi
      have hpair_conj : φ.conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hjpair ⊢
        rcases hjpair with hφ | hφ
        · right
          rw [hφ, hpair0 j hjN, hpair1 j hjN]
        · left
          rw [hφ, hpair1 j hjN, hpair0 j hjN]
          simp
      exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hji, hpair_conj⟩)
  obtain ⟨k, χmem, hχinj, hrange⟩ := exists_finEnum_irreducible hS₁fin hS₁irr
  have hmemS1 : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j
    rw [← hrange]
    exact Set.mem_range_self j
  have hmembarS1 : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ).conj ∈ S₁ :=
    fun j => hS₁conj (hmemS1 j)
  have hmemreal : ∀ j : Fin k, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ) := by
    intro j
    exact (hyp.xMember_characterFacts_of_irreducible_X hZH hX (hS₁X (hmemS1 j))).1
  have hmemdiffsupp : ∀ j : Fin k,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    intro j
    exact hyp.xMember_diffSupport_of_irreducible_X hX (hS₁X (hmemS1 j))
  have hmemconjortho : ∀ j : Fin k, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0 := by
    intro j
    rcases hyp.xMember_characterFacts_of_irreducible_X hZH hX (hS₁X (hmemS1 j)) with
      ⟨_, _, _, _, hχχbar⟩
    exact hχχbar
  have hmemortho : ∀ j l : Fin k,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem l : ClassFunction ↥L ℂ) = if j = l then (1 : ℂ) else 0 := by
    intro j l
    by_cases hjl : j = l
    · subst j
      simpa using irreducibleCharacter_inner_eq_ite (χmem l) (χmem l)
    · have hχne : χmem j ≠ χmem l := fun h => hjl (hχinj h)
      simpa [hjl, hχne] using irreducibleCharacter_inner_eq_ite (χmem j) (χmem l)
  exact ⟨k, χmem, hχinj, hrange, hmemreal, hmemdiffsupp, hmemS1, hmembarS1,
    hmemconjortho, hmemortho⟩

open scoped Classical in
/-- **(T8.11l) X-adjoin input from member-family degree ratios.**

Given a conjugate-pair cover step, an explicit finite member-family cover of the current prefix
`S₁ = pairUnion (xBaseBlock Z) pair i`, and degree-ratio data against a chosen anchor `χ₁`, this
assembles the full `XAdjoinStepInput` for adjoining `χᵢ`.  The theorem deliberately leaves the
arithmetical (6.6) payload as inputs: the member and new-character degree ratios, `deg i₁ = 1`, and
the strict inequality `2a < ∑ deg²`.  All non-arithmetical fields are discharged from the X-pair
cover, support bridges, virtual-character bridge, and the §7 anchor-generation lemma. -/
noncomputable def xAdjoinStepInput_of_memberFamily_degreeRatios
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι : Type} {s : Finset ι} {χmem : ι → IrreducibleCharacter ↥L}
    {deg : ι → ℕ} {i₁ : ι} {a : ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (ha1 : deg i₁ = 1)
    (hdeg_mem : ∀ j ∈ s,
      (χmem j : ClassFunction ↥L ℂ) 1 =
        (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1)
    (hdegχ : (χs i : ClassFunction ↥L ℂ) 1 =
      (a : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1)
    (hDeg : 2 * (a : ℝ) < ∑ j ∈ s, ((deg j : ℝ)) ^ 2) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  classical
  let S₁ : Set (ClassFunction ↥L ℂ) :=
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  have hχpair : (χs i : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0 i hi]
  have hχX : (χs i : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := hpairs i hi hχpair
  have hmemX : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := by
    intro j hj
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp (hmemS1 j hj) with hbase | ⟨k, hki, hkpair⟩
    · exact hyp.xBaseBlock_subset Z hbase
    · exact hpairs k (hki.trans hi) hkpair
  rcases hyp.xPair_stepCoreFacts_of_irreducible_X hZH hX hpair0 hpair1 hpairs hdisj hi with
    ⟨hrealχ, hdiffsuppχ, hχχ, hχbarχbar, hχχbar, hχbarχ, hχ_S1, hχbar_S1⟩
  have hmemdegdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ) - deg j •
          (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.xMember_scaledDiffSupports_of_degreeData hmemX hi₁ hdeg_mem
  have hdiffasuppχ : ((χs i : ClassFunction ↥L ℂ) - a •
        (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.xMember_scaledDiffSupport_of_degreeData hχX (hmemX i₁ hi₁) hdegχ
  have htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dade
      (hyp.dade.fullDadeIsometryData hyp.hconj)
      ((χs i : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G := by
    simpa [SibleyDadeHypothesis.tau] using hyp.scaledDiff_dadeImage_mem_ZIrr hdiffasuppχ
  have hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          {(χmem i₁ : ClassFunction ↥L ℂ)}) :=
    OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
      (L := ↥L) (S₁ := S₁)
      (A := OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      (χmem := fun j => (χmem j : ClassFunction ↥L ℂ)) (deg := deg) (i₁ := i₁)
      (by simpa [S₁] using hcover) hi₁ (by simpa [S₁] using hmemS1)
      (by simpa using hmemdegdiffsupp)
  exact
    { hrealχ := hrealχ
      hdiffsuppχ := hdiffsuppχ
      hχχ := hχχ
      hχbarχbar := hχbarχbar
      hχχbar := hχχbar
      hχbarχ := hχbarχ
      hχ_S1 := hχ_S1
      hχbar_S1 := hχbar_S1
      ι := ι
      s := s
      χmem := χmem
      deg := deg
      i₁ := i₁
      hi₁ := hi₁
      hmemreal := hmemreal
      hmemdiffsupp := hmemdiffsupp
      hmemdegdiffsupp := hmemdegdiffsupp
      hmemS1 := hmemS1
      hmembarS1 := hmembarS1
      hmemconjortho := hmemconjortho
      hmemortho := hmemortho
      a := a
      hdiffasuppχ := hdiffasuppχ
      htau1_memaχ := htau1_memaχ
      ha1 := ha1
      hDeg := hDeg
      hSgen := hSgen }

/-- **(T8 leaf 10 / T-A4) X-chain assembly from per-pair adjoining data.**

This is the Sibley/Xset wrapper around the abstract `xChainCoherent` fold.  It builds the
conjugate-pair cover of `X = hyp.Xset Z` over the minimal-degree base block
`S0 = hyp.xBaseBlock Z` (`exists_conjugatePairCover`), supplies the base coherence
`xBaseBlock_isCoherent_of_irreducible_X`, and leaves exactly the per-step (5.6)/(6.6) adjoining
payload as `hstep`.

The extra disjoint-prefix and degree-monotonicity facts exposed to `hstep` are produced by the pair
cover but are not consumed by `xChainCoherent` itself; they are the data needed to construct each
`XAdjoinStepInput` without re-enumerating `X`. -/
noncomputable def Xset_isCoherent_from_adjoinSteps_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty)
    (hstep : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N → ∀ (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
          (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)),
        XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hXfin : (hyp.Xset Z).Finite := hyp.xSet_finite_of_irreducible_X hX
  have hXconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) :=
    hyp.Xset_closedUnderConjugate_of_irreducible_X hZH hX
  have hXreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset Z) :=
    hyp.Xset_hasNoRealCharacters_of_irreducible_X hZH hX
  have hS0conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX
  choose e pair N hpairχ hsurj hpairs hcoverIdx hpair0Raw hpair1Raw hdisj hmono using
    exists_conjugatePairCover (X := hyp.Xset Z) (S₀ := hyp.xBaseBlock Z)
      hXfin hXconj hXreal hX hS0conj
  let χ0 : IrreducibleCharacter ↥L := ⟨Classical.choose hXne, hX _ (Classical.choose_spec hXne)⟩
  let χs : ℕ → IrreducibleCharacter ↥L := fun i => if hi : i < N then hpairχ i hi else χ0
  have hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ) := by
    intro i hi
    rw [hpair0Raw i hi]
    simp [χs, hi]
  have hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj := by
    intro i hi
    rw [hpair1Raw i hi]
    simp [χs, hi]
  have hcover : ∀ φ ∈ hyp.Xset Z, φ ∈ hyp.xBaseBlock Z ∨
      ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
    intro φ hφ
    obtain ⟨i, hi⟩ := hsurj φ hφ
    have hci := hcoverIdx i
    rw [hi] at hci
    exact hci
  exact xChainCoherent hyp.dade hyp.hconj pair N χs hpair0 hpair1
    (hyp.xBaseBlock_subset Z) hpairs hcover
    (hyp.xBaseBlock_isCoherent_of_irreducible_X hZH hX hXne)
    (fun i hi hcoh => hstep pair N χs hpair0 hpair1 hpairs hdisj hmono i hi hcoh)

/-- **(T8.10w) X-chain coherence engine, completeness-exposing variant.**  Identical to
`Xset_isCoherent_from_adjoinSteps_of_irreducible_X` but the per-step callback `hstep` additionally
receives the **Xset-cover completeness** witness
`hcover : ∀ φ ∈ X, φ ∈ xBaseBlock Z ∨ ∃ j < N, φ ∈ pairSet pair j`.  The base engine derives this
internally (from `exists_conjugatePairCover`) but does not expose it; the StepData producer needs it
to build the per-step `tailSet = X ∖ accumulator` and discharge `htail_le`/`hsum` (only well-behaved
when the conjugate-pair cover is complete — see `notes/peterfalvi/s08_6_8_blocker_central_Z.md`
finding #6).  Additive: no existing signature changes. -/
noncomputable def Xset_isCoherent_from_adjoinSteps_withCover_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty)
    (hstep : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      (∀ φ ∈ hyp.Xset Z, φ ∈ hyp.xBaseBlock Z ∨
        ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j) →
      ∀ i, i < N → ∀ (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
          (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)),
        XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hXfin : (hyp.Xset Z).Finite := hyp.xSet_finite_of_irreducible_X hX
  have hXconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) :=
    hyp.Xset_closedUnderConjugate_of_irreducible_X hZH hX
  have hXreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset Z) :=
    hyp.Xset_hasNoRealCharacters_of_irreducible_X hZH hX
  have hS0conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX
  choose e pair N hpairχ hsurj hpairs hcoverIdx hpair0Raw hpair1Raw hdisj hmono using
    exists_conjugatePairCover (X := hyp.Xset Z) (S₀ := hyp.xBaseBlock Z)
      hXfin hXconj hXreal hX hS0conj
  let χ0 : IrreducibleCharacter ↥L := ⟨Classical.choose hXne, hX _ (Classical.choose_spec hXne)⟩
  let χs : ℕ → IrreducibleCharacter ↥L := fun i => if hi : i < N then hpairχ i hi else χ0
  have hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ) := by
    intro i hi
    rw [hpair0Raw i hi]
    simp [χs, hi]
  have hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj := by
    intro i hi
    rw [hpair1Raw i hi]
    simp [χs, hi]
  have hcover : ∀ φ ∈ hyp.Xset Z, φ ∈ hyp.xBaseBlock Z ∨
      ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
    intro φ hφ
    obtain ⟨i, hi⟩ := hsurj φ hφ
    have hci := hcoverIdx i
    rw [hi] at hci
    exact hci
  exact xChainCoherent hyp.dade hyp.hconj pair N χs hpair0 hpair1
    (hyp.xBaseBlock_subset Z) hpairs hcover
    (hyp.xBaseBlock_isCoherent_of_irreducible_X hZH hX hXne)
    (fun i hi hcoh => hstep pair N χs hpair0 hpair1 hpairs hdisj hmono hcover i hi hcoh)

end SibleyDadeHypothesis


end OddOrder.Peterfalvi.S08
