/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S05_SigmaIsometry
import OddOrder.Peterfalvi.S05_GridTrichotomy

/-!
# Peterfalvi (3.8): the trichotomy for the `σ`-coefficient grid

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §3, pp. 15-20.

This file specialises the abstract grid trichotomy `grid_trichotomy` (`S05_GridTrichotomy`) to the
concrete `σ`-image coefficient grid `a_{ij} = ⟨ψ, ω_{ij}^σ⟩ =` `sigmaCoeff` (`S05_SigmaIsometry`),
giving the full **Peterfalvi Theorem (3.8)** for a class function `ψ` vanishing on `V`.

The companion `sigmaCoeff_eq_zero_of_sigmaNC_lt` (`S05_SigmaIsometry`) is the `NC(ψ) < min(w₁,w₂)`
corollary (the part used by (3.9.a)); this file supplies the full `NC(ψ) < 2w₁` trichotomy needed by
the §6 certain-type analysis (Peterfalvi (4.8)).
-/

namespace OddOrder.Peterfalvi.S05.TICyclicHypothesis

open OddOrder.Peterfalvi.S05
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

/-- **Peterfalvi Theorem (3.8)** (full trichotomy for the `σ`-coefficient grid).  Let `ψ` vanish on
`V`, with `w₁ + 2 ≤ w₂` (the odd-order gap from `w₁ < w₂`) and `NC(ψ) < 2w₁`.  Then one of:

* (a) every `σ`-image coefficient `⟨ψ, ω_{ij}^σ⟩` vanishes (`ψ = β`, orthogonal to `Im σ`);
* (b) a single `W₂`-column `j₀` carries a common nonzero coefficient `c`, the rest vanishing
  (`ψ = c·∑_i ω_{i,j₀}^σ + β`);
* (c) a single `W₁`-row `i₀` carries a common nonzero coefficient `c`, the rest vanishing
  (`ψ = c·∑_j ω_{i₀,j}^σ + β`).

Immediate from `grid_trichotomy` applied to `sigmaCoeff`, whose additive separability is
`sigmaCoeff_add_eq` (3.7) and whose support count is `sigmaNC` (3.6) by definition; the index sets
`Ŵ₁, Ŵ₂` have `|Ŵ_k| = w_k` (`card_charGroup_subgroupOf`). -/
theorem sigmaCoeff_trichotomy (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {ψ : ClassFunction G ℂ} (hψ : ∀ v ∈ hyp.V, ψ v = 0)
    (hgap : Nat.card hyp.W1 + 2 ≤ Nat.card hyp.W2)
    (hNC : hyp.sigmaNC hVeq app ψ < 2 * Nat.card hyp.W1) :
    (∀ pq, hyp.sigmaCoeff hVeq app ψ pq = 0) ∨
      (∃ (j₀ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) (c : ℂ), c ≠ 0 ∧
        (∀ p, hyp.sigmaCoeff hVeq app ψ (p, j₀) = c) ∧
        ∀ p q, q ≠ j₀ → hyp.sigmaCoeff hVeq app ψ (p, q) = 0) ∨
      (∃ (i₀ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (c : ℂ), c ≠ 0 ∧
        (∀ q, hyp.sigmaCoeff hVeq app ψ (i₀, q) = c) ∧
        ∀ p q, p ≠ i₀ → hyp.sigmaCoeff hVeq app ψ (p, q) = 0) := by
  haveI : Finite G := Finite.of_fintype G
  haveI : Nonempty ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := ⟨1⟩
  haveI : Nonempty ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := ⟨1⟩
  refine grid_trichotomy (fun pq => hyp.sigmaCoeff hVeq app ψ pq)
    (fun p p' q q' => hyp.sigmaCoeff_add_eq hVeq app hψ p p' q q') ?_ ?_
  · rw [hyp.card_charGroup_subgroupOf hyp.W1_le_W, hyp.card_charGroup_subgroupOf hyp.W2_le_W]
    exact hgap
  · rw [hyp.card_charGroup_subgroupOf hyp.W1_le_W]
    exact hNC

/-! ### The norm-`2` Dade-image trichotomy endgame (Peterfalvi (4.8)/(10.5))

The §6 certain-type isometry (4.8) and the §10 (10.5) Dade-image identity share the same endgame:
a virtual character `X` of `G` with `‖X‖² = 2` whose difference with `s·(χ_{P₁} − χ_{P₂})`
(`s = ±1`, `P₁ ≠ P₂` two `σ`-grid indices) vanishes on `V` must in fact *equal* it.  The proof is a
`σ`-coefficient computation feeding the abstract grid trichotomy `grid_trichotomy`; it is entirely a
`TICyclicHypothesis`-level fact (no certain-type data), abstracted here so both §6 and §10 reuse
it. -/

open scoped Classical in
/-- The `σ`-coefficient grid of `ψ = X − s·(χ_{P₁} − χ_{P₂})` (`s : ℤ`).  As the `χ`-family is
orthonormal (`chiFam_spec`), the `s`-part contributes `∓s` exactly at the two grid positions
`P₁, P₂`: `⟨ψ, χ_{pq}⟩ = ⟨X, χ_{pq}⟩ − s·([P₁ = pq] − [P₂ = pq])`.  The `TICyclicHypothesis`-level
generalisation of the §6 `sigmaCoeff_psi_eq`, used by the (4.8)/(10.5) Dade-image trichotomy. -/
theorem sigmaCoeff_sub_smul_chiFam_diff (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (X : ClassFunction G ℂ) (s : ℤ)
    (P1 P2 pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) :
    hyp.sigmaCoeff hVeq app
        (X - (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2)) pq
      = hyp.sigmaCoeff hVeq app X pq
        - (s : ℂ) * ((if P1 = pq then (1 : ℂ) else 0) - (if P2 = pq then (1 : ℂ) else 0)) := by
  simp only [sigmaCoeff, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    (hyp.chiFam_spec hVeq app).2.2.1]

/-- **Norm-`2` Dade image is `s·(χ_{P₁} − χ_{P₂})` once all `σ`-coefficients of the difference
vanish.**  If every `σ`-image coefficient of `ψ = X − s·(χ_{P₁} − χ_{P₂})` vanishes (with
`‖X‖² = 2`, `P₁ ≠ P₂`, `s = ±1`), then `X = s·(χ_{P₁} − χ_{P₂})`.

`⟨ψ, χ_{P₁}⟩ = ⟨ψ, χ_{P₂}⟩ = 0` (hypothesis) and `sigmaCoeff_sub_smul_chiFam_diff` pin
`⟨X, χ_{P₁}⟩ = s`, `⟨X, χ_{P₂}⟩ = −s`; then `‖ψ‖² = ‖X‖² − 2 = 0` (orthonormality of the `χ`-family,
`s² = 1`), so `ψ = 0`.  Generalises the §6 `certainType_diff_dade_eq_of_all_sigmaCoeff_zero`. -/
theorem eq_smul_chiFam_diff_of_all_sigmaCoeff_zero (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {X : ClassFunction G ℂ} (hX2 : ClassFunction.inner X X = 2)
    {P1 P2 : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)}
    (hPne : P1 ≠ P2) {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hall : ∀ pq, hyp.sigmaCoeff hVeq app
        (X - (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2)) pq = 0) :
    X = (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2) := by
  classical
  have hc1 : ClassFunction.inner X (hyp.chiFam hVeq app P1) = (s : ℂ) := by
    have he := hall P1
    rw [hyp.sigmaCoeff_sub_smul_chiFam_diff hVeq app X s P1 P2 P1, if_pos rfl,
      if_neg (Ne.symm hPne)] at he
    change hyp.sigmaCoeff hVeq app X P1 = _
    linear_combination he
  have hc2 : ClassFunction.inner X (hyp.chiFam hVeq app P2) = -(s : ℂ) := by
    have he := hall P2
    rw [hyp.sigmaCoeff_sub_smul_chiFam_diff hVeq app X s P1 P2 P2, if_neg hPne, if_pos rfl] at he
    change hyp.sigmaCoeff hVeq app X P2 = _
    linear_combination he
  have h11 : ClassFunction.inner (hyp.chiFam hVeq app P1) (hyp.chiFam hVeq app P1) = 1 := by
    rw [(hyp.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  have h22 : ClassFunction.inner (hyp.chiFam hVeq app P2) (hyp.chiFam hVeq app P2) = 1 := by
    rw [(hyp.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  have h12 : ClassFunction.inner (hyp.chiFam hVeq app P1) (hyp.chiFam hVeq app P2) = 0 := by
    rw [(hyp.chiFam_spec hVeq app).2.2.1, if_neg hPne]
  have h21 : ClassFunction.inner (hyp.chiFam hVeq app P2) (hyp.chiFam hVeq app P1) = 0 := by
    rw [(hyp.chiFam_spec hVeq app).2.2.1, if_neg (Ne.symm hPne)]
  have hc1' : ClassFunction.inner (hyp.chiFam hVeq app P1) X = (s : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hc1, star_intCast]
  have hc2' : ClassFunction.inner (hyp.chiFam hVeq app P2) X = -(s : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hc2, star_neg, star_intCast]
  have hsq : (s : ℂ) * (s : ℂ) = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hself : ClassFunction.inner
      (X - (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2))
      (X - (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2)) = 0 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hX2, hc1,
      hc2, hc1', hc2', h11, h22, h12, h21, star_intCast]
    linear_combination (-2 : ℂ) * hsq
  have hfin := eq_zero_of_inner_self_re_eq_zero (G := G)
    (φ := X - (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2)) (by rw [hself]; simp)
  rwa [sub_eq_zero] at hfin

/-- **Norm-`2` Dade-image trichotomy endgame** (Peterfalvi (4.8) conclusion (3) / (10.5)).  A virtual
character `X ∈ ℤ[Irr G]` with `‖X‖² = 2` whose difference `ψ = X − s·(χ_{P₁} − χ_{P₂})` (`s = ±1`,
`P₁ ≠ P₂`) vanishes on `V` satisfies `X = s·(χ_{P₁} − χ_{P₂})`.

`ψ`'s `σ`-coefficient grid is additively separable (3.7) with `NC(ψ) ≤ 4` (the `NC(X) ≤ 2` of the
norm-`2` `X` plus the two indices `P₁, P₂`).  As `w₁, w₂` are coprime odd (`≥ 3`), one of
`w₁ + 2 ≤ w₂`, `w₂ + 2 ≤ w₁` holds, so `NC(ψ) < 2·min(w₁,w₂)` and the (3.8) trichotomy
`grid_trichotomy` applies; the constant-column/row branches are impossible
(`grid_no_constant_column` on the grid resp. transpose, using `NC(X) ≤ 2` and `σ`-coefficients in
`{0,±1}`), so all coefficients vanish and `eq_smul_chiFam_diff_of_all_sigmaCoeff_zero` finishes.
Generalises the §6 `certainType_diff_dade_eq`. -/
theorem eq_smul_chiFam_diff_of_vanishOnV (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {X : ClassFunction G ℂ} (hXZ : X ∈ ZIrr G) (hX2 : ClassFunction.inner X X = 2)
    {P1 P2 : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)}
    (hPne : P1 ≠ P2) {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hψV : ∀ v ∈ hyp.V,
        (X - (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2)) v = 0) :
    X = (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2) := by
  classical
  haveI : Finite G := Finite.of_fintype G
  haveI : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : Nonempty ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := ⟨1⟩
  haveI : Nonempty ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := ⟨1⟩
  apply hyp.eq_smul_chiFam_diff_of_all_sigmaCoeff_zero hVeq app hX2 hPne hs
  set a : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) → ℂ :=
    fun pq => hyp.sigmaCoeff hVeq app
      (X - (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2)) pq with ha
  set Gr : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) → ℂ :=
    fun pq => hyp.sigmaCoeff hVeq app X pq with hGr
  have hae : ∀ pq, a pq = Gr pq - (s : ℂ) *
      ((if P1 = pq then (1 : ℂ) else 0) - (if P2 = pq then (1 : ℂ) else 0)) :=
    fun pq => hyp.sigmaCoeff_sub_smul_chiFam_diff hVeq app X s P1 P2 pq
  have hG2 : {x | Gr x ≠ 0}.ncard ≤ 2 := hyp.ncard_sigmaCoeff_ne_zero_le_two hVeq app hXZ hX2
  have hG01 : ∀ x, Gr x = 0 ∨ Gr x = 1 ∨ Gr x = -1 :=
    fun x => hyp.sigmaCoeff_eq_zero_or_one_of_inner_self_two hVeq app hXZ hX2 x
  have hsc : (s : ℂ) = 1 ∨ (s : ℂ) = -1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hadd : ∀ p p' q q', a (p, q) + a (p', q') = a (p, q') + a (p', q) :=
    fun p p' q q' => hyp.sigmaCoeff_add_eq hVeq app hψV p p' q q'
  have hNC4 : {x | a x ≠ 0}.ncard ≤ 4 := by
    have hsub : {x | a x ≠ 0} ⊆ {x | Gr x ≠ 0} ∪ {P1, P2} := by
      intro x hx
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or, not_not] at hcon
      exact hx (by rw [hae x, hcon.1, if_neg (Ne.symm hcon.2.1), if_neg (Ne.symm hcon.2.2)]; ring)
    have hbpair : ({P1, P2} : Set _).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    calc {x | a x ≠ 0}.ncard ≤ ({x | Gr x ≠ 0} ∪ {P1, P2}).ncard :=
          Set.ncard_le_ncard hsub (Set.finite_univ.subset (Set.subset_univ _))
      _ ≤ {x | Gr x ≠ 0}.ncard + ({P1, P2} : Set _).ncard := Set.ncard_union_le _ _
      _ ≤ 2 + 2 := add_le_add hG2 hbpair
      _ = 4 := rfl
  have h3w1 : 3 ≤ Nat.card hyp.W1 := hyp.three_le_card_W1
  have h3w2 : 3 ≤ Nat.card hyp.W2 := hyp.three_le_card_W2
  have hcard1 : Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) = Nat.card hyp.W1 :=
    hyp.card_charGroup_subgroupOf hyp.W1_le_W
  have hcard2 : Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) = Nat.card hyp.W2 :=
    hyp.card_charGroup_subgroupOf hyp.W2_le_W
  have hodd1 : Odd (Nat.card hyp.W1) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W1_le_W)
  have hodd2 : Odd (Nat.card hyp.W2) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W2_le_W)
  have hcop : Nat.Coprime (Nat.card hyp.W1) (Nat.card hyp.W2) := hyp.W_card_coprime
  have hwne : Nat.card hyp.W1 ≠ Nat.card hyp.W2 := by
    intro he; rw [he, Nat.Coprime, Nat.gcd_self] at hcop; omega
  rcases lt_or_gt_of_ne hwne with hlt | hgt
  · have hgap : Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) + 2
        ≤ Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := by
      rw [hcard1, hcard2]; obtain ⟨k1, hk1⟩ := hodd1; obtain ⟨k2, hk2⟩ := hodd2; omega
    have hNClt : {x | a x ≠ 0}.ncard
        < 2 * Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := by rw [hcard1]; omega
    rcases grid_trichotomy a hadd hgap hNClt with hz | ⟨j₀, c, hc, h1, h2⟩ | ⟨i₀, c, hc, h1, h2⟩
    · exact hz
    · exact (grid_no_constant_column (by rw [← Nat.card_eq_fintype_card, hcard1]; exact h3w1)
        Gr hG2 hG01 P1 P2 hPne hsc a hae hc h1 h2).elim
    · exact (grid_no_constant_row (by rw [← Nat.card_eq_fintype_card, hcard2]; exact h3w2)
        Gr hG2 hG01 P1 P2 hPne hsc a hae hc h1 h2).elim
  · set aT : ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) → ℂ :=
      fun x => a (x.2, x.1) with haT
    have hgap : Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) + 2
        ≤ Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := by
      rw [hcard1, hcard2]; obtain ⟨k1, hk1⟩ := hodd1; obtain ⟨k2, hk2⟩ := hodd2; omega
    have haddT : ∀ q q' p p', aT (q, p) + aT (q', p') = aT (q, p') + aT (q', p) :=
      fun q q' p p' => by simp only [haT]; linear_combination hadd p p' q q'
    have hNCltT : {x | aT x ≠ 0}.ncard
        < 2 * Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := by
      have h4 : {x | aT x ≠ 0}.ncard ≤ 4 :=
        le_trans (Set.ncard_le_ncard_of_injOn Prod.swap (fun x hx => hx)
          (Prod.swap_injective.injOn) (Set.toFinite _)) hNC4
      rw [hcard2]; omega
    rcases grid_trichotomy aT haddT hgap hNCltT with hz | ⟨p₀, c, hc, h1, h2⟩ | ⟨q₀, c, hc, h1, h2⟩
    · intro pq; exact hz (pq.2, pq.1)
    · exact (grid_no_constant_row (by rw [← Nat.card_eq_fintype_card, hcard2]; exact h3w2)
        Gr hG2 hG01 P1 P2 hPne hsc a hae hc (fun q => h1 q) (fun i j hi => h2 j i hi)).elim
    · exact (grid_no_constant_column (by rw [← Nat.card_eq_fintype_card, hcard1]; exact h3w1)
        Gr hG2 hG01 P1 P2 hPne hsc a hae hc (fun p => h1 p) (fun i j hj => h2 j i hj)).elim

end OddOrder.Peterfalvi.S05.TICyclicHypothesis
