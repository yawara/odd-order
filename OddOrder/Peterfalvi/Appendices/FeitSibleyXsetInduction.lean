/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyQ1Component

/-!
# Peterfalvi Appendix IV: the `𝒳`-relative `S`-side induction (step (3) Part B)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix IV, p. 147 (campaign issue 1054, Part B).  The mirror of reduction (2)
relative to `𝒳`: coherence of `𝒳₁ = 𝒳(S', Z)` (Part A,
`xsetOf_sder_coherent`) descends along `S`-side chief factors to
`𝒳 = 𝒳(⊥, Z) = 𝒮 − 𝒮(Z)`.

* `false_of_xset_induction_bounds` — the closing arithmetic (p. 147):
  `m·qz·(z−1) ≤ 2d·tθ·a`, `tθ² ≤ qz`, `a² ≤ m·qz`, `z ≥ 2d+1`, `m ≥ 2` are
  jointly contradictory (`m·(z−1)² ≤ 4d²` yet `(z−1)² ≥ 4d²` and `m ≥ 2`).
* `sq_ratio_sum_le_of_adjoin_incoherent_anchored` — the Lemma 1(a)
  contrapositive at a general anchor `χ₀(1) = d·t₀`, `t₀ ∣ a` (the
  rational-ratio Lemma 1(a) of issue 1050; generalises the degree-`d` form
  `sq_ratio_sum_le_of_adjoin_incoherent`).
* `exists_counterexample_anchored_of_not_coherent` — the counterexample
  extraction with a **per-`ψ` anchor supply**: Part B's anchor
  `Ind(θ ∘ q1Proj) ∈ 𝒳₁` (`exists_anchor_of_mem_XsetOf`) depends on the
  failing `ψ`, unlike the fixed degree-`d` anchor of reductions (1)(2).
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

/-! ## The closing arithmetic -/

/-- **The Part B closing arithmetic** (p. 147): the counting bound
`m·qz·(z−1) ≤ d·(2·tθ·a)`, the anchor bound `tθ² ≤ qz` ([Is] 2.30 at
`D₀ = S·Z`), the `ψ`-bound `a² ≤ m·qz` ([Is] 2.30 at `D₀ = S₁·Z`), the
`d`-odd fixed-point-free bound `z ≥ 2d+1`, and `m ≥ 2` (`S₁ ≤ S' ⊊ S`) are
jointly contradictory: squaring the counting bound gives
`m²·qz²·(z−1)² ≤ 4d²·tθ²·a² ≤ 4d²·qz·m·qz`, so `m·(z−1)² ≤ 4d²`, while
`(z−1)² ≥ 4d²` forces `m ≤ 1`. -/
theorem false_of_xset_induction_bounds {d tθ a m qz z : ℕ}
    (hd : 1 ≤ d) (hqz : 0 < qz)
    (h1 : (m : ℝ) * (qz : ℝ) * ((z : ℝ) - 1) ≤ (d : ℝ) * (2 * (tθ : ℝ) * (a : ℝ)))
    (h2 : tθ ^ 2 ≤ qz)
    (h3 : a ^ 2 ≤ m * qz)
    (h4 : 2 * d + 1 ≤ z)
    (h5 : 2 ≤ m) : False := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hqzR : (0 : ℝ) < (qz : ℝ) := by exact_mod_cast hqz
  have h2R : (tθ : ℝ) ^ 2 ≤ (qz : ℝ) := by exact_mod_cast h2
  have h3R : (a : ℝ) ^ 2 ≤ (m : ℝ) * (qz : ℝ) := by exact_mod_cast h3
  have h4R : 2 * (d : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast h4
  have h5R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h5
  have hz1 : 2 * (d : ℝ) ≤ (z : ℝ) - 1 := by linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hlhs0 : (0 : ℝ) ≤ (m : ℝ) * (qz : ℝ) * ((z : ℝ) - 1) := by
    have hz0 : (0 : ℝ) ≤ (z : ℝ) - 1 := by linarith
    exact mul_nonneg (mul_nonneg hm0.le hqzR.le) hz0
  -- square the counting bound
  have k1 : ((m : ℝ) * (qz : ℝ) * ((z : ℝ) - 1)) ^ 2
      ≤ ((d : ℝ) * (2 * (tθ : ℝ) * (a : ℝ))) ^ 2 := by
    have h := mul_self_le_mul_self hlhs0 h1
    simpa [sq] using h
  -- combine the two degree bounds
  have k2 : (tθ : ℝ) ^ 2 * (a : ℝ) ^ 2 ≤ (qz : ℝ) * ((m : ℝ) * (qz : ℝ)) :=
    mul_le_mul h2R h3R (sq_nonneg _) hqzR.le
  have k3 : (m : ℝ) ^ 2 * (qz : ℝ) ^ 2 * ((z : ℝ) - 1) ^ 2
      ≤ 4 * (d : ℝ) ^ 2 * ((m : ℝ) * (qz : ℝ) ^ 2) := by
    nlinarith [k1, k2, sq_nonneg ((d : ℝ) * (2 * (tθ : ℝ) * (a : ℝ)))]
  -- cancel `m·qz²`
  have k4 : (m : ℝ) * ((z : ℝ) - 1) ^ 2 ≤ 4 * (d : ℝ) ^ 2 := by
    have hden : (0 : ℝ) < (m : ℝ) * (qz : ℝ) ^ 2 := by positivity
    have h := k3
    rw [show (m : ℝ) ^ 2 * (qz : ℝ) ^ 2 * ((z : ℝ) - 1) ^ 2
        = ((m : ℝ) * ((z : ℝ) - 1) ^ 2) * ((m : ℝ) * (qz : ℝ) ^ 2) from by ring,
      show 4 * (d : ℝ) ^ 2 * ((m : ℝ) * (qz : ℝ) ^ 2)
        = (4 * (d : ℝ) ^ 2) * ((m : ℝ) * (qz : ℝ) ^ 2) from by ring] at h
    exact le_of_mul_le_mul_right h hden
  -- `(z−1)² ≥ 4d²` and `m ≥ 2` contradict `m·(z−1)² ≤ 4d²`
  have k5 : 4 * (d : ℝ) ^ 2 ≤ ((z : ℝ) - 1) ^ 2 := by nlinarith [hz1, hdR]
  nlinarith [k4, k5, mul_le_mul_of_nonneg_left k5 hm0.le, h5R, hdR,
    sq_nonneg ((d : ℝ) - 1)]

namespace Hypothesis

variable {G : Type*} [Group G] (hyp : Hypothesis G)

section AnchoredExtraction

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
variable [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]

/-- **The counterexample degree bound at a general anchor** (the rational-ratio
Lemma 1(a) contrapositive, issue 1050): if adjoining the fresh conjugate pair
`{χ, χ̄}` to a coherent, conjugation-closed `S₁ ⊆ 𝒮` containing an anchor of
degree `d·t₀` with `t₀ ∣ a` *breaks* coherence, then Peterfalvi's strict degree
inequality must fail: `∑_{x ∈ S₁} m(x)² ≤ 2·t₀·a`, where `x(1) = d·m(x)` and
`χ(1) = d·a`.  The contrapositive of `coherent_insert_pair_of_two_mul_lt_sum`;
the degree-`d` anchor form `sq_ratio_sum_le_of_adjoin_incoherent` is the case
`t₀ = 1`. -/
theorem sq_ratio_sum_le_of_adjoin_incoherent_anchored [Finite G] (hd : Odd hyp.d)
    (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    {S₁ : Set (ClassFunction ↥hyp.H ℂ)} (hS₁S : S₁ ⊆ hyp.Sset) (hS₁fin : S₁.Finite)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁ hyp.A))
    {χ₀ : ClassFunction ↥hyp.H ℂ} (hχ₀S₁ : χ₀ ∈ S₁)
    {t₀ : ℕ} (ht₀pos : 0 < t₀)
    (hχ₀deg : χ₀ (1 : ↥hyp.H) = (hyp.d : ℂ) * (t₀ : ℂ))
    {χ : ClassFunction ↥hyp.H ℂ} (hχS : χ ∈ hyp.Sset)
    (hχS₁ : χ ∉ S₁) (hχbarS₁ : χ.conj ∉ S₁)
    {a : ℕ} (hχdeg : χ (1 : ↥hyp.H) = (hyp.d : ℂ) * (a : ℂ)) (hdvd : t₀ ∣ a)
    (hfail : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (S₁ ∪ {χ, χ.conj}) hyp.A)) :
    ∃ m : ClassFunction ↥hyp.H ℂ → ℕ,
      (∀ x ∈ S₁, x (1 : ↥hyp.H) = (hyp.d : ℂ) * (m x : ℂ)) ∧
      (∑ x ∈ hS₁fin.toFinset, ((m x : ℝ)) ^ 2) ≤ 2 * (t₀ : ℝ) * (a : ℝ) := by
  classical
  have hm : ∀ x ∈ S₁, ∃ mx : ℕ, x (1 : ↥hyp.H) = (hyp.d : ℂ) * (mx : ℂ) :=
    fun x hx => (hyp.exists_apply_one_eq_d_mul (hS₁S hx)).imp fun _ h => h.2
  choose! m hmdeg using hm
  refine ⟨m, hmdeg, ?_⟩
  by_contra hlt
  push Not at hlt
  apply hfail
  have hd0 : (hyp.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.d_pos.ne'
  have hmχ₀ : m χ₀ = t₀ := by
    have h1 := hmdeg χ₀ hχ₀S₁
    rw [hχ₀deg] at h1
    exact_mod_cast (mul_left_cancel₀ hd0 h1).symm
  exact hyp.coherent_insert_pair_of_two_mul_lt_sum hd hQ1odd hS₁S hS₁fin hS₁conj hcoh
    hχ₀S₁ hmdeg (by rw [hmχ₀]; exact ht₀pos)
    hχS hχS₁ hχbarS₁ hχdeg (by rw [hmχ₀]; exact hdvd)
    (by rw [hmχ₀]; exact hlt)

open scoped Classical in
/-- **The Part B counterexample extraction** (Peterfalvi's "Suppose `𝒳 ∩ 𝒮(S₂)`
is not coherent.  By Lemma 1(a), there is a character `ψ` such that
`∑ χ(1)² ≤ 2χ(1)ψ(1)`"): if a coherent, conjugation-closed base `B` sits inside
a finite, conjugation-closed `Y ⊆ 𝒮` that is *not* coherent, and every `ψ ∈ Y`
carries an anchor in `B₀ ⊆ B` whose degree `d·tθ` divides `ψ(1) = d·a`, then for
some `ψ ∈ Y` and its anchor data `∑_{x ∈ B} m(x)² ≤ 2·tθ·a`.

The anchor is chosen **after** the failing `ψ` is found (unlike
`exists_counterexample_of_not_coherent`, whose degree-`d` anchor is fixed in
advance) — in Part B the anchor `Ind(θ ∘ q1Proj) ∈ 𝒳₁`
(`exists_anchor_of_mem_XsetOf`) is built from `ψ`'s own isotypic
`Q₁`-constituent. -/
theorem exists_counterexample_anchored_of_not_coherent [Finite G] (hd : Odd hyp.d)
    (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    {B₀ B Y : Set (ClassFunction ↥hyp.H ℂ)} (hB₀B : B₀ ⊆ B) (hBY : B ⊆ Y)
    (hYS : Y ⊆ hyp.Sset) (hYfin : Y.Finite)
    (hYconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Y)
    (hBconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate B)
    (hcohB : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau B hyp.A))
    (hanchor : ∀ ψ ∈ Y, ∃ (χθ : ClassFunction ↥hyp.H ℂ) (tθ a : ℕ),
      χθ ∈ B₀ ∧ 0 < tθ ∧ 0 < a ∧
      χθ (1 : ↥hyp.H) = (hyp.d : ℂ) * (tθ : ℂ) ∧
      ψ (1 : ↥hyp.H) = (hyp.d : ℂ) * (a : ℂ) ∧ tθ ∣ a)
    (hfail : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)) :
    ∃ (ψ χθ : ClassFunction ↥hyp.H ℂ) (tθ a : ℕ) (m : ClassFunction ↥hyp.H ℂ → ℕ),
      ψ ∈ Y ∧ χθ ∈ B₀ ∧ 0 < tθ ∧ 0 < a ∧
      χθ (1 : ↥hyp.H) = (hyp.d : ℂ) * (tθ : ℂ) ∧
      ψ (1 : ↥hyp.H) = (hyp.d : ℂ) * (a : ℂ) ∧
      (∀ x ∈ B, x (1 : ↥hyp.H) = (hyp.d : ℂ) * (m x : ℂ)) ∧
      (∑ x ∈ (hYfin.subset hBY).toFinset, ((m x : ℝ)) ^ 2)
        ≤ 2 * (tθ : ℝ) * (a : ℝ) := by
  classical
  have hnoreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters Y :=
    (hasNoRealCharacters_Sset hyp hd hQ1odd).mono hYS
  obtain ⟨N, pair, hUnion, hstep, -⟩ :=
    exists_conjPair_pairUnion_eq hBY hYfin hYconj hBconj hnoreal
  obtain ⟨i, hiN, hcoh_i, hfail_i⟩ :=
    exists_first_incoherent_step (τ := hyp.tau) (A := hyp.A) hcohB (hUnion ▸ hfail)
  obtain ⟨hconj_i, hmemY_i, hfresh1, hfresh2⟩ := hstep i hiN
  -- the accumulated family `S₁ = pairUnion B pair i` and its closure properties
  have hsub : ∀ j, j ≤ N →
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair j ⊆ Y := by
    intro j hjN x hx
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hx with hB | ⟨k, hkj, hk⟩
    · exact hBY hB
    · have hkN : k < N := by omega
      obtain ⟨hc, hY1, -, -⟩ := hstep k hkN
      rcases (by simpa [OddOrder.Peterfalvi.S07.pairSet] using hk : x = (pair k).1 ∨
          x = (pair k).2) with rfl | rfl
      · exact hY1
      · rw [hc]
        exact hYconj hY1
  have hconj_closed : ∀ j, j ≤ N → OddOrder.Peterfalvi.S03.ClosedUnderConjugate
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair j) := by
    intro j hjN
    induction j with
    | zero => simpa using hBconj
    | succ j ihj =>
      intro x hx
      rw [OddOrder.Peterfalvi.S07.pairUnion_succ] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihj (by omega) hx)
      · obtain ⟨hcj, -, -, -⟩ := hstep j (by omega)
        rcases (by simpa [OddOrder.Peterfalvi.S07.pairSet] using hx : x = (pair j).1 ∨
            x = (pair j).2) with rfl | rfl
        · exact Or.inr (by
            rw [← hcj]
            simp [OddOrder.Peterfalvi.S07.pairSet])
        · exact Or.inr (by
            rw [hcj, ClassFunction.conj_conj]
            simp [OddOrder.Peterfalvi.S07.pairSet])
  -- the failing pair's first member and its anchor
  have hψY : (pair i).1 ∈ Y := hmemY_i
  obtain ⟨χθ, tθ, a, hχθB₀, htθpos, hapos, hχθdeg, hψdeg, hdvd⟩ :=
    hanchor (pair i).1 hψY
  -- apply the anchored Lemma 1(a) contrapositive at the failing step
  have hS₁S : OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair i ⊆ hyp.Sset :=
    fun x hx => hYS (hsub i (by omega) hx)
  have hχθS₁ : χθ ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair i :=
    OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl (hB₀B hχθB₀))
  have hfail' : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      ((OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair i)
        ∪ {(pair i).1, ((pair i).1).conj}) hyp.A) := by
    intro h
    apply hfail_i
    rw [OddOrder.Peterfalvi.S07.pairUnion_succ]
    have hps : OddOrder.Peterfalvi.S07.pairSet (L := ↥hyp.H) pair i
        = {(pair i).1, ((pair i).1).conj} := by
      rw [OddOrder.Peterfalvi.S07.pairSet, hconj_i]
    rw [hps]
    exact h
  have hfresh2' : ((pair i).1).conj ∉
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair i := by
    rw [← hconj_i]
    exact hfresh2
  obtain ⟨m, hmdeg, hmsum⟩ := hyp.sq_ratio_sum_le_of_adjoin_incoherent_anchored hd hQ1odd
    hS₁S (hYfin.subset (hsub i (by omega))) (hconj_closed i (by omega)) hcoh_i
    hχθS₁ htθpos hχθdeg (hYS hψY) hfresh1 hfresh2' hψdeg hdvd hfail'
  refine ⟨(pair i).1, χθ, tθ, a, m, hψY, hχθB₀, htθpos, hapos, hχθdeg, hψdeg,
    fun x hx => hmdeg x (OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hx)), ?_⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hmsum
  · intro x hx
    rw [Set.Finite.mem_toFinset] at hx ⊢
    exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hx)
  · intro x _ _
    positivity

end AnchoredExtraction

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
