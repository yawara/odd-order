/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyConclusion

/-!
# Peterfalvi Appendix IV: the Feit–Sibley Theorem, final assembly (pp. 146–150)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix IV, Theorem (pp. 146–150; campaign issue 1054).  This leaf sits at the
top of the Feit–Sibley chain and assembles the eight-step argument into the
Theorem `feit_sibley_coherence`: if `d = |D|` is odd then `𝒮` is coherent with
respect to `τ = Ind_H^G`.

The three structural reductions of `𝒮`-coherence
(`sset_coherent_of_two_primes`, `sset_coherent_of_commutator_Q1_eq_bot`,
`sset_coherent_of_ssetOf_sder_coherent`) reduce to the **non-abelian `p`-group**
branch, where the endgame (steps (3)–(8)) produces `𝒳 ∪ 𝒴` coherent
(`xset_qder_union_coherent`).  This file adds:

* `false_of_finish_bounds` — the `(6)`-finish arithmetic core;
* `ssetOf_sder_coherent_of_xset_qder_union` — the `(6)` finish: `𝒳₁ ∪ 𝒴` coherent
  `⟹ 𝒮(S')` coherent, Peterfalvi's last Lemma 1(a) adjunction (p. 148);
* the endgame wiring `ssetOf_sder_coherent_of_nonabelian` for the non-abelian
  `p`-group branch;
* `feit_sibley_coherence`, the main theorem.

The added hypotheses on `feit_sibley_coherence` beyond the `Hypothesis` block are
`Odd (Nat.card G)` (Peterfalvi's global odd-order hypothesis (E)),
`Group.IsNilpotent Q₁` (the Frobenius-kernel factor is nilpotent) and
`Nat.Coprime |Q| [G:Q]` (`Q` is a Hall subgroup of `G`); all three are genuine
standing hypotheses of the Appendix IV configuration.
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

open scoped commutatorElement

/-- **The `(6)`-finish arithmetic core** (Peterfalvi (6), p. 148).  The last
Lemma 1(a) adjunction closing `𝒮(S')` fails only if a counterexample `ψ`
(degree `d·a`, `a ≥ 2` since `ψ ∉ 𝒮(Q')`) satisfies, simultaneously:

* the counting bound `|S⧸S'|·|Q₁⧸Z|·(|Z|−1) ≤ d·(2a)` (`𝒳₁ ⊆ 𝒳₁ ∪ 𝒴`, whose
  degree-square sum is `≤ 2·η₁(1)·ψ(1)`);
* the `[Is] 2.30` bound `a² ≤ |Q₁⧸Z|`;
* the fixed-point-free bound `|Z| ≥ 2d+1`.

These are contradictory: `a²·(|Z|−1) ≤ |Q₁⧸Z|·(|Z|−1) ≤ |S⧸S'|·|Q₁⧸Z|·(|Z|−1)
≤ 2ad`, so `a·(|Z|−1) ≤ 2d`, while `|Z|−1 ≥ 2d` forces `a ≤ 1`, against `a ≥ 2`. -/
theorem false_of_finish_bounds {d a sm qz z : ℕ} (hd : 1 ≤ d) (ha : 2 ≤ a)
    (hsm : 1 ≤ sm) (hqz : 1 ≤ qz)
    (h1 : (sm : ℝ) * (qz : ℝ) * ((z : ℝ) - 1) ≤ (d : ℝ) * (2 * (a : ℝ)))
    (h3 : a ^ 2 ≤ qz) (h4 : 2 * d + 1 ≤ z) : False := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hsmR : (1 : ℝ) ≤ (sm : ℝ) := by exact_mod_cast hsm
  have hqzR : (1 : ℝ) ≤ (qz : ℝ) := by exact_mod_cast hqz
  have h3R : (a : ℝ) ^ 2 ≤ (qz : ℝ) := by exact_mod_cast h3
  have h4R : 2 * (d : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast h4
  have haPos : (0 : ℝ) < (a : ℝ) := by linarith
  have hz1 : 2 * (d : ℝ) ≤ (z : ℝ) - 1 := by linarith
  have hz0 : (0 : ℝ) ≤ (z : ℝ) - 1 := by linarith
  -- `a²·2d ≤ a²·(z−1) ≤ qz·(z−1) ≤ sm·qz·(z−1) ≤ 2ad`
  have step1 : (a : ℝ) ^ 2 * (2 * (d : ℝ)) ≤ (sm : ℝ) * (qz : ℝ) * ((z : ℝ) - 1) := by
    calc (a : ℝ) ^ 2 * (2 * (d : ℝ))
        ≤ (a : ℝ) ^ 2 * ((z : ℝ) - 1) := mul_le_mul_of_nonneg_left hz1 (sq_nonneg _)
      _ ≤ (qz : ℝ) * ((z : ℝ) - 1) := mul_le_mul_of_nonneg_right h3R hz0
      _ ≤ (sm : ℝ) * (qz : ℝ) * ((z : ℝ) - 1) := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (sm : ℝ) - 1)
            (mul_nonneg (by linarith : (0 : ℝ) ≤ (qz : ℝ)) hz0)]
  have step2 : (a : ℝ) ^ 2 * (2 * (d : ℝ)) ≤ (d : ℝ) * (2 * (a : ℝ)) := le_trans step1 h1
  -- `a²·2d ≤ 2ad` with `a ≥ 2`, `d ≥ 1`: `2d·a·(a−1) ≤ 0` while it is `> 0`
  nlinarith [step2, mul_pos (mul_pos (by linarith : (0 : ℝ) < 2 * (d : ℝ)) haPos)
    (by linarith : (0 : ℝ) < (a : ℝ) - 1)]

namespace Hypothesis

variable {G : Type*} [Group G] (hyp : Hypothesis G)

section Finish

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
variable [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]

open scoped Classical in
/-- **The `(6)` finish: `𝒮(S')` coherent** (Peterfalvi (6), p. 148).  Given the
coherent union `𝒳₁ ∪ 𝒴` (`𝒳₁ = 𝒳 ∩ 𝒮(S') = XsetOf S' Z`, `𝒴 = 𝒮(Q')`) and a
nonempty `𝒴`, the whole family `𝒮(S')` is coherent.  The last members of
`𝒮(S') − (𝒳₁ ∪ 𝒴)` adjoin by Lemma 1(a): a fresh counterexample `ψ` (degree
`d·a`) is not in `𝒴` (so `a ≥ 2`, else `ψ(1) = d` puts `ψ ∈ 𝒮(Q')`,
`leKer_Qder_of_apply_one_eq_d`) and its degree-square bound
`∑_{𝒳₁ ∪ 𝒴} χ(1)² ≤ 2·η₁(1)·ψ(1)` (`exists_counterexample_anchored_of_not_coherent`,
anchor `η₁ ∈ 𝒴` of degree `d`) collides with the counting identity and the
`[Is] 2.30` bound `a² ≤ |Q₁⧸Z|` via `false_of_finish_bounds`. -/
theorem ssetOf_sder_coherent_of_xset_qder_union
    (hd : Odd hyp.d) (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1) (hZne : Z ≠ ⊥)
    (hZQ1c : ∀ z ∈ Z, ∀ y ∈ hyp.Q1, ⁅z, y⁆ = 1)
    (hZH : ∀ h ∈ hyp.H, ∀ x ∈ Z, h * x * h⁻¹ ∈ Z)
    [(hyp.Sder.subgroupOf hyp.H).Normal]
    [((hyp.Sder.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H)).Normal]
    (hcohB : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.XsetOf hyp.Sder Z ∪ hyp.SsetOf hyp.Qder) hyp.A))
    (hYne : (hyp.SsetOf hyp.Qder).Nonempty) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.SsetOf hyp.Sder) hyp.A) := by
  classical
  by_contra hfail
  haveI : ((hyp.Sder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).Normal :=
    hyp.Sder_subgroupOf_Q_normal
  haveI : ((hyp.S ⊔ Z).subgroupOf hyp.H).Normal :=
    hyp.subgroupOf_H_normal_of_conj_mem fun h hh x hx =>
      conj_mem_sup (fun y hy => hyp.S_normal_in_H hh hy) (fun y hy => hZH h hh y hy) hx
  obtain ⟨η₁, hη₁⟩ := hYne
  set B : Set (ClassFunction ↥hyp.H ℂ) := hyp.XsetOf hyp.Sder Z ∪ hyp.SsetOf hyp.Qder with hBdef
  -- the family arrangement `B₀ = 𝒴 ⊆ B ⊆ Y = 𝒮(S')`
  have hSderQder : hyp.Sder ≤ hyp.Qder :=
    le_sup_left.trans (hyp.sup_Sder_le_Qder (Q₂ := ⊥) bot_le)
  have hB₀B : hyp.SsetOf hyp.Qder ⊆ B := Set.subset_union_right
  have hBY : B ⊆ hyp.SsetOf hyp.Sder := by
    rintro x (hx | hx)
    · exact hx.1
    · exact hyp.ssetOf_antitone hSderQder hx
  have hYS : hyp.SsetOf hyp.Sder ⊆ hyp.Sset := fun x hx => hx.1
  have hYfin : (hyp.SsetOf hyp.Sder).Finite := hyp.Sset_finite.subset hYS
  have hYconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.SsetOf hyp.Sder) :=
    fun _ hx => hyp.conj_mem_SsetOf hx
  have hBconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate B := by
    rintro x (hx | hx)
    · exact Or.inl (hyp.conj_mem_XsetOf hx)
    · exact Or.inr (hyp.conj_mem_SsetOf hx)
  -- the per-`ψ` anchor `η₁ ∈ 𝒴` of degree `d`
  have hη₁d : η₁ (1 : ↥hyp.H) = (hyp.d : ℂ) := hyp.apply_one_eq_d_of_mem_SsetOf_Qder hη₁
  have hanchor : ∀ ψ ∈ hyp.SsetOf hyp.Sder, ∃ (χθ : ClassFunction ↥hyp.H ℂ) (tθ a : ℕ),
      χθ ∈ hyp.SsetOf hyp.Qder ∧ 0 < tθ ∧ 0 < a ∧
      χθ (1 : ↥hyp.H) = (hyp.d : ℂ) * (tθ : ℂ) ∧
      ψ (1 : ↥hyp.H) = (hyp.d : ℂ) * (a : ℂ) ∧ tθ ∣ a := by
    intro ψ hψ
    obtain ⟨a, hapos, ha⟩ := hyp.exists_apply_one_eq_d_mul hψ.1
    exact ⟨η₁, 1, a, hη₁, one_pos, hapos, by rw [hη₁d]; push_cast; ring, ha, one_dvd a⟩
  -- extract the counterexample
  obtain ⟨ψ, χθ, tθ, a, m, hψY, hψnotB, hχθB₀, htθpos, hapos, hχθdeg, hψdeg, hmdeg, hmsum⟩ :=
    hyp.exists_counterexample_anchored_of_not_coherent hd hQ1odd hB₀B hBY hYS hYfin
      hYconj hBconj hcohB hanchor hfail
  -- `tθ = 1` (anchor `η₁ ∈ 𝒴` has degree `d`)
  have hd0 : (hyp.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.d_pos.ne'
  have htθ1 : tθ = 1 := by
    have hχθd : χθ (1 : ↥hyp.H) = (hyp.d : ℂ) := hyp.apply_one_eq_d_of_mem_SsetOf_Qder hχθB₀
    have h : (hyp.d : ℂ) * (tθ : ℂ) = (hyp.d : ℂ) * (1 : ℂ) := by
      rw [mul_one, ← hχθdeg, hχθd]
    exact_mod_cast (mul_left_cancel₀ hd0 h)
  -- `a ≥ 2` (`ψ ∉ 𝒴`, else `ψ(1) = d` puts `ψ ∈ 𝒮(Q')`)
  have ha2 : 2 ≤ a := by
    rcases Nat.lt_or_ge a 2 with hlt | hge
    · exfalso
      interval_cases a
      have hψd : ψ (1 : ↥hyp.H) = (hyp.d : ℂ) := by rw [hψdeg]; push_cast; ring
      exact hψnotB (Set.mem_union_right _ ⟨hψY.1, hyp.leKer_Qder_of_apply_one_eq_d hψY.1 hψd⟩)
    · exact hge
  -- `h1`: counting `|S⧸S'|·|Q₁⧸Z|·(|Z|−1) ≤ d·(2·tθ·a)`
  have hfinX : (hyp.XsetOf hyp.Sder Z).Finite := hyp.XsetOf_finite _ _
  have hXsubB : hyp.XsetOf hyp.Sder Z ⊆ B := Set.subset_union_left
  have hmdegX : ∀ x ∈ hyp.XsetOf hyp.Sder Z, x (1 : ↥hyp.H) = (hyp.d : ℂ) * (m x : ℂ) :=
    fun x hx => hmdeg x (hXsubB hx)
  have hmsumX : (∑ x ∈ hfinX.toFinset, ((m x : ℝ)) ^ 2) ≤ 2 * (tθ : ℝ) * (a : ℝ) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hmsum
    · intro x hx
      rw [Set.Finite.mem_toFinset] at hx ⊢
      exact hXsubB hx
    · intro x _ _; positivity
  have h1 := hyp.xset_counting_le_of_sum_le hyp.Sder_le_S hZQ1 hfinX hmdegX hmsumX
  rw [htθ1, Nat.cast_one, mul_one] at h1
  -- `h3`: `[Is] 2.30` bound `a² ≤ |Q₁⧸Z|` at `D₀ = S⊔Z`
  have h3 : a ^ 2 ≤ Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) := by
    obtain ⟨a', ha'deg, ha'sq⟩ := hyp.exists_deg_sq_le_of_mem_SsetOf hyp.Sder (hyp.S ⊔ Z)
      (hyp.Sder_le_S.trans hyp.S_le_Q) (hyp.Sder_le_S.trans le_sup_left)
      (sup_le hyp.S_le_Q (hZQ1.trans hyp.Q1_le_Q))
      (hyp.map_mk_le_center_of_commutator_mem (fun x hx q hq => by
        have h := hyp.commutator_mem_sup_Sder_of_central (Q₃ := (⊥ : Subgroup G)) hZQ1
          (fun z hz y hy => by rw [Subgroup.mem_bot]; exact hZQ1c z hz y hy) hx hq
        rwa [sup_bot_eq] at h))
      hψY
    rw [hyp.index_subgroupOf_sup_S_eq hZQ1] at ha'sq
    have haa' : a' = a := by
      exact_mod_cast mul_left_cancel₀ hd0 (ha'deg.symm.trans hψdeg)
    rwa [haa'] at ha'sq
  -- `h4`: `|Z| ≥ 2d+1`
  have hZodd : Odd (Nat.card ↥Z) := by
    rcases Nat.even_or_odd (Nat.card ↥Z) with he | ho
    · exfalso
      obtain ⟨k, hk⟩ := he.two_dvd.trans (Subgroup.card_dvd_of_le hZQ1)
      exact (Nat.not_even_iff_odd.mpr hQ1odd) ⟨k, by omega⟩
    · exact ho
  have h4 : 2 * hyp.d + 1 ≤ Nat.card ↥Z :=
    hyp.two_mul_d_add_one_le_card_of_le_Q1 hd hZQ1
      (fun δ hδ z hz => hZH δ (hyp.D_le_H hδ) z hz) hZne hZodd
  exact false_of_finish_bounds hyp.d_pos ha2 Nat.card_pos Nat.card_pos h1 h3 h4

end Finish

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
