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

open scoped Classical in
/-- **The non-abelian `p`-group branch: `𝒮(S')` coherent** (Peterfalvi (3)–(6), pp. 147–148).
For a non-abelian `p`-group `Q₁` (`d` odd, `|G|` odd, `Q` Hall), `𝒮(S')` is coherent.  With
`Z = ⁅Q₁,Q₁⁆ ∩ Z(Q₁) ≠ 1`, step (3) makes `𝒳 = 𝒮 − 𝒮(Z) = XsetOf ⊥ Z` coherent
(`endgame_Xset_coherent`); the endgame steps (4)–(8) make `𝒳 ∪ 𝒴` coherent
(`xset_qder_union_coherent`, `𝒴 = 𝒮(Q')`) with the anchor package `exists_anchor_data`, the
Remark facts on `𝒴` (`ssetOf_Qder_coherent`, `two_le_ncard_SsetOf_Qder`), and a witness pair of
conjugates; restricting to `𝒳₁ ∪ 𝒴` (`isCoherent_subset`, `𝒳₁ = 𝒳 ∩ 𝒮(S') = XsetOf S' Z`) and
adjoining the rest of `𝒮(S')` (`ssetOf_sder_coherent_of_xset_qder_union`) closes it. -/
theorem ssetOf_sder_coherent_of_nonabelian
    (hd : Odd hyp.d) (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    (hoddG : Odd (Nat.card G)) (hHallG : Nat.Coprime (Nat.card ↥hyp.Q) hyp.Q.index)
    (hnil : Group.IsNilpotent ↥hyp.Q1)
    {p : ℕ} (hp : p.Prime) (hQ1p : IsPGroup p ↥hyp.Q1) (hnonab : ⁅hyp.Q1, hyp.Q1⁆ ≠ ⊥) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsetOf hyp.Sder) hyp.A) := by
  classical
  set Z : Subgroup G := hyp.endgameZ with hZdef
  have hZQ1 : Z ≤ hyp.Q1 := hyp.endgameZ_le_Q1
  have hZne : Z ≠ ⊥ := hyp.endgameZ_ne_bot hp hQ1p hnonab
  have hZQder : Z ≤ hyp.Qder := hyp.endgameZ_le_Qder
  have hZcent : ∀ w ∈ Z, ∀ y ∈ hyp.Q1, ⁅w, y⁆ = 1 :=
    fun w hw y hy => hyp.endgameZ_centralizes hw hy
  have hZH : ∀ h ∈ hyp.H, ∀ x ∈ Z, h * x * h⁻¹ ∈ Z :=
    fun h hh x hx => hyp.endgameZ_conj_mem_of_mem_H hh hx
  -- the three `H`-normal instances (as in `endgame_Xset_coherent`)
  haveI : (hyp.Sder.subgroupOf hyp.H).Normal :=
    hyp.subgroupOf_H_normal_of_conj_mem fun h hh x hx => hyp.Sder_conj_mem_of_mem_H hh hx
  haveI : (Z.subgroupOf hyp.H).Normal :=
    hyp.subgroupOf_H_normal_of_conj_mem hZH
  -- the no-real-character fact (Lemma 2(c)) for the conjugate witnesses
  have hnoreal := hasNoRealCharacters_Sset hyp hd hQ1odd
  -- (3): `𝒳 = XsetOf ⊥ Z` is coherent
  have hcohX := (hyp.endgame_Xset_coherent hd hp hQ1p hnonab).some
  -- (4) anchor package
  obtain ⟨χ₁, a, hχ₁X, ha, hχ₁deg, hXdiff⟩ :=
    hyp.exists_anchor_data hp hQ1p hZQ1 hZne hZQder hZH
  have hχ₁S : χ₁ ∈ hyp.Sset := hyp.XsetOf_subset_Sset ⊥ Z hχ₁X
  have hχ₂X : χ₁.conj ∈ hyp.XsetOf ⊥ Z := hyp.conj_mem_XsetOf hχ₁X
  have hχ₂ne : χ₁.conj ≠ χ₁ := fun h => hnoreal hχ₁S h
  -- `𝒴 = 𝒮(Q')` and its Remark facts
  have hlt : hyp.S ⊔ hyp.Qder < hyp.Q := hyp.sup_S_Qder_lt_Q hnil
  have hYne : (hyp.SsetOf hyp.Qder).Nonempty := hyp.ssetOf_Qder_nonempty hlt
  have hYS : hyp.SsetOf hyp.Qder ⊆ hyp.Sset := fun x hx => hx.1
  have hcohY := (hyp.ssetOf_Qder_coherent hd hQ1odd hYne).some
  obtain ⟨η₁, hη₁Y⟩ := hYne
  have hη₁S : η₁ ∈ hyp.Sset := hYS hη₁Y
  have hη₁d : η₁ (1 : ↥hyp.H) = (hyp.d : ℂ) := hyp.apply_one_eq_d_of_mem_SsetOf_Qder hη₁Y
  have hη₂Y : η₁.conj ∈ hyp.SsetOf hyp.Qder := hyp.conj_mem_SsetOf hη₁Y
  have hη₂ne : η₁.conj ≠ η₁ := fun h => hnoreal hη₁S h
  have hm : 2 ≤ (hyp.SsetOf hyp.Qder).ncard :=
    hyp.two_le_ncard_SsetOf_Qder hd hQ1odd ⟨η₁, hη₁Y⟩
  -- the `𝒴`-difference support and the keystone support
  have hYdiff : ∀ ψ ∈ hyp.SsetOf hyp.Qder,
      ψ - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) (hyp.SsetOf hyp.Qder) hyp.A :=
    fun ψ hψ => ⟨Submodule.sub_mem _ (Submodule.subset_span hψ) (Submodule.subset_span hη₁Y),
      hyp.diff_support_subset_A_of_mem_SsetOf_Qder hψ hη₁Y⟩
  have hsupp : χ₁ - a • η₁ ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) hyp.Sset hyp.A :=
    hyp.keystone_mem_zSupportedSpan hχ₁S hη₁S (by rw [hχ₁deg, hη₁d])
  -- a nontrivial `z ∈ Z^#`
  haveI : Nontrivial ↥Z := (Subgroup.nontrivial_iff_ne_bot _).mpr hZne
  obtain ⟨z₀, hz₀ne⟩ := exists_ne (1 : ↥Z)
  have hz₀H : (z₀ : G) ∈ hyp.H := hyp.Q_le_H (hyp.Q1_le_Q (hZQ1 z₀.2))
  set z : ↥hyp.H := ⟨(z₀ : G), hz₀H⟩ with hzdef
  have hzZ : (z : G) ∈ Z := z₀.2
  have hz1 : z ≠ 1 := fun h => hz₀ne (Subtype.ext (by simpa [hzdef] using congrArg Subtype.val h))
  -- (4)–(8): `𝒳 ∪ 𝒴` is coherent
  have hcohXY := hyp.xset_qder_union_coherent hZQ1 hZcent hoddG hHallG hcohX hχ₁X ha hχ₁deg
    hXdiff hχ₂X hχ₂ne hYS (fun φ hφ => hyp.xsetOf_bot_disjoint_ssetOf_Qder hZQder hφ)
    hcohY hη₁Y hYdiff hη₂Y hη₂ne hm hsupp hzZ hz1
  -- restrict to `𝒳₁ ∪ 𝒴` (`𝒳₁ = XsetOf S' Z`)
  have hXX' : hyp.XsetOf hyp.Sder Z ∪ hyp.SsetOf hyp.Qder
      ⊆ hyp.XsetOf ⊥ Z ∪ hyp.SsetOf hyp.Qder :=
    Set.union_subset_union (fun x hx => ⟨hyp.ssetOf_antitone bot_le hx.1, hx.2⟩) (subset_refl _)
  have hne : ∃ φ : ClassFunction ↥hyp.H ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
        (hyp.XsetOf hyp.Sder Z ∪ hyp.SsetOf hyp.Qder) hyp.A ∧ φ ≠ 0 :=
    ⟨η₁.conj - η₁,
      ⟨Submodule.sub_mem _ (Submodule.subset_span (Set.mem_union_right _ hη₂Y))
          (Submodule.subset_span (Set.mem_union_right _ hη₁Y)),
        hyp.diff_support_subset_A_of_mem_SsetOf_Qder hη₂Y hη₁Y⟩,
      fun h => hη₂ne (sub_eq_zero.mp h)⟩
  have hcohB : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.XsetOf hyp.Sder Z ∪ hyp.SsetOf hyp.Qder) hyp.A) :=
    ⟨hyp.isCoherent_subset hcohXY.some hXX' hne⟩
  -- (6) finish: `𝒮(S')` is coherent
  exact hyp.ssetOf_sder_coherent_of_xset_qder_union hd hQ1odd hZQ1 hZne hZcent hZH hcohB
    ⟨η₁, hη₁Y⟩

end Finish

end Hypothesis

/-! ## The Feit–Sibley Theorem (pp. 146–150) -/

variable {G : Type*} [Group G]

/-- **Peterfalvi Appendix IV, Theorem** (pp. 146–150; Feit–Sibley).  If `d = |D|` is odd, then
`𝒮` is coherent with respect to the induction isometry `τ = Ind_H^G` of Lemma 2(b).

The reduction declaration (pp. 146–147) splits on the structure of `Q₁`:

* `|Q₁|` has two distinct prime divisors — reductions (1)+(2)
  (`sset_coherent_of_two_primes`);
* `Q₁` abelian (`⁅Q₁,Q₁⁆ = ⊥`) — the Remark plus reduction (2)
  (`sset_coherent_of_commutator_Q1_eq_bot`);
* `Q₁` a non-abelian `p`-group — the endgame steps (3)–(8)
  (`ssetOf_sder_coherent_of_nonabelian`) plus reduction (2).

The `p`-power case is extracted from "not two primes" via
`Nat.eq_prime_pow_of_unique_prime_dvd`, and `|Q₁| ≠ 1` from `Q1_not_two_group`
(a trivial group is a `2`-group).  The three added hypotheses `Odd |G|`,
`Group.IsNilpotent Q₁` and `Nat.Coprime |Q| [G:Q]` are the standing hypotheses of
the Appendix IV configuration (Peterfalvi's global odd-order hypothesis (E), the
nilpotent Frobenius-kernel factor, and `Q` a Hall subgroup). -/
theorem feit_sibley_coherence [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis G) [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
    (hd : Odd hyp.d) (hoddG : Odd (Nat.card G))
    (hnil : Group.IsNilpotent ↥hyp.Q1)
    (hHallG : Nat.Coprime (Nat.card ↥hyp.Q) hyp.Q.index) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  classical
  letI : Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `|Q₁|` is odd (`Q₁ ≤ G`, `|G|` odd) and `≠ 1` (`Q₁` is not a `2`-group)
  have hQ1odd : Odd (Nat.card ↥hyp.Q1) :=
    hoddG.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.Q1)
  have hN1 : Nat.card ↥hyp.Q1 ≠ 1 := fun h1 =>
    hyp.Q1_not_two_group (IsPGroup.of_card (p := 2) (n := 0) (by rw [h1, pow_zero]))
  by_cases hab : ⁅hyp.Q1, hyp.Q1⁆ = ⊥
  · -- abelian `Q₁`
    exact hyp.sset_coherent_of_commutator_Q1_eq_bot hd hQ1odd hnil hab
  · by_cases htwo : ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧
        p ∣ Nat.card ↥hyp.Q1 ∧ r ∣ Nat.card ↥hyp.Q1
    · -- two distinct prime divisors
      obtain ⟨p, r, hp, hr, hpr, hpd, hrd⟩ := htwo
      exact hyp.sset_coherent_of_two_primes hd hQ1odd hnil hp hr hpr hpd hrd
    · -- `¬ two primes`: `Q₁` is a non-abelian `p`-group
      push Not at htwo
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hN1
      have hQ1p : IsPGroup p ↥hyp.Q1 :=
        IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (by
          intro d hd' hdvd
          by_contra hdp
          exact htwo d p hd' hp hdp hdvd hpd))
      have hlt : hyp.S ⊔ hyp.Qder < hyp.Q := hyp.sup_S_Qder_lt_Q hnil
      exact hyp.sset_coherent_of_ssetOf_sder_coherent hd hQ1odd hnil hlt
        (hyp.ssetOf_sder_coherent_of_nonabelian hd hQ1odd hoddG hHallG hnil hp hQ1p hab)

end OddOrder.Peterfalvi.Appendices.FeitSibley
