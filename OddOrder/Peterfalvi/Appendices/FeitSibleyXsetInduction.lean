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

open scoped commutatorElement

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

/-! ## The `S`-side chief-factor step and induction (step (3) Part B) -/

section SStepInduction

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
variable [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]

open scoped Classical in
omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥hyp.H]
  [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)] in
/-- **The Part B counting bound** (p. 147): the factored degree-square sum
`∑_{𝒳(S₁,Z)} χ(1)² = d·|S⧸S₁|·|Q₁⧸Z|·(|Z|−1)` (`sum_degreeSq_XsetOf_eq_mul`)
combined with the counterexample degree inequality `∑ m(x)² ≤ 2·tθ·a`
(`x(1) = d·m(x)`) gives `|S⧸S₁|·|Q₁⧸Z|·(|Z|−1) ≤ d·(2·tθ·a)` — the `h1` input
of `false_of_xset_induction_bounds`.  One factor of `d` cancels between the
degree-square sum (`d²·∑ m²`) and the counting total (`d·|S⧸S₁|·…`). -/
theorem xset_counting_le_of_sum_le [Finite G]
    {S₁ Z : Subgroup G} (hS₁S : S₁ ≤ hyp.S) (hZQ1 : Z ≤ hyp.Q1)
    [(S₁.subgroupOf hyp.H).Normal]
    [((S₁.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H)).Normal]
    (hfin : (hyp.XsetOf S₁ Z).Finite)
    {m : ClassFunction ↥hyp.H ℂ → ℕ}
    (hmdeg : ∀ x ∈ hyp.XsetOf S₁ Z, x (1 : ↥hyp.H) = (hyp.d : ℂ) * (m x : ℂ))
    {tθ a : ℕ}
    (hmsum : (∑ x ∈ hfin.toFinset, ((m x : ℝ)) ^ 2) ≤ 2 * (tθ : ℝ) * (a : ℝ)) :
    (Nat.card (↥hyp.S ⧸ S₁.subgroupOf hyp.S) : ℝ)
        * (Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) : ℝ)
        * ((Nat.card ↥Z : ℝ) - 1)
      ≤ (hyp.d : ℝ) * (2 * (tθ : ℝ) * (a : ℝ)) := by
  classical
  have hd0 : (0 : ℝ) < (hyp.d : ℝ) := by exact_mod_cast hyp.d_pos
  -- the `ℝ` counting identity, left-associated to match the `ℂ` lemma
  have hCR : (hyp.d : ℝ) ^ 2 * (∑ x ∈ hfin.toFinset, ((m x : ℝ)) ^ 2)
      = (hyp.d : ℝ) * (Nat.card (↥hyp.S ⧸ S₁.subgroupOf hyp.S) : ℝ)
          * (Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) : ℝ)
          * ((Nat.card ↥Z : ℝ) - 1) := by
    have hC := hyp.sum_degreeSq_XsetOf_eq_mul hS₁S hZQ1 hfin
    have h2 : ∑ x ∈ hfin.toFinset, (x (1 : ↥hyp.H)) ^ 2
        = (hyp.d : ℂ) ^ 2 * ∑ x ∈ hfin.toFinset, ((m x : ℂ)) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hmdeg x (hfin.mem_toFinset.mp hx)]
      ring
    rw [h2] at hC
    exact_mod_cast hC
  -- multiply the target through by `d` and cancel
  have key : (hyp.d : ℝ) * ((Nat.card (↥hyp.S ⧸ S₁.subgroupOf hyp.S) : ℝ)
        * (Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) : ℝ) * ((Nat.card ↥Z : ℝ) - 1))
      ≤ (hyp.d : ℝ) * ((hyp.d : ℝ) * (2 * (tθ : ℝ) * (a : ℝ))) := by
    have e1 : (hyp.d : ℝ) * ((Nat.card (↥hyp.S ⧸ S₁.subgroupOf hyp.S) : ℝ)
          * (Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) : ℝ) * ((Nat.card ↥Z : ℝ) - 1))
        = (hyp.d : ℝ) ^ 2 * (∑ x ∈ hfin.toFinset, ((m x : ℝ)) ^ 2) := by
      rw [hCR]; ring
    rw [e1, show (hyp.d : ℝ) * ((hyp.d : ℝ) * (2 * (tθ : ℝ) * (a : ℝ)))
        = (hyp.d : ℝ) ^ 2 * (2 * (tθ : ℝ) * (a : ℝ)) from by ring]
    exact mul_le_mul_of_nonneg_left hmsum (sq_nonneg _)
  exact le_of_mul_le_mul_left key hd0

open scoped Classical in
/-- **The reduction (3) Part B one-step lemma** (p. 147): coherence of the
`𝒳`-family `𝒳(S₁,Z)` propagates to `𝒳(S₂,Z)` along the `S`-side chief data
`S₂ ≤ S₁ ≤ ZS ≤ S` (`ZS` the lift of `Z(S⧸S₂)`, `⁅ZS,S⁆ ⊆ S₂`, `S₁ ≤ [S,S]`
proper in `S`), with `Z ≤ Z(Q₁)` the fixed nontrivial `H`-invariant central
subgroup of step (3).

Proof: suppose not.  The anchored counterexample extraction at `B₀ = 𝒳(S',Z)`,
`B = 𝒳(S₁,Z)`, `Y = 𝒳(S₂,Z)` (anchor `Ind(θ∘q1Proj) ∈ 𝒳₁`,
`exists_anchor_of_mem_XsetOf`) produces `ψ` of degree `d·a` and the anchor
`χθ` of degree `d·tθ` with `∑_{𝒳(S₁,Z)} m(x)² ≤ 2·tθ·a`.  The Part B counting
keeps the full product `|S⧸S₁|·|Q₁⧸Z|·(|Z|−1) ≤ d·2·tθ·a`
(`xset_counting_le_of_sum_le`); the anchor bound at `D₀ = S·Z` gives
`tθ² ≤ |Q₁⧸Z|` (`index_subgroupOf_sup_S_eq`), the `ψ`-bound at `D₀ = ZS·Z`
gives `a² ≤ |S⧸ZS|·|Q₁⧸Z| ≤ |S⧸S₁|·|Q₁⧸Z|` (`index_subgroupOf_sup_prod_eq`);
with the `d`-odd fixed-point-free bound `|Z| ≥ 2d+1` and `|S⧸S₁| ≥ 2`, the
arithmetic `false_of_xset_induction_bounds` closes the contradiction. -/
theorem xsetOf_S_coherent_step [Finite G]
    (hd : Odd hyp.d) (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    {S₁ S₂ ZS Z : Subgroup G}
    (hZQ1 : Z ≤ hyp.Q1) (hZne : Z ≠ ⊥)
    (hZQ1c : ∀ z ∈ Z, ∀ y ∈ hyp.Q1, ⁅z, y⁆ = 1)
    (hZH : ∀ h ∈ hyp.H, ∀ x ∈ Z, h * x * h⁻¹ ∈ Z)
    (hS₁der : S₁ ≤ hyp.Sder) (hS₂S₁ : S₂ ≤ S₁)
    (hSnotle : ¬ hyp.S ≤ S₁)
    (hZSS : ZS ≤ hyp.S) (hS₁ZS : S₁ ≤ ZS)
    (hZSc : ∀ z ∈ ZS, ∀ s ∈ hyp.S, ⁅z, s⁆ ∈ S₂)
    [(S₁.subgroupOf hyp.H).Normal]
    [((S₁.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H)).Normal]
    [((S₂.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).Normal]
    [((hyp.S ⊔ Z).subgroupOf hyp.H).Normal]
    [(ZS.subgroupOf hyp.H).Normal]
    [((ZS ⊔ Z).subgroupOf hyp.H).Normal]
    (hcoh₁ : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.XsetOf S₁ Z) hyp.A)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.XsetOf S₂ Z) hyp.A) := by
  classical
  by_contra hfail
  haveI : ((hyp.Sder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).Normal :=
    hyp.Sder_subgroupOf_Q_normal
  have hS₁S : S₁ ≤ hyp.S := hS₁der.trans hyp.Sder_le_S
  -- the families `B₀ = 𝒳(S',Z) ⊆ B = 𝒳(S₁,Z) ⊆ Y = 𝒳(S₂,Z)`
  have hB₀B : hyp.XsetOf hyp.Sder Z ⊆ hyp.XsetOf S₁ Z :=
    fun x hx => ⟨hyp.ssetOf_antitone hS₁der hx.1, hx.2⟩
  have hBY : hyp.XsetOf S₁ Z ⊆ hyp.XsetOf S₂ Z :=
    fun x hx => ⟨hyp.ssetOf_antitone hS₂S₁ hx.1, hx.2⟩
  have hYS : hyp.XsetOf S₂ Z ⊆ hyp.Sset := hyp.XsetOf_subset_Sset _ _
  have hYfin : (hyp.XsetOf S₂ Z).Finite := hyp.XsetOf_finite _ _
  have hYconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.XsetOf S₂ Z) :=
    fun _ hx => hyp.conj_mem_XsetOf hx
  have hBconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.XsetOf S₁ Z) :=
    fun _ hx => hyp.conj_mem_XsetOf hx
  -- the per-`ψ` anchor `Ind(θ∘q1Proj) ∈ 𝒳₁`
  have hanchor : ∀ ψ ∈ hyp.XsetOf S₂ Z, ∃ (χθ : ClassFunction ↥hyp.H ℂ) (tθ a : ℕ),
      χθ ∈ hyp.XsetOf hyp.Sder Z ∧ 0 < tθ ∧ 0 < a ∧
      χθ (1 : ↥hyp.H) = (hyp.d : ℂ) * (tθ : ℂ) ∧
      ψ (1 : ↥hyp.H) = (hyp.d : ℂ) * (a : ℂ) ∧ tθ ∣ a := by
    intro ψ hψ
    obtain ⟨χθ, tθ, e, hχθX, htθpos, hepos, hχθdeg, hψdeg⟩ :=
      hyp.exists_anchor_of_mem_XsetOf hZQ1 (fun h hh x hx => hZH h hh x hx) hψ
    exact ⟨χθ, tθ, e * tθ, hχθX, htθpos, Nat.mul_pos hepos htθpos, hχθdeg,
      hψdeg, dvd_mul_left tθ e⟩
  -- the counterexample
  obtain ⟨ψ, χθ, tθ, a, m, hψY, hχθX, htθpos, hapos, hχθdeg, hψdeg, hmdeg, hmsum⟩ :=
    hyp.exists_counterexample_anchored_of_not_coherent hd hQ1odd hB₀B hBY hYS hYfin
      hYconj hBconj hcoh₁ hanchor hfail
  -- `h1`: counting `|S⧸S₁|·|Q₁⧸Z|·(|Z|−1) ≤ d·2·tθ·a`
  have h1 := hyp.xset_counting_le_of_sum_le hS₁S hZQ1 (hYfin.subset hBY) hmdeg hmsum
  -- `h2`: anchor bound `tθ² ≤ |Q₁⧸Z|` at `D₀ = S·Z`
  have h2 : tθ ^ 2 ≤ Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) := by
    obtain ⟨t', ht'deg, ht'sq⟩ := hyp.exists_deg_sq_le_of_mem_SsetOf hyp.Sder (hyp.S ⊔ Z)
      (hyp.Sder_le_S.trans hyp.S_le_Q) (hyp.Sder_le_S.trans le_sup_left)
      (sup_le hyp.S_le_Q (hZQ1.trans hyp.Q1_le_Q))
      (hyp.map_mk_le_center_of_commutator_mem (fun x hx q hq => by
        have h := hyp.commutator_mem_sup_Sder_of_central (Q₃ := (⊥ : Subgroup G)) hZQ1
          (fun z hz y hy => by rw [Subgroup.mem_bot]; exact hZQ1c z hz y hy) hx hq
        rwa [sup_bot_eq] at h))
      (hyp.XsetOf_subset_SsetOf hyp.Sder Z hχθX)
    rw [hyp.index_subgroupOf_sup_S_eq hZQ1] at ht'sq
    have htt' : t' = tθ := by
      have hdne : (hyp.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.d_pos.ne'
      exact_mod_cast mul_left_cancel₀ hdne (ht'deg.symm.trans hχθdeg)
    rwa [htt'] at ht'sq
  -- `h3`: `ψ`-bound `a² ≤ |S⧸ZS|·|Q₁⧸Z| ≤ |S⧸S₁|·|Q₁⧸Z|` at `D₀ = ZS·Z`
  have h3 : a ^ 2 ≤ Nat.card (↥hyp.S ⧸ S₁.subgroupOf hyp.S)
      * Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) := by
    obtain ⟨a', ha'deg, ha'sq⟩ := hyp.exists_deg_sq_le_of_mem_SsetOf S₂ (ZS ⊔ Z)
      (hS₂S₁.trans (hS₁ZS.trans (hZSS.trans hyp.S_le_Q)))
      ((hS₂S₁.trans hS₁ZS).trans le_sup_left)
      (sup_le (hZSS.trans hyp.S_le_Q) (hZQ1.trans hyp.Q1_le_Q))
      (hyp.map_mk_le_center_of_commutator_mem (fun x hx q hq =>
        hyp.commutator_mem_of_central_pair hZSS hZQ1 hZSc hZQ1c hx hq))
      (hyp.XsetOf_subset_SsetOf S₂ Z hψY)
    rw [hyp.index_subgroupOf_sup_prod_eq hZSS hZQ1] at ha'sq
    have haa' : a' = a := by
      have hdne : (hyp.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.d_pos.ne'
      exact_mod_cast mul_left_cancel₀ hdne (ha'deg.symm.trans hψdeg)
    rw [haa'] at ha'sq
    refine le_trans ha'sq (Nat.mul_le_mul_right _ ?_)
    have hle : S₁.subgroupOf hyp.S ≤ ZS.subgroupOf hyp.S := fun x hx => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hS₁ZS hx
    have hdvd := Subgroup.index_dvd_of_le hle
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card] at hdvd
    exact Nat.le_of_dvd Nat.card_pos hdvd
  -- `h4`: `|Z| ≥ 2d+1`
  have h4 : 2 * hyp.d + 1 ≤ Nat.card ↥Z := by
    have hZodd : Odd (Nat.card ↥Z) := by
      rcases Nat.even_or_odd (Nat.card ↥Z) with he | ho
      · exfalso
        obtain ⟨k, hk⟩ := he.two_dvd.trans (Subgroup.card_dvd_of_le hZQ1)
        exact (Nat.not_even_iff_odd.mpr hQ1odd) ⟨k, by omega⟩
      · exact ho
    exact hyp.two_mul_d_add_one_le_card_of_le_Q1 hd hZQ1
      (fun δ hδ z hz => hZH δ (hyp.D_le_H hδ) z hz) hZne hZodd
  -- `h5`: `|S⧸S₁| ≥ 2`
  have h5 : 2 ≤ Nat.card (↥hyp.S ⧸ S₁.subgroupOf hyp.S) := by
    obtain ⟨s, hsS, hsS₁⟩ := SetLike.not_le_iff_exists.mp hSnotle
    have hne : (Quotient.mk'' (⟨s, hsS⟩ : ↥hyp.S) : ↥hyp.S ⧸ S₁.subgroupOf hyp.S)
        ≠ Quotient.mk'' (1 : ↥hyp.S) := by
      intro h
      have hmem := Quotient.eq''.mp h
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hmem
      apply hsS₁
      have h2 : s⁻¹ * (1 : G) ∈ S₁ := hmem
      rw [mul_one] at h2
      simpa using S₁.inv_mem h2
    haveI : Nontrivial (↥hyp.S ⧸ S₁.subgroupOf hyp.S) := ⟨_, _, hne⟩
    exact Finite.one_lt_card
  exact false_of_xset_induction_bounds hyp.d_pos Nat.card_pos h1 h2 h3 h4 h5

open scoped Classical in
/-- **The reduction (3) Part B chief-factor induction** (p. 147): given `𝒳(S',Z)`
coherent (Part A, `xsetOf_sder_coherent`), the family `𝒳(S₃,Z)` is coherent for
every `H`-invariant `S₃ ≤ S'` — descending from the base `S₃ = S'` along minimal
`H`-invariant steps through `xsetOf_S_coherent_step`, with the `S`-side lift
`ZS = centralLiftIn S S₃'` and `S₁ ≤ ZS` from `minimal_le_centralLiftIn` at
`W = S` (`S` is nilpotent by hypothesis).  The mirror of
`ssetOf_coherent_of_le_sder` relative to `𝒳`, carrying the fixed central `Z`. -/
theorem xsetOf_coherent_of_le_sder [Finite G]
    (hd : Odd hyp.d) (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1) (hZne : Z ≠ ⊥)
    (hZQ1c : ∀ z ∈ Z, ∀ y ∈ hyp.Q1, ⁅z, y⁆ = 1)
    (hZH : ∀ h ∈ hyp.H, ∀ x ∈ Z, h * x * h⁻¹ ∈ Z)
    [((hyp.S ⊔ Z).subgroupOf hyp.H).Normal]
    (hcohSder : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.XsetOf hyp.Sder Z) hyp.A))
    (S₃ : Subgroup G) (hS₃le : S₃ ≤ hyp.Sder)
    (hS₃H : ∀ h ∈ hyp.H, ∀ x ∈ S₃, h * x * h⁻¹ ∈ S₃) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.XsetOf S₃ Z) hyp.A) := by
  classical
  have hmain : ∀ n (S₃' : Subgroup G), S₃' ≤ hyp.Sder →
      (∀ h ∈ hyp.H, ∀ x ∈ S₃', h * x * h⁻¹ ∈ S₃') →
      Nat.card ↥hyp.Sder - Nat.card ↥S₃' ≤ n →
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
        (hyp.XsetOf S₃' Z) hyp.A) := by
    intro n
    induction n with
    | zero =>
      intro S₃' hle hinvH hcard
      have hcard_le : Nat.card ↥hyp.Sder ≤ Nat.card ↥S₃' := by
        have hpos : 0 < Nat.card ↥S₃' := Nat.card_pos
        omega
      rw [OddOrder.Isaacs.Ch09.eq_of_le_of_card_le hle hcard_le]
      exact hcohSder
    | succ n ih =>
      intro S₃' hle hinvH hcard
      by_cases heq : S₃' = hyp.Sder
      · rw [heq]; exact hcohSder
      have hS₃lt : S₃' < hyp.Sder := lt_of_le_of_ne hle heq
      obtain ⟨S₁, hS₃S₁, hS₁le, hS₁H, hmin⟩ :=
        hyp.exists_minimal_conjInvariant_between hS₃lt
          (fun h hh x hx => hyp.Sder_conj_mem_of_mem_H hh hx)
      have hinvS : ∀ s ∈ hyp.S, ∀ x ∈ S₃', s * x * s⁻¹ ∈ S₃' :=
        fun s hs x hx => hinvH s (hyp.S_le_H hs) x hx
      have hcard₁ : Nat.card ↥hyp.Sder - Nat.card ↥S₁ ≤ n := by
        have h1 : Nat.card ↥S₃' < Nat.card ↥S₁ := by
          rcases lt_or_ge (Nat.card ↥S₃') (Nat.card ↥S₁) with h | h
          · exact h
          · exact absurd (OddOrder.Isaacs.Ch09.eq_of_le_of_card_le hS₃S₁.le h) hS₃S₁.ne
        have h2 : Nat.card ↥S₁ ≤ Nat.card ↥hyp.Sder := Subgroup.card_le_of_le hS₁le
        omega
      have hcoh₁ := ih S₁ hS₁le hS₁H hcard₁
      have hS₁Z : S₁ ≤ hyp.centralLiftIn hyp.S S₃' hinvS :=
        hyp.minimal_le_centralLiftIn hyp.S hyp.S_nilpotent hyp.S_le_H
          (fun h' hh' x hx => hyp.S_normal_in_H hh' hx) hS₃S₁
          (hS₁le.trans hyp.Sder_le_S) hinvS hS₁H hinvH hmin
      have hSnotle : ¬ hyp.S ≤ S₁ := by
        intro hSle
        have hSder_eq : hyp.Sder = hyp.S :=
          le_antisymm hyp.Sder_le_S (hSle.trans hS₁le)
        have hS₁ne : S₁ ≠ ⊥ := by
          intro hbot
          rw [hbot] at hS₃S₁
          exact not_lt_bot hS₃S₁
        haveI : Nontrivial ↥hyp.S := (Subgroup.nontrivial_iff_ne_bot hyp.S).mpr
          (fun hbot => hS₁ne (eq_bot_iff.mpr
            ((hS₁le.trans hyp.Sder_le_S).trans (le_of_eq hbot))))
        haveI := hyp.S_nilpotent
        apply (IsSolvable.commutator_lt_top_of_nontrivial ↥hyp.S).ne
        rw [eq_top_iff]
        intro x _
        have hx : (x : G) ∈ Subgroup.map hyp.S.subtype (commutator ↥hyp.S) := by
          rw [map_subtype_commutator hyp.S]
          change (x : G) ∈ hyp.Sder
          rw [hSder_eq]
          exact x.2
        obtain ⟨y, hy, hyx⟩ := hx
        rwa [show y = x from Subtype.ext hyx] at hy
      -- relativised `Normal` instances (mirror of reduction (2), plus the `Z`-joins)
      haveI : (S₁.subgroupOf hyp.H).Normal :=
        hyp.subgroupOf_H_normal_of_conj_mem hS₁H
      -- the `((S₁ ⊔ Z)`-in-`H)` join uses the sup-of-`subgroupOf` form (counting):
      -- provide the `Z` component and let the sup-of-normals instance build it
      haveI : (Z.subgroupOf hyp.H).Normal :=
        hyp.subgroupOf_H_normal_of_conj_mem hZH
      haveI : ((S₃'.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).Normal :=
        hyp.subgroupOf_Q_normal_of_conj_mem fun q hq x hx =>
          hinvH q (hyp.Q_le_H hq) x hx
      have hZSH : ∀ h' ∈ hyp.H, ∀ x ∈ hyp.centralLiftIn hyp.S S₃' hinvS,
          h' * x * h'⁻¹ ∈ hyp.centralLiftIn hyp.S S₃' hinvS := fun h' hh' x hx =>
        hyp.centralLiftIn_conj_mem_of_mem_H hyp.S hinvS hinvH
          (fun h'' hh'' y hy => hyp.S_normal_in_H hh'' hy) hh' hx
      haveI : ((hyp.centralLiftIn hyp.S S₃' hinvS).subgroupOf hyp.H).Normal :=
        hyp.subgroupOf_H_normal_of_conj_mem hZSH
      haveI : (((hyp.centralLiftIn hyp.S S₃' hinvS) ⊔ Z).subgroupOf hyp.H).Normal :=
        hyp.subgroupOf_H_normal_of_conj_mem fun h' hh' x hx =>
          conj_mem_sup (fun y hy => hZSH h' hh' y hy)
            (fun y hy => hZH h' hh' y hy) hx
      -- the one-step lemma closes the induction step
      exact hyp.xsetOf_S_coherent_step hd hQ1odd hZQ1 hZne hZQ1c hZH hS₁le hS₃S₁.le
        hSnotle (hyp.centralLiftIn_le hyp.S hinvS) hS₁Z
        (fun z hz s hs => hz.2 s hs) hcoh₁
  exact hmain _ S₃ hS₃le hS₃H le_rfl

/-- **Reduction (3) Part B** (p. 147): if `𝒳(S',Z)` is coherent then `𝒳 = XsetOf ⊥ Z`
is coherent — the induction at `S₃ = ⊥`, with `𝒳(⊥,Z) = 𝒮 − 𝒮(Z)`. -/
theorem xset_coherent_of_xsetOf_sder_coherent [Finite G]
    (hd : Odd hyp.d) (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1) (hZne : Z ≠ ⊥)
    (hZQ1c : ∀ z ∈ Z, ∀ y ∈ hyp.Q1, ⁅z, y⁆ = 1)
    (hZH : ∀ h ∈ hyp.H, ∀ x ∈ Z, h * x * h⁻¹ ∈ Z)
    [((hyp.S ⊔ Z).subgroupOf hyp.H).Normal]
    (hcohSder : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.XsetOf hyp.Sder Z) hyp.A)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.XsetOf (⊥ : Subgroup G) Z) hyp.A) :=
  hyp.xsetOf_coherent_of_le_sder hd hQ1odd hZQ1 hZne hZQ1c hZH hcohSder ⊥ bot_le
    (fun h' _ x hx => by rw [Subgroup.mem_bot] at hx ⊢; rw [hx]; group)

open scoped Classical in
/-- **Reduction (3)** (Peterfalvi p. 147, campaign issue 1054): for a `p`-group
`Q₁` (`d` odd) and a nontrivial `H`-invariant central `Z ≤ Z(Q₁)`, the family
`𝒳 = 𝒮 − 𝒮(Z) = XsetOf ⊥ Z` is coherent.  Part A (`xsetOf_sder_coherent`) gives
`𝒳₁ = 𝒳(S',Z)` coherent; the Part B `S`-side induction
(`xset_coherent_of_xsetOf_sder_coherent`) descends it to `𝒳`. -/
theorem xset_coherent_of_le_center_Q1 (hd : Odd hyp.d) {p : ℕ} (hp : p.Prime)
    (hQ1p : IsPGroup p ↥hyp.Q1)
    {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1) (hZne : Z ≠ ⊥)
    (hZQ1c : ∀ z ∈ Z, ∀ y ∈ hyp.Q1, ⁅z, y⁆ = 1)
    (hZH : ∀ h ∈ hyp.H, ∀ x ∈ Z, h * x * h⁻¹ ∈ Z)
    [(hyp.Sder.subgroupOf hyp.H).Normal]
    [((hyp.Sder.subgroupOf hyp.H) ⊔ (Z.subgroupOf hyp.H)).Normal]
    [((hyp.S ⊔ Z).subgroupOf hyp.H).Normal] :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.XsetOf (⊥ : Subgroup G) Z) hyp.A) :=
  hyp.xset_coherent_of_xsetOf_sder_coherent hd (hyp.odd_card_Q1_of_isPGroup hp hQ1p)
    hZQ1 hZne hZQ1c hZH
    (hyp.xsetOf_sder_coherent hd hp hQ1p hZQ1 hZne hZQ1c)

end SStepInduction

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
