/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FixedPointCentralizer
import OddOrder.Isaacs.Ch06_FrobeniusActions.KernelNilpotent

/-!
# Peterfalvi Part II, Ch. I §2: Proposition 1 (the structure of `Q`)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §2, pp. 102–103.

From §2 onwards the book keeps the standing hypotheses (A1)–(A3) and the
§1 notation; here that is the same `Hypothesis` structure.

* **Prop 1 (a)**: `C_Q(x) = 1` for `x ∈ K - {1}` (`K` acts fixed-point-
  freely on `Q`).  An `x ∈ K` with three or more fixed points on `Ω`
  centralizes an involution `u ∈ H ∩ I` (§1 Prop 6(b)) and hence is
  trivial by the injectivity of `k ↦ u^k` (§1 Prop 3); so `Ω_x` is the
  pair `{basept, t • basept}`, forcing `C_H(x) ≤ D` and
  `C_Q(x) ≤ Q ⊓ D = 1`.
* **Prop 1 (b)**: `Q` is nilpotent — Thompson's theorem
  (Isaacs Thm 6.24, `isNilpotent_of_isFrobeniusAction`) applied to the
  conjugation action of `⟨x⟩` on `Q` for any `1 ≠ x ∈ K` (nonempty by
  (A3)).
* **Prop 1 (c)**: `H ∩ I ⊆ Z(Q)`, and `(H ∩ I) ∪ {1}` is an elementary
  abelian `2`-group.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

open MulAction

/-! ## Prop 1 (a): `K` acts fixed-point-freely on `Q` (p. 102) -/

/-- **Peterfalvi Part II, Ch. I §2 Prop 1 (a)** (p. 102), first step — an
element of `K` with at least three fixed points on `Ω` is trivial.  By §1
Prop 6(b) `C_Q(⟨x⟩)` contains an involution `u ∈ H ∩ I`; then
`u^x = u = u^1` and `k ↦ u^k` is injective on `K` (§1 Prop 3). -/
lemma eq_one_of_mem_KSet_of_three_le_ncard_fixedPoints {x : G}
    (hx : x ∈ hyp.KSet)
    (h3 : 3 ≤ (fixedPoints (Subgroup.zpowers x) Ω).ncard) : x = 1 := by
  have hXD : Subgroup.zpowers x ≤ hyp.D := Subgroup.zpowers_le.mpr hx.1
  obtain ⟨u, hu, hu2, hu1⟩ :=
    exists_sq_eq_one_of_even_card (hyp.even_card_cQ hXD h3)
  obtain ⟨huQ, huc⟩ := Subgroup.mem_inf.mp hu
  have hxu : x⁻¹ * u * x = u := by
    have h := Subgroup.mem_centralizer_iff.mp huc x (Subgroup.mem_zpowers x)
    calc x⁻¹ * u * x = x⁻¹ * (u * x) := by rw [mul_assoc]
      _ = x⁻¹ * (x * u) := by rw [← h]
      _ = u := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have h1 : (fun k : G => k⁻¹ * u * k) x = (fun k : G => k⁻¹ * u * k) 1 := by
    simp only [inv_one, one_mul, mul_one]
    exact hxu
  exact hyp.injOn_conj_KSet (hyp.Q_le_H huQ) hu2 hu1 hx hyp.one_mem_KSet h1

/-- **Peterfalvi Part II, Ch. I §2 Prop 1 (a)** (p. 102), second step — for
`1 ≠ x ∈ K` the fixed points of `x` on `Ω` are exactly the pair
`{basept, t • basept}`. -/
lemma fixedPoints_zpowers_eq_pair_of_mem_KSet {x : G} (hx : x ∈ hyp.KSet)
    (hx1 : x ≠ 1) :
    fixedPoints (Subgroup.zpowers x) Ω =
      {hyp.basept, hyp.t • hyp.basept} := by
  have : Finite Ω := hyp.finite_Omega
  have hXD : Subgroup.zpowers x ≤ hyp.D := Subgroup.zpowers_le.mpr hx.1
  have htb : hyp.t • hyp.basept ≠ hyp.basept :=
    hyp.smul_basept_ne_of_not_mem_H hyp.t_not_mem_H
  refine subset_antisymm ?_ ?_
  · intro ω hω
    by_contra hcon
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcon
    obtain ⟨hω1, hω2⟩ := hcon
    have hsub : {hyp.basept, hyp.t • hyp.basept, ω} ⊆
        fixedPoints (Subgroup.zpowers x) Ω := by
      intro ω' hω'
      rcases hω' with rfl | rfl | rfl
      · exact hyp.basept_mem_fixedPoints hXD
      · exact hyp.t_smul_basept_mem_fixedPoints hXD
      · exact hω
    have hcard : ({hyp.basept, hyp.t • hyp.basept, ω} : Set Ω).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [Ne.symm htb, Ne.symm hω1]),
        Set.ncard_insert_of_notMem (by simp [Ne.symm hω2]),
        Set.ncard_singleton]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hcard] at hle
    exact hx1 (hyp.eq_one_of_mem_KSet_of_three_le_ncard_fixedPoints hx hle)
  · intro ω hω
    rcases hω with rfl | hω
    · exact hyp.basept_mem_fixedPoints hXD
    · rw [Set.mem_singleton_iff] at hω
      subst hω
      exact hyp.t_smul_basept_mem_fixedPoints hXD

/-- **Peterfalvi Part II, Ch. I §2 Prop 1 (a)** (p. 102) — `C_Q(x) = 1`
for `1 ≠ x ∈ K`: the fixed points of `x` are `{basept, t • basept}`, so
`C_H(x) ≤ D` and `C_Q(x) ≤ Q ⊓ D = 1`. -/
theorem Q_inf_centralizer_eq_bot_of_mem_KSet {x : G} (hx : x ∈ hyp.KSet)
    (hx1 : x ≠ 1) : hyp.Q ⊓ Subgroup.centralizer {x} = ⊥ := by
  have hpair := hyp.fixedPoints_zpowers_eq_pair_of_mem_KSet hx hx1
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨hcQ, hcx⟩ := Subgroup.mem_inf.mp hc
  have hczp : c ∈ Subgroup.centralizer
      ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← hk]
    have hcomm : Commute c x := Subgroup.mem_centralizer_singleton_iff.mp hcx
    exact (hcomm.symm.zpow_left k).eq
  have hfix : c • (hyp.t • hyp.basept) ∈
      fixedPoints (Subgroup.zpowers x) Ω :=
    smul_mem_fixedPoints_of_mem_centralizer hczp
      (hyp.t_smul_basept_mem_fixedPoints (Subgroup.zpowers_le.mpr hx.1))
  rw [hpair] at hfix
  have hcb : c • hyp.basept = hyp.basept :=
    hyp.smul_basept_eq_of_mem_H (hyp.Q_le_H hcQ)
  have hct : c • (hyp.t • hyp.basept) = hyp.t • hyp.basept := by
    rcases Set.mem_insert_iff.mp hfix with h | h
    · exfalso
      have heq : c • (hyp.t • hyp.basept) = c • hyp.basept := by
        rw [h, hcb]
      exact hyp.smul_basept_ne_of_not_mem_H hyp.t_not_mem_H
        (smul_left_cancel c heq)
    · exact Set.mem_singleton_iff.mp h
  have hcD : c ∈ hyp.D := by
    rw [hyp.D_eq_stabilizer_inf]
    exact Subgroup.mem_inf.mpr
      ⟨hyp.H_def ▸ hyp.Q_le_H hcQ, mem_stabilizer_iff.mpr hct⟩
  have hbot : c ∈ hyp.Q ⊓ hyp.D := ⟨hcQ, hcD⟩
  rwa [hyp.Q_inf_D_eq_bot] at hbot

/-! ## Prop 1 (b): `Q` is nilpotent (pp. 102–103) -/

/-- `K` contains a nontrivial element: by (A3) `Q` contains a four-group,
so `|K| = |H ∩ I| ≥ 3 > 1` (§1 Prop 3). -/
lemma exists_ne_one_mem_KSet : ∃ x : G, x ∈ hyp.KSet ∧ x ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hle : hyp.KSet.ncard ≤ 1 := by
    have hsub : hyp.KSet ⊆ {1} := fun x hx => hcon x hx
    have h := Set.ncard_le_ncard hsub (Set.finite_singleton 1)
    simpa using h
  obtain ⟨E, hEQ, hE4, hEsq⟩ := hyp.exists_four_subgroup_le_Q
  have hEsub : ((E : Set G) \ {1}) ⊆
      {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} := by
    rintro x ⟨hxE, hx1⟩
    rw [Set.mem_singleton_iff] at hx1
    exact ⟨hEsq x hxE, hx1, hyp.Q_le_H (hEQ hxE)⟩
  have hEcoe : (E : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hE4
  have hE3 : ((E : Set G) \ {1}).ncard = 3 := by
    rw [Set.ncard_sdiff_singleton_of_mem E.one_mem, hEcoe]
  have h3le := Set.ncard_le_ncard hEsub (Set.toFinite _)
  rw [hyp.ncard_KSet_eq] at hle
  omega

open OddOrder.Isaacs.Ch06 in
/-- **Peterfalvi Part II, Ch. I §2 Prop 1 (b)** (pp. 102–103) — `Q` is
nilpotent.  Any `1 ≠ x ∈ K` acts fixed-point-freely on `Q` by conjugation
((a), applied to the integer powers of `x`, which stay in `K`); Thompson's
theorem (Isaacs Thm 6.24, `isNilpotent_of_isFrobeniusAction`) concludes. -/
theorem isNilpotent_Q : Group.IsNilpotent ↥hyp.Q := by
  classical
  obtain ⟨x, hxK, hx1⟩ := hyp.exists_ne_one_mem_KSet
  have hxH : x ∈ hyp.H := hyp.D_le_H hxK.1
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer hyp.Q := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => hyp.Q_normal_in_H x hxH h hh
    · intro hh
      have h2 := hyp.Q_normal_in_H x⁻¹ (inv_mem hxH) _ hh
      simpa [mul_assoc] using h2
  letI : MulDistribMulAction ↥(Subgroup.zpowers x) ↥hyp.Q :=
    MulDistribMulAction.compHom _ (Subgroup.inclusion hle)
  haveI : Nontrivial ↥(Subgroup.zpowers x) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact fun h => hx1 (Subgroup.zpowers_eq_bot.mp h)
  have hFrob : IsFrobeniusAction ↥(Subgroup.zpowers x) ↥hyp.Q := by
    intro a ha n hn hann
    have hcoe : ((a • n : ↥hyp.Q) : G) = (a : G) * (n : G) * (a : G)⁻¹ := rfl
    have haK : (a : G) ∈ hyp.KSet := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      rw [← hk]
      exact hyp.zpow_mem_KSet hxK k
    have ha1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    have hcomm : Commute (n : G) (a : G) := by
      have h : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
        rw [← hcoe]
        exact congrArg Subtype.val hann
      have h2 := congrArg (fun z : G => z * (a : G)) h
      simp only [inv_mul_cancel_right] at h2
      exact h2.symm
    have hnmem : (n : G) ∈ hyp.Q ⊓ Subgroup.centralizer {(a : G)} :=
      ⟨n.2, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    rw [hyp.Q_inf_centralizer_eq_bot_of_mem_KSet haK ha1,
      Subgroup.mem_bot] at hnmem
    exact hn (Subtype.ext hnmem)
  exact isNilpotent_of_isFrobeniusAction hFrob

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
