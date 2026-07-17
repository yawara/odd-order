/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FixedPointCentralizer
import OddOrder.Isaacs.Ch06_FrobeniusActions.KernelNilpotent
import OddOrder.Isaacs.Ch04_Commutators.Mann

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

/-! ## Prop 1 (c): `H ∩ I ⊆ Z(Q)` and `Q₀` is elementary abelian (p. 103) -/

open OddOrder.Isaacs.Ch04 in
/-- `Z(Q)` contains an involution: the Sylow `2`-subgroup of the nilpotent
group `Q` is normal (mathlib) and nontrivial (`|Q|` even), so it meets the
center (Isaacs Lemma 4.16 auxiliary,
`exists_mem_center_of_normal_ne_bot_of_isNilpotent`); a central element of
`2`-power order powers up to a central involution (Cauchy on `⟨x⟩`). -/
lemma exists_involution_mem_center_Q :
    ∃ u : G, u ∈ hyp.Q ∧ u ^ 2 = 1 ∧ u ≠ 1 ∧
      ∀ v ∈ hyp.Q, u * v = v * u := by
  classical
  haveI := hyp.isNilpotent_Q
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥hyp.Q) := Sylow.nonempty
  have hSne : (S : Subgroup ↥hyp.Q) ≠ ⊥ := by
    intro hbot
    have hcard := S.card_eq_multiplicity
    rw [hbot, Subgroup.card_bot] at hcard
    have hpos := Nat.Prime.factorization_pos_of_dvd Nat.prime_two
      Nat.card_pos.ne' hyp.Q_even.two_dvd
    have h1lt : 1 < 2 ^ (Nat.card ↥hyp.Q).factorization 2 :=
      Nat.one_lt_two_pow_iff.mpr hpos.ne'
    omega
  obtain ⟨x, hxS, hxc, hx1⟩ :=
    exists_mem_center_of_normal_ne_bot_of_isNilpotent hSne
  -- `x` has `2`-power order, so `⟨x⟩` has even order and contains an
  -- involution, still central
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hxS⟩
  have hxpow : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    push_cast at this
    exact this
  obtain ⟨j, -, horder⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (orderOf_dvd_of_pow_eq_one hxpow)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at horder
    exact hx1 horder
  have heven : Even (Nat.card ↥(Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers, horder, Nat.even_pow]
    exact ⟨even_two, hj0⟩
  obtain ⟨v, hvzp, hv2, hv1⟩ := exists_sq_eq_one_of_even_card heven
  have hvc : v ∈ Subgroup.center ↥hyp.Q :=
    Subgroup.zpowers_le.mpr hxc hvzp
  refine ⟨(v : ↥hyp.Q), v.2, ?_, fun h => hv1 (Subtype.ext h), ?_⟩
  · have := congrArg Subtype.val hv2
    push_cast at this
    exact this
  · intro w hw
    have h := Subgroup.mem_center_iff.mp hvc ⟨w, hw⟩
    have h2 := congrArg Subtype.val h
    push_cast at h2
    exact h2.symm

/-- **Peterfalvi Part II, Ch. I §2 Prop 1 (c)** (p. 103), first clause —
every involution of `H` centralizes `Q` (i.e. `H ∩ I ⊆ Z(Q)`, as the
involutions of `H` lie in `Q`).  `Z(Q)` contains one involution `u₀`, and
`u₀^K` exhausts `H ∩ I` (§1 Prop 3) while `K ⊆ D` normalizes `Q`. -/
theorem involutions_H_subset_centralizer_Q {u : G} (huH : u ∈ hyp.H)
    (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    u ∈ Subgroup.centralizer (hyp.Q : Set G) := by
  obtain ⟨u₀, hu₀Q, hu₀2, hu₀1, hu₀c⟩ := hyp.exists_involution_mem_center_Q
  have humem : u ∈ {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} := ⟨hu2, hu1, huH⟩
  rw [← hyp.image_conj_KSet_eq_involutions_H (hyp.Q_le_H hu₀Q) hu₀2 hu₀1]
    at humem
  obtain ⟨k, hkK, hku⟩ := humem
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hkH : k ∈ hyp.H := hyp.D_le_H hkK.1
  have hkv : k * v * k⁻¹ ∈ hyp.Q := hyp.Q_normal_in_H k hkH v hv
  have hcomm := hu₀c _ hkv
  rw [← hku]
  calc v * (k⁻¹ * u₀ * k) = k⁻¹ * ((k * v * k⁻¹) * u₀) * k := by group
    _ = k⁻¹ * (u₀ * (k * v * k⁻¹)) * k := by rw [← hcomm]
    _ = (k⁻¹ * u₀ * k) * v := by group

/-- `Q₀ = (H ∩ I) ∪ {1}` (p. 103, the book's standing notation): the
involutions of `H` together with the identity form a subgroup —
multiplicative closure holds because involutions of `H` centralize each
other (Prop 1(c)). -/
def Q0 : Subgroup G where
  carrier := {x | x ^ 2 = 1 ∧ x ∈ hyp.H}
  one_mem' := ⟨one_pow 2, hyp.H.one_mem⟩
  inv_mem' := by
    rintro x ⟨hx2, hxH⟩
    refine ⟨?_, hyp.H.inv_mem hxH⟩
    rw [inv_pow, hx2, inv_one]
  mul_mem' := by
    rintro a b ⟨ha2, haH⟩ ⟨hb2, hbH⟩
    refine ⟨?_, hyp.H.mul_mem haH hbH⟩
    rcases eq_or_ne a 1 with rfl | ha1
    · rwa [one_mul]
    have hbQ : b ∈ hyp.Q := hyp.mem_Q_of_sq_eq_one_of_mem_H hbH hb2
    have hcomm : b * a = a * b :=
      Subgroup.mem_centralizer_iff.mp
        (hyp.involutions_H_subset_centralizer_Q haH ha2 ha1) b hbQ
    calc (a * b) ^ 2 = a * (b * a) * b := by rw [sq]; group
      _ = a * (a * b) * b := by rw [hcomm]
      _ = a ^ 2 * b ^ 2 := by rw [sq, sq]; group
      _ = 1 := by rw [ha2, hb2, mul_one]

lemma mem_Q0_iff {x : G} : x ∈ hyp.Q0 ↔ x ^ 2 = 1 ∧ x ∈ hyp.H := Iff.rfl

/-- `Q₀` has exponent `2` ("elementary": every element squares to `1`). -/
lemma sq_eq_one_of_mem_Q0 {x : G} (hx : x ∈ hyp.Q0) : x ^ 2 = 1 := hx.1

lemma Q0_le_Q : hyp.Q0 ≤ hyp.Q := fun _ hx =>
  hyp.mem_Q_of_sq_eq_one_of_mem_H hx.2 hx.1

/-- **Peterfalvi Part II, Ch. I §2 Prop 1 (c)** (p. 103), second clause,
centralizer form — `Q₀ ≤ Z(Q)` (with `Q₀ ≤ Q` this is `H ∩ I ⊆ Z(Q)`). -/
lemma Q0_le_centralizer_Q :
    hyp.Q0 ≤ Subgroup.centralizer (hyp.Q : Set G) := by
  intro x hx
  rcases eq_or_ne x 1 with rfl | hx1
  · exact one_mem _
  · exact hyp.involutions_H_subset_centralizer_Q hx.2 hx.1 hx1

/-- **Peterfalvi Part II, Ch. I §2 Prop 1 (c)** (p. 103), second clause —
`Q₀` is abelian (with `sq_eq_one_of_mem_Q0`: elementary abelian). -/
lemma commute_of_mem_Q0 {a b : G} (ha : a ∈ hyp.Q0) (hb : b ∈ hyp.Q0) :
    Commute a b := by
  rcases eq_or_ne a 1 with rfl | ha1
  · exact Commute.one_left b
  exact (Subgroup.mem_centralizer_iff.mp
    (hyp.involutions_H_subset_centralizer_Q ha.2 ha.1 ha1) b
    (hyp.Q0_le_Q hb)).symm

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
