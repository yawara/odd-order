/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.OrderThreeSuzukiCentralizer
import OddOrder.Peterfalvi.Appendices.Suzuki.ActualCenter
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.ConjugateSummandSplit
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.TypeBRecognition

/-!
# Peterfalvi Part II, Ch. I §3, Lemma 5: the type-B conclusion

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, Lemma 5, p. 107.

Suppose `|st| = 3` and `Q` is a Suzuki `2`-group of order `q³`, `q = |Q₀|`.
This leaf assembles the type-B branch of Lemma 5: any nonidentity `w ∈ W`
acts on `Q` by conjugation as an odd-order automorphism which fixes `Q₀`
pointwise, commutes with the `K`-action, and whose nontrivial powers have
centralizer exactly `Q₀` (the first reduction of Lemma 5).  The conjugate
summand split then produces an equivariantly isomorphic invariant
two-summand split of `Q ⧸ Q₀`, and the Appendix III recognition theorem
concludes that `Q` is of type B.

The intermediate `LemmaFiveSetup` bundle collects the engine inputs — the
central-exponent facts, the transitive fixed-point-free actor data, the
`Z(Q) = Q₀` identification, and the isomorphic split itself — for reuse by
the cyclicity half of Lemma 5.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.Higman.Suzuki2Groups

namespace Hypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## Conjugation by `W` on `Q` -/

/-- Conjugation by the subgroup `W` on `Q`; `W ≤ V ≤ D ≤ H` and `Q ⊴ H`. -/
def conjQByW : ↥hyp.W →* MulAut ↥hyp.Q where
  toFun v :=
    { toFun := fun x => ⟨(v : G) * x * (v : G)⁻¹,
        hyp.Q_normal_in_H v
          (hyp.D_le_H (hyp.V_le_D (hyp.W_le_V v.2))) x x.2⟩
      invFun := fun x => ⟨(v : G)⁻¹ * x * (v : G), by
        simpa using hyp.Q_normal_in_H (v : G)⁻¹
          (inv_mem (hyp.D_le_H (hyp.V_le_D (hyp.W_le_V v.2)))) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by
        change (v : G) * ((x : G) * (y : G)) * (v : G)⁻¹ =
          ((v : G) * x * (v : G)⁻¹) * ((v : G) * y * (v : G)⁻¹)
        group) }
  map_one' := by
    ext x
    change ((1 : ↥hyp.W) : G) * (x : G) * ((1 : ↥hyp.W) : G)⁻¹ = (x : G)
    simp
  map_mul' v u := by
    ext x
    change (((v : G) * (u : G)) * (x : G) * (((v : G) * (u : G))⁻¹)) =
      (v : G) * ((u : G) * (x : G) * (u : G)⁻¹) * (v : G)⁻¹
    group

@[simp] lemma conjQByW_apply_val (v : ↥hyp.W) (x : ↥hyp.Q) :
    ((hyp.conjQByW v x : ↥hyp.Q) : G) = (v : G) * (x : G) * (v : G)⁻¹ := rfl

/-- Every element of `W` fixes the center of `Q` pointwise once the center
is identified with `Q₀`. -/
theorem conjQByW_fixes_center
    (hZQ0 : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (v : ↥hyp.W) :
    ∀ z ∈ Subgroup.center hyp.Q, hyp.conjQByW v z = z := by
  intro z hz
  have hzQ0 : (z : G) ∈ hyp.Q0 := by
    rw [hZQ0] at hz
    exact hz
  have hcomm : (v : G) * (z : G) = (z : G) * (v : G) := by
    have hmem := hyp.Q0_le_centralizer_zpowers_of_mem_W v.2 hzQ0
    rw [Subgroup.mem_centralizer_iff] at hmem
    exact hmem (v : G) (Subgroup.mem_zpowers _)
  apply Subtype.ext
  rw [hyp.conjQByW_apply_val]
  calc (v : G) * (z : G) * (v : G)⁻¹ = (z : G) * (v : G) * (v : G)⁻¹ := by
        rw [hcomm]
    _ = (z : G) := by group

/-- Every element of `W` commutes with the actual `K`-actor on `Q`:
`W = C_V(K)` centralizes `K` elementwise in `G`. -/
theorem conjQByW_commute_actualKActor (v : ↥hyp.W)
    (k : ↥hyp.actualKActor) :
    Commute (hyp.actualKActor.subtype k) (hyp.conjQByW v) := by
  obtain ⟨k', hk'⟩ := k.2
  have hcommG : (k' : G) * (v : G) = (v : G) * (k' : G) := by
    have hwC : (v : G) ∈ Subgroup.centralizer (hyp.K : Set G) := by
      rw [hyp.coe_K]
      exact v.2.2
    rw [Subgroup.mem_centralizer_iff] at hwC
    exact hwC (k' : G) k'.2
  have hgoal : hyp.conjQByK k' * hyp.conjQByW v =
      hyp.conjQByW v * hyp.conjQByK k' := by
    ext x
    rw [MulAut.mul_apply, MulAut.mul_apply, hyp.conjQByK_apply_val,
      hyp.conjQByW_apply_val, hyp.conjQByW_apply_val,
      hyp.conjQByK_apply_val]
    calc (k' : G) * ((v : G) * (x : G) * (v : G)⁻¹) * (k' : G)⁻¹
        = ((k' : G) * v) * (x : G) * ((k' : G) * v)⁻¹ := by group
      _ = ((v : G) * k') * (x : G) * ((v : G) * k')⁻¹ := by rw [hcommG]
      _ = (v : G) * ((k' : G) * (x : G) * (k' : G)⁻¹) * (v : G)⁻¹ := by
          group
  change (k : MulAut ↥hyp.Q) * hyp.conjQByW v =
    hyp.conjQByW v * (k : MulAut ↥hyp.Q)
  rw [← hk']
  exact hgoal

/-! ## The conjugation automorphism attached to `1 ≠ w ∈ W` -/

/-- The facts about `ω = conjQByW w` needed by the moved-summand engine:
`ω` is nontrivial of odd order, fixes `Z(Q)` pointwise, commutes with the
`K`-actor, and the fixed points of its nontrivial powers lie in `Z(Q)`.
The last input is the first reduction `C_Q(w^i) = Q₀` of Lemma 5. -/
theorem conjQByW_omega_facts
    {w : G} (hw : w ∈ hyp.W) (hw1 : w ≠ 1)
    (hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card hyp.Q = Nat.card hyp.Q0 ^ 3)
    (inductionHypothesis : TheoremAInductionBelow G Ω)
    (hZQ0 : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q) :
    hyp.conjQByW ⟨w, hw⟩ ≠ 1 ∧
    Odd (orderOf (hyp.conjQByW ⟨w, hw⟩)) ∧
    (∀ z ∈ Subgroup.center hyp.Q, hyp.conjQByW ⟨w, hw⟩ z = z) ∧
    (∀ k : ↥hyp.actualKActor,
      Commute (hyp.actualKActor.subtype k) (hyp.conjQByW ⟨w, hw⟩)) ∧
    ∀ i : ℕ, hyp.conjQByW ⟨w, hw⟩ ^ i ≠ 1 →
      ∀ x : ↥hyp.Q, (hyp.conjQByW ⟨w, hw⟩ ^ i) x = x →
        x ∈ Subgroup.center hyp.Q := by
  set ω : MulAut ↥hyp.Q := hyp.conjQByW ⟨w, hw⟩ with hωdef
  have hω1 : ω ≠ 1 := by
    intro h1
    have hQle : hyp.Q ≤ Subgroup.centralizer {w} := by
      intro x hx
      have happ : ((ω ⟨x, hx⟩ : ↥hyp.Q) : G) = x := by
        rw [h1]
        rfl
      rw [hωdef, hyp.conjQByW_apply_val] at happ
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * w = (w * x * w⁻¹) * w := by
            rw [show w * x * w⁻¹ = x from happ]
        _ = w * x := by group
    have hred := hyp.Q_inf_centralizer_singleton_eq_Q0_of_orderThree hw hw1
      hst hcardQ inductionHypothesis
    have hQQ0 : hyp.Q = hyp.Q0 := by
      rw [← hred]
      exact (inf_eq_left.mpr hQle).symm
    have hlt : 2 ^ m < (2 ^ m) ^ 3 := by
      rw [← pow_mul]
      exact Nat.pow_lt_pow_right one_lt_two (by omega)
    rw [hQQ0, hQ0card] at hcardQ
    exact Nat.ne_of_lt hlt hcardQ
  have hωodd : Odd (orderOf ω) := by
    have h1 : orderOf ω ∣ orderOf (⟨w, hw⟩ : ↥hyp.W) :=
      orderOf_map_dvd hyp.conjQByW _
    have h2 : orderOf (⟨w, hw⟩ : ↥hyp.W) ∣ Nat.card ↥hyp.W :=
      orderOf_dvd_natCard _
    have h3 : Nat.card ↥hyp.W ∣ Nat.card ↥hyp.D :=
      Subgroup.card_dvd_of_le (hyp.W_le_V.trans hyp.V_le_D)
    exact hyp.D_odd.of_dvd_nat ((h1.trans h2).trans h3)
  have hωZ : ∀ z ∈ Subgroup.center hyp.Q, ω z = z :=
    hyp.conjQByW_fixes_center hZQ0 ⟨w, hw⟩
  have hωcomm : ∀ k : ↥hyp.actualKActor,
      Commute (hyp.actualKActor.subtype k) ω := fun k =>
    hyp.conjQByW_commute_actualKActor ⟨w, hw⟩ k
  have hωfix : ∀ i : ℕ, ω ^ i ≠ 1 → ∀ x : ↥hyp.Q, (ω ^ i) x = x →
      x ∈ Subgroup.center hyp.Q := by
    intro i hi x hx
    have hpow : ω ^ i = hyp.conjQByW ((⟨w, hw⟩ : ↥hyp.W) ^ i) := by
      rw [hωdef, map_pow]
    have hwm : w ^ i ∈ hyp.W := pow_mem hw i
    have hwm1 : w ^ i ≠ 1 := by
      intro h
      apply hi
      have hsub : (⟨w, hw⟩ : ↥hyp.W) ^ i = 1 := Subtype.ext (by simpa using h)
      rw [hpow, hsub, map_one]
    have hred := hyp.Q_inf_centralizer_singleton_eq_Q0_of_orderThree hwm hwm1
      hst hcardQ inductionHypothesis
    have happ : w ^ i * (x : G) * (w ^ i)⁻¹ = x := by
      have := congrArg (fun y : ↥hyp.Q => (y : G)) hx
      rw [hpow] at this
      simpa [hyp.conjQByW_apply_val] using this
    have hxC : (x : G) ∈ Subgroup.centralizer {w ^ i} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (x : G) * w ^ i = (w ^ i * (x : G) * (w ^ i)⁻¹) * w ^ i := by
            rw [happ]
        _ = w ^ i * (x : G) := by group
    have hmem : (x : G) ∈ hyp.Q ⊓ Subgroup.centralizer {w ^ i} :=
      ⟨x.2, hxC⟩
    rw [hred] at hmem
    rw [hZQ0]
    exact hmem
  exact ⟨hω1, hωodd, hωZ, hωcomm, hωfix⟩

/-! ## The Lemma 5 setup bundle -/

/-- The engine inputs of Lemma 5, bundled for reuse: the exponent-2 center
identified with `Q₀`, the transitive fixed-point-free actor facts, the
cardinalities, and the isomorphic two-summand split of `Q ⧸ Z(Q)`. -/
structure LemmaFiveSetup (hyp : Hypothesis G Ω) (m : ℕ) where
  /-- the center has exponent two -/
  centerSq : ∀ z ∈ Subgroup.center hyp.Q, z ^ 2 = 1
  /-- squares are central -/
  sqMem : ∀ x : ↥hyp.Q, x ^ 2 ∈ Subgroup.center hyp.Q
  /-- involutions are central -/
  invMem : ∀ x : ↥hyp.Q, x ^ 2 = 1 → x ∈ Subgroup.center hyp.Q
  /-- the actor is transitive on the nonidentity central elements -/
  transCenter : ∀ s₁ s₂ : ↥hyp.Q, s₁ ∈ Subgroup.center hyp.Q → s₁ ≠ 1 →
    s₂ ∈ Subgroup.center hyp.Q → s₂ ≠ 1 →
    ∃ k : ↥hyp.actualKActor, hyp.actualKActor.subtype k s₁ = s₂
  /-- the induced actor action on the central quotient is fixed-point-free -/
  freeQuotient : ∀ k : ↥hyp.actualKActor, k ≠ 1 →
    ∀ q : ↥hyp.Q ⧸ Subgroup.center hyp.Q,
      IsAInvariant.quotientMulAutHom
        (IsAInvariant.of_characteristic hyp.actualKActor.subtype) k q = q →
      q = 1
  /-- the actor has order `2^m - 1` -/
  cardActor : Nat.card ↥hyp.actualKActor = 2 ^ m - 1
  /-- the actor has order `|Z(Q)| - 1` -/
  cardActorCenter : Nat.card ↥hyp.actualKActor =
    Nat.card ↥(Subgroup.center hyp.Q) - 1
  /-- the center is nontrivial -/
  centerNeBot : Subgroup.center hyp.Q ≠ ⊥
  /-- the center is exactly `Q₀` -/
  centerEqQ0 : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q
  /-- the isomorphic two-summand split of the central quotient -/
  isplit : Suzuki2Groups.IsomorphicOrderQModuleSplit hyp.actualKActor.subtype
    (Subgroup.center hyp.Q)
    (IsAInvariant.of_characteristic hyp.actualKActor.subtype)

/-- **The Lemma 5 setup** (Peterfalvi Part II, Ch. I §3, Lemma 5, p. 107).
If `|st| = 3`, `Q` is a Suzuki `2`-group of order `q³` with `q = |Q₀| = 2^m`,
and `1 ≠ w ∈ W`, the engine inputs of Lemma 5 can all be constructed; in
particular `Q ⧸ Z(Q)` has an equivariantly isomorphic invariant two-summand
split obtained by moving one summand with `w`. -/
theorem lemmaFiveSetup_of_orderThree_of_mem_W
    {w : G} (hw : w ∈ hyp.W) (hw1 : w ≠ 1)
    (hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hQsuz : IsSuzuki2Group ↥hyp.Q)
    {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card hyp.Q = Nat.card hyp.Q0 ^ 3)
    (inductionHypothesis : TheoremAInductionBelow G Ω) :
    Nonempty (hyp.LemmaFiveSetup m) := by
  classical
  have hKcyc : IsCyclic ↥hyp.actualKActor := hyp.actualKActor_isCyclic
  have hreg : ActsRegularlyOnInvolutions hyp.actualKActor :=
    hyp.actualKActor_actsRegularlyOnInvolutions
  -- cardinalities
  have hKKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1 := by
    have h1 : Nat.card ↥hyp.actualKActor = Nat.card ↥hyp.K :=
      Nat.card_congr (MonoidHom.ofInjective hyp.conjQByK_injective).toEquiv.symm
    rw [h1, hyp.card_K_eq_card_Q0_sub_one, hQ0card]
  have hcard : Nat.card ↥hyp.Q = (2 ^ m) ^ 3 := by
    rw [hcardQ, hQ0card]
  -- the Higman center payload
  obtain ⟨hZΦ, hZsq, ⟨csplit⟩⟩ :=
    center_payload_of_card_eq_cube hQsuz hKcyc hreg hm hKKcard hcard
  -- the center is exactly `Q₀`
  have hZQ0 : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q :=
    hyp.center_Q_eq_Q0_subgroupOf_of_sq_eq_one hZsq
  have hZcard : Nat.card ↥(Subgroup.center hyp.Q) = 2 ^ m := by
    rw [hZQ0,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv,
      hQ0card]
  have hcardK' : Nat.card ↥hyp.actualKActor =
      Nat.card ↥(Subgroup.center hyp.Q) - 1 := by
    rw [hZcard, hKKcard]
  have hZbot : Subgroup.center hyp.Q ≠ ⊥ := by
    intro h
    have hone : Nat.card ↥(Subgroup.center hyp.Q) = 1 := by
      rw [h, Subgroup.card_bot]
    rw [hZcard] at hone
    exact hm (by simpa using Nat.pow_eq_one.mp hone)
  -- ξ-structure inputs for the Agemo identity
  obtain ⟨hP2, hncomm, hmulti, -⟩ := id hQsuz
  have hxi : IsXiActor hyp.actualKActor := ⟨hKcyc, hreg.transitive⟩
  have hlen : HasXiLengthThree hyp.actualKActor.subtype :=
    hasXiLengthThree_of_card_eq_cube hQsuz hKcyc hreg hm hKKcard hcard
  obtain ⟨u₀, -, hu₀, -, -⟩ := id hmulti
  have hinvcard : (involutions ↥hyp.Q).ncard = Nat.card ↥hyp.actualKActor :=
    ncard_involutions_eq_card_of_regular hreg hu₀
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥hyp.actualKActor →
      p ∣ (involutions ↥hyp.Q).ncard := fun p _ hp => hinvcard ▸ hp
  have hAg := agemo_one_eq_frattini_of_xiLengthThree hP2 hncomm hmulti hxi
    hlen hprime
  -- squares land in the center; involutions are central
  have hAgemo : ∀ x : ↥hyp.Q, x ^ 2 ∈ Subgroup.center hyp.Q := by
    intro x
    rw [hZΦ, ← hAg]
    simpa using Agemo.mem_of_eq_pow (G := ↥hyp.Q) (p := 2) (n := 1) x
  have hinvZ : ∀ x : ↥hyp.Q, x ^ 2 = 1 → x ∈ Subgroup.center hyp.Q := by
    intro x hx2
    rcases eq_or_ne x 1 with rfl | hx1
    · exact Subgroup.one_mem _
    · exact involutions_subset_center hQsuz ⟨hx2, hx1⟩
  -- transitivity of `K` on the nonidentity central elements
  have htransZ : ∀ s₁ s₂ : ↥hyp.Q, s₁ ∈ Subgroup.center hyp.Q → s₁ ≠ 1 →
      s₂ ∈ Subgroup.center hyp.Q → s₂ ≠ 1 →
      ∃ k : ↥hyp.actualKActor, hyp.actualKActor.subtype k s₁ = s₂ := by
    intro s₁ s₂ hs₁ hs₁1 hs₂ hs₂1
    obtain ⟨k, hk, -⟩ := hreg s₁ ⟨hZsq s₁ hs₁, hs₁1⟩ s₂ ⟨hZsq s₂ hs₂, hs₂1⟩
    exact ⟨k, hk⟩
  -- fixed-point-freeness descends to the central quotient
  have hfreeP := fixedPointFree_of_actsRegularlyOnInvolutions hP2 hreg
  have hfree : ∀ k : ↥hyp.actualKActor, k ≠ 1 →
      ∀ q : ↥hyp.Q ⧸ Subgroup.center hyp.Q,
        IsAInvariant.quotientMulAutHom
          (IsAInvariant.of_characteristic hyp.actualKActor.subtype) k q = q →
          q = 1 := by
    apply Suzuki2Groups.quotient_fixedPointFree_of_fixedPoints_le
      hyp.actualKActor.subtype (Subgroup.center hyp.Q)
      (IsAInvariant.of_characteristic hyp.actualKActor.subtype)
    · exact Suzuki2Groups.card_coprime_of_card_eq_sub_one
        (Subgroup.center hyp.Q) hcardK'
    · intro k hk x hx
      rw [hfreeP k hk x hx]
      exact Subgroup.one_mem _
  -- the odd-order automorphism given by conjugation by `w`
  obtain ⟨hω1, hωodd, hωZ, hωcomm, hωfix⟩ :=
    hyp.conjQByW_omega_facts hw hw1 hst hm hQ0card hcardQ
      inductionHypothesis hZQ0
  -- assemble the isomorphic split
  obtain ⟨isplit⟩ :=
    Suzuki2Groups.nonempty_isomorphicOrderQModuleSplit_of_commuting_automorphism
      (le_refl _) hZsq hAgemo hinvZ csplit htransZ hfree hcardK' hZbot
      (hyp.conjQByW ⟨w, hw⟩) hω1 hωodd hωZ hωcomm hωfix
  exact ⟨{
    centerSq := hZsq
    sqMem := hAgemo
    invMem := hinvZ
    transCenter := htransZ
    freeQuotient := hfree
    cardActor := hKKcard
    cardActorCenter := hcardK'
    centerNeBot := hZbot
    centerEqQ0 := hZQ0
    isplit := isplit }⟩

/-! ## Lemma 5, type-B branch -/

/-- **Peterfalvi Part II, Ch. I §3, Lemma 5** (type-B branch, p. 107).
If `|st| = 3`, `Q` is a Suzuki `2`-group of order `q³` with `q = |Q₀| = 2^m`,
and `W ≠ 1`, then `Q` is of type B. -/
theorem isTypeB_Q_of_orderThree_of_mem_W
    {w : G} (hw : w ∈ hyp.W) (hw1 : w ≠ 1)
    (hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hQsuz : IsSuzuki2Group ↥hyp.Q)
    {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card hyp.Q = Nat.card hyp.Q0 ^ 3)
    (inductionHypothesis : TheoremAInductionBelow G Ω) :
    Suzuki2Groups.IsTypeB.{uG, 0} ↥hyp.Q := by
  obtain ⟨s⟩ := hyp.lemmaFiveSetup_of_orderThree_of_mem_W hw hw1 hst hQsuz
    hm hQ0card hcardQ inductionHypothesis
  have hcard : Nat.card ↥hyp.Q = (2 ^ m) ^ 3 := by
    rw [hcardQ, hQ0card]
  exact isTypeB_of_isomorphicOrderQModuleSplit_of_card_eq_cube hQsuz
    hyp.actualKActor_isCyclic hyp.actualKActor_actsRegularlyOnInvolutions
    hm s.cardActor hcard s.isplit

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
