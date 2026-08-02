/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourCorollaryOne
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.CaseABConclusion

/-!
# Peterfalvi Part II, Ch. IV §4, opening paragraph: the dichotomy that closes Theorem A

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV, p. 132.

Chapter IV has two halves, and the book joins them in a single sentence at the head of §4:

> By the proposition of §2 and Corollary 1 to the proposition of §3, to complete the proof
> of Theorem A, we may assume that `D` has a subgroup `P` of prime order `p` such that
> `C_{Q/Q₀}(P) ≠ 1`.  Since `C_Q(P) ≠ 1`, `P` has three fixed points on `Ω` and so is
> conjugate in `D` to a subgroup of `V`.  We may assume that `P ⊆ V`.  Since `W` acts
> fixed-point-freely on `Q/Q₀`, `P ∩ W = 1`.

So the dichotomy is on `Hypothesis.FreeD` — "`D` acts without fixed points on `(Q/Q₀)^#`",
the standing hypothesis of §2 — and *not* on `V = W`, which is strictly stronger
(issue 0169).  This file supplies the missing direction, `¬ FreeD ⟹ SectionFourSetup`,
and then the case split itself.

## Main results

* `Hypothesis.classStabilizer` — the stabilizer in `D` of a class of `Q/Q₀`.  `FreeD` says
  it is trivial for every `ω ∈ Q − Q₀`.
* `Hypothesis.exists_sectionFourSetup_of_not_freeD` — the four sentences quoted above:
  from a non-trivial class stabilizer, a subgroup `P ≤ V` of prime order with `P ∩ W = 1`
  and a `P`-fixed class outside `Q₀`, i.e. §4's `SectionFourSetup`.
* `SecondCaseHypothesis.nonempty_theoremAConclusion_of_caseC` — **Theorem A's conclusion
  in case (c) of Ch. III §1**: `by_cases` on `FreeD`, §2 + Corollary 1 on one side and §4
  on the other.
* `Hypothesis.SectionFourSetup.two_lt_natCard_inf_centralizer_Q0` — the book's `ℓ > 2`
  inside step (1) of §4.
* `SecondCaseHypothesis.nonempty_theoremAConclusion` — **Theorem A under the standing
  hypothesis of Ch. III**, all three cases of the Proposition of §1 together
  (`theoremAConclusion_or_caseC2` disposes of (a) and (b)), with the induction hypothesis
  as its only input.

Both clauses of §4's step (1) come from Ch. I §3 Proposition 1(c) and are supplied here,
not assumed: "`C_G(P)` has 2-rank ≥ 2" is the field
`SecondCaseHypothesis.twoRank_centralizer_ge_two`, and `ℓ > 2` is
`PSU3InductionTarget.one_lt_n` transported along `|C_{Q₀}(P)| = ℓ`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open OddOrder.GroupTheory.Suzuki2Group

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## The stabilizer in `D` of a class of `Q/Q₀` -/

/-- **The stabilizer in `D` of the class `ω Q₀`** (Peterfalvi Part II, Ch. IV §2, p. 129).

The quotient `Q/Q₀` is never formed in this development; "`c` fixes the class of `ω`" is
spelled out as `c ω c⁻¹ ω⁻¹ ∈ Q₀`, which is the shape both `FreeD` and §4's
`SectionFourSetup.x_class_fixed` use.  Collecting those `c` into a subgroup is what turns
"some `c ≠ 1` fixes the class" into "some subgroup of *prime order* fixes it", which is
how §4 states its hypothesis. -/
def classStabilizer (ω : G) : Subgroup G where
  carrier := {c | c ∈ hyp.D ∧ c * ω * c⁻¹ * ω⁻¹ ∈ hyp.Q0}
  one_mem' := ⟨hyp.D.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨haD, ha⟩ ⟨hbD, hb⟩
    refine ⟨hyp.D.mul_mem haD hbD, ?_⟩
    have hexp : a * b * ω * (a * b)⁻¹ * ω⁻¹
        = a * (b * ω * b⁻¹ * ω⁻¹) * a⁻¹ * (a * ω * a⁻¹ * ω⁻¹) := by group
    rw [hexp]
    exact hyp.Q0.mul_mem (hyp.conj_mem_Q0_of_mem_D haD hb) ha
  inv_mem' := by
    rintro a ⟨haD, ha⟩
    refine ⟨hyp.D.inv_mem haD, ?_⟩
    have hexp : a⁻¹ * ω * a⁻¹⁻¹ * ω⁻¹
        = (a⁻¹ * (a * ω * a⁻¹ * ω⁻¹) * a⁻¹⁻¹)⁻¹ := by group
    rw [hexp]
    exact hyp.Q0.inv_mem (hyp.conj_mem_Q0_of_mem_D (hyp.D.inv_mem haD) ha)

theorem mem_classStabilizer {ω c : G} :
    c ∈ hyp.classStabilizer ω ↔ c ∈ hyp.D ∧ c * ω * c⁻¹ * ω⁻¹ ∈ hyp.Q0 := Iff.rfl

theorem classStabilizer_le_D (ω : G) : hyp.classStabilizer ω ≤ hyp.D :=
  fun _ hc => hc.1

/-- Elements of `Q₀` are central in `Q` — the content of `hZ`, in element form. -/
theorem commute_of_mem_Q0_of_center (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {y x : G} (hy : y ∈ hyp.Q0) (hx : x ∈ hyp.Q) : x * y = y * x := by
  have hmem : (⟨y, hyp.Q0_le_Q hy⟩ : ↥hyp.Q) ∈ Subgroup.center hyp.Q := by
    rw [hZ]; exact Subgroup.mem_subgroupOf.mpr hy
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨x, hx⟩)

/-- **`q > 2`** — a Suzuki `2`-group has two distinct involutions by definition, and every
involution of `Q` lies in `Q₀ = {x ∈ H | x² = 1}`, so `|Q₀| ≥ 3`.

This sharpens `two_le_card_Q0`, and it is what turns `|Q₀| = 2^m` into `1 < m`, the
numerical hypothesis Ch. IV §3 carries (`3 ≤ |F|`). -/
theorem two_lt_card_Q0_of_isSuzuki2Group (hQsuz : IsSuzuki2Group ↥hyp.Q) :
    2 < Nat.card ↥hyp.Q0 := by
  classical
  obtain ⟨-, -, ⟨x, y, hx, hy, hxy⟩, -⟩ := hQsuz
  have hmem : ∀ z : ↥hyp.Q, z ∈ involutions ↥hyp.Q → (z : G) ∈ hyp.Q0 := fun z hz =>
    ⟨by simpa using congrArg Subtype.val hz.1, hyp.Q_le_H z.2⟩
  have hx1 : (x : G) ≠ 1 := fun hcon => hx.2 (Subtype.ext hcon)
  have hy1 : (y : G) ≠ 1 := fun hcon => hy.2 (Subtype.ext hcon)
  have hxy' : (x : G) ≠ (y : G) := fun hcon => hxy (Subtype.ext hcon)
  have hsub : ({1, (x : G), (y : G)} : Set G) ⊆ (hyp.Q0 : Set G) := by
    rintro z (rfl | rfl | rfl)
    · exact hyp.Q0.one_mem
    · exact hmem x hx
    · exact hmem y hy
  have hcount : ({1, (x : G), (y : G)} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hx1, Ne.symm hy1]),
      Set.ncard_insert_of_notMem (by simp [hxy']), Set.ncard_singleton]
  have hcard : ((hyp.Q0 : Set G)).ncard = Nat.card ↥hyp.Q0 := (Nat.card_coe_set_eq _).symm
  have hthree : (3 : ℕ) ≤ Nat.card ↥hyp.Q0 := by
    rw [← hcard]
    calc (3 : ℕ) = ({1, (x : G), (y : G)} : Set G).ncard := hcount.symm
      _ ≤ (hyp.Q0 : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-! ## `¬ FreeD` produces §4's standing data -/

/-- The negation of §2's hypothesis, unpacked. -/
theorem exists_ne_one_of_not_freeD (hfree : ¬ hyp.FreeD) :
    ∃ ω c y : G, ω ∈ hyp.Q ∧ ω ∉ hyp.Q0 ∧ c ∈ hyp.D ∧ y ∈ hyp.Q0 ∧
      c⁻¹ * ω * c = ω * y ∧ c ≠ 1 := by
  by_contra hc
  refine hfree fun ⦃ω c y⦄ hωQ hωQ0 hcD hy hconj => ?_
  by_contra hc1
  exact hc ⟨ω, c, y, hωQ, hωQ0, hcD, hy, hconj, hc1⟩

/-- **A prime-order subgroup fixing a class of `(Q/Q₀)^#`** — the book's

> we may assume that `D` has a subgroup `P` of prime order `p` such that
> `C_{Q/Q₀}(P) ≠ 1`

(p. 132), in the only form §2's hypothesis can fail: some `c ≠ 1` in `D` fixes some class
`ω Q₀ ≠ Q₀`, and then so does any subgroup of prime order of `⟨c⟩`. -/
theorem exists_prime_order_le_classStabilizer_of_not_freeD
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q) (hfree : ¬ hyp.FreeD) :
    ∃ (ω : G) (P : Subgroup G) (p : ℕ), ω ∈ hyp.Q ∧ ω ∉ hyp.Q0 ∧ p.Prime ∧
      Nat.card ↥P = p ∧ P ≤ hyp.classStabilizer ω := by
  classical
  obtain ⟨ω, c, y, hωQ, hωQ0, hcD, hyQ0, hconj, hc1⟩ := hyp.exists_ne_one_of_not_freeD hfree
  -- `c⁻¹` fixes the class of `ω`: conjugating moves `ω` by the central element `y`
  have hfix : c⁻¹ * ω * c⁻¹⁻¹ * ω⁻¹ ∈ hyp.Q0 := by
    have hstep : c⁻¹ * ω * c⁻¹⁻¹ * ω⁻¹ = c⁻¹ * ω * c * ω⁻¹ := by group
    rw [hstep, hconj, hyp.commute_of_mem_Q0_of_center hZ hyQ0 hωQ]
    simpa using hyQ0
  have hcS : c⁻¹ ∈ hyp.classStabilizer ω := ⟨hyp.D.inv_mem hcD, hfix⟩
  have hcinv1 : c⁻¹ ≠ 1 := fun h => hc1 (inv_eq_one.mp h)
  -- a prime dividing the order of `c⁻¹` divides the order of the stabilizer
  obtain ⟨p, hp, hpdvd⟩ :=
    Nat.exists_prime_and_dvd (n := orderOf c⁻¹) fun h => hcinv1 (orderOf_eq_one_iff.mp h)
  haveI := Fact.mk hp
  have hdvd : orderOf c⁻¹ ∣ Nat.card ↥(hyp.classStabilizer ω) :=
    Subgroup.orderOf_dvd_natCard _ hcS
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(hyp.classStabilizer ω)) p (hpdvd.trans hdvd)
  refine ⟨ω, Subgroup.zpowers ((x : G)), p, hωQ, hωQ0, hp, ?_, ?_⟩
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe]; exact hx
  · rw [Subgroup.zpowers_le]; exact x.2

/-- **🎯 The opening paragraph of Peterfalvi Part II, Ch. IV §4** (p. 132):

> we may assume that `D` has a subgroup `P` of prime order `p` such that
> `C_{Q/Q₀}(P) ≠ 1`.  Since `C_Q(P) ≠ 1`, `P` has three fixed points on `Ω` and so is
> conjugate in `D` to a subgroup of `V`.  We may assume that `P ⊆ V`.  Since `W` acts
> fixed-point-freely on `Q/Q₀`, `P ∩ W = 1`.

That is exactly the data of `SectionFourSetup`, so the failure of §2's hypothesis puts §4
in business.  The four steps are, in order:
`exists_prime_order_le_classStabilizer_of_not_freeD`, `exists_fixed_not_mem_Q0`
(Glauberman's coprime lift — the class fixed by `P` has a `P`-fixed representative, which
cannot lie in `Q₀`) followed by `three_le_ncard_fixedPoints_of_mem_centralizer`,
`exists_conj_mem_D_map_le_V` (Ch. I Prop 6 (c)), and
`eq_one_of_conj_eq_mul_Q0_of_mem_W` (`W` is fixed-point-free with no `V = W` in sight). -/
theorem exists_sectionFourSetup_of_not_freeD {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hQ2 : IsPGroup 2 ↥hyp.Q) (hSolv : IsSolvable ↥hyp.Q)
    (hfree : ¬ hyp.FreeD) :
    Nonempty hyp.SectionFourSetup := by
  classical
  obtain ⟨ω, P₀, p, hωQ, hωQ0, hp, hcard₀, hP₀S⟩ :=
    hyp.exists_prime_order_le_classStabilizer_of_not_freeD hZ hfree
  have hP₀D : P₀ ≤ hyp.D := hP₀S.trans (hyp.classStabilizer_le_D ω)
  have hclass : ∀ a ∈ P₀, a * ω * a⁻¹ * ω⁻¹ ∈ hyp.Q0 := fun a ha => (hP₀S ha).2
  -- `p` is odd, since `P₀ ≤ D` and `|D|` is odd
  have hpdvdD : p ∣ Nat.card ↥hyp.D := hcard₀ ▸ Subgroup.card_dvd_of_le hP₀D
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with rfl | h
    · exfalso
      obtain ⟨j, hj⟩ := hpdvdD
      have hmod := Nat.odd_iff.mp hyp.D_odd
      omega
    · exact h
  -- Glauberman's step needs `(|P₀|, |Q|) = 1`
  obtain ⟨n, hQcard⟩ := hQ2.exists_card_eq
  have hoddsub : Odd (Nat.card ↥(P₀.subgroupOf hyp.D)) :=
    Nat.coprime_two_left.mp
      ((Nat.coprime_two_left.mpr hyp.D_odd).coprime_dvd_right
        (Subgroup.card_subgroup_dvd_card _))
  have hCop : Nat.Coprime (Nat.card ↥(P₀.subgroupOf hyp.D)) (Nat.card ↥hyp.Q) := by
    rw [hQcard]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hoddsub)
  -- a `P₀`-fixed element of `Q − Q₀`
  obtain ⟨z, hzQ, hz0, hzfix⟩ :=
    hyp.exists_fixed_not_mem_Q0 hZ hP₀D hCop hSolv hωQ hωQ0 hclass
  have hz1 : z ≠ 1 := fun h => hz0 (h ▸ hyp.Q0.one_mem)
  have hzc : ∀ a ∈ P₀, a * z = z * a := by
    intro a ha
    calc a * z = a * z * a⁻¹ * a := by group
      _ = z * a := by rw [hzfix a ha]
  -- three fixed points, hence conjugate into `V` (Ch. I Prop 6 (c))
  have h3 := hyp.three_le_ncard_fixedPoints_of_mem_centralizer hP₀D hzQ hz1 hzc
  obtain ⟨k, hkD, hPV⟩ := hyp.exists_conj_mem_D_map_le_V hP₀D h3
  -- transport the fixed class along the conjugation
  have hxQ : k * ω * k⁻¹ ∈ hyp.Q := hyp.Q_normal_in_H k (hyp.D_le_H hkD) ω hωQ
  have hx0 : k * ω * k⁻¹ ∉ hyp.Q0 := by
    intro hc
    refine hωQ0 ?_
    have hback : ω = k⁻¹ * (k * ω * k⁻¹) * k⁻¹⁻¹ := by group
    rw [hback]
    exact hyp.conj_mem_Q0_of_mem_D (hyp.D.inv_mem hkD) hc
  have hxfix : ∀ a ∈ P₀.map (MulAut.conj k).toMonoidHom,
      a * (k * ω * k⁻¹) * a⁻¹ * (k * ω * k⁻¹)⁻¹ ∈ hyp.Q0 := by
    rintro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    have heq : (MulAut.conj k).toMonoidHom a₀ = k * a₀ * k⁻¹ := rfl
    rw [heq]
    have hexp : k * a₀ * k⁻¹ * (k * ω * k⁻¹) * (k * a₀ * k⁻¹)⁻¹ * (k * ω * k⁻¹)⁻¹
        = k * (a₀ * ω * a₀⁻¹ * ω⁻¹) * k⁻¹ := by group
    rw [hexp]
    exact hyp.conj_mem_Q0_of_mem_D hkD (hclass a₀ ha₀)
  refine ⟨{ P := P₀.map (MulAut.conj k).toMonoidHom
            P_le_V := hPV
            P_inf_W := ?_
            cardP := p
            prime_cardP := hp
            odd_cardP := hpodd
            card_P := ?_
            x := k * ω * k⁻¹
            x_mem_Q := hxQ
            x_notMem_Q0 := hx0
            x_class_fixed := hxfix }⟩
  · -- `P ∩ W = 1`, because `W` is fixed-point-free on `(Q/Q₀)^#`
    refine (Subgroup.eq_bot_iff_forall _).mpr ?_
    intro a ha
    obtain ⟨haP, haW⟩ := Subgroup.mem_inf.mp ha
    have hyQ0 := hxfix a haP
    have hcomm := hyp.commute_of_mem_Q0_of_center hZ hyQ0 hxQ
    have hrel : a⁻¹⁻¹ * (k * ω * k⁻¹) * a⁻¹
        = (k * ω * k⁻¹) * (a * (k * ω * k⁻¹) * a⁻¹ * (k * ω * k⁻¹)⁻¹) := by
      rw [hcomm]; group
    exact inv_eq_one.mp (hyp.eq_one_of_conj_eq_mul_Q0_of_mem_W M hZ hmu hxQ hx0
      (hyp.W.inv_mem haW) hyQ0 hrel)
  · rw [← hcard₀]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective P₀ (MulAut.conj k).toMonoidHom
        (MulAut.conj k).injective).toEquiv.symm

/-- **`ℓ > 2`** (Peterfalvi Part II, Ch. IV §4, step (1), p. 132):

> **(1)** Let `U = O^{2′}(C_G(P))`.  Then `U/(P ∩ U) ≅ PSU(3, ℓ)` with `q = ℓ^p` and
> `ℓ > 2`.
>
> *Proof.* By (C1), `C_G(P)` has 2-rank `≥ 2` and, by Chapter I, §3, Proposition 1(c),
> `U/Z(U) = PSU(3, ℓ)` for some `ℓ > 2` since `st` has order `3` and `C_Q(P)` has exponent
> `4`.  Now `|C_{Q₀}(P)| = ℓ` …

`ℓ > 2` is not a side condition of §4: it is part of what the induction returns
(`PSU3InductionTarget.one_lt_n`, i.e. `ℓ = 2ⁿ` with `n ≥ 2` — the standard `PSU(3, ℓ)`
model is only defined for those `ℓ`), and `|C_{Q₀}(P)| = ℓ` is
`natCard_centralizerQ0_eq_baseField_of_psu3Target`.  The branch itself is §4's own
`nonempty_psu3Data_sectionFour`, which is where `|st| = 3` and the exponent discriminator
are spent. -/
theorem SectionFourSetup.two_lt_natCard_inf_centralizer_Q0 (s4 : hyp.SectionFourSetup)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hQsuz : IsSuzuki2Group ↥hyp.Q)
    (hCop : Nat.Coprime (Nat.card ↥(s4.P.subgroupOf hyp.D)) (Nat.card ↥hyp.Q))
    (hSolv : IsSolvable ↥hyp.Q) (hP : s4.P ≠ ⊥)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer ((s4.P : Set G))),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (hord : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (ih : TheoremAInductionBelow G Ω) :
    2 < Nat.card ↥(hyp.Q0 ⊓ Subgroup.centralizer ((s4.P : Set G))) := by
  classical
  letI := hyp.centralizerQuotientMulAction s4.P_le_V
  obtain ⟨result, data, -⟩ :=
    hyp.nonempty_psu3Data_sectionFour s4 hZ hQsuz hCop hSolv hP hA3 hord ih
  have hbridge : Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer ((s4.P : Set G))))
      = Nat.card ↥(hyp.Q0 ⊓ Subgroup.centralizer ((s4.P : Set G))) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hcard :=
    hyp.natCard_centralizerQ0_eq_baseField_of_psu3Target s4.P_le_V hA3 result data
  rw [hbridge, OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.natCard_baseField
    data.n (Nat.zero_lt_one.trans data.one_lt_n)] at hcard
  have hpow : (2 : ℕ) ^ 2 ≤ 2 ^ data.n := Nat.pow_le_pow_right (by norm_num) data.one_lt_n
  omega

end Hypothesis

/-! ## Case (c) of Ch. III §1 closes Theorem A -/

namespace SecondCaseHypothesis

open OddOrder.GroupTheory.Suzuki2Group

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (sc : SecondCaseHypothesis G Ω)

/-- `(|P|, |Q|) = 1` for `P ≤ D`: `|D|` is odd and `Q` is a `2`-group. -/
theorem coprime_card_subgroupOf_D (hQ2 : IsPGroup 2 ↥sc.toHypothesis.Q)
    (P : Subgroup G) :
    Nat.Coprime (Nat.card ↥(P.subgroupOf sc.toHypothesis.D))
      (Nat.card ↥sc.toHypothesis.Q) := by
  obtain ⟨n, hQcard⟩ := hQ2.exists_card_eq
  have hodd : Odd (Nat.card ↥(P.subgroupOf sc.toHypothesis.D)) :=
    Nat.coprime_two_left.mp
      ((Nat.coprime_two_left.mpr sc.toHypothesis.D_odd).coprime_dvd_right
        (Subgroup.card_subgroup_dvd_card _))
  rw [hQcard]
  exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd)

/-- `C_Q(P)`, seen inside `C_G(P)`, is a `2`-group. -/
theorem isPGroup_two_Q_subgroupOf_centralizer (hQ2 : IsPGroup 2 ↥sc.toHypothesis.Q)
    (P : Subgroup G) :
    IsPGroup 2 ↥(sc.toHypothesis.Q.subgroupOf (Subgroup.centralizer (P : Set G))) := by
  intro x
  obtain ⟨k, hk⟩ := hQ2 ⟨((x : ↥(Subgroup.centralizer (P : Set G))) : G),
    Subgroup.mem_subgroupOf.mp x.2⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  simpa using congrArg Subtype.val hk

/-- **🎯🎯🎯🎯🎯🎯 Peterfalvi Part II, Theorem A in case (c) of Ch. III §1**
(pp. 116–117, 122–134): `O^{2′}(G) ≅ PSU(3, q)`, acting on `Ω` as on the Hermitian unital.

The case split is the book's own, at the head of §4 (p. 132): either `D` acts without
fixed points on `(Q/Q₀)^#`, and then the Proposition of §2 feeds Corollary 1 of §3
directly, or it does not, and then `exists_sectionFourSetup_of_not_freeD` produces the
standing data of §4, whose endgame feeds the *same* Corollary 1.  Neither half uses
`V = W`.

The hypotheses are case (c)'s output (`Q` a Suzuki `2`-group of order `q³`, `st` of order
`3`, `W ≠ 1`) plus the model data of Ch. III §3 and the induction hypothesis.  `ℓ > 2`
(`hl`) is the one clause of §4's step (1) still owed; see the module docstring. -/
theorem nonempty_theoremAConclusion_of_caseC
    {m : ℕ} (M : sc.toHypothesis.QuotientFieldModel m)
    (sfive : sc.toHypothesis.LemmaFiveSetup m) (hn : 1 < m)
    (hQ0card : Nat.card ↥sc.toHypothesis.Q0 = 2 ^ m)
    (hcardQ : Nat.card ↥sc.toHypothesis.Q = Nat.card ↥sc.toHypothesis.Q0 ^ 3)
    (hmu : Function.Injective M.mu)
    (hQsuz : IsSuzuki2Group ↥sc.toHypothesis.Q)
    (hord : orderOf (sc.toHypothesis.distinguishedInvolution * sc.toHypothesis.t) = 3)
    (hW : sc.toHypothesis.W ≠ ⊥)
    (ih : Hypothesis.TheoremAInductionBelow G Ω) :
    Nonempty (Hypothesis.TheoremAConclusion G Ω) := by
  classical
  have hm : m ≠ 0 := (Nat.zero_lt_one.trans hn).ne'
  have hQ2 : IsPGroup 2 ↥sc.toHypothesis.Q := sc.isPGroup_two_Q ih
  haveI : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  haveI : Group.IsNilpotent ↥sc.toHypothesis.Q := hQ2.isNilpotent
  have hSolv : IsSolvable ↥sc.toHypothesis.Q := inferInstance
  by_cases hfree : sc.toHypothesis.FreeD
  · -- §2's Proposition holds, and Corollary 1 of §3 reads it off
    obtain ⟨f, g, h, H₁, hfQ⟩ := sc.toHypothesis.exists_fgh_mapsTo
    have hC2 := sc.toHypothesis.braid_of_orderThree hord
    obtain ⟨hWcyc, hWdvd⟩ :=
      sc.toHypothesis.isCyclic_W_and_card_dvd_of_orderThree hord hQsuz hm hQ0card hcardQ ih
    obtain ⟨x₀, hx₀⟩ := sc.toHypothesis.exists_center_Q_ne_one
    have hcard : 3 ≤ Nat.card ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) := by
      rw [OddOrder.FiniteField.natCard_frobFixedSubfield M.card hm]
      have hpow : (2 : ℕ) ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hn
      omega
    have hW1 : 1 < Nat.card ↥sc.toHypothesis.W :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hW
    exact sc.toHypothesis.nonempty_theoremAConclusion_of_isStandardModel_of_closing
      H₁ hC2 hn sfive M sfive.centerEqQ0 hmu hfree hQ0card hcardQ hcard
      (sc.toHypothesis.card_actualKActor_eq sfive M hm hQ0card) hWdvd hW1 hWcyc hfQ x₀
      (sc.toHypothesis.exists_standardModel sfive M hord hm hQ0card hcardQ ih x₀ hx₀) hQ2
  · -- §2's hypothesis fails, and §4 takes over
    obtain ⟨s4⟩ := sc.toHypothesis.exists_sectionFourSetup_of_not_freeD M
      sfive.centerEqQ0 hmu hQ2 hSolv hfree
    have hPbot : s4.P ≠ ⊥ := by
      intro hc
      have hcard := s4.card_P
      rw [hc, Subgroup.card_bot] at hcard
      exact s4.prime_cardP.one_lt.ne hcard
    have hA3 := sc.twoRank_centralizer_ge_two s4.P s4.P_le_V s4.cardP s4.prime_cardP
      s4.card_P
    have hCop := sc.coprime_card_subgroupOf_D hQ2 s4.P
    exact Hypothesis.SectionFourSetup.nonempty_theoremAConclusion sc.toHypothesis s4 M sfive
      hQ0card hcardQ hmu hQ2 hQsuz hCop hSolv hPbot hA3 hord
      (sc.isPGroup_two_Q_subgroupOf_centralizer hQ2 s4.P) ih
      (Hypothesis.SectionFourSetup.two_lt_natCard_inf_centralizer_Q0 sc.toHypothesis s4
        sfive.centerEqQ0 hQsuz hCop hSolv hPbot hA3 hord ih)

include sc in
/-- **🎯🎯🎯🎯🎯🎯🎯 Peterfalvi Part II, Theorem A under the standing hypothesis of
Ch. III** (pp. 115–134): `O^{2′}(G)` is normal of odd index in `G` and carries the
standard model, in *all three* cases of the Proposition of Ch. III §1.

Cases (a) and (b) are `theoremAConclusion_or_caseC2` (Ch. III §3, p. 119, via Ch. I §3
Proposition 2); case (c) is the whole of Ch. IV, entered through
`nonempty_theoremAConclusion_of_caseC`.  Everything Ch. IV asks for beyond case (c)'s own
output is built here: the Lemma 5 setup and the field model of Ch. III §3 from a
non-trivial element of `W`, `μ`'s injectivity from Ch. III §3 step (4), and `q > 2` from
the two involutions a Suzuki `2`-group has by definition.

Nothing is owed: `ℓ > 2` comes out of the induction itself
(`SectionFourSetup.two_lt_natCard_inf_centralizer_Q0`). -/
theorem nonempty_theoremAConclusion (ih : Hypothesis.TheoremAInductionBelow G Ω) :
    Nonempty (Hypothesis.TheoremAConclusion G Ω) := by
  classical
  rcases sc.theoremAConclusion_or_caseC2 ih with hdone | ⟨-, hQsuz, hcardQ, hord, hW⟩
  · exact hdone
  -- case (c): build the model of Ch. III §3, then run Ch. IV's dichotomy
  have hQ2 : IsPGroup 2 ↥sc.toHypothesis.Q := sc.isPGroup_two_Q ih
  obtain ⟨m, hQ0card⟩ := (hQ2.to_le sc.toHypothesis.Q0_le_Q).exists_card_eq
  have hq2 := sc.toHypothesis.two_lt_card_Q0_of_isSuzuki2Group hQsuz
  rw [hQ0card] at hq2
  have hn : 1 < m := by
    by_contra hcon
    have hle : (2 : ℕ) ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hm : m ≠ 0 := (Nat.zero_lt_one.trans hn).ne'
  obtain ⟨w, hwW, hwbot⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hW)
  have hw1 : w ≠ 1 := fun hcon => hwbot (hcon ▸ Subgroup.one_mem ⊥)
  obtain ⟨sfive⟩ := sc.toHypothesis.lemmaFiveSetup_of_orderThree_of_mem_W hwW hw1 hord
    hQsuz hm hQ0card hcardQ ih
  obtain ⟨M⟩ := sc.toHypothesis.nonempty_quotientFieldModel_of_orderThree hord hQsuz hm
    hQ0card hcardQ ih sfive hwW hw1
  exact sc.nonempty_theoremAConclusion_of_caseC M sfive hn hQ0card hcardQ
    (sc.toHypothesis.mu_injective hord hm hQ0card hcardQ ih sfive M) hQsuz hord hW ih

end SecondCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
