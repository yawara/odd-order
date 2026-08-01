/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerTrichotomy
import OddOrder.Higman.Suzuki2Groups.CenterInvolutions
import OddOrder.GroupTheory.CoprimeFixedPoints
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3OrbitCount
import OddOrder.Peterfalvi.Appendices.Suzuki.GaloisCentralizer
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.PSUCentre

/-!
# Peterfalvi Part II, Ch. IV §4: the standing hypothesis and step (1)'s discriminators

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §4, step (1), p. 132:

> By (C1), `C_G(P)` has 2-rank `≥ 2` and, by Chapter I, §3, Proposition 1(c),
> `U/Z(U) ≅ PSU(3, ℓ)` for some `ℓ > 2` since `st` has order 3 and `C_Q(P)` has
> exponent 4.

Of the two conditions quoted there, `|st| = 3` excludes only the `Sz(ℓ)` branch — the
`PSL(2, ℓ)` branch has `|st| = 3` as well (`CentralizerPSLData`).  What excludes
`PSL(2, ℓ)` is the exponent: there `C_Q(X)` is elementary abelian, whereas `C_Q(P)` has
exponent `4`.

This file supplies that second discriminator in the form
`nonempty_psu3Data_of_orderOf_eq_three` consumes.  Its content is Higman's "evidently"
observation: `Q` is a Suzuki `2`-group, so all of its involutions are central
(`OddOrder.Higman.Suzuki2Groups.involutions_subset_center`), and `Z(Q) = Q₀`; hence an
element of `Q − Q₀` does *not* square to `1`.

## Main results

* `Hypothesis.sq_ne_one_of_not_mem_Q0` — the involutions of `Q` lie in `Q₀`.
* `Hypothesis.not_isElementaryAbelian_cQ_of_not_mem_Q0` — `C_Q(X)` is not elementary
  abelian once it meets `Q − Q₀`.
* `Hypothesis.conjQByD`, `Hypothesis.isAInvariant_conjQByD_Q0` — the conjugation action
  of `D` on `Q` and the `D`-invariance of `Q₀`, the data step (1)'s Glauberman reduction
  runs on.
* `Hypothesis.exists_fixed_not_mem_Q0` — Glauberman's step: a nontrivial `P`-fixed class
  of `Q/Q₀` has a `P`-fixed representative, necessarily outside `Q₀`.
* `Hypothesis.inf_W_eq_bot_of_centralizes`, `Hypothesis.eq_of_mem_mul_of_inf_eq_bot` —
  the two steps that take step (1) from `Z(U) ⊆ P W` to `Z(U) ⊆ P`.
* `Hypothesis.SectionFourSetup` — the standing hypothesis of §4, with
  `SectionFourSetup.not_isElementaryAbelian_cQ` (the exponent discriminator),
  `SectionFourSetup.natCard_Q0_eq_pow_cardP` (`q = ℓ^p`) and
  `SectionFourSetup.eq_P_of_centralizes` (`Z(U) ⊆ P`) read off it.
* `SectionFourSetup.inf_le_sup_W_of_centralizes`,
  `SectionFourSetup.inf_le_sup_centralizer_W` — step (2)'s `V ∩ U ⊆ P W` and
  `V ∩ U ⊆ P × C_W(P)`.
* `SectionFourSetup.t_mem_centralizer`, `SectionFourSetup.t_mem_primeComplementResidual`
  — `t ∈ U`, which is what lets §4 use the *same* involution inside `U`.
* `Hypothesis.theoremAInductionBelow_centralizerActionQuotient` — the induction
  hypothesis passes to the faithful centralizer quotient, so §2/§3 can be run there.
* `exists_pow_sq_eq_one_of_odd_kernel`, `exists_sq_eq_one_of_odd_kernel`,
  `map_involutionSet_eq_of_odd_kernel` — involutions lift through an odd-order normal
  subgroup, so the involution set of `H` maps *onto* that of `H̄`.  Since `Q₀` is the
  derived subgroup `{x | x² = 1 ∧ x ∈ H}`, this is the `Q₀`-analogue of
  `centralizerQQuotientEquiv` at the set level.
* `Hypothesis.centralizerQ0QuotientEquiv` — the resulting `C_{Q₀}(X) ≃ Q̄₀`, together
  with the order transports `natCard_quotient_Q0_eq`, `natCard_quotient_Q_eq`,
  `natCard_quotient_Q0_eq_pow`, `natCard_quotient_Q_eq_Q0_cube` and the property
  transport `isSuzuki2Group_quotient_Q`.  These are what turn the `CentralizerPSUData`
  facts about `C_Q(X)`, `C_{Q₀}(X)` into the hypotheses `exists_standardModel`,
  `lemmaFiveSetup_of_orderThree_of_mem_W` and
  `nonempty_quotientFieldModel_of_orderThree` take about `Q̄`, `Q̄₀`.
* `Hypothesis.exists_center_Q_ne_one` — the `x₀ ∈ Z(Q)`, `x₀ ≠ 1` of
  `exists_standardModel`.
* `Hypothesis.psu3Numerics_and_standingData_centralizerQuotient` — step (2)'s
  prerequisite in one piece: the `PSU(3, 2ⁿ)` numerics *and* both standing bundles
  (`LemmaFiveSetup`, `QuotientFieldModel`) for the centralizer quotient, from the branch
  data of Ch. I §3 Proposition 1(c).  Its one remaining input is `W̄ ≠ 1`.
* `Hypothesis.W_ne_bot_of_psu3_branch` — `W ≠ 1` throughout §4, because Ch. III §1's
  Proposition (p. 117) makes the `PSU(3, ℓ)` branch incompatible with `W = 1`.
* `Hypothesis.W_eq_inf_centralizer_Q0`, `Hypothesis.V_eq_W_iff_le_centralizer_Q0` —
  the hypothesis `V = W` that every §3 endpoint carries is exactly "`V` centralizes
  `Q₀`", which is how step (2) reads it off the structure of `PSU(3, ℓ)`.
* `Hypothesis.mem_centralizer_of_qv_decomposition`, `Hypothesis.D_le_normalizer_W` —
  the two group-theoretic ingredients of step (2)'s `ζ`: the `Q V`-decomposition of
  `C_H(s)` is unique, so both factors of `x = q v` inherit `x`'s centralizing property;
  and `P ≤ D` normalizes `W`, so `P ⊔ W = P · W`.
* `SectionFourSetup.exists_ne_one_mem_W_centralizer` — **`C_W(P) ≠ 1`**, the book's
  `|(V ∩ U)/(P ∩ U)| = (ℓ+1)/(ℓ+1,3) ≠ 1` in the form step (2) uses it.
* `SectionFourSetup.exists_ne_one_mem_quotient_W` — that `ζ` stays non-trivial in the
  quotient, because the kernel centralizes all of `C_Q(P)` while `W` is fixed-point-free
  on `Q/Q₀`.
* `SectionFourSetup.standingData_centralizerQuotient` — **§2/§3 run inside the
  centralizer quotient on §4's ambient hypotheses alone**: both standing bundles and the
  numerics of `exists_standardModel`, with no residual hypothesis about the quotient.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

include hyp in
/-- **The involutions of `Q` lie in `Q₀`.**

`Q` is a Suzuki `2`-group, so every involution of `Q` is central — Higman's easy
inclusion (`OddOrder.Higman.Suzuki2Groups.involutions_subset_center`, Peterfalvi
Appendix III (a), p. 141) — and `Z(Q) = Q₀`.  So an element of `Q − Q₀` squares to
something nontrivial, which is the "exponent 4" of Ch. IV §4, step (1). -/
theorem sq_ne_one_of_not_mem_Q0
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥hyp.Q)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {x : G} (hxQ : x ∈ hyp.Q) (hx0 : x ∉ hyp.Q0) :
    x ^ 2 ≠ 1 := by
  intro hsq
  refine hx0 ?_
  have hx1 : (⟨x, hxQ⟩ : ↥hyp.Q) ≠ 1 := by
    intro hc
    refine hx0 ?_
    rw [show x = 1 from congrArg (Subtype.val (p := fun y => y ∈ hyp.Q)) hc]
    exact hyp.Q0.one_mem
  have hsq' : (⟨x, hxQ⟩ : ↥hyp.Q) ^ 2 = 1 := Subtype.ext (by simpa using hsq)
  have hmem : (⟨x, hxQ⟩ : ↥hyp.Q) ∈ Subgroup.center hyp.Q :=
    OddOrder.Higman.Suzuki2Groups.involutions_subset_center hQsuz ⟨hsq', hx1⟩
  rw [hZ, Subgroup.mem_subgroupOf] at hmem
  exact hmem

include hyp in
/-- **`C_Q(X)` is not elementary abelian once it meets `Q − Q₀`.**

This is the discriminator that excludes the `PSL(2, ℓ)` branch of Ch. I §3 Proposition
1(c) in Ch. IV §4, step (1) (p. 132), and it is exactly the hypothesis
`nonempty_psu3Data_of_orderOf_eq_three` asks for. -/
theorem not_isElementaryAbelian_cQ_of_not_mem_Q0
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥hyp.Q)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {X : Subgroup G} {x : G} (hxQ : x ∈ hyp.Q) (hx0 : x ∉ hyp.Q0)
    (hxC : x ∈ Subgroup.centralizer (X : Set G)) :
    ¬ OddOrder.GroupTheory.IsElementaryAbelian 2
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) := by
  intro hea
  refine hyp.sq_ne_one_of_not_mem_Q0 hQsuz hZ hxQ hx0 ?_
  have hpt : (⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.mpr hxQ⟩ :
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))) ^ 2 = 1 := hea.2 _
  have := congrArg
    (fun z : ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =>
      ((z : ↥(Subgroup.centralizer (X : Set G))) : G)) hpt
  simpa using this

/-! ### The conjugation action of `D` on `Q`

Ch. IV §4's `P` lies in `V ≤ D`, and the Glauberman step of step (1) needs `P` acting on
`Q` with the `P`-invariant normal subgroup `Q₀`.  `conjQByK` and `conjQByW` are the same
construction for `K` and `W`; this is the version covering all of `D`. -/

/-- **Conjugation by `D` on `Q`** — `D ≤ H` and `Q ⊴ H`. -/
def conjQByD : ↥hyp.D →* MulAut ↥hyp.Q where
  toFun d :=
    { toFun := fun x => ⟨(d : G) * x * (d : G)⁻¹,
        hyp.Q_normal_in_H d (hyp.D_le_H d.2) x x.2⟩
      invFun := fun x => ⟨(d : G)⁻¹ * x * (d : G), by
        simpa using hyp.Q_normal_in_H (d : G)⁻¹
          (inv_mem (hyp.D_le_H d.2)) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by
        change (d : G) * ((x : G) * (y : G)) * (d : G)⁻¹ =
          ((d : G) * x * (d : G)⁻¹) * ((d : G) * y * (d : G)⁻¹)
        group) }
  map_one' := by
    ext x
    change ((1 : ↥hyp.D) : G) * (x : G) * ((1 : ↥hyp.D) : G)⁻¹ = (x : G)
    simp
  map_mul' d e := by
    ext x
    change (((d : G) * (e : G)) * (x : G) * (((d : G) * (e : G))⁻¹)) =
      (d : G) * ((e : G) * (x : G) * (e : G)⁻¹) * (d : G)⁻¹
    group

@[simp] theorem conjQByD_apply_val (d : ↥hyp.D) (x : ↥hyp.Q) :
    ((hyp.conjQByD d x : ↥hyp.Q) : G) = (d : G) * (x : G) * (d : G)⁻¹ := rfl

include hyp in
/-- **`Q₀` is `D`-invariant inside `Q`** — the normal subgroup along which step (1)'s
Glauberman argument reduces. -/
theorem isAInvariant_conjQByD_Q0 :
    OddOrder.Isaacs.Ch03.IsAInvariant hyp.conjQByD (hyp.Q0.subgroupOf hyp.Q) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro d x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact hyp.conj_mem_Q0_of_mem_D d.2 hx

include hyp in
/-- **Glauberman's step in Ch. IV §4, step (1)**: a nontrivial `P`-fixed class of
`Q/Q₀` has a `P`-fixed representative, which then lies outside `Q₀`.

The book assumes `C_{Q/Q₀}(P) ≠ 1` (spelled out here as an `x ∈ Q − Q₀` whose class is
`P`-fixed) and immediately works with `C_Q(P)`.  The passage from the quotient down to
`Q` is the coprime fixed-point lemma — Isaacs Cor 3.28, here through
`map_fixedSubgroup_eq_fixedSubgroup_quotient` — available because `|P|` is odd and `Q` is
a `2`-group.

Together with `not_isElementaryAbelian_cQ_of_not_mem_Q0` this supplies the exponent
discriminator of step (1) from the section's standing hypothesis. -/
theorem exists_fixed_not_mem_Q0
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {P : Subgroup G} (hPD : P ≤ hyp.D)
    (hCop : Nat.Coprime (Nat.card ↥(P.subgroupOf hyp.D)) (Nat.card ↥hyp.Q))
    (hSolv : IsSolvable ↥hyp.Q)
    {x : G} (hxQ : x ∈ hyp.Q) (hx0 : x ∉ hyp.Q0)
    (hxfix : ∀ a ∈ P, a * x * a⁻¹ * x⁻¹ ∈ hyp.Q0) :
    ∃ y : G, y ∈ hyp.Q ∧ y ∉ hyp.Q0 ∧ ∀ a ∈ P, a * y * a⁻¹ = y := by
  classical
  haveI hNnormal : (hyp.Q0.subgroupOf hyp.Q).Normal := by rw [← hZ]; infer_instance
  have hinv := hyp.isAInvariant_conjQByD_Q0
  have hkey := OddOrder.GroupTheory.map_fixedSubgroup_eq_fixedSubgroup_quotient
    (φ := hyp.conjQByD) (X := P.subgroupOf hyp.D) hinv hCop (Or.inr hSolv)
  -- the class of `x` is `P`-fixed
  have hclass : (QuotientGroup.mk' (hyp.Q0.subgroupOf hyp.Q) ⟨x, hxQ⟩) ∈
      OddOrder.GroupTheory.fixedSubgroup
        (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hinv)
        (P.subgroupOf hyp.D) := by
    intro d hd
    rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk' hinv,
      QuotientGroup.mk'_eq_mk']
    have hdP : (d : G) ∈ P := Subgroup.mem_subgroupOf.mp hd
    have hu : (d : G) * x * (d : G)⁻¹ * x⁻¹ ∈ hyp.Q0 := hxfix _ hdP
    have huQ : (d : G) * x * (d : G)⁻¹ * x⁻¹ ∈ hyp.Q :=
      hyp.Q.mul_mem (hyp.Q_normal_in_H d (hyp.D_le_H d.2) x hxQ) (hyp.Q.inv_mem hxQ)
    refine ⟨(⟨(d : G) * x * (d : G)⁻¹ * x⁻¹, huQ⟩ : ↥hyp.Q)⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hyp.Q0.inv_mem hu
    · have hcent : (⟨(d : G) * x * (d : G)⁻¹ * x⁻¹, huQ⟩ : ↥hyp.Q)
          ∈ Subgroup.center hyp.Q := by
        rw [hZ, Subgroup.mem_subgroupOf]; exact hu
      have hcommG : ((d : G) * x * (d : G)⁻¹ * x⁻¹) * x
          = x * ((d : G) * x * (d : G)⁻¹ * x⁻¹) := by
        have hc := Subgroup.mem_center_iff.mp hcent (⟨x, hxQ⟩ : ↥hyp.Q)
        simpa using congrArg (Subtype.val (p := fun z => z ∈ hyp.Q)) hc.symm
      refine Subtype.ext ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hyp.conjQByD_apply_val]
      set u : G := (d : G) * x * (d : G)⁻¹ * x⁻¹ with hudef
      have h1 : (d : G) * x * (d : G)⁻¹ = u * x := by rw [hudef]; group
      rw [h1, hcommG]
      group
  rw [← hkey] at hclass
  obtain ⟨c, hcfix, hceq⟩ := hclass
  refine ⟨(c : G), c.2, ?_, ?_⟩
  · -- `c` and `x` have the same class, and `x ∉ Q₀`
    intro hc0
    refine hx0 ?_
    have hmem : c⁻¹ * (⟨x, hxQ⟩ : ↥hyp.Q) ∈ hyp.Q0.subgroupOf hyp.Q := by
      have hq := hceq
      rwa [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hq
    rw [Subgroup.mem_subgroupOf] at hmem
    have hcQ0 : (c : G) ∈ hyp.Q0 := hc0
    have : x = (c : G) * ((c : G)⁻¹ * x) := by group
    rw [this]
    exact hyp.Q0.mul_mem hcQ0 hmem
  · intro a haP
    have hfix := hcfix ⟨a, hPD haP⟩ (Subgroup.mem_subgroupOf.mpr haP)
    exact congrArg (Subtype.val (p := fun z => z ∈ hyp.Q)) hfix

/-! ### `Z(U) ⊆ P`

Peterfalvi Part II, Ch. IV §4, step (1) (p. 132) closes with

> As `Z(U) ⊂ C_V(C_{Q₀}(P))`, `Z(U) ⊂ P W` by the theorem of Galois.  Since `P Z(U)`
> centralizes `C_Q(P) ⊄ Q₀`, `P Z(U) ∩ W = 1` and so `Z(U) ⊂ P`.

The Galois inclusion is `centralizer_V_centralizer_Q0`; the two steps below are the rest.
-/

include hyp in
/-- **A subgroup centralizing an element of `Q − Q₀` meets `W` trivially.**

`W` acts fixed-point-freely on `(Q/Q₀)^#` (`eq_one_of_conj_eq_mul_Q0_of_mem_W`) — and
that version needs no `V = W`, which is what makes it available in Ch. IV §4. -/
theorem inf_W_eq_bot_of_centralizes {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu)
    {S : Subgroup G} {y : G} (hyQ : y ∈ hyp.Q) (hy0 : y ∉ hyp.Q0)
    (hS : ∀ c ∈ S, c * y = y * c) :
    S ⊓ hyp.W = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  refine Subgroup.mem_bot.mpr ?_
  refine hyp.eq_one_of_conj_eq_mul_Q0_of_mem_W M hZ hmu hyQ hy0 hc.2 hyp.Q0.one_mem ?_
  rw [mul_one]
  have hcy := hS c hc.1
  calc c⁻¹ * y * c = c⁻¹ * (y * c) := by group
    _ = c⁻¹ * (c * y) := by rw [← hcy]
    _ = y := by group

omit [Finite G] in
/-- **Dedekind's step**: a subgroup whose elements factor as `P W` and which meets `W`
trivially is `P` itself.

This is how step (1) gets from `Z(U) ⊆ P W` and `P Z(U) ∩ W = 1` to `Z(U) ⊆ P`: apply
it to `S = P ⊔ Z(U)`.  Writing `s = p w` with `p ∈ P ≤ S` puts `w = p⁻¹ s` in `S ⊓ W`,
hence `w = 1`.

The factorization is taken as a hypothesis rather than derived from `S ≤ P ⊔ W`: the
subgroup lattice of a group is *not* modular in general, and what makes `P ⊔ W = P W`
here is that `W` is normal in `V`. -/
theorem eq_of_mem_mul_of_inf_eq_bot {P W S : Subgroup G} (hPS : P ≤ S)
    (hfac : ∀ s ∈ S, ∃ p ∈ P, ∃ w ∈ W, s = p * w)
    (hbot : S ⊓ W = ⊥) : S = P := by
  refine le_antisymm (fun s hs => ?_) hPS
  obtain ⟨p, hp, w, hw, rfl⟩ := hfac s hs
  have hwS : w ∈ S := by
    have hrw : w = p⁻¹ * (p * w) := by group
    rw [hrw]
    exact S.mul_mem (S.inv_mem (hPS hp)) hs
  have hw1 : w = 1 := Subgroup.mem_bot.mp (hbot ▸ ⟨hwS, hw⟩)
  rw [hw1, mul_one]
  exact hp

/-- **The induction hypothesis is inherited by the faithful centralizer quotient.**

`TheoremAInductionBelow G Ω` quantifies over *all* groups smaller than `G`, and the
quotient is smaller than `G` (`card_centralizerActionQuotient_lt`); so anything smaller
than the quotient is smaller than `G`.

Ch. IV §4 needs this to run §2/§3 inside the quotient, which is where the mappings
`f₁, h₁` of step (2) (p. 133) live. -/
theorem theoremAInductionBelow_centralizerActionQuotient {X : Subgroup G}
    (hXV : X ≤ hyp.V) (hX : X ≠ ⊥) (ih : TheoremAInductionBelow G Ω) :
    letI := hyp.centralizerQuotientMulAction hXV
    TheoremAInductionBelow (hyp.centralizerActionQuotient X)
      ↥(MulAction.fixedPoints X Ω) := by
  letI := hyp.centralizerQuotientMulAction hXV
  intro A Λ _ _ _ hlt hA
  exact ih (hlt.trans (hyp.card_centralizerActionQuotient_lt hXV hX)) hA

/-- **The induction hypothesis passes to any smaller-or-equal group.**

`TheoremAInductionBelow` quantifies over everything strictly below `Nat.card G`, so it
restricts to any group of at most that order — in whatever universe `B` and `Λ'` are
allowed by the statement.  This is how Ch. IV §4 feeds the ambient induction hypothesis
to the model it identifies `U/(P ∩ U)` with. -/
theorem TheoremAInductionBelow.of_natCard_le {B : Type u} {Λ' : Type v} [Group B]
    [MulAction B Λ'] [Finite B] (ih : TheoremAInductionBelow G Ω)
    (hle : Nat.card B ≤ Nat.card G) : TheoremAInductionBelow B Λ' := by
  intro A Λ'' _ _ _ hlt hA
  exact ih (hlt.trans_le hle) hA

/-- **`|U/Z(U)| < |G|`** for `U = O^{2′}(C_G(X))` and `1 ≠ X ≤ V`.

`U/Z(U)` is a quotient of a subgroup of `C_G(X)`, which is proper by
`natCard_centralizer_lt`. -/
theorem natCard_residualQuotient_lt {X : Subgroup G} (hXV : X ≤ hyp.V) (hX : X ≠ ⊥) :
    Nat.card (↥(Subgroup.primeComplementResidual 2 (Subgroup.centralizer (X : Set G))) ⧸
        Subgroup.center
          ↥(Subgroup.primeComplementResidual 2 (Subgroup.centralizer (X : Set G))))
      < Nat.card G := by
  classical
  have h1 : Nat.card (↥(Subgroup.primeComplementResidual 2
        (Subgroup.centralizer (X : Set G))) ⧸ Subgroup.center _)
      ≤ Nat.card ↥(Subgroup.primeComplementResidual 2
        (Subgroup.centralizer (X : Set G))) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card ↥(Subgroup.primeComplementResidual 2
        (Subgroup.centralizer (X : Set G)))
      ≤ Nat.card ↥(Subgroup.centralizer (X : Set G)) :=
    Nat.le_of_dvd Nat.card_pos
      (Subgroup.card_subgroup_dvd_card
        (Subgroup.primeComplementResidual 2 (Subgroup.centralizer (X : Set G))))
  exact lt_of_le_of_lt (h1.trans h2) (hyp.natCard_centralizer_lt hXV hX)

/-! ### Involutions lift through an odd-order kernel

The `Q₀`-analogue of `centralizerQQuotientEquiv` needs more than the `Q`-version: `Q₀` is
the *derived* subgroup `{x | x² = 1 ∧ x ∈ H}`, so surjectivity onto `Q̄₀` asks for a
preimage that is again an involution.  That is exactly the statement below, and it holds
because the kernel `𝒩(C_G(X)) ≤ C_D(X)` has odd order (`Hypothesis.D_odd`).
-/

/-- **An involution of `L/N` lifts to an involution of `L` when `|N|` is odd.**

Pick any preimage `x`.  Then `x² ∈ N`, so `d := orderOf (x²)` divides `|N|` and is odd;
`y := x^d` satisfies `y² = (x²)^d = 1`, and `ȳ = x̄^d = x̄` because `x̄² = 1` and `d` is
odd. -/
theorem exists_pow_sq_eq_one_of_odd_kernel {L : Type*} [Group L] [Finite L]
    {N : Subgroup L} [N.Normal] (hN : Odd (Nat.card ↥N)) {x : L}
    (h2 : (QuotientGroup.mk' N x) ^ 2 = 1) :
    ∃ d : ℕ, (x ^ d) ^ 2 = 1 ∧
      QuotientGroup.mk' N (x ^ d) = QuotientGroup.mk' N x := by
  classical
  have hx2N : x ^ 2 ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using h2
  have hdvd : orderOf (⟨x ^ 2, hx2N⟩ : ↥N) ∣ Nat.card ↥N := orderOf_dvd_natCard _
  obtain ⟨c, hc⟩ := hdvd
  rw [hc] at hN
  have hdodd : Odd (orderOf (⟨x ^ 2, hx2N⟩ : ↥N)) := (Nat.odd_mul.mp hN).1
  have hsq : (x ^ 2) ^ orderOf (⟨x ^ 2, hx2N⟩ : ↥N) = 1 :=
    congrArg (Subtype.val (p := fun w => w ∈ N))
      (pow_orderOf_eq_one (⟨x ^ 2, hx2N⟩ : ↥N))
  refine ⟨orderOf (⟨x ^ 2, hx2N⟩ : ↥N), ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]
    exact hsq
  · obtain ⟨k, hk⟩ := hdodd
    rw [hk, map_pow, pow_add, pow_mul, h2, one_pow, one_mul, pow_one]

/-- **An involution of `L/N` lifts to an involution of `L` when `|N|` is odd** — the
preimage-free form of `exists_pow_sq_eq_one_of_odd_kernel`. -/
theorem exists_sq_eq_one_of_odd_kernel {L : Type*} [Group L] [Finite L]
    {N : Subgroup L} [N.Normal] (hN : Odd (Nat.card ↥N)) {z : L ⧸ N} (h2 : z ^ 2 = 1) :
    ∃ y : L, y ^ 2 = 1 ∧ QuotientGroup.mk' N y = z := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
  obtain ⟨d, hd1, hd2⟩ := exists_pow_sq_eq_one_of_odd_kernel hN h2
  exact ⟨x ^ d, hd1, hd2⟩

/-- **The involutions of `H` map onto the involutions of `H̄`** when the kernel `N ≤ H`
has odd order.

This is `Q₀ ↦ Q̄₀` at the set level: `Q₀ = {x | x² = 1 ∧ x ∈ H}` is a *derived*
subgroup, so the `Q₀`-analogue of `centralizerQQuotientEquiv` reduces to this.  `⊆` is
immediate; `⊇` picks a preimage *inside `H`* and replaces it by an odd power
(`exists_pow_sq_eq_one_of_odd_kernel`), which stays in `H`. -/
theorem map_involutionSet_eq_of_odd_kernel {L : Type*} [Group L] [Finite L]
    {N H : Subgroup L} [N.Normal] (hN : Odd (Nat.card ↥N)) :
    (QuotientGroup.mk' N) '' {x : L | x ^ 2 = 1 ∧ x ∈ H}
      = {z : L ⧸ N | z ^ 2 = 1 ∧ z ∈ H.map (QuotientGroup.mk' N)} := by
  ext z
  constructor
  · rintro ⟨x, ⟨hx2, hxH⟩, rfl⟩
    exact ⟨by rw [← map_pow, hx2, map_one], Subgroup.mem_map_of_mem _ hxH⟩
  · rintro ⟨hz2, hzH⟩
    obtain ⟨x, hxH, rfl⟩ := hzH
    obtain ⟨d, hd1, hd2⟩ := exists_pow_sq_eq_one_of_odd_kernel hN hz2
    exact ⟨x ^ d, ⟨hd1, H.pow_mem hxH d⟩, hd2⟩

/-- `C_{Q₀}(X)` is the involution subgroup of `C_H(X)`, i.e. the shape
`map_involutionSet_eq_of_odd_kernel` consumes. -/
theorem coe_Q0_subgroupOf_centralizer (X : Subgroup G) :
    ((hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G)) :
        Subgroup ↥(Subgroup.centralizer (X : Set G))) :
        Set ↥(Subgroup.centralizer (X : Set G)))
      = {x : ↥(Subgroup.centralizer (X : Set G)) |
          x ^ 2 = 1 ∧ x ∈ hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))} := by
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_subgroupOf, hyp.mem_Q0_iff,
    Subtype.ext_iff, Subgroup.coe_pow, Subgroup.coe_one]

/-- **Peterfalvi Part II, Ch. I §3 Proposition 1(c), `Q₀`-version.**
The quotient map carries `C_{Q₀}(X)` *onto* `Q̄₀`.

Unlike the `Q`-version (`centralizerQQuotientEquiv`, where surjectivity is automatic
because `Q̄` is *defined* as the image of `C_Q(X)`), `Q₀` is the **derived** subgroup
`{x | x² = 1 ∧ x ∈ H}`, so `Q̄₀` is the involution subgroup of `H̄` rather than the image
of `C_{Q₀}(X)`.  Surjectivity is therefore a genuine lifting statement, supplied by
`map_involutionSet_eq_of_odd_kernel`: the kernel `𝒩(C_G(X))` lies in `C_D(X)` and hence
has odd order, so an involution of the quotient has an involution as preimage — and the
preimage can be taken inside `C_H(X)`. -/
theorem map_centralizer_Q0_eq_quotient_Q0 {X : Subgroup G} (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    letI := hyp.centralizerQuotientMulAction hXV
    (hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))).map
        (QuotientGroup.mk'
          (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore)
      = (hyp.centralizerQuotientHypothesis hXV hA3).Q0 := by
  letI := hyp.centralizerQuotientMulAction hXV
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let N : Subgroup ↥L := (hyp.H.subgroupOf L).normalCore
  let pi : ↥L →* ↥L ⧸ N := QuotientGroup.mk' N
  have hNleD : N ≤ hyp.D.subgroupOf L := by
    dsimp only [N, L]
    rw [hyp.normalCore_cH_eq_centralizer_cQ hXV]
    exact inf_le_left
  have hNodd : Odd (Nat.card ↥N) :=
    ((hyp.centralizerHypothesisA1 hXV).D_odd).of_dvd_nat
      (Subgroup.card_dvd_of_le hNleD)
  have hH : (hyp.centralizerQuotientHypothesis hXV hA3).H
      = (hyp.H.subgroupOf L).map pi := rfl
  refine SetLike.ext' ?_
  rw [Subgroup.coe_map, hyp.coe_Q0_subgroupOf_centralizer X,
    map_involutionSet_eq_of_odd_kernel (N := N) (H := hyp.H.subgroupOf L) hNodd]
  ext z
  simp only [Set.mem_setOf_eq, SetLike.mem_coe,
    (hyp.centralizerQuotientHypothesis hXV hA3).mem_Q0_iff, hH, pi]

/-- **Peterfalvi Part II, Ch. I §3 Proposition 1(c), `Q₀`-version** — the explicit
source equivalence `C_{Q₀}(X) ≃ Q̄₀`.

Injectivity is the `Q`-version's argument restricted along `Q₀ ≤ Q`
(`𝒩(C_G(X)) ≤ C_D(X)` and `C_Q(X) ∩ C_D(X) = 1`); surjectivity is
`map_centralizer_Q0_eq_quotient_Q0`. -/
noncomputable def centralizerQ0QuotientEquiv {X : Subgroup G} (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    letI := hyp.centralizerQuotientMulAction hXV
    ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) ≃*
      ↥(hyp.centralizerQuotientHypothesis hXV hA3).Q0 := by
  letI := hyp.centralizerQuotientMulAction hXV
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let N : Subgroup ↥L := (hyp.H.subgroupOf L).normalCore
  let Q0_L : Subgroup ↥L := hyp.Q0.subgroupOf L
  let pi : ↥L →* ↥L ⧸ N := QuotientGroup.mk' N
  have hNleD : N ≤ hyp.D.subgroupOf L := by
    dsimp only [N, L]
    rw [hyp.normalCore_cH_eq_centralizer_cQ hXV]
    exact inf_le_left
  have hQD : hyp.Q.subgroupOf L ⊓ hyp.D.subgroupOf L = ⊥ :=
    (hyp.centralizerHypothesisA1 hXV).Q_inf_D_eq_bot
  have hinj : Function.Injective (pi.subgroupMap Q0_L) := by
    intro q r hqr
    have hqr' : pi (q : ↥L) = pi (r : ↥L) := congrArg Subtype.val hqr
    have hquot : pi ((q : ↥L) * (r : ↥L)⁻¹) = 1 := by
      rw [map_mul, map_inv, hqr', mul_inv_cancel]
    have hmemN : (q : ↥L) * (r : ↥L)⁻¹ ∈ N :=
      (QuotientGroup.eq_one_iff _).mp hquot
    have hmemQ : (q : ↥L) * (r : ↥L)⁻¹ ∈ hyp.Q.subgroupOf L :=
      Subgroup.mem_subgroupOf.mpr
        (hyp.Q0_le_Q (Subgroup.mem_subgroupOf.mp
          (Q0_L.mul_mem q.2 (Q0_L.inv_mem r.2))))
    have hbot : (q : ↥L) * (r : ↥L)⁻¹ ∈
        hyp.Q.subgroupOf L ⊓ hyp.D.subgroupOf L :=
      ⟨hmemQ, hNleD hmemN⟩
    rw [hQD, Subgroup.mem_bot] at hbot
    exact Subtype.ext (mul_inv_eq_one.mp hbot)
  exact (MulEquiv.ofBijective (pi.subgroupMap Q0_L)
      ⟨hinj, pi.subgroupMap_surjective Q0_L⟩).trans
    (MulEquiv.subgroupCongr (hyp.map_centralizer_Q0_eq_quotient_Q0 hXV hA3))

/-- **`|Q̄₀| = |C_{Q₀}(X)|`** — the order transport `exists_standardModel` needs for the
quotient hypothesis, from `centralizerQ0QuotientEquiv`. -/
theorem natCard_quotient_Q0_eq {X : Subgroup G} (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    letI := hyp.centralizerQuotientMulAction hXV
    Nat.card ↥(hyp.centralizerQuotientHypothesis hXV hA3).Q0
      = Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) := by
  letI := hyp.centralizerQuotientMulAction hXV
  exact Nat.card_congr (hyp.centralizerQ0QuotientEquiv hXV hA3).symm.toEquiv

/-- **`|Q̄| = |C_Q(X)|`** — the `Q`-version of `natCard_quotient_Q0_eq`, from
`centralizerQQuotientEquiv`. -/
theorem natCard_quotient_Q_eq {X : Subgroup G} (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    letI := hyp.centralizerQuotientMulAction hXV
    Nat.card ↥(hyp.centralizerQuotientHypothesis hXV hA3).Q
      = Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) := by
  letI := hyp.centralizerQuotientMulAction hXV
  exact Nat.card_congr (hyp.centralizerQQuotientEquiv hXV).symm.toEquiv

/-! ### The order hypotheses of `exists_standardModel` for the centralizer quotient

`CentralizerPSUData` states its two order facts about `C_Q(X)` and `C_{Q₀}(X)`
(`natCard_cQ0_eq_baseField`, `natCard_cQ_eq_cQ0_cube`), while
`exists_standardModel` wants them about `Q̄` and `Q̄₀`.  The two transports above turn
one into the other. -/

/-- **`|Q̄₀| = 2ⁿ`** — `exists_standardModel`'s `hQ0card` for the centralizer quotient.
The input is `CentralizerPSUData.natCard_cQ0_eq_baseField` combined with
`|BaseField n| = 2ⁿ`. -/
theorem natCard_quotient_Q0_eq_pow {X : Subgroup G} (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    {n : ℕ} (hQ0 : Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G)))
      = 2 ^ n) :
    letI := hyp.centralizerQuotientMulAction hXV
    Nat.card ↥(hyp.centralizerQuotientHypothesis hXV hA3).Q0 = 2 ^ n := by
  letI := hyp.centralizerQuotientMulAction hXV
  rw [hyp.natCard_quotient_Q0_eq hXV hA3, hQ0]

/-- **`|Q̄| = |Q̄₀|³`** — `exists_standardModel`'s `hcardQ` for the centralizer quotient,
transported from `CentralizerPSUData.natCard_cQ_eq_cQ0_cube`. -/
theorem natCard_quotient_Q_eq_Q0_cube {X : Subgroup G} (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (hcube : Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))
      = Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) ^ 3) :
    letI := hyp.centralizerQuotientMulAction hXV
    Nat.card ↥(hyp.centralizerQuotientHypothesis hXV hA3).Q
      = Nat.card ↥(hyp.centralizerQuotientHypothesis hXV hA3).Q0 ^ 3 := by
  letI := hyp.centralizerQuotientMulAction hXV
  rw [hyp.natCard_quotient_Q_eq hXV hA3, hyp.natCard_quotient_Q0_eq hXV hA3, hcube]

/-- **`Q̄` is a Suzuki `2`-group** — transported from
`CentralizerPSUData.cQ_isSuzuki2Group` along `centralizerQQuotientEquiv`.  This is the
`hQsuz` that `lemmaFiveSetup_of_orderThree_of_mem_W` and
`nonempty_quotientFieldModel_of_orderThree` need for the quotient. -/
theorem isSuzuki2Group_quotient_Q {X : Subgroup G} (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))) :
    letI := hyp.centralizerQuotientMulAction hXV
    OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group
      ↥(hyp.centralizerQuotientHypothesis hXV hA3).Q := by
  letI := hyp.centralizerQuotientMulAction hXV
  exact OddOrder.GroupTheory.SpecificGroups.Suzuki.IsSuzuki2Group.of_equiv hQsuz
    (hyp.centralizerQQuotientEquiv hXV)

/-- **`Z(Q) ≠ 1`, in the shape `exists_standardModel` takes it** — a nonidentity element
of `Z(Q)`, packaged from `exists_involution_mem_center_Q`. -/
theorem exists_center_Q_ne_one : ∃ x₀ : ↥(Subgroup.center hyp.Q), x₀ ≠ 1 := by
  obtain ⟨u, huQ, _, hu1, hucomm⟩ := hyp.exists_involution_mem_center_Q
  refine ⟨⟨⟨u, huQ⟩, Subgroup.mem_center_iff.mpr fun v => ?_⟩, ?_⟩
  · exact Subtype.ext (hucomm (v : G) v.2).symm
  · exact fun hone => hu1 (congrArg (Subtype.val ∘ Subtype.val) hone)

/-- **The `PSU(3, 2ⁿ)` numerics and the §2/§3 standing data, for the centralizer
quotient** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133).

> If `f₁` and `h₁` denote the mappings `f` and `h` relative to `U`, `U ∩ H` and `t`,
> then, by Corollary 2 of the proposition of §3, there is an element
> `ω ∈ (Q − Q₀) ∩ U` such that `f₁(ω) ∈ ω^{-ζ₁}(P ∩ U)` and `h₁(ω) ∈ ζ₁³(P ∩ U)`.

Running §2/§3 there means supplying the data those sections are parametrized by.  This
assembles all of it out of the `PSU(3, ℓ)` branch of Ch. I §3 Proposition 1(c):

* `n ≠ 0`, `|Q̄₀| = 2ⁿ`, `|Q̄| = |Q̄₀|³` — the numerics `exists_standardModel` takes,
  transported from `CentralizerPSUData` by `natCard_quotient_Q0_eq_pow` and
  `natCard_quotient_Q_eq_Q0_cube`;
* `|s̄ t̄| = 3` (`orderOf_distinguishedInvolution_mul_t_of_psu3Target` at the quotient)
  and `Q̄` a Suzuki `2`-group (`isSuzuki2Group_quotient_Q`);
* and, for any `1 ≠ w ∈ W̄`, the two standing bundles themselves —
  `LemmaFiveSetup` (Ch. I §3 Lemma 5) and `QuotientFieldModel` (Ch. III §3).

The one remaining input for step (2) is therefore `W̄ ≠ 1`, which the book reads off the
`PSU(3, ℓ)` structure as `|(V ∩ U)/(P ∩ U)| = (ℓ+1)/(ℓ+1,3) ≠ 1`, using `ℓ > 2`. -/
theorem psu3Numerics_and_standingData_centralizerQuotient {X : Subgroup G}
    (hXV : X ≤ hyp.V) (hX : X ≠ ⊥)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (hord : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hnea : ¬ OddOrder.GroupTheory.IsElementaryAbelian 2
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (ih : TheoremAInductionBelow G Ω) :
    letI := hyp.centralizerQuotientMulAction hXV
    ∃ n : ℕ, n ≠ 0 ∧
      Nat.card ↥(hyp.centralizerQuotientHypothesis hXV hA3).Q0 = 2 ^ n ∧
      Nat.card (hyp.centralizerQuotientHypothesis hXV hA3).Q
        = Nat.card ↥(hyp.centralizerQuotientHypothesis hXV hA3).Q0 ^ 3 ∧
      orderOf ((hyp.centralizerQuotientHypothesis hXV hA3).distinguishedInvolution *
        (hyp.centralizerQuotientHypothesis hXV hA3).t) = 3 ∧
      OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group
        ↥(hyp.centralizerQuotientHypothesis hXV hA3).Q ∧
      ∀ w ∈ (hyp.centralizerQuotientHypothesis hXV hA3).W, w ≠ 1 →
        Nonempty ((hyp.centralizerQuotientHypothesis hXV hA3).LemmaFiveSetup n) ∧
        Nonempty ((hyp.centralizerQuotientHypothesis hXV hA3).QuotientFieldModel n) := by
  letI := hyp.centralizerQuotientMulAction hXV
  set qhyp := hyp.centralizerQuotientHypothesis hXV hA3 with hqhyp
  obtain ⟨tri⟩ := hyp.centralizer_trichotomy_of_induction hXV hX hA3 ih
  obtain ⟨⟨data, _teq, details⟩⟩ :=
    nonempty_psu3Data_of_orderOf_eq_three tri.branch hord hnea
  have hn0 : 0 < data.n := lt_trans Nat.zero_lt_one data.one_lt_n
  have hQ0 : Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G)))
      = 2 ^ data.n :=
    details.natCard_cQ0_eq_baseField.trans
      (OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.natCard_baseField
        data.n hn0)
  have hQ0card : Nat.card ↥qhyp.Q0 = 2 ^ data.n :=
    hyp.natCard_quotient_Q0_eq_pow hXV hA3 hQ0
  have hcardQ : Nat.card qhyp.Q = Nat.card ↥qhyp.Q0 ^ 3 :=
    hyp.natCard_quotient_Q_eq_Q0_cube hXV hA3 details.natCard_cQ_eq_cQ0_cube
  have hst : orderOf (qhyp.distinguishedInvolution * qhyp.t) = 3 :=
    orderOf_distinguishedInvolution_mul_t_of_psu3Target qhyp tri.result.L
      tri.result.normal tri.result.oddIndex data
  have hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥qhyp.Q :=
    hyp.isSuzuki2Group_quotient_Q hXV hA3 details.cQ_isSuzuki2Group
  have ihq : TheoremAInductionBelow (hyp.centralizerActionQuotient X)
      ↥(MulAction.fixedPoints X Ω) :=
    hyp.theoremAInductionBelow_centralizerActionQuotient hXV hX ih
  refine ⟨data.n, hn0.ne', hQ0card, hcardQ, hst, hQsuz, fun w hw hw1 => ?_⟩
  obtain ⟨sfive⟩ := qhyp.lemmaFiveSetup_of_orderThree_of_mem_W hw hw1 hst hQsuz
    hn0.ne' hQ0card hcardQ ihq
  exact ⟨⟨sfive⟩, qhyp.nonempty_quotientFieldModel_of_orderThree hst hQsuz hn0.ne'
    hQ0card hcardQ ihq sfive hw hw1⟩

/-- **`W ≠ 1` in Ch. IV §4.**

Ch. III §1 Proposition (p. 117) — `CentralizerPSUData.false_of_W_eq_bot`, "it follows
that `F/Z(F)` is not isomorphic to `PSU(3, ℓ)`" — says the `PSU(3, ℓ)` branch of Ch. I §3
Proposition 1(c) is incompatible with `W = 1`.  Step (1) of §4 puts us in exactly that
branch, so `W ≠ 1` throughout §4.  This is the ambient half of the book's
`|(V ∩ U)/(P ∩ U)| ≠ 1` (p. 133). -/
theorem W_ne_bot_of_psu3_branch {X : Subgroup G} (hXV : X ≤ hyp.V) (hX : X ≠ ⊥)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (hord : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hnea : ¬ OddOrder.GroupTheory.IsElementaryAbelian 2
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (ih : TheoremAInductionBelow G Ω) :
    hyp.W ≠ ⊥ := by
  intro hW
  letI := hyp.centralizerQuotientMulAction hXV
  obtain ⟨tri⟩ := hyp.centralizer_trichotomy_of_induction hXV hX hA3 ih
  obtain ⟨⟨data, _teq, details⟩⟩ :=
    nonempty_psu3Data_of_orderOf_eq_three tri.branch hord hnea
  exact details.false_of_W_eq_bot hXV hW tri.common

/-- **Both factors of `x = q v` inherit `x`'s centralizing property**, for `X ≤ V`.

`C_H(s) = Q V` with `Q ∩ V ≤ Q ∩ D = 1`, so the decomposition is unique.  An `a ∈ X`
lies in `V`, hence normalizes `Q` (it lies in `H`) and normalizes `V` (it centralizes
`t`, and `V = C_D(t)`); conjugating `x = q v` by `a` therefore produces a second
decomposition of `x`, which uniqueness identifies with the first. -/
theorem mem_centralizer_of_qv_decomposition {X : Subgroup G} (hXV : X ≤ hyp.V)
    {x q v : G} (hqQ : q ∈ hyp.Q) (hvV : v ∈ hyp.V) (hx : x = q * v)
    (hxC : x ∈ Subgroup.centralizer (X : Set G)) :
    q ∈ Subgroup.centralizer (X : Set G) ∧ v ∈ Subgroup.centralizer (X : Set G) := by
  have key : ∀ a ∈ X, a * q * a⁻¹ = q ∧ a * v * a⁻¹ = v := by
    intro a ha
    have haV : a ∈ hyp.V := hXV ha
    have haD : a ∈ hyp.D := hyp.V_le_D haV
    have haH : a ∈ hyp.H := hyp.D_le_H haD
    have haq : a * q * a⁻¹ ∈ hyp.Q := hyp.Q_normal_in_H a haH q hqQ
    have hav : a * v * a⁻¹ ∈ hyp.V := by
      refine ⟨hyp.D.mul_mem (hyp.D.mul_mem haD (hyp.V_le_D hvV)) (hyp.D.inv_mem haD), ?_⟩
      have hat := hyp.commute_t_of_mem_V haV
      have hvt := hyp.commute_t_of_mem_V hvV
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((hat.mul_left hvt).mul_left hat.inv_left)
    -- conjugating `x = q v` by `a` gives a second decomposition of the same element
    have hconj : (a * q * a⁻¹) * (a * v * a⁻¹) = q * v := by
      have hax : a * x * a⁻¹ = x := by
        have := Subgroup.mem_centralizer_iff.mp hxC a ha
        calc a * x * a⁻¹ = (x * a) * a⁻¹ := by rw [← this]
          _ = x := by group
      calc (a * q * a⁻¹) * (a * v * a⁻¹) = a * (q * v) * a⁻¹ := by group
        _ = a * x * a⁻¹ := by rw [hx]
        _ = x := hax
        _ = q * v := hx
    have hbot : q⁻¹ * (a * q * a⁻¹) ∈ hyp.Q ⊓ hyp.D := by
      refine ⟨hyp.Q.mul_mem (hyp.Q.inv_mem hqQ) haq, ?_⟩
      have heq : q⁻¹ * (a * q * a⁻¹) = v * (a * v * a⁻¹)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq.mpr hconj]
        group
      rw [heq]
      exact hyp.D.mul_mem (hyp.V_le_D hvV) (hyp.D.inv_mem (hyp.V_le_D hav))
    rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hbot
    refine ⟨hbot.symm, ?_⟩
    rw [← hbot] at hconj
    exact mul_left_cancel hconj
  constructor
  · refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    have := (key a ha).1
    calc a * q = (a * q * a⁻¹) * a := by group
      _ = q * a := by rw [this]
  · refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    have := (key a ha).2
    calc a * v = (a * v * a⁻¹) * a := by group
      _ = v * a := by rw [this]

/-- **`D` normalizes `W`**, in the ambient group: `W ⊴ D` (`KCyclic`). -/
theorem D_le_normalizer_W : hyp.D ≤ Subgroup.normalizer hyp.W := by
  have hconj : ∀ a ∈ hyp.D, ∀ n ∈ hyp.W, a * n * a⁻¹ ∈ hyp.W := by
    intro a ha n hn
    have hnD : n ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hn)
    have hmem : (⟨a, ha⟩ : ↥hyp.D) * ⟨n, hnD⟩ * (⟨a, ha⟩ : ↥hyp.D)⁻¹ ∈
        hyp.W.subgroupOf hyp.D :=
      (inferInstance : (hyp.W.subgroupOf hyp.D).Normal).conj_mem _
        (Subgroup.mem_subgroupOf.mpr hn) _
    exact Subgroup.mem_subgroupOf.mp hmem
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => hconj a ha n hn, fun hn => ?_⟩
  have := hconj a⁻¹ (hyp.D.inv_mem ha) _ hn
  simpa [mul_assoc] using this

/-! ### `V = W` is exactly "`V` centralizes `Q₀`"

Every §3 endpoint (`stepFive`, `corollaryTwo_of_stepFour`, …) carries the hypothesis
`V = W`.  Ch. IV §4 step (2) (p. 133) discharges it for `U` in the book's words

> By the structure of `PSU(3, ℓ)`, `(V ∩ U)/(P ∩ U)` centralizes `C_{Q₀}(P)`.

so it is worth having the two phrasings identified once and for all. -/

/-- **`W = D ∩ C(Q₀)`.**  `W_eq_centralizer_involutions_H` states this with the
involutions of `H`; `Q₀` is that set together with `1`, which every element centralizes. -/
theorem W_eq_inf_centralizer_Q0 :
    hyp.W = hyp.D ⊓ Subgroup.centralizer (hyp.Q0 : Set G) := by
  rw [hyp.W_eq_centralizer_involutions_H]
  refine le_antisymm (fun d hd => ?_) (fun d hd => ?_)
  · obtain ⟨hdD, hdc⟩ := Subgroup.mem_inf.mp hd
    refine Subgroup.mem_inf.mpr ⟨hdD, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    obtain ⟨hx2, hxH⟩ := hyp.mem_Q0_iff.mp hx
    rcases eq_or_ne x 1 with rfl | hx1
    · simp
    · exact Subgroup.mem_centralizer_iff.mp hdc x ⟨hx2, hx1, hxH⟩
  · obtain ⟨hdD, hdc⟩ := Subgroup.mem_inf.mp hd
    refine Subgroup.mem_inf.mpr ⟨hdD, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp hdc x (hyp.mem_Q0_iff.mpr ⟨hx.1, hx.2.2⟩)

/-- **`V = W` if and only if `V` centralizes `Q₀`** (Peterfalvi Part II, Ch. IV §4,
step (2), p. 133 — the book's "by the structure of `PSU(3, ℓ)`, `(V ∩ U)/(P ∩ U)`
centralizes `C_{Q₀}(P)`").

`W ≤ V` is free (`W_le_V`), and `W = D ∩ C(Q₀)` with `V ≤ D`, so the only content in
`V = W` is that `V` acts trivially on `Q₀`. -/
theorem V_eq_W_iff_le_centralizer_Q0 :
    hyp.V = hyp.W ↔ hyp.V ≤ Subgroup.centralizer (hyp.Q0 : Set G) := by
  constructor
  · intro hVW
    rw [hVW, hyp.W_eq_inf_centralizer_Q0]
    exact inf_le_right
  · intro hcent
    refine le_antisymm ?_ hyp.W_le_V
    rw [hyp.W_eq_inf_centralizer_Q0]
    exact le_inf hyp.V_le_D hcent

/-! ## The standing hypothesis of §4 -/

/-- **The standing hypothesis of Peterfalvi Part II, Ch. IV §4** (p. 132).

> By the proposition of §2 and Corollary 1 to the proposition of §3, to complete the
> proof of Theorem A, we may assume that `D` has a subgroup `P` of prime order `p` such
> that `C_{Q/Q₀}(P) ≠ 1`.  Since `C_Q(P) ≠ 1`, `P` has three fixed points on `Ω` and so
> is conjugate in `D` to a subgroup of `V`.  We may assume that `P ⊂ V`.  Since `W` acts
> fixed-point-freely on `Q/Q₀`, `P ∩ W = 1`.

The two reductions the book performs before fixing notation — conjugating `P` into `V`,
and `P ∩ W = 1` — are recorded as fields, since they are what the rest of §4 uses.
`C_{Q/Q₀}(P) ≠ 1` is spelled out as a witness `x ∈ Q − Q₀` whose class is `P`-fixed,
which avoids setting up the quotient action just to state it. -/
structure SectionFourSetup (hyp : Hypothesis G Ω) where
  /-- The subgroup of prime order the section works with. -/
  P : Subgroup G
  /-- `P ⊂ V`, after conjugating in `D`. -/
  P_le_V : P ≤ hyp.V
  /-- `P ∩ W = 1`, because `W` is fixed-point-free on `Q/Q₀`. -/
  P_inf_W : P ⊓ hyp.W = ⊥
  /-- The prime `p`. -/
  cardP : ℕ
  prime_cardP : cardP.Prime
  /-- `p` is odd — `D` has odd order. -/
  odd_cardP : Odd cardP
  card_P : Nat.card ↥P = cardP
  /-- A witness for `C_{Q/Q₀}(P) ≠ 1`. -/
  x : G
  x_mem_Q : x ∈ hyp.Q
  x_notMem_Q0 : x ∉ hyp.Q0
  x_class_fixed : ∀ a ∈ P, a * x * a⁻¹ * x⁻¹ ∈ hyp.Q0

namespace SectionFourSetup

variable {hyp} (s4 : hyp.SectionFourSetup)

/-- `P ≤ D`, since `P ≤ V ≤ D`. -/
theorem P_le_D : s4.P ≤ hyp.D := le_trans s4.P_le_V hyp.V_le_D

/-- **`C_Q(P)` meets `Q − Q₀`** — Glauberman's step at §4's `P`. -/
theorem exists_fixed_not_mem_Q0
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hCop : Nat.Coprime (Nat.card ↥(s4.P.subgroupOf hyp.D)) (Nat.card ↥hyp.Q))
    (hSolv : IsSolvable ↥hyp.Q) :
    ∃ y : G, y ∈ hyp.Q ∧ y ∉ hyp.Q0 ∧ ∀ a ∈ s4.P, a * y * a⁻¹ = y :=
  hyp.exists_fixed_not_mem_Q0 hZ s4.P_le_D hCop hSolv s4.x_mem_Q s4.x_notMem_Q0
    s4.x_class_fixed

/-- **`C_Q(P)` is not elementary abelian** — the exponent discriminator of step (1)
(p. 132: "`C_Q(P)` has exponent 4"), delivered in the form
`nonempty_psu3Data_of_orderOf_eq_three` consumes. -/
theorem not_isElementaryAbelian_cQ
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥hyp.Q)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hCop : Nat.Coprime (Nat.card ↥(s4.P.subgroupOf hyp.D)) (Nat.card ↥hyp.Q))
    (hSolv : IsSolvable ↥hyp.Q) :
    ¬ OddOrder.GroupTheory.IsElementaryAbelian 2
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer ((s4.P : Set G)))) := by
  obtain ⟨y, hyQ, hy0, hyfix⟩ := s4.exists_fixed_not_mem_Q0 hZ hCop hSolv
  refine hyp.not_isElementaryAbelian_cQ_of_not_mem_Q0 hQsuz hZ hyQ hy0 ?_
  refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
  have hconj := hyfix a ha
  calc a * y = (a * y * a⁻¹) * a := by group
    _ = y * a := by rw [hconj]

/-- **`q = ℓ^p`** (Peterfalvi Part II, Ch. IV §4, step (1), p. 132):

> Now `|C_{Q₀}(P)| = ℓ` and so `q = ℓ^p` since `P` acts on `Q₀` as a group of field
> automorphisms (Chapter I, §2, Proposition 3).

Artin's degree formula (`natCard_Q0_eq_pow`) needs the action of `P` on `Q₀` to be
faithful, which is `P ∩ W = 1` — a field of the setup.  (The `W = 1` form of the formula
would be useless here: §4 is the case `V ≠ W`.) -/
theorem natCard_Q0_eq_pow_cardP :
    Nat.card ↥hyp.Q0 =
      Nat.card ↥(hyp.Q0 ⊓ Subgroup.centralizer ((s4.P : Set G))) ^ s4.cardP := by
  rw [← s4.card_P]
  exact hyp.natCard_Q0_eq_pow s4.P_le_V s4.P_inf_W

/-- **`Z(U) ⊆ P`** (Peterfalvi Part II, Ch. IV §4, step (1), p. 132), in the shape the
assembly uses:

> Since `P Z(U)` centralizes `C_Q(P) ⊄ Q₀`, `P Z(U) ∩ W = 1` and so `Z(U) ⊂ P`.

Applied with `S = P Z(U)`: a subgroup containing `P`, factoring through `P W` (which is
what the Galois inclusion `Z(U) ⊆ P W` provides) and centralizing an element of
`Q − Q₀`, is `P` itself. -/
theorem eq_P_of_centralizes {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu)
    {S : Subgroup G} (hPS : s4.P ≤ S)
    (hfac : ∀ s ∈ S, ∃ p ∈ s4.P, ∃ w ∈ hyp.W, s = p * w)
    {y : G} (hyQ : y ∈ hyp.Q) (hy0 : y ∉ hyp.Q0)
    (hS : ∀ c ∈ S, c * y = y * c) :
    S = s4.P :=
  eq_of_mem_mul_of_inf_eq_bot hPS hfac
    (hyp.inf_W_eq_bot_of_centralizes M hZ hmu hyQ hy0 hS)

/-- **`V ∩ U ⊆ P W`** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133):

> By the structure of `PSU(3, ℓ)`, `(V ∩ U)/(P ∩ U)` centralizes `C_{Q₀}(P)`.  Thus, by
> the theorem of Galois, `V ∩ U ⊂ P W`.

The Galois theorem is `centralizer_V_centralizer_Q0`, which computes `C_V(C_{Q₀}(P))` as
`P ⊔ W` exactly; the hypothesis here is the centralizing statement the book reads off the
structure of `PSU(3, ℓ)`. -/
theorem inf_le_sup_W_of_centralizes {U : Subgroup G}
    (hcent : hyp.V ⊓ U ≤ Subgroup.centralizer
      (((hyp.Q0 ⊓ Subgroup.centralizer ((s4.P : Set G))) : Subgroup G) : Set G)) :
    hyp.V ⊓ U ≤ s4.P ⊔ hyp.W := by
  rw [← hyp.centralizer_V_centralizer_Q0 s4.P_le_V]
  exact le_inf inf_le_left hcent

/-- **`V ∩ U ⊆ P × C_W(P)`** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133):

> ... and, since `U ⊂ C_G(P)`, `V ∩ U ⊂ P × C_W(P)`.

Writing `v ∈ V ∩ U` as `p w`, the factor `w = p⁻¹ v` centralizes `P` because `v` does
(`U ⊆ C_G(P)`) and `p` does (`P` has prime order, hence is abelian). -/
theorem inf_le_sup_centralizer_W {U : Subgroup G}
    (hUC : U ≤ Subgroup.centralizer ((s4.P : Set G)))
    (hfac : ∀ v ∈ hyp.V ⊓ U, ∃ p ∈ s4.P, ∃ w ∈ hyp.W, v = p * w) :
    hyp.V ⊓ U ≤ s4.P ⊔ (hyp.W ⊓ Subgroup.centralizer ((s4.P : Set G))) := by
  haveI : Fact (Nat.Prime s4.cardP) := ⟨s4.prime_cardP⟩
  haveI : IsCyclic ↥s4.P := isCyclic_of_prime_card s4.card_P
  intro v hv
  obtain ⟨p, hp, w, hw, rfl⟩ := hfac v hv
  refine Subgroup.mul_mem_sup hp ⟨hw, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
  -- `p` commutes with `a` because `P` is abelian, and `p * w` because `U ⊆ C_G(P)`
  have hpa : p * a = a * p := by
    letI := IsCyclic.commGroup (α := ↥s4.P)
    exact congrArg (Subtype.val (p := fun z => z ∈ s4.P))
      (mul_comm (⟨p, hp⟩ : ↥s4.P) (⟨a, ha⟩ : ↥s4.P))
  have hva : a * (p * w) = (p * w) * a :=
    Subgroup.mem_centralizer_iff.mp (hUC hv.2) a ha
  have hcancel : p * (a * w) = p * (w * a) := by
    calc p * (a * w) = (p * a) * w := by group
      _ = (a * p) * w := by rw [hpa]
      _ = a * (p * w) := by group
      _ = (p * w) * a := hva
      _ = p * (w * a) := by group
  exact mul_left_cancel hcancel

open scoped Pointwise in
/-- **`C_W(P) ≠ 1`** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133) — the book's

> Furthermore, `|(V ∩ U)/(P ∩ U)| = (ℓ+1)/(ℓ+1,3) ≠ 1` since `ℓ > 2`.
> Let `ζ₁ ∈ (V ∩ U) − (P ∩ U)` and `ζ ∈ C_W(P)` be such that `ζ₁ ∈ ζ P`.

in the only form step (2) uses it: a non-trivial `ζ ∈ W` centralizing `P`.

The `PSU(3, ℓ)` input is Ch. III §1's `exists_mem_residual_commute_Q0`: an `x ∈ U` whose
image in `U/Z(U)` is non-trivial of odd order and which centralizes `C_{Q₀}(P)`.  Since
`x` centralizes the distinguished involution it lies in `H`, so `x = q v` with `q ∈ Q`,
`v ∈ V`; both factors centralize `P` (`mem_centralizer_of_qv_decomposition`), and the
theorem of Galois (`centralizer_V_centralizer_Q0`) puts `v ∈ P ⊔ W`.  Writing `v = p ζ`
— legitimate because `P ≤ D` normalizes `W` — gives `ζ ∈ C_W(P)`, and `ζ = 1` would make
`v ∈ P` central in `U`, so that the image of `x` would be the image of the `2`-element
`q`: impossible for a non-trivial element of odd order. -/
theorem exists_ne_one_mem_W_centralizer (hP : s4.P ≠ ⊥)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer ((s4.P : Set G))),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (hord : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hnea : ¬ OddOrder.GroupTheory.IsElementaryAbelian 2
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer ((s4.P : Set G)))))
    (ih : TheoremAInductionBelow G Ω) :
    ∃ w ∈ hyp.W, w ≠ 1 ∧ w ∈ Subgroup.centralizer ((s4.P : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime s4.cardP) := ⟨s4.prime_cardP⟩
  haveI : IsCyclic ↥s4.P := isCyclic_of_prime_card s4.card_P
  letI := hyp.centralizerQuotientMulAction s4.P_le_V
  obtain ⟨tri⟩ := hyp.centralizer_trichotomy_of_induction s4.P_le_V hP hA3 ih
  obtain ⟨⟨data, _teq, details⟩⟩ :=
    nonempty_psu3Data_of_orderOf_eq_three tri.branch hord hnea
  set C : Subgroup G := Subgroup.centralizer ((s4.P : Set G)) with hCdef
  set CQ : Subgroup ↥C := hyp.Q.subgroupOf C with hCQdef
  set F : Subgroup ↥C := Subgroup.primeComplementResidual 2 C with hFdef
  obtain ⟨x, hdne, hdodd, hcomm⟩ :=
    details.exists_mem_residual_commute_Q0 s4.P_le_V tri.common
  set xG : G := ((x : ↥C) : G) with hxG
  set s : G := hyp.distinguishedInvolution with hs
  have hs0 : s ∈ hyp.Q0 :=
    ⟨hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_mem_H⟩
  have hsC : s ∈ C := by
    refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
    have hgV : g ∈ hyp.V := s4.P_le_V hg
    rw [hyp.V_eq_centralizer_distinguishedInvolution] at hgV
    exact (Subgroup.mem_centralizer_iff.mp hgV.2 s rfl).symm
  have hxs : Commute xG s := hcomm s hs0 hsC
  have hxH : xG ∈ hyp.H :=
    hyp.centralizer_le_H_of_mem_Q (hyp.Q0_le_Q hs0)
      hyp.distinguishedInvolution_ne_one
      (Subgroup.mem_centralizer_singleton_iff.mpr hxs)
  obtain ⟨q, hqQ, v, hvV, hqv⟩ :=
    hyp.exists_mem_Q_mem_V_of_mem_H_of_commute_distinguishedInvolution hxH hxs
  have hxC : xG ∈ C := (x : ↥C).2
  obtain ⟨hqC, hvC⟩ :=
    hyp.mem_centralizer_of_qv_decomposition s4.P_le_V hqQ hvV hqv hxC
  -- the theorem of Galois: `v ∈ P ⊔ W`
  have hvGal : v ∈ hyp.V ⊓ Subgroup.centralizer
      ((hyp.Q0 ⊓ Subgroup.centralizer ((s4.P : Set G)) : Subgroup G) : Set G) := by
    refine ⟨hvV, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hxy : Commute xG y := hcomm y hy.1 hy.2
    have hqy : Commute q y :=
      Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hy.1) q hqQ
    have hv : v = q⁻¹ * xG := by rw [hqv]; group
    rw [hv]
    calc y * (q⁻¹ * xG) = (y * q⁻¹) * xG := by group
      _ = (q⁻¹ * y) * xG := by rw [hqy.inv_left.eq]
      _ = q⁻¹ * (y * xG) := by group
      _ = q⁻¹ * (xG * y) := by rw [hxy.symm.eq]
      _ = (q⁻¹ * xG) * y := by group
  have hvPW : v ∈ s4.P ⊔ hyp.W := by
    rw [← hyp.centralizer_V_centralizer_Q0 s4.P_le_V]
    exact hvGal
  -- `P ≤ D` normalizes `W`, so `P ⊔ W = P · W`
  have hcoe : ((s4.P ⊔ hyp.W : Subgroup G) : Set G) = (s4.P : Set G) * (hyp.W : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (le_trans s4.P_le_D hyp.D_le_normalizer_W)
  obtain ⟨p, hp, w, hw, hpw⟩ : v ∈ (s4.P : Set G) * (hyp.W : Set G) := hcoe ▸ hvPW
  have hPC : s4.P ≤ C := by
    intro a ha
    refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
    letI := IsCyclic.commGroup (α := ↥s4.P)
    exact congrArg (Subtype.val (p := fun z => z ∈ s4.P))
      (mul_comm (⟨b, hb⟩ : ↥s4.P) (⟨a, ha⟩ : ↥s4.P))
  have hwC : w ∈ C := by
    have : w = p⁻¹ * v := by rw [← hpw]; group
    rw [this]
    exact C.mul_mem (C.inv_mem (hPC hp)) hvC
  refine ⟨w, hw, ?_, hwC⟩
  intro hw1
  -- `w = 1` makes `v ∈ P`, hence central in `U`, so `x` and the `2`-element `q` agree there
  have hvP : v ∈ s4.P := by
    rw [← hpw, hw1]
    simpa using hp
  have hqCQ : (⟨q, hqC⟩ : ↥C) ∈ CQ := Subgroup.mem_subgroupOf.mpr hqQ
  have hCQF : CQ ≤ F := by
    rw [hFdef, tri.common.residual_eq_normalClosure]
    exact Subgroup.le_normalClosure
  have hqF : (⟨q, hqC⟩ : ↥C) ∈ F := hCQF hqCQ
  have hvF : (⟨v, hvC⟩ : ↥C) ∈ F := by
    have hveq : (⟨v, hvC⟩ : ↥C) = (⟨q, hqC⟩ : ↥C)⁻¹ * (x : ↥C) := by
      apply Subtype.ext
      change v = q⁻¹ * xG
      rw [hqv]; group
    rw [hveq]
    exact F.mul_mem (F.inv_mem hqF) x.2
  set qF : ↥F := ⟨⟨q, hqC⟩, hqF⟩ with hqFdef
  set vF : ↥F := ⟨⟨v, hvC⟩, hvF⟩ with hvFdef
  have hxqv : x = qF * vF := by
    apply Subtype.ext; apply Subtype.ext
    change xG = q * v
    exact hqv
  have hvZ : vF ∈ Subgroup.center ↥F := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext; apply Subtype.ext
    change ((z : ↥C) : G) * v = v * ((z : ↥C) : G)
    exact (Subgroup.mem_centralizer_iff.mp (z : ↥C).2 v hvP).symm
  have himg : QuotientGroup.mk (s := Subgroup.center ↥F) x =
      QuotientGroup.mk (s := Subgroup.center ↥F) qF := by
    rw [hxqv, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff vF).mpr hvZ, mul_one]
  obtain ⟨k, hk⟩ := tri.common.cQ_isPGroup (⟨⟨q, hqC⟩, hqCQ⟩ : ↥CQ)
  have hqpow : qF ^ 2 ^ k = 1 := by
    apply Subtype.ext; apply Subtype.ext
    change q ^ 2 ^ k = 1
    exact congrArg (fun z : ↥CQ => ((z : ↥C) : G)) hk
  have hmkpow : (QuotientGroup.mk (s := Subgroup.center ↥F) x) ^ 2 ^ k = 1 := by
    rw [himg, ← QuotientGroup.mk_pow, hqpow]
    rfl
  have hdvd : orderOf (QuotientGroup.mk (s := Subgroup.center ↥F) x) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hmkpow
  have hone : orderOf (QuotientGroup.mk (s := Subgroup.center ↥F) x) = 1 :=
    Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right k
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
          (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hdodd))).symm)
      dvd_rfl hdvd
  exact hdne (orderOf_eq_one_iff.mp hone)

/-- **Step (2)'s `ζ` survives in the centralizer quotient** (Peterfalvi Part II,
Ch. IV §4, p. 133).

`ζ ∈ C_W(P)` lands in `W̄` because `W = D ∩ C(Q₀)` on both sides
(`W_eq_inf_centralizer_Q0`) and `Q̄₀` is the image of `C_{Q₀}(P)`
(`map_centralizer_Q0_eq_quotient_Q0`).  It stays non-trivial because the kernel
`𝒩(C_G(P)) = C_D(P) ∩ C(C_Q(P))` centralizes *all* of `C_Q(P)`, which contains the
`P`-fixed `ω ∈ Q − Q₀` of step (1) — and `W` acts fixed-point-freely on `Q/Q₀`
(`eq_one_of_conj_eq_mul_Q0_of_mem_W`), so only `1` can do that.

This is the last input of `psu3Numerics_and_standingData_centralizerQuotient`. -/
theorem exists_ne_one_mem_quotient_W {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer ((s4.P : Set G))),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hωfix : ∀ a ∈ s4.P, a * ω * a⁻¹ = ω)
    {ζ : G} (hζW : ζ ∈ hyp.W) (hζ1 : ζ ≠ 1)
    (hζC : ζ ∈ Subgroup.centralizer ((s4.P : Set G))) :
    letI := hyp.centralizerQuotientMulAction s4.P_le_V
    ∃ z ∈ (hyp.centralizerQuotientHypothesis s4.P_le_V hA3).W, z ≠ 1 := by
  letI := hyp.centralizerQuotientMulAction s4.P_le_V
  set C : Subgroup G := Subgroup.centralizer ((s4.P : Set G)) with hCdef
  set N : Subgroup ↥C := (hyp.H.subgroupOf C).normalCore with hNdef
  set pi : ↥C →* ↥C ⧸ N := QuotientGroup.mk' N with hpidef
  have hζCmem : ζ ∈ C := hζC
  set ζC : ↥C := ⟨ζ, hζCmem⟩ with hζCdef
  have hωC : ω ∈ C := by
    refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    have := hωfix a ha
    calc a * ω = (a * ω * a⁻¹) * a := by group
      _ = ω * a := by rw [this]
  refine ⟨pi ζC, ?_, ?_⟩
  · rw [(hyp.centralizerQuotientHypothesis s4.P_le_V hA3).W_eq_inf_centralizer_Q0]
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    · exact ⟨ζC, Subgroup.mem_subgroupOf.mpr (hyp.V_le_D (hyp.W_le_V hζW)), rfl⟩
    · rw [← hyp.map_centralizer_Q0_eq_quotient_Q0 s4.P_le_V hA3] at hy
      obtain ⟨y0, hy0, rfl⟩ := hy
      have hy0Q0 : ((y0 : ↥C) : G) ∈ hyp.Q0 := Subgroup.mem_subgroupOf.mp hy0
      have hcomm : ζ * ((y0 : ↥C) : G) = ((y0 : ↥C) : G) * ζ :=
        (Subgroup.mem_centralizer_iff.mp
          (hyp.W_eq_inf_centralizer_Q0 ▸ hζW).2 _ hy0Q0).symm
      rw [← map_mul, ← map_mul]
      exact congrArg pi (Subtype.ext (by simpa using hcomm.symm))
  · intro hone
    have hmemN : ζC ∈ N := (QuotientGroup.eq_one_iff _).mp hone
    rw [hNdef, hyp.normalCore_cH_eq_centralizer_cQ s4.P_le_V] at hmemN
    have hωQC : (⟨ω, hωC⟩ : ↥C) ∈ hyp.Q.subgroupOf C := Subgroup.mem_subgroupOf.mpr hωQ
    have hcomm : ((⟨ω, hωC⟩ : ↥C) : ↥C) * ζC = ζC * ⟨ω, hωC⟩ :=
      Subgroup.mem_centralizer_iff.mp hmemN.2 _ hωQC
    have hcommG : ω * ζ = ζ * ω := congrArg (Subtype.val (p := fun z => z ∈ C)) hcomm
    refine hζ1 (hyp.eq_one_of_conj_eq_mul_Q0_of_mem_W M hZ hmu hωQ hωQ0 hζW
      hyp.Q0.one_mem ?_)
    rw [mul_one]
    calc ζ⁻¹ * ω * ζ = ζ⁻¹ * (ω * ζ) := by group
      _ = ζ⁻¹ * (ζ * ω) := by rw [hcommG]
      _ = ω := by group

/-- **§2/§3 run inside the centralizer quotient, on §4's ambient hypotheses alone**
(Peterfalvi Part II, Ch. IV §4, step (2), p. 133).

`psu3Numerics_and_standingData_centralizerQuotient` still asked for a `1 ≠ w ∈ W̄`; the
book supplies it as `ζ₁ ∈ (V ∩ U) − (P ∩ U)`.  Chaining `exists_ne_one_mem_W_centralizer`
(the `PSU(3, ℓ)` input) with `exists_ne_one_mem_quotient_W` (its descent) closes that last
gap, so both standing bundles of §2/§3 — and the numerics `exists_standardModel` takes —
are now available for the quotient with no residual hypothesis about it. -/
theorem standingData_centralizerQuotient {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu)
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥hyp.Q)
    (hCop : Nat.Coprime (Nat.card ↥(s4.P.subgroupOf hyp.D)) (Nat.card ↥hyp.Q))
    (hSolv : IsSolvable ↥hyp.Q) (hP : s4.P ≠ ⊥)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer ((s4.P : Set G))),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (hord : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (ih : TheoremAInductionBelow G Ω) :
    letI := hyp.centralizerQuotientMulAction s4.P_le_V
    ∃ n : ℕ, n ≠ 0 ∧
      Nat.card ↥(hyp.centralizerQuotientHypothesis s4.P_le_V hA3).Q0 = 2 ^ n ∧
      Nat.card (hyp.centralizerQuotientHypothesis s4.P_le_V hA3).Q
        = Nat.card ↥(hyp.centralizerQuotientHypothesis s4.P_le_V hA3).Q0 ^ 3 ∧
      orderOf ((hyp.centralizerQuotientHypothesis s4.P_le_V hA3).distinguishedInvolution *
        (hyp.centralizerQuotientHypothesis s4.P_le_V hA3).t) = 3 ∧
      OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group
        ↥(hyp.centralizerQuotientHypothesis s4.P_le_V hA3).Q ∧
      Nonempty ((hyp.centralizerQuotientHypothesis s4.P_le_V hA3).LemmaFiveSetup n) ∧
      Nonempty ((hyp.centralizerQuotientHypothesis s4.P_le_V hA3).QuotientFieldModel n) := by
  letI := hyp.centralizerQuotientMulAction s4.P_le_V
  have hnea := s4.not_isElementaryAbelian_cQ hQsuz hZ hCop hSolv
  obtain ⟨ω, hωQ, hωQ0, hωfix⟩ := s4.exists_fixed_not_mem_Q0 hZ hCop hSolv
  obtain ⟨ζ, hζW, hζ1, hζC⟩ := s4.exists_ne_one_mem_W_centralizer hP hA3 hord hnea ih
  obtain ⟨z, hzW, hz1⟩ :=
    s4.exists_ne_one_mem_quotient_W M hZ hmu hA3 hωQ hωQ0 hωfix hζW hζ1 hζC
  obtain ⟨n, hn, hQ0card, hcardQ, hst, hQsuzBar, hdata⟩ :=
    hyp.psu3Numerics_and_standingData_centralizerQuotient s4.P_le_V hP hA3 hord hnea ih
  obtain ⟨h5, hM⟩ := hdata z hzW hz1
  exact ⟨n, hn, hQ0card, hcardQ, hst, hQsuzBar, h5, hM⟩

/-- **`P ∩ U ≤ Z(U)`** (Peterfalvi Part II, Ch. IV §4, step (1), p. 132).

Statement (1) of §4 reads `U/(P ∩ U) ≅ PSU(3, ℓ)` while its proof produces
`U/Z(U) ≅ PSU(3, ℓ)` together with `Z(U) ⊆ P`.  The two agree, and this is the free
half: `U ≤ C_G(P)`, so every element of `U` centralizes `P`, hence `P ∩ U` is central in
`U`.  (The other half is step (1)'s `Z(U) ⊆ P`, `eq_P_of_centralizes`.) -/
theorem mem_center_primeComplementResidual_of_mem_P
    {x : ↥(Subgroup.centralizer ((s4.P : Set G)))}
    (hxU : x ∈ Subgroup.primeComplementResidual 2
      (Subgroup.centralizer ((s4.P : Set G))))
    (hxP : (x : G) ∈ s4.P) :
    (⟨x, hxU⟩ : ↥(Subgroup.primeComplementResidual 2
        (Subgroup.centralizer ((s4.P : Set G))))) ∈
      Subgroup.center ↥(Subgroup.primeComplementResidual 2
        (Subgroup.centralizer ((s4.P : Set G)))) := by
  rw [Subgroup.mem_center_iff]
  intro u
  apply Subtype.ext
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp
    ((u : ↥(Subgroup.centralizer ((s4.P : Set G)))).2) (x : G) hxP).symm

/-! ### `t` lives in `U`

Ch. IV §4 works with `f₁`, `h₁` "relative to `U`, `U ∩ H` and `t`" (p. 133) — the *same*
involution `t`.  That is legitimate: `t` centralizes `V ⊇ P`, and being an involution it
is a `2`-element, so it lies in a Sylow `2`-subgroup of `C_G(P)` and hence in
`O^{2'}(C_G(P)) = U`. -/

/-- `t` centralizes `P`, since `P ≤ V` and `t` centralizes `V`. -/
theorem t_mem_centralizer : hyp.t ∈ Subgroup.centralizer ((s4.P : Set G)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (hyp.commute_t_of_mem_V (s4.P_le_V hx)).eq

/-- **`t ∈ U = O^{2'}(C_G(P))`.** -/
theorem t_mem_primeComplementResidual :
    (⟨hyp.t, s4.t_mem_centralizer⟩ :
        ↥(Subgroup.centralizer ((s4.P : Set G)))) ∈
      Subgroup.primeComplementResidual 2
        (Subgroup.centralizer ((s4.P : Set G))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tC : ↥(Subgroup.centralizer ((s4.P : Set G))) :=
    ⟨hyp.t, s4.t_mem_centralizer⟩ with htCdef
  have htsq : tC ^ 2 = 1 := Subtype.ext (by simpa [htCdef] using hyp.t_sq)
  have hT : IsPGroup 2 ↥(Subgroup.zpowers tC) := by
    have hdvd : orderOf tC ∣ 2 := orderOf_dvd_of_pow_eq_one htsq
    have hcard : Nat.card ↥(Subgroup.zpowers tC) = orderOf tC := Nat.card_zpowers tC
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact IsPGroup.of_card (n := 0) (by rw [hcard, h1]; norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [hcard, h2]; norm_num)
  obtain ⟨S, hS⟩ := hT.exists_le_sylow
  exact Subgroup.le_primeComplementResidual S
    (hS (Subgroup.mem_zpowers tC))

end SectionFourSetup

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
