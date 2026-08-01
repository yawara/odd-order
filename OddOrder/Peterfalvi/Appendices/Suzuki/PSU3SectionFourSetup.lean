/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerTrichotomy
import OddOrder.Higman.Suzuki2Groups.CenterInvolutions
import OddOrder.GroupTheory.CoprimeFixedPoints
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3OrbitCount

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
* `Hypothesis.SectionFourSetup` — the standing hypothesis of §4, and
  `SectionFourSetup.not_isElementaryAbelian_cQ`, which delivers the exponent
  discriminator from it.
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

end SectionFourSetup

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
