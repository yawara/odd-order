/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerTrichotomy
import OddOrder.Higman.Suzuki2Groups.CenterInvolutions
import OddOrder.GroupTheory.CoprimeFixedPoints

/-!
# Peterfalvi Part II, Ch. IV §4: the exponent discriminator of step (1)

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

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
