/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.RankOneSetup
import OddOrder.GroupTheory.RankOneBNPairRigidity

/-!
# `Ω` in the coordinates of Peterfalvi Part II, Ch. IV §1

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §1, p. 123:

> Let `a` be a point in `X` whose stabilizer in `L` is `M`.  We can identify `X` with
> `Q ∪ {a}` by identifying `x ∈ Q` with `a t x`.

`RankOneBNPair` carries out that identification on `L ⧸ M` (`coordsEquiv`), because the
Lemma of §1 is about groups given abstractly.  A standing hypothesis, on the other hand,
comes with an honest point set `Ω` and a base point.  This file connects the two: the
orbit map `g H ↦ g • basept` is an equivariant bijection `G ⧸ H ≃ Ω`, so `Ω` inherits
the coordinates, and the permutation representation `permHom` of §1 *is* the action on
`Ω` read in them.

That is what turns the Lemma's group isomorphism into an isomorphism *of permutation
groups*, which is what Theorem A's conclusion (`PSU3InductionTarget.actionEquiv`) asks
for.

## Main results

* `Hypothesis.quotientHEquiv` — the equivariant bijection `G ⧸ H ≃ Ω`.
* `Hypothesis.pointEquiv` — the coordinates `Option ↥Q ≃ Ω`.
* `Hypothesis.pointEquiv_permHom` — `permHom` is the action on `Ω`.
* `Hypothesis.exists_conjQMulEquiv_actionEquiv` — the Lemma of §1 as a matching of
  permutation groups: `⟨Q^x⟩ ≃* ⟨Q'^x⟩` together with an equivariant `Ω ≃ Ω'`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair
open MulAction

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G] (hyp : Hypothesis G Ω)

include hyp

section /- Ch. IV §1: the point set (p. 123) -/

/-- The orbit map `g H ↦ g • basept`.  Well defined because `H` is the stabilizer of
`basept`. -/
noncomputable def quotientHMap (x : G ⧸ hyp.H) : Ω :=
  Quotient.liftOn' x (fun g : G => g • hyp.basept) (by
    intro a b hab
    have hmem : a⁻¹ * b ∈ hyp.H := QuotientGroup.leftRel_apply.mp hab
    have : (a⁻¹ * b) • hyp.basept = hyp.basept := hyp.smul_basept_eq_of_mem_H hmem
    calc a • hyp.basept = a • ((a⁻¹ * b) • hyp.basept) := by rw [this]
      _ = b • hyp.basept := by rw [smul_smul, mul_inv_cancel_left])

@[simp] theorem quotientHMap_mk (g : G) :
    hyp.quotientHMap (g : G ⧸ hyp.H) = g • hyp.basept := rfl

theorem quotientHMap_bijective : Function.Bijective hyp.quotientHMap := by
  have h2 := hyp.doubly_transitive
  have : IsPretransitive G Ω := isPretransitive_of_is_two_pretransitive
  constructor
  · intro x y hxy
    induction x using QuotientGroup.induction_on with
    | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
        rw [quotientHMap_mk, quotientHMap_mk] at hxy
        refine QuotientGroup.eq.mpr ?_
        rw [hyp.H_def, mem_stabilizer_iff, mul_smul, ← hxy, inv_smul_smul]
  · intro ω
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G hyp.basept ω
    exact ⟨(g : G ⧸ hyp.H), hg⟩

/-- **The point set of a standing hypothesis is `G ⧸ H`** — the identification the Lemma
of Ch. IV §1 works over. -/
noncomputable def quotientHEquiv : G ⧸ hyp.H ≃ Ω :=
  Equiv.ofBijective _ hyp.quotientHMap_bijective

@[simp] theorem quotientHEquiv_mk (g : G) :
    hyp.quotientHEquiv (g : G ⧸ hyp.H) = g • hyp.basept := rfl

/-- The identification is equivariant. -/
theorem quotientHEquiv_smul (g : G) (x : G ⧸ hyp.H) :
    hyp.quotientHEquiv (g • x) = g • hyp.quotientHEquiv x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    change hyp.quotientHEquiv ((g * a : G) : G ⧸ hyp.H) = _
    rw [quotientHEquiv_mk, quotientHEquiv_mk, mul_smul]

/-- **The coordinates of Ch. IV §1 on `Ω`**: the base point together with a copy of `Q`,
with `x ∈ Q` naming the point `basept · t x` of the book's right-action notation. -/
noncomputable def pointEquiv : Option ↥hyp.Q ≃ Ω :=
  (coordsEquiv hyp.rankOneSetup).trans hyp.quotientHEquiv

@[simp] theorem pointEquiv_none : hyp.pointEquiv none = hyp.basept := by
  change hyp.quotientHEquiv ((1 : G) : G ⧸ hyp.H) = _
  rw [quotientHEquiv_mk, one_smul]

@[simp] theorem pointEquiv_some (x : ↥hyp.Q) :
    hyp.pointEquiv (some x) = ((x : G)⁻¹ * hyp.t) • hyp.basept := rfl

/-- **`permHom` is the action of `G` on `Ω`, read in the coordinates of §1.**

This is what makes the Lemma of §1 a statement about permutation groups rather than
abstract groups: a matching of the permutation representations is a matching of the
actions on the two point sets. -/
theorem pointEquiv_permHom (g : G) (o : Option ↥hyp.Q) :
    hyp.pointEquiv (permHom hyp.rankOneSetup g o) = g • hyp.pointEquiv o := by
  change hyp.quotientHEquiv (coordsEquiv hyp.rankOneSetup
      ((coordsEquiv hyp.rankOneSetup).symm (g • coords hyp.H hyp.Q hyp.t o)))
    = g • hyp.quotientHEquiv (coordsEquiv hyp.rankOneSetup o)
  rw [Equiv.apply_symm_apply, coordsEquiv_apply, hyp.quotientHEquiv_smul]

/-- The same, solved for the coordinate of a translated point. -/
theorem pointEquiv_symm_smul (g : G) (ω : Ω) :
    hyp.pointEquiv.symm (g • ω)
      = permHom hyp.rankOneSetup g (hyp.pointEquiv.symm ω) := by
  refine hyp.pointEquiv.injective ?_
  rw [Equiv.apply_symm_apply, hyp.pointEquiv_permHom, Equiv.apply_symm_apply]

end

section /- Ch. IV §1: the Lemma as a matching of permutation groups (p. 123) -/

variable {G' Ω' : Type*} [Group G'] [MulAction G' Ω'] [Finite G']

/-- **The Lemma of Peterfalvi Part II, Ch. IV §1, as a matching of permutation groups**
(p. 123).

`conjQMulEquivOfData` says that a group isomorphism `Q ≃* Q'` intertwining `f` with `f'`
produces `⟨Q^x⟩ ≃* ⟨Q'^x⟩`.  Read through the coordinates of the two point sets it says
more: the *same* data produces a bijection `Ω ≃ Ω'` intertwining the two actions, which
is what Theorem A's conclusion asks for.

The isomorphism carries `⟨Q^x | x ∈ G⟩`, which for `Q` a Sylow `2`-subgroup is `O^{2′}(G)`
(`closure_iUnion_conj_eq_primeComplementResidual`). -/
theorem exists_conjQMulEquiv_actionEquiv (hyp' : Hypothesis G' Ω')
    {f g h : G → G} {f' g' h' : G' → G'}
    (H : OddOrder.GroupTheory.RankOneBNPair.IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (H' : OddOrder.GroupTheory.RankOneBNPair.IsFGH hyp'.H hyp'.Q hyp'.D hyp'.t f' g' h')
    (hcore : hyp.H.normalCore = ⊥) (hcore' : hyp'.H.normalCore = ⊥)
    (εQ : ↥hyp.Q ≃* ↥hyp'.Q)
    (hεf : ∀ (x : ↥hyp.Q) (hx1 : (x : G) ≠ 1),
      ((εQ ⟨f (x : G), H.f_mem x.2 hx1⟩ : ↥hyp'.Q) : G')
        = f' ((εQ x : ↥hyp'.Q) : G')) :
    ∃ (e : ↥(Subgroup.closure (⋃ y : G, ((fun q => y⁻¹ * q * y) '' (hyp.Q : Set G))))
          ≃* ↥(Subgroup.closure
            (⋃ y : G', ((fun q => y⁻¹ * q * y) '' (hyp'.Q : Set G')))))
        (α : Ω ≃ Ω'),
      ∀ (l : ↥(Subgroup.closure (⋃ y : G, ((fun q => y⁻¹ * q * y) '' (hyp.Q : Set G)))))
        (ω : Ω), α ((l : G) • ω) = ((e l : G') • α ω) := by
  classical
  refine ⟨conjQMulEquivOfData hyp.rankOneSetup hyp'.rankOneSetup H H' hcore hcore' εQ hεf,
    hyp.pointEquiv.symm.trans ((Equiv.optionCongr εQ.toEquiv).trans hyp'.pointEquiv),
    fun l ω => ?_⟩
  have hkey := permHom_conjQMulEquivOfData hyp.rankOneSetup hyp'.rankOneSetup H H'
    hcore hcore' εQ hεf l
  have hval := congrArg (fun p : Equiv.Perm (Option ↥hyp'.Q) =>
    p (Equiv.optionCongr εQ.toEquiv (hyp.pointEquiv.symm ω))) hkey
  simp only [permCongrHom_apply, Equiv.symm_apply_apply] at hval
  change hyp'.pointEquiv (Equiv.optionCongr εQ.toEquiv
      (hyp.pointEquiv.symm ((l : G) • ω))) = _
  rw [hyp.pointEquiv_symm_smul, ← hval, hyp'.pointEquiv_permHom]
  rfl

end

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
