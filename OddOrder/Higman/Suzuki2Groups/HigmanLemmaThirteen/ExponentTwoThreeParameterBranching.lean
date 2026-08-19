/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoThreePairCoordinates

/-!
# Higman's Lemma 13: branching the three coherent parameters

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

The three pairwise classifications force two of the coherent factor
parameters to coincide.  This leaf sharpens that raw coincidence into the
four branches needed downstream:

* align the `X ⊔ T` and `Z ⊔ T` joins through the common factor `T`;
* align the `X ⊔ Z` and `T ⊔ Z` joins through the common factor `Z`;
* align the `Z ⊔ X` and `T ⊔ X` joins through the common factor `X`; or
* all three factor parameters agree and are nontrivial.

In each aligned branch the two copy equalities and Higman's uniqueness
alternative are retained together, so the downstream graph construction
does not need to repeat the parameter case split.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe u uP

/-- The parameter data needed to align two pairwise joins: the two
non-common factor copies have equal parameters, the two common-factor
copies have equal parameters, and the left parameter is either trivial or
different from the common parameter. -/
structure AlignedTwoJoinParameterData
    {α : Type u} [One α]
    (leftJ commonJ leftK commonK : α) : Prop where
  left_eq : leftJ = leftK
  common_eq : commonJ = commonK
  unique : leftJ = 1 ∨ leftJ ≠ commonJ

/-- The remaining branch after all aligned alternatives with a distinct
common parameter have failed: all three parameters agree and their common
value is nontrivial. -/
structure AllEqualNontrivialParameterData
    {α : Type u} [One α] (x z t : α) : Prop where
  x_eq_z : x = z
  z_eq_t : z = t
  ne_one : x ≠ 1

/-- A coincidence among three parameters refines into one of the three
aligned alternatives or the all-equal nontrivial alternative.

The `x = 1` disjunct is deliberately retained in each aligned case: it is
exactly the commutative-factor side of the uniqueness hypothesis used by
the aligned graph theorem. -/
theorem
    pairwise_parameterCoincidence_refines_to_aligned_or_allEqualNontrivial
    {α : Type u} [One α] {x z t : α}
    (hcoincidence : x = z ∨ x = t ∨ z = t) :
    (x = z ∧ (x = 1 ∨ x ≠ t)) ∨
      (x = t ∧ (x = 1 ∨ x ≠ z)) ∨
      (z = t ∧ (z = 1 ∨ z ≠ x)) ∨
      (x = z ∧ z = t ∧ x ≠ 1) := by
  classical
  rcases hcoincidence with hxz | hxt | hzt
  · by_cases hxOne : x = 1
    · exact Or.inl ⟨hxz, Or.inl hxOne⟩
    by_cases hxt : x = t
    · exact Or.inr (Or.inr (Or.inr
        ⟨hxz, hxz.symm.trans hxt, hxOne⟩))
    · exact Or.inl ⟨hxz, Or.inr hxt⟩
  · by_cases hxOne : x = 1
    · exact Or.inr (Or.inl ⟨hxt, Or.inl hxOne⟩)
    by_cases hxz : x = z
    · exact Or.inr (Or.inr (Or.inr
        ⟨hxz, hxz.symm.trans hxt, hxOne⟩))
    · exact Or.inr (Or.inl ⟨hxt, Or.inr hxz⟩)
  · by_cases hzOne : z = 1
    · exact Or.inr (Or.inr (Or.inl ⟨hzt, Or.inl hzOne⟩))
    by_cases hzx : z = x
    · have hxOne : x ≠ 1 := by
        intro hx
        exact hzOne (hzx.trans hx)
      exact Or.inr (Or.inr (Or.inr
        ⟨hzx.symm, hzt, hxOne⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hzt, Or.inr hzx⟩))

/-- **Higman Lemma 13 (p. 93), coherent three-pair parameter branching.**

The first branch uses `XT` and `ZT` with common factor `T`.  The second
views `ZT` in reverse order and uses `XZ` and `TZ` with common factor `Z`.
The third views both incident joins in reverse order and uses `ZX` and `TX`
with common factor `X`.  Each branch exposes exactly the `left` equality,
`common` equality, and uniqueness disjunction required by the aligned graph
construction.  The final branch records equality and nontriviality of the
three actual-factor parameters. -/
theorem coherent_threePairCoordinates_parameterBranching
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    {X Z T : Subgroup P}
    (hXinv : IsAInvariant Y.subtype X)
    (hZinv : IsAInvariant Y.subtype Z)
    (hTinv : IsAInvariant Y.subtype T)
    (hPhiEA : IsElementaryAbelian 2 (frattini P))
    (hMapXZ : (frattini ↥(X ⊔ Z)).map (X ⊔ Z).subtype = frattini P)
    (hMapXT : (frattini ↥(X ⊔ T)).map (X ⊔ T).subtype = frattini P)
    (hMapZT : (frattini ↥(Z ⊔ T)).map (Z ⊔ T).subtype = frattini P)
    {n : ℕ}
    (c : Y)
    (ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (nu : GaloisField 2 n) :
    let hXZEA : IsElementaryAbelian 2 (frattini ↥(X ⊔ Z)) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMapXZ).symm hPhiEA
    let hXTEA : IsElementaryAbelian 2 (frattini ↥(X ⊔ T)) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMapXT).symm hPhiEA
    let hZTEA : IsElementaryAbelian 2 (frattini ↥(Z ⊔ T)) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMapZT).symm hPhiEA
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    letI : IsMulCommutative (frattini ↥(X ⊔ Z)) :=
      IsMulCommutative.of_comm hXZEA.comm
    letI : Module (ZMod 2) (Additive (frattini ↥(X ⊔ Z))) :=
      hXZEA.zmodModule
    letI : IsMulCommutative (frattini ↥(X ⊔ T)) :=
      IsMulCommutative.of_comm hXTEA.comm
    letI : Module (ZMod 2) (Additive (frattini ↥(X ⊔ T))) :=
      hXTEA.zmodModule
    letI : IsMulCommutative (frattini ↥(Z ⊔ T)) :=
      IsMulCommutative.of_comm hZTEA.comm
    letI : Module (ZMod 2) (Additive (frattini ↥(Z ⊔ T))) :=
      hZTEA.zmodModule
    ∀
    (xz : NormalizedActualFactorPairCoordinates
      hXinv hZinv hPhiEA hMapXZ c ePhi nu)
    (xt : NormalizedActualFactorPairCoordinates
      hXinv hTinv hPhiEA hMapXT c ePhi nu)
    (zt : NormalizedActualFactorPairCoordinates
      hZinv hTinv hPhiEA hMapZT c ePhi nu)
    (_hthetaX : xz.left.theta = xt.left.theta)
    (_hthetaZ : xz.right.theta = zt.left.theta)
    (_hthetaT : xt.right.theta = zt.right.theta)
    (_hcoincidence :
      xz.left.theta = xz.right.theta ∨
        xz.left.theta = xt.right.theta ∨
        xz.right.theta = xt.right.theta),
    AlignedTwoJoinParameterData
        xt.left.theta xt.right.theta zt.left.theta zt.right.theta ∨
      AlignedTwoJoinParameterData
        xz.left.theta xz.right.theta zt.right.theta zt.left.theta ∨
      AlignedTwoJoinParameterData
        xz.right.theta xz.left.theta xt.right.theta xt.left.theta ∨
      AllEqualNontrivialParameterData
        xz.left.theta xz.right.theta xt.right.theta := by
  classical
  dsimp only
  let hXZEA : IsElementaryAbelian 2 (frattini ↥(X ⊔ Z)) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapXZ).symm hPhiEA
  let hXTEA : IsElementaryAbelian 2 (frattini ↥(X ⊔ T)) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapXT).symm hPhiEA
  let hZTEA : IsElementaryAbelian 2 (frattini ↥(Z ⊔ T)) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMapZT).symm hPhiEA
  let : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hPhiEA.comm
  let : CommGroup (frattini P) := inferInstance
  let : Module (ZMod 2) (Additive (frattini P)) :=
    hPhiEA.zmodModule
  let : IsMulCommutative (frattini ↥(X ⊔ Z)) :=
    IsMulCommutative.of_comm hXZEA.comm
  let : CommGroup (frattini ↥(X ⊔ Z)) := inferInstance
  let : Module (ZMod 2) (Additive (frattini ↥(X ⊔ Z))) :=
    hXZEA.zmodModule
  let : IsMulCommutative (frattini ↥(X ⊔ T)) :=
    IsMulCommutative.of_comm hXTEA.comm
  let : CommGroup (frattini ↥(X ⊔ T)) := inferInstance
  let : Module (ZMod 2) (Additive (frattini ↥(X ⊔ T))) :=
    hXTEA.zmodModule
  let : IsMulCommutative (frattini ↥(Z ⊔ T)) :=
    IsMulCommutative.of_comm hZTEA.comm
  let : CommGroup (frattini ↥(Z ⊔ T)) := inferInstance
  let : Module (ZMod 2) (Additive (frattini ↥(Z ⊔ T))) :=
    hZTEA.zmodModule
  intro xz xt zt hthetaX hthetaZ hthetaT hcoincidence
  rcases
      pairwise_parameterCoincidence_refines_to_aligned_or_allEqualNontrivial
        hcoincidence with
    ⟨hxz, hunique⟩ | ⟨hxt, hunique⟩ |
      ⟨hzt, hunique⟩ | ⟨hxz, hzt, hxOne⟩
  · apply Or.inl
    refine ⟨?_, hthetaT, ?_⟩
    · exact hthetaX.symm.trans (hxz.trans hthetaZ)
    rcases hunique with hxOne | hxtNe
    · exact Or.inl (hthetaX.symm.trans hxOne)
    · exact Or.inr fun h =>
        hxtNe (hthetaX.trans h)
  · apply Or.inr
    apply Or.inl
    exact ⟨hxt.trans hthetaT, hthetaZ,
      hunique⟩
  · apply Or.inr
    apply Or.inr
    apply Or.inl
    exact ⟨hzt, hthetaX, hunique⟩
  · exact Or.inr (Or.inr (Or.inr
      ⟨hxz, hzt, hxOne⟩))


end

end OddOrder.Higman.Suzuki2Groups
