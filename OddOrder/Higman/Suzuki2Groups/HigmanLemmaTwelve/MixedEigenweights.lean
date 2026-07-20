/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.BilinearEigenweight
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.PrescribedFactorCoordinates

/-!
# Higman's Lemma 12: the mixed weight equation

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
p. 90.

Once conjugate bases `x₀, …, x_{n-1}` for `X/Φ(G)`, `y₀, …, y_{n-1}` for
`Y/Φ(G)` and `v₀, …, v_{n-1}` for `Φ(G)` are fixed, the description of `G` is
completed by the mixed products `[xᵢ, yⱼ]`.  Higman's two facts about them are

* they cannot all vanish, since `X` and `Y` would then commute elementwise;
* `[xᵢ, yⱼ]` can be nonzero only if `λ^(2^i) μ^(2^j)` is an eigenvalue of the
  actor on `Φ(G)`.

This leaf establishes both in the actual objects.  The two invariant factors
carry different natural quotients (an Agemo quotient in the commutative branch,
a lower-central layer in the noncommutative one), so their coordinates are
pushed into the common ambient zeroth layer `P/Φ(P)`, where the actual
lower-central bracket already provides the pairing and its nonzero mixed
witness.  The resulting weight equation `λ^(2^i) μ^(2^j) = ν^(2^k)` is exactly
the input to Higman's B/C/D case analysis; no case is opened here.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.RepresentationTheory
open OddOrder.Isaacs.Ch03
open Module
open scoped IsMulCommutative TensorProduct BigOperators

universe uP uG uF uQ

noncomputable section

local instance mixedEigenweightLayerCommGroup
    (H : Type uP) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

local instance mixedEigenweightLayerModule
    (H : Type uP) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-! ## The ambient centre as the second lower-central layer -/

variable {P : Type uP} [Group P]

/-- Group-level identification of the ambient second lower-central layer with
the ambient Frattini subgroup.

This is the ambient sibling of `factorLayerOneEquivAmbientFrattini`: there the
factor's layer is compared with the *ambient* Frattini subgroup, here the
ambient layer is, so no `subgroupOf` correction occurs. -/
def ambientLayerOneEquivFrattini
    (hK1 : lowerCentralLayerKernel P 1 = ⊥)
    (hterm : lowerCentralTerm P 1 = frattini P) :
    lowerCentralLayer P 1 ≃* frattini P :=
  (QuotientGroup.quotientMulEquivOfEq hK1).trans
    (QuotientGroup.quotientBot.trans (MulEquiv.subgroupCongr hterm))

/-- Linear form of the ambient layer-to-Frattini identification. -/
def ambientLayerOneLinearEquivFrattini
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hK1 : lowerCentralLayerKernel P 1 = ⊥)
    (hterm : lowerCentralTerm P 1 = frattini P) :
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) :=
      hEA.zmodModule
    Additive (lowerCentralLayer P 1) ≃ₗ[ZMod 2]
      Additive ↑(frattini P) := by
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : CommGroup ↑(frattini P) := inferInstance
  letI : Module (ZMod 2) (Additive ↑(frattini P)) :=
    hEA.zmodModule
  exact (MulEquiv.toAdditive
      (ambientLayerOneEquivFrattini hK1 hterm)).toLinearEquiv
    (fun c x => ZMod.map_smul
      (MulEquiv.toAdditive
        (ambientLayerOneEquivFrattini hK1 hterm)).toAddMonoidHom c x)

/-- The ambient layer-to-Frattini identification intertwines the layer action
with the actual Frattini action. -/
theorem ambientLayerOneLinearEquivFrattini_equivariant
    {Y : Subgroup (MulAut P)}
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hK1 : lowerCentralLayerKernel P 1 = ⊥)
    (hterm : lowerCentralTerm P 1 = frattini P) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) :=
      hEA.zmodModule
    ∀ (g : Y) (v : Additive (lowerCentralLayer P 1)),
      ambientLayerOneLinearEquivFrattini hEA hK1 hterm
          (lowerCentralLayerRepresentation Y.subtype 1 g v) =
        elabRepresentation 2 hPhiInv.restrict g
          (ambientLayerOneLinearEquivFrattini hEA hK1 hterm v) := by
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : CommGroup ↑(frattini P) := inferInstance
  letI : Module (ZMod 2) (Additive ↑(frattini P)) :=
    hEA.zmodModule
  intro g v
  change ambientLayerOneLinearEquivFrattini hEA hK1 hterm
        (lowerCentralLayerRepresentation Y.subtype 1 g
          (Additive.ofMul v.toMul)) =
      elabRepresentation 2 hPhiInv.restrict g
        (ambientLayerOneLinearEquivFrattini hEA hK1 hterm
          (Additive.ofMul v.toMul))
  rw [lowerCentralLayerRepresentation_apply]
  change Additive.ofMul
        (ambientLayerOneEquivFrattini hK1 hterm
          (lowerCentralLayerAction Y.subtype 1 g v.toMul)) =
      elabRepresentation 2 hPhiInv.restrict g
        (Additive.ofMul
          (ambientLayerOneEquivFrattini hK1 hterm v.toMul))
  rw [elabRepresentation_apply]
  apply Additive.ofMul.injective
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel P 1) v.toMul
  rw [← hx, lowerCentralLayerAction_apply_mk]
  apply Subtype.ext
  exact IsAInvariant.restrict_apply_val
    (IsAInvariant.lowerCentralSeries Y.subtype 1) g x

/-- The ambient centre coordinate: identify the second lower-central layer
`L₁ = Φ(P)` with the Singer field `GF(2, n)`. -/
def ambientCenterCoordinate {n : ℕ}
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hK1 : lowerCentralLayerKernel P 1 = ⊥)
    (hterm : lowerCentralTerm P 1 = frattini P)
    (ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n) :
    Additive (lowerCentralLayer P 1) ≃ₗ[ZMod 2] GaloisField 2 n :=
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  (ambientLayerOneLinearEquivFrattini hEA hK1 hterm).trans ePhi

/-- In the ambient centre coordinate, the actor acts as multiplication by the
primitive scalar `ν`. -/
theorem ambientCenterCoordinate_compat {Y : Subgroup (MulAut P)} {n : ℕ}
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hK1 : lowerCentralLayerKernel P 1 = ⊥)
    (hterm : lowerCentralTerm P 1 = frattini P)
    (ePhi :
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (c : Y) (nu : GaloisField 2 n)
    (hconj :
      let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
        IsAInvariant.of_characteristic Y.subtype
      letI : IsMulCommutative ↑(frattini P) :=
        IsMulCommutative.of_comm hEA.comm
      letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
      ePhi.conj (elabRepresentation 2 hPhiInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu)
    (v : Additive (lowerCentralLayer P 1)) :
    ambientCenterCoordinate hEA hK1 hterm ePhi
        (lowerCentralLayerRepresentation Y.subtype 1 c v) =
      nu * ambientCenterCoordinate hEA hK1 hterm ePhi v := by
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) := hEA.zmodModule
  have hcompatPhi : ∀ w,
      ePhi (elabRepresentation 2 hPhiInv.restrict c w) = nu * ePhi w := by
    intro w
    have h := DFunLike.congr_fun hconj (ePhi w)
    simpa [LinearEquiv.conj_apply] using h
  change ePhi
      (ambientLayerOneLinearEquivFrattini hEA hK1 hterm
        (lowerCentralLayerRepresentation Y.subtype 1 c v)) =
    nu * ePhi
      (ambientLayerOneLinearEquivFrattini hEA hK1 hterm v)
  rw [ambientLayerOneLinearEquivFrattini_equivariant hEA hK1 hterm c v]
  exact hcompatPhi _

/-! ## Factor quotients inside the ambient zeroth layer -/

/-- Any group mapping to `P` maps to the zeroth lower-central term, which is
the whole group. -/
def ambientTermZeroHom {G : Type uG} [Group G] (f : G →* P) :
    G →* ↥(lowerCentralTerm P 0) where
  toFun g := ⟨f g, by simp [lowerCentralTerm]⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' g h := Subtype.ext (map_mul f g h)

/-- The class of a zeroth-term element in the zeroth lower-central layer. -/
def layerZeroClass (x : ↥(lowerCentralTerm P 0)) :
    Additive (lowerCentralLayer P 0) :=
  Additive.ofMul (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x)

/-- Push a quotient of a group mapped into `P` into the ambient zeroth
lower-central layer.

Both invariant factors of Higman's Lemma 12 arrive this way: the commutative
branch as `S ⧸ ℧₁(S)` and the noncommutative branch as the factor's own zeroth
lower-central layer.  Only the denominator's image in `Φ(P)` is needed. -/
def quotientToAmbientLayerZero
    {G : Type uG} [Group G] (f : G →* P) {N : Subgroup G} [N.Normal]
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (hf : ∀ g ∈ N, f g ∈ frattini P) :
    (G ⧸ N) →* lowerCentralLayer P 0 :=
  QuotientGroup.lift N
    ((QuotientGroup.mk' (lowerCentralLayerKernel P 0)).comp
      (ambientTermZeroHom f)) (by
        intro g hg
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff, hK0]
        exact Subgroup.mem_subgroupOf.mpr (hf g hg))

@[simp]
theorem quotientToAmbientLayerZero_mk
    {G : Type uG} [Group G] (f : G →* P) {N : Subgroup G} [N.Normal]
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (hf : ∀ g ∈ N, f g ∈ frattini P) (g : G) :
    quotientToAmbientLayerZero f hK0 hf (QuotientGroup.mk' N g) =
      QuotientGroup.mk' (lowerCentralLayerKernel P 0)
        (ambientTermZeroHom f g) := rfl

/-- Linear form of the factor-to-ambient map on zeroth layers. -/
def quotientToAmbientLayerZeroLinear
    {G : Type uG} [Group G] (f : G →* P) {N : Subgroup G} [N.Normal]
    [IsMulCommutative (G ⧸ N)]
    [Module (ZMod 2) (Additive (G ⧸ N))]
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (hf : ∀ g ∈ N, f g ∈ frattini P) :
    Additive (G ⧸ N) →ₗ[ZMod 2] Additive (lowerCentralLayer P 0) :=
  { MonoidHom.toAdditive (quotientToAmbientLayerZero f hK0 hf) with
    map_smul' := ZMod.map_smul
      (MonoidHom.toAdditive (quotientToAmbientLayerZero f hK0 hf)) }

@[simp]
theorem quotientToAmbientLayerZeroLinear_mk
    {G : Type uG} [Group G] (f : G →* P) {N : Subgroup G} [N.Normal]
    [IsMulCommutative (G ⧸ N)]
    [Module (ZMod 2) (Additive (G ⧸ N))]
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (hf : ∀ g ∈ N, f g ∈ frattini P) (g : G) :
    quotientToAmbientLayerZeroLinear f hK0 hf
        (Additive.ofMul (QuotientGroup.mk' N g)) =
      layerZeroClass (ambientTermZeroHom f g) := rfl

/-- **Equivariance of the factor-to-ambient zeroth-layer map.**

If a factor quotient action `qAct` is represented on group elements by `sigma`,
and the inclusion `f` intertwines `sigma` with the ambient action of `a`, then
`quotientToAmbientLayerZero` intertwines the factor action with the ambient
zeroth-layer action.  This is the naturality of “act then include = include
then act”, which holds because the factor action is the restriction of the
ambient action. -/
theorem quotientToAmbientLayerZero_equivariant
    {G : Type uG} [Group G] (f : G →* P) {N : Subgroup G} [N.Normal]
    {Y : Subgroup (MulAut P)} (a : Y)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (hf : ∀ g ∈ N, f g ∈ frattini P)
    (qAct : G ⧸ N → G ⧸ N) (sigma : G → G)
    (hqAct : ∀ g, qAct (QuotientGroup.mk' N g) =
      QuotientGroup.mk' N (sigma g))
    (hf_int : ∀ g, f (sigma g) = (Y.subtype a : MulAut P) (f g))
    (q : G ⧸ N) :
    quotientToAmbientLayerZero f hK0 hf (qAct q) =
      lowerCentralLayerAction Y.subtype 0 a
        (quotientToAmbientLayerZero f hK0 hf q) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  rw [hqAct, quotientToAmbientLayerZero_mk, quotientToAmbientLayerZero_mk,
    lowerCentralLayerAction_apply_mk]
  apply congrArg (QuotientGroup.mk' (lowerCentralLayerKernel P 0))
  apply Subtype.ext
  change f (sigma g) = (Y.subtype a : MulAut P) (f g)
  exact hf_int g

/-- Linear form of the equivariance, for representations induced from the
factor and ambient actions. -/
theorem quotientToAmbientLayerZeroLinear_equivariant
    {G : Type uG} [Group G] (f : G →* P) {N : Subgroup G} [N.Normal]
    [IsMulCommutative (G ⧸ N)]
    [Module (ZMod 2) (Additive (G ⧸ N))]
    {Y : Subgroup (MulAut P)} (a : Y)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (hf : ∀ g ∈ N, f g ∈ frattini P)
    (fRep : Additive (G ⧸ N) →ₗ[ZMod 2] Additive (G ⧸ N))
    (sigma : G → G)
    (hfRep : ∀ g, fRep (Additive.ofMul (QuotientGroup.mk' N g)) =
      Additive.ofMul (QuotientGroup.mk' N (sigma g)))
    (hf_int : ∀ g, f (sigma g) = (Y.subtype a : MulAut P) (f g))
    (v : Additive (G ⧸ N)) :
    quotientToAmbientLayerZeroLinear f hK0 hf (fRep v) =
      lowerCentralLayerRepresentation Y.subtype 0 a
        (quotientToAmbientLayerZeroLinear f hK0 hf v) := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N v.toMul
  have hv : Additive.ofMul (QuotientGroup.mk' N g) = v := by
    rw [hg]; rfl
  rw [← hv, hfRep, quotientToAmbientLayerZeroLinear_mk,
    quotientToAmbientLayerZeroLinear_mk]
  change layerZeroClass (ambientTermZeroHom f (sigma g)) =
    lowerCentralLayerRepresentation Y.subtype 0 a
      (Additive.ofMul (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
        (ambientTermZeroHom f g)))
  rw [lowerCentralLayerRepresentation_apply, lowerCentralLayerAction_apply_mk]
  apply congrArg Additive.ofMul
  apply congrArg (QuotientGroup.mk' (lowerCentralLayerKernel P 0))
  apply Subtype.ext
  change f (sigma g) = (Y.subtype a : MulAut P) (f g)
  exact hf_int g

/-! ## The base-changed eigenvector family of one factor -/

section EigenFamily

variable {F : Type uF} [Field F] [Finite F] [Algebra (ZMod 2) F]
variable {Q : Type uQ} [AddCommGroup Q] [Module (ZMod 2) Q]
variable {Y : Subgroup (MulAut P)}

/-- The base-changed eigenvector family of one invariant factor, living in the
common ambient module `F ⊗ (P/Φ(P))`.  Each conjugate basis vector of the
factor's quotient coordinate `eQuot` is transported by the equivariant
inclusion `iota` into `P/Φ(P)`. -/
noncomputable def factorAmbientEigenFamily
    (eQuot : Q ≃ₗ[ZMod 2] F)
    (iota : Q →ₗ[ZMod 2] Additive (lowerCentralLayer P 0)) :
    Fin (Module.finrank (ZMod 2) F) →
      F ⊗[ZMod 2] Additive (lowerCentralLayer P 0) :=
  fun i => iota.baseChange F (conjugateTensorBasisOfLinearEquiv F eQuot i)

/-- Each family member is an eigenvector of the base-changed ambient actor with
the Frobenius-power eigenvalue `λ^(2^i)`. -/
theorem factorAmbientEigenFamily_eigen
    (c : Y) (eQuot : Q ≃ₗ[ZMod 2] F)
    (Aq : Module.End (ZMod 2) Q) (lambda : F)
    (hAq : ∀ v, eQuot (Aq v) = lambda * eQuot v)
    (iota : Q →ₗ[ZMod 2] Additive (lowerCentralLayer P 0))
    (hiota : ∀ v, iota (Aq v) =
      lowerCentralLayerRepresentation Y.subtype 0 c (iota v))
    (i : Fin (Module.finrank (ZMod 2) F)) :
    (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange F
        (factorAmbientEigenFamily eQuot iota i) =
      lambda ^ (2 ^ i.val) • factorAmbientEigenFamily eQuot iota i := by
  have hcomp : (lowerCentralLayerRepresentation Y.subtype 0 c) ∘ₗ iota =
      iota ∘ₗ Aq :=
    LinearMap.ext fun v => (hiota v).symm
  have hbc : (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange F ∘ₗ
        iota.baseChange F =
      iota.baseChange F ∘ₗ Aq.baseChange F := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hcomp]
  show (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange F
      (iota.baseChange F (conjugateTensorBasisOfLinearEquiv F eQuot i)) = _
  rw [show (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange F
        (iota.baseChange F (conjugateTensorBasisOfLinearEquiv F eQuot i)) =
      iota.baseChange F (Aq.baseChange F
        (conjugateTensorBasisOfLinearEquiv F eQuot i)) from
    congrFun (congrArg DFunLike.coe hbc)
      (conjugateTensorBasisOfLinearEquiv F eQuot i),
    baseChange_eigen_conjugateTensorBasisOfLinearEquiv F eQuot Aq lambda hAq i,
    map_smul]
  rfl

/-- The span of the family contains every ground vector coming from the factor
image, i.e. `1 ⊗ iota v` for any `v`. -/
theorem one_tmul_mem_span_factorAmbientEigenFamily
    (eQuot : Q ≃ₗ[ZMod 2] F)
    (iota : Q →ₗ[ZMod 2] Additive (lowerCentralLayer P 0))
    (v : Q) :
    (1 : F) ⊗ₜ[ZMod 2] iota v ∈
      Submodule.span F (Set.range (factorAmbientEigenFamily eQuot iota)) := by
  have hrange : Set.range (factorAmbientEigenFamily eQuot iota) =
      iota.baseChange F ''
        Set.range (conjugateTensorBasisOfLinearEquiv F eQuot) :=
    Set.range_comp (iota.baseChange F)
      (conjugateTensorBasisOfLinearEquiv F eQuot)
  rw [hrange]
  have hmem : (1 : F) ⊗ₜ[ZMod 2] v ∈
      Submodule.span F
        (Set.range (conjugateTensorBasisOfLinearEquiv F eQuot)) := by
    rw [(conjugateTensorBasisOfLinearEquiv F eQuot).span_eq]
    exact Submodule.mem_top
  have := Submodule.apply_mem_span_image_of_mem_span
    (iota.baseChange F) hmem
  rwa [LinearMap.baseChange_tmul] at this

/-- A ground tensor `1 ⊗ w` is nonzero whenever `w` is, read off the nonzero
Frobenius coordinate in the conjugate basis. -/
theorem one_tmul_ne_zero_of_ne_zero
    (e : Q ≃ₗ[ZMod 2] F) {w : Q} (hw : w ≠ 0) :
    (1 : F) ⊗ₜ[ZMod 2] w ≠ 0 := by
  intro h0
  have hsum :
      ∑ i : Fin (Module.finrank (ZMod 2) F),
          (e w) ^ (2 ^ i.val) • conjugateTensorBasisOfLinearEquiv F e i = 0 := by
    rw [← one_tmul_eq_sum_conjugateTensorBasisOfLinearEquiv F e w]; exact h0
  have hcoeff := Fintype.linearIndependent_iff.mp
    (conjugateTensorBasisOfLinearEquiv F e).linearIndependent
    (fun i => (e w) ^ (2 ^ i.val)) hsum
  have hpos : 0 < Module.finrank (ZMod 2) F := Module.finrank_pos
  have hi := hcoeff ⟨0, hpos⟩
  simp only [Fin.val_mk, pow_zero, pow_one] at hi
  exact hw (e.injective (by rw [hi, map_zero]))

/-- The base-changed ambient bracket is nonzero on `1 ⊗ a`, `1 ⊗ b` whenever
the actual bracket of `a`, `b` is nonzero. -/
theorem lowerCentralCommutatorBilinearBaseChange_one_tmul_ne_zero
    (a b : Additive (lowerCentralLayer P 0))
    (e : Additive (lowerCentralLayer P 1) ≃ₗ[ZMod 2] F)
    (hab : lowerCentralCommutatorBilinear P a b ≠ 0) :
    lowerCentralCommutatorBilinearBaseChange F P
        ((1 : F) ⊗ₜ[ZMod 2] a) ((1 : F) ⊗ₜ[ZMod 2] b) ≠ 0 := by
  have hval : lowerCentralCommutatorBilinearBaseChange F P
        ((1 : F) ⊗ₜ[ZMod 2] a) ((1 : F) ⊗ₜ[ZMod 2] b) =
      (1 : F) ⊗ₜ[ZMod 2] lowerCentralCommutatorBilinear P a b := by
    unfold lowerCentralCommutatorBilinearBaseChange
    rw [LinearMap.BilinMap.baseChange_tmul, one_mul]
  rw [hval]
  exact one_tmul_ne_zero_of_ne_zero e hab

end EigenFamily

end

end OddOrder.Higman.Suzuki2Groups
