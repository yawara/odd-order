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

local instance mixedEigenweightLayerIsMulComm
    (H : Type uP) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

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

/-- Assemble one factor's base-changed eigenvector family from the uniform data
shared by both branches: an equivariant inclusion `iota` built from a group map
`f : G → P` whose denominator `N` lands in `Φ(P)`, a factor quotient coordinate
`eQuot`, and its actor `Aq`.  The family lies in the common ambient module and
its span covers every ground vector of the factor. -/
theorem factorFamily_of_iota_data
    {G : Type uG} [Group G] (f : G →* P) {N : Subgroup G} [N.Normal]
    [IsMulCommutative (G ⧸ N)] [Module (ZMod 2) (Additive (G ⧸ N))]
    (c : Y)
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (hf : ∀ g ∈ N, f g ∈ frattini P)
    (eQuot : Additive (G ⧸ N) ≃ₗ[ZMod 2] F)
    (Aq : Module.End (ZMod 2) (Additive (G ⧸ N))) (lambda : F)
    (hAq : ∀ v, eQuot (Aq v) = lambda * eQuot v)
    (sigma : G → G)
    (hfRep : ∀ g, Aq (Additive.ofMul (QuotientGroup.mk' N g)) =
      Additive.ofMul (QuotientGroup.mk' N (sigma g)))
    (hf_int : ∀ g, f (sigma g) = (Y.subtype c : MulAut P) (f g))
    {S : Subgroup P} (hSrange : ∀ x : P, x ∈ S → ∃ g : G, f g = x) :
    ∃ family : Fin (Module.finrank (ZMod 2) F) →
        F ⊗[ZMod 2] Additive (lowerCentralLayer P 0),
      (∀ i, (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange F
          (family i) = lambda ^ (2 ^ i.val) • family i) ∧
      (∀ x : lowerCentralTerm P 0, (x : P) ∈ S →
        (1 : F) ⊗ₜ[ZMod 2] layerZeroClass x ∈
          Submodule.span F (Set.range family)) := by
  set iota := quotientToAmbientLayerZeroLinear f hK0 hf with hiotaDef
  have hiota : ∀ v, iota (Aq v) =
      lowerCentralLayerRepresentation Y.subtype 0 c (iota v) :=
    quotientToAmbientLayerZeroLinear_equivariant f c hK0 hf Aq sigma hfRep hf_int
  refine ⟨factorAmbientEigenFamily eQuot iota, ?_, ?_⟩
  · intro i
    exact factorAmbientEigenFamily_eigen c eQuot Aq lambda hAq iota hiota i
  · intro x hx
    obtain ⟨g, hg⟩ := hSrange (x : P) hx
    have hv : iota (Additive.ofMul (QuotientGroup.mk' N g)) = layerZeroClass x := by
      rw [hiotaDef, quotientToAmbientLayerZeroLinear_mk]
      exact congrArg layerZeroClass (Subtype.ext hg)
    rw [← hv]
    exact one_tmul_mem_span_factorAmbientEigenFamily eQuot iota _

/-- The noncommutative factor branch supplies its base-changed eigenvector
family in the common ambient module. -/
theorem exists_factorFamily_of_noncommutative
    {S : Subgroup P} {hSinv : IsAInvariant Y.subtype S} {hPhiS : frattini P ≤ S}
    (c : Y) {n : ℕ}
    [IsMulCommutative ↑(frattini P)] [Module (ZMod 2) (Additive ↑(frattini P))]
    {ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (data : NoncommutativeFactorCoordinateData hSinv hPhiS c ePhi nu) :
    ∃ family : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)) →
        GaloisField 2 n ⊗[ZMod 2] Additive (lowerCentralLayer P 0),
      (∀ i, (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (family i) =
          data.lambda ^ (2 ^ i.val) • family i) ∧
      (∀ x : lowerCentralTerm P 0, (x : P) ∈ S →
        (1 : GaloisField 2 n) ⊗ₜ[ZMod 2] layerZeroClass x ∈
          Submodule.span (GaloisField 2 n) (Set.range family)) := by
  let f : ↥(lowerCentralTerm (↥S) 0) →* P :=
    S.subtype.comp (lowerCentralTerm (↥S) 0).subtype
  have hf : ∀ g ∈ lowerCentralLayerKernel (↥S) 0, f g ∈ frattini P := by
    intro g hg
    rw [lowerCentralLayerKernel_zero_eq_of_squares_le (↥S) data.hSq,
      Subgroup.mem_subgroupOf, data.hterm, Subgroup.mem_subgroupOf] at hg
    exact hg
  refine factorFamily_of_iota_data f c hK0 hf data.eQuot
    (lowerCentralLayerRepresentation hSinv.restrict 0 c) data.lambda
    data.quotient_compatible
    (fun g => lowerCentralTermAction hSinv.restrict 0 c g) ?_ ?_ ?_
  · intro g
    rw [lowerCentralLayerRepresentation_apply, lowerCentralLayerAction_apply_mk]
  · intro g
    show S.subtype ((lowerCentralTerm (↥S) 0).subtype
        (lowerCentralTermAction hSinv.restrict 0 c g)) =
      (Y.subtype c : MulAut P) (S.subtype ((lowerCentralTerm (↥S) 0).subtype g))
    rw [show (lowerCentralTerm (↥S) 0).subtype
        (lowerCentralTermAction hSinv.restrict 0 c g) =
        (hSinv.restrict c) ((lowerCentralTerm (↥S) 0).subtype g) from
      IsAInvariant.restrict_apply_val
        (IsAInvariant.lowerCentralSeries hSinv.restrict 0) c g]
    exact IsAInvariant.restrict_apply_val hSinv c _
  · intro x hx
    exact ⟨⟨⟨x, hx⟩, by simp [lowerCentralTerm]⟩, rfl⟩

/-- The commutative factor branch supplies its base-changed eigenvector family
in the common ambient module.  The Agemo quotient carries the canonical
`F₂`-module structure and its actor is the induced quotient automorphism. -/
theorem exists_factorFamily_of_commutative [Finite P]
    {S : Subgroup P} {hSinv : IsAInvariant Y.subtype S} {hPhiS : frattini P ≤ S}
    (c : Y) {n : ℕ}
    [IsMulCommutative ↑(frattini P)] [Module (ZMod 2) (Additive ↑(frattini P))]
    {ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (data : CommutativeFactorCoordinateData hSinv hPhiS c ePhi nu) :
    ∃ family : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)) →
        GaloisField 2 n ⊗[ZMod 2] Additive (lowerCentralLayer P 0),
      (∀ i, (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (family i) =
          data.lambda ^ (2 ^ i.val) • family i) ∧
      (∀ x : lowerCentralTerm P 0, (x : P) ∈ S →
        (1 : GaloisField 2 n) ⊗ₜ[ZMod 2] layerZeroClass x ∈
          Submodule.span (GaloisField 2 n) (Set.range family)) := by
  letI : CommGroup ↥S :=
    { (inferInstance : Group ↥S) with mul_comm := data.hcomm.is_comm.comm }
  letI : IsMulCommutative (↥S ⧸ Agemo (↥S) 2 1) :=
    IsMulCommutative.of_comm mul_comm
  have h2 : ∀ q : Additive (↥S ⧸ Agemo (↥S) 2 1), 2 • q = 0 := by
    intro q
    apply Additive.toMul.injective
    change (Additive.toMul q) ^ 2 = 1
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
    rw [← hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    simpa using Agemo.mem_of_eq_pow (G := ↥S) (p := 2) (n := 1) x
  letI : Module (ZMod 2) (Additive (↥S ⧸ Agemo (↥S) 2 1)) :=
    AddCommGroup.zmodModule h2
  let eQuotLin : Additive (↥S ⧸ Agemo (↥S) 2 1) ≃ₗ[ZMod 2] GaloisField 2 n :=
    { data.eQuot with
      map_smul' := ZMod.map_smul data.eQuot.toAddMonoidHom }
  let Aqmul : ↥S ⧸ Agemo (↥S) 2 1 ≃* ↥S ⧸ Agemo (↥S) 2 1 :=
    (IsAInvariant.of_characteristic hSinv.restrict).quotientMulAutHom c
  let Aq : Additive (↥S ⧸ Agemo (↥S) 2 1) →ₗ[ZMod 2]
      Additive (↥S ⧸ Agemo (↥S) 2 1) :=
    { (MulEquiv.toAdditive Aqmul).toAddMonoidHom with
      map_smul' := fun z x => ZMod.map_smul (MulEquiv.toAdditive Aqmul).toAddMonoidHom z x }
  refine factorFamily_of_iota_data S.subtype c hK0 ?_ eQuotLin Aq data.lambda ?_
    (fun g => (hSinv.restrict c) g) ?_ ?_ ?_
  · intro g hg
    rw [data.hN, Subgroup.mem_subgroupOf] at hg
    exact hg
  · intro v
    exact data.quotient_compatible v
  · intro g
    exact congrArg Additive.ofMul
      ((IsAInvariant.of_characteristic hSinv.restrict).quotientMulAutHom_apply_mk' c g)
  · intro g
    exact IsAInvariant.restrict_apply_val hSinv c g
  · intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Either factor branch supplies its base-changed eigenvector family. -/
theorem exists_factorFamily [Finite P]
    {S : Subgroup P} {hSinv : IsAInvariant Y.subtype S} {hPhiS : frattini P ≤ S}
    (c : Y) {n : ℕ}
    [IsMulCommutative ↑(frattini P)] [Module (ZMod 2) (Additive ↑(frattini P))]
    {ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (hK0 : lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0))
    (data : FactorCoordinateData hSinv hPhiS c ePhi nu) :
    ∃ family : Fin (Module.finrank (ZMod 2) (GaloisField 2 n)) →
        GaloisField 2 n ⊗[ZMod 2] Additive (lowerCentralLayer P 0),
      (∀ i, (lowerCentralLayerRepresentation Y.subtype 0 c).baseChange
          (GaloisField 2 n) (family i) =
          data.lambda ^ (2 ^ i.val) • family i) ∧
      (∀ x : lowerCentralTerm P 0, (x : P) ∈ S →
        (1 : GaloisField 2 n) ⊗ₜ[ZMod 2] layerZeroClass x ∈
          Submodule.span (GaloisField 2 n) (Set.range family)) := by
  cases data with
  | commutative d =>
      simpa [FactorCoordinateData.lambda] using
        exists_factorFamily_of_commutative c hK0 d
  | noncommutative _ d =>
      simpa [FactorCoordinateData.lambda] using
        exists_factorFamily_of_noncommutative c hK0 d

end EigenFamily

set_option maxHeartbeats 800000 in
/-- **Higman Lemma 12 (p. 90), the mixed weight equation.**

Over the common ambient Singer datum on `Φ(P)`, the actual complementary
factors `X ≅ A(n, θ)`, `Y ≅ A(n, φ)` have a nonzero mixed commutator, and its
Frobenius weight satisfies Higman's displayed relation
`λ^(2^i) μ^(2^j) = ν^(2^k)`.  Together with the two source equations
`ν = λ θ(λ) = μ φ(μ)` this is exactly the state immediately preceding the
B/C/D case split; no case is opened here. -/
theorem exists_mixedFrobeniusWeightEquation_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    let hEA : IsElementaryAbelian 2 ↑(frattini P) :=
      frattini_isElementaryAbelian_of_xiLengthThree
        hP hncomm hmulti hxi hlen hprime
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) :=
      hEA.zmodModule
    let n := Module.finrank (ZMod 2) (Additive ↑(frattini P))
    ∃ (factors : XiLengthThreeTypeAFactorData P Y)
      (c : Y)
      (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
      (nu : GaloisField 2 n)
      (left : FactorCoordinateData
        factors.left_invariant factors.frattini_lt_left.le c ePhi nu)
      (right : FactorCoordinateData
        factors.right_invariant factors.frattini_lt_right.le c ePhi nu)
      (i j k : Fin (Module.finrank (ZMod 2) (GaloisField 2 n))),
      2 ≤ n ∧
      IsPrimitiveRoot nu (2 ^ n - 1) ∧
      nu = left.lambda * left.theta left.lambda ∧
      nu = right.lambda * right.theta right.lambda ∧
      left.lambda ^ (2 ^ i.val) * right.lambda ^ (2 ^ j.val) =
        nu ^ (2 ^ k.val) := by
  classical
  dsimp only
  have hEA : IsElementaryAbelian 2 ↑(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : Module (ZMod 2) (Additive ↑(frattini P)) :=
    hEA.zmodModule
  set n := Module.finrank (ZMod 2) (Additive ↑(frattini P)) with hn
  obtain ⟨factors, c, ePhi, nu, left, right,
      hnTwo, _hcgen, hnuPrim, hconj, hleft, hright⟩ :=
    exists_complementaryFactorCoordinates_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hK0 :=
    lowerCentralLayerKernel_zero_eq_frattini_subgroupOf_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hK1 :=
    lowerCentralLayerKernel_one_eq_bot_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hterm :=
    lowerCentralTerm_one_eq_frattini_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  obtain ⟨famL, hLeigen, hLcov⟩ := exists_factorFamily c hK0 left
  obtain ⟨famR, hReigen, hRcov⟩ := exists_factorFamily c hK0 right
  -- Centre eigenbasis with weights `ν^(2^k)`.
  set eCenter := ambientCenterCoordinate hEA hK1 hterm ePhi with heC
  have hCenterEigen : ∀ k,
      (lowerCentralLayerRepresentation Y.subtype 1 c).baseChange
          (GaloisField 2 n)
          (conjugateTensorBasisOfLinearEquiv (GaloisField 2 n) eCenter k) =
        nu ^ (2 ^ k.val) •
          conjugateTensorBasisOfLinearEquiv (GaloisField 2 n) eCenter k := by
    intro k
    exact baseChange_eigen_conjugateTensorBasisOfLinearEquiv
      (GaloisField 2 n) eCenter
      (lowerCentralLayerRepresentation Y.subtype 1 c) nu
      (ambientCenterCoordinate_compat hEA hK1 hterm ePhi c nu hconj) k
  -- Nonzero mixed commutator witness.
  have hPhiNeBot : frattini P ≠ (⊥ : Subgroup P) := by
    intro hPhiBot
    have hcommBot : _root_.commutator P = ⊥ :=
      le_bot_iff.mp
        ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
          (le_of_eq hPhiBot))
    exact hncomm ((commutator_eq_bot_iff P).mp hcommBot)
  have hinvPhi : involutions P ⊆ frattini P :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive
      (IsAInvariant.of_characteristic Y.subtype) hPhiNeBot
  obtain ⟨x0, y0, hx0L, hy0R, hbne⟩ :=
    factors.exists_mixed_lowerCentralCommutatorBilinear_ne_zero
      hxi hinvPhi hEA hK1
  -- The witness lies in each factor span; the base-changed bracket is nonzero.
  have hbeta_ne :
      lowerCentralCommutatorBilinearBaseChange (GaloisField 2 n) P
          ((1 : GaloisField 2 n) ⊗ₜ[ZMod 2] layerZeroClass x0)
          ((1 : GaloisField 2 n) ⊗ₜ[ZMod 2] layerZeroClass y0) ≠ 0 :=
    lowerCentralCommutatorBilinearBaseChange_one_tmul_ne_zero
      (layerZeroClass x0) (layerZeroClass y0) eCenter hbne
  obtain ⟨i, j, k, _, hweight⟩ :=
    exists_pair_ne_zero_and_weight_eq
      ((lowerCentralLayerRepresentation Y.subtype 0 c).baseChange (GaloisField 2 n))
      ((lowerCentralLayerRepresentation Y.subtype 0 c).baseChange (GaloisField 2 n))
      ((lowerCentralLayerRepresentation Y.subtype 1 c).baseChange (GaloisField 2 n))
      (lowerCentralCommutatorBilinearBaseChange (GaloisField 2 n) P)
      famL famR (conjugateTensorBasisOfLinearEquiv (GaloisField 2 n) eCenter)
      (fun i => left.lambda ^ (2 ^ i.val))
      (fun j => right.lambda ^ (2 ^ j.val))
      (fun k => nu ^ (2 ^ k.val))
      hLeigen hReigen hCenterEigen
      (fun u v =>
        lowerCentralCommutatorBilinearBaseChange_equivariant
          (GaloisField 2 n) Y.subtype c u v)
      (hLcov x0 hx0L) (hRcov y0 hy0R) hbeta_ne
  exact ⟨factors, c, ePhi, nu, left, right, i, j, k,
    hnTwo, hnuPrim, hleft, hright, hweight⟩

end

end OddOrder.Higman.Suzuki2Groups
