/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleEigenweights

/-!
# Higman's Lemma 13: transport of the restricted zeroth layer

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, pp. 92–93.

The exponent-four branch studies complementary factors inside a restricted
subgroup and compares their Singer coordinates with the ambient group.  This
file constructs the natural map from the restricted zeroth lower-central layer
to the ambient zeroth layer, together with its actor equivariance.  No
injectivity is asserted: in the intended application the left factor is killed
and only the right factor survives in the ambient layer.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

local instance restrictedLayerZeroIsMulCommutative
    (H : Type uP) [Group H] (i : Nat) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

noncomputable local instance restrictedLayerZeroZModTwoModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- Inclusion of the zeroth lower-central term of a subgroup into the
zeroth lower-central term of the ambient group. -/
def subgroupLowerCentralTermZeroHom
    {P : Type uP} [Group P] (S : Subgroup P) :
    lowerCentralTerm S 0 →* lowerCentralTerm P 0 :=
  ambientTermZeroHom
    (S.subtype.comp (lowerCentralTerm S 0).subtype)

/-- Naturality of the zeroth lower-central-layer denominator under subgroup
inclusion. -/
theorem subgroupLowerCentralLayerKernelZero_le_comap
    {P : Type uP} [Group P] (S : Subgroup P) :
    lowerCentralLayerKernel S 0 ≤
      (lowerCentralLayerKernel P 0).comap
        (subgroupLowerCentralTermZeroHom S) := by
  change
    (Agemo (lowerCentralTerm S 0) 2 1 ⊔
        (lowerCentralTerm S 1).subgroupOf (lowerCentralTerm S 0)) ≤ _
  apply sup_le
  · rw [Agemo, Subgroup.closure_le]
    rintro x ⟨y, rfl⟩
    change subgroupLowerCentralTermZeroHom S (y ^ (2 ^ 1)) ∈
      lowerCentralLayerKernel P 0
    simpa only [map_pow, pow_one] using
      sq_mem_lowerCentralLayerKernel P 0
        (subgroupLowerCentralTermZeroHom S y)
  · intro x hx
    change subgroupLowerCentralTermZeroHom S x ∈
      lowerCentralLayerKernel P 0
    rw [← lowerCentralLayerKernelInAmbient_subgroupOf P 0,
      Subgroup.mem_subgroupOf]
    apply lowerCentralTerm_succ_le_layerKernelInAmbient P 0
    rw [Subgroup.mem_subgroupOf] at hx
    have hxmap :
        S.subtype ((lowerCentralTerm S 0).subtype x) ∈
          (lowerCentralTerm S 1).map S.subtype :=
      Subgroup.mem_map_of_mem S.subtype hx
    have hle :
        (lowerCentralTerm S 1).map S.subtype ≤
          lowerCentralTerm P 1 := by
      change
        ((⊤ : Subgroup S).lowerCentralSeries 1).map S.subtype ≤
          (⊤ : Subgroup P).lowerCentralSeries 1
      rw [Subgroup.top_subtype_lowerCentralSeries]
      exact Subgroup.lowerCentralSeries_mono 1 le_top
    exact hle hxmap

/-- The natural map `L₀(S) → L₀(P)` induced by subgroup inclusion. -/
def subgroupLowerCentralLayerZeroHom
    {P : Type uP} [Group P] (S : Subgroup P) :
    lowerCentralLayer S 0 →* lowerCentralLayer P 0 :=
  QuotientGroup.map
    (lowerCentralLayerKernel S 0)
    (lowerCentralLayerKernel P 0)
    (subgroupLowerCentralTermZeroHom S)
    (subgroupLowerCentralLayerKernelZero_le_comap S)

/-- Linear form of the natural map `L₀(S) → L₀(P)`. -/
noncomputable def subgroupLowerCentralLayerZeroLinear
    {P : Type uP} [Group P] (S : Subgroup P) :
    Additive (lowerCentralLayer S 0) →ₗ[ZMod 2]
      Additive (lowerCentralLayer P 0) :=
  { MonoidHom.toAdditive (subgroupLowerCentralLayerZeroHom S) with
    map_smul' := ZMod.map_smul
      (MonoidHom.toAdditive (subgroupLowerCentralLayerZeroHom S)) }

@[simp]
theorem subgroupLowerCentralLayerZeroLinear_mk
    {P : Type uP} [Group P] (S : Subgroup P)
    (x : lowerCentralTerm S 0) :
    subgroupLowerCentralLayerZeroLinear S
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel S 0) x)) =
      Additive.ofMul
        (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
          (subgroupLowerCentralTermZeroHom S x)) := rfl

/-- The natural map from a restricted subgroup layer to the ambient layer
intertwines the restricted and ambient actor representations. -/
theorem subgroupLowerCentralLayerZeroLinear_equivariant
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)} {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S) (c : Y)
    (v : Additive (lowerCentralLayer S 0)) :
    subgroupLowerCentralLayerZeroLinear S
        (lowerCentralLayerRepresentation hSinv.restrict 0 c v) =
      lowerCentralLayerRepresentation Y.subtype 0 c
        (subgroupLowerCentralLayerZeroLinear S v) := by
  obtain ⟨g, hg⟩ :=
    QuotientGroup.mk'_surjective
      (lowerCentralLayerKernel S 0) v.toMul
  have hv :
      Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel S 0) g) = v := by
    rw [hg]
    rfl
  rw [← hv, lowerCentralLayerRepresentation_apply,
    lowerCentralLayerAction_apply_mk,
    subgroupLowerCentralLayerZeroLinear_mk,
    subgroupLowerCentralLayerZeroLinear_mk,
    lowerCentralLayerRepresentation_apply,
    lowerCentralLayerAction_apply_mk]
  apply congrArg Additive.ofMul
  apply congrArg (QuotientGroup.mk' (lowerCentralLayerKernel P 0))
  apply Subtype.ext
  change S.subtype
      ((lowerCentralTerm S 0).subtype
        (lowerCentralTermAction hSinv.restrict 0 c g)) =
    (Y.subtype c : MulAut P)
      (S.subtype ((lowerCentralTerm S 0).subtype g))
  rw [show (lowerCentralTerm S 0).subtype
      (lowerCentralTermAction hSinv.restrict 0 c g) =
        (hSinv.restrict c) ((lowerCentralTerm S 0).subtype g) from
    IsAInvariant.restrict_apply_val
      (IsAInvariant.lowerCentralSeries hSinv.restrict 0) c g]
  exact IsAInvariant.restrict_apply_val hSinv c _

end OddOrder.Higman.Suzuki2Groups
