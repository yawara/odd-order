/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoFactorQuotientRange

/-!
# Higman Lemma 13: factor geometry in the Frattini quotient

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

Three lifted factors in `P` meet along `Φ(P)`.  Passing to `P / Φ(P)`
therefore turns their relative-intersection identities into directness
identities.  This file records the result first for the actual quotient
subgroups and then for the corresponding `ZMod 2`-submodules used by the
linear range API.

The optional full-geometry versions also retain that the three quotient
factors span the whole Frattini quotient.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03

noncomputable section

universe uP uG

/-- If two subgroups contain the kernel of a quotient map and meet exactly
in that kernel, then their images in the quotient are disjoint. -/
theorem quotient_map_inf_eq_bot_of_inf_eq_kernel
    {G : Type uG} [Group G]
    (N A B : Subgroup G) [N.Normal]
    (hNA : N ≤ A)
    (hNB : N ≤ B)
    (hAB : A ⊓ B = N) :
    A.map (QuotientGroup.mk' N) ⊓
        B.map (QuotientGroup.mk' N) =
      ⊥ := by
  let q := QuotientGroup.mk' N
  apply (QuotientGroup.comapMk'OrderIso N).injective
  apply Subtype.ext
  change Subgroup.comap q
      (A.map q ⊓ B.map q) =
    Subgroup.comap q (⊥ : Subgroup (G ⧸ N))
  rw [Subgroup.comap_inf]
  simp only [q, QuotientGroup.comap_map_mk',
    sup_eq_right.mpr hNA, sup_eq_right.mpr hNB,
    MonoidHom.comap_bot, QuotientGroup.ker_mk', hAB]

/-- **Higman Lemma 13 (p. 93), direct quotient-factor geometry.**

If `X` and `Z` meet in `Φ(P)` and the third factor `T` meets their join in
`Φ(P)`, then the corresponding quotient subgroup images satisfy the two
directness identities used in the exponent-two construction.
-/
theorem frattiniQuotient_factorImages_direct_geometry
    {P : Type uP} [Group P]
    (X Z T : Subgroup P)
    (hPhiX : frattini P ≤ X)
    (hPhiZ : frattini P ≤ Z)
    (hPhiT : frattini P ≤ T)
    (hXZ : X ⊓ Z = frattini P)
    (hXZ_T : (X ⊔ Z) ⊓ T = frattini P) :
    let q := QuotientGroup.mk' (frattini P)
    X.map q ⊓ Z.map q = ⊥ ∧
      (X.map q ⊔ Z.map q) ⊓ T.map q = ⊥ := by
  dsimp only
  let q := QuotientGroup.mk' (frattini P)
  have hFirst :
      X.map q ⊓ Z.map q = ⊥ :=
    quotient_map_inf_eq_bot_of_inf_eq_kernel
      (frattini P) X Z hPhiX hPhiZ hXZ
  have hPhiXZ : frattini P ≤ X ⊔ Z :=
    hPhiX.trans le_sup_left
  have hSecond :
      (X.map q ⊔ Z.map q) ⊓ T.map q = ⊥ := by
    rw [← Subgroup.map_sup]
    exact quotient_map_inf_eq_bot_of_inf_eq_kernel
      (frattini P) (X ⊔ Z) T hPhiXZ hPhiT hXZ_T
  exact ⟨hFirst, hSecond⟩

/-- Full quotient-subgroup geometry, including that the three factor images
span all of `P / Φ(P)`. -/
theorem frattiniQuotient_factorImages_full_geometry
    {P : Type uP} [Group P]
    (X Z T : Subgroup P)
    (hPhiX : frattini P ≤ X)
    (hPhiZ : frattini P ≤ Z)
    (hPhiT : frattini P ≤ T)
    (hXZ : X ⊓ Z = frattini P)
    (hXZ_T : (X ⊔ Z) ⊓ T = frattini P)
    (hTotal : X ⊔ Z ⊔ T = ⊤) :
    let q := QuotientGroup.mk' (frattini P)
    X.map q ⊓ Z.map q = ⊥ ∧
      (X.map q ⊔ Z.map q) ⊓ T.map q = ⊥ ∧
        X.map q ⊔ Z.map q ⊔ T.map q = ⊤ := by
  dsimp only
  let q := QuotientGroup.mk' (frattini P)
  obtain ⟨hFirst, hSecond⟩ :=
    frattiniQuotient_factorImages_direct_geometry
      X Z T hPhiX hPhiZ hPhiT hXZ hXZ_T
  have hSpan :
      X.map q ⊔ Z.map q ⊔ T.map q = ⊤ := by
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, hTotal]
    exact Subgroup.map_top_of_surjective q
      (QuotientGroup.mk'_surjective (frattini P))
  exact ⟨hFirst, hSecond, hSpan⟩

/-- **Higman Lemma 13 (p. 93), direct quotient-submodule geometry.**

Transporting the quotient subgroup images through the elementary-abelian
subgroup/submodule order equivalence preserves their meets, joins, and
bottom.  Thus the same two directness identities hold for the submodules
which occur as ranges of genuine factor inclusions.
-/
theorem frattiniQuotient_factorSubmodules_direct_geometry
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (X Z T : Subgroup P)
    (hPhiX : frattini P ≤ X)
    (hPhiZ : frattini P ≤ Z)
    (hPhiT : frattini P ≤ T)
    (hXZ : X ⊓ Z = frattini P)
    (hXZ_T : (X ⊔ Z) ⊓ T = frattini P) :
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    let q := QuotientGroup.mk' (frattini P)
    let Xbar : Submodule (ZMod 2) (Additive (P ⧸ frattini P)) :=
      (elabSubmoduleSubgroupEquiv (K := P ⧸ frattini P) 2).symm (X.map q)
    let Zbar : Submodule (ZMod 2) (Additive (P ⧸ frattini P)) :=
      (elabSubmoduleSubgroupEquiv (K := P ⧸ frattini P) 2).symm (Z.map q)
    let Tbar : Submodule (ZMod 2) (Additive (P ⧸ frattini P)) :=
      (elabSubmoduleSubgroupEquiv (K := P ⧸ frattini P) 2).symm (T.map q)
    Xbar ⊓ Zbar = ⊥ ∧
      (Xbar ⊔ Zbar) ⊓ Tbar = ⊥ := by
  dsimp only
  let : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  let : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  let q := QuotientGroup.mk' (frattini P)
  let E := elabSubmoduleSubgroupEquiv (K := P ⧸ frattini P) 2
  let Xbar := E.symm (X.map q)
  let Zbar := E.symm (Z.map q)
  let Tbar := E.symm (T.map q)
  obtain ⟨hFirstImages, hSecondImages⟩ :=
    frattiniQuotient_factorImages_direct_geometry
      X Z T hPhiX hPhiZ hPhiT hXZ hXZ_T
  have hFirst : Xbar ⊓ Zbar = ⊥ := by
    apply E.injective
    rw [E.map_inf, E.apply_symm_apply, E.apply_symm_apply, E.map_bot]
    exact hFirstImages
  have hSecond : (Xbar ⊔ Zbar) ⊓ Tbar = ⊥ := by
    apply E.injective
    rw [E.map_inf, E.map_sup, E.apply_symm_apply,
      E.apply_symm_apply, E.apply_symm_apply, E.map_bot]
    exact hSecondImages
  exact ⟨hFirst, hSecond⟩

/-- Full quotient-submodule geometry, including that the three factor
submodules span the entire additive Frattini quotient. -/
theorem frattiniQuotient_factorSubmodules_full_geometry
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (X Z T : Subgroup P)
    (hPhiX : frattini P ≤ X)
    (hPhiZ : frattini P ≤ Z)
    (hPhiT : frattini P ≤ T)
    (hXZ : X ⊓ Z = frattini P)
    (hXZ_T : (X ⊔ Z) ⊓ T = frattini P)
    (hTotal : X ⊔ Z ⊔ T = ⊤) :
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    let q := QuotientGroup.mk' (frattini P)
    let Xbar : Submodule (ZMod 2) (Additive (P ⧸ frattini P)) :=
      (elabSubmoduleSubgroupEquiv (K := P ⧸ frattini P) 2).symm (X.map q)
    let Zbar : Submodule (ZMod 2) (Additive (P ⧸ frattini P)) :=
      (elabSubmoduleSubgroupEquiv (K := P ⧸ frattini P) 2).symm (Z.map q)
    let Tbar : Submodule (ZMod 2) (Additive (P ⧸ frattini P)) :=
      (elabSubmoduleSubgroupEquiv (K := P ⧸ frattini P) 2).symm (T.map q)
    Xbar ⊓ Zbar = ⊥ ∧
      (Xbar ⊔ Zbar) ⊓ Tbar = ⊥ ∧
        Xbar ⊔ Zbar ⊔ Tbar = ⊤ := by
  dsimp only
  let : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  let : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  let q := QuotientGroup.mk' (frattini P)
  let E := elabSubmoduleSubgroupEquiv (K := P ⧸ frattini P) 2
  let Xbar := E.symm (X.map q)
  let Zbar := E.symm (Z.map q)
  let Tbar := E.symm (T.map q)
  obtain ⟨hFirstImages, hSecondImages, hSpanImages⟩ :=
    frattiniQuotient_factorImages_full_geometry
      X Z T hPhiX hPhiZ hPhiT hXZ hXZ_T hTotal
  have hFirst : Xbar ⊓ Zbar = ⊥ := by
    apply E.injective
    rw [E.map_inf, E.apply_symm_apply, E.apply_symm_apply, E.map_bot]
    exact hFirstImages
  have hSecond : (Xbar ⊔ Zbar) ⊓ Tbar = ⊥ := by
    apply E.injective
    rw [E.map_inf, E.map_sup, E.apply_symm_apply,
      E.apply_symm_apply, E.apply_symm_apply, E.map_bot]
    exact hSecondImages
  have hSpan : Xbar ⊔ Zbar ⊔ Tbar = ⊤ := by
    apply E.injective
    rw [E.map_sup, E.map_sup, E.apply_symm_apply,
      E.apply_symm_apply, E.apply_symm_apply, E.map_top]
    exact hSpanImages
  exact ⟨hFirst, hSecond, hSpan⟩

end

end OddOrder.Higman.Suzuki2Groups
