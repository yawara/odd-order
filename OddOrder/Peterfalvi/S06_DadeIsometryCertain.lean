/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S05_TICyclic

/-!
# Peterfalvi §6: The Dade Isometry for a Certain Type of Subgroup

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§6, pp. 21-24.

This module introduces the carrier structures for the "certain type" Dade
applications in §6.  It deliberately reuses the §4 bundled Dade data instead of
creating a second isometry interface.  The coefficient-parametric
`DadeApplication` records the pointwise and inner-product parts, while
`FullDadeApplication` records the complex virtual-character preservation part.

Reference note: `notes/peterfalvi/s06_dade_certain_subgroup.md`.
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G}

/- 4: Dade isometry for a certain type of subgroup (pp. 21-24) -/

/-- The structural hypotheses used by Peterfalvi §6 before the concrete
character calculations begin.

The fields `K`, `W1`, and `W2` are subgroups of `L` because §6 works internally
inside the normalizer subgroup while still mapping class functions into `G` via
the §4 Dade map. -/
structure CertainTypeHypothesis (A : Set G) (L : Subgroup G) where
  dade : OddOrder.Peterfalvi.S04.Hypothesis G A L
  K : Subgroup L
  W1 : Subgroup L
  W2 : Subgroup L
  K_normal : K.Normal
  W1_nontrivial : W1 ≠ ⊥
  W2_nontrivial : W2 ≠ ⊥
  W_sup : W1 ⊔ W2 = ⊤
  W_disjoint : Disjoint W1 W2

namespace CertainTypeHypothesis

variable {k : Type*} [CommRing k] [StarRing k]
variable [Fintype L] [Invertible (Nat.card G : k)] [Invertible (Nat.card L : k)]

/-- A §6 application package: the structural §6 hypothesis plus a Dade map
known to satisfy the §4 pointwise and isometry interfaces. -/
structure DadeApplication (hyp : CertainTypeHypothesis (G := G) A L) where
  tau : OddOrder.Peterfalvi.S04.DadeIsometryData (G := G) (k := k) hyp.dade

instance (hyp : CertainTypeHypothesis (G := G) A L) :
    CoeFun (DadeApplication (G := G) (k := k) hyp)
      (fun _ => OddOrder.Peterfalvi.S04.DadeMap (G := G) k A L) :=
  ⟨fun app => app.tau.toDadeMap⟩

@[simp] theorem coe_mk (hyp : CertainTypeHypothesis (G := G) A L)
    (tau : OddOrder.Peterfalvi.S04.DadeIsometryData (G := G) (k := k) hyp.dade) :
    ((DadeApplication.mk tau : DadeApplication (G := G) (k := k) hyp) :
      OddOrder.Peterfalvi.S04.DadeMap (G := G) k A L) = tau.toDadeMap :=
  rfl

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card L : ℂ)]

/-- A complex §6 application package including the virtual-character part of
the §4 Dade isometry theorem. -/
structure FullDadeApplication (hyp : CertainTypeHypothesis (G := G) A L) where
  tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) hyp.dade

instance (hyp : CertainTypeHypothesis (G := G) A L) :
    CoeFun (FullDadeApplication (G := G) hyp)
      (fun _ => OddOrder.Peterfalvi.S04.DadeMap (G := G) ℂ A L) :=
  ⟨fun app => app.tau.toDadeMap⟩

@[simp] theorem full_coe_mk (hyp : CertainTypeHypothesis (G := G) A L)
    (tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) hyp.dade) :
    ((FullDadeApplication.mk tau : FullDadeApplication (G := G) hyp) :
      OddOrder.Peterfalvi.S04.DadeMap (G := G) ℂ A L) = tau.toDadeMap :=
  rfl

theorem full_inner_eq {hyp : CertainTypeHypothesis (G := G) A L}
    (app : FullDadeApplication (G := G) hyp)
    (α β : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L) :
    ClassFunction.inner (app.tau.toDadeMap α) (app.tau.toDadeMap β) =
      ClassFunction.inner (α : ClassFunction L ℂ) (β : ClassFunction L ℂ) :=
  app.tau.inner_eq α β

theorem full_maps_virtualCharacter {hyp : CertainTypeHypothesis (G := G) A L}
    (app : FullDadeApplication (G := G) hyp)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L)
    (hα : (α : ClassFunction L ℂ) ∈ ZIrr L) :
    app.tau.toDadeMap α ∈ ZIrr G :=
  app.tau.maps_virtualCharacter α hα

end CertainTypeHypothesis

end OddOrder.Peterfalvi.S06
