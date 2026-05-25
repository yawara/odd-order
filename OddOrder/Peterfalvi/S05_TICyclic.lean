/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S03_PreliminaryCharacter
import OddOrder.Peterfalvi.S04_DadeIsometry

/-!
# Peterfalvi §5: TI-Subsets with Cyclic Normalizers

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§5, pp. 15-20.

This file starts the formal interface for the TI-cyclic normalizer setup in
Peterfalvi (3.1).  The key point of the current slice is that this setup gives
a canonical TI-specialized instance of the §4 Dade hypothesis, and then reuses
the §4 Dade-isometry packages for the maps used in (3.2)-(3.5).

Reference note: `notes/peterfalvi/s05_ti_cyclic_normalizer.md`.
-/

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory
open scoped Pointwise

variable {G : Type*} [Group G] [Fintype G]

/- 3: TI-subsets with cyclic normalizers (pp. 15-20) -/

/-- The ambient data in Peterfalvi (3.1).

`V` is kept as a field instead of being defined from `W`, `W1`, and `W2` so that
later sections can use the same interface for the slightly varied normalizer
setups that occur in §6 and §8. -/
structure TICyclicHypothesis (G : Type*) [Group G] [Fintype G] where
  W : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W1_le_W : W1 ≤ W
  W2_le_W : W2 ≤ W
  W1_nontrivial : W1 ≠ ⊥
  W2_nontrivial : W2 ≠ ⊥
  W_sup : W1 ⊔ W2 = W
  W_disjoint : Disjoint W1 W2
  W_card_coprime : Nat.Coprime (Nat.card W1) (Nat.card W2)
  W_card_odd : Odd (Nat.card W)
  V : Set G
  V_subset_sharp : V ⊆ OddOrder.Peterfalvi.S04.sharp (Set.univ : Set G)
  V_subset_W : V ⊆ W
  W_normalizes_V :
    ∀ (w : W) ⦃v : G⦄, v ∈ V → (w : G) * v * (w : G)⁻¹ ∈ V
  V_ti : OddOrder.GroupTheory.IsTISubset V W

namespace TICyclicHypothesis

/-- Peterfalvi (3.1), viewed as the `H(a)=1` specialization of §4 Hypothesis
(2.2). -/
def toDadeHypothesis (hyp : TICyclicHypothesis G) :
    OddOrder.Peterfalvi.S04.Hypothesis G hyp.V hyp.W :=
  OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset
    hyp.V_subset_sharp hyp.V_subset_W hyp.W_normalizes_V hyp.V_ti

@[simp] theorem toDadeHypothesis_H (hyp : TICyclicHypothesis G)
    (a : {a : G // a ∈ hyp.V}) :
    (hyp.toDadeHypothesis).H a = ⊥ :=
  rfl

theorem toDadeHypothesis_isTISubset (hyp : TICyclicHypothesis G) :
    OddOrder.GroupTheory.IsTISubset hyp.V hyp.W :=
  (hyp.toDadeHypothesis).isTISubset_of_forall_H_eq_bot
    (fun a => hyp.toDadeHypothesis_H a)

/-- The supported class-function space `CF(W,V)` used by (3.2)-(3.5). -/
abbrev SupportedOnV (k : Type*) [CommRing k] (hyp : TICyclicHypothesis G) :=
  OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) k hyp.V hyp.W

variable {k : Type*} [CommRing k] [StarRing k]
variable [Invertible (Nat.card G : k)]

/-- A §5 application package: a TI-cyclic setup together with a Dade map for
the induced §4 `H(a)=1` hypothesis. -/
structure DadeApplication (hyp : TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : k)] where
  tau : OddOrder.Peterfalvi.S04.DadeIsometryData
    (G := G) (k := k) hyp.toDadeHypothesis

instance (hyp : TICyclicHypothesis G) [Fintype hyp.W] [Invertible (Nat.card hyp.W : k)] :
    CoeFun (DadeApplication (G := G) (k := k) hyp)
      (fun _ => OddOrder.Peterfalvi.S04.DadeMap (G := G) k hyp.V hyp.W) :=
  ⟨fun app => app.tau.toDadeMap⟩

@[simp] theorem coe_mk (hyp : TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : k)]
    (tau : OddOrder.Peterfalvi.S04.DadeIsometryData
      (G := G) (k := k) hyp.toDadeHypothesis) :
    ((DadeApplication.mk tau : DadeApplication (G := G) (k := k) hyp) :
      OddOrder.Peterfalvi.S04.DadeMap (G := G) k hyp.V hyp.W) = tau.toDadeMap :=
  rfl

variable [Invertible (Nat.card G : ℂ)]

/-- A complex §5 application package including the virtual-character part of
the §4 Dade isometry theorem. -/
structure FullDadeApplication (hyp : TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)] where
  tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData
    (G := G) hyp.toDadeHypothesis

instance (hyp : TICyclicHypothesis G) [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)] :
    CoeFun (FullDadeApplication (G := G) hyp)
      (fun _ => OddOrder.Peterfalvi.S04.DadeMap (G := G) ℂ hyp.V hyp.W) :=
  ⟨fun app => app.tau.toDadeMap⟩

@[simp] theorem full_coe_mk (hyp : TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    (tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData
      (G := G) hyp.toDadeHypothesis) :
    ((FullDadeApplication.mk tau : FullDadeApplication (G := G) hyp) :
      OddOrder.Peterfalvi.S04.DadeMap (G := G) ℂ hyp.V hyp.W) = tau.toDadeMap :=
  rfl

theorem full_inner_eq {hyp : TICyclicHypothesis G}
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    (app : FullDadeApplication (G := G) hyp)
    (α β : SupportedOnV (G := G) ℂ hyp) :
    ClassFunction.inner (app.tau.toDadeMap α) (app.tau.toDadeMap β) =
      ClassFunction.inner (α : ClassFunction hyp.W ℂ) (β : ClassFunction hyp.W ℂ) :=
  app.tau.inner_eq α β

theorem full_maps_virtualCharacter {hyp : TICyclicHypothesis G}
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    (app : FullDadeApplication (G := G) hyp)
    (α : SupportedOnV (G := G) ℂ hyp)
    (hα : (α : ClassFunction hyp.W ℂ) ∈ ZIrr hyp.W) :
    app.tau.toDadeMap α ∈ ZIrr G :=
  app.tau.maps_virtualCharacter α hα

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05
