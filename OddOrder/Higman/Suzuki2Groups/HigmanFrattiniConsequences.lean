/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanAbelian
import OddOrder.BG.Ch1_Preliminary.S01_Solvable

/-!
# Higman Lemma 3: Frattini consequences

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 3,
pp. 83--84.

This file proves the immediate consequences of Phi(C) = Phi(A): mixed
commutators lie in A squared, squares from C lie in A squared, and the
commutator estimate propagates from A squared to A to the fourth power.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open scoped commutatorElement

/-- For a finite abelian `2`-group, its Frattini subgroup is its square
subgroup. -/
private theorem frattini_eq_agemo_one_of_comm_two
    {A : Type*} [CommGroup A] [Finite A] (hA : IsPGroup 2 A) :
    frattini A = Agemo A 2 1 := by
  have h := OddOrder.BG.Ch1.S01.commutator_sup_pow_closure_eq_frattini hA
  rw [commutator_eq_bot, bot_sup_eq] at h
  rw [← h, Agemo]
  congr 1
  ext x
  constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, rfl⟩

/-- Ambient form of `[C,A] ≤ Φ(C) = Φ(A)`. -/
private theorem commutator_le_frattini_map_of_frattini_map_eq
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {A C : Subgroup P} (hAC : A ≤ C)
    (hΦ : (frattini C).map C.subtype = (frattini A).map A.subtype) :
    ⁅C, A⁆ ≤ (frattini A).map A.subtype := by
  calc
    ⁅C, A⁆ ≤ ⁅C, C⁆ := Subgroup.commutator_mono le_rfl hAC
    _ = (_root_.commutator C).map C.subtype :=
      C.map_subtype_commutator.symm
    _ ≤ (frattini C).map C.subtype := Subgroup.map_mono
      (OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup
        (hP.to_subgroup C))
    _ = (frattini A).map A.subtype := hΦ

/-- The two immediate ambient consequences of `Φ(C)=Φ(A)` in Higman
Lemma 3: mixed commutators and squares of elements of `C` lie in `A²`. -/
theorem frattini_map_eq_consequences
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {A C : Subgroup P} (hAC : A ≤ C)
    (hAcomm : IsMulCommutative A)
    (hΦ : (frattini C).map C.subtype = (frattini A).map A.subtype) :
    ⁅C, A⁆ ≤ (Agemo A 2 1).map A.subtype ∧
      (Agemo C 2 1).map C.subtype ≤ (Agemo A 2 1).map A.subtype := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  have hΦA : frattini A = Agemo A 2 1 :=
    frattini_eq_agemo_one_of_comm_two (hP.to_subgroup A)
  constructor
  · rw [← hΦA]
    exact commutator_le_frattini_map_of_frattini_map_eq hP hAC hΦ
  · have hCpow : Agemo C 2 1 ≤ frattini C := by
      rw [Agemo, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      simpa using OddOrder.GroupTheory.IsPGroup.pow_mem_frattini
        (hP.to_subgroup C) c
    calc
      (Agemo C 2 1).map C.subtype ≤ (frattini C).map C.subtype :=
        Subgroup.map_mono hCpow
      _ = (frattini A).map A.subtype := hΦ
      _ = (Agemo A 2 1).map A.subtype := congrArg (Subgroup.map A.subtype) hΦA

/-- Element form: conjugation by an element of `C` is the identity on `A`
modulo the ambient image of `A²`. -/
theorem conjugation_mul_inv_mem_agemo_one_of_frattini_map_eq
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {A C : Subgroup P} (hAC : A ≤ C)
    (hAcomm : IsMulCommutative A)
    (hΦ : (frattini C).map C.subtype = (frattini A).map A.subtype)
    {u a : P} (hu : u ∈ C) (ha : a ∈ A) :
    u⁻¹ * a * u * a⁻¹ ∈ (Agemo A 2 1).map A.subtype := by
  have hCA := (frattini_map_eq_consequences hP hAC hAcomm hΦ).1
  have hmem : ⁅u⁻¹, a⁆ ∈ ⁅C, A⁆ :=
    Subgroup.commutator_mem_commutator (C.inv_mem hu) ha
  simpa only [commutatorElement_def, inv_inv] using hCA hmem

/-- Element form: every square of an element of `C` lies in the ambient
image of `A²`. -/
theorem square_mem_agemo_one_of_frattini_map_eq
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {A C : Subgroup P} (hAC : A ≤ C)
    (hAcomm : IsMulCommutative A)
    (hΦ : (frattini C).map C.subtype = (frattini A).map A.subtype)
    {u : P} (hu : u ∈ C) :
    u ^ 2 ∈ (Agemo A 2 1).map A.subtype := by
  have hpow := (frattini_map_eq_consequences hP hAC hAcomm hΦ).2
  have huAg : (⟨u, hu⟩ : C) ^ (2 ^ 1) ∈ Agemo C 2 1 :=
    Agemo.mem_of_eq_pow (⟨u, hu⟩ : C)
  have hm := hpow (Subgroup.mem_map_of_mem C.subtype huAg)
  simpa using hm

end OddOrder.Higman.Suzuki2Groups
