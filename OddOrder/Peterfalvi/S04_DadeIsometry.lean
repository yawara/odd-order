/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
import OddOrder.GroupTheory.TISubset
import OddOrder.GroupTheory.RepresentationTheory.ClassFunction
import OddOrder.Peterfalvi.S02_Notation

/-!
# Peterfalvi §4: The Dade Isometry

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§4, pp. 10-14.

This file starts the formal interface for the Dade isometry.  The full theorem
has two parts:

* **(2.6.a)** normalized inner-product preservation for the map
  `CF(L, A) → ClassFunction G`;
* **(2.6.b)** preservation of virtual characters.

The virtual-character lattice `Z[Irr G]` is not available yet, so the first
slice records the `(2.2)` hypothesis and the normalized inner-product/isometry
interface.
The `Z[Irr]` field should be added to this same interface once the Wave 1a
`ZIrr` module lands.

## Main declarations

* `OddOrder.Peterfalvi.S04.centralizerIn` — `C_L(a)` as a subgroup of `G`.
* `OddOrder.Peterfalvi.S04.supportInSubgroup` — the subset of `L` induced by
  `A ⊆ G`.
* `OddOrder.Peterfalvi.S04.SupportedClassFunctions` — Peterfalvi's `CF(L,A)`.
* `OddOrder.Peterfalvi.S04.SupportedClassFunctions.inclusion` — the natural map
  `CF(L,A₁) → CF(L,A)` for `A₁ ⊆ A`.
* `OddOrder.Peterfalvi.S04.Hypothesis` — Peterfalvi Hypothesis (2.2), bundled.
* `OddOrder.Peterfalvi.S04.DadeMap` and `IsDadeIsometry` — the current
  inner-product part of the Dade isometry interface.

Reference note: `notes/peterfalvi/s04_dade_isometry.md`.
-/

namespace OddOrder.Peterfalvi.S04

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/- 2: The Dade Isometry (pp. 10-14) -/

/-- The nonidentity part `A# = A \ {1}`. -/
def sharp (A : Set G) : Set G :=
  A \ {1}

@[simp] theorem mem_sharp {A : Set G} {g : G} :
    g ∈ sharp A ↔ g ∈ A ∧ g ≠ 1 := by
  simp [sharp]

/-- `C_L(a)`, viewed as a subgroup of the ambient group `G`. -/
def centralizerIn (L : Subgroup G) (a : G) : Subgroup G :=
  L ⊓ Subgroup.centralizer ({a} : Set G)

@[simp] theorem mem_centralizerIn {L : Subgroup G} {a x : G} :
    x ∈ centralizerIn L a ↔ x ∈ L ∧ x * a = a * x := by
  simp [centralizerIn, Subgroup.mem_centralizer_singleton_iff]

/-- The subset of a subgroup `L` obtained by restricting an ambient subset
`A ⊆ G` to elements of `L`. -/
def supportInSubgroup (A : Set G) (L : Subgroup G) : Set L :=
  {x | (x : G) ∈ A}

@[simp] theorem mem_supportInSubgroup {A : Set G} {L : Subgroup G} {x : L} :
    x ∈ supportInSubgroup A L ↔ (x : G) ∈ A := Iff.rfl

theorem supportInSubgroup_mono {A₁ A : Set G} {L : Subgroup G} (hA₁A : A₁ ⊆ A) :
    supportInSubgroup A₁ L ⊆ supportInSubgroup A L := fun _ hx => hA₁A hx

/-- Peterfalvi's `CF(L,A)`: class functions on `L` supported on the ambient
subset `A`. -/
abbrev SupportedClassFunctions (k : Type*) [CommRing k] (A : Set G) (L : Subgroup G) :=
  ↥(ClassFunction.supportedSubmodule (G := L) (k := k) (supportInSubgroup A L))

namespace SupportedClassFunctions

variable {k : Type*} [CommRing k]
variable {A A₁ : Set G} {L : Subgroup G}

/-- The natural inclusion `CF(L,A₁) → CF(L,A)` induced by `A₁ ⊆ A`.

This is the domain map used by the restriction statement in Peterfalvi (2.11). -/
def inclusion (hA₁A : A₁ ⊆ A) :
    (SupportedClassFunctions (G := G) k A₁ L) →ₗ[k]
      (SupportedClassFunctions (G := G) k A L) :=
  Submodule.inclusion (by
    intro φ hφ
    exact fun x hx => hA₁A (hφ hx))

@[simp] theorem coe_inclusion (hA₁A : A₁ ⊆ A)
    (α : SupportedClassFunctions (G := G) k A₁ L) :
    ((inclusion (G := G) (k := k) (L := L) hA₁A α :
        SupportedClassFunctions (G := G) k A L) : ClassFunction L k) =
      (α : ClassFunction L k) :=
  rfl

@[simp] theorem inclusion_apply (hA₁A : A₁ ⊆ A)
    (α : SupportedClassFunctions (G := G) k A₁ L) (x : L) :
    ((inclusion (G := G) (k := k) (L := L) hA₁A α :
        SupportedClassFunctions (G := G) k A L) : ClassFunction L k) x =
      (α : ClassFunction L k) x :=
  rfl

end SupportedClassFunctions

/-- **Peterfalvi Hypothesis (2.2).**

The centralizer decomposition `(2.2.b)` is encoded as a product-like pair of
fields:

* `centralizer_eq_sup`: `C_G(a) = H(a) ⊔ C_L(a)`;
* `centralizer_disjoint`: `H(a) ⊓ C_L(a) = ⊥` in `Disjoint` form.

This keeps the statement usable before a dedicated semidirect-product predicate
for internal subgroup products is introduced. -/
structure Hypothesis (G : Type*) [Group G] [Fintype G] (A : Set G) (L : Subgroup G) where
  subset_sharp : A ⊆ sharp (Set.univ : Set G)
  subset_L : A ⊆ L
  L_normalizes_A : ∀ (l : L) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A
  H : {a : G // a ∈ A} → Subgroup G
  conj_in_L :
    ∀ ⦃a b : G⦄, a ∈ A → b ∈ A → IsConj a b →
      ∃ l : L, (l : G) * a * (l : G)⁻¹ = b
  centralizer_eq_sup :
    ∀ a : {a : G // a ∈ A},
      Subgroup.centralizer ({a.1} : Set G) = H a ⊔ centralizerIn L a.1
  centralizer_disjoint :
    ∀ a : {a : G // a ∈ A}, Disjoint (H a) (centralizerIn L a.1)
  centralizer_coprime :
    ∀ a b : {a : G // a ∈ A},
      Nat.Coprime (Nat.card (H a)) (Nat.card (centralizerIn L b.1))

namespace Hypothesis

variable {A A₁ : Set G} {L : Subgroup G}

variable [Fintype G]

theorem mem_L (hyp : Hypothesis G A L) {a : G} (ha : a ∈ A) : a ∈ L :=
  hyp.subset_L ha

theorem ne_one (hyp : Hypothesis G A L) {a : G} (ha : a ∈ A) : a ≠ 1 :=
  (mem_sharp.mp (hyp.subset_sharp ha)).2

/-- One direction of **Peterfalvi (2.3)**: under Hypothesis (2.2), if all
subgroups `H(a)` are trivial, then `A` is a TI-subset relative to `L`. -/
theorem isTISubset_of_forall_H_eq_bot (hyp : Hypothesis G A L)
    (hH : ∀ a : {a : G // a ∈ A}, hyp.H a = ⊥) :
    OddOrder.GroupTheory.IsTISubset A L := by
  intro g hgap
  rcases hgap with ⟨a, ha, hga⟩
  have hconj : IsConj a (g * a * g⁻¹) := by
    rw [isConj_iff]
    exact ⟨g, rfl⟩
  rcases hyp.conj_in_L ha hga hconj with ⟨l, hl⟩
  let y : G := (l : G)⁻¹ * g
  have hy_comm_left : a * y = y * a := by
    change a * ((l : G)⁻¹ * g) = ((l : G)⁻¹ * g) * a
    calc
      a * ((l : G)⁻¹ * g) = (l : G)⁻¹ * ((l : G) * a * (l : G)⁻¹) * g := by
        group
      _ = (l : G)⁻¹ * (g * a * g⁻¹) * g := by rw [hl]
      _ = ((l : G)⁻¹ * g) * a := by
        group
  have hy_cent : y ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hy_comm_left.symm
  have hcent_eq := hyp.centralizer_eq_sup ⟨a, ha⟩
  rw [hH ⟨a, ha⟩, bot_sup_eq] at hcent_eq
  have hy_in_centralizerIn : y ∈ centralizerIn L a := by
    rw [← hcent_eq]
    exact hy_cent
  have hy_L : y ∈ L := (mem_centralizerIn.mp hy_in_centralizerIn).1
  have hg : (l : G) * y ∈ L := L.mul_mem l.property hy_L
  have hg_eq : (l : G) * y = g := by
    simp [y]
  exact hg_eq ▸ hg

/-- The other direction of **Peterfalvi (2.3)** in the relative-normalizer API:
from a TI-subset relative to `L`, build Hypothesis (2.2) with all `H(a)=⊥`.

Peterfalvi also states `L = N_G(A)` when `A` is nonempty.  This file keeps
`L` as an explicit normalizer-bound, so the theorem takes the required
`A ⊆ L` and `L`-normalizes-`A` assumptions as fields. -/
def of_isTISubset (hA_sharp : A ⊆ sharp (Set.univ : Set G)) (hA_L : A ⊆ L)
    (hL_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A)
    (hTI : OddOrder.GroupTheory.IsTISubset A L) :
    Hypothesis G A L where
  subset_sharp := hA_sharp
  subset_L := hA_L
  L_normalizes_A := hL_norm
  H := fun _ => ⊥
  conj_in_L := by
    intro a b ha hb hconj
    rcases isConj_iff.mp hconj with ⟨g, rfl⟩
    exact ⟨⟨g, hTI g ⟨a, ha, hb⟩⟩, rfl⟩
  centralizer_eq_sup := by
    intro a
    rw [bot_sup_eq]
    ext x
    constructor
    · intro hx
      have hx_comm : x * a.1 = a.1 * x := by
        simpa [Subgroup.mem_centralizer_singleton_iff] using hx
      have hx_conj : x * a.1 * x⁻¹ = a.1 := by
        calc
          x * a.1 * x⁻¹ = a.1 * x * x⁻¹ := by rw [hx_comm]
          _ = a.1 := by group
      have hx_L : x ∈ L := hTI x ⟨a.1, a.2, by simp [hx_conj, a.2]⟩
      rw [mem_centralizerIn]
      exact ⟨hx_L, hx_comm⟩
    · intro hx
      rw [mem_centralizerIn] at hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hx.2
  centralizer_disjoint := fun _ => disjoint_bot_left
  centralizer_coprime := fun _ _ => by
    simp

@[simp] theorem of_isTISubset_H (hA_sharp : A ⊆ sharp (Set.univ : Set G))
    (hA_L : A ⊆ L)
    (hL_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A)
    (hTI : OddOrder.GroupTheory.IsTISubset A L) (a : {a : G // a ∈ A}) :
    (of_isTISubset hA_sharp hA_L hL_norm hTI).H a = ⊥ :=
  rfl

/-- **Peterfalvi (2.3)**, expressed with this file's relative-normalizer
predicate: under the ambient set and `L`-normalizer assumptions, `A` is TI
relative to `L` iff Hypothesis (2.2) holds with all `H(a)` trivial. -/
theorem isTISubset_iff_exists_hypothesis_with_trivial_H
    (hA_sharp : A ⊆ sharp (Set.univ : Set G)) (hA_L : A ⊆ L)
    (hL_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A) :
    OddOrder.GroupTheory.IsTISubset A L ↔
      ∃ hyp : Hypothesis G A L, ∀ a : {a : G // a ∈ A}, hyp.H a = ⊥ := by
  constructor
  · intro hTI
    exact ⟨of_isTISubset hA_sharp hA_L hL_norm hTI, fun _ => rfl⟩
  · rintro ⟨hyp, hH⟩
    exact hyp.isTISubset_of_forall_H_eq_bot hH

/-- Restrict Hypothesis (2.2) to an `L`-stable subset `A₁ ⊆ A`.

This is the setup part of Peterfalvi (2.11).  The equality of the corresponding
Dade maps is stated later, once `dadeMap` is defined. -/
def restrict (hyp : Hypothesis G A L) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    Hypothesis G A₁ L where
  subset_sharp := fun _ ha => hyp.subset_sharp (hA₁A ha)
  subset_L := fun _ ha => hyp.subset_L (hA₁A ha)
  L_normalizes_A := hA₁_norm
  H := fun a => hyp.H ⟨a.1, hA₁A a.2⟩
  conj_in_L := by
    intro _ _ ha hb hconj
    exact hyp.conj_in_L (hA₁A ha) (hA₁A hb) hconj
  centralizer_eq_sup := fun a => hyp.centralizer_eq_sup ⟨a.1, hA₁A a.2⟩
  centralizer_disjoint := fun a => hyp.centralizer_disjoint ⟨a.1, hA₁A a.2⟩
  centralizer_coprime := fun a b =>
    hyp.centralizer_coprime ⟨a.1, hA₁A a.2⟩ ⟨b.1, hA₁A b.2⟩

@[simp] theorem restrict_H (hyp : Hypothesis G A L) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (a : {a : G // a ∈ A₁}) :
    (hyp.restrict hA₁A hA₁_norm).H a = hyp.H ⟨a.1, hA₁A a.2⟩ :=
  rfl

/-- The coset `aH(a)` appearing in Peterfalvi (2.5), as an ambient subset of
`G`. -/
def hCoset (hyp : Hypothesis G A L) (a : {a : G // a ∈ A}) : Set G :=
  {g | ∃ h : G, h ∈ hyp.H a ∧ g = a.1 * h}

@[simp] theorem mem_hCoset (hyp : Hypothesis G A L) (a : {a : G // a ∈ A})
    {g : G} :
    g ∈ hyp.hCoset a ↔ ∃ h : G, h ∈ hyp.H a ∧ g = a.1 * h := Iff.rfl

/-- The support candidate for the Dade map: the union of the `G`-conjugates of
the cosets `aH(a)`. -/
def dadeSupport (hyp : Hypothesis G A L) : Set G :=
  ⋃ a : {a : G // a ∈ A}, Group.conjugatesOfSet (hyp.hCoset a)

theorem mem_dadeSupport_iff (hyp : Hypothesis G A L) {g : G} :
    g ∈ hyp.dadeSupport ↔
      ∃ a : {a : G // a ∈ A}, ∃ h : G, h ∈ hyp.H a ∧ IsConj (a.1 * h) g := by
  rw [dadeSupport, Set.mem_iUnion]
  constructor
  · rintro ⟨a, hg⟩
    rcases Group.mem_conjugatesOfSet_iff.mp hg with ⟨y, hy, hconj⟩
    rcases hy with ⟨h, hh, rfl⟩
    exact ⟨a, h, hh, hconj⟩
  · rintro ⟨a, h, hh, hconj⟩
    exact ⟨a, Group.mem_conjugatesOfSet_iff.mpr ⟨a.1 * h, ⟨h, hh, rfl⟩, hconj⟩⟩

theorem mem_dadeSupport_of_mem_hCoset (hyp : Hypothesis G A L)
    {a : {a : G // a ∈ A}} {h : G} (hh : h ∈ hyp.H a) :
    a.1 * h ∈ hyp.dadeSupport :=
  hyp.mem_dadeSupport_iff.mpr ⟨a, h, hh, IsConj.refl _⟩

theorem conj_mem_dadeSupport (hyp : Hypothesis G A L) {g x : G}
    (hg : g ∈ hyp.dadeSupport) :
    x * g * x⁻¹ ∈ hyp.dadeSupport := by
  rw [hyp.mem_dadeSupport_iff] at hg ⊢
  rcases hg with ⟨a, h, hh, hconj⟩
  exact ⟨a, h, hh, hconj.trans (isConj_iff.mpr ⟨x, rfl⟩)⟩

end Hypothesis

section DadeMap

variable {A A₁ : Set G} {L : Subgroup G}
/-- A candidate Dade map `τ : CF(L,A) → ClassFunction G`. -/
abbrev DadeMap (k : Type*) [CommRing k] (A : Set G) (L : Subgroup G) :=
  SupportedClassFunctions (G := G) k A L → ClassFunction G k

variable {k : Type*} [CommRing k]

namespace DadeMap

/-- Restrict the domain of a candidate Dade map along `A₁ ⊆ A`. -/
def restrictDomain (τ : DadeMap (G := G) k A L) (hA₁A : A₁ ⊆ A) :
    DadeMap (G := G) k A₁ L :=
  fun α => τ (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α)

@[simp] theorem restrictDomain_apply (τ : DadeMap (G := G) k A L) (hA₁A : A₁ ⊆ A)
    (α : SupportedClassFunctions (G := G) k A₁ L) :
    restrictDomain (G := G) (k := k) (L := L) τ hA₁A α =
      τ (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α) :=
  rfl

end DadeMap

section IsDadeMap

variable [Fintype G]

/-- Predicate form of Peterfalvi (2.5): a candidate map is the Dade map for
`hyp` if it has the prescribed values on conjugates of `aH(a)` and is zero off
their conjugacy-saturated union.

The uniqueness/well-definedness proof from (2.4.b) is intentionally kept out of
this predicate, so later work can either construct a map or assume one and use
these equations directly. -/
structure IsDadeMap (hyp : Hypothesis G A L) (τ : DadeMap (G := G) k A L) : Prop where
  map_eq_of_isConj_hCoset :
    ∀ (α : SupportedClassFunctions (G := G) k A L) (g : G)
      (a : {a : G // a ∈ A}) (h : G),
      h ∈ hyp.H a → IsConj (a.1 * h) g →
        τ α g = (α : ClassFunction L k) ⟨a.1, hyp.mem_L a.2⟩
  map_eq_zero_of_not_mem_dadeSupport :
    ∀ (α : SupportedClassFunctions (G := G) k A L) (g : G),
      g ∉ hyp.dadeSupport → τ α g = 0

namespace IsDadeMap

theorem restrictDomain {hyp : Hypothesis G A L} {τ : DadeMap (G := G) k A L}
    (hτ : IsDadeMap hyp τ) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    IsDadeMap (hyp.restrict hA₁A hA₁_norm)
      (DadeMap.restrictDomain (G := G) (k := k) (L := L) τ hA₁A) where
  map_eq_of_isConj_hCoset α g a h hh hconj := by
    simpa using hτ.map_eq_of_isConj_hCoset
      (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α) g
      ⟨a.1, hA₁A a.2⟩ h hh hconj
  map_eq_zero_of_not_mem_dadeSupport α g hg := by
    by_cases hgsupp : g ∈ hyp.dadeSupport
    · rcases hyp.mem_dadeSupport_iff.mp hgsupp with ⟨a, h, hh, hconj⟩
      have ha_not : a.1 ∉ A₁ := by
        intro ha₁
        apply hg
        have hh' : h ∈ (hyp.restrict hA₁A hA₁_norm).H ⟨a.1, ha₁⟩ := by
          change h ∈ hyp.H ⟨a.1, hA₁A ha₁⟩
          have ha_eq : (⟨a.1, hA₁A ha₁⟩ : {a : G // a ∈ A}) = a := Subtype.ext rfl
          simpa [ha_eq] using hh
        exact (hyp.restrict hA₁A hA₁_norm).mem_dadeSupport_iff.mpr
          ⟨⟨a.1, ha₁⟩, h, hh', hconj⟩
      have hα_zero :
          (α : ClassFunction L k) ⟨a.1, hyp.mem_L a.2⟩ = 0 := by
        by_contra hne
        exact ha_not (α.property hne)
      have hmap := hτ.map_eq_of_isConj_hCoset
        (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α) g a h
        hh hconj
      rw [DadeMap.restrictDomain_apply, hmap]
      simpa using hα_zero
    · exact hτ.map_eq_zero_of_not_mem_dadeSupport
        (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α) g hgsupp

end IsDadeMap

end IsDadeMap

variable [StarRing k]
variable [Fintype G] [Fintype L]
variable [Invertible (Nat.card G : k)] [Invertible (Nat.card L : k)]

/-- The currently available part of the Dade isometry interface: preservation
of Peterfalvi's normalized class-function inner product.

The virtual-character preservation field from (2.6.b) is intentionally
postponed until the `Z[Irr]` lattice is available. -/
structure IsDadeIsometry (τ : DadeMap (G := G) k A L) : Prop where
  inner_eq :
    ∀ α β : SupportedClassFunctions (G := G) k A L,
      ClassFunction.inner (τ α) (τ β) =
        ClassFunction.inner (α : ClassFunction L k) (β : ClassFunction L k)

namespace IsDadeIsometry

/-- The inner-product part of a Dade isometry restricts along `A₁ ⊆ A`.

This is the currently formalized part of Peterfalvi (2.11). -/
theorem restrictDomain {τ : DadeMap (G := G) k A L} (hτ : IsDadeIsometry τ)
    (hA₁A : A₁ ⊆ A) :
    IsDadeIsometry (DadeMap.restrictDomain (G := G) (k := k) (L := L) τ hA₁A) where
  inner_eq α β := by
    simpa using hτ.inner_eq
      (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α)
      (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A β)

end IsDadeIsometry

end DadeMap

end OddOrder.Peterfalvi.S04
