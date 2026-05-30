/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
import OddOrder.GroupTheory.TISubset
import OddOrder.GroupTheory.CoprimeConjugacy
import OddOrder.GroupTheory.RepresentationTheory.ClassFunction
import OddOrder.GroupTheory.RepresentationTheory.ZIrr
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter
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

The coefficient-parametric interface records the `(2.2)` hypothesis and the
normalized inner-product/isometry property from `(2.6.a)`.  The complex
interface `FullDadeIsometryData` adds the virtual-character preservation
property from `(2.6.b)` using the Wave 1a `ZIrr` lattice.

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
* `OddOrder.Peterfalvi.S04.DadeIsometryData` — a bundled map with the current
  Dade-map equations and normalized isometry property.
* `OddOrder.Peterfalvi.S04.PreservesVirtualCharacters` and
  `FullDadeIsometryData` — the complex-coefficient `(2.6.b)` interface.

Reference note: `notes/peterfalvi/s04_dade_isometry.md`.
-/

namespace OddOrder.Peterfalvi.S04

open OddOrder.RepresentationTheory
open scoped Pointwise

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

/-- Conjugation by `l ∈ L` is an order-preserving bijection
`C_L(l a l⁻¹) ≃ C_L(a)`, so `|C_L(l a l⁻¹)| = |C_L(a)|`.  Used to see that the
centralizers `C_L(a)` are constant on each `L`-conjugacy class. -/
theorem card_centralizerIn_conj {L : Subgroup G} {l : G} (hl : l ∈ L) (a : G) :
    Nat.card (centralizerIn L (l * a * l⁻¹)) = Nat.card (centralizerIn L a) := by
  apply Nat.card_congr
  refine
    { toFun := fun c => ⟨l⁻¹ * c.1 * l, ?_⟩
      invFun := fun c => ⟨l * c.1 * l⁻¹, ?_⟩
      left_inv := fun c => Subtype.ext (by group)
      right_inv := fun c => Subtype.ext (by group) }
  · obtain ⟨hcL, hcomm⟩ := mem_centralizerIn.mp c.2
    refine mem_centralizerIn.mpr ⟨L.mul_mem (L.mul_mem (L.inv_mem hl) hcL) hl, ?_⟩
    calc (l⁻¹ * c.1 * l) * a
        = l⁻¹ * (c.1 * (l * a * l⁻¹)) * l := by group
      _ = l⁻¹ * ((l * a * l⁻¹) * c.1) * l := by rw [hcomm]
      _ = a * (l⁻¹ * c.1 * l) := by group
  · obtain ⟨hcL, hcomm⟩ := mem_centralizerIn.mp c.2
    refine mem_centralizerIn.mpr ⟨L.mul_mem (L.mul_mem hl hcL) (L.inv_mem hl), ?_⟩
    calc (l * c.1 * l⁻¹) * (l * a * l⁻¹)
        = l * (c.1 * a) * l⁻¹ := by group
      _ = l * (a * c.1) * l⁻¹ := by rw [hcomm]
      _ = (l * a * l⁻¹) * (l * c.1 * l⁻¹) := by group

/-- **`L`-conjugator count.**  If `b` lies in the `L`-conjugacy class of `a`, the
set of `l ∈ L` conjugating `a` to `b` is a left coset of `C_L(a)`, hence has
cardinality `|C_L(a)|`. -/
theorem card_conjugatorIn_L {L : Subgroup G} {a b : G}
    (h : ∃ l : L, (l : G) * a * (l : G)⁻¹ = b) :
    Nat.card {l : L // (l : G) * a * (l : G)⁻¹ = b}
      = Nat.card (centralizerIn L a) := by
  obtain ⟨l₀, hl₀⟩ := h
  apply Nat.card_congr
  refine
    { toFun := fun l => ⟨(l₀ : G)⁻¹ * (l.1 : G), ?_⟩
      invFun := fun c => ⟨⟨(l₀ : G) * c.1, L.mul_mem l₀.2 (mem_centralizerIn.mp c.2).1⟩, ?_⟩
      left_inv := fun l => Subtype.ext (Subtype.ext (by group))
      right_inv := fun c => Subtype.ext (by group) }
  · refine mem_centralizerIn.mpr ⟨L.mul_mem (L.inv_mem l₀.2) l.1.2, ?_⟩
    have e1 : (l.1 : G) * a * (l.1 : G)⁻¹ = (l₀ : G) * a * (l₀ : G)⁻¹ := by rw [l.2, hl₀]
    have hsas : ((l₀ : G)⁻¹ * (l.1 : G)) * a * ((l₀ : G)⁻¹ * (l.1 : G))⁻¹ = a := by
      calc ((l₀ : G)⁻¹ * (l.1 : G)) * a * ((l₀ : G)⁻¹ * (l.1 : G))⁻¹
          = (l₀ : G)⁻¹ * ((l.1 : G) * a * (l.1 : G)⁻¹) * (l₀ : G) := by group
        _ = (l₀ : G)⁻¹ * ((l₀ : G) * a * (l₀ : G)⁻¹) * (l₀ : G) := by rw [e1]
        _ = a := by group
    exact mul_inv_eq_iff_eq_mul.mp hsas
  · have hc : c.1 * a = a * c.1 := (mem_centralizerIn.mp c.2).2
    calc ((l₀ : G) * c.1) * a * ((l₀ : G) * c.1)⁻¹
        = (l₀ : G) * (c.1 * a * c.1⁻¹) * (l₀ : G)⁻¹ := by group
      _ = (l₀ : G) * a * (l₀ : G)⁻¹ := by
          rw [show c.1 * a * c.1⁻¹ = a from by rw [hc]; group]
      _ = b := hl₀

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
  /-- `H(a)` is normal in `C_G(a)`: the normal-complement half of the
  semidirect product `(2.2.b)` `C_G(a) = H(a) ⋊ C_L(a)`.  Without this the join
  `H(a) ⊔ C_L(a)` need not have cardinality `|H(a)|·|C_L(a)|`. -/
  H_normalized :
    ∀ (a : {a : G // a ∈ A}) (c : G),
      c ∈ Subgroup.centralizer ({a.1} : Set G) → ∀ x ∈ H a, c * x * c⁻¹ ∈ H a
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
  H_normalized := fun _ _ _ x hx => by
    rw [Subgroup.mem_bot.mp hx, mul_one, mul_inv_cancel]; exact (⊥ : Subgroup G).one_mem
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
  H_normalized := fun a => hyp.H_normalized ⟨a.1, hA₁A a.2⟩
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

theorem hCoset_subset_dadeSupport (hyp : Hypothesis G A L)
    (a : {a : G // a ∈ A}) :
    hyp.hCoset a ⊆ hyp.dadeSupport := by
  rintro _ ⟨h, hh, rfl⟩
  exact hyp.mem_dadeSupport_of_mem_hCoset hh

theorem conj_mem_dadeSupport (hyp : Hypothesis G A L) {g x : G}
    (hg : g ∈ hyp.dadeSupport) :
    x * g * x⁻¹ ∈ hyp.dadeSupport := by
  rw [hyp.mem_dadeSupport_iff] at hg ⊢
  rcases hg with ⟨a, h, hh, hconj⟩
  exact ⟨a, h, hh, hconj.trans (isConj_iff.mpr ⟨x, rfl⟩)⟩

theorem mem_dadeSupport_conj_iff (hyp : Hypothesis G A L) {g x : G} :
    x * g * x⁻¹ ∈ hyp.dadeSupport ↔ g ∈ hyp.dadeSupport := by
  constructor
  · intro hg
    have hg' := hyp.conj_mem_dadeSupport (x := x⁻¹) hg
    convert hg' using 1
    group
  · intro hg
    exact hyp.conj_mem_dadeSupport (x := x) hg

theorem dadeSupport_conj_eq (hyp : Hypothesis G A L) (x : G) :
    (fun g : G => x * g * x⁻¹) '' hyp.dadeSupport = hyp.dadeSupport := by
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hyp.conj_mem_dadeSupport hy
  · intro hg
    refine ⟨x⁻¹ * g * x, ?_, by group⟩
    have hg' := hyp.conj_mem_dadeSupport (x := x⁻¹) hg
    simpa using hg'

theorem preimage_dadeSupport_conj_eq (hyp : Hypothesis G A L) (x : G) :
    (fun g : G => x * g * x⁻¹) ⁻¹' hyp.dadeSupport = hyp.dadeSupport := by
  ext g
  exact hyp.mem_dadeSupport_conj_iff

/-- In the TI-specialized case `H(a)=1`, the coset `aH(a)` is the singleton
`{a}`. -/
theorem hCoset_eq_singleton_of_H_eq_bot (hyp : Hypothesis G A L)
    {a : {a : G // a ∈ A}} (hH : hyp.H a = ⊥) :
    hyp.hCoset a = {a.1} := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hh_one : h = 1 := by
      have : h ∈ (⊥ : Subgroup G) := by
        simpa [hH] using hh
      exact Subgroup.mem_bot.mp this
    simp [hh_one]
  · intro hg
    rw [Set.mem_singleton_iff] at hg
    subst g
    exact ⟨1, (hyp.H a).one_mem, by simp⟩

/-- In the TI-specialized case `H(a)=1`, the Dade support is just the
conjugacy-saturation of `A`. -/
theorem dadeSupport_eq_conjugatesOfSet_of_forall_H_eq_bot
    (hyp : Hypothesis G A L) (hH : ∀ a : {a : G // a ∈ A}, hyp.H a = ⊥) :
    hyp.dadeSupport = Group.conjugatesOfSet A := by
  ext g
  constructor
  · intro hg
    rcases hyp.mem_dadeSupport_iff.mp hg with ⟨a, h, hh, hconj⟩
    have hh_one : h = 1 := by
      have : h ∈ (⊥ : Subgroup G) := by
        simpa [hH a] using hh
      exact Subgroup.mem_bot.mp this
    exact Group.mem_conjugatesOfSet_iff.mpr ⟨a.1, a.2, by simpa [hh_one] using hconj⟩
  · intro hg
    rcases Group.mem_conjugatesOfSet_iff.mp hg with ⟨a, ha, hconj⟩
    exact hyp.mem_dadeSupport_iff.mpr
      ⟨⟨a, ha⟩, 1, (hyp.H ⟨a, ha⟩).one_mem, by simpa using hconj⟩

/-- The formal shape of Peterfalvi (2.4.a): the subgroups `H(a)` are
equivariant under conjugation by `L`.

This is kept as a predicate for now because the proof in the book identifies
`H(a)` with a `π'`-core of `C_G(a)`, and that π-core API is not yet part of the
S04 scaffold. -/
def HConjInvariant (hyp : Hypothesis G A L) : Prop :=
  ∀ (a : {a : G // a ∈ A}) (l : L),
    hyp.H ⟨(l : G) * a.1 * (l : G)⁻¹, hyp.L_normalizes_A l a.2⟩ =
      MulAut.conj (l : G) • hyp.H a

theorem HConjInvariant.of_forall_H_eq_bot (hyp : Hypothesis G A L)
    (hH : ∀ a : {a : G // a ∈ A}, hyp.H a = ⊥) :
    hyp.HConjInvariant := by
  intro a l
  rw [hH ⟨(l : G) * a.1 * (l : G)⁻¹, hyp.L_normalizes_A l a.2⟩, hH a,
    Subgroup.smul_bot]

theorem HConjInvariant.restrict {hyp : Hypothesis G A L} (hconj : hyp.HConjInvariant)
    (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    (hyp.restrict hA₁A hA₁_norm).HConjInvariant := by
  intro a l
  simpa [HConjInvariant] using hconj ⟨a.1, hA₁A a.2⟩ l

theorem hCoset_conj_mem_of_HConjInvariant (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) (a : {a : G // a ∈ A}) (l : L) {g : G}
    (hg : g ∈ hyp.hCoset a) :
    (l : G) * g * (l : G)⁻¹ ∈
      hyp.hCoset ⟨(l : G) * a.1 * (l : G)⁻¹, hyp.L_normalizes_A l a.2⟩ := by
  rcases hg with ⟨h, hh, rfl⟩
  refine ⟨(l : G) * h * (l : G)⁻¹, ?_, by group⟩
  have hh_smul :
      (MulAut.conj (l : G)) h ∈ MulAut.conj (l : G) • hyp.H a :=
    Subgroup.smul_mem_pointwise_smul h (MulAut.conj (l : G)) (hyp.H a) hh
  rw [hconj a l]
  simpa [MulAut.conj_apply] using hh_smul

theorem hCoset_conj_mem_iff_of_HConjInvariant (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) (a : {a : G // a ∈ A}) (l : L) {g : G} :
    (l : G) * g * (l : G)⁻¹ ∈
        hyp.hCoset ⟨(l : G) * a.1 * (l : G)⁻¹, hyp.L_normalizes_A l a.2⟩ ↔
      g ∈ hyp.hCoset a := by
  refine ⟨fun hg => ?_, hyp.hCoset_conj_mem_of_HConjInvariant hconj a l⟩
  have hg' := hyp.hCoset_conj_mem_of_HConjInvariant hconj
    ⟨(l : G) * a.1 * (l : G)⁻¹, hyp.L_normalizes_A l a.2⟩ l⁻¹ hg
  obtain ⟨h, hh, heq⟩ := hg'
  refine ⟨h, ?_, ?_⟩
  · have idx_val :
        ((l⁻¹ : L) : G) * ((l : G) * a.1 * (l : G)⁻¹) * ((l⁻¹ : L) : G)⁻¹ = a.1 := by
      push_cast; group
    have idx_eq :
        (⟨((l⁻¹ : L) : G) * ((l : G) * a.1 * (l : G)⁻¹) * ((l⁻¹ : L) : G)⁻¹,
          hyp.L_normalizes_A l⁻¹ (hyp.L_normalizes_A l a.2)⟩ : {a : G // a ∈ A}) = a :=
      Subtype.ext idx_val
    exact idx_eq ▸ hh
  · have lhs_eq :
        ((l⁻¹ : L) : G) * ((l : G) * g * (l : G)⁻¹) * ((l⁻¹ : L) : G)⁻¹ = g := by
      push_cast; group
    have rhs_eq :
        ((l⁻¹ : L) : G) * ((l : G) * a.1 * (l : G)⁻¹) * ((l⁻¹ : L) : G)⁻¹ * h = a.1 * h := by
      push_cast; group
    calc g = ((l⁻¹ : L) : G) * ((l : G) * g * (l : G)⁻¹) * ((l⁻¹ : L) : G)⁻¹ := lhs_eq.symm
      _ = ((l⁻¹ : L) : G) * ((l : G) * a.1 * (l : G)⁻¹) * ((l⁻¹ : L) : G)⁻¹ * h := heq
      _ = a.1 * h := rhs_eq

theorem hCoset_conj_eq_of_HConjInvariant (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) (a : {a : G // a ∈ A}) (l : L) :
    (fun g : G => (l : G) * g * (l : G)⁻¹) '' hyp.hCoset a =
      hyp.hCoset ⟨(l : G) * a.1 * (l : G)⁻¹, hyp.L_normalizes_A l a.2⟩ := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hyp.hCoset_conj_mem_of_HConjInvariant hconj a l hx
  · intro hg
    refine ⟨(l : G)⁻¹ * g * (l : G), ?_, by group⟩
    have hg_eq : (l : G) * ((l : G)⁻¹ * g * (l : G)) * (l : G)⁻¹ = g := by
      group
    have hmem :
        (l : G) * ((l : G)⁻¹ * g * (l : G)) * (l : G)⁻¹ ∈
          hyp.hCoset ⟨(l : G) * a.1 * (l : G)⁻¹, hyp.L_normalizes_A l a.2⟩ := by
      simpa [hg_eq] using hg
    exact (hyp.hCoset_conj_mem_iff_of_HConjInvariant hconj a l).mp hmem

/-- Every element of `H(a)` commutes with `a`, since `H(a) ≤ C_G(a)` by the
centralizer decomposition `(2.2.b)`. -/
theorem commute_of_mem_H (hyp : Hypothesis G A L) (a : {a : G // a ∈ A}) {u : G}
    (hu : u ∈ hyp.H a) : Commute a.1 u := by
  have hle : hyp.H a ≤ Subgroup.centralizer ({a.1} : Set G) := by
    rw [hyp.centralizer_eq_sup a]; exact le_sup_left
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hu)).symm

/-- `orderOf a` divides `|C_L(a)|`, since `a ∈ C_L(a)`. -/
theorem orderOf_dvd_card_centralizerIn (hyp : Hypothesis G A L)
    {a : G} (ha : a ∈ A) : orderOf a ∣ Nat.card (centralizerIn L a) :=
  (centralizerIn L a).orderOf_dvd_natCard
    (mem_centralizerIn.mpr ⟨hyp.mem_L ha, rfl⟩)

/-- **Peterfalvi (2.4.b).**  If `a * u` is conjugate in `G` to `b * v` for some
`u ∈ H(a)`, `v ∈ H(b)`, then `a` and `b` are conjugate in `L`.

This is the well-definedness input for the Dade map (2.5): conjugate cosets
`(aH(a))^G` come from `L`-conjugate base points.  The proof is the
`π`-part argument of Peterfalvi, packaged as `isConj_of_isConj_mul`. -/
theorem isConj_in_L_of_mul_H (hyp : Hypothesis G A L) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) {u v : G} (hu : u ∈ hyp.H ⟨a, ha⟩) (hv : v ∈ hyp.H ⟨b, hb⟩)
    (hconj : IsConj (a * u) (b * v)) :
    ∃ l : L, (l : G) * a * (l : G)⁻¹ = b := by
  set m : ℕ := Nat.card (hyp.H ⟨a, ha⟩) * Nat.card (hyp.H ⟨b, hb⟩) with hm
  -- coprimality of `orderOf a` (resp. `orderOf b`) with `m`
  have hcop_CL : ∀ {c : G} (hc : c ∈ A), Nat.Coprime (orderOf c) m := by
    intro c hc
    refine Nat.Coprime.coprime_dvd_left (hyp.orderOf_dvd_card_centralizerIn hc) ?_
    rw [hm]
    exact Nat.coprime_mul_iff_right.mpr
      ⟨(hyp.centralizer_coprime ⟨a, ha⟩ ⟨c, hc⟩).symm,
       (hyp.centralizer_coprime ⟨b, hb⟩ ⟨c, hc⟩).symm⟩
  have hum : orderOf u ∣ m :=
    ((hyp.H ⟨a, ha⟩).orderOf_dvd_natCard hu).trans (dvd_mul_right _ _)
  have hvm : orderOf v ∣ m :=
    ((hyp.H ⟨b, hb⟩).orderOf_dvd_natCard hv).trans (dvd_mul_left _ _)
  have hab : IsConj a b :=
    OddOrder.GroupTheory.isConj_of_isConj_mul (hyp.commute_of_mem_H ⟨a, ha⟩ hu)
      (hyp.commute_of_mem_H ⟨b, hb⟩ hv) (hcop_CL ha) (hcop_CL hb) hum hvm hconj
  exact hyp.conj_in_L ha hb hab

/-- **`|C_G(a)| = |H(a)| · |C_L(a)|`.**  The semidirect decomposition `(2.2.b)`
`C_G(a) = H(a) ⋊ C_L(a)` is order-multiplicative: `H(a)` is normal in `C_G(a)`
(`H_normalized`) and meets `C_L(a)` trivially (`centralizer_disjoint`), so the
multiplication map `H(a) × C_L(a) → C_G(a)` is a bijection. -/
theorem card_centralizer_eq (hyp : Hypothesis G A L) (a : {a : G // a ∈ A}) :
    Nat.card (Subgroup.centralizer ({a.1} : Set G))
      = Nat.card (hyp.H a) * Nat.card (centralizerIn L a.1) := by
  classical
  have hHC : hyp.H a ≤ Subgroup.centralizer ({a.1} : Set G) := by
    rw [hyp.centralizer_eq_sup a]; exact le_sup_left
  have hCLC : centralizerIn L a.1 ≤ Subgroup.centralizer ({a.1} : Set G) := by
    rw [hyp.centralizer_eq_sup a]; exact le_sup_right
  have hnorm : centralizerIn L a.1 ≤ Subgroup.normalizer (hyp.H a) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hcC : c ∈ Subgroup.centralizer ({a.1} : Set G) := hCLC hc
    refine ⟨fun hh => hyp.H_normalized a c hcC h hh, fun hh => ?_⟩
    have hmem := hyp.H_normalized a c⁻¹ (Subgroup.inv_mem _ hcC) _ hh
    have heq : c⁻¹ * (c * h * c⁻¹) * (c⁻¹)⁻¹ = h := by group
    rwa [heq] at hmem
  have hcoe : (↑(Subgroup.centralizer ({a.1} : Set G)) : Set G)
      = ↑(hyp.H a) * ↑(centralizerIn L a.1) := by
    rw [hyp.centralizer_eq_sup a]
    exact Subgroup.coe_mul_of_right_le_normalizer_left (hyp.H a) (centralizerIn L a.1) hnorm
  let f : (hyp.H a) × (centralizerIn L a.1) → Subgroup.centralizer ({a.1} : Set G) :=
    fun p => ⟨(p.1 : G) * (p.2 : G),
      (Subgroup.centralizer ({a.1} : Set G)).mul_mem (hHC p.1.2) (hCLC p.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun g => ?_⟩
    · have hval : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) :=
        congrArg Subtype.val hpq
      exact Subgroup.mul_injective_of_disjoint (hyp.centralizer_disjoint a) hval
    · have hmem : (g : G) ∈ (↑(hyp.H a) * ↑(centralizerIn L a.1) : Set G) := by
        rw [← hcoe]; exact g.2
      obtain ⟨h, hh, c, hc, hgeq⟩ := hmem
      exact ⟨(⟨h, hh⟩, ⟨c, hc⟩), Subtype.ext hgeq⟩
  calc Nat.card (Subgroup.centralizer ({a.1} : Set G))
      = Nat.card ((hyp.H a) × (centralizerIn L a.1)) :=
        (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = Nat.card (hyp.H a) * Nat.card (centralizerIn L a.1) := Nat.card_prod _ _

open Classical in
/-- **Orbit count for the (2.7) adjoint formula.**  For `g` in the Dade support,
the centralizers `|C_L(a)|`, summed over the `a ∈ A` whose coset `aH(a)` meets
the `G`-conjugacy class of `g`, total `|L|`.

The index set `{a : g ∈ (aH(a))^G}` is a single `L`-conjugacy class `a₀^L`
(`[2.4.b]` for `⊆`, `HConjInvariant` for `⊇`).  Mapping `l ↦ l a₀ l⁻¹` from `L`
onto it has fibers that are `C_L(a₀)`-cosets (`card_conjugatorIn_L`), and the
summand `|C_L(a)|` is constant `= |C_L(a₀)|` on the class
(`card_centralizerIn_conj`); fiberwise counting then gives `|L|`. -/
theorem sum_card_centralizerIn_eq [Fintype {a : G // a ∈ A}]
    (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant) {g : G}
    (hg : g ∈ hyp.dadeSupport) :
    ∑ a ∈ Finset.univ.filter
        (fun a : {a : G // a ∈ A} => ∃ x ∈ hyp.H a, IsConj (a.1 * x) g),
      Nat.card (centralizerIn L a.1) = Nat.card L := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  obtain ⟨a₀, x₀, hx₀, hca₀⟩ := hyp.mem_dadeSupport_iff.mp hg
  let φ : L → {a : G // a ∈ A} :=
    fun l => ⟨(l : G) * a₀.1 * (l : G)⁻¹, hyp.L_normalizes_A l a₀.2⟩
  set S := Finset.univ.filter
    (fun a : {a : G // a ∈ A} => ∃ x ∈ hyp.H a, IsConj (a.1 * x) g) with hS
  have hmaps : ∀ l : L, φ l ∈ S := by
    intro l
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (l : G) * x₀ * (l : G)⁻¹, ?_, ?_⟩
    · change (l : G) * x₀ * (l : G)⁻¹ ∈
        hyp.H ⟨(l : G) * a₀.1 * (l : G)⁻¹, hyp.L_normalizes_A l a₀.2⟩
      rw [hconj a₀ l]
      exact Subgroup.smul_mem_pointwise_smul x₀ (MulAut.conj (l : G)) (hyp.H a₀) hx₀
    · have heq : (φ l).1 * ((l : G) * x₀ * (l : G)⁻¹)
          = (l : G) * (a₀.1 * x₀) * (l : G)⁻¹ := by
        change ((l : G) * a₀.1 * (l : G)⁻¹) * ((l : G) * x₀ * (l : G)⁻¹)
          = (l : G) * (a₀.1 * x₀) * (l : G)⁻¹
        group
      have h1 : IsConj (a₀.1 * x₀) ((φ l).1 * ((l : G) * x₀ * (l : G)⁻¹)) := by
        rw [heq]; exact isConj_iff.mpr ⟨(l : G), rfl⟩
      exact h1.symm.trans hca₀
  have horbit : ∀ a ∈ S, ∃ l : L, (l : G) * a₀.1 * (l : G)⁻¹ = a.1 := by
    intro a ha
    rw [hS, Finset.mem_filter] at ha
    obtain ⟨x, hx, hax⟩ := ha.2
    exact hyp.isConj_in_L_of_mul_H a₀.2 a.2 hx₀ hx (hca₀.trans hax.symm)
  have hfiber : ∀ a ∈ S, (Finset.univ.filter (fun l : L => φ l = a)).card
      = Nat.card (centralizerIn L a.1) := by
    intro a ha
    obtain ⟨lₐ, hlₐ⟩ := horbit a ha
    have hcard1 : (Finset.univ.filter (fun l : L => φ l = a)).card
        = Nat.card {l : L // (l : G) * a₀.1 * (l : G)⁻¹ = a.1} := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype (fun l : L => φ l = a)]
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (fun l => Subtype.ext_iff)
    rw [hcard1, card_conjugatorIn_L ⟨lₐ, hlₐ⟩, ← hlₐ, card_centralizerIn_conj lₐ.2 a₀.1]
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := φ) (s := (Finset.univ : Finset L)) (t := S) (fun l _ => hmaps l)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hsum
  rw [hsum]
  exact Finset.sum_congr rfl (fun a ha => (hfiber a ha).symm)

open Classical in
/-- **Fiber regrouping for the (2.7) adjoint formula.**  For a fixed `a ∈ A` and
any `F : G → ℂ`, summing `F` over the conjugates `t(ax)t⁻¹` (`x ∈ H(a)`, `t ∈ G`)
collapses to a sum over the target values `b`, each weighted by the fiber size
`|C_G(a)|` (`card_conj_fiber`): a value `b` is hit iff `b ∈ (aH(a))^G`. -/
theorem fiber_regroup (hyp : Hypothesis G A L) (a : {a : G // a ∈ A})
    (F : G → ℂ) :
    ∑ x : hyp.H a, ∑ t : G, F ((t : G) * (a.1 * (x : G)) * (t : G)⁻¹)
      = ∑ b ∈ Finset.univ.filter (fun b : G => ∃ x ∈ hyp.H a, IsConj (a.1 * x) b),
          (Nat.card (Subgroup.centralizer ({a.1} : Set G)) : ℂ) * F b := by
  classical
  have hcomm : ∀ x ∈ hyp.H a, Commute a.1 x := fun x hx => hyp.commute_of_mem_H a hx
  have hcop : Nat.Coprime (orderOf a.1) (Nat.card (hyp.H a)) :=
    Nat.Coprime.coprime_dvd_left (hyp.orderOf_dvd_card_centralizerIn a.2)
      (hyp.centralizer_coprime a a).symm
  set ν : (hyp.H a) × G → G :=
    fun p => (p.2 : G) * (a.1 * (p.1 : G)) * (p.2 : G)⁻¹ with hν
  -- nested sum = sum over the product, then regroup by value
  have step1 : (∑ x : hyp.H a, ∑ t : G, F ((t : G) * (a.1 * (x : G)) * (t : G)⁻¹))
      = ∑ p : (hyp.H a) × G, F (ν p) := by rw [Fintype.sum_prod_type]
  rw [step1, ← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset G)) (g := ν)
      (fun p _ => Finset.mem_univ _) (f := fun p => F (ν p)),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hQ : ∃ x ∈ hyp.H a, IsConj (a.1 * x) b
  · rw [if_pos hQ]
    obtain ⟨x₀, hx₀, hx₀conj⟩ := hQ
    have hcard : (Finset.univ.filter (fun p : (hyp.H a) × G => ν p = b)).card
        = Nat.card (Subgroup.centralizer ({a.1} : Set G)) := by
      rw [← Fintype.card_subtype (fun p : (hyp.H a) × G => ν p = b),
        ← Nat.card_eq_fintype_card]
      rw [← OddOrder.GroupTheory.card_conj_fiber hcomm (hyp.H_normalized a) hcop hx₀ hx₀conj]
      apply Nat.card_congr
      exact
        { toFun := fun q => ⟨((q.1.1 : G), q.1.2), q.1.1.2, q.2⟩
          invFun := fun q => ⟨(⟨q.1.1, q.2.1⟩, q.1.2), q.2.2⟩
          left_inv := fun q => rfl
          right_inv := fun q => rfl }
    calc ∑ p ∈ Finset.univ.filter (fun p : (hyp.H a) × G => ν p = b), F (ν p)
        = ∑ _p ∈ Finset.univ.filter (fun p : (hyp.H a) × G => ν p = b), F b :=
          Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2])
      _ = (Finset.univ.filter (fun p : (hyp.H a) × G => ν p = b)).card • F b :=
          Finset.sum_const _
      _ = (Nat.card (Subgroup.centralizer ({a.1} : Set G)) : ℂ) * F b := by
          rw [hcard, nsmul_eq_mul]
  · rw [if_neg hQ]
    apply Finset.sum_eq_zero
    intro p hp
    exact absurd ⟨p.1, p.1.2, by
      rw [← (Finset.mem_filter.mp hp).2]; exact isConj_iff.mpr ⟨(p.2 : G), rfl⟩⟩ hQ

/- 2.8: The semidirect structure `M(B) = H(B) ⋊ N_L(B)` (pp. 12) -/

section SemidirectStructure

open scoped Classical in
/-- For `l ∈ L` and `a ∈ A`, the conjugate `l · a · l⁻¹` as an element of the subtype
`{a : G // a ∈ A}`, using `L_normalizes_A`.  This is the conjugation action of `L` on `A`
used to define `N_L(B)`. -/
def conjA (hyp : Hypothesis G A L) (l : L) (a : {a : G // a ∈ A}) : {a : G // a ∈ A} :=
  ⟨(l : G) * a.1 * (l : G)⁻¹, hyp.L_normalizes_A l a.2⟩

@[simp] theorem conjA_coe (hyp : Hypothesis G A L) (l : L) (a : {a : G // a ∈ A}) :
    (hyp.conjA l a).1 = (l : G) * a.1 * (l : G)⁻¹ := rfl

theorem conjA_one (hyp : Hypothesis G A L) (a : {a : G // a ∈ A}) :
    hyp.conjA 1 a = a := by
  apply Subtype.ext; simp

theorem conjA_mul (hyp : Hypothesis G A L) (l₁ l₂ : L) (a : {a : G // a ∈ A}) :
    hyp.conjA (l₁ * l₂) a = hyp.conjA l₁ (hyp.conjA l₂ a) := by
  apply Subtype.ext
  simp only [conjA_coe, Subgroup.coe_mul, mul_inv_rev]
  group

theorem conjA_inv_conjA (hyp : Hypothesis G A L) (l : L) (a : {a : G // a ∈ A}) :
    hyp.conjA l⁻¹ (hyp.conjA l a) = a := by
  rw [← conjA_mul, inv_mul_cancel, conjA_one]

theorem conjA_conjA_inv (hyp : Hypothesis G A L) (l : L) (a : {a : G // a ∈ A}) :
    hyp.conjA l (hyp.conjA l⁻¹ a) = a := by
  rw [← conjA_mul, mul_inv_cancel, conjA_one]

/-- **Peterfalvi (2.8), `H(B)`.**  For a nonempty `B ⊆ A`, the subgroup
`H(B) = ⋂_{a ∈ B} H(a)`. -/
noncomputable def hIntersection (hyp : Hypothesis G A L)
    (B : Finset {a : G // a ∈ A}) (hB : B.Nonempty) : Subgroup G :=
  B.inf' hB (fun a => hyp.H a)

theorem hIntersection_le (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) {a : {a : G // a ∈ A}}
    (ha : a ∈ B) : hIntersection hyp B hB ≤ hyp.H a :=
  Finset.inf'_le _ ha

theorem mem_hIntersection (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) {x : G} :
    x ∈ hIntersection hyp B hB ↔ ∀ a ∈ B, x ∈ hyp.H a := by
  classical
  refine ⟨fun hx a ha => hIntersection_le hyp hB ha hx, fun hx => ?_⟩
  rw [hIntersection]
  induction hB using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hx a (by simp)
  | cons a s ha hs ih =>
      rw [Finset.inf'_cons hs]
      exact Subgroup.mem_inf.mpr
        ⟨hx a (by simp), ih (fun b hb => hx b (by simp [hb]))⟩

/-- **Peterfalvi (2.8), `N_L(B)`.**  The `L`-set-stabilizer of `B` under conjugation:
`{ℓ ∈ L | ℓ permutes B}`.  Mathlib's `Subgroup.setNormalizer` is `Subgroup.normalizer`
(defined for subgroups, not a `Finset`), so `N_L(B)` is built by hand here.  Closure under
inverses uses that conjugation by `ℓ` is an injective self-map of the finite set `B`, hence
surjective. -/
noncomputable def setLStabilizer (hyp : Hypothesis G A L)
    (B : Finset {a : G // a ∈ A}) : Subgroup L where
  carrier := {l : L | ∀ a ∈ B, hyp.conjA l a ∈ B}
  one_mem' := by intro a ha; rwa [conjA_one]
  mul_mem' {x y} hx hy := by
    intro a ha; rw [conjA_mul]; exact hx _ (hy a ha)
  inv_mem' {x} hx := by
    classical
    intro a ha
    -- conjugation by `x` is an injective `MapsTo B B`, hence surjective on `B`
    have hmaps : Set.MapsTo (hyp.conjA x) (B : Set {a : G // a ∈ A}) B := fun b hb => hx b hb
    have hinj : Set.InjOn (hyp.conjA x) (B : Set {a : G // a ∈ A}) := by
      intro b _ c _ hbc
      have := congrArg (hyp.conjA x⁻¹) hbc
      rwa [conjA_inv_conjA, conjA_inv_conjA] at this
    have hsurj : Set.SurjOn (hyp.conjA x) (B : Set {a : G // a ∈ A}) B :=
      Finset.surjOn_of_injOn_of_card_le (hyp.conjA x) hmaps hinj le_rfl
    obtain ⟨b, hb, hbeq⟩ := hsurj (Finset.mem_coe.mpr ha)
    -- `x b x⁻¹ = a`, so `x⁻¹ a x = b ∈ B`
    have hba : hyp.conjA x⁻¹ a = b := by rw [← hbeq, conjA_inv_conjA]
    rw [hba]; exact Finset.mem_coe.mp hb

@[simp] theorem mem_setLStabilizer (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} {l : L} :
    l ∈ setLStabilizer hyp B ↔ ∀ a ∈ B, hyp.conjA l a ∈ B := Iff.rfl

/-- `N_L(B)`, viewed as a subgroup of the ambient group `G` (via `L.subtype`).  This is the
right factor `N_L(B)` of `M(B) = H(B) · N_L(B)`. -/
noncomputable def nLStabilizerIn (hyp : Hypothesis G A L)
    (B : Finset {a : G // a ∈ A}) : Subgroup G :=
  (setLStabilizer hyp B).map L.subtype

theorem nLStabilizerIn_le_L (hyp : Hypothesis G A L)
    (B : Finset {a : G // a ∈ A}) : nLStabilizerIn hyp B ≤ L := by
  rw [nLStabilizerIn]
  rintro _ ⟨l, _, rfl⟩
  exact l.2

theorem mem_nLStabilizerIn (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} {x : G} :
    x ∈ nLStabilizerIn hyp B ↔
      ∃ hx : x ∈ L, (⟨x, hx⟩ : L) ∈ setLStabilizer hyp B := by
  rw [nLStabilizerIn]
  constructor
  · rintro ⟨l, hl, rfl⟩; exact ⟨l.2, by simpa using hl⟩
  · rintro ⟨hx, hl⟩; exact ⟨⟨x, hx⟩, hl, rfl⟩

/-- Membership in the conjugated subgroup `H(ℓ·a·ℓ⁻¹)`, via `(2.4.a)` `HConjInvariant`:
`y ∈ H(conjA l a) ↔ ℓ⁻¹ y ℓ ∈ H(a)`. -/
theorem mem_H_conjA_iff (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (a : {a : G // a ∈ A}) (l : L) {y : G} :
    y ∈ hyp.H (hyp.conjA l a) ↔ (l : G)⁻¹ * y * (l : G) ∈ hyp.H a := by
  have hHeq : hyp.H (hyp.conjA l a) = MulAut.conj (l : G) • hyp.H a := hconj a l
  rw [hHeq, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rw [show ((MulAut.conj (l : G))⁻¹ • y) = (MulAut.conj (l : G))⁻¹ y from rfl,
    MulAut.conj_inv_apply]

/-- **Peterfalvi (2.8), normality.**  `N_L(B)` normalizes `H(B)`.

By `(2.4.a)`, conjugation by `ℓ ∈ N_L(B)` sends `H(a)` to `H(ℓ·a·ℓ⁻¹)`; since `ℓ` permutes
`B`, it sends `H(B) = ⋂_{a∈B} H(a)` to itself. -/
theorem nLStabilizerIn_le_normalizer (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    nLStabilizerIn hyp B ≤ Subgroup.normalizer (hIntersection hyp B hB) := by
  intro x hx
  obtain ⟨hxL, hxN⟩ := (mem_nLStabilizerIn hyp).mp hx
  set l : L := ⟨x, hxL⟩ with hl
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_hIntersection, mem_hIntersection]
  have hlx : (l : G) = x := rfl
  have hlinv : ((l⁻¹ : L) : G) = x⁻¹ := by rw [Subgroup.coe_inv, hlx]
  constructor
  · -- `y ∈ H(B)` ⇒ `x y x⁻¹ ∈ H(B)`: for `a ∈ B`, `x⁻¹ a x ∈ B` (ℓ permutes B)
    intro hy a ha
    have hpre : hyp.conjA l⁻¹ a ∈ B :=
      ((setLStabilizer hyp B).inv_mem hxN) a ha
    have hmem := hy (hyp.conjA l⁻¹ a) hpre
    rw [mem_H_conjA_iff hyp hconj, hlinv] at hmem
    -- `hmem : (x⁻¹)⁻¹ * y * x⁻¹ ∈ H(a)`
    rwa [show (x⁻¹)⁻¹ * y * x⁻¹ = x * y * x⁻¹ from by group] at hmem
  · -- `x y x⁻¹ ∈ H(B)` ⇒ `y ∈ H(B)`
    intro hy a ha
    have hmem := hy (hyp.conjA l a) (hxN a ha)
    rw [mem_H_conjA_iff hyp hconj, hlx] at hmem
    -- `hmem : x⁻¹ * (x * y * x⁻¹) * x ∈ H(a)`
    rwa [show x⁻¹ * (x * y * x⁻¹) * x = y from by group] at hmem

/-- **Peterfalvi (2.8), disjointness.**  `H(B) ∩ N_L(B) = 1`.

For any `a ∈ B`: `x ∈ H(B) ∩ N_L(B)` gives `x ∈ H(a)` (so `x` commutes with `a` by the
centralizer decomposition `(2.2.b)`) and `x ∈ L`, hence `x ∈ C_L(a)`; but
`H(a) ∩ C_L(a) = 1` (`centralizer_disjoint`), so `x = 1`. -/
theorem hIntersection_disjoint_nLStabilizerIn (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    Disjoint (hIntersection hyp B hB) (nLStabilizerIn hyp B) := by
  obtain ⟨a, ha⟩ := hB.exists_mem
  rw [disjoint_iff_inf_le]
  intro x hx
  obtain ⟨hxH, hxN⟩ := Subgroup.mem_inf.mp hx
  have hxHa : x ∈ hyp.H a := hIntersection_le hyp hB ha hxH
  have hxL : x ∈ L := nLStabilizerIn_le_L hyp B hxN
  have hxCL : x ∈ centralizerIn L a.1 :=
    mem_centralizerIn.mpr ⟨hxL, (hyp.commute_of_mem_H a hxHa).symm⟩
  exact (disjoint_iff_inf_le.mp (hyp.centralizer_disjoint a)) (Subgroup.mem_inf.mpr ⟨hxHa, hxCL⟩)

/-- **Peterfalvi (2.8), `M(B)`.**  `M(B) = H(B) · N_L(B)`, as the join subgroup
`H(B) ⊔ N_L(B)` of `G`. -/
noncomputable def mBSubgroup (hyp : Hypothesis G A L)
    (B : Finset {a : G // a ∈ A}) (hB : B.Nonempty) : Subgroup G :=
  hIntersection hyp B hB ⊔ nLStabilizerIn hyp B

/-- The underlying set of `M(B) = H(B) ⊔ N_L(B)` is the product `H(B) · N_L(B)`, because
`N_L(B)` normalizes `H(B)` (`(2.4.a)`). -/
theorem coe_mBSubgroup (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    (↑(mBSubgroup hyp B hB) : Set G)
      = (↑(hIntersection hyp B hB) : Set G) * (↑(nLStabilizerIn hyp B) : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (hyp.nLStabilizerIn_le_normalizer hconj hB)

/-- **Peterfalvi (2.8), the semidirect order identity.**  `|M(B)| = |H(B)| · |N_L(B)|`.

This is the internal-semidirect-product content of `M(B) = H(B) ⋊ N_L(B)`: the
multiplication map `H(B) × N_L(B) → M(B)` is a bijection, because `N_L(B)` normalizes
`H(B)` (`(2.4.a)`, gives the product is `M(B)`) and `H(B) ∩ N_L(B) = 1`
(`hIntersection_disjoint_nLStabilizerIn`, gives injectivity).  Same argument as
`card_centralizer_eq`. -/
theorem card_mBSubgroup (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    Nat.card (mBSubgroup hyp B hB)
      = Nat.card (hIntersection hyp B hB) * Nat.card (nLStabilizerIn hyp B) := by
  classical
  have hHle : hIntersection hyp B hB ≤ mBSubgroup hyp B hB := le_sup_left
  have hNle : nLStabilizerIn hyp B ≤ mBSubgroup hyp B hB := le_sup_right
  have hcoe := hyp.coe_mBSubgroup hconj hB
  let f : (hIntersection hyp B hB) × (nLStabilizerIn hyp B) → mBSubgroup hyp B hB :=
    fun p => ⟨(p.1 : G) * (p.2 : G),
      (mBSubgroup hyp B hB).mul_mem (hHle p.1.2) (hNle p.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun g => ?_⟩
    · have hval : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) :=
        congrArg Subtype.val hpq
      exact Subgroup.mul_injective_of_disjoint
        (hyp.hIntersection_disjoint_nLStabilizerIn hB) hval
    · have hmem : (g : G) ∈
          (↑(hIntersection hyp B hB) * ↑(nLStabilizerIn hyp B) : Set G) := by
        rw [← hcoe]; exact g.2
      obtain ⟨h, hh, n, hn, hgeq⟩ := hmem
      exact ⟨(⟨h, hh⟩, ⟨n, hn⟩), Subtype.ext hgeq⟩
  calc Nat.card (mBSubgroup hyp B hB)
      = Nat.card ((hIntersection hyp B hB) × (nLStabilizerIn hyp B)) :=
        (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = Nat.card (hIntersection hyp B hB) * Nat.card (nLStabilizerIn hyp B) :=
        Nat.card_prod _ _

theorem hIntersection_le_mBSubgroup (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    hIntersection hyp B hB ≤ mBSubgroup hyp B hB := le_sup_left

theorem nLStabilizerIn_le_mBSubgroup (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    nLStabilizerIn hyp B ≤ mBSubgroup hyp B hB := le_sup_right

/-- `H(B)` is normal in `M(B)`: `M(B) = H(B) ⊔ N_L(B)` and both factors normalize `H(B)`
(self-normalization and `(2.4.a)` for `N_L(B)`). -/
theorem hIntersection_subgroupOf_normal (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    ((hIntersection hyp B hB).subgroupOf (mBSubgroup hyp B hB)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hyp.hIntersection_le_mBSubgroup hB)]
  rw [mBSubgroup]
  exact sup_le (hIntersection hyp B hB).le_normalizer
    (hyp.nLStabilizerIn_le_normalizer hconj hB)

/-- `H(B)` and `N_L(B)` are complementary subgroups inside `M(B)`: this is the internal
semidirect decomposition `M(B) = H(B) ⋊ N_L(B)` as a `Subgroup.IsComplement'`. -/
theorem isComplement'_subgroupOf (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    Subgroup.IsComplement'
      ((nLStabilizerIn hyp B).subgroupOf (mBSubgroup hyp B hB))
      ((hIntersection hyp B hB).subgroupOf (mBSubgroup hyp B hB)) := by
  haveI : Finite (mBSubgroup hyp B hB) := Subtype.finite
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · -- `|N_sub| · |H_sub| = |M(B)|`
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hyp.nLStabilizerIn_le_mBSubgroup hB)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hyp.hIntersection_le_mBSubgroup hB)).toEquiv,
      mul_comm, ← hyp.card_mBSubgroup hconj hB]
  · -- disjointness of the lifted subgroups
    rw [disjoint_iff_inf_le]
    intro x hx
    obtain ⟨hxN, hxH⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_subgroupOf] at hxN hxH
    have hxbot := (disjoint_iff_inf_le.mp
      (hyp.hIntersection_disjoint_nLStabilizerIn hB)) (Subgroup.mem_inf.mpr ⟨hxH, hxN⟩)
    rw [Subgroup.mem_bot] at hxbot
    rw [Subgroup.mem_bot]
    exact Subtype.ext hxbot

/-- **Peterfalvi (2.9), `f_B`.**  The natural homomorphism `f_B : M(B) →* L` with kernel
`H(B)`, coming from the semidirect decomposition `M(B) = H(B) ⋊ N_L(B)`.

Concretely `f_B` is the composite `M(B) → M(B)/H(B) ≅ N_L(B) ↪ L`, where the middle
isomorphism is `IsComplement'.QuotientMulEquiv` (`H(B)` normal, `N_L(B)` a complement) and
the last map is the inclusion `N_L(B) ≤ L`. -/
noncomputable def dadeQuotientHom (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    mBSubgroup hyp B hB →* L :=
  haveI : ((hIntersection hyp B hB).subgroupOf (mBSubgroup hyp B hB)).Normal :=
    hyp.hIntersection_subgroupOf_normal hconj hB
  (Subgroup.inclusion (hyp.nLStabilizerIn_le_L B)).comp
    (((Subgroup.subgroupOfEquivOfLe (hyp.nLStabilizerIn_le_mBSubgroup hB)).toMonoidHom).comp
      ((hyp.isComplement'_subgroupOf hconj hB).QuotientMulEquiv.toMonoidHom.comp
        (QuotientGroup.mk' _)))

/-- **`f_B` has kernel `H(B)`.**  Confirms the Peterfalvi (2.9) description of `f_B` as "the
natural homomorphism `M(B) → L` with kernel `H(B)`": everything after the quotient map
`mk' : M(B) → M(B)/H(B)` is injective (an isomorphism followed by the inclusion
`N_L(B) ≤ L`), so `ker f_B = ker mk' = H(B)` (as a subgroup of `M(B)`). -/
theorem ker_dadeQuotientHom (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    (hyp.dadeQuotientHom hconj hB).ker
      = (hIntersection hyp B hB).subgroupOf (mBSubgroup hyp B hB) := by
  haveI : ((hIntersection hyp B hB).subgroupOf (mBSubgroup hyp B hB)).Normal :=
    hyp.hIntersection_subgroupOf_normal hconj hB
  -- the post-`mk'` part of `f_B`
  set post :=
      (Subgroup.inclusion (hyp.nLStabilizerIn_le_L B)).comp
        (((Subgroup.subgroupOfEquivOfLe (hyp.nLStabilizerIn_le_mBSubgroup hB)).toMonoidHom).comp
          (hyp.isComplement'_subgroupOf hconj hB).QuotientMulEquiv.toMonoidHom) with hpost
  have hinj : Function.Injective post := by
    rw [hpost]
    refine (Set.inclusion_injective (hyp.nLStabilizerIn_le_L B)).comp ?_
    exact (Subgroup.subgroupOfEquivOfLe (hyp.nLStabilizerIn_le_mBSubgroup hB)).injective.comp
      (hyp.isComplement'_subgroupOf hconj hB).QuotientMulEquiv.injective
  have hfB : hyp.dadeQuotientHom hconj hB = post.comp (QuotientGroup.mk' _) := rfl
  rw [hfB]
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
  rw [← map_one post, hinj.eq_iff, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']

/-- **Peterfalvi (2.9), `α_B`.**  For `α ∈ CF(L)` and a nonempty `B ⊆ A`, the class function
`α_B = α ∘ f_B` on `M(B)`. -/
noncomputable def alphaB (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) (α : ClassFunction L ℂ) :
    ClassFunction (mBSubgroup hyp B hB) ℂ :=
  ClassFunction.compHom (hyp.dadeQuotientHom hconj hB) α

/-- **Peterfalvi (2.9), virtual-character preservation.**  If `α` is a virtual character of
`L`, then `α_B` is a virtual character of `M(B)`.

Since `α_B = α ∘ f_B` is the pullback of `α` along the group hom `f_B : M(B) →* L`, this is
the general `ClassFunction.compHom_mem_ZIrr` (pullback preserves `ℤ[Irr]`), which holds
because the character of *any* finite-dimensional representation lies in `ℤ[Irr]`. -/
theorem alphaB_mem_ZIrr (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) {α : ClassFunction L ℂ}
    (hα : α ∈ ZIrr L) :
    alphaB hyp hconj hB α ∈ ZIrr (mBSubgroup hyp B hB) := by
  haveI : Finite (mBSubgroup hyp B hB) := Subtype.finite
  exact ClassFunction.compHom_mem_ZIrr (hyp.dadeQuotientHom hconj hB) hα

end SemidirectStructure

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

theorem map_eq_of_mem_hCoset {hyp : Hypothesis G A L} {τ : DadeMap (G := G) k A L}
    (hτ : IsDadeMap hyp τ) (α : SupportedClassFunctions (G := G) k A L)
    (a : {a : G // a ∈ A}) {g : G} (hg : g ∈ hyp.hCoset a) :
    τ α g = (α : ClassFunction L k) ⟨a.1, hyp.mem_L a.2⟩ := by
  rcases hg with ⟨h, hh, rfl⟩
  exact hτ.map_eq_of_isConj_hCoset α (a.1 * h) a h hh (IsConj.refl _)

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

/-- In the TI-specialized case `H(a)=1`, the Dade-map equation is simply
constant on `G`-conjugates of elements of `A`. -/
theorem map_eq_of_isConj_of_forall_H_eq_bot {hyp : Hypothesis G A L}
    {τ : DadeMap (G := G) k A L} (hτ : IsDadeMap hyp τ)
    (hH : ∀ a : {a : G // a ∈ A}, hyp.H a = ⊥)
    (α : SupportedClassFunctions (G := G) k A L) {a g : G} (ha : a ∈ A)
    (hconj : IsConj a g) :
    τ α g = (α : ClassFunction L k) ⟨a, hyp.mem_L ha⟩ := by
  simpa using hτ.map_eq_of_isConj_hCoset α g ⟨a, ha⟩ 1
    (by simp [hH ⟨a, ha⟩]) (by simpa using hconj)

theorem map_eq_of_mem_A_of_forall_H_eq_bot {hyp : Hypothesis G A L}
    {τ : DadeMap (G := G) k A L} (hτ : IsDadeMap hyp τ)
    (hH : ∀ a : {a : G // a ∈ A}, hyp.H a = ⊥)
    (α : SupportedClassFunctions (G := G) k A L) {a : G} (ha : a ∈ A) :
    τ α a = (α : ClassFunction L k) ⟨a, hyp.mem_L ha⟩ :=
  map_eq_of_isConj_of_forall_H_eq_bot hτ hH α ha (IsConj.refl a)

/-- In the TI-specialized case `H(a)=1`, a Dade map vanishes outside the
conjugacy-saturation of `A`. -/
theorem map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot
    {hyp : Hypothesis G A L} {τ : DadeMap (G := G) k A L} (hτ : IsDadeMap hyp τ)
    (hH : ∀ a : {a : G // a ∈ A}, hyp.H a = ⊥)
    (α : SupportedClassFunctions (G := G) k A L) {g : G}
    (hg : g ∉ Group.conjugatesOfSet A) :
    τ α g = 0 := by
  apply hτ.map_eq_zero_of_not_mem_dadeSupport
  rwa [hyp.dadeSupport_eq_conjugatesOfSet_of_forall_H_eq_bot hH]

end IsDadeMap

/-- Peterfalvi (2.6.b): a complex Dade map sends supported virtual characters
on `L` to virtual characters of `G`.

The domain is still represented by the complex supported class-function space
`CF(L,A)`; the hypothesis says that, whenever such a supported class function
also lies in the integral lattice `ℤ[Irr L]`, its image lies in `ℤ[Irr G]`. -/
def PreservesVirtualCharacters (τ : DadeMap (G := G) ℂ A L) : Prop :=
  ∀ α : SupportedClassFunctions (G := G) ℂ A L,
    ((α : ClassFunction L ℂ) ∈ ZIrr L) → τ α ∈ ZIrr G

namespace PreservesVirtualCharacters

/-- Virtual-character preservation restricts along `A₁ ⊆ A`.

This is the `(2.6.b)` companion to the restriction statement in Peterfalvi
(2.11). -/
theorem restrictDomain {τ : DadeMap (G := G) ℂ A L}
    (hτ : PreservesVirtualCharacters (G := G) (A := A) (L := L) τ)
    (hA₁A : A₁ ⊆ A) :
    PreservesVirtualCharacters (G := G) (A := A₁) (L := L)
      (DadeMap.restrictDomain (G := G) (k := ℂ) (L := L) τ hA₁A) := by
  intro α hα
  exact hτ
    (SupportedClassFunctions.inclusion (G := G) (k := ℂ) (L := L) hA₁A α)
    (by simpa using hα)

end PreservesVirtualCharacters

variable [StarRing k]
variable [Fintype G] [Fintype L]
variable [Invertible (Nat.card G : k)] [Invertible (Nat.card L : k)]

/-- The coefficient-parametric part of the Dade isometry interface:
preservation of Peterfalvi's normalized class-function inner product. -/
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

/-- A bundled Dade isometry candidate relative to `hyp`.

This packages the pointwise equations from Peterfalvi (2.5) together with the
coefficient-parametric normalized inner-product part of (2.6.a).  The
complex-coefficient full bundle below adds the virtual-character preservation
property from (2.6.b). -/
structure DadeIsometryData (hyp : Hypothesis G A L) where
  toDadeMap : DadeMap (G := G) k A L
  isDadeMap : IsDadeMap hyp toDadeMap
  isDadeIsometry : IsDadeIsometry toDadeMap

namespace DadeIsometryData

variable {hyp : Hypothesis G A L}

instance : CoeFun (DadeIsometryData (G := G) (k := k) hyp)
    (fun _ => DadeMap (G := G) k A L) :=
  ⟨fun τ => τ.toDadeMap⟩

@[simp] theorem coe_mk (τ : DadeMap (G := G) k A L)
    (hmap : IsDadeMap hyp τ) (hiso : IsDadeIsometry τ) :
    ((DadeIsometryData.mk τ hmap hiso : DadeIsometryData (G := G) (k := k) hyp) :
      DadeMap (G := G) k A L) = τ :=
  rfl

/-- Restrict a bundled Dade isometry to an `L`-stable subset `A₁ ⊆ A`.

This is the bundled form of the currently available part of Peterfalvi (2.11). -/
def restrict (τ : DadeIsometryData (G := G) (k := k) hyp) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    DadeIsometryData (G := G) (k := k) (hyp.restrict hA₁A hA₁_norm) where
  toDadeMap := DadeMap.restrictDomain (G := G) (k := k) (L := L) τ.toDadeMap hA₁A
  isDadeMap := IsDadeMap.restrictDomain τ.isDadeMap hA₁A hA₁_norm
  isDadeIsometry := IsDadeIsometry.restrictDomain τ.isDadeIsometry hA₁A

@[simp] theorem restrict_toDadeMap
    (τ : DadeIsometryData (G := G) (k := k) hyp) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    (τ.restrict hA₁A hA₁_norm).toDadeMap =
      DadeMap.restrictDomain (G := G) (k := k) (L := L) τ.toDadeMap hA₁A :=
  rfl

@[simp] theorem restrict_apply
    (τ : DadeIsometryData (G := G) (k := k) hyp) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (α : SupportedClassFunctions (G := G) k A₁ L) :
    (τ.restrict hA₁A hA₁_norm).toDadeMap α =
      τ.toDadeMap (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α) :=
  rfl

end DadeIsometryData

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card L : ℂ)]

/-- The full complex Dade-isometry interface used by Peterfalvi after (2.6):
the Dade-map equations, normalized isometry, and preservation of virtual
characters. -/
structure FullDadeIsometryData (hyp : Hypothesis G A L) where
  toDadeIsometryData : DadeIsometryData (G := G) (k := ℂ) hyp
  preserves_virtualCharacters :
    PreservesVirtualCharacters (G := G) (A := A) (L := L) toDadeIsometryData.toDadeMap

namespace FullDadeIsometryData

variable {hyp : Hypothesis G A L}

/-- The underlying Dade map of a full complex Dade-isometry package. -/
abbrev toDadeMap (τ : FullDadeIsometryData (G := G) hyp) : DadeMap (G := G) ℂ A L :=
  τ.toDadeIsometryData.toDadeMap

instance : CoeFun (FullDadeIsometryData (G := G) hyp)
    (fun _ => DadeMap (G := G) ℂ A L) :=
  ⟨fun τ => τ.toDadeMap⟩

@[simp] theorem coe_mk (τ : DadeIsometryData (G := G) (k := ℂ) hyp)
    (hvirt : PreservesVirtualCharacters (G := G) (A := A) (L := L) τ.toDadeMap) :
    ((FullDadeIsometryData.mk τ hvirt : FullDadeIsometryData (G := G) hyp) :
      DadeMap (G := G) ℂ A L) = τ.toDadeMap :=
  rfl

theorem inner_eq (τ : FullDadeIsometryData (G := G) hyp)
    (α β : SupportedClassFunctions (G := G) ℂ A L) :
    ClassFunction.inner (τ.toDadeMap α) (τ.toDadeMap β) =
      ClassFunction.inner (α : ClassFunction L ℂ) (β : ClassFunction L ℂ) :=
  τ.toDadeIsometryData.isDadeIsometry.inner_eq α β

theorem maps_virtualCharacter (τ : FullDadeIsometryData (G := G) hyp)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    (hα : (α : ClassFunction L ℂ) ∈ ZIrr L) :
    τ.toDadeMap α ∈ ZIrr G :=
  τ.preserves_virtualCharacters α hα

/-- Restrict a full complex Dade isometry to an `L`-stable subset `A₁ ⊆ A`. -/
def restrict (τ : FullDadeIsometryData (G := G) hyp) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    FullDadeIsometryData (G := G) (hyp.restrict hA₁A hA₁_norm) where
  toDadeIsometryData := τ.toDadeIsometryData.restrict hA₁A hA₁_norm
  preserves_virtualCharacters :=
    PreservesVirtualCharacters.restrictDomain τ.preserves_virtualCharacters hA₁A

@[simp] theorem restrict_toDadeMap
    (τ : FullDadeIsometryData (G := G) hyp) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    (τ.restrict hA₁A hA₁_norm).toDadeMap =
      DadeMap.restrictDomain (G := G) (k := ℂ) (L := L) τ.toDadeMap hA₁A :=
  by simp [restrict, toDadeMap, DadeIsometryData.restrict]

@[simp] theorem restrict_apply
    (τ : FullDadeIsometryData (G := G) hyp) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (α : SupportedClassFunctions (G := G) ℂ A₁ L) :
    (τ.restrict hA₁A hA₁_norm).toDadeMap α =
      τ.toDadeMap (SupportedClassFunctions.inclusion (G := G) (k := ℂ) (L := L) hA₁A α) :=
  by simp [restrict, toDadeMap, DadeIsometryData.restrict]

end FullDadeIsometryData

section AdjointFormula

variable (hyp : Hypothesis G A L)

/-- The Peterfalvi (2.7) **adjoint averaging map**: given `χ : ClassFunction G ℂ`,
this is the function `L → ℂ` defined on `A` by `a ↦ |H(a)|⁻¹ ∑_{x ∈ H(a)} χ(ax)`,
and zero off `A`.  Classical logic is used to decide membership in `A` and to
provide a `Fintype` for `↥(hyp.H a)` from `[Fintype G]`. -/
noncomputable def adjointAverageFun (χ : ClassFunction G ℂ) : L → ℂ := by
  intro ℓ
  classical
  exact if h : (ℓ : G) ∈ A then
    (Nat.card ↥(hyp.H ⟨(ℓ : G), h⟩) : ℂ)⁻¹ *
      ∑ x : ↥(hyp.H ⟨(ℓ : G), h⟩), χ ((ℓ : G) * (x : G))
  else 0

/-- **Peterfalvi (2.7) adjoint formula.**

Given a candidate Dade map `τ` satisfying the (2.5) defining equations on the
support of `α : CF(L, A)`, a class function `χ : ClassFunction G ℂ`, and a
class function `ψ : ClassFunction L ℂ` whose values on `A` average `χ` along
the cosets `aH(a)`:

    ψ(a) = |H(a)|⁻¹ · ∑_{x ∈ H(a)} χ(ax)    (a ∈ A),

the inner products satisfy `⟨τ α, χ⟩_G = ⟨α, ψ⟩_L`.

In Peterfalvi's textbook this is proved by rewriting `⟨τ α, χ⟩_G` as a sum over
G-conjugacy class representatives of `A`, using (2.4) and the defining equation
(2.5).  The Lean statement keeps `ψ` as an explicit input; the special case
`ψ = Res_L^G χ` (with `χ` constant on each `aH(a)`) is the form used in the
proof of Theorem (2.6.a).

This lemma is Peterfalvi §4's heaviest external export: §7 (5.4), §9 (7.2.b),
§12 (9.5) ×2, §13 (10.3), §16 (14.1) ×2 all apply it directly (audit
2026-05-23). -/
theorem adjoint_formula
    (τ : DadeMap (G := G) (k := ℂ) A L) (hτ : IsDadeMap hyp τ)
    (hconj : hyp.HConjInvariant)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    (χ : ClassFunction G ℂ) (ψ : ClassFunction L ℂ)
    (hψ : ∀ a : {a : G // a ∈ A},
        ψ ⟨a.1, hyp.subset_L a.2⟩ =
          adjointAverageFun hyp χ ⟨a.1, hyp.subset_L a.2⟩) :
    ClassFunction.inner (τ α) χ =
      ClassFunction.inner (α : ClassFunction L ℂ) ψ := by
  classical
  letI : Fintype {a : G // a ∈ A} := Fintype.ofFinite _
  set aα : {a : G // a ∈ A} → ℂ :=
    fun a => (α : ClassFunction L ℂ) ⟨a.1, hyp.subset_L a.2⟩ with haα
  set F : G → ℂ := fun g => (τ α) g * star (χ g) with hF
  set M : ℂ := ∑ a : {a : G // a ∈ A}, ∑ x : hyp.H a, ∑ t : G,
      (Nat.card (hyp.H a) : ℂ)⁻¹ * aα a *
        star (χ ((t : G) * (a.1 * (x : G)) * (t : G)⁻¹)) with hM
  -- |H(a)| ≠ 0 in ℂ
  have hHne : ∀ a : {a : G // a ∈ A}, (Nat.card (hyp.H a) : ℂ) ≠ 0 := by
    intro a
    have : 0 < Nat.card (hyp.H a) := Nat.card_pos
    exact_mod_cast this.ne'
  -- the averaging value, unfolded
  have hψa : ∀ a : {a : G // a ∈ A},
      ψ ⟨a.1, hyp.subset_L a.2⟩
        = (Nat.card (hyp.H a) : ℂ)⁻¹ * ∑ x : hyp.H a, χ (a.1 * (x : G)) := by
    intro a
    rw [hψ a]
    simp only [adjointAverageFun]
    rw [dif_pos a.2]
  -- support reindexing of the L-inner sum
  have hISL : ClassFunction.innerSum (α : ClassFunction L ℂ) ψ
      = ∑ a : {a : G // a ∈ A}, aα a * star (ψ ⟨a.1, hyp.subset_L a.2⟩) := by
    rw [ClassFunction.innerSum]
    rw [← Finset.sum_subset
      (Finset.filter_subset (fun ℓ : L => (ℓ : G) ∈ A) Finset.univ)
      (fun ℓ _ hℓ => by
        have hα0 : (α : ClassFunction L ℂ) ℓ = 0 := by
          by_contra hne
          exact hℓ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, α.2 hne⟩)
        rw [hα0, zero_mul])]
    refine (Finset.sum_bij (fun a _ => (⟨a.1, hyp.subset_L a.2⟩ : L)) ?_ ?_ ?_ ?_).symm
    · intro a _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.2⟩
    · intro a _ b _ hab; exact Subtype.ext (by simpa using congrArg Subtype.val hab)
    · intro ℓ hℓ
      exact ⟨⟨ℓ.1, (Finset.mem_filter.mp hℓ).2⟩, Finset.mem_univ _, Subtype.ext rfl⟩
    · intro a _; rfl
  -- WAY 1: M = |G| · ⟨α, ψ⟩_L
  have way1 : M = (Nat.card G : ℂ) * ClassFunction.innerSum (α : ClassFunction L ℂ) ψ := by
    rw [hISL, Finset.mul_sum, hM]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hstar_psi : star (ψ ⟨a.1, hyp.subset_L a.2⟩)
        = (Nat.card (hyp.H a) : ℂ)⁻¹ * ∑ x : hyp.H a, star (χ (a.1 * (x : G))) := by
      rw [hψa a, star_mul', star_sum, star_inv₀, star_natCast]
    calc ∑ x : hyp.H a, ∑ t : G, (Nat.card (hyp.H a) : ℂ)⁻¹ * aα a *
            star (χ ((t : G) * (a.1 * (x : G)) * (t : G)⁻¹))
        = ∑ x : hyp.H a, (Nat.card G : ℂ) *
            ((Nat.card (hyp.H a) : ℂ)⁻¹ * aα a * star (χ (a.1 * (x : G)))) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          simp only [ClassFunction.conj_eq]
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
      _ = (Nat.card G : ℂ) * (aα a * star (ψ ⟨a.1, hyp.subset_L a.2⟩)) := by
          rw [hstar_psi, ← Finset.mul_sum]
          congr 1
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          ring
  -- substitution aα a = (τ α)(t (a x) t⁻¹)
  have hsub : ∀ (a : {a : G // a ∈ A}) (x : hyp.H a) (t : G),
      aα a = (τ α) ((t : G) * (a.1 * (x : G)) * (t : G)⁻¹) := by
    intro a x t
    rw [haα]
    exact (hτ.map_eq_of_isConj_hCoset α _ a (x : G) x.2
      (isConj_iff.mpr ⟨(t : G), rfl⟩)).symm
  -- WAY 2: M = |L| · ⟨τ α, χ⟩_G
  have way2 : M = (Nat.card L : ℂ) * ClassFunction.innerSum (τ α) χ := by
    have step : M = ∑ a : {a : G // a ∈ A},
        ∑ b ∈ Finset.univ.filter (fun b : G => ∃ x ∈ hyp.H a, IsConj (a.1 * x) b),
          (Nat.card (centralizerIn L a.1) : ℂ) * F b := by
      rw [hM]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      have e1 : (∑ x : hyp.H a, ∑ t : G, (Nat.card (hyp.H a) : ℂ)⁻¹ * aα a *
              star (χ ((t : G) * (a.1 * (x : G)) * (t : G)⁻¹)))
          = (Nat.card (hyp.H a) : ℂ)⁻¹ *
              ∑ x : hyp.H a, ∑ t : G, F ((t : G) * (a.1 * (x : G)) * (t : G)⁻¹) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [hsub a x t, hF]
        ring
      rw [e1, hyp.fiber_regroup a F, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [← mul_assoc]
      congr 1
      rw [hyp.card_centralizer_eq a, Nat.cast_mul, ← mul_assoc,
        inv_mul_cancel₀ (hHne a), one_mul]
    rw [step]
    -- turn inner filtered sum into an if-sum, then swap
    have step2 : (∑ a : {a : G // a ∈ A},
          ∑ b ∈ Finset.univ.filter (fun b : G => ∃ x ∈ hyp.H a, IsConj (a.1 * x) b),
            (Nat.card (centralizerIn L a.1) : ℂ) * F b)
        = ∑ b : G, ∑ a : {a : G // a ∈ A},
            (if (∃ x ∈ hyp.H a, IsConj (a.1 * x) b)
              then (Nat.card (centralizerIn L a.1) : ℂ) * F b else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_filter]
    rw [step2, show (Nat.card L : ℂ) * ClassFunction.innerSum (τ α) χ
          = ∑ b : G, (Nat.card L : ℂ) * F b from by
        rw [ClassFunction.innerSum, Finset.mul_sum]]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    -- ∑_a (if Q then |C_L a| * F b else 0) = |L| * F b
    have factor : (∑ a : {a : G // a ∈ A},
          (if (∃ x ∈ hyp.H a, IsConj (a.1 * x) b)
            then (Nat.card (centralizerIn L a.1) : ℂ) * F b else 0))
        = (∑ a : {a : G // a ∈ A},
            (if (∃ x ∈ hyp.H a, IsConj (a.1 * x) b)
              then (Nat.card (centralizerIn L a.1) : ℂ) else 0)) * F b := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      split <;> simp
    rw [factor]
    by_cases hb : b ∈ hyp.dadeSupport
    · have hN : (∑ a : {a : G // a ∈ A},
            (if (∃ x ∈ hyp.H a, IsConj (a.1 * x) b)
              then (Nat.card (centralizerIn L a.1) : ℂ) else 0)) = (Nat.card L : ℂ) := by
        rw [← Finset.sum_filter, ← Nat.cast_sum, hyp.sum_card_centralizerIn_eq hconj hb]
      rw [hN, mul_comm]
    · have hF0 : F b = 0 := by
        rw [hF]
        simp only
        rw [hτ.map_eq_zero_of_not_mem_dadeSupport α b hb, zero_mul]
      rw [hF0, mul_zero, mul_zero]
  -- combine and divide by |G|, |L|
  have hcombine : (Nat.card L : ℂ) * ClassFunction.innerSum (τ α) χ
      = (Nat.card G : ℂ) * ClassFunction.innerSum (α : ClassFunction L ℂ) ψ :=
    way2.symm.trans way1
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum,
    ClassFunction.inner_eq_inv_card_mul_innerSum]
  calc ⅟(Nat.card G : ℂ) * ClassFunction.innerSum (τ α) χ
      = ⅟(Nat.card G : ℂ) * ⅟(Nat.card L : ℂ) *
          ((Nat.card L : ℂ) * ClassFunction.innerSum (τ α) χ) := by
        rw [mul_assoc, ← mul_assoc (⅟(Nat.card L : ℂ)), invOf_mul_self, one_mul]
    _ = ⅟(Nat.card G : ℂ) * ⅟(Nat.card L : ℂ) *
          ((Nat.card G : ℂ) * ClassFunction.innerSum (α : ClassFunction L ℂ) ψ) := by
        rw [hcombine]
    _ = ⅟(Nat.card L : ℂ) * ClassFunction.innerSum (α : ClassFunction L ℂ) ψ := by
        rw [mul_comm (⅟(Nat.card G : ℂ)) (⅟(Nat.card L : ℂ)), mul_assoc,
          ← mul_assoc (⅟(Nat.card G : ℂ)), invOf_mul_self, one_mul]

omit [Fintype L] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card L : ℂ)] in
/-- For a Dade map `τ` and `β : CF(L, A)`, the (2.7) averaging map applied to the
class function `τ β` recovers `β` on `A`.

Indeed `τ β` is constant equal to `β(a)` on the coset `aH(a)` (this is the (2.5)
defining equation `IsDadeMap.map_eq_of_mem_hCoset`), so averaging it over `H(a)`
gives back `β(a)`.  This is the computation behind Peterfalvi's remark, at the
start of the proof of (2.6.a), that "`β^τ` is constant on `aH(a)`". -/
theorem adjointAverageFun_dadeMap_eq
    (τ : DadeMap (G := G) (k := ℂ) A L) (hτ : IsDadeMap hyp τ)
    (β : SupportedClassFunctions (G := G) ℂ A L) (a : {a : G // a ∈ A}) :
    adjointAverageFun hyp (τ β) ⟨a.1, hyp.subset_L a.2⟩ =
      (β : ClassFunction L ℂ) ⟨a.1, hyp.subset_L a.2⟩ := by
  classical
  -- unfold the averaging map at `a`
  simp only [adjointAverageFun]
  rw [dif_pos a.2]
  -- `τ β` is constant `= β(a)` on the coset `a · H(a)`
  have hconst : ∀ x : ↥(hyp.H ⟨a.1, a.2⟩),
      (τ β) (a.1 * (x : G)) = (β : ClassFunction L ℂ) ⟨a.1, hyp.subset_L a.2⟩ := by
    intro x
    have hx : a.1 * (x : G) ∈ hyp.hCoset a := ⟨(x : G), x.2, rfl⟩
    simpa using hτ.map_eq_of_mem_hCoset β a hx
  have hHne : (Nat.card (hyp.H ⟨a.1, a.2⟩) : ℂ) ≠ 0 := by
    have : 0 < Nat.card (hyp.H ⟨a.1, a.2⟩) := Nat.card_pos
    exact_mod_cast this.ne'
  rw [Finset.sum_congr rfl (fun x _ => hconst x), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hHne, one_mul]

/-- **Peterfalvi (2.6.a).**  Any map `τ` satisfying the (2.5) Dade-map equations
(`IsDadeMap`) and the (2.4.a) `L`-equivariance of the subgroups `H(a)`
(`HConjInvariant`) automatically preserves Peterfalvi's normalized inner product:

    `(α^τ, β^τ)_G = (α, β)_L`    for all `α, β ∈ CF(L, A)`.

This is the textbook proof of (2.6.a): since `β^τ` is constant on each coset
`aH(a)`, the (2.7) adjoint formula with `χ = β^τ` and `ψ = β` reduces the
`G`-inner product to the `L`-inner product `(α, β)_L`.  Together with
`IsDadeMap` this upgrades a Dade map to a full `DadeIsometryData` without
assuming the isometry property separately. -/
theorem isDadeIsometry_of_isDadeMap
    (τ : DadeMap (G := G) (k := ℂ) A L) (hτ : IsDadeMap hyp τ)
    (hconj : hyp.HConjInvariant) :
    IsDadeIsometry (k := ℂ) τ where
  inner_eq α β :=
    adjoint_formula hyp τ hτ hconj α (τ β) (β : ClassFunction L ℂ)
      (fun a => (adjointAverageFun_dadeMap_eq hyp τ hτ β a).symm)

/-- Bundle a Dade map satisfying the (2.5) equations into a `DadeIsometryData`,
using `isDadeIsometry_of_isDadeMap` to supply the (2.6.a) isometry property. -/
noncomputable def DadeIsometryData.ofIsDadeMap
    (τ : DadeMap (G := G) (k := ℂ) A L) (hτ : IsDadeMap hyp τ)
    (hconj : hyp.HConjInvariant) :
    DadeIsometryData (G := G) (k := ℂ) hyp where
  toDadeMap := τ
  isDadeMap := hτ
  isDadeIsometry := isDadeIsometry_of_isDadeMap hyp τ hτ hconj

@[simp] theorem DadeIsometryData.ofIsDadeMap_toDadeMap
    (τ : DadeMap (G := G) (k := ℂ) A L) (hτ : IsDadeMap hyp τ)
    (hconj : hyp.HConjInvariant) :
    (DadeIsometryData.ofIsDadeMap hyp τ hτ hconj).toDadeMap = τ :=
  rfl

end AdjointFormula

end DadeMap

end OddOrder.Peterfalvi.S04
