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

/-- The identity lies outside the Dade support `⋃_{a∈A} (a·H(a))^G`.

If `1 ∈ dadeSupport`, then `IsConj (a·h) 1` for some `a ∈ A`, `h ∈ H(a)`, hence `a·h = 1`
(`isConj_one_left`) and `a = h⁻¹ ∈ H(a)`.  But `a` also lies in `C_L(a)` (it is in `L` and
commutes with itself), and `H(a)` is disjoint from `C_L(a)` (`centralizer_disjoint` of
Hypothesis (2.2)), so `a ∈ H(a) ⊓ C_L(a) = ⊥`, i.e. `a = 1` — contradicting `a ≠ 1`
(`ne_one`, from `A ⊆ G^#`).  This is the support-side fact behind vanishing-at-`1` of the Dade
map: any Dade image vanishes off `dadeSupport` (`IsDadeMap.map_eq_zero_of_not_mem_dadeSupport`),
hence at `1`. -/
theorem one_notMem_dadeSupport (hyp : Hypothesis G A L) :
    (1 : G) ∉ hyp.dadeSupport := by
  intro hone
  obtain ⟨a, h, hh, hconj⟩ := hyp.mem_dadeSupport_iff.mp hone
  have hah : a.1 * h = 1 := isConj_one_left.mp hconj
  -- `a = h⁻¹ ∈ H(a)`.
  have ha_eq : a.1 = h⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]; exact hah
  have ha_H : a.1 ∈ hyp.H a := by
    rw [ha_eq]; exact (hyp.H a).inv_mem hh
  -- `a ∈ C_L(a)`.
  have ha_cent : a.1 ∈ centralizerIn L a.1 :=
    mem_centralizerIn.mpr ⟨hyp.mem_L a.2, rfl⟩
  -- Disjointness forces `a = 1`.
  have ha_one : a.1 = 1 := by
    have := (Subgroup.disjoint_def.mp (hyp.centralizer_disjoint a)) ha_H ha_cent
    simpa using this
  exact hyp.ne_one a.2 ha_one

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

/-- **The `O_{π'}`-containment behind `(2.4)`/`(2.10.2)`.**  Any `x ∈ C_G(a)` whose
order is prime to `|C_L(a)|` already lies in `H(a)`.

Since `H(a) ⊴ C_G(a)` (`H_normalized`) with relative index `[C_G(a) : H(a)] =
|C_L(a)|` (`card_centralizer_eq`), the element `x ^ |C_L(a)|` lies in `H(a)`
(`pow_index_mem`); and `x` is itself a power of `x ^ |C_L(a)|` because `|C_L(a)|`
is prime to `orderOf x` (Chinese remainder).  Equivalently, the image of `x` in
`C_G(a)/H(a) ≅ C_L(a)` has order prime to `|C_L(a)|`, hence is trivial. -/
theorem mem_H_of_mem_centralizer_coprime (hyp : Hypothesis G A L)
    (a : {a : G // a ∈ A}) {x : G}
    (hx : x ∈ Subgroup.centralizer ({a.1} : Set G))
    (hcop : Nat.Coprime (orderOf x) (Nat.card (centralizerIn L a.1))) :
    x ∈ hyp.H a := by
  classical
  set C := Subgroup.centralizer ({a.1} : Set G) with hCdef
  set m := Nat.card (centralizerIn L a.1) with hmdef
  have hHaC : hyp.H a ≤ C := by rw [hCdef, hyp.centralizer_eq_sup a]; exact le_sup_left
  -- `C_G(a)` normalizes `H(a)` (both directions of `H_normalized`).
  have hCnorm : C ≤ Subgroup.normalizer (hyp.H a) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hyp.H_normalized a c hc h hh, fun hh => ?_⟩
    have hmem := hyp.H_normalized a c⁻¹ (Subgroup.inv_mem _ hc) _ hh
    have heq : c⁻¹ * (c * h * c⁻¹) * (c⁻¹)⁻¹ = h := by group
    rwa [heq] at hmem
  haveI hnormal : ((hyp.H a).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHaC).mpr hCnorm
  -- `[C_G(a) : H(a)] = |C_L(a)|`.
  have hindex : ((hyp.H a).subgroupOf C).index = m := by
    have hcard_sub : Nat.card ((hyp.H a).subgroupOf C) = Nat.card (hyp.H a) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHaC).toEquiv
    have hmul := Subgroup.index_mul_card ((hyp.H a).subgroupOf C)
    rw [hcard_sub] at hmul
    have hCcard : Nat.card C = Nat.card (hyp.H a) * m := by
      rw [hCdef, hmdef]; exact hyp.card_centralizer_eq a
    rw [hCcard] at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hmul]; ring)
  -- `x ^ |C_L(a)| ∈ H(a)`.
  have hxm : x ^ m ∈ hyp.H a := by
    have hpow := Subgroup.pow_index_mem ((hyp.H a).subgroupOf C) (⟨x, hx⟩ : C)
    rw [hindex, Subgroup.mem_subgroupOf] at hpow
    simpa using hpow
  -- `x` is a power of `x ^ |C_L(a)|`.
  obtain ⟨k, hk1, hk0⟩ := Nat.chineseRemainder hcop 1 0
  have hxk : x ^ k = x := by
    have : x ^ k = x ^ 1 := pow_eq_pow_iff_modEq.mpr hk1
    simpa using this
  obtain ⟨j, rfl⟩ := (Nat.modEq_zero_iff_dvd).mp hk0
  have hxeq : x = (x ^ m) ^ j := by rw [← pow_mul, hxk]
  rw [hxeq]
  exact (hyp.H a).pow_mem hxm j

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

open scoped Classical in
/-- **Peterfalvi (2.10.2).**  For a nonempty `B ⊆ A` and `a ∈ A`, the centralizer of
`a` inside `H(B)` is `H(B ∪ {a})`:  `C_G(a) ⊓ H(B) = H(insert a B)`.

`⊇`: `H(insert a B) ⊆ H(a) ⊆ C_G(a)` and `⊆ H(B)`.  `⊆`: any
`x ∈ C_G(a) ⊓ H(B)` has order dividing some `|H(b₀)|` (`b₀ ∈ B`), which is prime to
`|C_L(a)|` by `(2.2.c)`, so `x ∈ H(a)` by `mem_H_of_mem_centralizer_coprime`. -/
theorem centralizer_inf_hIntersection (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) (a : {a : G // a ∈ A}) :
    Subgroup.centralizer ({a.1} : Set G) ⊓ hIntersection hyp B hB
      = hIntersection hyp (insert a B) (Finset.insert_nonempty a B) := by
  classical
  ext x
  simp only [Subgroup.mem_inf, mem_hIntersection]
  constructor
  · rintro ⟨hxC, hxB⟩ b hb
    rw [Finset.mem_insert] at hb
    rcases hb with hb | hb
    · rw [hb]
      obtain ⟨b₀, hb₀⟩ := hB
      have hcop : Nat.Coprime (orderOf x) (Nat.card (centralizerIn L a.1)) :=
        Nat.Coprime.coprime_dvd_left ((hyp.H b₀).orderOf_dvd_natCard (hxB b₀ hb₀))
          (hyp.centralizer_coprime b₀ a)
      exact hyp.mem_H_of_mem_centralizer_coprime a hxC hcop
    · exact hxB b hb
  · intro hx
    refine ⟨?_, fun b hb => hx b (Finset.mem_insert_of_mem hb)⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hyp.commute_of_mem_H a (hx a (Finset.mem_insert_self a B))).symm

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

/-- `IsComplement'.QuotientMulEquiv` is a retraction onto the complement: on the class of a
complement element `x : H`, it returns `x` (`QuotientMulEquiv.symm x = mk' ↑x`). -/
theorem _root_.Subgroup.IsComplement'.QuotientMulEquiv_mk'_coe {G' : Type*} [Group G']
    {H K : Subgroup G'} [K.Normal] (h : H.IsComplement' K) (x : H) :
    h.QuotientMulEquiv (QuotientGroup.mk' K (x : G')) = x := by
  rw [show (QuotientGroup.mk' K (x : G')) = h.QuotientMulEquiv.symm x from rfl,
    MulEquiv.apply_symm_apply]

/-- **`f_B` retracts `N_L(B)`.**  For `m ∈ M(B)` whose underlying element lies in `N_L(B)`,
`f_B(m) = m` (in `L`).  Together with `ker f_B = H(B)` this pins down `f_B` on the
semidirect factors. -/
theorem dadeQuotientHom_coe_of_mem_nLStabilizerIn (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (m : mBSubgroup hyp B hB) (hm : (m : G) ∈ nLStabilizerIn hyp B) :
    ((hyp.dadeQuotientHom hconj hB m : L) : G) = (m : G) := by
  haveI : ((hIntersection hyp B hB).subgroupOf (mBSubgroup hyp B hB)).Normal :=
    hyp.hIntersection_subgroupOf_normal hconj hB
  set κ : (nLStabilizerIn hyp B).subgroupOf (mBSubgroup hyp B hB) :=
    ⟨m, (Subgroup.mem_subgroupOf).mpr hm⟩ with hκ
  have hmk : (hyp.isComplement'_subgroupOf hconj hB).QuotientMulEquiv
      (QuotientGroup.mk' _ m) = κ := by
    rw [show (m : mBSubgroup hyp B hB) = ((κ : (nLStabilizerIn hyp B).subgroupOf _) :
        mBSubgroup hyp B hB) from rfl]
    exact (hyp.isComplement'_subgroupOf hconj hB).QuotientMulEquiv_mk'_coe κ
  simp only [dadeQuotientHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hmk,
    Subgroup.coe_inclusion]
  rfl

/-- **Peterfalvi (2.9), defining equation.**  For `h ∈ H(B)`, `b ∈ N_L(B)`, the class
function `α_B = α ∘ f_B` satisfies `α_B(h·b) = α(b)`.  Indeed `f_B(h·b) = f_B(h)·f_B(b) =
1·b = b`, since `H(B) = ker f_B` and `f_B` retracts `N_L(B)`. -/
theorem alphaB_apply_mul (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) (α : ClassFunction L ℂ)
    {h b : G} (hh : h ∈ hIntersection hyp B hB) (hb : b ∈ nLStabilizerIn hyp B)
    (hmem : h * b ∈ mBSubgroup hyp B hB) :
    alphaB hyp hconj hB α ⟨h * b, hmem⟩
      = α ⟨b, nLStabilizerIn_le_L hyp B hb⟩ := by
  have hhM : h ∈ mBSubgroup hyp B hB := hyp.hIntersection_le_mBSubgroup hB hh
  have hbM : b ∈ mBSubgroup hyp B hB := hyp.nLStabilizerIn_le_mBSubgroup hB hb
  have hsplit : (⟨h * b, hmem⟩ : mBSubgroup hyp B hB)
      = (⟨h, hhM⟩ : mBSubgroup hyp B hB) * ⟨b, hbM⟩ := rfl
  have hfh : hyp.dadeQuotientHom hconj hB ⟨h, hhM⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hyp.ker_dadeQuotientHom hconj hB, Subgroup.mem_subgroupOf]
    exact hh
  have hval : hyp.dadeQuotientHom hconj hB ⟨b, hbM⟩
      = ⟨b, nLStabilizerIn_le_L hyp B hb⟩ := by
    apply Subtype.ext
    exact hyp.dadeQuotientHom_coe_of_mem_nLStabilizerIn hconj hB ⟨b, hbM⟩ hb
  show α (hyp.dadeQuotientHom hconj hB ⟨h * b, hmem⟩) = _
  rw [hsplit, map_mul, hfh, one_mul, hval]

/- 2.10.1: `L`-conjugacy invariance of `Ind_{M(B)}^G α_B` (Dade-specific form). -/

section ConjugacyInvariance

open scoped Classical in
/-- The conjugate finset `B^l = { l·a·l⁻¹ | a ∈ B }`, as the `conjA l`-image of `B`. -/
noncomputable def conjFinset (hyp : Hypothesis G A L) (l : L)
    (B : Finset {a : G // a ∈ A}) : Finset {a : G // a ∈ A} :=
  B.image (hyp.conjA l)

@[simp] theorem mem_conjFinset (hyp : Hypothesis G A L) {l : L}
    {B : Finset {a : G // a ∈ A}} {a : {a : G // a ∈ A}} :
    a ∈ hyp.conjFinset l B ↔ ∃ b ∈ B, hyp.conjA l b = a := by
  classical
  simp [conjFinset]

theorem conjFinset_nonempty (hyp : Hypothesis G A L) {l : L}
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    (hyp.conjFinset l B).Nonempty := by
  classical
  rw [conjFinset]
  exact hB.image _

@[simp] theorem conjFinset_one (hyp : Hypothesis G A L) (B : Finset {a : G // a ∈ A}) :
    hyp.conjFinset 1 B = B := by
  classical
  rw [conjFinset]
  rw [show (hyp.conjA 1) = id from funext fun a => hyp.conjA_one a]
  exact Finset.image_id

theorem conjFinset_mul (hyp : Hypothesis G A L) (l₁ l₂ : L)
    (B : Finset {a : G // a ∈ A}) :
    hyp.conjFinset (l₁ * l₂) B = hyp.conjFinset l₁ (hyp.conjFinset l₂ B) := by
  classical
  rw [conjFinset, conjFinset, conjFinset, Finset.image_image]
  exact Finset.image_congr (fun a _ => hyp.conjA_mul l₁ l₂ a)

theorem conjFinset_card (hyp : Hypothesis G A L) (l : L) (B : Finset {a : G // a ∈ A}) :
    (hyp.conjFinset l B).card = B.card := by
  classical
  rw [conjFinset, Finset.card_image_of_injective]
  intro a b hab
  have := congrArg (hyp.conjA l⁻¹) hab
  rwa [conjA_inv_conjA, conjA_inv_conjA] at this

/-- **Peterfalvi (2.10.1), `H(B^x) = H(B)^x`.**  Conjugation by `l ∈ L` carries `H(B)` to
`H(B^l)`: `H(B^l) = l · H(B) · l⁻¹`.  Uses `(2.4.a)` (`mem_H_conjA_iff`): an element lies in
`H(l·a·l⁻¹)` iff its `l`-untwist lies in `H(a)`. -/
theorem hIntersection_conjFinset (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (l : L) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    hIntersection hyp (hyp.conjFinset l B) (hyp.conjFinset_nonempty hB)
      = MulAut.conj (l : G) • hIntersection hyp B hB := by
  classical
  ext x
  rw [mem_hIntersection, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_hIntersection]
  constructor
  · intro hx a ha
    have hmem : x ∈ hyp.H (hyp.conjA l a) := hx _ ((hyp.mem_conjFinset).mpr ⟨a, ha, rfl⟩)
    rw [mem_H_conjA_iff hyp hconj] at hmem
    rwa [show ((MulAut.conj (l : G))⁻¹ • x) = (l : G)⁻¹ * x * (l : G) from by
      rw [show ((MulAut.conj (l : G))⁻¹ • x) = (MulAut.conj (l : G))⁻¹ x from rfl,
        MulAut.conj_inv_apply]]
  · intro hx a ha
    obtain ⟨b, hb, rfl⟩ := (hyp.mem_conjFinset).mp ha
    rw [mem_H_conjA_iff hyp hconj]
    have := hx b hb
    rwa [show ((MulAut.conj (l : G))⁻¹ • x) = (l : G)⁻¹ * x * (l : G) from by
      rw [show ((MulAut.conj (l : G))⁻¹ • x) = (MulAut.conj (l : G))⁻¹ x from rfl,
        MulAut.conj_inv_apply]] at this

/-- `conjA` conjugation relation: `(conjA l)⁻¹ ∘ conjA ℓ ∘ conjA l = conjA (l⁻¹ ℓ l)`. -/
theorem conjA_conj (hyp : Hypothesis G A L) (l ℓ : L) (a : {a : G // a ∈ A}) :
    hyp.conjA l⁻¹ (hyp.conjA ℓ (hyp.conjA l a)) = hyp.conjA (l⁻¹ * ℓ * l) a := by
  rw [← conjA_mul, ← conjA_mul]

/-- **Peterfalvi (2.10.1), `N_L(B^x)` membership.**  An element `ℓ ∈ L` stabilizes the
conjugate finset `B^l` iff its `l`-untwist `l⁻¹ ℓ l` stabilizes `B`. -/
theorem mem_setLStabilizer_conjFinset (hyp : Hypothesis G A L) (l ℓ : L)
    {B : Finset {a : G // a ∈ A}} :
    ℓ ∈ setLStabilizer hyp (hyp.conjFinset l B)
      ↔ l⁻¹ * ℓ * l ∈ setLStabilizer hyp B := by
  classical
  simp only [mem_setLStabilizer, mem_conjFinset]
  constructor
  · intro h b hb
    obtain ⟨c, hc, hceq⟩ := h (hyp.conjA l b) ⟨b, hb, rfl⟩
    have : hyp.conjA (l⁻¹ * ℓ * l) b = c := by
      rw [← conjA_conj, ← hceq, conjA_inv_conjA]
    rw [this]; exact hc
  · rintro h a ⟨b, hb, rfl⟩
    refine ⟨hyp.conjA (l⁻¹ * ℓ * l) b, h b hb, ?_⟩
    rw [← conjA_conj, conjA_conjA_inv]

/-- **Peterfalvi (2.10.1), `N_L(B^x) = N_L(B)^x`.**  Conjugation by `l ∈ L` carries `N_L(B)`
to `N_L(B^l)`: `N_L(B^l) = l · N_L(B) · l⁻¹`. -/
theorem nLStabilizerIn_conjFinset (hyp : Hypothesis G A L) (l : L)
    {B : Finset {a : G // a ∈ A}} :
    nLStabilizerIn hyp (hyp.conjFinset l B)
      = MulAut.conj (l : G) • nLStabilizerIn hyp B := by
  classical
  ext x
  rw [mem_nLStabilizerIn, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_nLStabilizerIn]
  have hsmul : ((MulAut.conj (l : G))⁻¹ • x) = (l : G)⁻¹ * x * (l : G) := by
    rw [show ((MulAut.conj (l : G))⁻¹ • x) = (MulAut.conj (l : G))⁻¹ x from rfl,
      MulAut.conj_inv_apply]
  rw [hsmul]
  constructor
  · rintro ⟨hxL, hxN⟩
    have hconjL : (l : G)⁻¹ * x * (l : G) ∈ L :=
      L.mul_mem (L.mul_mem (L.inv_mem l.2) hxL) l.2
    refine ⟨hconjL, ?_⟩
    have : (⟨(l : G)⁻¹ * x * (l : G), hconjL⟩ : L) = l⁻¹ * ⟨x, hxL⟩ * l := by
      apply Subtype.ext; push_cast; ring
    rw [this]
    exact (hyp.mem_setLStabilizer_conjFinset l ⟨x, hxL⟩).mp hxN
  · rintro ⟨hconjL, hxN⟩
    have hxL : x ∈ L := by
      have : x = (l : G) * ((l : G)⁻¹ * x * (l : G)) * (l : G)⁻¹ := by group
      rw [this]; exact L.mul_mem (L.mul_mem l.2 hconjL) (L.inv_mem l.2)
    refine ⟨hxL, ?_⟩
    rw [hyp.mem_setLStabilizer_conjFinset l ⟨x, hxL⟩]
    have : (l⁻¹ * ⟨x, hxL⟩ * l : L) = ⟨(l : G)⁻¹ * x * (l : G), hconjL⟩ := by
      apply Subtype.ext; push_cast; ring
    rw [this]; exact hxN

/-- **Peterfalvi (2.10.1), `M(B^x) = M(B)^x`.**  Conjugation by `l ∈ L` carries `M(B)` to
`M(B^l)`: `M(B^l) = l · M(B) · l⁻¹`.  Since `M(B) = H(B) ⊔ N_L(B)` and conjugation is a
lattice homomorphism (`smul_sup`), this follows from the conjugation of the two factors. -/
theorem mBSubgroup_conjFinset (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (l : L) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    mBSubgroup hyp (hyp.conjFinset l B) (hyp.conjFinset_nonempty hB)
      = MulAut.conj (l : G) • mBSubgroup hyp B hB := by
  rw [mBSubgroup, mBSubgroup, hyp.hIntersection_conjFinset hconj l hB,
    hyp.nLStabilizerIn_conjFinset l, Subgroup.smul_sup]

/-- `M(B) = H(B)^x ⊔ N_L(B)^x`-conjugation packaged as `Subgroup.map`: `M(B^l) = M(B).map (conj l)`.
This is the form consumed by the generic `induce_map_conj` (which produces a `.map (conj ℓ)`
subgroup). -/
theorem mBSubgroup_conjFinset_eq_map (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (l : L) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    mBSubgroup hyp (hyp.conjFinset l B) (hyp.conjFinset_nonempty hB)
      = (mBSubgroup hyp B hB).map (MulAut.conj (l : G) : G →* G) := by
  rw [hyp.mBSubgroup_conjFinset hconj l hB, Subgroup.pointwise_smul_def]; rfl

/-- A congruence principle for `induce` along a subgroup equality: if `H₁ = H₂` and the two class
functions take equal values on the common carrier, the induced class functions agree. -/
theorem induce_congr_of_subgroup_eq {H₁ H₂ : Subgroup G} (h : H₁ = H₂)
    [Invertible (Nat.card H₁ : ℂ)] [Invertible (Nat.card H₂ : ℂ)]
    {θ₁ : ClassFunction ↥H₁ ℂ} {θ₂ : ClassFunction ↥H₂ ℂ}
    (hval : ∀ x (hx₁ : x ∈ H₁) (hx₂ : x ∈ H₂), θ₁ ⟨x, hx₁⟩ = θ₂ ⟨x, hx₂⟩) :
    ClassFunction.induce H₁ θ₁ = ClassFunction.induce H₂ θ₂ := by
  subst h
  have hθ : θ₁ = θ₂ := by ext x; exact hval x.1 x.2 x.2
  rw [hθ]; congr 1; exact Subsingleton.elim _ _

/-- **Peterfalvi (2.10.1), transported `α_B`.**  On the conjugate subgroup `M(B^l)`, the class
function `α_{B^l}` agrees with the transport `transportConj l α_B` of `α_B` to `M(B)^l`.

Both values are computed via the (2.9) defining equation `alphaB_apply_mul`: writing `y = l m l⁻¹`
with `m = h·b ∈ M(B)` (`h ∈ H(B)`, `b ∈ N_L(B)`), the left side is `α((lbl⁻¹))` (since
`y = (lhl⁻¹)(lbl⁻¹)` with `lhl⁻¹ ∈ H(B^l)`, `lbl⁻¹ ∈ N_L(B^l)`) and the right side is `α(b)`;
they agree because `α` is an `L`-class function and `l, b ∈ L`. -/
theorem alphaB_conjFinset_eq_transportConj (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (l : L) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) (α : ClassFunction L ℂ)
    (y : G) (hy₁ : y ∈ mBSubgroup hyp (hyp.conjFinset l B) (hyp.conjFinset_nonempty hB))
    (hy₂ : y ∈ (mBSubgroup hyp B hB).map (MulAut.conj (l : G) : G →* G)) :
    alphaB hyp hconj (hyp.conjFinset_nonempty hB) α ⟨y, hy₁⟩
      = ClassFunction.transportConj (l : G) (alphaB hyp hconj hB α) ⟨y, hy₂⟩ := by
  classical
  -- `m := l⁻¹ y l ∈ M(B)`, so `y = l m l⁻¹`; decompose `m = h * b`, `h ∈ H(B)`, `b ∈ N_L(B)`.
  have hmM : (l : G)⁻¹ * y * (l : G) ∈ mBSubgroup hyp B hB := by
    have := (Subgroup.mem_map_equiv).mp hy₂
    rwa [MulAut.conj_symm_apply] at this
  have hmem_prod : (l : G)⁻¹ * y * (l : G)
      ∈ (↑(hIntersection hyp B hB) * ↑(nLStabilizerIn hyp B) : Set G) := by
    rw [← hyp.coe_mBSubgroup hconj hB]; exact hmM
  obtain ⟨h, hh, b, hb, hhb⟩ := hmem_prod
  -- `hhb : h * b = l⁻¹ * y * l`; hence `y = (l h l⁻¹)(l b l⁻¹)`.
  have hyhb : y = ((l : G) * h * (l : G)⁻¹) * ((l : G) * b * (l : G)⁻¹) := by
    have hconj_y : (l : G) * ((l : G)⁻¹ * y * (l : G)) * (l : G)⁻¹ = y := by group
    rw [← hconj_y, ← hhb]; group
  have hbL : b ∈ L := nLStabilizerIn_le_L hyp B hb
  have hhM : h ∈ mBSubgroup hyp B hB := hyp.hIntersection_le_mBSubgroup hB hh
  have hbM : b ∈ mBSubgroup hyp B hB := hyp.nLStabilizerIn_le_mBSubgroup hB hb
  have hhbM : h * b ∈ mBSubgroup hyp B hB := (mBSubgroup hyp B hB).mul_mem hhM hbM
  -- Right side: `transportConj l α_B ⟨y,_⟩ = α_B ⟨l⁻¹ y l,_⟩ = α(b)`.
  have hRHS : ClassFunction.transportConj (l : G) (alphaB hyp hconj hB α) ⟨y, hy₂⟩
      = α ⟨b, hbL⟩ := by
    rw [ClassFunction.transportConj_apply]
    have harg : ((MulEquiv.subgroupMap (MulAut.conj (l : G)) (mBSubgroup hyp B hB)).symm
        ⟨y, hy₂⟩ : mBSubgroup hyp B hB) = ⟨h * b, hhbM⟩ := by
      apply Subtype.ext
      simp only [MulEquiv.subgroupMap_symm_apply, MulAut.conj_symm_apply]
      exact hhb.symm
    rw [harg]
    exact hyp.alphaB_apply_mul hconj hB α hh hb hhbM
  -- Left side: `lhl⁻¹ ∈ H(B^l)`, `lbl⁻¹ ∈ N_L(B^l)`, so `α_{B^l} ⟨y,_⟩ = α(lbl⁻¹)`.
  have hh'mem : (l : G) * h * (l : G)⁻¹
      ∈ hIntersection hyp (hyp.conjFinset l B) (hyp.conjFinset_nonempty hB) := by
    rw [hyp.hIntersection_conjFinset hconj l hB,
      show (l : G) * h * (l : G)⁻¹ = (MulAut.conj (l : G)) h from (MulAut.conj_apply _ _).symm]
    exact Subgroup.smul_mem_pointwise_smul h (MulAut.conj (l : G)) (hIntersection hyp B hB) hh
  have hb'mem : (l : G) * b * (l : G)⁻¹ ∈ nLStabilizerIn hyp (hyp.conjFinset l B) := by
    rw [hyp.nLStabilizerIn_conjFinset l,
      show (l : G) * b * (l : G)⁻¹ = (MulAut.conj (l : G)) b from (MulAut.conj_apply _ _).symm]
    exact Subgroup.smul_mem_pointwise_smul b (MulAut.conj (l : G)) (nLStabilizerIn hyp B) hb
  have hb'L : (l : G) * b * (l : G)⁻¹ ∈ L := nLStabilizerIn_le_L hyp (hyp.conjFinset l B) hb'mem
  have hLHS : alphaB hyp hconj (hyp.conjFinset_nonempty hB) α ⟨y, hy₁⟩
      = α ⟨(l : G) * b * (l : G)⁻¹, hb'L⟩ := by
    have hyeq : (⟨y, hy₁⟩ : mBSubgroup hyp (hyp.conjFinset l B) (hyp.conjFinset_nonempty hB))
        = ⟨((l : G) * h * (l : G)⁻¹) * ((l : G) * b * (l : G)⁻¹), by rw [← hyhb]; exact hy₁⟩ :=
      Subtype.ext hyhb
    rw [hyeq]
    exact hyp.alphaB_apply_mul hconj (hyp.conjFinset_nonempty hB) α hh'mem hb'mem
      (by rw [← hyhb]; exact hy₁)
  -- Bridge: `α(lbl⁻¹) = α(b)` by `L`-class invariance (conjugator `l⁻¹`).
  rw [hLHS, hRHS]
  refine ClassFunction.of_isConj α (isConj_iff.mpr ⟨l⁻¹, ?_⟩)
  apply Subtype.ext
  push_cast; group

/-- **Peterfalvi (2.10.1) (Dade-specific).**  The induced class function
`Ind_{M(B^x)}^G α_{B^x}` is `L`-conjugacy invariant: it equals `Ind_{M(B)}^G α_B`.

This is the textbook (2.10.1) used to re-index the inclusion–exclusion sum over `ℬ`
(`L`-conjugacy class representatives of nonempty subsets) into one over all nonempty subsets `𝒫`.
The proof combines the subgroup conjugation `M(B^l) = M(B)^l` (`mBSubgroup_conjFinset_eq_map`),
the class function transport `α_{B^l} = transportConj l α_B` (`alphaB_conjFinset_eq_transportConj`),
and the generic `induce_map_conj`. -/
theorem induce_alphaB_conjFinset (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (l : L) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) (α : ClassFunction L ℂ)
    [Invertible (Nat.card (mBSubgroup hyp (hyp.conjFinset l B)
      (hyp.conjFinset_nonempty hB)) : ℂ)]
    [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)] :
    ClassFunction.induce (mBSubgroup hyp (hyp.conjFinset l B) (hyp.conjFinset_nonempty hB))
        (alphaB hyp hconj (hyp.conjFinset_nonempty hB) α)
      = ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hconj hB α) := by
  haveI : Invertible (Nat.card ((mBSubgroup hyp B hB).map
      (MulAut.conj (l : G) : G →* G)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- Step 1: rewrite the source subgroup to `M(B)^l` and identify the class functions.
  rw [induce_congr_of_subgroup_eq (hyp.mBSubgroup_conjFinset_eq_map hconj l hB)
    (θ₂ := ClassFunction.transportConj (l : G) (alphaB hyp hconj hB α))
    (fun x hx₁ hx₂ => hyp.alphaB_conjFinset_eq_transportConj hconj l hB α x hx₁ hx₂)]
  -- Step 2: generic (2.10.1) `Ind_{H^ℓ}(transportConj ℓ θ) = Ind_H θ`.
  exact ClassFunction.induce_map_conj (l : G) (alphaB hyp hconj hB α)

end ConjugacyInvariance

/- 2.10: The `L`-conjugacy transversal `ℬ` of nonempty subsets of `A`. -/

section Transversal

/-- **Peterfalvi (2.10), the `L`-action on subsets of `A`.**  The `L`-conjugation action
`conjFinset` (`B ↦ B^l = {l·a·l⁻¹ | a ∈ B}`) on `Finset {a : G // a ∈ A}` is a `MulAction`:
the action laws are exactly `conjFinset_one` and `conjFinset_mul`.

This is the action whose orbits index the inclusion–exclusion sum (2.10): the alternating sum
`-∑_{B ∈ ℬ} (-1)^{|B|} Ind_{M(B)} α_B` runs over `L`-conjugacy class representatives `ℬ` of the
nonempty subsets, made well defined by `induce_alphaB_conjFinset` ((2.10.1)) and `conjFinset_card`
(the sign `(-1)^{|B|}` is `L`-invariant since `|B^l| = |B|`).  It is provided as a `def` (not a
global instance) because it depends on the hypothesis `hyp`; downstream lemmas activate it with
`letI := hyp.conjFinsetAction`. -/
@[reducible] noncomputable def conjFinsetAction (hyp : Hypothesis G A L) :
    MulAction L (Finset {a : G // a ∈ A}) where
  smul := hyp.conjFinset
  one_smul := hyp.conjFinset_one
  mul_smul := hyp.conjFinset_mul

@[simp] theorem conjFinsetAction_smul (hyp : Hypothesis G A L) (l : L)
    (B : Finset {a : G // a ∈ A}) :
    (letI := hyp.conjFinsetAction; l • B) = hyp.conjFinset l B := rfl

/-- **Peterfalvi (2.10), the stabilizer is `N_L(B)`.**  Under the `conjFinset` action, the
`MulAction` stabilizer of `B` is exactly the set-stabilizer `setLStabilizer hyp B = N_L(B)`.

`l • B = B` unfolds to `B.image (conjA l) = B`; since `conjA l` is injective this is equivalent to
`conjA l` mapping `B` into `B`, i.e. `∀ a ∈ B, conjA l a ∈ B` — the defining condition of
`setLStabilizer`.  This identifies the orbit-stabilizer weight `|orbit B| = [L : N_L(B)]` used in
(2.10). -/
theorem stabilizer_conjFinsetAction (hyp : Hypothesis G A L)
    (B : Finset {a : G // a ∈ A}) :
    (letI := hyp.conjFinsetAction; MulAction.stabilizer L B) = setLStabilizer hyp B := by
  classical
  letI := hyp.conjFinsetAction
  ext l
  rw [MulAction.mem_stabilizer_iff, mem_setLStabilizer]
  change hyp.conjFinset l B = B ↔ ∀ a ∈ B, hyp.conjA l a ∈ B
  constructor
  · intro hl a ha
    rw [← hl]
    exact (hyp.mem_conjFinset).mpr ⟨a, ha, rfl⟩
  · intro hl
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := (hyp.mem_conjFinset).mp ha
      exact hl b hb
    · rw [hyp.conjFinset_card]

/-- **Peterfalvi (2.10), the transversal `ℬ`.**  The quotient of `Finset {a : G // a ∈ A}` by the
`L`-conjugacy relation (`conjFinset` orbits); its elements index the inclusion–exclusion sum once
restricted to nonempty subsets.  Representatives are obtained via `Quotient.out` (`transversalRep`),
realizing Peterfalvi's "`ℬ` = set of representatives of the `L`-conjugacy classes of subsets". -/
noncomputable def conjClassQuotient (hyp : Hypothesis G A L) : Type _ :=
  letI := hyp.conjFinsetAction
  MulAction.orbitRel.Quotient L (Finset {a : G // a ∈ A})

instance (hyp : Hypothesis G A L) : Finite hyp.conjClassQuotient := by
  classical
  unfold Hypothesis.conjClassQuotient
  letI := hyp.conjFinsetAction
  letI : Finite (Finset {a : G // a ∈ A}) := Finite.of_fintype _
  infer_instance

/-- A chosen representative subset of an `L`-conjugacy class (`Quotient.out`).  This is one element
of Peterfalvi's transversal `ℬ`. -/
noncomputable def transversalRep (hyp : Hypothesis G A L)
    (C : hyp.conjClassQuotient) : Finset {a : G // a ∈ A} :=
  letI := hyp.conjFinsetAction
  Quotient.out (s := MulAction.orbitRel L (Finset {a : G // a ∈ A})) C

/-- The chosen representative of the class of `B` is `L`-conjugate to `B`: there is some `l ∈ L`
with `transversalRep ⟦B⟧ = B^l`.  This is the well-definedness bridge from `ℬ` back to arbitrary
subsets, dual to `induce_alphaB_conjFinset` (2.10.1). -/
theorem transversalRep_conj (hyp : Hypothesis G A L) (B : Finset {a : G // a ∈ A}) :
    letI := hyp.conjFinsetAction
    ∃ l : L, hyp.transversalRep (Quotient.mk'' B) = hyp.conjFinset l B := by
  letI := hyp.conjFinsetAction
  have hout : (Quotient.mk'' (hyp.transversalRep (Quotient.mk'' B)) :
      MulAction.orbitRel.Quotient L (Finset {a : G // a ∈ A})) = Quotient.mk'' B := by
    rw [transversalRep]
    exact Quotient.out_eq' _
  obtain ⟨l, hl⟩ := Quotient.exact' hout
  exact ⟨l, hl.symm⟩

/-- **Peterfalvi (2.10), orbit-stabilizer weight.**  For a subset `B`, the size of its
`L`-conjugacy orbit times `|N_L(B)|` equals `|L|`.  Equivalently `|orbit B| = [L : N_L(B)]`, the
fibrewise weight attached to each representative `B ∈ ℬ` in the (2.10) sum normalization.

This is the orbit-stabilizer theorem `card_orbit_mul_card_stabilizer_eq_card_group` specialized to
the `conjFinset` action, with the stabilizer rewritten to `setLStabilizer hyp B`
(`stabilizer_conjFinsetAction`).  Stated with `Nat.card` so no ambient `Fintype L` is needed. -/
theorem card_orbit_mul_card_setLStabilizer (hyp : Hypothesis G A L)
    (B : Finset {a : G // a ∈ A}) :
    letI := hyp.conjFinsetAction
    Nat.card (MulAction.orbit L B) * Nat.card (setLStabilizer hyp B)
      = Nat.card L := by
  classical
  letI := hyp.conjFinsetAction
  letI : Fintype L := Fintype.ofFinite L
  letI : Fintype (MulAction.orbit L B) := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer L B) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← hyp.stabilizer_conjFinsetAction B, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group L B

end Transversal

/- 2.10.3: Pointwise value of `Ind_{M(B)}^G α_B` (Dade-specific form). -/

section PointwiseValue

open scoped Classical in
/-- **Peterfalvi (2.10.3), the conjugating set `𝒜(g, X)`.**  For `g : G` and a subset
`X ⊆ G`, `𝒜(g, X) = { x ∈ G | x⁻¹ g x ∈ X }`, as a `Finset G` (using `[Fintype G]`).
This is the index set of the transversal sum in the induced-character value formula. -/
noncomputable def conjFiber (g : G) (X : Set G) : Finset G :=
  Finset.univ.filter (fun x : G => x⁻¹ * g * x ∈ X)

@[simp] theorem mem_conjFiber {g x : G} {X : Set G} :
    x ∈ conjFiber g X ↔ x⁻¹ * g * x ∈ X := by
  classical
  simp [conjFiber]

open scoped Classical in
/-- **Peterfalvi (2.10.3), first displayed equation (transversal form).**  The pointwise
value of the induced class function `Ind_{M(B)}^G α_B` at `g`:

    `(Ind_{M(B)}^G α_B)(g) = ⅟|M(B)| · ∑_{x ∈ 𝒜(g, M(B))} induceTerm M(B) α_B x g`.

This is the literal first line of Peterfalvi's proof of (2.10.3): the induction formula
`induce_apply_eq_sum_filter`, restated with the conjugating set `𝒜(g, M(B)) = conjFiber`.
On the filter the summand `induceTerm M(B) α_B x g` *is* `α_B(x⁻¹ g x)`
(`alphaB_induceTerm_of_mem` below). -/
theorem induce_alphaB_apply_eq_sum_conjFiber (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (α : ClassFunction L ℂ) [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)] (g : G) :
    ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hconj hB α) g
      = ⅟(Nat.card (mBSubgroup hyp B hB) : ℂ) *
          ∑ x ∈ conjFiber g (↑(mBSubgroup hyp B hB) : Set G),
            ClassFunction.induceTerm (mBSubgroup hyp B hB) (alphaB hyp hconj hB α) x g := by
  rw [ClassFunction.induce_apply_eq_sum_filter]
  rfl

/-- On the conjugating set `𝒜(g, M(B))`, the induction summand `induceTerm M(B) α_B x g`
is the explicit value `α_B(x⁻¹ g x)`.  Combined with
`induce_alphaB_apply_eq_sum_conjFiber` this is the `α_B`-explicit first line of (2.10.3). -/
theorem alphaB_induceTerm_of_mem (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) (α : ClassFunction L ℂ)
    {x g : G} (hx : x⁻¹ * g * x ∈ mBSubgroup hyp B hB) :
    ClassFunction.induceTerm (mBSubgroup hyp B hB) (alphaB hyp hconj hB α) x g
      = alphaB hyp hconj hB α ⟨x⁻¹ * g * x, hx⟩ :=
  ClassFunction.induceTerm_of_mem _ hx

/-- **Peterfalvi (2.10.3), the `α_B(x⁻¹gx) = α(b)` collapse.**  For `x ∈ 𝒜(g, M(B))`,
write the conjugate `x⁻¹ g x = h · b` with `h ∈ H(B)` and `b ∈ N_L(B)` (the semidirect
factorization of `M(B)`, `coe_mBSubgroup`).  Then the induction summand collapses, via the
(2.9) defining equation `alphaB_apply_mul`, to `α(b)`.

This isolates the value half of Peterfalvi's "`α_B(x⁻¹ g x) = α(b)`" step (the membership
half — `α(b) ≠ 0 ⟹ b ∈ A` and then `g ∈ (bH(b))^G` — is the coprime-conjugacy argument
driving the `card_conj_fiber` aggregation, tracked separately). -/
theorem exists_nLStabilizerIn_alphaB_induceTerm (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (α : ClassFunction L ℂ) {x g : G} (hx : x⁻¹ * g * x ∈ mBSubgroup hyp B hB) :
    ∃ (h : G) (_ : h ∈ hIntersection hyp B hB) (b : G) (hb : b ∈ nLStabilizerIn hyp B),
      x⁻¹ * g * x = h * b ∧
        ClassFunction.induceTerm (mBSubgroup hyp B hB) (alphaB hyp hconj hB α) x g
          = α ⟨b, nLStabilizerIn_le_L hyp B hb⟩ := by
  classical
  -- factor `x⁻¹ g x = h * b` with `h ∈ H(B)`, `b ∈ N_L(B)`
  have hmem_prod : x⁻¹ * g * x
      ∈ (↑(hIntersection hyp B hB) * ↑(nLStabilizerIn hyp B) : Set G) := by
    rw [← hyp.coe_mBSubgroup hconj hB]; exact hx
  obtain ⟨h, hh, b, hb, hhb⟩ := hmem_prod
  -- `hhb : h * b = x⁻¹ * g * x`
  refine ⟨h, hh, b, hb, hhb.symm, ?_⟩
  have hhbeq : h * b = x⁻¹ * g * x := hhb
  have hhbM : h * b ∈ mBSubgroup hyp B hB := by rw [hhbeq]; exact hx
  have harg : (⟨x⁻¹ * g * x, hx⟩ : mBSubgroup hyp B hB) = ⟨h * b, hhbM⟩ :=
    Subtype.ext hhb.symm
  calc ClassFunction.induceTerm (mBSubgroup hyp B hB) (alphaB hyp hconj hB α) x g
      = alphaB hyp hconj hB α ⟨x⁻¹ * g * x, hx⟩ :=
        alphaB_induceTerm_of_mem hyp hconj hB α hx
    _ = alphaB hyp hconj hB α ⟨h * b, hhbM⟩ := congrArg (alphaB hyp hconj hB α) harg
    _ = α ⟨b, nLStabilizerIn_le_L hyp B hb⟩ := hyp.alphaB_apply_mul hconj hB α hh hb hhbM

/-- **Coprimality of `orderOf b` with `|H(B)|`** (Peterfalvi (2.2.c), the input to (2.1) in the
proof of (2.10.3)).  For `b ∈ A`, the order of `b` is coprime to `|H(B)|`: `|H(B)| ∣ |H(b₀)|`
for any `b₀ ∈ B` (`H(B) ⊆ H(b₀)`), which is coprime to `|C_L(b)|` by `centralizer_coprime`, and
`orderOf b ∣ |C_L(b)|` since `b ∈ C_L(b)`. -/
theorem coprime_orderOf_card_hIntersection (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) {b : G} (hbA : b ∈ A) :
    Nat.Coprime (orderOf b) (Nat.card (hIntersection hyp B hB)) := by
  obtain ⟨b₀, hb₀⟩ := hB.exists_mem
  have hdvdH : Nat.card (hIntersection hyp B hB) ∣ Nat.card (hyp.H b₀) :=
    Subgroup.card_dvd_of_le (hIntersection_le hyp hB hb₀)
  have hcop : Nat.Coprime (Nat.card (hyp.H b₀)) (Nat.card (centralizerIn L b)) :=
    hyp.centralizer_coprime b₀ ⟨b, hbA⟩
  have hcop' : Nat.Coprime (Nat.card (hIntersection hyp B hB))
      (Nat.card (centralizerIn L b)) :=
    Nat.Coprime.coprime_dvd_left hdvdH hcop
  exact (Nat.Coprime.coprime_dvd_right (hyp.orderOf_dvd_card_centralizerIn hbA) hcop').symm

/-- **Peterfalvi (2.10.3), the vanishing case.**  If `g` lies outside `⋃_{a∈A} (aH(a))^G` (the
Dade support), then `(Ind_{M(B)}^G α_B)(g) = 0`.

Each summand `induceTerm M(B) α_B x g` over `x ∈ 𝒜(g, M(B))`, if nonzero, has
`x⁻¹ g x = h·b` with `h ∈ H(B)`, `b ∈ N_L(B)` and `α(b) ≠ 0`, so `b ∈ A`
(`exists_nLStabilizerIn_alphaB_induceTerm` + support of `α`).  By (2.1)
(`exists_mem_centralizer_conj`, with `b` normalizing the coprime `H(B)`), `h·b` is
`H(B)`-conjugate to `c·b` with `c ∈ C_{H(B)}(b) = H(B∪{b}) ⊆ H(b)` (`centralizer_inf_hIntersection`);
since `c` commutes with `b`, `c·b = b·c ∈ b·H(b) ⊆ hCoset b`, so `g ∈ (bH(b))^G ⊆ dadeSupport` —
contradicting `g ∉ dadeSupport`.  Hence every summand vanishes. -/
theorem induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)] {g : G} (hg : g ∉ hyp.dadeSupport) :
    ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hconj hB (α : ClassFunction L ℂ)) g
      = 0 := by
  classical
  rw [induce_alphaB_apply_eq_sum_conjFiber hyp hconj hB (α : ClassFunction L ℂ) g]
  rw [mul_eq_zero]; right
  apply Finset.sum_eq_zero
  intro x hx
  rw [mem_conjFiber] at hx
  -- factor the conjugate and read off the summand value `α(b)`
  obtain ⟨h, hh, b, hb, hxgx, hterm⟩ :=
    hyp.exists_nLStabilizerIn_alphaB_induceTerm hconj hB (α : ClassFunction L ℂ) hx
  rw [hterm]
  by_contra hαb
  -- `α(b) ≠ 0 ⇒ b ∈ A`
  have hbA : b ∈ A := α.property hαb
  -- `b` normalizes `H(B)` and is coprime to `|H(B)|`; apply (2.1)
  have hnorm : ∀ y ∈ hIntersection hyp B hB, b * y * b⁻¹ ∈ hIntersection hyp B hB := by
    intro y hy
    have := hyp.nLStabilizerIn_le_normalizer hconj hB hb
    rw [Subgroup.mem_normalizer_iff] at this
    exact (this y).mp hy
  have hcop := hyp.coprime_orderOf_card_hIntersection hB hbA
  obtain ⟨c, hcmem, x', hx'H, hx'eq⟩ :=
    OddOrder.GroupTheory.exists_mem_centralizer_conj (g := b) (H := hIntersection hyp B hB)
      hcop hnorm hh
  -- `c ∈ C_{H(B)}(b) = H(B ∪ {b}) ⊆ H(b)`, and `c` commutes with `b`
  obtain ⟨hcH, hccomm⟩ := Subgroup.mem_inf.mp hcmem
  have hccb : Commute c b :=
    Subgroup.mem_centralizer_singleton_iff.mp hccomm
  have hcHb : c ∈ hyp.H ⟨b, hbA⟩ := by
    have hcInsert : c ∈ hIntersection hyp (insert ⟨b, hbA⟩ B)
        (Finset.insert_nonempty _ B) := by
      rw [← hyp.centralizer_inf_hIntersection hB ⟨b, hbA⟩]
      exact Subgroup.mem_inf.mpr ⟨hccomm, hcH⟩
    exact hIntersection_le hyp (Finset.insert_nonempty _ B) (Finset.mem_insert_self _ B) hcInsert
  -- `c·b = b·c ∈ hCoset b`
  have hcb_mem : c * b ∈ hyp.hCoset ⟨b, hbA⟩ := by
    rw [mem_hCoset]
    exact ⟨c, hcHb, hccb.eq⟩
  -- `g` is conjugate to `c·b` (via `x' x⁻¹`), hence in `dadeSupport`
  have hgconj : (x' * x⁻¹) * g * (x' * x⁻¹)⁻¹ = c * b := by
    rw [← hx'eq, ← hxgx]; group
  apply hg
  rw [hyp.mem_dadeSupport_iff]
  refine ⟨⟨b, hbA⟩, c, hcHb, ?_⟩
  rw [show (⟨b, hbA⟩ : {a : G // a ∈ A}).1 * c = c * b from (hccb.eq).symm]
  exact (isConj_iff.mpr ⟨x' * x⁻¹, hgconj⟩).symm

/-- **The `N_L(B)`-component of an element of `M(B)`.**  For `m ∈ M(B)` and `b ∈ N_L(B)`, the
quotient homomorphism `f_B = dadeQuotientHom` sends `m` to `b` (in `L`) exactly when `m` lies in
the coset `H(B)·b`.  This realizes the semidirect decomposition `M(B) = H(B) ⋊ N_L(B)`: `f_B`
projects onto the `N_L(B)`-factor, with fibers the `H(B)`-cosets.

`(⇐)` `m = h·b` with `h ∈ H(B) = ker f_B`, `b ∈ N_L(B)` (retracted by `f_B`); `(⇒)` `m·b⁻¹` maps
to `1` under `f_B`, hence lies in `ker f_B = H(B)`. -/
theorem dadeQuotientHom_eq_iff_mem_hIntersection_mul (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (m : mBSubgroup hyp B hB) {b : G} (hb : b ∈ nLStabilizerIn hyp B) :
    ((hyp.dadeQuotientHom hconj hB m : L) : G) = b ↔
      (m : G) ∈ (↑(hIntersection hyp B hB) : Set G) * ({b} : Set G) := by
  classical
  set bM : mBSubgroup hyp B hB := ⟨b, hyp.nLStabilizerIn_le_mBSubgroup hB hb⟩ with hbM
  have hfbM : ((hyp.dadeQuotientHom hconj hB bM : L) : G) = b :=
    hyp.dadeQuotientHom_coe_of_mem_nLStabilizerIn hconj hB bM hb
  constructor
  · intro hfm
    -- `m * bM⁻¹ ∈ ker = H(B)`
    have hker : (m * bM⁻¹ : mBSubgroup hyp B hB) ∈ (hyp.dadeQuotientHom hconj hB).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hfm, hfbM, mul_inv_cancel]
      rfl
    rw [hyp.ker_dadeQuotientHom hconj hB, Subgroup.mem_subgroupOf] at hker
    -- `(m * bM⁻¹ : G) = (m:G) * b⁻¹ ∈ H(B)`, so `(m:G) = (that) * b ∈ H(B)·b`
    refine ⟨(m : G) * b⁻¹, ?_, b, rfl, ?_⟩
    · have : ((m * bM⁻¹ : mBSubgroup hyp B hB) : G) = (m : G) * b⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rwa [this] at hker
    · group
  · rintro ⟨h, hh, _, rfl, hmeq⟩
    -- `m = h·b` with `h ∈ H(B)`, so `f_B(m) = f_B(h)·f_B(b) = 1·b = b`
    have hhM : h ∈ mBSubgroup hyp B hB := hyp.hIntersection_le_mBSubgroup hB hh
    have hmsplit : m = (⟨h, hhM⟩ : mBSubgroup hyp B hB) * bM := by
      apply Subtype.ext; rw [Subgroup.coe_mul]; exact hmeq.symm
    have hfh : hyp.dadeQuotientHom hconj hB ⟨h, hhM⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hyp.ker_dadeQuotientHom hconj hB, Subgroup.mem_subgroupOf]
      exact hh
    rw [hmsplit, map_mul, hfh, one_mul, hfbM]

/-- The `f_B`-image of any `m ∈ M(B)` lands in the `N_L(B)`-factor: `f_B(m) ∈ N_L(B)`.
This is structural — `f_B = dadeQuotientHom` factors through the inclusion `N_L(B) ≤ L`. -/
theorem dadeQuotientHom_mem_nLStabilizerIn (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (m : mBSubgroup hyp B hB) :
    ((hyp.dadeQuotientHom hconj hB m : L) : G) ∈ nLStabilizerIn hyp B := by
  haveI : ((hIntersection hyp B hB).subgroupOf (mBSubgroup hyp B hB)).Normal :=
    hyp.hIntersection_subgroupOf_normal hconj hB
  -- `dadeQuotientHom m = inclusion(N_L(B) ≤ L) z` for `z = …`
  set z : nLStabilizerIn hyp B :=
    (Subgroup.subgroupOfEquivOfLe (hyp.nLStabilizerIn_le_mBSubgroup hB))
      ((hyp.isComplement'_subgroupOf hconj hB).QuotientMulEquiv (QuotientGroup.mk' _ m)) with hz
  have hval : hyp.dadeQuotientHom hconj hB m = Subgroup.inclusion (hyp.nLStabilizerIn_le_L B) z :=
    rfl
  rw [hval]
  exact z.2

open Classical in
/-- **Peterfalvi (2.10.3), the `N_L(B)`-aggregated value (value case, before specialization).**
The pointwise value of `Ind_{M(B)}^G α_B` regrouped over the `N_L(B)`-component `b` of the
conjugate `x⁻¹ g x`:

    `(Ind_{M(B)}^G α_B)(g) = ⅟|M(B)| · ∑_{b ∈ N_L(B)} α(b) · |𝒜(g, H(B)·b)|`.

This is the heart of (2.10.3): the conjugating set `𝒜(g, M(B))` partitions over the
`N_L(B)`-factor of `M(B) = H(B) ⋊ N_L(B)`; on the fiber `{x : comp(x⁻¹gx) = b}` the induction
summand is the constant `α(b)` (the (2.9) defining equation, `alphaB_apply_mul`), and that fiber is
exactly `𝒜(g, H(B)·b)` (`dadeQuotientHom_eq_iff_mem_hIntersection_mul`).  The textbook value
formula `(α(a)/|M(B)|)·∑_{b ∈ N_L(B)∩a^L} |𝒜(g, H(B)b)|` follows by discarding the `b ∉ a^L` terms
(where `α(b) = 0` by support of `α`) once `g ∈ (aH(a))^G` is fixed. -/
theorem induce_alphaB_apply_eq_sum_nLStabilizerIn (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (α : ClassFunction L ℂ) [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)] (g : G) :
    ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hconj hB α) g
      = ⅟(Nat.card (mBSubgroup hyp B hB) : ℂ) *
          ∑ b : (nLStabilizerIn hyp B),
            α ⟨(b : G), nLStabilizerIn_le_L hyp B b.2⟩ *
              (conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(b : G)} : Set G))).card := by
  rw [induce_alphaB_apply_eq_sum_conjFiber hyp hconj hB α g]
  congr 1
  -- The component map sends `𝒜(g, M(B))` into `N_L(B)` (the `f_B`-image, with a junk default).
  set φ : G → nLStabilizerIn hyp B := fun x =>
    if hx : x⁻¹ * g * x ∈ mBSubgroup hyp B hB then
      ⟨((hyp.dadeQuotientHom hconj hB ⟨x⁻¹ * g * x, hx⟩ : L) : G),
        hyp.dadeQuotientHom_mem_nLStabilizerIn hconj hB ⟨x⁻¹ * g * x, hx⟩⟩
    else 1 with hφ
  have hmaps : ∀ x ∈ conjFiber g (↑(mBSubgroup hyp B hB) : Set G),
      φ x ∈ (Finset.univ : Finset (nLStabilizerIn hyp B)) := fun x _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (f := fun x => ClassFunction.induceTerm (mBSubgroup hyp B hB) (alphaB hyp hconj hB α) x g)]
  apply Finset.sum_congr rfl
  intro b _
  -- the fiber over `b` is `𝒜(g, H(B)·b)`, and the summand is constant `α(b)` there
  have hfiber_eq : (conjFiber g (↑(mBSubgroup hyp B hB) : Set G)).filter (fun x => φ x = b)
      = conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(b : G)} : Set G)) := by
    ext x
    simp only [Finset.mem_filter, mem_conjFiber]
    -- value of `φ x` when `x⁻¹gx ∈ M(B)`
    have hφval : ∀ hxM : x⁻¹ * g * x ∈ mBSubgroup hyp B hB,
        ((φ x : nLStabilizerIn hyp B) : G)
          = ((hyp.dadeQuotientHom hconj hB ⟨x⁻¹ * g * x, hxM⟩ : L) : G) := by
      intro hxM
      simp only [hφ, dif_pos hxM]
    constructor
    · rintro ⟨hxM, hφx⟩
      have hφx' : ((hyp.dadeQuotientHom hconj hB ⟨x⁻¹ * g * x, hxM⟩ : L) : G) = (b : G) := by
        rw [← hφval hxM, hφx]
      exact (hyp.dadeQuotientHom_eq_iff_mem_hIntersection_mul hconj hB
        ⟨x⁻¹ * g * x, hxM⟩ b.2).mp hφx'
    · intro hxHb
      rw [Set.mem_mul] at hxHb
      obtain ⟨h, hh, b', hb', hmeq⟩ := hxHb
      rw [Set.mem_singleton_iff] at hb'
      subst hb'
      have hxM : x⁻¹ * g * x ∈ mBSubgroup hyp B hB := by
        rw [← hmeq]
        exact (mBSubgroup hyp B hB).mul_mem (hyp.hIntersection_le_mBSubgroup hB hh)
          (hyp.nLStabilizerIn_le_mBSubgroup hB b.2)
      refine ⟨hxM, ?_⟩
      apply Subtype.ext
      rw [hφval hxM]
      exact (hyp.dadeQuotientHom_eq_iff_mem_hIntersection_mul hconj hB
        ⟨x⁻¹ * g * x, hxM⟩ b.2).mpr ⟨h, hh, _, rfl, hmeq⟩
  rw [hfiber_eq]
  -- on `𝒜(g, H(B)·b)` every summand is `α(b)`
  have hconst : ∀ x ∈ conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(b : G)} : Set G)),
      ClassFunction.induceTerm (mBSubgroup hyp B hB) (alphaB hyp hconj hB α) x g
        = α ⟨(b : G), nLStabilizerIn_le_L hyp B b.2⟩ := by
    intro x hx
    rw [mem_conjFiber] at hx
    rw [Set.mem_mul] at hx
    obtain ⟨h, hh, b', hb', hmeq⟩ := hx
    rw [Set.mem_singleton_iff] at hb'
    subst hb'
    have hxM : x⁻¹ * g * x ∈ mBSubgroup hyp B hB := by
      rw [← hmeq]
      exact (mBSubgroup hyp B hB).mul_mem (hyp.hIntersection_le_mBSubgroup hB hh)
        (hyp.nLStabilizerIn_le_mBSubgroup hB b.2)
    rw [alphaB_induceTerm_of_mem hyp hconj hB α hxM]
    have harg : (⟨x⁻¹ * g * x, hxM⟩ : mBSubgroup hyp B hB)
        = ⟨h * (b : G), by rw [hmeq]; exact hxM⟩ := Subtype.ext hmeq.symm
    rw [harg]
    exact hyp.alphaB_apply_mul hconj hB α hh b.2 _
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_comm]

open Classical in
/-- **Peterfalvi (2.10.3), the support-restricted value.**  When `α ∈ CF(L, A)` is supported on
`A`, the `N_L(B)`-aggregated value of `Ind_{M(B)}^G α_B` may be summed over only those
`b ∈ N_L(B)` lying in `A`:

    `(Ind_{M(B)}^G α_B)(g) = ⅟|M(B)| · ∑_{b ∈ N_L(B), b ∈ A} α(b) · |𝒜(g, H(B)·b)|`.

This is the first reduction of (2.10.3)'s value case: the terms with `b ∉ A` carry a vanishing
factor `α(b) = 0` (support of `α`) and so drop out of the `N_L(B)`-sum of
`induce_alphaB_apply_eq_sum_nLStabilizerIn`.  After fixing a Dade-support representative `a` with
`g ∈ (aH(a))^G`, the surviving `b` are moreover `L`-conjugate to `a` (Peterfalvi (2.4.b)), which
collapses `α(b)` to the constant `α(a)` in the textbook value formula. -/
theorem induce_alphaB_apply_eq_sum_nLStabilizerIn_inA (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)] (g : G) :
    ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hconj hB (α : ClassFunction L ℂ)) g
      = ⅟(Nat.card (mBSubgroup hyp B hB) : ℂ) *
          ∑ b ∈ (Finset.univ : Finset (nLStabilizerIn hyp B)).filter
              (fun b : (nLStabilizerIn hyp B) => ((b : G) ∈ A)),
            (α : ClassFunction L ℂ) ⟨(b : G), nLStabilizerIn_le_L hyp B b.2⟩ *
              (conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(b : G)} : Set G))).card := by
  rw [induce_alphaB_apply_eq_sum_nLStabilizerIn hyp hconj hB (α : ClassFunction L ℂ) g]
  congr 1
  -- terms with `b ∉ A` vanish since `α(b) = 0` there (support of `α`)
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun b _ hb => ?_).symm
  rw [Finset.mem_filter] at hb
  have hbA : (b : G) ∉ A := fun h => hb ⟨Finset.mem_univ _, h⟩
  have hα0 : (α : ClassFunction L ℂ) ⟨(b : G), nLStabilizerIn_le_L hyp B b.2⟩ = 0 := by
    by_contra hαne
    exact hbA (α.property hαne)
  rw [hα0, zero_mul]

end PointwiseValue

/- 2.10/2.6.b: The right-hand side of the inclusion–exclusion is a virtual character. -/

section VirtualCharacterRHS

/-- **Peterfalvi (2.6.b), each summand is a virtual character.**  For `α ∈ ℤ[Irr L]` and a
nonempty `B ⊆ A`, the induced class function `Ind_{M(B)}^G α_B` lies in `ℤ[Irr G]`.

This is the building block of the (2.10) inclusion–exclusion's right-hand side
`-∑_{B ∈ ℬ} (-1)^{|B|} Ind_{M(B)}^G α_B`: each term is a virtual character, so any
`ℤ`-linear (in particular alternating) combination is one too.  It chains the (2.9)
pullback `alphaB_mem_ZIrr` (`α_B = α ∘ f_B ∈ ℤ[Irr M(B)]`) with the induction lemma
`ClassFunction.induce_mem_ZIrr` (induction preserves `ℤ[Irr]`). -/
theorem induce_alphaB_mem_ZIrr (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    [Invertible (Nat.card G : ℂ)]
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) {α : ClassFunction L ℂ}
    (hα : α ∈ ZIrr L) [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)] :
    ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hconj hB α) ∈ ZIrr G := by
  haveI : Fintype (mBSubgroup hyp B hB) := Fintype.ofFinite _
  exact ClassFunction.induce_mem_ZIrr (mBSubgroup hyp B hB)
    (hyp.alphaB_mem_ZIrr hconj hB hα)

/-- **Peterfalvi (2.10), an inclusion–exclusion summand `Ind_{M(B)}^G α_B`.**  Packaged as a
`ClassFunction G ℂ` carrying its own `Invertible (|M(B)| : ℂ)` instance (supplied from
`Nat.card_pos`), so the (2.10) right-hand side `-∑_{B ∈ ℬ} (-1)^{|B|} Ind_{M(B)} α_B` can be
formed as an ordinary `Finset` sum without threading invertibility through each binder.  The
subset `B` is carried together with its nonemptiness proof as the subtype `{B // B.Nonempty}`. -/
noncomputable def induceAlphaBTerm (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (α : ClassFunction L ℂ) (p : {B : Finset {a : G // a ∈ A} // B.Nonempty}) :
    ClassFunction G ℂ :=
  letI : Invertible (Nat.card (mBSubgroup hyp p.1 p.2) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  ClassFunction.induce (mBSubgroup hyp p.1 p.2) (alphaB hyp hconj p.2 α)

/-- **Peterfalvi (2.10.1), packaged form.**  The inclusion–exclusion summand `induceAlphaBTerm`
is `L`-conjugacy invariant: replacing the subset `B` by a conjugate `B^l` leaves
`Ind_{M(B)}^G α_B` unchanged.

This lifts the bare-`induce` invariance `induce_alphaB_conjFinset` ((2.10.1) Dade-specific) to the
packaged `ClassFunction G ℂ` summand `induceAlphaBTerm` (which carries its own `Invertible (|M(B)|
: ℂ)` instance).  It is the well-definedness fact making the (2.10) right-hand side
`-∑_{B ∈ ℬ} (-1)^{|B|} Ind_{M(B)} α_B` independent of the chosen transversal representatives:
together with `conjFinset_card` (the sign `(-1)^{|B|}` is `L`-invariant) it lets the sum over the
transversal `ℬ` (`conjClassQuotient`/`transversalRep`) be re-indexed over all nonempty subsets. -/
theorem induceAlphaBTerm_conjFinset (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (α : ClassFunction L ℂ) (l : L) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    hyp.induceAlphaBTerm hconj α ⟨hyp.conjFinset l B, hyp.conjFinset_nonempty hB⟩
      = hyp.induceAlphaBTerm hconj α ⟨B, hB⟩ := by
  letI : Invertible (Nat.card (mBSubgroup hyp (hyp.conjFinset l B)
      (hyp.conjFinset_nonempty hB)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  simp only [induceAlphaBTerm]
  exact hyp.induce_alphaB_conjFinset hconj l hB α

/-- **Peterfalvi (2.6.b), each packaged summand is a virtual character.**  For `α ∈ ℤ[Irr L]`,
the term `induceAlphaBTerm` lies in `ℤ[Irr G]` — the `induce_alphaB_mem_ZIrr` content with the
invertibility instance pinned to the one carried by `induceAlphaBTerm`. -/
theorem induceAlphaBTerm_mem_ZIrr (hyp : Hypothesis G A L) (hconj : hyp.HConjInvariant)
    [Invertible (Nat.card G : ℂ)] {α : ClassFunction L ℂ} (hα : α ∈ ZIrr L)
    (p : {B : Finset {a : G // a ∈ A} // B.Nonempty}) :
    hyp.induceAlphaBTerm hconj α p ∈ ZIrr G := by
  letI : Invertible (Nat.card (mBSubgroup hyp p.1 p.2) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact hyp.induce_alphaB_mem_ZIrr hconj p.2 hα

/-- **Peterfalvi (2.10)/(2.6.b), the right-hand side is a virtual character.**  Any finite
`ℤ`-linear combination `∑_{p ∈ s} c p • Ind_{M(B)}^G α_B` of the inclusion–exclusion summands
(`induceAlphaBTerm`) is a virtual character of `G`.

This is part (d) of the (2.6.b) program: granting the (2.10) identity
`α^τ = -∑_{B ∈ ℬ} (-1)^{|B|} Ind_{M(B)} α_B` (the special case `c B = -(-1)^{|B|}` and
`s = ℬ`), the right-hand side, hence `α^τ`, lies in `ℤ[Irr G]`.  Immediate from
`Submodule.sum_mem` / `Submodule.smul_mem` over `induceAlphaBTerm_mem_ZIrr`. -/
theorem zsmul_induceAlphaBTerm_sum_mem_ZIrr (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) [Invertible (Nat.card G : ℂ)]
    {α : ClassFunction L ℂ} (hα : α ∈ ZIrr L)
    (s : Finset {B : Finset {a : G // a ∈ A} // B.Nonempty})
    (c : {B : Finset {a : G // a ∈ A} // B.Nonempty} → ℤ) :
    (∑ p ∈ s, c p • hyp.induceAlphaBTerm hconj α p) ∈ ZIrr G :=
  Submodule.sum_mem _ (fun p _ =>
    Submodule.smul_mem _ _ (hyp.induceAlphaBTerm_mem_ZIrr hconj hα p))

end VirtualCharacterRHS

/- 2.10: The Möbius (inclusion–exclusion) assembly of the Dade map. -/

section MobiusAssembly

open scoped Classical

/-- **Peterfalvi (2.1)/(2.10.3), the conjugating-set cardinality `|𝒜(g, K·a)| = |C_G(a)|`** when
`a` *centralizes* the subgroup `K` (so `K ⊆ C_G(a)`), `C_G(a)` normalizes `K`, `⟨a⟩` and `K` have
coprime orders, and `g` is `G`-conjugate to an element `a·x₀` (`x₀ ∈ K`).

This is the textbook's "`𝒜(g, H(a)a) = x C_G(a)`" remark.  The conjugating set
`𝒜(g, K·a) = {y | y⁻¹gy ∈ K·a}` is in bijection with the `card_conj_fiber` pair set
`{(p₁, p₂) | p₁ ∈ K ∧ p₂(a·p₁)p₂⁻¹ = g}`: each conjugator `y = p₂` determines a unique `p₁` via
`y⁻¹gy = a·p₁ ∈ a·K = K·a` (the cosets agree as `a` centralizes `K`).  By `card_conj_fiber` the pair
set has cardinality `|C_G(a)|`.  Applied at the Möbius survivor `B = {a}` (where `H({a}) = H(a) ⊆
C_G(a)`, normalized by `C_G(a)` via `H_normalized`) it evaluates the surviving term of (2.10). -/
theorem card_conjFiber_coset_eq_card_centralizer {K : Subgroup G} {a : G}
    (hcomm : ∀ x ∈ K, Commute a x)
    (hnorm : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ x ∈ K, c * x * c⁻¹ ∈ K)
    (hcop : Nat.Coprime (orderOf a) (Nat.card K))
    {g x₀ : G} (hx₀K : x₀ ∈ K) (hx₀ : IsConj (a * x₀) g) :
    (conjFiber g ((↑K : Set G) * ({a} : Set G))).card
      = Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  classical
  rw [← OddOrder.GroupTheory.card_conj_fiber hcomm hnorm hcop hx₀K hx₀]
  -- `(conjFiber g (K·a)).card = Nat.card {y // y⁻¹gy ∈ K·a}`.
  have hcard1 : (conjFiber g ((↑K : Set G) * ({a} : Set G))).card
      = Nat.card {y : G // y⁻¹ * g * y ∈ (↑K : Set G) * ({a} : Set G)} := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y => mem_conjFiber)
  rw [hcard1]
  -- Bijection `{y // y⁻¹gy ∈ K·a} ≃ {p : G×G // p.1 ∈ K ∧ p.2(a·p.1)p.2⁻¹ = g}`.
  refine Nat.card_congr ?_
  refine
    { toFun := fun y => ⟨(a⁻¹ * (y.1⁻¹ * g * y.1), y.1), ?_, ?_⟩
      invFun := fun p => ⟨p.1.2, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- `a⁻¹·(y⁻¹gy) ∈ K`: from `y⁻¹gy ∈ K·a = a·K`.
    show a⁻¹ * (y.1⁻¹ * g * y.1) ∈ K
    obtain ⟨h, hh, a', ha', hyeq⟩ := y.2
    rw [Set.mem_singleton_iff] at ha'
    simp only at hyeq
    -- `hyeq : h * a' = y.1⁻¹ * g * y.1`, `ha' : a' = a`
    rw [← hyeq, ha']
    have hreduce : a⁻¹ * (h * a) = h := by
      have hcomm_ha : a * h = h * a := (hcomm h hh).eq
      rw [← hcomm_ha]; group
    rw [hreduce]
    exact hh
  · -- `y·(a·(a⁻¹·(y⁻¹gy)))·y⁻¹ = g`
    show y.1 * (a * (a⁻¹ * (y.1⁻¹ * g * y.1))) * y.1⁻¹ = g
    group
  · -- `p.1.2⁻¹·g·p.1.2 ∈ K·a`: from `p.2(a·p.1)p.2⁻¹ = g`, `p.1∈K`.
    obtain ⟨⟨q1, q2⟩, hq1, hq2⟩ := p
    show q2⁻¹ * g * q2 ∈ (↑K : Set G) * ({a} : Set G)
    rw [Set.mem_mul]
    refine ⟨a * q1 * a⁻¹, ?_, a, Set.mem_singleton _, ?_⟩
    · -- `a·q1·a⁻¹ ∈ K` (`K` is normalized by `a`, which lies in `C_G(a)`)
      have hacomm : a * q1 * a⁻¹ = q1 := by rw [(hcomm q1 hq1).eq]; group
      rw [hacomm]; exact hq1
    · -- `q2⁻¹·g·q2 = (a·q1·a⁻¹)·a`
      have hconj : q2⁻¹ * g * q2 = a * q1 := by rw [← hq2]; group
      rw [hconj]; group
  · -- left inverse
    rintro ⟨y, hy⟩
    rfl
  · -- right inverse
    rintro ⟨⟨x, t⟩, hx, ht⟩
    apply Subtype.ext
    apply Prod.ext
    · -- `a⁻¹·(t⁻¹·g·t) = x` from `t(a·x)t⁻¹ = g`
      show a⁻¹ * (t⁻¹ * g * t) = x
      conv_lhs => rw [← ht]
      group
    · rfl

/-- **Peterfalvi (2.10.3), the support test for a single component `b`.**  For `b ∈ N_L(B)` with
`b ∈ A`, if some conjugate `y⁻¹gy` lies in the coset `H(B)·b` (i.e. `𝒜(g, H(B)b) ≠ ∅`), then
`g ∈ (bH(b))^G` lies in the Dade support.

This is the contrapositive content of the vanishing case
`induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport` isolated to one fiber: by (2.1)
(`exists_mem_centralizer_conj`, with `b` normalizing the coprime `H(B)`), `y⁻¹gy = h·b` is
`H(B)`-conjugate to `c·b` with `c ∈ C_{H(B)}(b) = H(B∪{b}) ⊆ H(b)` (`centralizer_inf_hIntersection`);
since `c` commutes with `b`, `c·b = b·c ∈ b·H(b) ⊆ hCoset b`, so `g ∈ (bH(b))^G`. -/
theorem exists_mem_H_isConj_of_mem_conjFiber_coset (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    {b : G} (hbN : b ∈ nLStabilizerIn hyp B) (hbA : b ∈ A) {g y : G}
    (hy : y⁻¹ * g * y ∈ (↑(hIntersection hyp B hB) : Set G) * ({b} : Set G)) :
    ∃ c ∈ hyp.H ⟨b, hbA⟩, IsConj (b * c) g := by
  classical
  -- factor `y⁻¹gy = h·b` with `h ∈ H(B)`
  rw [Set.mem_mul] at hy
  obtain ⟨h, hh, b', hb', hyeq⟩ := hy
  rw [Set.mem_singleton_iff] at hb'
  rw [hb'] at hyeq
  -- `hyeq : h * b = y⁻¹ * g * y`
  -- `b` normalizes `H(B)` and is coprime to `|H(B)|`; apply (2.1)
  have hnorm : ∀ z ∈ hIntersection hyp B hB, b * z * b⁻¹ ∈ hIntersection hyp B hB := by
    intro z hz
    have := hyp.nLStabilizerIn_le_normalizer hconj hB hbN
    rw [Subgroup.mem_normalizer_iff] at this
    exact (this z).mp hz
  have hcop := hyp.coprime_orderOf_card_hIntersection hB hbA
  obtain ⟨c, hcmem, x', hx'H, hx'eq⟩ :=
    OddOrder.GroupTheory.exists_mem_centralizer_conj (g := b) (H := hIntersection hyp B hB)
      hcop hnorm hh
  obtain ⟨hcH, hccomm⟩ := Subgroup.mem_inf.mp hcmem
  have hccb : Commute c b := Subgroup.mem_centralizer_singleton_iff.mp hccomm
  have hcHb : c ∈ hyp.H ⟨b, hbA⟩ := by
    have hcInsert : c ∈ hIntersection hyp (insert ⟨b, hbA⟩ B) (Finset.insert_nonempty _ B) := by
      rw [← hyp.centralizer_inf_hIntersection hB ⟨b, hbA⟩]
      exact Subgroup.mem_inf.mpr ⟨hccomm, hcH⟩
    exact hIntersection_le hyp (Finset.insert_nonempty _ B) (Finset.mem_insert_self _ B) hcInsert
  -- `g` is conjugate to `c·b = b·c`
  have hgconj : (x' * y⁻¹) * g * (x' * y⁻¹)⁻¹ = c * b := by
    rw [← hx'eq, hyeq]; group
  refine ⟨c, hcHb, ?_⟩
  rw [show b * c = c * b from (hccb.eq).symm]
  exact (isConj_iff.mpr ⟨x' * y⁻¹, hgconj⟩).symm

/-- **Peterfalvi (2.10.3), the support test for a single component `b`.**  If `𝒜(g, H(B)b) ≠ ∅`
(some `y⁻¹gy ∈ H(B)·b`) with `b ∈ N_L(B) ∩ A`, then `g ∈ (bH(b))^G ⊆ dadeSupport`.  Immediate from
the explicit conjugacy witness `exists_mem_H_isConj_of_mem_conjFiber_coset`. -/
theorem mem_dadeSupport_of_mem_conjFiber_coset (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    {b : G} (hbN : b ∈ nLStabilizerIn hyp B) (hbA : b ∈ A) {g y : G}
    (hy : y⁻¹ * g * y ∈ (↑(hIntersection hyp B hB) : Set G) * ({b} : Set G)) :
    g ∈ hyp.dadeSupport := by
  obtain ⟨c, hcHb, hgc⟩ := hyp.exists_mem_H_isConj_of_mem_conjFiber_coset hconj hB hbN hbA hy
  exact hyp.mem_dadeSupport_iff.mpr ⟨⟨b, hbA⟩, c, hcHb, hgc⟩

open Classical in
/-- **Peterfalvi (2.10.3), the value case `a^L`-specialized.**  Fix a Dade-support representative
`a` with `g ∈ (aH(a))^G` (witnessed by `h ∈ H(a)`, `IsConj (a·h) g`).  Then the `N_L(B)`-aggregated
value of `Ind_{M(B)}^G α_B` collapses to the textbook value formula

    `(Ind_{M(B)}^G α_B)(g) = (α(a)/|M(B)|) · ∑_{b ∈ N_L(B) ∩ a^L} |𝒜(g, H(B)·b)|`,

the sum running only over `b` that are `L`-conjugate to `a`.  Starting from
`induce_alphaB_apply_eq_sum_nLStabilizerIn_inA` (sum over `b ∈ N_L(B), b ∈ A`), the terms with
`b ∉ a^L` vanish: if `|𝒜(g, H(B)b)| ≠ 0` then `g ∈ (bH(b))^G` by
`mem_dadeSupport_of_mem_conjFiber_coset`, whence `a·h` and `b·h'` are `G`-conjugate, so by (2.4.b)
(`isConj_in_L_of_mul_H`) `b ∈ a^L` — a contradiction.  On the surviving `b ∈ a^L` the value
`α(b) = α(a)` (an `L`-class function), and `α(a)` factors out. -/
theorem induce_alphaB_apply_eq_alpha_mul_sum_conjL (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)]
    {a : {a : G // a ∈ A}} {h g : G} (hh : h ∈ hyp.H a) (hga : IsConj (a.1 * h) g) :
    ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hconj hB (α : ClassFunction L ℂ)) g
      = ⅟(Nat.card (mBSubgroup hyp B hB) : ℂ) *
          ((α : ClassFunction L ℂ) ⟨a.1, hyp.mem_L a.2⟩ *
            ∑ b ∈ (Finset.univ : Finset (nLStabilizerIn hyp B)).filter
                (fun b : (nLStabilizerIn hyp B) =>
                  ∃ l : L, (l : G) * a.1 * (l : G)⁻¹ = (b : G)),
              ((conjFiber g ((↑(hIntersection hyp B hB) : Set G)
                * ({(b : G)} : Set G))).card : ℂ)) := by
  classical
  rw [induce_alphaB_apply_eq_sum_nLStabilizerIn_inA hyp hconj hB α g]
  congr 1
  -- restrict `{b ∈ N_L(B), b ∈ A}` to `{b ∈ N_L(B), b ∈ a^L}`, factoring `α(a)`.
  rw [Finset.mul_sum]
  -- abbreviations for the two filtering predicates and the `N`-summand
  set N : (nLStabilizerIn hyp B) → ℂ := fun b =>
    ((conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(b : G)} : Set G))).card : ℂ) with hN
  set sP : Finset (nLStabilizerIn hyp B) :=
    (Finset.univ : Finset (nLStabilizerIn hyp B)).filter (fun b => ((b : G) ∈ A)) with hsP
  set sQ : Finset (nLStabilizerIn hyp B) :=
    (Finset.univ : Finset (nLStabilizerIn hyp B)).filter
      (fun b => ∃ l : L, (l : G) * a.1 * (l : G)⁻¹ = (b : G)) with hsQ
  -- `sQ ⊆ sP` (a^L ⊆ A) and on `sP \ sQ` the summand `N b` vanishes.
  have hsub : sQ ⊆ sP := by
    intro b hb
    rw [hsQ, Finset.mem_filter] at hb
    obtain ⟨l, hl⟩ := hb.2
    rw [hsP, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hl ▸ hyp.L_normalizes_A l a.2⟩
  -- `∑_{sP} α(b)·N b = ∑_{sQ} α(b)·N b`: terms outside `sQ` have `N b = 0`.
  have hPQ : ∑ b ∈ sP, (α : ClassFunction L ℂ) ⟨(b : G), nLStabilizerIn_le_L hyp B b.2⟩ * N b
      = ∑ b ∈ sQ, (α : ClassFunction L ℂ) ⟨(b : G), nLStabilizerIn_le_L hyp B b.2⟩ * N b := by
    refine (Finset.sum_subset hsub fun b hbP hbQ => ?_).symm
    rw [hsP, Finset.mem_filter] at hbP
    obtain ⟨_, hbA⟩ := hbP
    -- `b ∉ sQ` ⟹ `b ∉ a^L`; show `N b = 0`, i.e. `𝒜(g, H(B)b) = ∅`.
    have hbnotQ : ¬ ∃ l : L, (l : G) * a.1 * (l : G)⁻¹ = (b : G) := by
      intro hQ; exact hbQ (by rw [hsQ, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hQ⟩)
    have hfiber0 : N b = 0 := by
      show ((conjFiber g ((↑(hIntersection hyp B hB) : Set G)
        * ({(b : G)} : Set G))).card : ℂ) = 0
      norm_cast
      rw [Finset.card_eq_zero]
      by_contra hne
      rw [← Ne, ← Finset.nonempty_iff_ne_empty] at hne
      obtain ⟨y, hy⟩ := hne
      rw [mem_conjFiber] at hy
      obtain ⟨c, hcHb, hgc⟩ :=
        hyp.exists_mem_H_isConj_of_mem_conjFiber_coset hconj hB b.2 hbA hy
      have hconjab : IsConj (a.1 * h) ((b : G) * c) := hga.trans hgc.symm
      obtain ⟨l, hl⟩ := hyp.isConj_in_L_of_mul_H a.2 hbA hh hcHb hconjab
      exact hbnotQ ⟨l, hl⟩
    rw [hfiber0, mul_zero]
  rw [hPQ]
  -- on `sQ`, `α(b) = α(a)`.
  apply Finset.sum_congr rfl
  intro b hb
  rw [hsQ, Finset.mem_filter] at hb
  obtain ⟨l, hl⟩ := hb.2
  have hαeq : (α : ClassFunction L ℂ) ⟨(b : G), nLStabilizerIn_le_L hyp B b.2⟩
      = (α : ClassFunction L ℂ) ⟨a.1, hyp.mem_L a.2⟩ := by
    refine ClassFunction.of_isConj (α : ClassFunction L ℂ) (isConj_iff.mpr ⟨l⁻¹, ?_⟩)
    apply Subtype.ext
    show (l⁻¹ : L) * (b : G) * ((l⁻¹ : L) : G)⁻¹ = a.1
    rw [← hl]; push_cast; group
  simp only [hN]
  rw [hαeq]

/-- **Peterfalvi (2.10), conjugation invariance of the conjugating set.**  For any `c : G` and
subset `X ⊆ G`, right translation by `c` is a bijection `𝒜(g, X) ≃ 𝒜(g, c·X·c⁻¹)`; in particular
the cardinalities agree:

    `|𝒜(g, c·X·c⁻¹)| = |𝒜(g, X)|`.

Indeed `y⁻¹gy ∈ c·X·c⁻¹ ⟺ (yc⁻¹)⁻¹ g (yc⁻¹) ∈ X`, so `𝒜(g, c·X·c⁻¹) = 𝒜(g, X)·c`.  This is the
reindexing fact `|𝒜(g, H(B^x)b)| = |𝒜(g, H(B)a)|` (with `b = a^x`, `H(B^x) = x·H(B)·x⁻¹` by
(2.10.1)) used to collapse the `a^L`-sum in the proof of (2.10). -/
theorem card_conjFiber_conj_eq (g c : G) (X : Set G) :
    (conjFiber g ((fun z => c * z * c⁻¹) '' X)).card = (conjFiber g X).card := by
  classical
  apply Finset.card_bij' (fun y _ => y * c) (fun y _ => y * c⁻¹)
  · intro y hy
    rw [mem_conjFiber] at hy ⊢
    obtain ⟨z, hz, hzeq⟩ := hy
    simp only at hzeq
    -- `hzeq : c·z·c⁻¹ = y⁻¹gy` ⟹ `(yc)⁻¹ g (yc) = z ∈ X`
    have hval : (y * c)⁻¹ * g * (y * c) = z := by
      have : y⁻¹ * g * y = c * z * c⁻¹ := hzeq.symm
      rw [show (y * c)⁻¹ * g * (y * c) = c⁻¹ * (y⁻¹ * g * y) * c by group, this]; group
    rw [hval]; exact hz
  · intro y hy
    rw [mem_conjFiber] at hy ⊢
    -- `(yc⁻¹)⁻¹ g (yc⁻¹) = c·(y⁻¹gy)·c⁻¹ ∈ c·X·c⁻¹`
    refine ⟨y⁻¹ * g * y, hy, ?_⟩
    group
  · intro y _; group
  · intro y _; group

/-- **Peterfalvi (2.1), the conjugacy-image fiber count.**  Let `a` normalize a finite subgroup `K`
coprimely and `C = K ⊓ C_G(a)`.  For `w` in the coset `K·a` (`w·a⁻¹ ∈ K`), the fiber of the
parametrization `(c, x) ↦ x⁻¹(c·a)x` of `K·a` over `w` has exactly `|C|` elements:

    `|{(c, x) ∈ C × K | x⁻¹(c·a)x = w}| = |C|`.

This is the disjoint-union count `H(B)a = ⨆ (C·a)^x` (`coset_eq_cosetConjImage`) read fiberwise.
Given a witness `(c₀, x₀)` for `w`, the map `e ↦ (e c₀ e⁻¹, e x₀)` (`e ∈ C`) bijects `C` with the
fiber, with inverse `(c, x) ↦ x x₀⁻¹` landing in `C` by the rigidity
`mem_centralizer_of_coset_conj_eq`. -/
theorem card_cosetConjFiber_eq_card_centralizerInf {K : Subgroup G} {a : G}
    (hcop : Nat.Coprime (orderOf a) (Nat.card K)) {w : G}
    (hwImage : ∃ c ∈ K ⊓ Subgroup.centralizer ({a} : Set G), ∃ x ∈ K,
      x⁻¹ * (c * a) * x = w) :
    ((Finset.univ : Finset (↥(K ⊓ Subgroup.centralizer ({a} : Set G)) × ↥K)).filter
        (fun p => (p.2 : G)⁻¹ * ((p.1 : G) * a) * (p.2 : G) = w)).card
      = Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set G)) := by
  classical
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({a} : Set G) with hC
  obtain ⟨c₀, hc₀C, x₀, hx₀K, hcx₀⟩ := hwImage
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ (α := C)]
  -- membership of `e c₀ e⁻¹` in `C`, packaged for the forward map.
  have hfwd1 : ∀ e : C, (e : G) * (c₀ : G) * (e : G)⁻¹ ∈ C := by
    intro e
    obtain ⟨heK, hecomm⟩ := Subgroup.mem_inf.mp e.2
    obtain ⟨hc₀K, hc₀comm⟩ := Subgroup.mem_inf.mp hc₀C
    refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem heK hc₀K) (K.inv_mem heK),
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hge : Commute (e : G) a := Subgroup.mem_centralizer_singleton_iff.mp hecomm
    have hgc₀ : Commute (c₀ : G) a := Subgroup.mem_centralizer_singleton_iff.mp hc₀comm
    have hgeinv : (e : G)⁻¹ * a = a * (e : G)⁻¹ := hge.inv_left.eq
    calc (e : G) * (c₀ : G) * (e : G)⁻¹ * a
        = (e : G) * (c₀ : G) * (a * (e : G)⁻¹) := by rw [mul_assoc, hgeinv]
      _ = (e : G) * ((c₀ : G) * a) * (e : G)⁻¹ := by group
      _ = (e : G) * (a * (c₀ : G)) * (e : G)⁻¹ := by rw [hgc₀.eq]
      _ = (e : G) * a * (c₀ : G) * (e : G)⁻¹ := by group
      _ = a * ((e : G) * (c₀ : G) * (e : G)⁻¹) := by rw [hge.eq]; group
  -- `(c, x) ↦ x x₀⁻¹ ∈ C` for fiber elements, packaged for the inverse map.
  have hinv1 : ∀ p : ↥C × ↥K, p ∈ (Finset.univ : Finset (↥C × ↥K)).filter
        (fun p => (p.2 : G)⁻¹ * ((p.1 : G) * a) * (p.2 : G) = w) →
      (p.2 : G) * (x₀ : G)⁻¹ ∈ C := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hxx₀ := OddOrder.GroupTheory.mem_centralizer_of_coset_conj_eq (g := a) (H := K)
      hcop p.2.2 hx₀K p.1.2 hc₀C (by rw [hp.2, ← hcx₀])
    have := C.inv_mem hxx₀
    rwa [mul_inv_rev, inv_inv] at this
  refine Eq.symm ?_
  refine Finset.card_bij'
    (i := fun e _ => ((⟨(e : G) * (c₀ : G) * (e : G)⁻¹, hfwd1 e⟩ : ↥C),
      (⟨(e : G) * x₀, K.mul_mem ((Subgroup.mem_inf.mp e.2).1) hx₀K⟩ : ↥K)))
    (j := fun p hp => (⟨(p.2 : G) * (x₀ : G)⁻¹, hinv1 p hp⟩ : ↥C))
    ?_ ?_ ?_ ?_
  · -- `i e ∈ fiber`
    intro e _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨-, hecomm⟩ := Subgroup.mem_inf.mp e.2
    have hge : Commute (e : G) a := Subgroup.mem_centralizer_singleton_iff.mp hecomm
    have hge' : (e : G)⁻¹ * a = a * (e : G)⁻¹ := hge.inv_left.eq
    show ((e : G) * x₀)⁻¹ * (((e : G) * (c₀ : G) * (e : G)⁻¹) * a) * ((e : G) * x₀) = w
    rw [← hcx₀]
    calc ((e : G) * x₀)⁻¹ * (((e : G) * (c₀ : G) * (e : G)⁻¹) * a) * ((e : G) * x₀)
        = x₀⁻¹ * ((c₀ : G) * ((e : G)⁻¹ * a * (e : G))) * x₀ := by group
      _ = x₀⁻¹ * ((c₀ : G) * a) * x₀ := by rw [hge']; group
  · -- `j p ∈ univ`
    intro p _; exact Finset.mem_univ _
  · -- left inverse: `j (i e) = e`
    intro e _
    apply Subtype.ext
    show (e : G) * x₀ * (x₀ : G)⁻¹ = (e : G)
    group
  · -- right inverse: `i (j p) = p`
    rintro ⟨⟨c, hcC⟩, ⟨x, hxK⟩⟩ hp
    rw [Finset.mem_filter] at hp
    have hpeq : x⁻¹ * (c * a) * x = w := hp.2
    apply Prod.ext
    · -- first coordinate: `(x x₀⁻¹) c₀ (x x₀⁻¹)⁻¹ = c`
      apply Subtype.ext
      show (x * (x₀ : G)⁻¹) * (c₀ : G) * (x * (x₀ : G)⁻¹)⁻¹ = c
      have hxx₀ := OddOrder.GroupTheory.mem_centralizer_of_coset_conj_eq (g := a) (H := K)
        hcop hxK hx₀K hcC hc₀C (by rw [hpeq, ← hcx₀])
      obtain ⟨-, hcomm⟩ := Subgroup.mem_inf.mp hxx₀
      have hxx₀comm : (x₀ : G) * x⁻¹ * a = a * ((x₀ : G) * x⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.mp hcomm
      have heq : x⁻¹ * (c * a) * x = x₀⁻¹ * ((c₀ : G) * a) * x₀ := by rw [hpeq, hcx₀]
      have e2 : c * a = x * (x₀ : G)⁻¹ * ((c₀ : G) * a) * ((x₀ : G) * x⁻¹) := by
        calc c * a
            = x * (x⁻¹ * (c * a) * x) * x⁻¹ := by group
          _ = x * (x₀⁻¹ * ((c₀ : G) * a) * x₀) * x⁻¹ := by rw [heq]
          _ = x * (x₀ : G)⁻¹ * ((c₀ : G) * a) * ((x₀ : G) * x⁻¹) := by group
      have e3 : c * a = x * (x₀ : G)⁻¹ * (c₀ : G) * (x * (x₀ : G)⁻¹)⁻¹ * a := by
        calc c * a
            = x * (x₀ : G)⁻¹ * ((c₀ : G) * a) * ((x₀ : G) * x⁻¹) := e2
          _ = x * (x₀ : G)⁻¹ * (c₀ : G) * (a * ((x₀ : G) * x⁻¹)) := by group
          _ = x * (x₀ : G)⁻¹ * (c₀ : G) * (((x₀ : G) * x⁻¹) * a) := by rw [hxx₀comm]
          _ = x * (x₀ : G)⁻¹ * (c₀ : G) * (x * (x₀ : G)⁻¹)⁻¹ * a := by group
      exact mul_right_cancel e3.symm
    · -- second coordinate: `(x x₀⁻¹) x₀ = x`
      apply Subtype.ext
      show x * (x₀ : G)⁻¹ * (x₀ : G) = x
      group

/-- **Peterfalvi (2.1), the fiber factorization** (the long pole of (2.10) STEP 2).  Let `a`
normalize a finite subgroup `K` coprimely and `C = K ⊓ C_G(a)`.  Then for any `g`,

    `|𝒜(g, K·a)| · |C| = |𝒜(g, C·a)| · |K|`,

equivalently `|𝒜(g, K·a)| = |𝒜(g, C·a)| · [K : C]`.  This is Peterfalvi's "`H(B)a` is the disjoint
union of `[H(B):C_{H(B)}(a)]` conjugates of `C_{H(B)}(a)a`, so `|𝒜(g, H(B)a)| =
|𝒜(g, C_{H(B)}(a)a)|·[H(B):C_{H(B)}(a)]`".

Both sides are computed as `|S|`, where `S = {(y, c, x) ∈ G × C × K | y⁻¹gy = x⁻¹(c·a)x}`:
* projecting to `y` and using the conjugacy-image fiber count
  `card_cosetConjFiber_eq_card_centralizerInf` (each nonempty fiber has size `|C|`,
  via `coset_eq_cosetConjImage` for the image membership) gives `|S| = |𝒜(g, K·a)|·|C|`;
* the involution-free bijection `(y, c, x) ↦ (yx⁻¹, c, x)` onto
  `{(w, c, x) | w⁻¹gw = c·a}`, in which `x ∈ K` is now free, gives `|S| = |𝒜(g, C·a)|·|K|`. -/
theorem card_conjFiber_coset_mul_card_centralizerInf {K : Subgroup G} {a : G}
    (hnorm : ∀ x ∈ K, a * x * a⁻¹ ∈ K)
    (hcop : Nat.Coprime (orderOf a) (Nat.card K)) (g : G) :
    (conjFiber g ((↑K : Set G) * ({a} : Set G))).card
        * Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set G))
      = (conjFiber g ((↑(K ⊓ Subgroup.centralizer ({a} : Set G)) : Set G) * ({a} : Set G))).card
        * Nat.card ↥K := by
  classical
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({a} : Set G) with hC
  letI : Fintype ↥C := Fintype.ofFinite _
  letI : Fintype ↥K := Fintype.ofFinite _
  -- The bridge set `S`.
  set S : Finset (G × ↥C × ↥K) := (Finset.univ : Finset (G × ↥C × ↥K)).filter
    (fun p => p.1⁻¹ * g * p.1 = (p.2.2 : G)⁻¹ * ((p.2.1 : G) * a) * (p.2.2 : G)) with hS
  -- helper: `x⁻¹(c·a)x ∈ K·a` for `c ∈ C`, `x ∈ K`.
  have hmemKa : ∀ (c : G) (_ : c ∈ K) (x : G) (_ : x ∈ K),
      x⁻¹ * (c * a) * x ∈ (↑K : Set G) * ({a} : Set G) := by
    intro c hc x hx
    rw [Set.mem_mul]
    refine ⟨x⁻¹ * c * (a * x * a⁻¹), K.mul_mem (K.mul_mem (K.inv_mem hx) hc) (hnorm x hx),
      a, Set.mem_singleton _, by group⟩
  -- ### `|S| = |𝒜(g, K·a)| · |C|`
  have hSleft : S.card = (conjFiber g ((↑K : Set G) * ({a} : Set G))).card * Nat.card ↥C := by
    rw [hS, Nat.card_eq_fintype_card, ← Finset.card_univ (α := ↥C), ← smul_eq_mul,
      ← Finset.sum_const]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : G × ↥C × ↥K => p.1)
      (t := conjFiber g ((↑K : Set G) * ({a} : Set G))) ?_]
    · -- each fiber over `y ∈ 𝒜(g, K·a)` has card `|univ C|`
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [mem_conjFiber] at hy
      -- `y⁻¹gy = x⁻¹(c·a)x` (image membership) via (2.1)
      have himg : ∃ c ∈ C, ∃ x ∈ K, x⁻¹ * (c * a) * x = y⁻¹ * g * y := by
        obtain ⟨k, hk, a', ha', hkeq⟩ := hy
        rw [Set.mem_singleton_iff] at ha'
        rw [ha'] at hkeq
        -- `hkeq : k * a = y⁻¹ g y`
        obtain ⟨c, hcC, x, hxK, hxeq⟩ :=
          OddOrder.GroupTheory.exists_mem_centralizer_conj (g := a) (H := K) hcop hnorm hk
        -- `hxeq : x (k a) x⁻¹ = c a`, so `y⁻¹gy = k a = x⁻¹ (c a) x`
        refine ⟨c, hcC, x, hxK, ?_⟩
        rw [← hkeq]
        have hxeq' : x * (k * a) * x⁻¹ = c * a := hxeq
        rw [← hxeq']; group
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
        ← card_cosetConjFiber_eq_card_centralizerInf hcop himg]
      -- the `S`-fiber over `y` (drop the fixed first coordinate) bijects with the conjugacy fiber.
      refine Finset.card_bij' (i := fun p _ => p.2) (j := fun q _ => (y, q))
        ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        obtain ⟨hpeq, hpy⟩ := hp
        rw [← hpy]; exact hpeq.symm
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hq.symm, trivial⟩
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        obtain ⟨_, hpy⟩ := hp
        exact Prod.ext hpy.symm rfl
      · intro q _; rfl
    · intro p hpS
      simp only [Finset.mem_coe, mem_conjFiber]
      have hp : p.1⁻¹ * g * p.1 = (p.2.2 : G)⁻¹ * ((p.2.1 : G) * a) * (p.2.2 : G) :=
        (Finset.mem_filter.mp hpS).2
      rw [hp]
      exact hmemKa (p.2.1 : G) (Subgroup.mem_inf.mp p.2.1.2).1 (p.2.2 : G) p.2.2.2
  -- helper: membership `w⁻¹gw ∈ C·a ⟹ (w⁻¹gw)·a⁻¹ ∈ C`.
  have hcwC : ∀ w : G, w⁻¹ * g * w ∈ (↑C : Set G) * ({a} : Set G) →
      w⁻¹ * g * w * a⁻¹ ∈ C := by
    intro w hw
    obtain ⟨c, hc, a', ha', hceq⟩ := hw
    rw [Set.mem_singleton_iff] at ha'
    rw [ha'] at hceq
    rw [← hceq, mul_assoc, mul_inv_cancel, mul_one]; exact hc
  -- ### `|S| = |𝒜(g, C·a)| · |K|` via `(y,c,x) ↦ (yx⁻¹, c, x)` and freeing `x`.
  have hSright : S.card
      = (conjFiber g ((↑C : Set G) * ({a} : Set G))).card * Nat.card ↥K := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ (α := ↥K), ← Finset.card_product]
    refine Finset.card_bij'
      (i := fun p _ => (p.1 * (p.2.2 : G)⁻¹, p.2.2))
      (j := fun q hq => (q.1 * (q.2 : G),
        ⟨q.1⁻¹ * g * q.1 * a⁻¹,
          hcwC q.1 (mem_conjFiber.mp (Finset.mem_product.mp hq).1)⟩, q.2))
      ?_ ?_ ?_ ?_
    · -- `i p ∈ conjFiber(C·a) ×ˢ univ`
      intro p hpS
      rw [Finset.mem_product]
      refine ⟨?_, Finset.mem_univ _⟩
      simp only [mem_conjFiber]
      have hp : p.1⁻¹ * g * p.1 = (p.2.2 : G)⁻¹ * ((p.2.1 : G) * a) * (p.2.2 : G) :=
        (Finset.mem_filter.mp hpS).2
      -- `(p.1 p.2.2⁻¹)⁻¹ g (p.1 p.2.2⁻¹) = p.2.2 (p.1⁻¹ g p.1) p.2.2⁻¹ = p.2.1 · a`
      have hval : (p.1 * (p.2.2 : G)⁻¹)⁻¹ * g * (p.1 * (p.2.2 : G)⁻¹)
          = (p.2.1 : G) * a := by
        rw [show (p.1 * (p.2.2 : G)⁻¹)⁻¹ * g * (p.1 * (p.2.2 : G)⁻¹)
            = (p.2.2 : G) * (p.1⁻¹ * g * p.1) * (p.2.2 : G)⁻¹ by group, hp]; group
      rw [hval]
      exact ⟨(p.2.1 : G), p.2.1.2, a, Set.mem_singleton _, rfl⟩
    · -- `j q ∈ S`
      intro q hq
      rw [Finset.mem_product] at hq
      have hwCa : q.1⁻¹ * g * q.1 ∈ (↑C : Set G) * ({a} : Set G) := by
        have := (mem_conjFiber (g := g)).mp (Finset.mem_coe.mpr hq.1); simpa using this
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      -- S-condition: `(q.1 q.2)⁻¹ g (q.1 q.2) = q.2⁻¹ ((q.1⁻¹gq.1·a⁻¹)·a) q.2`
      show (q.1 * (q.2 : G))⁻¹ * g * (q.1 * (q.2 : G))
        = (q.2 : G)⁻¹ * ((q.1⁻¹ * g * q.1 * a⁻¹) * a) * (q.2 : G)
      rw [show (q.1⁻¹ * g * q.1 * a⁻¹) * a = q.1⁻¹ * g * q.1 by group]
      group
    · -- left inverse `j (i p) = p`
      intro p hpS
      have hp : p.1⁻¹ * g * p.1 = (p.2.2 : G)⁻¹ * ((p.2.1 : G) * a) * (p.2.2 : G) :=
        (Finset.mem_filter.mp hpS).2
      -- `(p.1 p.2.2⁻¹)·p.2.2 = p.1`, and the recovered `c = p.2.1`.
      apply Prod.ext
      · show p.1 * (p.2.2 : G)⁻¹ * (p.2.2 : G) = p.1; group
      apply Prod.ext
      · -- recovered centralizer component equals `p.2.1`
        apply Subtype.ext
        show (p.1 * (p.2.2 : G)⁻¹)⁻¹ * g * (p.1 * (p.2.2 : G)⁻¹) * a⁻¹ = (p.2.1 : G)
        rw [show (p.1 * (p.2.2 : G)⁻¹)⁻¹ * g * (p.1 * (p.2.2 : G)⁻¹)
            = (p.2.2 : G) * (p.1⁻¹ * g * p.1) * (p.2.2 : G)⁻¹ by group, hp]
        group
      · rfl
    · -- right inverse `i (j q) = q`
      intro q hq
      apply Prod.ext
      · show q.1 * (q.2 : G) * (q.2 : G)⁻¹ = q.1; group
      · rfl
  rw [hSleft] at hSright
  exact hSright

/-- **Peterfalvi (2.10), the Möbius cancellation identity** (the toggle-`a` pairing of (2.10)).
For `a ∈ A` normalizing `H(B)` (i.e. `a ∈ N_L(B)`) and nonempty `B ⊆ A`,

    `|𝒜(g, H(B)·a)| · |H(B ∪ {a})| = |𝒜(g, H(B ∪ {a})·a)| · |H(B)|`.

This is the (2.10) STEP 2 factorization `card_conjFiber_coset_mul_card_centralizerInf` specialized to
`K = H(B)`, with `C = H(B) ⊓ C_G(a) = C_{H(B)}(a) = H(B ∪ {a})` by (2.10.2)
(`centralizer_inf_hIntersection`).  In the (2.10) alternating sum it shows the summands
`(-1)^{|B|}/|H(B)| · |𝒜(g, H(B)·a)|` for `B` and `B ∪ {a}` are equal (so cancel by the opposite
signs `(-1)^{|B|}` vs `(-1)^{|B|+1}`), leaving only the survivor `B = {a}`. -/
theorem card_conjFiber_hIntersection_mul_eq (hyp : Hypothesis G A L)
    (hconj : hyp.HConjInvariant)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) {a : {a : G // a ∈ A}}
    (haN : (a : G) ∈ nLStabilizerIn hyp B) (g : G) :
    (conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(a : G)} : Set G))).card
        * Nat.card (hIntersection hyp (insert a B) (Finset.insert_nonempty a B))
      = (conjFiber g ((↑(hIntersection hyp (insert a B) (Finset.insert_nonempty a B)) : Set G)
            * ({(a : G)} : Set G))).card
        * Nat.card (hIntersection hyp B hB) := by
  classical
  -- `a` normalizes `H(B)` coprimely; `H(B) ⊓ C_G(a) = H(insert a B)` by (2.10.2).
  have hnorm : ∀ x ∈ hIntersection hyp B hB, (a : G) * x * (a : G)⁻¹ ∈ hIntersection hyp B hB := by
    intro x hx
    have hmem := hyp.nLStabilizerIn_le_normalizer hconj hB haN
    rw [Subgroup.mem_normalizer_iff] at hmem
    exact (hmem x).mp hx
  have hcop := hyp.coprime_orderOf_card_hIntersection hB a.2
  -- `H(B) ⊓ C_G(a) = H(insert a B)`
  have hCeq : hIntersection hyp B hB ⊓ Subgroup.centralizer ({(a : G)} : Set G)
      = hIntersection hyp (insert a B) (Finset.insert_nonempty a B) := by
    rw [inf_comm]; exact hyp.centralizer_inf_hIntersection hB a
  -- apply STEP 2 and rewrite `C` via (2.10.2)
  have hfact := card_conjFiber_coset_mul_card_centralizerInf
    (K := hIntersection hyp B hB) (a := (a : G)) hnorm hcop g
  rw [hCeq] at hfact
  exact hfact

/-! #### STEP 3b: the toggle-`a` Möbius cancellation

The proof of (2.10) collapses the alternating sum over `𝒫(a)` (nonempty `B ⊆ A` with
`a ∈ N_L(B)`) to its `B = {a}` survivor.  We index `𝒫(a)` as a `Finset`, define the summand
`mobiusSummand` `= (-1)^{|B|}/|H(B)| · |𝒜(g, H(B)a)|`, and cancel pairs `B ↔ B △ {a}` by the
multiplicative identity `card_conjFiber_hIntersection_mul_eq`. -/

variable (hyp : Hypothesis G A L)

/-- `𝒫(a)` as a `Finset`: the nonempty subsets `B ⊆ A` with `a ∈ N_L(B)`. -/
noncomputable def mobiusIndex (a : {a : G // a ∈ A}) :
    Finset (Finset {a : G // a ∈ A}) := by
  classical
  letI : Fintype {a : G // a ∈ A} := Fintype.ofFinite _
  exact (Finset.univ.powerset).filter
    (fun B => B.Nonempty ∧ (a : G) ∈ nLStabilizerIn hyp B)

theorem mem_mobiusIndex {a : {a : G // a ∈ A}} {B : Finset {a : G // a ∈ A}} :
    B ∈ hyp.mobiusIndex a ↔ B.Nonempty ∧ (a : G) ∈ nLStabilizerIn hyp B := by
  classical
  letI : Fintype {a : G // a ∈ A} := Fintype.ofFinite _
  simp only [mobiusIndex, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]

/-- The Möbius summand `(-1)^{|B|}/|H(B)| · |𝒜(g, H(B)·a)|` (as a complex number). -/
noncomputable def mobiusSummand (a : {a : G // a ∈ A}) (g : G)
    (B : Finset {a : G // a ∈ A}) : ℂ := by
  classical
  exact if hB : B.Nonempty then
      ((-1 : ℂ) ^ B.card / (Nat.card (hIntersection hyp B hB) : ℂ)) *
        ((conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(a : G)} : Set G))).card : ℂ)
    else 0

theorem mobiusSummand_of_nonempty (a : {a : G // a ∈ A}) (g : G)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    hyp.mobiusSummand a g B
      = ((-1 : ℂ) ^ B.card / (Nat.card (hIntersection hyp B hB) : ℂ)) *
        ((conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(a : G)} : Set G))).card : ℂ) := by
  rw [mobiusSummand, dif_pos hB]

/-- Membership of `a` in `N_L(B)` is insensitive to inserting `a` into `B` (for `a ∉ B`): since
conjugation by `a` fixes `a` (`a·a·a⁻¹ = a`), `a` permutes `B` iff it permutes `insert a B`. -/
theorem mem_nLStabilizerIn_insert_iff (a : {a : G // a ∈ A})
    {B : Finset {a : G // a ∈ A}} (haB : a ∉ B) :
    (a : G) ∈ nLStabilizerIn hyp (insert a B) ↔ (a : G) ∈ nLStabilizerIn hyp B := by
  classical
  have ha : (a : G) ∈ L := hyp.mem_L a.2
  have hfix : ∀ hx : (a : G) ∈ L, hyp.conjA ⟨(a : G), hx⟩ a = a := by
    intro hx
    apply Subtype.ext
    show (a : G) * (a : G) * (a : G)⁻¹ = (a : G)
    group
  have hfixinv : ∀ hx : (a : G) ∈ L, hyp.conjA ⟨(a : G), hx⟩⁻¹ a = a := by
    intro hx
    apply Subtype.ext
    show (a : G)⁻¹ * (a : G) * ((a : G)⁻¹)⁻¹ = (a : G)
    group
  rw [mem_nLStabilizerIn, mem_nLStabilizerIn]
  constructor
  · rintro ⟨hx, hstab⟩
    refine ⟨ha, ?_⟩
    intro c hc
    have hmem := hstab c (Finset.mem_insert_of_mem hc)
    rw [Finset.mem_insert] at hmem
    rcases hmem with hca | hca
    · -- `conjA a c = a` forces `c = a`, contradicting `a ∉ B` (as `c ∈ B`)
      exfalso
      have hceq : c = a := by
        have := congrArg (hyp.conjA ⟨(a : G), hx⟩⁻¹) hca
        rwa [conjA_inv_conjA, hfixinv hx] at this
      exact haB (hceq ▸ hc)
    · exact hca
  · rintro ⟨hx, hstab⟩
    refine ⟨ha, ?_⟩
    intro c hc
    rw [Finset.mem_insert] at hc
    rcases hc with rfl | hc
    · rw [hfix hx]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hstab c hc)

/-- **Peterfalvi (2.10), the toggle-`a` pairwise cancellation.**  For `a ∉ B`, nonempty `B ⊆ A`
with `a ∈ N_L(B)`, the Möbius summands for `B` and `insert a B` are negatives:

    `mobiusSummand a g B + mobiusSummand a g (insert a B) = 0`.

This is the multiplicative identity `card_conjFiber_hIntersection_mul_eq`
(`|𝒜(g,H(B)a)|·|H(B∪{a})| = |𝒜(g,H(B∪{a})a)|·|H(B)|`) cleared of denominators, together with the
sign flip `(-1)^{|B|+1} = -(-1)^{|B|}` from `|insert a B| = |B| + 1`.  It is the cancellation law
fed to `Finset.sum_involution`. -/
theorem mobiusSummand_add_insert_eq_zero (hconj : hyp.HConjInvariant) (g : G)
    {a : {a : G // a ∈ A}} {B : Finset {a : G // a ∈ A}} (haB : a ∉ B) (hB : B.Nonempty)
    (haN : (a : G) ∈ nLStabilizerIn hyp B) :
    hyp.mobiusSummand a g B + hyp.mobiusSummand a g (insert a B) = 0 := by
  classical
  have hiB : (insert a B).Nonempty := Finset.insert_nonempty a B
  -- the multiplicative cancellation identity
  have hmul := hyp.card_conjFiber_hIntersection_mul_eq hconj hB haN g
  -- nonzero cardinalities
  have hHBne : (Nat.card (hIntersection hyp B hB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hHiBne : (Nat.card (hIntersection hyp (insert a B) hiB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [hyp.mobiusSummand_of_nonempty a g hB, hyp.mobiusSummand_of_nonempty a g hiB]
  -- card of `insert a B` and sign flip
  rw [Finset.card_insert_of_notMem haB, pow_succ]
  -- abbreviations
  set p : ℂ := (-1 : ℂ) ^ B.card
  set hb : ℂ := (Nat.card (hIntersection hyp B hB) : ℂ)
  set hib : ℂ := (Nat.card (hIntersection hyp (insert a B) hiB) : ℂ)
  set fb : ℂ := ((conjFiber g ((↑(hIntersection hyp B hB) : Set G)
    * ({(a : G)} : Set G))).card : ℂ)
  set fib : ℂ := ((conjFiber g ((↑(hIntersection hyp (insert a B) hiB) : Set G)
    * ({(a : G)} : Set G))).card : ℂ)
  -- cast the multiplicative identity to ℂ: `fb * hib = fib * hb` (`hiB` and `insert_nonempty`
  -- give defeq `H(insert a B)`)
  have hmulC : fb * hib = fib * hb := by
    show ((conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(a : G)} : Set G))).card : ℂ)
        * (Nat.card (hIntersection hyp (insert a B) (Finset.insert_nonempty a B)) : ℂ)
      = ((conjFiber g ((↑(hIntersection hyp (insert a B) (Finset.insert_nonempty a B)) : Set G)
            * ({(a : G)} : Set G))).card : ℂ)
        * (Nat.card (hIntersection hyp B hB) : ℂ)
    exact_mod_cast hmul
  -- assemble: `p/hb · fb + (p·(-1))/hib · fib = (p/(hb·hib)) · (fb·hib - fib·hb) = 0`
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  rw [div_add_div (p * fb) (p * -1 * fib) hHBne hHiBne, div_eq_zero_iff]
  left
  -- numerator: `(p·fb)·hib + hb·(p·(-1)·fib) = p·(fb·hib - fib·hb) = 0`
  linear_combination p * hmulC

/-- The singleton `{a}` lies in `𝒫(a)`. -/
theorem singleton_mem_mobiusIndex (a : {a : G // a ∈ A}) :
    ({a} : Finset {a : G // a ∈ A}) ∈ hyp.mobiusIndex a := by
  classical
  rw [hyp.mem_mobiusIndex]
  refine ⟨Finset.singleton_nonempty a, ?_⟩
  rw [mem_nLStabilizerIn]
  refine ⟨hyp.mem_L a.2, ?_⟩
  intro c hc
  rw [Finset.mem_singleton] at hc
  rw [hc, Finset.mem_singleton]
  apply Subtype.ext
  show (a : G) * (a : G) * (a : G)⁻¹ = (a : G)
  group

/-- The toggle-`a` map `B ↦ B △ {a}`: removes `a` from `B` if present, else inserts it. -/
noncomputable def toggleA (a : {a : G // a ∈ A}) (B : Finset {a : G // a ∈ A}) :
    Finset {a : G // a ∈ A} := by
  classical
  exact if a ∈ B then B.erase a else insert a B

theorem toggleA_of_mem {a : {a : G // a ∈ A}} {B : Finset {a : G // a ∈ A}}
    (haB : a ∈ B) : toggleA a B = B.erase a := by
  classical rw [toggleA]; simp only [if_pos haB]

theorem toggleA_of_not_mem {a : {a : G // a ∈ A}} {B : Finset {a : G // a ∈ A}}
    (haB : a ∉ B) : toggleA a B = insert a B := by
  classical rw [toggleA]; simp only [if_neg haB]

/-- **Peterfalvi (2.10), the toggle-`a` involution collapses `𝒫(a)` to its `B = {a}` survivor.**

    `∑_{B ∈ 𝒫(a)} mobiusSummand a g B = mobiusSummand a g {a}`.

The toggle `B ↦ B △ {a}` (`toggleA`) is a fixed-point-free involution on `𝒫(a) \ {{a}}` under which
the summands cancel pairwise (`mobiusSummand_add_insert_eq_zero`), so `∑_{𝒫(a) \ {{a}}} = 0` by
`Finset.sum_involution`; adding back the isolated survivor `{a}` gives the claim. -/
theorem sum_mobiusSummand_eq_singleton (hconj : hyp.HConjInvariant) (g : G)
    (a : {a : G // a ∈ A}) :
    ∑ B ∈ hyp.mobiusIndex a, hyp.mobiusSummand a g B = hyp.mobiusSummand a g {a} := by
  classical
  -- a helper: `toggleA a B ∈ 𝒫(a) \ {{a}}` and the pairwise data, packaged once.
  have key : ∀ B ∈ (hyp.mobiusIndex a).erase ({a} : Finset {a : G // a ∈ A}),
      hyp.mobiusSummand a g B + hyp.mobiusSummand a g (toggleA a B) = 0
        ∧ toggleA a B ∈ (hyp.mobiusIndex a).erase ({a} : Finset {a : G // a ∈ A})
        ∧ toggleA a (toggleA a B) = B := by
    intro B hB
    rw [Finset.mem_erase, hyp.mem_mobiusIndex] at hB
    obtain ⟨hBne, hBnonempty, hBnorm⟩ := hB
    by_cases haB : a ∈ B
    · -- `toggleA a B = B.erase a`, write `B = insert a (B.erase a)`
      set B' := B.erase a with hB'
      have haB' : a ∉ B' := Finset.notMem_erase a B
      have hBins : B = insert a B' := by rw [hB', Finset.insert_erase haB]
      have hB'ne : B'.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty, hB']
        intro hempty
        rcases (Finset.erase_eq_empty_iff B a).mp hempty with h | h
        · rw [h] at haB; exact absurd haB (Finset.notMem_empty a)
        · exact hBne h
      have hB'norm : (a : G) ∈ nLStabilizerIn hyp B' := by
        rw [← hyp.mem_nLStabilizerIn_insert_iff a haB', ← hBins]; exact hBnorm
      refine ⟨?_, ?_, ?_⟩
      · rw [toggleA_of_mem haB]
        have := hyp.mobiusSummand_add_insert_eq_zero hconj g haB' hB'ne hB'norm
        rw [← hBins] at this
        rw [add_comm]; exact this
      · rw [toggleA_of_mem haB, Finset.mem_erase, hyp.mem_mobiusIndex]
        refine ⟨fun hcontra => haB' ?_, hB'ne, hB'norm⟩
        show a ∈ B.erase a
        rw [hcontra]; exact Finset.mem_singleton_self a
      · rw [toggleA_of_mem haB]
        rw [toggleA_of_not_mem haB', Finset.insert_erase haB]
    · -- `toggleA a B = insert a B`
      have hains : (a : G) ∈ nLStabilizerIn hyp (insert a B) :=
        (hyp.mem_nLStabilizerIn_insert_iff a haB).mpr hBnorm
      refine ⟨?_, ?_, ?_⟩
      · rw [toggleA_of_not_mem haB]
        exact hyp.mobiusSummand_add_insert_eq_zero hconj g haB hBnonempty hBnorm
      · rw [toggleA_of_not_mem haB, Finset.mem_erase, hyp.mem_mobiusIndex]
        refine ⟨?_, Finset.insert_nonempty a B, hains⟩
        intro hcontra
        obtain ⟨c, hc⟩ := hBnonempty
        have hcins : c ∈ insert a B := Finset.mem_insert_of_mem hc
        rw [hcontra, Finset.mem_singleton] at hcins
        exact haB (hcins ▸ hc)
      · rw [toggleA_of_not_mem haB, toggleA_of_mem (Finset.mem_insert_self a B),
          Finset.erase_insert haB]
  -- isolate the survivor `{a}`: `∑_{𝒫(a)} = mobiusSummand {a} + ∑_{𝒫(a) \ {{a}}}`
  rw [← Finset.sum_erase_add _ _ (hyp.singleton_mem_mobiusIndex a)]
  have hzero : ∑ B ∈ (hyp.mobiusIndex a).erase ({a} : Finset {a : G // a ∈ A}),
      hyp.mobiusSummand a g B = 0 := by
    refine Finset.sum_involution (fun B _ => toggleA a B)
      (fun B hB => (key B hB).1)
      (fun B hB _ => ?_)
      (fun B hB => (key B hB).2.1)
      (fun B hB => (key B hB).2.2)
    -- `hg₃`: `toggleA a B ≠ B` (toggle changes membership of `a`)
    show toggleA a B ≠ B
    by_cases haB : a ∈ B
    · rw [toggleA_of_mem haB]
      intro hcontra
      rw [← hcontra] at haB
      exact (Finset.notMem_erase a B) haB
    · rw [toggleA_of_not_mem haB]
      intro hcontra
      have : a ∈ B := by rw [← hcontra]; exact Finset.mem_insert_self a B
      exact haB this
  rw [hzero, zero_add]

/-- `H({a}) = H(a)`: the intersection over the singleton `{a}` is `H(a)`. -/
theorem hIntersection_singleton (a : {a : G // a ∈ A}) :
    hIntersection hyp {a} (Finset.singleton_nonempty a) = hyp.H a := by
  apply le_antisymm
  · exact hyp.hIntersection_le _ (Finset.mem_singleton_self a)
  · intro x hx
    rw [mem_hIntersection]
    intro b hb
    rw [Finset.mem_singleton] at hb
    exact hb ▸ hx

/-- **Peterfalvi (2.10), evaluation of the surviving `B = {a}` term.**  For `g ∈ (aH(a))^G`
(witnessed by `h ∈ H(a)`, `IsConj (a·h) g`),

    `mobiusSummand a g {a} = -(|C_L(a)| : ℂ)`.

Indeed `|{a}| = 1`, `H({a}) = H(a)`, and the surviving conjugating set has
`|𝒜(g, H(a)·a)| = |C_G(a)|` (`card_conjFiber_coset_eq_card_centralizer`), while
`|C_G(a)| = |H(a)|·|C_L(a)|` (`card_centralizer_eq`); the `|H(a)|` cancels the denominator,
leaving `(-1)·|C_L(a)|`. -/
theorem mobiusSummand_singleton_eq (g : G) {a : {a : G // a ∈ A}} {h : G}
    (hh : h ∈ hyp.H a) (hga : IsConj (a.1 * h) g) :
    hyp.mobiusSummand a g {a} = -(Nat.card (centralizerIn L a.1) : ℂ) := by
  classical
  rw [hyp.mobiusSummand_of_nonempty a g (Finset.singleton_nonempty a)]
  -- `H({a}) = H(a)`
  have hHeq : hIntersection hyp {a} (Finset.singleton_nonempty a) = hyp.H a :=
    hyp.hIntersection_singleton a
  rw [hHeq, Finset.card_singleton, pow_one]
  -- `|𝒜(g, H(a)·a)| = |C_G(a)|`
  have hcomm : ∀ x ∈ hyp.H a, Commute a.1 x := fun x hx => hyp.commute_of_mem_H a hx
  have hnorm : ∀ c ∈ Subgroup.centralizer ({a.1} : Set G), ∀ x ∈ hyp.H a, c * x * c⁻¹ ∈ hyp.H a :=
    fun c hc x hx => hyp.H_normalized a c hc x hx
  have hcop : Nat.Coprime (orderOf a.1) (Nat.card (hyp.H a)) := by
    have := hyp.coprime_orderOf_card_hIntersection (Finset.singleton_nonempty a) a.2
    rwa [hHeq] at this
  have hAcard : (conjFiber g ((↑(hyp.H a) : Set G) * ({a.1} : Set G))).card
      = Nat.card (Subgroup.centralizer ({a.1} : Set G)) :=
    card_conjFiber_coset_eq_card_centralizer hcomm hnorm hcop hh hga
  rw [hAcard]
  -- `|C_G(a)| = |H(a)|·|C_L(a)|`
  rw [hyp.card_centralizer_eq a]
  -- `(-1)/|H(a)| · (|H(a)|·|C_L(a)|) = -|C_L(a)|`
  have hHne : (Nat.card (hyp.H a) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  push_cast
  field_simp

/-! #### STEP 3a: orbit-averaging the transversal sum to the powerset

The (2.10) right-hand side is a sum over the `L`-conjugacy transversal `ℬ` of an orbit-constant
summand.  We convert it to a sum over the full powerset weighted by `1/|orbit B|`. -/

/-- The conjugation orbit of `B` is contained in `A`-subsets of the same cardinality, so it is
finite; `Nat.card (orbit B) > 0`. -/
theorem card_orbit_pos (B : Finset {a : G // a ∈ A}) :
    letI := hyp.conjFinsetAction
    0 < Nat.card (MulAction.orbit L B) := by
  letI := hyp.conjFinsetAction
  letI : Finite (MulAction.orbit L B) := Set.finite_coe_iff.mpr (Set.toFinite _)
  letI : Nonempty (MulAction.orbit L B) := ⟨⟨B, MulAction.mem_orbit_self B⟩⟩
  exact Nat.card_pos

/-- **Peterfalvi (2.10), orbit-averaging.**  For any `ℂ`-valued `h` constant on `L`-conjugacy orbits
of subsets (`h (B^l) = h B`), the transversal sum equals the powerset sum weighted by inverse orbit
size:

    `∑_{C ∈ ℬ} h(rep C) = ∑_{B ⊆ A} h(B) / |orbit B|`.

Each orbit `O` contributes `∑_{B ∈ O} h(B)/|orbit B| = |O| · h(rep)/|O| = h(rep)` (the numerator is
orbit-constant and `|orbit B| = |O|` throughout `O`); partitioning the powerset sum into orbit fibers
(`Finset.sum_fiberwise_of_maps_to` along `Quotient.mk''`) collapses it to the transversal sum.  This
realizes the `1/|L:N_L(B)|` weight of (2.10) (`card_orbit_mul_card_setLStabilizer`). -/
theorem sum_transversalRep_eq_sum_div_orbit
    (h : Finset {a : G // a ∈ A} → ℂ)
    (hinv : ∀ (l : L) (B : Finset {a : G // a ∈ A}), h (hyp.conjFinset l B) = h B) :
    letI := hyp.conjFinsetAction
    letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
    letI : Fintype (Finset {a : G // a ∈ A}) := Fintype.ofFinite _
    ∑ C : hyp.conjClassQuotient, h (hyp.transversalRep C)
      = ∑ B : Finset {a : G // a ∈ A},
          h B / (Nat.card (MulAction.orbit L B) : ℂ) := by
  classical
  letI := hyp.conjFinsetAction
  letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
  letI : Fintype (Finset {a : G // a ∈ A}) := Fintype.ofFinite _
  -- `h` and `Nat.card (orbit ·)` are constant along orbits.
  have horbit_const : ∀ B : Finset {a : G // a ∈ A}, ∀ B' ∈ MulAction.orbit L B,
      h B' = h B := by
    rintro B B' ⟨l, rfl⟩
    exact hinv l B
  have hcard_const : ∀ B : Finset {a : G // a ∈ A}, ∀ B' ∈ MulAction.orbit L B,
      MulAction.orbit L B' = MulAction.orbit L B := by
    rintro B B' hB'
    exact (MulAction.orbit_eq_iff.mpr hB')
  -- partition the powerset sum into orbit fibers along `Quotient.mk''`.
  rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun B => (Quotient.mk'' B : hyp.conjClassQuotient))
      (s := Finset.univ) (t := Finset.univ)
      (fun B _ => Finset.mem_univ _)
      (f := fun B => h B / (Nat.card (MulAction.orbit L B) : ℂ))]
  refine Finset.sum_congr (by congr 1; exact Subsingleton.elim _ _) fun C _ => ?_
  -- evaluate the fiber over `C`: it is the orbit of `out C = transversalRep C`.
  set B₀ := hyp.transversalRep C with hB₀
  -- the fiber `{B | ⟦B⟧ = C}` as a Finset; on it the summand is the constant `h B₀ / |orbit B₀|`.
  have hfiber_eq : ((Finset.univ : Finset (Finset {a : G // a ∈ A})).filter
        (fun B => (Quotient.mk'' B : hyp.conjClassQuotient) = C))
      = (MulAction.orbit L B₀).toFinset := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
    rw [hB₀, transversalRep]
    constructor
    · intro hB
      rw [MulAction.mem_orbit_iff]
      have : (Quotient.mk'' B : hyp.conjClassQuotient)
          = Quotient.mk'' (Quotient.out (s := MulAction.orbitRel L (Finset {a : G // a ∈ A})) C) := by
        rw [hB, Quotient.out_eq']
      exact Quotient.exact' this
    · intro hB
      have : (Quotient.mk'' B : hyp.conjClassQuotient)
          = Quotient.mk'' (Quotient.out (s := MulAction.orbitRel L (Finset {a : G // a ∈ A})) C) :=
        Quotient.sound' (by rwa [MulAction.mem_orbit_iff] at hB)
      rw [this, Quotient.out_eq']
  rw [hfiber_eq]
  -- on the orbit, the summand is constant `= h B₀ / |orbit B₀|`; there are `|orbit B₀|` terms.
  have hconst : ∀ B ∈ (MulAction.orbit L B₀).toFinset,
      h B / (Nat.card (MulAction.orbit L B) : ℂ) = h B₀ / (Nat.card (MulAction.orbit L B₀) : ℂ) := by
    intro B hB
    rw [Set.mem_toFinset] at hB
    rw [horbit_const B₀ B hB, hcard_const B₀ B hB]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  -- `|orbit B₀| · (h B₀ / |orbit B₀|) = h B₀`.
  have hcardpos : 0 < Nat.card (MulAction.orbit L B₀) := hyp.card_orbit_pos B₀
  have hcard_eq : ((MulAction.orbit L B₀).toFinset.card : ℂ)
      = (Nat.card (MulAction.orbit L B₀) : ℂ) := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
  rw [hcard_eq]
  rw [mul_div_assoc']
  rw [mul_div_cancel_left₀]
  exact Nat.cast_ne_zero.mpr hcardpos.ne'

/-- `|H(B^l)| = |H(B)|`: conjugation by `l` is a cardinality-preserving bijection of subgroups. -/
theorem card_hIntersection_conjFinset (hconj : hyp.HConjInvariant) (l : L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    Nat.card (hIntersection hyp (hyp.conjFinset l B) (hyp.conjFinset_nonempty (l := l) hB))
      = Nat.card (hIntersection hyp B hB) := by
  rw [hyp.hIntersection_conjFinset hconj l hB]
  refine Nat.card_congr ?_
  have hsmul : ∀ z : G, ((MulAut.conj (l : G))⁻¹ • z) = (l : G)⁻¹ * z * (l : G) := by
    intro z
    rw [show ((MulAut.conj (l : G))⁻¹ • z) = (MulAut.conj (l : G))⁻¹ z from rfl,
      MulAut.conj_inv_apply]
  refine
    { toFun := fun x => ⟨(l : G)⁻¹ * (x : G) * (l : G), ?_⟩
      invFun := fun y => ⟨(l : G) * (y : G) * (l : G)⁻¹, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun y => ?_ }
  · -- `x ∈ conj•H(B) ⟹ l⁻¹·x·l ∈ H(B)`
    have hx := x.2
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hsmul] at hx
    exact hx
  · -- `y ∈ H(B) ⟹ l·y·l⁻¹ ∈ conj•H(B)`
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hsmul]
    rw [show (l : G)⁻¹ * ((l : G) * (y : G) * (l : G)⁻¹) * (l : G) = (y : G) from by group]
    exact y.2
  · apply Subtype.ext; show (l : G) * ((l : G)⁻¹ * (x : G) * (l : G)) * (l : G)⁻¹ = (x : G); group
  · apply Subtype.ext; show (l : G)⁻¹ * ((l : G) * (y : G) * (l : G)⁻¹) * (l : G) = (y : G); group

/-- The conjugation orbit element `a^l` lies in `N_L(B^l)` iff `a` lies in `N_L(B)`. -/
theorem mem_nLStabilizerIn_conjA_conjFinset (l : L)
    {a : {a : G // a ∈ A}} {B : Finset {a : G // a ∈ A}} :
    (hyp.conjA l a : G) ∈ nLStabilizerIn hyp (hyp.conjFinset l B)
      ↔ (a : G) ∈ nLStabilizerIn hyp B := by
  rw [hyp.nLStabilizerIn_conjFinset l, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rw [show ((MulAut.conj (l : G))⁻¹ • (hyp.conjA l a : G)) = (l : G)⁻¹ * (hyp.conjA l a : G)
      * (l : G) from by
    rw [show ((MulAut.conj (l : G))⁻¹ • (hyp.conjA l a : G))
        = (MulAut.conj (l : G))⁻¹ (hyp.conjA l a : G) from rfl, MulAut.conj_inv_apply]]
  rw [show (l : G)⁻¹ * (hyp.conjA l a : G) * (l : G) = (a : G) from by
    simp only [conjA_coe]; group]

/-- Conjugation `B ↦ B^l` sends `𝒫(a)` bijectively to `𝒫(a^l)`. -/
theorem mem_mobiusIndex_conjFinset (l : L)
    {a : {a : G // a ∈ A}} {B : Finset {a : G // a ∈ A}} :
    hyp.conjFinset l B ∈ hyp.mobiusIndex (hyp.conjA l a) ↔ B ∈ hyp.mobiusIndex a := by
  classical
  rw [hyp.mem_mobiusIndex, hyp.mem_mobiusIndex, conjFinset,
    Finset.image_nonempty, ← conjFinset, hyp.mem_nLStabilizerIn_conjA_conjFinset l]

/-- **Peterfalvi (2.10), conjugation-invariance of the `mobiusSummand`.**  For `l ∈ L`,

    `mobiusSummand (a^l) g (B^l) = mobiusSummand a g B`.

`|B^l| = |B|`, `H(B^l) = l·H(B)·l⁻¹` has the same cardinality, and the conjugating set
`|𝒜(g, H(B^l)·a^l)| = |𝒜(g, l·(H(B)·a)·l⁻¹)| = |𝒜(g, H(B)·a)|` by `card_conjFiber_conj_eq`. -/
theorem mobiusSummand_conjFinset (hconj : hyp.HConjInvariant) (l : L) (g : G)
    (a : {a : G // a ∈ A}) (B : Finset {a : G // a ∈ A}) :
    hyp.mobiusSummand (hyp.conjA l a) g (hyp.conjFinset l B)
      = hyp.mobiusSummand a g B := by
  classical
  by_cases hB : B.Nonempty
  · have hBl : (hyp.conjFinset l B).Nonempty := hyp.conjFinset_nonempty (l := l) hB
    rw [hyp.mobiusSummand_of_nonempty _ g hBl, hyp.mobiusSummand_of_nonempty a g hB]
    rw [hyp.conjFinset_card, hyp.card_hIntersection_conjFinset hconj l hB]
    -- only the conjugating-set cardinality remains
    congr 2
    -- `|𝒜(g, H(B^l)·a^l)| = |𝒜(g, H(B)·a)|`
    have hset : (↑(hIntersection hyp (hyp.conjFinset l B) hBl) : Set G)
          * ({(hyp.conjA l a : G)} : Set G)
        = (fun z => (l : G) * z * (l : G)⁻¹) ''
            ((↑(hIntersection hyp B hB) : Set G) * ({(a : G)} : Set G)) := by
      rw [hyp.hIntersection_conjFinset hconj l hB]
      have hsmul : ∀ z : G, ((MulAut.conj (l : G))⁻¹ • z) = (l : G)⁻¹ * z * (l : G) := by
        intro z
        rw [show ((MulAut.conj (l : G))⁻¹ • z) = (MulAut.conj (l : G))⁻¹ z from rfl,
          MulAut.conj_inv_apply]
      ext y
      simp only [Set.mem_mul, Set.mem_image, Set.mem_singleton_iff, conjA_coe,
        SetLike.mem_coe]
      constructor
      · rintro ⟨p, hp, q, rfl, rfl⟩
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hsmul] at hp
        refine ⟨(l : G)⁻¹ * p * (l : G) * (a : G),
          ⟨(l : G)⁻¹ * p * (l : G), hp, a, rfl, rfl⟩, by group⟩
      · rintro ⟨z, ⟨p, hp, q, rfl, rfl⟩, rfl⟩
        refine ⟨(l : G) * p * (l : G)⁻¹, ?_, (l : G) * (a : G) * (l : G)⁻¹, rfl, by group⟩
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hsmul,
          show (l : G)⁻¹ * ((l : G) * p * (l : G)⁻¹) * (l : G) = p from by group]
        exact hp
    rw [hset, card_conjFiber_conj_eq]
  · have hBe : ¬ (hyp.conjFinset l B).Nonempty := by
      rw [conjFinset, Finset.image_nonempty]; exact hB
    simp only [mobiusSummand, dif_neg hBe, dif_neg hB]

/-- **Peterfalvi (2.10), the `𝒫(b)`-sum is `L`-conjugation invariant.**  For `l ∈ L`,

    `∑_{B ∈ 𝒫(a^l)} mobiusSummand (a^l) g B = ∑_{B₀ ∈ 𝒫(a)} mobiusSummand a g B₀`.

The bijection `B₀ ↦ B₀^l` carries `𝒫(a)` to `𝒫(a^l)` (`mem_mobiusIndex_conjFinset`) and preserves
the summand (`mobiusSummand_conjFinset`).  This is the `b = a^x` reindex of (2.10) (lines making the
inner `𝒫(b)`-sum independent of `b ∈ a^L`). -/
theorem sum_mobiusSummand_conjFinset (hconj : hyp.HConjInvariant) (l : L) (g : G)
    (a : {a : G // a ∈ A}) :
    ∑ B ∈ hyp.mobiusIndex (hyp.conjA l a), hyp.mobiusSummand (hyp.conjA l a) g B
      = ∑ B₀ ∈ hyp.mobiusIndex a, hyp.mobiusSummand a g B₀ := by
  classical
  refine Finset.sum_bij' (fun B _ => hyp.conjFinset l⁻¹ B) (fun B₀ _ => hyp.conjFinset l B₀)
    ?_ ?_ ?_ ?_ ?_
  · -- `i : 𝒫(a^l) → 𝒫(a)`
    intro B hB
    have hmem := (hyp.mem_mobiusIndex_conjFinset l⁻¹ (a := hyp.conjA l a) (B := B)).mpr
    rw [conjA_inv_conjA] at hmem
    exact hmem hB
  · -- `j : 𝒫(a) → 𝒫(a^l)`
    intro B₀ hB₀
    exact (hyp.mem_mobiusIndex_conjFinset l (a := a) (B := B₀)).mpr hB₀
  · intro B _
    show hyp.conjFinset l (hyp.conjFinset l⁻¹ B) = B
    rw [← hyp.conjFinset_mul, mul_inv_cancel, hyp.conjFinset_one]
  · intro B₀ _
    show hyp.conjFinset l⁻¹ (hyp.conjFinset l B₀) = B₀
    rw [← hyp.conjFinset_mul, inv_mul_cancel, hyp.conjFinset_one]
  · -- summand agrees: `mobiusSummand (a^l) g B = mobiusSummand a g (B^{l⁻¹})`
    intro B hB
    show hyp.mobiusSummand (hyp.conjA l a) g B
      = hyp.mobiusSummand a g (hyp.conjFinset l⁻¹ B)
    have := hyp.mobiusSummand_conjFinset hconj l⁻¹ g (hyp.conjA l a) B
    rw [conjA_inv_conjA] at this
    exact this.symm

/-- `|N_L(B)| = |setLStabilizer B|`: `N_L(B) = setLStabilizer.map L.subtype` along the injection
`L ↪ G`, so the two cardinalities agree. -/
theorem card_nLStabilizerIn_eq (B : Finset {a : G // a ∈ A}) :
    Nat.card (nLStabilizerIn hyp B) = Nat.card (setLStabilizer hyp B) := by
  rw [nLStabilizerIn]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective).symm.toEquiv

/-- The packaged summand `induceAlphaBTerm` evaluated at `g` equals the bare induced value,
independent of the carried invertibility instance (`Invertible.subsingleton`). -/
theorem induceAlphaBTerm_apply (hconj : hyp.HConjInvariant) (α : ClassFunction L ℂ)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    [inst : Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)] (g : G) :
    hyp.induceAlphaBTerm hconj α ⟨B, hB⟩ g
      = ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hconj hB α) g := by
  have h : inst = invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne') :=
    Subsingleton.elim _ _
  rw [induceAlphaBTerm, h]

/-- **Peterfalvi (2.10), per-`B` weight simplification.**  For nonempty `B` and `g ∈ (aH(a))^G`, the
orbit-averaged inclusion–exclusion summand collapses, using `|orbit B|·|N_L(B)| = |L|`
(`card_orbit_mul_card_setLStabilizer`) and `|M(B)| = |H(B)|·|N_L(B)|` (`card_mBSubgroup`):

    `(-1)^{|B|}/|orbit B| · (Ind_{M(B)} α_B)(g)
      = (α(a)/|L|) · ∑_{b ∈ N_L(B) ∩ a^L} (-1)^{|B|}/|H(B)| · |𝒜(g, H(B)·b)|`.

The factor `1/(|orbit B|·|M(B)|) = 1/(|orbit B|·|H(B)|·|N_L(B)|) = 1/(|L|·|H(B)|)`. -/
theorem mobiusSummand_orbit_weighted (hconj : hyp.HConjInvariant)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)]
    {a : {a : G // a ∈ A}} {h g : G} (hh : h ∈ hyp.H a) (hga : IsConj (a.1 * h) g) :
    letI := hyp.conjFinsetAction
    ((-1 : ℂ) ^ B.card / (Nat.card (MulAction.orbit L B) : ℂ))
        * hyp.induceAlphaBTerm hconj (α : ClassFunction L ℂ) ⟨B, hB⟩ g
      = ((α : ClassFunction L ℂ) ⟨a.1, hyp.mem_L a.2⟩ / (Nat.card L : ℂ))
          * ∑ b ∈ (Finset.univ : Finset (nLStabilizerIn hyp B)).filter
              (fun b : (nLStabilizerIn hyp B) =>
                ∃ l : L, (l : G) * a.1 * (l : G)⁻¹ = (b : G)),
            ((-1 : ℂ) ^ B.card / (Nat.card (hIntersection hyp B hB) : ℂ)) *
              ((conjFiber g ((↑(hIntersection hyp B hB) : Set G)
                * ({(b : G)} : Set G))).card : ℂ) := by
  classical
  letI := hyp.conjFinsetAction
  rw [hyp.induceAlphaBTerm_apply hconj _ hB g,
    hyp.induce_alphaB_apply_eq_alpha_mul_sum_conjL hconj hB α hh hga]
  -- abbreviations
  set p : ℂ := (-1 : ℂ) ^ B.card with hp
  set αa : ℂ := (α : ClassFunction L ℂ) ⟨a.1, hyp.mem_L a.2⟩ with hαa
  set Hc : ℂ := (Nat.card (hIntersection hyp B hB) : ℂ) with hHc
  set Nc : ℂ := (Nat.card (nLStabilizerIn hyp B) : ℂ) with hNc
  set Oc : ℂ := (Nat.card (MulAction.orbit L B) : ℂ) with hOc
  -- `|M(B)| = |H(B)|·|N_L(B)|` and `|orbit B|·|N_L(B)| = |L|`.
  have hM : (Nat.card (mBSubgroup hyp B hB) : ℂ) = Hc * Nc := by
    rw [hHc, hNc]; exact_mod_cast hyp.card_mBSubgroup hconj hB
  have hON : Oc * Nc = (Nat.card L : ℂ) := by
    rw [hOc, hNc, hyp.card_nLStabilizerIn_eq B]
    exact_mod_cast hyp.card_orbit_mul_card_setLStabilizer B
  have hHne : Hc ≠ 0 := by rw [hHc]; exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hNne : Nc ≠ 0 := by rw [hNc]; exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hOne : Oc ≠ 0 := by rw [hOc]; exact Nat.cast_ne_zero.mpr (hyp.card_orbit_pos B).ne'
  -- name the inner sum `S = ∑_b |𝒜(g, H(B)b)|`.
  set S : ℂ := ∑ b ∈ (Finset.univ : Finset (nLStabilizerIn hyp B)).filter
      (fun b : (nLStabilizerIn hyp B) => ∃ l : L, (l : G) * a.1 * (l : G)⁻¹ = (b : G)),
      ((conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(b : G)} : Set G))).card : ℂ)
      with hS
  -- expand `⅟|M(B)|` and pull the per-term scalar `p/Hc` out of the RHS sum.
  rw [show (⅟(Nat.card (mBSubgroup hyp B hB) : ℂ)) = (Hc * Nc)⁻¹ from by
    rw [invOf_eq_inv, hM]]
  rw [show (∑ b ∈ (Finset.univ : Finset (nLStabilizerIn hyp B)).filter
        (fun b : (nLStabilizerIn hyp B) => ∃ l : L, (l : G) * a.1 * (l : G)⁻¹ = (b : G)),
        (p / Hc) * ((conjFiber g ((↑(hIntersection hyp B hB) : Set G)
          * ({(b : G)} : Set G))).card : ℂ)) = (p / Hc) * S from by
    rw [hS, Finset.mul_sum]]
  -- now both sides are scalar multiples of `S`; equate scalars using `Oc·Nc = |L|`.
  rw [← hON]
  field_simp

/-! #### Final assembly: the (2.10) pointwise identity and `FullDadeIsometryData`

The remaining work assembles the per-`B` weight identity `mobiusSummand_orbit_weighted` into the
(2.10) pointwise identity `α^τ(g) = -∑_{C ∈ ℬ} (-1)^{|rep C|} Ind_{M(rep C)} α_{rep C}(g)`, by
(a) orbit-averaging the transversal sum to the powerset, (b) recognizing the inner RHS term as
`mobiusSummand b g B`, (c) swapping the resulting double sum to sum over `b ∈ a^L` first, (d)
collapsing each inner `𝒫(b)`-sum to its survivor `mobiusSummand b g {b} = -|C_L(b)|`, and (e)
totalling `∑_{b ∈ a^L} |C_L(b)| = |L|` (`sum_card_centralizerIn_eq`). -/

/-- The orbit-averaging summand `(-1)^{|B|} · Ind_{M(B)} α_B(g)` (and `0` if `B` is empty),
packaged so `sum_transversalRep_eq_sum_div_orbit` applies. -/
noncomputable def mobiusTermCF (hconj : hyp.HConjInvariant) (α : ClassFunction L ℂ)
    (g : G) (B : Finset {a : G // a ∈ A}) : ℂ := by
  classical
  exact if hB : B.Nonempty then
      (-1 : ℂ) ^ B.card * hyp.induceAlphaBTerm hconj α ⟨B, hB⟩ g
    else 0

theorem mobiusTermCF_of_nonempty (hconj : hyp.HConjInvariant) (α : ClassFunction L ℂ)
    (g : G) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    hyp.mobiusTermCF hconj α g B
      = (-1 : ℂ) ^ B.card * hyp.induceAlphaBTerm hconj α ⟨B, hB⟩ g := by
  rw [mobiusTermCF, dif_pos hB]

theorem mobiusTermCF_of_not_nonempty (hconj : hyp.HConjInvariant) (α : ClassFunction L ℂ)
    (g : G) {B : Finset {a : G // a ∈ A}} (hB : ¬ B.Nonempty) :
    hyp.mobiusTermCF hconj α g B = 0 := by
  rw [mobiusTermCF, dif_neg hB]

/-- The orbit-averaging summand is `L`-conjugacy invariant: `mobiusTermCF (B^l) = mobiusTermCF B`.
Uses `conjFinset_card` (the sign `(-1)^{|B|}` is `L`-invariant) and `induceAlphaBTerm_conjFinset`
(the packaged induced summand is invariant). -/
theorem mobiusTermCF_conjFinset (hconj : hyp.HConjInvariant) (α : ClassFunction L ℂ)
    (g : G) (l : L) (B : Finset {a : G // a ∈ A}) :
    hyp.mobiusTermCF hconj α g (hyp.conjFinset l B) = hyp.mobiusTermCF hconj α g B := by
  classical
  by_cases hB : B.Nonempty
  · have hBl : (hyp.conjFinset l B).Nonempty := hyp.conjFinset_nonempty (l := l) hB
    rw [hyp.mobiusTermCF_of_nonempty hconj α g hBl, hyp.mobiusTermCF_of_nonempty hconj α g hB,
      hyp.conjFinset_card l B, hyp.induceAlphaBTerm_conjFinset hconj α l hB]
  · have hBe : ¬ (hyp.conjFinset l B).Nonempty := by
      rw [conjFinset, Finset.image_nonempty]; exact hB
    rw [mobiusTermCF, mobiusTermCF, dif_neg hBe, dif_neg hB]

/-- The `L`-orbit of the support representative `a`, as a `Finset {a : G // a ∈ A}`: the elements
`b' ∈ A` with `b' = l·a·l⁻¹` for some `l ∈ L`.  This is the fixed (`B`-independent) index over which
the inner `b`-sum of (2.10) ranges; it coincides with the support filter `Sg` of
`sum_card_centralizerIn_eq` when `g ∈ (aH(a))^G` (`mem_aOrbitFinset_iff_mem_supportFilter`). -/
noncomputable def aOrbitFinset (a : {a : G // a ∈ A}) : Finset {a : G // a ∈ A} := by
  classical
  letI : Fintype {a : G // a ∈ A} := Fintype.ofFinite _
  exact Finset.univ.filter (fun b => ∃ l : L, hyp.conjA l a = b)

theorem mem_aOrbitFinset {a b : {a : G // a ∈ A}} :
    b ∈ hyp.aOrbitFinset a ↔ ∃ l : L, hyp.conjA l a = b := by
  classical
  letI : Fintype {a : G // a ∈ A} := Fintype.ofFinite _
  simp only [aOrbitFinset, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Peterfalvi (2.10), per-`B` weight identity, inner sum over the fixed index `a^L`.**  For
`g ∈ (aH(a))^G`,

    `mobiusTermCF B / |orbit B| =
       (α(a)/|L|) · ∑_{b' ∈ a^L} (if b' ∈ N_L(B) then mobiusSummand b' g B else 0)`.

Recasting `mobiusSummand_orbit_weighted` so the inner sum ranges over the **`B`-independent** Finset
`aOrbitFinset a` (with an `if (b':G) ∈ N_L(B)` guard) instead of the `B`-dependent subtype
`N_L(B)`; this fixed index is what makes the subsequent `Finset.sum_comm` double-sum swap go
through.  The reindexing bijection sends `b : N_L(B)` with `b ∈ a^L` to `⟨b.val, _⟩ : {a // a ∈ A}`
(in `a^L ⊆ A`), and the term `(-1)^{|B|}/|H(B)| · |𝒜(g, H(B)·b)|` is `mobiusSummand b' g B`. -/
theorem mobiusTermCF_div_orbit_eq (hconj : hyp.HConjInvariant)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    {a : {a : G // a ∈ A}} {h g : G} (hh : h ∈ hyp.H a) (hga : IsConj (a.1 * h) g) :
    letI := hyp.conjFinsetAction
    hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g B / (Nat.card (MulAction.orbit L B) : ℂ)
      = ((α : ClassFunction L ℂ) ⟨a.1, hyp.mem_L a.2⟩ / (Nat.card L : ℂ))
          * ∑ b' ∈ hyp.aOrbitFinset a,
            (if (b' : G) ∈ nLStabilizerIn hyp B then hyp.mobiusSummand b' g B else 0) := by
  classical
  letI := hyp.conjFinsetAction
  letI : Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- start from the orbit-weight identity, which sums over `b : N_L(B)` with `b ∈ a^L`.
  rw [hyp.mobiusTermCF_of_nonempty hconj _ g hB, mul_div_right_comm,
    hyp.mobiusSummand_orbit_weighted hconj α hB hh hga]
  congr 1
  -- reindex the `N_L(B)`-subtype sum to the fixed `aOrbitFinset` sum.
  rw [← Finset.sum_filter]
  refine Finset.sum_bij'
      (i := fun b hb => (⟨(b : G), by
        rw [Finset.mem_filter] at hb
        obtain ⟨l, hl⟩ := hb.2
        exact hl ▸ hyp.L_normalizes_A l a.2⟩ : {a : G // a ∈ A}))
      (j := fun b' hb' => (⟨(b' : G), by
        rw [Finset.mem_filter] at hb'
        exact hb'.2⟩ : nLStabilizerIn hyp B))
      ?_ ?_ ?_ ?_ ?_
  · -- `i b ∈ aOrbitFinset a` with `(i b : G) ∈ N_L(B)`
    intro b hb
    rw [Finset.mem_filter] at hb ⊢
    obtain ⟨l, hl⟩ := hb.2
    refine ⟨hyp.mem_aOrbitFinset.mpr ⟨l, ?_⟩, b.2⟩
    apply Subtype.ext; rw [conjA_coe]; exact hl
  · -- `j b' ∈ (univ.filter (a^L))`
    intro b' hb'
    rw [Finset.mem_filter] at hb' ⊢
    obtain ⟨l, hl⟩ := (hyp.mem_aOrbitFinset).mp hb'.1
    exact ⟨Finset.mem_univ _, l, by rw [← hyp.conjA_coe l a, hl]⟩
  · intro b _; rfl
  · intro b' _; rfl
  · -- summands agree
    intro b _
    rw [hyp.mobiusSummand_of_nonempty _ g hB]

/-- For `g ∈ (aH(a))^G` and `b' = a^l ∈ a^L`, also `g ∈ (b'H(b'))^G`: there is `x ∈ H(b')` with
`IsConj (b'·x) g`.  Transporting the witness `(a, h)` by `l`: `x = l·h·l⁻¹ ∈ H(a^l) = H(b')` by
(2.4.a), and `b'·x = l·(a·h)·l⁻¹` is `G`-conjugate to `a·h`, hence to `g`. -/
theorem exists_mem_H_isConj_of_mem_aOrbitFinset (hconj : hyp.HConjInvariant)
    {a b' : {a : G // a ∈ A}} {h g : G} (hh : h ∈ hyp.H a) (hga : IsConj (a.1 * h) g)
    (hb' : b' ∈ hyp.aOrbitFinset a) :
    ∃ x ∈ hyp.H b', IsConj (b'.1 * x) g := by
  obtain ⟨l, hl⟩ := hyp.mem_aOrbitFinset.mp hb'
  refine ⟨(l : G) * h * (l : G)⁻¹, ?_, ?_⟩
  · have hmem : (l : G) * h * (l : G)⁻¹ ∈ hyp.H (hyp.conjA l a) := by
      rw [hyp.mem_H_conjA_iff hconj a l]
      rw [show (l : G)⁻¹ * ((l : G) * h * (l : G)⁻¹) * (l : G) = h from by group]
      exact hh
    rwa [hl] at hmem
  · have hconjeq : b'.1 * ((l : G) * h * (l : G)⁻¹) = (l : G) * (a.1 * h) * (l : G)⁻¹ := by
      rw [← hl, conjA_coe]; group
    rw [hconjeq]
    exact (isConj_iff.mpr ⟨(l : G), rfl⟩).symm.trans hga

/-- `mobiusSummand` vanishes on the empty subset (no `a`). -/
theorem mobiusSummand_empty (a : {a : G // a ∈ A}) (g : G) :
    hyp.mobiusSummand a g (∅ : Finset {a : G // a ∈ A}) = 0 := by
  rw [mobiusSummand, dif_neg (by simp)]

/-- `mobiusTermCF` vanishes on the empty subset. -/
theorem mobiusTermCF_empty (hconj : hyp.HConjInvariant) (α : ClassFunction L ℂ) (g : G) :
    hyp.mobiusTermCF hconj α g (∅ : Finset {a : G // a ∈ A}) = 0 := by
  rw [mobiusTermCF, dif_neg (by simp)]

/-- **Peterfalvi (2.10), the support-side total.**  For `g ∈ (aH(a))^G` (witnessed by `h ∈ H(a)`,
`IsConj (a·h) g`), the transversal sum of orbit-averaging summands evaluates to `-α(a)`:

    `∑_{C ∈ ℬ} mobiusTermCF (rep C) = -α(a)`.

The proof: (1) orbit-average to the powerset (`sum_transversalRep_eq_sum_div_orbit`); (2) recast
each term via `mobiusTermCF_div_orbit_eq` to `(α(a)/|L|) · ∑_{b' ∈ a^L} [b' ∈ N_L(B)] mobiusSummand
b' g B` (handling the empty `B` separately, both sides zero); (3) swap the double sum by
`Finset.sum_comm`; (4) the inner `B`-sum over `𝒫(b')` collapses to its survivor `mobiusSummand b' g
{b'} = -|C_L(b')|` (`sum_mobiusSummand_eq_singleton` + `mobiusSummand_singleton_eq`, using
`g ∈ (b'H(b'))^G` for `b' ∈ a^L`); (5) `∑_{b' ∈ a^L} |C_L(b')| = |L|`
(`sum_card_centralizerIn_eq`), giving `(α(a)/|L|) · (-|L|) = -α(a)`. -/
theorem sum_mobiusTermCF_transversalRep_eq_neg (hconj : hyp.HConjInvariant)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    {a : {a : G // a ∈ A}} {h g : G} (hh : h ∈ hyp.H a) (hga : IsConj (a.1 * h) g) :
    letI := hyp.conjFinsetAction
    letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
    ∑ C : hyp.conjClassQuotient, hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g
        (hyp.transversalRep C)
      = -((α : ClassFunction L ℂ) ⟨a.1, hyp.mem_L a.2⟩) := by
  classical
  letI := hyp.conjFinsetAction
  letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
  letI : Fintype {a : G // a ∈ A} := Fintype.ofFinite _
  letI : Fintype (Finset {a : G // a ∈ A}) := Fintype.ofFinite _
  set αa : ℂ := (α : ClassFunction L ℂ) ⟨a.1, hyp.mem_L a.2⟩ with hαa
  -- (1) orbit-average the transversal sum to the powerset.
  rw [hyp.sum_transversalRep_eq_sum_div_orbit
    (h := fun B => hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g B)
    (fun l B => hyp.mobiusTermCF_conjFinset hconj _ g l B)]
  -- (2) recast each term; factor out `αa/|L|` over the `B`-sum.
  have hterm : ∀ B : Finset {a : G // a ∈ A},
      hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g B / (Nat.card (MulAction.orbit L B) : ℂ)
        = (αa / (Nat.card L : ℂ))
          * ∑ b' ∈ hyp.aOrbitFinset a,
            (if (b' : G) ∈ nLStabilizerIn hyp B then hyp.mobiusSummand b' g B else 0) := by
    intro B
    by_cases hB : B.Nonempty
    · exact hyp.mobiusTermCF_div_orbit_eq hconj α hB hh hga
    · -- empty `B`: both sides vanish.
      rw [Finset.not_nonempty_iff_eq_empty] at hB
      subst hB
      rw [hyp.mobiusTermCF_empty hconj, zero_div]
      rw [show (∑ b' ∈ hyp.aOrbitFinset a,
          (if (b' : G) ∈ nLStabilizerIn hyp (∅ : Finset {a : G // a ∈ A})
            then hyp.mobiusSummand b' g ∅ else 0)) = 0 from ?_, mul_zero]
      refine Finset.sum_eq_zero fun b' _ => ?_
      rw [hyp.mobiusSummand_empty, ite_self]
  rw [Finset.sum_congr rfl (fun B _ => hterm B), ← Finset.mul_sum]
  -- (3) swap the double sum: `∑_B ∑_{b'} = ∑_{b'} ∑_B`.
  rw [Finset.sum_comm]
  -- (4) collapse the inner `B`-sum over `𝒫(b')` to its survivor `-|C_L(b')|`.
  have hinner : ∀ b' ∈ hyp.aOrbitFinset a,
      (∑ B : Finset {a : G // a ∈ A},
        (if (b' : G) ∈ nLStabilizerIn hyp B then hyp.mobiusSummand b' g B else 0))
        = -((Nat.card (centralizerIn L b'.1)) : ℂ) := by
    intro b' hb'
    -- the `b'`-survivor needs `g ∈ (b'H(b'))^G`, i.e. `∃ x ∈ H(b'), IsConj (b'·x) g`.
    obtain ⟨x', hx', hgx'⟩ :=
      hyp.exists_mem_H_isConj_of_mem_aOrbitFinset hconj hh hga hb'
    -- restrict the full powerset `B`-sum to `𝒫(b')` (the `if` is `0` off it); the only difference
    -- is the empty set (in the filter via `b' ∈ N_L(∅)` but not in `mobiusIndex`), where the
    -- summand vanishes.  Then apply the survivor collapse.
    rw [← Finset.sum_filter]
    rw [show (∑ B ∈ Finset.univ.filter
          (fun B : Finset {a : G // a ∈ A} => (b' : G) ∈ nLStabilizerIn hyp B),
          hyp.mobiusSummand b' g B)
        = ∑ B ∈ hyp.mobiusIndex b', hyp.mobiusSummand b' g B from ?_]
    · rw [hyp.sum_mobiusSummand_eq_singleton hconj g b',
        hyp.mobiusSummand_singleton_eq g hx' hgx']
    · -- `∑_{mobiusIndex} = ∑_{filter}` since they differ only by `∅` (where the summand is `0`).
      refine (Finset.sum_subset ?_ ?_).symm
      · -- `mobiusIndex b' ⊆ filter`
        intro B hB
        rw [hyp.mem_mobiusIndex] at hB
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hB.2⟩
      · -- off `mobiusIndex` (i.e. `B = ∅`), the summand vanishes.
        intro B hBfilter hBnot
        rw [Finset.mem_filter] at hBfilter
        rw [hyp.mem_mobiusIndex] at hBnot
        have hBempty : ¬ B.Nonempty := fun hne => hBnot ⟨hne, hBfilter.2⟩
        rw [Finset.not_nonempty_iff_eq_empty] at hBempty
        rw [hBempty, hyp.mobiusSummand_empty]
  -- (5) combine: `∑_{b' ∈ a^L} (-|C_L(b')|) = -|L|`, giving `(αa/|L|)·(-|L|) = -αa`.
  -- evaluate the inner-collapsed sum `∑_{b' ∈ a^L} (-|C_L(b')|) = -|L|`.
  have hsum_eval :
      (∑ b' ∈ hyp.aOrbitFinset a,
        (∑ B : Finset {a : G // a ∈ A},
          (if (b' : G) ∈ nLStabilizerIn hyp B then hyp.mobiusSummand b' g B else 0)))
        = -((Nat.card L : ℂ)) := by
    rw [Finset.sum_congr rfl hinner]
    -- rewrite the `aOrbitFinset` index to the support filter `Sg` of `sum_card_centralizerIn_eq`.
    have hSg : hyp.aOrbitFinset a
        = Finset.univ.filter
          (fun b : {a : G // a ∈ A} => ∃ x ∈ hyp.H b, IsConj (b.1 * x) g) := by
      ext b'
      rw [Finset.mem_filter]
      constructor
      · intro hb'
        exact ⟨Finset.mem_univ _,
          hyp.exists_mem_H_isConj_of_mem_aOrbitFinset hconj hh hga hb'⟩
      · rintro ⟨-, x, hx, hbx⟩
        rw [hyp.mem_aOrbitFinset]
        obtain ⟨l, hl⟩ := hyp.isConj_in_L_of_mul_H a.2 b'.2 hh hx (hga.trans hbx.symm)
        exact ⟨l, Subtype.ext (by rw [conjA_coe]; exact hl)⟩
    rw [hSg, Finset.sum_neg_distrib, ← Nat.cast_sum,
      hyp.sum_card_centralizerIn_eq hconj (hyp.mem_dadeSupport_iff.mpr ⟨a, h, hh, hga⟩)]
  -- `(αa/|L|)·(-|L|) = -αa`.
  have hLne : (Nat.card L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [hsum_eval]
  field_simp

end MobiusAssembly

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

/-- **Peterfalvi (2.5), uniqueness.**  The defining equations of the Dade map pin it
down completely: any two candidate maps satisfying `IsDadeMap hyp` agree.  On
`dadeSupport` both values are `α(a)` for a common witness `a` (`map_eq_of_isConj_hCoset`),
and off `dadeSupport` both vanish. -/
theorem unique {hyp : Hypothesis G A L} {τ₁ τ₂ : DadeMap (G := G) k A L}
    (h₁ : IsDadeMap hyp τ₁) (h₂ : IsDadeMap hyp τ₂) : τ₁ = τ₂ := by
  funext α
  refine ClassFunction.ext fun g => ?_
  by_cases hg : g ∈ hyp.dadeSupport
  · obtain ⟨a, h, hh, hconj⟩ := hyp.mem_dadeSupport_iff.mp hg
    rw [h₁.map_eq_of_isConj_hCoset α g a h hh hconj,
      h₂.map_eq_of_isConj_hCoset α g a h hh hconj]
  · rw [h₁.map_eq_zero_of_not_mem_dadeSupport α g hg,
      h₂.map_eq_zero_of_not_mem_dadeSupport α g hg]

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

/-! ### The explicit Dade map of Peterfalvi (2.5)

We construct the Dade map `α ↦ α^τ` *pointwise* from its defining equations (2.5):
`α^τ(g) = α(a)` if `g` is `G`-conjugate to an element of some coset `aH(a)`, and `0`
otherwise.  Well-definedness (independence of the chosen `a`) is exactly (2.4.b).
This realizes the previously interface-only `IsDadeMap` as an honest construction;
together with `isDadeIsometry_of_isDadeMap` it gives a genuine `DadeIsometryData`.
The remaining (2.6.b) virtual-character preservation, which needs the (2.10)
inclusion–exclusion, upgrades it to a `FullDadeIsometryData`. -/

/-- The value `α^τ(g)` of the Peterfalvi (2.5) Dade map: `α(a)` when `g` is
`G`-conjugate to an element of some coset `aH(a)`, else `0`.  The chosen `a` is
irrelevant by (2.4.b) (`dadeValue_eq`). -/
noncomputable def Hypothesis.dadeValue (hyp : Hypothesis G A L)
    (α : SupportedClassFunctions (G := G) k A L) (g : G) : k := by
  classical
  exact if hg : g ∈ hyp.dadeSupport then
      (α : ClassFunction L k)
        ⟨(hyp.mem_dadeSupport_iff.mp hg).choose.1,
          hyp.mem_L (hyp.mem_dadeSupport_iff.mp hg).choose.2⟩
    else 0

theorem Hypothesis.dadeValue_of_not_mem_dadeSupport (hyp : Hypothesis G A L)
    (α : SupportedClassFunctions (G := G) k A L) {g : G} (hg : g ∉ hyp.dadeSupport) :
    hyp.dadeValue α g = 0 := by
  rw [Hypothesis.dadeValue, dif_neg hg]

/-- **Peterfalvi (2.5), well-definedness.**  `α^τ(g) = α(a)` whenever `g` is
`G`-conjugate to an element of `aH(a)`.  Two such base points `a, a'` are
`L`-conjugate by (2.4.b) (`isConj_in_L_of_mul_H`), and `α` is an `L`-class function. -/
theorem Hypothesis.dadeValue_eq (hyp : Hypothesis G A L)
    (α : SupportedClassFunctions (G := G) k A L)
    {a : {a : G // a ∈ A}} {h g : G} (hh : h ∈ hyp.H a) (hga : IsConj (a.1 * h) g) :
    hyp.dadeValue α g = (α : ClassFunction L k) ⟨a.1, hyp.mem_L a.2⟩ := by
  classical
  have hg : g ∈ hyp.dadeSupport := hyp.mem_dadeSupport_iff.mpr ⟨a, h, hh, hga⟩
  rw [Hypothesis.dadeValue, dif_pos hg]
  set a₀ := (hyp.mem_dadeSupport_iff.mp hg).choose with ha₀
  obtain ⟨h₀, hh₀, hga₀⟩ := (hyp.mem_dadeSupport_iff.mp hg).choose_spec
  obtain ⟨l, hl⟩ := hyp.isConj_in_L_of_mul_H a₀.2 a.2 hh₀ hh (hga₀.trans hga.symm)
  refine ClassFunction.of_isConj (α : ClassFunction L k) (isConj_iff.mpr ⟨l, ?_⟩)
  exact Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; exact hl)

/-- The Peterfalvi (2.5) Dade map as a `ClassFunction G k`.  Conjugation invariance:
if `g` lies in `dadeSupport` it is `G`-conjugate to some `aH(a)`, hence so is
`x g x⁻¹` with the *same* `a`, so both values are `α(a)`; off `dadeSupport` both are `0`
(`dadeSupport` is conjugation-stable). -/
noncomputable def Hypothesis.dadeMapCF (hyp : Hypothesis G A L)
    (α : SupportedClassFunctions (G := G) k A L) : ClassFunction G k :=
  ⟨hyp.dadeValue α, by
    intro g x
    by_cases hg : g ∈ hyp.dadeSupport
    · obtain ⟨a, h, hh, hga⟩ := hyp.mem_dadeSupport_iff.mp hg
      rw [hyp.dadeValue_eq α hh (hga.trans (isConj_iff.mpr ⟨x, rfl⟩)),
        hyp.dadeValue_eq α hh hga]
    · have hxg : x * g * x⁻¹ ∉ hyp.dadeSupport := by
        rw [hyp.mem_dadeSupport_conj_iff]; exact hg
      rw [hyp.dadeValue_of_not_mem_dadeSupport α hxg,
        hyp.dadeValue_of_not_mem_dadeSupport α hg]⟩

/-- **Peterfalvi (2.5).**  The explicit Dade map `τ : CF(L, A) → CF(G)`. -/
noncomputable def Hypothesis.dadeMap (hyp : Hypothesis G A L) :
    DadeMap (G := G) k A L :=
  fun α => hyp.dadeMapCF α

@[simp] theorem Hypothesis.dadeMap_apply (hyp : Hypothesis G A L)
    (α : SupportedClassFunctions (G := G) k A L) (g : G) :
    hyp.dadeMap α g = hyp.dadeValue α g := rfl

/-- The Peterfalvi (2.5) Dade map is `k`-linear in its argument.

`dadeValue α g` is, at each `g ∈ dadeSupport`, the *evaluation* `α(a)` at a fixed base point `a`
(and `0` off the support), so it is `k`-linear in `α`: `dadeValue (c•α+β) g = c·dadeValue α g +
dadeValue β g` pointwise.  This packages the bare `DadeMap` function `hyp.dadeMap` as an honest
`k`-linear map `CF(L,A) →ₗ[k] CF(G)` — the form needed to extend it to a total integral character
map (the coherence base map `τ` of Peterfalvi (5.1)). -/
noncomputable def Hypothesis.dadeLinearMap (hyp : Hypothesis G A L) :
    SupportedClassFunctions (G := G) k A L →ₗ[k] ClassFunction G k where
  toFun := hyp.dadeMap (k := k)
  map_add' α β := by
    ext g
    classical
    by_cases hg : g ∈ hyp.dadeSupport
    · obtain ⟨a, h, hh, hga⟩ := hyp.mem_dadeSupport_iff.mp hg
      rw [ClassFunction.add_apply, hyp.dadeMap_apply, hyp.dadeMap_apply, hyp.dadeMap_apply,
        hyp.dadeValue_eq α hh hga, hyp.dadeValue_eq β hh hga, hyp.dadeValue_eq (α + β) hh hga]
      rfl
    · rw [ClassFunction.add_apply, hyp.dadeMap_apply, hyp.dadeMap_apply, hyp.dadeMap_apply,
        hyp.dadeValue_of_not_mem_dadeSupport α hg, hyp.dadeValue_of_not_mem_dadeSupport β hg,
        hyp.dadeValue_of_not_mem_dadeSupport (α + β) hg, add_zero]
  map_smul' c α := by
    ext g
    classical
    by_cases hg : g ∈ hyp.dadeSupport
    · obtain ⟨a, h, hh, hga⟩ := hyp.mem_dadeSupport_iff.mp hg
      rw [RingHom.id_apply, ClassFunction.smul_apply, hyp.dadeMap_apply, hyp.dadeMap_apply,
        hyp.dadeValue_eq α hh hga, hyp.dadeValue_eq (c • α) hh hga]
      rfl
    · rw [RingHom.id_apply, ClassFunction.smul_apply, hyp.dadeMap_apply, hyp.dadeMap_apply,
        hyp.dadeValue_of_not_mem_dadeSupport α hg,
        hyp.dadeValue_of_not_mem_dadeSupport (c • α) hg, mul_zero]

@[simp] theorem Hypothesis.dadeLinearMap_apply (hyp : Hypothesis G A L)
    (α : SupportedClassFunctions (G := G) k A L) :
    hyp.dadeLinearMap (k := k) α = hyp.dadeMap (k := k) α := rfl

/-- **Peterfalvi (2.5).**  The explicit Dade map satisfies the defining equations,
i.e. it `IsDadeMap`.  This discharges the `IsDadeMap` interface by construction. -/
theorem Hypothesis.isDadeMap_dadeMap (hyp : Hypothesis G A L) :
    IsDadeMap hyp (hyp.dadeMap (k := k)) where
  map_eq_of_isConj_hCoset α g a h hh hconj := hyp.dadeValue_eq α hh hconj
  map_eq_zero_of_not_mem_dadeSupport α g hg :=
    hyp.dadeValue_of_not_mem_dadeSupport α hg

/-- **Peterfalvi (2.11), restriction compatibility of the constructed Dade map.**  The
explicit Dade map of the restricted hypothesis `hyp.restrict` is the domain-restriction
of the explicit Dade map of `hyp`: `(α₁)^{τ₁} = (ι α₁)^τ` for `α₁ ∈ CF(L, A₁)`.

This fulfils the promise recorded at `Hypothesis.restrict` — that "the equality of the
corresponding Dade maps is stated later, once `dadeMap` is defined".  It now holds *as a
theorem about the genuine construction* (not an interface assumption): both sides satisfy
the (2.5) defining equations for `hyp.restrict` — the left by `isDadeMap_dadeMap`, the
right by `IsDadeMap.restrictDomain` applied to `hyp`'s — so they coincide by the (2.5)
uniqueness `IsDadeMap.unique`. -/
theorem Hypothesis.dadeMap_restrict (hyp : Hypothesis G A L) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    (hyp.restrict hA₁A hA₁_norm).dadeMap (k := k) =
      DadeMap.restrictDomain (G := G) (k := k) (L := L) (hyp.dadeMap (k := k)) hA₁A :=
  IsDadeMap.unique
    ((hyp.restrict hA₁A hA₁_norm).isDadeMap_dadeMap (k := k))
    (IsDadeMap.restrictDomain (hyp.isDadeMap_dadeMap (k := k)) hA₁A hA₁_norm)

/-- **Peterfalvi (2.11)**, pointwise form of `Hypothesis.dadeMap_restrict`: the restricted
Dade map evaluated at `α₁ ∈ CF(L, A₁)` is `hyp`'s Dade map at the included `α₁`. -/
theorem Hypothesis.dadeMap_restrict_apply (hyp : Hypothesis G A L) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (α : SupportedClassFunctions (G := G) k A₁ L) :
    (hyp.restrict hA₁A hA₁_norm).dadeMap (k := k) α =
      hyp.dadeMap (k := k)
        (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α) := by
  rw [hyp.dadeMap_restrict hA₁A hA₁_norm, DadeMap.restrictDomain_apply]

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

/-- **Peterfalvi (2.6.b), reduced to the (2.10) identity.**  If the explicit Dade map
`hyp.dadeMap` agrees, on every supported virtual character `α ∈ ℤ[Irr L, A]`, with *some* finite
`ℤ`-linear combination of inclusion–exclusion summands `Ind_{M(B)}^G α_B` (`induceAlphaBTerm`),
then `hyp.dadeMap` preserves virtual characters, i.e. satisfies `PreservesVirtualCharacters`.

This isolates the remaining content of (2.6.b) to the (2.10) identity
`α^τ = -∑_{B ∈ ℬ} (-1)^{|B|} Ind_{M(B)} α_B` itself: once that pointwise identity is available
(with `s = ℬ` the `L`-conjugacy transversal and `c B = -(-1)^{|B|}`), this lemma upgrades the
`DadeIsometryData` to a `FullDadeIsometryData`.  Membership of the right-hand side in `ℤ[Irr G]`
is `zsmul_induceAlphaBTerm_sum_mem_ZIrr`. -/
theorem preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis G A L} (hconj : hyp.HConjInvariant)
    (hτ : ∀ α : SupportedClassFunctions (G := G) ℂ A L,
        ((α : ClassFunction L ℂ) ∈ ZIrr L) →
        ∃ (s : Finset {B : Finset {a : G // a ∈ A} // B.Nonempty})
          (c : {B : Finset {a : G // a ∈ A} // B.Nonempty} → ℤ),
          hyp.dadeMap (k := ℂ) α
            = ∑ p ∈ s, c p • hyp.induceAlphaBTerm hconj (α : ClassFunction L ℂ) p) :
    PreservesVirtualCharacters (G := G) (A := A) (L := L) (hyp.dadeMap (k := ℂ)) := by
  intro α hα
  obtain ⟨s, c, hsum⟩ := hτ α hα
  rw [hsum]
  exact hyp.zsmul_induceAlphaBTerm_sum_mem_ZIrr hconj hα s c

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

/-- **The explicit Dade isometry of Peterfalvi (2.5)–(2.6.a).**  Bundles the pointwise
Dade map `dadeMap` (satisfying the (2.5) equations, `isDadeMap_dadeMap`) with the (2.6.a)
isometry property, supplied automatically by `isDadeIsometry_of_isDadeMap`.

This realizes the previously interface-only `DadeIsometryData` as an actual construction,
relative to Hypothesis (2.2) plus the (2.4.a) `L`-equivariance `HConjInvariant`.
Virtual-character preservation (2.6.b) — which upgrades this to a `FullDadeIsometryData` —
needs the (2.10) inclusion–exclusion and is tracked separately (issue 0040). -/
noncomputable def Hypothesis.dadeIsometryData (hconj : hyp.HConjInvariant) :
    DadeIsometryData (G := G) (k := ℂ) hyp :=
  DadeIsometryData.ofIsDadeMap hyp (hyp.dadeMap (k := ℂ))
    (hyp.isDadeMap_dadeMap (k := ℂ)) hconj

@[simp] theorem Hypothesis.dadeIsometryData_toDadeMap (hconj : hyp.HConjInvariant) :
    (hyp.dadeIsometryData hconj).toDadeMap = hyp.dadeMap (k := ℂ) :=
  rfl

/-! ### Peterfalvi (2.10), the pointwise inclusion–exclusion identity and `FullDadeIsometryData`

The (2.10) identity `α^τ = -∑_{C ∈ ℬ} (-1)^{|rep C|} Ind_{M(rep C)} α_{rep C}` is now assembled from
the support-side total `sum_mobiusTermCF_transversalRep_eq_neg` and the non-support vanishing
`induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport`, then fed through the bridge
`preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum` to construct the
`FullDadeIsometryData`. -/

open scoped Classical in
/-- **Peterfalvi (2.10), the pointwise identity.**  For a supported class function `α ∈ CF(L, A)`,
the Dade map equals the negated transversal sum of orbit-averaging summands:

    `α^τ(g) = -∑_{C ∈ ℬ} mobiusTermCF (rep C) (g)`,

where `mobiusTermCF (rep C) = (-1)^{|rep C|} Ind_{M(rep C)}^G α_{rep C}`.  On the Dade support
(`g ∈ (aH(a))^G`) the transversal sum is `-α(a) = -α^τ(g)`
(`sum_mobiusTermCF_transversalRep_eq_neg`); off the support both sides vanish — `α^τ(g) = 0` by the
(2.5) definition, and each `Ind_{M(rep C)} α_{rep C}(g) = 0` by
`induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport`. -/
theorem Hypothesis.dadeMap_eq_neg_sum_mobiusTermCF (hconj : hyp.HConjInvariant)
    (α : SupportedClassFunctions (G := G) ℂ A L) :
    letI := hyp.conjFinsetAction
    letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
    hyp.dadeMap (k := ℂ) α
      = (⟨fun g => -∑ C : hyp.conjClassQuotient,
            hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g (hyp.transversalRep C),
          by
            intro g x
            classical
            simp only [neg_inj]
            refine Finset.sum_congr rfl fun C _ => ?_
            by_cases hC : (hyp.transversalRep C).Nonempty
            · letI : Invertible (Nat.card (mBSubgroup hyp (hyp.transversalRep C) hC) : ℂ) :=
                invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
              rw [hyp.mobiusTermCF_of_nonempty hconj _ g hC,
                hyp.mobiusTermCF_of_nonempty hconj _ (x * g * x⁻¹) hC]
              congr 1
              rw [hyp.induceAlphaBTerm_apply hconj _ hC, hyp.induceAlphaBTerm_apply hconj _ hC]
              exact (ClassFunction.induce (mBSubgroup hyp (hyp.transversalRep C) hC)
                (alphaB hyp hconj hC (α : ClassFunction L ℂ))).2 g x
            · rw [hyp.mobiusTermCF_of_not_nonempty hconj _ g hC,
                hyp.mobiusTermCF_of_not_nonempty hconj _ (x * g * x⁻¹) hC]⟩
          : ClassFunction G ℂ) := by
  classical
  letI := hyp.conjFinsetAction
  letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
  refine ClassFunction.ext fun g => ?_
  show hyp.dadeValue (α : SupportedClassFunctions (G := G) ℂ A L) g
    = -∑ C : hyp.conjClassQuotient,
        hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g (hyp.transversalRep C)
  by_cases hg : g ∈ hyp.dadeSupport
  · -- support side: the transversal sum is `-α(a)`.
    obtain ⟨a, h, hh, hga⟩ := hyp.mem_dadeSupport_iff.mp hg
    rw [hyp.dadeValue_eq α hh hga,
      hyp.sum_mobiusTermCF_transversalRep_eq_neg hconj α hh hga, neg_neg]
  · -- non-support side: both sides are `0`.
    rw [hyp.dadeValue_of_not_mem_dadeSupport α hg]
    rw [show (∑ C : hyp.conjClassQuotient,
          hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g (hyp.transversalRep C)) = 0 from ?_,
      neg_zero]
    refine Finset.sum_eq_zero fun C _ => ?_
    by_cases hC : (hyp.transversalRep C).Nonempty
    · letI : Invertible (Nat.card (mBSubgroup hyp (hyp.transversalRep C) hC) : ℂ) :=
        invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      rw [hyp.mobiusTermCF_of_nonempty hconj _ g hC, hyp.induceAlphaBTerm_apply hconj _ hC,
        hyp.induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport hconj hC α hg, mul_zero]
    · rw [hyp.mobiusTermCF_of_not_nonempty hconj _ g hC]

open scoped Classical in
/-- The transversal sum of `mobiusTermCF` reindexes over the `Finset` of nonempty subsets that are
their own conjugacy-class representative (`transversalRep (mk'' B) = B`), with the summand the
packaged induced character:

    `∑_{C ∈ ℬ} mobiusTermCF (rep C) (g) = ∑_{p ∈ s} (-1)^{|p.1|} · Ind_{M(p)}^G α_p (g)`,

`s` ranging over `{p : {B // B.Nonempty} // transversalRep (mk'' p.1) = p.1}` (as a `Finset`).
This converts the (2.10) identity into the `∑ c_p • induceAlphaBTerm p` shape demanded by the bridge
`preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum`.  The bijection sends a class `C` with
nonempty representative to `⟨rep C, _⟩` and back via `p ↦ mk'' p.1` (`Quotient.out_eq'`); the empty
classes contribute `0` on the left and are excluded on the right. -/
theorem Hypothesis.sum_mobiusTermCF_transversalRep_eq_sum_subtype (hconj : hyp.HConjInvariant)
    (α : SupportedClassFunctions (G := G) ℂ A L) (g : G) :
    letI := hyp.conjFinsetAction
    letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
    letI : Fintype {B : Finset {a : G // a ∈ A} // B.Nonempty} := Fintype.ofFinite _
    (∑ C : hyp.conjClassQuotient,
        hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g (hyp.transversalRep C))
      = ∑ p ∈ (Finset.univ : Finset {B : Finset {a : G // a ∈ A} // B.Nonempty}).filter
          (fun p => hyp.transversalRep (Quotient.mk'' p.1) = p.1),
          ((-1 : ℂ) ^ p.1.card) * hyp.induceAlphaBTerm hconj (α : ClassFunction L ℂ) p g := by
  classical
  letI := hyp.conjFinsetAction
  letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
  letI : Fintype {B : Finset {a : G // a ∈ A} // B.Nonempty} := Fintype.ofFinite _
  -- restrict the left sum to nonempty-rep classes (empty reps contribute `0`).
  rw [← Finset.sum_filter_of_ne (p := fun C : hyp.conjClassQuotient =>
        (hyp.transversalRep C).Nonempty) ?_]
  · -- now bijection between `{C : rep C nonempty}` and the fixed-point subtype Finset.
    refine Finset.sum_bij'
      (i := fun C hC => (⟨hyp.transversalRep C, by
          rw [Finset.mem_filter] at hC; exact hC.2⟩
        : {B : Finset {a : G // a ∈ A} // B.Nonempty}))
      (j := fun p _ => (Quotient.mk'' p.1 : hyp.conjClassQuotient))
      ?_ ?_ ?_ ?_ ?_
    · -- `i C ∈ s`
      intro C hC
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show hyp.transversalRep (Quotient.mk'' (hyp.transversalRep C)) = hyp.transversalRep C
      simp only [transversalRep, Quotient.out_eq']
    · -- `j p ∈ filter (rep nonempty)`
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hp.2]; exact p.2
    · -- left inverse: `mk'' (rep C) = C`
      intro C hC
      show Quotient.mk'' (hyp.transversalRep C) = C
      simp only [transversalRep, Quotient.out_eq']
    · -- right inverse: `⟨rep (mk'' p.1), _⟩ = p`
      intro p hp
      rw [Finset.mem_filter] at hp
      apply Subtype.ext
      exact hp.2
    · -- summand agreement
      intro C hC
      rw [Finset.mem_filter] at hC
      rw [hyp.mobiusTermCF_of_nonempty hconj _ g hC.2]
  · -- the dropped terms (empty reps) are zero: if the summand is nonzero, the rep is nonempty.
    intro C _ hC
    by_contra hne
    exact hC (hyp.mobiusTermCF_of_not_nonempty hconj _ g hne)

/-- Evaluation of a `Finset` sum of class functions is the sum of the evaluations. -/
private theorem classFunction_finset_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → ClassFunction G ℂ) (g : G) :
    (∑ p ∈ s, f p) g = ∑ p ∈ s, f p g := by
  classical
  refine s.induction_on (by simp) ?_
  intro p s' hps' ih
  rw [Finset.sum_insert hps', Finset.sum_insert hps', ClassFunction.add_apply, ih]

open scoped Classical in
/-- **Peterfalvi (2.6.b).**  The complex Dade map preserves virtual characters:
`τ : ℤ[Irr L, A] → ℤ[Irr G]`.

This is the culmination of the (2.10) inclusion–exclusion.  Feeding the pointwise identity
`α^τ = -∑_{C ∈ ℬ} (-1)^{|rep C|} Ind_{M(rep C)} α_{rep C}` (`dadeMap_eq_neg_sum_mobiusTermCF`,
reindexed over the representative subtype by `sum_mobiusTermCF_transversalRep_eq_sum_subtype`) into
the bridge `preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum`: the right-hand side is a
`ℤ`-linear combination (`c p = -(-1)^{|p.1|}`) of inclusion–exclusion summands `induceAlphaBTerm`,
each a virtual character (`induceAlphaBTerm_mem_ZIrr`), so `α^τ ∈ ℤ[Irr G]`. -/
theorem Hypothesis.preservesVirtualCharacters_dadeMap (hconj : hyp.HConjInvariant) :
    PreservesVirtualCharacters (G := G) (A := A) (L := L) (hyp.dadeMap (k := ℂ)) := by
  refine preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum hconj ?_
  intro α _
  letI := hyp.conjFinsetAction
  letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
  letI : Fintype {B : Finset {a : G // a ∈ A} // B.Nonempty} := Fintype.ofFinite _
  refine ⟨(Finset.univ : Finset {B : Finset {a : G // a ∈ A} // B.Nonempty}).filter
      (fun p => hyp.transversalRep (Quotient.mk'' p.1) = p.1),
    fun p => -((-1 : ℤ) ^ p.1.card), ?_⟩
  refine ClassFunction.ext fun g => ?_
  rw [hyp.dadeMap_eq_neg_sum_mobiusTermCF hconj α]
  show -∑ C : hyp.conjClassQuotient,
      hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g (hyp.transversalRep C)
    = (∑ p ∈ (Finset.univ : Finset {B : Finset {a : G // a ∈ A} // B.Nonempty}).filter
        (fun p => hyp.transversalRep (Quotient.mk'' p.1) = p.1),
        (-((-1 : ℤ) ^ p.1.card)) • hyp.induceAlphaBTerm hconj (α : ClassFunction L ℂ) p) g
  rw [hyp.sum_mobiusTermCF_transversalRep_eq_sum_subtype hconj α g,
    classFunction_finset_sum_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  -- `(-(-1)^|p.1| • Ind p) g = -((-1)^|p.1| · Ind p g)`.
  rw [show (-((-1 : ℤ) ^ p.1.card)) • hyp.induceAlphaBTerm hconj (α : ClassFunction L ℂ) p
      = (((-((-1 : ℤ) ^ p.1.card) : ℤ) : ℂ)) • hyp.induceAlphaBTerm hconj (α : ClassFunction L ℂ) p
      from by rw [Int.cast_smul_eq_zsmul], ClassFunction.smul_apply]
  push_cast
  ring

/-- **Peterfalvi (2.6).**  The full complex Dade-isometry package: the (2.5) Dade-map equations, the
(2.6.a) normalized isometry, and the (2.6.b) virtual-character preservation, all constructed from
Hypothesis (2.2) plus the (2.4.a) `L`-equivariance `HConjInvariant`.

This is the honest construction of `FullDadeIsometryData` (no longer an interface assumption):
`toDadeIsometryData` is the `dadeIsometryData` built from the explicit (2.5) Dade map, and
`preserves_virtualCharacters` is the (2.10) inclusion–exclusion result
`preservesVirtualCharacters_dadeMap`. -/
noncomputable def Hypothesis.fullDadeIsometryData (hconj : hyp.HConjInvariant) :
    FullDadeIsometryData (G := G) hyp where
  toDadeIsometryData := hyp.dadeIsometryData hconj
  preserves_virtualCharacters := by
    rw [hyp.dadeIsometryData_toDadeMap hconj]
    exact hyp.preservesVirtualCharacters_dadeMap hconj

end AdjointFormula

end DadeMap

end OddOrder.Peterfalvi.S04
