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
# S04_DadeIsometryBasic

Prefix-split from `OddOrder.Peterfalvi.S04_DadeIsometry` (2000-line limit, issue 0103 第 2 パス).
-/

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

/-- If the full centralizer of a point `a ∈ A` lies in `L`, then the local
subgroup `H(a)` of **any** Hypothesis (2.2) datum on `(A, L)` is trivial:
`H(a) ≤ C_G(a)` by `centralizer_eq_sup`, so `C_G(a) ≤ L` places `H(a)` inside
`C_L(a)`, and `centralizer_disjoint` then forces `H(a) = ⊥`.

This is data-independent — it reads only the proof fields of the hypothesis, so
it applies to opaque (2.2) data (e.g. a packaged `dadeData` field) without
knowing how its `H` was constructed. -/
theorem H_eq_bot_of_centralizer_le (hyp : Hypothesis G A L)
    (a : {a : G // a ∈ A})
    (hle : Subgroup.centralizer ({a.1} : Set G) ≤ L) : hyp.H a = ⊥ := by
  have hHle : hyp.H a ≤ Subgroup.centralizer ({a.1} : Set G) :=
    le_sup_left.trans (hyp.centralizer_eq_sup a).ge
  have hHin : hyp.H a ≤ centralizerIn L a.1 := by
    rw [centralizerIn]
    exact le_inf (hHle.trans hle) hHle
  exact (hyp.centralizer_disjoint a).eq_bot_of_le hHin

/-- The reverse direction of **Peterfalvi (2.3)**: over a TI-subset `A`
relative to `L`, **every** Hypothesis (2.2) datum has all local subgroups
trivial, `H(a) = ⊥` — not just the canonical `of_isTISubset` one.  (TI places
the whole centralizer `C_G(a) ≤ L` for `a ∈ A`, cf.
`IsTISubset.centralizer_le`.)  Combined with the uniqueness
`dadeHypothesis_eq_of_forall_H_eq_bot` (`S12_TICyclicSigmaBridge`), the (2.2)
datum on a TI pair `(A, L)` is therefore unique. -/
theorem H_eq_bot_of_isTISubset (hyp : Hypothesis G A L)
    (hTI : OddOrder.GroupTheory.IsTISubset A L) (a : {a : G // a ∈ A}) :
    hyp.H a = ⊥ :=
  hyp.H_eq_bot_of_centralizer_le a (hTI.centralizer_le a.2)

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

/-- **Order of a Dade-support element**: every `x ∈ Ã(A)` — a conjugate of `a·h` with `a ∈ A`,
`h ∈ H(a)` — has a prime divisor of `orderOf a` dividing `orderOf x`.  The parts commute
(`H(a) ≤ C_G(a)`, `centralizer_eq_sup`) with coprime orders (`centralizer_coprime` at `b = a`,
since `a ∈ C_L(a)`), so `orderOf (a·h) = orderOf a · orderOf h`, and order is a conjugacy
invariant.  This is the order-theoretic half of Peterfalvi (13.19.a)-style support
disjointness: elements of `Ã(A(L))` carry a prime of `|L_F|`. -/
theorem exists_mem_A_prime_dvd_orderOf_of_mem_dadeSupport (hyp : Hypothesis G A L)
    {x : G} (hx : x ∈ hyp.dadeSupport) :
    ∃ a ∈ A, ∃ r : ℕ, r.Prime ∧ r ∣ orderOf a ∧ r ∣ orderOf x := by
  rw [hyp.mem_dadeSupport_iff] at hx
  obtain ⟨a, h, hh, hconj⟩ := hx
  -- `h` centralizes `a` (`H(a) ≤ C_G(a)`)
  have hhc : h ∈ Subgroup.centralizer ({a.1} : Set G) := by
    rw [hyp.centralizer_eq_sup a]
    exact Subgroup.mem_sup_left hh
  have hcomm : Commute a.1 h :=
    (Subgroup.mem_centralizer_singleton_iff.mp hhc).symm
  -- `orderOf a ∣ |C_L(a)|` (self-centralizing) and `orderOf h ∣ |H(a)|`, coprime
  have haC : a.1 ∈ centralizerIn L a.1 := by
    rw [mem_centralizerIn]
    exact ⟨hyp.mem_L a.2, rfl⟩
  have hdvd_a : orderOf a.1 ∣ Nat.card (centralizerIn L a.1) :=
    Subgroup.orderOf_dvd_natCard _ haC
  have hdvd_h : orderOf h ∣ Nat.card (hyp.H a) :=
    Subgroup.orderOf_dvd_natCard _ hh
  have hcop : Nat.Coprime (orderOf h) (orderOf a.1) :=
    Nat.Coprime.coprime_dvd_right hdvd_a
      (Nat.Coprime.coprime_dvd_left hdvd_h (hyp.centralizer_coprime a a))
  -- a prime of `orderOf a` (`a ≠ 1`)
  have hane : orderOf a.1 ≠ 1 := fun h1 => hyp.ne_one a.2 (orderOf_eq_one_iff.mp h1)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hane
  refine ⟨a.1, a.2, r, hr, hrdvd, ?_⟩
  -- `orderOf x = orderOf (a·h) = orderOf a · orderOf h`
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hox : orderOf x = orderOf a.1 * orderOf h := by
    have hinj : orderOf ((MulAut.conj c).toMonoidHom (a.1 * h)) = orderOf (a.1 * h) :=
      orderOf_injective (MulAut.conj c).toMonoidHom (MulEquiv.injective _) _
    rw [← hc,
      show c * (a.1 * h) * c⁻¹ = (MulAut.conj c).toMonoidHom (a.1 * h) by
        simp [MulAut.conj_apply],
      hinj, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop.symm]
  rw [hox]
  exact hrdvd.trans (dvd_mul_right _ _)

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

This predicate is **always satisfied** under Hypothesis (2.2): see `Hypothesis.hConjInvariant`,
which derives it from `mem_H_iff_coprime_orderOf`.  It is retained as a named predicate only
because it is threaded as an explicit argument through the (2.6)–(2.10) API; every such
argument can now be discharged by `hyp.hConjInvariant`.

(The book proves this via `H(a) = O_{π'}(C_G(a))` for the global prime set
`π = ⋃_{b ∈ A} π(|C_L(b)|)`; the repo proof uses the equivalent local characterization of
`H(a)` by coprimality to `|C_L(a)|`, which needs no `O_{π'}` API.) -/
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

/-- **Elementwise characterization of `H(a)`.**  Under Hypothesis (2.2), `H(a)` consists of
exactly the elements of `C_G(a)` whose order is prime to `|C_L(a)|`:

`x ∈ H(a) ↔ x ∈ C_G(a) ∧ gcd(o(x), |C_L(a)|) = 1`.

`⊆` is (2.2.c): `o(x)` divides `|H(a)|`, which is prime to `|C_L(a)|`.  `⊇` is
`mem_H_of_mem_centralizer_coprime`, i.e. the semidirect decomposition
`C_G(a) = H(a) ⋊ C_L(a)` of (2.2.b).

This is the `π'`-core description of `H(a)` used in the book's proof of (2.4.a), but stated
with the *per-`a`* modulus `|C_L(a)|` in place of the global prime set
`π = ⋃_{b ∈ A} π(|C_L(b)|)`.  The two agree here — coprimality to `|C_L(a)|` already pins
`H(a)` down — and the local form avoids needing any `O_{π'}` API. -/
theorem mem_H_iff_coprime_orderOf (hyp : Hypothesis G A L)
    (a : {a : G // a ∈ A}) (x : G) :
    x ∈ hyp.H a ↔
      x ∈ Subgroup.centralizer ({a.1} : Set G) ∧
        Nat.Coprime (orderOf x) (Nat.card (centralizerIn L a.1)) := by
  constructor
  · intro hx
    have hle : hyp.H a ≤ Subgroup.centralizer ({a.1} : Set G) := by
      rw [hyp.centralizer_eq_sup a]; exact le_sup_left
    exact ⟨hle hx,
      Nat.Coprime.coprime_dvd_left ((hyp.H a).orderOf_dvd_natCard hx)
        (hyp.centralizer_coprime a a)⟩
  · rintro ⟨hxC, hcop⟩
    exact hyp.mem_H_of_mem_centralizer_coprime a hxC hcop

/-- **Peterfalvi (2.4.a)**: `H(a^l) = H(a)^l` for `a ∈ A` and `l ∈ L`.

Hypothesis (2.2) *implies* the equivariance predicate `HConjInvariant`; it need not be
assumed.  By `mem_H_iff_coprime_orderOf`, membership `x ∈ H(a)` is the conjunction of two
conditions, and conjugation by `l` transports each:

* `x ∈ C_G(a^l) ↔ l⁻¹xl ∈ C_G(a)` (centralizers are conjugation-equivariant);
* `o(l⁻¹xl) = o(x)` (conjugation preserves order);
* `|C_L(a^l)| = |C_L(a)|` (`card_centralizerIn_conj`) — **this is where `l ∈ L` is used**,
  since conjugation by `l` must map `C_L(a)` onto `C_L(a^l)`.

The book argues via `H(a) = O_{π'}(C_G(a))` for the global prime set `π`; the local
characterization above gives the same conclusion without any `π`-core API. -/
theorem hConjInvariant (hyp : Hypothesis G A L) : hyp.HConjInvariant := by
  intro a l
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    hyp.mem_H_iff_coprime_orderOf ⟨(l : G) * a.1 * (l : G)⁻¹, hyp.L_normalizes_A l a.2⟩,
    hyp.mem_H_iff_coprime_orderOf a]
  have hsmul : ((MulAut.conj (l : G))⁻¹ • x) = (l : G)⁻¹ * x * (l : G) := by
    simp [MulAut.conj]
  rw [hsmul]
  -- conjugation preserves order
  have hord : orderOf ((l : G)⁻¹ * x * (l : G)) = orderOf x := by
    have hsc : SemiconjBy (l : G) ((l : G)⁻¹ * x * (l : G)) x := by
      show (l : G) * ((l : G)⁻¹ * x * (l : G)) = x * (l : G)
      group
    exact SemiconjBy.orderOf_eq (l : G) hsc
  -- `|C_L(a^l)| = |C_L(a)|` (uses `l ∈ L`)
  have hcard : Nat.card (centralizerIn L ((l : G) * a.1 * (l : G)⁻¹))
      = Nat.card (centralizerIn L a.1) := card_centralizerIn_conj l.2 a.1
  -- centralizer condition transports
  have hcent : x ∈ Subgroup.centralizer ({(l : G) * a.1 * (l : G)⁻¹} : Set G)
      ↔ (l : G)⁻¹ * x * (l : G) ∈ Subgroup.centralizer ({a.1} : Set G) := by
    simp only [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h2 : (l : G)⁻¹ * (x * ((l : G) * a.1 * (l : G)⁻¹)) * (l : G)
          = (l : G)⁻¹ * (((l : G) * a.1 * (l : G)⁻¹) * x) * (l : G) := by rw [h]
      calc ((l : G)⁻¹ * x * (l : G)) * a.1
          = (l : G)⁻¹ * (x * ((l : G) * a.1 * (l : G)⁻¹)) * (l : G) := by group
        _ = (l : G)⁻¹ * (((l : G) * a.1 * (l : G)⁻¹) * x) * (l : G) := h2
        _ = a.1 * ((l : G)⁻¹ * x * (l : G)) := by group
    · intro h
      calc x * ((l : G) * a.1 * (l : G)⁻¹)
          = (l : G) * (((l : G)⁻¹ * x * (l : G)) * a.1) * (l : G)⁻¹ := by group
        _ = (l : G) * (a.1 * ((l : G)⁻¹ * x * (l : G))) * (l : G)⁻¹ := by rw [h]
        _ = ((l : G) * a.1 * (l : G)⁻¹) * x := by group
  rw [hord, hcard, hcent]

/-- **Peterfalvi (2.4.c)**: `N_G(a·H(a)) = C_G(a)` for `a ∈ A`.

Stated elementwise: `g` stabilizes the coset `H(a)·a` under conjugation exactly when `g`
centralizes `a`.  (`H(a) ≤ C_G(a)`, so `H(a)·a = a·H(a)` is the book's coset `aH(a)`.)

`⊇` is the book's implicit converse: a `g ∈ C_G(a)` normalizes `H(a)` (`H_normalized`, applied
to `g` and to `g⁻¹`) and fixes `a`, hence permutes the coset.

`⊆` is the book's argument "`a^g = (a^g)_π = a`, and so `g ∈ C_G(a)`", with the local modulus
`|C_L(a)|` in place of the global prime set `π` (as in `mem_H_iff_coprime_orderOf`): since
`a ∈ H(a)·a`, stability gives `g·a·g⁻¹ = u·a` for some `u ∈ H(a)`.  Now `u` commutes with `a`
(`H(a) ≤ C_G(a)`) and `o(u) ∣ |H(a)|` is prime to `o(a) ∣ |C_L(a)|`
(`centralizer_coprime`), so `o(u·a) = o(u)·o(a)`; but conjugation preserves order, so
`o(u·a) = o(a)`, forcing `o(u) = 1`, i.e. `u = 1` and `g·a·g⁻¹ = a`. -/
theorem conj_coset_H_eq_iff_mem_centralizer (hyp : Hypothesis G A L)
    (a : {a : G // a ∈ A}) (g : G) :
    (fun x => g * x * g⁻¹) '' ((↑(hyp.H a) : Set G) * ({a.1} : Set G))
        = (↑(hyp.H a) : Set G) * ({a.1} : Set G)
      ↔ g ∈ Subgroup.centralizer ({a.1} : Set G) := by
  have hHC : (hyp.H a : Subgroup G) ≤ Subgroup.centralizer ({a.1} : Set G) := by
    rw [hyp.centralizer_eq_sup a]; exact le_sup_left
  constructor
  · intro himg
    -- `a ∈ H(a)·a`, so `g·a·g⁻¹ = u·a` for some `u ∈ H(a)`.
    have hamem : a.1 ∈ (↑(hyp.H a) : Set G) * ({a.1} : Set G) :=
      ⟨1, (hyp.H a).one_mem, a.1, Set.mem_singleton _, one_mul _⟩
    have hga : g * a.1 * g⁻¹ ∈ (↑(hyp.H a) : Set G) * ({a.1} : Set G) := by
      rw [← himg]; exact ⟨a.1, hamem, rfl⟩
    obtain ⟨u, hu, b, hb, hueq⟩ := hga
    rw [Set.mem_singleton_iff] at hb
    subst hb
    -- `u` commutes with `a`, and their orders are coprime.
    have hueq' : u * a.1 = g * a.1 * g⁻¹ := hueq
    have hcomm : Commute u a.1 := Subgroup.mem_centralizer_singleton_iff.mp (hHC hu)
    have hcop : Nat.Coprime (orderOf u) (orderOf a.1) := by
      refine Nat.Coprime.coprime_dvd_left ((hyp.H a).orderOf_dvd_natCard hu) ?_
      refine Nat.Coprime.coprime_dvd_right ?_ (hyp.centralizer_coprime a a)
      exact (centralizerIn L a.1).orderOf_dvd_natCard
        (mem_centralizerIn.mpr ⟨hyp.mem_L a.2, rfl⟩)
    -- Conjugation preserves order, so `o(u)·o(a) = o(a)`, i.e. `o(u) = 1`.
    have hordconj : orderOf (g * a.1 * g⁻¹) = orderOf a.1 :=
      SemiconjBy.orderOf_eq g⁻¹ (show g⁻¹ * (g * a.1 * g⁻¹) = a.1 * g⁻¹ by group)
    have hordmul : orderOf (u * a.1) = orderOf u * orderOf a.1 :=
      hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
    have hkey : orderOf u * orderOf a.1 = orderOf a.1 := by
      rw [← hordmul, hueq', hordconj]
    have hone : orderOf u = 1 :=
      Nat.eq_of_mul_eq_mul_right (orderOf_pos a.1) (by rw [one_mul]; exact hkey)
    have hu1 : u = 1 := orderOf_eq_one_iff.mp hone
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : g * a.1 * g⁻¹ = a.1 := by rw [← hueq', hu1, one_mul]
    calc g * a.1 = (g * a.1 * g⁻¹) * g := by group
      _ = a.1 * g := by rw [hfix]
  · intro hg
    have hga : g * a.1 * g⁻¹ = a.1 := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hg
      calc g * a.1 * g⁻¹ = (a.1 * g) * g⁻¹ := by rw [this]
        _ = a.1 := by group
    ext y
    constructor
    · rintro ⟨x, ⟨u, hu, b, hb, rfl⟩, rfl⟩
      rw [Set.mem_singleton_iff] at hb
      subst hb
      refine ⟨g * u * g⁻¹, hyp.H_normalized a g hg u hu, a.1, Set.mem_singleton _, ?_⟩
      calc g * u * g⁻¹ * a.1 = (g * u * g⁻¹) * (g * a.1 * g⁻¹) := by rw [hga]
        _ = g * (u * a.1) * g⁻¹ := by group
    · rintro ⟨u, hu, b, hb, rfl⟩
      rw [Set.mem_singleton_iff] at hb
      subst hb
      have huinv : g⁻¹ * u * g ∈ hyp.H a := by
        have := hyp.H_normalized a g⁻¹ (Subgroup.inv_mem _ hg) u hu
        rwa [inv_inv] at this
      refine ⟨(g⁻¹ * u * g) * a.1, ⟨g⁻¹ * u * g, huinv, a.1, Set.mem_singleton _, rfl⟩, ?_⟩
      calc g * ((g⁻¹ * u * g) * a.1) * g⁻¹
          = u * (g * a.1 * g⁻¹) := by group
        _ = u * a.1 := by rw [hga]

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
  change α (hyp.dadeQuotientHom hconj hB ⟨h * b, hmem⟩) = _
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

end ConjugacyInvariance
end SemidirectStructure
end Hypothesis
end OddOrder.Peterfalvi.S04
