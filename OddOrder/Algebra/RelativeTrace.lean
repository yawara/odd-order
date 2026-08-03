/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

/-!
# Relative traces of a `G`-algebra

Let a finite group `G` act on a ring `A` by ring automorphisms (`MulSemiringAction G A`).  For
subgroups `K ≤ H ≤ G` the **relative trace**

`Tr^H_K (a) = ∑_{xK ⊆ H} x • a`

sends `K`-fixed elements to `H`-fixed elements.  Its image `A^H_K := Tr^H_K (A^K)` is an ideal of
`A^H`, and these ideals are the basic invariant of Green's theory of vertices and (for
`A = 𝒪G` with `G` acting by conjugation) of **defect groups** of blocks.

The definition below sums over a *fixed* choice of coset representatives (`Quotient.out`); the
workhorse `sum_smul_eq_relTrace` says that on `K`-fixed elements any other family of
representatives gives the same answer, and every structural property is deduced from it.

## Main definitions

* `OddOrder.GAlgebra.relTrace K H a` — the relative trace `Tr^H_K(a)`.

## Main results

* `OddOrder.GAlgebra.sum_smul_eq_relTrace` — independence of the representatives.
* `OddOrder.GAlgebra.smul_relTrace` — `Tr^H_K(a)` is `H`-fixed when `a` is `K`-fixed.
* `OddOrder.GAlgebra.relTrace_self` — `Tr^H_H` is the identity on `H`-fixed elements.
* `OddOrder.GAlgebra.relTrace_trans` — transitivity `Tr^H_K ∘ Tr^K_L = Tr^H_L`.
* `OddOrder.GAlgebra.relTrace_mul_of_fixed`, `OddOrder.GAlgebra.mul_relTrace_of_fixed` —
  the projection (Frobenius) formula: `Tr^H_K` is `A^H`-bilinear.
* `OddOrder.GAlgebra.relTrace_conj` — conjugation equivariance.
* `OddOrder.GAlgebra.relTrace_one` — `Tr^H_K(1) = [H : K] · 1`.
* `OddOrder.GAlgebra.relTrace_mul_eq_self` — `A^H_K = A^H` when `[H : K]` is invertible.

## Implementation notes

The `Fintype` instance on `↥H ⧸ K.subgroupOf H` is produced inside the definition by
`Fintype.ofFinite`, following mathlib's `Subgroup.leftTransversals.diff`, so that it never leaks
into a statement.  Consequently every lemma about the defining sum is proved by transporting
along `sum_smul_eq_relTrace`, whose left-hand side ranges over an *arbitrary* index type.
-/

namespace OddOrder.GAlgebra

variable {G : Type*} [Group G] [Finite G] {A : Type*}

/-- mathlib registers `Finite (G ⧸ H)` only through `Subgroup.FiniteIndex`; the direct instance
from `Finite G` is missing and is needed to sum over cosets. -/
instance instFiniteQuotientSubgroup {α : Type*} [Group α] [Finite α] (s : Subgroup α) :
    Finite (α ⧸ s) :=
  Quotient.finite _

section DistribMulAction

variable [AddCommMonoid A] [DistribMulAction G A]

/-- The **relative trace** `Tr^H_K(a) = ∑_{xK ⊆ H} x • a`, summed over the canonical coset
representatives.  It is the intended notion only on `K`-fixed elements, where it is independent
of the choice (`sum_smul_eq_relTrace`), but it is convenient to have it as a total additive map
`A → A`. -/
noncomputable def relTrace (K H : Subgroup G) (a : A) : A :=
  letI := Fintype.ofFinite (↥H ⧸ K.subgroupOf H)
  ∑ x : ↥H ⧸ K.subgroupOf H, ((x.out : ↥H) : G) • a

omit [Finite G] in
/-- Equality of left cosets of `K.subgroupOf H`, read off inside `G`. -/
theorem mk_eq_mk_iff_mem {K H : Subgroup G} {u v : ↥H} :
    (QuotientGroup.mk u : ↥H ⧸ K.subgroupOf H) = QuotientGroup.mk v ↔ (u : G)⁻¹ * (v : G) ∈ K := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  push_cast
  exact Iff.rfl

omit [Finite G] in
/-- Two elements of `H` in the same left coset of `K` act in the same way on a `K`-fixed
element. -/
theorem smul_eq_smul_of_mk_eq {K H : Subgroup G} {a : A} (ha : ∀ g ∈ K, g • a = a) {u v : ↥H}
    (h : (u : ↥H ⧸ K.subgroupOf H) = v) : (u : G) • a = (v : G) • a := by
  have hmem : u⁻¹ * v ∈ K.subgroupOf H := QuotientGroup.eq.mp h
  rw [Subgroup.mem_subgroupOf] at hmem
  have hv : (v : G) = (u : G) * ((u⁻¹ * v : ↥H) : G) := by
    push_cast
    exact (mul_inv_cancel_left _ _).symm
  rw [hv, mul_smul, ha _ hmem]

/-- **Independence of the coset representatives.**  If `f : ι → G` takes values in `H` and induces
a bijection from `ι` onto the left cosets of `K` in `H`, then `∑ i, f i • a` computes `Tr^H_K(a)`
for every `K`-fixed `a`. -/
theorem sum_smul_eq_relTrace {K H : Subgroup G} {a : A} (ha : ∀ g ∈ K, g • a = a) {ι : Type*}
    [Fintype ι] (f : ι → G) (hf : ∀ i, f i ∈ H)
    (hbij : Function.Bijective fun i =>
      (QuotientGroup.mk ⟨f i, hf i⟩ : ↥H ⧸ K.subgroupOf H)) :
    ∑ i, f i • a = relTrace K H a := by
  letI := Fintype.ofFinite (↥H ⧸ K.subgroupOf H)
  change ∑ i, f i • a = ∑ x : ↥H ⧸ K.subgroupOf H, ((x.out : ↥H) : G) • a
  refine Fintype.sum_bijective _ hbij _ (fun x => ((x.out : ↥H) : G) • a) fun i => ?_
  exact smul_eq_smul_of_mk_eq (u := ⟨f i, hf i⟩) ha (QuotientGroup.out_eq' _).symm

@[simp]
theorem relTrace_zero (K H : Subgroup G) : relTrace K H (0 : A) = 0 := by
  simp [relTrace]

theorem relTrace_add (K H : Subgroup G) (a b : A) :
    relTrace K H (a + b) = relTrace K H a + relTrace K H b := by
  simp [relTrace, smul_add, Finset.sum_add_distrib]

/-- The relative trace as an additive homomorphism. -/
@[simps]
noncomputable def relTraceHom (K H : Subgroup G) : A →+ A where
  toFun := relTrace K H
  map_zero' := relTrace_zero K H
  map_add' := relTrace_add K H

theorem relTrace_smul {R : Type*} [Monoid R] [DistribMulAction R A] [SMulCommClass G R A]
    (K H : Subgroup G) (r : R) (a : A) : relTrace K H (r • a) = r • relTrace K H a := by
  simp [relTrace, smul_comm, Finset.smul_sum]

/-- `Tr^H_K(a)` is fixed by `H` whenever `a` is fixed by `K`. -/
theorem smul_relTrace {K H : Subgroup G} {a : A} (ha : ∀ g ∈ K, g • a = a) {g : G} (hg : g ∈ H) :
    g • relTrace K H a = relTrace K H a := by
  letI := Fintype.ofFinite (↥H ⧸ K.subgroupOf H)
  have hf : ∀ x : ↥H ⧸ K.subgroupOf H, g * ((x.out : ↥H) : G) ∈ H :=
    fun x => H.mul_mem hg (x.out).2
  have hrw : ∀ x : ↥H ⧸ K.subgroupOf H,
      (QuotientGroup.mk ⟨g * ((x.out : ↥H) : G), hf x⟩ : ↥H ⧸ K.subgroupOf H)
        = (⟨g, hg⟩ : ↥H) • x := by
    intro x
    have hmul : (⟨g * ((x.out : ↥H) : G), hf x⟩ : ↥H) = (⟨g, hg⟩ : ↥H) * x.out := rfl
    rw [hmul, ← smul_eq_mul, MulAction.Quotient.coe_smul_out]
  have hbij : Function.Bijective fun x : ↥H ⧸ K.subgroupOf H =>
      (QuotientGroup.mk ⟨g * ((x.out : ↥H) : G), hf x⟩ : ↥H ⧸ K.subgroupOf H) := by
    simpa only [hrw] using MulAction.bijective (α := ↥H) (β := ↥H ⧸ K.subgroupOf H) ⟨g, hg⟩
  calc g • relTrace K H a
      = ∑ x : ↥H ⧸ K.subgroupOf H, (g * ((x.out : ↥H) : G)) • a := by
        simp only [relTrace, Finset.smul_sum, mul_smul]
    _ = relTrace K H a := sum_smul_eq_relTrace ha _ hf hbij

/-- The absolute trace `Tr^G_K` is the sum over `G ⧸ K` in the familiar sense.  (The definition
uses `↥⊤ ⧸ K.subgroupOf ⊤`, which this identifies with `G ⧸ K`.) -/
theorem sum_out_smul_eq_relTrace_top {K : Subgroup G} {a : A} (ha : ∀ g ∈ K, g • a = a)
    [Fintype (G ⧸ K)] : ∑ x : G ⧸ K, ((x.out : G)) • a = relTrace K ⊤ a := by
  refine sum_smul_eq_relTrace ha (fun x : G ⧸ K => (x.out : G)) (fun _ => Subgroup.mem_top _) ?_
  constructor
  · intro x y hxy
    rw [mk_eq_mk_iff_mem] at hxy
    have h := QuotientGroup.eq.mpr hxy
    simpa only [QuotientGroup.out_eq'] using h
  · intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
    refine ⟨QuotientGroup.mk (w : G), ?_⟩
    rw [mk_eq_mk_iff_mem]
    exact QuotientGroup.eq.mp (QuotientGroup.out_eq' _)

/-- `Tr^H_H` is the identity on `H`-fixed elements. -/
theorem relTrace_self {H : Subgroup G} {a : A} (ha : ∀ g ∈ H, g • a = a) :
    relTrace H H a = a := by
  have hall : ∀ y : ↥H ⧸ H.subgroupOf H,
      y = (QuotientGroup.mk ⟨(1 : G), H.one_mem⟩ : ↥H ⧸ H.subgroupOf H) := by
    intro y
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective y
    exact QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr (u⁻¹ * ⟨(1 : G), H.one_mem⟩).2)
  have hbij : Function.Bijective fun _ : Unit =>
      (QuotientGroup.mk ⟨(1 : G), H.one_mem⟩ : ↥H ⧸ H.subgroupOf H) :=
    ⟨fun _ _ _ => rfl, fun y => ⟨(), (hall y).symm⟩⟩
  have key := sum_smul_eq_relTrace (K := H) (H := H) ha (fun _ : Unit => (1 : G))
    (fun _ => H.one_mem) hbij
  simpa using key.symm

/-- **Transitivity of the relative trace**: `Tr^H_K ∘ Tr^K_L = Tr^H_L` for `L ≤ K ≤ H`.

Together with the projection formula this is what makes the images `A^H_K = Tr^H_K(A^K)` a family
of ideals of `A^H` that *decreases* as `K` shrinks. -/
theorem relTrace_trans {L K H : Subgroup G} (hLK : L ≤ K) (hKH : K ≤ H) {a : A}
    (ha : ∀ g ∈ L, g • a = a) :
    relTrace K H (relTrace L K a) = relTrace L H a := by
  letI := Fintype.ofFinite (↥H ⧸ K.subgroupOf H)
  letI := Fintype.ofFinite (↥K ⧸ L.subgroupOf K)
  letI := Fintype.ofFinite (↥H ⧸ L.subgroupOf H)
  set f : (↥H ⧸ K.subgroupOf H) × (↥K ⧸ L.subgroupOf K) → G :=
    fun i => ((i.1.out : ↥H) : G) * ((i.2.out : ↥K) : G) with hfdef
  have hf : ∀ i, f i ∈ H := fun i => H.mul_mem (i.1.out).2 (hKH (i.2.out).2)
  have hinj : Function.Injective fun i =>
      (QuotientGroup.mk ⟨f i, hf i⟩ : ↥H ⧸ L.subgroupOf H) := by
    rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ hEq
    rw [mk_eq_mk_iff_mem] at hEq
    simp only [hfdef] at hEq
    have hx : ((x₁.out : ↥H) : G)⁻¹ * ((x₂.out : ↥H) : G) ∈ K := by
      have hrewrite : ((y₁.out : ↥K) : G) *
          ((((x₁.out : ↥H) : G) * ((y₁.out : ↥K) : G))⁻¹ *
            (((x₂.out : ↥H) : G) * ((y₂.out : ↥K) : G))) * ((y₂.out : ↥K) : G)⁻¹
          = ((x₁.out : ↥H) : G)⁻¹ * ((x₂.out : ↥H) : G) := by group
      rw [← hrewrite]
      exact K.mul_mem (K.mul_mem (y₁.out).2 (hLK hEq)) (K.inv_mem (y₂.out).2)
    have hx12 : x₁ = x₂ := by
      have h := (mk_eq_mk_iff_mem (K := K) (u := x₁.out) (v := x₂.out)).mpr hx
      simpa only [QuotientGroup.out_eq'] using h
    subst hx12
    have hy : ((y₁.out : ↥K) : G)⁻¹ * ((y₂.out : ↥K) : G) ∈ L := by
      have hrewrite : ((y₁.out : ↥K) : G)⁻¹ * ((y₂.out : ↥K) : G)
          = (((x₁.out : ↥H) : G) * ((y₁.out : ↥K) : G))⁻¹ *
            (((x₁.out : ↥H) : G) * ((y₂.out : ↥K) : G)) := by group
      rw [hrewrite]
      exact hEq
    have hy12 : y₁ = y₂ := by
      have h := (mk_eq_mk_iff_mem (K := L) (H := K) (u := y₁.out) (v := y₂.out)).mpr hy
      simpa only [QuotientGroup.out_eq'] using h
    simp [hy12]
  have hcard : Fintype.card ((↥H ⧸ K.subgroupOf H) × (↥K ⧸ L.subgroupOf K))
      = Fintype.card (↥H ⧸ L.subgroupOf H) := by
    have e1 : Fintype.card (↥H ⧸ K.subgroupOf H) = K.relIndex H := by
      rw [← Nat.card_eq_fintype_card]; exact (Subgroup.index_eq_card _).symm
    have e2 : Fintype.card (↥K ⧸ L.subgroupOf K) = L.relIndex K := by
      rw [← Nat.card_eq_fintype_card]; exact (Subgroup.index_eq_card _).symm
    have e3 : Fintype.card (↥H ⧸ L.subgroupOf H) = L.relIndex H := by
      rw [← Nat.card_eq_fintype_card]; exact (Subgroup.index_eq_card _).symm
    rw [Fintype.card_prod, e1, e2, e3, mul_comm]
    exact Subgroup.relIndex_mul_relIndex L K H hLK hKH
  have hbij : Function.Bijective fun i =>
      (QuotientGroup.mk ⟨f i, hf i⟩ : ↥H ⧸ L.subgroupOf H) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩
  rw [← sum_smul_eq_relTrace ha f hf hbij]
  simp only [relTrace, Fintype.sum_prod_type, hfdef, mul_smul, Finset.smul_sum]

open scoped Pointwise in
/-- **Conjugation equivariance**: `c · Tr^H_K(a) = Tr^{cHc⁻¹}_{cKc⁻¹}(c · a)`.

This is what makes the family of ideals `A^H_K` behave under conjugation, and hence what makes
defect groups a single conjugacy class. -/
theorem relTrace_conj (c : G) {K H : Subgroup G} {a : A} (ha : ∀ g ∈ K, g • a = a) :
    relTrace (MulAut.conj c • K) (MulAut.conj c • H) (c • a) = c • relTrace K H a := by
  letI := Fintype.ofFinite (↥H ⧸ K.subgroupOf H)
  have hconj : ∀ x : G, (MulAut.conj c) • x = c * x * c⁻¹ := fun _ => rfl
  have hmemK : ∀ x : G, c * x * c⁻¹ ∈ MulAut.conj c • K ↔ x ∈ K := fun x => by
    rw [← hconj]; exact Subgroup.smul_mem_pointwise_smul_iff
  have hmemH : ∀ x : G, c * x * c⁻¹ ∈ MulAut.conj c • H ↔ x ∈ H := fun x => by
    rw [← hconj]; exact Subgroup.smul_mem_pointwise_smul_iff
  have ha' : ∀ g ∈ MulAut.conj c • K, g • (c • a) = c • a := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_smul_pointwise_iff_exists g (MulAut.conj c) K |>.mp hg
    rw [hconj, ← mul_smul, inv_mul_cancel_right, mul_smul, ha k hk]
  set f : ↥H ⧸ K.subgroupOf H → G := fun x => c * ((x.out : ↥H) : G) * c⁻¹ with hfdef
  have hf : ∀ x, f x ∈ MulAut.conj c • H := fun x => (hmemH _).mpr (x.out).2
  have hbij : Function.Bijective fun x =>
      (QuotientGroup.mk ⟨f x, hf x⟩ :
        ↥(MulAut.conj c • H) ⧸ (MulAut.conj c • K).subgroupOf (MulAut.conj c • H)) := by
    constructor
    · intro x₁ x₂ hEq
      rw [mk_eq_mk_iff_mem] at hEq
      simp only [hfdef] at hEq
      have hrewrite : (c * ((x₁.out : ↥H) : G) * c⁻¹)⁻¹ * (c * ((x₂.out : ↥H) : G) * c⁻¹)
          = c * (((x₁.out : ↥H) : G)⁻¹ * ((x₂.out : ↥H) : G)) * c⁻¹ := by group
      rw [hrewrite, hmemK] at hEq
      have h := (mk_eq_mk_iff_mem (K := K) (u := x₁.out) (v := x₂.out)).mpr hEq
      simpa only [QuotientGroup.out_eq'] using h
    · intro z
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
      have hw : c⁻¹ * (w : G) * c ∈ H := by
        refine (hmemH _).mp ?_
        have : c * (c⁻¹ * (w : G) * c) * c⁻¹ = (w : G) := by group
        rw [this]; exact w.2
      refine ⟨QuotientGroup.mk ⟨c⁻¹ * (w : G) * c, hw⟩, ?_⟩
      rw [mk_eq_mk_iff_mem]
      have hK : (((QuotientGroup.mk ⟨c⁻¹ * (w : G) * c, hw⟩ :
          ↥H ⧸ K.subgroupOf H).out : ↥H) : G)⁻¹ * (c⁻¹ * (w : G) * c) ∈ K :=
        (mk_eq_mk_iff_mem (K := K)).mp (QuotientGroup.out_eq' _)
      have hrewrite : (f (QuotientGroup.mk ⟨c⁻¹ * (w : G) * c, hw⟩))⁻¹ * (w : G)
          = c * ((((QuotientGroup.mk ⟨c⁻¹ * (w : G) * c, hw⟩ :
              ↥H ⧸ K.subgroupOf H).out : ↥H) : G)⁻¹ * (c⁻¹ * (w : G) * c)) * c⁻¹ := by
        simp only [hfdef]; group
      rw [hrewrite, hmemK]
      exact hK
  rw [← sum_smul_eq_relTrace ha' f hf hbij]
  simp only [hfdef, relTrace, Finset.smul_sum, ← mul_smul, inv_mul_cancel_right]

end DistribMulAction

section Semiring

variable [Semiring A] [MulSemiringAction G A]

/-- `Tr^H_K(1) = [H : K] · 1`. -/
theorem relTrace_one (K H : Subgroup G) : relTrace K H (1 : A) = (K.relIndex H) • (1 : A) := by
  letI := Fintype.ofFinite (↥H ⧸ K.subgroupOf H)
  simp only [relTrace, smul_one, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card]
  rfl

/-- **Projection formula** (right version): `Tr^H_K` is right `A^H`-linear. -/
theorem relTrace_mul_of_fixed {K H : Subgroup G} {b : A} (hb : ∀ g ∈ H, g • b = b) (a : A) :
    relTrace K H (a * b) = relTrace K H a * b := by
  letI := Fintype.ofFinite (↥H ⧸ K.subgroupOf H)
  simp only [relTrace, Finset.sum_mul, smul_mul']
  exact Finset.sum_congr rfl fun x _ => by rw [hb _ (x.out).2]

/-- **Projection formula** (left version): `Tr^H_K` is left `A^H`-linear. -/
theorem mul_relTrace_of_fixed {K H : Subgroup G} {b : A} (hb : ∀ g ∈ H, g • b = b) (a : A) :
    relTrace K H (b * a) = b * relTrace K H a := by
  letI := Fintype.ofFinite (↥H ⧸ K.subgroupOf H)
  simp only [relTrace, Finset.mul_sum, smul_mul']
  exact Finset.sum_congr rfl fun x _ => by rw [hb _ (x.out).2]

/-- **Invertible index criterion.**  If `[H : K] · 1` has an `H`-fixed inverse `v`, then every
`H`-fixed element is a relative trace from `K`, i.e. `A^H_K = A^H`.

Applied with `A` an algebra over a field of characteristic `p` and `p ∤ [H : K]`, this is the
reason a defect group may always be shrunk to a `p`-subgroup. -/
theorem relTrace_mul_eq_self {K H : Subgroup G} {a v : A} (ha : ∀ g ∈ H, g • a = a)
    (hv : ∀ g ∈ H, g • v = v) (hvinv : ((K.relIndex H : ℕ) • (1 : A)) * v = 1) :
    relTrace K H (v * a) = a := by
  have hfix : ∀ g ∈ H, g • (v * a) = v * a := fun g hg => by
    rw [smul_mul', hv g hg, ha g hg]
  have hproj := relTrace_mul_of_fixed (K := K) hfix (1 : A)
  rw [one_mul] at hproj
  rw [hproj, relTrace_one, ← mul_assoc, hvinv, one_mul]

end Semiring

end OddOrder.GAlgebra
