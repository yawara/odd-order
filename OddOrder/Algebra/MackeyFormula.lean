/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Quotient
import OddOrder.Algebra.RelativeTrace

/-!
# Mackey's formula for relative traces

Restricting a relative trace `Tr^G_L` to a subgroup `K` breaks it up over the `K`-`L` double
cosets:

`Tr^G_L (a) = ∑_{g ∈ [K \ G / L]} Tr^K_{K ∩ ᵍL} (g · a)`.

The proof is the orbit decomposition of `G ⧸ L` under the left action of `K`: the orbit of the
coset `gL` is indexed by `K ⧸ (K ∩ ᵍL)`, because that intersection is exactly the stabiliser
(`smul_mk_eq_iff_mem_inf_conj`).

Together with `relTraceIdeal_mono` and the projection formula this gives
`A^G_D · A^G_{D'} ⊆ ∑_g A^G_{D ∩ ᵍD'}`, which (with Rosenberg's lemma) is what forces the defect
groups of a block to form a single conjugacy class.

## Main results

* `OddOrder.GAlgebra.smul_mk_eq_iff_mem_inf_conj` — the stabiliser of `gL` in `K` is `K ∩ ᵍL`.
* `OddOrder.GAlgebra.exists_mackey` — Mackey's formula, with the double-coset representatives
  produced as a `Finset G`.
-/

namespace OddOrder.GAlgebra

open MulAction

variable {G : Type*} [Group G] [Finite G] {A : Type*}

section DistribMulAction

variable [AddCommMonoid A] [DistribMulAction G A]

omit [Finite G] in
/-- Two group elements in the same left coset of `L` act identically on an `L`-fixed element. -/
theorem smul_eq_smul_of_mk_eq_mk {L : Subgroup G} {a : A} (ha : ∀ g ∈ L, g • a = a) {u v : G}
    (h : (QuotientGroup.mk u : G ⧸ L) = QuotientGroup.mk v) : u • a = v • a := by
  have hmem : u⁻¹ * v ∈ L := QuotientGroup.eq.mp h
  calc u • a = u • ((u⁻¹ * v) • a) := by rw [ha _ hmem]
    _ = v • a := by rw [← mul_smul, mul_inv_cancel_left]

open scoped Pointwise in
omit [Finite G] in
/-- **The stabiliser of the coset `gL` under left multiplication by `K` is `K ∩ ᵍL`.** -/
theorem smul_mk_eq_iff_mem_inf_conj (K L : Subgroup G) (g : G) (u : ↥K) :
    u • (QuotientGroup.mk g : G ⧸ L) = QuotientGroup.mk g
      ↔ u ∈ (K ⊓ MulAut.conj g • L).subgroupOf K := by
  have hact : u • (QuotientGroup.mk g : G ⧸ L) = QuotientGroup.mk ((u : G) * g) := rfl
  have hconj : ∀ y : G, ((MulAut.conj g)⁻¹ • y : G) = g⁻¹ * y * g := fun _ => rfl
  rw [hact, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hconj, QuotientGroup.eq]
  constructor
  · intro h
    refine ⟨u.2, ?_⟩
    have h' : g⁻¹ * (u : G)⁻¹ * g ∈ L := by
      have heq : ((u : G) * g)⁻¹ * g = g⁻¹ * (u : G)⁻¹ * g := by group
      rwa [heq] at h
    have hinv := L.inv_mem h'
    have heq2 : (g⁻¹ * (u : G)⁻¹ * g)⁻¹ = g⁻¹ * (u : G) * g := by group
    rwa [heq2] at hinv
  · rintro ⟨-, h⟩
    have hinv := L.inv_mem h
    have heq : (g⁻¹ * (u : G) * g)⁻¹ = ((u : G) * g)⁻¹ * g := by group
    rwa [heq] at hinv

open scoped Pointwise in
/-- **Mackey's formula.**  The relative trace from `L`, viewed inside `K`, is the sum of the
relative traces from the intersections `K ∩ ᵍL`, over a set of `K`-`L` double coset
representatives. -/
theorem exists_mackey (K : Subgroup G) {L : Subgroup G} {a : A} (ha : ∀ g ∈ L, g • a = a) :
    ∃ s : Finset G,
      relTrace L ⊤ a = ∑ g ∈ s, relTrace (K ⊓ MulAut.conj g • L) K (g • a) := by
  classical
  letI := Fintype.ofFinite (G ⧸ L)
  letI : Fintype (orbitRel.Quotient ↥K (G ⧸ L)) := Fintype.ofFinite _
  set Ω := orbitRel.Quotient ↥K (G ⧸ L) with hΩ
  set rep : Ω → G := fun ω => ((ω.out : G ⧸ L).out : G) with hrep
  set D : Ω → Subgroup G := fun ω => K ⊓ MulAut.conj (rep ω) • L with hD
  letI : ∀ ω : Ω, Fintype (↥K ⧸ (D ω).subgroupOf K) := fun _ => Fintype.ofFinite _
  have hmk : ∀ ω : Ω, (QuotientGroup.mk (rep ω) : G ⧸ L) = ω.out := fun ω =>
    QuotientGroup.out_eq' _
  -- Orbits of `K` on `G ⧸ L` are indexed by `Ω`, and each is a copy of `K ⧸ (K ∩ ᵍL)`.
  have horb : ∀ (ω : Ω) (k : ↥K), (Quotient.mk'' (k • (ω.out : G ⧸ L)) : Ω) = ω := by
    intro ω k
    have hstep : (Quotient.mk'' (k • (ω.out : G ⧸ L)) : Ω)
        = Quotient.mk'' (ω.out : G ⧸ L) :=
      Quotient.sound' (orbitRel_apply.mpr ⟨k, rfl⟩)
    rw [hstep, Quotient.out_eq']
  set Φ : (Σ ω : Ω, ↥K ⧸ (D ω).subgroupOf K) → G ⧸ L :=
    fun p => (p.2.out : ↥K) • (p.1.out : G ⧸ L) with hΦ
  have hΦbij : Function.Bijective Φ := by
    constructor
    · rintro ⟨ω₁, k₁⟩ ⟨ω₂, k₂⟩ heq
      simp only [hΦ] at heq
      have hω : ω₁ = ω₂ := by
        rw [← horb ω₁ k₁.out, ← horb ω₂ k₂.out, heq]
      subst hω
      have hstab : (k₁.out⁻¹ * k₂.out) • (ω₁.out : G ⧸ L) = ω₁.out := by
        rw [mul_smul, ← heq, inv_smul_smul]
      rw [← hmk ω₁] at hstab
      have hmem := (smul_mk_eq_iff_mem_inf_conj K L (rep ω₁) _).mp hstab
      have hq : (QuotientGroup.mk k₁.out : ↥K ⧸ (D ω₁).subgroupOf K)
          = QuotientGroup.mk k₂.out := QuotientGroup.eq.mpr hmem
      have hk : k₁ = k₂ := by simpa only [QuotientGroup.out_eq'] using hq
      rw [hk]
    · intro x
      set ω : Ω := Quotient.mk'' x with hω
      have hxorb : x ∈ orbit ↥K (ω.out : G ⧸ L) := by
        rw [← orbitRel_apply]
        exact Quotient.exact' (hω.symm.trans (Quotient.out_eq' ω).symm)
      obtain ⟨u, hu⟩ := hxorb
      refine ⟨⟨ω, QuotientGroup.mk u⟩, ?_⟩
      simp only [hΦ]
      set k₀ : ↥K := (QuotientGroup.mk u : ↥K ⧸ (D ω).subgroupOf K).out with hk₀
      have hq : (QuotientGroup.mk k₀ : ↥K ⧸ (D ω).subgroupOf K) = QuotientGroup.mk u := by
        rw [hk₀, QuotientGroup.out_eq']
      have hmem : k₀⁻¹ * u ∈ (D ω).subgroupOf K := QuotientGroup.eq.mp hq
      have hstab : (k₀⁻¹ * u) • (QuotientGroup.mk (rep ω) : G ⧸ L) = QuotientGroup.mk (rep ω) :=
        (smul_mk_eq_iff_mem_inf_conj K L (rep ω) _).mpr hmem
      rw [hmk ω, mul_smul] at hstab
      have hkey : k₀ • (ω.out : G ⧸ L) = u • (ω.out : G ⧸ L) := by
        conv_lhs => rw [← hstab]
        rw [smul_inv_smul]
      change k₀ • (ω.out : G ⧸ L) = x
      rw [hkey]
      exact hu
  -- Reindex and split.
  refine ⟨Finset.univ.image rep, ?_⟩
  have hrepinj : ∀ ω₁ ∈ (Finset.univ : Finset Ω), ∀ ω₂ ∈ (Finset.univ : Finset Ω),
      rep ω₁ = rep ω₂ → ω₁ = ω₂ := by
    intro ω₁ _ ω₂ _ h
    exact Quotient.out_injective (Quotient.out_injective h)
  rw [Finset.sum_image hrepinj]
  have hL : relTrace L ⊤ a = ∑ x : G ⧸ L, ((x.out : G)) • a :=
    (sum_out_smul_eq_relTrace_top ha).symm
  rw [hL, ← Fintype.sum_bijective Φ hΦbij (fun p => (((Φ p).out : G)) • a)
    (fun x : G ⧸ L => ((x.out : G)) • a) fun _ => rfl, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hR : relTrace (D ω) K (rep ω • a)
      = ∑ k : ↥K ⧸ (D ω).subgroupOf K, ((k.out : ↥K) : G) • (rep ω • a) := rfl
  rw [hR]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_smul]
  refine smul_eq_smul_of_mk_eq_mk ha ?_
  rw [QuotientGroup.out_eq']
  change (((⟨ω, k⟩ : Σ ω : Ω, ↥K ⧸ (D ω).subgroupOf K).2.out : ↥K) • (ω.out : G ⧸ L))
    = QuotientGroup.mk (((k.out : ↥K) : G) * rep ω)
  rw [← hmk ω]
  rfl

end DistribMulAction

section Ring

variable [Ring A] [MulSemiringAction G A]

open scoped Pointwise in
/-- **The product of two trace ideals lies in the sum of the trace ideals of the
intersections**: `A^G_D · A^G_{D'} ⊆ ∑_g A^G_{D ∩ ᵍD'}`.

This is Mackey's formula combined with the projection formula and transitivity.  With Rosenberg's
lemma it is what forces the defect groups of a block to form a single conjugacy class. -/
theorem exists_mul_eq_sum_relTraceIdeal_inf {D D' : Subgroup G} {x y : A}
    (hx : x ∈ relTraceIdeal D ⊤) (hy : y ∈ relTraceIdeal D' ⊤) :
    ∃ (s : Finset G) (c : G → A),
      (∀ g ∈ s, c g ∈ relTraceIdeal (D ⊓ MulAut.conj g • D') ⊤) ∧ x * y = ∑ g ∈ s, c g := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨s, hs⟩ := exists_mackey D hv
  have hfix : ∀ g : G, ∀ w ∈ D ⊓ MulAut.conj g • D', w • (u * (g • v)) = u * (g • v) := by
    intro g w hw
    obtain ⟨hwD, hwD'⟩ := Subgroup.mem_inf.mp hw
    rw [smul_mul', hu w hwD, forall_conj_smul_eq hv g w hwD']
  refine ⟨s, fun g => relTrace (D ⊓ MulAut.conj g • D') ⊤ (u * (g • v)),
    fun g _ => ⟨u * (g • v), hfix g, rfl⟩, ?_⟩
  have hyfix : ∀ w ∈ (⊤ : Subgroup G), w • relTrace D' ⊤ v = relTrace D' ⊤ v :=
    fun w _ => smul_relTrace hv (Subgroup.mem_top w)
  rw [← relTrace_mul_of_fixed hyfix u, hs, Finset.mul_sum,
    Finset.sum_congr rfl fun g _ => (mul_relTrace_of_fixed hu (g • v)).symm,
    ← relTraceHom_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [relTraceHom_apply]
  exact relTrace_trans inf_le_left le_top (hfix g)

end Ring

end OddOrder.GAlgebra
