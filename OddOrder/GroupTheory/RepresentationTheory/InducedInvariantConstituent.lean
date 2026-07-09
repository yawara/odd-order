/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.GroupTheory.RepresentationTheory.GallagherDecomposition
import OddOrder.GroupTheory.RepresentationTheory.CliffordSingleOrbit
import OddOrder.GroupTheory.RepresentationTheory.CliffordCorrespondence

/-!
# The general Peterfalvi (1.7.b): equal-degree induced constituents (abelian inertia quotient)

For a normal subgroup `H ⊴ K` with `K/H` **abelian** and a `K`-invariant `θ ∈ Irr H`, the
irreducible constituents of `Ind_H^K θ` all share the common degree `ψ(1) = e·θ(1)` (where `ψ` is any
one constituent and `e = ⟨Res ψ, θ⟩`).  This is Peterfalvi (1.7.b) at the inertia group
`T = I_K(θ)` (where `θ` is invariant); **no coprimality** is assumed, so it applies where the
coprime Gallagher decomposition (`induce_eq_sum_mul_linearClassFunction`) does not — in particular at
the `H'/H` level of Peterfalvi (12.5), where `K/H = H/H'` is abelian automatically (`H' = [H,H]`) but
`|H'|` and `[H:H']` share prime divisors.

The proof assembles the bottom-up chain:
* `induce_restrict_mul` — projection formula `Ind_H^K(Res_H φ · χ) = φ · Ind_H^K χ`;
* `induce_trivial_eq_sum_linearClassFunction` — `Ind_H^K 1_H = ∑_β Inf(β)`;
* `induce_restrict_eq_mul_sum_linearClassFunction` — `Ind_H^K(Res ψ) = ψ · ∑_β Inf(β)`;
* `restrict_eq_restrictionMultiplicity_smul_of_invariant` — `Res_H ψ = e · θ` (Clifford, invariant).

Here `induce_smul_eq_mul_sum_of_invariant` combines the last two into
`e · Ind_H^K θ = ψ · ∑_β Inf(β)`, exhibiting the constituents `ψ·Inf(β)` (all of degree `ψ(1)`).
-/

namespace OddOrder.RepresentationTheory

open scoped commutatorElement

variable {K : Type*} [Group K] {H : Subgroup K} [hH : H.Normal]

open scoped commutatorElement in
/-- **Peterfalvi (1.7.b), the invariant-constituent decomposition.**  For `H ⊴ K` with `K/H` abelian
and a `K`-invariant `θ ∈ Irr H`, if `ψ ∈ Irr K` lies over `θ` then
`e · Ind_H^K θ = ψ · ∑_β Inf(β)`, where `e = ⟨Res ψ, θ⟩` and `β` ranges over `Hom(K/H, ℂˣ)`.

Combines `induce_restrict_eq_mul_sum_linearClassFunction` (`Ind_H^K(Res ψ) = ψ·∑_β Inf(β)`) with the
invariant Clifford restriction `restrict_eq_restrictionMultiplicity_smul_of_invariant`
(`Res_H ψ = e·θ`), pushing the scalar through `Ind` (`induce_smul`).  The right side displays the
irreducible constituents `ψ·Inf(β)` of `Ind_H^K θ`, each of degree `ψ(1)`. -/
theorem induce_smul_eq_mul_sum_of_invariant [Finite K] [Fintype K] [Fintype ↥H]
    [Invertible (Nat.card K : ℂ)] [Invertible (Nat.card ↥H : ℂ)]
    [Fintype (IrreducibleCharacter ↥H)] [Fintype ((K ⧸ H) →* ℂˣ)]
    (hab : ∀ x y : K, ⁅x, y⁆ ∈ H)
    (θ : IrreducibleCharacter ↥H) (ψ : IrreducibleCharacter K)
    (hover : IrreducibleCharacter.LiesOver H ψ θ) (hinv : ∀ g : K, IrreducibleCharacter.conjBy g θ = θ) :
    ClassFunction.restrictionMultiplicity H (ψ : ClassFunction K ℂ) (θ : ClassFunction ↥H ℂ) •
        ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
      = (ψ : ClassFunction K ℂ) *
          ∑ β : (K ⧸ H) →* ℂˣ, linearClassFunction (β.comp (QuotientGroup.mk' H)) := by
  have h3 := induce_restrict_eq_mul_sum_linearClassFunction hab (ψ : ClassFunction K ℂ)
  have h4 := restrict_eq_restrictionMultiplicity_smul_of_invariant ψ θ hover hinv
  rw [h4, ClassFunction.induce_smul] at h3
  exact h3

open scoped commutatorElement in
/-- **The general Peterfalvi (1.7.b): equal-degree induced constituents.**  For `H ⊴ K` with `K/H`
abelian and a `K`-invariant `θ ∈ Irr H`, every irreducible constituent `φ` of `Ind_H^K θ` has the
common degree `φ(1) = ψ(1)`, where `ψ` is any fixed constituent.

By `induce_smul_eq_mul_sum_of_invariant`, `e·Ind_H^K θ = ∑_β ψ·Inf(β)` (distributing
`ClassFunction.mul_sum`), whose summands `ψ·Inf(β)` are irreducible
(`isIrreducibleCharacter_mul_linearClassFunction`).  Taking `⟨·, φ⟩` and using orthonormality of
irreducibles, `e·⟨Ind θ, φ⟩ = #{β : ψ·Inf(β) = φ}`; since `φ` is a constituent (`⟨Ind θ, φ⟩ ≠ 0`)
and `e = ⟨Res ψ, θ⟩ ≠ 0` (`ψ` over `θ`), some `β` has `φ = ψ·Inf(β)`, so
`φ(1) = ψ(1)·Inf(β)(1) = ψ(1)`.  No coprimality is used, so this applies at the `H'/H` level of
Peterfalvi (12.5) where the coprime Gallagher decomposition does not. -/
theorem induce_invariant_constituent_apply_one_eq [Finite K] [Fintype K] [Fintype ↥H]
    [Invertible (Nat.card K : ℂ)] [Invertible (Nat.card ↥H : ℂ)]
    [Fintype (IrreducibleCharacter ↥H)] [Fintype ((K ⧸ H) →* ℂˣ)]
    (hab : ∀ x y : K, ⁅x, y⁆ ∈ H)
    (θ : IrreducibleCharacter ↥H) (ψ : IrreducibleCharacter K)
    (hover : IrreducibleCharacter.LiesOver H ψ θ)
    (hinv : ∀ g : K, IrreducibleCharacter.conjBy g θ = θ)
    (φ : IrreducibleCharacter K)
    (hφ : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
        (φ : ClassFunction K ℂ) ≠ 0) :
    (φ : ClassFunction K ℂ) (1 : K) = (ψ : ClassFunction K ℂ) (1 : K) := by
  classical
  -- The irreducible twists `ψ·Inf(β)`, bundled.
  set Φ : ((K ⧸ H) →* ℂˣ) → IrreducibleCharacter K := fun β =>
    ⟨(ψ : ClassFunction K ℂ) * linearClassFunction (β.comp (QuotientGroup.mk' H)),
      isIrreducibleCharacter_mul_linearClassFunction ψ.isIrreducible _⟩ with hΦ
  -- `e · Ind_H^K θ = ∑_β (Φ β)`.
  have h5a := induce_smul_eq_mul_sum_of_invariant hab θ ψ hover hinv
  rw [ClassFunction.mul_sum] at h5a
  -- Pair with `φ`: `e · ⟨Ind θ, φ⟩ = ∑_β [Φ β = φ]`.
  have hkey : ClassFunction.restrictionMultiplicity H (ψ : ClassFunction K ℂ)
        (θ : ClassFunction ↥H ℂ)
        * ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) (φ : ClassFunction K ℂ)
      = ∑ β : (K ⧸ H) →* ℂˣ, (if Φ β = φ then (1 : ℂ) else 0) := by
    rw [← ClassFunction.inner_smul_left, h5a, inner_sum_left]
    refine Finset.sum_congr rfl fun β _ => ?_
    have := irreducibleCharacter_inner (Φ β) φ
    simpa [hΦ] using this
  -- `e ≠ 0` (`ψ` lies over `θ`) and `⟨Ind θ, φ⟩ ≠ 0`, so the sum of indicators is nonzero.
  have he : ClassFunction.restrictionMultiplicity H (ψ : ClassFunction K ℂ)
      (θ : ClassFunction ↥H ℂ) ≠ 0 := hover
  have hsum_ne : (∑ β : (K ⧸ H) →* ℂˣ, (if Φ β = φ then (1 : ℂ) else 0)) ≠ 0 := by
    rw [← hkey]; exact mul_ne_zero he hφ
  obtain ⟨β, _, hβ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hΦβ : Φ β = φ := by by_contra h; rw [if_neg h] at hβ; exact hβ rfl
  -- Read off the degree: `φ(1) = (ψ·Inf β)(1) = ψ(1) · 1 = ψ(1)`.
  have hcoe : (φ : ClassFunction K ℂ)
      = (ψ : ClassFunction K ℂ) * linearClassFunction (β.comp (QuotientGroup.mk' H)) := by
    rw [← hΦβ]
  rw [hcoe, ClassFunction.mul_apply, linearClassFunction_apply, map_one, Units.val_one, mul_one]

open scoped commutatorElement in
/-- **Peterfalvi (1.7.b), lifted to the full group via the Clifford correspondence.**  For `N ⊴ L`
with `θ ∈ Irr N`, inertia `T = I_L(θ)`, and `T/N` abelian, the induced character `Ind_N^L θ`
decomposes (scaled by `e = ⟨Res_T ψ, θ'⟩` for a `T`-constituent `ψ`) as
`e · Ind_N^L θ = ∑_β Ind_T^L(ψ·Inf(β))`, each summand irreducible of degree `[L:T]·ψ(1)`.

Combines induction in stages (`induce_induce_subgroupOf`, `Ind_N^L θ = Ind_T^L(Ind_N^T θ')`) with the
inertia-level general (1.7.b) decomposition `induce_smul_eq_mul_sum_of_invariant`
(`e·Ind_N^T θ' = ψ·∑_β Inf(β)`, valid since `θ'` is `T`-invariant as `T = I_L(θ)` and `T/N` is
abelian), pushing `Ind_T^L` through the scalar (`induce_smul`), the product-sum
(`ClassFunction.mul_sum`), and the sum (`induce_sum`).  The general (no-coprimality) analog of
`exists_extension_induce_eq_sum_induce_mul`, using a constituent `ψ` (with factor `e`) in place of an
extension `χ`.  Feeds the `H'/H`-level equal-degree that Peterfalvi (12.5) needs. -/
theorem induce_smul_eq_sum_induce_mul_of_invariant_inertia
    {L : Type*} [Group L] [Finite L] [Fintype L] [Invertible (Nat.card L : ℂ)]
    {N T : Subgroup L} [N.Normal] [(N.subgroupOf T).Normal] (hNT : N ≤ T)
    [Fintype ↥N] [Fintype ↥T] [Fintype ↥(N.subgroupOf T)]
    [Invertible (Nat.card ↥N : ℂ)] [Invertible (Nat.card ↥T : ℂ)]
    [Invertible (Nat.card ↥(N.subgroupOf T) : ℂ)]
    [Fintype (IrreducibleCharacter ↥(N.subgroupOf T))] [Fintype ((↥T ⧸ N.subgroupOf T) →* ℂˣ)]
    (hab : ∀ x y : ↥T, ⁅x, y⁆ ∈ N.subgroupOf T)
    (θ : IrreducibleCharacter ↥N)
    (hinertia : ClassFunction.inertia (G := L) (θ : ClassFunction ↥N ℂ) = T)
    (ψ : IrreducibleCharacter ↥T)
    (hover : IrreducibleCharacter.LiesOver (N.subgroupOf T) ψ
      (⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hNT).toMonoidHom
          (θ : ClassFunction ↥N ℂ),
        IsIrreducibleCharacter.compHom_of_surjective
          (Subgroup.subgroupOfEquivOfLe hNT).surjective θ.isIrreducible⟩ :
        IrreducibleCharacter ↥(N.subgroupOf T))) :
    ClassFunction.restrictionMultiplicity (N.subgroupOf T) (ψ : ClassFunction ↥T ℂ)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hNT).toMonoidHom
          (θ : ClassFunction ↥N ℂ))
      • ClassFunction.induce N (θ : ClassFunction ↥N ℂ)
      = ∑ β : (↥T ⧸ N.subgroupOf T) →* ℂˣ,
          ClassFunction.induce T ((ψ : ClassFunction ↥T ℂ) *
            linearClassFunction (β.comp (QuotientGroup.mk' (N.subgroupOf T)))) := by
  classical
  set θ' : IrreducibleCharacter ↥(N.subgroupOf T) :=
    ⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hNT).toMonoidHom
        (θ : ClassFunction ↥N ℂ),
      IsIrreducibleCharacter.compHom_of_surjective
        (Subgroup.subgroupOfEquivOfLe hNT).surjective θ.isIrreducible⟩ with hθ'
  -- `θ` is `T`-invariant (as `T = I_L(θ)`), transported to `θ'` on `N.subgroupOf T`.
  have hinvT : ∀ t : ↥T, ClassFunction.conjBy ((t : L)) (θ : ClassFunction ↥N ℂ)
      = (θ : ClassFunction ↥N ℂ) := fun t => by
    have hmem : (t : L) ∈ ClassFunction.inertia (G := L) (θ : ClassFunction ↥N ℂ) := by
      rw [hinertia]; exact t.2
    exact (ClassFunction.mem_inertia).mp hmem
  have hinertia' : ClassFunction.inertia (G := ↥T)
      (θ' : ClassFunction ↥(N.subgroupOf T) ℂ) = ⊤ :=
    inertia_compHom_subgroupOfEquivOfLe_eq_top hNT hinvT
  have hinv' : ∀ y : ↥T, IrreducibleCharacter.conjBy y θ' = θ' := fun y => by
    apply IrreducibleCharacter.ext
    rw [IrreducibleCharacter.coe_conjBy]
    have hmem : y ∈ ClassFunction.inertia (G := ↥T)
        (θ' : ClassFunction ↥(N.subgroupOf T) ℂ) := by
      rw [hinertia']; exact Subgroup.mem_top y
    exact (ClassFunction.mem_inertia).mp hmem
  -- Inertia-level general (1.7.b): `e · Ind_N^T θ' = ψ · ∑_β Inf(β)`.
  have h5a := induce_smul_eq_mul_sum_of_invariant (K := ↥T) (H := N.subgroupOf T) hab θ' ψ hover hinv'
  -- Induction in stages: `Ind_T^L(Ind_N^T θ') = Ind_N^L θ`.
  have hstages := induce_induce_subgroupOf (M := L) hNT (θ : ClassFunction ↥N ℂ)
  have hcoe' : (θ' : ClassFunction ↥(N.subgroupOf T) ℂ)
      = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hNT).toMonoidHom
          (θ : ClassFunction ↥N ℂ) := rfl
  rw [← hstages, ← ClassFunction.induce_smul, ← hcoe', h5a, ClassFunction.mul_sum,
    ClassFunction.induce_sum]

open scoped commutatorElement in
/-- **The induced block sum vanishes off the normal subgroup** (Peterfalvi (12.5) `DpsiH`
block-vanishing).  For `N ⊴ L`, inertia `T = I_L(θ)`, `T/N` abelian, the induced-block sum
`∑_β Ind_T^L(ψ·Inf β)` (the `e`-scaled constituent sum of `Ind_N^L θ`) vanishes at every `g ∉ N`:
it equals `e·Ind_N^L θ` (`induce_smul_eq_sum_induce_mul_of_invariant_inertia`), and `Ind_N^L θ`
vanishes off the normal `N` (`induce_apply_eq_zero_of_not_mem_normal`).  Each `λ ≠ 1` block of the
(12.5) `DpsiH` regrouping is a `c_λ`-multiple of such a sum, so vanishes on `H − H'`. -/
theorem sum_induce_mul_apply_eq_zero_of_not_mem_normal
    {L : Type*} [Group L] [Finite L] [Fintype L] [Invertible (Nat.card L : ℂ)]
    {N T : Subgroup L} [N.Normal] [(N.subgroupOf T).Normal] (hNT : N ≤ T)
    [Fintype ↥N] [Fintype ↥T] [Fintype ↥(N.subgroupOf T)]
    [Invertible (Nat.card ↥N : ℂ)] [Invertible (Nat.card ↥T : ℂ)]
    [Invertible (Nat.card ↥(N.subgroupOf T) : ℂ)]
    [Fintype (IrreducibleCharacter ↥(N.subgroupOf T))] [Fintype ((↥T ⧸ N.subgroupOf T) →* ℂˣ)]
    (hab : ∀ x y : ↥T, ⁅x, y⁆ ∈ N.subgroupOf T)
    (θ : IrreducibleCharacter ↥N)
    (hinertia : ClassFunction.inertia (G := L) (θ : ClassFunction ↥N ℂ) = T)
    (ψ : IrreducibleCharacter ↥T)
    (hover : IrreducibleCharacter.LiesOver (N.subgroupOf T) ψ
      (⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hNT).toMonoidHom
          (θ : ClassFunction ↥N ℂ),
        IsIrreducibleCharacter.compHom_of_surjective
          (Subgroup.subgroupOfEquivOfLe hNT).surjective θ.isIrreducible⟩ :
        IrreducibleCharacter ↥(N.subgroupOf T)))
    {g : L} (hg : g ∉ N) :
    (∑ β : (↥T ⧸ N.subgroupOf T) →* ℂˣ,
        ClassFunction.induce T ((ψ : ClassFunction ↥T ℂ) *
          linearClassFunction (β.comp (QuotientGroup.mk' (N.subgroupOf T))))) g = 0 := by
  rw [← induce_smul_eq_sum_induce_mul_of_invariant_inertia hNT hab θ hinertia ψ hover,
    ClassFunction.smul_apply,
    ClassFunction.induce_apply_eq_zero_of_not_mem_normal N (θ : ClassFunction ↥N ℂ) hg, mul_zero]

open scoped commutatorElement in
/-- **The general Peterfalvi (1.7.b): H-level equal degree** (the fact (12.5) consumes).  For `N ⊴ L`
with inertia `T = I_L(θ)`, `T/N` abelian, and a `T`-constituent `ψ` over `θ'`, every irreducible
constituent `φ` of `Ind_N^L θ` has degree `φ(1) = [L:T]·ψ(1)`.

From `induce_smul_eq_sum_induce_mul_of_invariant_inertia`, `e·Ind_N^L θ = ∑_β Ind_T^L(ψ·Inf β)`,
whose summands are irreducible (`isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq`, since
`Res(ψ·Inf β) = Res ψ` lies over `θ'`).  Pairing with `φ` and using orthonormality,
`e·⟨Ind θ, φ⟩ = #{β : Ind_T(ψ·Inf β) = φ}`; `φ` a constituent and `e ≠ 0` force
`φ = Ind_T(ψ·Inf β)`, of degree `[L:T]·(ψ·Inf β)(1) = [L:T]·ψ(1)` (`induce_apply_one`).  As two
constituents share this common value, `Ind_N^L θ` has equal-degree constituents — with the
abelian-quotient inertia, no coprimality — as Peterfalvi (12.5) needs at `H'/H`. -/
theorem induce_inertia_constituent_apply_one_eq
    {L : Type*} [Group L] [Finite L] [Fintype L] [Invertible (Nat.card L : ℂ)]
    {N T : Subgroup L} [N.Normal] [(N.subgroupOf T).Normal] (hNT : N ≤ T)
    [Fintype ↥N] [Fintype ↥T] [Fintype ↥(N.subgroupOf T)]
    [Invertible (Nat.card ↥N : ℂ)] [Invertible (Nat.card ↥T : ℂ)]
    [Invertible (Nat.card ↥(N.subgroupOf T) : ℂ)]
    [Fintype (IrreducibleCharacter ↥(N.subgroupOf T))] [Fintype ((↥T ⧸ N.subgroupOf T) →* ℂˣ)]
    (hab : ∀ x y : ↥T, ⁅x, y⁆ ∈ N.subgroupOf T)
    (θ : IrreducibleCharacter ↥N)
    (hinertia : ClassFunction.inertia (G := L) (θ : ClassFunction ↥N ℂ) = T)
    (ψ : IrreducibleCharacter ↥T)
    (hover : ClassFunction.restrictionMultiplicity (N.subgroupOf T) (ψ : ClassFunction ↥T ℂ)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hNT).toMonoidHom
          (θ : ClassFunction ↥N ℂ)) ≠ 0)
    (φ : IrreducibleCharacter L)
    (hφ : ClassFunction.inner (ClassFunction.induce N (θ : ClassFunction ↥N ℂ))
        (φ : ClassFunction L ℂ) ≠ 0) :
    (φ : ClassFunction L ℂ) (1 : L) = (T.index : ℂ) * (ψ : ClassFunction ↥T ℂ) (1 : ↥T) := by
  classical
  set θ'cf : ClassFunction ↥(N.subgroupOf T) ℂ :=
    ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hNT).toMonoidHom
      (θ : ClassFunction ↥N ℂ) with hθ'cf
  -- Each twist `ψ·Inf(β)` lies over `θ'` (its restriction to `N.subgroupOf T` is `Res ψ`).
  have hoverβ : ∀ β : (↥T ⧸ N.subgroupOf T) →* ℂˣ,
      ClassFunction.restrictionMultiplicity (N.subgroupOf T)
        ((ψ : ClassFunction ↥T ℂ) * linearClassFunction (β.comp (QuotientGroup.mk' (N.subgroupOf T))))
        θ'cf ≠ 0 := by
    intro β
    rw [ClassFunction.restrictionMultiplicity_def,
      ClassFunction.restrict_mul_of_apply_eq_one (ψ : ClassFunction ↥T ℂ) _
        (fun x => linearClassFunction_comp_mk'_apply_eq_one β x.2),
      ← ClassFunction.restrictionMultiplicity_def]
    exact hover
  -- The irreducible constituents `Φ β = Ind_T^L(ψ·Inf β)`, bundled.
  set Φ : ((↥T ⧸ N.subgroupOf T) →* ℂˣ) → IrreducibleCharacter L := fun β =>
    ⟨ClassFunction.induce T ((ψ : ClassFunction ↥T ℂ) *
        linearClassFunction (β.comp (QuotientGroup.mk' (N.subgroupOf T)))),
      isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq (G := L) hNT θ.isIrreducible
        hinertia
        (⟨(ψ : ClassFunction ↥T ℂ) *
            linearClassFunction (β.comp (QuotientGroup.mk' (N.subgroupOf T))),
          isIrreducibleCharacter_mul_linearClassFunction ψ.isIrreducible _⟩ :
          IrreducibleCharacter ↥T)
        (hoverβ β)⟩ with hΦ
  have hlift := induce_smul_eq_sum_induce_mul_of_invariant_inertia hNT hab θ hinertia ψ hover
  -- Pair with `φ`.
  have hkey : ClassFunction.restrictionMultiplicity (N.subgroupOf T) (ψ : ClassFunction ↥T ℂ) θ'cf
        * ClassFunction.inner (ClassFunction.induce N (θ : ClassFunction ↥N ℂ)) (φ : ClassFunction L ℂ)
      = ∑ β : (↥T ⧸ N.subgroupOf T) →* ℂˣ, (if Φ β = φ then (1 : ℂ) else 0) := by
    rw [← ClassFunction.inner_smul_left, hlift, inner_sum_left]
    refine Finset.sum_congr rfl fun β _ => ?_
    simpa using irreducibleCharacter_inner (Φ β) φ
  have hsum_ne : (∑ β : (↥T ⧸ N.subgroupOf T) →* ℂˣ, (if Φ β = φ then (1 : ℂ) else 0)) ≠ 0 := by
    rw [← hkey]; exact mul_ne_zero hover hφ
  obtain ⟨β, _, hβ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hΦβ : Φ β = φ := by by_contra h; rw [if_neg h] at hβ; exact hβ rfl
  have hcoe : (φ : ClassFunction L ℂ) = ClassFunction.induce T ((ψ : ClassFunction ↥T ℂ) *
      linearClassFunction (β.comp (QuotientGroup.mk' (N.subgroupOf T)))) := by rw [← hΦβ]
  rw [hcoe, ClassFunction.induce_apply_one, ClassFunction.mul_apply, linearClassFunction_apply,
    map_one, Units.val_one, mul_one]

/-- **Equal-degree constituents of `Ind_N^H λ` have equal multiplicity in it.**  Lifts
`restrictionMultiplicity_eq_of_liesOver_of_apply_one_eq` through
`inner_induce_coe_eq_restrictionMultiplicity` (`⟨Ind_N λ, φ⟩ = restrictionMultiplicity N φ λ`).  For
`N ⊴ H`, `λ ∈ Irr N` and constituents `φ₁, φ₂` of `Ind_N^H λ` (both lying over `λ`) with equal degree
`φ₁(1) = φ₂(1)`, `⟨Ind_N λ, φ₁⟩ = ⟨Ind_N λ, φ₂⟩`.  Combined with the general (1.7.b) equal degree of
*all* constituents, this is the **common multiplicity `e`** of the Peterfalvi (12.5) `DpsiH` block
`Ind_N λ = e·∑_{φ constituent} φ`. -/
theorem inner_induce_constituent_eq_of_apply_one_eq {H : Type*} [Group H]
    [Fintype H] [Invertible (Nat.card H : ℂ)]
    {N : Subgroup H} [hN : N.Normal] [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    [Fintype (IrreducibleCharacter ↥N)]
    {φ₁ φ₂ : IrreducibleCharacter H} {ρ : IrreducibleCharacter ↥N}
    (h₁ : IrreducibleCharacter.LiesOver (G := H) (H := N) φ₁ ρ)
    (h₂ : IrreducibleCharacter.LiesOver (G := H) (H := N) φ₂ ρ)
    (hdeg : (φ₁ : ClassFunction H ℂ) 1 = (φ₂ : ClassFunction H ℂ) 1) :
    ClassFunction.inner (ClassFunction.induce N (ρ : ClassFunction ↥N ℂ)) (φ₁ : ClassFunction H ℂ)
      = ClassFunction.inner (ClassFunction.induce N (ρ : ClassFunction ↥N ℂ))
          (φ₂ : ClassFunction H ℂ) := by
  rw [inner_induce_coe_eq_restrictionMultiplicity, inner_induce_coe_eq_restrictionMultiplicity]
  exact restrictionMultiplicity_eq_of_liesOver_of_apply_one_eq h₁ h₂ hdeg

open scoped Classical in
/-- **Peterfalvi (12.5) core: block-constant coefficients ⟹ constant off `H`.**  For `H ⊴ G` and
`g ∈ CF(G)`, suppose within each `Ind_H^G ρ`-block (`ρ ∈ Irr H`) the inner products `⟨g, θ⟩` agree
across the *non-trivial* constituents (`hcoeff`), and the multiplicities `⟨Ind_H ρ, θ⟩` agree across
*all* constituents (`hmult`, the common `e`).  Then `g` is constant off `H`: `g x = g y` for
`x, y ∉ H`.

Proof (the `DpsiH` decomposition of Peterfalvi (12.5)): Fourier `g = ∑_θ ⟨g,θ⟩·θ`, so
`g x − g y = ∑_θ ⟨g,θ⟩(θ x − θ y)`; regroup over the `Ind_H^G` partition
(`exists_induce_constituent_partition`, `Finset.sum_biUnion`).  Each block `A` over `ρ` satisfies
`e·(block sum) = c·∑_{θ∈A}⟨Ind ρ,θ⟩(θ x − θ y) = c·(Ind ρ x − Ind ρ y) = 0` (with `c = ⟨g,θ₀⟩`,
`e = ⟨Ind ρ,θ₀⟩ ≠ 0` for a non-trivial `θ₀ ∈ A`), since `Ind_H^G ρ` vanishes off `H`
(`induce_apply_eq_zero_of_not_mem_normal`) and the trivial character drops (`θ x − θ y = 0`).
Blocks with no non-trivial constituent contribute `0` termwise. -/
theorem constant_off_normal_of_inner_block_const {G : Type*} [Group G] [Finite G]
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {H : Subgroup G} [hH : H.Normal] [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    [Fintype (IrreducibleCharacter G)]
    (g : ClassFunction G ℂ)
    (hcoeff : ∀ (θ₁ θ₂ : IrreducibleCharacter G) (ρ : IrreducibleCharacter ↥H),
        θ₁ ≠ trivialIrreducibleCharacter G → θ₂ ≠ trivialIrreducibleCharacter G →
        IrreducibleCharacter.LiesOver H θ₁ ρ → IrreducibleCharacter.LiesOver H θ₂ ρ →
        ClassFunction.inner g (θ₁ : ClassFunction G ℂ)
          = ClassFunction.inner g (θ₂ : ClassFunction G ℂ))
    (hmult : ∀ (θ₁ θ₂ : IrreducibleCharacter G) (ρ : IrreducibleCharacter ↥H),
        IrreducibleCharacter.LiesOver H θ₁ ρ → IrreducibleCharacter.LiesOver H θ₂ ρ →
        ClassFunction.inner (ClassFunction.induce H (ρ : ClassFunction ↥H ℂ))
              (θ₁ : ClassFunction G ℂ)
          = ClassFunction.inner (ClassFunction.induce H (ρ : ClassFunction ↥H ℂ))
              (θ₂ : ClassFunction G ℂ))
    {x y : G} (hx : x ∉ H) (hy : y ∉ H) :
    g x = g y := by
  classical
  obtain ⟨parts, hcover, hdisj, hchar⟩ := exists_induce_constituent_partition (G := G) (H := H)
  have hg_eval : ∀ z : G, g z = ∑ θ : IrreducibleCharacter G,
      ClassFunction.inner g (θ : ClassFunction G ℂ) * (θ : ClassFunction G ℂ) z := by
    intro z
    conv_lhs => rw [← sum_inner_irreducibleCharacter_smul g]
    rw [ClassFunction.sum_apply]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [ClassFunction.smul_apply]
  rw [← sub_eq_zero, hg_eval x, hg_eval y, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [hcover, Finset.sum_biUnion hdisj]
  refine Finset.sum_eq_zero fun A hA => ?_
  simp only [id_eq]
  obtain ⟨ρ, hρ⟩ := hchar A hA
  have hIndeval : ∀ z : G, ∑ θ ∈ A,
      ClassFunction.inner (ClassFunction.induce H (ρ : ClassFunction ↥H ℂ)) (θ : ClassFunction G ℂ)
          * (θ : ClassFunction G ℂ) z
        = ClassFunction.induce H (ρ : ClassFunction ↥H ℂ) z := by
    intro z
    have hf : ∀ θ ∈ (Finset.univ : Finset (IrreducibleCharacter G)), θ ∉ A →
        ClassFunction.inner (ClassFunction.induce H (ρ : ClassFunction ↥H ℂ))
            (θ : ClassFunction G ℂ) * (θ : ClassFunction G ℂ) z = 0 := by
      intro θ _ hθA
      have hz : ClassFunction.inner (ClassFunction.induce H (ρ : ClassFunction ↥H ℂ))
          (θ : ClassFunction G ℂ) = 0 := by
        by_contra hne
        exact hθA ((hρ θ).mpr
          ((IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver H θ ρ).mp hne))
      rw [hz, zero_mul]
    rw [Finset.sum_subset (Finset.subset_univ A) hf]
    conv_rhs => rw [← sum_inner_irreducibleCharacter_smul
      (ClassFunction.induce H (ρ : ClassFunction ↥H ℂ))]
    rw [ClassFunction.sum_apply]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [ClassFunction.smul_apply]
  by_cases hnt : ∃ θ₀ ∈ A, θ₀ ≠ trivialIrreducibleCharacter G
  · obtain ⟨θ₀, hθ₀A, hθ₀nt⟩ := hnt
    have hlo₀ : IrreducibleCharacter.LiesOver H θ₀ ρ := (hρ θ₀).mp hθ₀A
    have he_ne : ClassFunction.inner (ClassFunction.induce H (ρ : ClassFunction ↥H ℂ))
        (θ₀ : ClassFunction G ℂ) ≠ 0 :=
      (IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver H θ₀ ρ).mpr hlo₀
    have hkey : ClassFunction.inner (ClassFunction.induce H (ρ : ClassFunction ↥H ℂ))
          (θ₀ : ClassFunction G ℂ)
        * (∑ θ ∈ A, ClassFunction.inner g (θ : ClassFunction G ℂ)
            * ((θ : ClassFunction G ℂ) x - (θ : ClassFunction G ℂ) y)) = 0 := by
      rw [Finset.mul_sum]
      have hswap : (∑ θ ∈ A, ClassFunction.inner (ClassFunction.induce H (ρ : ClassFunction ↥H ℂ))
              (θ₀ : ClassFunction G ℂ)
            * (ClassFunction.inner g (θ : ClassFunction G ℂ)
              * ((θ : ClassFunction G ℂ) x - (θ : ClassFunction G ℂ) y)))
          = ClassFunction.inner g (θ₀ : ClassFunction G ℂ)
            * ∑ θ ∈ A, ClassFunction.inner (ClassFunction.induce H (ρ : ClassFunction ↥H ℂ))
                (θ : ClassFunction G ℂ)
              * ((θ : ClassFunction G ℂ) x - (θ : ClassFunction G ℂ) y) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun θ hθA => ?_
        by_cases hθt : θ = trivialIrreducibleCharacter G
        · subst hθt; simp
        · have hlo : IrreducibleCharacter.LiesOver H θ ρ := (hρ θ).mp hθA
          rw [hcoeff θ θ₀ ρ hθt hθ₀nt hlo hlo₀, hmult θ θ₀ ρ hlo hlo₀]; ring
      rw [hswap]
      have hI0 : ∑ θ ∈ A, ClassFunction.inner (ClassFunction.induce H (ρ : ClassFunction ↥H ℂ))
            (θ : ClassFunction G ℂ) * ((θ : ClassFunction G ℂ) x - (θ : ClassFunction G ℂ) y) = 0 := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, hIndeval x, hIndeval y,
          ClassFunction.induce_apply_eq_zero_of_not_mem_normal H _ hx,
          ClassFunction.induce_apply_eq_zero_of_not_mem_normal H _ hy, sub_zero]
      rw [hI0, mul_zero]
    exact (mul_eq_zero.mp hkey).resolve_left he_ne
  · push Not at hnt
    refine Finset.sum_eq_zero fun θ hθA => ?_
    rw [hnt θ hθA]; simp

/-- **Equal degree of the constituents of `Ind_N^L θ`** (Peterfalvi (1.7.b), the exact form the
(12.5) `DpsiH` decomposition consumes).  Immediate from `induce_inertia_constituent_apply_one_eq`
applied to `φ₁, φ₂` with the *same* Clifford correspondent `ψ`: both degrees equal `[L:T]·ψ(1)`.
With `T/N` abelian (the `H'/H = [H,H]/H` case), this is the coprimality-free equal degree feeding the
`DpsiH` block coefficient/multiplicity constancy. -/
theorem induce_inertia_constituents_apply_one_eq
    {L : Type*} [Group L] [Finite L] [Fintype L] [Invertible (Nat.card L : ℂ)]
    {N T : Subgroup L} [N.Normal] [(N.subgroupOf T).Normal] (hNT : N ≤ T)
    [Fintype ↥N] [Fintype ↥T] [Fintype ↥(N.subgroupOf T)]
    [Invertible (Nat.card ↥N : ℂ)] [Invertible (Nat.card ↥T : ℂ)]
    [Invertible (Nat.card ↥(N.subgroupOf T) : ℂ)]
    [Fintype (IrreducibleCharacter ↥(N.subgroupOf T))] [Fintype ((↥T ⧸ N.subgroupOf T) →* ℂˣ)]
    (hab : ∀ x y : ↥T, ⁅x, y⁆ ∈ N.subgroupOf T)
    (θ : IrreducibleCharacter ↥N)
    (hinertia : ClassFunction.inertia (G := L) (θ : ClassFunction ↥N ℂ) = T)
    (ψ : IrreducibleCharacter ↥T)
    (hover : ClassFunction.restrictionMultiplicity (N.subgroupOf T) (ψ : ClassFunction ↥T ℂ)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hNT).toMonoidHom
          (θ : ClassFunction ↥N ℂ)) ≠ 0)
    (φ₁ φ₂ : IrreducibleCharacter L)
    (hφ₁ : ClassFunction.inner (ClassFunction.induce N (θ : ClassFunction ↥N ℂ))
        (φ₁ : ClassFunction L ℂ) ≠ 0)
    (hφ₂ : ClassFunction.inner (ClassFunction.induce N (θ : ClassFunction ↥N ℂ))
        (φ₂ : ClassFunction L ℂ) ≠ 0) :
    (φ₁ : ClassFunction L ℂ) (1 : L) = (φ₂ : ClassFunction L ℂ) (1 : L) := by
  rw [induce_inertia_constituent_apply_one_eq hNT hab θ hinertia ψ hover φ₁ hφ₁,
    induce_inertia_constituent_apply_one_eq hNT hab θ hinertia ψ hover φ₂ hφ₂]

open scoped commutatorElement in
/-- **Equal degree of the constituents of `Ind_{[HH,HH]}^{HH} ρ`** (Peterfalvi (1.7.b) specialised to
the derived subgroup — the exact `H' = [H,H]` case (12.5) needs, self-contained).  For a finite `HH`
and `ρ ∈ Irr [HH,HH]`, any two constituents `θ₁, θ₂` of `Ind_{[HH,HH]}^{HH} ρ` have equal degree.
Since `HH/[HH,HH]` is abelian, every inertia quotient `I(ρ)/[HH,HH]` is abelian, so
`induce_inertia_constituents_apply_one_eq` applies with `N = [HH,HH]`, `T = I(ρ)`, `hab` from
`⁅x,y⁆ ∈ ⁅⊤,⊤⁆`, and a Clifford correspondent `ψ` from `exists_liesOver_of_subgroup`. -/
theorem commutator_induce_constituents_apply_one_eq {HH : Type*} [Group HH] [Finite HH]
    [Fintype HH] [Invertible (Nat.card HH : ℂ)]
    [Fintype ↥(commutator HH)] [Invertible (Nat.card ↥(commutator HH) : ℂ)]
    (ρ : IrreducibleCharacter ↥(commutator HH))
    (θ₁ θ₂ : IrreducibleCharacter HH)
    (h₁ : IrreducibleCharacter.LiesOver (commutator HH) θ₁ ρ)
    (h₂ : IrreducibleCharacter.LiesOver (commutator HH) θ₂ ρ) :
    (θ₁ : ClassFunction HH ℂ) 1 = (θ₂ : ClassFunction HH ℂ) 1 := by
  classical
  have hNT : commutator HH ≤ ClassFunction.inertia (ρ : ClassFunction ↥(commutator HH) ℂ) :=
    ClassFunction.subgroup_le_inertia _
  haveI : Fintype ↥(ClassFunction.inertia (ρ : ClassFunction ↥(commutator HH) ℂ)) :=
    Fintype.ofFinite _
  haveI : Fintype ↥((commutator HH).subgroupOf
      (ClassFunction.inertia (ρ : ClassFunction ↥(commutator HH) ℂ))) := Fintype.ofFinite _
  haveI : Invertible
      (Nat.card ↥(ClassFunction.inertia (ρ : ClassFunction ↥(commutator HH) ℂ)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Invertible (Nat.card ↥((commutator HH).subgroupOf
      (ClassFunction.inertia (ρ : ClassFunction ↥(commutator HH) ℂ))) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype (IrreducibleCharacter ↥((commutator HH).subgroupOf
      (ClassFunction.inertia (ρ : ClassFunction ↥(commutator HH) ℂ)))) := Fintype.ofFinite _
  haveI : Fintype ((↥(ClassFunction.inertia (ρ : ClassFunction ↥(commutator HH) ℂ)) ⧸
      (commutator HH).subgroupOf
        (ClassFunction.inertia (ρ : ClassFunction ↥(commutator HH) ℂ))) →* ℂˣ) :=
    Fintype.ofFinite _
  haveI : ((commutator HH).subgroupOf
      (ClassFunction.inertia (ρ : ClassFunction ↥(commutator HH) ℂ))).Normal :=
    ClassFunction.subgroupOf_inertia_normal _
  have hab : ∀ x y : ↥(ClassFunction.inertia (ρ : ClassFunction ↥(commutator HH) ℂ)),
      ⁅x, y⁆ ∈ (commutator HH).subgroupOf
        (ClassFunction.inertia (ρ : ClassFunction ↥(commutator HH) ℂ)) := by
    intro x y
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  obtain ⟨ψ, hψ⟩ := exists_liesOver_of_subgroup
    (⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hNT).toMonoidHom
        (ρ : ClassFunction ↥(commutator HH) ℂ),
      IsIrreducibleCharacter.compHom_of_surjective
        (Subgroup.subgroupOfEquivOfLe hNT).surjective ρ.isIrreducible⟩ :
      IrreducibleCharacter ↥((commutator HH).subgroupOf
        (ClassFunction.inertia (ρ : ClassFunction ↥(commutator HH) ℂ))))
  exact induce_inertia_constituents_apply_one_eq hNT hab ρ rfl ψ hψ θ₁ θ₂
    ((IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver (commutator HH) θ₁ ρ).mpr h₁)
    ((IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver (commutator HH) θ₂ ρ).mpr h₂)

end OddOrder.RepresentationTheory
