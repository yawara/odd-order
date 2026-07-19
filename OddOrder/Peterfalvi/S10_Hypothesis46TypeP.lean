/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S10_StructureSetup
import OddOrder.Peterfalvi.S12_MaximalIII_IV_V_Core.Hypothesis
import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF.SetupLemma151

/-!
# Peterfalvi (8.15), claim 2: Hypothesis (4.6) for a type-`P` maximal, `H = M_F` / `H = M_s`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, (8.15) claim 2, pp. 47-48 (issue 1042).

**(8.15), claim 2**: if `M` is of type `P` and `M' = [M,M]`, then Hypothesis (4.6) holds with
`L = M`, `K = M'`, `A = A(M)`, `A₀ = A₀(M)`, and `H = M_F` **or** `H = M_s` (both choices
satisfy (4.6.c,d)).  Proof from (8.4.a,d), (8.5.c), (8.10).  Coq mirror: `FT_prDade_hyp`
(`PFsection8.v:799`, the `prime_Dade_hypothesis` bundling `ctiW`/`ptiWM`/`FT_Dade0_hyp` at the
core `M`_\s`; Coq carries only the `H = M_s` choice).

## What this file provides

The §8-level producer `typePData_toHypothesis46` — Hypothesis (4.6) from **bare** type-`P`
inputs (a `TypePData`, the (8.15) claim-1 Dade datum `DadeSupportHypothesisData M (A₀(M))`,
oddness, and the (8.4.a) Hall coprimality) — with the (4.6.c) subgroup `H` a **parameter**
(any normal `H` with `W₂ ≤ H ≤ K`), plus the two book choices:

* `typePData_toHypothesis46_hallKernel` — `H = M_F = maxNilpotentNormalHall M` (= `data.H`;
  (8.10) writes `M_F` for it), normality from `maxNilpotentNormalHall_subgroupOf_normal` and
  `W₂ ≤ M_F ≤ M'` from the `TypePData` fields `W2_le`/`H_le`;
* `typePData_toHypothesis46_derived` — `H = K = M'`, the `H = M_s` choice in the type-`P₁`
  regime (`M_s = M'` for types III/IV, and for type V via `U = ⊥`; for type II — `P₂` —
  `M_s = M_F ⊊ M'`, so there the faithful `M_s` choice is `_hallKernel`, cf. issue 9008).

The (4.6.d) covering `⋃_{h∈H^#} C_K(h)^# ⊆ A(M)` is **trivial for every `H ≤ K`** in the
type-`P` instantiation: `A(M) = (M')^# = K^#` (`typePA_eq_sharpSubgroup_derivedInG`) already
contains every nonidentity element of `K` — which is why the book can offer both choices.

## Relation to the existing §10 producer

`S12.Hypothesis.toHypothesis46` (`S12_MaximalIII_IV_V_Core/Hypothesis.lean`) is the same
construction bundled inside the §10 Hypothesis (10.1) (types III/IV/V) and fixed at `H = K`;
its `hHall` input is discharged there via `typePData_W1_hall_coprime` (currently
sorry-carrying through BG 16.1).  This file exposes the (8.15)-level general statement:
bare `TypePData`, claim-1 datum as input, `hHall` as an explicit hypothesis — so the producers
here are **axiom-clean**, and every field source is the same brick the §10 producer uses
(`typePData_toS06Hypothesis`, `typePData_toTICyclicHypothesis`, `S04.Hypothesis.restrict`).
The `M`-stability of `A(M)` is proved bare below (`conj_mem_typePA`), replacing the
§10-bundled `le_normalizer_typePA`.
-/

namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ### 8D: `M`-stability of `A(M)` (bare form of the (8.16) easy half, p. 48) -/

section TypePAStability

variable {M : Subgroup G}

/-- **`A(M)` is `M`-invariant, bare `TypePData` form**: conjugation by `l ∈ M` preserves
`A(M) = (M')^#` (`typePA_eq_sharpSubgroup_derivedInG`) — `M` normalizes its derived subgroup
(`derivedInG_pointwise_smul` + `Subgroup.conj_smul_eq_self_of_mem`) and conjugation preserves
nonidentity.  Bare form of the §10-bundled `S12.le_normalizer_typePA`
(`S12_MaximalIII_IV_V_Core/Hypothesis.lean:433`), in the shape `S04.Hypothesis.restrict`
consumes. -/
theorem conj_mem_typePA (data : TypePData M) :
    ∀ (l : ↥M) ⦃a : G⦄, a ∈ typePA M data →
      (l : G) * a * (l : G)⁻¹ ∈ typePA M data := by
  intro l a ha
  rw [typePA_eq_sharpSubgroup_derivedInG] at ha ⊢
  obtain ⟨haM', ha1⟩ := ha
  refine ⟨?_, ?_⟩
  · -- conjugation by `l ∈ M` preserves `M' = derivedInG M`
    rw [SetLike.mem_coe]
    have hM'inv : MulAut.conj (l : G) • derivedInG M = derivedInG M := by
      rw [derivedInG_pointwise_smul, Subgroup.conj_smul_eq_self_of_mem l.2]
    rw [← hM'inv, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hsm : (MulAut.conj (l : G))⁻¹ • ((l : G) * a * (l : G)⁻¹) = a := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]
      group
    rw [hsm]
    exact haM'
  · -- conjugation preserves nonidentity
    simp only [Set.mem_singleton_iff]
    intro h1
    refine ha1 (Set.mem_singleton_iff.mpr ?_)
    have hrw : a = (l : G)⁻¹ * ((l : G) * a * (l : G)⁻¹) * (l : G) := by group
    rw [hrw, h1]
    group

end TypePAStability

/-! ### 8D: the (8.15) claim-2 Hypothesis (4.6) producers (pp. 47-48) -/

section Hypothesis46TypeP

variable [Finite G] {M : Subgroup G}

open OddOrder.Peterfalvi.S12 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (8.15), claim 2, general `H`**: Hypothesis (4.6) holds with `L = M`, `K = M'`,
`A = A(M)`, `A₀ = A₀(M)`, for **any** normal `H` with `W₂ ≤ H ≤ K` — the (4.6.d) covering is
trivial since `A(M) = K^#`.  The two book choices `H = M_F` / `H = M_s` are the corollaries
below.

Field sources (all bare): the (4.2) structural part is `typePData_toS06Hypothesis` (with the
(8.4.a) Hall coprimality `hHall` an explicit input — its §10 discharge
`typePData_W1_hall_coprime` is sorry-carrying, so taking it as a hypothesis keeps this producer
axiom-clean); the `A`-side Dade datum restricts the claim-1 `A₀`-datum `d.dade` along
`A(M) ⊆ A₀(M)` with the `M`-stability `conj_mem_typePA`; the (4.6.b) TI-cyclic data is
`typePData_toTICyclicHypothesis` (whose `V` is definitionally `typePV M data`, so the (4.6.d)
`A₀ = A ∪ V^M` datum is **definitionally** `d.dade` — the payoff of stating (8.10) `typePA0`
with `conjClassSetIn`); the (4.6.e) isometry is the claim-1 `fullDadeIsometryData d.hconj`. -/
noncomputable def typePData_toHypothesis46 (data : TypePData M)
    (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1))
    (d : DadeSupportHypothesisData M (typePA0 M data))
    (H : Subgroup ↥M) (hHnorm : H.Normal)
    (hW2H : data.W2.subgroupOf M ≤ H)
    (hHK : H ≤ (derivedInG M).subgroupOf M) :
    OddOrder.Peterfalvi.S06.Hypothesis46 (typePA M data) M :=
  { toHypothesis := typePData_toS06Hypothesis data hodd hHall
    dade := d.dade.restrict Set.subset_union_left (conj_mem_typePA data)
    tic := typePData_toTICyclicHypothesis data hodd
    tic_W1 := (Subgroup.map_subgroupOf_eq_of_le data.W1_le).symm
    tic_W2 := (Subgroup.map_subgroupOf_eq_of_le (typePData_W2_le_self data)).symm
    tic_V := rfl
    subH := H
    subH_normal := hHnorm
    W2_le_subH := hW2H
    subH_le_K := hHK
    A_covers := fun _ _ _ x hx hx1 => by
      rw [typePA_eq_sharpSubgroup_derivedInG]
      exact ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2,
        fun h1 => hx1 (OneMemClass.coe_eq_one.mp (Set.mem_singleton_iff.mp h1))⟩
    dade0 := d.dade
    tau := d.dade.fullDadeIsometryData d.hconj }

open OddOrder.Peterfalvi.S12 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (8.15), claim 2, the `H = M_F` choice**: Hypothesis (4.6) with
`H = M_F = maxNilpotentNormalHall M` (= `data.H`, the nilpotent Hall kernel of (8.10); in the
type-`P₂` regime this *is* the faithful `M_s` choice, `M_s = M_F` for type II).  Normality of
`M_F` inside `M` is `maxNilpotentNormalHall_subgroupOf_normal` through `data.H_eq`;
`W₂ ≤ M_F ≤ M'` are the `TypePData` fields `W2_le` (through the first factor) and `H_le`. -/
noncomputable def typePData_toHypothesis46_hallKernel (data : TypePData M)
    (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1))
    (d : DadeSupportHypothesisData M (typePA0 M data)) :
    OddOrder.Peterfalvi.S06.Hypothesis46 (typePA M data) M :=
  typePData_toHypothesis46 data hodd hHall d (data.H.subgroupOf M)
    (by rw [data.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal M)
    (Subgroup.comap_mono (data.W2_le.trans inf_le_left))
    (Subgroup.comap_mono data.H_le)

open OddOrder.Peterfalvi.S12 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (8.15), claim 2, the `H = K = M'` choice** — the book's `H = M_s` in the
type-`P₁` regime (`M_s = M'` for types III/IV, and for type V via `U = ⊥`; issue 9008).  This
is the choice the §10-bundled producer `S12.Hypothesis.toHypothesis46` fixes; here it comes
from bare inputs.  Normality of `K = M'` and `W₂ ≤ K` are the `typePData_toS06Hypothesis`
fields themselves. -/
noncomputable def typePData_toHypothesis46_derived (data : TypePData M)
    (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1))
    (d : DadeSupportHypothesisData M (typePA0 M data)) :
    OddOrder.Peterfalvi.S06.Hypothesis46 (typePA M data) M :=
  typePData_toHypothesis46 data hodd hHall d
    ((typePData_toS06Hypothesis data hodd hHall).K)
    (typePData_toS06Hypothesis data hodd hHall).K_normal
    (typePData_toS06Hypothesis data hodd hHall).W2_le_K
    (le_refl _)

end Hypothesis46TypeP

end OddOrder.Peterfalvi.S10
