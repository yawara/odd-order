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

The §8-level producer `typePData_toHypothesis46_ofSupport` — Hypothesis (4.6) from **bare**
type-`P` inputs (a `TypePData`, the `A₀`-Dade hypothesis with its `HConjInvariant`, oddness, and
the (8.4.a) Hall coprimality) — with **both** the support `A` and the (4.6.c) subgroup `H`
parameters.  On top of it, two families of instances, one per (8.10) support:

**(a) `A = typePA M data = (M')^#`, the type-`P₁` specialisation** (issue 9008):

* `typePData_toHypothesis46` — `H` still a parameter (any normal `H` with `W₂ ≤ H ≤ K`);
* `typePData_toHypothesis46_hallKernel` — `H = M_F = maxNilpotentNormalHall M` (= `data.H`);
* `typePData_toHypothesis46_derived` — `H = K = M'`, the `H = M_s` choice for type `P₁`
  (`M_s = M'` for types III/IV, and for type V via `U = ⊥`).

Here the (4.6.d) covering `⋃_{h∈H^#} C_K(h)^# ⊆ A` is **trivial for every `H ≤ K`**, since
`A = K^#` (`typePA_eq_sharpSubgroup_derivedInG`) already contains every nonidentity element of
`K`.

**(b) `A = typePACore M = ⋃_{x∈M_s^#} C_{M'}(x)^#`, the book-literal support**
(`S10_StructureSetup`; faithful for every type, in particular type `P₂` = type II where
`M_s = M_F ⊊ M'`):

* `typePACore_toHypothesis46` — `H` a parameter (normal, `W₂ ≤ H ≤ M_s`);
* `typePACore_toHypothesis46_core` — the book's `H = M_s = M_σ` choice (Coq `FT_prDade_hyp`);
* `typePACore_toHypothesis46_hallKernel` — the book's `H = M_F` choice, via `M_F ≤ M_s`.

Here the covering is not free but *definitional*: it is exactly what `typePACore` says
(`mem_typePACore`).  This family is what a type-II maximal needs; the (13.1) `S`-instance is
`S15.Hypothesis.hyp46S`.  Hub ruling 9163 (Option B′).

## Relation to the existing §10 producer

`S12.Hypothesis.toHypothesis46` (`S12_MaximalIII_IV_V_Core/Hypothesis.lean`) is the same
construction bundled inside the §10 Hypothesis (10.1) (types III/IV/V) and fixed at `H = K`;
its `hHall` input is discharged there via `typePData_W1_hall_coprime` (which needs `hG`/`hM`
and the type hypothesis).  This file exposes the (8.15)-level general statement: bare
`TypePData`, Dade datum as input, `hHall` as an explicit hypothesis — matching the book, which
states (8.15.2) as a consequence of (8.4.a) rather than re-deriving it — and every field source
is the same brick the §10 producer uses
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
/-- **Peterfalvi (8.15), claim 2, support-parametric core**: Hypothesis (4.6) holds with `L = M`,
`K = M'`, `A₀ = A ∪ V^M`, for **any** `M`-stable support `A` satisfying the (4.6.d) covering
`⋃_{h∈H^#} C_K(h)^# ⊆ A`, and any normal `H` with `W₂ ≤ H ≤ K`.

Both (8.10) supports are instances: `A = typePA M data = (M')^#` (the `P₁` specialisation, where
the covering is trivial for every `H ≤ K`) and `A = typePACore M = ⋃_{x∈M_s^#} C_{M'}(x)^#` (the
book-literal support, valid for every type, where the covering is exactly its defining property at
`H = M_s`).  Keeping `A` a parameter is what makes the book's freedom in choosing `H` — and the
`P₁`/`P₂` split of the support — one construction rather than two.

Field sources (all bare): the (4.2) structural part is `typePData_toS06Hypothesis` (with the
(8.4.a) Hall coprimality `hHall` an explicit input, matching the book, which cites (8.4.a) here
rather than re-deriving it; the §10 discharge is `typePData_W1_hall_coprime`, which needs
`hG`/`hM`/`IsTypeP` that (8.15.2) itself does not); the `A`-side Dade datum restricts the `A₀`-Dade
`dade0` along `A ⊆ A₀` with the `M`-stability `hAnorm`; the (4.6.b) TI-cyclic data is
`typePData_toTICyclicHypothesis` (whose `V` is definitionally `typePV M data`, so the (4.6.d)
`A₀ = A ∪ V^M` datum is **definitionally** `dade0` — the payoff of stating (8.10)
`typePA0`/`typePACore0` with `conjClassSetIn`); the (4.6.e) isometry is
`fullDadeIsometryData hconj`.

`dade0`/`hconj` are taken raw rather than bundled as a `DadeSupportHypothesisData`: the extra
field of the bundle (`H_eq_ftSupportKernel`, the (8.14) faithfulness of the stabilizers) is not
used by (4.6), and consumers holding only a bare `S04.Hypothesis` — e.g. the (13.1) `S`-instance's
`dadeHypS0` — must be able to call this.  The bundled entry point is
`typePData_toHypothesis46`. -/
noncomputable def typePData_toHypothesis46_ofSupport (data : TypePData M)
    (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1))
    (A : Set G)
    (dade0 : OddOrder.Peterfalvi.S04.Hypothesis G (A ∪ conjClassSetIn M (typePV M data)) M)
    (hconj : dade0.HConjInvariant)
    (hAnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A)
    (H : Subgroup ↥M) (hHnorm : H.Normal)
    (hW2H : data.W2.subgroupOf M ≤ H)
    (hHK : H ≤ (derivedInG M).subgroupOf M)
    (hcover : ∀ (hh : ↥M), hh ∈ H → hh ≠ 1 →
      ∀ (x : ↥M), x ∈ Subgroup.centralizer ({hh} : Set ↥M) ⊓ (derivedInG M).subgroupOf M →
        x ≠ 1 → (M.subtype x) ∈ A) :
    OddOrder.Peterfalvi.S06.Hypothesis46 A M :=
  { toHypothesis := typePData_toS06Hypothesis data hodd hHall
    dade := dade0.restrict Set.subset_union_left hAnorm
    tic := typePData_toTICyclicHypothesis data hodd
    tic_W1 := (Subgroup.map_subgroupOf_eq_of_le data.W1_le).symm
    tic_W2 := (Subgroup.map_subgroupOf_eq_of_le (typePData_W2_le_self data)).symm
    tic_V := rfl
    subH := H
    subH_normal := hHnorm
    W2_le_subH := hW2H
    subH_le_K := hHK
    A_covers := hcover
    dade0 := dade0
    tau := dade0.fullDadeIsometryData hconj }

open OddOrder.Peterfalvi.S12 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (8.15), claim 2, general `H`, `P₁` support**: Hypothesis (4.6) with
`A = A(M) = typePA M data`, for **any** normal `H` with `W₂ ≤ H ≤ K` — the (4.6.d) covering is
trivial since `typePA M data = K^#` (`typePA_eq_sharpSubgroup_derivedInG`) already contains every
nonidentity element of `K`, which is why the book can offer both choices of `H` here.  The two
book choices `H = M_F` / `H = M_s` are the corollaries below.

⚠ `typePA` is the type-`P₁` specialisation of (8.10) (issue 9008); for type `P₂` (= type II) use
`typePACore_toHypothesis46` below, whose support is the book-literal `A(M)`. -/
noncomputable def typePData_toHypothesis46 (data : TypePData M)
    (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1))
    (d : DadeSupportHypothesisData M (typePA0 M data))
    (H : Subgroup ↥M) (hHnorm : H.Normal)
    (hW2H : data.W2.subgroupOf M ≤ H)
    (hHK : H ≤ (derivedInG M).subgroupOf M) :
    OddOrder.Peterfalvi.S06.Hypothesis46 (typePA M data) M :=
  typePData_toHypothesis46_ofSupport data hodd hHall (typePA M data) d.dade d.hconj
    (conj_mem_typePA data) H hHnorm hW2H hHK
    (fun _ _ _ x hx hx1 => by
      rw [typePA_eq_sharpSubgroup_derivedInG]
      exact ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2,
        fun h1 => hx1 (OneMemClass.coe_eq_one.mp (Set.mem_singleton_iff.mp h1))⟩)

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

/-! ### 8D: the (8.15) claim-2 producers on the **book-literal** support `A(M)` (type `P₂` included)

The producers above run on `typePA M data = (M')^#`, the type-`P₁` specialisation of (8.10).  The
ones below run on the book-literal `A(M) = typePACore M = ⋃_{x∈M_s^#} C_{M'}(x)^#`, which is
faithful for **every** Peterfalvi type — in particular for type `P₂` (= type II), where
`M_s = M_F ⊊ M'` and the two supports genuinely differ (issue 9008, hub ruling 9163 Option B′).

Note the direction of the (4.6.d) covering flips between the two families.  On `typePA` the
covering is *free* (`A = K^#` contains everything) but the support over-claims for `P₂`; on
`typePACore` the support is exact and the covering is *exactly its defining property*, available
for every `H ≤ M_s`.  This is why the book states (8.15.2) with the core `M_s` in hand. -/

open OddOrder.Peterfalvi.S12 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (8.15), claim 2, book-literal support, general `H ≤ M_s`**: Hypothesis (4.6)
holds with `L = M`, `K = M'`, `A = A(M) = typePACore M`, `A₀ = A₀(M) = typePACore0 M data`, for
any normal `H` with `W₂ ≤ H ≤ M_s`.

The (4.6.d) covering `⋃_{h∈H^#} C_K(h)^# ⊆ A` is here *the definition of* `A(M)`: an
`x ∈ C_{M'}(h)^#` with `h ∈ H^# ⊆ M_s^#` is a nonidentity element of `M'` centralizing a
nonidentity element of `M_s`, which is exactly membership in
`typePACore M = centralizerSupport (M_s^#) M'` (`mem_typePACore`).  Contrast
`typePData_toHypothesis46`, where the covering came for free from the `P₁` over-approximation
`A = K^#`.

`hσK : M_s ≤ M'` and `W₂ ≤ M_s` are taken as hypotheses to keep the producer bare (their
§15/§16 discharges are `Msigma_le_derived` and
`maxNilpotentNormalHall_le_Msigma` composed with the `TypePData` field `W2_le`, both needing
`hG`/`hM`). -/
noncomputable def typePACore_toHypothesis46 (data : TypePData M)
    (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1))
    (dade0 : OddOrder.Peterfalvi.S04.Hypothesis G (typePACore0 M data) M)
    (hconj : dade0.HConjInvariant)
    (H : Subgroup ↥M) (hHnorm : H.Normal)
    (hW2H : data.W2.subgroupOf M ≤ H)
    (hHσ : H ≤ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
    (hσK : OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M) :
    OddOrder.Peterfalvi.S06.Hypothesis46 (typePACore M) M :=
  typePData_toHypothesis46_ofSupport data hodd hHall (typePACore M) dade0 hconj
    (fun l _ ha => typePACore_conj_mem l.2 ha) H hHnorm hW2H
    (hHσ.trans (Subgroup.comap_mono hσK))
    (by
      intro hh hhH hh1 x hx hx1
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxC, hxD⟩ := hx
      rw [Subgroup.mem_subgroupOf] at hxD
      have hhσ : (hh : G) ∈ OddOrder.BG.Ch3.S10.Msigma M :=
        Subgroup.mem_subgroupOf.mp (hHσ hhH)
      rw [Subgroup.mem_centralizer_iff] at hxC
      rw [mem_typePACore]
      refine ⟨hxD, ?_, (hh : G), ⟨hhσ, ?_⟩, ?_⟩
      · simpa using hx1
      · simpa using hh1
      · rw [Subgroup.mem_centralizer_iff]
        rintro g rfl
        have hcomm := hxC (hh : ↥M) rfl
        have := congrArg M.subtype hcomm
        simpa using this)

open OddOrder.Peterfalvi.S12 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (8.15), claim 2, the book's `H = M_s` choice** — the faithful type-`P₂` (= type
II) instance, and simultaneously the type-uniform one: `M_s = M_σ` is normal in `M`
(`Msigma_subgroupOf` exhibits it as a `π`-core of `↥M`), and the (4.6.d) covering holds at the
largest admissible `H`.  Coq mirror: `FT_prDade_hyp` (`PFsection8.v:799`) carries exactly this
choice. -/
noncomputable def typePACore_toHypothesis46_core (data : TypePData M)
    (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1))
    (dade0 : OddOrder.Peterfalvi.S04.Hypothesis G (typePACore0 M data) M)
    (hconj : dade0.HConjInvariant)
    (hW2σ : data.W2 ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hσK : OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M) :
    OddOrder.Peterfalvi.S06.Hypothesis46 (typePACore M) M :=
  typePACore_toHypothesis46 data hodd hHall dade0 hconj
    ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
    (by rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance)
    (Subgroup.comap_mono hW2σ) (le_refl _) hσK

open OddOrder.Peterfalvi.S12 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (8.15), claim 2, the book's `H = M_F` choice** on the book-literal support:
`H = M_F = maxNilpotentNormalHall M` (= `data.H`).  Needs `M_F ≤ M_s`
(`maxNilpotentNormalHall_le_Msigma`), which is an equality for types I, II and V; the book offers
this second choice of `H` precisely because the covering is monotone in `H`. -/
noncomputable def typePACore_toHypothesis46_hallKernel (data : TypePData M)
    (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1))
    (dade0 : OddOrder.Peterfalvi.S04.Hypothesis G (typePACore0 M data) M)
    (hconj : dade0.HConjInvariant)
    (hHσ : data.H ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hσK : OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M) :
    OddOrder.Peterfalvi.S06.Hypothesis46 (typePACore M) M :=
  typePACore_toHypothesis46 data hodd hHall dade0 hconj (data.H.subgroupOf M)
    (by rw [data.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal M)
    (Subgroup.comap_mono (data.W2_le.trans inf_le_left))
    (Subgroup.comap_mono hHσ) hσK

end Hypothesis46TypeP

end OddOrder.Peterfalvi.S10
