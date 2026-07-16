/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Metacyclic Groups

`OddOrder.GroupTheory` shared module: 'metacyclic group' の概念.

mathlib v4.29.1 にはこの概念 (∃ cyclic normal `N ⊴ G` で `G ⧸ N` cyclic) が無いため,
**BG §4 (p-Groups of Small Rank)** Lem 4.10, Prop 4.11 (Huppert classification), Thm 4.12
で必要となる shared concept として独立 module に切り出す.

## Main definitions

* `OddOrder.GroupTheory.IsMetacyclic G`:
  `G` は metacyclic, i.e. `∃ N : Subgroup G` で `N.Normal ∧ IsCyclic N ∧ IsCyclic (G ⧸ N)`.

## Main results

* `IsMetacyclic.of_isCyclic`: 巡回群 ⇒ metacyclic (`N = ⊥` を取る).
* `IsMetacyclic.isSolvable`: metacyclic ⇒ solvable (cyclic-by-cyclic extension).

## Design notes

* `Prop` 定義 (構造体ではない); 補題で `∃` を unpack.
* 閉包性 (Isaacs Lem 10.13): 部分群 = `subgroup`, 準同型像 (⊇ 商群) = `of_surjective`.
* 将来 mathlib upstream 視野で `OddOrder/Mathlib/IsMetacyclic.lean` 候補.

## References

* BG §4 (p-Groups of Small Rank), Lem 4.10, Prop 4.11 (Huppert), Thm 4.12.
* Huppert, _Endliche Gruppen I_ (1967), Satz III.13.5.

## Audit context

Phase 2a 第 1 波 audit 2026-05-23 で新規 shared module 候補として確定.
詳細は `notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`.
-/

namespace OddOrder.GroupTheory

variable (G : Type*) [Group G]

/-- **Metacyclic group**: there exists a cyclic normal subgroup `N ≤ G` with `G ⧸ N` cyclic.

教科書 (Huppert, BG §4) の標準定義. `N = ⊥` の取り方で巡回群を包含し,
`N = ⊤` の取り方で trivial-quotient 系も包含する. -/
def IsMetacyclic : Prop :=
  ∃ N : Subgroup G, ∃ _ : N.Normal, IsCyclic N ∧ IsCyclic (G ⧸ N)

variable {G}

namespace IsMetacyclic

/-- Every cyclic group is metacyclic: take `N = ⊥`. -/
theorem of_isCyclic [IsCyclic G] : IsMetacyclic G := by
  refine ⟨⊥, Subgroup.normal_bot, ?_, ?_⟩
  · -- `↥(⊥ : Subgroup G)` is `Unique` (only the identity 1), hence trivially cyclic
    exact ⟨⟨1, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩⟩
  · -- `IsCyclic (G ⧸ ⊥)` follows from `IsCyclic G` via the surjective quotient map
    exact isCyclic_of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective ⊥)

/-- A metacyclic group has cyclic commutator subgroup.

Since `G ⧸ N` is cyclic (hence abelian), `commutator G ≤ N` by
`Subgroup.Normal.quotient_commutative_iff_commutator_le`; and a subgroup of the cyclic
group `N` is cyclic (`Subgroup.isCyclic`), so `commutator G` is cyclic via the
group isomorphism `(commutator G).subgroupOf N ≃* commutator G`.

**BG §4** Thm 4.12(a) の補題段 (mmd L1592: "R metacyclic ⇒ R′ cyclic"). -/
theorem isCyclic_commutator (hmeta : IsMetacyclic G) : IsCyclic (commutator G) := by
  obtain ⟨N, hN, hN_cyc, hQ_cyc⟩ := hmeta
  haveI := hN
  haveI : IsCyclic (G ⧸ N) := hQ_cyc
  have hle : commutator G ≤ N :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  haveI : IsCyclic N := hN_cyc
  haveI : IsCyclic ↥((commutator G).subgroupOf N) := Subgroup.isCyclic _
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hle).surjective

/-- **Isaacs Lemma 10.13(a)** (homomorphic-image form): the image of a metacyclic
group under a surjective homomorphism is metacyclic; taking `f = QuotientGroup.mk' U`
recovers the textbook statement that every quotient of a metacyclic group is
metacyclic.

If `N ⊴ G` is cyclic with `G ⧸ N` cyclic, then `N.map f ⊴ H` is cyclic (image of a
cyclic group) and `H ⧸ N.map f` is a surjective image of `G ⧸ N` (the composite
`G → H → H ⧸ N.map f` kills `N`), hence cyclic. -/
theorem of_surjective {H : Type*} [Group H] {f : G →* H} (hf : Function.Surjective f)
    (h : IsMetacyclic G) : IsMetacyclic H := by
  obtain ⟨N, hN, hN_cyc, hQ_cyc⟩ := h
  haveI := hN
  haveI : IsCyclic N := hN_cyc
  haveI : IsCyclic (G ⧸ N) := hQ_cyc
  haveI : (N.map f).Normal := Subgroup.Normal.map hN f hf
  refine ⟨N.map f, inferInstance, ?_, ?_⟩
  · exact isCyclic_of_surjective (f.subgroupMap N) (f.subgroupMap_surjective N)
  · -- `G ⧸ N` surjects onto `H ⧸ N.map f` via the descent of `mk' (N.map f) ∘ f`.
    have hker : N ≤ ((QuotientGroup.mk' (N.map f)).comp f).ker := by
      intro x hx
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact Subgroup.mem_map_of_mem f hx
    refine isCyclic_of_surjective (QuotientGroup.lift N _ hker) ?_
    intro y
    obtain ⟨h', rfl⟩ := QuotientGroup.mk'_surjective (N.map f) y
    obtain ⟨g, rfl⟩ := hf h'
    exact ⟨QuotientGroup.mk g, rfl⟩

/-- **Every subgroup of a metacyclic group is metacyclic.**

If `G` has a cyclic normal subgroup `N` with `G ⧸ N` cyclic, then for any `H ≤ G` the
subgroup `N.subgroupOf H = N ∩ H` is normal in `H`, cyclic (it injects into the cyclic
`N` via `x ↦ (x : G)`), and the quotient `H ⧸ (N.subgroupOf H)` is cyclic (it injects into
the cyclic `G ⧸ N` via the lift of `mk' N ∘ H.subtype`, whose kernel is `N.subgroupOf H`).

This is a genuine lemma — *not* a thin wrapper — and is needed in BG Theorem 4.12(b)(c)
where part (a) is applied to the subgroup `T = [R, A]`. (The textbook leaves this implicit;
mathlib v4.29.1 has no `IsMetacyclic`.)

**BG §4** Thm 4.12(b)(c) の補題段 (Huppert). -/
theorem subgroup {H : Subgroup G} (h : IsMetacyclic G) : IsMetacyclic ↥H := by
  classical
  obtain ⟨N, hN, hN_cyc, hQ_cyc⟩ := h
  haveI := hN
  refine ⟨N.subgroupOf H, hN.subgroupOf H, ?_, ?_⟩
  · -- cyclic normal part: `N.subgroupOf H` injects into the cyclic `N`.
    haveI : IsCyclic N := hN_cyc
    let g : (N.subgroupOf H) →* N :=
      { toFun := fun x => ⟨(x : G), by have hx := x.2; rwa [Subgroup.mem_subgroupOf] at hx⟩
        map_one' := rfl, map_mul' := fun _ _ => rfl }
    refine isCyclic_of_injective (G' := N) g ?_
    intro a b hab
    have h1 : ((g a : N) : G) = ((g b : N) : G) := congrArg (fun z : N => (z : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  · -- cyclic quotient part: `H ⧸ (N.subgroupOf H)` injects into the cyclic `G ⧸ N`.
    haveI : (N.subgroupOf H).Normal := hN.subgroupOf H
    haveI : IsCyclic (G ⧸ N) := hQ_cyc
    have hf_ker : N.subgroupOf H ≤ ((QuotientGroup.mk' N).comp H.subtype).ker := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      simpa [MonoidHom.mem_ker, QuotientGroup.eq_one_iff] using hx
    refine isCyclic_of_injective (G' := G ⧸ N)
      (QuotientGroup.lift _ ((QuotientGroup.mk' N).comp H.subtype) hf_ker) ?_
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf H) x
    rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.lift_mk] at hx
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, Subgroup.coe_subtype,
      QuotientGroup.eq_one_iff] at hx
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact hx

/-- A metacyclic group is solvable.

Cyclic groups are commutative hence solvable. The extension `1 → N → G → G ⧸ N → 1`
with both ends solvable yields `IsSolvable G` via `solvable_of_ker_le_range`. -/
theorem isSolvable (h : IsMetacyclic G) : IsSolvable G := by
  obtain ⟨N, hN, hN_cyc, hQ_cyc⟩ := h
  haveI := hN
  letI : CommGroup ↥N := IsCyclic.commGroup
  letI : CommGroup (G ⧸ N) := IsCyclic.commGroup
  exact solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end IsMetacyclic

end OddOrder.GroupTheory
