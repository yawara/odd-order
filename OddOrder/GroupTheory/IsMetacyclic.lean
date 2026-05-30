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
* 部分群への閉包 (every subgroup of a metacyclic group is metacyclic) は **非自明** で
  別途証明要; 本 module では未収載.
* 商群への閉包は trivial だが対応 `N` の構成が必要 — 後の補強で.
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
