/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# 有限可解群の素数指数正規部分群

`OddOrder.RepresentationTheory.exists_normal_index_prime_of_solvable` (FongSwan.lean) と
`OddOrder.BG.Ch2.S07.exists_normal_index_prime_of_solvable` (private, S07_Hypothesis75.lean) に
同一の ~30 行証明が重複していたのを共有 leaf へ集約したもの (issue 9111)。
FongSwan の元 docstring が「once the BG side is refactored、単一の共有 public leaf へ統合すべき」と
明記していた統合先。
-/

namespace OddOrder.GroupTheory

/-- **A nontrivial finite solvable group has a normal subgroup of prime index.**  Take a proper
normal subgroup `N` of maximal order; the quotient `Q ⧸ N` is simple and solvable, hence abelian,
so `Group.is_simple_iff_prime_card` gives `[Q:N] = |Q ⧸ N|` prime. -/
theorem exists_normal_index_prime_of_solvable {Q : Type*} [Group Q] [Finite Q]
    [IsSolvable Q] (hQ : Nontrivial Q) : ∃ N : Subgroup Q, N.Normal ∧ N.index.Prime := by
  obtain ⟨N, hNmem, hNmax⟩ :=
    Set.exists_max_image {N : Subgroup Q | N.Normal ∧ N < ⊤} (fun N : Subgroup Q => Nat.card ↥N)
      (Set.toFinite _) ⟨⊥, inferInstance, bot_lt_top⟩
  obtain ⟨hNnorm, hNlt⟩ := hNmem
  haveI := hNnorm
  refine ⟨N, hNnorm, ?_⟩
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  haveI hntq : Nontrivial (Q ⧸ N) := by
    obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt hNlt
    exact ⟨QuotientGroup.mk x, 1, by rw [Ne, QuotientGroup.eq_one_iff]; exact hx⟩
  haveI hsimple : IsSimpleGroup (Q ⧸ N) := by
    refine ⟨fun Nbar hNbar => ?_⟩
    set N' : Subgroup Q := Nbar.comap (QuotientGroup.mk' N) with hN'
    haveI : N'.Normal := hNbar.comap _
    have hNN' : N ≤ N' := by
      intro x hx
      rw [hN', Subgroup.mem_comap,
        show (QuotientGroup.mk' N) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
      exact one_mem _
    have hmapeq : N'.map (QuotientGroup.mk' N) = Nbar := by
      rw [hN', Subgroup.map_comap_eq_self_of_surjective hsurj]
    rcases lt_or_eq_of_le (le_top : N' ≤ ⊤) with hN'lt | hN'top
    · left
      have hcard : Nat.card ↥N' ≤ Nat.card ↥N := hNmax N' ⟨inferInstance, hN'lt⟩
      have hN'eqN : N = N' := Subgroup.eq_of_le_of_card_ge hNN' hcard
      rw [← hmapeq, ← hN'eqN]
      simp [QuotientGroup.map_mk'_self]
    · right
      rw [← hmapeq, hN'top, Subgroup.map_top_of_surjective _ hsurj]
  haveI : IsMulCommutative (Q ⧸ N) := ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance⟩⟩
  rw [Subgroup.index_eq_card]
  exact Group.is_simple_iff_prime_card.mp hsimple

end OddOrder.GroupTheory
