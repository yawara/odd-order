/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup

/-!
# Isaacs Problem 6B.2 — 既約な忠実可換作用は巡回 (書籍 p. 195)

**主張**: 可換群 `A` が `N` に忠実に作用し, `N` の非自明な真部分群がどれも `A`-不変でないなら,
`A` は巡回群である。

**証明**: 書籍の hint (`p ∣ |N|` と `P ∈ Syl_p`, `C_N(P)` は `A`-不変で非自明) は
**Lemma 6.20 の coprime 仮定を外すため**のもの。ここでは仮説がより強い ("`⊥` か `⊤` しかない")
ことを使って直接 coprime を出す:

* `1 ≠ a ∈ A` に対し固定部分群 `F_a = {n | a • n = n}` は `A` が可換なので `A`-不変。
  仮説より `F_a = ⊥` または `⊤`。`⊤` なら `a` が自明に作用して忠実性に反するので **`F_a = ⊥`**。
* すなわち作用は **Frobenius 作用** であり, `IsFrobeniusAction.coprime_card` から
  `(|A|, |N|) = 1`。
* あとは repo 既存の **Isaacs Lemma 6.20**
  (`isCyclic_of_faithful_trivial_on_proper_invariant`) に流し込めばよい
  (真の不変部分群は `⊥` しかなく, `A` はその上で自明に作用する)。
-/

namespace OddOrder.Isaacs.Ch06

section /- 6B.2: 既約な忠実可換作用 (p. 195) -/

/-- **Isaacs Problem 6B.2** (p. 195) ⭐: 可換群 `A` が `N` に忠実に作用し, `N` の `A`-不変な
部分群が `⊥` と `⊤` しかないなら `A` は巡回群。 -/
theorem isCyclic_of_faithful_of_forall_invariant_eq_bot_or_top
    {A N : Type*} [Group A] [Finite A] [IsMulCommutative A]
    [Group N] [Finite N] [MulDistribMulAction A N] [FaithfulSMul A N]
    (hsimple : ∀ M : Subgroup N, (∀ a : A, ∀ n ∈ M, a • n ∈ M) → M = ⊥ ∨ M = ⊤) :
    IsCyclic A := by
  classical
  by_cases hN : Nontrivial N
  · have := hN
    -- 各 `1 ≠ a` の固定部分群は `A`-不変ゆえ `⊥` (`⊤` は忠実性に反する) — つまり Frobenius 作用
    have hFrob : IsFrobeniusAction A N := by
      intro a ha n hn hfix
      set Fa : Subgroup N :=
        { carrier := {m : N | a • m = m}
          mul_mem' := fun {x y} hx hy => by
            simp only [Set.mem_ofPred_eq] at hx hy ⊢
            rw [smul_mul', hx, hy]
          one_mem' := by
            simp only [Set.mem_ofPred_eq]
            exact smul_one a
          inv_mem' := fun {x} hx => by
            simp only [Set.mem_ofPred_eq] at hx ⊢
            rw [smul_inv', hx] } with hFadef
      have hFainv : ∀ b : A, ∀ m ∈ Fa, b • m ∈ Fa := by
        intro b m hm
        have hm' : a • m = m := hm
        change a • (b • m) = b • m
        rw [smul_smul, (IsMulCommutative.is_comm (M := A)).comm a b, ← smul_smul, hm']
      have hnFa : n ∈ Fa := hfix
      rcases hsimple Fa hFainv with h | h
      · rw [h, Subgroup.mem_bot] at hnFa
        exact hn hnFa
      · refine ha (eq_of_smul_eq_smul (m₁ := a) (m₂ := 1) fun x : N => ?_)
        have hx : x ∈ Fa := by rw [h]; exact Subgroup.mem_top x
        have hx' : a • x = x := hx
        rw [hx', one_smul]
    have hcop : Nat.Coprime (Nat.card A) (Nat.card N) := by
      have : Fintype A := Fintype.ofFinite A
      have : Fintype N := Fintype.ofFinite N
      simpa only [Nat.card_eq_fintype_card] using
        (IsFrobeniusAction.coprime_card (A := A) (N := N) hFrob).symm
    refine isCyclic_of_faithful_trivial_on_proper_invariant hcop ?_
    intro M hMinv hMne a n hn
    rcases hsimple M hMinv with h | h
    · rw [h, Subgroup.mem_bot] at hn
      rw [hn, smul_one]
    · exact absurd h hMne
  · -- `N` が自明なら忠実性から `A` も自明
    have : Subsingleton N := not_nontrivial_iff_subsingleton.mp hN
    have : Subsingleton A :=
      ⟨fun a b => eq_of_smul_eq_smul (m₁ := a) (m₂ := b)
        fun x : N => Subsingleton.elim (a • x) (b • x)⟩
    exact isCyclic_of_subsingleton

end

end OddOrder.Isaacs.Ch06
