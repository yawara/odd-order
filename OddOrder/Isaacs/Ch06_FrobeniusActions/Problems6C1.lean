/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.KernelNilpotent

/-!
# Isaacs Problem 6C.1(a) — 素数位数の固定点自由な自己同型 (書籍 p. 197)

**主張**: `α ∈ Aut(G)` が単位元しか固定せず, かつ素数位数をもつなら `G` は冪零。

**証明**: `A := ⟨α⟩ ≤ Aut(G)` は位数 `p` の巡回群で, `A` の `G` への自然な作用は
**Frobenius** である — `a ∈ A` が非自明なら素数位数ゆえ `⟨a⟩ = A ∋ α` なので, `a` が固定する
元は `α` も固定し, 仮定から単位元しかない。あとは Isaacs Thm 6.24 (Thompson,
`isNilpotent_of_isFrobeniusAction`) を適用すればよい。

書籍の (b) 「位数 `4` では冪零でない例 (`|G| = 75`) がある」は別 leaf で扱う。
-/

namespace OddOrder.Isaacs.Ch06

section /- 6C.1(a): 素数位数の固定点自由な自己同型 (p. 197) -/

/-- **Isaacs Problem 6C.1(a)** (p. 197) ⭐: 素数位数の自己同型 `α` が単位元しか固定しないなら
`G` は冪零。

`⟨α⟩` の作用が Frobenius であることを確認して Isaacs Thm 6.24 (Thompson) に流す。 -/
theorem isNilpotent_of_prime_orderOf_mulAut_of_fixedFree {G : Type*} [Group G] [Finite G]
    {α : MulAut G} {p : ℕ} (hp : p.Prime) (hord : orderOf α = p)
    (hfix : ∀ g : G, α g = g → g = 1) : Group.IsNilpotent G := by
  classical
  set A : Subgroup (MulAut G) := Subgroup.zpowers α with hAdef
  have hcardA : Nat.card ↥A = p := by rw [hAdef, Nat.card_zpowers, hord]
  have hAnt : Nontrivial ↥A := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hcardA]
    exact hp.one_lt
  let actA : MulDistribMulAction ↥A G := MulDistribMulAction.compHom G A.subtype
  refine isNilpotent_of_isFrobeniusAction (A := ↥A) (N := G) ?_
  intro a ha n hn hfixn
  -- `a ≠ 1` と `|A| = p` 素数から `⟨a⟩ = A`, したがって `α` は `a` の冪
  have hgen : Subgroup.zpowers ((a : MulAut G)) = A :=
    Subgroup.zpowers_eq_of_prime_card (by rw [hcardA]; exact hp) a.2
      (fun h => ha (Subtype.ext h))
  have hmemα : α ∈ Subgroup.zpowers ((a : MulAut G)) := by
    rw [hgen, hAdef]; exact Subgroup.mem_zpowers α
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmemα
  -- 安定化群は部分群なので `a` が `n` を固定すれば `α = a ^ m` も固定する
  have hastab : (a : MulAut G) ∈ MulAction.stabilizer (MulAut G) n := hfixn
  have hαstab : α ∈ MulAction.stabilizer (MulAut G) n := by
    rw [← hm]; exact zpow_mem hastab m
  exact hn (hfix n hαstab)

end

end OddOrder.Isaacs.Ch06
