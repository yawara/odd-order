/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.PGroup

/-!
# 指数が素数の部分群の `p`-元は核に入る (Isaacs Problem 8D.6 の Hint)

`X ≤ Y` が指数 `p` (素数) なら, `X` の `p`-元はすべて `X` の `Y`-核 `core_Y(X)` に入る。
したがって `X` の `p`-元が生成する部分群は `Y` で正規になり, Isaacs の Hint
「`O^{p'}(X) ◁ Y`」が従う。

## 証明

`g ∈ X` を `p`-冪位数の元とすると `⟨g⟩` は `p`-群で, 剰余類集合 `Y ⧸ X` (`p` 点) に
左乗法で作用し `⟦1⟧` を固定する。`p`-群の固定点数は `|Y ⧸ X| = p` と mod `p` で合同
(`IsPGroup.card_modEq_card_fixedPoints`) だから `p ∣ |Fix|`, さらに `1 ≤ |Fix| ≤ p` なので
`|Fix| = p`, すなわち `g` は全剰余類を固定する。核の特徴づけ
`Subgroup.normalCore_eq_ker` から `g ∈ core_Y(X)`。

## Main results

- `mem_normalCore_of_orderOf_eq_prime_pow` — 上記。
- `closure_primePow_normal` — `X` の `p`-元が生成する部分群は `Y` で正規。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

section /- 指数が素数の部分群 -/

variable {Y : Type*} [Group Y] {p : ℕ}

/-- **Isaacs Problem 8D.6 の Hint の核心**。`X ≤ Y` が指数 `p` (素数) なら,
`X` の `p`-冪位数の元は `X` の `Y`-核に入る。 -/
theorem mem_normalCore_of_orderOf_eq_prime_pow (hp : p.Prime) {X : Subgroup Y}
    (hX : X.index = p) {g : Y} (hg : g ∈ X) {k : ℕ} (hord : orderOf g = p ^ k) :
    g ∈ X.normalCore := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (Y ⧸ X) := Subgroup.index_ne_zero_iff_finite.mp (by rw [hX]; exact hp.pos.ne')
  have hcard : Nat.card (Y ⧸ X) = p := hX
  -- `⟨g⟩` は `p`-群
  have hpg : IsPGroup p ↥(Subgroup.zpowers g) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hord])
  -- `⟦1⟧` は固定点
  have hzle : Subgroup.zpowers g ≤ X := Subgroup.zpowers_le.mpr hg
  have hfix1 : (QuotientGroup.mk (1 : Y) : Y ⧸ X) ∈
      fixedPoints ↥(Subgroup.zpowers g) (Y ⧸ X) := by
    intro h
    have hmem : (h : Y) ∈ X := hzle h.2
    exact QuotientGroup.eq.mpr (by simpa using X.inv_mem hmem)
  -- 固定点の個数は `p`
  have hmod := hpg.card_modEq_card_fixedPoints (Y ⧸ X)
  rw [hcard] at hmod
  have hle : Nat.card ↥(fixedPoints ↥(Subgroup.zpowers g) (Y ⧸ X)) ≤ p := by
    rw [← hcard]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  have hpos : 0 < Nat.card ↥(fixedPoints ↥(Subgroup.zpowers g) (Y ⧸ X)) :=
    Nat.card_pos_iff.mpr ⟨⟨_, hfix1⟩, Set.finite_coe_iff.mpr (Set.toFinite _)⟩
  have hfixcard : Nat.card ↥(fixedPoints ↥(Subgroup.zpowers g) (Y ⧸ X)) = p := by
    -- `p ≡ |Fix| [MOD p]` と `p ≡ 0 [MOD p]` から `p ∣ |Fix|`
    have hdvd : p ∣ Nat.card ↥(fixedPoints ↥(Subgroup.zpowers g) (Y ⧸ X)) :=
      Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))
    have := Nat.le_of_dvd hpos hdvd
    omega
  -- したがって固定点集合は全体
  have huniv : fixedPoints ↥(Subgroup.zpowers g) (Y ⧸ X) = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
    rw [Set.ncard_univ, hcard, ← Nat.card_coe_set_eq, hfixcard]
  -- `g` は全剰余類を固定するので核に入る
  rw [Subgroup.normalCore_eq_ker, MonoidHom.mem_ker]
  ext q
  have hq : q ∈ fixedPoints ↥(Subgroup.zpowers g) (Y ⧸ X) := huniv ▸ Set.mem_univ q
  change g • q = q
  exact hq ⟨g, Subgroup.mem_zpowers g⟩

/-- `X ≤ Y` が指数 `p` (素数) なら, `X` の `p`-元が生成する部分群は `Y` で正規。

生成集合「`X` に属する `p`-冪位数の元」は共役で不変: 上の補題からそれらは
`core_Y(X) ◁ Y` に入るので共役も `X` に留まり, 位数は共役不変だから。 -/
theorem closure_primePow_normal (hp : p.Prime) {X : Subgroup Y} (hX : X.index = p) :
    (Subgroup.closure {g : Y | g ∈ X ∧ ∃ k : ℕ, orderOf g = p ^ k}).Normal := by
  classical
  set S : Set Y := {g : Y | g ∈ X ∧ ∃ k : ℕ, orderOf g = p ^ k} with hS
  -- 生成集合は共役で閉じている: `core_Y(X) ◁ Y` かつ位数は共役不変
  have hconj : ∀ y x : Y, x ∈ S → y * x * y⁻¹ ∈ S := by
    rintro y x ⟨hxX, k, hk⟩
    refine ⟨?_, k, ?_⟩
    · have hcore := mem_normalCore_of_orderOf_eq_prime_pow hp hX hxX hk
      exact X.normalCore_le ((Subgroup.normalCore_normal X).conj_mem x hcore y)
    · rw [← hk]
      exact orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective x
  have hinv : ∀ y : Y, (fun x => y * x * y⁻¹) '' S = S := by
    intro y
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hconj y x hx
    · intro x hx
      exact ⟨y⁻¹ * x * y, by simpa using hconj y⁻¹ x hx, by group⟩
  refine ⟨fun a ha y => ?_⟩
  have hmap : (Subgroup.closure S).map (MulAut.conj y).toMonoidHom = Subgroup.closure S := by
    rw [MonoidHom.map_closure]
    congr 1
    exact hinv y
  have : y * a * y⁻¹ ∈ (Subgroup.closure S).map (MulAut.conj y).toMonoidHom :=
    ⟨a, ha, by simp [MulAut.conj]⟩
  rwa [hmap] at this

end -- 指数が素数の部分群

end OddOrder.Isaacs.Ch08
