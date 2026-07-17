---
id: 3013
slug: lem45c-prop46-normal-p2
title: "BG Lem 4.5(c) + Prop 4.6: Ω₁(Z₂) noncyclic exp p / noncyclic normal S に R-normal E_p²"
created: 2026-07-18
---

# BG Lem 4.5(c) + Prop 4.6

## 背景

BG §4 の残ギャップ (survey は Lem 4.5(a) を stale に「未」記載していたが 4.5(a) 一般形は
`exists_normal_isElementaryAbelian_card_prime_sq_of_not_isCyclic` で済、commit で訂正済)。
実際の残 = **Lem 4.5(c)** と **Prop 4.6** (Prop 4.6 の内容 = 4.5(c))。共に done infra から S-sized 導出。

## statement (BG mmd)

- **Lem 4.5(c)** (L1498): p odd, R noncyclic p-group ⟹ `Ω₁(Z₂(R))` は noncyclic, exponent p。
- **Prop 4.6** (L1516): p odd, R p-group, S noncyclic normal subgroup of R ⟹ S は order p² の
  **R-normal** elementary abelian 部分群を含む。

## 証明

**Lem 4.5(c)**: Z = Ω₁(Z₂(R))。
- exponent p: Z₂(R) は class ≤ 2 ゆえ (p odd で p > 2 ≥ class) Prop 4.3(a) (§4A、Ω₁ of cl≤2 p-group
  has exponent 1 or p) を Z₂(R) に適用 ⟹ Ω₁(Z₂(R)) exponent p。
- noncyclic + order ≥ p²: 4.5(a) で R は normal E_{p²} = W を持つ。R nilpotent ゆえ [W,R]⊂W,
  [W,R,R]=1 ⟹ [W,R]⊆Z(R), W⊆Z₂(R)。W noncyclic elementary abelian (exp p) ⟹ W ⊆ Ω₁(Z₂(R)) = Z
  ⟹ Z noncyclic, |Z| ≥ p²。

**Prop 4.6**: Z = Ω₁(Z₂(S))。4.5(c) を S に適用 ⟹ Z exponent p, |Z| ≥ p²。Z char S ◁ R ⟹ Z ◁ R。
R p-group ゆえ Lem 1.22 (`normal_subgroup_card_pow_le_of_pGroup`, S01_Solvable) で Z は order p² の
R-normal 部分群を含む。elementary abelian (exp p の Z の部分群)。

## 既存 infra (reuse)

- **4.5(a)** `exists_normal_isElementaryAbelian_card_prime_sq_of_not_isCyclic` (S04_SmallRankBasic §4E)。
- **Prop 4.3(a)** §4A (S04_SmallRankBasic:281-、Ω₁ of cl≤2 p-group exponent 1 or p)。
- **Lem 1.22** `OddOrder.BG.Ch1.S01.normal_subgroup_card_pow_le_of_pGroup` (S01_Solvable:1322)。
- Z₂(R) = upperCentralSeries / center of quotient。`Ω₁` = `Omega R p 1` / `omega1*`。

## 完了条件

Lem 4.5(c) + Prop 4.6 を book strength・sorry-free・axiom-clean。AxiomsCheck 登録、survey 正本
Lem 4.5 / Prop 4.6「済」。

## 参照

- BG mmd L1496-1516、既存 S04_SmallRankBasic (4.5(a)(b), 4.3(a))
