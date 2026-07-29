---
id: 9216
slug: subnormal-pi-subgroup-in-opicore
title: "shared infra claim: subnormal な π-部分群は O_π(G) に入る (SubgroupInAmbient.lean へ追加)"
created: 2026-07-29
---

# shared infra claim: subnormal な π-部分群は `O_π(G)` に入る

## 背景

Isaacs Problem 9C.1 (書籍 p. 288: Thm 9.24 の設定で `H`, `K` がともに subnormal なら
`U = 1` または `V = 1`) の hint が「さもなくば `O_p(G) > 1`」で始まる。
`U ⊴ H ⊲⊲ G` の `U` は subnormal な `p`-群なので、そこから `O_p(G) > 1` を出すのに
**「subnormal な `p`-部分群は `O_p(G)` に含まれる」**が要る。

repo 検索: `le_opiCoreInG_of_normal_of_isPiSubgroup` (`GroupTheory/SubgroupInAmbient.lean`)
は **normal** 版しか無い。subnormal 版は repo にも mathlib にも無い
(`grep -rn "IsSubnormal" OddOrder/ | grep -i "oPiCore\|opiCore"` は 0 hit)。
Fitting 経由 (`Ch02.le_fitting_iff` = 「`H ≤ F(G)` ⟺ nilpotent かつ subnormal」) でも
出せるが、`O_p(F(G)) = O_p(G)` と「冪零群の `p`-部分群は `O_p` に入る」の 2 段が要り
遠回りなので、鎖に沿った直接帰納で書く。

## claim (lane a, 2026-07-29)

**追加先**: `OddOrder/GroupTheory/SubgroupInAmbient.lean` (既存の `opiCoreInG` 一式の
canonical home。新規ファイルは作らない)。

## 中身 (設計)

`Subgroup.IsSubnormal` は mathlib の**帰納述語** (`top` / `step`) なので、
`K` について帰納する**強めた形**で回す:

```
K.IsSubnormal → ∀ S ≤ K, (S.subgroupOf K).Normal → IsPiSubgroup π S → S ≤ O_π(G)
```

* `top` (`K = ⊤`): `S ⊴ G` かつ π-群 ⟹ `Subgroup.IsPiGroup.le_oPiCore` (極大性)。
* `step` (`K ≤ L`, `K ⊴ L`, `L` subnormal): `S ≤ O_π(K)`
  (`le_opiCoreInG_of_normal_of_isPiSubgroup`) で、`O_π(K)` は
  `K` に characteristic ゆえ `L` に normal
  (`le_normalizer_opiCoreInG_of_le_normalizer`) かつ π-群
  (`isPiSubgroup_opiCoreInG`) なので IH が当たる。

⚠ 素朴に「`S` について帰納」しようとすると `step` の IH が `K` (π-群とは限らない)
についての主張になって回らない。`O_π(K)` を噛ませて `K` 側に持ち上げるのが要点。

系: `S.IsSubnormal → IsPiSubgroup π S → S ≤ O_π(G)` (`K := S` で適用)。

## 完了条件

- [x] `le_oPiCore_of_isSubnormal` が `SubgroupInAmbient.lean` に landing (sorry-free)
- [x] 9C.1 側から実使用

## 完了記録 (2026-07-29)

`le_oPiCore_of_normal_in_isSubnormal` (強めた形) + `le_oPiCore_of_isSubnormal` (系) が
`SubgroupInAmbient.lean` に landing。**一発 green** (設計どおり、修正 0 回)。
`#print axioms` = `[propext, Classical.choice, Quot.sound]`。

9C.1 (`relCore_thompsonWielandtCore_eq_bot_or_of_isSubnormal`,
`Ch09_MoreSubnormality/Problems9C.lean`) が 2 箇所で実使用:
`O_p(G) ≠ 1` の導出と、`U ≤ O_p(G)` (書籍 hint の「`U` が `p`-群」の場合)。

## 参照

* [issues/1055-isaacs-problems-campaign.md](1055-isaacs-problems-campaign.md) — §9C 着手
* `OddOrder/Isaacs/Ch03_SplitExtensions/Theorem315.lean` — `oPiCore` / `IsPiGroup.le_oPiCore`
* `OddOrder/GroupTheory/SubgroupInAmbient.lean` — `opiCoreInG` 一式
* 書籍ページ画像 `references/isaacs/pages/isaacs-p288-301.png` — 9C.1 の原文と hint
