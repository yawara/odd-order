---
id: 1011
slug: hub-tp-w1-pin-mp-k
title: "HUB: Section16TypePStructure が tp.W1=mp.K を露出する要 (cd producer grid 用)"
created: 2026-06-23
---

# HUB: Section16TypePStructure が tp.W1=mp.K を露出する要 (cd producer grid 用)

## 背景

lane-b の cd producer (`section16CharacterData_of_isMinimalSimpleOdd`, FeitThompson.lean, POLE-1 charData,
issue 1004) を実装中に判明した **cross-lane architectural gap**。詳細 = `notes/peterfalvi/s12_s10_character_bridge.md`
更新¹⁶。

cd producer は character grid `ω`/`μ`/`ν` を構成する。これらは **`tp.W₁`-direction を row、`tp.W₂`-direction を
column** として index される (`Section16CharacterData.mu_definition` = Pf (13.1.e):
`Ind_W^S(ω_{ij}−ω_{0j}) = δ_j(μ_{ij}−μ_{0j})`、i は W₁ 方向)。

lane-b は grid source の certain-type machinery を **`mp.K` で** 構成済 (`certainTypeHypothesis_of_typeP_kappaHall`
/ `Section16MaximalPair.certainTypeS`/`certainTypeT`、build-green + axiom-clean)。S の自然な exceptional char 分解は
**κ-Hall complement 方向 = mp.K** なので、grid index も mp.K であるべき。

**問題**: cd producer は任意の `tp : Section16TypePStructure mp` を取るが、`Section16TypePStructure` には
**W₁ を mp.K に pin する field が無い** (W₁ は「W=S∩T の prime cyclic factor」という制約のみ; mp.K と**共役だが
等しい保証なし**)。実 `tp = section16TypePStructure_of_isMinimalSimpleOdd hG mp` は内部で
`section16TypePStructure_of_components mp.K mp.Kstar …` と呼び W₁:=mp.K に**真には設定している**が、producer の
`obtain`/casesOn が definitional reduction を block するため **`tp.W₁ = mp.K` が `rfl` で証明できない**
(実証: cd に `(hW1 : tp.W₁ = mp.K)` を追加 + section16Inputs で `rfl` 供給 → "Application type mismatch")。

tp producer は **POLE-1 tp[F] = lane-f 所有**ゆえ lane-b 単独で解決不可。

## やること

lane-f (tp producer 所有) が、以下のいずれかで `tp.W₁ = mp.K` (and `tp.W₂ = mp.Kstar`) を accessibly 露出:

- [ ] **案 A (推奨)**: `Section16TypePStructure` に field `W1_eq_K : W1 = mp.K` (and `W2_eq_Kstar : W2 = mp.Kstar`)
      を追加。`section16TypePStructure_of_components` は `W1` を直接受けるので、producer 側で `rfl` (or 容易) に
      discharge。下流 (cd) は `tp.W1_eq_K` で grid を mp.K に align。
- [ ] **案 B**: 補題 `section16TypePStructure_of_isMinimalSimpleOdd_W1_eq :
      (section16TypePStructure_of_isMinimalSimpleOdd hG mp).W1 = mp.K` を lane-f が提供 (producer の reduction を
      lane-f が証明; obtain/casesOn を proof-irrelevance で越える)。cd 側は条件付き
      `(hW1 : tp.W1 = mp.K)` を取り、section16Inputs がこの補題で discharge。

どちらでも cd は `tp.W1 = mp.K` を仮定して Step B-E (grid transport) を genuine に組める。

## 完了条件

cd producer (lane-b) が `tp.W1 = mp.K` / `tp.W2 = mp.Kstar` を build-green に入手できる
(field or 補題)。これにより lane-b は cd の grid (`ω`/`μ`/`ν`) を `certainTypeS`/`certainTypeT` から
`induce_chiColumn_diff_mu_diff` 経由で組める。

## 参照

- 設計: `notes/peterfalvi/s12_s10_character_bridge.md` 更新¹⁵/¹⁶
- lane-b 側 landed: `certainTypeHypothesis_of_typeP_kappaHall` / `Section16MaximalPair.certainTypeS`/`certainTypeT`
  / `S06.induce_chiColumn_diff_mu_diff` (commits dd65cb37 / aa7fd31e / 本セッション)
- 構造: `Section16TypePStructure` (FeitThompson.lean:220)、producer `section16TypePStructure_of_components` (:445) /
  `section16TypePStructure_of_isMinimalSimpleOdd` (:501)
- 関連: 1004 (cd producer) / 7005 (typeP_structure, lane-f)
