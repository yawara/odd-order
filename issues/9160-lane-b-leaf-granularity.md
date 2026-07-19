---
id: 9160
slug: lane-b-leaf-granularity
title: "lane b: 新 leaf の粒度が CLAUDE.md 目安 (300-1500 行) を下回っている — Lemma 5 の区切りで統合を"
created: 2026-07-19
owner: lane b
priority: low (即時是正は不要。Lemma 5 = issue 2048 が締まった区切りで)
---

# lane b: 新 leaf の粒度が CLAUDE.md の目安を下回っている

⚠ **これは STOP でも是正命令でもない。** b の数学的な output は問題なく、
本 session で最多の行数 (13.2k) と feat 件数 (45) を landing している。
指摘は**ファイル粒度だけ**で、対応は **Lemma 5 (issue 2048) を締めた区切りで**よい。

## 実測 (2026-07-18 23:00 以降に b が新設した leaf、32 本)

| 統計 | b | 参考: c |
|---|---|---|
| 中央値 | **177 行** | 497 行 |
| 平均 | **246 行** | 647 行 |
| 最小 / 最大 | 46 / 687 | 70 / 1096 |

CLAUDE.md「ファイル粒度」の目安は **1 ファイル ≈ 300–1,500 行 / 1 トピック**で、
**「過度な細分化 (<~300 行が乱立) は固定 ~5s/ファイルが効いて逆効果」**と明記されている
(2026-06-05 の実測に基づく)。b の 32 leaf のうち **23 本が 300 行未満**。

### 300 行未満の leaf (23 本)

```
 46  Suzuki2Groups/Basic.lean
 57  GroupTheory/SolvablePrimeIndex.lean        ← hub が作成 (issue 9111)、b の責ではない
 93  Suzuki2Groups/ActualQuotientAction.lean
 96  Suzuki2Groups/CenterInvolutions.lean
103  Suzuki2Groups/CenterHomocyclic.lean
112  GroupTheory/NormalHallHeredity.lean        ← c が作成、b の責ではない
121  Suzuki2Groups/KSubgroupOrbit.lean
129  Suzuki2Groups/AgemoLayers.lean
136  Suzuki2Groups/HigmanDE.lean
143  Suzuki/ActualCenter.lean
145  Suzuki2Groups/HigmanAbelian.lean
158  Suzuki2Groups/HigmanEndomorphismLift.lean
160  GroupTheory/RepresentationTheory/ProjectiveFreeTwoDim.lean
162  Suzuki2Groups/HigmanFrattiniConsequences.lean
168  Suzuki/OrderThreeSuzukiCentralizer.lean
177  Suzuki2Groups/HigmanNormalAbelian.lean
187  GroupTheory/FittingHeredity.lean           ← c が作成、b の責ではない
204  Suzuki2Groups/HigmanNormalCover.lean
207  Suzuki2Groups/InvariantSummands.lean
213  Suzuki/ConjugacyInV.lean
218  Suzuki/ActualKActor.lean
276  Suzuki2Groups/QuadraticExtensions.lean
298  Suzuki2Groups/Types.lean
```

特に **`Higman*` 系 9 本** (`HigmanDE` / `HigmanAbelian` / `HigmanNormalAbelian` /
`HigmanNormalCover` / `HigmanFrattiniConsequences` / `HigmanEndomorphismLift` /
`HigmanIdempotents` / `HigmanIdempotentFamily` / `HigmanIdempotentCovariance` /
`HigmanIdempotentAction`) は**すべて issue 2048 = Suzuki Lemma 5 という単一の目標**への
部品であり、CLAUDE.md の「1 ファイル = 1 つの数学的トピック (定義+API、または 1 定理と
その支持補題群)」に照らすと **1〜3 ファイルに収まるべき塊**に見える。

## なぜ今すぐ直さなくてよいか

- 現時点でフルビルド時間に見える悪影響は出ていない (30 秒〜12 分で、支配要因は変更ファイルの
  再 elaboration であってファイル数ではない)。
- **作業中の frontier を細かい leaf に置くこと自体は CLAUDE.md が推奨**している
  (「active frontier を小さな leaf に残し、凍結クラスタを上流ファイルへ押し出して hub が束ねる」)。
  Lemma 5 に向けて動いている今の状態は、その推奨形とも読める。
- ⟹ **問題になるのは「Lemma 5 が締まった後もこの粒度で凍結すること」**。

## やること (Lemma 5 = issue 2048 が締まった時点で)

- [ ] `Higman*` 系の leaf を**トピック単位で統合**する。目安は 1 ファイル 300–1,500 行。
      分割の逆操作なので、`Suzuki2Groups/Higman.lean` のような topic file に寄せるか、
      idempotent 系 (`HigmanIdempotent*` 4 本、計 1,550 行) を 1 本にする等。
- [ ] 統合後も 2000 行を超えないこと。超えるなら prefix-split で分ける。
      ⚠ 分割の既知の落とし穴 3 件 (hub が本日踏んだもの):
      **(1) `… in` 修飾子チェーンは直後の宣言の一部ゆえ途中で切らない**
      (`end` が「名前のない section を閉じようとしている」エラーになる)、
      **(2) 末尾の空行**で `end` 行の位置判定が外れる、
      **(3) `private` 宣言がファイルを跨ぐと `Unknown identifier`** → public 化する。
- [ ] module 名が変わる統合になるので、下流の import を追随させる (leaf build で検証)。

## 完了条件

`Suzuki2Groups/` 配下の leaf が概ね 300 行以上になっている (frontier の作業中 leaf は除く)。

## 参照

- CLAUDE.md「開発規約 > ファイル粒度」(2026-07-09 明文化、mathlib 実測に基づく)
- issue 2048 (Suzuki Lemma 5 = b の現 frontier)
- issue 0124 (逆向きの watch: 1500 行超の分割)
