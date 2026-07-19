---
id: 9161
slug: dedup-cyclic-subgroup-uniqueness
title: "CLAIM+HUB: cyclic_subgroup_eq_of_card_eq の 3 重複を shared leaf へ集約 (cross-lane: Pf 側 call site あり)"
created: 2026-07-19
owner: lane c (提起) / hub (裁定 + 実施、2026-07-19 完了)
---

# cyclic_subgroup_eq_of_card_eq — 3 重複 + 汎用群論が BG 配下

## 事実 (2026-07-19 実測)

「有限巡回群で位数の等しい 2 部分群は一致する」= **汎用有限群論**が BG 配下に **3 コピー**ある:

| 場所 | 可視性 |
|---|---|
| `BG/Ch3_MaximalSubgroups/S10_LocalLemmasCore.lean:64` | public |
| `BG/Ch3_MaximalSubgroups/S10_BetaRadicalGlobal.lean:32` | private |
| `BG/Ch3_MaximalSubgroups/S12_Proposition1215.lean:44` | private |

⚠ **S10_LocalLemmasCore の docstring 自身が重複を認めて「shared helper へ hoist すべき」と
書いている**が、その後も 3 コピー目が増えている。

## なぜ今か

`OddOrder/GroupTheory/CNGroupStructure.lean` (issue 9133、Gorenstein Thm 12.1.5) の
「`A` は冪零」ステップで、巡回 Sylow `Q` の `Ω₁(Q)` の位数が `q` であることを出すのに要る。
`GroupTheory` leaf は `BG` を import できないので、現状 **4 コピー目を作るしかない**状態。

## ⚠ cross-lane — lane c 単独では実施しない

call site が **lane a territory の Peterfalvi 本文**にもある:
- `Peterfalvi/S10_MinimalSimpleBasic.lean:1030`
- `Peterfalvi/S16_NonExistenceG/SubgroupM.lean:729`

no-wrapper 方針ゆえ alias を残さず全 call site を repoint する必要があり、これは lane a の
ファイルを触る。territorial ルール上 lane c が単独でやるべきでないので hub へ上げる。

## 提案 (hub 裁定待ち)

1. 新 leaf `OddOrder/GroupTheory/CyclicSubgroupUniqueness.lean` に本体を置く。実装は
   S10_LocalLemmasCore:64 のものをそのまま (依存は mathlib のみ:
   `IsCyclic.card_powMonoidHom_ker` + `Subgroup.eq_of_le_of_card_ge`)。
2. BG の 3 コピーを削除し BG 内 call site を repoint (S10_LocalLemmasCore ×3 /
   S10_BetaRadicalGlobal / S12_Proposition1215 / S13_Theorem1310 / S12_Corollary129 /
   S12_Lemma1211 / S16_Lemma1413 / S16 TypeBridges) — **ここは lane c が実施可能**
   (全て `^OddOrder/BG/`)。
3. Peterfalvi 側 2 件の repoint は **lane a に依頼するか hub が実施**。あるいは hub 裁定で
   「c が Pf の 2 行だけ機械的置換してよい」とする (衝突リスクは極小)。

## 当面の lane c の回避策

`CNGroupStructure` 側は巡回性を使わずに済む形を先に探す。無理なら本 issue の解決を待つ。
**4 コピー目は作らない。**

## 完了条件

`OddOrder/GroupTheory/` に本体が 1 つだけあり、BG/Pf の 3 コピーが消え、全 call site が
新名を指し、full build green。

## 参照
- issue 9133 (CN 3-step dichotomy — 本 issue の需要元)
- 同種の dedup: 9130 / 9159 / 9109 / 9111
- CLAUDE.md「ラッパー方針」(alias を残さない) + 「claim-before-build」

---

## ✅ RULING + 実施完了 (hub, 2026-07-19)

### 裁定

lane c の事実報告を hub が独自再検証して**全て確認**: 3 コピーは逐語同一 (binder 名とコメントの差のみ)、
mathlib に対応物なし。提案 1 (新 leaf `OddOrder/GroupTheory/CyclicSubgroupUniqueness.lean`) を承認。

**提案 3 (cross-lane 部分) の裁定 = hub が全体を 1 コミットで実施**。lane c にも lane a にも振らない。
理由は territorial な配慮ではなく**技術的必然**: ラッパー方針により alias を残せないので
「本体新設 + 3 コピー削除 + 全 call site repoint」は**不可分**。c が BG 分だけ先行すれば Pf の
call site が宙に浮いて main が赤くなり、a を待てば issue 9133 がブロックされ続ける。
BG・Pf・GroupTheory を横断して 1 コミットで触りフルビルドで gate できるのは hub だけ。

⟹ lane c の「当面の回避策 (巡回性を使わない形を探す)」は**不要**。`CNGroupStructure` は
新 leaf を import して素直に使ってよい。**4 コピー目を作らず escalate した判断は正しい**。

### 実施結果 (full build green, 4505 jobs, error 0, AxiomsCheck 全 OK, sorry 23 不変)

- 新 leaf: `OddOrder/GroupTheory/CyclicSubgroupUniqueness.lean` (mathlib のみ依存・warning 0)
- 削除: public 1 (S10_LocalLemmasCore) + private 2 (S10_BetaRadicalGlobal / S12_Proposition1215)
- `OddOrder.lean` に import 登録

### ⚠ 実施して判明した 2 点 (次の dedup はこれを前提に)

1. **call site の修飾形は 3 種類に分かれていた** — 本 issue の repoint リストは「BG 内 call site」を
   一括りにしていたが、実際は:

   | 形 | 件数 | 対応 |
   |---|---|---|
   | 未修飾 `cyclic_subgroup_eq_of_card_eq` | 8 | consumer 8 file が全て `open OddOrder.GroupTheory` 済 ⟹ **無修正で新宣言に解決** |
   | `OddOrder.BG.Ch3.S10.…` (完全修飾) | 4 | 個別置換 |
   | **`S10.…` (部分修飾)** | **4** | 個別置換 |

   ⟹ 想定より変更は小さかった (大半が open 経由) が、**部分修飾形が罠**。

2. **🔥 実害**: hub が最初 `grep "BG.Ch3.S10.cyclic_…"` で探したため**部分修飾 `S10.` 形 4 件を取りこぼし**、
   3 コピー削除後に `Unknown identifier` でフルビルドが落ちた (`S12_Corollary129:279` 他)。
   **正しい探し方** = 識別子の前方一致を全部拾って修飾形ごとに数える:
   ```bash
   grep -rno "[A-Za-z0-9_.]*<名前>" OddOrder/ --include=*.lean | awk -F: '{print $3}' | sort | uniq -c
   ```
   宣言を消す**前**にこれを実行し、修飾形の内訳を確定してから着手すること。
   leaf build では検出できない (cross-file) ので、dedup は必ずフルビルドで gate する。

## 完了条件 — ✅ 達成

`OddOrder/GroupTheory/` に本体 1 つ、BG の 3 コピー消滅、全 call site が新名を指し、full build green。
