---
id: 124
slug: file-size-watch-1500
title: "1500 行超 leaf の分割 watch (S01_Solvable / TypeP1Criteria)"
created: 2026-07-19
---

# 1500 行超 leaf の分割 watch (S01_Solvable / TypeP1Criteria)

## 背景

2026-07-18 深夜の合流 tick (merge `ba8dfe04` = lane b / `e4407935` = lane c) で、
CLAUDE.md「ファイル粒度」の hub gate (1,500 行超ファイルへの追記を検出したら flag + 分割 issue 起票)
に該当した:

| file | 行数 | owner | 状況 |
|---|---|---|---|
| `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean` | 1560 | c | 本 tick で +156 (Cn 三段論法系) → 1500 を新たに超過 |
| `OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TypeP1Criteria.lean` | 1655 | c | 既に超過、本 tick で +16 |
| `OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TheoremsAE.lean` | 1800 | c | 2026-07-19 tick (merge `2a2df98`) で検出。本 tick では -60 行 (15.7(b) 強化に伴う恒真 disjunct 削除) と**減少方向**だが、watch 対象中で最大。`PisetBetaDisjoint.lean` (1469) は 1500 直下ゆえ次の追記で超過見込み |
| `OddOrder/Isaacs/Ch03_SplitExtensions/Basic.lean` | 1728 | a | 2026-07-19 tick (merge `1e1b0ed`) で追記 — 新規検出。Lem 3.1 本体は新 leaf `SplitExtensionUniqueness.lean` に切られており (lane trigger 遵守)、Basic.lean 側は薄い wrapper 追加のみ |

`OddOrder/AxiomsCheck.lean` (10475 行) は機械列挙 file ゆえ**恒久例外** (対象外)。

## 2026-07-19 hub 監査: 2000 行超は S03f_Thm36 の 1 件のみ — ただし**正規の宣言済み例外**

| file | 行数 | owner | 判定 |
|---|---|---|---|
| `OddOrder/BG/Ch1_Preliminary/S03f_Thm36.lean` | 3822 | (凍結) | **例外として妥当。分割 action は不要** |

hub が「hard 上限 2000 の唯一の違反が watch 漏れしている」と一旦疑ったが、**実測して否定された**。
記録として経緯を残す (同じ誤検出を次の tick で繰り返さないため):

- 本 file は **`set_option linter.style.longFile 4000` を 75 行目に持つ** — CLAUDE.md
  「意図的例外は per-file `set_option linter.style.longFile N` で明示」の手続きを**踏んだ上での例外**
  であり、規約違反ではない。`AxiomsCheck.lean` (10475 行 / opt-out 10600) と同じ扱い。
- **数学的に分割不能**であることが file 自身の docstring (95-104 行) に記録済み: 中身は
  `private theorem thm36_aux` **ただ 1 宣言** (106-3811 行) + `thm36` (3812 行) の計 2 宣言で、
  equations (3.6)-(3.37) を**単一の最小反例法の証明**で運ぶ。「IH を消費する Phase A-E は
  誘導の内側から切り出せないため、これ以上の分割は IH 自体の仮説化が要る」。
  ⟹ **flat prefix-split もディレクトリ化も適用できない** (宣言境界が存在しないため)。
  実際 Phase F ((3.38)、IH-free) は既に `S03f_OrbitParity` へ分離済みで、切れる分は切ってある。
- 2026-07-09 の commit `150611796` の message「2000 行超の 55 files を flat prefix-split —
  全 file が上限 2000 以下に」は、**この宣言済み例外を勘定に入れていない書き方**ではある
  (当時も本 file は 3822 行)。実害は無いが、次に同種の一括 pass をやるときは
  「opt-out 済み例外を除いて」と明記すること。

⟹ **本 issue の watch 対象外**。将来 `thm36_aux` の IH を仮説化する再構成をやるなら、それは
行数規約の話ではなく **elaboration コスト** (3.8k 行 ≈ 50s、CLAUDE.md「計測事実」に実測例として
記載) を下げる独立した最適化タスクとして起票する。

## 経過 (lane c, 2026-07-19)

- `PisetBetaDisjoint.lean`: **1473 → 1253 行** (1500 未満に復帰)。BG 15.7(e) の per-prime witness
  `exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI` (219 行) を新 leaf
  `S15_MF/WitnessPGroup.lean` へ移設した (issue 3022 の `p = |X|` 機構と同居させるため)。
  消費側は S16 の 2 file のみで、S16 は `S15_MF` hub 経由ゆえ **import 無変更**。
- `OpicoreCentralizer.lean`: 1485 行 (据え置き)。以後 15.7(e) の追記は `WitnessPGroup` 側に置くので
  ここは増えない見込み。
- `TypeP1Criteria.lean`: 1655 → **1640 行** (rank-2 議論を S15 へ抽出した分)。まだ 1500 超で watch 継続。
- `TheoremsAE.lean`: **1800 行のまま**。表の 1800 は既に `Msigma_inf_conj_isCyclic` 移設後の値で、
  本 tick で追加の減少は無い。watch 対象中で最大。

## やること

- [ ] どちらかが **2000 行 (本リポジトリの hard 上限、CLAUDE.md 2026-07-09 裁定)** に達したら hub が
      凍結境界で分割する。両者とも現状 2000 未満ゆえ **即時分割は必須でない** — 本 issue は watch。
- [ ] 分割時の形: ディレクトリ化を第一候補 — `S01_Solvable.lean` は pure re-export hub 化 →
      `S01_Solvable/<Topic>.lean` の topic leaves。`TypeP1Criteria` は既に `S16_MainResults/` 配下ゆえ
      flat な兄弟 prefix-split で足りる。いずれも module 名不変 = 下流 import 無変更。
- [ ] lane c 側 trigger の再確認: 同 file に**次の主結果番号**を書き始めるときは新 leaf を切る
      (同一 file 追記は「現に証明中の定理の helper」のみ)。

## 2026-07-19 hub tick 実測 (merge a+b+c 後)

1500 行超は **20 files** (AxiomsCheck 除く)。watch 表の 4 file は全て据え置き
(`S01_Solvable` 1560 / `TypeP1Criteria` 1640 / `TheoremsAE` 1800 / `Ch03/Basic` 1731)
— 本 tick では**いずれも増えていない**。2000 超は上記 `S03f_Thm36` (3822) の 1 件のみ。

1500–1900 帯には他に S04g_Thm418 (1963)・S10_MinimalSimpleBasic (1882)・
S7B2_NormalJ_PComplement (1879)・FrobeniusActionTI (1873)・AppC_FrobeniusClassSum (1868) 等が居るが、
**CLAUDE.md の gate は 1500 で flag / 2000 で分割必須**ゆえ、これらは flag 段階
(分割必須でない)。2000 に接近したものから個別に扱う。

## 完了条件

両 file が 1500 行未満に戻る (分割実施)、または frontier が離れて追記が止まり watch 不要と hub が判断。

## 参照

- CLAUDE.md「開発規約 > ファイル粒度」/ `notes/meta/merge_monitor.md` (hub gate)
- issue 0103 (機械分割の道具立て: preamble 再現・private public 化・sorry/宣言/namespace 文脈保存検証)
