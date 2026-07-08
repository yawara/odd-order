---
id: 101
slug: s11-nineeleven-carveout
title: "HUB 裁定: S11_NineElevenCoherence = b 所有 carve-out + (9.11) caseA/caseB 分担境界"
created: 2026-07-08
---

# HUB 裁定: S11_NineElevenCoherence = b 所有 carve-out + (9.11) caseA/caseB 分担境界

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

# HUB 裁定 (2026-07-08 監視 tick): (9.11) の a/b 分担境界

## 経緯

- 監視 tick の step 1.5 で lane b の新規 `OddOrder/Peterfalvi/S11_NineElevenCoherence.lean`
  (commit 1e178611) を検出 — Pf S11 は lane a の namespace regex に掛かる + (9.11) は a の 1019 が
  進行中のクラスタ ⟹ trial merge を abort し hub 精査。
- 精査結果: b の着工は **9016 HUB RULING (hY producer = b / S07_Subcoherent)** の実施であり、
  1017 update²⁴ に設計裁定 (Dade-pair パラメータ化・S12/S13 非 import・a の §12 部品は入力) を
  self-flag 済み。a の 1019 側は caseB (9.7.b) 一様 route を S13 で fold まで landing 済み、
  caseA (9.7.a) は在庫のみで未組立。重複は「caseB 一様 route」のみで、b 自身が分担確認を要請していた。

## 裁定

1. **carve-out**: `S11_NineElevenCoherence.lean` は **lane b 所有** (0090 精神 — a の S11 namespace
   パターン内だが別ファイル隔離)。step 1.5 で b がこのファイルを編集しても逸脱でない。
   a がこのファイルを編集したら逸脱。b は他の S11 ファイル (`S11_MaximalII_III_IV` 等) には
   従来どおり触れない (import cite のみ可)。
2. **分担境界**:
   - **caseA (9.7.a) maximality 帰納** ((9.11.1) squeeze + (9.11.2)–(9.11.8) 反証) = **b** (本 leaf)。
   - **caseB (9.7.b) 一様 route** = **a** (S13 で landed 済: all-reducible corner +
     `caseB_coherent_sOf_H0Cprime_of_mixed` fold)。**b は caseB を再構築しない** — a の S13 結果を
     cite するか hypothesis 入力として受ける。
   - **full (9.11) assembly** (Clifford 二分の合成) = consumer 側 (S12/S13 は S11 leaf を import
     可能、循環なし)。実施 owner = a (gate-2 hY 消費地点)。
3. **R1 前倒し**: a は caseA を本裁定で手放す ⟹ 1019 の残 = caseB named §9 facts
   (hμmem/hunif/hDeg/anchor) + assembly のみ。完了次第 **endgame 計画 R1 (9000 typeP_Galois pivot)**
   へ移行する (ft_endgame_plan_2026_07_07.md)。
4. 本裁定は merge_monitor.md 🔒 所有マップに転記。b の staged merge は本裁定後に再実施・合流。

## 完了条件

- [ ] a が 1019 で本裁定を確認 (caseA 手放し + b leaf cite 化)
- [ ] b が caseB 非再構築を 1017 で確認
- [ ] full assembly landing 時に本 issue close

## 2026-07-08 追加 carve-out: S11_NineElevenCaseA.lean = b 所有 (entry point)

commit 00943a2c で新 leaf `OddOrder/Peterfalvi/S11_NineElevenCaseA.lean` を b が作成
(Hypothesis-level、namespace `OddOrder.Peterfalvi.S13`、S13_MaximalIII_IV import)。
`caseA_coherent_sOf_H0Cprime_of_refuter` = caseA (9.7.a) coherence を maximality refuter 節への
reduction (a の base case sOf_degreeSubfamily_isCoherent + b の skeleton
coherent_of_maximal_coherent_pair_refuted、witness は (9.8.d) count から genuine 導出)。

**S11_NineElevenCoherence (本 issue の carve-out) と同様、b 所有 carve-out として扱う**
(S13 namespace だが別 file 隔離、a の S13_MaximalIII_IV/S13_CoreStructure とは非衝突)。
a がこの file を編集したら逸脱。b は他の S13 file には従来どおり触れない (import cite のみ)。
merge_monitor 🔒 所有マップに転記要。
