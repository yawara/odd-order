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

## 🧭 HUB RECONCILIATION (2026-07-12 監視 tick, Opus hub) — a の (10.8) threading 編集権を追認

**背景**: 監視 tick で lane a が S11_NineElevenCaseA を **編集** (merge a85869eb、9083 Phase E
machinery = `caseA_two_summand_inertia_inputs` / `NineElevenNormBound` / `C_eq_cSub` 系の signature
threading)。上記 2026-07-08 carve-out では「a がこの file を編集したら逸脱」ゆえ**名目上は範囲逸脱**。
hub が調査し、**逸脱 STOP でなく編集権追認**で reconcile:

**追認の根拠**:
1. **user+hub 裁定 (A) が authorize**: (10.8) knot 閉包 = **ユーザー 2026-07-12「Aで」+ HUB RULING
   (issue 9087)**。a の 9087 が threading target を明記 (`S11_NineElevenCaseA` の
   nineElevenPairBound/caseA_two_summand_inertia_inputs/caseA_nineElevenThree_count_inputs/
   caseA_nineElevenTwo_tiWitness を含む)。a はこの authorized 方向を実行しただけ (rogue 逸脱でない)。
2. **b の entry point は preserved**: `caseA_coherent_sOf_H0Cprime_of_refuter` (line 70) は無変更、
   a は decl を **1 本も削除/追加していない** (decl 16→16)。a が触ったのは 9083 Phase E machinery の
   proof/signature threading のみ (b の entry point 論法には非接触)。
3. **collision なし**: b は本 file に **非 ahead** (b-vs-main diff = 0、b の active work は S15_SAndT の
   2038 で S11 非接触)。concurrent 編集衝突は発生しない。
4. **merge-safety 全通過**: build green (4177 jobs) / AxiomsCheck OK / sorry 65→65 (regression なし) /
   新 axiom なし / conflict なし。

**追認内容 (時限)**: **(10.8) 閉包 (issue 1025) の期間中、a は S11_NineElevenCaseA の 9083 Phase E
caseA machinery 宣言を編集してよい** (threading = signature/proof の honest-route 化)。b の entry point
`caseA_coherent_sOf_H0Cprime_of_refuter` は b 専有・a 非接触を維持。3002/2038 供給編集権と同型の
時限 carve-out。**(10.8) 閉包 landing で失効** (以後 a の本 file 編集は通常どおり逸脱)。
恒久解: (10.8) 閉包後、この file の Phase E machinery が真に a 所有なら owner 再割当を検討
(現状は混在 leaf = b entry point + a Phase E machinery、decl 単位で判定)。

**⚠ 併記 — step 1.5 更新**: 以後 hub は S11_NineElevenCaseA について「a=Phase E machinery 編集可
(1025 期間)、b=entry point 専有」で判定 (decl 単位)。merge_monitor 🔒 所有マップにも本 reconciliation
を反映。
