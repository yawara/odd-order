---
id: 4008
slug: hub-basic-structure-cross-lane
title: "HUB: basic_structure (13.2) carrier enrich は cross-lane (lane-f POLE-1) — 前回診断の lane-local 前提を訂正"
created: 2026-06-23
---

# HUB: basic_structure (13.2) carrier enrich は cross-lane (lane-f POLE-1) — 前回診断の lane-local 前提を訂正

## 背景

lane-c 再開 (main マージ後) の精査で、前回診断 (commit `c5100441`,
`notes/peterfalvi/s15_s_and_t.md` 旧「lane-c carrier 診断」節) の**中核前提が誤り**と判明。

- **数学的洞察は正しい**: `basic_structure` (13.2, `S15_SAndT.lean:239`) の U-side 結論
  (`UW1_frobenius`, `U_commutative`) は、`hyp.U`/`hyp.W1` を type-P 分解の `data.U`/`data.W1` と
  reconcile しないと転送できない。`Hypothesis` は `S_deriv_eq_PU : derivedInG S = P ⊔ U` を
  **join のみ**で持ち complement 性 (`P ⊓ U = ⊥`) を欠くため、`typePData_of_isTypeNonI` の自前 U と
  一致保証がなく blocked。これは正しい。
- **誤りだった前提**: 「`Hypothesis` は producer 無し ⟹ field 追加は C 所有・安全」。
  実際は `S15.Hypothesis` は `sectionSixteenHypothesis_of_inputs`
  (`OddOrder/FeitThompson.lean:655`) で **record literal として明示構成**され、各フィールドを
  `inp : Section16Inputs G` から取る。`Section16Inputs` の producer は
  `section16Inputs_of_isMinimalSimpleOdd` で、type-P 部分は
  `section16TypePStructure_of_isMinimalSimpleOdd` (= **lane-f POLE-1, issue 7005**)。

## 問題: enrich は lane-local でなく cross-lane

`S15.Hypothesis` に `Sdata : TypePData hyp.S` (+ `Sdata.U = hyp.U` 等の reconciliation) を足すと:

1. `FeitThompson.lean:655` の record literal が壊れる (**lane-c 非所有ファイル**)。
2. ソースとして `Section16TypePStructure` / `section16TypePStructure_of_components` /
   `Section16Inputs` にフィールド追加が必要 (**すべて FeitThompson.lean = lane-f 領域**)。
3. discharge には「**指定 complement `U` を持つ `TypePData mp.S` を構成する**」実作業が要る。
   `typePData_of_isTypeNonI` は自前 U を作るので不可。`hyp.U` の源
   `exists_kappaHall_invariant_complement_to_MF` (`S14_TypePComplement.lean:85`) は内部で
   Schur–Zassenhaus complement (`M_F ⊓ U = ⊥`) を作りながら**返り値型で破棄** (`obtain ⟨U, -, …⟩`)。
   complement 性の露出 + `TypePData` 化が lane-f 作業。

lane-f の POLE-1 producer は既に sorry なので obligation 自体は吸収されるが、**TypePData の complement
指定構成は genuine な新作業**で、basic_structure は授権があっても multi-session の cross-lane 仕事。

## frontier 評価: lane-c S15 は現在 ungated closable work が無い

実 sorry 23 本は全て cross-lane gated (詳細 = `notes/peterfalvi/s15_s_and_t.md`「frontier 全評価」節):
basic_structure 系は上記 carrier (lane-f)、char cascade は lane-b §3-13、§15 固有 Fitting (`card_Q_eq`
`|Q|=q^p` 等) も同じ type-P carrier に bottom out、`normalizer_W1` は §13 multi-obligation (lane-h 確認済)。

## やること (HUB の判断 — 選択肢)

- [ ] **(A)** lane-c に cross-lane enrich を授権 (FeitThompson.lean + Section16TypePStructure 編集可)。
      basic_structure を unblock する唯一の honest path。ただし lane-f POLE-1 (issue 7005) と境界を共有。
- [ ] **(B)** enrich を lane-f に割当 (Section16TypePStructure に `Sdata`/`Tdata : TypePData` を
      reconciliation 付きで carry させる)。lane-c は cite 側。issue 7005 にこの obligation を追記。
- [ ] **(C)** lane-c を別の FT-path セグメントへ再配置 (現 S15 frontier が全 cross-lane gated のため)。

## 完了条件

HUB が (A)/(B)/(C) を決定し、対応する LAUNCH.md / issue 7005 / relane を更新したら closed。

## 参照

- 訂正対象: commit `c5100441`、`notes/peterfalvi/s15_s_and_t.md`「lane-c carrier 診断」節 (訂正済)
- carrier: `OddOrder/FeitThompson.lean:655` (`sectionSixteenHypothesis_of_inputs`),
  `:445` (`section16TypePStructure_of_components`), `:501`
  (`section16TypePStructure_of_isMinimalSimpleOdd` = lane-f POLE-1)
- complement 源: `OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePComplement.lean:85`
- 関連: issue 7005 (lane-f POLE-1 tp producer), issue 4007 (relane), 4003 (s15 eta carrier)

---

## 解決 (2026-06-23, ユーザー裁可 = (A))

**ユーザー裁可 = (A) lane-c に POLE-1 carrier 構築を授権** (relane #3)。lanes 等価方針 ⟹ carrier/BG 作業も
lane-c 可。POLE-1 tp producer carrier を **lane-f→lane-c 移譲**:

- **lane-c 新スコープ**: `S14_TypePComplement.lean` (complement 性 `M_F⊓U=⊥` を返り値露出) +
  `FeitThompson.lean` tp 系 def (`Section16TypePStructure`:220 / `section16TypePStructure_of_components`:445 /
  `section16TypePStructure_of_isMinimalSimpleOdd`:501 / `Section16Inputs`:95 tp フィールド)。指定 complement U を
  持つ `TypePData mp.S`/`mp.T` を構成 → `Section16TypePStructure` に `Sdata`/`Tdata` + reconciliation 追加 →
  §15 `basic_structure` 系を unblock + **POLE-1 (critical path) 前進**。
- **lane-f**: hderF/Prop16.1 に集中、tp carrier は cite のみ、`mp` は F のまま。
- **co-edit 境界**: FeitThompson.lean は def 単位で F=mp+Prop16.1 / B=cd / C=tp の 3 者共有 (signature-first)。
  `S14_TypePComplement` は F が cite、C が育てる。
- 反映: lane-c/lane-f LAUNCH.md、merge_monitor.md (所有マップ + owned_re[C+=S14_TypePComplement] +
  shared_re[+=FeitThompson] + relane#3 note)、cron (`36d0bfee`)。issue 7005 (lane-f POLE-1) は C が carrier を
  landing したら consumer 側で解消に向かう。

CLOSED。
