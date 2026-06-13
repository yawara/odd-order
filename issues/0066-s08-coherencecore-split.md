---
id: 66
slug: s08-coherencecore-split
title: "S08_CoherenceCore (11.9k行) 分割 — build-critical 唯一の巨大frontier"
created: 2026-06-14
owner: hub (凍結境界 prefix-split)
---

# S08_CoherenceCore (11.9k行) 分割 — build-critical 唯一の巨大frontier

## 背景

`OddOrder/Peterfalvi/S08_CoherenceCore.lean = 11,969 行` (1500 行規約の **8 倍**)。
2026-06-14 実測:
- warm no-op full build = **37.5s** (closure traversal 下限; これは**分割で下がらない** —
  job 数は閉包深さ依存, CLAUDE.md「S09 4分割→3580 jobs 不変」)。
- **ただし pathological な巨大ファイルの per-file 再 elaboration は行数支配** (CLAUDE.md 実測
  S08 11.8k ≈21s/回, S03f 3.8k ≈50s)。⟹ **S08_CoherenceCore を touch するマージの build から
  ~15-20s 削れる + 編集ループ高速化**。
- repo の >1500 行は systemic (32 ファイル) だが、大半は ~5s 固定費支配で分割無益。**build 速度に
  効くのは S08_CoherenceCore (11.9k) が実質唯一** (次点 S16 6.8k / S09 6.7k / S07 6.5k は凍結 or
  非 frontier ゆえ優先度低)。

## タイミング (トリガー条件) ✅ 充足

**「B が S08_CoherenceCore の凍結 prefix を編集していない」**= prefix-split が B frontier と衝突しない状態。
- 2026-06-14: **充足**。B は case-B を**新 leaf `S08_CaseBCoherence.lean` (1273行) に分離**し、直近
  28 commits は S08_CoherenceCore を**一切触っていない** (`git log e8b019e8..88968a3e -- …S08_CoherenceCore`
  = 空)。S08_CoherenceCore の最後の編集 = (6.8) faithfulness fix (`11a8959b`, merge 済)。
- ⟹ **now が split 窓**。ただし B が再び S08_CoherenceCore に戻る可能性があるので、着手前に
  `git log --oneline main..b-peterfalvi -- …S08_CoherenceCore` で B の未マージ変更が無いことを再確認。

## やること (hub prefix-split 手順)

- [ ] B の未マージ commit が S08_CoherenceCore を触っていないことを確認 (触っていれば先にマージ or 延期)。
- [ ] S08_CoherenceCore の宣言を topic で 3-4 群に区分 (前方参照不可ゆえ任意の宣言境界で安全)。
      凍結済の coherence 基盤群を**上流ファイル**へ prefix-split、active/frontier 寄りを残置。
      候補境界: `S08_CoherenceTheorems` が cite する公開 API を leaf に残し、内部 helper 群を Core 上流へ。
- [ ] 新ファイルは `OddOrder.lean` に import 追加 (root closure); 下流 (`S08_CoherenceTheorems` /
      `S08_CaseBCoherence` / Pf §9-16) が壊れないこと。
- [ ] `lake build OddOrder OddOrder.AxiomsCheck` 緑 + AxiomsCheck OK + 実 sorry 不変。
- [ ] 分割後の各ファイル < 1500-2000 行目安。

## 完了条件

- S08_CoherenceCore が ~2-4 ファイルに分割され、最大ファイル < ~3000 行。
- full build 緑・AxiomsCheck OK・実 tactic sorry 不変。
- B の frontier (S08_CaseBCoherence) と非衝突。

## 参照

- 規約: `CLAUDE.md`「ファイル粒度」「分割の owner と trigger」, `notes/meta/merge_monitor.md`「サイズ watch」
- 関連: issue 0046 ((6.8) coherence 証明本体), issue 0063/0064 (済の S10/S05 split 前例)
- 計測: 2026-06-14 hub session (warm build 37.5s, S08 11,969 行)
