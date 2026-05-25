---
id: 16
slug: bg-s01-thm-1-13-critical
title: "BG §1 Thm 1.13 Thompson critical subgroup を形式化する"
created: 2026-05-25
---

# BG §1 Thm 1.13 Thompson critical subgroup を形式化する

## 背景

BG Thm 1.13 は Thompson critical subgroup theorem。監査メモでは Isaacs 4.31
(Thompson P×Q lemma) との同一視が誤りで、別 theorem と整理済み。

後続 §13 で参照されるため、定義・存在定理・Aut_G(H) が p-group であることの表現を
独立 issue として扱う。

## やること

- [ ] BG Thm 1.13 の原 statement を mmd で確認する。
- [ ] critical subgroup の構造 (`[H,G] ≤ Z(H)`, class ≤ 2, exponent p, characteristic)
      を表す Lean 定義が必要か判断する。
- [ ] `Aut_G(H)` の p-group 性の表現方法を決める。
- [ ] 必要な shared module を `OddOrder.GroupTheory` 配下に最小追加する。
- [ ] BG-facing theorem を `S01_Solvable.lean` に追加する。

## 完了条件

- BG Thm 1.13 の statement と依存定義が Lean 上で確定している。
- 証明が sorry-free、または未証明なら明確に別 issue へ分割されている。
- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` が通る。
- `lake build OddOrder.AxiomsCheck` が通る。

## 参照

- `notes/bg/s01_solvable.md`
- `references/bg/local-analysis.mmd` L461-L472 付近
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`
- `OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean`
