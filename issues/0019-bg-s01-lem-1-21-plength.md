---
id: 19
slug: bg-s01-lem-1-21-plength
title: "BG §1 Lemma 1.21 p-length one package を形式化する"
created: 2026-05-25
---

# BG §1 Lemma 1.21 p-length one package を形式化する

## 背景

BG Lemma 1.21 は p-length one の基本性質 5 部。BG 固有の definition
`G = O_{p',p,p'}(G)` を使うため、`S01_Solvable.lean` では将来 `PLength.lean`
へ切り出す予定とだけ記録されている。

§6 と §16 の structural condition で使うため、早めに定義だけでも固定しておきたい。

## やること

- [ ] `p-length one` の定義を `OddOrder.GroupTheory` または BG §1 ローカルに置くか決める。
- [ ] `O_{p',p,p'}` を既存 `oPiCore` API でどう表すか決める。
- [ ] Lemma 1.21(a)-(e) の statement を分割して実装する。
- [ ] 後続 BG §6 / App.A で使う名前を notes に記録する。

## 完了条件

- p-length one の定義場所と名前が確定している。
- BG Lemma 1.21(a)-(e) が sorry-free、または重い部分が個別 issue に分割済み。
- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` が通る。
- `lake build OddOrder.AxiomsCheck` が通る。

## 参照

- `notes/bg/s01_solvable.md`
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`
- `references/bg/local-analysis.mmd` L564-L577 付近
