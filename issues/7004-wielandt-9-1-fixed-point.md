---
id: 7004
slug: wielandt-9-1-fixed-point
title: "Pf (9.1) Wielandt fixed-point formula — CoprimeAction.lean 3 sorries"
created: 2026-06-16
owner: lane-f
---

# Pf (9.1) Wielandt fixed-point formula — CoprimeAction.lean 3 sorries

## 背景

2026-06-16 (夜³): F は §16 / POLE-2 / Pf がすべて 2 long pole（H `typeP_duality`,
B `(6.8)`）に gated で STANDBY だった。hub の実コード再検証で両 trigger 未達を確認した一方、
**唯一の非衝突 ungated・FT-closure タスク = Wielandt (9.1)** が `CoprimeAction.lean` に
3 本の実 sorry として残存していると判明（141 のうち 3 本）。ユーザー裁可で F を reactivate。

- 依存的に ungated: 入力 = `IsFrobeniusGroup`（Isaacs Ch06 済）+ coprime/card のみ。
- 非衝突: 消費側は Pf §11（`S11_MaximalII_III_IV`）の docstring 参照のみ（term 未配線）。
- FT-path 必然: Pf §11 (9.2)-(9.9) の全 character count が (9.1) ベース。

## やること

- [ ] `wielandt_fixedPoint_frobenius`（`CoprimeAction.lean:113`）= 本体
      `|C_H(UE)|^|E| · |H| = |C_H(E)|^|E| · |C_H(U)|`
- [ ] `wielandt_fixedPoint_trivial_E_fixed`（:121）= 系(i) `C_H(E)=1 ⇒ fixedByU=⊤`
- [ ] `wielandt_fixedPoint_trivial_U_fixed`（:129）= 系(ii) `C_H(U)=1 ⇒ |H|=|C_H(E)|^|E|`
- [ ] 必要なら `CoprimeFrobeniusAction` 構造体を再設計（証明に足る field へ）
- [ ] mathlib に Wielandt/coprime-action fixed-point 基盤があるか先に確認

## 完了条件

`CoprimeAction.lean` の 3 sorry が消え、`lake build OddOrder OddOrder.AxiomsCheck` が green +
AxiomsCheck 違反なし + 実 sorry が 3 本減（hub merge tick で検証）。

## 参照

- 正本: `references/peterfalvi/04.11_pp_50_57_On_the_Maximal_Subgroups_of_G_of_Types_II_III_and_IV.mmd` (9.1)
- 古典出典: Wielandt の定理 = [HB] Ch.XI Thm 12.4
- 解析メモ: `notes/peterfalvi/s11_maximal_II_III_IV.md:47`（§(9.1)）
- F の LAUNCH.md（2026-06-16 夜³ 指令）
