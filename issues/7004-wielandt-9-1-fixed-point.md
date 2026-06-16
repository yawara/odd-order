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

## 進捗 (2026-06-17)

- [x] `CoprimeFrobeniusAction` faithful 再設計（実 action `φ:L→MulAut H`, fixedByUE/E/U
      = `fixedSubgroup`; 旧構造は作用無しで証明不能だった）— `c55f6db2`（main 合流済）
- [x] 系(i)(ii) を本体から証明（`wielandt_fixedPoint_trivial_E_fixed`/`_U_fixed`）
- [x] **3 sorry → 1**（残=本体 `wielandt_fixedPoint_frobenius`）
- [ ] 本体 `wielandt_fixedPoint_frobenius` = `|C_H(UE)|^|E|·|H| = |C_H(E)|^|E|·|C_H(U)|`

## 方針: NO axiom, ボトムアップ完全形式化 (ユーザー裁可 2026-06-17)

本体の **勘定核心 (†)** `Wᵁ=0 ⇒ dim W=|E|·dim Wᴱ` は「E が非自明 `𝔽_p[U]`-既約**加群**に
自由作用」＝ **modular Brauer permutation lemma (𝔽̄_p 上, p′-群)** を要する。repo の Brauer は
**ℂ-指標版のみ**で `𝔽_p`-加群へ橋渡し不可。⟹ **欠落インフラを新規構築（axiom 無し）**。

- **FT 接続確認済**: (9.1) → Pf `S11`→`S12`/`S13`→`S14`→`S15`→`S16` → S16.Hypothesis → `feitThompson`
- **レーン干渉なし**: F は `GroupTheory/CoprimeAction` + 新規 `GroupTheory/RepresentationTheory/*`
  のみ編集; lane-b/g/h はこれら・`RepresentationTheory/` を一切 commit せず（検証済）

### 新規インフラ sub-pieces（正本 = notes/peterfalvi/s11_wielandt_91_design.md）

- [x] coprime 分解 `V=V^G⊕[V,G]`（dim 形 + `[V,G]^G=0` + `IsCompl`）— `WielandtCounting.lean` `a1bddfaa`
- [x] **step 2: el-ab 恒等式 (⋆) COMPLETE (modulo (†))** — `finrank_elab_identity` `95757a9f`。toolkit: `Vᵁᴱ=Vᵁ⊓Vᴱ`(`80a4d926`) + compatible-decomposition(`fadb55d6`) + averageMap 明示形(`87816c20`) + `[V,U]` L-不変性 via `MulAut.conjNormal`(`6e2df864`)
- [ ] (I-3) regular-orbit fixed-space count（抽象・Brauer-free）
- [ ] 系(i) を BG 3.3 + chief-series で **unconditional 化**
- [ ] (I-2) isotypic 分解（mathlib `IsSemisimpleModule`+`Maschke`）
- [ ] (I-1) **modular Brauer permutation lemma**（`Z(𝔽̄_p[U])` の char-0 trace-lift）← 核心
- [ ] (†) kernel-FPF count + (I-4) base change `𝔽_p→𝔽̄_p`
- [ ] (I-5) chief-series coprime（`C_{H/N}(X)=C_H(X)N/N`, L-invariant el-ab 系, 乗法性）
- [ ] assembly → `wielandt_fixedPoint_frobenius`

**見積 ~6-9 session**（I-1 が `p`-adic lifting まで要れば再 flag）。

## 完了条件

`CoprimeAction.lean` の本体 sorry が消え、`lake build OddOrder OddOrder.AxiomsCheck` green +
**新規 axiom 無し** + 実 sorry が（最終的に）3 本減（hub merge tick で検証）。

## 参照

- 正本: `references/peterfalvi/04.11_pp_50_57_On_the_Maximal_Subgroups_of_G_of_Types_II_III_and_IV.mmd` (9.1)
- 古典出典: Wielandt の定理 = [HB] Ch.XI Thm 12.4
- 解析メモ: `notes/peterfalvi/s11_maximal_II_III_IV.md:47`（§(9.1)）
- F の LAUNCH.md（2026-06-16 夜³ 指令）
