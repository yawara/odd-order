---
id: 5002
slug: bg-s12-triage-lemma121
title: "BG §12 triage + Lemma 12.1 (E の基本構造) — §11.5-7 は 10.13 ブロック確定後の D-lane frontier"
created: 2026-06-10
---

# BG §12 triage + Lemma 12.1 (E の基本構造) — §11.5-7 は 10.13 ブロック確定後の D-lane frontier

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 背景 (2026-06-10 triage)

Prop 10.11 完成 (issue 5001 closed) 後の D-lane frontier 選定。

**§11 残 3 定理は D で進められない** (mmd L2997-3056 で確認済、再 triage 不要):
- **Thm 11.5** (`sylow_p_isCommutative`@S11:812): 証明が **Lemma 10.13(c)** を明示使用
  (「all of the subgroups in ℰ¹(A)−{X} are conjugate in P」)。
- **Cor 11.6** (`omega1_eq_and_centralizer_trivial`@S11:820): 第一歩が「P is abelian of rank two」
  = Thm 11.5。推移ブロック。
- **Thm 11.7** (`MsigmaA_normal`@S11:827): Cor 11.6(a)(c) + **Prop 10.11(d)** (✅ 完成済) +
  Prop 10.10(c) + Lem 10.4(c)。Cor 11.6 経由で推移ブロック。

Lemma 10.13 は D 対象外 (group-level Additive diamond、休止 `c-bg-s10` base 4000 委任)。
⟹ **D の次は §12** (`S12_E.lean`、20 sorry の scaffold、τ₁/τ₂/τ₃ 定義 + statement 済)。

## やること

- [x] §12 各 sorry の依存 triage: mmd L3029- を読み、§11 (Thm 11.5/11.7) 依存のものと
      §10-only のものを分類 (file docstring は「imports §11 intentional」と言うが定理単位で要確認)。
      Lemma 12.1 (`subgroupE_basic`, mmd L3035) は r(E)≤2 / E' nilpotent / Sylow abelian の
      基本パッケージで、おそらく Prop 10.9/10.11 + Thm 4.20 で §11 非依存 — 第一 leaf 候補。
      **⟹ 2026-06-10 完了: 着手可能 5 件 (12.1 / 12.2(a) / 12.17 / 12.19 / 12.18) vs
      ブロック 14 件 (根 = Thm 11.7 直接使用の 12.3 と Lem 10.13 直接使用の 12.7)。
      詳細 = notes/bg/s12_subgroup_e.md「2026-06-10 D-lane triage」**。
- [ ] 第一 leaf の実装 (issue 5001 の実装知見が直接効く: Hall σ'-overgroup パターン、
      Thm 4.20(a)(c)、`rank_le_iff`+`alpha_subset_sigma` の r(E)≤2 論法は §12 でも頻出)。
      **レシピ確定済 (notes 同節): (a) は Thm 4.20(a) 代替 (Thm 10.2 の M'/M_σ nilpotent は
      repo 未収載のため)。⚠ 12.1(e) `E₂ ⊴ E₁⊔E₂` は旧 SubgroupESetup で反例があり偽 —
      field `E₁₂_hall` 追加で原文 faithful 化 (constructor 使用ゼロで波及なし)**。
- [x] §11 依存と判明した定理は §11 と同様 10.13 ブロックとして notes に記録 (forward-axiom 化はしない)。

## 参照

- Prop 10.11 実装知見: `issues/closed/5001-bg-prop1011-sigma-complement-rank.md` 完了記録
- §11 ブロック詳細: `notes/bg/s10_spine_blockers.md` 2026-06-10 夕更新
