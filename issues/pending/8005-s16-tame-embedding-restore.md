---
id: 8005
slug: s16-tame-embedding-restore
title: "BG §16 Thm I/II tame-embedding 構造の faithful 復元 (Pf consumer gate)"
created: 2026-06-15
---

# BG §16 Thm I/II tame-embedding 構造の faithful 復元 (Pf consumer gate)

## 背景

FT-critical §16 faithful 精査 (2026-06-15, commit `fdd8798a`) で、Thm I / Thm II が
tame-embedding 構造を lossy に落としていると判明。substantive 復元はユーザー裁可で **defer**
(speculative encoding を避け、Peterfalvi consumer の実需要に合わせる)。本 issue はその
deferred 復元タスク。**正本プラン = `notes/bg/s15_16_audit.md` §12.3**。

落ちている句:
- **Thm I** (`theoremI_…dichotomy`, mmd L4526): W=W₁×W₂ の normalizer-V 性質
  「N_G(W₀)=W ∀ nonempty W₀⊆W−W₁−W₂」+ W_i≠1、S=W₁S'/T=W₂T'/S'∩W₁=1/T'∩W₂=1/S∩T=W。
  (条件(5)「S,T とも II-V型」は `IsTypeNonI` で捕捉済 ⟹ 復元不要)。
- **Thm II** (`theoremII_tame_embedding`, mmd L4548): (Tii) supporting-subgroup system
  (M₁..Mₙ, (a)-(e)) + (Tiii) (Frobenius/cyclic complement/M_F not TI)。

## トリガー条件 (この issue を着手すべきとき)

**Peterfalvi が落ちた構造を消費し始めるとき**:
- **Thm I**: Pf `S10_MinimalSimpleStructure` (8.8) を**超えて** W=W₁×W₂ tame-embedding を
  消費する Pf 補題が出現したとき。
- **Thm II**: Pf (8.12)/(8.13) (現在 BG §14-15 gate で未形式化) が tame-embedding を
  消費し始めるとき。

現 lossy statement は現 consumer ((8.8), `S10_BGInterface`) には十分ゆえ、現 spine は block
しない (s15_16_audit §12.4)。⟹ Pf §10-13 が BG §14-15 landing で駆動し始めるまで保留。

## やること

- [ ] **Thm I 復元** (notes §12.3): mmd (1)(2) を復元。**(8.8) の tuple 形状
  (5 binder+9 conjunct, `⟨S,T,_W1,_W2,_W,hS,hT,hST,_hW,_hWcyc,hSnonI,hTnonI,hII,hcov⟩`) を
  壊さないこと** — clean 復元は (8.8) 同時更新が必須 (Pf レーン協調) か shape-preserving folding。
- [ ] **Thm II 復元** (notes §12.3): (Tii)(a)-(e) + (Tiii)。M_i family encoding (`Fin n → Subgroup G`)、
  per-M_i K_i (A0Set が K 依存)、(e) の「C_{H_i}(y)C_M(y)」積構造、(Tiii) Frobenius kernel/complement
  の **モデル化は Pf 消費形に合わせる**。
- [ ] 各復元後 **full build (S10_BGInterface / S10_MinimalSimpleStructure 含む) で consumer
  非破壊を検証**。sorry-neutral (既存 sorry の結論強化) を保つ (新 sorry'd theorem 追加は monitor abort)。

## 完了条件

Thm I / Thm II の statement が mmd L4526 / L4548 と faithful に一致 (tame-embedding 構造を含む)、
かつ Pf consumer (S10_BGInterface / S10_MinimalSimpleStructure + 新規消費側) が build-green。

## 参照

- 正本プラン: `notes/bg/s15_16_audit.md` §12 (特に §12.3 復元プラン、§12.1 consumer マップ)
- docstring 修正 (済): commit `fdd8798a`
- consumer: `OddOrder/Peterfalvi/S10_BGInterface.lean` (Prop 16.1)、
  `OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean` (Thm I, (8.8))
- mmd: `references/bg/local-analysis.mmd` Thm I=L4526 / Thm II=L4548 / "tamely imbedded" 定義=L4560

## 🧾 pending 移行 (2026-07-02 hub 全体レビュー)

本 issue は **trigger-gated task で trigger 未発火のまま** (Pf 側に tame-embedding 構造を
消費する補題は依然出現していない; BG 側 frontier は凍結)。open に置く意味が無いため
`issues/pending/` へ移動 — trigger (Pf consumer 出現) 発火時に再 activate。
