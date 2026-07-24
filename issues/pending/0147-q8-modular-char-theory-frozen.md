---
id: 147
slug: q8-modular-char-theory-frozen
title: "【凍結】Q₈ Brauer-Suzuki: modular character theory 長期プロジェクト"
created: 2026-07-23
---

# 【凍結】Q₈ Brauer–Suzuki のための modular character theory 長期プロジェクト

## 状態: FROZEN（ユーザー裁定 2026-07-23）

Peterfalvi App C Prop 1（`rankOne_affine_nearField`）の残り唯一の `sorry` = **Brauer–Suzuki の
Q₈（`|S|=8`）ケース**を閉じるための **modular character theory 整備**を、**書籍選定を含む
deliberate な長期プロジェクト**として**凍結**する。lane c はこれを primary frontier にしない。

**project spec 正本 = [`notes/meta/q8_modular_char_theory_frozen_project.md`](../notes/meta/q8_modular_char_theory_frozen_project.md)**
（目的・凍結根拠・書籍選定候補と基準・整備 infra の内訳・既存 repo 資産・pickup 手順を収録）。

## 凍結根拠（要約）

- **FT critical path 外**（mathcomp は App.C 無しで FT 完成）・**terminal**（下流消費者ゼロ）。
- **mathlib-absent subfield**（modular 表現論は mathlib にも他の証明支援系にも先行形式化なし = 完全 greenfield）。
- **`|S| ≥ 16` は完成済**（`brauerSuzuki_of_quaternionSylow`）。Q₈ だけが別ルート（Gorenstein 明言:
  「all known proofs require the theory of modular characters」）。
- ⚠ **恒久対象外ではない** — 文献に完全証明があるので **in-scope の低優先・長期繰延**。cost/規模が理由
  ではなく terminal 性 + 別スケール infra が理由（[[feedback-cost-scope-not-a-criterion]] は維持）。

## 書籍選定（プロジェクト最初のタスク、pickup 時に確定）

- 証明本体: **Dade 1971**（Powell–Higman *Finite Simple Groups* Ch.VIII、Wikipedia の "detailed proof"）
  第一候補 / Brauer 1964（J.Algebra）/ 原典 Brauer–Suzuki 1959。
- infra: **Navarro 1998**（*Characters and Blocks*、clean）第一候補 / Feit 1982（網羅的）。
- 詳細な候補比較・選定基準は project note §2。

## やること（解凍時、bottom-up）

- [ ] 書籍選定を確定（証明 1 本を原文精読 → 最小 infra slice 確定）
- [ ] p-modular system → Brauer 指標 → 分解/Cartan 行列 → principal block → quaternion defect
- [ ] Q₈ BS を証明 → `brauerSuzuki_quaternionSylow_q8` (2026-07-24 単離; RankOneAffineModel.lean) の `sorry` を置換

## 完了条件（解凍時）

`rankOne_affine_nearField` axiom-clean → Peterfalvi App C Prop 1 残 sorry ゼロ。

## 参照

- project spec: `notes/meta/q8_modular_char_theory_frozen_project.md`
- 前提調査: `notes/peterfalvi/appendixC_prop1_q8_brauer_suzuki.md`
- BS 本体（|S|≥16 完了）: [9318](9318-brauer-suzuki-theorem.md)
