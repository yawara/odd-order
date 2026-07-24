---
id: 147
slug: q8-modular-char-theory-frozen
title: "【解凍】Q₈ Brauer-Suzuki: modular character theory 長期プロジェクト (Navarro spine)"
created: 2026-07-23
---

# 【解凍】Q₈ Brauer–Suzuki のための modular character theory 長期プロジェクト

## 状態: THAWED（ユーザー裁定 2026-07-25）— 書籍確定、PDF 確保待ち

**2026-07-25 にユーザーが解凍・書籍選定を確定**: spine = **Navarro 1998** *Characters and Blocks of
Finite Groups*（Cambridge LMS LNS 250）**Ch.1–7 一冊のみ、endgame = Ch.7 の Z\*-定理経由**
（Q₈ BS は Z\* の系; bridge は初等 — 詳細 = project spec note §2）。Dade 1971/Feit 1982 は
行間補完の併読に降格。PDF はユーザーが購入手配（正規無料版なし; Cambridge Core digital £92 =
章別 PDF DL 可、or 紙+スキャン → `references/navarro/` 収納 + `pdftotext -layout` 抽出）。
担当レーンは未割当（着手時に hub/ユーザーが指定）。

（旧状態: FROZEN、ユーザー裁定 2026-07-23。凍結根拠は下記に経緯として保持。）

Peterfalvi App C Prop 1（`rankOne_affine_nearField`）の残り唯一の `sorry` = **Brauer–Suzuki の
Q₈（`|S|=8`）ケース**を閉じるための **modular character theory 整備**プロジェクト。

**project spec 正本 = [`notes/meta/q8_modular_char_theory_frozen_project.md`](../notes/meta/q8_modular_char_theory_frozen_project.md)**
（目的・凍結根拠・書籍選定候補と基準・整備 infra の内訳・既存 repo 資産・pickup 手順を収録）。

## 凍結の経緯（2026-07-23 の根拠、記録）

- **FT critical path 外**（mathcomp は App.C 無しで FT 完成）・**terminal**（下流消費者ゼロ）。
- **mathlib-absent subfield**（modular 表現論は mathlib にも他の証明支援系にも先行形式化なし = 完全 greenfield）。
- **`|S| ≥ 16` は完成済**（`brauerSuzuki_of_quaternionSylow`）。Q₈ だけが別ルート（Gorenstein 明言:
  「all known proofs require the theory of modular characters」）。
- ⚠ **恒久対象外ではない** — 文献に完全証明があるので **in-scope の低優先・長期繰延**。cost/規模が理由
  ではなく terminal 性 + 別スケール infra が理由（[[feedback-cost-scope-not-a-criterion]] は維持）。

## 書籍選定 — ★確定（ユーザー裁定 2026-07-25）

- **spine = Navarro 1998 Ch.1–7**（1 Algebras / 2 Brauer Characters / 3 Blocks / 4–6 三大定理 /
  **7 The Z\*-Theorem フル証明** — Cambridge TOC 実測 2026-07-25）。Q₈ は Z\* の系
  （唯一 involution は isolated → `z` 中心 mod `O(G)` → Sylow 共役 bridge で
  `O_{2'}(G) ⊔ C_G(z) = ⊤`）。
- 旧 2 本立て（証明本体 = Dade 1971 の quaternion-defect block 分析）は**不要化**。
  Dade 1971 / Brauer 1964 / Feit 1982 は併読（Gorenstein posture）。
- Navarro 2018（McKay 本）にブロック章なし・2020 年代新刊なし → 再サーベイ不要（2026-07-25 web 実測）。
- 詳細な比較・入手ルートは project note §2。

## やること（bottom-up）

- [x] 書籍選定を確定（2026-07-25: Navarro 1998 Ch.1–7、Z\* 経由）
- [ ] PDF 確保（ユーザー購入 → references/navarro/ 収納 → pdftotext 抽出）→ Ch.5–7 精読で slice を絞る
- [ ] p-modular system → Brauer 指標 → 分解/Cartan 行列 → block・Brauer 対応 → 2nd/3rd main → Z\*
- [ ] Z\* → Q₈ bridge（初等）で `brauerSuzuki_quaternionSylow_q8` (2026-07-24 単離; RankOneAffineModel.lean) の `sorry` を置換

## 完了条件

`rankOne_affine_nearField` axiom-clean → Peterfalvi App C Prop 1 残 sorry ゼロ。

## 参照

- project spec: `notes/meta/q8_modular_char_theory_frozen_project.md`
- 前提調査: `notes/peterfalvi/appendixC_prop1_q8_brauer_suzuki.md`
- BS 本体（|S|≥16 完了）: [9318](9318-brauer-suzuki-theorem.md)
