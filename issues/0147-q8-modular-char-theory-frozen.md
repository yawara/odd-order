---
id: 147
slug: q8-modular-char-theory-frozen
title: "【解凍】Q₈ Brauer-Suzuki: modular character theory 長期プロジェクト (Navarro spine)"
created: 2026-07-23
---

# 【解凍】Q₈ Brauer–Suzuki のための modular character theory 長期プロジェクト

## 状態: THAWED — 書籍確定 + **PDF 確保済（2026-08-04）**、着手可能

**2026-07-25 にユーザーが解凍・書籍選定を確定**: spine = **Navarro 1998** *Characters and Blocks of
Finite Groups*（Cambridge LMS LNS 250）。Dade 1971/Feit 1982 は行間補完の併読に降格。
担当レーンは未割当（着手時に hub/ユーザーが指定）。

**2026-08-04: ユーザーが PDF を確保 → `references/navarro/` に収納済**
（`characters-and-blocks.pdf` + `.pdftotext.txt` + `SOURCE.md`）。
実測: スキャン 297p + OCR レイヤ、**PDF ページ = 書籍ページ + 10**、single-char token 率
20.8%（正常域）で Peterfalvi 型のグリフ分解は無く素の `pdftotext -layout` で grep 可。
⚠ 数式・記号の OCR 崩れは重い（`∈`→`G`、`N`→`TV`、`R`→`ii`、`Irr`→`IYT`）⟹ statement 確定は
ページ画像で。

### ⚠ 経路の訂正（2026-08-04、原文実測）— **Z\* は不要**

当初計画は「Ch.1–7、endgame = Z\*-定理、Q₈ BS は Z\* の系」だったが、**Navarro の Ch.7 は逆順**:

- Ch.7 冒頭（書籍 p.131）に "In this chapter, we finally give a proof of Glauberman's Z\*-theorem.
  **First, we need to prove the Brauer–Suzuki theorem**" — BS は Z\* の**系ではなく前提**。
- (7.1) が BS の statement、(7.2)–(7.6) が feeder、**書籍 p.139 "Proof of the Brauer–Suzuki
  Theorem" が p.145/146 で完結**。そのあと "To prove Glauberman's Z\*-theorem, we need one more
  result…" として (7.7)(7.8) を足し、(7.9) が Z\*。
- Navarro は **Q₈ ケースを名指しで狙っている**: "The deep part of the theorem involves the case
  when the Sylow 2-subgroup is the quaternion group of order 8, **and this is what we will focus
  on here**"（`|S| > 8` は Isaacs *Characters* Thm 7.8 に外出し = repo の
  `brauerSuzuki_of_quaternionSylow` に対応）。⟹ 本 issue の欲しいものと完全一致。

**⟹ 必要 slice は Ch.1–6 + (7.1)–(7.6) + BS 証明（書籍 pp.139–146）。Z\*(7.7)–(7.9) と
「Z\* → Q₈ bridge」は経路から落ちる**（bridge の初等補題を書く必要も無い）。
BS 証明が直接引くのは Cor (6.13) / Cor (5.8) + 第三主定理 / Lemma (5.13.b) / block orthogonality。

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

- **spine = Navarro 1998**（1 Algebras p.1 / 2 Brauer Characters p.16 / 3 Blocks p.48 /
  4 第一主定理 p.80 / 5 第二主定理 p.99 / 6 第三主定理 p.119 / 7 The Z\*-Theorem p.131 —
  **手元 PDF の目次で実測 2026-08-04**、2026-07-25 の Cambridge TOC と一致）。
  必要 slice は **Ch.1–6 + Ch.7 前半**（上記「経路の訂正」）。
  ~~Q₈ は Z\* の系~~ ← 誤り。BS は Ch.7 で直接証明され、Z\* がその下流。
- 旧 2 本立て（証明本体 = Dade 1971 の quaternion-defect block 分析）は**不要化**。
  Dade 1971 / Brauer 1964 / Feit 1982 は併読（Gorenstein posture）。
- Navarro 2018（McKay 本）にブロック章なし・2020 年代新刊なし → 再サーベイ不要（2026-07-25 web 実測）。
- 詳細な比較・入手ルートは project note §2。

## やること（bottom-up）

- [x] 書籍選定を確定（2026-07-25: Navarro 1998）
- [x] PDF 確保 → `references/navarro/` 収納 + `pdftotext -layout` 抽出（2026-08-04）
- [x] 経路の確定（2026-08-04 原文実測: **Z\* 不要**、BS は Ch.7 で直接証明。上記「経路の訂正」）
- [ ] BS 証明（書籍 pp.139–146）を精読し、引く結果を全部列挙して必要 slice を確定
      （既に判明: Cor (6.13) / Cor (5.8) + 第三主定理 / Lemma (5.13.b) / block orthogonality /
      (7.2) Klein four ケース / (7.3) basic set / (7.4) / (7.5) / (7.6)）
- [ ] p-modular system → Brauer 指標 → 分解/Cartan 行列 → block・Brauer 対応 → 第二/第三主定理
- [ ] (7.2)–(7.6) → BS 本証明で `brauerSuzuki_quaternionSylow_q8` (2026-07-24 単離;
      RankOneAffineModel.lean) の `sorry` を置換

## 完了条件

`rankOne_affine_nearField` axiom-clean → Peterfalvi App C Prop 1 残 sorry ゼロ。

## 参照

- project spec: `notes/meta/q8_modular_char_theory_frozen_project.md`
- 前提調査: `notes/peterfalvi/appendixC_prop1_q8_brauer_suzuki.md`
- BS 本体（|S|≥16 完了）: [9318](9318-brauer-suzuki-theorem.md)
