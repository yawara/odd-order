---
id: 1055
slug: isaacs-problems-campaign
title: "Isaacs 演習問題 (Problems) 形式化 campaign (scope 拡大 2026-07-22)"
created: 2026-07-22
---

# Isaacs 演習問題 (Problems) 形式化 campaign (scope 拡大 2026-07-22)

## 背景

**scope 拡大 (ユーザー裁定 2026-07-22、issue 9205 ③)**: lane a の割当 territory
(Isaacs 番号付き結果 + Pf 本文 + FeitSibley/NearFields Prop2) が全完済し、hub が
再配分をユーザーに escalate → **(E) Isaacs 演習問題 (Problems) を in-scope 化**して
lane a が形式化することに決定。従来の被覆測定 (`notes/isaacs/frontier_measured_2026_07_19.md`)
は「番号付き結果のみ」で演習を対象外にしていた ⟹ 本 campaign で演習も形式化対象に加える。

## 構造 (実測)

Isaacs FGT は各章を section (1A, 1B, ...) に分け、各 section 末に "Problems NX" として
演習を `NX.M` 形式で番号付け (例: 1A.1–1A.10, 1B.1–…, 1C.1–1C.8, 1D.1–1D.18,
1E.1–1E.8, 1F.1–…, 1G.1–…)。全 10 章で数百問。⚠ pdftotext は OCR ノイズあり
(記号・式散乱) → **statement は PDF ページ画像で確定** (Isaacs は PDF ページ = 書籍ページ + 13)。

## やること (上流優先 + 文書順)

各章の演習を section 順・番号順に形式化。置き場 = `OddOrder/Isaacs/ChNN_.../Problems*.lean`
(章ディレクトリ内の新 leaf、mathlib 互換記述名、`OddOrder.lean` 配線)。

- [ ] **Ch.1 Sylow** — 1A / 1B / 1C / 1D / 1E / 1F / 1G Problems
- [ ] Ch.2 Subnormality
- [ ] Ch.3 Split Extensions
- [ ] Ch.4 Commutators
- [ ] Ch.5 Transfer
- [ ] Ch.6 Frobenius Actions
- [ ] Ch.7 Thompson Subgroup
- [ ] Ch.8 Permutation Groups
- [ ] Ch.9 More Subnormality
- [ ] Ch.10 More Transfer

## 方針

- **番号付き結果と同じ強度**で形式化 (statement を PDF で確定 → theorem 化 → 実証明)。
- 演習が **mathlib 既存**または **repo 既存定理**で即従うものは、docstring で対応を記録
  (ラッパー方針: 純粋リネームは書かない)。
- 演習が**定義の導入のみ**のもの (例: 1A.5 が transitive action を定義) は、mathlib に既存概念が
  あれば docstring 記録、無ければ必要な範囲で定義。
- 前提インフラが repo/mathlib に無い演習は **honest な sorry-cite skeleton** を置かず、
  必要なら shared infra を先に build (claim-first)。真に blocked なら注記して次へ (文書順は維持)。
- **難易度・quick-win は着手基準でない** — 文書順で正面から。ただし 1 問で堂々巡りせず、
  genuine に blocked なら記録して先へ進み後で戻る。

## 進捗

**Ch.1 §1A** (`Ch01_Sylow/Problems.lean`、2026-07-22 着手):
- ✅ 実証明: **1A.1** (素数指数+最小性→正規) / **1A.4** (H·K=G⟹H·K^z=G + 帰結 H·H^x=G⟹H=⊤) /
  **1A.9** (|G|=pm,p>m→位数p部分群一意) / **1A.10(b)** (p群H, p∣[G:H]→p∣[N_G(H):H])。
- ✅ mathlib 対応 docstring 記録: **1A.6** (Burnside 軌道計数) / **1A.8** (Cauchy) / **1A.10(a)**
  (`fixedPointsMulLeftCosetsEquivQuotient`)。
- ✅ 実証明: **1A.2** (`card_doubleCoset_mul_card_inf_conj`: 二重剰余類 |HgK|·|K∩H^g|=|H||K|、
  H×K の両側作用 (h,k)•x=hxk⁻¹ の orbit-stabilizer)。
- ✅ 実証明: **1A.3** (`card_mul_card_inf` helper = |HK|·|H∩K|=|H||K| (1A.2 g=1) /
  `card_mul_le_card_mul_card_inf` (a)≤ / `card_mul_eq_iff_mul_eq_univ` (a)等号⟺HK=G /
  `mul_eq_univ_of_coprime_index` (b) coprime index⟹HK=G)。
- ✅ 実証明: **1A.5** (`isPretransitive_prod_iff`: G が α,β に推移的作用のとき積作用が推移的
  ⟺ G_a·G_b=univ、両方向とも安定化群と剰余類の交わり)。
- ⬜ 残 §1A: **1A.7** (真部分群 H の共役の和集合に入らない元 ≥|H|)。**正しい論法 (導出済)**:
  χ = G の G⧸H (右剰余類) 上の置換指標。(i) Burnside for G: `∑_{g∈G}χ(g)=|G|` (G は推移的ゆえ
  軌道 1 個)。(ii) Burnside for H (制限作用): `∑_{h∈H}χ(h)=|H|·(#H-軌道)=|H|·(#二重剰余類 H\G/H)
  ≥ 2|H|` (真部分群ゆえ二重剰余類 ≥2: H·1·H と HxH(x∉H))。(iii) `χ(g)=0 ⟺ g∉∪共役` ゆえ
  z=|{χ=0}|。z ≥ (|G|-|H|)-∑_{g∉H}χ(g) ≥ (|G|-|H|)-(|G|-2|H|)=|H|。mathlib =
  `sum_card_fixedBy_eq_card_orbits_mul_card_group` (Burnside)、H の制限作用の軌道=二重剰余類。
- ⬜ §1B–§1G 未着手。

## 完了条件

Isaacs Ch.1–10 の全演習問題が形式化 (実証明 or mathlib/repo 対応の docstring 記録)、
build green、AxiomsCheck OK。章単位で commit・issue checkbox 更新。

## 参照

- issue 9205 (scope 拡大の裁定元)、`notes/isaacs/frontier_measured_2026_07_19.md` (番号付き結果の完済正本)
- `references/isaacs/finite-group-theory.pdf` (statement 確定用、PDF ページ = 書籍ページ + 13)
- CLAUDE.md「トレーサビリティ」「ファイル粒度」「ラッパー方針」
