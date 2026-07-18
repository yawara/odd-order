---
id: 9150
slug: subnormal-vs-normal-audit
title: "HUB: mmd 由来の normal/subnormal 取り違えを全 repo 監査"
created: 2026-07-18
---

# HUB: mmd 由来の normal/subnormal 取り違えを全 repo 監査

## 背景

**`references/**/*.mmd` (Nougat 抽出) は subnormal `⊲⊲` を単一の `\triangleleft` に
潰している。** mmd だけを典拠にすると、教科書が subnormal を要求する仮説を
**normal で形式化してしまう**。

2026-07-18 に lane a が Isaacs §9B で実害を確認 (issue 1037):

- **Isaacs 9.13 / 9.21 (Schenkman)** は原典 (PDF p.281 / p.283) では `S ⊲⊲ G` だが、
  本 repo は **`S.Normal` で形式化**していた。
- その結果 **Thm 9.10 (Wielandt automorphism tower) が「書籍に normal/subnormal の
  行間ギャップがある」と誤診され frontier が停止**していた (実際にはギャップなし)。
- 同じ §9B でも 9.15/9.16/9.18 は**地の文が "arbitrary subnormal subgroup" と
  明言していたため正しく `IsSubnormal` で入っている**。
  → **地の文が曖昧な定理だけが危ない**。

## 検出方法

```
pdftotext -f <page> -l <page> <pdf> -
```
で `⊲⊲` → **`«`**、`⊲` → **`<`** に落ちる。決定打は `Read` で PDF ページ画像。
Isaacs は **PDF ページ = 書籍ページ + 13** (他の 2 冊は要実測)。

grep レシピ (Isaacs 全体で subnormal 記号を含む文を拾う):
```
pdftotext references/isaacs/finite-group-theory.pdf - | grep -n "«"
```

## 監査結果 (Isaacs、2026-07-19 hub 実施)

**手順**: `pdftotext` で全文抽出 → 文字文脈の `«` (両側が大文字の部分群記号) だけを拾い、
作用ドット `a«g` の OCR ノイズ (13 行) を除外 → **真の `⊲⊲` 使用 28 件**を特定 →
うち 23 件を **PDF ページ画像**で 1 件ずつ確認 (6 エージェント並列、read-only)。

**結果: 21 件 OK / 2 件 MISMATCH**。

- OK: 1.46 / 2.5 / 2.6 / 2.7 / 2.8 / 2.10 / 2.11 / 2.12 / 2.13 / 4.8 / 9.3 / 9.6 / 9.8 /
  9.13 / 9.20 / 9.21 / 9.31。**9.13 と 9.21 は issue 1037 対応で修正済**を確認。
- **MISMATCH: Lem 9.26 / Cor 9.27** → **issue 0125** に切り出し (lane a へ配分)。
- ⚠ 副産物として、**「書籍に gap がある」という誤った注記 3 件**を発見
  (ThompsonWielandt.lean:143-145 / 180-181、PResidual.lean:410-411)。
  ページ画像で確認したところ書籍は一貫して `V ⊲⊲ H` と書いており、gap は存在しない。
  issue 1037 と同じ mmd 由来の誤読。0125 に訂正項目として記載。

**機械照合の第一印象は当てにならない**という教訓: 宣言の近傍 22 行で最初に現れる
`Normal`/`IsSubnormal` トークンを拾う方式では、2.6 のように「S は subnormal だが
M は minimal **normal**」という結果で M の binder を誤って拾う。**必ず statement を読む**。

### BG / Peterfalvi

未走査。両書は subnormal の使用が少ないと見込まれるが要確認 (下記チェックリスト)。

## やること

- [x] Isaacs 全体を `«` で走査し、`⊲⊲` を含む定理番号を列挙する。(28 件)
- [x] 各番号について repo の対応宣言の binder が `IsSubnormal` か `Normal` かを照合。(23 件確認、MISMATCH 2)
- [ ] BG / Peterfalvi でも同様の走査 (両書とも subnormal を使う箇所は少ないはずだが要確認)。
- [ ] 取り違えが見つかったら、**normal 版は消さず**に subnormal 版を追加する
      (normal 版の方が bound が鋭い等、独立の価値があるケースがある — 実例:
      Isaacs 9.13 の repo 版は `|G| ≤ |Z(S^∞)||Aut(S^∞)|` で書籍の階乗版より鋭い)。
- [x] 発見をレーンに配分 → **issue 0125** (lane a: Isaacs 全域)。

## 完了条件

3 冊の `⊲⊲` 使用箇所が列挙され、repo の対応宣言との照合が済み、
差分があれば issue 化 or 修正されている。

## 参照

- issue 1037 (Isaacs 9.10 / 9.13 / 9.21 — 実害の初出)
- memory `mmd-collapses-subnormal-symbol`
- mathlib `Mathlib/GroupTheory/IsSubnormal.lean`

## ⚠ 9000 レンジの採番衝突について (hub 案件)

本 issue は 9132 → 9133 → **9150** と 2 度改番している。原因は
**`issues/SEQUENCE.9000` がブランチごとに存在する**こと: 各レーンが自分の複製を
インクリメントするため、同じ番号を同時に払い出してしまう。

2026-07-18 時点で main に実在する衝突: **9125 / 9132 / 9133** (9133 は三重)。
本 issue は 9150 へ退避したが、**残る衝突は他レーン所有なので触っていない**。

hub への提案 (採番機構自体の是正が要る):
- `SEQUENCE.9000` を main 専用にして 9000 番の払い出しを hub 経由にする、または
- レーンごとに 9000 レンジ内のサブレンジを割る (例 a=9100-9199, b=9200-9299, c=9300-9399)、
  あるいは
- `bin/new-issue` が採番前に `git fetch origin main` して main 側の最大値も見る。
