---
id: 9133
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

## やること

- [ ] Isaacs 全体を `«` で走査し、`⊲⊲` を含む定理番号を列挙する。
- [ ] 各番号について repo の対応宣言の binder が `IsSubnormal` か `Normal` かを照合。
- [ ] BG / Peterfalvi でも同様の走査 (両書とも subnormal を使う箇所は少ないはずだが要確認)。
- [ ] 取り違えが見つかったら、**normal 版は消さず**に subnormal 版を追加する
      (normal 版の方が bound が鋭い等、独立の価値があるケースがある — 実例:
      Isaacs 9.13 の repo 版は `|G| ≤ |Z(S^∞)||Aut(S^∞)|` で書籍の階乗版より鋭い)。
- [ ] 発見をレーンに配分 (該当章の owner レーンへ)。

## 完了条件

3 冊の `⊲⊲` 使用箇所が列挙され、repo の対応宣言との照合が済み、
差分があれば issue 化 or 修正されている。

## 参照

- issue 1037 (Isaacs 9.10 / 9.13 / 9.21 — 実害の初出)
- memory `mmd-collapses-subnormal-symbol`
- mathlib `Mathlib/GroupTheory/IsSubnormal.lean`
