---
id: 111
slug: s15-sandt-resplit
title: "S15_SAndT 1637 行 → 再分割 (b の (13.19) cascade 完了後)"
created: 2026-07-12
---

# S15_SAndT 1637 行 → 再分割 (b の (13.19) cascade 完了後)

## 背景

2026-07-12 監視 tick で `OddOrder/Peterfalvi/S15_SAndT.lean` が **1637 行** に到達
(merge afc368a0 = 2038 (13.19.c) dichotomy 組立)。CLAUDE.md 粒度規約の **1500 行 watch 閾値**超過
(2000 行 hard 上限は未達ゆえ緊急でない)。過去に 0075/0102 で分割済 (→ S15_SAndTBasic 1176 /
S15_SAndTDefs 1084 に切出し) だが本体が再成長。

⚠ **本 file は lane b の active frontier**: b は 2038 (13.19.c) の c1 bound / assembly を継続中で
S15_SAndT をさらに触る。**active file の分割は b の作業と衝突する**ため、分割は **b の (13.19)
cascade が settle した後**に hub が凍結境界で実施 (mathlib 準拠 = topic leaf への追加切出し or
prefix-split、module 名不変で下流 import 無変更)。

## 更新 (2026-07-12 tick, merge a2fe7a0b)

**S15_SAndT が 1869 行に成長 (1637→1869)、2000 hard 上限に接近**。同 tick で b が
`typeI_caseC_bound_c1` を証明し **(13.19.c) 完結・S15_SAndT 実 sorry 0** に到達。⟹ b の当該 file
frontier が settle に近づいた可能性。**次の hub 判断**: (i) 2000 超で split 必須化、または
(ii) b の 2038 が S15_SAndT 非接触フェーズ (assembly/別 file) に移ったら split 着手。b が引き続き
S15_SAndT を触るなら deferred 継続。hub は毎 tick の size watch で 2000 接近を監視。

## ✅ 完了 (2026-07-12 監視 tick, hub 実施)

b が (13.19.c) 完結で S15_SAndT を実 sorry 0 で凍結・idle 化 → hub が prefix-split 実施:
- **新 leaf `S15_SAndTGrid.lean` (792 行)** = (13.19) type-I orthogonality **producer / grid-facts 層**
  (`OddIntegerInner` / `TypeIOrthogonalityData` bundle / `typeIBetaL` 分解 / disjoint-support /
  row·col constancy、21 decl)。namespace `OddOrder.Peterfalvi.S15` 維持。
- **`S15_SAndT.lean` (1105 行)** = (13.19.c) dichotomy (parity core + 2 case bounds + assembly) +
  (14.5) complement exclusion (17 decl)。冒頭で `S15_SAndTGrid` を import。
- decl 総数 38 保存 (21+17)、namespace 名不変 ⟹ **下流 import 無変更**、build green (4178 jobs)・
  AxiomsCheck OK・sorry 63→63 (中立)・新 axiom なし。root closure = S15_SAndT の import 経由 (transitive、
  prior-split 兄弟と同慣例ゆえ OddOrder.lean 追記不要)。

- [x] b の (13.19.c) landing で S15_SAndT 凍結 → 着手
- [x] 分割方式 = 新 topic leaf S15_SAndTGrid への prefix-split
- [x] hub が凍結境界 (line 794 = (13.19) producer 層 / (13.19.c) dichotomy の topic 境界) で実施

## 完了条件 (達成)

- [x] S15_SAndT.lean (1105) + S15_SAndTGrid.lean (792) が各 2000 行未満・1500 未満
- [x] `lake build OddOrder` green・下流 import 無変更

## 参照

- CLAUDE.md「ファイル粒度」(2026-07-09 節: 1500 watch / 2000 hard / dir 化第一)
- 過去分割 = issues/closed/0075, 0102, 0094 (S15 setup)
- issue 2038 (b の (13.19) frontier)、merge afc368a0 (1637 行到達)
