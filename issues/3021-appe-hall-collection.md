---
id: 3021
slug: appe-hall-collection
title: "BG App.E 全体の唯一の unlock = Hall's collecting process (一般 class ≤ p−1)"
created: 2026-07-18
---

# BG App.E: 全体の唯一の unlock = Hall's collecting process

## 済: opaque scaffold の de-opacify (2026-07-18)

`AppE_FurtherResults.lean` は 163 行の **opaque-Prop scaffold** (全仮説・結論が自由 `Prop` +
自己保持 `_holds` ⟹ `∃ data, …` が自明に充足) で、E.1-E.5 に 1:1 対応する 5 sorry があったが
**book strength の内容はゼロ**だった。482 行に書き直し、**opaque フィールド 0 / `_holds` 0**
(コメント除去後) を確認済。実 sorry 9 は全て **honest な book-strength statement の下**にある
(「opaque で sorry-free」より「honest + sorry」を優先 = CLAUDE.md 方針)。

**sorry-free で証明済 (全 axiom-clean)**: `collectionTail_zero` / `collectionTail_one` /
`collectionTail_eq_of_eq_one_of_three_le` / **`hallCollection_of_class_le_two`** (E.1 の class≤2、
既存 `GroupTheory.mul_pow_eq_commutator_pow_mul_of_class_le_two` に接続) /
**`pow_mul_of_class_le_two`** (E.2(b) の class≤2) / `RegularOperatorSetup.isAInvariant_R₀` /
**`RegularOperatorSetup.card_A_dvd_half_p_sub_one`** (= **E.3(a) 完成**、`q ∣ (p−1)/2`)。

honest statement + sorry: `hallCollection` (E.1 一般) / `pow_mul_of_commutator_pow_eq_one`
(E.2 Step1) / `omega_pow_eq_one_of_lowerCentralSeries_eq_bot` (E.2(a)) /
`pow_mul_of_commutator_le_omega` (E.2(b)) / E.3(b)(c)(d) 3 件 / E.4 / E.5。
E.3 の `RegularOperatorSetup` は 18 の実型付きフィールド (opaque でない)。
E.5 は §14-§16 の実語彙 (`IsMinimalSimpleOdd`/`maximalSubgroups`/`S10.Msigma`/`S14.maximalTypeFFamily`
等) で記述、仮説ブロックは既形式化の BG Cor 15.9 (`S16.centralizer_escape_final_local`) と同一。

## 残: 依存グラフは 1 つの根に収束

```
E.1 (Hall's collecting process, 一般 class ≤ p−1)  ← ★根。前提なし・自己完結
 └─ E.2 Step1 (記述済、E.1 待ち)
     └─ E.2(a) + |R| 帰納
         └─ E.2(b) (記述済)
         └─ E.3(b)(c) + BG §5 narrow-p-group 機構 (repo にあり)
             └─ E.3(d) + Schur-Zassenhaus 共役 (repo にあり)
             └─ E.4 + S/S' 固有値論法
                 └─ E.5 + §14 counting (Lem 14.5/Thm 14.7、repo にあり) + Cor 15.9 (repo にあり)
```

**App.E が BG §4/§5/§14/§15/§16 から必要とするものは全て repo に在る**。⟹ **一般 class ≤ p−1 の
Hall collecting process を形式化することが付録 E 全体の唯一の unlock**。純粋な交換子計算で
上流依存が無く、`OddOrder/GroupTheory/HallCollection.lean` 等の独立 leaf に書ける。
既存の class≤2/≤3 特殊例 (`S04_SmallRankBasic.lean`, `CriticalSubgroup.lean`,
`Isaacs/Ch04_Commutators/CommutatorBasics.lean`) が出発点。

⚠ shared infra (`OddOrder/GroupTheory/**`) ゆえ着手前に **9000 claim** + 既存検索。

## 完了条件

Hall collecting process (一般 class ≤ p−1) を形式化 → E.1 一般形 → E.2 → E.3(b)(c)(d) → E.4 → E.5
を順に sorry-free・axiom-clean 化。AppE の sorry が 0 に。survey App.E 行更新。
(E.3/E.4 は Feit-Thompson 1991 の regular-operator bound が別途要る可能性 — 着手時に再評価。)

## 参照
- `OddOrder/BG/AppE_FurtherResults.lean` (de-opacify 済、482 行)、mmd の App.E 節。
- 既存特殊例: `GroupTheory.mul_pow_eq_commutator_pow_mul_of_class_le_two` (CriticalSubgroup.lean:657)、
  `GroupTheory.Omega.pow_eq_one_of_class_le_two`。
- 関連: issue 3020 (App.D の Gorenstein §14.1 ブロッカー)。
