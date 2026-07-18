---
id: 9132
slug: hall-collecting-process
title: "CLAIM: Hall's collecting process (一般 class ≤ p−1) — BG App.E 全体の unlock"
created: 2026-07-18
---

# CLAIM (shared infra): Hall's collecting process — 一般 class ≤ p−1

**claim 主体**: lane c。**予定 leaf**: `OddOrder/GroupTheory/HallCollection.lean` (新規)。

## claim-before-build の事前検索 (2026-07-18 実施)

- repo 内で `Hall.*[Pp]etrescu` / `collecting process` / `hallCollection` / `collection_formula` を grep:
  ヒットは **`GroupTheory/CriticalSubgroup.lean` (class≤2 特殊例)** と `BG/AppE_FurtherResults.lean`
  (本 issue が unlock する側)、`AxiomsCheck.lean` (登録) のみ。**一般形は不在**。
- mathlib (`Mathlib/GroupTheory/`) に `Petrescu`/`collecting` のヒット **なし**。
- open 9000 issue に重複 claim なし (9109/9111/9130/9131 は無関係)。

⟹ **未構築の genuine shared infra**。重複再構築の恐れなし。

## なぜ本丸か: App.E の依存グラフの単一の根

```
E.1 (Hall's collecting process, 一般 class ≤ p−1)  ← ★根。前提なし・自己完結
 └─ E.2 Step1 → E.2(a) → E.2(b) → E.3(b)(c) → E.3(d) → E.4 → E.5
```
`OddOrder/BG/AppE_FurtherResults.lean` の **9 sorry を一括で開く唯一の unlock**。
App.E が BG §4/§5/§14/§15/§16 から要する他の前提は**全て repo に在る** (issue 3021 で確認済)。

## 内容

BG App.E の E.1 (Hall collection 公式) の一般形。現在 `AppE_FurtherResults.lean` に
**honest statement + sorry** で置いてある `hallCollection`:
> `∃ c : ℕ → G`, `(∀ r, 2 ≤ r → r ≤ n → c r ∈ γ_{r−1}(G))` かつ
> `x^n * y^n = (x*y)^n * collectionTail c n`、ここで `collectionTail` は順序付き積
> `c₂^{e₂}⋯cₙ^{eₙ}` (`List.prod` over `List.range' 2 (n-1)`、`eᵣ = n.choose r`)。
> 書籍の `Gᵣ` = `lowerCentralSeries (r−1)`。

これを一般 class ≤ p−1 で証明する。純粋な交換子計算で**上流依存なし**。

## 出発点 (既存の特殊例 — 再証明せず再利用/一般化)

- `GroupTheory.mul_pow_eq_commutator_pow_mul_of_class_le_two` (`CriticalSubgroup.lean:657`) — class≤2。
- `AppE.hallCollection_of_class_le_two` (本 session で証明済、上記に接続) — E.1 の class≤2 版。
- `GroupTheory.Omega.pow_eq_one_of_class_le_two`、class≤3 collection 公式 (`S04_SmallRankBasic.lean`)。
- `Isaacs/Ch04_Commutators/CommutatorBasics.lean` の交換子基本補題群。

## 完了条件

`HallCollection.lean` で一般形を book strength・sorry-free・axiom-clean で証明 →
`AppE_FurtherResults.lean` の `hallCollection` を接続 → E.2 以降を順に解錠。
AxiomsCheck 登録、survey 更新、本 claim を close。

## 参照
- issue 3021 (App.E de-opacify 済 + 依存グラフ)、`OddOrder/BG/AppE_FurtherResults.lean`。
- ⚠ shared infra (`OddOrder/GroupTheory/**`) ゆえ他レーンは着手前に本 claim を確認のこと。
