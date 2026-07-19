---
id: 9400
slug: regular-pgroup-class-lt-p
title: "CLAIM: p-groups of class < p — BG Prop E.2 の induction (RegularPGroup.lean)"
created: 2026-07-20
---

# CLAIM (shared infra): `OddOrder/GroupTheory/RegularPGroup.lean`

**claim 主体**: lane c。**leaf**: `OddOrder/GroupTheory/RegularPGroup.lean` (新規、着手済)。
**consumer**: `OddOrder/BG/AppE_FurtherResults.lean` の E.2(a)(b) 以降 (issue 3021)。

## claim-before-build の事前検索 (2026-07-20)

- repo grep `regular p-group` / `RegularPGroup` / `class.*lt.*p` → 既存なし。
- mathlib に regular p-group / Ω₁ の exponent 定理はなし (`Mathlib/GroupTheory/PGroup.lean`
  に該当なし)。`OddOrder/GroupTheory/OmegaSubgroup.lean` は Ω/℧ の定義と可換な場合のみ。
- Coq math-comp/odd-order にも regular p-group はなし (BGsection4.v は weight 3 の
  切り詰めを証明ローカルに手書き)。
- open 9xxx issue に重複 claim なし。

⟹ 未構築の genuine shared infra。

## 済 (2026-07-20)

Hall の収集公式 (Thm E.1) が証明できた (issue 9132) ので、その群論的な帰結を取りに行く層。
現時点で 2 本、sorry 0 / axiom-clean:

- `lowerCentralSeries_eq_bot_of_subgroup` — **class の上界は部分群に遺伝する**
  (mathlib `Subgroup.lowerCentralSeries_map_subtype_le` + subtype 単射)。
  `|G|` についての帰納を回すのに要る。
- `Omega.pow_eq_one_of_mul_closed` — **`Ω₁` の指数を「p-捻れ元が積で閉じる」に還元**
  (閉じていれば p-捻れ元はそれ自体が部分群なので closure = それ自身)。

## 残: BG Prop E.2(a) の帰納

**目標**: `R` 有限 p 群、`γ_p(R) = 1` (mathlib: `lowerCentralSeries (p−1) = ⊥`) のとき
`x^p = y^p = 1 ⟹ (xy)^p = 1`。⟹ 上の 2 本で `Ω₁(R)` の指数が p。

**BG Step 2 の議論** (`Nat.card R` についての強帰納):

1. `H := ⟨x, y⟩`。`H < ⊤` なら IH を `↥H` に適用 (class は上の補題で遺伝、`|H| < |R|`) して終わり。
2. `H = ⊤` の場合:
   - `⟨y⟩ = ⊤` なら `R` は `y` 生成の巡回群で `y^p = 1` ⟹ 全元の p 乗が 1 ⟹ 済。
   - そうでなければ `⟨y⟩ ≤ M < ⊤` なる**極大部分群 `M`** を取る。`R` は冪零 (class ≤ p−1)
     ゆえ **極大部分群は正規** (mathlib `Mathlib/GroupTheory/Nilpotent.lean:1239` の TFAE に
     `∀ H, IsCoatom H → H.Normal` がある)。
   - IH を `↥M` に適用 ⟹ `Ω₁(M)` の指数は p。`y ∈ M`, `y^p = 1` ⟹ `y ∈ Ω₁(M)`。
   - `Ω₁(M)` は `M` に特性的 + `M ⊴ R` ⟹ **`Ω₁(M) ⊴ R`**。
   - `R = ⟨x, y⟩` かつ `y ∈ Ω₁(M)` ⟹ **`R/Ω₁(M)` は `x` の像で生成される巡回群** ⟹ アーベル
     ⟹ **`R' ≤ Ω₁(M)`** ⟹ `R'` の全元の p 乗が 1。
   - ⟹ **E.2 Step 1** (`AppE.pow_mul_of_commutator_pow_eq_one`、E.1 が証明されたので現在は
     実証明) が使えて `x^p·y^p = (xy)^p` ⟹ `(xy)^p = 1`。

**要る補助** (着手時に repo/mathlib を実測すること):
- 有限群で真部分群を含む極大部分群の存在 (`IsCoatom`; repo `MaximalSubgroup.lean` に
  `maximalSubgroupsContaining` あり)。
- 冪零 ⟹ 極大部分群は正規 (mathlib TFAE)。
- `Ω₁` が特性的 (`Omega` は `closure {g | g^(p^n) = 1}` なので自己同型で不変 — 要 lemma)。
- 巡回商 ⟹ `commutator ≤ kernel`。
- 部分群の型 `↥H` と `Nat.card` の帰納の取り回し。

## 完了条件

E.2(a) (`AppE.omega_pow_eq_one_of_lowerCentralSeries_eq_bot`) が sorry-free になり、
E.2(b) (`AppE.pow_mul_of_commutator_le_omega`) も解錠される。本 claim を close。

## 補助補題の実測 (2026-07-20) — ⚠ 配置の見直しが必要

| 要るもの | 実測結果 |
|---|---|
| 真部分群を含む極大部分群の存在 | `IsCoatomic.eq_top_or_exists_le_coatom` (`Mathlib/Order/Atoms.lean:335`)。有限なら `isCoatomic_of_orderTop_gt_wellFounded` (:510) で instance が立つ |
| 冪零 ⟹ 極大部分群は正規 | `Group.isNilpotent_of_finite_tfae` (`Mathlib/GroupTheory/Nilpotent.lean:1237`) の項目 3 = `∀ H, IsCoatom H → H.Normal`。直接には `NormalizerCondition.normal_of_coatom` + `normalizerCondition_of_isNilpotent` |
| `γ_{p-1} = ⊥ ⟹ IsNilpotent` | `Group.nilpotent_iff_lowerCentralSeries` (:500) |
| `Ω_n` が characteristic | **repo に既にある**: `OddOrder.GroupTheory.Omega.characteristic` instance (`OmegaSubgroup.lean:91`) |
| **characteristic in normal ⟹ ambient で normal** | ⚠ 下記 |
| 巡回商 ⟹ `commutator ≤ N` | mathlib に直接名なし。`⁅x,y⁆` の像が 1 になることから素朴に出る (数行) |

### ⚠ 配置の訂正: induction は `GroupTheory/` に置けない

「`N ⊴ W`、`L` char `↥N` ⟹ `(L.map N.subtype).Normal`」が要る (Ω₁(M) ⊴ R の段)。
これは **closed issue 9109** の対象で、**public 版は
`OddOrder.BG.Ch3.normal_map_subtype_of_characteristic`
(`BG/Ch3_MaximalSubgroups/S10_BetaRadicalGlobal.lean:409`) にしかない**。
`OddOrder/GroupTheory/` は Ch3 より上流なので import できず、ここに induction を書くと
**6 site 目の複製**になる (9109 は既に 5 site を数えており、同名 public 化は Huppert.lean の
無修飾参照と衝突して build を壊すことも実測済 = naive な consolidation 不可)。

⟹ **E.2(a) の帰納本体は `OddOrder/BG/AppE_FurtherResults.lean` に直接書く**
(E.2 Step 1 `pow_mul_of_commutator_pow_eq_one` が同ファイルにあるので、別 leaf に切ると
循環 import になる。同ファイルなら Ch3 経由で上記 public 補題が使える)。
現在 ~640 行なので +250 行程度は粒度規約 (≤1500) 内。

`GroupTheory/RegularPGroup.lean` には**汎用の還元 2 本だけを残す**
(`lowerCentralSeries_eq_bot_of_subgroup` / `Omega.pow_eq_one_of_mul_closed`) —
どちらも上記補題を必要とせず、上流に置く価値がある。

### 帰納の形 (型レベル)

部分群を型として扱う必要があるので、`Nat.card` に関する数値の帰納で群を量化する:

```lean
theorem aux (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∀ (R : Type u) [Group R] [Finite R], Nat.card R < n →
      (⊤ : Subgroup R).lowerCentralSeries (p - 1) = ⊥ →
      ∀ x y : R, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1
```
`H < ⊤` なら `Nat.card ↥H < Nat.card R` (要: 該当 mathlib 補題の実測。
`Subgroup.card_lt_card_of_lt` は見つからなかったので index 経由か
`Nat.card_eq_card_subgroup_mul_index` などから導く)。

## ⭐ 2026-07-20 (2): characteristic-in-normal 依存が消えた + 汎用部品が全部そろった

**設計上の改善**: `Ω₁(M)` を `M.subtype` で押し出す代わりに、**「M の p-捻れ元」を
ambient の部分群として直接定義**する (`torsionOf M p hclosed`) と、**正規性が自明**になる
(共役は「M に入る」も「p 乗が 1」も明らかに保つ)。
⟹ **`normal_map_subtype_of_characteristic` (closed issue 9109 の複製問題) が不要**。
前節の「配置の訂正」の理由のうち、この 1 件は解消した。

`RegularPGroup.lean` (128 行、sorry 0、axiom-clean) に帰納が要る部品が**全部そろった**:

- `lowerCentralSeries_eq_bot_of_subgroup` — class の上界は部分群に遺伝
  (非推奨 API を避け `Subgroup.top_subtype_lowerCentralSeries` + `lowerCentralSeries_mono` 経由)。
- `Omega.pow_eq_one_of_mul_closed` — Ω₁ の指数を「p-捻れ元が積で閉じる」に還元。
- ⭐ `torsionOf` / `torsionOf_normal` — 正規部分群の p-捻れ元は**正規部分群**。
- ⭐ `commutator_le_of_closure_pair` — `G = ⟨x,y⟩` かつ `y ∈ N ⊴ G` ⟹ `G/N` は x の像で
  生成される巡回群 ⟹ アーベル ⟹ **`G' ≤ N`**。
- `card_lt_card_of_lt_top` — 有限群の真部分群は位数が真に小さい。

### 残る配置の論点: E.2 Step 1 の置き場所

帰納は最後に **Step 1** (`class < p` かつ `G'` の指数が p ⟹ `x^p·y^p = (xy)^p`) を使う。
現在これは `AppE.pow_mul_of_commutator_pow_eq_one` として AppE にあり、`hallCollection`
経由で `exists_hallPetresco` に依存している。選択肢:

- (A) 帰納を AppE に書く — Step 1 がそのまま使える。ビルドが遅い (2 分超/回)。
- (B) **Step 1 を `RegularPGroup.lean` へ移す** (`exists_hallPetresco` から直接証明) —
  Step 1 は BG の番号付き結果ではなく Prop E.2 の内部ステップなので、AppE から移して
  AppE 側は E.2(a)(b) から GroupTheory 版を呼ぶ形にすれば**ラッパーも複製も生じない**。
  帰納全体が GroupTheory に収まりビルドが速い。**(B) を推奨**。
