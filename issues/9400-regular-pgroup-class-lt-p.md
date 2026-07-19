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
