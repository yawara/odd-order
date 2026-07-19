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

## 進捗 (2026-07-18): 枠組み + class ≤ 3 まで landing、一般形は障害を特定して継続中

**新 leaf `OddOrder/GroupTheory/HallCollection.lean` (249 行、sorry 0、全 axiom-clean)**:
- `hallTail` — 順序付き尾部 `c₂^{C(n,2)}⋯cₙ^{C(n,n)}` (旧 `AppE.collectionTail` と**定義が字面まで同一**)。
  崩壊/吸収補題: `hallTail_block_eq_one` / `_eq_of_eq_one_of_three_le` / `_eq_of_eq_one_of_four_le` /
  `hallTail_eq_prefix_mul_top` (最上位スロットの指数は `C(n,n)=1`)。
- **`pow_succ_collect`** — 収集の 1 ステップ漸化式 (エンジン):
  `x^n y^n = (xy)^n T ⟹ x^(n+1) y^(n+1) = (xy)^(n+1) * (⁅x⁻¹,((xy)^n)⁻¹⁆ * T)^y`。**公理は propext のみ**。
- 深さ管理: `conj_mem_lowerCentralSeries` / `pow_succ_collect_mem` /
  `commutatorElement_mem_lowerCentralSeries_add` (`[γᵢ,γⱼ] ≤ γ_{i+j}`)。
- **`exists_hallCollection_of_residue`** — 固定 `n` の E.1 は `γ_n` を法とする合同そのもの
  (最上位スロットが残差を吸収)。⟹ **隠れた exactness を仮定していないことの保証**。

**`AppE.hallCollection_of_class_le_three`** — `γ₃ = 1` なら **全 `n` について E.1** が成立。
既存 class≤2 を真に包含。`c₂ = ⁅y,x⁆⁻¹(d₁d₂²)⁻¹`, `c₃ = (d₁d₂²)⁻¹`, `cᵣ=1 (r≥4)` と明示。
repo の `BG.Ch1.S04.mul_pow_eq_collect_of_triple_central` を走らせ、その weight-3 指数
`C(n+1,3)`, `2C(n+1,3)` を **Pascal 分割 `C(n+1,3) = C(n,2)+C(n,3)`** で Hall の形に変換
(= weight 3 で二項係数が正しく出る理由)。

⚠ **`hallCollection` (一般形) の statement は完全に不変** (diff で逐語一致を確認済) — 弱化なし。
repo 全体 sorry 22 → 22 (偽の削減なし)。AxiomsCheck に 3 件登録。

### 残る唯一の障害 (docstring にも記載)

枠組みにより E.1 は weight 帰納に帰着した。開いているのは:
> weight `2..k−1` を収集した残差 `w(n) ∈ γ_k` が、`γ_k/γ_{k+1}` の中で **`C(n,k)` 乗**であることを示す段。

これに必要なのは **(i) 自由冪零群と各 `γ_k/γ_{k+1}` の basic-commutator 基底**、
**(ii) 収集係数の `n` に関する多項式性 (Hall 多項式 / Lazard)**。
mathlib には `FreeGroup` はあるが**自由冪零商も basic commutator も無く**、`Petrescu`/`collecting` も皆無。
class ≤ 3 が回避できるのは、残差が中心 `γ₃` に落ち生成元が 2 つと明示できるため。

⟹ 次段は (i)(ii) の形式化。いずれも独立した shared infra で、これ自体が相当量。

## 完了条件

`HallCollection.lean` で一般形を book strength・sorry-free・axiom-clean で証明 →
`AppE_FurtherResults.lean` の `hallCollection` を接続 → E.2 以降を順に解錠。
AxiomsCheck 登録、survey 更新、本 claim を close。
(現状: 枠組み + class≤3 済。一般形は上記 (i)(ii) 待ち。)

## 参照
- issue 3021 (App.E de-opacify 済 + 依存グラフ)、`OddOrder/BG/AppE_FurtherResults.lean`。
- ⚠ shared infra (`OddOrder/GroupTheory/**`) ゆえ他レーンは着手前に本 claim を確認のこと。

## 出典調査 (2026-07-19、App.D 完了後に実測)

**BG は E.1 を証明していない** — 本文は引用のみ (PDF p.157):
> "The following result was proved by Philip Hall ... using his commutator collecting process.
> It may be found on pp. 37-41 of [26] and in many other books (e.g., [17, pp. 315-318])."

- `[26]` = **Suzuki, _Group Theory II_** (Grundlehren 248, 1986) — `references/` に無い。
- `[17]` = **Huppert, _Endliche Gruppen I_** (Grundlehren 134, 1967) — `references/` に無い。
- **Gorenstein には無い** (唯一の追加参照可能書): Ch.5 は §1 Frattini / §2-§3 p'-自己同型 /
  §4 p-groups of small depth / §5 extra-special / §6 associated Lie ring。
  regular p-group も collection formula も節が無く、`grep "collection\|regular p-group"` も空振り。
- **mathlib に無し** (`grep -rl "Petrescu\|collecting\|collection formula" Mathlib/GroupTheory/` = 空)。
- **Coq math-comp/odd-order にも無し** (`coq/theories/` に `BGappendixD/E` 自体が存在しない —
  App.D/E は FT 経路外ゆえ Coq 形式化の対象外)。

⟹ **参照可能な証明本体がどこにも無い**。自前で古典証明を再構成する (impasse なら
[[feedback-ask-chatgpt-for-elided-gaps]] の手順)。CLAUDE.md の「文献引用のみで本文に証明が
無い結果は恒久対象外にせず低優先繰延」に該当するが、**BG の残 sorry は App.E の 9 件のみ**
なので lane c の frontier としては live。

## 障害の正確な形 (2026-07-19 に独立検証)

repo の `exists_hallCollection_of_residue` により、E.1 は「weight `k` ごとに `γ_{k+1}` を法として
合わせる」帰納に帰着している (最上位スロットの指数 `C(n,n)=1` が残差を吸収するため)。
その帰納段で必要なのは:

> 残差 `R ∈ γ_k` の `γ_k/γ_{k+1}` (アーベル) における類が、**ある固定元 `c` の `C(n,k)` 乗**であること。

アーベル群の元が一般に `C(n,k)` 乗であるとは限らないので、これは自動でない。成立する理由は
`F = F(x,y)` の中で `γ_k(F)/γ_{k+1}(F)` が **weight `k` の basic commutator を基底とする自由
アーベル群**であり、収集係数が `n` の整数値多項式で、weight `k` 成分がちょうど `C(n,k)` の定数倍に
なること (Hall 多項式)。⟹ issue 記載の (i)(ii) が本当に要る、という当初評価を**再確認**した。

なお `⁅a, bⁿ⁆ ≡ ∏_i ⁅a,b;i⁆^{C(n,i)}` (左正規化交換子の 1 変数収集) は `n` の帰納で
独立に証明でき、weight 2 の係数が `C(n,1)=n` → Pascal で `C(n+1,2)` を出す仕組みそのもの。
**次段の最初の一歩はこれ** (自由群不要・自己完結)。
