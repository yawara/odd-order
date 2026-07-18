---
id: 3026
slug: bg-thm64-invariant-pi-conjugacy
title: "BG Thm 6.4: H-不変な π-部分群 J₁,J₂ の共役合成 — ⟨J₁^x,J₂⟩ が π-群かつ x が H を中心化"
created: 2026-07-19
---

# BG Thm 6.4: H-不変な π-部分群 J₁,J₂ の共役合成 — ⟨J₁^x,J₂⟩ が π-群かつ x が H を中心化

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 状態 (2026-07-19 実測)

**完全に未形式化**。survey L481 で refutation 済 (repo 内の "Thm 6.4"/"Theorem 6.4" hit は
すべて **Isaacs** Thm 6.4 = Frobenius 群の四同値で別物)。本 session でも
`H-invariant` / conjugation 系の grep で該当なしを再確認。

BG §6 の残り最後の 1 件 (6.1 ✅ / 6.2 は issue 3024 に blocked / 6.3 ✅ / 6.5,6.6,6.7 ✅)。

## 原文 (mmd L2011)

> **Theorem 6.4.** Suppose `G` is a group, `π` is a set of primes, `H` is a `π'`-subgroup of `G`,
> and `G₀` is a normal Hall subgroup of `G`. Assume that `G₀/F(G₀)` and `(G/G₀)/F(G/G₀)` are
> nilpotent. Assume further that `H` normalizes two `π`-subgroups `J₁` and `J₂` of `G`.
> Then there exists an element `x ∈ ⟨J₁, J₂⟩` such that `⟨J₁ˣ, J₂⟩` is a `π`-group and
> `x` centralizes `H`.

⚠ **BG は証明を本文に持っている** (mmd L2015 以降、`|G| + |H|` の帰納法)。Thm 6.2 のように
Gorenstein への引用で済ませてはいない ⟹ **本 issue は形式化労力であって research gap ではない**
([[verify-port-state-by-number-not-coq-name]])。

証明の骨格 (mmd L2015-):
- `|G| + |H|` に関する帰納法。`G ≠ 1` としてよい。`M := G₀` (`G₀ ≠ 1` のとき)、さもなくば `M := G`。
  `L := ⟨J₁, J₂⟩`。
- (6.1) `M` は `G` の非自明 normal Hall 部分群で `M/F(M)` は冪零。
- `H` は `J₁,J₂` を正規化するので `L` も正規化 ⟹ `G = LH` としてよい。`G/L` は `π'`-群で、
  (6.2) `L` は `G` の任意の `π`-部分群を含む。
- `π(F(G)) ⊄ π(H)` の場合: `p ∈ π(F(G)) ∖ π(H)` を取り、`O_p(F(G))` 内の極小正規部分群 `N` へ
  帰納法。以下続く (原文参照)。

## 見積・注意

- **M** (survey 評価)。帰納法の各分岐で Hall/Fitting/冪零商の道具を使う。
- 前提は repo に揃っているはず (Hall 部分群・`fittingInAmbient`・冪零性・π-群 API)。
  着手時に **実測で確認**すること (名前一致の罠に注意 — 本 session で 5 回踏みかけた)。
- Coq 対応は **無い**: math-comp は「revised proof に不要」として §6 の一部を落としている。
  repo にも consumer は無い。⚠ **これは deprioritize の理由にならない**
  (CLAUDE.md「進捗の測り方」— consumer 0 / gate 無しは着手判断の基準ではない)。

## 参照

- BG mmd `references/bg/local-analysis.mmd` L2011 (statement) 以降 (proof)。
- survey `notes/meta/three_books_full_survey_2026_07_16.md` L481 (refutation 記録)。
- `notes/bg/s06_additional.md` (§6 全体の状況)。

---

## 進捗 (2026-07-19): 上流 2 件を landed + **book の誤りを発見・修正**

Thm 6.4 本体は**未完**。ただし Case 1 の hard step 2 件を standalone で landed し、
形式化を止めていた原因 (book の誤り) を解消した。新 leaf
`OddOrder/BG/Ch1_Preliminary/S06_Thm64.lean` (216 行)。

### ⚠ BG p.50 (mmd L2031) に誤り — `H ∩ L = 1` は従わない

原文は Case 1 の末尾で
> `[H, yz] ⊆ H ∩ L = 1.`
と書くが、**`H ∩ L = 1` は仮説から従わない**。直前の reduction が与えるのは `G = LH` と
`L ⊴ G`、したがって `G/L ≅ H/(H ∩ L)` だけで、`H ∩ L` の自明性は何も言っていない。
しかも `L = ⟨J₁, J₂⟩` が `π`-群であることは**本定理の結論そのもの**なので未知であり、
`π'`-群 `H` と交わりうる。

**正しい部分群は `N`**: `[H, yz] ⊆ H ∩ N = 1`。根拠:
- `(H^y)^z = H` より `yz ∈ N_G(H)` ゆえ `[H, yz] ⊆ H`;
- (6.3) で `y` は `HN/N` を中心化するので `h⁻¹ h^y ∈ N`、`z ∈ N` と `N ⊴ G` から
  `h⁻¹ h^{yz} ∈ N`;
- `N ≤ O_p(F(G))` は `p`-群で `p ∉ π(H)` ゆえ `H ∩ N = 1` — これは **BG 自身が 1 行前に
  「`H` is a Hall `p'`-subgroup of `HN`」と書いている内容そのもの**。

⟹ `L` は `N` の書き損じ。結論は健全で定理は危うくない。mmd だけでなく **PDF の紙面
(p.50 = PDF p.63) でも確認済**。Lean 側は module docstring に記録し、
`mem_centralizer_of_mem_normalizer_of_commutator_le` として正しい形で形式化した。

### landed (いずれも sorry-free・axiom-clean、AxiomsCheck 登録済)

- **`exists_centralizing_conj_sup_isPiGroup`** — **coprime `A` に対する Thm 6.4**
  (= BG Prop 1.5(b)+(c) の joint subgroup 形)。Thm 6.4 はこれを「coprime 位数」から
  「Hall/Fitting 仮説」へ一般化したものなので、Case 1 が最後に呼ぶエンジンそのもの。
- **`mem_centralizer_of_mem_normalizer_of_commutator_le`** — 上記の修正済 Case-1 中心化ステップ。
- 付随の transport 補題 4 件 (`conj_smul_eq_map` / `isPiSubgroup_of_le` /
  `isPiGroup_subgroupOf` / `isPiSubgroup_map_subtype`)。

### 残り見積 — 約 1,350-2,150 行 / 2 leaf (2026-07-19 **下方修正**)

| 残作業 | 行 |
|---|---|
| `\|G\| + \|H\|` の帰納骨格 (ℕ 上の強帰納; 商・部分群は同 universe に留まる) | 150-250 |
| ~~部分群 `L ⊔ H` への仮説 transport~~ ✅ **完了** (normal-Hall 側 55 行 + Fitting 側 cite) | ~~150-250~~ |
| ~~`G ⧸ N` への仮説 transport~~ ✅ **完了** (同上) | ~~150-250~~ |
| **`quotientMapSubgroupOfOfLe` の単射性** (下記 ⚠、mathlib に無い) | 50-100 |
| Case 1 assembly (極小正規 `N ≤ O_p(F(G))`、`N ≤ L`、SZ 共役、landed 済 2 定理) | 300-450 |
| Case 2 (`B = H ⊓ M`、補群 `H*`、`[J₁,B] ≤ F(M)`、`O_π(F) ≤ O_π(G) = 1`、`B` が `L` を中心化) | 500-800 |
| ~~2 つの Fitting 商仮説から `IsSolvable G` を導く~~ ✅ **完了** (25 行) | ~~100-150~~ |

**新しい数学は不要** — 入力はすべて repo に在る。

✅ **transport の Fitting 部分は完了 (issue 9157、2026-07-19)**。当初この 2 行を 500-700 行ずつと
見積もっていたが、実際は汎用補題 `OddOrder/GroupTheory/FittingHeredity.lean` (155 行、6 定理、
axiom-clean) で片付き、消費側は cite するだけになった。⟹ 上表を下方修正。
使う形は **`isNilpotent_quotient_fitting_of_le`** (`H ≤ K` 共通 ambient) と
**`isNilpotent_quotient_fitting_quotient`** (`N ⊴ X`)、および同型を挟む場合は
`isNilpotent_quotient_fitting_of_injective/of_surjective` に `e.toMonoidHom` を渡す。

⚠ 起票時に「部分群遺伝は一般には自明でなく追加仮説が要るかも」と書いたが**それは誤り**だった。
`F(X) ⊓ Y ≤ F(Y)` は常に成立する (`F(X) ⊴ X` ゆえ `Y` で normal、`F(X)` の部分群ゆえ冪零、
あとは Fitting 極大性)。一般に成り立たないのは逆包含 `F(Y) ≤ F(X)` だが、そちらは不要。

### 付随して見つかった stale / 重複 (本 lane では直さない)

- **`OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean:739`** (lane a territory) — §3E の節見出しが
  「**形式化状態**: 全 stub. 完全実装は ~8-12 週の大規模作業」と書くが**誤り**。Thm 3.23 /
  3.24 (Glauberman) / 3.28 は実装済で、今回消費した BG Prop 1.5(a)(b)(c) はその上に建っている。
- **private helper の三重化**: `subtype_comp_conj_eq` / `map_subtype_conj_subgroupOf` が
  `OddOrder/Mathlib/SchurZassenhausConj.lean:267,275` と
  `BG/Ch3_MaximalSubgroups/S13_PrimeAction.lean:579,584` に `private` で重複し、今回 3 つ目を
  作らざるを得なかった。ファイル跨ぎ `private` は CLAUDE.md 規約違反ゆえ
  `OddOrder/Mathlib/Subgroup.lean` へ de-privatize したい (shared infra)。

---

## 進捗 (2026-07-19 第2波): transport + solvability 完了、残り ~1,000-1,600 行

### landed (すべて sorry-free・axiom-clean、AxiomsCheck 登録済)

- **`OddOrder/GroupTheory/NormalHallHeredity.lean`** (新規 112 行) — normal Hall の遺伝:
  `coprime_card_index_comap_of_injective` / `_map_of_surjective` (hom レベル一般形) と
  `normal_coprime_card_index_subgroupOf` / `_map_mk'` (消費側の形、`Normal ∧ Coprime` を同時に返す)。
  ⚠ **有限性を一切要求しない** — `Nat.card`/`index` は無限の場合 `0` を返し、使う整除性は
  無条件に成り立つ。normality を使うのは部分群方向のみなので全射版は `[K.Normal]` を持たない。
- **`S06_Thm64.isSolvable_of_isNilpotent_quotient_fitting`** (+ `_of_normal` 版) —
  `X/F(X)` 冪零 ⟹ `IsSolvable X`、および Thm 6.4 の形での組み立て。Prop 1.5 が要求する。

### ⚠ 新たに判明した残作業: `quotientMapSubgroupOfOfLe` の単射性

`FittingHeredity` の 3 corollary を cite すれば transport が済む、というのは**不正確**だった。
帰納法が行う 4 つの transport のうち `_of_le` で直接当たるのは `G₀ ⊓ S ≤ G₀` の 1 つだけで、
残り 3 つは同型を挟むため `_of_injective`/`_of_surjective` + **消費側が hom を用意する**必要がある。

特に部分群側の仮説「`(↥S ⧸ G₀.subgroupOf S)/F(…)` 冪零」には**単射** hom
`↥S ⧸ G₀.subgroupOf S →* G ⧸ G₀` が要る。mathlib に写像は在る
(`QuotientGroup.quotientMapSubgroupOfOfLe`、`QuotientGroup/Basic.lean:179`) が
**単射性の補題が無い** ⟹ kernel 計算を自分で書く必要がある (50-100 行)。
`FittingHeredity.lean` の module docstring にもこの注意を追記済。

### 併せて見つかった重複 (lane a territory、本 lane では直さない)

`OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean:242-256` が
`normal_coprime_card_index_subgroupOf` と**同じ内容を ~15 行インラインで再導出**している
(`relIndex` の手計算 + `inf_subgroupOf_left`/`subgroupOfEquivOfLe`)。de-dup 候補。
新設した汎用補題に価値があったことの傍証でもある。
