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

---

## 進捗 (2026-07-19 第3波): 単射性 + 帰納骨格 + (6.2) — 残り Case 1/Case 2 のみ

### landed (すべて sorry-free・axiom-clean `[propext, Classical.choice, Quot.sound]`)

**1. `OddOrder/Mathlib/QuotientGroup.lean` (新規 117 行) — 前波の ⚠ 残作業を解消**

mathlib の `QuotientGroup.quotientMapSubgroupOfOfLe` に核・単射性の補題が無い件を埋めた。

- `QuotientGroup.ker_quotientMapSubgroupOfOfLe` (:54) — 核 =
  `(B'.subgroupOf A).map (mk' (A'.subgroupOf A))`。`QuotientGroup.ker_map` + comap の同定。
- `QuotientGroup.quotientMapSubgroupOfOfLe_injective_iff` (:77) — **単射 ⟺ `A ⊓ B' ≤ A'`**。
  `h' : A' ≤ B'` 込みで読むと「`A` の中では `A'` が既に `B'` の全 trace」の意 (`A ⊓ A' = A ⊓ B'`)。
  `A' = B'` なら常に成立。
- `QuotientGroup.quotientMapSubgroupOfOfLe_injective` (:96) — mpr 方向の便利形。
- `QuotientGroup.map_subgroupOf_subtype_injective` (:109) — 消費側の具体形:
  `↥S ⧸ N.subgroupOf S →* G ⧸ N` (= `QuotientGroup.map (N.subgroupOf S) N S.subtype le_rfl`)
  は単射。**第二同型定理を埋め込みとして読んだもの** (`S/(S ⊓ N) ↪ G/N`)。
  mathlib の `quotientInfEquivProdNormalQuotient` は `SN/N` への同型止まりで埋め込みは無い。

⚠ **一般形は具体形を包含しない**: `quotientMapSubgroupOfOfLe` の値域は部分群型の商
`↥B ⧸ …` なので `B := ⊤` としても `↥(⊤ : Subgroup G) ≃* G` の transport が残る。
よって具体形は `QuotientGroup.map` から直接証明した (核が**定義的に** `N.subgroupOf S`)。
4 定理とも `@[to_additive]` 付きで加法版も生成済 (`QuotientAddGroup.*`)。

**2. `OddOrder/GroupTheory/FittingHeredity.lean:179` — 消費側 corollary**

- `isNilpotent_quotient_fitting_quotient_subgroupOf` — `N ⊴ X` で `(X/N)/F(X/N)` 冪零なら
  任意の `S ≤ X` について `(S/(S ⊓ N))/F(…)` も冪零。上の埋め込み + `_of_injective`。
  module docstring の ⚠ ブロック (「単射性は genuine remaining step」) を解消済に更新。

**3. `OddOrder/BG/Ch1_Preliminary/S06_Thm64.lean` — 帰納骨格 (Piece 2) と (6.2)**

測度と降下:
- `card_lt_card_of_lt` (:349) — `K < H` ⟹ `|K| < |H|` (mathlib に無い)。
- `card_quotient_add_card_map_mk'_lt` (:362) — 場合 1 の降下 `(G ⧸ N, HN/N)`。
- `card_subgroup_add_card_subgroupOf_lt` (:375) — reduction の降下 `(↥S, H ⊓ S)`。

強帰納法と statement:
- `card_add_card_strongInduction` (:403) — **測度 `Nat.card G + Nat.card H` に関する強帰納原理**。
  `motive : ∀ (X : Type u) [Group X] [Finite X], Subgroup X → Prop` と**群の型を量化**する形。
  `↥S`・`G ⧸ N`・`G` の 3 種の降下が型は違えど**同じ universe に留まる**ので成立する
  (elaborate 確認済 — universe polymorphism の懸念は実在しなかった)。
- `Thm64Statement` (:431) — 定理の主張。Hall 性は π 非依存の `Nat.Coprime |G₀| [G:G₀]`
  (`NormalHallHeredity` と同 convention)、共役は左作用 `MulAut.conj x • J₁`
  (BG の `J₁ˣ` とは `x ↦ x⁻¹` 違いだが `⟨J₁,J₂⟩` も `C_G(H)` も逆元で閉じるので同値)。
- `Thm64IH` (:450) — 帰納法の仮定。`Ch09.BartelsIH` と同じく**明示パラメータ**設計なので
  場合 1 / 場合 2 をそれぞれ**単独で sorry-free な定理**として書ける。
- `thm64_of_ih` (:463) — 骨格を閉じる。**残る数学は全部 `step` の側**。

BG の名前付きステップ 2 件:
- `inf_eq_bot_of_isPiSubgroup_compl` (:176) — `π'`-部分群 ⊓ `π`-部分群 = `⊥`。
  場合 1 の「`H` is a Hall `p'`-subgroup of `HN`」⟹ `H ∩ N = 1`。
  第1波の `mem_centralizer_of_mem_normalizer_of_commutator_le` の `hdisj` を供給する。
- `le_of_isPiSubgroup_of_quotient_isPiGroup` (:189) — **(6.2)**「`L` contains every
  `π`-subgroup of `G`」。`G/L` が `π'`-群であることから。
- 支持補題 `isPiSubgroup_map` (:142) / `isPiSubgroup_of_isPiGroup` (:150) /
  `eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl` (:161)。

### 残り (Case 1 / Case 2 の中身のみ)

| 残作業 | 行 |
|---|---|
| ~~`quotientMapSubgroupOfOfLe` の単射性~~ ✅ **完了** | ~~50-100~~ |
| ~~`\|G\| + \|H\|` の帰納骨格~~ ✅ **完了** (measure 3 + 強帰納 + statement + IH) | ~~150-250~~ |
| ~~(6.2)~~ ✅ **完了** | — |
| **reduction 「`G = LH` としてよい」の実施** (6 仮説を `↥(L ⊔ H)` へ transport し結論を押し戻す) | 200-350 |
| **Case 1** (極小正規 `N ≤ O_p(F(G))` の取得、`N ≤ L`、SZ 共役 `z`、landed 済 2 定理の合成) | 300-450 |
| **Case 2** (`B = H ⊓ M`、補群 `H*`、`[J₁,B] ≤ F(M)`、`O_π(F) ≤ O_π(G) = 1`、`B` が `L` を中心化) | 500-800 |

reduction の transport に要る道具は**全部揃った**: normal Hall = `NormalHallHeredity`
(`normal_coprime_card_index_subgroupOf` / `_map_mk'`)、Fitting 商 = `FittingHeredity`
(`isNilpotent_quotient_fitting_of_le` / `_quotient` / `_quotient_subgroupOf`)、
測度減少 = 上記 3 件。**新しい数学はやはり不要**。

### 併せて見つかった重複 (本 lane では直さない)

- **`Nat.card ↥K < Nat.card G` (真部分群) が 3 箇所に重複**:
  `Isaacs/Ch04_Commutators/Main/BaerTrick.lean:1021` (`Ch04.subgroup_card_lt_of_ne_top`)、
  `Isaacs/Ch09_MoreSubnormality/SubnormalClosure.lean:241` (`Ch09.card_lt_of_ne_top`)、
  さらに `BaerTrick.lean:557` に同内容の local `have` が 3 つ目。
- **`Nat.card (G ⧸ K) < Nat.card G` が 2 箇所**:
  `Mathlib/Subgroup.lean:515` (`Subgroup.card_quotient_lt_of_ne_bot`) と
  `SubnormalClosure.lean:440` (`Ch09.card_quotient_lt_of_ne_bot`)。
  前者が mathlib 候補配置なので後者を消して前者に寄せるのが筋。

## ✅ hub による誤植の独立検証 (2026-07-19)

c の「BG p. 50 の `H ∩ L = 1` は誤植で正しくは `H ∩ N = 1`」という指摘を、
**PDF ページ画像 (book p.50 = PDF p.63) で独立に検証し、正しいと確認した。**

原文の該当箇所 (Theorem 6.4 の証明、場合 1):

> In this case, `H` is a Hall `p'`-subgroup of `HN`. Take `z ∈ N` such that `(H^y)^z = H`.
> Let `L* = ⟨J₁^{yz}, J₂⟩N`. Then `yz ∈ L` and
> `[H, yz] ⊆ H ∩ L = 1.`

**`[H, yz] ⊆ H ∩ L` までは正しい** (`yz ∈ L` かつ `H` が `L` を正規化し `G = LH` ゆえ `L ⊴ G`、
よって `[H,yz] ⊆ L`; `yz ∈ N_G(H)` ゆえ `[H,yz] ⊆ H`)。
**しかし `H ∩ L = 1` はこの時点で正当化されていない**: `L = ⟨J₁,J₂⟩` は `π`-部分群 2 つで
生成されるが `L` 自身が `π`-群とは限らず (それこそが本定理の結論)、`G/L ≅ H/(H∩L)` は
`H ∩ L` の自明性を与えない。

c の訂正 `H ∩ N = 1` は正当: `N ≤ O_p(F(G))` は `p`-群、`H` は `HN` の Hall `p'`-部分群
(原文が直前に明記) ゆえ交わりは自明。`[H,yz] ⊆ N` も成立する ((6.3) で `y` が `HN/N` を
中心化 ⟹ `h⁻¹h^y ∈ N`、`z ∈ N` と `N ⊴ G` ⟹ `h⁻¹h^{yz} ∈ N`)。
⟹ **結論 (`yz` が `H` を中心化) は不変で、`L` を `N` に読み替えれば証明は通る。**

⚠ **これは本プロジェクトが確認した初の「本物の教科書の誤り」**である。
これまで repo に混入していた 3 件の「書籍に gap がある」という注記 (issue 0125) は
いずれも `.mmd` の `⊲⊲`→`⊲` 潰れによる**私たちの誤読**だった。今回は
mmd・pdftotext・**ページ画像の 3 つとも同一の印字**であることを確認しており、
性質が異なる。

---

## 進捗 (2026-07-19 第4波): `G = LH` reduction 完了 — 残りは 2 つの場合の本体のみ

`S06_Thm64.lean` 477 → 599 行。3 定理、すべて sorry-free・axiom-clean・AxiomsCheck 登録済。

- **`thm64_of_le_proper_subgroup`** (`:524`) — 本体。`J₁, J₂, H` を含む**任意の真部分群 `S`**
  について、帰納法の仮定を `↥S` の中で使えば結論が出る。8 仮説すべてが transport し、
  結論 2 つが `S.subtype` に沿って押し戻る。
  ⚠ BG は `S = L ⊔ H` で述べるが、**証明は `S` の形を一切使わない**ので一般の `S` で述べた。
- **`thm64_of_sup_ne_top`** (`:592`) — BG の形 (`J₁ ⊔ J₂ ⊔ H ≠ ⊤`)。上の 1 行特殊化。
- **`subgroupOf_le_normalizer_subgroupOf`** (`:496`) — normalizer の subtype への transport。
  `S` に仮説を一切要求しない (`H ≤ S` すら不要)。mathlib の
  `normal_subgroupOf_iff_le_normalizer` 族は `H.subgroupOf K` の**正規性**の特徴付けで別物。

使った道具はすべて既存: `isPiGroup_subgroupOf` ×3 / `normal_coprime_card_index_subgroupOf` /
`isNilpotent_quotient_fitting_of_le` / **`isNilpotent_quotient_fitting_quotient_subgroupOf`**
(第3波の mathlib 単射性補題が設計どおりここで効いた) / `card_subgroup_add_card_subgroupOf_lt`。

### 見積はまた 2-3 倍高かった

「reduction の実施 200-350 行」と見積もっていたが、docstring 込みで **~105 行**。
第2波の transport 行と同じパターン (実装してみると見積もりの 1/2〜1/3)。

### 残り = 2 つの場合の本体のみ (どちらも `G = LH` を仮定してよくなった)

| 残作業 | 行 |
|---|---|
| Case 1 `π(F(G)) ⊄ π(H)` | 300-450 |
| Case 2 `π(F(G)) ⊆ π(H)` | 500-800 |

Case 1 が第2波の商側 transport (`normal_coprime_card_index_map_mk'` /
`isNilpotent_quotient_fitting_quotient`) の消費者。まだ誰も使っていない。

### ⚠ 新たに発見した重複 (issue 9159 に分離)

`Subgroup.IsPiGroup` (`Ch03_SplitExtensions/Theorem315.lean:298`) と
`Subgroup.IsPiSubgroup` (`GroupTheory/OpResidual.lean:39`) が **byte-identical な別定義**で、
どちらも `Subgroup` 名前空間に在る。`thm64_of_le_proper_subgroup` は現に両者の defeq に
依存して 3 箇所を通している (compile は通るが、片方が `@[irreducible]` になれば壊れる)。

### mathlib gap (今回は回避、記録のみ)

`MonoidHom.subgroupComap` (`Mathlib/Algebra/Group/Subgroup/Map.lean:496`) に
`subgroupComap_surjective_of_surjective` はあるが**単射版が無い**。今回は
`MulEquiv.subgroupCongr` + `Subgroup.subgroupOfEquivOfLe` で迂回したので新規 infra は不要だった。
