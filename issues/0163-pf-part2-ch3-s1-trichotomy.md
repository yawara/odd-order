---
id: 163
slug: pf-part2-ch3-s1-trichotomy
title: "Peterfalvi Part II Ch.III §1 Proposition: S の 3 分岐 (S=Q₀ / type A / type B)"
created: 2026-07-29
---

# Peterfalvi Part II Ch.III §1 Proposition: S の 3 分岐 (S=Q₀ / type A / type B)

## 背景

[issue 0162](closed/0162-pf-part2-ch3-theorem-c.md) で **Theorem C** (`Q` は 2-群) が
2026-07-29 に完成 (`7175e6a73`)。文書順の次は同じ Ch.III §1 の **Proposition** (p. 116 下部)。

### 実測 (2026-07-29) — survey ラベルの棚卸し

survey (`three_books_full_survey_2026_07_16.md` L825–L862) の「Pf App: Suzuki」表で
**「未」のうち 3 件が実際は済**だった (ラベル stale、CLAUDE.md の警告どおり):

| survey ラベル | 実測 |
|---|---|
| I.3 Lemma 5 = 未 | **済** — `Suzuki/WCyclicDivides.lean:352` (完全な statement)。支えは `TypeBFromW.lean` / `Suzuki2Groups/{SquareCosetFiber,ConjugateSummandSplit,KSubgroupOrbit,ActualQuotientAction}.lean` / `Suzuki/OrderThreeSuzukiCentralizer.lean` |
| Thm B = 未 | **済** — `Suzuki/FirstCase/TheoremB.lean:81` (2026-07-26 `55ec6f681`) |
| Thm C = 未 | **済** — 2026-07-29 (issue 0162) |
| 「Higman classification は scaffold-only, `higman_classification` sorried」 | **stale** — `higman_classification` は repo に**存在しない** (grep 0 件)。`OddOrder/Higman/Suzuki2Groups/**` と `Peterfalvi/Appendices/Suzuki2Groups/**` は**全 file sorry ゼロ** (comment-strip 済カウント) |

`OddOrder/Peterfalvi/Appendices/**` 全体の実 sorry は **1 件のみ** =
`RankOneAffineModel.lean:299` (`brauerSuzuki_quaternionSylow_q8`、issue 0147 の Q₈ 長期案件、
Navarro 1998 待ち — 本 issue とは無関係)。

⟹ **Ch.III §1 Prop が真の次 frontier**。`Ch. IV` は file ゼロで完全未着手 (これは survey どおり)。

## 書籍 (p. 116 下部 – p. 117、ページ画像 `references/peterfalvi/pages/peterfalvi-p116.png` / `-p117.png` で確定)

**Proposition.** 次の 3 つのうち 1 つが成り立つ。

* (a) `S = Q₀` かつ `st` は位数 3。
* (b) `S` は **type A** の Suzuki 2-群、`st` は位数 5、`W = 1`。
* (c) `S` は **type B** の Suzuki 2-群、`st` は位数 3、`W ≠ 1`。

### 証明の骨格

**共通の設定**: `P ≤ V` を素数位数 `p` の部分群 (`W ≠ 1` なら `P ⊂ W` に取る)。
`F = O^{2'}(C_G(P))`、`ℓ = |C_{Q₀}(P)|`。**(C1) + Ch.I §3 Prop 1** で次の 3 択:

| | `st` の位数 | `C_S(P)` | `F/Z(F)` |
|---|---|---|---|
| (i) | 3 | 基本アーベル | `PSL(2, ℓ)` |
| (ii) | 5 | type A の Suzuki 2-群 | `Sz(ℓ)` |
| (iii) | 3 | 位数 `ℓ³` の Suzuki 2-群 | `PSU(3, ℓ)` |

さらに Ch.I §2 で「`S` はアーベル or Suzuki 2-群」。Appendix III の定義と定理を使って
`S` の位数で場合分けする。

**(1) `S` がアーベル** ⟹ `C_S(P)` もアーベル ⟹ 3 択は (i) ⟹ `st` 位数 3、`C_S(P) ⊂ Q₀`。
そこで `S = Q₀` を示す (背理法):
`S ≠ Q₀` なら `K` が `Q₀^#` 上推移的なので `x² = s` なる `x ∈ S` が在り、`S` アーベルゆえ
`{y ∈ S | y² = s} = xQ₀`。`P` は `s` を中心化する (**Ch.I §1 Prop 5**: `V = C_D(s)`) ので
`xQ₀` を正規化するが、`|xQ₀| = |Q₀|` は `p` と互素 ⟹ `P` は `xQ₀` に不動点を持つ ⟹
`C_S(P) ⊄ Q₀` で矛盾。

**(2) `S` が非アーベルで位数 `q²`** ⟹ type A。`x² = s` なる `x` を取り
`|{y ∈ S | y² = s}| = (q² − q)/(q − 1) = q` から再び `{y | y² = s} = xQ₀`、
`P` が `xQ₀` を正規化 ⟹ `C_S(P)` の指数は 4。
`W ≠ 1` なら `C_S(P)` は指数 4 の `K`-部分群ゆえ `C_S(P) = S` ⟹ `D` が `S` に忠実に作用する
ことに矛盾 ⟹ **`W = 1`**。Ch.I §2 Prop 3 で `V` は `Q₀` 上の体自己同型群として作用し、
Galois 理論で `C_V(C_{Q₀}(P)) = P`。
`G₀ = PSU(3,ℓ)`、`S₀ ∈ Syl₂(G₀)`、`N_{G₀}(S₀) = S₀ ⋊ D₀` について
**`C_{D₀}(Ω₁(S₀)) ≠ 1`** (書籍は "as can be checked") ⟹ `F/Z(F) ≇ PSU(3,ℓ)` ⟹
`C_S(P)` の指数が 4 なので `F/Z(F) ≅ Sz(ℓ)`、`st` は位数 5。

**(3) `S` が非アーベルで位数 `q³`**:
type C / type D なら `S/Q₀` は `𝐅₂[K]`-加群で `S/Q₀ = X ⊕ Y` (`X`, `Y` は非同型・位数 `q`)
⟹ `X`, `Y` は `S/Q₀` の位数 `q` の唯一の `𝐅₂[K]`-部分加群 ⟹ `P` は `X`, `Y` を正規化。
`st` が位数 5 と仮定すると `C_S(P)` は type A。`S` が type B なら位数 4 の元は位数 `q²` の
`K`-部分群を生成し、位数 `q²` の `K`-部分群は `q+1` 個 ⟹ `P` は 2 つ以上の `K`-部分群
`X`, `Y` (位数 `q²`) を正規化 (type C/D でも前段落より同じ) ⟹ (2) と同様に
`x ∈ X`, `y ∈ Y` で `x² = y² = s` を中心化 ⟹ `C_S(P)` が type A ゆえ
`y ∈ x·Ω₁(C_S(P))` かつ `y ∈ X` で矛盾 ⟹ **`st` は位数 3**。
`W = 1` と仮定すると (2) と同様に `C_V(C_{Q₀}(P)) = P`、`F/Z(F) ≇ PSU(3,ℓ)`、
`C_S(P)` 基本アーベルの場合になる。しかし `[K,P] ⋊ P` は `S/Q₀` 上 Frobenius 群で
`[K,P]` は `S/Q₀` 上不動点自由 ⟹ `C_{S/Q₀}(P) ≠ 1` で矛盾 ⟹ **`W ≠ 1`**。
**Ch.I §3 Lemma 5** で `S` は type B。

## 前提の所在 (2026-07-29 実測)

| 書籍 | repo | 状態 |
|---|---|---|
| Ch.I §3 Prop 1(c) の 3 択 | `centralizer_trichotomy_of_induction` (`CentralizerTrichotomy.lean`) | ✅ 教科書強度。`CentralizerPSLData` / `CentralizerSuzukiData` / `CentralizerPSUData` が `distinguishedProduct_order` (= `orderOf (st)`)・`cQ_isElementaryAbelian`・`natCard_cQ0_eq_field` 等を実データで持つ |
| Ch.I §2 Cor (`S` アーベル or Suzuki 2-群) | `sylowTwo_isMulCommutative_or_isSuzuki2Group` (`SylowTwo.lean:61`) | ✅ |
| `Q₀` | `QStructure.lean:293` | ✅ |
| `K` が `Q₀^#` 上推移的 | `conjQ0bar_transitive` (`KCyclic.lean:147`)、`fittingAction_transitive` (`SemilinearIdentification.lean:147`) | ✅ |
| Ch.I §1 Prop 5 (`V = C_D(s)`) | `V_eq_centralizer_distinguishedInvolution` (`CentralizerStructure.lean:143`) | ✅ |
| Ch.I §2 Prop 3 (`V` が体自己同型) | `exists_semilinear_equiv` (`SemilinearRealization.lean:339`) | ✅ |
| Ch.I §3 Lemma 5 | `WCyclicDivides.lean:352` | ✅ |
| Appendix III type A / type B | `IsTypeA` / `IsTypeB` (`Suzuki2Groups/Types.lean:194` / `:285`) | ✅ |
| Appendix III type C / type D | ✅ **在る (2026-07-29 再実測)** — `IsTypeC` / `IsTypeD` は `OddOrder.Higman.Suzuki2Groups` 名前空間 (`Peterfalvi/Appendices/Suzuki2Groups/Types.lean` でなく `Higman/Suzuki2Groups/**`)。前回の「無い」は grep 範囲が狭かっただけ |
| **Appendix III の定理 (Higman classification)** | ✅ **在る・sorry-free** — `Higman.Suzuki2Groups.higmanClassification_of_isSuzuki2Group : IsSuzuki2Group P → IsTypeA ∨ IsTypeB ∨ IsTypeC ∨ IsTypeD`。派生の `pow_four_eq_one_of_isSuzuki2Group` (Higman Thm 1(a), 指数 ∣ 4) も在り、`Trichotomy.lean` の import closure から到達可 |
| `PSU(3,ℓ)` の `C_{D₀}(Ω₁(S₀)) ≠ 1` | **未** — 書籍が "as can be checked" とする具体計算。`CentralizerPSU*.lean` が何を構成済かを実測してから判断 |

## やること

- [x] **case (1)** (`S` アーベル ⟹ `S = Q₀` かつ `st` 位数 3) — **2026-07-29 完了** (下記)
- [x] **case (2) の指数 4 パート** — **2026-07-29 完了** (`C_Q(P)` が Suzuki 2-群 = PSL 分岐排除)
- [ ] case (2) の `W = 1` パート (`C_S(P)` は指数 4 の `K`-部分群 ⟹ `C_S(P) = S` ⟹ `D` の忠実性に矛盾)
- [ ] case (2) の PSU 排除 (`C_{D₀}(Ω₁(S₀)) ≠ 1`) — gated なら 9500 番台で hub issue 化
- [ ] case (3) の `st` 位数 3 パート
- [ ] case (3) の `W ≠ 1` パート (Frobenius `[K,P] ⋊ P`)
- [ ] 3 分岐の組み立て (Proposition 本体)

⚠ 上流優先 + 文書順に従い、**gated な部分 (PSU 計算) が出ても止まらない**:
sorried-cite skeleton で前倒しし、ungated な genuine math を先に全部埋める
(CLAUDE.md 「レーン内 frontier 選択は自律判断」policy (A))。

## 完了条件

`SecondCaseHypothesis` (または適切な仮説) の下で 3 分岐の disjunction が sorry-free で landing し、
AxiomsCheck に登録されて axiom-clean。フルビルド green + `--strict` 警告ゼロ + sorry 非退行。

## 参照

* 前の結果 = [issue 0162](closed/0162-pf-part2-ch3-theorem-c.md) (Theorem C、2026-07-29 完成)
* Ch.II Theorem B = [issue 2053](pending/2053-pf-suzuki-theorem-b.md) (2026-07-26 完成)
* 書籍 pp. 116–117 = `references/peterfalvi/pages/peterfalvi-p116.png` / `-p117.png`
* 章 PDF = `references/peterfalvi/pdf/05.5_pp_115_121_The_Structure_of_H.pdf`

## case (1) 完了記録 (2026-07-29)

新 leaf `StructureOfH/Trichotomy.lean` (`OddOrder.lean` 配線済、AxiomsCheck 登録済、
5 定理すべて `[propext, Classical.choice, Quot.sound]` のみ):

| 定理 | 内容 |
|---|---|
| `SecondCaseHypothesis.sylowTwoOfQ_eq_Q` | Theorem C (`Q₁ = ⊥`) より **書籍の `S` は `Q`** |
| `Hypothesis.mem_Q0_of_mem_Q_of_sq_eq_one` | `Ω₁(Q) = Q₀` (repo の `Q₀ = {x \| x²=1 ∧ x∈H}` から即座) |
| `Hypothesis.exists_sq_eq_distinguishedInvolution` | 「`x² = s` なる `x ∈ S` が在る (`K` が `Q₀^#` 上推移的)」 |
| `SecondCaseHypothesis.centralizer_le_Q0_and_orderOf_st_of_commute` | 分岐選択: `Q` 可換 ⟹ PSL 分岐 ⟹ `orderOf (st) = 3` かつ `C_Q(P) ≤ Q₀` |
| `SecondCaseHypothesis.Q_eq_Q0_of_commute_of_centralizer_le` | coset + 不動点の核 |
| `SecondCaseHypothesis.Q_eq_Q0_and_orderOf_st_of_commute` | **case (1) 本体**: `Q` 可換 ⟹ `Q = Q₀` かつ `orderOf (st) = 3` |

### 分岐選択が思ったより軽かった (実測)

`centralizer_trichotomy_of_induction` の `CentralizerSuzukiData` / `CentralizerPSUData` が
両方 **`cQ_isSuzuki2Group : IsSuzuki2Group ↥(Q.subgroupOf C_G(P))`** を持ち、
`IsSuzuki2Group` の定義 (`GroupTheory/SpecificGroups/Suzuki2Group/Basic.lean:355`) は
第 2 連言子に **`¬ IsMulCommutative P`** を含む。⟹ `Q` 可換なら `C_Q(P)` も可換なので
2 分岐が即座に落ちる (`det.cQ_isSuzuki2Group.2.1` に `absurd`)。
書籍の「`C_S(P)` はアーベルゆえ `st` は位数 3」がそのまま 1 行になった。

`C_S(P) ⊂ Q₀` も PSL 分岐の 2 フィールド
`natCard_cQ0_eq_field` / `natCard_cQ_eq_field` (どちらも `= |F|`) から
`Subgroup.eq_of_le_of_card_ge` で出る。

### 次 = case (2) (`S` 非アーベルで位数 `q²`)

書籍 p.117 の (2)。`W = 1` パートまでは ungated に見える
(`C_S(P)` の指数 4 + `D` の `S` 上の忠実性)。PSU 排除の
`C_{D₀}(Ω₁(S₀)) ≠ 1` が gated 候補 — 着手時に `CentralizerPSU*.lean` /
`GroupTheory/SpecificGroups/ProjectiveUnitary/**` が何を構成済かを実測する。

## case (2) 前半 完了記録 (2026-07-29)

case (1) から**再利用可能な機構を切り出して**から case (2) に進んだ:

| 定理 | 内容 |
|---|---|
| `Hypothesis.sqFibre` | 書籍の `{y ∈ S \| y² = s}` (3 ケース共通) |
| `Hypothesis.mul_mem_sqFibre` | `Q₀ ≤ Z(Q)` ゆえ fibre は `Q₀`-剰余類の和 (**`Q` の可換性は不要**) |
| `Hypothesis.prime_ne_two_of_le_V` / `not_dvd_card_Q0` | `p` は奇 / `p ∤ \|Q₀\|` |
| `Hypothesis.exists_mem_centralizer_mem_sqFibre` | **不動点ステップ**: `p ∤ \|fibre\|` ⟹ `C_Q(P)` に `s` の平方根 |
| `Hypothesis.card_sqFibre_eq_card_Q0_of_commute` | case (1) の数え上げ (`Q` 可換) |
| `Hypothesis.two_le_card_Q0` | `s ∈ Q₀` ゆえ `\|Q₀\| ≥ 2` |
| `Hypothesis.card_sqFibre_eq_card_Q0_of_isSuzuki2Group` | **case (2) の数え上げ** `(q²−q)/(q−1) = q` |
| `SecondCaseHypothesis.exists_mem_centralizer_mem_sqFibre_of_isSuzuki2Group` | 指数 4 (位数 4 の元が `C_Q(P)` に在る) |
| `SecondCaseHypothesis.isSuzuki2Group_centralizer_of_card_sq` | **case (2) の分岐選択**: `C_Q(P)` は Suzuki 2-群 (= PSL 分岐排除) |

### case (2) の数え上げの実装

Higman Thm 1(a) (`pow_four_eq_one_of_isSuzuki2Group`) で指数 ∣ 4 ⟹ 平方は `Q₀` に入り、
`Q ∖ Q₀` は `Q₀^#` 上に写る。`K`-共役 (`image_conj_KSet_eq_involutions_H`) で
`\|Q₀\| − 1` 本の fibre が全単射に対応 (`Finset.card_image_of_injective`)、
`Finset.card_eq_sum_card_fiberwise` + `Finset.sum_const` で
`\|Q\| − \|Q₀\| = (\|Q₀\|−1)·\|fibre\|`、`\|Q\| = \|Q₀\|²` と `\|Q₀\| ≥ 2` から
`Nat.eq_of_mul_eq_mul_left` で `\|fibre\| = \|Q₀\|`。

### 次にやること

1. **case (2) の `W = 1`** — 書籍: `W ≠ 1` なら `C_S(P)` は指数 4 の `K`-部分群ゆえ
   `C_S(P) = S`、しかし `D` は `S` に忠実に作用するので矛盾。
   ⟹ 「`K`-部分群」の repo での表現 (`Suzuki2Groups/KSubgroupOrbit.lean` 系) と
   `D` の忠実性 (`dMulAutHom_injective` 系?) を実測すること。
2. **case (2) の PSU 排除** (`C_{D₀}(Ω₁(S₀)) ≠ 1`) — 書籍 "as can be checked"。
   `isSuzuki2Group_centralizer_of_card_sq` が入力を用意済なので、ここだけが残る。
   `GroupTheory/SpecificGroups/ProjectiveUnitary/**` の実測が必要。
3. case (3)、そして 3 分岐の組み立て。
