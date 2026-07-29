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
- [x] case (2) の `W = 1` パート — **2026-07-29 完了**
- [x] case (2) の PSU 排除 — **2026-07-29 完了 (書籍と別経路: 位数の数え上げ)**
- [x] case (3) の `st` 位数 3 パート — **type C/D 側 2026-07-29 完了**
- [x] case (3) の `st` 位数 3 パート — **type B 側も 2026-07-29 完了 (無条件)**
- [x] case (3) の PSL 分岐排除 — **2026-07-29 完了** (Frobenius 論法は不要になった)
- [ ] case (3) の `W ≠ 1` パート — **[issue 0164](0164-psu3-sylow-normalizer-centralizer.md) に gate**
- [ ] Suzuki 2-群の位数二分法 `|P| = |Z(P)|²` (type A) / `|Z(P)|³` (type B/C/D) — 3 分岐の組み立ての前提
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

## case (2) の `W = 1` パート — 部品の実測 (2026-07-29)

書籍 p.117: 「`W ≠ 1` なら `C_S(P)` は指数 4 の `K`-部分群ゆえ `C_S(P) = S`、
しかし `D` は `S` に忠実に作用するので矛盾 ⟹ `W = 1`」。

| 必要なもの | repo | 状態 |
|---|---|---|
| `D` が `Q` に忠実 (`C_D(Q) = 1`) | `centralizer_Q_inf_D_eq_bot` (`DistinguishedInvolution.lean:356`) | ✅ |
| 「`K`-不変部分群は `⊥` か `⊤`」engine | `Suzuki2Groups.invariant_eq_bot_or_top_of_fixedPointFree_card` (`InvariantSummands.lean:165`) | ✅ 仮説 = `rho : K →* MulAut E` の不動点自由性 + **`\|K\| = \|U\| − 1`** + `IsAInvariant` |
| `KSet · W` の構造 | `fittingPreimageInG_eq_KSet_mul_W` (`KCyclic.lean:664`) | ✅ |
| `W = C_D(H ∩ I)` | `W_eq_centralizer_involutions_H` (`CentralizerStructure.lean:241`) | ✅ |

### ⚠ 次セッションで最初に確定すべき論点

書籍は「`C_S(P)` は `K`-部分群」と言うが、これは **`P ⊂ W` という証明冒頭の取り方**
(「`W ≠ 1` なら `P ⊂ W` と仮定する」) に依存する。`K` が `C_S(P)` を正規化する理由
(= `K` が `P` を正規化/中心化する理由) を repo の事実で確定すること。候補:

* `W = C_D(H ∩ I) = C_D(Q₀^#)` なので `P ⊆ W` は `Q₀` を中心化する。
* `D` の構造 (`\|D\| = \|V\|\|K\|`、`K ⊴ D` cyclic = I.2 Prop 2、`W ≤ V`) から
  `[K, W] = 1` が出るか。**これは未確認** — `KCyclic.lean` / `CentralizerStructure.lean` を
  実測し、無ければ書籍 pp. 100-107 の該当箇所をページ画像で読む。

⚠ この論点を仮定で埋めない。確定できないうちは「`K` が `C_Q(P)` を正規化する」を
**明示仮説に取った形**で `W = 1` を証明し、仮説の供給は別 landing にする
(sorried-cite でなく仮説パラメータ化なので sorry は増えない)。

## ✅ `[K, W] = 1` を解決 (2026-07-29) — 前セッションで flag した論点

前節で「未確定」とした「`K` が `C_S(P)` を正規化する根拠」は **repo の既存事実 3 つから導けた**
(書籍 pp.100-107 を読む必要は無かった):

| 使った事実 | 所在 |
|---|---|
| `W = C_D(Q₀)` = `D` の `Q₀` 上の作用の核 | `ker_conjQ0` (`KCyclic.lean:96`) |
| `K ⊴ D` (Ch.I §2 Prop 2) | `K_normal` (`KCyclic.lean:800`) |
| `K ⊓ V = ⊥` | `K_inf_V_eq_bot` (`KCyclic.lean:830`)、`W_le_V` (`Basic.lean:202`) |

`w ∈ W`, `k ∈ K` に対し `wkw⁻¹k⁻¹` は正規性で `K` に入り、`w` が `Q₀` 上自明ゆえ
`Q₀` 上自明 ⟹ `K ⊓ W ≤ K ⊓ V = ⊥` ⟹ `= 1`。

landing した定理:

| 定理 | 内容 |
|---|---|
| `Hypothesis.commute_of_mem_K_of_mem_W` | **`[K, W] = 1`** |
| `Hypothesis.conj_mem_centralizer_of_mem_K_of_le_W` | ⟹ `P ≤ W` なら `C_Q(P)` は `K`-不変 (= 書籍の「`C_S(P)` は `K`-部分群」) |
| `Hypothesis.sqFibre_eq_coset_of_card` | 「`{y ∈ S \| y² = s} = xQ₀`」(サイズ一致から集合一致) |

## 次 = `W = 1` の組み立て (設計確定済、2026-07-29)

残るのは「`K`-不変で位数 4 の元を含む `Q` の部分群は `Q` 自身」。**engine は要らない** —
`invariant_eq_bot_or_top_of_fixedPointFree_card` の仮説 (`\|K\| = \|U\|−1` + 不動点自由) を
揃えるより、次の 2 段が直接的:

1. **`Q₀` 側**: `X ≤ Q₀` が `K`-不変で `≠ ⊥` なら `X = Q₀`。
   `image_conj_KSet_eq_involutions_H` (`K` が `Q₀^#` 上推移的) から**直接**。
2. **`Q/Q₀` 側**: `K` は `(Q/Q₀)^#` 上推移的。
   **`card_sqFibre_eq_card_Q0_of_isSuzuki2Group` + `sqFibre_eq_coset_of_card` が鍵**:
   平方写像は `Q/Q₀ → Q₀` を誘導し (`c ∈ Q₀ ≤ Z(Q)`, `c² = 1` ゆえ well-defined)、
   fibre が単一 `Q₀`-剰余類なので**単射**、`\|Q/Q₀\| = \|Q₀\| = q` (case 2) ゆえ**全単射**。
   `K`-同変なので `Q₀^#` 上の推移性が `(Q/Q₀)^#` に移る。
   具体的には `y, z ∈ Q ∖ Q₀` に対し `a, b ∈ KSet` で `a⁻¹ s a = y²`, `b⁻¹ s b = z²` を取り
   `k := b⁻¹a ∈ K` とすると `k y² k⁻¹ = z²`、`b` 共役で fibre を `s` 側に移して
   `sqFibre_eq_coset_of_card` を当てると `k y k⁻¹ ∈ z Q₀`。
3. ⟹ `X` が `K`-不変で位数 4 の元 `y` を含めば `y² ∈ Q₀^#` から (1) で `Q₀ ≤ X`、
   `ȳ ≠ 1` から (2) で `X Q₀ = Q` ⟹ `X = Q`。
4. `C_Q(P) = Q` は `C_D(Q) = 1` (`centralizer_Q_inf_D_eq_bot`) に矛盾
   (`P ≤ W ≤ V ≤ D`、`P ≠ ⊥`) ⟹ **`W = 1`**。


## case (2) 完結記録 (2026-07-29)

case (2) = 書籍の (b) のうち **`W = 1`** と **`orderOf (st) = 5`** の両方が landing。

### `W = 1`

| 定理 | 内容 |
|---|---|
| `exists_le_card_eq_prime` | 「素数位数の部分群 `P` を取る」(`V` 側・`W` 側で共用) |
| `Hypothesis.exists_mem_K_conj_eq_of_mem_Q0` | `K` は `Q₀^#` 上推移的 (§1 Prop 3 の要素形) |
| `Hypothesis.eq_bot_or_Q0_le_of_kInvariant` | `Q₀` 内の `K`-不変部分群は `⊥` か `Q₀` |
| `Hypothesis.sq_mem_Q0_of_isSuzuki2Group` | 指数 4 (Higman Thm 1(a)) ⟹ 平方は `Q₀ = Ω₁(Q)` |
| `Hypothesis.inv_mul_mem_Q0_of_sq_eq` | 平方の fibre はどれも単一 `Q₀`-剰余類 |
| `Hypothesis.exists_mem_K_conj_mem_coset` | `K` は `(Q/Q₀)^#` 上推移的 |
| `Hypothesis.Q_le_of_kInvariant_of_sq_ne_one` | `K`-不変で位数 4 の元を含む `X ≤ Q` は `Q` |
| `SecondCaseHypothesis.W_eq_bot_of_isSuzuki2Group` | **`W = 1`** |

`P ≤ W` を素数位数に取ると `[K,W] = 1` から `C_Q(P)` は `K`-不変、そこに `s` の平方根
(位数 4) が在るので `C_Q(P) = Q`。すると `P ≤ W ≤ V ≤ D` が `Q` を中心化して
`C_D(Q) = 1` (Ch.I Prop 4(c)) に反する。

### `orderOf (st) = 5` — ⚠ 書籍から意図的に逸脱

書籍は PSU(3,ℓ) 分岐を **「`G₀ = PSU(3,ℓ)`、`S₀ ∈ Syl₂(G₀)`、`N_{G₀}(S₀) = S₀ ⋊ D₀` とすると、
確かめられるように `C_{D₀}(Ω₁(S₀)) ≠ 1`」** で排除するが、**本文はこの計算を実行していない**。
repo の `CentralizerPSUData` が同分岐の**位数関係 `|C_Q(P)| = |C_{Q₀}(P)|³`**
(`natCard_cQ_eq_cQ0_cube`) を既に持っているので、数え上げで正面から矛盾させた:

| 定理 | 内容 |
|---|---|
| `Hypothesis.two_le_natCard_inf_Q0_centralizer` | `P ≤ V = C_D(s)` ゆえ `s ∈ C_{Q₀}(P)` ⟹ `|C_{Q₀}(P)| ≥ 2` |
| `Hypothesis.natCard_inf_centralizer_le_sq` | **`|C_Q(P)| ≤ |C_{Q₀}(P)|²`** |
| `SecondCaseHypothesis.orderOf_st_eq_five_of_isSuzuki2Group` | **`orderOf (st) = 5`** |

平方写像 `C_Q(P) → C_{Q₀}(P)` の fibre はどれも `C_{Q₀}(P)` の剰余類に含まれる
(`sq_mem_Q0_of_isSuzuki2Group` + `inv_mul_mem_Q0_of_sq_eq`) ⟹ fibre 数 ≤ `|C_{Q₀}(P)|`、
各 fibre ≤ `|C_{Q₀}(P)|`。`|C_{Q₀}(P)| ≥ 2` なら `|C_{Q₀}(P)|³ > |C_{Q₀}(P)|²` で PSU 分岐は不可能。
PSL 分岐は位数 4 の元で既に排除済 ⟹ 残るのは `Sz(ℓ)` 分岐。

⟹ **gated 候補だった PSU 計算は不要になった**。9500 番台の hub issue は起票せず。

### ファイル分割 (2026-07-29)

case (2) 完結時点で `Trichotomy.lean` が 1090 行 ⟹ mathlib 粒度に沿って 2 分割:

* `StructureOfH/SquareRootFibres.lean` (781 行) — 3 ケース共通の機構
  (fibre・数え上げ・不動点ステップ・`K`-推移性・`[K,W] = 1`・case (1) の核)
* `StructureOfH/Trichotomy.lean` (367 行) — `exists_le_card_eq_prime` と 3 ケースの組み立て

module 名不変ゆえ下流 import は無変更。`OddOrder.lean` / `AxiomsCheck.lean` 配線済。


## case (3) 進捗 (2026-07-29)

### 完了した部分

| 定理 | 所在 | 内容 |
|---|---|---|
| `mul_titsTwist_injective` | `Suzuki/Field.lean` | `a ↦ a·θ(a)` は体全体で単射 (`θ(θx) = x²` だけで証明) |
| `RootGroup.sq_inv_mul_eq_one_of_sq_eq` / `StandardTypeAData.sq_inv_mul_eq_one_of_sq_eq` | `Suzuki/{RootGroup,RootSubgroupSuzukiType}.lean` | **type A の平方写像は Ω₁ を法として単射** |
| `exists_mem_centralizer_of_conj_invariant` | `SquareRootFibres.lean` | 不動点ステップの一般形 |
| `card_sqFibreIn_eq_card_Q0_of_kInvariant` ほか `*In` 系 | `SquareRootFibres.lean` | fibre 機構を `S` から K-不変 `X` (`Q₀ ≤ X ≤ Q`、位数 `\|Q₀\|²`) へ一般化 |
| `inf_eq_Q0_of_ne_of_kInvariant` | `SquareRootFibres.lean` | 相異なる 2 つの K-部分群は `Q₀` で交わる |
| `false_of_typeA_centralizer_of_two_kSubgroups` | `Trichotomy.lean` | **case (3) の矛盾本体** |
| `orderOf_st_eq_three_of_two_kSubgroups` | `Trichotomy.lean` | 2 つの K-部分群 ⟹ `orderOf (st) = 3` |
| `liftCentralQuotient` + 4 補題 / `exists_two_kSubgroups_of_card_cube` | `TwoKSubgroups.lean` (新 leaf) | **Higman (d) を G の言葉へ** |
| `isKSubgroupSquare_map_conj` / `map_conj_eq_self_of_unique` / `conj_mem_of_unique_of_le_V` | `TwoKSubgroups.lean` | 奇位数の `P` は 2 元集合を交換できない (`g` の平方根 `h = g^((p+1)/2)` を取るだけ) |
| `exists_two_kSubgroups_unique_of_card_cube` | `TwoKSubgroups.lean` | **`¬IsTypeB` ⟹ K-部分群はちょうど 2 つ** |
| `orderOf_st_eq_three_of_card_cube_of_not_isTypeB` | `Trichotomy.lean` | **type C/D 側の case (3) `st` 位数 3 が完結** |

### 残り (1): type B 側の設計 — 数え上げでなく Maschke で行く

書籍は「位数 4 の元が生成する K-部分群 (1 つ目) + 位数 `q²` の K-部分群は `q+1` 個」
という**数え上げ**で 2 つ目を得るが、`q+1` の計算には `End_K(M) = 𝐅_q` 相当の加群論が要る。
**より短い経路を採る**:

1. **1 つ目**: Sz 分岐なら `C_Q(P)` は Suzuki 2-群 = 非可換 ⟹ 位数 4 の元 `v ∈ C_Q(P)` が在る。
   `v̄ ∈ S/Q₀` は `P` 不動で `≠ 1`。`N := ⟨v̄^K⟩` は `K`-不変
   (`P` は `v̄` を固定し `K ⊴ D` を正規化するので **`P`-不変でもある**)。
2. **`\|N\| = q` を出す** (type B のときの鍵): `S/Q₀ = X̄ ⊕ Ȳ` で
   `e : X̄ ≅_K Ȳ` が在る (type B = 和因子が K-同変同型;
   `IsTypeB.exists_isomorphicOrderQModuleSplit`)。`v̄ = x·y` と分解して
   * `y = 1` / `x = 1` なら `N ⊆ X̄` または `Ȳ` で位数 ≤ q
   * 両方 ≠ 1 なら **`K` は `Ȳ^#` 上推移的** (`restrict_transitive_of_fixedPointFree_card`)
     なので `k·(e x) = y` なる `k ∈ K` が在り、**graph**
     `N' := {z · (k·(e z)) : z ∈ X̄}` が `v̄` を含む位数 `q` の `K`-部分加群。
     `⟨v̄^K⟩ ⊆ N'` ゆえ `\|N\| ≤ q`。
3. **2 つ目**: **operator Maschke**
   (`BG/Ch1_Preliminary/OperatorMaschke.lean` の
   `exists_aInvariant_complement_of_isElementaryAbelian`) を
   `E := ↥Q ⧸ Z(↥Q)` (基本アーベル 2-群、`csplit.quotientEA`)、
   `A := K ⊔ P ≤ D` (**`\|D\|` は奇** = `hyp.D_odd` ゆえ `\|A\|` も奇で `\|E\|` と互素)、
   `U := N` に当てて `A`-不変な補群 `N'` (位数 `q`) を得る。
   `A`-不変 ⟹ `K`-不変かつ `P`-不変。⟹ `N`, `N'` の lift が求める `X ≠ Y`。

必要な新規プラミング: `conjQByD : ↥hyp.D →* MulAut ↥hyp.Q` (既存の
`conjQByK` / `conjQByW` と同型の構成) とその `K ⊔ P` への制限。

### 残り (2): `W ≠ 1` (Frobenius)

書籍: `W = 1` とすると case (2) 同様 `C_V(C_{Q₀}(P)) = P`、`F/Z(F) ≇ PSU(3,ℓ)`、
`st` 位数 3 ゆえ `C_S(P)` 基本アーベルの場合になる。しかし `[K,P] ⋊ P` は `S/Q₀` 上の
Frobenius 群で `[K,P]` は不動点自由 ⟹ `C_{S/Q₀}(P) ≠ 1` で矛盾。

⟹ 必要なのは (i) `C_S(P)` 基本アーベル ⟹ `C_{S/Q₀}(P) = 1`、
(ii) Frobenius 群の補群は不動点を持つ (repo の `CoprimeFrobeniusKernel` 系を実測)。

### 残り (3): Ch.I §3 Lemma 5 で締める

`lemmaFive_of_orderThree` (`WCyclicDivides.lean:352`) が
`st` 位数 3 + `W ≠ 1` から **type B** を出す。これは**完成形で repo に在る**。


## case (3) の `st` 位数 3 が無条件で完結 (2026-07-29)

書籍の型分け (type C/D は「K-部分群は 2 つだけ」/ type B は「q+1 個」) を、
**「Higman split の和因子が K-同変同型か」**という二分法に書き換えて統一した。

| 定理 | 所在 | 内容 |
|---|---|---|
| `exists_invariant_mem_of_kEquivariantMulEquiv` | `Suzuki2Groups/SplitUniqueness.lean` | 和因子が同型なら任意の元が位数 q の K-不変部分群に入る (graph 構成) |
| `conjQBy` / `conjQuotientBy` / `conj_mem_liftCentralQuotient` / `aInvariant_map_of_conj_mem` | `TwoKSubgroups.lean` | 任意の作用素部分群 `A ≤ H` 版の作用と橋 |
| `exists_kSubgroupSquare_complement` | `TwoKSubgroups.lean` | **operator Maschke** (`\|D\|` 奇 + `Q ⧸ Z(Q)` 基本アーベル 2-群) で相棒を作る |
| `conj_mem_sup` / `conj_mem_of_mem_centralizer` | `TwoKSubgroups.lean` | P が中心化する元を含む K-部分群は P-不変 |
| `exists_two_kSubgroups_invariant_of_card_cube` | `TwoKSubgroups.lean` | **P が正規化する 2 つの K-部分群 (無条件)** |
| `orderOf_st_eq_three_of_card_cube` | `Trichotomy.lean` | **case (3) の `orderOf (st) = 3` (無条件)** |
| `not_cQ_isElementaryAbelian_of_kSubgroup` | `Trichotomy.lean` | P-不変な K-部分群が在れば **PSL(2,ℓ) 分岐は排除される** |

## 残り: `W ≠ 1` の分析 (2026-07-29)

書籍 p.117 の最後の段落を実測して分解した:

1. `W = 1` ⟹ Ch.I §2 Prop 3 で `V` は `Q₀` 上の体自己同型群、Galois で
   `C_V(C_{Q₀}(P)) = P`。
2. それと **`PSU(3,ℓ)` の `C_{D₀}(Ω₁(S₀)) ≠ 1`** から `F/Z(F) ≇ PSU(3,ℓ)`。
3. `st` 位数 3 ゆえ残るのは PSL 分岐 (`C_S(P)` 基本アーベル)。
4. `[K,P] ⋊ P` が `S/Q₀` 上 Frobenius ⟹ `C_{S/Q₀}(P) ≠ 1` で矛盾。

**(4) は不要になった**: `not_cQ_isElementaryAbelian_of_kSubgroup` が、P-不変な
K-部分群の平方根 fibre から位数 4 の元を直接出して PSL 分岐を潰す
(Frobenius 群の議論も `\|V\| = \|C_V(B)\|^{\|F\|}` 型の定理も不要)。

**残る gate は (1)+(2) のみ** = 書籍自身が "as can be checked" で省略する
`PSU(3,ℓ)` の Sylow 2-正規化群の計算。⚠ case (2) では位数の数え上げで代替できたが、
**case (3) では代替できない** — 実際 case (3) の分岐は PSU そのものだから
(`\|C_Q(P)\| = \|C_{Q₀}(P)\|³` が成り立つ)。`W = 1` の仮定が本質的に効く箇所である。

⟹ **`W ≠ 1` は `PSU(3,ℓ)` の構造計算 (issue 0164) を待つ**。それまでは
case (3) の残りを仮説パラメータ化して前倒しする。


## 次の前提: Suzuki 2-群の位数二分法 (2026-07-29 実測)

Proposition 本体 (3 分岐の disjunction) の組み立てには、書籍が
「Appendix III の定理」で使う**位数の二分法**が要る:

> Suzuki 2-群 `P` は `|P| = |Z(P)|²` (type A) または `|P| = |Z(P)|³` (type B/C/D)。

**repo に無い** (2026-07-29 実測):
* `higmanClassification_of_isSuzuki2Group` は型の disjunction を出すが**位数は言わない**
* `XiLengthFromCard.lean` は `|P| = q³ ⟹ ξ-length 3` の**向きだけ**
  (`hasXiLengthThree_of_card_eq_cube`)。逆向き (型 ⟹ 位数) は無い
* 各型の `*Data` は `equivModel : P ≃* TypeXModel …` を持つので、
  **モデルの位数**から出る: `TypeXModel = QuadraticExtension q basis
  = BilinearTwistedProduct (q.toBilin basis)` は `W × V` 型ゆえ
  `Nat.card = |W| * |V|`。type A は `V = W = F` で `|F|²`、
  type B/C/D は `V = F × F`, `W = F` で `|F|³`。
* あわせて `Z(P) = inl.range` (位数 `|F|`) の同定が要る
  (`range_inl_le_center` は片側包含のみ; 逆包含は非可換性から)。

⚠ 部分的な代替: `K` が `Q₀^#` 上推移的なので平方写像の fibre 数え上げから
`(|Q₀|−1) ∣ (|Q|/|Q₀| − 1)` が出て `|Q| = |Q₀|^{k+1}` (`k ≥ 1`) までは言える。
上限 `k ≤ 2` が Higman (ξ-length ≤ 3) の内容で、そこが未 export。
