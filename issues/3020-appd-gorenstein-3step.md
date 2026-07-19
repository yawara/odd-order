---
id: 3020
slug: appd-gorenstein-3step
title: "BG App.D D.1/D.2 のブロッカー = Gorenstein §14.1 (3-step 群 + Cor 14.1.6) — 2026-07-19 に大幅縮小"
created: 2026-07-18
---

# BG App.D: D.1/D.2 の残ブロッカー = Gorenstein Ch.14 §14.1

## 済: opaque scaffold の de-opacify + **偽の文の修正** (2026-07-18)

`AppD_CNGroups.lean` は minimal-simplicity/nonsolvability を**自由 Prop フィールド**
(`minimal_simple : Prop` + `minimal_simple_holds : minimal_simple`) で持っていたため、構造体が
**任意の奇数位数 CN 群で充足可能** (`True`/`trivial` を入れればよい) だった。結果 D.1/D.2 は
「すべての奇数位数 CN 群」について主張することになり、**両方とも偽**:

- **D.2 は反証済 (機械検査、sorry-free)**: `G = C₃` (可換 ⟹ CN、位数 3 奇数)。Sylow-3 は `P = ⊤ ≠ ⊥`
  だが `derivedInG (N_G(P)) = ⊥` ゆえ `P ≤ derivedInG (N_G(P))` は成立しない。
- **D.1 は反証** (手検証): 可解奇数 CN 群 `F_{3⁶} ⋊ (C₇ ⋊ C₃)` (位数 3⁷·7)。正規初等アーベル核
  `K = F_{3⁶}` は全 Sylow-3 に含まれ、かつ `n₃ = 7 ≠ 1` (商 `C₇⋊C₃` の Sylow-3 が 7 個) ゆえ
  相異なる Sylow-3 が非自明に交わる。

**修正済**: 仮説を `IsCNGroup G` + 標準の `OddOrder.BG.IsMinimalSimpleOdd G` (BG §7-§16 で統一使用)
に置換 → D.1/D.2 は本物の定理文になった。vacuous な `CNTheoremReductionData`/`cnTheorem_reduction`
(構成要素は D.1 + D.2 + Gorenstein Thm 14.2.2 で、honest 化後は無内容な wrapper。no-wrapper 方針違反)
は**削除**。sorry 3 → 2 (D.1/D.2 のみ)、opaque フィールド 0、build green。下流 consumer は無し。

## ⚠ 2026-07-19 更新 — 「repo に不在」は解消済み (issue 9133)

**以下の「不在」記述は 2026-07-18 時点のもので、もう正しくない。**
Gorenstein §14.1 (手元の版では Ch.12 §1) は `OddOrder/GroupTheory/CNGroupStructure.lean` で構築中:

- **3-step 群の定義** `IsThreeStepGroup` — 逐語で形式化済。D.1 が実際に消費する 2 帰結
  (`oPiCore_pPrime_eq_bot` / `isPGroup_quotient` + `nontrivial_quotient`) は **sorry-free**。
- **Cor 14.1.6** = `oPiCore_isSylow_or_isThreeStepGroup` — **Thm 1.5 から sorry-free で導出済**。
- 残 sorry は **Thm 1.5 本体のみ** (`solvableCN_nilpotent_or_frobenius_or_threeStep`)。
  その step 1 / 2 / 3 は証明済で、残るのは「`A` の冪零性」と最終組み立て。

⟹ D.1 のブロッカーは「Gorenstein §14.1 全体」から **「Thm 1.5 の組み立て」**に縮小した。
最新の step 単位の状態は **issue 9133** が正本。

## 残: D.1 の証明に必要な Gorenstein §14.1 (⚠ 以下 2026-07-18 時点の記述、上記で更新済)

D.1 の証明 (mmd L5155-5178) が要するもの:

1. **Gorenstein Ch.14 §14.1 Cor 14.1.6** ← **不在・load-bearing**: 可解 `M` が `O_p(M) ≠ 1` かつ
   `P ∩ M ≠ O_p(M)` なら `M` は `p` に関する **3-step group**。
2. **3-step group の定義** (Gorenstein Ch.14 冒頭) ← **不在**。D.1 が使うのは 2 性質:
   `O_{p'}(M) = 1` と `N/O_{p,p'}(N)` が非自明 `p`-群。
3. BG Thm 6.2 (Glauberman `Z(J(P)) ⊴ M`) ← **repo にあり** (ZJ / `L(P)`+Thm B.4 代替)。
4. Focal Subgroup Thm (BG Thm 1.17) ← **mathlib にあり** (`Subgroup.commutator_inf_eq_focalSubgroup`)。

⟹ ブロッカーは **Gorenstein §14.1 (3-step 群の定義 + Cor 14.1.6) のみ**。D.2 は D.1 が入れば短い
(Focal Subgroup + 単純性から `G' = G`)。

### ⚠ Isaacs で代替可能か = **不可** (2026-07-18 検証済)

CLAUDE.md 方針「BG の **G** 引用はまず Isaacs に読み替え、Isaacs が欠く場合のみ Gorenstein」に従い
検証した結果、**これは Isaacs 代替不可**:
- Isaacs `finite-group-theory.mmd` に **`CN-group`/`CN group` の記述はゼロ**、`3-step group` もゼロ。
- Gorenstein の当該箇所は **§14.2「CN-groups of odd order」という CN 専用の構造論**であり、
  汎用 p-可解理論ではない ([[bg-gorenstein-reread-as-isaacs]] が言う「ほぼ既存被覆」の例外に当たる)。

### ただし「Gorenstein Ch.14 を全形式化する」必要は無い (scope 限定)

BG が実際に使うのは **Cor 14.1.6 の二者択一だけ**:
> 可解 `N` が `O_p(N) ≠ 1` なら、**`N` は p に関する 3-step 群** であるか、
> **`O_p(N)` が `N` の Sylow p-部分群** であるかのいずれか (Gorenstein 原文 7877 行の用法で確認)。

BG は対偶で使う: `P∩M ≠ O_p(M)` (= `O_p(M)` が Sylow でない) ⟹ M は 3-step 群。
そこから使う帰結も **2 つだけ**: `O_{p'}(M) = 1` と `M/O_{p,p'}(M)` が非自明 p-群。

その証明に要る下部構造 (Hall-Higman 1.2.3 = `Isaacs.Ch03.hall_higman_1_2_3`、`O_{p',p}` 系、
ZJ/Thompson subgroup = `Isaacs/Ch07_ThompsonSubgroup/**`) は **Isaacs 経由で repo に既に在る**。
また BG 自身が「§14.1 は G が奇数位数なら少し易しくなる」「G の Thm 7.6.1/10.2.1 は BG の
Thm 4.18(b)/3.7 で置換可」と注記している (mmd L5150)。

⟹ **やるべきは「CN 群に対する 3-step 二者択一 (Cor 14.1.6) とその 2 帰結」を、奇数位数の簡約と
既存 Isaacs 級機構を使って自前で証明すること**。CLAUDE.md の「BG が **G** を引いて証明を省く箇所は
Gorenstein 原文を読んで Lean に書き起こす」がまさにこれ。**「Gorenstein の章節を独立に全形式化する」
ことではない** (それは CLAUDE.md が明示的に禁じている)。`OddOrder/GroupTheory/` の新 leaf
(shared infra ゆえ着手前に 9000 claim)。

## ⚠ vacuous discharge は禁止

`feitThompson` が完成しているので honest な minimal-simple-CN 仮説は**空**であり、D.1/D.2 は
vacuously discharge **できてしまう**。しかしこれは:
1. **依存順序が逆** — CN 定理は FT の *入力* (BG p.153「actually needed in **FT**」)。
   `feitThompson` から導くと形式化対象の文献依存を逆走する。
2. [[scaffold-sorry-free-not-done]] の失敗モードそのもの (sorry-free・AxiomsCheck OK だが中身ゼロ)。
3. 付録の趣旨 (Feit-Hall-Thompson 証明の読解ガイド) を壊す。

⟹ **Gorenstein §14.1 を書いて正面から証明する**。それまで D.1/D.2 は honest statement + sorry で置く。

## 完了条件

Gorenstein §14.1 (3-step 群の定義 + Cor 14.1.6) を `OddOrder/GroupTheory/` に形式化し、
D.1 → D.2 を book strength・sorry-free・axiom-clean で証明。AppD の sorry が 0 に。survey 更新。

## 参照
- `OddOrder/BG/AppD_CNGroups.lean` (de-opacify 済)、mmd L5132-5199 (App.D)。
- Gorenstein `references/gorenstein/finite-groups.{pdf,mmd}` Ch.14 §14.1。
- [[bg-gorenstein-reread-as-isaacs]] (まず Isaacs/repo/mathlib を grep)。⚠ なお 9133 の実測で、
  当初「不在」とした前提のうち 3 件は誤りだった (Thm 5.3.5 / `C_G(F)≤F` の配置 / Thm 10.3.1(v))。
- issue 9133 (CN 3-step dichotomy) — **本 issue の残作業の正本**。
