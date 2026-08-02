---
id: 170
slug: psu3-c1-first-or-second-case
title: "(C1) の場合分けを組む — `V ≠ 1` なら Theorem A が無条件で出る"
created: 2026-08-02
---

# (C1) の場合分け — 第一の場合 (Ch. II) と第二の場合 (Ch. III/IV) を合流させる

## 背景

[issue 0169](closed/0169-psu3-section-two-free-d.md) で

```
SecondCaseHypothesis.nonempty_theoremAConclusion
  : (sc : SecondCaseHypothesis G Ω) → TheoremAInductionBelow G Ω
    → Nonempty (TheoremAConclusion G Ω)
```

が仮説ゼロ・axiom-clean で通った。しかし **`SecondCaseHypothesis` は repo のどこでも
構成されていない** (2026-08-02 実測: `StructureOfH/` と `PSU3TheoremADichotomy.lean`
以外に出現しない)。ここを繋ぐのが本 issue。

## 書籍 (p. 115, Ch. III §1 冒頭)

> Suppose that `V = 1`. … Thus `G` is a Zassenhaus group. By [HB], Chapter XI,
> Theorem 11.16, `G` is isomorphic to `PSL(2,q)` or to `Sz(q)`, and the conclusion of
> Theorem A is valid. **Taking Theorem B into account**, we will then assume from this
> point on that
>
> **(C1)** The subgroup `V` is non-trivial; `C_G(P)` has 2-rank `≥ 2` for every subgroup
> `P` of `V` which is of prime order.

⟹ (C1) は 2 本の否定を消費して立つ:

1. `V = 1` — **Zassenhaus 群の分類 ([HB] XI.11.16) の文献引用**。書籍が証明を書いて
   いない箇所なので低優先繰延 (CLAUDE.md の方針どおり恒久対象外にはしない)。
2. ある素数位数 `P ≤ V` で `C_G(P)` の 2-rank が `≤ 1` — **これは第一の場合**で、
   repo の `FirstCaseHypothesis` がまさにその仮説
   (`twoRank_centralizer_le_one`)、`FirstCaseHypothesis.theoremB` が結論を出す。

## やること

- [x] **完了 (2026-08-02)** `V ≠ ⊥` から `Nonempty (TheoremAConclusion G Ω)` を無条件で出す:

```
by_cases hall : ∀ P ≤ V, ∀ p, p.Prime → Nat.card P = p →
                  ∃ E : Subgroup ↥(C_G(P)), Nat.card E = 4 ∧ ∀ x ∈ E, x^2 = 1
· -- (C1) が立つ ⟹ SecondCaseHypothesis ⟹ 0169 の定理
· -- ある P で 2-rank ≤ 1 ⟹ FirstCaseHypothesis ⟹ theoremB
```

### 部品

| 要るもの | 出どころ |
|---|---|
| `FirstCaseHypothesis` の `P`/`p`/`p_prime`/`P_le_V`/`card_P` | `exists_le_card_eq_prime V_ne_bot` |
| `twoRank_centralizer_le_one` | `hall` の否定 (下記の橋渡しが要る) |
| `theoremB` | `FirstCase/TheoremB.lean` (既存) |
| `SecondCaseHypothesis` | `V_ne_bot` + `hall` |

### ⚠ 2 つの 2-rank 条件の橋渡し

* `SecondCaseHypothesis.twoRank_centralizer_ge_two`:
  `∃ E : Subgroup ↥(Subgroup.centralizer (P : Set G)), Nat.card E = 4 ∧ ∀ x ∈ E, x^2 = 1`
* `FirstCaseHypothesis.twoRank_centralizer_le_one`:
  `∀ E : Subgroup G, E ≤ Subgroup.centralizer (P : Set G) → (∀ x ∈ E, x^2 = 1) →
   Nat.card E ≤ 2`

型が違う (`Subgroup ↥C` vs `Subgroup G` + `≤ C`) ので `map (C.subtype)` / `subgroupOf`
で往復する。さらに「位数 `> 2` の指数 2 の群から位数 4 の部分群を取る」
(= `4 = 2² ∣ |E|` に `Sylow.exists_subgroup_card_pow_prime`) が要る。

## 完了条件

```
Hypothesis.nonempty_theoremAConclusion_of_V_ne_bot
  : hyp.V ≠ ⊥ → TheoremAInductionBelow G Ω → Nonempty (TheoremAConclusion G Ω)
```
が sorry-free・axiom-clean。残るのは `V = 1` の Zassenhaus 分類 (文献引用) のみ。

## 参照

* 書籍 = `references/peterfalvi/pdftotext/05.5_pp_115_121_The_Structure_of_H.txt` 冒頭
* 第一の場合 = `OddOrder/Peterfalvi/Appendices/Suzuki/FirstCase/`
* 第二の場合 = `OddOrder/Peterfalvi/Appendices/Suzuki/StructureOfH/` +
  `PSU3TheoremADichotomy.lean`

## ✅ 完了 (2026-08-02) — ただし Ch. II 由来の `sorry` を継承する

新 leaf [`TheoremANonTrivialV.lean`](../OddOrder/Peterfalvi/Appendices/Suzuki/TheoremANonTrivialV.lean)。

```
Hypothesis.nonempty_theoremAConclusion_of_V_ne_bot
  : hyp.V ≠ ⊥ → TheoremAInductionBelow G Ω → Nonempty (TheoremAConclusion G Ω)
```

* `twoRank_centralizer_le_one_of_not_exists` — 2 つの綴りの橋渡し。位数 `> 2` の
  指数 2 の群 `E ≤ C_G(P)` は `|E| = 2ⁿ` (`n ≥ 2`) なので `Sylow.exists_subgroup_card_pow_prime`
  で位数 4 の部分群が取れ、`Subgroup.inclusion hEC` で `C_G(P)` の中へ移す。**axiom-clean**。
* 場合分けは `by_cases` を**存在命題側**に置いて `push_neg` を避けた
  (`push_neg` は deprecated で `--strict` gate に掛かる)。

### ⚠ 実測: `sorryAx` を継承する (新規混入ではない)

`#print axioms` の実測 (2026-08-02):

| 定理 | axioms |
|---|---|
| `SecondCaseHypothesis.nonempty_theoremAConclusion` (Ch. III/IV) | clean |
| `twoRank_centralizer_le_one_of_not_exists` | clean |
| **`FirstCaseHypothesis.theoremB` (Ch. II)** | **`sorryAx`** |
| `nonempty_theoremAConclusion_of_V_ne_bot` | **`sorryAx`** |

経路 = `theoremB` → `NearFields.rankOne_affine_nearField` →
`RankOneHypothesis.brauerSuzuki` → **`brauerSuzuki_quaternionSylow_q8`**
(`RankOneAffineModel.lean:299`) = Brauer–Suzuki の `Q₈` の場合
= **[issue 0147](0147-q8-modular-char-theory-frozen.md)** (modular character theory を要する
長期プロジェクト、2026-07-25 解凍済)。

⟹ **本 issue が入れた sorry ではなく、Ch. II が前から持っていたもの**。よって
`nonempty_theoremAConclusion_of_V_ne_bot` は AxiomsCheck に**登録しない** (意図的)。
これが埋まれば `V ≠ 1` の Theorem A が完全に axiom-clean になる。

## 残り

1. **issue 0147** (Brauer–Suzuki `Q₈`) — Ch. II の唯一の sorry。
2. `V = 1` の Zassenhaus 群分類 ([HB] XI.11.16) — 書籍が文献引用で済ませる箇所、低優先繰延。

## ✅✅ 続き (同日): Theorem A の帰納法まで閉じた

`TheoremAZassenhausCase.lean`:

```
theoremA : ZassenhausClassification →
  ∀ {G Ω} [Group G] [MulAction G Ω] [Finite G], Hypothesis G Ω →
    Nonempty (TheoremAConclusion G Ω)
```

書籍 p.115 の `V = 1` 段落。**文献引用は Zassenhaus 群の分類 ([HB] XI.11.16) だけ**で、
「`G` が Zassenhaus 群」の 2 節は形式化済 (どちらも axiom-clean):

| 定理 | 内容 |
|---|---|
| `eq_one_of_three_fixedPoints_of_V_eq_bot` | 3 点固定化群が自明 (2-推移性で基点対へ運び Prop 6(c)) |
| `natCard_normal_ne_natCard_Omega` | 正規部分群は位数 `|Ω|` を持てない (⟹ 正則な正規部分群なし) |

分類定理は `def ZassenhausClassification : Prop` として**明示の引数**にした
(axiom でも sorry でもない ⟹ 形式化の境界が型に出る)。

⟹ **issue 0170 クローズ**。Suzuki Theorem A に残るのは
1. `ZassenhausClassification` ([HB] XI.11.16 の形式化) — 書籍が引用で済ませる箇所、低優先繰延
2. issue 0147 (Brauer–Suzuki `Q₈`) — Ch. II の唯一の `sorry`
の 2 つだけ。
