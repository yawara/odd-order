---
id: 173
slug: peterfalvi-65-generalize-nilpotent
title: "Peterfalvi (6.5) を書籍の K/M 冪零へ一般化 (現状は K 冪零)"
created: 2026-08-07
---

# Peterfalvi (6.5) を書籍の K/M 冪零へ一般化 (現状は K 冪零)

## 背景

issue [0172](0172-peterfalvi-full-formalization.md) の §6 逐条監査 (2026-08-07) で確定した
**特殊化債務**。

### 書籍 (p. 31、`references/peterfalvi/pages/peterfalvi-p031.png`)

**(6.4) Hypothesis.** (a) Hypothesis (6.1) が成立し `|L|` は奇。
(b) `M` を `K` に含まれる `L` の正規部分群で **`K/M` が冪零**なものとする。
(c) `H₁/M` を `K/M` の交換子群とし、`L/H₁` は核 `K/H₁` の Frobenius 群と仮定する。

**(6.5)** Hypothesis (6.4) を仮定し `𝒮(M)` が **coherent でない**とする。
(a) `K/H₁` は `L` の chief factor で `|K:H₁| ≤ 4|L:K|² + 1`。
(b) ある素数 `p` が在って **`K/M` は非可換 `p`-群**。
(c) `|L:K|` は `p − 1` を割らない。

### repo の現状 (`OddOrder/Peterfalvi/S08_SixFiveGeneral.lean`)

| 書籍 | repo |
|---|---|
| (6.5)(a) | `relIndex_le_of_not_isCoherent` + `isChiefFactor_of_not_isCoherent` |
| (6.5)(b) | `exists_prime_isPGroup_of_not_isCoherent` |
| (6.5)(c) | `not_dvd_sub_one_of_not_isCoherent` |

**⚠ これらは `K` 自体の冪零性を要求する**。書籍 (6.4)(b) が要求するのは `K/M` の冪零性で、
`M ≠ 1` では真に狭い。`AxiomsCheck.lean:4141` が既に自認している:

> ⚠ `K` nilpotent where the book has `K/M` nilpotent (inherited from `six_three_of_imageData`;
> the two agree at `M = 1`, the case (6.6) uses).

### 影響範囲

- **(6.6) は無傷** — 書籍自身が「Hypothesis (6.4) holds **with `M = 1`**」と置くので
  `K/M = K` となり両者一致する。
- **現時点で (6.5) の下流消費点はゼロ** (grep: `S08_SixFiveGeneral` と `AxiomsCheck` 以外に無い)。
  ⚠ ただし CLAUDE.md より **consumer 0 は繰延の理由にならない** —
  「特殊化債務はできる限り一般化する」「deferred-payoff だから deprioritize は誤り」。

## 🔎 出所を特定 (2026-08-07、書籍 p.30 と突合)

**債務は (6.5) でなく (6.3) 本体に在る。**

**書籍 (6.3) Theorem** (p.30): Hypothesis (6.1) を仮定。`M ⊆ H₁ ⊆ H ⊆ K` を `L` の正規部分群とし、
さらに **(a) `H/M` が冪零** / (b) `𝒮(H₁)` が coherent / (c) `|H:H₁| > 4|L:K|²+1` を仮定。
Then `𝒮(M)` is coherent.

**repo** `S08_SixTwoThreeFromImageFamilies.six_three_of_imageData:447`:
```
{H M H₁ : Subgroup ↥L} [Group.IsNilpotent ↥H] [M.Normal] [H₁.Normal]
```
⟹ **`H` 自体の冪零性**を要求している (書籍は `H/M`)。`M ≠ 1` では真に狭い。
(6.5) はこれを `H = K` で適用するので `K` 冪零を引き継ぐ。

### 冪零性が使われる箇所は 1 つだけ

書籍 (6.3) の証明 (p.30 末尾):

> Since `H/M` is nilpotent, we have `(A/B) ∩ Z(H/B) ≠ 1` and, by the maximality of `B`,
> `A/B ⊆ Z(H/B)`.

`M ⊆ B ⊊ A ⊆ H₁` に対する **「冪零群の非自明な正規部分群は中心と交わる」**の 1 ステップ。
`M ⊆ B` なので `H/B` は `H/M` の商 ⟹ 冪零。⟹ **書籍の弱い仮説で十分**。
`H` 冪零からも `H/B` 冪零は出るので、repo は同じステップを**より強い仮説**で通しているだけ。

⟹ **一般化は安価な見込み**: `[Group.IsNilpotent ↥H]` を `Group.IsNilpotent (↥H ⧸ M.subgroupOf H)`
相当に置換し、`M ≤ B` から `H/B` の冪零性を導く。

## やること

- [x] 債務の出所を特定 → **(6.3) 本体** (`six_three_of_imageData` の `[Group.IsNilpotent ↥H]`)。
      冪零性の実使用は「`H/B` の非自明正規部分群が中心と交わる」1 ステップのみ (上記)。
- [ ] repo 側の証明で冪零性インスタンスが実際にどこで消費されているか確認する
      (`six_three_of_six_two_oracle` の中。⚠「threading されている」≠「依存している」—
      memory `generalize-by-measuring-which-carrier-fields-are-used`)。
- [ ] `H/M` 冪零版を証明する (`Group.IsNilpotent (↥H ⧸ M.subgroupOf H)` を仮説に)。
- [ ] **旧 `K` 冪零版をその特殊化に置換**し、コンパイラに同値性を検証させる
      (§1 の (1.6)(b) と同じ標準処方。linter の unused 仮説は「最初から不要だった」の合図)。
- [ ] `AxiomsCheck.lean:4141` の ⚠ 注記を更新。

## 完了条件

(6.3)(a) が書籍どおり `H/M` 冪零で述べられ、(6.5) がそれを継いで `K/M` 冪零になり、旧 `K` 冪零版がその特殊化として
繋がっている。フルビルド green + `bin/check-warnings --strict` + sorry 非退行 + axiom-clean。

## 参照

- census note: [`notes/peterfalvi/full_formalization_census_2026_08_07.md`](../notes/peterfalvi/full_formalization_census_2026_08_07.md) §6 表
- 書籍ページ: `references/peterfalvi/pages/peterfalvi-p031.png`
- 自認箇所: `OddOrder/AxiomsCheck.lean:4141`
