---
id: 179
slug: bg-appc-remark-iv-glauberman-norton
title: "BG App.C Remark (IV): Glauberman–Norton の p ≤ 3 強化を形式化"
created: 2026-08-08
---

# BG App.C Remark (IV) — Glauberman–Norton の `p ≤ 3` 強化

## 位置づけ

3 冊逐条監査 (issue [0172](closed/0172-peterfalvi-full-formalization.md) /
[0176](closed/0176-isaacs-full-formalization.md) /
[0177](closed/0177-bg-full-formalization.md)、775 件) の完了後に**残っている着手可能な唯一の項目**。

CLAUDE.md の裁定 (2026-07-16): 文献引用のみで本文に証明が無い結果は「恒久対象外にせず
**低優先繰延**」。ユーザー指示 (2026-08-08) で解凍 — **Rem (IV) → Problem 1 の順**に進める
(Problem 1 = 未解決問題は別途ユーザーが ChatGPT に当てる)。

## 書籍の主張

**BG p.148, Appendix C, Preliminary Remark (IV)**:

> In [12], S. P. Norton and the second author have extended Theorem C to show that `p ≤ 3`.
> Example (II) above shows that `p` may be equal to 2. It is not yet known whether `p` may
> be equal to 3.

**BG p.149** が組合せ的な形に再述している (これが形式化のターゲット):

> The work mentioned in (IV) shows that whenever `p` and `q` are primes that satisfy (A)
> and `E = E⁻¹`, then `p ≤ 3`.

ここで (A) = `q ∤ p − 1` (BG Remark (I))、`E = { a ∈ 𝔽_{p^q} | N(a) = N(2−a) = 1 }`
(repo の `OddOrder.BG.AppC.NormSet.normSetE`)。

## 原論文 (2026-08-08 に取得・収録済)

`references/glauberman-norton/` (submodule commit `373aa0b`):
G. Glauberman, S. P. Norton, *On a combinatorial problem associated with the odd order
theorem*, Proc. Amer. Math. Soc. **119** (1993), 1089–1094,
[10.1090/S0002-9939-1993-1160299-X](https://doi.org/10.1090/S0002-9939-1993-1160299-X)。
PDF + pdftotext + 誌面ページ画像 (`pages/glauberman-norton-p1089.png` …) + `SOURCE.md`。

## 🚨 論文 Proposition 7 は literal には偽 — 条件が要る

論文の主結果 **Prop 7「`E = E⁻¹ ⟺ p ≤ 3`」は仮説なしの iff として述べられているが偽**。
`p` 奇 かつ `q = 2` のとき論文自身の **Lemma 5(a)** が `E = {1}` と言っており、`E = E⁻¹` は
自明に成立するのに `p > 3` でありうる。総当り計算で確認 (2026-08-08):

| `(p,q)` | `\|E\|` | `E = E⁻¹` | `q ∣ p−1` |
|---|---|---|---|
| (5,2) | 1 | **真** | 真 (⟹ (A) 不成立) |
| (7,2) | 1 | **真** | 真 |
| (11,2) | 1 | **真** | 真 |
| (5,3) | 7 | 偽 | 偽 |
| (3,5) | 61 | 真 (`p=3` ✓) | 偽 |
| (5,5) | 191 | 偽 | 偽 |

原因: Prop 7 の証明 (p.1092) 冒頭「By Lemma 5, we have (5) `E = E⁻¹` and `|E| ≥ 2`」が、
Lemma 5 が `|E| ≥ 2` を**与えない場合 (a)** を除外し損ねている。

**BG の再述 (p.149) は条件 (A) 付きなので正しい** — (A) の下では `q = 2 ⟹ p = 2` (奇素数
`p` は常に `2 ∣ p−1`) なので破れるケースがちょうど排除される。

⟹ **形式化の方針**: 必要十分な弱い仮説 **`q ≠ 2 ∨ p = 2`** (= Lemma 5 が `|E| ≥ 2` を
与える条件) で一般形を証明し、**BG の (A) 版はその系**として出す
(CLAUDE.md「特殊化債務はできる限り一般化する」)。

## 証明の構成 (論文 pp.1089–1093)

| 番号 | 主張 | repo 状況 |
|---|---|---|
| Lemma 1(a) | `E = E⁻¹`, `b ∈ E` ⟹ `1 + k(1−b) ∈ U` (∀ `k ∈ 𝔽_p`) | ✅ **既存** = `NormSet.normN_dSeq_eq_one` (`dSeq p q a k = (1−a)·k + 1`) |
| Lemma 1(b) | ⟹ `p ≤ q` | ✅ 既存 = `NormSet.lemmaC1` (= BG Lem C.1) |
| Lemma 2 | `p,q` 奇 ⟹ `\|E\| ≥ 2` | ✅ 既存 = `NormSet.lemmaC2` (= BG Lem C.2) |
| Lemma 4(a) | `p = 2` ⟹ `U = E = E⁻¹` | ⬜ 新規 (char 2 で `2−b = b`) |
| Lemma 4(b) | `p = 3` ⟹ `E = E⁻¹` | ⬜ 新規 (`2−c⁻¹ = c⁻¹(2c−1) = c⁻¹(2−c)`; char 3) |
| Lemma 5 | `¬(p 奇 ∧ q = 2)` ⟹ `\|E\| ≥ 2` | ⬜ 新規 (`p=2` は Lemma 4(a) + `\|U\| = 2^q−1 ≥ 2`; 奇奇は Lemma 2) |
| **Prop 6** | アフィン空間の条件 (C) + `p ≥ 5` + `\|S\| ≥ \|A\|/2` ⟹ `S = A` | ⬜ 新規 (**本体**) |
| **Prop 7** | `E = E⁻¹ ⟺ p ≤ 3` (要修正仮説) | ⬜ 新規 (Step 1–4) |

**条件 (C)**: `b ∈ A`, `x ∈ V`, `b−x, b, b+x ∈ S` ⟹ `∀ k ∈ 𝔽_p`, `b + k·x ∈ S`
(「`S` と 3 点で交わり 1 点が他 2 点の中点であるアフィン直線は `S` に含まれる」)。

### Prop 6 の証明 (論文 p.1091) — Lean 向けに整理した形

**直線の場合 (`A = 𝔽_p`)**: `T ⊆ ZMod p` が (C) を満たし `p < 2|T|` ⟹ `T = univ`。
1. `|T| > p/2 ≥ 2` から相異なる `c, b ∈ T` を取り、`v = b − c ≠ 0` で
   `T' = {k | c + k·v ∈ T}` に移す (アフィン全単射なので (C) と濃度が保たれ、`0, 1 ∈ T'`)。
2. `x ≠ 0` に対し `x, −x` が両方 `T'` に入ることはない
   (`(b,x) = (0,x)` で (C) ⟹ `∀k, k·x ∈ T'` ⟹ `T' = univ`)。
3. ⟹ `|T'| ≤ 1 + (p−1)/2`。`|T'| > p/2` と合わせて **等号**、すなわち `0 ∈ T'` かつ
   各対 `{k,−k}` からちょうど 1 つ。
4. `2 ∉ T'` (さもなくば `(b,x) = (1,1)` で `0,1,2 ∈ T'` ⟹ `T' = univ`) ⟹ `−2 ∈ T'`。
5. 対 `{4,−4}` (`p ≥ 5` ゆえ `4 ≠ 0`, `4 ≠ −4`) のちょうど一方が `T'`:
   - `−4 ∈ T'` ⟹ `(b,x) = (−2,2)`: `−4, −2, 0 ∈ T'` ⟹ `T' = univ` (2 は可逆)。
   - `4 ∈ T'` ⟹ `(b,x) = (1,3)`: `−2, 1, 4 ∈ T'` ⟹ `T' = univ` (3 は可逆)。
   ⚠ 論文は `p = 5` / `p = 7` / `p ≥ 11` を場合分けしているが、**上の形なら一様**
   (`p = 5` では `−4 = 1 ∈ T'` が第 1 分岐に直接当たる)。

**一般の場合**: `λ ∉ S` を取り `λ = 0` に平行移動。`V ∖ {0}` は 0 を通る穴あき直線
(= `(ZMod p)ˣ` のスカラー倍軌道、各サイズ `p−1`) に分割され、各直線 `L` は `0 ∉ S` ゆえ
`S ∩ L ≠ L`、直線の場合より `|S ∩ L| ≤ (p−1)/2`。
⟹ 二重数え上げ `Σ_{x≠0} |S ∩ line(x)| = (p−1)|S|` と `≤ (|V|−1)(p−1)/2` から
`2|S| ≤ |V| − 1 < |V|`、仮説に矛盾。
(⚠ 分割の Lean 実装は `MulAction` の軌道分解でなく**上の二重数え上げ**を使う方が軽い。)

### Prop 7 の証明 (論文 pp.1092–1093)

- **Step 1**: 任意のアフィン部分空間 `A ⊆ F` に対し `S = A ∩ U` は (C) を満たす
  (`b, b±x ∈ A ∩ U` ⟹ `c = b⁻¹(b−x) ∈ E` ⟹ Lemma 1(a) ⟹ `b + kx = b(1+kd) ∈ U`)。
- **Step 2**: `c ∈ E ∖ {1}`, `b = 1 − c ≠ 0` として
  `A_r = {1 + k₁b + ⋯ + k_r b^r}` は `|A_r| = p^r` (⟸ `b` の `𝔽_p` 上の次数は `q`)。
- **Step 3**: `A_r ⊆ U` を `r` について帰納。`c = 1 + b f(b)` が既約でない/次数が落ちるなら
  帰納法、既約なら次数 `r` の既約多項式が高々 `(p^r − p)/r` 個 ⟹
  `|A_r ∩ U| ≥ p^r − (p^r−p)/r > p^r/2` ⟹ Step 1 + Prop 6 で `A_r ⊆ U`。
- **Step 4**: `p^q = |A_q| ≤ |U| = (p^q−1)/(p−1) < p^q` で矛盾。

## 配置

新 leaf 2 枚 (mathlib 粒度 ≤1500 行、`OddOrder.lean` に同 commit で配線):

- `OddOrder/BG/AppC_AffineLineCondition.lean` — 条件 (C) と **Prop 6** (純アフィン組合せ論、
  `normSetE` に依存しない)。
- `OddOrder/BG/AppC_GlaubermanNorton.lean` — Lemma 4 / Lemma 5 / **Prop 7** + BG (A) 版の系。

namespace = `OddOrder.BG.AppC.NormSet` (既存 App.C に合わせる)。

## やること

- [x] **Lemma 4(a)(b) + Lemma 5** (`q ≠ 2 ∨ p = 2` 版) — `AppC_GlaubermanNorton.lean`
      (`normSetE_eq_setOf_ne_zero_of_two` / `normSetE_eq_inv_of_le_three` /
      `two_le_normSetE_ncard`)。4(b) は既存の `normSetE_eq_inv_of_p_eq_three` を再利用。
- [x] **Prop 6 直線の場合** — `eq_univ_of_condCLine_of_zero_one` + `eq_univ_of_condCLine`
      + `two_mul_ncard_le_of_condCLine_ne_univ`。⚠ 論文の `p = 5 / 7 / ≥11` の場合分けは不要で、
      `{4, −4}` の分岐に畳むと一様になる (`p = 5` では `−4 = 1`)。
- [x] **Prop 6 一般の場合** — `eq_univ_of_condC`。⚠ 分割 (商) を作らず
      `{(x,k) | x ≠ 0, k ≠ 0, k·x ∈ S}` の二重数え上げ (`Finset.sum_comm` + `card_nbij'`)。
- [x] **Prop 7 Step 1** — `condC_normOneSet` (任意のアフィン部分空間 `a₀ + W` について
      `A ∩ U` が (C) を満たす)。Lemma 1(a) の素体版 `normN_one_add_smul_one_sub` 込み。
- [x] **既約多項式の個数上界** — 新 leaf `OddOrder/Algebra/FiniteFieldIrreducibleCount.lean`:
      `mul_card_le : r * #ι ≤ p^r − p` (単項既約 `r` 次多項式の単射族)。
- [x] **Prop 7 Step 2** — `natDegree_minpoly_eq` (`b` の次数 = `q`) /
      `aeval_ne_zero_of_degree_lt` / `towerMap` / `towerSubmodule` / `towerMap_injective` /
      `card_towerSubmodule` (`|A_r| = p^r`)。
- [x] **Prop 7 Step 3** (帰納法本体) — `aeval_mem_normOneSet_of_not_irreducible` (易しい 2 分岐) /
      `towerSet_succ_subset_normOneSet` (既約分岐 = 個数上界 + Prop 6) /
      `towerSet_one_subset_normOneSet` (base = Lemma 1(a)) / `towerSet_subset_normOneSet`。
- [x] **Prop 7 Step 4 + 主定理 + BG (A) 版の系 + AxiomsCheck 登録** —
      `ncard_towerSet` / `normSetE_ne_inv_of_five_le` / `normSetE_eq_inv_iff` /
      `le_three_of_conditionA_of_normSetE_eq_inv`。AxiomsCheck に 9 件登録、全て axiom-clean。

## ✅ 完了 (2026-08-08)

BG p.149 の再述が Lean の定理として存在し axiom-clean:

```lean
theorem le_three_of_conditionA_of_normSetE_eq_inv [Fact p.Prime] (hq : q.Prime)
    (hA : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (hEinv : normSetE p q = (normSetE p q)⁻¹) : p ≤ 3
```

より一般の形 (必要十分な弱仮説) と `⟸` 方向も揃っている:

```lean
theorem normSetE_eq_inv_iff [Fact p.Prime] (hq : q.Prime) (h : q ≠ 2 ∨ p = 2) :
    normSetE p q = (normSetE p q)⁻¹ ↔ p ≤ 3
```

論文 Prop 7 の literal 版が偽であることは module docstring / AxiomsCheck の節 /
`references/glauberman-norton/SOURCE.md` の 3 箇所に明記した。

### 成果物

| ファイル | 内容 |
|---|---|
| `OddOrder/BG/AppC_AffineLineCondition.lean` | 条件 (C) と **Prop 6** (直線 + 一般次元) |
| `OddOrder/Algebra/FiniteFieldIrreducibleCount.lean` | `r · #{r 次単項既約} ≤ p^r − p` |
| `OddOrder/BG/AppC_GlaubermanNorton.lean` | Lemma 4 / Lemma 5 / **Prop 7** (Step 1–4) + BG (A) 版 |

### 副産物 (未使用仮説の除去による一般化 2 件)

* `NormSet.lemmaC2` から条件 (A) を削除 (書籍の Note 自身が「p, q が奇であればよい」と明記)
* `AppC.theoremC_abstract` から条件 (A) を削除 (3 つの step lemma がいずれも (A) を使わない)

### Step 3 の設計 (次セッションの入口)

**目標**: 仮説 `p ≥ 5`, `q` 素数, `E = E⁻¹`, `c₀ ∈ E ∖ {1}`, `b = 1 − c₀`,
`b ∉ 𝔽_p` の下で、`1 ≤ r ≤ q` について `A_r ⊆ U`。ここで
`A_r = {1 + w | w ∈ towerSubmodule p q b r}`。

**多項式による言い換え** (最初に証明する橋渡し補題):
`x ∈ A_r ↔ ∃ g : (ZMod p)[X], g.natDegree ≤ r ∧ g.coeff 0 = 1 ∧ x = aeval b g`。
(⟸ は `X * g.divX + C (g.coeff 0) = g` = `Polynomial.X_mul_divX_add` と
`degree_divX_lt` で `f = g.divX ∈ degreeLT r` を作る。)

**帰納段** (`2 ≤ r ≤ q`、`A_{r−1} ⊆ U` を仮定):
1. `x ∈ A_r` を `g` (次数 ≤ r, `g.coeff 0 = 1`) で表す。
2. `g.natDegree < r` なら `x ∈ A_{r−1} ⊆ U`。
3. `g.natDegree = r` かつ `g` 可約なら `g = g₁g₂` (両者 1 ≤ 次数 < r)。
   `g.coeff 0 = g₁.coeff 0 · g₂.coeff 0 = 1` なので定数項は両方非零 ⟹
   `g₁ ← g₁ * C (g₁.coeff 0)⁻¹`, `g₂ ← g₂ * C (g₁.coeff 0)` に正規化すると
   両方の定数項が 1。⟹ `aeval b gᵢ ∈ A_{r−1} ⊆ U` で `U` は積で閉じる。
4. 残りは `g` 既約 (次数ちょうど `r`)。**単項化** `h = g * C (g.leadingCoeff)⁻¹` は
   単項既約 `r` 次。`g ↦ h` は単射 (`g.coeff 0 = 1` から `g = h * C (h.coeff 0)⁻¹` で戻せる)。
   ⟹ `FiniteFieldCount.mul_card_le` で `r · |A_r ∖ U| ≤ p^r − p`。
5. `|A_r ∖ U| ≤ (p^r − p)/r ≤ (p^r − p)/2` ⟹
   `|A_r ∩ U| ≥ p^r − (p^r − p)/2 = (p^r + p)/2 > p^r/2 = |A_r|/2`。
6. Step 1 (`condC_normOneSet`) + **Prop 6** (`Affine.eq_univ_of_condC`, `p ≥ 5`) ⟹
   `A_r ∩ U = A_r`。

**Prop 6 への渡し方**: `V := ↥(towerSubmodule p q b r)`,
`S := {w : ↥V | 1 + (w : 𝔽_{p^q}) ∈ normOneSet p q}`。`Nat.card V = p^r`
(`card_towerSubmodule`) と `|S| = |A_r ∩ U|` を使う。

**Step 4**: `p^q = |A_q| ≤ |U| = (p^q − 1)/(p − 1) < p^q` で矛盾
(`normOneUnits_card` が `|U|` を与える)。⟹ `p ≥ 5` かつ `E = E⁻¹` は不可能。

### Step 3 で使う mathlib 資産 (2026-08-08 実測)

個数上界 `r · |I_r| ≤ p^r − p` は「各既約 `h` が `GF(p^r)` にちょうど `r` 個の根を持ち、
相異なる `h` の根集合は交わらない。根は `𝔽_p` の外」で出る。必要な部品は全部ある:

* **根の存在**: `FiniteField.nonempty_algHom_iff_finrank_dvd` — `AdjoinRoot h` (finrank `r`)
  から `GaloisField p r` (finrank `r`) への `AlgHom` があり、`AdjoinRoot.root h` の像が根。
* **分裂**: `GaloisField.lean:197` の `instance (priority := 100) … : IsGalois K K'`
  (有限体の任意の拡大は Galois) ⟹ `Normal` ⟹ `minpoly` が分裂。
* **重根なし**: `PerfectField.ofFinite` (有限体は完全) ⟹ `Irreducible.separable`。
* **根の個数**: `Polynomial.card_rootSet_eq_natDegree` (separable + splits ⟹ 根の個数 = 次数)。

⚠ 「単項既約 `r` 次多項式の集合」を Finset として扱うと Fintype 付けが面倒なので、
**`A_r ∖ U` の元 `c` から直接**その既約多項式・根集合を取り、`Finset.card_biUnion` で
`r · |A_r ∖ U| ≤ p^r − p` を出す方針 (`c ↦ h_c` の単射性は `b` の次数が `q ≥ r` から従う)。

## 完了条件

BG p.149 の再述が Lean の定理として存在し axiom-clean:

```
theorem …  (hq : q.Prime) (hA : ¬ q ∣ (p - 1))
    (hEinv : normSetE p q = (normSetE p q)⁻¹) : p ≤ 3
```

かつ、より一般の `q ≠ 2 ∨ p = 2` 版と `⟸` 方向 (`p ≤ 3 ⟹ E = E⁻¹`) も揃っていること。
論文 Prop 7 の literal 版が偽であることは docstring に明記する。

## 参照

- 原論文: `references/glauberman-norton/` (`SOURCE.md` に書誌・OCR 事情・反例表)
- BG: `references/bg/local-analysis.pdf` (Rem (IV) = p.148、再述 = p.149、Problem 1 = p.152)
- repo の App.C: `OddOrder/BG/AppC_NormSet*.lean` (`normSetE` / `lemmaC1` / `lemmaC2`)
- 次項: **BG App.C Problem 1** (「Theorem C で `p = 3` はありうるか」= 未解決問題)
