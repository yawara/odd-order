---
id: 169
slug: psu3-section-two-free-d
title: "Ch. IV §2 の仮説を書籍どおり「D が (Q/Q₀)^# に固定点なく作用」へ一般化 (現状は V = W)"
created: 2026-08-02
---

# Ch. IV §2 の仮説を書籍どおり "D acts without fixed points on `(Q/Q₀)^#`" へ

## 背景 — Theorem A の最上位組立てがここで止まる

Ch. IV は 2026-08-02 に**両分岐とも `TheoremAConclusion` に届いた**:

* `V = W` 側: `Hypothesis.nonempty_theoremAConclusion_of_isStandardModel_of_closing`
  (`PSU3PropositionModel.lean`)
* `V ≠ W` 側: `Hypothesis.SectionFourSetup.nonempty_theoremAConclusion`
  (`PSU3SectionFourCorollaryOne.lean`)

残るのは **Ch. III §1 Proposition の case (c) からこの 2 分岐へ振り分ける**ところ。
ここで書籍と repo の仮説がずれていて塞がっている。

## 書籍の二分法 vs repo の二分法

書籍 p.132 (§4 冒頭):

> By the proposition of §2 and Corollary 1 to the proposition of §3, to complete the
> proof of Theorem A, we may assume that `D` has a subgroup `P` of prime order `p` such
> that `C_{Q/Q₀}(P) ≠ 1`.

書籍 p.129 (§2 の閉じ Proposition):

> **Proposition.** Suppose that `D` acts without fixed points on `(Q/Q₀)^#`. Then there
> exists an index `i`, `1 ≤ i ≤ n`, such that `f(ω) = (ω⁻¹)^ζ` and `h(ω) ∈ W` for
> `ω = ω_i`.

⟹ **書籍の二分法は「`D` が `(Q/Q₀)^#` 上 fixed-point-free か否か」**。
repo は §2/§3 の全体を **`hVW : V = W`** で書いている (40 宣言)。

### `V = W` は書籍より真に強い (2026-08-02 の分析)

* `V = W ⟹ D = K W ⟹ D` fpf: repo に在る
  (`exists_mem_K_mem_W_mul` → `eq_one_of_conj_eq_mul_Q0_of_mem_D`)。
* **逆は成り立たない**。`W ⊴ V` で `V/W ↪ Gal(𝔽_q/𝔽_2)` (Ch. I §2 Prop 3)。
  `v ∈ V ∖ W` は `Q/Q₀ ≅ E` に `x ↦ c·x^τ` と半線形に作用し、固定点が在るのは
  `N_τ(c) = 1` のときだけ (Hilbert 90)。`N_τ(c)` は `v^{ord τ}` がスカラーとして
  作用する値なので、`v^{ord τ} ∈ W ∖ {1}` なら `N_τ(c) ≠ 1` で**固定点なし**。
  ⟹ 例: `V` 巡回 9 次・`W` 位数 3 は `V ≠ W` かつ `D` fpf。
* 同じ例が「`V ≠ W ⟹ 素数位数の P ≤ V` で `C_{Q/Q₀}(P) ≠ 1`」も潰す
  (`V = ℤ/9`, `W = ℤ/3` では位数 3 の部分群は `W` ただ 1 つで、それは fpf)。

⟹ **`V = W` / `V ≠ W` の二分法では case (c) を尽くせない**。書籍どおり
fpf で切るしかなく、そのためには §2/§3 の `hVW` を fpf に一般化する必要がある。

## やること

- [ ] (1) fpf を述語として導入する (`Hypothesis.FreeD` 仮称):
      `∀ ω c y, ω ∈ Q → ω ∉ Q0 → c ∈ D → y ∈ Q0 → c⁻¹ ω c = ω y → c = 1`。
      `eq_one_of_conj_eq_mul_Q0_of_mem_D` はこの述語の**証明**から
      「`V = W ⟹ FreeD`」という補題へ格下げする。
- [ ] (2) `hVW` を `FreeD` に置換していく (40 宣言)。大半は
      `eq_one_of_conj_eq_mul_Q0_of_mem_D` 経由なので機械的。
- [ ] (3) ⚠ **機械的でない 4 箇所** = `PSU3OrbitCount.lean` の数え上げ
      (`stepEight` / `ncard_eq_card_W_sub_one_of_f_eq_conj_self` 系、
      L466/468/525/603)。repo は `[D : K] = |V|` (`index_K_subgroupOf_D`) を
      `hVW` で `|W|` に読み替えているが、**書籍 (7)(8) はそう論じていない**:

      > (8) The number of elements `x ∈ Q₀` such that `f(ω₁x)` is in the orbit of `ω̄₁`
      > under `KW` is `m` if `i > 1` and `m − 1` if `i = 1`.
      > Proof. … `m_i ≤ m` for `i > 1` by (7) …

      書籍は `a ∈ K W` (対象が **`KW`-軌道**) から `|K W / K| = |W|` で抑える。
      ⟹ `D/K` でなく `KW/K` で数え直すのが正しい一般化。
- [ ] (4) case (c) → Ch. IV の振り分けを組む:
      `by_cases` on 「∃ 素数位数 `P ≤ D` with `C_{Q/Q₀}(P) ≠ 1`」
      * yes → `P` を `D`-共役で `V` へ入れ (書籍「`P` has three fixed points on `Ω`
        and so is conjugate in `D` to a subgroup of `V`」)、`P ∩ W = 1` は
        `eq_one_of_conj_eq_mul_Q0_of_mem_W` (`W` は常に fpf) ⟹ `SectionFourSetup`
        ⟹ `SectionFourSetup.nonempty_theoremAConclusion`
      * no → `FreeD` ⟹ §2 ⟹ `nonempty_theoremAConclusion_of_isStandardModel_of_closing`
        の `hVW`-free 版

## 準備として済んでいること (2026-08-02)

* `stepThree_model` から `hVW` を除去済 (`hhW₀ : h ω₀ ∈ W` を直接取る形へ)。
* Hilbert 90 の `C_Q(X) ⊄ Q₀` 系 (`exists_field_realization_K` /
  `exists_mem_inf_centralizer_not_mem_Q0(_of_orbit,_of_card_cube)`) から
  `hW : W = ⊥` を除去し `¬ X ≤ W` へ一般化済 — `V ≠ W` の設定でも使える。
  補助 `notMem_of_not_le_of_prime_card` (`HilbertNinetyOnQ.lean`)。

## 完了条件

`SecondCaseHypothesis` の case (c) から `Nonempty (TheoremAConclusion G Ω)` が
sorry-free で出る。⟹ Ch. II (`theoremB`) + Ch. III case (a)(b)
(`theoremAConclusion_of_caseA/B`) と合わせて、`V ≠ 1` の Theorem A が閉じる
(`V = 1` の Zassenhaus 分類は書籍が文献引用で済ませる箇所なので別扱い)。

## 参照

* 書籍 = `references/peterfalvi/pdftotext/05.6_pp_122_134_Characterization_of_PSU3_q.txt`
  (§2 Proposition = p.129、§4 冒頭 = p.132)
* Ch. IV 到達状態 = [`notes/peterfalvi/partII_ch4_section4_state.md`](../notes/peterfalvi/partII_ch4_section4_state.md)
* 親 issue = [0168](0168-pf-part2-ch4-psu3.md)
