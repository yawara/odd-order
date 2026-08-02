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
- [x] (2) **完了 (2026-08-02)**。§2 の閉じ Proposition `exists_f_eq_conj_inv` と
      Corollary 1 経路 `nonempty_theoremAConclusion_of_isStandardModel_of_closing` が
      `FreeD` だけで走る。`PSU3BarOrbit.lean` / `PSU3StepTwenty.lean` /
      `PSU3StepFifteen.lean` は `hVW` ゼロ。残る `hVW` は Corollary 2 側 (正当) と
      旧 `D`-版の遺構のみ。
- [x] (3) **数え上げは既に解決済だった** (2026-08-02 に実測して訂正)。
      `PSU3OrbitCount.lean` の `stepEight` /
      `ncard_eq_card_W_sub_one_of_f_eq_conj_self` は `[D : K] = |V|`
      (`index_K_subgroupOf_D`) を `hVW` で `|W|` に読み替えているが、
      **`PSU3StepEightKW.lean` が書籍どおりの `KW`-版を既に持っている**
      (ファイル冒頭が「§3 が `V = W` を持ち回る羽目になっていた、それは §4 が
      持たない仮説」と明記):

      | `hVW` 版 (`PSU3OrbitCount`) | `hVW`-free 版 (`PSU3StepEightKW`) |
      |---|---|
      | `ncard_fiber_orbitOfF_le` | `ncard_fiber_orbitOfF_le_W` |
      | `ncard_fiber_orbitOfF_base_le` | `ncard_fiber_orbitOfF_base_le_W` |
      | `stepEight` | `stepEight_of_KW` |
      | `exists_mem_Q0_orbitOfF_eq` | `exists_mem_Q0_orbitOfF_eq_of_KW` |

      残るのは `ncard_eq_card_W_sub_one_of_f_eq_conj_self` (等式版) の `_of_KW`
      変種を作ること — `≤` は既に `ncard_le_card_W_sub_one_of_f_eq_conj_self`
      (hVW-free)、`≥` は `stepEight_of_KW` から出る。
      消費点は `PSU3StepFifteen.lean:365`。
      ⟹ **(2) の置換はほぼ完全に機械的**。
- [ ] (4) case (c) → Ch. IV の振り分けを組む:
      `by_cases` on 「∃ 素数位数 `P ≤ D` with `C_{Q/Q₀}(P) ≠ 1`」
      * yes → `P` を `D`-共役で `V` へ入れ (書籍「`P` has three fixed points on `Ω`
        and so is conjugate in `D` to a subgroup of `V`」)、`P ∩ W = 1` は
        `eq_one_of_conj_eq_mul_Q0_of_mem_W` (`W` は常に fpf) ⟹ `SectionFourSetup`
        ⟹ `SectionFourSetup.nonempty_theoremAConclusion`
      * no → `FreeD` ⟹ §2 ⟹ `nonempty_theoremAConclusion_of_isStandardModel_of_closing`
        の `hVW`-free 版

## 進捗 (2026-08-02)

### ✅ 済: (1) `FreeD` 導入、(3) 数え上げ、§2 (8)(9)(15)

| 追加/変更 | 場所 |
|---|---|
| `FreeD` / `freeD_of_V_eq_W` | `PSU3OrbitCount.lean` |
| `ncard_eq_card_W_sub_one_of_f_eq_conj_self_of_KW` | `PSU3StepEightKW.lean` |
| `exists_witness_mem_W_of_KW` (step (9) の witness) | 同上 |
| `stepNine_of_KW` | 同上 |
| `stepElevenSeq_mem_KW` (書籍の `d_i ∈ KW`) / `stepElevenSeq_fst_mem_orbitSet_KW` | `PSU3Sequence.lean` |
| `PSU3StepFifteen.lean` 4 定理を `hVW` → `FreeD` | — |

⚠ 副産物: `stepFifteen_stop_d_eq_inv` / `stepFifteen_length_eq` /
`stepElevenSeq_fst_injOn` は `M`・`hZ`・`hmu` が最初から不要だった (削除)。
`stepFifteen_exhaust` は `KW`-形の集合で述べ直した (書籍の言い方そのもの)。

### ✅ 済 (続き): §2 (18) と Frobenius 補群

* **(18) は交換性を使わない** (書籍 p.127 のページ画像で確認)。repo は
  `commute_h_zeta` (= `D = KW`) 経由だったが、`N + 2 = orderOf ζ` から
  `ζ^N = ζ^{-2}`、(H4) と突き合わせて `g^N h(ω) = ζ h(ω)⁻¹ ζ` (`g := h(ω)ζ⁻¹`)、
  `g` を 2 つ掛けて `1`。⟹ `stepEighteen` の仮説は `FreeD` のみ
  (`M`/`hZ`/`hmu`/`hWcard` も不要だった)。
* **`FreeD ⟹ IsZGroup D`** (`PSU3FrobeniusD.lean`) — 書籍の Huppert V.8.15 引用。
  `FreeD` = `IsFrobeniusAction D (Q ⧸ Z(Q))` そのもので、Isaacs Cor 6.17 に食わせる。
* **一般補題** `mem_of_pow_card_eq_one_of_isZGroup`
  (`OddOrder/GroupTheory/ZGroupNormalCyclic.lean`):
  `IsZGroup D` + `W ⊴ D` + `IsCyclic W` + `g^{|W|} = 1` ⟹ `g ∈ W`。
  書籍の `p`-成分論法。`W` が巡回なので `W_p ⊴ D` (`normal_of_le_of_isCyclic_normal`)
  ⟹ **あらゆる** Sylow に含まれる (`IsPGroup.le_sylow_of_normal`) ので、書籍の
  `|P ∩ W| = m_p` の同定は不要。`g` の `p`-分解は `exists_isPiElement_mul` を
  `orderOf g` の強帰納法で。補助 `le_of_card_dvd_of_isCyclic` を
  `CyclicSubgroupUniqueness.lean` に追加。

### 旧記述 (解決済): §2 (18) / `h(ω) ∈ W` — 書籍は **Frobenius 補群**で通す

`PSU3StepEighteen.lean` の `commute_h_zeta` / `h_mem_W` は
`exists_mem_K_mem_W_mul hVW` (= `D = K W`) で `h(ω) = κ v` と分解している。
これは `V = W` そのものなので `FreeD` では出ない。

**書籍 p.129 の Proposition 証明はまったく別の筋**:

> By [H], Kapitel V, Satz 8.15, the Sylow subgroups of `D` are cyclic. Then (18)
> implies that, if `ω` is one of the elements `ω_i`, then `h(ω) ∈ W`. In fact, if `p`
> is a prime number, then, if `x` is the `p`-component of `h(ω)ζ⁻¹` and `P` is a Sylow
> `p`-subgroup of `D` containing `x`, `x^{m_p} = 1` and `|P ∩ W| = m_p` since `W ⊴ D`,
> whence `x ∈ W`.

* 「`D` の Sylow が巡回」は **`D` が `(Q/Q₀)^#` に固定点なく作用する** (= `FreeD`)
  ことから来る (Frobenius 補群; `D` は奇数位数なので quaternion 分岐は消える)。
  ⟹ **`FreeD` がここで本質的に効く**。
* (18) `(h(ω)ζ⁻¹)^m = 1` 自体は repo に在る (`stepEighteen`) が、
  その証明が `commute_h_zeta` 経由で `hVW` を使っている。書籍の (18) 証明は
  (13)(16)+(H6)+(1) の帰納なので、まず commutation を経由しない形に直すか、
  Frobenius 側から `h(ω) ∈ W` を直接出すかの二択。

**✅ 完了 (2026-08-02)**: `h_mem_W_of_frobeniusD` (`PSU3StepEighteen.lean`) が通った。
`W ⊴ D` は `normal_W_subgroupOf_D` (Ch. I Prop 5 の `W = D ∩ C(H∩I)` 経由 —
`W = D ∩ C(Q₀)` の方は §4 側にあって上流から使えない)。
⚠ **命名衝突**: `PSU3SectionThree.h_mem_W_of_freeD` が既存 (そこでの "free D" は
仮説 `V = W` の綴り) なので、新しい方は `h_mem_W_of_frobeniusD`。

### 残り = §2 の閉じ Proposition まで `FreeD` を通す

`PSU3StepTwenty.lean` / `PSU3BarOrbit.lean` の `hVW` (12 宣言)。実測した内訳:

* **`FreeD` で済むもの** — `eq_one_of_conj_eq_mul_Q0_of_mem_D` 経由
  (`PSU3StepTwenty:544`、`PSU3BarOrbit:207` ほか)。機械的。
* **`D = K W` を使うもの** — `exists_mem_K_conj_of_mem_D` (`PSU3StepTwenty:230`) が
  `exists_mem_K_mem_W_mul hVW` で共役子 `c ∈ D` を `κ v` に割る。
  ⟹ step (9) と同じ処方: **仮説を `KW` の形で取る**
  (`hrel : f (ω₁ z) = (κ₀ v)⁻¹ (ω₂ w) (κ₀ v)`, `κ₀ ∈ K`, `v ∈ W`)。

  **⚠ ただし呼び出し側の連鎖が深い** (2026-08-02 実測): `stepTwenty_snd` (318) /
  `stepTwenty_of_mem_D` (390) の呼び出し元は `PSU3BarOrbit.lean` で、そこは
  **`dOrbitRel` (= `D`-軌道)** で組まれている (`barOrbitRel_of_stepNine`,
  `dOrbitRel_mul_of_barOrbitRel`, `y_eq_of_barOrbitRel`, …)。
  一方**書籍 §2 の (7)–(9)・(19)–(20) はすべて `KW`-軌道**
  (「`f(ω₁(0,x₁)) = (ω₂(0,x₂))^k` with `k ∈ K`」)。`D`-軌道で書けているのは
  `D = KW` (= `V = W`) を仮定しているから。

  ⟹ **`KW` を部分群として導入して `PSU3StepTwenty` は全部 `FreeD`/`KW` 化済**
  (`KW` / `conj_t_mem_KW` / `KW_eq_D_of_V_eq_W`、`exists_mem_K_conj_of_mem_KW` /
  `stepTwenty_of_mem_KW` / `sq_eq_of_dOrbitRel` / `f_eq_conj_inv_of_stepTwenty_chain`)。

### ⚠ 残る 1 点 = (H5) 連鎖の共役子が `KW` に入ること (書籍 p.129 の 1 文)

`PSU3BarOrbit.lean` の `barOrbitRel` を `KW`-軌道に張り替えようとして判明:
`dOrbitRel_of_stepTwenty_chain` ((H5) の連鎖) が返す共役子は `h(x)⁻¹` で、
これは `D` の元としてしか押さえられていない (`IsFGH.dOrbitRel_fj_cube`)。
一方 `barOrbitRel` を `KW` にすると、この共役子も `KW` である必要がある。

書籍 p.129 はまさにそこを 1 文で済ませている:

> Moreover, by (H4), `h(f(ω(0,r))) ∈ K W`. By (H5), it follows that
> `(ω̄⁻¹(0,r))^{KW} = (ω(0,α+r))^{KW}`, whence `i = k` and `ω_i² = (0,α)`.

**✅ 部品は landing 済 (2026-08-02)**: `h_mul_stepElevenSeq_mem_KW`
(`PSU3StepEighteen.lean`)。書籍が (18) の証明で表示する

  `h(ω(0,u_i)) = (h(ω)ζ⁻¹)^i ζ^i (α / (β^i + β^{-i}))`

は repo の `stepEighteen_unroll`
(`h(ω z_n) = (h(ω)ζ⁻¹)^n h(ω) ζ^n k⁻¹`, `k ∈ K`) そのもの。
`h(ω) ∈ W` (= `h_mem_W_of_frobeniusD`) を入れると最後の因子以外が `W` に入り、
最後が `K` なので全体が `KW`。補助 `mem_KW_of_mul_W_K` を `PSU3StepEightKW` に追加。

**残る配線 (次の入口)** — 2026-08-02 に (H4) 経由の還元をここまで詰めた:

repo の `exists_f_eq_conj_inv` の記号 (`ω` = 書籍 `ω₁`、`ρ = ω²` = `(0,r)`、
`y` = `(0,α)`、`ωi := r (f (ω ρ))`、`ωk := r (f (ω (ρ y)))`) で、(H5) の連鎖
`dOrbitRel_of_stepTwenty_chain` の共役子は `h(X)⁻¹`、`X = ωk⁻¹ ρ`。

(H4) で 2 段還元できる:
1. `X⁻¹ = ωk ρ` (`ρ` は `Q` の中心にあり `ρ² = 1`)、`h(x⁻¹) = h(x)⁻¹` ⟹
   `h(X) = h(ωk ρ)⁻¹`。
2. `hk : ωk ρ = c⁻¹ · f(ω(ρ y)) · c` (`c ∈ KW`)、`h(x^a) = a⁻¹ h(x) a` と
   `h(f(z)) = h(z)⁻¹` ⟹ `h(ωk ρ) = c⁻¹ · h(ω(ρ y))⁻¹ · c`。

⟹ **`h(X) ∈ KW` ⟺ `h(ω(ρ y)) ∈ KW`**。これは基点 `ω` の fibre 元なので、
`h_mul_stepElevenSeq_mem_KW` (+ `h(ω) ∈ W`) が使える形。**要るのは
`ρ y` が `ω` の数列値であること**、すなわち step (15) の exhaustion
(`stepFifteen_exhaust`) の集合に入ること =
「`f(ω(ρ y))` が `ω̄` の `KW`-軌道に入る」。

⚠ **そこが未確定**: `ωk` は定義上 `f(ω(ρ y))` の軌道の代表なので、この条件は
`ω̄k = ω̄` と同値。書籍はそれを (17)(20) の 3 本の等式 (A)(B)(C) の組合せで
出しているように見える。書籍 (B) `(f∘j)((ω₁(0,α+r))^{KW}) = ω₁^{KW}` は
`(ω(ρy))⁻¹ = ω y` なので「`f(ω y)` が `ω̄` の軌道」= `y` が `ω` の数列値、
という別の情報を与える。**次はこの 3 本を repo の `hi`/`hk` と突き合わせて
`f(ω(ρ y))` 側の軌道を特定すること。**

現状 `PSU3BarOrbit.lean` は `hVW` を保持しているが、内部では
`KW_eq_D_of_V_eq_W` / `freeD_of_V_eq_W` 経由で新 API に接続済なので、
この 1 点が埋まれば置換は機械的。

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
