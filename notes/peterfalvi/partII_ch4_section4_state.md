# Peterfalvi Part II, Ch. IV §4 — 到達状態 (2026-08-02)

> 正本の作業ログは [issue 0168](../../issues/0168-pf-part2-ch4-psu3.md) (9k 行)。
> 本 note はその §4 部分の**要約と残件**だけを持つ。

## 何が通ったか

書籍 pp. 132–134 の §4 **全体**が 1 本の定理に組み上がっている:

```
Hypothesis.SectionFourSetup.exists_mem_W
  : standing data + hcent + (ζ₁ ∈ V∩U, ζ₁ ∉ P) ⟹ ∃ x ∈ Q − Q₀, k x ∈ W
```
(`OddOrder/Peterfalvi/Appendices/Suzuki/PSU3SectionFourEndgame.lean`)

主要な中間定理 (すべて axiom-clean, AxiomsCheck 登録済):

| 書籍 | Lean | file |
|---|---|---|
| (4) `a² f(ωs^a)‾ = ζ⁻¹ f(ωs^a)‾^η + ω̄` | `sectionFour_four_linear` | `PSU3SectionFourCoordinate` |
| `η` の半線形性 / 体自己同型 `μ` | `coordConjD`, `coordFieldAut` | `PSU3SectionFourSemilinear` |
| (3)(5)(6) | `sectionFour_three_coord`, `_five_linear`, `_six_linear` | `PSU3SectionFourEquations` |
| (7)(8)(9) | `sectionFour_seven_eight_nine` | 同上 |
| `λ = 1`, `b²+a^{-2μ²} = ζ+ζ⁻¹` | `sectionFour_lambda` | `PSU3SectionFourEndgame` |
| (10) | `sectionFour_ten`, `sectionFour_ten_of_mem_frobFixed` | 同上 |
| `μ² = id` on `F` → `μ = 1` | `coordFieldAut_sq_eq_id_on_frobFixed` 他 | 同上 |
| `η ∈ W`, `h(ω) ∈ W` | `sectionFour_mem_W` | 同上 |
| step (1) `Z(U) ⊆ D`, `Z(U) ⊆ P` | `center_le_subgroupOf_D`, `center_residualImage_le_P` | 同上 |
| step (1)–(3) 配管 | `exists_stepThree_data` | 同上 |

## 実測で判明した「不要だったもの」

* **Appendix I Prop 2 の抽象体と `M.E` の同定は不要**。intertwining が既知のスカラーは
  `μ(K) = F^×` と `μ(1,ζ)` で、後者が `F` の外だから両者が `E` を張る。
  `σ(x) := Ψ(x)/Ψ(1)` の乗法性が 2 行で出る (`addEquiv_mul_mul_eq_of_span`)。
* **書籍が行間で済ませた `μ = 1 ⟹ η ∈ W` は `W = C_V(K)` の定義そのもの**
  (`Basic.lean:183`)。`Q₀` 側の Galois 対応は要らない。
* **(3) は既存の `stepTen_quotient_coord` がそのまま**。§4 固有なのは指数 4 の橋渡し
  (`ω⁴ = 1`) だけ。
* **`hZD : Z(U) ≤ D`** (Intrinsic に 177 箇所 threading されていた) は
  `D = H ∩ H^t` と `C_G(ω) ≤ H` (`ω ∈ Q^#`) から出る。
* **`hS`** (`P·Z(U)` が `C_Q(P)` を中心化) も導出できた。

## ⚠ `hcent` は**導出できる** (2026-08-02 の追加調査)

`hcent : V ⊓ U ≤ C_G(C_{Q₀}(P))` は外部入力ではなく、商仮説の `V̄ = W̄` から出る:

1. `W_eq_inf_centralizer_Q0 : W = D ⊓ C(Q₀)` (`PSU3SectionFourSetup:781`) は
   **一般の `Hypothesis` に対する定理**なので intrinsic 商仮説にも当たる:
   `W̄ = D̄ ⊓ C(Q̄₀)`。
2. `V_eq_W_intrinsicResidualQuotient` (既存) と合わせて **`V̄ ≤ C(Q̄₀)`**。
3. `ζ₁ ∈ V ⊓ U` の像は `V̄` (`mem_W_intrinsicResidualQuotient_of_mem_V` の前半)、
   `y ∈ C_{Q₀}(P)` の像は `Q̄₀` (`y` は 2-元なので `y ∈ U`)。
   ⟹ `[ζ₁, y] ∈ Z(U)`。
4. 一方 `ζ₁ ∈ D` は `Q` を正規化するので `[ζ₁, y] ∈ Q`。
5. `Z(U) ≤ D` (既 landing) と `Q ⊓ D = ⊥` (`Hypothesis` の公理) ⟹
   **`[ζ₁, y] = 1`** ⟹ `ζ₁ ∈ C(y)` ∎

⟹ **実装済** (`inf_le_centralizer_centralizer_Q0`)。`exists_mem_W` の仮説からも外れた。

## `V̄`-元の持ち上げは `V` に留まる (2026-08-02)

`SectionFourSetup.eq_one_of_conj_t_mem_P`: 任意の `ζ` に対し
`c := ζ⁻¹·ζ^t` は `c^t = c⁻¹` を満たす (`t² = 1` の 2 行計算)。
もし `c ∈ P` なら `t ∈ C_G(P)` で `c^t = c` なので `c = c⁻¹`、
`P` は奇数位数だから **`c = 1`**。

⟹ `V̄`-元の持ち上げ `ζ₁ ∈ D ∩ U` は `[ζ₁,t] ∈ Z(U) ⊆ P` を持つので
`[ζ₁,t] = 1`、すなわち **`ζ₁ ∈ V`**。持ち上げの `V`-所属は自動。

## `ζ₁ ∉ P` も導出できた — `P ∩ U ⊆ Z(U)`

`SectionFourSetup.mem_center_of_mem_P` / `notMem_P_of_mk_ne_one`:
`U ≤ C_G(P)` (`residualImage_le_centralizer`) なので `P` の元が `U` に入れば
`U` の中心に入る。⟹ **`P ∩ U ⊆ Z(U)`**。

⟹ `ζ̄ = mk' ζ₁ ≠ 1` なら `ζ₁ ∉ Z(U)` なので `ζ₁ ∉ P ∩ U`、`ζ₁ ∈ U` と
合わせて **`ζ₁ ∉ P`**。

⟹ 書籍の `|(V∩U)/(P∩U)| = (ℓ+1)/(ℓ+1,3) ≠ 1` という**数え上げは不要**
(PSU(3,ℓ) の構造は使わない)。残るのは `W̄^#` の元を `D̄` 経由で持ち上げて
`exists_mem_W` に食わせる組立てのみ。

## ✅ §4 完了 (2026-08-02)

```
Hypothesis.SectionFourSetup.exists_mem_W
  : (§4 の standing data のみ)
    ⟹ ∃ x ∈ Q − Q₀, ∃ ζ ∈ W^#, f x = ζ⁻¹x⁻¹ζ ∧ k x ∈ W    -- = §3 Prop の仮説
```
外部入力ゼロ。`hcent` も `ζ₁ ∈ (V∩U) − (P∩U)` も導出できた:

* `hcent` = `inf_le_centralizer_centralizer_Q0` — 商仮説の `V̄ = W̄` から。
* `ζ₁` = `SectionFourSetup.exists_zeta_one` — `W̄^#` の元を `D̄` 経由で
  持ち上げ、`eq_one_of_conj_t_mem_P` で `V`-所属を、`P ∩ U ⊆ Z(U)` で
  `∉ P` を得る。**書籍の数え上げ `|(V∩U)/(P∩U)| = (ℓ+1)/(ℓ+1,3) ≠ 1` は不要**。

⟹ §3 Corollary 1 への接続 (Ch. IV 全体の完了) が次の作業。

## 実装上の注意 (再訪時)

* `PSU3SectionFourEndgame.lean` の `variable (hyp)` は**明示**。`include hyp in` を
  付けた `SectionFourSetup.*` 補題はドット記法が効かないので
  `SectionFourSetup.foo hyp s4 …` と書く。
* `hyp` を使わない補題は `omit [MulAction G Ω] [Finite G] in` が要る
  (`unusedSectionVars` は `--strict` gate で赤)。
* `show` は style linter に掛かる — `change` を使う。
* AxiomsCheck の登録名は `namespace Hypothesis` 内なら `Hypothesis.` を付ける
  (leaf build では検出できず、フルビルドで初めて赤になる)。

## 次の作業 = §3 Corollary 1 への接続 (Ch. IV 完了)

書籍 p.132 (原文):

> **Corollary 1.** Under the hypothesis of the proposition, `O^{2′}(G) = PSU(3,q)`.
> In particular, if `V = W`, then `G` is isomorphic to `PSU(3,q)` or to `PGU(3,q)`.

§4 の出力 (`∃ ω ∈ Q−Q₀`, `f(ω) = (ω⁻¹)^ζ` (ζ ∈ W^#), `h(ω) ∈ W`) は
**§3 の Proposition の仮説そのもの**なので、Corollary 1 が `V ≠ W` の場合にも
`O^{2′}(G) ≅ PSU(3,q)` を与えて Theorem A が閉じる。

✅ `exists_mem_W` の結論は強化済 (2026-08-02):
`∃ x ∈ Q − Q₀, ∃ ζ ∈ W, ζ ≠ 1 ∧ f x = ζ⁻¹x⁻¹ζ ∧ k x ∈ W`
= **§3 Proposition の仮説そのもの**。

要調査: §3 Proposition の結論 (`θ = 1` と `f(ρ) = (ρ̄/y, 1/y)`) と
Corollary 1 が repo にどこまで在るか。`stepThree` は Proposition の
stage (3) まで。`PSU3CorollaryTwo.lean` は Corollary 2 のみ。

## §3 Proposition / Corollary 1 の repo 実測 (2026-08-02)

* **Proposition の結論** `θ = 1` と `f(ρ) = (ρ̄/y, 1/y)`:
  * `θ = 1` = `stepThree` / `stepThree_of_odd` / `thetaModel_eq_id_on_frobFixed` ✅
  * `f(ρ) = (ρ̄/y, 1/y)` の機械は在る — `PSU3RootGroupModel.lean` (冒頭 docstring が
    まさにこの主張)、`PSU3StarEquation.lean` (`f(ρ)s^a = (ω̄', x'+A)`)、
    `PSU3InverseFormula.lean:1039`。**組み上がった「Proposition」1 本があるか要確認**。
* **Corollary 1** = 「`O^{2′}(G) = PSU(3,q)`」は repo では
  `TheoremAConclusion` (= `L` 正規・奇指数 + 標準モデル、`CentralizerInductionBridge:91`)
  の `target = psu3` を作ること。`TheoremAConclusion.Q_and_residual` が
  `L = primeComplementResidual 2 G` を与えるので、`O^{2′}(G)` の同定はそこ。
  ⟹ Corollary 1 の形式化 = 「Proposition の仮説から `TheoremAConclusion` (psu3) を
  構成する」。

**次セッションの入口**: `PSU3RootGroupModel` / `PSU3StarEquation` /
`PSU3InverseFormula` を読み、§3 Proposition が 1 本に組まれているかを実測する。
組まれていれば `exists_mem_W` の出力を食わせるだけで Ch. IV が閉じる。

## §3 の `V = W` は repo 側の特殊化債務だった (2026-08-02, 解消済)

書籍 p.129 の §3 Proposition は `V = W` を仮定しない。仮定するのは
`ω ∈ Q−Q₀`, `ζ ∈ W^#`, `f(ω) = (ω⁻¹)^ζ`, **`h(ω) ∈ W`** の 4 つだけ。
それでも repo の §3 は `hVW : V = W` を全段に threading していた。根は 2 つ:

1. **§2 step (8) の fibre bound**。書籍は `mᵢ ≤ m = |W|`、repo は `mᵢ ≤ |V|`。
   repo は共役元を `a ∈ D` としか記録せず `x ↦ aK ∈ D/K` (`|D:K| = |V|`) で
   数えていた。squeeze は `n·m = q+1` でしか閉じないので `V = W` が要る。
   **書籍の論法**: fibre 条件は `KW`-軌道への所属なので共役元は `k v`
   (`k ∈ K`, `v ∈ W`) の形。`x ↦ v` が `W` への単射 (同じ `v` なら 2 つの
   共役元は `K` の同じ剰余類 ⟹ step (7))。`k v ∈ K ⟺ v = 1` で `m₁ ≤ m−1`。
   ⟹ `PSU3StepEightKW.lean` (`stepEight_of_KW`,
   `exists_mem_Q0_orbitOfF_eq_of_KW`)。

2. **`D` の `(Q/Q₀)^#` 上の自由性** (`eq_one_of_conj_eq_mul_Q0_of_mem_D`)。
   内部で `D = KW` を使い、それが `V = W` を要求していた。
   **書籍の論法**: `h(ω⁻¹) = (h(ω)^t)⁻¹ = h(ω)⁻¹ ∈ W` (∵ `h(ω) ∈ W ≤ C_D(t)`)
   なので `ζ³·h(ω⁻¹) ∈ W`、`W`-自由性 (`..._of_mem_W`、`V=W` 不要) で足りる。
   ⟹ `h_inv_eq` 以下 §3 全段の `hVW` を `hhW : h ω ∈ hyp.W` に置換。

Corollary 2 (`G ≅ PSU(3,q)`) は `V = W` が定理なので `_of_freeD` 版を保持し、
`h_mem_W_of_freeD` で `hhW` を作って一般版へ渡す (証明の重複ゼロ)。

## §3 Proposition が 1 本に組み上がった (2026-08-02)

`PSU3Proposition.lean`:
* `proposition_inverseFormula` — 書籍の仮説 (上記 4 つ) から
  **全ての `ρ ∈ Q−Q₀`** で `f(ρ)` の単位座標が `(ρ̄/y, 1/y)`。
  stage (4) = `stepFour_cover_of_base`、stage (5) = `stepFive`。
* `proposition_reciprocal` — それを `unitaryRootEquiv` で `RootGroup q` に移し
  **`ε(f ρ) = RootGroup.reciprocal (ε ρ)`**。

対になる標準モデル側 = `StandardModelFGH.lean` の `standardModel_f_rootHom`
(`f(R u) = R(u₁/u₂, 1/u₂)`、Bruhat 関係から `fgh_eq_of_canonical` で読み取り)。

## 次の作業 = Corollary 1 の組立て

材料は揃った:
* `RankOneBNPairRigidity.lean` の `conjQMulEquivOfData`
  (`εQ : Q ≃* Q'` が `f` と `f'` を intertwine ⟹ `⟨Q^x⟩ ≃* ⟨Q'^x⟩`) と
  `closure_iUnion_conj_eq_primeComplementResidual` (`⟨Q^x⟩ = O^{2′}(L)`)。
* `G` 側 = `proposition_reciprocal`、標準モデル側 = `standardModel_f_rootHom`、
  `Q ≃* RootGroup q` = `unitaryRootEquiv ∘ Ψ`、
  `RootGroup q ≃* standardRootSubgroup q` = `rootEquivStandardRoot`。
* faithfulness = `Setup.normalCore_eq_bot` / `..._of_isSimpleGroup`。

残るのは **`PSU3InductionTarget` の `actionEquiv`** — 群同型だけでなく
`Ω ≃ Unital n` の同変全単射が要る。`conjQMulEquivOfPermMatch` は点集合
`Option ↥Q ≃ Option ↥Q'` から作られているので原理的には取れる
(`coordsEquiv : (L ⧸ M) ≃ Option ↥Q`)。ここが次の設計ポイント。

### Corollary 1 の `actionEquiv` — 点集合の辞書 (実測 2026-08-02)

* `RankOneBNPair.coords (M Q t) : Option ↥Q → L ⧸ M` は
  `none ↦ 1·M`、`some x ↦ (x⁻¹ t)·M`。
* `Hypothesis.qRegularEquiv : hyp.Q ≃ {ω : Ω // ω ≠ hyp.basept}` は
  `x ↦ x • (t • basept)` (`Basic.lean:294`)。
* `Ω ≅ G ⧸ H` (`g • basept ↦ gH`) の下で `coords (some x) ↦ x⁻¹ • (t • basept)`
  なので、両者は **`Option.map (·⁻¹)` だけずれる**。
⟹ `Ω ≃ Option ↥Q` は `qRegularEquiv` + `basept ↦ none` で作り、
`coords` 側と合わせるときに `inv` を挟む。`Unital n = Option (RootGroup n)` も
同じ形なので `Equiv.optionCongr εQ` で繋がる。
