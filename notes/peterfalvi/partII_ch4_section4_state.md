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

## 残り = **`ζ₁ ∈ (V ∩ U) − (P ∩ U)` の存在 1 つだけ**

書籍 §4 step (2) (p. 133)「`|(V∩U)/(P∩U)| = (ℓ+1)/(ℓ+1,3) ≠ 1` since `ℓ > 2`」。

`hcent` は上記のとおり導出済 (`inf_le_centralizer_centralizer_Q0`) で、
`exists_mem_W` の仮説からも外した。

⚠ 既存の `SectionFourSetup.exists_ne_one_mem_W_centralizer` (= `C_W(P) ≠ 1`) は
docstring が「書籍の `(ℓ+1)/(ℓ+1,3) ≠ 1` を step (2) が使う形」と述べるが、
それは `standingData_centralizerQuotient` 用であり、**`ζ₁ ∈ V ∩ U` は出ない**
(`w ∈ C_W(P)` が `U = O^{2′}(C_G(P))` に入る保証がない)。別途要形式化。

## 実装上の注意 (再訪時)

* `PSU3SectionFourEndgame.lean` の `variable (hyp)` は**明示**。`include hyp in` を
  付けた `SectionFourSetup.*` 補題はドット記法が効かないので
  `SectionFourSetup.foo hyp s4 …` と書く。
* `hyp` を使わない補題は `omit [MulAction G Ω] [Finite G] in` が要る
  (`unusedSectionVars` は `--strict` gate で赤)。
* `show` は style linter に掛かる — `change` を使う。
* AxiomsCheck の登録名は `namespace Hypothesis` 内なら `Hypothesis.` を付ける
  (leaf build では検出できず、フルビルドで初めて赤になる)。
