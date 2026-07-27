---
id: 162
slug: pf-part2-ch3-theorem-c
title: "Peterfalvi Part II Ch.III Theorem C: Q は 2-群 (Q₁ = 1)"
created: 2026-07-28
---

# Peterfalvi Part II Ch.III Theorem C: `Q` は 2-群 (`Q₁ = 1`)

## 実測 (2026-07-28) — 本当に未形式化かの検証

survey (`three_books_full_survey_2026_07_16.md` L852) は Thm C を「未」とするが、
**その根拠は stale** (「`structure_of_H` (Suzuki.lean:133, sorry) が opaque scaffold」と
書くが、当該宣言は de-opacification campaign で**削除済**)。ラベルを信用せず実測した:

| 検証 | 結果 |
|---|---|
| `Appendices/Suzuki.lean` | **宣言ゼロ**の pure re-export hub (58 行)。scaffold は削除済で、置換もされていない |
| `(C1)` 仮説の carrier | repo 全体に**存在しない** (grep 0 件) |
| `feit_sibley_coherence` の consumer | **ゼロ** (自 file chain と AxiomsCheck のみ)。書籍でこの定理を使うのは Thm C の証明だけなので、これが決定的 |
| `theoremC` 識別子 | 全て **BG App.C / BG §16 の Theorem C** — 別の本の別定理 |
| `Q₁ = ⊥` の hit | すべて Ch.II FirstCase で `Q₁ = ⊥` を**仮説に取る**側 (`FirstCase/StepSix.lean:270` `card_Q_eq_two_pow_of_Q1_eq_bot`)。Thm C が供給すべきものであって Thm C ではない |
| pp. 115–121 / "Structure of H" を参照する file | **ゼロ** |
| 未マージのレーン作業 | b / c / d とも main の 0 commit 先行 = 無し |

⟹ **未形式化で確定**。「`Q₁ = 1` ⟹ `Q` は 2-群」の配管だけは Ch.II 側に既存で、
欠けているのは `Q₁ = 1` を**証明する**側。

### git log からも直接読める (2026-07-28 確認)

| 時刻 | commit |
|---|---|
| 07-26 05:30 | `55ec6f681` **Theorem B 完成** — Ch.II 完結 |
| 07-26 05:32 | `2e431ea73` Hall–Wielandt を AxiomsCheck 登録 |
| 07-26 05:34 | `b90e31082` issue 9503 close / 2053 を pending 化 |
| 07-26 05:43 | `25521c85c` **docs(survey): Isaacs のラベル突き合わせを再実測** ← 別トラックへ pivot |

`OddOrder/Peterfalvi/Appendices/Suzuki/` への commit は **07-26 05:30 の Theorem B 完成が最後**で、
以後ゼロ。全期間の commit message にも Peterfalvi の Theorem C / Ch.III / "Structure of H" は
一度も現れない。⟹ Ch.II 完結の直後に Part I の一般化トラック (0151–0161) へ移り、
**文書順の次である Ch.III に入らないまま**現在に至った。

### 原因 = frontier リスト側の取りこぼし (process bug)

survey の「📍 2026-07-26 終了時点の frontier」(L1441 `### 残っているもの`) が挙げる 6 項目に
**Part II Ch.III–Ch.IV が入っていない**。一方 `### Pf App: Suzuki` の表には Thm C 以下
**12 行の「未」**が並んでいる。frontier 節が Part I 側の表からしか拾っていなかったため、
「残りは packaging とごく少数」という誤った全体像になっていた。
⟹ 本 issue と同時に frontier 節を訂正する。

## 書籍 (pp. 115–116、ページ画像 `references/peterfalvi/pages/peterfalvi-p115.png` / `-p116.png` で確定)

**(C1)** `V ≠ 1` かつ、素数位数の任意の `P ≤ V` に対し `C_G(P)` の 2-rank ≥ 2。

**Theorem C.** `Q` は 2-群。

証明 (背理法、`Q₁ ≠ 1` と仮定):

1. **`D` が `Q₁` に fixed-point-freely 作用**。素数位数の `P ≤ D` について
   `|Ω_P| = 2` なら `C_H(P) ⊆ D` ゆえ `C_Q(P) = 1`;
   `|Ω_P| ≥ 3` なら `P` は `D` 内で `V` の部分群に共役 (Ch.I §1 Prop 6(c)) ゆえ
   (C1) + Ch.I §3 Prop 1(c) で `C_{Q₁}(P) = 1`。
2. **`Q ∩ Q^x = 1` (`x ∈ G − H`)** — `H ∩ H^x` が `H` 内で `D` に共役ゆえ。
3. ⟹ Feit–Sibley (Appendix IV) の仮説が充足 ⟹
   `𝒮 = {χ ∈ Irr(H) | Q₁ ⊄ Ker χ}` が `Ind_H^G` について coherent。
4. `λ` = `H` の線形指標、`λ ≠ 1_H`、`QK ⊆ Ker λ` (`H/QK ≅ V` が可解非自明ゆえ存在)。
5. `(|K|,|V|) ≠ 1` なら `D` が位数 `p²` の非巡回部分群を持ち fpf に反する
   ([H] Kap V Satz 8.15) ⟹ **`QK` は `H` の Hall 部分群**。
6. `x, x^g ∈ H` ⟹ `λ(x^g) = λ(x)` (π′-成分に帰着 → Hall の定理で `V` の元に共役 →
   Ch.I §3 Lemma 2 で `V` 内共役)。
7. ⟹ `(Ind λ)(x) = λ(x)(Ind 1_H)(x)` (`x ∈ H`) ⟹ `⟨Ind λ, Ind λ⟩ = 2`。
8. `Ind_H^G λ = f₁ + f₂` (`fᵢ ∈ Irr(G)`)、`⟨Ind λ, 1_G⟩ = ⟨λ, 1_H⟩ = 0` ゆえ `fᵢ ≠ 1_G`。
9. `𝒮 = {χ₁,…,χₙ}`、`χᵢ(1) = aᵢ|D|`、`a₁ = 1`、coherence から
   `Ind(χᵢ − aᵢχ₁) = eᵢ − aᵢe₁` (`i ≥ 2`, `eᵢ ∈ ±Irr(G)`)。
10. `f₁ = ±eᵢ` を仮定すると矛盾: Appendix IV Lemma 2(c) で `χ̄ᵢ ≠ χᵢ ∈ 𝒮`、
    `Ind(χᵢ − χ̄ᵢ) = eᵢ − e′ᵢ`、[Is] Lemma 7.7 で `Res(eᵢ − e′ᵢ) = χᵢ − χ̄ᵢ`
    (`Q` が Hall + `χᵢ − χ̄ᵢ` が `H − Q` で消える) ⟹ `Ind λ = ±(eᵢ + e′ᵢ)` ⟹
    `|Q| + 1 = ±2eᵢ(1)` は `|Q|` 偶より不可能。
11. ⟹ `⟨Res f_j, χᵢ − aᵢχ₁⟩ = 0` ⟹ `Res f_j = b_j(∑ aᵢχᵢ) + ψ_j` (`Q₁ ⊆ Ker ψ_j`)。
12. 次数評価 `|Q| + 1 = f₁(1) + f₂(1) ≥ (b₁+b₂)∑aᵢχᵢ(1) = (b₁+b₂)|S|(|Q₁|−1)`
    ⟹ `b₁ + b₂ ≤ |Q₁|/(|Q₁|−1) < 2` ⟹ ある `j` で `b_j = 0` ⟹ `Q₁ ⊆ Ker f_j`。
13. `N = Ker f_j` は `1 ≠ N ≠ G` の正規部分群 ⟹ Ch.I §3 Prop 2 で Theorem A の結論
    ⟹ Ch.I §3 Lemma 1 で `Q` は 2-群 ⟹ `Q₁ = 1`、矛盾。

⚠ pdftotext の誤り 1 件: 書籍は `χᵢ(1) = aᵢ|D|` (OCR は `aᵢ|K|` に見える)。ページ画像で確定済。

## 前提の所在 (実測、すべて landed)

| 書籍 | repo |
|---|---|
| Ch.I §1 Prop 6(c) | `exists_conj_mem_D_map_le_V` (`FixedPointCentralizer.lean:485`) |
| Ch.I §3 Prop 1(c) | `centralizer_trichotomy_of_induction` (`CentralizerTrichotomy.lean`) |
| Ch.I §3 Prop 2 | `theoremAConclusion_of_not_simple` (`InductionNonSimple.lean:627`) |
| Ch.I §3 Lemma 1 | `TheoremAConclusion.Q_and_residual` (`CentralizerInductionBridge.lean:112`) — `IsPGroup 2 Q` を直接与える |
| Ch.I §3 Lemma 2 | `ConjugacyInV.lean` |
| Appendix IV (Feit–Sibley) | `feit_sibley_coherence` (`FeitSibleyMain.lean:319`)、sorry-free |
| `Q = S × Q₁` | `SylowDecomposition.lean` (`Q1` = `Q` の正規 2-補群、characteristic、奇位数) |
| `Q` 冪零 | `isNilpotent_Q` (`QStructure.lean`) |

## 置き場

新ディレクトリ `OddOrder/Peterfalvi/Appendices/Suzuki/StructureOfH/`
(Ch.II の `FirstCase/` と同じ流儀)。**新 leaf は同じ commit で `OddOrder.lean` に配線する。**

## ⚠ step 3 で判明した上流の阻害 — Feit–Sibley が書籍に無い `Odd |G|` を要求している

`feit_sibley_coherence` は `(hoddG : Odd (Nat.card G))` を取るが、**書籍 Appendix IV の
"Hypotheses and Notation" (p. 144、ページ画像で確定) に `G` の奇性は無い**:

> `G` is a finite group and `H = Q ⋊ D` is a **proper** subgroup of `G`. We assume that
> `(|D|,|Q|) = 1` and that `Q ∩ Q^x = 1` for `x ∈ G − H`. …
> `Q = S × Q₁`, `|Q₁|` and `|S|` are relatively prime, `D` acts without fixed points on `Q₁`,
> `Q₁` is not a 2-group and `S` is nilpotent.
> **Theorem.** If `d` is odd, then `𝒮` is coherent …

⟹ **Ch.III は `|G|` が偶 (involution `t ∈ G`) なので、現状の repo 版は適用できない。**
Theorem C は Appendix IV の唯一の consumer なので、これが `feit_sibley_coherence` の
consumer ゼロだった真因でもある。

### `hoddG` が実際に何に使われているか (trace 済)

1. `Odd (Nat.card Q1)` の導出 (`feit_sibley_coherence` 冒頭)。
2. `witness_charValue_cong` → **`peterfalvi_67_hall_of_odd`** — ここでは
   `hreal : ConjClasses.mk z⁻¹ ≠ ConjClasses.mk z` (= `z` が `z⁻¹` と共役でない) を作るためだけ
   に使われている。一般版 `peterfalvi_67_hall` は `hreal` を直接取る。

### 書籍は (2) を `d` 奇から出している (p. 149、step (7))

> **Since `d` is odd**, we may assume that `𝒦₁ ∩ Z^# ≠ ∅` and `𝒦₂ = (𝒦₁)⁻¹`.

論法 (`Z = [Q₁,Q₁] ∩ Z(Q₁)`、`Z ⊴ H`、`Q` は `Z` を中心化):
`g z g⁻¹ = z⁻¹` とすると `z⁻¹ ∈ Q ⊓ Q^g` が非自明 ⟹ TI より `g ∈ H = QD` ⟹
`g = q·δ` と書くと `q` は `Z` を中心化するので `δ` が `z` を反転 ⟹ `δ²` は `z` を中心化 ⟹
fpf より `δ² = 1` ⟹ `|D|` 奇より `δ = 1` ⟹ `z = z⁻¹` ⟹ `z² = 1`、`|Q₁|` 奇に矛盾。

### やること (step 3 の前段)

**`feit_sibley_coherence` の `Odd (Nat.card G)` を `Odd (Nat.card Q₁)` に弱める** — 書籍が
実際に使うのはこれだけ (Lemma 2(c) の「odd order group `Q₁D`」も `|Q₁|` 奇 + `d` 奇)。
`hreal` は上記の書籍論法で `hd` から導出する。影響範囲は `FeitSibleyMain` /
`FeitSibleyConclusion` の 4 signature + `peterfalvi_67_hall_of_odd` の呼び出し 1 箇所
(`peterfalvi_67_hall_of_odd` の consumer はこの 1 箇所のみと実測)。

## やること

- [x] step 1: `(C1)` carrier `SecondCaseHypothesis` + `D` の `Q₁` 上 fpf (2026-07-28、commit `794473d39`)
- [ ] step 2: `Q ∩ Q^x = 1` (`x ∉ H`)
- [ ] **step 3a (新): Feit–Sibley の `Odd |G|` を書籍どおり `Odd |Q₁|` へ弱める**
- [ ] step 3b: Feit–Sibley `Hypothesis` の構成と coherence の取得
- [ ] step 4: 指標側 endgame (λ / `Ind λ = f₁ + f₂` / 次数評価)
- [ ] step 5: `Q₁ = ⊥` の結論 + AxiomsCheck 登録

## 完了条件

`SecondCaseHypothesis` の下で `IsPGroup 2 hyp.Q` (同値に `hyp.Q1 = ⊥`) が sorry-free で
landing し、AxiomsCheck に登録されて axiom-clean。フルビルド green + `--strict` 警告ゼロ +
sorry 非退行。

## 参照

* 前章 = [issue 2053](pending/2053-pf-suzuki-theorem-b.md) (Ch.II Theorem B、2026-07-26 完成)
* Appendix IV = issues 1049 / 1053 / 1054 (Feit–Sibley、lane a)
* survey `notes/meta/three_books_full_survey_2026_07_16.md` L825–L862 (Pf App: Suzuki の表)
