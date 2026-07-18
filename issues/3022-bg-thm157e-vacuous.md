---
id: 3022
slug: bg-thm157e-vacuous
title: "BG Thm 15.7 の bundled statement が book より大幅に弱い — (b) 準恒真 / (d) 3/4 欠落 / (e) 恒真"
created: 2026-07-18
---

# BG Thm 15.7: `fitting_not_ti_cases` は book の 5 条項のうち実質 (a) しか運んでいない

## 経緯 (2026-07-18 起票 → 同日 scope 拡大)

初版は (e) の恒真性のみを扱っていたが、**BG mmd 原文 (L4249) と Lean statement を逐条照合した
結果、同じ定理に同種の欠落が 4 件あることが判明**したので issue を書き直す。
⚠ (e) だけ直して「15.7 完了」と数えないこと (初版のままだとそう誤読される)。

**また、(e) の恒真性は新発見ではない**: `S16_MainResults/TypeP1Criteria.lean` の docstring が
2026-06-23 (commit 078a0b883) 以降ずっと *"currently weakened to the tautology
`abelian M_F ∨ ¬abelian M_F`"* と明記しており、`notes/bg/s15_16_audit.md:114` も 2026-06-14 から
(d)(e) を "known-deferred" として記録していた。本 issue はそれを追跡可能な作業項目に昇格させる
もの。

## 原文 (BG mmd L4249) と Lean の逐条対応

原文は「`F(M)` が TI でないとし、`H = M_F`、`g ∈ G−M` を `X = F(M) ∩ F(M)^g ≠ 1` となるように
**選び**、`E, E₁, E₂, E₃` を §12-13 のとおりに取る。このとき——」と、**特定の `X` を固定して**
5 条項を述べる。Lean は `OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/OpicoreCentralizer.lean:361`
`fitting_not_ti_cases`。

| 条項 | book | Lean の現状 | 判定 |
|---|---|---|---|
| (a) | `M ∈ ℳ_F ∪ ℳ_{P₁}` かつ `H = M_σ` | 同じ (`:363`) | ✅ **faithful** |
| (b) | `X ⊆ H` かつ `X` cyclic (`X = F(M) ∩ F(M)^g` は**固定**) | `∃ X, X ≤ MF M ∧ X ≠ ⊥ ∧ IsCyclic X` (`:364-365`) | ❌ **準恒真** |
| (c) | `M' = F(M) = M_σ × O_{σ(M)'}(F(M))` | `derivedInG M ≤ fittingInAmbient M` (`:374`) | ⚠ **意図的**・正当 |
| (d) | `E₃ = 1`, `E₂ ⊲ E`, `E/E₂ ≅ E₁` cyclic | bundled statement に**無し** | ❌ **3/4 欠落** |
| (e) | 3 分岐の詳細 trichotomy (下記) | `A ∨ (¬A ∧ (a))` (`:377-379`) | ❌ **恒真** |

### 根本原因: `∃ X` による decoupling

book は `X` を**先に固定**し、(b) がその `X` の性質を述べ、(e) が `p = |X|` で `X` と結びつく。
Lean は `∃ X, …` の下に (b)(c)(e) を並べたが、**(c) も (e) も `X` に言及しない**ので束縛が効かず、
各条項が独立の存在主張に分解してしまった。ここから 3 つの欠陥が同時に出ている:

1. **(b) が `M_F ≠ ⊥` と同値**: `X ≤ M_F ∧ X ≠ ⊥ ∧ IsCyclic X` は `M_F ≠ 1` なら任意の素数位数
   部分群で満たされる。実際 `:406-412` の証明は位数 `q` の元 `w` を取って `Subgroup.zpowers w`
   を渡しているだけ。**book の `X = F(M) ∩ F(M)^g` という同定を一切運んでいない**。
2. **(e) が排中律に潰れる**: 末尾 conjunct は `IsMulCommutative (MF M) ∨ (¬IsMulCommutative (MF M)
   ∧ (IsTypeF M ∨ IsTypeP1 M))` で、第2枝の `IsTypeF M ∨ IsTypeP1 M` は**同定理の (a) が既に
   与える** ⟹ `A ∨ ¬A`。情報ゼロ。
3. **`p` が `X` と無関係**: book は `p = |X|` だが Lean は `∃ p, p.Prime ∧ p ∈ σ(M) ∧ p ∉ β(M)`
   と独立に存在量化。`σ ∖ β` の非空性しか述べていない。

### book の (e) が実際に主張している内容 (mmd L4249)

1. `M ∈ ℳ_F` かつ `H` は**階数 2 の可換群**。
2. `p = |X|` は `σ(M) − β(M)` の素数、`O_p(H)` 非可換、`O_{p'}(H)` cyclic、`M/H` の指数が
   すべての `q ∈ π(H)` について `q − 1` を割る。
3. `p = |X|` は `σ(M) − β(M)` の素数、`O_{p'}(H)` cyclic、`O_p(H)` は位数 `p³` で非可換、
   `M ∈ ℳ_{P₁}`、`|M/H|` が `p + 1` を割る。

### (c) の `≤` 弱化は正当 (直さない)

book の `M' = F(M)` は type-`F` で**overstatement**であり、権威ある MathComp 形式化
(`BGsection15.v` `nonTI_Fitting_structure`) も `M^'(1) ⊆ 'F(M)` と包含で述べ、原文の等式が
*"does not appear to be valid"* とコメントしている。詳細は同 file の docstring 参照。
**この 1 件のみ現状維持が正しい。**

### (d) の現状 (調査済)

- ✅ `E₃ = 1`: `OpicoreCentralizer.lean:263` `E3_eq_bot_of_not_fittingIsTI` (sorry-free) に**存在
  する**が、`fitting_not_ti_cases` の結論には**入っていない**。
- ❌ `E₂ ⊲ E`: 未形式化。素材は `S12_ECore.lean:998` `SubgroupESetup.E23_normal`
  (`E ≤ normalizer (E₂ ⊔ E₃)`) にあり、`E₃ = ⊥` と合わせれば即出るが誰も合成していない。
- ❌ `E/E₂ ≅ E₁` / `cyclic (E/E₂)`: 未形式化 (該当 `MulEquiv` も `IsCyclic` も repo に無い)。
- 参考: `TaxonomyOutput.lean:847-851` は `E = E₁` cyclic を得ているが、Thm 15.8 の `τ₂(M) = ∅`
  を**追加仮説として**使うので (d) を subsume しない。
- 旧 issue `issues/closed/2037-thm-15-7-d-sigma-compl-e3-eq-bot.md` は `E₃=1` のみを scope として
  close 済 (他 3 条項は意図的に対象外)。

## やること

- [x] **(b) の修正** (2026-07-18 完了)。`X` を `fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M`
      に束縛し、`∀ g ∉ M` 形で `X ≤ MF M ∧ IsCyclic X` を述べた (nontriviality 仮説は不要 —
      両結論とも `g ∉ M` だけで成立するので、`∃ g` より強い `∀ g` 形にした)。新規補題 4 件:
      - `le_Msigma_of_isPGroup_le_fitting` — `exists_inf_conj_fitting_orderP_witness` 内の
        local `have hMσ_of` を top-level に抽出 (重複解消)。
      - `inf_conj_fitting_le_Msigma` — BG の「`π(X) ⊆ σ(M)` ⟹ `X ⊆ M_σ`」。
        `mem_sigma_of_prime_dvd_card_inf_conj_fitting` (既存) で全素数を σ に落とし、
        nilpotent `F(M)` の normal Hall 部分群 `O_{σ(M)}(F(M)) = F(M_σ)` が σ-部分群を吸収
        (`isPiGroup_le_of_normal_isHallSubgroup` + `oPiCore_isHall_of_isNilpotent`)。
      - `inf_conj_fitting_le_conj_Msigma` — `X^{g⁻¹} = F(M) ⊓ F(M)^{g⁻¹}` の対称性で `g⁻¹` に帰着。
      - `inf_conj_fitting_isCyclic` — `X ≤ M_σ ⊓ M^g` cyclic (Lemma 12.17 三番目の clause)。
      **付随して `Msigma_inf_conj_isCyclic` を S16_MainResults/TheoremsAE → S15_MF/PisetBetaDisjoint
      へ上流移設** (S15 が consume するため; 依存は全て §12 + §15 の rank-1 helper で、S16 の
      ものは使っていなかった)。`TaxonomyOutput` は `open ...S15` 済で無変更、AxiomsCheck の
      namespace のみ更新。
- [x] **末尾の恒真 disjunct を削除** (2026-07-18)。`IsMulCommutative M_F ∨ (¬IsMulCommutative M_F ∧
      (IsTypeF M ∨ IsTypeP1 M))` は `A ∨ ¬A` で情報ゼロだったため、残さず落とした。
      `∃ p ∈ σ(M) ∖ β(M)` は実内容なので存続 ((e) の `p = |X|` 束縛は未了)。
- [ ] **(e) の修正**: 上記 book 3 分岐を述べ直す。**実内容はすでに repo に存在する**ので新規の
      深い数学ではなく再パッケージが主: 分岐 1 ≈ `isTypeI_of_isTypeF` の可換枝
      (`TypeP1Criteria.lean:868-893`、rank = 2 を証明済)、分岐 2 ≈ 同 非可換枝 (`:894-906`、
      `typeF_exponent_dvd_sub_one_of_invariant_card` + `typeF_nonabelian_cyclic_opiCore_compl`)。
      分岐 3 (`|O_p(H)| = p³`, `|M/H| ∣ p+1`, type `P₁`) は未形式化とみられる — 要確認。
- [ ] **`p = |X|` の結合**: (e) の `p` を独立存在量化でなく `X` の位数として述べる。
- [ ] **(d) の追加**: 既存の `E3_eq_bot_of_not_fittingIsTI` を結論に入れ、`E₂ ⊲ E` を
      `E23_normal` + `E₃ = ⊥` から合成し、`E/E₂ ≅ E₁` と `cyclic` を新規に証明する。
- [ ] 各修正後、**恒真に潰れていないこと**を確認する (「(a) から従うか?」を必ず自問)。
- [ ] survey の BG §15 欄と `notes/bg/s15_16_audit.md` を更新。

## 完了条件

(b)(d)(e) が (a) から独立な内容を主張し、`p = |X|` の結合が復元され、book strength・sorry-free・
axiom-clean で証明されること。(c) は `≤` のまま (MathComp 準拠、上記理由)。
⚠ **現状の (b)(e) を「証明済」と数えない**。(e) だけ直して閉じない。

## 下流への影響 (blocking ではない)

`isTypeI_of_isTypeF` (`TypeP1Criteria.lean:840`) と `isTypeV_of_isTypeP1_mf_eq_msigma` は、
**vacuous な (e) を経由せず**非 TI 分岐を自前で再導出しているため、いずれも sorry-free・
axiom-clean で完結している (2026-07-18 検証)。よって本 issue は**下流を block していない** —
直せば下流が重複した再導出をやめて (e) を cite できるようになる、という改善。

## 参照
- `S15_MF/OpicoreCentralizer.lean:361-379` (statement)、`:406-412` ((b) を潰している証明箇所)。
- BG mmd `references/bg/local-analysis.mmd:4249` (原文 + 証明)。
- Coq `coq/theories/BGsection15.v` `nonTI_Fitting_structure` (権威ある形式化; (d) を
  `sigma_complement` 込みで述べている)。
- 先行記録: `notes/bg/s15_16_audit.md:114` (2026-06-14、(d)(e) を known-deferred と記録)、
  `TypeP1Criteria.lean` docstring (2026-06-23 以降、(e) の恒真性を明記)。
- 類似の「真だが内容ゼロ」パターン: App.D の旧 `cnTheorem_reduction`、NearFields の旧
  `∃ classification : Prop, classification` (いずれも de-opacify 済)。
- [[scaffold-sorry-free-not-done]] の系: sorry-free でも内容ゼロなら doneness でない。
