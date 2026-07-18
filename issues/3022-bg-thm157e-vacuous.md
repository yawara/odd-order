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
- [~] **(e) の修正** — **部分完了 (2026-07-18)**。`fitting_not_ti_trichotomy` として、BG の証明が
      実際に行う場合分け (`H = M_F` が可換か否か) の形で述べ直した。恒真スロットは解消済み
      (両枝が case 判定述語以外の内容を持つ)。
      - **分岐 1 (H 可換) = BG (e1) を完全形式化**:
        - `isTypeF_of_isMulCommutative_mf_of_not_fittingIsTI` (**新規**) — 「H 可換 ⟹ M ∈ ℳ_F」。
          type `P₁` を排除する BG の議論をそのまま形式化: type `P₁` なら
          `typeP1_msigma_eq_derivedInG` で `M_σ = M'`、`M_F = M_σ` と合わせ `M' = M_F` 可換 ⟹
          `M'' = 1`。しかし Cor 15.6 (`typeP_kstar_in_mf`) が `1 ≠ K* ≤ M''` を与えるので矛盾。
          **この条項はどこにも無かった** (`isTypeI_of_isTypeF` は type F を仮説に持つので不要だった)。
        - `rank_mf_eq_two_of_isMulCommutative_of_not_fittingIsTI` (**S16 から S15 へ抽出**) —
          `isTypeI_of_isTypeF` 内にインライン展開されていた rank = 2 の議論を独立補題化。
          S16 側は cite に置換 (重複 ~25 行を削除)。
      - **分岐 2/3 (H 非可換) = (e2)(e3) の共通部分のみ**: `p ∈ σ(M) − β(M)`、`O_p(H)` 非可換
        (`opiCore_singleton_not_isMulCommutative_of_witness`)、`O_{p'}(H)` cyclic
        (`typeF_nonabelian_cyclic_opiCore_compl`)。
- [ ] **`p = |X|` の結合** — **未了 (ただし前提は揃っている)**。BG は `X = X₁` を示して `p = |X|`
      を得る: `Z₀ = Ω₁(Z(P))`、`B = X₁ × Z₀ ∈ ℰ²(P) ∩ ℰ*(P)` (`C_H(X₁)` の rank < 3 による)、
      そこから `|Z₀| = p` と `Z(P)` cyclic、最後に **Lemma 10.13(b)** で
      `C_P(X₁) = C_P(B) = X₁ × Z` (Z cyclic)。
      ⚠ **Lemma 10.13 は形式化済**: `S10_LocalLemmas.lean:975`
      `nonabelian_pSubgroup_rankTwo_elemAbelian_structure` が (a)(b)(c) 全条項を持ち、(b) は
      `∃ Z, Z ≤ P ∧ IsCyclic Z ∧ Ω₁(Z(P)) ≤ Z ∧ A₀ ⊓ Z = ⊥ ∧ C_G(A) ⊓ P = A₀ ⊔ Z` の形。
      (`S10_HallStructureCore.lean:53` の「statement skeleton を配置済」は **scaffold 期の
      stale な注記**で、本体は実在する — 初版の本 issue はこれを信じて「未形式化」と誤記した。
      [[verify-port-state-by-number-not-coq-name]])
      よって残作業は §15 側の組み立て (`B` の構成 + `B ∈ ℰ²(P) ∩ ℰ*(P)` + 10.13 適用) のみ。

      **⚠ さらに調査 (2026-07-19): `B` の構成も既に書かれている。**
      `exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI` (`PisetBetaDisjoint.lean:1101`) の
      `q = p` 分岐 (`:1118-1210`) が BG の当該段落をほぼそのまま持っている:
      - `P := O_p(M_F)`、`X₁ ≤ P`、`P` 非可換 (`:1131`)、`C₁ = C_{M_F}(X₁)` 可換 (`:1134`)
      - `Z := Ω₁(Z(P))` elementary abelian (`:1137-1143`)
      - `X₁ ⊄ Z` (BG の「Clearly X₁ ≠ Z₀」、`:1155` — `X₁ ≤ Z(P)` なら `P ≤ C₁` 可換で矛盾)
      - `X₁ ⊓ Z = ⊥` (`:1172`)、`B := X₁ ⊔ Z` elementary abelian かつ `≤ C₁` (`:1182-1191`)
      - `|B| = p·|Z|` (`:1197`)、`log_p |B| ≤ rank C₁ < 3` (`:1202`) ⟹ `|Z| = p`
      **これらは全て局所 `have` で、外に公開されていない**。⟹ 実作業は:
      1. この `q = p` 分岐から `B`/`Z₀` の事実を **top-level 補題へ抽出** (`|Z₀| = p`,
         `B = X₁ ⊔ Z₀` が rank 2 elementary abelian, `B ≤ C₁`)。
      2. `IsMaximalElementaryAbelian p B` を示す (`GroupTheory/NarrowPGroup.lean:104` の定義 =
         「`B` を含む elementary abelian は `B` 自身のみ」)。BG の根拠は `C_H(X₁)` の rank < 3 で、
         `B ≤ C₁` かつ `rank C₁ < 3` から出る (rank 3 の elementary abelian が `C₁` に入れない)。
      3. Lemma 10.13 を `A := B`, `A₀ := X₁`, `P := O_p(M_F)` で適用 → `C_G(B) ⊓ P = X₁ ⊔ Z'`
         (`Z'` cyclic)。
      4. `X ≤ P` (BG「X is a p-group」— 要根拠確認) と `X ≤ C_G(B)` から `X ≤ X₁ ⊔ Z'`、
         `X` cyclic と合わせて `X = X₁`、ゆえに `p = |X|`。
      **未確認の 1 点** = 手順 4 の「`X` は p-群」。BG は「`O_{p'}(H)` は `C_H(X₁)` 可換ゆえ可換。
      Hence `P = O_p(H)` is not abelian and `X` is a `p`-group」と一文で済ませており、
      この含意の根拠が原文では省略されている。ここが唯一の行間 — 詰まったら
      [[feedback-ask-chatgpt-for-elided-gaps]] (Coq `BGsection15.v` 精読 → ChatGPT 再構成)。

      **付随して必要**: `exists_inf_conj_fitting_orderP_witness` の結論に
      `X₁ ≤ F(M) ⊓ conj g • F(M)` を追加する (構成上は真だが公開されておらず、現状 `X₁` と
      `X` が statement 上結びついていない)。これが無いと手順 4 が書けない。
- [ ] **(e2)/(e3) の型別分離** — **未了**。type `F` 側の exponent 条件
      (`exp(M/H) ∣ q − 1`) は `typeF_exponent_dvd_sub_one_of_invariant_card` として**存在し**、
      `isTypeI_of_isTypeF` が使っている (trichotomy へは未配線)。type `P₁` 側の
      `|O_p(H)| = p³` と `|M/H| ∣ p + 1` (BG Thm 5.5(b) + Cor 10.7(b) + Thm 2.5 経由) は未形式化。
- [x] **(d) の追加** (2026-07-18 完了)。`sigmaComplement_structure_of_not_fittingIsTI` として、
      `fitting_not_ti_cases` の bundle でなく **§12 E-setup を取る独立定理**にした (BG (d) は
      「§12-13 のとおりに取った E, E₁, E₂, E₃」についての主張なので、E-setup を引数に取る形が
      faithful)。4 条項すべて sorry-free:
      - `E₃ = 1` — 既存 `E3_eq_bot_of_not_fittingIsTI` を cite。
      - `E₂ ⊲ E` — `E23_normal` (`E ≤ N(E₂ ⊔ E₃)`) に `E₃ = ⊥` を代入。
      - `E = E₁E₂` + `E₁` が `E₂` の complement — `eq_sup` に `E₃ = ⊥` を代入し、
        τ₁ は p-rank 1・τ₂ は p-rank 2 ゆえ τ₁ ∩ τ₂ = ∅ → `|E₁|`,`|E₂|` coprime → `E₁ ⊓ E₂ = ⊥`。
      - `E₁` cyclic — 既存 `E1_isCyclic`。
      印字されている `E/E₂ ≅ E₁` は `quotientE2MulEquivE1` (mathlib
      `Subgroup.IsComplement'.QuotientMulEquiv` + `subgroupOfEquivOfLe`) として別途提供。
- [ ] 各修正後、**恒真に潰れていないこと**を確認する (「(a) から従うか?」を必ず自問)。
- [ ] survey の BG §15 欄と `notes/bg/s15_16_audit.md` を更新。

## 完了条件

(b)(d)(e) が (a) から独立な内容を主張し、`p = |X|` の結合が復元され、book strength・sorry-free・
axiom-clean で証明されること。(c) は `≤` のまま (MathComp 準拠、上記理由)。
⚠ **現状の (b)(e) を「証明済」と数えない**。(e) だけ直して閉じない。

### 進捗 (2026-07-18)

| 条項 | 状態 |
|---|---|
| (a) | ✅ 元から faithful |
| (b) | ✅ **完了** — X を束縛、`∀ g ∉ M` 形 |
| (c) | ✅ `≤` のまま正しい (MathComp 準拠) |
| (d) | ✅ **完了** — `sigmaComplement_structure_of_not_fittingIsTI` + `quotientE2MulEquivE1` |
| (e) | ⚠ **部分** — (e1) 完全、(e2)(e3) は共通部分のみ。残 = `p = \|X\|` (Lemma 10.13(b) 依存) と型別分離 |

**本 issue を閉じる条件 = 残り 2 チェックボックス** (`p = |X|` / (e2)(e3) 分離)。
どちらも **§15 内で完結する組み立て作業**で、上流の未形式化 gate は無い (Lemma 10.13 は形式化済 —
上記参照)。type `P₁` 側の `|O_p(H)| = p³` / `|M/H| ∣ p+1` だけは BG Thm 5.5(b) + Cor 10.7(b) +
Thm 2.5 の被覆確認が要る。

⚠ **ファイル行数**: `S15_MF/OpicoreCentralizer.lean` は本作業で 1485 行。CLAUDE.md の分割 trigger
(1500 行) 直下なので、**次にこのファイルへ追記する前に分割**すること。

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
