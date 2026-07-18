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
- [x] **`p = |X|` の結合** — **完了 (2026-07-19)**。以下 4 段すべて sorry-free・axiom-clean、
      新 leaf `S15_MF/WitnessPGroup.lean` に集約。最終形 =
      `inf_conj_fitting_eq_of_not_isMulCommutative` (`X = X₁`) と
      `card_inf_conj_fitting_eq_of_not_isMulCommutative` (`|X| = p`)。
      (以下は着手前の調査メモ)
BG は `X = X₁` を示して `p = |X|`
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

      **手順 2 完了 (2026-07-19)**: `exists_rankTwo_elemAbelian_of_witness` (`WitnessPGroup`)。
      当初は `q = p` 分岐を丸ごと top-level へ抽出する計画だったが、**その必要は無かった** —
      `exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI` の結論が既に `q := p` で
      `|Z₀| = p` / `¬ X₁ ≤ Z₀` / `Z₀ = Ω₁(Z(O_p(M_F)))` を与えるので、それを **cite して**
      `B` を組み立てるだけで済む (`X₁ ⊓ Z₀ = ⊥`、`X₁ ≤ C_G(Z₀)`、`B` elementary abelian、
      `|B| = p²`、`B ≤ C₁`)。大きな refactor を回避できた。

      **⚠ 手順 3 の障害と、その解決 (2026-07-19)**: BG は `B ∈ ℰ*(P)` と書き、素朴には
      「`P` の中で極大」と読める。一方 Lean の `IsMaximalElementaryAbelian p A`
      (`GroupTheory/NarrowPGroup.lean:104`) は `∀ F : Subgroup R` と **ambient 型全体**で量化し、
      Lemma 10.13 は `A : Subgroup G` を取るので ambient は `G`。当初これを不整合と見て
      `S10_LocalLemmas.lean:441` の手口の転用を考えたが、**同所は「G で極大 ⟹ 部分群 S で極大」の
      逆向き**で使えない (P→G 方向は一般に偽)。

      **Coq 精読で決着**: `coq/theories/BGsection15.v:1119` は
      `p2maxElemB : [group of B] \in 'E_p^2(G) :&: 'E*_p(G)` — **Coq も ambient は `G`**。
      つまり BG の `ℰ*(P)` は「`P` に含まれる `G`-極大」の意で、repo の
      `elemAbelianOfRankIn p n H X := X ∈ elemAbelianOfRank G p n ∧ X ≤ H` と同じ読み。
      **不整合ではなく、私の記法の誤読だった。**

      証明の核は同 file の `max_rB` (:1100-1113) で、**`A` を共役で `P` に押し込んでから rank 評価**:

      1. `P = O_p(M_F)` は **`G` の Sylow p-部分群** (`M_σ` が `G` の σ-Hall
         = `Msigma_isHall` (`S10_HallStructure:584`)、`p ∈ σ(M)`、`M_σ = M_F` nilpotent ゆえ
         `O_p(M_σ)` がその Sylow p)。
      2. `A` は p-群なので、ある `a` で `A^a ≤ P` (mathlib `IsPGroup.exists_le_sylow` + Sylow 共役)。
      3. `a` は `X₁` を正規化するとは限らないので **σ-Hall tameness = BG Cor 15.3(b)** で補正:
         `x₁ ∈ P` と `x₁^a ∈ P` が `G`-共役なら `∃ b ∈ N_G(P)`, `x₁^a = x₁^b`。
         **Lean に在る** — `mf_hall_centralizer_control` (`TIFailure.lean:1311`) の第 2 conjunct が
         まさにこれ (`∀ x ∈ H, ∀ y ∈ H, G-共役 → ∃ n ∈ N_G(H), …`)。`H := P` を `M_σ` の
         `piSet`-Hall 部分群として渡す。
      4. `a * b⁻¹` は `X₁` を正規化し `A^(ab⁻¹) ≤ P^(b⁻¹) = P`。よって
         `rank A = rank A^(ab⁻¹) ≤ rank (M_F ⊓ C_G(X₁)) < 3` (既存 `hrank3`)。

      `|B| = p²` と合わせ、`B ⊆ A` elementary abelian なら `|A| ≤ p²` ゆえ `A = B`。
      **入力 4 点すべて repo に実在を確認済み** — 未形式化の上流は無く、組み立てのみ。

      **手順 4 (最終段) も Coq で確認済** (`defX`, :1128-1137): `X ≤ C_P(B)` を出し
      (`X ≤ P` は `inf_conj_fitting_isPGroup_of_not_isMulCommutative` + `X ≤ M_F`;
      `C_P(X₁) = C_P(B)` は `P` が `Z₀ ≤ Z(P)` を中心化するから)、10.13(b) で
      `C_P(B) = X₁ × Z` (`Z` cyclic)、`X` cyclic かつ `X₁ ⊓ Z = ⊥` から `X = X₁`。

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
      ~~**未確認の 1 点** = 手順 4 の「`X` は p-群」~~ → **解決済 (2026-07-19)**。
      BG は「`O_{p'}(H)` は `C_H(X₁)` 可換ゆえ可換。Hence `P = O_p(H)` is not abelian and `X` is
      a `p`-group」と一文で済ませ根拠を書いていないが、既存の 2 事実の衝突で出る:
      - **任意の**素数 `d ∣ |X|` について `O_d(M_F)` は非 cyclic。これは BG 冒頭の段
        (「`O_p(M)` が cyclic なら `X₁` が `M` と `M^g` の両方で正規になり不可能」) =
        `not_isCyclic_opiCore_mf_of_orderP_le_conj`。`X` の位数 `d` の部分群が `M_F` と `M_F^g`
        の**両方**に入る (`inf_conj_fitting_le_Msigma` + 共役版 + `M_F = M_σ`) ので `d` で使える。
      - 一方 `M_F` 非可換なら `O_{p'}(M_F)` は cyclic (`typeF_nonabelian_cyclic_opiCore_compl`)
        で、`d ≠ p` なら `O_d(M_F) ≤ O_{p'}(M_F)`。
      ⟹ `p` 以外の素数は `|X|` を割れない。**ChatGPT 相談は不要だった。**
      形式化: `S15_MF/WitnessPGroup.lean`
      `inf_conj_fitting_isPGroup_of_not_isMulCommutative` (sorry-free, axiom-clean)。

      **付随して必要** → **完了 (2026-07-19)**: `exists_inf_conj_fitting_orderP_witness` の結論に
      `X₁ ≤ F(M) ⊓ conj g • F(M)` を追加済 (構成上真だが未公開だった)。消費側 4 箇所も更新。

      **新 leaf の layering**: `mf_eq_msigma_of_not_fittingIsTI` が `OpicoreCentralizer` に在るため、
      `WitnessPGroup` は `PisetBetaDisjoint` でなく **`OpicoreCentralizer` を import** する
      (PisetBetaDisjoint → OpicoreCentralizer → WitnessPGroup)。⟹ **`p = |X|` 完成後の
      「精密化された (e)」は `OpicoreCentralizer` でなく `WitnessPGroup` 側 (かその下流) に置く**
      (現 `fitting_not_ti_trichotomy` は OpicoreCentralizer に在り WitnessPGroup を cite できない)。
- [ ] **(e2)/(e3) の分離** — **未了 (ただし残作業は assembly のみ)**。

      ⚠ **2026-07-19 訂正: 本項の旧記述「type `P₁` 側の `|O_p(H)| = p³` と `|M/H| ∣ p + 1` は
      未形式化」は誤り。** 実測したところ **(e2)(e3) の数学的内容はすべて形式化済・axiom-clean**
      で、`isTypeV_of_isTypeP1_mf_eq_msigma` (`S16_MainResults/TypeVSinger.lean:392`) が現に
      両分岐を証明している。旧記述は stale な docstring を信じたもの
      ([[verify-port-state-by-number-not-coq-name]] の再発)。実在確認:

      | 部品 | 所在 | 状態 |
      |---|---|---|
      | `\|O_p(H)\| = p³` | `TypeVSinger.lean:277` `card_opiCore_eq_prime_cube_singer` | ✅ AxiomsCheck:7474 |
      | `\|M/H\| ∣ p+1` | `GroupTheory/RepresentationTheory/ExtraspecialSinger.lean:319` `card_dvd_succ_of_primeAction_extraspecial` | ✅ AxiomsCheck:9147 |
      | `r(P) ≤ 2` | `TypeVSinger.lean:133` `pRank_opiCore_le_two_of_kappaHall` | ✅ AxiomsCheck:9143 |
      | `\|Z(P)\| = p` | `TypeVSinger.lean:194` `card_center_opiCore_eq_prime_of_omega1Center_le_kstar` | ✅ AxiomsCheck:7463 |
      | BG Thm 5.5 | `S05_NarrowAutomorphisms.lean:966` `solvableAut_of_narrow` | ✅ AxiomsCheck:2526 |
      | BG Cor 10.7(b) | `S10_BetaRadicalCore.lean:695` `sylow_structure` (第2 conjunct) | ✅ |
      | (e2) exponent | `TypeP1Criteria.lean:799` `typeF_exponent_dvd_sub_one_of_invariant_card` | ✅ |
      | (e2) type-`P₁` 版 engine | `TypeP1Criteria.lean:1556` `kappaHall_card_dvd_sub_one_of_inf_kstar_eq_bot` | ✅ |
      | semiprime `C_H(k) = K*` | `TypeP1Criteria.lean:1534` `centralizer_msigma_kappaElement_eq_kstar` | ✅ |

      ⚠ 併せて **stale docstring 2 件**を訂正すること (将来の誤読源):
      `TypeVSinger.lean:255-274` (「the sole remaining content is …`sylow_structure_b` を
      de-privatize せよ」= 完了済) と `:376-390` (「the sole remaining residual は (8.8) の
      `W₁`-action analysis で未形式化」= 完了済)。proof 内の `-- (sorry 1)` / `-- (sorry 2)`
      コメントも実 sorry でなく歴史的ラベル。

      **⚠ さらに重要な訂正: 私の当初の「(e2) = type `F` / (e3) = type `P₁`」という読みは誤り。**
      BG 原文でも Coq でも **(e2) に型の制約は無い** — (e2) は exponent 条件そのもので、
      type `P₁` でも成り立ちうる。権威ある Coq (`BGsection15.v:947-950`) の形が正本:

      ```coq
      (*e*) (*1*) [/\ M \in 'M_'F, abelian H & 'r(H) = 2]
         \/ let p := #|X| in [/\ prime p, ~~ abelian 'O_p(H), cyclic 'O_p^'(H)
          & (*2*) {in \pi(H), forall q, exponent (M / H) %| q.-1}
         \/ (*3*) [/\ #|'O_p(H)| = (p ^ 3)%N, M \in 'M_'P1 & #|M / H| %| p.+1] ]
      ```

      すなわち **共通 conjunct (`p = |X|` prime / `O_p(H)` 非可換 / `O_{p'}(H)` cyclic) を括り出し、
      (e2) ∨ (e3) を内側の disjunction** にする。これが形式化目標の正本。

      **Coq の (e2)/(e3) 分岐ロジック** (`BGsection15.v:1185-1204`) —
      場合分けは含意 `Ks = Z₀ → |K| ∣ p−1` の真偽:
      - **含意が真 ⟹ (e2)**。各 `q ∈ π(H)` について: `Z q = Ks` なら `|Z q| = q`・`|Ks| = p` から
        `q = p` で仮定が直接効く。`Z q ≠ Ks` なら `|Ks|` 素数ゆえ `Z q ⊓ Ks = 1`、
        semiprime (`C_H(k) = K*`) で `K` が `Z q` に半正則作用 ⟹ `|K| ∣ q−1`。
      - **含意が偽 ⟹ `Ks = Z₀` かつ `¬(|K| ∣ p−1)` ⟹ (e3)** (Singer 鎖)。

      type `F` 側 (Coq `FmaxM` 分岐) は `U₀` の Frobenius 作用 = Lean
      `typeF_exponent_dvd_sub_one_of_invariant_card` に対応。

      ⟹ **残作業は「上記部品を Coq の形の 1 定理に組み上げる」assembly のみ**。未形式化の上流は無い。
      配置: (e2)(e3) が S16 の補題を要するため、trichotomy 本体は **S16 の新 leaf**
      (`TypeVSinger` の下流) に置く。S15 の `fitting_not_ti_trichotomy` は S15 レベルの
      partial として存続させる (S15 は S16 を cite できない)。

      #### 手順 (2026-07-19 確定)

      **手順 A — witness extractor を per-`g` へ一般化**。`p = |X|` を述べるには `X` を固定する
      必要があり、Coq も `g \notin M -> X :!=: 1 ->` を仮説に取る。現状の
      `exists_inf_conj_fitting_orderP_witness` (`PisetBetaDisjoint.lean:581`) は `∃ g` 形だが、
      **証明本体は `:597` で `exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI` から
      `hgM`/`hXne` を obtain した直後、以降 `hnotTI` を使っていない** (2026-07-19 確認済 —
      `hnotTI` の出現は署名 `:583` と `:597` の 2 箇所のみ、定理は `:684` まで)。⟹ 署名を
      `{g : G} (hgM : g ∉ M) (hXne : X ≠ ⊥)` に変え `∃ p X₁, …` を返す形へ一般化し、
      `:597` の obtain を削除するだけ。既存の `∃ g` 版は新版からの 2 行の導出として残す
      (消費側 4 箇所を書き換えずに済む; 純粋リネーム wrapper ではなく genuine な特殊化)。

      **手順 B — trichotomy 本体**を新 leaf `S16_MainResults/FittingNonTITrichotomy.lean` に。
      Coq の形どおり共通 conjunct を括り出す。`|M/H|` は `Subgroup.index` 
      (`((MF M).subgroupOf M).index`) で述べる — repo の既存イディオム
      (`card_W1_eq_derived_index` と同じ) で、normality instance を要求せずに済む。
      exponent 条件のみ商群 `↥M ⧸ (MF M).subgroupOf ↥M` が要るので `MF M ⊲ M` を供給する。
      証明の骨格:
      - `H` 可換 ⟹ (e1) (既存 `isTypeF_of_isMulCommutative_mf_of_not_fittingIsTI` +
        `rank_mf_eq_two_…`)。
      - `H` 非可換 ⟹ `p = |X|` (`card_inf_conj_fitting_eq_of_not_isMulCommutative`)、共通 conjunct
        2 件 (`opiCore_singleton_not_isMulCommutative_of_witness` /
        `typeF_nonabelian_cyclic_opiCore_compl`)、その後 (a) で type `F` / `P₁` に分岐:
        - type `F` ⟹ (e2): 各 `q ∈ π(H)` に per-prime witness
          (`exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI`) +
          `typeF_exponent_dvd_sub_one_of_invariant_card`。
        - type `P₁` ⟹ Coq の含意 `Ks = Z₀ → |K| ∣ p−1` で場合分け。真なら (e2)
          (`Z q = Ks` なら `q = p`; さもなくば `Z q ⊓ Ks = ⊥` + semiprime で
          `kappaHall_card_dvd_sub_one_of_inf_kstar_eq_bot`)。偽なら (e3) (Singer 鎖 =
          `card_opiCore_eq_prime_cube_singer` + `card_dvd_succ_of_primeAction_extraspecial`)。

      **⚠ 手順 B の唯一の未形式化サブ補題 = `|K*| = p` (Coq `oKs`, `BGsection15.v:1178`)**
      (2026-07-19 調査)。type `P₁` の (e2) 分岐で `Z q = K*` の場合に `q = p` を出すのに要る。

      - **既存の `kstar_le_opiCore_of_inputs` (`Theorem152Helpers.lean:268`) は使えない** —
        仮説に `hne : MF M ≠ Msigma M` を持つが、15.7(e) の設定は逆の `M_F = M_σ` (`hmf`)。
        ⚠ 名前だけ見て流用しないこと。
      - **正しい経路** (Coq `sKsP` を辿る): `K* ≤ M''` は **Cor 15.6 =
        `typeP_kstar_in_mf` (`Corollary155.lean:1425`)** が与える (`1 ≠ K* ≤ M''`)。
        あとは `M'' ≤ O_p(M_F)` を出せばよく、これは
        `M' = M_F = M_σ` (type `P₁`、`typeP1_msigma_eq_derivedInG`) と
        `M_F` nilpotent の分解 `M_F = O_p(M_F) × O_{p'}(M_F)`、および
        `O_{p'}(M_F)` cyclic ⟹ 可換 (`typeF_nonabelian_cyclic_opiCore_compl`) から
        「`M'/O_p(M_F)` 可換 ⟹ `M'' ≤ O_p(M_F)`」で出る。
        `K* ≤ O_p(M_F)` と `|K*|` 素数 (`kstar_card_prime_of_inputs`) と
        `O_p(M_F)` が `p`-群であることから `|K*| = p`。
      - 見積 ~40 行。ここだけが新規の数学で、残りは既存補題の cite。
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

### `p = |X|` chain の完成 (2026-07-19)

| 段 | 内容 | 定理 |
|---|---|---|
| 1 | `X` は p-群 (BG は根拠を書いていない) | `inf_conj_fitting_isPGroup_of_not_isMulCommutative` |
| 2 | `B = X₁ × Ω₁(Z(P))` が rank 2 elementary abelian | `exists_rankTwo_elemAbelian_of_witness` |
| 3 | `B` が (ambient `G` で) 極大 — Sylow 押し込み + σ-Hall tameness | `isMaximalElementaryAbelian_sup_omega1Center_of_witness` |
| 4 | Lemma 10.13(b) → `X = X₁`、ゆえに `p = \|X\|` | `inf_conj_fitting_eq_of_not_isMulCommutative` / `card_…` |

段 4 の詰め (BG の "Thus X = X₁" 一言) は: `X ⊓ Z = ⊥` (非自明なら位数 `p` の部分群を含み、
`X` cyclic ゆえそれは `X₁` に一致 → `X₁ ⊓ Z = ⊥` に矛盾)、そして `x = u·v` 分解と `X₁` の指数 `p`
から `x^p = v^p ∈ X ⊓ Z = 1` ⟹ `X` の指数が `p` を割る ⟹ cyclic + `X₁ ≤ X` で `X = X₁`。

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
