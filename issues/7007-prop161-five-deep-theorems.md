---
id: 7007
slug: prop161-five-deep-theorems
title: "Prop 16.1 axiom-clean: 5 deep §15/§16 structural theorems"
created: 2026-06-19
---

# Prop 16.1 axiom-clean: 5 deep §15/§16 structural theorems

## 背景

POLE-1 の構造側 producer 2 本（`section16MaximalPair` / `section16TypePStructure`）は
2026-06-19 に assembly-complete 化（issue 7005/7006 closed、sorry 140→139）。両 producer の残
`sorryAx` は全て上流 gate に由来し、最も近い lane-f 所有の gate が **BG Proposition 16.1**
(`proposition_type_classification`, `S16_MainResults.lean:894`, 現 `sorry`)。

Prop 16.1 の **組み立て層は完成済み**: engine `proposition_type_classification_of_inputs`
(`S16:817`) は 11 個の named obligation から 6 連言を sorry-free で組む。assembler 群
(`typePData_of_inputs` `S16:695` / `isType{II,III/IV,V}_of_typePData` `S16:763/750/776` /
`typeFData_of_kappa_eq_bot` `S16:555`) と bridge (`typePData_of_isTypeNonI` 等) も clean。

**∴ Prop 16.1 axiom-clean 化の残コスト = 丸ごと「5 本の深い §15/§16 構造定理の本体」**
（Workflow `wpn72i4yc` 2026-06-19 の精査で確定）。§14 long pole (Thm 14.7 `typeP_duality`,
`S14:7982`) は **clean** になったので frontier は §14 を抜け §15/§16 に上がった。

## 5 本の深い定理（= 真の残務）

⚠ **2026-06-23 更新: この表は大半が STALE。5 本中 4 本が完了。** 残るは `theoremA_maximal_structure`
のみ（standalone 版は faithfulness 未修正で `sorry`、faithful 変種 `theoremA_maximal_structure_faithful`
は cont.² で完成済）。**かつ Prop 16.1 の真の gate は「5 deep theorems」ではなく 8 型 bridge =
TypeXData construction**（下記）。

| Lean 名 | 場所 | BG | 状態 |
|---|---|---|---|
| `theoremC_paired_structure` | `S16:620` | Thm C | ✅ **DONE**（2026-06-23、conjunct 2 = Cor 14.12 配線、axiom-clean） |
| `typeP_auxiliary_structure_gated` | `S15:1640` | Lemma 15.1 | ✅ **DONE**（standalone 4 lemma の term-mode cite、axiom-clean、2026-06-23 確認・AxiomsCheck 登録） |
| `mf_ne_msigma_typeP1_structure` | `S15` | Thm 15.2(a) | ✅ **DONE**（issue 8012、AxiomsCheck 登録） |
| `fitting_not_ti_cases` | `S15` | Thm 15.7 | ✅ **DONE**（type-F M'=F(M) 還元済、AxiomsCheck 登録） |
| `theoremA_maximal_structure` | `S16:144` sorry | Thm A | ⚠ standalone は faithfulness 未修正で残 sorry（hFI = M' の TypeFData）。faithful 版完成済 |

**∴ Prop 16.1 (`proposition_type_classification`, S16:1984 sorry) の真の残務 = 11 obligation のうち
9/10/11 (`hP_derived`/`hF_not_derived`/`h152a`) は ✅ DONE、残り 8 = 型 bridge
(`hFI`/`hP2II`/`hP1neIIIIV`/`hP1eqV` 順方向 + `hIF`/`hIIP2`/`hIIIIVP1`/`hVP1` 逆方向)** =
BG-local 型 (`IsTypeF`/`IsTypeP1`/`IsTypeP2`、κ ベース) ↔ 抽象型 (`IsTypeI`–`V`、TypeXData) の同値。
これは §16 TypeXData construction gate ([[bg-s16-gated-on-typedata-construction]])。matched-pair
producer `typeP2_exists_matched_kappa_hall_pair`（2026-06-23 landed）は `hP2II` (S16:1236 `hKnorm`) を
unblock する。

## BG schematic proof（原典 recipe、mmd 4420-4444）

```
Theorem A:
  Thm 10.2(b) → (1) M_σ unique σ-Hall + σ(G)-Hall         [✅ Msigma_isHall, ungated 済]
  Lemma 15.1(a) → (2) K cyclic Hall κ
  Prop 14.2(a)(b)(c) → (3)(4)(5)  M=KUM_σ, U◁UK, C_U(k)=1, K*=C_Mσ(K)≠1, C_M(k)=K×K*
  Thm 15.2(a), Cor 15.5, Thm 15.7(a)(b) → (6)(7)(8)
    (6) 1⊂M_F⊆M_σ⊆M'⊊M, M'/M_F nilpotent  [(6 partial) MF≤Msigma, Msigma≤M' ungated 済]
    (7) M''⊆F(M)=C_M(M_F)M_F, K≠1→F(M)⊆M'
    (8) M_F≠M_σ → U=1, F(M) TI, K prime

Theorem C (K≠1):
  Cor 14.12, Cor 15.6, Lemma 15.1(b) → (1)(2)(3)  U abelian+N(U)⊄M; K* cyclic 1⊂K*⊆M_F, M_F 非cyclic; M'=UM_σ, K*⊆M''
  Thm 10.1(b), Thm 14.7(a)(b)(c), Prop 14.2(c) → (4)(5)  ∃!Mstar; M(C(X))={M}/{Mstar}
  Thm 14.7(d)(f)(g)(e) → (6)(7)(11)(8)  M∩Mstar=Z=K×K* cyclic; M or Mstar P2 + 共役; U=1→K* prime; Ẑ TI N(Ẑ)=Z
  Prop 14.2(d), Thm A(3)(5) → (9)  C_M(Ẑ)=A0(M)-A(M) TI
  Prop 14.2(g), Thm 15.7(a) → (10) U≠1→K prime + F(M) TI ⊇M_σ

Theorem D (assembly): Cor 15.3(b)→(1); Lem 12.17→(2); Thm 14.4(b)+A(8)+Cor 15.9→(3)(4)
  [engine theoremD_..._of_inputs は既存; lane-f/H で配線]
```

**Thm C は ∃!Mstar=(4)=`typeP_duality`(clean) を含み、(6)(7)(8)も Thm 14.7 経由 ⟹ §14 clean 化の恩恵大。**

## 依存補正した buildable 順序（重要）

ユーザー選択は「Thm A→C→Lem15.1→15.2→15.7」だが、**実際の依存は Thm A/C が §15 lemma に
bottom-out** するので、clean 化には §15 foundation が先。真の順序:

1. **Lemma 15.1 (`typeP_auxiliary_structure_gated` S15:704)** — 最上流土台。deps = Prop 14.2(a)
   ✅ / Thm 14.7 ✅clean / Thm 12.12。4 conjunct: ①K≠⊥→M'=U⊔M_σ ∧ U abelian ②C_G(X) funnel
   (X cyclic+τ2) ③⟨U∩M̂_σ⟩ abelian ④U≠⊥→Frobenius U0M_σ。
2. **Thm 15.2(a) / Thm 15.7 / Cor 15.5** — Thm A の (6)(7)(8) が要する §15 残り。
3. **Thm A (`theoremA_maximal_structure` S16:144)** — Lemma 15.1 + Prop 14.2 + §15 で組む。
4. **Thm C (`theoremC_paired_structure` S16:274)** — Thm A + Thm 14.7 + Lemma 15.1(b) で組む。
5. **Prop 16.1 配線** — 11 obligation を構築し `exact proposition_type_classification_of_inputs …`、
   AxiomsCheck 登録。

### ⚠ stale docstring 注意（2026-06-19 発見）

`typeP_auxiliary_structure` の docstring (S15:745-758, Lane G 記載) は「conjunct 2/5 は **sorried**
§14 typeP_duality (Thm 14.7) を cite」とするが、**Thm 14.7 は今 clean**。docstring は stale で、
これら conjunct は既に unblock されている可能性が高い。着手時にまず Thm 14.7 経由の citation が
通るか確認すること（早期の勝ち筋）。

## 関連 forward lemmas（既存・活用可）

- `derivedInG_eq_Msigma_sup_derivedInG_complement` (S14:7741, clean): `M' = M_σ ⊔ E'`。
  Lemma 15.1①の `M'=U⊔M_σ` には E の Frobenius 構造 `E=K⋉U`（U=E₂E₃=E'）経由で `E'↔U` を繋ぐ要。
- `typeP_derivedInG_isComplement_kappaHall` (S14:7806, clean): `M'` complements `K`（piece 2 で使用）。
- `typeP_structure` = Prop 14.2 (S14:1665, proven): ActsPrimeOn / Kstar≠⊥ / N(X)⊓M=K⊔Kstar / TI 等。
- `theoremA_ungated_conjuncts` (S16:181, clean): Thm A の (1)(5 partial)(6 partial) 既証。
- `theoremB_U_sylow_abelian_rank_le_two` (S16:242, clean): Thm B(1)。

## 進捗ログ

**2026-06-23 (cont.⁸) ✅✅✅ Prop 16.1 forward bridges の真の linchpin = M_F-internal Fitting 分解 (BG Cor 15.5) を type-`P₂` で完成 → TypePData carrier が全 type-`P₂` から構成可能化、sorry-free + axiom-clean** (lane-f RESUME、full build green、AxiomsCheck 3 本登録、FT-path sorry 124 不変=carrier 構成は honest 進捗で headline sorry は forward bridge 完了まで動かない):

「5 deep theorems」frontier 精査で **Thm 15.7 (`fitting_not_ti_cases`) は既に完全 DONE** と確認 (type-F の `M'≤F(M)` は Lemma 12.19 + `fitting_decomposition` 経由で ungated 済、proof は S15:7824-7926 sorry なし)。LAUNCH.md item 3「M'=F(M) 一点に還元済」は stale。⟹ frontier は **Prop 16.1 forward bridges の 6 deep TypePData field** に集約、その最深 gate = `hDcompl`/`hSDfit`/`hFiteq` (M_F-internal complement = BG Cor 15.5)。本セッションでこれを完成:

- **新 `typeP2_mf_internal_fitting_decomposition` (S15, sorry-free + axiom-clean)**: type-`P₂` maximal `M` + κ-Hall `K` + (κ∪σ)'-Hall `U` ⟹ 3 deep field を一括供給。
  - `hDcompl` (M' = M_F × U complement in M'): `M_F = M_σ` (type-P2 ⟹ M_σ nilpotent) + `M' = U ⊔ M_σ` (Lemma 15.1b) + `U ⊓ M_σ = ⊥` (互素 Hall) ⟹ `isComplement'_of_disjoint_and_mul_eq_univ`。
  - `hFiteq` (F(M) = M_F ⊔ (U⊓C_M(M_F))): crux = **Y := O_{σ'}(F(M)) ≤ U**。Y は τ₂-群 (Cor 15.5a)、`σ'` (opiCore) ∧ `κ'` (τ₂∩κ=∅ via rank: κ-prime rank 1 vs τ₂-prime rank 2)、normal in M ⟹ `normal_le_hall` で (κ∪σ)'-Hall U に含、かつ Y centralizes M_σ=M_F ⟹ `F = M_F ⊔ Y ≤ M_F ⊔ (U⊓C) ≤ F`。
  - `hSDfit` (M'' ≤ ...): `M'' ≤ F(M)` (Cor 15.5) + hFiteq から自明。
- **新 helper `opiCoreInG_sigmaCompl_fittingInAmbient_primeFactors_subset_tau2` (S15, axiom-clean)**: Cor 15.5(a) の τ₂-membership 形 (cyclic 形の sibling、Y の κ' を供給)。
- **新 `typePData_of_isTypeP2` (S16, sorry-free + axiom-clean)**: matched-pair producer (`typeP2_exists_matched_kappa_hall_pair`: abelian U, K≤N(U)) + 上記分解 ⟹ `typePData_of_isTypeP_of_inputs` を type-`P₂` で**完全適用**。**∴ TypePData carrier が全 type-`P₂` maximal から sorry-free 構成可能** (= CLAUDE.md「carrier 構成可能性 = doneness」マイルストーン)。Type-valued def ゆえ Prop 存在子は `Exists.choose`/projection で抽出 (obtain 不可)。

**▶ 次 = hP2II は {hderF, hderfit}(M' type-F 構造)のみに還元済 (cont.⁹、`isTypeII_of_isTypeP2_of_derived_typeF`)** — cont.⁸ の「hcommon 多レーン gated」評価は **誤りと判明・訂正**:
- **`hcommon` (`TypePNontrivialCore`) は全体 lane-f-local** (cont.⁹ で確定): `U≠⊥`(matched) ∧ `(card W1).Prime`(**Prop 14.2(g) `typeP_structure` proven、lane-b 10.11 不要** — (10.11) は partner 側 primality であって type-P2 の κ-Hall ではない) ∧ `IsTISubset (sharp M_F) (N(M_F))`(**Prop 14.2(g) が `IsTISubset (sigmaSharp M) (N(M_σ))` を供給、M_F=M_σ ゆえ一致**)。
- **`hnorm` (N(U)⊄M)** = Cor 14.12 を matched U の Sylow-r 部分群に適用。lane-f。
- ⟹ `isTypeII_of_isTypeP2_of_derived_typeF` (cont.⁹, axiom-clean) が hcommon/hUcomm/hnorm/TypePData を全 discharge、**hP2II = この補題 + {`hderF`(M' type-F) + `hderfit`(F(M')=M_F)} だけ**。
- ③ **真の唯一 gate = `hderF` (M' が type-F)** = Peterfalvi (8.6)、`IsTypeF (derivedInG M)` = `Nonempty (TypeFData M')`。

**▶ hderF 深掘り (cont.⁹、結論: 深い未形式化 §15/§16 構造補題、char-gate の可能性あり — 単純な template 流用は不可)**:
- TypeFData(M') の構成は `typeFData_of_kappa_eq_bot` (type-F maximal の TypeFData) が template、materials = my decomposition の hDcompl (M'=M_σ⋊U complement) + Lemma 15.1(e) Frobenius (conjunct 8 of `typeP_auxiliary_structure`) + 15.1(d) U1。
- **但し crux = `maxNilpotentNormalHall M' = M_σ` (= TypeFData.H_eq + hderfit)**。⊇ (M_σ は nilpotent normal Hall in M') は easy (`le_maxNilpotentNormalHall`)。**⊆ が深い**: `maxNilpotentNormalHall M' = F(M)` 一般 (F(M)≤M' for ¬type-F by Cor 15.5(d)、F(M) nilpotent normal Hall in M')、`= M_σ ⟺ Y:=O_{σ'}(F(M))=⊥ ⟺ F(M)=M_σ`。⚠ 私の decomposition で **Y≤U かつ Y≤C(M_σ)** ゆえ Y≠⊥ なら F(M)=M_σ×Y⊋M_σ で `maxNilpotentNormalHall M'≠M_σ` ⟹ **hderfit が偽**。
- **✅ 精緻化 (cont.⁹): TypeFData の `frobenius_HU0` は `H⊔U0`=M_σ⊔U0 の Frobenius = Lemma 15.1(e) そのもの (full-U FPF 不要、U0 のみ)**。U1_commutative=15.1(d)、complement=my hDcompl。**∴ hderF の deep gate は純粋に `maxNilpotentNormalHall M' = M_σ` (= TypeFData.H_eq + hderfit) のみ**。
- **`maxNilpotentNormalHall M' = M_σ`** ⟺ `Y=⊥` (= F(M)=M_σ)。⊇ easy。⊆: M_σ ⊊ N (nilpotent normal Hall in M') が存在 ⟺ 非自明 `W≤C_U(M_σ)` で W が U の Hall かつ M' で normal。**Y≤C_U(M_σ)∩U かつ Y τ₂-Hall** ゆえ Y≠⊥ なら反例候補。**∴ 要 `Y=⊥` (τ₂-part of F(M) trivial)、これが subtle な §15/§16 数論的 fact** (C_U(M_σ) の構造 = full U が FPF か)。Peterfalvi 版 `typeII_derived_frobenius` (10.7) は sorried+char-gated+弱 carrier ゆえ cite 不可。
- **∴ hderF = 未形式化の deep §15/§16 補題「type-P2 で F(M)=M_σ (Y=⊥)」**。要 BG §15 精読 (Cor 15.9/Thm 15.8 周辺の τ₂(M) 構造) または ChatGPT 相談。multi-session、lane-f 所有可だが大物。
- ∴ **lane-f の §16 構造 frontier は本質的に「完了 or deep-gated」**: POLE-1 tp producer ✅assembly-complete (lane-b 10.11 待ち) / hP2II ✅{hderF}に還元 / hderF=deep未形式化 / 他 bridge=carrier-gated。**lane 再配置 (hub 判断) or hderF deep 投資の岐路**。hP1neIIIIV/hP1eqV (type-P1) も別 deep (U=SZ-complement、M'/M_F nilpotent deferred)。

**2026-06-23 ✅ Lemma 15.1 (`typeP_auxiliary_structure_gated`) は既に DONE と確認 — 早期勝ち筋は banked 済、AxiomsCheck 登録 + stale 表/docstring 修正** (commit に含む):

「5 deep theorems」の早期勝ち筋調査 (ユーザー選択)。`#print axioms typeP_auxiliary_structure{,_gated}` = `[propext, Classical.choice, Quot.sound]` を確認 — **Lemma 15.1 は前セッションで既に sorry-free + axiom-clean** だった (4 conjunct が standalone clean lemma `typeP_hall_derived_eq_and_abelian`/`typeP_hall_small_subgroup_cyclic_tau2`/`typeP_centralizerGeneratedBySigma_isMulCommutative`/`typeP_hall_frobenius_factor` の term-mode cite、Thm 14.7 も clean)。表の `S15:704 sorry` は stale。→ AxiomsCheck に両者登録 (regression lock)、`typeP_auxiliary_structure` の "Proof status" docstring の "(sorried)" 記述を訂正。**5 deep theorems は 4/5 完了 (Thm A standalone のみ残、faithful 版は完成済)**。真の Prop 16.1 gate = 8 型 bridge (上表参照)。

**2026-06-23 ✅✅✅✅ BG Theorem C (`theoremC_paired_structure`) 完全完成 — conjunct 2 (`N_G(U)⊄M`) を Cor 14.12 に配線、sorry-free + axiom-clean** (commit `b9646712`、AxiomsCheck 登録、full build 3881 green、FT-path sorry 125→124):

Cor 14.12 完成を受け、その唯一の consumer であった Thm C conjunct 2 (type-`P₂` 分岐 `¬ N_G(U) ≤ M`、S16:811) を close。**Thm C は全 12 conjunct sorry-free + axiom-clean** (10/11/12 は cont.⁵ で既済、2 が最後の residual)。`#print axioms theoremC_paired_structure` = `[propext, Classical.choice, Quot.sound]`。

- **新 producer `typeP2_exists_matched_kappa_hall_pair` (S16, axiom-clean, AxiomsCheck 登録)**: type-`P₂` maximal `M` から **matched** な κ-Hall `K₀` + (κ∪σ)'-Hall `U₀` (`U₀` abelian, `U₀≠⊥`, `K₀ ≤ N_G(U₀)`) を構成。BG `kappa_complement` = Frobenius 補元 `E = K ⋉ U`、`U₀ = E₂E₃ ◁ E ∋ K₀=E₁`。**Cor 14.12 の `hKNU : K≤N(U)` 仮説を供給する reusable infra** (S16 `hP2II` / Prop 16.1 でも同 prerequisite が要)。
  - 退化ケース除外: `κ∩τ₃≠∅` または `E₂E₃=⊥` ⟹「`E` が κ-群」⟹ `κ = π∖σ` = type-`P₁` ⟹ `hP2` と矛盾 (新 S14 helper `kappa_eq_sigmaComplementPrimes_of_isPiGroup_card_E`)。
  - `E₁=κ-Hall` (`mem_kappa_of_mem_primeFactors_card_E1`)、`U₀=E₂E₃=[E:E₁]=(κ∪σ)'-Hall` (E₁ の index は κ' + E が σ'-群 ⟹ (κ∪σ)'; τ₂/τ₃ の prime content 不要、`hallPiece_isHall_in_M` 経由)、abelian は Lemma 15.1(b) (`typeP_hall_derived_eq_and_abelian` に `U₀` を渡す)。
- **conjunct 2 配線 (S16:811)**: 独立な `K,U` (Thm C 署名) では `K≤N(U)` が出ないため、**conjugacy-transport**: producer で matched `(K₀,U₀)` を作り Cor 14.12 を適用 → `¬(H⊓N_G(U₀)≤M)`; `U₀~U` (共に (κ∪σ)'-Hall, M-共役、`exists_conj_eq_of_isHall_subgroupOf`) で `N_G(U)≤M` を `N_G(U₀)≤M` へ transport (smul 代数 + `conj_smul_eq_self_of_mem_normalizer`/`mem_normalizer_of_conj_smul_eq_self`) し矛盾。option (b) [署名に `K≤N(U)` 追加] は consumer (S16:2112/2138, arbitrary K,U) を壊すため不採用。
- S14 helper 2本追加: `kappa_subset_sigmaComplementPrimes` (κ⊆π∖σ)、`kappa_eq_sigmaComplementPrimes_of_isPiGroup_card_E`。

**▶ 次 frontier (Prop 16.1 へ向けた残り)**: Thm C 完成で 5 deep theorems のうち **Thm C ✅ / Thm 15.2(a) ✅ (issue 8012)** が済。残り = **Thm A** residual (hFI = M' の TypeFData / hF_not_derived ✅) + **Lemma 15.1** (`typeP_auxiliary_structure_gated`, §15 土台) + **Thm 15.7** (`fitting_not_ti_cases`, type-F の `M'=F(M)` 一点に還元済 cont.⁵)。また **Prop 16.1 `hP2II` (S16:1236, `hKnorm` 仮説)** は今回の matched-pair producer で供給可能になった (要配線)。

---

**2026-06-23 ✅✅✅ BG Cor 14.12 (`typeP2_neighbor_is_typeF`) 完全完成 — sorry-free + axiom-clean** (commits `65194ead` conjunct 4 + shared infra / `05b8f119` conjunct 3、AxiomsCheck 登録、full build 3881 green、FT-path sorry 126→125):

cont.¹¹ の残 conjunct 3/4 を 2 commit で close。**Cor 14.12 全 4 conjunct (+H membership) 証明完了、`#print axioms` = `[propext, Classical.choice, Quot.sound]`** (上流 typeP_structure/typeP_duality/Lemma 14.11 等が全 sorry-free ゆえ sorryAx 漏れ無し)。

- **shared σ-decomposition infra** (conjunct 2 を `refine` 前に `hUMsH` として hoist; conjuncts 3/4 が `U ⊆ F(H)` を共有するため):
  - **`hHsFH : M_σ(H) ⊆ F(H)`** (Coq `sHsFH`): `H` type-`F` ⟹ `q ∉ κ(H) = ∅` (free!) ⟹ `msigma_structure_of_notMem_sigma_kappa` (Lemma 14.1, 既存 S14:1184) + 最大階数 elem abelian witness で `M_σ(H)` nilpotent → `nilpotent_normal_le_fitting`。**⚠ issue が flag した「`q∈τ₂(H)` gate」は不要だった** (type-F なら κ(H)=∅ で Lemma 14.1 の `q∉κ` が自明、Coq `notP1type_Msigma_nil` 経路)。
  - **`Fu := O_{(κ(M)∪σ(M))'}(F(H))`** + `U ≤ Fu` (`oPiCore_isHall_of_isNilpotent` + `isPiGroup_le_of_normal_isHallSubgroup`) + `Fu ◁ H` + **`defU : M ⊓ Fu = U`** (Hall 極大性、cardinality)。
  - 新 reusable helper `eq_of_isNilpotent_normalizer_inf_le` (`sylow_coe_eq_of_normalizer_inf_le` の一般化、`P` が Sylow でなく `N` nilpotent だけ要)。
- **conjunct 4 (`N_H(U) ⊄ M`)** (`65194ead`): `N_H(U) ≤ M` 仮定 → `N_Fu(U) ≤ M ⊓ Fu = U` → nilpotent `Fu` の normalizer condition で `Fu = U` → `H ≤ N(Fu) = N(U)` → `H ≤ M` → `H = M` (both maximal) vs `H ≁ M`。
- **conjunct 3 (`M ⊓ H = U ⊔ K`)** (`05b8f119`): `⊇` 自明; `⊆` = `M ⊓ H ⊆ N_M(U) = U ⊔ K`。3 piece:
  - **σ-decomp `M = M_σ ⊔ (U⊔K)`**: σ-Hall `M_σ`/κ-Hall `K`/(κ∪σ)'-Hall `U` が全素数を被覆 ⟹ `[M:join]` に素因子無し (各 `p` は担当 Hall の index 条件で排除) ⟹ index 1。
  - **`C_{M_σ}(U) = ⊥`** (Lemma 14.1): `R` (Sylow `r` of `U`, `r∈(κ∪σ)'`) は Sylow `r` of `M` (`pRank ↥R r = pRank ↥M r` via `pRank_sylow_eq`) ⟹ 最大階数 `A ≤ R ≤ U` で `M_σ ⊓ C(A)=⊥` → `C(U)` に lift。
  - **`defNMU : N_M(U) = U⊔K`** = BG 6.5(b) (`normalizer_eq_centralizerK_mul_normalizerU`) in `↥M`: `N(U) = (C(U)⊓M_σ)·(N(U)⊓(U⊔K))`、第1因子 `C_{M_σ}(U)=1` ⟹ `N_M(U) ≤ U⊔K`。geometric `M⊓H ⊆ N_M(U)` は `le_normalizer_inf` (`U=M⊓Fu`, `Fu◁H`)。

**▶ 次 frontier = Cor 14.12 を cite する下流**: BG Thm C (`theoremC_paired_structure` S16:620) の **conjunct 2 (`¬ N_G(U) ≤ M`, S16:668 sorry, `U≠⊥` の type-`P₂` 分岐)** が Cor 14.12 conjunct 4 そのもの (`¬(H⊓N_G(U)≤M)` ⟹ `¬(N_G(U)≤M)`)。**⚠ ただし即配線不可: Cor 14.12 は `hKNU : K ≤ N(U)` を仮定するが、Thm C は K (κ-Hall) と U ((κ∪σ)'-Hall) を独立に取る (hP/hKM/hK/hUM/hU/hM'eq) ため、K が U を normalize するとは限らない** — `K≤N(U)` (= `⁅U,K⁆≤U`) は BG `kappa_complement` で U,K が**同一 complement `E = U⋊K` (`U◁E`) から来る matched pair** だから成立する。Thm C の独立な U,K では (a) U を matched に取り直す (Thm C 内で kappa_complement を構成し U をそれに固定) か (b) Thm C 署名に `K≤N(U)` を追加するか、いずれか要。**∴ 次の上流タスク = `kappa_complement` producer (E=U⋊K, U◁E, K=κ-Hall, U=(κ∪σ)'-Hall を bundle) を建てて Thm C の U を固定 + Cor 14.12 cite で conjunct 2 解禁**。⚠ E-setup の κ/τ₁τ₃ overlap ゆえ U=E₂E₃ 同定が非自明。同 prerequisite が S16 `hP2II` (Prop 16.1) wiring でも必要 (S16:1236 が hKnorm を仮定として持つ → consumer 側が matched pair を供給する設計)。残 §15 foundation (Lemma 15.1 `typeP_auxiliary_structure_gated`) も依然上流。

---

**2026-06-22 (cont.¹¹) ✅ A(4)/A(5) を S16→S14 relocate + BG `defUK` (`typeP2_kappaHall_commutator_eq_self`) landed — Cor 14.12 conjunct 2/3/4 の lower-half 着手** (commits `1edf774a` relocate / `730a7049` defUK、full build 3881 green、sorry 数不変 = scaffold 追加):

lane-f RESUME。Cor 14.12 残 = conjunct 2/3/4 (σ-decomposition of `H`) で `S14:9518/9521/9524` の 3 sorry。Coq `P2type_signalizer` (BGsection14.v **L2243-2407**) を完全精読し proof map 確定 + lower-half の核を landed:

- **relocate (`1edf774a`)**: A(4) `typeP_hall_inf_centralizer_kappaElement_eq_bot` / A(5) `typeP_centralizer_kappaElement_eq` を S16→**S14** (Cor 14.12 直前)。S14 は下流 S16 を import 不可だが conjunct 2/3/4 が A(4) を要するため。S16 の consumer は `open S14` で無変更、axiom-clean 維持。
- **`defUK` (`730a7049`, sorry-free, axiom-clean, AxiomsCheck 登録)**: `⁅U,K⁆ = U`。`fitting_coprime_abelian_decomp` (P=U abelian, K≤N(U), coprime) の `U=(C(K)⊓U)⊔⁅U,K⁆` を `C_U(K)=C(K)⊓U=⊥` で collapse。後者 = A(4) を任意 `k∈K#` で (`C(K)⊓U ≤ C(k)⊓U = U⊓C(k) = ⊥`)。`IsCyclic K` は |K|=q prime (Prop 14.2(g)=`typeP_structure.2.2.2.2.1 hP2`)。

**▶ 残 (次セッション、全 API 解決済・straight 実装) = Coq L2291-2406 の翻訳**。証明骨格 (3 conjunct は `H∩M*=D` を共有する一塊):

**(I) 上半: K⊆F(D) → D⊆M*** (semiregular 不要):
- `hFmaxH : IsTypeF H` を refine 前に hoist (現 conjunct 1 inline 証明 = `(hcover H hHmax hHP).elim notMGH notMstGH` を `have` 化、Lemma 14.11 の `hF` 引数用)。
- **検証済コード (revert 済・貼り戻すだけ)** — `s'H_K` (K σ(H)'-群) + `D` (σ(H)'-Hall⊇K):
  ```lean
  haveI hHsol : IsSolvable ↥H := hG.solvable_of_mem_maximalSubgroups hHmax
  obtain ⟨-, -, -, -, hP2struct, -, -⟩ := typeP_structure hG hM hP hKM hK hKstardef hU
  obtain ⟨-, q, hqprime, hKcard, -⟩ := hP2struct hP2
  haveI : Fact q.Prime := ⟨hqprime⟩
  haveI hKcyc : IsCyclic ↥K := isCyclic_of_prime_card hKcard
  have hKelemq : K ∈ elemAbelianOfRank G q 1 :=
    mem_elemAbelianOfRank.mpr ⟨Subgroup.IsElementaryAbelian.of_card_prime hKcard, by rw [hKcard, pow_one]⟩
  have defUK : (⁅U, K⁆ : Subgroup G) = U :=
    typeP2_kappaHall_commutator_eq_self hG hM hP2 hKM hUM hK hKstardef hU hUab hKNU
  have hKMsigmaMst : K ≤ OddOrder.BG.Ch3.S10.Msigma Mst := hMstpair.2.2.le.trans inf_le_left
  have hHMstdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma H) (OddOrder.BG.Ch3.S10.sigma Mst) :=
    sigma_disjoint_of_nonconjugate hG hHmax hMstmax notMstGH
  have hsH_K : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma H)ᶜ K := by
    intro p hp; rw [Set.mem_compl_iff]; intro hpσH
    exact (Set.disjoint_left.mp hHMstdisj) hpσH
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mst p
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hKMsigmaMst) Nat.card_pos.ne' hp))
  obtain ⟨D, hDH, hDhall, hKD⟩ : ∃ D : Subgroup G, D ≤ H ∧
      Ch03.IsHallSubgroup ((OddOrder.BG.Ch3.S10.sigma H)ᶜ) (D.subgroupOf H) ∧ K ≤ D := by
    have hKsub : ∀ p ∈ (Nat.card ↥(K.subgroupOf H)).primeFactors, p ∈ (OddOrder.BG.Ch3.S10.sigma H)ᶜ := by
      intro p hp; rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv] at hp; exact hsH_K p hp
    obtain ⟨D', hD'hall, hD'ge⟩ := Ch03.hall_D (G := ↥H) hKsub
    have hDeq : (D'.map H.subtype).subgroupOf H = D' :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective D'
    refine ⟨D'.map H.subtype, Subgroup.map_subtype_le D', ?_, ?_⟩
    · rw [hDeq]; exact hD'hall
    · exact le_of_eq_of_le (Subgroup.map_subgroupOf_eq_of_le hKH).symm (Subgroup.map_mono hD'ge)
  ```
  ⚠ 上記 hoist 時は現 `refine ⟨H, hHmem, ...⟩` の**前**に置く。これ単体では未使用 warning (green) ゆえ未 commit。
- **`uniqMst : 𝓜(C(K))={Mst}`** (sK_FD 用): typeP_structure を **Mst** に適用 (Mst の κ-Hall=Kstar [hMstpair.2.1], Mst の dual="K"=`Msigma Mst⊓C(Kstar)` [hMstpair.2.2]) し **conjunct 6** (`.2.2.2.2.2.1`) を `p=q, X=K` (`hKelemq`, `le_rfl`) で。Mst の U は `Ch03.hall_D (G:=↥Mst) (U:=⊥, vacuous hyp `by simp`)` で構成→lift。
- **`sK_FD : K⊆F(D)`** = **Lemma 14.11 `exists_maximal_of_typeF_notMem_fitting` cite** (S14:8845)。引数: M↦H, E↦D, Q↦K (|K|=q prime ⟹ `hQ:K∈ℰ_q¹`=hKelemq), `hF`=hFmaxH, `hE:IsComplement' (Msigma H).subgroupOf H (D.subgroupOf H)` [D=σ(H)'-Hall が normal-Hall M_σ(H) を補完、要 API], `hEM`=hDH, `hq:q∈piSet D` [K≤D], `hQE`=hKD, `hQF`=¬sK_FD (contra)。出力 ∃M*' [(q∈τ₂ ∧ 𝓜(C(K))={M*'}) ∨ (q∈κ(M*') ∧ IsTypeP1 M*')]。矛盾: case1 uniqMst⟹M*'=Mst⟹q∈τ₂(Mst) vs q∈σ(Mst)[K≤Mst_σ]; case2 hcover(M*')⟹M*'~M[P1 vs P2 矛盾] or ~Mst[q∈κ vs q∈σ(Mst) 矛盾]。
- **`sDMst : D⊆Mst`** = K<|<|D (K⊆F(D)[sK_FD], F(D) nilpotent⟹K subnormal in F(D), F(D)◁D) → snK_sMst。**`snK_sMst : K<|<|L⟹L⊆Mst`** = subnormal 帰納 (`sK_uniqMst:K≤Mst^a⟹a∈Mst` 必要、`typeP_structure`(Mst) TI clause `.2.2.2.1` から)。⚠ 要 subnormal API (`Subgroup.IsSubnormal`, Isaacs Ch02 `isSubnormal_of_isNilpotent_finite` 等)。

**(II) 下半: U⊆H_σ** (= **conjunct 2**, semiregular=defUK 要):
- `sUHs : U⊆H_σ` (Coq L2334-2352): `H=H_σ⋊D` (sdprod_sigma, 要 σ-core 補元 API), `HsDq:=H_σ⊔O_q(D)`, H_σ は q'-Hall of HsDq (`coprime_mulGp_Hall`), K⊆HsDq (K q群⊆O_q(F(D)), 要 sK_FD), U=⁅U,K⁆⊆HsDq (defUK+commgSS), U は q'群 → `sub_normal_Hall` で U⊆H_σ。⚠ 要 API: σ-core sdprod, O_q-core, `coprime_mulGp_Hall`, `sub_Hall_pcore`, `sub_normal_Hall`。

**(III) 仕上げ: H∩M*=D → conjunct 3/4** (Coq L2362-2406):
- `sHsFH:H_σ⊆F(H)` (Fitting_max, type-F H で H_σ nilpotent), `defNMU:N_M(U)=E` (coprime_norm_cent + Ω₁(R)⊆U)。
- **`H∩M*=D`** = main equality (`sdprod_sigma` + Fitting-Hall; D≠H∩M* case は Thm 12.5(e) `Msigma_nilpotent_of_tau2` 系 + C_{H_σ}(K)≠1→q∈τ₂(H) 矛盾)。
- conjunct 3 (`M⊓H=U⊔K`): Fu=O_{(σ∪κ)'}(F(H)), U⊆Fu, M∩Fu=U (Hall) + defNMU。conjunct 4 (`N_H(U)⊄M`): N_H(U)≤M⟹H~M (eq_mmax + nilpotent_sub_norm) vs notMGH。

**解決済 API (grep 済)**: `Ch03.hall_D` (S03:1486, solvable Hall-superset) / `sigma_disjoint_of_nonconjugate` (S13_Theorem1310:159, Thm 13.9) / `Msigma_isPiGroup` (S10_HallStructureCore:227) / `fitting_coprime_abelian_decomp` (Isaacs Ch05:352) / `Msigma_isHall` (S10_HallStructure:584) / Lemma 14.11 (S14:8845)。

**★ de-risk 追補 (cont.¹¹ session 末、grep 確定)** — sK_FD の最大 gating だった `hE:IsComplement'` 構成が解消:
- **`D` は `exists_subgroupESetup_with_le hG hHmax hKH hsH_K'` で取得**（S12_Proposition1215:260; `hsH_K'`=hsH_K を IsPiSubgroup 形に）→ `⟨E,E₁,E₂,E₃,hsetup,hKE,hE_pi⟩`、**E⊇K かつ σ(H)'-Hall かつ補元内蔵**。これで自前 hall_D の D 構成は不要（E を D に使う）。
- **Lemma 14.11 の `hE` = `hsetup.isComplement'_subgroupOf`**（SubgroupESetup メソッド、Msigma-first 形 `(Msigma H).subgroupOf H).IsComplement' (E.subgroupOf H)`; S15_MF:608 が `.symm` で使用＝無印が Msigma-first）。`hEM`=`hsetup.E_le`。
- **σ-core sdprod (sUHs/H∩M* 用) も E-setup の `E_compl_inf`/`E_compl_sup` から**（`Msigma H ⊓ E=⊥`, `Msigma H ⊔ E=M`=H）。別途 sdprod_sigma API 不要。
- **subnormal (sDMst 用)** = `isSubnormal_of_isNilpotent_finite`（Isaacs Ch02_Subnormality/Main:94, nilpotent⟹subnormal）+ `Subgroup.IsSubnormal` の trans/Fitting API（同ファイル）。
- **残・要探索 API（sUHs HsDq）**: `O_q` pcore = `opiCoreInG`／`Subgroup.IsPiGroup.le_oPiCore`(Ch03:1713, q群⊆O_q)／`isPiSubgroup_le_of_normal_isHall`(S12_Theorem1212c:43)＋`isPiGroup_le_of_normal_isHallSubgroup`(S10_HallStructureCore:237, U q'群⊆H_σ)／`piGroup_le_opiCoreInG_of_nilpotent`(S12_Lemma128d:65)。`coprime_mulGp_Hall`(H_σ·O_q の q'-Hall) は未発見＝自前構成要。Thm 12.5(e)=`Msigma_nilpotent_of_tau2`(S12_Theorem125:101)。

**★★ 重大 re-scope (cont.¹¹ session 末、sK_FD 精査で判明 — 旧「straight 実装」評価を訂正)**: sK_FD の **case 2a (M*'∼M, IsTypeP1 M*')** の矛盾は `IsTypeP1 (conj a • M*') = IsTypeP1 M ⟹ M∈P1` を要し、これは **`kappa_conj_smul : kappa (conj a • M) = kappa M`（BG `kappaJ`）が必須**。だが **repo に kappa/IsTypeP1/tau1/tau3 の共役不変性は無い**（`sigma`/`Msigma` のみ private で存在）。case 2b/case 1 は `sigma_conj_smul_eq`+`tau2_subset_sigma_compl`+`kappa_subset_sigmaCompl` で足りる（共役不変は σ のみ）が、**case 2a だけ kappa_conj を要する**。
- **`kappa_conj_smul` は構築可能・~70-100行の独立 infra task**（次セッション最初の一手）。`tau1 M ∪ tau3 M = {p | p∉σ(M) ∧ pRank ↥M p=1}` ⟹ σ_conj + pRank_conj + (∃P 条件の) elemAbelian/Msigma/centralizer transport。**building blocks 全存在**: `sigma_conj_smul_eq`(S14:2620 priv)／`Msigma_conj_smul`(S14:2655 priv)／`pRank_eq_of_mulEquiv`(GroupTheory/MaximalSubgroupTypeConj:175)／`centralizer_pointwise_smul`(同:96)／`card_derivedInG_conj`(S12_Corollary1216:111 priv)。**要新規**: 共役 MulEquiv `↥(φ•M)≅↥M`、`elemAbelianOfRank` 共役不変、`pRank (φ•M) p = pRank M p`。`kappa_conj` 後 `isTypeP/P1/P2_conj_smul` は scp=π∖σ 共役不変から即。**置き場**: kappa は S14 だが tau1/tau3 は S12 — kappa_conj は S14 に置き tau13 部分は σ_conj+pRank_conj で直接（tau1/tau3 個別 conj 不要、∉σ∧rank1 で一括）。
- **∴ Cor 14.12 真の残務 = (a) `kappa_conj_smul` infra (~80行) → (b) sK_FD (uniqMst+Lemma14.11+case 分析) → (c) sDMst (subnormal) → (d) sUHs (HsDq, coprime_mulGp_Hall 自前) → (e) H∩M*=D+conjunct 3/4。~200-250 行、2 session 規模**（kappa_conj 分で上方修正）。

**✅✅ (a) `kappa_conj_smul` DONE (commit `e6bd440e`, sorry-free + axiom-clean, AxiomsCheck 登録)**: `kappa (conj g•M) = kappa M` + 系 `sigmaComplementPrimes/isTypeP/isTypeP1/isTypeP2_conj_smul`（全 S14）。一方向 (∀ a N) + 対称性。`MaximalSubgroupTypeConj` toolkit + 既存 `conj_smul_mem_elemAbelianOfRank`/`sigma_conj_smul_eq`/`Msigma_conj_smul` で構築（S14 に import 追加）。

**✅✅✅ (b) sK_FD + 上半 infra DONE (commit `cde460a4`, full build 3881)**: `typeP2_neighbor_is_typeF` の refine 前に shared σ-decomposition infra を hoist。**`hsK_FE : K ≤ F(E)`（Coq sK_FD）完成** = Lemma 14.11 (`exists_maximal_of_typeF_notMem_fitting`) を `hEsetup.isComplement'_subgroupOf` (E-setup の補元) で適用 → case 1 (`huniqMst`+`tau2_subset_sigma_compl`) / case 2a (`isTypeP1_conj_smul`+`not_isTypeP1_and_isTypeP2`) / case 2b (`kappa_conj_smul`+`kappa_subset_sigmaCompl`)。同時に hoist: `hFmaxH`(conjunct 1)/`q,hKcard,hKcyc,hKelemq`/`defUK`/`hKMsigmaMst`/`hsH_K`/E-setup `⟨E,E₁,E₂,E₃,hEsetup,hKE,hE_pi⟩`/`hqσMst`/`huniqMst`。conjunct 1 は `hFmaxH` で配線済。残 conjunct 2/3/4 = sorry。

**✅✅✅ (c) sUHs → conjunct 2 (`U ≤ Msigma H`) DONE (commit `00e05828`, full build 3881)**: HsDq machinery 完成。`HsDq := Msigma H ⊔ O_q(F(E))`; **HsDq◁H は quotient 不要**で `H=Msigma H⊔E≤N(HsDq)`（`M_σ(H)≤HsDq` + `E≤N(M_σ(H))⊓N(O_q(F(E)))` via `opiCoreInG_fittingInG_subgroupOf_normal`+`le_normalizer_sup`）。`U=⁅U,K⁆≤⁅H,HsDq⁆≤HsDq`（`commutator_le_of_le_normalizer`）、`M_σ(H)⊓O_q=⊥`⟹`M_σ(H)` は HsDq の normal {q}'-Hall（`[HsDq:M_σ(H)]=|O_q|` q-数、`card_sup_eq_mul_of_le_normalizer_of_disjoint`）⟹`isPiGroup_le_of_normal_isHallSubgroup`。+ refactor: `R`-char facts（hRcardU/hRUnorm/hPchar）を hKH から lift し `hUH:U≤H` 共有。**⟹ Cor 14.12 conjunct 1+2 完成、残 3/4。**

**▶ 次 = (d)(e) conjunct 3/4** = `H∩Mst=E`（main equality）共有の coupled chunk（~80行、Coq L2362-2406）:
- **`sDMst : E⊆Mst`** = `K<|<|E`（K⊆F(E)[hsK_FE]⟹K subnormal in nilpotent F(E)⟹subnormal in E）→ subnormal 帰納 `snK_sMst`（K<|<|L⟹L⊆Mst、`hsKuniq:K≤Mst^a⟹a∈Mst` を partner_inf_and_uniq から hoist 要、現 notMstGH 内 local）。
- **`sHsFH : H_σ⊆F(H)`** = `nilpotent_normal_le_fitting`（H_σ nilpotent normal; type-F で H_σ nilpotent、Coq は Fitting_max+sigma'_kappa'_facts）。
- **main equality `H∩Mst=E`** = `sdprod_sigma`(H=H_σ⋊E) + modular law + **wlog/Thm 12.5(e)**（`tau2_context` の Lean 等価未確定、`Msigma_nilpotent_of_tau2`(S12:101) 周辺; C_{H_σ}(K)≠1→q∈τ₂(H) 矛盾）。
- **conjunct 3 (`M⊓H=U⊔K`)**: `Fu:=O_{(σ∪κ)'}(F(H))`, `U⊆Fu`(sUHs⊆H_σ⊆F(H)+`sub_Hall_pcore`), `M⊓Fu=U`, `defNMU:N_M(U)=U⊔K`(coprime_norm_cent), `M's E=U⊔K`(K≤N(U) ゆえ U<*>K=U⊔K)。
- **conjunct 4 (`N_H(U)⊄M`)**: `N_H(U)≤M⟹H~M`(eq_mmax + nilpotent_sub_norm via Fu) vs notMGH。
- **要 API 確認**: `tau2_context` 等価, subnormal trans/Fitting (Isaacs Ch02), `sub_Hall_pcore`(`Subgroup.IsPiGroup.le_oPiCore` 在), `nilpotent_sub_norm`。**~80行、1.5 session。**

**★ conjuncts 3/4 精密 scope (session 末、Lean は末尾 2 clause [K⊆F(H∩Mst), σ(H)'-Hall] を省略ゆえ深い main equality [Thm 12.5e] は不要、Fu 構造のみ)**:
- **`sHsFH : H_σ ⊆ F(H)`** = `Msigma_nilpotent_of_tau2`(S12_Theorem125:101, 要 `q∈τ₂(H)` + `A∈ℰ_q²(H)`) → `nilpotent_normal_le_fitting`(Isaacs Ch01:904)。⚠ **gate: `q∈τ₂(H)` の確立に subtlety** — Lean `kappa` def(S14:121)は centralizer 条件 `M_σ(H)⊓C(X)≠⊥` を含むので、Coq t2Hq(`partition_pi_sigma_compl`+`FtypeP`)の直訳は `M_σ(H)⊓C(K)≠⊥` を要し非自明(`pRank ↥H q = 2` を別途示すか、Coq \kappa def との差異を解消)。**最初に解くべき gate**。
- **`defNMU : N_M(U) = U⊔K`** = ⚠ **`coprime_norm_cent`(coprime 作用 N=C)が repo に無い** — 要 locate/build。+ `Ω₁(R)⊆U`。conjunct 3 (`M⊓H=U⊔K`) の M⊓H⊆U⊔K 方向で使用。
- **`eq_mmax : 極大 H≤M ⟹ H=M`** = ⚠ 直接補題無し(coatom 一意性から ~5行で導出可、reusable infra として建てるとよい)。conjunct 4 (`¬(H⊓N(U)≤M)`) で使用。
- **Fu/defU**: `Fu:=opiCoreInG (σ∪κ)'ᶜ (F(H))` 的, `U⊆Fu`(U⊆H_σ⊆F(H)[sHsFH]+`Subgroup.IsPiGroup.le_oPiCore`), `M⊓Fu=U`(Hall), `Fu◁H`(char in F(H)◁H)。
- **conjunct 4** 追加: `lt_normalizer_of_isNilpotent_of_lt_top`(Isaacs Ch01:410, nilpotent_sub_norm) + Fu。**conjunct 4 は defNMU 不要**(sHsFH/Fu/defU/eq_mmax のみ)ゆえ conjunct 3 より先に着手可。
- `sDMst`(E⊆Mst, subnormal `K<|<|E`, `hsKuniq` を partner_inf_and_uniq から hoist)は **省略 2 clause 用**で Lean conjuncts 3/4 には不要。
- **着手順**: ① `q∈τ₂(H)` 解決 → sHsFH → Fu/defU → ② `eq_mmax` 建てる → conjunct 4 → ③ `coprime_norm_cent` 建てる → defNMU → conjunct 3。**~70行 + 2 helper(eq_mmax, coprime_norm_cent)、1.5 session。**

**(旧 sUHs plan、参考) HsDq machinery（DONE）**:
- 反転: `U ≤ Msigma H` ⟸ `isPiGroup_le_of_normal_isHallSubgroup` を **↥HsDq 内**で適用（`HsDq := Msigma H ⊔ Oq`, `Oq := opiCoreInG {q} (fittingInG E)`; `(Msigma H).subgroupOf HsDq` が normal {q}ᶜ-Hall, `U.subgroupOf HsDq` が {q}ᶜ-群）。
- `K ≤ Oq` = **`le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent`**(S08:460, K q-群 + `hsK_FE`(K≤F(E)) + F(E) nilpotent)。
- `Msigma H ⊓ Oq = ⊥`（σ(H) vs q∉σ(H) coprime）⟹ `|HsDq|=|Msigma H|·|Oq|`（`Subgroup.card_HK_mul_card_inf_eq_card_mul_card`）⟹ Msigma H は {q}ᶜ-Hall of HsDq（[HsDq:Msigma H]=|Oq| は q-数, Msigma H q'-群 ∵ q∉σ(H)）。
- `U ⊆ HsDq` = `U=⁅U,K⁆`(defUK) + K⊆Oq⊆HsDq + `U≤H` + `⁅H,HsDq⁆⊆HsDq` ∵ **`HsDq ◁ H`**（⛔ **最深: quotient 論法**。Coq: `HsDq/Msigma H = Oq·Msigma H/Msigma H ◁ H/Msigma H`、Oq=O_q(F(E))◁E≅H/Msigma H、pcore_normal+quotient_normal）。
- `U ≤ H`（Coq sUH）= R=O_r(U) char in abelian U + N(R)≤H（hNRH）。R-char は既存 hKH block 内 `hPchar` を再構成。
- `U {q}ᶜ-群` ∵ q∈κ(M)（hK.1）⟹ q∉π(U)（U は (κ∪σ)'-Hall）。
- **要 API 確認**: `opiCoreInG_fittingInG_subgroupOf_normal`(S08:429) や quotient normality (`Subgroup.Normal` の H/Msigma H ↔ E 翻訳) — HsDq◁H が唯一の非自明 gate。**(d) sDMst (subnormal) → (e) H∩M*=D + conjunct 3/4 は不変**。~120-150 行残。

**2026-06-22 (cont.¹⁰) ✅✅ BG Cor 14.12 conjunct 1 (`IsTypeF H`) 完全完成 — `notMstGH` close、sorry-free** (commit `81fba262`, full build 3881 green, FT-path sorry 133→132):

cont.⁹ の `notMstGH` 残務を 3 ピースで close。**conjunct 1 (`IsTypeF H`) は sorry-free** (covering `hcover` + `notMGH` + `notMstGH`):

- **新 private helper `partner_inf_and_uniq`** (S14, sorry-free): `typeP_structure` を partner `M*` に適用 (M* の κ-Hall = K*、`K = M*_σ ⊓ C(K*)`) し **両方を一発で**生成:
  - `ziMMst : M ⊓ M* = K ⊔ K*` (Coq `Ptype_embedding` の `ziMMst`): cyclic K* の characteristic order-p line で `b1` clause → `N_{M*}(K*) = K* ⊔ K`、`M_σ ⊓ M* = K*`(=cont.⁹ kernel) と合わせ `M ⊓ M* ⊆ N(K*) ⊓ M* = K⊔K*`。
  - `sK_uniqMst : K ≤ M*^a ⟹ a ∈ M*` (TI clause `.2.2.2.1`)。
- **署名に `hKNU : K ≤ N(U)` 追加** = BG `kappa_complement` の **`group_set (U*K)` 成分** (faithful・構成可能、consumer 0 ゆえ安全)。⟹ **`K ≤ H` (Coq `sEH`/`sKH`)**: `R = O_r(U)` は abelian `U` で characteristic (normal Sylow-r, `Sylow.characteristic_of_normal`)、`K ≤ N(U) ⟹ K ≤ N(R) ≤ H` (`mem_normalizer_map_subtype_of_characteristic`)。
- **`notMstGH`**: `H ~ M*` なら `K ≤ H` + `sK_uniqMst` で `H = M*` (`conj_smul_eq_self_of_mem`)、ゆえ `R ≤ M ⊓ M* = K⊔K*`; だが `r ∤ |K⊔K*| = |K|·|K*|` (`card_sup_eq_mul_of_le_normalizer_of_disjoint`, disjoint+commuting, `r ∉ κ∪σ`) かつ `r ∣ |R|`、矛盾。

**残 = conjunct 2/3/4 (σ-decomposition of H、相互依存)** — Coq `P2type_signalizer` L2302-2406 の完全 map (次セッション):
- **追加要仮説 `semiregular U K` (= `C_U(K) = U ⊓ C(K) = ⊥`、`regK`)** = kappa_complement の残り成分 (Prop 14.2 由来、現 `typeP_structure` 未露出)。`defUK : [U,K]=U` に必須。
- **upper (semiregular 不要)**: `s'H_K` (K は σ(H)'-群、`sigma_partition` + K⊆Mst_σ) → `D := σ(H)'-Hall(H) ⊇ K` (`Hall_superset`) → **`sK_FD : K ⊆ F(D)`** (**Lemma 14.11 `exists_maximal_of_typeF_notMem_fitting`✅DONE を cite** + uniqMst + defPmax で dichotomy 矛盾) → `sDMst : D ⊆ Mst` (subnormal `snK_sMst`: K<|<|L⟹L⊆Mst、要 sK_uniqMst + `nilpotent_subnormal`)。
- **lower (semiregular 要)**: `defUK : [U,K]=U` (`coprime_cent_prod` + `cent_semiregular`) → `sUHs : U ⊆ H_σ` (HsDq=H_σ·O_q(D) の q'-Hall、U=[U,K]⊆HsDq) → `defNMU : N_M(U)=E` (`coprime_norm_cent` + Ω₁(R)⊆U) → `sHsFH : H_σ ⊆ F(H)` (`Fitting_max`)。
- **main equality `H ∩ M* = D`** + Thm 12.5(e) (D≠H∩M* case: C_{H_σ}(K)≠1 → q∈τ₂(H) で矛盾)。⟹ conjunct 3 (`M⊓H=U⊔K`) + conjunct 4 (`N_H(U)⊄M` = **Thm C conjunct 2 の payload**)。
- 要確認 BG 補題: `sigma_partition`/`sigma'_kappa'_facts` (§10)、`coprime_cent_prod`/`coprime_norm_cent` の Lean 等価、subnormal API、Thm 12.5(e) の正確形 (S12_Theorem125)。**~250 行・多 sub-lemma、2-3 session 規模**。

**2026-06-22 (cont.⁹) ✅ BG Cor 14.12 — `msigma_inf_partner_eq_kstar` (M_σ ∩ M* = K*) 完成 = ziMMst kernel、conjunct-b 恐怖を解消** (commit `284d2854`, full build 3881 green, sorry 133):

ユーザー選択 (A) = ziMMst を建てる。**cont.⁸ で「ziMMst の `⊆` は embedding conjunct (d) で deep」と評価したが、kernel は conjunct (b) を回避できると判明・実証明した**:
- **`msigma_inf_partner_eq_kstar` (Coq `defMsMstar`, BG 14.7(d) kernel, sorry-free)**: `M_σ ⊓ M* = K*`。
  Coq の conjunct (d) 証明は conjunct (b) [`K*` は σ(M)-Hall of `M*`] 経由だが (Lean `typeP_duality` は (b) 未露出)、
  **新証明は (b) を完全回避**: `y ∈ M_σ ⊓ M*` に対し `⁅⟨y⟩,K⁆ ≤ M_σ` (`K≤M≤N(M_σ)`,`y∈M_σ`) ∧ `⁅⟨y⟩,K⁆ ≤ M*_σ`
  (`K≤M*_σ◁M*`,`y∈M*≤N(M*_σ)`) ⟹ `⁅⟨y⟩,K⁆ ≤ M_σ⊓M*_σ = ⊥` (Lemma 10.12 `disjoint_of_not_conj` +
  type-P2 で M_σ nilpotent) ⟹ `y∈C(K)` ⟹ `y∈M_σ⊓C(K)=K*`。`notMstGH` に wire 済 (`hMsMst` 確立)。
- ⟹ **ziMMst は feasible (deep でない)**。残 assembly は機械的:

**残 (notMstGH 完成への mapped 機械手順)**:
1. **`N_{M*}(K*) = Z`** (= K⊔K*): `⊇` (K*⊆N(K*), K⊆C(K*)⊆N(K*) ∵ Z cyclic abelian, Z⊆M*); `⊆`
   cyclic K* の characteristic order-p line X∈ℰ¹(K*) で `N(K*)⊆N(X)` (Lem14.11 の
   `characteristic_of_subgroup_of_isCyclic`+`mem_normalizer_map_subtype_of_characteristic` 流用)、
   `typeP_structure`(M*) conjunct b1 (`.2.2.1`: `N_G(X)⊓M* = K*⊔K`) で `N_{M*}(X)=Z` (要 U-Hall(M*) を
   `hall_E_exists` で構成、`typeP_partner_centralizer_singleton` のパターン)。~60行。
2. **`ziMMst : M ⊓ M* = K⊔K*`**: `M⊓M* ⊆ N(K*)` (hMsMst 経由: M⊓M* は M_σ と M* を normalize ⟹ M_σ∩M*=K* を
   normalize) ⟹ `M⊓M* = M⊓N_{M*}(K*) = M⊓Z = Z` (Z⊆M)。~20行。
3. **`sK_uniqMst`** (`K⊆M*^a ⟹ a∈M*`): `typeP_structure`(M*) の TI clause (`.2.2.2.1`) + K≠⊥。~30行。
4. **notMstGH 仕上げ**: H=M*^a ⟹ (sK_uniqMst) H=M* ⟹ R⊆M∩M*=Z、Z は {κ,σ}-群 (r∉κ(M)∪σ(M)) で
   r∤|Z| ⟹ R=⊥、R≠⊥ と矛盾。~40行。**閉じれば conjunct 1 (IsTypeF H) 完成**。

**2026-06-22 (cont.⁸) ▶ BG Cor 14.12 着手 — faithful statement + verified foundation + `notMGH` 完成** (commits `1cb13404` + `6934f97b`, full build 3881 green, FT-path sorry 130→133):

`typeP2_neighbor_is_typeF` (S14:9004) を着手。**完成済 (sorry-free, 検証済)**:
- **statement 拡張 (faithful, FT-path)**: 結論に **`¬ (H ⊓ N_G(U) ≤ M)`** (= BG `N_H(U) ⊄ M`) 追加 →
  `N_H(U) ≤ N_G(U)` で Thm C conjunct 2 (`N_G(U) ⊄ M`) を供給。署名に `hKM : K ≤ M` / `hUM : U ≤ M` /
  `hRU : R ≤ U` 追加 (BG-faithful; subgroupOf Hall は包含を含意しない)。consumer 0 ゆえ安全。BG の残 2 clause
  (`K ⊆ F(H∩M*)` / `σ(H)'-Hall(H∩M*)`) は M* を署名に出す要があり未 consume ゆえ省略 (proof は `H∩M*=D` を
  内部で立てるので導出可)。
- **foundation**: `r ∉ σ(M)` (`hrσM`, U が (κ∪σ)'-Hall) / `R ≠ ⊥` (`r∣|U|`,`r∤[U:R]`⟹`r∣|R|`) /
  dual partner `M*` を `typeP_duality` から抽出 (∃! unpack 検証) / witness `H ∈ 𝓜(N_G(R))` 構成
  (`N_G(R) < ⊤` via `R≤M`,`R≠⊥`,simple G)。
- **conjunct 1 (`IsTypeF H`)** を covering (`hcover`: 全 type-P maximal は M か M* に共役) 経由で
  非共役 2 本に還元 (assembly 証明済)。
- **✅ `notMGH : ¬ IsConjugateSubgroup H M` 完成** (sorry-free, ~50行): `H=M^a` ⟹ `|H|=|M|` ⟹
  R が H の Sylow_r ⟹ `r∈σ(H)` ⟹ (`sigma_conj`) `r∈σ(M)` 矛盾。**reusable sub-facts**:
  Hall {r}-subgroup card = r-part (`Nat.eq_pow_of_factorization_eq_single`+`factorization_mul`), `Sylow.ofCard`
  で `Sylow r ↥H` witness 構成。

**残 (次セッション、precise gap map)**:
- **`notMstGH : ¬ IsConjugateSubgroup H Mst`** ← **`ziMMst : M ∩ M* = K ⊔ K*`** が要 (R⊆M∩M*=Z,
  Z は {κ,σ}-群 r∤|Z| ⟹ R=⊥ 矛盾)。`⊇` は易 (K≤M⊓M*, K*≤M⊓M*) だが **`⊆` 方向は deep embedding fact で
  repo 未収載** (`family_inf_msigma_union_eq` は `(K⊔K*)⊓M_σ(N)` で別物)。+ `sK_uniqMst` (K⊆M*^a⟹a∈M*,
  Prop 14.2(d) TI for M*, `typeP_structure` を M* に適用すれば出る) も要。**notMstGH が閉じれば conjunct 1 完了**。
- **conjunct 2/3/4 (analytic)**: `defUK : [U,K]=U` ← **`semiregular U K` (BG regK)** が要だが **現 Prop 14.2
  (`typeP_structure`) は regK/semidirect 構造を露出していない** (Coq `kappa_compl_context` が Ptype_structure
  から取る; Lean では Prop 14.2 拡張 or 別 lemma が要)。`commutator_eq_self_of_frobenius_DK` (S15:6073) は
  FPF 条件があれば使える。`sUHs : U⊆H_σ` ← sdprod_sigma + pcore Hall。`defNMU : N_M(U)=E` ← coprime_norm_cent。
  `sHsFH : H_σ⊆F(H)` ← Fitting_max。**`H∩M*=D`** = main equality (sdprod_sigma + Fitting-Hall)。
- **新規発見の prerequisite 2 件**: (1) `ziMMst` (M∩M*=Z, ⊆ deep), (2) `semiregular U K` (Prop 14.2 拡張)。

**2026-06-22 (cont.⁷) ▶ NEXT = BG Cor 14.12 (`typeP2_neighbor_is_typeF`) で Thm C conjunct 2 を閉じる — Coq `P2type_signalizer` (BGsection14.v:2240) 精読で proof map 確定**:
Thm C conjunct 2 (`N_G(U)⊄M`, S16:773 の type-P2 residual) = Cor 14.12 の `N_H(U)⊄M` clause (N_H(U)≤N_G(U) ゆえ ⟹ N_G(U)⊄M)。現状 `typeP2_neighbor_is_typeF` (S14:9001) は **conclusion に `N_H(U)⊄M` を含まず sorry** — 結論を BG full (`N_H(U)⊄M ∧ K⊆F(H∩M*) ∧ σ(H)'-Hall(H∩M*)`) に拡張 + 全証明が要る。**~160行の多段証明** (Coq P2type_signalizer 翻訳):
- **setup**: `Ptype_embedding` (=typeP_duality) で M*=Mst + `uniqMst : 𝓜(C(K))={Mst}` (Prop 14.2(d))。`q:=|K|` prime (Prop 14.2(g))。
- **`sK_uniqMst`**: `K⊆Mst^a ⟹ a∈Mst` (uniqueness, Prop 14.2(d) の `tiK_MstG`)。
- **`snK_sMst`** (subnormal 帰納, ~8 Coq 行): `K<|<|L ⟹ L⊆Mst`。
- **`sEH`**: E⊆H (R=O_r(U), N(R)⊆H, gFnorm_trans)。`sUH/sKH`: U,K⊆H。
- **`notMGH`/`notMstGH`**: H≁M (r∈σ(H) vs r∉σ(M)) / H≁Mst (R∩=coprime TI 矛盾)。**`FmaxH`: H∈𝓜_F** (defPmax = Thm 14.7(g))。
- **`s'H_K`**: K は σ(H)'-群 (`sigma_partition`)。`D`:= σ(H)'-Hall(H) ⊇K (`Hall_superset`)。
- **`sK_FD`: K⊆F(D)** — ⊄F(D) なら **Lemma 14.11 (`exists_maximal_of_typeF_notMem_fitting`, ✅DONE)** で H* dichotomy → `uniqMst`/`defPmax`/q∈σ(Mst) で矛盾。**← ここで Lemma 14.11 を cite**。
- **`sDMst`: D⊆Mst** (`nilpotent_subnormal (Fitting_nil D) sK_FD` → snK_sMst)。
- **`defUK`: [U,K]=U** (`coprime_cent_prod` + `cent_semiregular regK`, C_U(K)=1)。
- **`sUHs`: U⊆H_σ** (U=[U,K]⊆O_q(D)·H_σ, q^'-Hall 議論, sdprod_sigma)。
- **最終**: `M⊓H=U⊔K`, `N_H(U)⊄M` (Lemma 14.1 `N_M(U)=UK`, H_σ⊆F(H))。`D≠H∩M*` ケース: C_{H_σ}(K)≠1 → q∈τ₂(H) → **Thm 12.5(e)** (`Msigma_nilpotent_of_tau2` 系) で H_σ∩M*=1 矛盾。
- **要確認補題**: Thm 12.5(e) の正確な形 (S12_Theorem125), `coprime_cent_prod`/`semiregular` の Lean 等価, subnormal API (`Subgroup.Subnormal`?), `sigma_partition`。
- ⟹ **大きい fresh-session タスク**。bottom-up helper (snK_sMst / FmaxH / sK_FD / sUHs) で分割推奨。署名拡張 (`N_H(U)⊄M` 追加) も要。

**2026-06-22 (cont.⁶) ✅✅✅ BG Lemma 14.11 COMPLETE — `exists_maximal_of_typeF_notMem_fitting` sorry-free + axiom-clean** (`dc4c9055` + AxiomsCheck `6c562aa0`, full build 3881 green, FT-path sorry **131→130**):
S8-S13 assembly 完結。**cont.⁵ で「残 gate」と誤判定した `C_{M*_σ}(Q)≠⊥` は resolvable だった** — MathComp `BGsection14.v` の `primes_non_Fitting_Ftype` (Coq Lemma 14.11) 精読で確定: **A は σ(M*)-subgroup ゆえ `A≤M*_σ`** (`sigma_subgroup_le_Msigma_of_isHall`; M*_σ は normal Hall σ-subgroup で全 σ-subgroup を含む — O_σ が任意 p-subgroup を含まないという私の懸念は誤り)、よって `C_{M*_σ}(Q)⊇A₁=A⊓C(Q)≠⊥`。
- **assembly 鍵補題**: L=cyclic K' の order-p line (`characteristic_of_subgroup_of_isCyclic`+`mem_normalizer_map_subtype_of_characteristic` で M≤N(L)) / A E-normal (`elemAb_normal_in_E_of_tau2`) / index `q|[E:C_E(A)]` (`prime_dvd_index_of_sylow_not_le_of_normal`, Q⊄C(A) は ⁅A,Q⁆≠⊥ から直接) / Cor 12.9 で A₁∈ℰ_p¹ / Lemma 12.11 / τ₂(M*)=Cor 14.3 `maximalContaining_centralizer_eq_singleton_of_tau2_element` / κ(M*)=witness Q + ¬P2 (typeP_structure conj5 で σ=β、p∈σ\β と矛盾)。
- 署名に `hEM : E ≤ M` 追加。**全 3 補題 (main + bundle + A-choice) を AxiomsCheck 登録**。
- **▶ unblocks**: Cor 14.12 (`typeP2_neighbor_is_typeF`, S14:8614 の deferred `N_H(U)⊄M` clause) → **Thm C conjunct 2** → Prop 16.1。次 = Cor 14.12 で Lemma 14.11 を cite して `N_H(U)⊄M` を実証明 (issue 7007 「やること」conjunct 2)。

**2026-06-22 (cont.⁵) ✅ BG Lemma 14.11 — FPF bundle + A-choice landed (4 commits) — assembly は全補題特定済、残 gate = `C_{M*_σ}(Q)≠⊥`**
(lane-f, commits `6cf7d246`/`ab96c39d`/`5642817d`/`13132807`, full build 3881 green):

実装済 infrastructure (全 sorry-free):
- **S5 helper** `Q_le_fittingInG_of_commutator_centralizesQ` (`6cf7d246`)
- **K' bundle (FPF 込)** `exists_typeF_complement_cyclic_commutator` (`5642817d`): K'=⁅⁅E,Q⁆,Q⁆ ≤E,
  ≠⊥, cyclic, ≤C(M_σ), M≤N(K'), π(K')⊆τ₂, **C_{K'}(Q)=⊥** (FPF: `commutator_commutator_right_eq_of_le_normalizer`
  で ⁅K',Q⁆=K' + `Isaacs.Ch05.fitting_coprime_abelian_decomp`)
- **A-choice** `exists_elemAb_rank_two_le_E_containing_line` (`13132807`): L◁M order-p (p∈τ₂)、L≤E ⟹
  ∃A∈ℰ_p²(E), L≤A。BG Lemma 10.5 (`pRank_eq_two_of_normalizer_le`, N_G(L)=M 経由) + Hall 共役
  (`exists_conj_smul_le_hallPiece`、L は M-invariant で固定)。**Sylow/pRank bookkeeping 回避**。

**残 main assembly (`exists_maximal_of_typeF_notMem_fitting`) — 全補題特定済、機械実装 ~150行**:
1. **署名に `hEM : E ≤ M` 追加**（`esetup_of_isComplement` 要求）。
2. **L 構成**: K' から order-p 元 `a`、`L:=zpowers a`。`L.subgroupOf K'` は **cyclic 部分群ゆえ characteristic**
   (`characteristic_of_subgroup_of_isCyclic`) → `M≤N(K')⟹M≤N(L)` (`mem_normalizer_map_subtype_of_characteristic`)。
   `⁅L,Q⁆≠⊥`: `L⊓C(Q)≤K'⊓C(Q)=C_{K'}(Q)=⊥` (FPF) ⟹ L⊄C(Q)。L∈ℰ_p¹。
3. **A-choice 適用** → A∈ℰ_p²(E), L≤A。`⁅A,Q⁆≠⊥` (⊇⁅L,Q⁆≠⊥, `commutator_mono`)。
4. **Cor 12.9** `commutator_decomp_of_tau1_action` (要 q∈τ₁ M = phase 1, hCQ): A₀=⁅A,Q⁆∈ℰ_p¹/≤A/
   =A⊓C(M_σ)/M≤N(A₀); ¬∃g conj g•A₀=A₁; A₁=A⊓C(Q)∈ℰ_p¹/≤A/¬(C(A₁)≤M)。
5. **index `q|[E:C_E(A)]`**: **Q⊄C(A₀)** = ¬conj 節 (Q≤C(A₀)⟹A₀≤A⊓C(Q)=A₁⟹A₀=A₁[both ℰ_p¹]⟹g=1 矛盾)。
   E≤N(A₀)(M≤N(A₀))、C_E(A₀)◁E、Q⊓C_E(A₀)=⊥(q 素数) ⟹ `card_dvd_of_injective` で q|[E:C_E(A₀)];
   C_E(A)≤C_E(A₀) (A⊇A₀) ⟹ `index_dvd_of_le` で [E:C_E(A₀)]|[E:C_E(A)] ⟹ q|[E:C_E(A)]。
6. **M*∈𝓜(N_G(A))** (N_G(A)<⊤ ∵ A⊄◁simple G; maximalSubgroupsContaining 非空)。
7. **Lemma 12.11** `tau2_transfer_to_maximal`: conjunct1 p∈σ(M*)\β(M*); conjunct2 (q∈index 経由)
   **q∈τ₁(M*)∪τ₂(M*)**。case split:
   - **q∈τ₂(M*)**: Cor 12.10(e) (`nilpotent_sigmaComplement_abelian.2.2.2.2.2` for M*、要 M*-E-setup) で
     𝓜(C_G(Q))={M*} (Or.inl)。
   - **q∈τ₁(M*)**: q∈κ(M*) (witness Q, C_{M*_σ}(Q)≠⊥) + σ(M*)≠β(M*)→¬P2→IsTypeP1 M* (Or.inr)。

**⛔ 残 gate (両 case 共通) = `C_{M*_σ}(Q) = M*_σ⊓C(Q) ≠ ⊥`** (BG「C_{M*_γ}(Q)⊇C_A(Q)=A₁⊃1」):
要 **A₁≤M*_σ**。A₁=A⊓C(Q)∈ℰ_p¹, A₁≤A≤M*, p∈σ(M*)。だが p-部分群 A₁ が O_σ(M*)=M*_σ に入るのは
**一般に非自明**（O_σ は normal σ-core）。BG の根拠（Lemma 12.11 の σ-theory 内部構造、A≤M*_σ か A₁ の
M*-positioning）は**未再構成 = 真の残 math gate**。Lemma 12.11 proof / §12 σ-theory の精読要。これが解ければ
両 case の witness が出て assembly 完結。**次セッションの最優先 = この gate の解明**（infrastructure は全完備）。

**2026-06-22 (cont.⁴) ✅ BG Lemma 14.11 S5 helper + S4-S7 (τ₂(M)≠∅) landed — S8-S13 完全再構成**
(lane-f, commits `6cf7d246` + `ab96c39d`, leaf build green):

- **S5 helper** `Q_le_fittingInG_of_commutator_centralizesQ` (S14, private, sorry-free): `Q≤E` abelian,
  `⁅E,Q⁆` abelian, `⁅E,Q⁆≤C_G(Q)` (= 退化ケース `⁅⁅E,Q⁆,Q⁆=1`) ⟹ 正規閉包 `Q⊔⁅E,Q⁆` が abelian かつ
  E-normal ⟹ `Q≤F(E)`。**E-normality は commutator の sup-distribution を回避**: 「`⁅x,e⁆∈Q⊔R` を満たす
  `x` の集合」を部分群として構成 (`⁅a*b,e⁆=a*⁅b,e⁆*a⁻¹*⁅a,e⁆` を `group` で)、生成元 `Q`,`R=⁅E,Q⁆` を含む
  ⟹ `E≤N(Q⊔R)`。abelian は `centralizer_sup_eq` + `R≤C_G(Q)`、最後に `nilpotent_normal_le_fitting` を `↥E` で。
- **S4-S7** `exists_mem_tau2_of_typeF_complement` (S14, sorry-free): Lemma 14.11 の仮説下で `τ₂(M)≠∅`。
  `K:=⁅E,Q⁆` abelian (Cor 12.10(b) `.2.1.2`)・q'群 (≤`derivedInG M`, `tau1_not_mem_derived_primeFactors`)・
  σ'群 (≤E, `mem_tau_union_of_mem_primeFactors`)、`Q≤N(K)⊓M` → **Prop 10.11(d)**
  `sigma_complement_commutator_cyclic_normal` で `K':=⁅K,Q⁆` cyclic・≤`C_G(M_σ)`・`M≤N(K')`。
  `K'≠⊥` = S5 helper (`K'=⊥⟹⁅E,Q⁆≤C_G(Q)⟹Q≤F(E)` 矛盾)。`p∈π(K')⟹p∈τ₂`: 否なら `p∈τ₁∪τ₃` で
  `r_p=1`、line `A∈ℰ_p¹` of `K'≤C_G(M_σ)` が `C_{M_σ}(A)=M_σ≠1` (Lemma 14.1 `msigma_structure_of_notMem_sigma_kappa` 矛盾)。

**残 = S8-S13 (M* 二分律) — 数学完全再構成済 (次セッション straight 実装 ~300行)**:
1. **coprime FPF `C_{K'}(Q)=⊥`**: `K=⁅E,Q⁆` は `E` で normal、`Q` と coprime (K q'群)。`↥E` 内で
   `commutator_commutator_right_eq (K.subgroupOf E) (Q.subgroupOf E) [Normal] (coprime)` (要 `[IsSolvable ↥E]`)
   → `⁅K,Q⁆=⁅⁅K,Q⁆,Q⁆` i.e. `K'=⁅K',Q⁆`。coprime 分解 `K'=C_{K'}(Q)×⁅K',Q⁆`
   (`fitting_coprime_abelian_decomp`, Cor 12.9 で既使用) + `⁅K',Q⁆=K'` ⟹ `|C_{K'}(Q)|=1` ⟹ `C_{K'}(Q)=⊥`。
2. **`L:=Ω₁(K'_p)`** (p∈π(K'), K' cyclic ゆえ p-part も cyclic): order p, `≤C_G(M_σ)`, `M≤N(L)`
   (K'_p char in cyclic K' → `M≤N(K')` 経由、Ω₁ char)。`C_{K'}(Q)=⊥⟹C_L(Q)=⊥⟹⁅L,Q⁆=L≠⊥` (coprime on L)。
3. **A 選択** `A∈ℰ_p²(E)` with `L≤A` ⟹ `⁅A,Q⁆⊇⁅L,Q⁆=L≠⊥`:
   - **nonabelian Sylow_p(E)**: `exists_canonical_line_of_nonabelianSylow` (S12_Theorem127:325) が `A∈ℰ_p²`+canonical
     line `A₀` + **universal property `∀W, M≤N(W)∧IsPGroup p W∧W≤M ⟹ W≤A₀`**。`L` は `M≤N(L)`/p群/≤M ⟹ `L≤A₀≤A`。
   - **abelian Sylow_p(E)**: `A:=Ω₁(Sylow_p(E))∈ℰ_p²` (rank 2)、`L≤Sylow_p` ⟹ `L=Ω₁(L)≤A`。
4. **`⁅A,Q⁆≠⊥` → `q|[E:C_E(A)]`** (✅ **subtlety RESOLVED via A₀**): `Q⊄C_E(A)` だけでは不十分 (A は E-normal でない)
   が、**A₀:=⁅A,Q⁆ は M-normal** (`M≤N(A₀)` = Cor 12.9 `commutator_decomp_of_tau1_action` の `.1.2.2.2`、E≤M ゆえ
   `E≤N(A₀)`) ゆえ A₀ で index 議論が回る:
   - `Q⊄C_E(A₀)`: `⁅A₀,Q⁆=⁅⁅A,Q⁆,Q⁆=⁅A,Q⁆=A₀≠⊥` (coprime 恒等式 `commutator_commutator_right_eq` を A (p群, Q-coprime)
     に、A∈ℰ_p² が E で normal 要 — または A₀∈ℰ_p¹ order p で `Q≤C(A₀)⟹⁅A₀,Q⁆=⊥` 矛盾を直接)。
   - `E≤N(A₀)` + `Q⊄C_E(A₀)` + `|Q|=q` 素数 ⟹ `Q⊓C_E(A₀)=⊥` ⟹ `|C_E(A₀)|_q<|E|_q` (A₀ E-normal ゆえ Sylow_q 議論
     が回る: `|C_E(A₀)|_q=|E|_q` なら Sylow_q(E)≤C_E(A₀)、E-conj で全 Sylow_q≤C_E(A₀^e)=C_E(A₀)、Q≤C_E(A₀) 矛盾)
     ⟹ `q|[E:C_E(A₀)]`。
   - `C_E(A)≤C_E(A₀)` (A⊇A₀) ⟹ `[E:C_E(A₀)] | [E:C_E(A)]` (tower) ⟹ **`q|[E:C_E(A)]`**。✅
   - Cor 12.9 は `hAQ:⁅A,Q⁆≠⊥` を要求 (step 3 で確立); 同時に `A₀=A⊓C(M_σ)`/`A₁=A⊓C(Q)∈ℰ_p¹`/`C_G(A₁)⊄M` も供給
     (κ(M*) case や TI に再利用可)。**∴ S8-S13 の数学ギャップは全て閉じた**。実装は abelian/nonabelian Sylow_p(E)
     の A-choice 場合分け (step 3) が主な分量。
5. **Lemma 12.11** `tau2_transfer_to_maximal` (M*∈𝓜(N_G(A))): conjunct 1 `p∈σ(M*)−β(M*)`、conjunct 2
   `q∈τ₁(M*)∪τ₂(M*)`。case `q∈τ₂(M*)`: Cor 12.10(e) (`nilpotent_sigmaComplement_abelian.2.2.2.2.2`,
   要 x∈M# with orderOf-primes⊆τ₂ ∧ M_σ⊓C(x)≠⊥ — Q の生成元で) → `𝓜(C_G(Q))={M*}` (Or.inl)。
   case `q∈τ₁(M*)`: `q∈κ(M*)` (witness Q, `C_{M*_σ}(Q)⊇C_A(Q)≠1`) + `σ(M*)≠β(M*)` (p∈σ−β) → ¬P2 →
   `IsTypeP1 M*` (`typeP_structure` conjunct 5 の対偶 + `isTypeP_iff_isTypeP1_or_isTypeP2`) (Or.inr)。
- **署名修正要**: main theorem `exists_maximal_of_typeF_notMem_fitting` に `hEM : E ≤ M` を追加 (現 `IsComplement'`
  だけでは E≤M 不導出、`esetup_of_isComplement` が要求)。BG「E is a complement of M_σ in M」に忠実、downstream
  Cor 14.12 は D=H∩M*≤H で供給。

**2026-06-22 (cont.³) ▶ BG Lemma 14.11 着手 — 依存閉包を全解決 + phase 1 (`q∈τ₁ ∧ C_{M_σ}(Q)=1`) landed**:
`exists_maximal_of_typeF_notMem_fitting` (S14_TypePCounting:8473, sorry) は Thm C conjunct 2
(`N_G(U)⊄M`=Cor 14.12) と Prop 16.1 の `hP2II` 両方の linchpin (TypeIIData.normalizer_not_le)。
**「§13 gated」は STALE** — 実依存は §12/§10/§14 で全 landed (Workflow `wf_136774bc-e30` で監査確定)。

- **de-privatize `subgroupESetup_of_complement`** (S12_Proposition1215:170 `private`→public): 与えられた
  `M_σ`-補元 `E` 上に E-setup を張る (`exists_subgroupESetup_with_le` は別 `E'` を作り `Q⊄F(E)` を
  運べないので、与えられた `E` 上に張る必要)。
- **landed helpers** (S14_TypePCounting, Lemma 14.11 直前, 全 build-green):
  `esetup_of_isComplement` (IsComplement'→E-setup) / `typeF_complement_q_notMem_tau2` (S1, Cor 12.6(a)
  `elemAb_normal_in_E_of_tau2` + `le_fittingInG_of_normal_isPiSubgroup_singleton`) /
  `typeF_complement_q_notMem_tau3` (S2, `E3_le_fittingInG` + `isPiGroup_le_of_normal_isHallSubgroup`) /
  `typeF_complement_q_tau1_and_centralizer` (S3 τ-partition `mem_tau_union_of_mem_primeFactors` + gap C:
  κ(M)=∅ で `C_{M_σ}(Q)=1`)。

**残 (S4-S13) = 全 lemma 名解決済、次セッションは straight 実装**:
- **S4-S7 (τ₂(M)≠∅)**: `K:=⁅E,Q⁆` は abelian (`⁅E,Q⁆≤derivedInG E`, Cor 12.10(b)
  `nilpotent_sigmaComplement_abelian` の `.2.1.2`) かつ `q'`-群 (`≤derivedInG M`, `q∈τ₁⟹q∉π(M')` =
  `tau1_not_mem_derived_primeFactors`)。`Q≤N(K)` = `subgroup_le_normalizer_commutator_self E Q` ∘ `hQE`。
  `C_{M_σ}(Q)=1` (phase 1) で **Prop 10.11(d) `sigma_complement_commutator_cyclic_normal`** を lemma-K=`⁅E,Q⁆`,
  P=Q で適用 → `K':=⁅⁅E,Q⁆,Q⁆` cyclic normal, `≤C(M_σ)`, `M≤N(K')`。**`K'≠⊥`**: 反対なら
  `⁅E,Q⁆≤C(Q)` (`commutator_eq_bot_iff_le_centralizer`) → `Q^E=Q⊔⁅E,Q⁆` abelian normal → `≤fittingInG E`
  (`nilpotent_normal_le_fitting`) → `Q⊆F(E)` 矛盾。**`π(K')⊆τ₂`**: `K'≤C(M_σ)` で `M_σ⊓C(K')=M_σ≠⊥`、
  各 `p∈π(K')` に `typeP_hall_small_subgroup_cyclic_tau2` の Part-A (S14:2461-2490) を port
  (`p∉τ₂⟹r_p=1⟹`Lemma 14.1 `msigma_structure_of_notMem_sigma_kappa` antitone 矛盾)。注: ⁅E,Q⁆=⁅⁅E,Q⁆,Q⁆
  の Frattini 恒等式は **不要** (A₀=K 同定は BG の注記のみで存在結論に未使用)。
- **S8-S13 (M* 二分律)**: `p∈τ₂`, `A∈ℰ_p²(E)` (`exists_elemAb_rank_two_le_E_of_tau2`)、`⁅A,Q⁆≠⊥`
  (Q⊄C_E(A); A∈ℰ_p², Q∈ℰ_q¹ p≠q)。**Cor 12.9 `commutator_decomp_of_tau1_action`** (hp hq hA hAE hQ hQE hCQ hAQ)
  → `A₀=⁅A,Q⁆=A⊓C(M_σ)` (M≤N(A₀)) + `A₁=A⊓C(Q)`, `C_G(A₁)⊄M`。`M*∈𝓜(N_G(A))` (maximalSubgroupsContaining
  存在)。**Lemma 12.11 `tau2_transfer_to_maximal`** → `.1`: p∈σ(M*)∖β(M*); `.2.1`: q∈τ₁(M*)∪τ₂(M*)
  (q∈π([E:C_E(A)]), Q⊄C_E(A) より)。case q∈τ₂(M*): Cor 12.10(e) (`nilpotent_sigmaComplement_abelian.2.2.2.2.2`)
  → `𝓜(C_G(Q))={M*}` (Or.inl)。case q∈τ₁(M*): `q∈κ(M*)` (witness Q, C_{M*_σ}(Q)⊇C_A(Q)≠⊥) + σ(M*)≠β(M*)
  → ¬P2 → `IsTypeP1 M*` (typeP_structure conjunct 5 + `isTypeP_iff_isTypeP1_or_isTypeP2`) (Or.inr)。

**2026-06-22 (cont.²) ✅✅✅ Thm C conjunct 10 (BG C(9) `A0-A` TI) 完全完成 — sorry-free + axiom-clean** (`491bdd3d`, full build 3881 green):
- 構造的包含 `a0_minus_a_subset_conj_zTilde` を **完全に証明** (前 commit `d553f1e0` の residual を充足)。`#print axioms` = 標準3公理のみ。AxiomsCheck 登録 (transport 補題と共に)。
- **Helper A** (κ'-元 ∈ M'): `M'` が Hall κ-部分群 `K` を補完 (`typeP_duality.symm.index_eq_card` で `[M:M']=|K|` κ-数) → `↥M⧸M'` での像の位数が `[M:M']` と `orderOf x` (κ'-数) を割る → 1 → `x∈M'`。quotient-order 論法。
- **Helper B** (`M'⊓(K⊔K*)=K*`): `K` が `K⊔K*` で normal (K*≤C(K))、`K⊓M'=⊥` (補完の disjoint) → `le_centralizerFactor_of_le_sup_of_le_Msigma` と同型の `mem_sup_of_normal_left` 分解で `x=a·b`, `a∈K⊓M'=⊥`, `x=b∈K*`。
- 知見: `IsComplement'.index_eq_card` は `K.index=card H` 方向 (要 `.symm`); `subgroupOf` の inf 分配は elementwise (`Subtype.ext_iff`) が安全; `le_normalizer_derivedInG` + `normal_subgroupOf_of_le_normalizer` で `(derivedInG M).subgroupOf M` normal。
- ⟹ **Thm C 残 = conjunct 2 (Cor 14.12 `N_G(U)⊄M`) のみ** (Lemma 14.11 sorry に gated、最深)。

**2026-06-22 (cont.) ✅ Thm C conjunct 10 (BG C(9) `A0-A` TI) を構造的包含一点に還元 + 数学的完全再構成** (`d553f1e0`, full build 3881 green):
- **再利用可能な TI-transport 補題** `IsTISubset.of_subset_conj_of_isTISubset` (TISubset.lean、純群論、`Mathlib.Tactic.Group` import 追加): `T` が TI (normalizer `Z≤M`) かつ `A` の各元が `T` の元に `M`-共役 ⟹ `A` は TI (normalizer `M`)。BG Theorem B(5) (`A(M)-M_σ` TI) にも使える。
- **conjunct 10 を還元**: `theoremC_paired_structure` の conjunct 10 を transport 補題 + `typeP_duality` の Ẑ-TI (`hMstarP.2.2.2.2.2.1`、`N_G(Ẑ)=K⊔K*≤M`) で discharge。残 = 構造的包含 `a0_minus_a_subset_conj_zTilde` (S16, sorry) のみ。
- **✅✅ 構造的包含の数学的証明を完全再構成** (docstring に記載、要 Lean 化):
  - `a ∈ A0-A` = `a∈M`, `M_σ⊓C_G(a)≠1`, `a∉𝒞_G(K#)`, `a∉U M_σ`。κ/κ'-分解 `a=a_κ·a_{κ'}` (`exists_isPiElement_mul`、可換、a の冪)。
  - `a_κ` を Hall-共役で `K` 内へ (`exists_conj_smul_le_isHall_kappa`、`⟨a_κ⟩` は κ-部分群)。`w∈M`、`b:=waw⁻¹=b_κ b_{κ'}`、`b_κ∈K`。
  - `a_κ≠1`: 否なら `a=a_{κ'}` は κ'-元 ⟹ `a∈M'=U⊔M_σ` (下記補題) で `a∉U M_σ` と矛盾。
  - `b_{κ'}≠1`: 否なら `a` が `b_κ∈K#` に `G`-共役 ⟹ `a∈𝒞_G(K#)` 矛盾。
  - **`b_{κ'}∈K*` (簡略化済・linchpin)**: `b_{κ'}∈M'` (κ'-元), `b_{κ'}` は `b_κ` と可換。`C_{M'}(b_κ)=M'⊓C_M(b_κ)=M'⊓(K⊔K*)=K*`。最後の等号は **直接集合計算** (`x=k k*∈M'`, `k*∈K*≤M'` ⟹ `k=x(k*)⁻¹∈M'`, `k∈K⊓M'=1`, `x=k*∈K*`)。**⚠ 旧計画の「K normalizes U + U⋊M_σ 分解」は不要** — `M'⊓(K⊔K*)=K*` で直接。
  - 組立: `b=b_κ b_{κ'}∈K·K*` 両非自明 ⟹ `b∈Z-(K∪K*)=Ẑ`。`a=w⁻¹ b w`、`m=w⁻¹∈M`、`t=b`。
- **残る唯一の実質補題 = 「M の κ'-元 ∈ M'=U⊔M_σ」** (coprime-index): `M'=derivedInG M` (Thm C(3) `typeP_hall_derived_eq_and_abelian.1`) ◁ M, `[M:M']=|K|` (κ-数)。κ'-元 `x` の `M/M'` 内 image の位数は `orderOf x` (κ'-数) と `[M:M']` (κ-数) を割る ⟹ 1 ⟹ `x∈M'`。~60-100 行。+ `M'⊓(K⊔K*)=K*` 集合計算 ~30 行 + 組立。**全 sorry-free 化可能、次の単位**。
- 既存材料: Thm A(5) `typeP_centralizer_kappaElement_eq` (`M⊓C(k)=K⊔K*`)、`exists_conj_smul_le_isHall_kappa`、`exists_isPiElement_mul`、`card_kappaHall_ne_one`。

**2026-06-22 ✅✅✅ BG Thm 15.7 `fitting_not_ti_cases` 完全完成 — type-F の `M'≤F(M)` residual close、sorry-free + axiom-clean** (`549511d7`, full build 3881 green, 実 sorry 134→133):
- 前セッションで (c) を faithful な `M'≤F(M)` に弱め (overstatement 判明)、唯一残っていた **type-F の `M'≤F(M)`** sorry を close。`=F(M)` gate (`C_Y(E₁)=1`) が消えたので **ungated**。
- 証明は **type 非依存** (旧 type-P1-only 証明を包含、`rcases ha` 場合分けは `≤` 方向には spurious だったので削除):
  - §12 E-setup `M=M_σ⋊E` (`exists_subgroupESetup`) ⟹ `M'=M_σ⊔E'` (`derivedInG_eq_Msigma_sup_derivedInG_complement`)
  - Lemma 12.19 (`derivedE_centralizes_betaComplement`) で Hall β'-部分群 `W≤M_σ` (E' が中心化) を取得。`π(M_σ)=π(M_F)` は `β(M)` と disjoint (`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`、M_F=M_σ) ゆえ M_σ は β'-群 → index `[M_σ:W]=1` → `W=M_σ` → `E'≤C_G(M_σ)`
  - `M_σ≤F(M)` (M_σ=M_F nilpotent normal) + `E'≤C_G(M_σ)⊓M≤F(M)` (`fitting_decomposition`: `F(M)=(C_M(M_F)⊓M)⊔M_F`) ⟹ `M'=M_σ⊔E'≤F(M)`
- **`#print axioms` = `[propext, Classical.choice, Quot.sound]`** (sorryAx 無し)。`fittingIsTI_of_isTypeP2` と共に AxiomsCheck 登録 (回帰保護)。
- ⟹ **5 deep 定理のうち Lemma 15.1 / Thm 15.2(a) / Thm 15.7 / Cor 15.5 が全完了**。残 = **Thm C conjunct 2 (N(U)⊄M=Cor 14.12) / conjunct 10 (A0-A TI=Thm A(3)(5)+Prop 14.2(d))** + **Prop 16.1 配線**。

**2026-06-21 (cont.) ✅✅ BG Thm 15.7(a) `fittingIsTI_of_isTypeP2` 完成 → Thm C conjunct 11 close (10/12) + 15.7 を (c) 残のみに** (`dc2fe378` + `7eeb933b`, full build 3881 green, sorry 136→135):
- **`fittingIsTI_of_isTypeP2` (S15, BG Thm 15.7 conjunct (a), mmd L4244)**: type-P2 maximal ⟹ FittingIsTI。
  証明 = landed §15 piece のみ: `¬FittingIsTI ⟹ MF=Mσ` (`mf_eq_msigma_of_not_fittingIsTI`) + `π(MF)∩β=∅`
  (`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`)、type-P2 は σ=β (Prop 14.2(g))、Mσ≠⊥ で q∈π(Mσ)=π(MF)⊆σ=β、
  disjoint と矛盾。sorry-free declaration (既存 `fitting_decomposition` sorryAx を transitively 保持、新規導入なし)。
- **Thm C conjunct 11 完全 close**: `U≠⊥→IsTypeP2` (`isTypeP2_of_hall_subgroupOf_ne_bot`) + |K| prime (Prop 14.2)
  + FittingIsTI (本補題)。⟹ **Thm C は 10/12 conjunct 実証明**、残 = conjunct 2 (N(U)⊄M=Cor 14.12)/10 (A0-A TI=Thm A(3)(5)) のみ。
- **`fitting_not_ti_cases` (フル 15.7) も (a)+(b) wire 済** (`7eeb933b`): (a)=本補題の対偶+F/P1/P2 三分律、(b)=`mf_eq_msigma_of_not_fittingIsTI`。
  残 sorry = (c)-(e) のみ (cyclic X=X₁∈Mσ / M'=F(M) / O_p(M) 非可換・Lem 10.13(b) / 三 local case = deep §15)。
- 15.7(a) は Prop 16.1 の hP1eqV/hVP1 にも再利用可 (型分類 reverse 方向)。**次 = Thm C conjunct 2/10、または 15.7(c)、または Cor 14.12**。

**2026-06-21 (lane F resume) ✅ Thm C `theoremC_paired_structure` 9/12 conjunct discharge + faithfulness 修正 2 件** (`8f636b54` + `ec711630`, full build 3881 green):
- TypePData de-contradiction (issue 7008, `0530f90c`) で lane unblock → Thm C 着手。Thm C は full sorry の scaffold だったが **9/12 conjunct を landed §14/§15 補題から実証明**:
  - conjunct 1,7 (U abelian, M'=U⊔M_σ) ← `typeP_hall_derived_eq_and_abelian` (Lem 15.1(b))
  - conjunct 3,4,5,6,8 (K*≠⊥/cyclic/≤M_F/≤M''/¬cyclic M_F) ← `typeP_kstar_in_mf` (Cor 15.6)
  - conjunct 9 (∃! M*) ← `typeP_duality` (Thm 14.7)
  - conjunct 12 (U=⊥→|K*| prime) ← `kstar_card_prime_of_inputs` (要 `kappa_eq_sigmaComplementPrimes_of_hall_subgroupOf_eq_bot` を Thm C 前へ hoist)
- **faithfulness 修正 2 件** (lane-internal、caller=`theoremII_tame_embedding{,_of_inputs}` のみ、3 定理に伝播):
  1. **署名に `hKM : K ≤ M`, `hUM : U ≤ M` 追加** — `subgroupOf M` Hall 条件は K,U⊆M を含意せず、conjunct 7 (M'=U⊔M_σ) は U⊄M で偽。BG は K,U が M の Hall factor (M=KUM_σ)。
  2. **`∃! M*` を `typeP_duality` の強い述語に強化** — 旧 scaffold の弱い述語 (maximal∧typeP∧¬conj∧(P2 M∨P2 M*)) は partner M* の全 G-共役が満たす (N_G(M*)=M*⊊G) ゆえ **∃! が literally false**。強い述語は dual Hall datum (K*≤M*, K=M*_σ⊓C(K*)) で M* を pin。caller は TI conjunct のみ projection ゆえ安全。
- **残 residual = genuinely-deep 3 conjunct のみ**: conjunct 2 (N(U)⊄M = Cor 14.12)、conjunct 10 (A0(M)-A(M) TI = Thm A(3)(5)+Prop 14.2(d))、conjunct 11 (U≠⊥→|K|prime∧F(M) TI = Thm C(10)=Prop 14.2(g)+Thm 15.7(a))。これらは standalone 補題未 landed。
- sorry 134→136 (1 opaque sorry を 9 conjunct 実証明 + 3 named residual に itemize、+ 2 bug fix)。進捗は sorry 数でなく実証明で測る ([[scaffold-sorry-free-not-done]])。
- **次**: Thm C residual (conjunct 2/10/11) は §16 Theorems A-E と連動の deep construction。または Thm A faithful (`theoremA_maximal_structure_faithful` 既 sorry-free) を活用した hard input 方向、Prop 16.1 wire。

**2026-06-19 (cont.³) ✅✅ BG Lemma 15.1 完全完成 — conjunct 4 + gated lemma wire DONE**:
- `3d240069`: **conjunct 4 (15.1(e)) COMPLETE** — τ₂ **nonabelian** sub-case 着地で `typeP_hall_frobenius_factor`
  全 sorry-free (K=⊥ / K≠⊥ τ₁∪τ₃ / τ₂ abelian / τ₂ nonabelian すべて)。nonabelian: Lemma 10.13
  (`nonabelian_pSubgroup_rankTwo_elemAbelian_structure`) で `C_{S'}(A)=A₀⊔Z` (Z cyclic) を取得、
  S'⊇Sylow_p(U) で C_{S'}(A)=Sylow_p(U)、Z regular は clause (c)、exp Z=exp SUG は not-cyclic 論法。
  新規 infra: `open scoped IsMulCommutative` (CommGroup 導出)。
- `7337cdf2`: **`typeP_auxiliary_structure_gated` wire DONE** — 4 conjunct standalone lemma の直接 4-tuple、
  sorry-free。BG Lemma 15.1 の §14-gated 構造内容が全 proven。
- sorry count 136→134 (merge 後)。**Lemma 15.1 は Thm A/C/TypePData の土台 — 完成で §16 endpoint へ前進**。
- **次 = Thm 15.2(a) `mf_ne_msigma_typeP1_structure` (S15) / Thm 15.7 `fitting_not_ti_cases` / Thm A / Thm C / Prop 16.1 wire**。


**2026-06-19 conjunct 4 (BG 15.1(e)) — K=⊥ DONE + K≠⊥ engine/packaging DONE, kernel isolated**:
- `06278a11`: K=⊥ branch (type F) of `typeP_hall_frobenius_factor` (Thm 12.12(b))。sorry-free。
- `49e1a380`: K≠⊥ の **assembly 層を全て sorry-free 化** + kernel を最小 per-prime 補題へ隔離:
  - `isFrobeniusGroup_of_regular_le_maximal` (sorry-free): `isFrobeniusGroup_of_regular` の E-setup-free
    一般化 (`U0≤M` + `M_σ⊓U0=⊥` + regularity を直接取る)。
  - `frobenius_factor_of_regular_components` (sorry-free): U abelian + per-prime regular component
    `Z_p` から `U0=⊔Z_p` (exp U0=exp U, U0M_σ Frobenius) を組む engine。
  - `typeP_hall_regular_component_at_prime` (**唯一の残 sorry**): p∣|U| → regular p-component Z_p≤Sylow_p(U)
    of full p-exponent。`typeP_hall_frobenius_factor` 自体は sorry-free (engine+helper に委譲)。
  - K≠⊥ branch = `M_σ⊓U=⊥` (coprimality) + engine 適用。**sorry count 不変** (K≠⊥ の sorry が
    最小 per-prime helper へ relocate)。full build 3862 green。
- `2f34b0a0`: **linchpin 確立 + τ1∪τ3 case DONE**。`exists_subgroupESetup_with_le hG hM hUM hUpi`
  (S12_Proposition1215:283) で **U≤E の E-setup** を取得 (U は σ'-subgroup ゆえ)。τ1∪τ3 (p∉τ2 ⟹
  r_p=1, `hsetup.pRank_M_le_two` の rank≤2 から): Z=Sylow_p(U) を G へ push、`factorization_exponent_le_of_sylow`
  + Lemma 14.1 (K=⊥ と同じ discharge)。**残 = τ2 case のみ** (helper の唯一 sorry)。
- **τ2 route 確定 (次の一手、~1 session)**: U-localization の conjugacy 罠は
  **S:=Sylow_p(U) を full G-Sylow として使う**ことで回避 (`exists_cyclic_Enormal_regular_of_abelianSylow`
  は `Z ≤ (S:Subgroup G)` を返す ⟹ S=Sylow_p(U) なら Z≤Sylow_p(U)≤U 直接)。要:
  - **hreg** (τ1∪τ3 regularity on E、K=⊥ パターン再利用、~30行)。
  - **full-Sylow-in-G fact (abelian)**: A=Ω₁(Sylow_p(U))∈ℰ_p²、S':Sylow p G⊇A、S' abelian ⟹
    S'≤C_G(A)≤E≤M (`centralizer_le_E_of_tau2`)、|S'|≤(card M).fact p=(card U).fact p=|Sylow_p(U)| ⟹
    |Sylow_p(U)|=(card G).fact p (full G-Sylow)。`Sylow.ofCard SU` で S:Sylow p G 化、適用。
  - **nonabelian sub-case**: Sylow_p(U)=C_S(A)=A₀×Z (Thm 12.7, mmd 3237)、Z=regular cyclic factor。
    既存 Lean `frobFact_of_nonabelianSylow` は FrobFactConclusion を返すゆえ per-prime Z 抽出は別途要 (harder)。

**2026-06-19 (cont.²) τ₂ abelian DONE — 残 sorry = nonabelian τ₂ のみ (1 本)**:
- `49e1a380`→`54b01ba0` で engine+packaging+τ1∪τ3+linchpin+**τ2 abelian** すべて proven。新 infra:
  `isFrobeniusGroup_of_regular_le_maximal` / `frobenius_factor_of_regular_components` (S15 sorry-free)
  + `exists_regular_cyclic_in_abelianSylow_tau2` (S12_Theorem1212b, hreg/hCES-free CES_eq variant —
  E=KU では hreg 偽 [κ⊆τ1∪τ3] かつ C_E(S)≠E ゆえ両 hyp 落とした) + de-private rank-2 constructor。
- **nonabelian τ₂ precise plan (next, ~60-100 行)**: `exists_canonical_line_of_nonabelianSylow`
  (S12_Theorem127:325) が A₀ (order p, centralizes M_σ) + **clause (c)** (non-A₀ line X∈ℰ_p¹(E) は
  M_σ⊓C(X)=⊥) 供給。要 = cyclic Z≤Sylow_p(U) of full exponent with Ω₁(Z)≠A₀ (⟹ (c) で regular)。
  abelian 構造: Sylow_p(U)=A₀×Z (A₀ direct factor ⟺ A₀⊄℧¹(Sylow_p(U)))、max-order cyclic の
  Ω₁=L_char≠A₀ (a>b) / 任意 non-A₀ line (a=b)。cyclic Z' は既存 lemma 未露出
  (`exists_complement_of_canonical_line` S12_Theorem127d:163 は E 内 complement E₀、cyclic Z' でない)
  ⟹ Sylow_p(U) 上で A₀×Z 分解 or agemo-with-(c)-line を再構成要。

- **kernel の shared linchpin (確定)**: τ1∪τ3 (partition coverage `pRank_M_le_two` で r_p=1) も
  τ2 (regular cyclic machinery) も **両方とも type-P M の E-setup with U≤E を要求**。`pRank_M_le_two`
  (S12_ECore:267) と `mem_tau_union_of_mem_primeFactors` (S12_ECore:295) は E-setup メソッド、τ2 機械
  (`exists_cyclic_Enormal_regular_of_CES_eq` 等) も E-setup 取る。⟹ **次の一手 = type-P M の E-setup
  (E=KU σ-complement, U≤E) を構成** (`subgroupESetup_of_complement` S12_Proposition1215:194 は private、
  M=KUM_σ から M_σ⊓KU=⊥ ∧ M_σ⊔KU=M を示し E=KU で適用、または de-private wrapper)。これが linchpin。

**2026-06-19 conjunct 1 (BG Lemma 15.1(b)) DONE** (`cab5603a`): standalone clean lemma
`typeP_hall_derived_eq_and_abelian` (S15_MF.lean, `typeP_auxiliary_structure_gated` 直前) =
`K≠⊥ → M'=U⊔M_σ ∧ IsMulCommutative U`。sorry-free + axiom-clean、full build 3862 green。
+ helper `card_mul_card_mul_card_eq_of_three_hall` (|M|=|K||U||M_σ| 三 Hall 分割)。
証明: `typeP_duality`(clean) で M' complements K + coprime → M_σ≤M' / U≤M'(|U| coprime [M:M']=|K|)
→ 三 Hall card で |U⊔M_σ|=|M'| → M'=U⊔M_σ。U abelian = `[U,U]≤[M',M']≤M_σ`(`derivedDerived_le_Msigma`)
∧ `[U,U]≤U` → `[U,U]≤U⊓M_σ=⊥`。**sorry count 不変 (139)** — gated 定理に wire するのは conjunct 2-4 着地後。

**conjunct 2-4 の依存状況 (2026-06-19 精査確定)**:
- conjunct 2 (BG 15.1(c) C_G(X) funnel + X cyclic τ2): **全ピース available** ⟹ reachable。
  - Thm 12.5(d) (rank-2 A の `Mσ⊓C(A)=⊥`) = **`Msigma_nilpotent_of_tau2`** (S14:~1275 で使用、`.2.2.2.1`)
  - Lemma 14.1 (rank-1, p∉σ∪κ の `Mσ⊓C(A)=⊥`) = **`msigma_structure_of_notMem_sigma_kappa`** (S14:1183)
  - Cor 14.3 funnel (τ2-element → 𝓜(C_G(x))={M}) = **`maximalContaining_centralizer_eq_singleton_of_tau2_element`** (S14:2199)
  - Cor 12.10(b) (E' abelian) = **`nilpotent_sigmaComplement_abelian hG h`** の `.2.1.2` (`IsMulCommutative (derivedInG E)`)
  → conjunct 2 を background subagent に委譲 (2026-06-19, S14 に standalone lemma `typeP_hall_small_subgroup_cyclic_tau2`)。
- **✅ 訂正 (2026-06-19): Thm 12.12 は形式化済み — conjunct 3,4 も reachable**:
  前の「Thm 12.12 未形式化」は **誤ディレクトリ grep の false alarm** (`Ch3_Uniqueness/` を見ていたが §12 は
  **`OddOrder/BG/Ch3_MaximalSubgroups/`** に在る)。Thm 12.12 = `S12_Theorem1212{,b,c}.lean`、**全 sorry-free**。
  結論述語 `FrobFactConclusion M E` (S12_Theorem1212:35) = (a)∃ abelian normal A₀≤E, E≤N(A₀), ∀x∈Mσ#,
  E⊓C(x)≤A₀; (b)∃ E₀≤E, exp E₀=exp E, Mσ⊔E₀ Frobenius kernel Mσ。producer: `frobFact_of_regular_all`
  (S12_Theorem1212:182, hyp=∀e∈E# Mσ⊓C(e)=⊥) / `frobFact_of_nonabelianSylow`(:414) / `frobFact_of_abelianSylow`
  (S12_Theorem1212c:394)。**まだ §14/§15 から consume されていない** (要 wire)。
  - conjunct 3 (BG 15.1(d) `IsMulCommutative (centralizerGeneratedBySigma M U)`): **K≠⊥ = conjunct 1** (U abelian
    ⟹ `centralizerGeneratedBySigma ≤ U` abelian)。**K=⊥ = Thm 12.12(a)**: κ=∅ ⟹ E=U、A₀ abelian で
    `centralizerGeneratedBySigma = sSup{U⊓C(x)} ≤ A₀` ⟹ abelian。
  - conjunct 4 (BG 15.1(e) `U≠⊥ → ∃U0…Frobenius U0Mσ`): **K=⊥ = Thm 12.12(b)** (E=U, U0=E₀)。
    **K≠⊥ (type P2) = 別議論** (BG 4178「easy C_E(S)=E case」; type-P で U が Mσ に FPF 作用 →
    `isFrobeniusGroup_of_regular` で U0=U。`Msigma_centralizer_E23_eq_bot_of_caseTau1` 系の FPF 補題要確認)。
  - ⟹ **Lemma 15.1 の 4 conjunct 全て reachable**。Thm 12.12 を wire すれば gated 定理が組め count 139→138。
    onion の底は Thm 12.12 で、それは既に床が張られていた。

## やること

- [x] Lemma 15.1 conjunct 1 (BG 15.1(b)) = `typeP_hall_derived_eq_and_abelian` ✅ `cab5603a`
- [x] conjunct 2 (BG 15.1(c)) = `typeP_hall_small_subgroup_cyclic_tau2` ✅ `e11e3028`
- [x] BG Thm 12.12 形式化確認 — ✅ 既存 sorry-free (`frobenius_factorization_of_regular` S12_Theorem1212c:520)
- [x] conjunct 3 (BG 15.1(d)) = `typeP_centralizerGeneratedBySigma_isMulCommutative` ✅ `80aa03cf`
- [~] **conjunct 4 (BG 15.1(e))** `typeP_hall_frobenius_factor` (S15_MF:1007) `U≠⊥ → ∃U0≤U, exp U0=exp U, Mσ⊔U0 Frobenius kernel Mσ`:
  - **✅ K=⊥ branch (type F) DONE + committed** (`06278a11`, 2026-06-19): E=U setup
    (`subgroupESetup_of_isHall_kappa_eq_bot`) + `frobenius_factorization_of_regular` part (b) (U0=E₀)。
    hreg discharge は conjunct 3 と同型 (Lemma 14.1 `msigma_structure_of_notMem_sigma_kappa`)。sorry-free。
  - **⬜ K≠⊥ branch (type P2) = 残 kernel** (2026-06-19 **完全再スコープ**, BG 原文 + §12 machinery 精読):
    - **訂正 1 — assembly は CLEAN (U abelian)**: U0=⊔_{p∈π(U)} Z_p。U abelian ⟹ `card_finsetSup_eq_prod`/
      `mem_Z_of_orderOf_prime_mem` (S12_Theorem1212c:102/138, H=U) の normalizer 条件 `U≤N(Z_p)` が**自動**。
      exp は `exponent_eq_of_forall_factorization_le` (S12_Theorem1212:90, E-setup 不要)。regularity は
      `inf_centralizer_eq_bot_of_forall_prime_order` で素数位数還元 → 各 prime-order 元は `mem_Z_of_orderOf_prime_mem`
      で Z_r 内 → Z_r の regularity。Frobenius packaging は `isFrobeniusGroup_of_regular` (S12_Theorem1212:119)
      の **E-setup-free 一般化** (proof は h を mem_maximal/E_le/E_compl_inf でしか使わず U0≤M + Mσ⊓U0=⊥ で代替可)。
    - **訂正 2 — BG「easy C_E(S)=E」の意味**: BG 4178「(e) is obvious from the easy C_E(S)=E argument」=
      U abelian ⟹ C_U(Sylow_p(U))=U 自動 ⟹ Thm 12.12 の C_E(S)=E 易枝に常に居る。`exists_cyclic_Enormal_regular_of_CES_eq`
      (S12_Theorem1212b:1044) がこの枝。**但し S:Sylow p G with S≤M を要求** = full-Sylow-in-G fact。
    - **訂正 3 — nonabelian は full-Sylow-in-G が FAILS だが Z_p は依然存在**: Thm 12.7 proof (mmd 3227)
      `P=C_S(A)=Sylow_p(M) ⊊ S=Sylow_p(G)` ⟹ M は full G-Sylow を含まない。だが `P=A₀×Z` (mmd 3237,
      A₀ order p centralizes Mσ=非regular, Z cyclic regular) ⟹ **Z_p=Z** が regular cyclic of full exponent
      (A₀ は exp p で exp を上げない)。Thm 12.7(d) `frobFact_of_nonabelianSylow` (S12_Theorem1212:414) が供給源。
    - **正スコープ (確定)**: ① sorry-free engine `frobenius_factor_of_regular_components` (assembly + 一般化
      Frobenius packaging, 上記訂正 1 の通り、~100 行) + ② per-prime witness の discharge: τ1∪τ3 (Z_p=Sylow_p(U)
      cyclic, Lemma 14.1 で regular, inline 易) / **τ2 = 唯一の hard kernel** (abelian: full-Sylow-in-G fact
      `S=Sylow_p(U)≤M` 確立 → CES_eq; nonabelian: Thm 12.7 から Z 抽出)。**τ2 kernel = ~1 session の深い §12 work**。
    - **prior 530-line 失敗の死因 = abelian only に簡略化し circular** (訂正 3 が示す通り nonabelian は別構造で回避要)。
      σ-template = `exists_sylow_le_of_mem_sigma` (S10:536)、`centralizer_le_E_of_tau2` (full-Sylow abelian 枝)。
- [ ] conjunct 1-4 を `typeP_auxiliary_structure_gated` に wire (sorry 139→138)
- [ ] Thm 15.2(a) `mf_ne_msigma_typeP1_structure` (S15:1144)
- [x] **Thm 15.7 `fitting_not_ti_cases` 完全完成** (`549511d7`, 2026-06-22): type-F の `M'≤F(M)` residual を close、**sorry-free + axiom-clean** (AxiomsCheck 登録)。type 非依存証明で旧 type-P1-only を包含。詳細 = 上記進捗ログ 2026-06-22。↓ 以下は (c) overstatement 発見の経緯記録 (resolved):
- [~] Thm 15.7 `fitting_not_ti_cases` — **✅✅✅ 2026-06-22 重大発見: BG 印刷版 conjunct (c) `M'=F(M)` は overstatement、faithful 版は `M'≤F(M)`** (ChatGPT GPT-5 Pro 相談 + MathComp 検証で確定):
  - **等式 `M'=F(M)` は type-F で `C_Y(E₁)=1` (E₁ が τ₂-Fitting 因子 Y=O_σ'(F(M)) 上 FPF) 一点に等価** (lane-f 独立検証) で、引用補題 (12.1/12.6/12.12/15.1/15.5) から**導出不能** (Cor 12.6(d) は E₃=1 で vacuous、他は Mσ 作用で Y でない)。私の旧診断「C_E(Mσ)=1 (Frobenius)」は過剰 — 正しい等価は弱い `C_Y(E₁)=1` (C_E(H)=E')。
  - **authoritative MathComp odd-order 形式化 (`theories/BGsection15.v`/`nonTI_Fitting_structure`) が conjunct (c) を `M^'(1) ⊆ 'F(M)` (包含, L944) ∧ `Mσ × O_σ('F(M)) = 'F(M)` と形式化、等式でない** → BG 印刷版が overstatement と確定。**形式化者コメント (L916-922) が smoking gun**: "We had to change the statement ... the first equality of part (c) does not appear to be valid ... only the inclusion M' ⊆ F(M) seems to be needed" (= C_Y(E₁)≠1 機序)。**curl で一次ソース独立検証済** (workflow `wddw8y3qt`; ChatGPT が付けた source「Ethiopian digital library」は偽だったが MathComp の事実は本物 — 再 cite 時は一次ソース参照)。詳細 `notes/bg/s15_7_typeF_chatgpt_prompt.md`。
  - ⟹ **Lean statement を `≤` に弱める faithfulness 修正** (Theorem C ∃! と同種、`fitting_not_ti_cases` consumer ゼロゆえ安全)。(a)=`fittingIsTI_of_isTypeP2`+三分律 / (b)=`mf_eq_msigma_of_not_fittingIsTI` / ∃X+prime+disjunct 全 discharge / **M'≤F(M) type-P1 case 実証明** (M'=Mσ via Lem15.1b U=⊥ + Mσ=MF nilpotent)。
  - **残 = type-F の M'≤F(M) のみ・now ungated** (C_Y(E₁)=1 gate 消滅): `exists_subgroupESetup` (一般 M) → M'=Mσ⊔E' (`derivedInG_eq_Msigma_sup_derivedInG_complement`) → E'≤C(Mσ) (Lem 12.19 `derivedE_centralizes_betaComplement` + W=Mσ [π(Mσ)∩β=∅]) → E'≤C_G(Mσ)⊓M≤F(M) (`fitting_decomposition` F=(C⊔MF)) + Mσ≤F(M) ⟹ sup_le。**M' nilpotent 経由不要**、crux = W=Mσ の Hall plumbing のみ
- [ ] Thm A `theoremA_maximal_structure` (S16:144) — Lemma 15.1 + Prop 14.2 + §15 で全 conjunct
- [~] Thm C `theoremC_paired_structure` — **11/12 conjunct DONE** (conjunct 10 = BG C(9) `A0-A` TI を `491bdd3d` で完全証明、残 = conjunct 2 (Cor 14.12) のみ)。旧: 10/12 + faithfulness 修正 2 件 DONE (`8f636b54`/`ec711630`/`378e91cf`/`dc2fe378`, 2026-06-21)。残 = conjunct 2 (N(U)⊄M=Cor 14.12)/10 (A0-A TI=Thm A(3)(5)) のみ (conjunct 11 は 15.7(a) で close)
- [ ] Prop 16.1 配線 `proposition_type_classification` (S16:894) + AxiomsCheck 登録

## 完了条件

`proposition_type_classification` (S16:894) が sorry-free + axiom-clean（#print axioms で標準3公理のみ）
で、5 本の深い定理も同様。これにより mp/tp producer の sorryAx 源（Prop 16.1 分）が解消。

## 参照

- 先行: issue 7005/7006 (closed, POLE-1 構造側 assembly-complete)、commit `8c231082`
- Workflow 精査: `wpn72i4yc` (2026-06-19, frontier map)
- BG 原典: `references/bg/local-analysis.mmd` §16 (4328-4449), Lemma 15.1 (4116 付近), Prop 16.1 (4478)
- memory: [[s16-typep-producer-unfillable]] [[bg-s16-gated-on-typedata-construction]]
- 残り obligation 詳細（reverse lemmas hIF/hIIP2/hIIIIVP1/hVP1 は新規・gated）: Workflow plan 参照
