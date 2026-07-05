---
id: 2035
slug: char-degree-analysis-producer
title: "(13.3) character_degree_analysis producer — S11 (9.x) + (9.11)/(6.8) coherence + (5.8) formula の組立 campaign"
created: 2026-07-05
---

# (13.3) character_degree_analysis producer — S11 (9.x) + (9.11)/(6.8) coherence + (5.8) formula の組立 campaign

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 目標

`character_degree_analysis` (S15_SAndT_Setup:654, sorried) — CharacterDegreeData の honest 構成。
2034 で materialize した fields (λ = Ind_{PC}(linear) P-non-kernel / τ₁ 4 fields) を実供給する。

## 設計 map (07-05 it.46 調査)

Pf (13.3) proof の引用 ↔ repo 在庫:

| Pf | 内容 | repo 状態 |
|---|---|---|
| (13.3.a) | μⱼ = Ind_{PC}(linear), μⱼ(1) = uq | S11 `caseB_character_counts` (6252, **sorried**) — SOf 機械・Clifford case 分析は大部分 proven |
| (13.3.b) | λ の存在 (WLOG 分岐) | μ₁ を λ に採用 (13.3.a 経由) |
| (13.3.c) δ=1 | (4.3.d)+(4.4) + u≡1 mod q | S06 CertainTypeConjugation の (4.9)(a)-bridges + UW₁ Frobenius (basic_structure) |
| (13.3.c) formula | (4.9) or (5.8): μⱼ^{τ₁} = Σᵢ ηᵢⱼ | S05_SigmaTrichotomy `(5.8) full-column endgame` (:318) — **core proven** |
| τ₁ 存在 | (13.2.d) 𝒮 coherent ⇐ (9.11) | S11 `coherent_H0C_commutator` — **(6.8) wired 済**、残 gap = `sibleyTarget_H0C` (:6304, sorried, §14-gated 構造 witness) |
| (9.11) の (6.8) | Sibley coherence | `S08.sibleySetup_is_coherent` **proven** (cascade notes 2026-07-02: 旧「lane B 供給待ち」framing は obsolete) |

## 実装順 (upstream-first)

1. [ ] **S15 ↔ S11 instantiation bridge**: hyp.S (type II) に対する
   `TypesIIIIIIVSetup`/`ChiefFactorData`/`Section11CharacterData` の構成。
   **precheck 済 (it.47)**: S12 に `toTypesIIIIIIVSetup` (III/IV 用 — type II 分岐
   Or.inl は未使用だが構造は II を受容) + `mkSection11CharacterData` が既存。
   **⚠ 重大 caveat: S12 の mk は `H0CprimeSupport := ∅` + `tau := hyp.tau` の
   count-専用 placeholder** (docstring 明記「used only by the (9.11) coherence, not by
   the degree fact」) — (9.11)-coherence 用途には **∅-support で IsCoherent が
   偽/空虚化する Sset := ∅ 型の罠**。本 campaign は honest 版
   (実 H0CprimeSupport = (H₀C')^#-support + 実 Dade tau) を新規構成する:
   - TypesIIIIIIVSetup: maximal := S_maximal / typeP := hyp.Sdata /
     nontrivial := TypePNontrivialCore (basic_structure の hSdataUne 系から) /
     type_alt := Or.inl (isTypeII_of_isTypeP2)
   - ChiefFactorData: S11.exists_chiefFactorData
   - Section11CharacterData: u は S12-mk と同型 (rfl-pin)、tau := (S, (H₀C')^#) の
     honest Dade map (H_sharp_dadeHypothesis の H₀C'-版)、H0CprimeSupport := 実 support
2. [ ] `sibleyTarget_H0C` (§14 structural witness) — S14 の SibleyTarget 供給
   (S14_MaximalI 機械 or type-II 側の直接構成; §14-gated の実態を precheck)
3. [ ] (13.3.a): S11 `caseB_character_counts` の残 sorry を閉じる — **精査済 (it.58)**:
   4 conjunct 中 3 は proven (caseB_degree_qu / reducible_count_sOf_H0 /
   reducible_mem_sOf_H0C)。残 = (9.9.c) 1 本:
   「𝒮(H₀C′) に既約なし → C = ⊥ ∧ u = (p^q−1)/(p−1)」。Pf 証明は 2 分岐:
   - **C ≠ 1 枝**: θ ≠ 1 (H̄-linear), λ ≠ 1 (C-linear) の積 θλ を取り
     Ind_{HC}^{HU} 既約 (fpf-inertia = C; S11 `hcZeta_induceHU_irreducible` 系が既存)
     + Ind_{HU}^M 既約 ((9.9.b) reducible は C ⊆ Ker 側) → 既約メンバー構成で矛盾
   - **C = 1 枝**: Frobenius H̄⋊U の kernel-非自明既約 = (p^q−1)/u 本
     (Isaacs 6.34-count; S11 `card_pffun_on`/oXtheta 系) が全部 reducible 誘導なら
     (9.9.b) の p−1 本と一致 → u = (p^q−1)/(p−1)
   **順序訂正 (it.59)**: 結論の第 1 conjunct が C = ⊥ を主張するため、C ≠ 1 の
   否定 (branch-1: θ≠1, λ≠1 の θλ-lift + `hcZeta_induceHU_irreducible` 系で
   既約メンバー構成 → hno と矛盾) が第一義。その後 C = ⊥ の下で counting
   (free-action orbit 数 = (p^q−1)/u: `card_conjByOrbit_eq_index_inertia` +
   Frobenius-6.34 既約性 [在庫確認済 InducedIrreducible:544-590] + (9.9.b) の
   p−1 本と突合)。
   `exceptional_case_frobenius_realization` (9.10) も同素材で続けて閉じる見込み。
4. [ ] τ₁-fields 導出: `coherent_H0C_commutator` の IsCoherent (extension_agrees /
   inner_eq_on_supported) から 2034 の 4 fields (extends-Ind は τ=Ind (H_sharp_tau_eq_induce
   の M-版) 経由; ⊥η は (5.3.b)-系)
5. [ ] (5.8)-formula → mu_tau1 Props の materialize + δ=1
6. [ ] assembly: `character_degree_analysis` 本体

## 備考

- S-side τ₁ だが hub 裁定 2026-07-02 §2 と整合: atoms は W-side restate 済 (2034)、
  producer の coherence 構成は Pf-cite の本物 (13.2.d)⇐(9.11) 経路 — placeholder Sset 非依存。
- tau1T (T-side dual) も同型の構成 (T = type II dual, K = QD)。
- 関連: issues/2034 (fields 設計、残 checklist), closed/2033。

## route 候補 B (it.47 発見、要 precheck — 候補 A = (9.11)/H₀C′ より短い可能性)

**(6.8) Sibley を (G, L := hyp.S, H := hyp.H = PC) に直接適用**:
- `SibleyTarget` (S10_CoherenceWiring:96) = H ⊴ L + `S08.SibleyDadeHypothesis (G,L,H)` +
  τ/family/A₀ 一致 3 等式。`coherent_of_sibleyTarget` (sorry-free) で IsCoherent。
- (13.5)-family 𝒮₁ = {Ind_{PC}^S θ} は Sibley の base family そのもの;
  A₀ = (PC)^#-support、τ = H_sharp Dade (= Ind、13.2.e proven)。
- H = PC = F(S) ⊴ S ✓ / H^# TI + normalizer S ✓ (proven) — 残 = (6.8)(a)/(b)/(c) の
  正確な条件を S08.SibleyDadeHypothesis の fields で確認し (13.2)-carrier から充足するか。
- これが通れば S11-chars の honest 再構成 (route A step 1-2) を丸ごと skip し、
  IsCoherent → τ₁ + 4 fields 導出 (extension_agrees/inner_eq_on_supported) に直行。
- 次 iteration: S08.SibleyDadeHypothesis の fields 精読 + (S, PC)-充足性判定。

## route 判定 (it.48)

- **route B (Sibley 直接 (S, PC)) は死亡**: SibleyDadeHypothesis は (6.8.a) split
  `L = H ⋊ W₁` (IsComplement') を要求 — |S| = |PC|·u·q なので H = PC は S を複補しない。
- **route A 確定**: (9.11) = repo `coherent_H0C_commutator` ((6.8)-還元 wiring 済、
  Pf 原文の 8 段 maximal-coherent 論法は (6.8) に subsume との設計)。
  真の残 gap = `sibleyTarget_H0C` (S11:6304) — (6.8)-shape witness
  (H-Sibley ≈ H₀C′、split の complement は W₁ 単独でなく合成; (c2) = Hypothesis46 側)。
  §14-gated の構造 obligation で multi-session 級。
- **合わせて必要**: S 用の honest Section11CharacterData (∅-placeholder 不可、it.47 caveat)。

## 次の動き方

campaign は正しく mapped されたが critical path (sibleyTarget_H0C + S11 caseB 2 sorry) が
深い。上流優先の原則で、並行して **ungated な (13.9.a) `G0_nonvanishing_dichotomy`**
(文書順は (13.3) より後だが gate なしの genuine math) を先に閉じにいく
(Galois/cyclic-closure 論法 — GaloisRationalInteger 在庫と接続の見込み)。

## ✅ (9.9.c) 完全証明 + (9.10) u-conjunct (it.61-68, 2026-07-05)

**caseB_character_counts (Pf 9.9) が全 4 conjuncts sorry-free** (実装順):

1. it.61-62: hcPsiPair (θ,λ)-積指標 + inertia/既約性 + H₀C′ ◁ M + kernel 3 段 +
   ζ_{θ,λ} ∈ 𝒳(H₀C′) (`hcZetaPair_mem_xiOf`)
2. it.63: 存在補題 (θ ≠ 1 dual-card / λ ≠ 1 + C′-kill: solvable abelianization +
   cInHuEquivC transport)
3. it.64: **C = ⊥ 半分** (`caseB_no_irreducible_forces_C_bot`) — reducible → 𝒮(H₀C) →
   source M-共役 → H₀C ◁ M kernel 転送 → kernel descent → λ = 1 ⟂
4. it.65: caseB oXtheta (`caseB_oXtheta_count`: u·|Xζ| = p^q−1)
5. it.66: exhaustion (`caseB_xiOf_H0C_eq_induce_hcPsi`: Clifford 対応 + trivial-seed 排除)
6. it.67: **u-formula** (`caseB_no_irreducible_u_formula`) — prime-index inertia dichotomy
   (`conjBy_eq_self_of_not_isIrreducibleCharacter_induceHU`) で単射、exhaustion で全射 →
   |Xζ| = p−1 → u·(p−1) = p^q−1
7. it.68: (9.10) の u-conjunct 実配線 (degree 条件は caseB_degree_qu で冗長 → hno-bridge)

**(9.10) 残 sorry 2**: conjunct-1 `quotientSemidirectFrobenius` = opaque Prop field
(de-opacify 設計判断: 実 content は `chiefFactor_caseB_action_fpf` が既に carry;
field 差し替えは S12-bridge 供給と要調整 — 統一 restate は hub 相談推奨) /
conjunct-3 type-II HU-Frobenius = 指標論的 Frobenius 判定法 (Isaacs 7 章級の新規 machinery、
今 campaign の資材 [全 𝒳(H₀)-member が H-induced] が主入力になる見込み)。

→ campaign step 3 ((13.3.a) の S11 側) は本質完了。次 = step 1-2 (S15↔S11 bridge の
honest Section11CharacterData 構成 + sibleyTarget_H0C) or step 4 (τ₁ 導出)。

## ✅ (13.3.c) S-side ∀j δⱼ=1 完成 (it.87-88)

- it.87: mu_degree_modEq_delta threading ((4.3.d) 合同) + delta_eq_one_of_ne_zero
  (j≥1: μ₀ⱼ(1)=u + u≡1 mod q + δⱼ=±1 + q odd prime → δⱼ=1)
- it.88: delta_zero_eq_one threading (δ₀=1 via (4.4) certainType_zero_column_anchor) +
  delta_eq_one_S (∀j δⱼ=1 統合)。CharacterDegreeData.delta_eq_one の S-half 完全証明。

**producer 残 gate (確定)**:
- delta_eq_one T-side (∀i δ'ᵢ=1): reconciled_typePData_T (S15:2838, **7 sorries** T-carrier
  σ-gated BG §14) 依存で gated。v≡1 mod p は u≡1 mod q と同 route だが T-Frobenius が
  T-carrier 要 → gated。
- τ₁ 4 fields + mu_tau1_formula: sibleyTarget_H0C (S11:6305, §14-gated coherence witness)
- λ family: (13.3.b) 条件付き既約存在

→ 次: T-carrier が Section16 Tdata analog から threading 可能か調査 (可能なら T-dual 全開)。

## ✅ u ≡ 1 mod q 完全証明 (it.86) — δ=1 の crux ungated 実証

`Hypothesis.u_modEq_one` (S15): |Ū| ≡ 1 mod q を Singer field_model **不要**で証明。
UW₁ Frobenius (typeP_uW1_frobenius) の共役 φ : Sdata.U⊔W₁ →* Aut(P)、
kernel-image φ(U) = U/C_U(P) = Ū、`IsFrobeniusGroup.card_range_comp_subtype_modEq_one`
(Isaacs 6.1, purpose-built) で |Ū| ≡ 1 mod |W₁|。|Ū|=u (ker ψ = C を
equivMapOfInjective で同定)、|W₁|=q。→ it.84-85 の「ungated」評価が実証完了。

**δ=1 残 assembly (次 iteration)**:
- (4.3.d) 合同を Hypothesis field 化: `∃ a:ℤ, μᵢⱼ(1) = δⱼ + q·a`
  (producer supply = certainType_degree_modEq on certainTypeS、6-site threading)
- delta_eq_one (S-side j≥1): (u:ℂ)=δⱼ+q·a (field + mu_apply_one_eq_u) ∧ u=1+q·b (u_modEq_one)
  → δⱼ=1+q(b-a) 整数 → δⱼ≡1 mod q ∧ δⱼ=±1 (delta_pm_one) ∧ q≥3 → δⱼ=1
- j=0: δ₀=1 via (4.4) μ₀₀=1_L (要 threading or 別 route)
- T-side δ'ᵢ=1: dual (v≡1 mod p、reconciled_typePData_T gated の可能性)

## 🔑 (13.3.c) δ=1 は ungated と判明 (it.84-85 訂正) + (13.3.a) degree 完成

**(13.3.a) degree 完成 (it.84)**: `card_H_eq` (|H|=p^q·c、P⊓C=⊥ coprime + 複補)、
`H_index_eq_uq` ([S:PC]=uq)、`mu_j_degree` (μⱼ(1)=uq)。(13.3.a) statement 両半分 sorry-free。

**★重要な訂正 (it.85)**: δ=1 の crux `u ≡ 1 mod q` は Singer field_model **不要**、ungated:
- W₁ (order q) が Ū = U/C に共役作用、FPF (C_Ū(w)=1 for w∈W₁^#):
  - UW₁ Frobenius (typeP_uW1_frobenius, **proven**) → C_U(w)=1
  - W₁ normalizes C = U⊓C_G(P) (W1_normalizes_U + P=S_F)
  - coprime 作用 (gcd(q,|U|)=1) の fixed-quotient
    (`map_fixedSubgroup_eq_fixedSubgroup_quotient`, CoprimeFixedPoints:61):
    C_Ū(w) = image C_U(w) = image ⊥ = ⊥
- 素位数群 ⟨w⟩ (q-group) 作用の fixed-point 合同
  (`IsPGroup.card_modEq_card_fixedPoints`, mathlib PGroup:158):
  |Ū| ≡ |C_Ū(w)| = 1 mod q → u ≡ 1 mod q ✓

→ **δ=1 の残実装** (次 iteration): u≡1 mod q (上記、~多段だが ungated) +
per-entry μᵢⱼ(1)=u (mu_j_degree + columnFamily 等次数 — ⚠ certainTypeS が
Hypothesis で columnFamily_mu_apply_one_eq が Hypothesis46 の構造非互換、要 bridge) +
(4.3.d) certainType_degree_modEq → δⱼ ≡ 1 mod q ∧ δⱼ=±1 ∧ q≥3 → δⱼ=1。

**producer 残 gate 再整理**:
- δ=1: **ungated** (上記 u≡1 mod q route)、多段実装
- τ₁ 4 fields + mu_tau1_formula: coherence (sibleyTarget_H0C §14-gated)
- λ family: (13.3.b) 条件付き既約存在 ((9.8.c)/(9.9) S-lift)
- basic_structure_gated (P elem abelian / u_bound): BG §10/§14 σ-theory

## ✅ (13.3.a) 完全証明 — mu_j_isIndPC (it.74-83, 2026-07-05)

**Pf (13.3.a) の genuine math 完結**: `Hypothesis.mu_j_isIndPC` (S15) —
∀ j ≠ 0, ∃ θ linear irr on hyp.H.subgroupOf S, μⱼ = Ind_{PC} θ。
CharacterDegreeData の `mu_j_linear_induced` field の内容そのもの (構成可能性 honest 検証)。

積み上げた実証明 (全 sorry-free):
- S11: `caseB/caseA/reducible_sOf_H0_isIndHC` (case-agnostic isIndHC — reducible 𝒮(H₀)-member
  = Ind_{HC}^M linear)、`isIndHC_of_source_eq_induce_hcPsi` (stages-flatten helper)、
  `hcRealized_map_subtype_eq` (M-level HC = (H⊔C).subgroupOf M)、(9.9.c) 全証明機構
- S15: `mu_colSum_not_irreducible` (μⱼ = q distinct irr の和 → reducible)、
  `mu_colSum_mem_sOf_H0` (𝒮(H₀)-membership)、`toTypesIIIIIIVSetupS` bridge、
  `toTypesIIIIIIVSetupS_chief_N_eq_bot`/`_H0_eq_bot`、`toTypesIIIIIIVSetupS_cSub_eq_C`
  (C_U(H̄)=C_U(P)=U⊓C_G(P))、`mu_colSum_eq_induce`/`mu_irreducible`/`mu_col_injective` threading
- FeitThompson: 上記 3 fields の 3 層 threading (additive、self-flag)

**次の候補** (character_degree_analysis producer への残):
- μⱼ(1) = uq degree corollary (isIndHC + [S:PC]=uq、quick)
- (13.3.c) δ=1 + mu_tau1_formula: (4.3.d)/(4.4)/(5.8) 経由 (sibleyTarget 非 gated、別 sub-campaign)
- τ₁ 4 fields: coherent_H0C_commutator の IsCoherent 経由 (sibleyTarget_H0C §14-gated)
- assembly: 全 fields 揃い次第 character_degree_analysis 本体

## (13.3.a) μⱼ ∈ 𝒮(H₀) 同定チェーン (it.74 recon — 経路確定)

**Coq 対応**: PFsection13 は `mu_ := primeTIred` + `FTseqInd_TIred : mu_ j ∈ calS`
(証明 = `cfInd_prTIres`: μⱼ = Ind of its S′-restriction、prime-TI 構成的性質)。

**repo 在庫 (4.5.a)-analog 発見**: `S06_CertainTypeClifford.induce_restrict_certainType_eq`
— **Σᵢ (columnFamily χ₂).mu i = Ind_{h.K}^{L}(chiRestrict χ₂)**、chiRestrict =
Res(μ₀ⱼ) は既約 (`certainTypeRestrict_isIrreducible` = (4.5.a))。

**残チェーン (S15-側、hyp.mu = certainTypeS-columnFamily 経由)**:
1. reindex 和恒等式: Σᵢ hyp.mu i j = Ind_{K}^{S}(chiRestrict (chi2enum j))
   (muS-def + eqQ Equiv.sum_comp; mu_definition と同型の producer-側 supply →
   S15.Hypothesis に `mu_colSum_eq_induce`-field として threading が最短)
2. K-spelling 突合: certainTypeS.K = S′ = PU = huSub (toTypesIIIIIIVSetupS)
   (K_eq-系 field/lemma 要確認)
3. χⱼ ∈ 𝒳(H₀-of-S-instance): (i) P ⊄ Ker χⱼ (xiSet 半分)、(ii) H₀ ⊆ Ker χⱼ —
   ω-列の nontriviality/kernel から ((13.2)-隣接の genuine math、恐らく producer-側
   supply が正: certainType 側の facts として証明して threading)
→ 1+2+3 で mem_sOf ⟨χⱼ-bundled, xiOf-mem, sum-eq⟩ → μⱼ ∈ 𝒮(H₀) →
mu_colSum_not_irreducible (済) で reducible-𝒮 → isIndHC (済) → (13.3.a) 完成。

## (13.3.a) step 3 進捗 (it.76-77)

- **H₀ = ⊥ 済** (it.76 `toTypesIIIIIIVSetupS_chief_H0_eq_bot`): P 自体が chief factor
  (card_P_eq × chiefFactor_quotient_card 突合)。kernel 条件の片方が自動化。
- **P ⊄ Ker χⱼ の核も在庫と判明 (it.77)**: S06_CertainTypeSupport
  `not_subset_characterKernel_chiRestrict_of_ne_one` = Pf (4.7) j≥1 kernel step
  (χ₂ ≠ 1 → W₂ ⊄ Ker χⱼ; (4.3.c) 値公式 + kernel translation の ω-積分解論法)。
  P-nonkernel は W₂ ≤ P の monotone で従う。
- **残実装 (次 iteration)**: mu_colSum_eq_induce の ∃ に conjunct
  「j ≠ 0 → ¬ P-realized ⊆ Ker ψ」を追加して 6 サイト再 threading。producer 供給 =
  上記 S06-lemma + (i) chi2enum の nontriviality (chi2enum j ≠ 1 for j ≠ 0 —
  0 ↦ trivial pin の確認要) + (ii) mp-level W₂ ≤ P (mp.Kstar ≤ maxNilpotentNormalHall mp.S —
  hyp-level W2_le_P の producer-analog、要在庫確認/新規)。
- その後: 𝒳(⊥)-membership 組立 → μⱼ ∈ 𝒮(H₀) → (13.3.a) assembly。

## (13.3.a) isIndHC-corollary build-spec (it.70 recon)

**S↔§9 bridge 開通済 (it.69)**: `toTypesIIIIIIVSetupS` + `mkSection11CharacterDataS`。
§9-H = S_F = P、§9-HC = PC = hyp.H。

**次の §9-corollary (Coq PFsection9 の `isIndHC`)**: caseB で reducible φ ∈ 𝒮(H₀) は
Ind_{HC}^{M}(linear):

```
caseB_reducible_sOf_H0_isIndHC :
  φ ∈ sOf data chief.H0 → ¬Irr φ →
  ∃ ψ : CF ↥((hInHu ⊔ realizedH0C).map (huSub data).subtype) ℂ,
    IsIrr ψ ∧ ψ 1 = 1 ∧ φ = ClassFunction.induce _ ψ
```

構成: (9.9.b) reducible_mem_sOf_H0C → ζ' ∈ 𝒳(H₀C) → exhaustion
(caseB_xiOf_H0C_eq_induce_hcPsi) → ζ' = Ind_{HC}(hcPsi θbar) →
段階誘導 `induce_induce_subgroupOf` (InducedTransport:74, K ≤ H ≤ M 在庫 lemma) で
φ = Ind_{HU}(Ind_{HC} pair) = Ind_{K}(ψ)、K := HC.map subtype。

transport 設計 (cast 回避):
- hKeq : K.subgroupOf (huSub) = HC-orig via `Subgroup.comap_map_eq_self_of_injective`
  (subtype injective; subgroupOf = comap subtype)
- f : ↥K ≃* ↥HC-orig := (subgroupOfEquivOfLe map_subtype_le).symm.trans
  (MulEquiv.subgroupCongr hKeq) — G-val preserving
- ψ := compHom f.toMonoidHom (hcPsi θbar)-coe; stages-lemma の inner-term 一致は
  compHom_comp (S11:6018 パターン) + subgroupCongr で処理; ψ linear:
  compHom は 1 を 1 に (f 1 = 1) → ψ 1 = pair 1 = 1; Irr: compHom_of_surjective (f surj)

S15-側の残 gap (それでも): μ-columns ∈ 𝒮(H₀)-linkage (hyp.mu の membership spec が
未 pin — mu は W-side τ₃-cascade 供給、(13.1.e)-relation field のみ)。isIndHC 完成後、
μ-column 側は「Σᵢ μᵢⱼ が S-family の reducible member」を hyp-fields から導く追加
threading が必要 (要 recon: mu_col の degree/vanishing spec)。

## (9.9.c) branch-1 build-spec (it.60 recon)

Pf の C ≠ 1 否定枝の Lean 化に必要な新規構成:

1. **λ の存在**: C ≠ ⊥ + C abelian (caseB: U abelian、C ≤ U) → ∃ λ : C-hom ≠ 1
   (dual-card = |C| > 1、it.42 の `CommGroup.card_monoidHom` パターン)。
2. **(θ,λ)-積指標**: 既存 `hcPsi` (θ-inflation、λ-slot なし = C 上自明) の一般化
   `hcPsiPair (θ, λ)` — HC-join 上の線形指標 (H̄-inflation ⊗ C-lift;
   omegaProdChar-パターン; H ∩ C の整合は H₀-商で処理)。
3. **既約性**: `hcZeta_induceHU_irreducible` (inertia = HC、fpf) を hcPsiPair に適用
   → χ := Ind_{HC}^{HU}(θλ) ∈ Irr(HU)。
4. **membership**: H₀C′ ⊆ Ker(θλ) (λ は C′-trivial: C abelian → C′ = ⊥ ✓ 自明) →
   Ind_{HU}^M χ ∈ SOf(H₀C′)。
5. **Ind_{HU}^M χ 既約**: C ⊄ Ker χ (λ ≠ 1) + (9.9.b) の「reducible は全て
   𝒮(H₀C) 側 = C ⊆ Ker-族」(`reducible_mem_sOf_H0C` proven) との
   dichotomy → 既約 → `hno` と矛盾 → C = ⊥。
6. **C = ⊥ counting** (第 2 conjunct): free-action orbit 数
   (`card_conjByOrbit_eq_index_inertia`) + 6.34-既約性 (在庫) + (9.9.b) p−1 本の突合
   → u = (p^q−1)/(p−1)。

規模見積: 2 (積指標) が主 (~150 行)、3-5 は既存機械の適用 (~80 行)、6 は counting (~100 行)。

## ✅ T-side complement disjointness `Q ⊓ V = ⊥` un-gated (it.89, 2026-07-05, commit 4ea27401)

**issue の「次: T-carrier が Section16 Tdata analog から threading 可能か調査」への確定回答**:

- **full T-carrier は §14 gated 確定**: `typePData_of_kappaHall_hallComplement` は `IsTypeP2 M` 必須
  → T では `IsTypeP2 T` = (14.9) = `IsTypeII T` (§16/c-lane)。§16 constructor は T の型が構築時
  未確定ゆえ full Tdata を供給不可 (設計通り「no T-side carrier」)。`reconciled_typePData_T` の
  残 6 sorry (W2_le / M_complement / U_nilpotent / secondDerived_le_fitting / fitting_eq /
  centralizer_W1) はこの §14 gate に残る。
- **ただし complement disjointness `Q ⊓ V = ⊥` は ungated**: `exists_kappaHall_invariant_complement_to_MF`
  (S14_TypePComplement:32) が `M_F ⊓ U = ⊥` を **`IsTypeP M`** (= `T_nonI`、(14.9) 不要) から返す。
  §16 constructor では `hTcompl.choose_spec.2.2` として在るが、抽象 `T_deriv_eq_QV` (`T' = Q ⊔ V`) が
  disjointness を捨てていた。
- **実施**: honest field `V_inf_Q_eq_bot` を `Section16TypePStructure` → `Section16Inputs` →
  `S15.Hypothesis.Q_inf_V_eq_bot` に threading (3 constructor sites とも `hTcompl` から供給)。効果:
  - `reconciled_typePData_T.derived_complement`: 7→6 sorry (field + `T_deriv_eq_QV` で実証明)
  - `isMulCommutative_V`: **完全 honest 化** — sorried `reconciled_typePData_T` call を除去、
    (14.9) `IsTypeII T` 仮説のみに gated (V-side 他 lemma と同型)。(13.16) V-side subtree が解放。
  - 循環 `Q_inf_V_eq_bot_of_reconciled` 撤去 (callers は `hyp.Q_inf_V_eq_bot` 直参照)。
- **次の同型 win 候補**: `M_complement` (W2 が T' を T で複補) も ungated
  (`typeP_derivedInG_isComplement_kappaHall` via `T_typeP` + W2=κ-Hall)。threading すれば
  `coprime_card_Q_card_VW2` を full honest 化できる (W2=κ-Hall の field 追加要)。

**B-lane frontier 総括 (it.89 時点)**: S15 (§13) の ungated genuine math は essentially 完了
(S-side 全 + T-side disjointness)。残りは一律 §14 gate (`IsTypeII T` = (14.9), c-lane)
の gated-endpoint threading + deep §13 char (complement_inf_Q/P (13.17.c) 等)。
