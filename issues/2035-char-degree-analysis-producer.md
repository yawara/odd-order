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

## ✅ M_complement (T = T' ⋊ W₂) も un-gated (it.90, 2026-07-05, commit d63e7526)

前 it.89 の「次候補」を実施。`W2_isComplement_T_deriv` field を 3 structure 経由で threading
(`typeP_derivedInG_isComplement_kappaHall` = BG 14.7(h)、`T_nonI` から、(14.9) 不要)。
- `reconciled_typePData_T.M_complement`: 6→5 sorry (field で実証明)
- `coprime_card_Q_card_VW2`: **完全 honest 化** — 2 fields (Q_inf_V_eq_bot + W2_isComplement_T_deriv)
  から直接組立、sorried reconciliation の obtain を除去。docstring の「ungated」が真に成立。

**reconciled_typePData_T 残 5 sorry** (session 開始時 7): W2_le / U_nilpotent /
secondDerived_le_fitting / fitting_eq / centralizer_W1 — いずれも §14 gated
(`IsTypeP2 T` = (14.9)) の T 型-`P₂` σ-structure。ungated complement facts は出し切った。
次: これら残 5 は (14.9) 必須ゆえ、B-lane の ungated genuine math は別 frontier へ
(S-side (13.3.b) λ 存在 or deep §13 char の complement_inf_Q/P (13.17.c) 調査)。

## ✅ P_elementaryAbelian (S-instance, 13.2.b/11.7) 実証明 (it.91, 2026-07-05, commit 65b840a9)

T-carrier complements 出し切り後、別 ungated frontier: `basic_structure_gated.P_elementaryAbelian`
(`P = S_F` elementary abelian exp p) を honest 化。§11 chief-factor data (S-instance) から組立:
`exists_chiefFactorData (toTypesIIIIIIVSetupS)` → N=⊥ (`toTypesIIIIIIVSetupS_chief_N_eq_bot` 既証)
→ P 自体が chief factor → `quotient_elementaryAbelian` (chief.p=p, |P|=p^q 強制) を
↥H⧸⊥ ≃* ↥H で transport → H=P。**ungated** (S-instance H₀=⊥ は既証、a-lane generic
`chief_H0_eq_bot` sorry と別)。新 `Hypothesis.P_elementaryAbelian` は sorry-free。
`basic_structure_gated`: 2→1 sorry (残 `u_bound` = 2u≤|P|-1 = issue 9000 σ-producer)。

**session 累計 (it.89-91, 4 commits)**: T-carrier 7→5 sorry (Q⊓V + T=T'⋊W₂) + isMulCommutative_V/
coprime_card_Q_card_VW2 完全 honest + P_elementaryAbelian。次 ungated 候補 (fresh 調査要):
u_bound (9000 σ 依存の可能性) or chief-factor パターンの他 S-instance facts への波及。

## Q_elementaryAbelian_T (T-side dual) 実証明 (it.92, 2026-07-05, commit b34ed53c)

P_elementaryAbelian (S-side, ungated) の T-side dual を実装。(14.9) type-II T → reconciled
TypePData T → TypesIIIIIIVSetup T → chief N=⊥ (|Q|=q^p Wielandt 経由) → quotient_elementaryAbelian
(chief.p=q) transport。**gated-endpoint body** (IsTypeP2 T gated via reconciled_typePData_T、
card_Q_eq と同 gate) — 独立仮説でなく type-P σ-structure から導出、σ-structure landing で auto-close。

**frontier shift (it.89-92, 6 commits)**: 明確な ungated win (T-carrier complements +
P_elementaryAbelian) は出し切り。以降は gated-endpoint body (IsTypeP2 T gated の T-side dual 群:
V_inf_centralizer_Q_eq_bot=13.12 d=1 T-side 等) or deep char (13.4 orthogonality) or
σ-producer (u_bound=9000)。次候補 = V_inf_centralizer_Q_eq_bot (S-side U_inf_centralizer_P_eq_bot
の dual、gated-endpoint body 見込み) — fresh context で mirror 調査推奨。

## 🔎 frontier assessment: B-lane ungated ceiling 到達 (it.93, 2026-07-05)

session it.89-92 で明確な ungated win (T-carrier complements ×2 + P_elementaryAbelian +
Q_elementaryAbelian_T gated-body) を出し切り。it.93 で残候補を精査、いずれも clean でないと確定:

- **u_bound** (2u≤|P|-1, 13.2.c): issue 9000 typeP_Galois σ-theory (lane a/d 進行中) gated。leaf
  `TypePGaloisUBound` は module-level (sorry-free) だが hyp への dichotomy assembly が 9000 の残作業。
- **V_inf_centralizer_Q_eq_bot** (13.12 d=1 T-side): S-side dual `U_inf_centralizer_P_eq_bot` =
  `C_eq_bot` = **`c_eq_one` (sorried, deep 13.12 numeric → 13.10 → char_degree_analysis)**。deep-gated。
- **reconciled_typePData_T refactor** (thread IsTypeII T): 17 call-site の signature 変更に対し
  payoff は U_nilpotent 1 本のみ確実 (5→4)、consumers は残 sorry で gated のまま。**low-payoff、非推奨**。

**結論**: B-lane の残 frontier は全て deep-gated on 他レーンの upstream ((14.9) IsTypeP2 T = c-lane /
issue 9000 σ = a·d / coherence·τ₁ keystone = char_degree_analysis 本体)。次の実質前進は
(a) 他レーンが gate を閉じるのを待って re-assess (un-gate 波及)、or (b) deep keystone
(char_degree_analysis τ₁ construction or 13.4 orthogonality) を multi-session で正面 engage。
clean/quick な ungated leaf は現時点で枯渇。

## 2026-07-06 更新 (lane b loop): (13.12) 数値部は ungated だった + (13.3) tractability 精査

**「ungated leaf 枯渇」の部分訂正 — (13.12) `c_eq_one` の数値消去は ungated で closed済**:
上の結論は (13.10) `analytic_inequality` が sorry-free assembly になった payoff を見落としていた。
- **`c_eq_one_forces_params` (新, sorry-free)**: (13.10)+(13.2.c Singer)+(13.11)+FPF `c≥2q+1` で
  `p=5∧q=3∧c=7` に絞る純 ℚ/ℕ 算術 (commit a1dc3748)。`c_eq_one` の bare sorry 撤去。
- **`c_eq_one_final_case` の maximality 矛盾も実証明** (commit b6ddff8e): `pc_le_maxNilpotentNormalHall`
  (PC ≤ M_F) → C ≤ P → 7∤125。**(13.12) 残 gap = `pc_le_maxNilpotentNormalHall` のみ** (PC が
  nilpotent[proven-able: PC abelian] normal[W₁-struct] Hall[gcd(c,u)=1 = case 9.7.b ⇒ u∣31 の
  typeP_Galois]。issue 9000 σ-theory と同 gate)。

**(13.3) `character_degree_analysis` tractability 精査 (Explore agent 系統調査)**:
- **確定: production `character_degree_analysis` は `sibleyTarget_H0C` (S11:6348 sorried, §14-gated)
  無しには閉じない。~3-5 session。** route B (Sibley 直 (S,PC)) は (6.8.a) split で死亡 (既知)。
  route A = `coherent_H0C_commutator` (9.11) が sibleyTarget_H0C を要す ((6.8)-shape witness for
  H₀C'、W₁-composite complement)。
- **landable path = "gated-endpoint body"**: `character_degree_analysis_of_sibleyTarget`
  (SibleyTarget を仮説パラメータ化、~400 行、sorry-free extraction)。τ₁ = `coh.extension`
  (S07 `IsCoherent` 構造 :1659) から抽出: `extension_inner_eq` → `tau1S_inner_induce` /
  `extends_on_supported` → `tau1S_apply_induce_sub` / `extension_mem_ZIrr` → `tau1S_induce_mem_ZIrr`。
- **既 proven fields** (assembly で cite 可): `mu_j_linear_induced` (it.83) / `delta_eq_one` S-side
  (it.87-88) / `mu_col_tau1_eta_col_one`。残 = 4 coherence-extraction fields + lambda(MEDIUM) +
  mu_tau1_formula (S05 (5.8) machinery threading)。
- **次 session 推奨**: 上記 gated-endpoint body を専用 session で landing (SibleyTarget 仮説化で
  §14 依存を parallel track に切り出し、(13.3) 構成 principle を実証)。

## 2026-07-06 更新 #2 (lane b, 専用エージェント調査): (13.3) の実 gate = S15→S13 bridge (sibleyTarget 診断は誤り)

**gated-endpoint body (`character_degree_analysis_of_sibleyTarget`) 戦略は REFUTED** (build-capable
agent が probe → coupling wall 確認 → 綺麗に revert、net-zero/green)。根本原因:
- **spine は `S15.Hypothesis` を `Sset:=∅ / A0S:=∅ / tauS:=0` で instantiate** (`FeitThompson.lean:2668`、
  vestigial・hub 裁定 `sibleyTarget_S` docstring 760-773「do not complete」)。ゆえ
  `cohereOfSibleyTarget wit_S` の extension は `zSpan ∅ = {0}` 上でしか保証を持たず、nonzero
  `induce θ` に無力 → **4 tau1S fields は cohereOfSibleyTarget から取れない**。
- coherence+(5.8) machinery (`coherent_S_of_coherent_SH0C` S13:1192、`sixTwoDecompositionData`
  `S13_SixTwoBridge.lean:814`、**両方 sorry-free**) は **`S13/S14.Hypothesis M` 世界**の
  parameterization。honest `.base.tau`/`.base.Sset` を持つ。
- **`sibleyTarget_H0C` は named では存在しない** (最も近いのは `coherent_S_of_coherent_SH0C`、Hypothesis M 世界)。
  従来の「(13.3) = sibleyTarget_H0C §14-gated」診断は不正確。

**⟹ (13.3) の真の gate = `S15.Hypothesis → S13.Hypothesis (hyp.S)` reduction + `hyp.mu`/`hyp.eta` ↔
`muGrid`/`Section16CharacterData` grid reconciliation の bridge を構築すること**。この bridge が
在れば **既 proven の `sixTwoDecompositionData`/(5.8) で `tau1S_*`/`mu_col`/`mu_tau1_formula` を discharge 可**。
これが本物の §14 work (structural、char-analytic でない — 相対的に tractable かもしれないが multi-session)。

**今 proven 可の 2 fields** (bridge 無しでも): `mu_j_linear_induced` ← `mu_j_isIndPC` (:2621) /
`delta_eq_one` S-side ← `delta_eq_one_S` (:3537)。**別 gap**: T-side `δ'_i=1` は `deltaPrime_eq_one`
不在 (delta_eq_one_S の T-side mirror が要る)。

**次 session 推奨**: (13.3) を直接触らず、上記 **S15→S13 Hypothesis bridge + grid reconciliation** を
専用 session で。それまで `character_degree_analysis` の単一 sorry を fan-out しない (undischargeable
hypotheses に分解するのは net-negative)。

## 2026-07-06 更新 #3 (lane b, 型検証): S13-bridge 診断は誤り — 型 II vs III/IV 不整合。route A (S11) が正

更新 #2 の「S15→S13 Hypothesis bridge」推奨は **型不整合で無効と判明**:
- `S13.Hypothesis` (S13_MaximalIII_IV.lean:108) は **`type_alt : IsTypeIII M ∨ IsTypeIV M`** (:122) を
  要求。しかし `hyp.S` は **type II** (`S_typeP2` → `isTypeII_of_isTypeP2`)。⟹ `coherent_S_of_coherent_SH0C`
  (:1192、S13.Hypothesis 経由ゆえ **type III/IV 専用**) は type-II `hyp.S` に**適用不可**。S13 route は dead-end。
- **正しい (13.3) type-II path = route A via S11** (issue 冒頭の設計に回帰):
  1. `toTypesIIIIIIVSetupS` (S15:458, **sorry-free 既存**) で S15→S11.TypesIIIIIIVSetup(hyp.S) — type II/III/IV 汎用ゆえ type-II OK。
  2. **honest `Section11CharacterData` for hyp.S** — ∅-placeholder (`mkSection11CharacterDataS` は
     H0CprimeSupport:=∅/count-only) を避け、実 H0CprimeSupport = (H₀ ⊔ C')^# + 実 Dade tau
     (S15 `H_sharp_dadeHypothesis` の (S,(H₀C')^#)-版を mirror)。**これが実 gate**。
  3. `coherent_H0C_commutator` (S11:6361, TypesIIIIIIVSetup 汎用) → `IsCoherent`。`sibleyTarget_H0C`
     (S11:6348 sorried §14) を sorried-cite。
  4. coherence.extension = tau1S → (13.3) の tau1S_* fields を discharge。
- **建設順**: honest Section11CharacterData (step 2) が最初の substantial build。実 support は構成可
  ((H₀⊔C')^#)、実 Dade tau が hard 部 (S04 Hypothesis for (S,(H₀C')^#))。multi-session。

## 2026-07-06 更新 #4 (lane b): (13.3) tractable と判明 — chars.tau は free field + S-instance で H₀=⊥。増分 build 計画

**tractability breakthrough**: `Section11CharacterData` (S11:2002) は property 制約が
`u_eq_card_quotient` のみ、**`H0CprimeSupport`/`tau` は free data field**。ゆえ:
- **S-instance simplification**: `toTypesIIIIIIVSetupS_chief_N_eq_bot` (S15:531) で **N=⊥, H₀=⊥**
  (|P|=p^q=(chief.p)^q ⟹ chief.p=p, N=⊥)。⟹ honest support = (H₀⊔C')^# = **(C')^#** (C'=[C,C])。
- **`chars.tau := Ind_S^G`** に設定可 (free field)。すると `coherent_H0C_commutator chars`
  (sibleyTarget_H0C sorried-backed) の `IsCoherent (Ind_S^G) chars.S support` から
  `.extension = tau1S`、`extends_on_supported: tau1S = Ind_S^G on supported span` ⟹
  **`tau1S_apply_induce_sub` は family⊆supported で成立**。`tau1S_inner_induce` ← `extension_inner_eq`、
  `tau1S_induce_mem_ZIrr` ← `extension_mem_ZIrr`。

**増分 build 計画 (各 lemma は standalone compile → commit 可、最後に assemble)**:
1. `Ind_S^G` を `IntegralCharacterMap ↥S G` として (ClassFunction.induce の ℤ-linear wrap)。
2. `(C')^#` = ([C,C])^# support の TI/family-membership 性質 (Ind θ ∈ zSpan chars.S 等)。
3. honest `mkSection11CharacterDataS_honest` (tau:=Ind_S^G, support:=(C')^#)。
4. tau1S extraction + 4 tau1S_* fields (coherence + family membership から)。
5. lambda (13.3.b) + mu_col_tau1 (5.8) + mu_tau1_formula → CharacterDegreeData assemble。
6. `character_degree_analysis` = 上記 + sorried-cite sibleyTarget_H0C。

**注意**: main が S11 を 338 行 restructure 済 (2026-07-06 merge)。build 前に coherent_H0C_commutator
(現 S11:6628) の現行 signature 再確認。

## 2026-07-06 更新 #5 (lane b): ✅ foundation (step 1-4) LANDED — τ₁ extension 実構成 (commit 0032cc7a)

**tractability breakthrough は実証された** (bounded agent build、full 3929 green / AxiomsCheck OK /
新 axiom なし / sorry 数不変):
- ✅ `indS` : Ind_S^G を IntegralCharacterMap ↥S G として (induce_add/smul + restrictScalars ℤ)。sorry-free。
- ✅ `Cprime`/`cprimeSharpS` : (C')^# support (H₀=⊥ 退化)。sorry-free。
- ✅ `mkSection11CharacterDataS_honest` : tau:=Ind_S^G / support:=(C')^#。sorry-free。
- ✅ `coherent_H0Cprime_S` → `tau1S_ofHonest` (=.extension = (13.2.d) τ₁) + `tau1S_ofHonest_extends_on_supported`
  (τ₁=Ind_S on supported span)。sibleyTarget_H0C (§14) のみ sorried-cite。

**残 (13.3) work (foundation 済ゆえ全て unblocked)**:
- **step 5a (tau1S_* fields)**: CharacterDegreeData の `tau1S_apply_induce_sub`/`tau1S_inner_induce`/
  `tau1S_induce_mem_ZIrr`/`tau1S_induce_inner_eta` を tau1S_ofHonest + extends_on_supported +
  **family membership** (Ind θ ∈ zSpan chars.S、differences ∈ zSupportedSpan — 要 (7.6)-family 構造) から証明。
- **step 5b (lambda 13.3.b)**: degree-uq irreducible λ (column sum でなく specific 既約構成)。
- **step 5c (mu_col/mu_tau1 5.8)**: mu_col_tau1_eta_col_one + mu_tau1_formula (S05 (5.8) machinery)。
- **step 6 (assemble)**: CharacterDegreeData 全 field → `character_degree_analysis` = 上記 + sorried-cite。
- **T-side δ' (別 gap)**: deltaPrime_eq_one (delta_eq_one_S mirror、T-side 構造要)。

**次**: step 5a (tau1S_* fields via family membership) — 最も foundation に近い増分。

## 2026-07-06 更新 #6 (lane b, bounded agent): ✅ step 5a helper 2/3 landed + 2 つの genuine gap を isolation

**τ₁ helper 2 本が sorry-free で landing** (full 3929 green / 新 axiom なし / signature 変更なし / net +76 行 additive):
- ✅ `Hypothesis.tau1S_ofHonest_inner_induce` (S15:648) — `⟨τ₁(Ind_{PC}θ), τ₁(Ind_{PC}θ')⟩ = ⟨Ind θ, Ind θ'⟩`
  (irr θ,θ' on H.subgroupOf S、**P⊄Ker θ,θ' 仮説付き**)。`coherent_H0Cprime_S.extension_inner_eq` + family membership。
- ✅ `Hypothesis.tau1S_ofHonest_induce_mem_ZIrr` (S15:674) — `τ₁(Ind_{PC}θ) ∈ ZIrr G` (P⊄Ker θ 付き)。
  `.extension_mem_ZIrr` + family membership。
- 🔑 `Hypothesis.induce_H_mem_zSpan_S` (S15:629, **isolated sorry**) — `Ind_{PC}^S θ ∈ zSpan 𝒮` (P⊄Ker θ)。

**GENUINE GAP #1 (family membership = Coq `sS1S`, (1.5.a))**: `Ind_{PC}^S θ ∈ ℤ[𝒮]` は本物の §9/§13 定理。
Coq `PFsection13:428` `sS1S : {subset calS1 <= 'Z[calS]}` (calS1=seqIndD H S P 1, calS=seqIndD PU S P 1)。
証明 `S1cases` = prime-TI Clifford dichotomy「Ind_{PC}θ = μ_j (∈𝒮 via FTseqInd_TIred) ∨ ∈ ℤ[𝒮∩Irr S]」。
**既存 S11 stock からは this (source→family) 方向は不可** (在庫 isIndHC/reducible_sOf_H0_isIndHC は逆向き
family→Ind_{PC}(linear))。**⚠ 訂正: field は ∀irr θ だが membership は `P⊄Ker θ` に本質的に制限が要る**
(P⊆Ker θ なら Ind_{PC}θ は P∈kernel で 𝒮∌ — 𝒮=Ind_{HU}𝒳 の全 member は P⊄Ker)。field 側にも P⊄Ker 仮説の追加が必要。

**GENUINE GAP #2 (foundation の support が (13.3) に対して小さすぎる — helper 3 blocked)**:
`tau1S_ofHonest_apply_induce_sub` (差 `Ind θ - Ind θ'` 上で τ₁ = Ind_S) は **本 foundation では landing 不可**。
理由: `coherent_H0Cprime_S` の `.extends_on_supported` は `A = (C')^# = H0CprimeSupport` (9.11 由来) 上のみ agreement。
しかし差 `Ind_{PC}θ - Ind_{PC}θ'` は **H^#=(PC)^# 上に台** ((C')^# ⊊ H^# 厳密: C'≤U, P∩U=⊥ ゆえ P^#⊄(C')^#)。
Pf の実論法 (mmd:68, (13.2.e)): `(ζ_i−ζ_0)^τ = Ind_S^G(ζ_i−ζ_0)` は Dade τ が **A₀(S) ⊇ H^#** 相対だから成立。
**⟹ (13.3) の τ₁ は support `A₀(S)` (or 少なくとも `(S')^#`⊇H^#) の coherence を要する**。repo に裏付け:
`S13_SixTwoBridge.mderivSharp_subset_A0` = `(M')^# ⊆ A₀(M)` (M=S で `(S')^#⊆A₀(S)`, H^#⊆(S')^# ゆえ H^#⊆A₀(S))。
→ **foundation 修正**: `mkSection11CharacterDataS_honest` の `H0CprimeSupport := (C')^#` を
`A₀(S)` (or `(S')^#`) に広げた coherence が要る (9.11 の (C')^#-coherence とは別 object)。
これは next-session の foundation redesign work (helper 1/2 の tau1S_ofHonest/coherent_H0Cprime_S base は再利用可、
support だけ差し替え)。**helper 3 は speculative sorry で前倒しせず、この support 診断を正本記録して停止** (fan-out 回避)。

**step 5a route の判定**: helper 1/2 は family membership (gap#1) さえ閉じれば完成。helper 3 (=field
`tau1S_apply_induce_sub`) は gap#1 に加え gap#2 (support redesign) が要る。**step 5a は未完** (2/3 landed、
1/3 は foundation-support blocked)。tau1S_induce_inner_eta ((5.3.b) η-orthogonality) は別 harder field で今回対象外。

## 2026-07-06 更新 #7 (lane b): sS1S = **prime-TI residue API** 依存と精密判明 — repo 未形式化の基盤 (~2-3 session)

`induce_H_mem_zSpan_S` (sS1S / Pf (1.5.a)) を精査 (build-agent、no fake proof、tree clean、build green):
- **本 gap = prime-TI residue machinery** (`primeTIred mu_`, `prTIres_irr_cases` = prime-TI residue の
  constituent 分類, `cfInd_prTIres`)。**repo に未形式化** (docstring/comment のみ、mathcomp character
  library の foundational piece)。Coq proof = `S1cases` (PFsection13.v:401-428) の prime-TI Clifford
  dichotomy (zeta=mu_j ∈𝒮 or ∈ℤ[𝒮∩Irr])。
- **(9.9) counts は blocker でない**: `caseB_character_counts` は sorry-free 済 (it.61-68)、かつ sS1S は
  counts を経由せず prime-TI residue theory を経由 (orthogonal)。
- **既存 §9 isIndHC stack は逆方向** (family→Ind_{PC}(linear)) ゆえ本 source→family 方向を供給しない
  (`mu_j_isIndPC` も逆写像で反転不可)。
- **建設 (~4-4.5 session)**: (1) prime-TI residue API `(W,S)` [~2-3 session、mathcomp port、**substantial
  新 infra**] → (2) forward `FTseqInd_TIred` (mu_j∈𝒮) [~0.5] → (3) `S1cases` dichotomy assembly [~1] →
  (4) sS1S wrapper [~1h]。**step 1 (prime-TI residue API) は §13 μ_j machinery も unblock** (broad value)。
- downstream: `tau1S_ofHonest_inner_induce`/`_induce_mem_ZIrr` は sS1S を cite して landed 済 →
  sS1S closure で完全 sorry-free 化。`tau1S_apply_induce_sub` は別 gap (#6 の A₀(S) support-widening)。

**戦略的岐路**: (13.3) 完遂 + broad §13 は **prime-TI residue API** (major ~2-3 session infra port) に gated。

## 2026-07-13 更新 (lane b, /loop) — (9.11) S-instance coherence landed による gap#2 再評価

**本日 issue 1017 で `sSet_coherent_indS_A` (S-instance (9.11) coherence、support = A(S)) が
closed** (caseA: alphaSupport + sevenEight 全討伐、残 sorryAx = dadeHypS parity のみ)。これによる
本 issue への影響:

1. **gap#2 (support-widening) は A(S) で解消の見込み**: 旧診断は「foundation の support (C')^# が
   H^# を含まない」だったが、**H^# ⊆ A(S) が成立** (h ∈ H^# = Sσ^# は x := h 自身を Sσ^#-witness
   に y ∈ C(x) を満たし、H ≤ S′ ゆえ mem_honestTypeP2ASet の 3 条件を満たす)。つまり
   A₀(S)-widening を待たず、A(S)-coherence (`coherent_H0Cprime_S` を sSet_coherent_indS_A ベースに
   re-point 済のもの) の `extends_on_supported` が zero-degree の H^#-supported 差を被覆する。
   `tau1S_apply_induce_sub` はこの route で buildable 候補。
2. **⚠ field 署名の宿題は残る**: `CharacterDegreeData.tau1S_apply_induce_sub` / `tau1S_inner_induce`
   / `tau1S_induce_mem_ZIrr` は ∀ irr θ (P⊄Ker 無し、equal-degree 無し) のまま。update #6 の指摘
   通り P⊄Ker (と apply_induce_sub は zero-degree 化 or 別処理) の要否を consumer
   (Canonicalization:277/1049, NormEstimates:806) の実引数と突き合わせて設計する必要。
3. **残 field 対応表 (現状)**: inner_induce/mem_ZIrr = engine landed (P⊄Ker 付き) /
   induce_inner_eta = (A) core engine landed / apply_induce_sub = 上記 route 1 /
   mu_col_tau1_eta_col_one + mu_tau1_formula = **mu_tau1red (13.6)-(13.9) port (major、未着手)** /
   mu_j_linear_induced (13.3.a) / delta_eq_one (13.3.c) = 要確認。

**次**: b-sorry 再 census (subagent 実行中) の結果と突き合わせ、`character_degree_analysis`
(Machinery135:178、S15 最上流 sorry) の assembly 設計 (field 署名調整の要否含む) に着手。

## 2026-07-13 更新 #2 (lane b, /loop) — 再 census 結果 + (13.3) assembly 計画 (正本)

**census (subagent、comment-strip、17 bare sorry)**: S15_SAndT_Setup+S15_SAndT+S14 のうち、本日の
`sSet_coherent_indS_A` landing で解除されるのは **`character_degree_analysis` (Machinery135:181) のみ**。
他は T-side (13.4)/9013・§14/BG§16・(13.10) analytic・typeP_Galois §14 に gated、`sibleyTarget_S` は
vestigial (do-not-complete 維持)。`sibleyTarget_frobI` (12.6) は §14 type-I Frobenius 系で別物。
⚠ S15_CaseACoherence の docstring に「sole residual is the refuter」等の stale 記述が残存 (本日
refuter closed 済) — 次の編集時に更新。

### CharacterDegreeData assembly 計画 (fields 9)

carrier `tau1S := hyp.tau1S_ofHonest hG chief` (= sSet_coherent_indS_A → coherent_H0Cprime_S →
extension、landed)。

1. **tau1S_apply_induce_sub** ((13.2.e)): H^# ⊆ A(S) (更新 #1) → zero-degree 差は A(S)-supported →
   `extends_on_supported`。⚠ field は equal-degree 仮定無し: θ,θ' irr with P⊄Ker は同 degree とは
   限らない → **P⊄Ker + zero-degree の要否を consumer 実引数 (Canonicalization:277/1049 の θ.2) と
   突き合わせ、field 署名を amend** (b-owned structure; consumer 側は μ-column/λ 由来で P⊄Ker・
   同 degree uq を満たすはず — 要 build 検証、lane-c consumer (CountingLayer:1740) も再 compile 確認)。
2. **tau1S_inner_induce / tau1S_induce_mem_ZIrr**: engines landed
   (`tau1S_ofHonest_inner_induce`/`_induce_mem_ZIrr`、P⊄Ker 付き) — field 署名 amend (P⊄Ker 追加) で直結。
3. **tau1S_induce_inner_eta** ((5.3.b)): (A) core engine `coherentIndS_image_inner_eta_eq_zero`
   (S15_SAndT_Setup/CoherenceEtaOrthogonality) landed — 接続のみ。
4. **mu_j_linear_induced** ((13.3.a)): 既存 §9 stock の family→Ind_{PC}(linear) 方向
   (isIndHC / mu_j_isIndPC 系) から derivable 見込み — 最初の brick 候補。
5. **mu_col_tau1_eta_col_one ((13.9.a)) / mu_tau1_formula ((13.3.c)) / delta_eq_one**: **mu_tau1red
   (Coq PFsection13 (13.6)-(13.9)) deep port が必須** — P1_int2_lb / 2-sided norm 下界 /
   FTtypeP_sum_Ind_Fitting_lb (13.6) / FTtypeP_sum_cycTIiso10_lb (13.7)。repo に template 無、
   major fresh port (~1-2 session、subagent 委譲候補)。

**着手順 (文書順)**: 4 (13.3.a) → 1-3 (13.2.d/e 系 field 署名 amend + engine 接続) → 5 (13.6-13.9 port)
→ producer assembly。

## 2026-07-13 更新 #3 (lane b, /loop) — field 対応表の訂正: (13.3.a) は landed 済

- **mu_j_linear_induced ((13.3.a)) = `Hypothesis.mu_j_isIndPC` (DegreesFirstSplit.lean:766) が
  landed 済・sorry-free** (docstring が field の materialization と明記)。brick 4 は完了扱い。
- ⟹ CharacterDegreeData 9 fields のうち **未充足の本物の数学は mu_tau1red 系 3 fields
  (mu_col_tau1_eta_col_one / mu_tau1_formula / delta_eq_one) のみ** = Coq PFsection13
  (13.6)-(13.9) norm-bound machinery の fresh port。他は landed engine の接続 + field 署名 amend
  (P⊄Ker / zero-degree) のみ。
- **次 iteration**: mu_tau1red port に着手 — Coq PFsection13.v の mu_tau1red / (13.6)
  FTtypeP_sum_Ind_Fitting_lb / (13.7) FTtypeP_sum_cycTIiso10_lb を精読し S-side statement を設計、
  chunk 分割して build (subagent 委譲可)。

## 2026-07-13 更新 #4 (lane b, /loop) — ★再診断: 3 fields は (13.3.c)、"(13.6)-(13.9) port" は誤り

**更新 #3 の「次 = mu_tau1red (13.6)-(13.9) deep port」は誤診断。撤回する。** Coq PFsection13 精読で確定:

- **(13.3.c) は (13.6)-(13.9) の上流**: `FTtypeP_coherence` (13.3.c main, `PFsection13.v:347`) と
  `FTprTIsign` (13.3.c first δ=1, `:281`) は、norm-bound machinery `FTtypeP_sum_Ind_Fitting_lb`
  (13.6, `:595`) 等より**前**に証明される。Coq Section-local lemma は順序証明ゆえ前方依存は構文上
  不可能。Coq コメント (`:335-337`) も「(13.3.c) の reformulation は (13.7)(13.8)(13.9) *で使われる*」と
  明記 = (13.3.c) は下流でなく上流。`FTtypeP_coherence` の実依存は `FTtypeP_facts` (13.2 coherence) +
  `uniform_prTIred_coherent` (**PFsection4**) + `FTtypeP_coherent_TIred` (**PFsection8**) + `delta1`。
  **どれも (13.6)-(13.9) でない。** ⟹ mu_tau1red / P1_int2_lb / FTtypeP_sum_*_lb の port は**不要**。

### CharacterDegreeData 9 fields の正しい状態 (grep 検証済)

| field | Pf | 状態 |
|---|---|---|
| tau1S (carrier) | (13.2.d) | `tau1S_ofHonest` landed。chief = `S11.exists_chiefFactorData hG data` |
| tau1S_inner_induce | (13.2.d) | engine `tau1S_ofHonest_inner_induce` landed (要 P⊄Ker 署名 amend) |
| tau1S_induce_mem_ZIrr | | engine `tau1S_ofHonest_induce_mem_ZIrr` landed |
| tau1S_induce_inner_eta | (5.3.b) | engine `coherentIndS_image_inner_eta_eq_zero` / `coherent_extension_orthogonal_eta_of_mem_Sset` landed |
| tau1S_apply_induce_sub | (13.2.e) | `extends_on_supported` + H^#⊆A(S) route |
| mu_j_linear_induced | (13.3.a) | `mu_j_isIndPC` landed |
| **delta_eq_one** | (13.3.c-first) | **S-side `delta_eq_one_S` 証明済** (`u_modEq_one`+`mu_apply_one_eq_u`)。T-side (deltaPrime) = swap+`delta_eq_one_S(swap)` だが `IsTypeP2 T` 要 → `T_typeII` は **S16 (TTypeII.lean:986)** = character_degree_analysis (S15 Machinery135) の**下流** ⟹ producer 内で使うと循環。**layering 課題** (下記) |
| **lambda** (+3 fields) | (13.3.b) | **未実装**。最多消費 (Canon:79/150/209/523, NormEstimates:799, CountingLayer:1770)。typeP_Galois 場合分け (calS 全 reducible 時に irr λ が在るか) の subtlety あり — 要設計確認 |
| **mu_col_tau1_eta_col_one / mu_tau1_formula** | (13.3.c-main) | **未実装 = keystone**。`tau1S(∑ᵢμᵢⱼ)=δⱼ∑ᵢηᵢⱼ` の coherence-pin。S11-world analog = `coherent_sOf_H0C_extension_muColumnSum_pin_of_irr` (S13_Orthogonality:290, γ-trick+正定値 pin)。S15 world 未実装。mu_col は formula + mu_j_isIndPC の系 |

### frontier = (13.3) assembly campaign (multi-iteration)

genuinely-missing な S-side math: **(13.3.b) lambda 構成** (document 順で先) と **(13.3.c) formula keystone**。
T-side (deltaPrime / tau1T carrier) は S16 layering 複雑 (character_degree_analysis が IsTypeP2 T を
どこで得るか = producer 署名に IsTypeP2 T を追加するか、T_typeII を上流移設するか、の設計判断)。

**着手方針**: 難所回避せず (13.3.c) keystone formula `tau1S_ofHonest(∑ᵢμᵢⱼ)=δⱼ·∑ᵢηᵢⱼ` を S15 world で
build (S13_Orthogonality の γ-trick pin を S15 coherence に port/bridge)。δ=1 は `delta_eq_one_S` で
`=∑ᵢηᵢⱼ` に。次いで (13.3.b) lambda。**subagent 委譲は "port (13.6)-(13.9)" では NG** (誤ターゲット)。

## 2026-07-13 更新 #5 (lane b, /loop) — (13.3.c) keystone formula の pin 素材 landed + assembly recipe

再診断 (更新 #4) に基づき (13.3.c) main formula `tau1S(∑ᵢμᵢⱼ)=δⱼ·∑ᵢηᵢⱼ` を **honest bottom-up** で構築中。
positive-definiteness pin の 3 素材を Machinery135 に landed (全 sorry-free, commit f2ac3a3f/b6b8876c):

- `Hypothesis.muColumn_inner_self` : ⟨∑ᵢμᵢⱼ, ∑ᵢμᵢⱼ⟩ = q  (mu_orthonormal 対角和)
- `Hypothesis.etaColumn_inner_self` : ⟨∑ᵢηᵢⱼ, ∑ᵢηᵢⱼ⟩ = q  (eta_orthonormal 対角和)
- `inner_pin_eq` : ⟨x,x⟩=⟨y,y⟩=⟨x,y⟩=n (star n=n) ⟹ x=y  (‖x−y‖²=0、正定値)

### assembly recipe (次 iteration — 下流 leaf、Machinery135+CaseACoherence を import)

`x := tau1S_ofHonest hG chief (∑ᵢμᵢⱼ)`, `y := ∑ᵢηᵢⱼ`, `n := (q:ℂ)`。`inner_pin_eq hxx hyy hxy (by simp)`:
- **hyy** = `etaColumn_inner_self` (済)
- **hxx** = isometry: `⟨tau1S(∑μ), tau1S(∑μ)⟩ = ⟨∑μ,∑μ⟩ = q`。
  `(hyp.coherent_H0Cprime_S hG chief).extension_inner_eq (∑μ) (∑μ) hmem hmem` ∘ `muColumn_inner_self`。
  ⚠ `tau1S_ofHonest = coherent_H0Cprime_S.extension` (定義)。**hmem = ∑μ ∈ zSpan (mkSection11CharacterDataS_honest).S** の family alignment が要:
  `mu_colSum_mem_sOf_H0` (HypothesisBasics:815) は ∑μ ∈ `S11.sOf (toTypesIIIIIIVSetupS) chief.H0` を与える。
  `(mkSection11CharacterDataS_honest).S` = この sOf family と一致するか (定義展開) を確認して zSpan membership を得る。
- **hxy** = ★step 3 = **γ-trick** `⟨tau1S(∑μ), ∑η⟩ = δⱼ·q` (δⱼ=1 は `delta_eq_one_S` で正)。
  = (13.3.c) の本体 hard core。S11-world に完全 analog `coherent_sOf_H0C_extension_muColumnSum_pin_of_irr`
  (S13_Orthogonality:290, γ=ξ(1)μⱼ−μⱼ(1)ξ の A₀-supported Dade + 正定値 pin, ~100 行) が在り、
  S15 world に port/bridge する。**これが残る唯一の本物の数学** (他は上記 pin 代数で機械的)。

⚠ 注意: character_degree_analysis (Machinery135) は tau1S_ofHonest (CaseACoherence) を **見えない** (import DAG)。
producer assembly 全体は両者を import する下流 leaf に置くか、tau1S_ofHonest を上流移設する architectural 判断が要る
(別途)。formula 自体も同 leaf。

**次 iteration**: 下流 leaf 新設 → family alignment で hxx wiring → step 3 は
`coherent_sOf_H0C_extension_muColumnSum_pin_of_irr` の S15 port (subagent 委譲候補、ただし "port (13.6)-(13.9)"
ではなく "S13_Orthogonality の γ-trick pin を S15 tau1S_ofHonest に port" が正しい指示)。

### 追記 (更新 #5): family alignment の要注意点 (hxx wiring)

coherence `coherent_H0Cprime_S` の domain は **H0Cprime** support 側の family
(`S11.sOf hyp.s11Setup hyp.H0Cprime`, CaseA coherence が使う; S11_NineElevenCaseA:88/542 参照) だが、
`mu_colSum_mem_sOf_H0` (HypothesisBasics:815) が与えるのは **chief.H0** 側 (`sOf ... chief.H0`)。
**support mismatch (H0Cprime vs chief.H0)** ゆえ、∑μ ∈ zSpan(coherence domain) を得るには
sOf の containment/monotone (chief.H0 ⊆ H0Cprime 方向 or その逆) を経由する必要がある
(`sOf_subset_SOf` / `inducedKernelFamily_antitone` 系、`induce_H_mem_zSpan_S` の証明が同種の bridge を
既に踏んでいる — その pattern を流用可)。次 iteration はまず `induce_H_mem_zSpan_S`
(S15_CaseACoherence:801) が `∑μ`/`Ind_{H}θ` を coherence domain の zSpan に入れる正確な形を読み、
それを ∑μ = Ind_{S'}ψ (mu_colSum_eq_induce) に適用する。

### 追記² (更新 #5): isometry wiring は clean と確定 — 残る hard core は step 3 のみ

family alignment 解決: `(mkSection11CharacterDataS_honest).S = sSet (toTypesIIIIIIVSetupS)` (定義、
ChiefFactorCore:653 `def S _chars := sSet data`)。`sOf_subset_sSet` (ChiefFactorCore:165,
`sOf data Y ⊆ sSet data`) と `mu_colSum_mem_sOf_H0` (∑μ ∈ sOf chief.H0) で ∑μ ∈ sSet = .S。よって:

```
have hmem : (∑ i, hyp.mu i j) ∈ S07.zSpan (hyp.mkSection11CharacterDataS_honest hG chief).S :=
  Submodule.subset_span (sOf_subset_sSet _ _ (hyp.mu_colSum_mem_sOf_H0 hG chief j hj))
have hxx : ⟨tau1S_ofHonest hG chief (∑μ), tau1S_ofHonest hG chief (∑μ)⟩ = (q:ℂ) := by
  rw [Hypothesis.tau1S_ofHonest,
      (hyp.coherent_H0Cprime_S hG chief).extension_inner_eq _ _ hmem hmem,
      hyp.muColumn_inner_self]  -- tau1S_ofHonest = coherent_H0Cprime_S.extension (defeq)
```

⟹ **assembly は step 3 (γ-trick `⟨tau1S(∑μ), ∑η⟩ = q`) を除き全て機械的**:
`inner_pin_eq hxx (hyp.etaColumn_inner_self j) hstep3 (by simp [Complex.star_def])`。
step 3 = `coherent_sOf_H0C_extension_muColumnSum_pin_of_irr` (S13_Orthogonality:290) の S15 port。

**次 iteration 手順**: (1) 下流 leaf 新設 (import Machinery135 + S15_CaseACoherence、cycle 無しを build 確認)、
(2) 上記 hxx/hyy/hn を wire + step 3 を genuine sorried lemma `Hypothesis.muColumn_tau1_inner_etaColumn`
として分離 → formula `Hypothesis.tau1S_ofHonest_muColumn_eq_etaColumn` を build green 化、
(3) step 3 の γ-trick port に着手 (これが (13.3.c) の唯一残る本物の数学)。

## 2026-07-13 更新 #6 (lane b, /loop) — ★(13.3.c) formula landed (build-green)、残る本物の数学は γ-trick 1 点

`OddOrder/Peterfalvi/S15_SAndT_Setup/MuColumnPin.lean` 新設 (commit c23fe9f5):

- **`Hypothesis.tau1S_ofHonest_muColumn_eq_etaColumn`** : `τ₁(∑ᵢμᵢⱼ) = ∑ᵢηᵢⱼ` (j≠0, δ=1) =
  (13.3.c) main **build-green**。pin/isometry/norm/family-alignment 全て **sorry-free** で proven。
- **`Hypothesis.muColumn_tau1_inner_etaColumn`** : `⟨τ₁μⱼ, ∑ηᵢⱼ⟩ = q` = **唯一の sorry** = γ-trick。

⟹ (13.3.c) formula の残る本物の数学は **γ-trick (`muColumn_tau1_inner_etaColumn`) 1 点のみ**。
これは `coherent_sOf_H0C_extension_muColumnSum_pin_of_irr` (S13_Orthogonality:290、S11/S12-world、
γ=ξ(1)μⱼ−μⱼ(1)ξ の A₀-supported Dade + 正定値 pin) の **S15-world port**。

### 次 iteration = γ-trick port (`muColumn_tau1_inner_etaColumn`)

S13_Orthogonality:290 の証明を精読し S15 world (tau1S_ofHonest coherence, hyp.mu/eta grid,
honestTypeP2A0Set support) に移す。必要な S15 素材: `mu_diff_support` (μ列差の A₀-support, field)、
`extends_on_supported` (Dade=Ind on A₀-supported)、`tau1S_induce_inner_eta` (η⊥coherence image、
但し H=PC induction 側 — mu列は S'induction ゆえ別、要 case 確認)、`eta_eq_tau_omega`。
Coq は `FTtypeP_coherence` (PFsection13:347)。has-irr 場合と uniform 場合の 2 分岐に注意。
**subagent 委譲時の正しい指示** = 「S13_Orthogonality の γ-trick pin を S15 tau1S_ofHonest に port」
(NOT "port (13.6)-(13.9)" — 更新 #4 の誤診断)。

## 2026-07-13 更新 #7 (lane b, /loop) — γ-trick は S13 clean port 不可、S15-abstract 証明が必要

S13_Orthogonality:290 `coherent_sOf_H0C_extension_muColumnSum_pin_of_irr` の完全な証明を精読した結果:
**S12 concrete 機構に深く依存** — `inducedKernelFamily_*` (mem_intDegree/pairwise_orthogonal/
inner_self_real_pos/conjDiff_support)、`SOf_coherent_extension_cross_orthogonal`、
`SOf_coherent_extension_eq_sum_memberRFamily`、`certainTypeR`/`certainTypeRImage`/
`certainTypeOmegaSigma_muColumnChar_eq_aligned` (world-bridge)、`toHypothesis46`/`muColumnChar`/
`columnFamily.sign_eq`。これらは S12 `Hypothesis M` の concrete grid 構成であり、
**S15 の abstract `Hypothesis` (mu/eta が抽象 field) には移植できない**。

⟹ `muColumn_tau1_inner_etaColumn` は S15-abstract fields から fresh に証明する必要
(= Coq `FTtypeP_coherent_TIred` (PFsection8) の S15-abstract 版)。利用可能な abstract 素材:
coherence (extends_on_supported = Dade on A₀-supported / extension_inner_eq isometry) +
mu_diff_support (μ列差 A₀-supported) + mu_definition (μ↔ω via induce) + eta_eq_tau_omega +
mu/eta_orthonormal + delta_eq_one_S。⚠ γ-trick が要する「irreducible ξ ∈ 𝒮」が abstract field で
保証されるか (has-irr vs uniform-degree 場合分け) は要確認 — 保証されないなら **abstract field
不足の設計課題**が露見する可能性 (lambda (13.3.b) の typeP_Galois subtlety と同根)。

**subagent に深掘り委譲中** (background): abstract route の特定 + 証明試行 or 精密 blocker 報告。

## 2026-07-13 更新 #8 (lane b, /loop) — ★★重大発見: (13.3.c) pin は carrier 再設計が必須 (unpinned choice)

subagent 調査 + **自己検証済**の重大な設計発見 (CLAUDE.md doneness 検証 [[scaffold-sorry-free-not-done]]
= carrier 構成可能性で判定、が scaffold を捕捉):

### 発見: `muColumn_tau1_inner_etaColumn` は現 carrier で証明不可 (flip witness で偽)

- `tau1S_ofHonest := (coherent_H0Cprime_S).extension`、`coherent_H0Cprime_S := (sSet_coherent_indS_A).some`。
- **`sSet_coherent_indS_A` (S15_CaseACoherence:689) は pin 無しの bare `Nonempty (S07.IsCoherent Ind_S^G 𝒮 A(S))` を返す** (694-696、検証済)。
- `S07.IsCoherent` は data-carrying structure (`extension : IntegralCharacterMap`、NormInequalities:480)
  ゆえ `.some = Classical.choice` は**任意の inhabitant** を選ぶ。
- `IsCoherent Ind_S^G 𝒮 A(S)` は**複数 inhabitant を持つ**: all-reducible 場合 (clifford_dichotomy caseB、
  type-P₂ S で到達可)、符号反転 `F(μ_j) := −∑ᵢη_{i,finNeg j}` も valid (isometric・A(S)-supported 差
  `μ_j−μ_{finNeg j}` 上で Ind に一致・ZIrr)。この F では `⟨F(μ_j),Ω_j⟩ = 0 ≠ q`。
- ⟹ **μ-column pin は coherence inhabitant 不変でない**。`.some` では決まらず、**証明不可能**。
  Coq は `typeP_TIred_coherent tau1` (PFsection13:338) として **coherence に pin を bundle** している。

⟹ **更新 #6 の「formula build-green で landed」は honest-done でない**: `tau1S_ofHonest_muColumn_eq_etaColumn`
は上記の証明不可能 sorry (`muColumn_tau1_inner_etaColumn`) に載っている scaffold。pin/isometry/norm 素材
(muColumn/etaColumn_inner_self, inner_pin_eq) は valid で再利用されるが、**単独 sorry では pin は閉じない**。

### 真の frontier = carrier 再設計 (coherence に pin を bundle) — 全 engine 実在確認済

`sSet_coherent_indS_A` を **pin 込み** (例 `Nonempty (Σ c : IsCoherent …, ∀ j≠0, c.extension(∑ᵢμᵢⱼ)=∑ᵢηᵢⱼ)`)
に強化 → `coherent_H0Cprime_S := .some.1` に projection、`tau1S_ofHonest` は型不変、pin は `.some.2`。
`clifford_dichotomy` で分岐 (S15_CaseACoherence:697 の既存分岐と同型):
- **caseA (has-irr)**: 任意 coherence + γ-forcing。engine: `sSet_coherent_extension_eq_sum_memberRFamily`
  (SSetMemberRFamily:765、任意 coherence 拡張 = signed R-family 和) + `sSet_memberRFamily_imageSet_of_red`
  (:476、reducible μ_j の R-family = {η_ij}∪{−η_{i,finNeg j}}) + `sSet_irr_memberRFamily_eta_inner`
  (:519、irr member ⊥ η) + `caseA_exists_irreducible_qa` + `tauS_mu_cross` (BridgeCharacter:917, sorry-free)。
- **caseB (all-reducible)**: 符号を + に固定した pinned coherence。engine: `sSet_coherent_dade_caseB`
  (CaseBReducibleCoherence:46) / `uniform_degree_coherence_of_families` (S07_PivotCoherence)。

⚠ signature: `coherent_H0Cprime_S`/`tau1S_ofHonest` の**型は不変**に保つ (下流 engine
tau1S_ofHonest_inner_induce 等は forced property のみ使うので影響なし)。内部 def のみ pin projection に変更。
これで `muColumn_tau1_inner_etaColumn` は pin `.some.2` から直接 discharge (MuColumnPin の inner_pin_eq scaffold は
optional 化)。⚠ subagent の engine 名は一部 M-side 混同あり、上記は自己 grep で S15 実名を確定済。

## 2026-07-13 更新 #9 (lane b, /loop) — carrier 再設計の feasibility 確定 (全ピース実在) + 実装 recipe

更新 #8 の bundling が feasible と確定。追加で判明した実装の鍵:

- **map-type subtlety**: `sSet_coherent_indS_A` は `IsCoherent hyp.indS` (`indS θ = induce hyp.S θ`、純 Ind_S^G)
  を返すが、linchpin engine `sSet_coherent_extension_eq_sum_memberRFamily` (SSetMemberRFamily:765) は
  **dade-coherence** `IsCoherent (dadeIntegralCharacterMap (dadeHypS…))` を取る。
- **bridge 実在**: `IsCoherent.congrMap hindS_dade` で indS-coherence → dade-coherence 変換
  (`S15_CaseBReducibleCoherence.lean:436` に既存使用例 `cohS₂ := cohS₂_indS.congrMap hindS_dade`)。
  extension field は不変ゆえ pin (extension の性質) は両 map 間で transport 可。

### 実装 recipe (次 iteration、複数回可)
1. engine で `c'.extension(∑ᵢμᵢⱼ) = ∑_{α∈E} α`, `E ⊆ (memberRFamily (∑μ)).imageSet`。
   `sSet_memberRFamily_imageSet_of_red` (:476) で imageSet = `{ηᵢⱼ}ᵢ ∪ {−η_{i,finNeg j}}ᵢ`。isometry
   (‖∑μ‖²=q, muColumn_inner_self) + orthonormal で `|E|=q`。
2. **+符号 (E={ηᵢⱼ}) の強制**:
   - caseA: irreducible member ξ (`caseA_exists_irreducible_qa`) に対し `sSet_irr_memberRFamily_eta_inner`
     (:519、irr member の像 ⊥ η) + `tauS_mu_cross` (BridgeCharacter:917) で γ-forcing → mix/−符号を排除。
   - caseB: `sSet_coherent_dade_caseB` (CaseBReducibleCoherence:46) を +符号で構成 (M-side
     `exists_pinned_coherent_sOf_H0C_of_all_reducible` (S13_Orthogonality:560) の S-side 類比)。
3. bundle: `sSet_coherent_indS_A` の戻り値を `Nonempty (Σ' c : IsCoherent hyp.indS 𝒮 A(S),
   ∀ j≠0, c.extension(∑ᵢμᵢⱼ)=∑ᵢηᵢⱼ)` に。`coherent_H0Cprime_S := .some.1` (型不変)、
   pin accessor `.some.2`。下流 engine (tau1S_ofHonest_inner_induce 等) は forced property のみ
   ゆえ無影響。
4. `muColumn_tau1_inner_etaColumn` を pin accessor から discharge。

**安全策**: まず新 `sSet_coherent_indS_A_pinned` を additive に建て (既存 coherent_H0Cprime_S 不変)、
branch pin 2 本を sorried-skeleton で landing → 各 branch pin を proven → 最後に coherent_H0Cprime_S
rewire。これで load-bearing carrier の破壊リスクを最小化。

## 2026-07-13 更新 #10 (lane b, /loop) — carrier 再設計の深度確定: caseB は S07 pin 露出が必要

更新 #9 の実装に着手し、caseB 分岐が想定より深いことが判明 (精読で確定):

- **caseA (has-irr)**: 任意 coherence で γ-forcing 可 (`sSet_irr_memberRFamily_eta_inner` +
  `caseA_exists_irreducible_qa`)。⟹ `sSet_coherent_indS_caseA.some` + 後付け pin 証明で bundle 可。S15-local。
- **caseB (all-reducible)**: ⚠ flip witness が valid ゆえ **任意 coherence で pin 証明不可**。
  `sSet_coherent_dade_caseB` (:46) は `uniform_degree_coherence_of_families` (S07_PivotCoherence:793)
  経由だが、**両者とも bare `Nonempty (IsCoherent)` を返し pin を expose しない** → `.some` は任意 inhabitant
  → caseB の pin も現状決まらない。
  - 必要: `uniform_degree_coherence_of_families` / `pivotCoherence` (S07、**shared infra**) を
    `Nonempty (Σ c, c.extension(pivot)=<pivot partner>)` に強化して pin (pivot の像) を露出、
    or S-side glue 構成 (M-side `exists_pinned_coherent_sOf_H0C_of_all_reducible` (S13:560) の類比
    — ただし M-side は concrete glue machinery 依存)。
  - `pivotCoherence` は pivot η₁ を specific に写すので **pin は構成上決まっている**が、`Nonempty` が
    witness を消している。露出は S07 の return type 変更 (shared、9000 claim 対象の可能性)。

### frontier 現状 (正確)
(13.3.c) formula は「carrier に μ-column pin を bundle」に帰着し、その pin bundle は:
1. caseA = S15-local な γ-forcing (中程度)
2. caseB = **S07 `uniform_degree_coherence_of_families` の pin 露出** (shared infra 強化) が本丸

= 深い multi-layer 課題。fresh session で S07 pin-露出強化から着手推奨 (shared ゆえ着手前に 9000 claim +
既存 open 9000 scan)。MuColumnPin の formula scaffold は bundle 完成まで sorried-cite で保持 (soundness 問題なし
= tau1S_ofHonest は valid coherence、pin が未確定なだけ)。

## 2026-07-13 更新 #11 (lane b, /loop) — ★実装プラン確定: Route 2 (S15-local glue mirror) — 全ピース sorry-free で在庫確認済

更新 #10 の「S07 pin 露出 (shared infra)」より**優れる route を確定**。精読で全ピースが揃った:

### 発見: pin は「diff lemma (sorry-free) + pivot pin (carrier bundle)」に分解できる

`muColumn_tau1_inner_etaColumn` (`⟨τ₁μcol_j, ηcol_j⟩ = q`, ∀ j≠0) は次に帰着:
1. **diff lemma** `τ₁(μcol_j) − τ₁(μcol_1) = ηcol_j − ηcol_1` — **sorry-free**:
   - μcol_j − μcol_1 ∈ zSupportedSpan 𝒮 A(S): 両 column ∈ 𝒮 (`mu_colSum_mem_sOf_H0`+`sOf_subset_sSet`)、
     degree 一定 qu (`mu_apply_one_eq_u`、**case 非依存** — mixed-degree は irr qa メンバーの話で μ-column は常に uq) ⟹ 差の value(1)=0 ⟹ A(S)-supported (`sSet_member_support_subset`)。
   - τ₁(diff) = indS(diff) (`IsCoherent.extends_on_supported`) = dadeHypS(diff) (`sInstance_dade_eq_induce`)
   - dadeHypS(μcol_j − μcol_1) = ηcol_j − ηcol_1: `tauS_mu_cross` (BridgeCharacter:917, **sorry-free**、
     任意列 j≠k) を i で和。既存 `tauS_muColumn_diff_eq` (SSetMemberRFamily:148) の一般列版
     (conjugate 制約を外す)。dadeHypS0↔dadeHypS↔indS reconciliation は `sInstance_dade0/S_eq_induce` で解決済。
2. **pivot pin** `τ₁μcol_1 = ηcol_1` (or `⟨τ₁μcol_1, ηcol_1⟩=q`) — **carrier bundle** (deep, flip witness ゆえ .some 不可):
   - **caseB (all-reducible)**: M-side `exists_pinned_coherent_sOf_H0C_of_all_reducible` (S13_Orthogonality:560,
     ~360 行 proven) を mirror。`coherentImageMap` (S07_Coherence/PsiDecomposition:951, **shared, b 所有**) で
     μ-column ↦ aligned η-column を構成で pin。入力 = mu_orthonormal (member 直交) / eta_orthonormal
     (image 直交) / column 恒等式 (residual、= diff lemma の dade 版) / degree 一定 / eta ∈ ZIrr。全て S-side 在庫あり。
   - **caseA (has-irr)**: M-side `coherent_sOf_H0C_extension_muColumnSum_pin_of_irr` (S13_Orthogonality:290) を
     mirror。任意 coherence + irreducible member の γ-trick で pin (flip 対称性を irr が破る)。carrier 構成不要
     (既存 .some + 後付け証明)。

### なぜ Route 2 > update #10 の S07 route
- **S07 shared infra 非接触**: `coherentImageMap` は既存 (b 所有 S07_Coherence)、改変不要。`uniform_degree_coherence_of_families`
  の return type 変更 (10+ consumer に波及) を回避。⟹ **9000 claim 不要** (全て b-owned S15 + 既存 shared 利用)。
- **全 column を pin** (S07 pivot 露出は pivot 列のみ)。
- M-side に **proven template 実在** (`exists_pinned_coherent_sOf_H0C_of_all_reducible` / `..._pin_of_irr`)。

### 実装順 (upstream-first、複数 iteration)
1. [ ] diff lemma + general 列 dade diff (sorry-free) → `muColumn_tau1_inner_etaColumn` を pivot (j=1) に帰着
2. [ ] caseB glue: `sSet_coherent_...caseB` pinned 版 (coherentImageMap mirror)
3. [ ] caseA γ: `..._pin_of_irr` S-side mirror
4. [ ] bundle → `sSet_coherent_indS_A` pinned 化 (安全策: additive、coherent_H0Cprime_S 型不変)
5. [ ] pivot pin discharge → MuColumnPin scaffold 完成

⚠ soundness: 現 `tau1S_ofHonest` は valid coherence (pin 未確定なだけ)、MuColumnPin scaffold は bundle 完成まで
sorried-cite 保持で問題なし。

## 2026-07-13 更新 #12 (lane b, /loop) — pivot pin の設計確定: dispatch は「has-irreducible by_cases」+ 2 branch の精査

subagent 調査 + M-side γ-trick 精読 (`coherent_sOf_H0C_extension_muColumnSum_pin_of_irr` S13_Orthogonality:290-546) で
pivot pin `tau1S_ofHonest_muColumn_pivot` の構造を確定。**landing 済 (build green)**:
- column-independence 帰着 (更新 #11、commit b9360714): general-j pin → single pivot 列 (sorry-free)
- column 恒等式 hoist + off-diagonal `muColumn_inner`/`etaColumn_inner` (commit 6bdaeeec): glue の upstream infra

### dispatch (M-side に忠実): Clifford dichotomy でなく **`by_cases ∃ξ∈𝒮 irreducible`**
M-side (S13:910-922) は Clifford caseA/B でなく **irreducible member 存在の by_cases**。`push_neg` で
`hallred` が無料。両 branch とも `∃ c:IsCoherent indS 𝒮 A(S), c.extension μcol_1 = ηcol_1` を返す。
S-side 部品 (subagent 確認、全存在):
- reducible member → μ-column: `sSet_reducible_eq_muColumnSum` (SSetMemberRFamily:47) ✅
- irreducible の coherent 像 ⊥ η-grid (crux): `coherentIndS_image_inner_eta_eq_zero` (CoherenceEtaOrthogonality:67) ✅
- pin: `inner_pin_eq` + `muColumn_inner_self`/`etaColumn_inner_self` ✅
- `coherentImageMap` glue (shared, b 所有 S07_Coherence) ✅

### ★重大 subtlety (γ-trick、自己精読で発見): S-side に capstone Ω-isolation が無い
M-side `hkey: ⟨c(μ),Ω⟩=w₁` は capstone `θ=μ−dζ` の dadeHypS 像 = `Ω−d·coh(ζ)` が **Ω を単独 isolate**
(ζ 項は `⟨c(μ),coh(ζ)⟩=⟨c(ξ),coh(ζ)⟩=0` で drop) することに依存。**honest S-side は C'=⊥ で ζ (S(HC) stratum) が
無い** → 唯一の supported capstone = column 差 `μcol_1−μcol_k`、その dadeHypS 像 = `ηcol_1−ηcol_k` (2 列)。
展開すると `⟨c(μcol_1),ηcol_1⟩ − ⟨c(μcol_1),ηcol_k⟩ = q` の **1 方程式**しか出ず、`⟨c(μcol_1),ηcol_k⟩` 項が
残って pin が解けない (M-side の `⟨c(μ),coh(ζ)⟩=0` に相当する drop が S-side に無い — ηcol_k は同 grid で別 family でない)。
⟹ **γ-trick S-side mirror は自明でない**。候補解: (a) uniform (caseB) では irr ξ も degree qu ゆえ
`θ=μcol_1−ξ` (degree 0 supported) が使え、`⟨c(ξ),ηcol_1⟩=0` (crux) で Ω isolate 可能か精査; (b) glue-over-full-family;
(c) Frobenius reciprocity + Res_S(η) の直接計算 (deep char theory)。

### glue-over-full-family の degree 問題
irr も含む全 family を coherentImageMap (columns→ηcol、irr ξ→c(ξ)) で glue: **isometry は成立**
(target 直交・norm 一致: ⟨ηcol_j,c(ξ)⟩=0 crux、⟨c(ξ),c(ξ')⟩=⟨ξ,ξ'⟩)。だが **supported-agreement の residual
論法は uniform degree を要求** (M-side hextends は共通 degree D で residual = x1/D·r)。caseA (mixed qu/qa) で破綻。
uniform (caseB) では columns の residual `r=ηcol_1−dadeHypS(μcol_1)` は column 恒等式で一定だが、irr の residual
`c(ξ)−dadeHypS(ξ)` が同じ r に一致するかは要精査。

### 次段の実装順 (確定)
1. [ ] **all-reducible glue** `exists_pinned_coherent_sSet_of_all_reducible` (M-side S13:560-823 の clean mirror、
   全 member = μ-column ゆえ uniform、residual = column 恒等式で解決) → `by_cases` の hallred branch を close。
   ⟵ 部品全確認済、~150 行 mirror。**まずこれ** (確実)。
2. [ ] has-irreducible branch: 上記 subtlety を candidate (a)/(b)/(c) で解決 (careful design、次 session fresh context 推奨)。
3. [ ] bundle `sSet_coherent_indS_A_pinned` (by_cases) + rewire `coherent_H0Cprime_S` + discharge pivot。

## 2026-07-13 更新 #13 (lane b, /loop) — Coq 戦略で subtlety 解決: pin は uniform μ-column subfamily glue で確立

CLAUDE.md 方針 (行間は Coq 精読) で Coq `FTtypeP_coherence` (PFsection13.v:347-365) を精読。更新 #12 の
γ-trick subtlety を回避する正しい戦略が判明:

### Coq の pin 構成 (γ-trick でない)
```
have [_ [tau1 Dtau1]] := uniform_prTIred_coherent pddS nz_k.  (* uniform μ-column seq に pin 付き coherence *)
set calT := uniform_prTIred_seq pddS k => cohT.
apply: subset_coherent_with cohT ...                          (* full calS へ関連付け *)
```
`uniform_prTIred_coherent` = **uniform-degree μ-column subfamily** (全 reducible、degree qu 一定) 上の
**pin 付き coherence** (`Dtau1` = tau1 が μ-column → η-column)。これは M-side `exists_pinned_coherent_sOf_H0C_of_all_reducible`
= coherentImageMap glue と同型。pin は uniform subfamily で確立 (glue の residual 論法が uniform ゆえ成立)。
`subset_coherent_with` (PFsection5:520 = restriction S2⊇S1) で full family と関連付け。

⟹ **γ-trick (更新 #12 の capstone subtlety) は不要**。pin は uniform μ-column glue で構成的に得る。

### essential buildable piece = uniform μ-column subfamily glue
`exists_pinned_coherent_sSet_of_all_reducible` の S-side mirror だが、対象を **μ-column subfamily
𝒮_μ = {∑ᵢμ_ij : j≠0}** (uniform qu、全 member = column) に取る。全部品確認済 (更新 #12 の inventory)。
これが `IsCoherent indS 𝒮_μ A(S)` + pin `c.extension(μcol_1)=ηcol_1` を構成で与える (residual = column 恒等式で一定)。

### 残る設計課題 = full 𝒮 への transfer
`coherent_H0Cprime_S`/`tau1S_ofHonest` は full 𝒮 (sSet) の coherence。μ-column subfamily の pinned coherence
から full 𝒮 の pinned coherence を得る transfer:
- 現 `sSet_coherent_indS_A` は base subfamily (caseA=S₁(qa) irr / caseB=uniform) を
  `coherent_of_maximal_coherent_pair_refuted` で full へ拡張。
- 拡張が base member 像を保存するなら、base を μ-column subfamily に取れば pin 保存。⟵ 要確認
  (`coherent_of_maximal_coherent_pair_refuted` / retarget が base 像保存か)。
- or Coq `subset_coherent_with` 型: full 𝒮 coherence を μ-column subfamily に restrict しても pin は
  subfamily 上の像だから、full coherence が subfamily 上で pin を満たすよう構成すればよい。

### 次段 (確定、fresh context 推奨)
1. [ ] uniform μ-column subfamily glue `exists_pinned_coherent_sSet_muColumn` (coherentImageMap mirror、~150 行)
2. [ ] transfer 設計確定 (base 像保存 or restrict 論法) → `sSet_coherent_indS_A_pinned`
3. [ ] rewire `coherent_H0Cprime_S` + discharge `tau1S_ofHonest_muColumn_pivot`

本 session landing: column-independence 帰着 (b9360714) + column 恒等式 hoist/off-diagonal (6bdaeeec) +
γ-trick subtlety 発見 + Coq 戦略確定。pivot pin は uniform glue + transfer の 2 段で次段。

## 2026-07-13 更新 #14 (lane b, /loop) — ★完全 architecture 確定: subfamily glue + bridge transfer (全 tool 実在)

更新 #13 の transfer を精査し、**pivot pin の完全な解法**が確定 (全て proven M-side template + shared tool の mirror):

### 3 段構成 (by_cases 不要、uniform transfer)
1. **subfamily glue** `exists_pinned_coherent_sSet_muColumn` (or all-reducible full 𝒮 版):
   μ-column subfamily 𝒮_μ = {∑ᵢμ_ij : j≠0} (uniform qu、全 reducible) 上の pinned coherence を
   `coherentImageMap` (S07_Coherence/PsiDecomposition:951) で構成。pin `c_μ.extension(μcol_1)=ηcol_1` を
   `coherentImageMap_apply_eq_of_orthogonal` で。residual = `dadeHypS_muColumn_diff` で一定。
   ⟵ **subagent build 中** (2026-07-13、all-reducible full 𝒮 版 = M-side `exists_pinned_coherent_sOf_H0C_of_all_reducible` mirror)。
2. **bridge transfer** = M-side `coherent_SOf_H0C_of_column_identities` (S13_Orthogonality:858) の mirror:
   `coherentUnion_of_glued_of_bridge` (bridge_coherent、S07_Coherence/CoherenceUnion) で X=𝒮_μ (pinned c_μ) +
   Y=irreducibles (既存 sSet_coherent_indS_A restrict) を **column 差 bridge に沿って glue**、full 𝒮 の
   pinned coherence を得る。pin 保存 = ν が X 上で c_μ に一致 (hagreeX)。
   - **plain `coherentUnion_of_glued` (:1186) は hgen (generation) を要し mixed degree (caseA qu/qa) で破綻**
     ⟹ bridge 版が必須 (M-side が bridge を選んだ理由、S13:833 docstring)。
   - image 直交 (himg_ortho: ⟨ηcol, c(irr)⟩=0) = **crux `coherentIndS_image_inner_eta_eq_zero`** (CoherenceEtaOrthogonality:67)。
   - source 直交 (⟨μcol, irr⟩=0) = 𝒮 pairwise orthogonality。
3. **bundle + rewire**: `sSet_coherent_indS_A_pinned := ⟨transfer coherence, pin⟩` →
   `coherent_H0Cprime_S := .choose` (型不変) → `tau1S_ofHonest_muColumn_pivot := .choose_spec` で discharge。

### 全 tool 実在確認済
- `coherentImageMap` / `_apply_eq_of_orthogonal` ✅ (shared, b 所有)
- `coherentUnion_of_glued_of_bridge` (bridge_coherent) ✅ (S07_Coherence、b 所有)
- crux `coherentIndS_image_inner_eta_eq_zero` ✅
- column 恒等式 `dadeHypS_muColumn_diff` / off-diagonal `muColumn_inner`/`etaColumn_inner` ✅ (更新 #11-#13 で landing)
- `sSet_reducible_eq_muColumnSum` / `sSet_finite` / `eta_mem_ZIrr` / `inner_pin_eq` ✅

### 残作業 (build のみ、新数学なし)
- [ ] subfamily glue (subagent 中)
- [ ] bridge transfer (M-side `coherent_SOf_H0C_of_column_identities` mirror、~100 行) — 次段
- [ ] bundle + rewire + discharge pivot

γ-trick (更新 #12) は完全に回避。全て proven template の mirror ゆえ「新数学なし・transcription」。

## 2026-07-13 更新 #15 (lane b, /loop) — ★architecture 訂正 (bridge 不要): Coq FTtypeP_coherence = by_cases(all-reducible/has-irr)

更新 #14 の bridge transfer は**誤り** (bridge は M-side の 𝒮(H₀C)∪S(HC) 二 family 用、honest S-side は C'=⊥ で単一 family)。
Coq `FTtypeP_coherence` (PFsection13:350-383) 精読で**正しい (かつより simple) 構成**が確定:

### by_cases: calS が all-reducible か (irreducible member の有無)
- **all-reducible (redS)**: μ-column の uniform seq coherence を `subset_coherent_with` で calS へ restrict
  (all-reducible ゆえ calS ⊆ uniform seq)。⟹ **`exists_pinned_coherent_sSet_of_all_reducible` が対応、landing 済** (commit 71b34d70) ✓
- **has-irr**: `FTtypeP_facts` の **arbitrary な既存 full coherence** を取り、pin を**証明** (bridge も subfamily glue も新 coherence 構成も不要):
  - (A) `FTtypeP_coherent_TIred` (Coq PFsection8:852): coherent tau1 + irr member で `tau1(mu_j) = ±∑ᵢη_i(col)`
    (符号 δ・共役 conjC まで)。core = `coherent_prDade_TIred` (prime-Dade)。**S-side analog = R-family 機構**:
    - `sSet_coherent_extension_eq_sum_memberRFamily` (SSetMemberRFamily:879): coherent ext = signed R-family 和
    - `sSet_memberRFamily_imageSet_of_red` (:590): reducible μ-column の R-family imageSet = {η_ij} ∪ {−η_ik}
    - `sSet_irr_memberRFamily_eta_inner` (:633): irr member の R-family ⊥ η-grid
    - positivity で (δ,col) を {(d,j),(~d,conjC j)} に pin
  - (B) 符号確定 (Coq FTtypeP_coherence:362-382): flip `tau1(mu_k)=−tau1(mu_j)` を **isometry** で排除
    (`tau1(mu_k)=tau(mu_k−mu_j)+tau1(mu_j)` = column 恒等式 `dadeHypS_muColumn_diff` + isometry)。
    p=3 subtlety あり (Coq コメント 343-346)。

⟹ 更新 #12 の capstone subtlety は **detour**。正しくは R-family γ-trick (更新 #8/#9 の caseA recipe が正解だった)。

### 残作業 (訂正)
1. [x] all-reducible glue (commit 71b34d70) — hallred branch
2. [ ] **has-irr γ-trick** `sSet_coherent_muColumn_pin_of_irr`: 既存 coherence + irr member → pin
   (R-family (A) + 符号確定 (B))。~150 行、Coq FTtypeP_coherent_TIred + branch-2 template。
3. [ ] bundle `sSet_coherent_indS_A_pinned` = by_cases(∃irr) → {γ-trick / glue} + rewire coherent_H0Cprime_S + discharge pivot

## 2026-07-13 更新 #16 (lane b, /loop) — ⚠ has-irr γ-trick に p=3 global-sign subtlety (target 選定要確認)

γ-trick 精査で Coq `typeP_TIred_coherent` 定義 (PFsection13:338-340) の重要な nuance:
```
tau1(mu_j) = (-1)^b *: \sum_i eta_i (signW2 b j)   -- b : bool, b → p = 3
```
**pin は global sign b を許す** (b=true は p=3 のみ)。clean pin `tau1(mu_j) = ∑ᵢη_ij` は b=false 相当。

- **all-reducible glue (landing 済)**: b=false を**構成で保証** (μcol_j ↦ ∑η_j 直写)。clean pin ✓。
- **has-irr**: `FTtypeP_facts` の arbitrary coherence は b が未定 (p=3 で b=true 可)。⟹ scaffold target
  `tau1S_ofHonest_muColumn_pivot` (clean, b=false) は p=3,b=true の coherence では**偽になりうる**。

### 要確認 (次段で解決)
1. downstream (`character_degree_analysis` / `mu_tau1_formula`) が clean pin (b=false) を要するか、
   global-sign 形を許すか。delta_eq_one_S (δ=1) は clean を示唆。
2. clean pin を要するなら: **b=false coherence を選択/構成**する必要。候補:
   (a) has-irr でも μ-column subfamily glue (b=false) を base に取り full 𝒮 へ拡張 (base 保存拡張、要 lemma);
   (b) p=3 の flip を isometry で排除 (Coq FTtypeP_coherence:362-382 の p=3 分析を mirror);
   (c) p≠3 は自動 b=false、p=3 のみ特別処理。
3. p=3 が honest S-instance で実際に起こるか (p,q 奇素数ゆえ p=3 可)。

### 現状 (clean、正しい)
all-reducible glue = landed (clean pin, b=false)。pivot sorry は honest に残存 (has-irr の b 選定が未解決ゆえ
誤 target で bundle を組まない)。has-irr γ-trick + bundle は上記解決後。**誤った pin target で build しないため保留**。

## 2026-07-13 更新 #17 (lane b, /loop) — ★更新 #16 の 3 問全決着: 正しい pin target = disjunction、has-irr 機構 = row-exchange (全 tool 実在)

### Q1 (downstream 要件) — 決着: clean pin 不要
`CharacterDegreeData.mu_tau1_formula` (Machinery135:169) は**最初から disjunction**:
`(∀j≠0, τ₁μ_j = ∑η_ij) ∨ (p=3 ∧ ∀ j≠j'≠0, τ₁μ_j = −∑η_ij')`。`mu_col_tau1_eta_col_one` も δ=±1 許容。
⟹ scaffold `tau1S_ofHonest_muColumn_pivot` (clean 形) は **overstatement**。MuColumnPin 3 lemma は
consumer 0・importer 0 (OddOrder.lean 未登録!) ゆえ restatement 完全 free。正しい target = mu_tau1_formula と同形の disjunction。

### Q3 (p=3 の現実性) — 決着: 排除不能かつ mixed split の脅威は has-irr では消える
- p=3 all-reducible: **mixed split** `c(μ₁)=∑_{A}η_i1−∑_{B}η_i2` (|A|+|B|=q, A_2=B₁ᶜ, B_2=A₁ᶜ) が
  真に coherent (isometry+diff-identity+ZIrr 全部 OK、supported span が μ₁−μ₂ の倍数のみゆえ)。
  ⟹ 任意 `.some` は disjunction すら破りうる → **glue 構成 (landed) が p=3 all-red の唯一の supply**。
- p≥5: diff-identity の係数比較だけで **任意の coherence が clean pin** (下記)。flip は不成立。
- p=3 has-irr: Coq 通り disjunction まで pin 可能 (b 排除は不能、Coq も keep)。

### has-irr 機構 (Coq coherent_prDade_TIred PFsection5:1371 精読) — S-side 全 tool 実在
Coq の核 = **row-exchange**: irr member ζ で τ₁(μ_k) が V=Ŵ 上消滅 → `cycTIiso_cfdot_exchange` (PF 3.5) で
`⟨φ,η_il⟩` が行 i に独立 → mixed split 排除 → norm=q で column 全取り 1 本 → clean or conj-column flip。
S-side 対応 (全部既存!):
1. **ζ-消滅**: `coherentIndS_image_inner_eta_eq_zero` (CoherenceEtaOrthogonality:67, crux) →
   `vanish_of_inner_eta_eq_zero` (Canonicalization:501, (3.2.d)) + class-fn conj 飽和 → c.ext(ξ) は Ŵ^G 消滅。
2. **γ-element**: γ = ξ(1)•μcol_j − μcol_j(1)•ξ (ℤ-係数、`sSet_subset_inducedKernelFamily`
   (CaseBRed:197) + `inducedKernelFamily_mem_intDegree` 型整数次数)、γ(1)=0 →
   support ⊆ A(S) (`sSet_member_support_subset` + muColumn_diff_supported パターン) →
   c.ext(γ) = indS(γ) = Dade⁰(γ) (`sInstance_dade0_eq_induce`) → **`dadeS0_apply_eq_zero_of_regular`**
   (SSetMemberRFamily:522) で Ŵ^G 消滅 → φ_j := c.ext(μcol_j) が Ŵ^G 消滅 (ξ(1)≠0 で割る)。
3. **exchange**: 新設不要 — **`S16.inner_eta_grid_relation`** (S16_GridExpansion, (3.7)) が既にある:
   Ŵ^G-消滅 ψ に `⟨ψ,η_ij⟩+⟨ψ,η_00⟩=⟨ψ,η_i0⟩+⟨ψ,η_0j⟩` → φ の 0-column 消滅と合わせ row-uniformity。
4. **E-分解**: `sSet_coherent_extension_eq_sum_memberRFamily` (:879, τ=Dade 版) へは
   **`IsCoherent.congrMap`** (S08_CaseBCoherence2:1084, extension 保存) + `sInstance_dade_eq_induce` で transport。
   `sSet_memberRFamily_imageSet_of_red` で E ⊆ {η_ij}∪{−η_ik} (k=conj 列、k≠j: no-real、k≠0: 列一意性)。
5. **endgame**: ⟨φ,η_aj⟩=[η_aj∈E]∈{0,1} 行独立 s、⟨φ,η_ak⟩=−[−η_ak∈E] 行独立 t、‖φ‖²=q ⟹ q(s+t)=q ⟹
   (s,t)=(1,0): φ=∑η_ij (clean) / (0,1): φ=−∑η_ik (conj-flip)。
6. **flip 排除 (p≥5)**: c-generic diff-identity (c.ext(μ_j)−c.ext(μ_j')=ηcol_j−ηcol_j'、任意 c で成立:
   extends_on_supported+`dadeHypS_muColumn_diff`) を ηcol_j と内積: j'∉{j,k_j,0} を選ぶ (p−1≥4 で可) と
   flip_j なら 0=q 矛盾。p=3 は k_1=2,k_2=1 強制で clean↔clean / flip↔flip が diff で連動 → disjunction。

### 実装 plan (既存宣言の移動ゼロ)
- **MuColumnPin.lean を c-generic 機構 leaf に転換**: import = Machinery135 + S15_CaseBReducibleCoherence +
  CoherenceEtaOrthogonality (CaseACoherence import を外す)。内容: c-generic diff / ξ・φ-消滅 /
  `coherentIndS_muColumn_pin_of_irr` (係数抽出+endgame) / formula 組み立て。旧 tau1S-特化 3 lemma は撤去。
- **CaseACoherence** += import MuColumnPin: `sSet_coherent_indS_A_pinned` (∃c, formula) を by_cases(∃irr) で
  構成 (has-irr: `.some`+formula_of_irr / all-red: `exists_pinned_coherent_sSet_of_all_reducible`+diff 拡張)、
  `coherent_H0Cprime_S := .choose` に rewire (型不変)、`tau1S_ofHonest_muColumn_formula := .choose_spec`。
- OddOrder.lean に MuColumnPin 登録 (現在未登録)。

## 2026-07-13 更新 #18 (lane b, /loop) — ★★(13.3.c) main formula LANDED (sorry-free、pivot sorry 消滅)

更新 #17 の plan を完全実装 (commits 5a198c90 + 7376ec89、full build 4188 jobs green + AxiomsCheck OK):

1. **MuColumnPin.lean** = c-generic pin 機構 leaf (sorry-free):
   `muColumn_not_irreducible` / `coherentIndS_muColumn_diff` (列独立性、任意 coherence) /
   `coherentIndS_extension_irr_vanish_regular` (irr 像の Ŵ^G 消滅) /
   `coherentIndS_muColumn_vanish_regular` (γ-trick) /
   **`coherentIndS_muColumn_pin_of_irr`** (dichotomy: clean ∨ conj-column flip; R-family 分解を
   congrMap transport + (3.7) inner_eta_grid_relation row-uniformity + norm=q) /
   `coherentIndS_muColumn_eq_etaColumn_of_pivot` (pivot→全列)。
2. **CaseACoherence**: `sSet_coherent_indS_A_pinned` (by_cases ∃irr; flipped pivot → p≥5 矛盾
   (hno3rd) → p=3 強制 + swap 組み立て; all-red → glue) → `coherent_H0Cprime_S := .choose` rewire
   (型不変) → **`tau1S_ofHonest_muColumn_formula`** = (13.3.c) main:
   `(∀j≠0, τ₁μ_j = ∑η_ij) ∨ (p=3 ∧ swap-negate)` — `mu_tau1_formula` field と同形。
3. 旧 scaffold の閉じ得ない clean-pivot sorry (`tau1S_ofHonest_muColumn_pivot`) は撤去
   (honest な proven formula に置換)。

### 残作業 (次段) = CharacterDegreeData 材料化 (issue 2035 本丸)
`character_degree_analysis` (Machinery135:~215, sorry) の Nonempty (CharacterDegreeData hyp) 構成:
- `mu_tau1_formula` ⟵ **tau1S_ofHonest_muColumn_formula で直接 discharge 可** ✓
- `tau1S := hyp.tau1S_ofHonest hG hnoV chief` を採る場合、hG/hnoV/chief の供給設計が要
  (CharacterDegreeData は hyp のみ参照 — hnoV・chief を仮説/field としてどう thread するか)。
- 他 field: tau1S_isometry 系 = tau1S_ofHonest_inner_induce / _induce_mem_ZIrr ✓ (proven)、
  `tau1S_induce_inner_eta` = crux ✓、`mu_j_linear_induced` (13.3.a)、`delta_eq_one`、
  `mu_col_tau1_eta_col_one` ⟵ formula + (13.3.a) の合成。lambda 系 field は要調査。

## 2026-07-13 更新 #19 (lane b, /loop) — carrier bug 修正 + CharacterDegreeData 材料化 inventory

### ⚠ uninhabitability 発見・修正済
`tau1S_induce_inner_eta` (∀ irr θ: ⟨η_ij, τ₁(Ind θ)⟩=0) が `mu_col_tau1_eta_col_one` と矛盾
(θ := (13.3.a) の θ_j で ±1 = 0) → structure uninhabited だった。修正 = 2 field 化
(irr(Ind θ) 仮説付き本体 + 列0限定 ∀θ 版 `tau1S_induce_inner_eta_col_zero`)、consumer 3 箇所調整。

### 材料化 inventory (character_degree_analysis の構成部品)
signature (hG, hyp) は不変で OK — **hnoV = `S12.no_typeV_maximal_unconditional hG`**、
**chief = `exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupS hG)`** で内部調達可能。
- tau1S := tau1S_ofHonest hG hnoV chief ✓
- mu_tau1_formula ⟵ tau1S_ofHonest_muColumn_formula ✓ (更新 #18)
- mu_j_linear_induced ⟵ **mu_j_isIndPC** (DegreesFirstSplit:767, proven) ✓
- delta_eq_one ⟵ S 側 **delta_eq_one_S** (CountingLayer:1547, proven) ✓ + δ' 側 (swap 経由? 要確認)
- mu_col_tau1_eta_col_one ⟵ formula + mu_j_isIndPC の合成 (buildable、p=3 分岐で j 選択)
- tau1S_inner_induce ⟵ tau1S_ofHonest_inner_induce ✓ / tau1S_induce_mem_ZIrr ⟵ ..._induce_mem_ZIrr ✓
- tau1S_apply_induce_sub ⟵ tau1S_ofHonest_extends_on_supported + induce_H_mem_zSpan_S
  (zSpan 所属) + degree-0 差の A(S)-support (要小 lemma: zSpan 元の (η−η')(1)=0 → A(S)-supported)
- tau1S_induce_inner_eta ⟵ crux coherentIndS_image_inner_eta_eq_zero (Ind θ irr member 版、
  Ind θ ∈ sSet の membership が要 — 𝒳 kernel 条件の確認要)
- tau1S_induce_inner_eta_col_zero ⟵ zSpan 分解 + formula + crux (irr/red 両対応)
- **lambda (13.3.b) = 未存在の genuine content** (irr・degree uq・H-linear-induced な member の存在)
- tau1T ⟵ hyp.swap (HypothesisSwap:153) の tau1S_ofHonest (swap 側 chief も exists_chiefFactorData)

## 2026-07-13 更新 #20 (lane b, /loop) — ⚠ (13.3.b) は dichotomy: CharacterDegreeData.lambda 無条件 field は overstatement の疑い濃厚

### 原文・Coq の確定事実
- **Pf (13.3.b)** (mmd 04.15 line 43): 「𝒮 が PC の線型指標から誘導される次数 uq の既約指標を
  **含まないなら**、(9.7.b) が M=S, C=1, u=(p^q−1)/(p−1) で成立」— λ の存在は **dichotomy**、無条件でない。
- **Coq PFsection13:307-310**: `~~ has irrIndH calS → [typeP_Galois, C=1, u=(p^q−1)/(p−1)]` — 同形。
- Coq は (13.4) を skip し、(13.5-8) は `calS1 = seqIndD H S P 1` の member zeta を**引数に取る条件付き**
  (S1cases :402: zeta ∈ calS1 → μ-column か irr)。λ を無条件に選ぶ lemma は存在しない。
- book 後段 (13.15) (mmd line 262): x = (p^q−1)/((p−1)u) の算術で x ≥ 2q+1 の場合に no-λ 分岐を
  refute して初めて「By (13.3.b), there is a character λ」と言う — **no-λ (Galois, C=1) は
  (13.3) 時点で live な case**。
- ⟹ `character_degree_analysis : Nonempty (CharacterDegreeData hyp)` (無条件 λ 込み) は
  no-λ case を排除できない限り証明不能の疑い。要確認: S15.Hypothesis が C≠1/非Galois を既に
  field で排除していないか (排除していれば無条件で OK)。していなければ restructure:
  **(A) λ-free core** (μ/τ₁/δ field 群 — 全て landed engine で供給可) **+ λ-cluster 条件付き carrier**、
  or **(B)** producer を dichotomy 化 `Nonempty CDD ∨ (Galois ∧ C=1 ∧ u=…)`。
  consumer 影響: NormEstimates ×5 (13.8-T 系、λ 前提で自然) + **TTypeII:194 (lane c 所有)** —
  restructure は cross-lane 影響あり、実施時は hub 調整 (9000 issue) 経由。

### 今 iteration の landing
- `tau1S_ofHonest_mu_col_eta_col_one` (CaseACoherence、sorry-free): mu_col_tau1_eta_col_one
  field の honest supply (formula + mu_j_isIndPC 合成、p=3 分岐で j=2/δ=−1)。

## 2026-07-13 更新 #21 (lane b, /loop) — (13.3.b) 数学は landed 済と判明 + 残 build list 確定

- **(13.3.b) dichotomy glue = `caseB_of_no_irreducible_sOf_H0Cprime`** (CountingLayer:1042,
  sorry-free, §9-generic) が既に存在 — no-irr → caseB + C=⊥ + u=(p^q−1)/(p−1)。
  (9.10) 相当 = `exceptional_case_frobenius_realization` (ThetaCountAssembly:993, sorry 3 残
  は type-II HU-Frobenius 節のみ)。9094 の裁定対象は carrier 形状のみに縮小 (追記済)。
- **残 build list (ungated、9094 裁定と独立に有用)**:
  1. conditional producer `character_degree_analysis_of_irr`: (∃ λ witness) → Nonempty (CDD hyp)
     — 全 field を landed engine で組む (λ-cluster は witness から)。
  2. `tau1S_apply_induce_sub` 供給: zSpan(sSet) 元の degree-0 → A(S)-supported 小 lemma +
     tau1S_ofHonest_extends_on_supported + induce_H_mem_zSpan_S。
  3. `tau1S_induce_inner_eta` (restated 版) 供給: Ind θ irr → sSet membership 橋 + crux。
  4. `tau1S_induce_inner_eta_col_zero` 供給: induce_H_mem_zSpan_S の zSpan 分解 + formula + crux。
  5. tau1T / δ'-half: `Hypothesis.swap` 経由 — 前提 = hT2 (T type-P₂) + Tdata + **NuGridSupplyData**
    (T-side (13.1.e)/(4.3)/(4.4) grid facts の Prop bundle、producer 未確認 — 要調査)。

## 2026-07-13 更新 #22 (lane b, /loop) — ⚠ τ₁ field 群は P ⊄ Ker guard が必須 (第 5 の overstatement) + (7.7) trivial-base 問題と rebase 修理経路

### 発見 1: 3 つの τ₁ field は無条件形では供給不能
`tau1S_apply_induce_sub` / `tau1S_inner_induce` / `tau1S_induce_mem_ZIrr` (Machinery135) は
全 irr θ, θ' で量化するが、IsCoherent が与えるのは ℤ[𝒮] 上のみ:
- `extension_inner_eq` / `extension_mem_ZIrr` は zSpan 𝒮 membership が前提
- Ind θ ∈ ℤ[𝒮] は **P ⊄ Ker θ が必要** (induce_H_mem_zSpan_S の hθP; P ⊆ Ker θ なら
  constituents が P-kernel irr で sSet 外)
- 原文 (13.5) 証明 (mmd 04.15:69-73) も同形: 「For i ≤ n, ζ_i ∈ ℤ[𝒮] by (1.5.a), and, by
  (13.2.e), (ζ_i−ζ_0)^τ = Ind(ζ_i−ζ_0)」 — τ₁ 変換は **𝒮₁ member (P ⊄ Ker) のみ**。
  P-kernel 側の係数は未知のまま α に吸収 ((13.5.a) の構造そのもの)。
- τ₁ = .choose の opaque extension ゆえ ℤ[𝒮] 外の値は未拘束 → 無条件 field は証明不能
  (2034 lambda_mem / #19 tau1S_induce_inner_eta / 9094 λ-cluster に続く同型第 5 例)。
- **供給は landed**: tau1S_ofHonest_inner_induce / _induce_mem_ZIrr (既存、guarded) +
  **tau1S_ofHonest_apply_induce_sub** (今回 landing、guarded; zSpan_sSet_degree_zero_support +
  extends_on_supported)。⟹ **9094 案 A の Core 定義時に 3 field を guarded 形で入れる**。

### 発見 2: H_sharp_hypothesis76 の trivial base で (13.5) 系 cCoeff 補題が実質証明不能
- repo の (7.6) instantiation は `hypothesis76OfDadeTrivialBase` — **zeta 0 = Ind 1_H (P-kernel!)**。
- Canonicalization の `lambda_tau1_cCoeff` / `eta10_cCoeff_*` (:326, :1073) は
  hfield1/hfield2 を **(θ, trivial) pair に適用** — guarded field では討ち取れず、
  絶対値 claim (c_{i₁}=1 ∧ c_i=0) は trivial base では genuinely undetermined
  (τ₁ の choice に依存: ⟨Ind ζ₀^triv, τ₁λ⟩ は coherence が pin しない)。
- 原文は application ごとに base を選ぶ ((7.8.b) 「We use (7.7) with ζ₀ ∈ 𝒮−{ζ}」、
  (13.5) は ζ₀ ∈ 𝒮₁)。
- **修理経路 (instantiation 再構築不要)**: rebase 恒等式
  `∑_{全 i} ζ_i/‖ζ_i‖² |_{H^#} = 0` (H abelian ⟹ ∑_{θ∈Irr H} θ = reg_H = |H|·δ_1) により、
  trivial-base chiRho_decomp から **任意の P-non-kernel base i₀ への rebased (7.7.a)** が
  定理として導出可能: χ^ρ(x) = ∑_{i≠i₀} ((c̄_i − c̄_{i₀})/‖ζ_i‖²) ζ_i(x)。
  c_i − c_{i₀} = ⟨τ(ζ_i − ζ_{i₀}), χ⟩ は P-non-kernel pair なら guarded field で計算可。
  base witness: i₀ = μ-column index (mu_j_isIndPC、λ ≠ μ_j は irr/red で分離、p−1 ≥ 2 本)。
- 影響: Canonicalization ×2 (cCoeff 補題の証明再構成; conclusion 形は book-faithful に要修正 —
  絶対値でなく「P-non-kernel 係数差」または rebased 係数)、NormEstimates:806・
  CountingLayer:1805 は λ/μ の P-witness thread のみ (statement 不変)。
  **Q_sharp_hypothesis76 (NormEstimates:246 系、T-side twin) も同パターン — 要同修理**。
- 派生要件: μ 側 field (`mu_j_linear_induced` / `mu_col_tau1_eta_col_one`) に **P ⊄ Ker θ
  witness の追加が必要** (供給側: μ_ij ∈ 𝒮 は P-non-kernel + P ⊴ S ⟹ P ⊆ Ker θ なら全
  constituent P-kernel、で導出可)。

### 今 iteration landing
- `zSpan_sSet_support_subset` / `zSpan_sSet_degree_zero_support` (CaseBReducibleCoherence)
- `tau1S_ofHonest_apply_induce_sub` (CaseACoherence) — 全て sorry-free、build green
- 残 build list (#21) の item 2 完了。next = 9094 案 A 実装 (Core は guarded field で定義、
  発見 1-2 を織り込み) → item 1 (conditional producer) と統合。

## 2026-07-14 更新 #23 (lane b, /loop) — τ₁ field 供給 5 本完備 + item 5 (tau1T/swap) 調査完了

### landed (S15_CharacterDegreeSupply.lean、新 leaf)
- `induce_H_mem_zSpan_sSet_irr` (Coq S1cases irr-branch): irr な Ind_{PC}^S θ (P⊄Ker) ∈ ℤ[𝒮∩Irr S]
- `tau1S_ofHonest_zSpanIrr_inner_eta` + `tau1S_ofHonest_induce_inner_eta` (field 供給、guard 付き)
- `tau1S_ofHonest_zSpan_inner_eta_col_zero` + `tau1S_ofHonest_induce_inner_eta_col_zero`
  (混在族対応: irr→crux / red→μ-column→(13.3.c) formula→η-grid 直交)
- 前 iteration: `tau1S_ofHonest_apply_induce_sub` + zSpan 支持補題 2 本 (CaseA/CaseB leaf)
⟹ **CDD の τ₁ field 群 (inner_induce / mem_ZIrr / apply_induce_sub / inner_eta /
inner_eta_col_zero) の guarded supply が全て sorry-free で完備**。

### item 5 (tau1T/swap) 調査結果
- `NuGridSupplyData` (HypothesisSwap:62) 定義済 + `Hypothesis.swap` (:153) 構成済。
- producer `Hypothesis.nuGridSupply` (:131) = **sorried**。discharge 経路は docstring に文書化済:
  FT-layer で hyp.nu ↔ certainTypeT grid (nuT) 同定 + muS_* 供給鎖の T-instance 読出し。
  **carrier files が a 所有 (FeitThompson{,Setup}.lean)** — 9081 pattern の coordinated field
  addition が要 (2038 iter 26 の記録)。tau1T は swap 経由 sorried-cite で組める
  (conditional producer は nuGridSupply を cite、discharge は別 coordination)。

### next
9094 案 A 実装: CharacterDegreeCore (guarded field 版、#22 発見織り込み) + conditional
producer (置き場 = S15_CharacterDegreeSupply、CaseACoherence+Machinery135 の合流点 —
RULING の「Machinery135/CountingLayer」は import 上不可能 (producer は tau1S_ofHonest =
CaseACoherence 下流が必須) ゆえ b 裁量で新 leaf に配置、と 9094 に追記予定)。

## 2026-07-14 更新 #24 (lane b, /loop) — 案 A 1/3 landed + rebase 経路の簡素化

- **CharacterDegreeCore + 無条件 producer landed** (詳細 = 9094 追記): 残 sorry は
  deltaPrime_eq_one_T (ν-gated) のみ。
- **#22 発見 2 の修理経路を簡素化**: hypothesis76OfFamily が base-agnostic (generic
  certificate 証明済) と判明 → `hypothesis76OfDadeBase` (任意 φ₀ base builder、landed) で
  P-non-kernel base の (7.7) instance を直接作れる。**rebase 恒等式 ∑ζ_i/‖ζ_i‖²|_{H^#} = 0
  の形式化は不要**。
- **next (案 A 2/3 の残り)**:
  1. S15 instantiation `H_sharp_hypothesis76_base φ₀` (Machinery135 mirror、supply leaf)
  2. cCoeff 補題 2 本 (lambda_tau1_cCoeff / eta10 版) を base = μ-source で restate
     (guarded field 版証明; base ≠ λ は irr/red 分離、P-non-kernel 係数のみ claim)
  3. LambdaClusterData structure + conditional producer (packaging)
  4. NormEstimates:806 / CountingLayer:1805 の witness thread 版
  5. flip: CDD = Core extends + λ-cluster、旧 field 消費の一斉差替え (build-green 1 commit)
  6. dichotomy producer (no-λ 分岐 ↔ caseB_of_no_irreducible_sOf_H0Cprime の条件差
     「no-λ-witness vs no-irr-member」の橋 = caseB では全 irr member が deg qu、
     PC-linear-induced 性の確認要 — Coq (13.3.b) 対応箇所精読)

## 2026-07-14 更新 #25 (lane b, /loop) — 案 A 2/3 核心完了: cCoeff 補題 2 本の guarded restate landed

- `lambda_tau1_cCoeff_base` + `eta10_cCoeff_base_eq_zero` (S15_CharacterDegreeSupply):
  chosen-base instance (H_sharp_hypothesis76_base、ζ₀ = Ind φ₀ ∈ 𝒮₁) 上で旧 Canonicalization
  版 (trivial base、実質証明不能) を book-faithful に復元。guarded Core field 経由、
  P-non-kernel index のみ claim (P-kernel は (13.5.a) α 吸収)。両方 sorry-free。
- 残 (更新 #24 リスト): ④ NormEstimates:806/CountingLayer:1805 の Core/LambdaCluster 版
  (witness thread、旧 lemma の statement 不変で proof 差替え or 並行版) → ⑤ flip
  (CDD = Core extends + λ-cluster; (13.6)/(13.7) norm 系は cCoeff_base 版に接続替え) →
  ⑥ dichotomy producer (no-λ vs no-irr 橋: Coq PFsection13 :296-340 の
  FTtypeP_no_Ind_Fitting_facts 精読)。

## 2026-07-14 更新 #26 (lane b, /loop) — ④ 前半完了 (NormEstimates 側)

- `lambda_tau1_apply_eq_of_not_mem_H_sat_core` landed (S15_CharacterDegreeSupply、sorry-free):
  (13.9.a) 第一段の Core/λ-cluster 版。witness thread パターン確立
  (mu_col の P-witness + λ-cluster witness → guarded apply_induce_sub)。
- **次 = ④ 後半**: `lambda_forces_T_caseB` (CountingLayer:1758、(13.4)) の core/lam 版 —
  **TTypeII endpoint (T_side_caseB_facts) の直接上流**。配置 = CountingLayer 内
  (Machinery135 は upstream ✓)。chars 使用箇所: tau1S_apply_induce_sub (:1805、
  thetaL/θlin = λ/μ witnesses で discharge)、tau1S_induce_inner_eta (:1808-1814、
  λ の witness + irr(λ) = irr(Ind thetaL) で discharge)、mu_col/lambda fields。
  同 file の tSide_theta_package_of_not_caseB (:1727、sorry 持ち) は chars 非依存で流用可か確認。
- その後: ⑤ flip (旧 CDD consumer 全差替え — Canonicalization 旧 cCoeff 2 本と
  NormEstimates (13.6)/(13.7) 系の cCoeff_base 接続替えを含む) → ⑥ dichotomy producer。

## 2026-07-14 更新 #27 (lane b, /loop) — ⑤ flip 開始: TTypeII cross-lane endpoint 移行 (9094 §4 carve-out)

前 iteration で ④ (NormEstimates/CountingLayer witness thread) 完了。⑤ flip の最初の対象 =
**TTypeII (lane c 所有) の cross-lane endpoint** を選択 (RULING §4 carve-out あり + λ-branch 機械完備 +
no-λ 分岐が sorried bridging 明示許可 + downstream ゆえ CountingLayer legacy 非接触)。

- **landed** (S15_CharacterDegreeSupply、build green 4191 jobs / AxiomsCheck OK / 新 axiom なし):
  - `LambdaWitness hyp` (def) = (13.3.b) dichotomy 条件述語。
  - `T_caseB_facts_unconditional` = `by_cases LambdaWitness` の dichotomy producer
    (λ枝 lambda_forces_T_caseB_core / no-λ枝 T_caseB_facts_no_lambda)。
  - `T_caseB_facts_no_lambda` = no-λ T-mirror の precisely-named sorried bridge。
- **TTypeII rewire**: `T_side_caseB_facts` proof を差替え、`character_degree_analysis` 依存除去
  (statement 不変)。詳細 = 9094 追記。
- **残 `character_degree_analysis` 実 consumer = NormEstimates 5 obtain-site** (454/570/704/1093/1197)。
  全て λ-dependent (`chars.tau1S chars.lambda` / `lambda_forces_T_caseB` / 構造 field)。
- **次 = ⑤ flip 続き**: NormEstimates 5 の dichotomy 移行。keystone = general S-side dichotomy
  `Nonempty (LambdaClusterData hyp) ∨ (C=⊥ ∧ u=(p^q−1)/(p−1))`。no-λ 枝 =
  `caseB_of_no_irreducible_sOf_H0Cprime` (S-instance) 経由だが「no LambdaWitness → no irr member of
  S-instance SOf」橋 = (13.3.b) の核心 (S15↔S11 SOf bridge、deep)。NormEstimates statement は
  λ 非依存ゆえ no-λ 枝は (13.10)-arithmetic (c=1 ∧ u=full) で閉じる (RULING §3-2)。

## 2026-07-14 更新 #28 (lane b, /loop) — ⑤ flip 2/N: general S-side dichotomy producer landed (keystone)

NormEstimates 5 obtain-site 移行の keystone = **general S-side dichotomy** を landing:

- **`lambdaCluster_or_caseB`** (S15_CharacterDegreeSupply、**完全証明**): `Nonempty (LambdaClusterData hyp)
  ∨ (hyp.C = ⊥ ∧ hyp.u = (p^q−1)/(p−1))`。`by_cases LambdaWitness` — λ枝 =
  `lambdaClusterData_of_irr_witness`、no-λ枝 = `S_caseB_facts_no_lambda`。全 λ-independent consumer が
  thread する producer (λ枝で LambdaClusterData 供給 / no-λ枝で (13.10)-arithmetic 入力 C=⊥∧u=full)。
- **`S_caseB_facts_no_lambda`** (precisely-named sorried bridge): `¬LambdaWitness → C=⊥ ∧ u=full`。
  `caseB_of_no_irreducible_sOf_H0Cprime` (§9-generic, sorry-free) 経由だが、hno 供給に
  **「irr member of S-instance SOf(H0⊔C') → LambdaWitness」= (13.3.b) forward の深い S15↔S11 橋**が要る
  (irr SOf member が uq 次数 PC-linear-induced であることを示す; chars.C/chars.u → hyp.C/hyp.u 変換も;
  multi-session)。`mu_j_isIndPC_not_ker` の SOf→Ind 機械 (mu_colSum_mem_sOf_H0 / induceHU_eq_induce) が
  素材だが、reducible μ-column 版で、irr member + linear θ 抽出が未構築。

**深い橋の所在確定** (issue の設計 map を更新): 9094 の残 genuine math gate は 3 本に isolate —
(a) `tSide_theta_package_of_not_caseB_core` (ν-gated (13.4) T-package)、
(b) `T_caseB_facts_no_lambda` (no-λ T-mirror: q<p + (13.13)/(13.12)-on-T)、
(c) `S_caseB_facts_no_lambda` (no-λ S-side: (13.3.b) forward S15↔S11 SOf bridge)。
(c) が最上流の genuine math (S-instance SOf の irr-member 特徴付け)。

**次 = ⑤ flip 3/N**: NormEstimates 8 helper の core/lam 版 + 5 obtain-site の dichotomy 移行
(λ枝 = core+lam で helper 呼出、no-λ枝 = C=⊥∧u=full からの (13.10)-arithmetic)。または (c) の
deep bridge を先に engage (最上流 genuine math、multi-session)。

## 2026-07-14 更新 #29 (lane b, /loop) — ⚠ 重大 architecture 発見: NormEstimates 移行は import DAG でブロック (honest producer が下流)

⑤ flip 3/N (NormEstimates 5 obtain-site 移行) 着手時に **import 上の根本ブロッカー**を発見:

- **honest producer 群 (`T_caseB_facts_unconditional` / `lambdaCluster_or_caseB` /
  `characterDegreeCore_nonempty` / `lambda_forces_T_caseB_core`、全て S15_CharacterDegreeSupply)
  は NormEstimates の *下流***。理由 = producer は `tau1S_ofHonest` (S15_CaseACoherence) が必須で、
  `S15_CharacterDegreeSupply → CaseACoherence → MuColumnPin → CoherenceEtaOrthogonality →
  {S15_HonestTypeP2A0, S16_GridExpansion} → hub S15_SAndT_Setup → NormEstimates`。
- ⟹ **NormEstimates は honest producer を import 不能** (cycle)。overstatement
  `character_degree_analysis` (Machinery135, 上流) 経由でしか character-degree data を取れない。
- 教科書層序 ((13.3) char degrees → (13.6-15) analytic) に対し repo は **逆転** (honest (13.3)
  producer が τ₁ coherence engine 依存で (13.6-15) NormEstimates の下流に来た)。
- **層逆転の実在**: `CoherenceEtaOrthogonality (S15) → S16_GridExpansion (S16)` — S15 が S16 を import。
  hub を import する closure 内ファイル = S16_GridExpansion / S15_SAndTDefs / S13_PrimeTIResidueBridge /
  S15_HonestTypeP2A0 の複数。単一 spurious edge の de-hub では解けない (multi-file relayer + S15↔S16
  層序修正が要る、delicate)。

### 含意 (9094 RULING §3 の feasibility 修正)
- RULING §3-2「NormEstimates 5 を dichotomy thread に proof 移行」は **現 import DAG では不可能**。
  前提に「honest producer が NormEstimates 上流」があったが、実際は下流。
- RULING §3-3「全 consumer 移行後 character_degree_analysis 削除」も NormEstimates 移行がブロックゆえ
  現状不可。**overstatement は当面上流 interface として残る** (§13 analytic 枝は honest 化できない = FT
  honest 証明の債務、要 relayer)。
- 移行済は downstream consumer のみ = TTypeII (S16、honest producer 下流ゆえ可、更新 #27)。

### 選択肢 (次の方針)
- **(A) multi-file relayer**: CoherenceEtaOrthogonality 系の hub 依存を specific-leaf import に置換 +
  S15↔S16 層逆転解消 → honest producer を NormEstimates 上流へ。high-leverage だが delicate・多反復・
  build 検証必須 ([[relayer-verify-with-build-not-bfs]])。
- **(B) deep math bridge を先に**: `S_caseB_facts_no_lambda` ((13.3.b) forward, S-instance irr SOf
  member → LambdaWitness) / `T_caseB_facts_no_lambda` (no-λ T-mirror)。honest producer を下流のまま
  honest 化 (downstream TTypeII 枝が fully honest に)。upstream genuine math。
- hub 監視 tick で本発見を確認 (RULING §3 前提の訂正ゆえ)。b は当面 (B) の deep math を engage
  (relayer は別 major effort、着手前に規模精査)。

## 2026-07-14 更新 #30 (lane b, /loop) — 次 session 実行プラン: S_caseB_facts_no_lambda の structuring (deep bridge の de-opacify)

deep S-side bridge `S_caseB_facts_no_lambda` (S15_CharacterDegreeSupply:1211, monolithic sorry) を
**structured proof + isolated irr-member sub-gate** に de-opacify する具体プラン (素材は全て所在確認済):

**目標**: `¬LambdaWitness hyp → hyp.C = ⊥ ∧ hyp.u = (p^q−1)/(p−1)` を
`caseB_of_no_irreducible_sOf_H0Cprime` (CountingLayer:1041, sorry-free, 上流ゆえ import 可) 経由で組む。

**手順**:
1. S-instance 構築: `chief := (exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupS hG)).choose`、
   `chars := hyp.mkSection11CharacterDataS hG chief` (SubcoherenceInputs:547)。
2. `hno : ¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime), IsIrreducibleCharacter χ` を
   **新 sorried sub-lemma** `irr_sOf_S_to_lambdaWitness` (χ irr ∈ S-instance SOf → LambdaWitness) の
   contrapositive で供給。**これが唯一の残 genuine gate** = (13.3.b) forward: S-instance の irr SOf
   member が uq 次数 PC-linear-induced (θ irr linear P⊄Ker on H.subgroupOf S, Ind θ irr) であること。
   reducible 版 (`caseB_reducible_sOf_H0_isIndHC`, InnerCompHom:281) は (9.9.b) 依存で irr に非適用 —
   irr member は (9.9.b) で捕まらぬ特別ゆえ新機械が要る (multi-session、S11_MaximalII_III_IV 資材の
   caseA irr witness [ThetaCountAssembly:730, degree qu ∈ SOf(H0⊔C)] を Ind 形に落とす)。
3. `obtain ⟨_, hCbot, hufull⟩ := caseB_of_no_irreducible_sOf_H0Cprime hG chars hno`
   → `chars.C = ⊥ ∧ chars.u = (chief.p ^ data.q − 1)/(chief.p − 1)`。
4. **translations** (全て HypothesisBasics:1130-1166 に inline have あり、抽出/再導出):
   - `hq : (toTypesIIIIIIVSetupS hG).q = hyp.q` (:1134, Sdata_W1_eq + q_eq_card_W1)
   - `hpp : chief.p = hyp.p` (:1138, card_P_eq + chiefFactor_quotient_card)
   - `hu_eq : chars.u = hyp.u` (:1152, relIndex_cSub_U_eq_u + cSub_eq_C + card_U_eq_uc)
   - `chars.C = hyp.C`: chars.C は導出値、`toTypesIIIIIIVSetupS_cSub_eq_C` (:1040) + Section11CharacterData.C
     定義 (ChiefFactorCore:606) の展開 (SubcoherenceInputs:592-593「C = C_U(P), cprimeSub = derivedInG(cSub)」)
   → `refine ⟨C 変換 ▸ hCbot, u/p/q 変換 ▸ hufull⟩`。

**効果**: monolithic sorry → 1 本の precisely-named sub-gate (irr_sOf_S_to_lambdaWitness) に isolate。
sub-gate は (13.3.b) forward の genuine math (multi-session)。translations は既存 inline have の抽出。

**注意**: このプランは deep math を honest 化するが、**NormEstimates 移行ブロッカー (更新 #29) は別問題**
(architecture relayer 要、S15↔S16 層逆転含む)。honest producer が下流のままなので、S_caseB_facts_no_lambda を
閉じても NormEstimates は救われない (downstream の TTypeII 枝が honest になるのみ)。

## 2026-07-14 更新 #31 (lane b, /loop) — ✅ S_caseB_facts_no_lambda を de-opacify: 構造化 + translations proven + 単一 gate 分離

更新 #30 プランを実行、deep S-side bridge を **monolithic sorry → 構造化 proof + 単一 isolated
(13.3.b)-forward gate** に de-opacify (full build green 4194 jobs / AxiomsCheck OK / 新 axiom なし):

- **translations 3 本 landed** (HypothesisBasics、additive、`u_le_cyclotomicQuotient` の inline have
  から抽出した reusable API、全て sorry-free):
  - `toTypesIIIIIIVSetupS_q_eq` : `(toTypesIIIIIIVSetupS hG).q = hyp.q`
  - `chiefFactorS_p_eq` : `chief.p = hyp.p`
  - `mkSection11CharacterDataS_u_eq` : `(mkSection11CharacterDataS hG chief).u = hyp.u`
- **S_caseB_facts_no_lambda 構造化** (S15_CharacterDegreeSupply):
  - S-instance 構築 → `caseB_of_no_irreducible_sOf_H0Cprime hG chars hno` 適用 → **proven**
  - C 変換 (`chars.C = cSub = hyp.C` via toTypesIIIIIIVSetupS_cSub_eq_C) → **proven**
  - u/p/q 変換 (3 translations で `chars.u=(chief.p^data.q−1)/…` → `hyp.u=(p^q−1)/(p−1)`) → **proven**
  - **残 sorry = `hbridge` 1 本のみ** = (13.3.b) forward「irr S-instance SOf member → LambdaWitness」。
    precisely-named、genuine deep math (irr member の (13.3.a)-for-irr 特徴付け; reducible 版
    `caseB_reducible_sOf_H0_isIndHC` は (9.9.b) 依存で非適用; multi-session S15↔S11 assembly)。
- **効果**: 9094 の残 genuine gate の 1 つ (S-side no-λ) を、算術/plumbing を全部証明し尽くして
  **唯一の本質的 math 障害 (irr-member 特徴付け) に凝縮**。次に engage すべき対象が完全に isolate された。

### 別件 flag (hub 向け)
- **AxiomsCheck.lean が 7905 行で longFile 制限 7900 超過** (a-lane merge 由来の warning、build は green)。
  shared file ゆえ hub が `set_option linter.style.longFile` を bump 推奨 (b territory 外、未編集)。

### 次 (残 (13.3.b) forward gate `hbridge`)
irr S-instance SOf member → LambdaWitness の genuine 構成。素材 = caseA irr witness
(ThetaCountAssembly:730, degree qu ∈ SOf(H0⊔C)) を Ind_{H.subgroupOf S} linear 形に落とす +
induceHU_eq_induce (PU↔PC) + irr 保存。multi-session、S11_MaximalII_III_IV 精読要。

## 2026-07-14 更新 #32 (lane b, /loop) — hbridge の構成 map 確定 (deep S11、multi-session)

`hbridge` = 「irr χ ∈ S-instance SOf(H0⊔C') → LambdaWitness」= (13.3.a)-for-irr の構成 map を精査確定
(reducible 版 `caseB_reducible_sOf_H0_isIndHC` は (9.9.b) 依存で irr 非適用、新機械が要る):

**SOf/xiOf 構造** (ChiefFactorCore): `sOf(Y) = {induceHU ζ | ζ ∈ xiOf(Y)}`、
ζ = irr on huSub(=PU=S') で H⊄Ker ∧ Y⊆Ker。`induceHU ζ = Ind_{PU}^M ζ` (induceHU_eq_induce)。
degree: induceHU(ζ)(1) = q·ζ(1) (induceHU_apply_one_eq_q_mul) → 度数 qu なら ζ(1)=u。

**LambdaWitness 目標**: θ irr **linear** on PC.subgroupOf S (P⊄Ker)、Ind_{PC} θ irr。
χ = Ind_{PC} θ なら Ind θ irr = χ irr ✓。要: χ = induceHU ζ を Ind_{PC}(linear) 形に。

**caseA (tractable half)**: caseA member は explicit = `induceHU(hcuZetaPair caseA θ hinv lam)`
(ThetaCountAssembly:868/871、hcuZetaPair_induceHU_mem_sOf/caseA_member_induceHU_irreducible)。
`hcuZetaPair = Ind_{hInHu⊔cuInHu}^{PU}(hcuPsiPair)`、`hcuPsiPair` = **linear** (hcuPairHom : →*ℂˣ 由来、
ThetaCountAssembly:148 hom_eq)。`hInHu⊔cuInHu = HC(=PC)` 想定 (hInHu=P-in-HU, cuInHu=C_U-in-HU)。
⟹ caseA member = induceHU(Ind_{HC-in-PU} linear) = Ind_{HC}(linear) [stages] = LambdaWitness。
**要 M-transport**: HC-in-HU (hInHu⊔cuInHu を huSub 内) ↔ PC.subgroupOf S。pattern =
caseB_reducible_sOf_H0_isIndHC:322-350 (subgroupOfEquivOfLe.symm.trans subgroupCongr +
compHom + induce_induce_subgroupOf)。~80 行。

**caseB (harder half)**: C≠⊥ の irr member (caseB_no_irreducible_forces_C_bot の contrapositive で存在)
も H-induced のはずだが caseB Clifford 構造の characterization が要 (未特定、要 CaseBXi/CharacterCounts 精読)。

**logical 構造** (現行 hbridge 維持が最適、clifford split は core 難度不変ゆえ非推奨):
現行 = 単一 hbridge + caseB_of_no_irreducible_sOf_H0Cprime (clifford split を内部処理)。
hbridge の内部で clifford_dichotomy → caseA (lambdaWitness_of_caseA、explicit witness、χ 不要) /
caseB (caseB member → LambdaWitness、χ 使用)。

**推奨**: focused subagent or 次 session で S11_MaximalII_III_IV 精読 → lambdaWitness_of_caseA を先に
(explicit witness ゆえ tractable) → caseB member 版。build-verify 必須 (transport plumbing)。

### #32 追記 — ⚠ caseA approach の subtlety (要解決): cuInHu = C_U(S₀) ≠ C
`cuInHu caseA` = **C_U(S₀)** (S₀ = Clifford summand of H̄)、**C = C_U(P) ではない**
(InertiaLift:327「uInHu ⊓ (hInHu⊔cuInHu) = cuInHu」= U⊓H·C_U(S₀)=C_U(S₀))。caseA (a>1) では
C_U(S₀) ⊋ C_U(P)=C ゆえ `hInHu⊔cuInHu = P·C_U(S₀) ⊋ PC`。⟹ caseA witness = Ind_{P·C_U(S₀)}(linear)
は素朴には Ind_{PC} でない。degree qu との整合 ([S':P·C_U(S₀)]=[U:C_U(S₀)] vs u=[U:C_U(P)]) が
未解決。**caseA witness → LambdaWitness (Ind_{PC} linear) の正しい経路は要精査** (Clifford
correspondence の inertia lift; hcuZetaPair が実は further-induce で Ind_{PC} に落ちるか、或いは
別の member を採るか)。次の focused effort はこの degree/centralizer 整合を最初に解決すること。

## 2026-07-14 更新 #33 (lane b, /loop + subagent) — ✅ hbridge caseA branch を genuine に証明 (subtlety は red herring)

#32 の cuInHu subtlety は **red herring** と判明 (subagent 精査 + 自己検証)。2 種類の caseA member を混同:
- degree-**qa** (`hcuZetaPair`, cuInHu=C_U(S₀)) = (9.8.d) count in SOf(H₀⊔U') — LambdaWitness でない
- degree-**qu** witness = (9.8.c) `caseA_exists_irreducible_sOf_H0C` — **regular seed** θ (全 Clifford summand
  で非自明) の inflation hcPsi θ は inertia = **full HC** (`caseA_regular_inflation_inertia_eq`)、source
  ζ=Ind_{HC}(hcPsi θ) degree u、induceHU(ζ) degree qu=[S:PC]。M-transport で真に Ind_{PC}(linear) = LambdaWitness。
  正しい経路は `hcZeta_*` (cuInHu 不介入)。

**landed** (S15_CharacterDegreeSupply、build green 4114 jobs / #print axioms = [propext,Classical.choice,
Quot.sound] のみ = sorryAx なし / signature 不変):
- `caseA_exists_irreducible_witnessed` (**sorry-free**): (9.8.c) parity 論法を mirror + regular seed θ を露出。
- **hbridge の caseA branch を完全証明**: clifford_dichotomy → caseA で LambdaWitness を genuine 構成
  (caseA_exists_irreducible_witnessed → isIndHC_of_source_eq_induce_hcPsi flatten → hcRealized_map_subtype_eq
  + cSub_eq_C transport → θ' 構成、irr/linear/P⊄Ker[mu_j_isIndPC_not_ker 流]/Ind-irr の 4 条件)。
- **残 sorry = caseB branch 1 本のみ** (S15:1401)。net sorry 4→4 不変 (hbridge sorry → caseB sorry)、
  caseA は proven に置換。

**残 caseB gate の plan** (#32 harder half を精緻化): caseB (Singer, U irr on H̄) では全非自明 θ̄ が inertia HC
(`inertia_eq_hcInHu` + caseB.actsIrreducibly)、given irr χ=induceHU ζ (ζ∈𝒳(H₀C')) は Ind_{HC}(hcPsiPair θ λ)
(linear pair, λ≠1 on C when C≠⊥, Cprime=[C,C])。transport は caseA と同一 (既に caseB-agnostic)。
**唯一の欠落 = reverse characterization `caseB_xiOf_H0Cprime_eq_induce_hcPsiPair`** = `caseB_xiOf_H0C_eq_induce_hcPsi`
(InnerCompHom:36) の **pair (C'-kernel) 版** (現行は C-kernel family 𝒳(H₀C) のみで λ≠1 pair member 非対応)。
~100 行の Clifford correspondence、S11 material ゆえ **InnerCompHom.lean に追加すべき** (S15 でも可だが所属は S11)。
forward 部品 (hcPsiPair/hcZetaPair_irreducible/hcZetaPair_mem_xiOf) は既存。

### hub 向け flag
- subagent は S15 単一ファイル scope ゆえ main 同期せず (branch は main の 4 commit 遅れを検出)。commit 後に lane b が同期。

## 2026-07-14 更新 #34 (lane b, /loop + subagent) — caseB の hard S11 math (reverse characterization) landed; wiring は set-artifact 回避で follow-up

第 2 subagent が caseB の **hard S11 math を genuine に構築** (InnerCompHom.lean、build green、#print axioms
= sorryAx なし、0 sorry):
- `caseB_xiOf_H0Cprime_eq_induce_hcPsiPair` (:173): pair (C'-kernel) 版 reverse characterization
  「ζ ∈ 𝒳(H₀C') irr ⟹ ∃ θbar lam, ζ = Ind_{HC}(hcPsiPair θbar lam)」= 既存 `caseB_xiOf_H0C_eq_induce_hcPsi`
  (C-kernel 版) の pair 拡張 (λ≠1 on C 対応)。#32/#33 が「唯一の欠落」と特定したもの。
- `isIndHC_of_source_eq_induce_hcPsiPair` (:493): pair 版 flatten helper。

**⚠ S15 caseB wiring は set-artifact で未完了 (revert 済)**: subagent の S15 caseB branch は
`set data`/`set chars` (caseA から共有) + `mem_sOf.mp _hχmem` の相互作用で **chief✝/ζ✝ の folding artifact**
(型不一致)。extraction を set 前に移動しても `set` が obtain 済 hypothesis を rename して悪化。
S15 は committed 版 (caseA proven, caseB sorried) に revert。InnerCompHom lemma は保持。

**wiring の clean 経路 (follow-up)**: caseB branch を inline せず、**explicit-arg standalone lemma
`lambdaWitness_of_caseB_member` (chief chars caseB χ hmem hirr を explicit に取る) に切り出す** →
set 不使用ゆえ artifact 回避。中身は caseA branch の mirror (mem_sOf 抽出 →
caseB_xiOf_H0Cprime_eq_induce_hcPsiPair → isIndHC_of_source_eq_induce_hcPsiPair flatten → transport
hcRealized_map_subtype_eq/cSub_eq_C → θ' の 4 条件)。~50 行。

## 2026-07-14 更新 #35 (lane b, /loop + subagent) — ✅✅ hbridge 完全 CLOSE: S-side (13.3.b) forward gate proven

第 3 subagent が caseB wiring を完成、**`S_caseB_facts_no_lambda` が完全 sorry-free** に (自己検証済:
leaf build green 4115 jobs / #print axioms = [propext,Classical.choice,Quot.sound] のみ = sorryAx なし /
残 file sorry = deltaPrime_eq_one_T・tSide_theta_package・T_caseB_facts_no_lambda の 3 pre-existing のみ /
新 axiom なし / signature 不変 / InnerCompHom 非接触):

- **set-artifact の根治**: hbridge を **set-free** 化。`set data`/`set chars` が外部 obtain の chief を
  folded copy + stray `chief✝` に分裂させ _hχmem と caseB が non-defeq chief fvar を参照 → 単一 lemma
  call 不能だった。解決 = caseA/caseB を **explicit-arg standalone lemma** に切り出し (`let data`、set 不使用):
  - `lambdaWitness_of_caseA` (proven caseA body を verbatim 移設、set→let)
  - `lambdaWitness_of_caseB_member` (χ→ζ mem_sOf 抽出 → caseB_xiOf_H0Cprime_eq_induce_hcPsiPair →
    isIndHC_of_source_eq_induce_hcPsiPair flatten → transport → θ' の 4 条件。Ind θ' irr = `hχeq ▸ _hχirr`
    = 与 χ の既約性、genuine)
  - hbridge = `rcases clifford_dichotomy` + 2 つの one-line `exact`。
- **soundness 検証**: caseB は与えられた χ (hχmem/_hχirr) を genuine に使用、reverse characterization
  経由で LambdaWitness を構成 (vacuous でない)。caseA 移設は proven content 保全。

**⟹ `lambdaCluster_or_caseB` dichotomy の S-side が honest に。9094 の残 genuine gate は 2 本に減:**
`tSide_theta_package_of_not_caseB_core` (ν-gated (13.4) T-package) と `T_caseB_facts_no_lambda`
(no-λ T-mirror、S16 q<p gated)。deltaPrime_eq_one_T は ν-gated (a carrier)。

## 2026-07-14 更新 #36 (lane b, /loop) — frontier assessment: S-side 完了、残は全て cross-lane gated → hub direction 依頼 (9096)

hbridge closed (#35) 後、残 9094 gate を精査、b-solo S15 では全て close 不能と確定:
- **tSide_theta_package_of_not_caseB_core / deltaPrime_eq_one_T**: a-owned ν-carrier (nuGridSupply)。
- **T_caseB_facts_no_lambda**: S16-gated (T-side D/v machinery が S16_NonExistenceG/**、q<p が S16 field)。
  S15 から到達不可。de-opacify (S_caseB_facts_no_lambda proven 経由 + galois_S_forces_T_caseB gate) は
  forward-reference (S_caseB は後方定義) で不適 — reorder churn 過大ゆえ見送り。
- **NormEstimates 移行**: honest producer 下流 (#29)。relayer の S15→S16 inversion
  (CoherenceEtaOrthogonality → S16_GridExpansion) は genuine (2 lemma) かつ S16_GridExpansion=c-owned。

⟹ **b の S-side char-degree genuine math は完了、残は cross-lane 調整 or a-ν 待ち**。CLAUDE.md 準拠で
**hub に direction 依頼 (issue 9096)**。b は待機中も re-assess を continue: a-lane が ν-carrier を
landing したら un-gate 波及 (tSide_theta_package/deltaPrime_T) を検出して T-side を再開。

**session 総括 (2026-07-14 大量 landing)**: TTypeII 移行 + dichotomy keystone + translation API +
S-side (13.3.b) forward gate 完全証明 (caseA + caseB pair-Clifford、3 subagent + 自己検証)。
9094 の S-side deliverable 達成。

## 2026-07-14 更新 #37 (lane b, /loop) — T-side 再開: deltaPrime_eq_one_T 完全 assembly 化 (9096 split 後続)

9096 bundle split (ruling item 2) 完了後、T-side (13.3.c) を再開。新 leaf
`S15_SAndT_Setup/TSideDegrees.lean` に S-side (13.3) 度数/counting 層の T-mirror を実証明:

- **`v_modEq_one`** (Pf「As (V/D)W₂ is a Frobenius group, v ≡ 1 (mod p)」): `u_modEq_one` の
  完全 mirror。reconciled_typePData_T の tpd で `typeP_uW1_frobenius` → Isaacs 6.1
  `card_range_comp_subtype_modEq_one` → kernel = D (`D_eq`)、`|V| = vd`。**genuine 証明**。
- **`vd_ne_one`**: nontriviality を無仮定で導出 (T_nonI 4 択 + II/III/IV witness の
  `common.1` + `card_U_eq_index` witness 独立性 + type V は proven `no_typeV_maximal_unconditional`
  (Pf 10.10) で排除)。`toTypesIIIIIIVSetupT` の `hvd` 入力もこれで discharge 可能に。
- **`K_le_T` / `card_K_val` (|K| = |Q|·d) / `K_index_eq_vp` ([T:K] = v·p)**: `card_H_eq` /
  `H_index_eq_uq` mirror。**key: Fitting order |Q| は約分で消える**ので (14.9)-gated な
  `|Q| = q^p` (card_Q_eq) 不要。
- **`nu_apply_one_row_const`**: `nu_definition` (honest field) 経由の行内 degree 定数性。
- **`nu_rowSum_not_irreducible`** (pins 引数): p ≥ 2 distinct irr の和。
- **`deltaPrime_eq_one_of_ne_zero_T`** (pins 引数): (4.3.d)-T congruence + v ≡ 1 + δ' = ±1 +
  p odd ≥ 3 の完全 assembly。

`deltaPrime_eq_one_T` (S15_CharacterDegreeSupply:528) の **sorry を除去**し、anchor
(`pins.deltaPrime_zero_eq_one`) + 上記 assembly の実証明に置換。

### 残 obligation は 1 点に isolate: `nu_apply_one_eq_v` (TSideDegrees.lean, sorried)

(13.3.a)-at-T per-entry degree `ν_{ij}(1) = v` (i ≠ 0)。route は S-side `mu_j_isIndPC` mirror
(§9-on-T: `nu_rowSum_eq_induce` + reducible → `reducible_sOf_H0_isIndHC` at
`toTypesIIIIIIVSetupT` → Ind_{QD} linear、degree [T:K] = vp proven、row-const で per-entry)。
**gate**: sOf-membership に T-instance chief kernel triviality `H₀ = ⊥` が要り、それは
`|Q| = q^p` = (13.2.b)-at-T。S-side は carried `S_typeP2` で読めたが T の対応 carrier は
(14.9) 結論 (`S16.T_typeII` は sorryAx + 循環リスクで cite 不可、9096 audit)。type III 分岐は
(11.7) chain (`S13_ElementaryAbelianKernel`、§11 hypothesis は noncoherence-conditional)。

**discharge 経路 2 択** (docstring にも記載):
1. **canonical certain-type readout** (a-territory): FT-layer 構成サイトで `T = mp.certainTypeT`
   は §16 構造を持ち、per-entry degree は canonical grid property として証明可能see。
   nuGridSupply producer threading (9096 follow-up) と同時に埋まる形。**a への通知**: canonical
   側で `nuT_apply_one_eq_v` 相当を証明して bundle field 追加を検討する場合は 9096 で API 調整。
2. §11 (11.7) chain の T-instantiation (b-solo 可能だが noncoherence-conditional の処理要、大)。

build green (4136 jobs)。CharacterDegreeSupply 残 sorry = tSide_theta_package /
T_caseB_facts_no_lambda の 2 本 (どちらも既知 gate、#36)。

## 2026-07-14 更新 #38 (lane b, /loop iter 2) — ✅ (13.3.a)+(13.3.c)-at-T 完全証明: nu_apply_one_eq_v の gate 突破

#37 で isolate した `nu_apply_one_eq_v` の gate (`|Q| = q^p`) を**破った**。「(14.9)-gated」は誤認で、
§11/§13 の既存 sorry-free 資産で全 T_nonI 分岐が閉じる:

- **`card_Q_eq_qp`** (|Q| = q^p、(13.2.b)-at-T、**無条件**):
  - type II: (9.3) Wielandt order relation (Gate3 card_Q_eq と同計算、分岐仮定が IsTypeII を直接供給)
  - type III/IV: **(11.7) は type III/IV maximal に対し既に無条件証明済み** (`S13.card_H_eq_of_base`
    + `S13.S_H0C_not_coherent_unconditional` — (11.3) を Thm (10.8) unconditional から出す honest 経路;
    Pf Hypothesis (11.2) は「(10.1) + M type III/IV」のみで noncoherence は帰結)。local w₁/w₂ ↔ 抽象 p/q
    の同定は derived index (`card_W1_eq_derived_index` vs `W2_isComplement_T_deriv`) と κ-Hall 双対因子
    橋 (`S10.card_Msigma_inf_centralizer_eq_card_W2` vs proven `W1_eq_Msigma_T_inf_centralizer_W2`)。
  - type V: `no_typeV_maximal_unconditional`。
- **§9-on-T kernel collapse**: `toTypesIIIIIIVSetupT_chief_N_eq_bot` / `_chief_H0_eq_bot` /
  `_cSub_eq_D` (S-instance 三兄弟の mirror、card_Q_eq_qp が動力)。
- **(13.3.a)-at-T**: `nu_rowSum_mem_sOf_H0_T` (pins) → `nu_i_isIndQD` (ν_i = Ind_{QD}^T linear、
  `mu_j_isIndPC` mirror、generic `reducible_sOf_H0_isIndHC` + `mkSection11CharacterDataT`) →
  `nu_apply_one_eq_v` (ν_{ij}(1) = v) **実証明化** (sorry 除去)。

**#print axioms 検証済** (card_Q_eq_qp / v_modEq_one / nu_i_isIndQD / nu_apply_one_eq_v /
deltaPrime_eq_one_of_ne_zero_T すべて [propext, Classical.choice, Quot.sound] のみ)。

**⟹ (13.3.c) δ'_i = 1 は pins パラメトリックに sorry-free**。`deltaPrime_eq_one_T`
(CharacterDegreeSupply) の残依存は `nuGridSupply` cite のみ (a の producer threading で消える形)。
TSideDegrees.lean は **sorry 0**。#37 に記録した「discharge 経路 2 択」は不要になった (abstract 経路で完結)。

次: (13.4) `tSide_theta_package_of_not_caseB_core` (残 2 sorry の上流側) — (13.3.b)-at-T
(caseB_of_no_irreducible_sOf_H0Cprime T-instance) + ν-row τ₁-formula + 直交性。今回の
S11-T-instance 基盤 (setupT/chars/chief collapse) がそのまま土台になる。

## 2026-07-14 更新 #39 (lane b, /loop iter 3) — ✅ (13.3.b)-at-T θ-witness dichotomy 完全証明

(13.4) `tSide_theta_package` の Step 1 (θ-supply) を閉じた。`LambdaWitness` 機構の T-mirror 一式、
**全て sorry-free / #print axioms clean**:

- `ThetaWitness` def (vp-degree QD-linear induced irr of T)
- `thetaWitness_of_caseB_member` / `thetaWitness_of_caseA` (S-side witness 2 lemma の逐語 mirror;
  generic S11 部材 caseB_xiOf_H0Cprime_eq_induce_hcPsiPair / isIndHC_of_source_* /
  caseA_exists_irreducible_witnessed / hcZeta_* がすべて M-generic だったので transport 3 点
  (H_eq → toTypesIIIIIIVSetupT_H_eq、cSub_eq_C → cSub_eq_D、W2_le_P → Q normal) の差し替えのみ)
- `T_caseB_facts_no_theta`: ¬ThetaWitness → D = ⊥ ∧ v = (q^p−1)/(q−1) (S_caseB_facts_no_lambda mirror)
- `thetaWitness_of_not_caseB`: (13.4) の _hne → ThetaWitness (対偶 + card_Q_eq_qp で第 3 conjunct 消化)

同定 3 lemma (TSideDegrees 側): `toTypesIIIIIIVSetupT_q_eq` (setup.q = p) / `chiefFactorT_p_eq`
(chief.p = q、card_Q_eq_qp 経由) / `mkSection11CharacterDataT_v_eq` (chars.u = v、relIndex +
cSub_eq_D)。

配置: witness 機構 5 宣言は S15_CharacterDegreeSupply (caseA_exists_irreducible_witnessed が同
ファイル定義のため; LambdaWitness 機構の直後で読みやすい)。同 file ~1846 行 (2000 未満、次の
大型追加で分割要検討)。

### tSide_theta_package 残り conjunct の状況

θT := Ind_K θ' (ThetaWitness) として:
- conjunct 1 (δ' = ±1): delta_pm_one.2 ✓ 既存
- conjunct 2 (support ⊆ (Q⊔D)#): θT, ν_r とも Ind_K (nu_i_isIndQD #38) で同 degree vp →
  K ⊴ T (D normal: S12.typePData_C_normalized_by_M の T-instance) + Ind vanishing off K
- conjunct 3 (Ind formula): θG 存在量化ゆえ θG := Ind_T(θT − ν_r) + δ'∑η_{rj} で定義消化
- conjunct 4 (⟨η, θG⟩ = 0): 実内容 = ⟨η_{ij}, Ind_T^G(θT − ν_r)⟩ = −δ'·[i=r]·(j-sum 相当) 型の
  Dade/直交計算 — S-side の tau1S_induce_inner_eta 系 mirror + ν_r^τ = δ'∑η formula (§4/§6-T)
- conjunct 5 (⟨τ₁S λ, θG⟩ = 0): (13.2.e) disjoint support 直交
次 iteration: conjunct 4 の ν-η formula (Ind_T(ν_{rj} 差) と η の関係、nu_definition + Dade 経由) を精査。

## 2026-07-14 更新 #40 (lane b, /loop iter 4) — (13.4) conjunct 2 (support estimate) 実証明

`tSide_theta_package` の conjunct 2 を閉じた (TSideDegrees、sorry-free):
- **`K_subgroupOf_T_normal`**: K = QD ⊴ T。Q = T_F Fitting Hall + D = V ⊓ C_G(Q) の T-正規性
  (`typePData_C_normalized_by_M` reconciled T-instance、D は F(T) の π(Q)'-part) + normal sup。
- **`indK_sub_nuRow_support`**: `(Ind_K^T θ − ν_r).support ⊆ (QD)^#`。両項とも normal K からの
  induce (`nu_i_isIndQD`) → K 外で消滅 (`induce_apply_eq_zero_of_not_mem_normal`)、1 では両者
  degree v·p (`K_index_eq_vp`) で相殺。

### tSide_theta_package 残り conjunct 状況 (再掲+更新)
- conjunct 1 (δ'=±1) ✓ / conjunct 2 (support) ✓ #40 / conjunct 3 (Ind formula) = θG 定義消化 ✓方針
- **conjunct 4 (∀ij ⟨η_{ij}, θG⟩ = 0) = 残る本丸**: θG = Ind(θT−ν_r) + δ'∑η_{rj} の η-直交
  ⟺ ⟨η_{ij}, Ind_T^G(θT−ν_r)⟩ = −δ'[i=r]。原文 route は τ₁-T formula (ν_r^{τ₁} = δ'∑η_{rj})
  + θ^τ ⊥ η ((5.3.b)-T) — **T-side (9.11) coherence (`sSet_coherent_indT_A_pinned` 相当) の構築
  が必要** (S-side 機構 sSet_coherent_indS_{caseA,caseB} + coherentIndS_image_inner_eta_eq_zero
  の T-instance 化; S-side 自体に mixed-family lift の sorried-cite residual あり)。
- conjunct 5 (⟨τ₁Sλ, θG⟩ = 0): (13.2.e) S/T cross disjoint-support 直交。

次 iteration: S-side coherence 機構の generic 性精査 → T-instance 化の設計判断。

## 2026-07-14 更新 #41 (lane b, /loop iter 5) — (13.4) conjunct 4/5 の T-side coherence 戦線: 設計確定

conjunct 4 (∀ij ⟨η_{ij}, θG⟩ = 0) の short route (Frobenius reciprocity + K#-support 直接計算) を
検討したが **不成立** (η の K# 上の値は coherence 抜きに決まらない; 原文も (13.3.c)-T formula =
coherent extension 経由)。**T-side (9.11) coherence の構築が正道** — S-side stack の T-mirror。

### S-side coherence stack の現状 (精査済)
- `sSet_coherent_indS_A_pinned` = dispatch (`clifford_dichotomy`) + caseA/caseB + μ-column pin
- **caseB** (`S15_CaseBReducibleCoherence`): uniform-degree (5.7) route、landed;
  residual = `sSet_memberRFamily` reducible branch (§6 certain-type image-family port)
- **caseA** (`S15_CaseACoherence`): (9.11) 非 Galois maximal-pair refutation;
  base cut + reduction landed; residual = `sSet_caseA_nineElevenRefutation`
  ((9.11.7)-(9.11.8) は M-side 共通 residual、issue 9083 Phase E)
- Dade 基盤 = `dadeHypS`/`dadeHypS0` (S15_HonestTypeP2A0)

### T-side 建設計画 (資産と残作業)

**既存資産 (この session で建った物を含む)**:
- `dadeHypT0` (S15_HonestTypeP2A0:598、hT2/Tdata パラメトリック A₀(T)-Dade) ✓
- T-instance §9 完備: `toTypesIIIIIIVSetupT` + `mkSection11CharacterDataT` + kernel collapse
  (chief_N/H0_eq_bot、cSub_eq_D) + 同定 (q_eq/p_eq/v_eq) ✓ (#38/#39)
- **uniform degree v·p** = `nu_apply_one_eq_v` ✓ (#38 — caseB-T の (5.7) 入力そのもの)
- generic engines: `uniform_degree_coherence_of_families` (5.7) / S07 maximal-pair reduction /
  `clifford_dichotomy` ✓
- conjunct 2 support (`indK_sub_nuRow_support`) + K ⊴ T ✓ (#40)

**残 construction (建設順)**:
1. 𝒯-family 同定: generic `sSet (toTypesIIIIIIVSetupT)` と (13.1) の 𝒯 の対応 + ν-row sums が
   reducible members (`sSet_reducible_eq_nuRowSum` mirror)
2. caseB-T: `sSet_caseB_apply_one_eq_vp` (uniform degree — 部材済で組むだけ) +
   T-instance R-family (§6-T port; S-side と同じ residual 構造になる)
3. caseA-T: base cut (degree p·a irr) + reduction (generic) + refuter (M-common residual cite)
4. dispatch + **ν-row pin** (`sSet_coherent_indT_A_pinned`: ν_r^{τ₁T} = δ'∑_j η_{rj} form)
5. `tau1T_ofHonest` + (5.3.b)-T (`coherentIndT_image_inner_eta_eq_zero` mirror) +
   conjunct 4 assembly (⟨η_{ij}, Ind(θT−ν_r)⟩ = −δ'[i=r]: coherence ext = Ind on A₀(T)-supported
   (conjunct 2 support) + pin + (5.3.b)-T)
6. conjunct 5: (13.2.e) S/T cross disjoint-support 直交 ((H#)^G ∩ (K#)^G = ∅、原文 13.4 冒頭)
7. package assembly → `tSide_theta_package_of_not_caseB_core` sorry 置換

規模: S-side stack ~2500 行の mirror (generic 部分は cite で短縮、実質 ~1000-1500 行 + 2 residual
は S-side と共通の precisely-named sorried-cite に collapse)。複数 session。CLAUDE.md 原則
(コスト・規模は判断基準でない) により淡々と建設する。次 iteration: step 1-2 (caseB-T、
uniform-degree route) から。

## 2026-07-14 更新 #42 (lane b, /loop iter 6) — caseB-T step 1 landed + step 2 の D-abelian 解析

**step 1 ✓**: `sSet_reducible_eq_nuRowSum` (TSideDegrees、sorry-free) — 𝒯 の reducible member =
ν-row sum。`pins.nu_reducible_dichotomy` (pure grid field) 経由の機械 mirror。

**step 2 (`sSet_caseB_apply_one_eq_vp`) の障害と解決 route**: S-side は `sSet_eq_sOf_H0Cprime`
(𝒮(H₀C')=𝒮 同定) で Cprime = derivedInG cSub = ⊥ を「cSub ≤ U abelian (carried
S_U_commutative)」から出す。T-side の対応 cSub-T = D で **D abelian ⟸ V abelian が (14.9)-gated**。

**解決 (caseB 分岐内で V abelian を導出)**:
- T type II/III: witness `U_commutative` (TypeII/IIIData 両方が field に持つ) + Schur–Zassenhaus
  conjugate transport (isMulCommutative_V の証明パターンの分岐版)。
- T type IV: witness は `U_not_commutative` — だが **caseB (Singer) データと (11.6)-T で排除可能**:
  (11.6)-T (S13.core_structure T-instance、card_Q_eq_qp と同じ chain): D = V' (C = U' の T)。
  caseB の Ū = V/D cyclic → V/V' cyclic、V nilpotent (isNilpotent_V) →
  「nilpotent + cyclic abelianization → abelian」(標準事実、mathlib/repo 所在要確認) → V abelian
  → type IV の U_not_commutative と矛盾 (witness transport) → **type IV は caseB と両立しない**。
- ⟹ `V_commutative_of_caseB : CliffordCaseBData (charsT) → IsMulCommutative ↥hyp.V`
  (unconditional、(14.9) 不要) → D abelian → Cprime-T = ⊥ → sSet_eq_sOf_H0Cprime-T →
  step 2 uniform degree。

次: 「nilpotent + cyclic abelianization → abelian」の所在確認 → V_commutative_of_caseB 構築。

## 🧭 HUB (2026-07-14, tick 38): #42 の「nilpotent + cyclic abelianization」所在 = 既存 repo leaf

#42 の「所在要確認」への回答: **`OddOrder/GroupTheory/NilpotentAbelianization.lean` に既存**
(lane a claim 9086、2026-07-12、sorry-free、S13_NonGaloisExclusion が live consume 中)。
`isCyclic_of_isNilpotent_of_isCyclic_quotient` + `isMulCommutative_of_isCyclic` を cite すること。
b の `2ca52edf` (新 leaf NilpotentCyclicAbelianization) は同内容の複製ゆえ差し戻し (合流せず) —
詳細 = issue 9086 HUB RULING。`V_commutative_of_caseB` の route (#43) 自体は genuine と評価済み、
supply 元を既存 leaf に差し替えて続行されたい。

## 2026-07-14 更新 #43 (lane b, /loop iter 6 続) — shared lemma landed + V_commutative_of_caseB 組み立て経路確定

**landed**: `OddOrder/GroupTheory/NilpotentCyclicAbelianization.lean` (新 shared leaf、sorry-free、
mathlib のみ依存): `commutator_eq_bot_of_isCyclic_quotient` + `isMulCommutative_of_isNilpotent_of_isCyclic_quotient`
(H nilpotent + H/H' cyclic → abelian; H⧸⁅H',⊤⁆ の central-kernel × cyclic quotient → mathlib
`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` → lcs stabilization)。

**`isMulCommutative_V_of_caseB` の組み立て経路 (次 iteration)**:
- 置き場所: S15_CharacterDegreeSupply (θ-witness 機構の隣; II 分岐が S15_SAndTBasic の
  isMulCommutative_V を使うため Setup 配下は不可)。
- T_nonI 分岐: **II** = isMulCommutative_V (既存、IsTypeII 直) / **V** = no_typeV 排除 /
  **III/IV** = 以下:
  1. `Ubar_cyclic` (CliffordCaseBData field): IsCyclic (uActionHom setupT chief).range。
     **setupT.typeP.U = V (reconciled choose_spec.1) なので domain は V-sub、ker.map = cSub = D
     (cSub_eq_D 済)** → V/D ≅ range cyclic (quotientKerEquivRange、
     mkSection11CharacterDataT_v_eq の key と同じ構図)。
  2. **D ≤ V'** ((11.6) deep 側): S13 chain (exists_hypothesis_of_typeIIIorIVorV →
     exists_hypothesis_of_isTypeIIIorIV → core_structure 第 4 成分 C = U') は witness
     w.U ≠ V なので **conjugation transport**: V = g • w.U (Schur–Zassenhaus
     exists_conj_of_coprime、isMulCommutative_V の証明パターン)、Q normal →
     D = V ⊓ C(Q) = g • (w.U ⊓ C(Q)) = g • s13.C = g • w.U' = (g • w.U)' = V'。
  3. D ≤ V' + V/D cyclic → V/V' cyclic (cyclic の quotient) + V nilpotent (isNilpotent_V)
     → 新 shared lemma → IsMulCommutative ↥V。
- 帰結: `Cprime-T = derivedInG D = ⊥` (D ≤ V' … V abelian → V' = ⊥ → D = ⊥!実は V abelian
  なら D ≤ V' = ⊥ で **D = ⊥ まで出る**) → sSet_eq_sOf_H0Cprime-T → step 2 uniform degree。

## 2026-07-14 更新 #44 (lane b, /loop iter 7) — ✅ isMulCommutative_V_unconditional: (13.2.a)-T V-side が完全 ungated

#43 の複雑な route (conjugation transport + (11.6)-T + cyclic-abelianization) は**不要だった**:
repo 精査で **S13_NonGaloisExclusion が (11.9.c) を sorry-free で完備**していると判明 —
`not_isTypeIV_of_mem_maximalSubgroups` (universal type-IV 排除) + `isTypeIII_of_hypothesis` +
`isMulCommutative_typePData_U_of_typePData_U` (witness 間 Schur–Zassenhaus conjugacy transfer)。

**`Hypothesis.isMulCommutative_V_unconditional`** (TSideDegrees、sorry-free、
#print axioms clean): T_nonI 4 分岐 — II/III は witness `U_commutative` + conjugacy transfer で
reconciled `tpd.U = V` へ、IV は (11.9.c) universal 排除、V は (10.10)。

**波及**:
1. **caseB-T の D-abelian 解決**: D ≤ V abelian → D abelian → `Cprime-T = derivedInG D = ⊥`
   (#42/#43 の障害消滅)。V abelian は caseB 前提すら不要。
2. **9096 hV 供給の unconditional 化**: `Hypothesis.swap` の `hV` は
   isMulCommutative_V_unconditional で直接供給可能 (hT2 → dictionary 経由は不要に;
   既存 consumer は変更不要だが a の producer threading はこちらを使える)。→ 9096 に通知。
3. hub audit (9096) の「V_commutative = post-(14.9) fact」は audit 当時は正しかったが、
   (11.9.c) chain (S13_NonGaloisExclusion、issue 1024) の landing により**現在は ungated**。
   NuGridSupplyData から外した判断自体は正しいまま (grid fact でないことに変わりなし)。

新 shared leaf `NilpotentCyclicAbelianization` (#43 で landing 済) は独立の価値で保持
(mathlib 級の一般補題)。次: sSet_eq_sOf_H0Cprime-T (Cprime = ⊥ 経由) → step 2 uniform degree。

## 2026-07-14 更新 #45 (lane b, /loop iter 7 続) — caseB-T step 2 (uniform degree) landed

**`sSet_caseB_apply_one_eq_vp`** (TSideDegrees、sorry-free): Clifford caseB で 𝒯 全 member の
degree = setupT.q · chars.u (= p·v)。`sSet_eq_sOf_H0Cprime` 相当を inline — H₀ = ⊥ (kernel
collapse #39) + **Cprime-T = ⊥** (cSub ≤ V + `isMulCommutative_V_unconditional` #44 →
derivedInG cSub = ⊥) → 𝒮(H₀C') = 𝒯 → generic `caseB_degree_qu`。

caseB-T coherence の残り: member diff support (S-side `sSet_caseB_member_diff_supported` mirror —
uniform degree + (4.7)-T support fact `sSet_member_support_subset` の T 版が要る)、per-member
R-family (S-side `S15_SSetMemberRFamily` route-B の T-mirror — S-side 自身に reducible-branch
residual あり)、(5.7) engine assembly (`sSet_coherent_dade_caseB` mirror)、caseA-T、pin、τ₁T。

## 2026-07-14 更新 #46 (lane b, /loop iter 8) — HUB tick 38 裁定受領: 重複 leaf 削除

hub 裁定 (tick 38 / issue 9086) を受領: 私の `NilpotentCyclicAbelianization.lean` (2ca52edf) は
lane a の 9086 claim (`NilpotentAbelianization.lean`、2026-07-12、S13_NonGaloisExclusion が live
consume) の**複製** — claim-before-build の 9000 scan を怠ったのが原因 (反省点として記録)。
b branch から削除する (consumer 0 — #44 の isMulCommutative_V_unconditional は conjugacy
transfer 経由で本 leaf を使っていない)。#43 の supply 計画は #44 の unconditional 化で
そもそも不要になっており、差し替え作業も発生しない。

なお #44 で「発見」と書いた S13_NonGaloisExclusion の (11.9.c) chain は a の issue 1024 P3 +
9086 の成果物 (2026-07-12 landing)。正しく attribute する。

## 2026-07-14 更新 #47 (lane b, /loop iter 8 続) — member-support-T の経路確定

caseB-T member-diff support の残り部材 `sSet_member_support_subset_A` T-mirror の経路精査:
- S-side は `hPeq : P = Msigma S` (type-II 等号、S_typeP2 carrier 経由) を使うが、**使用箇所は
  membership 方向のみ** — T-side は等号不要で `Q ≤ Msigma T` で足りる。
- **`OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hM`** (proven、TypeP1Criteria で
  live 使用) がそれを与える — type III でも成立 (M_F ≠ M_σ でも ≤ は一般)。
- 他の部品 (`support_induce_subset_conjugatesIntoSet` / (1.2) core
  `irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot` /
  `honestTypeP2ASet_conj_mem` / `mem_honestTypeP2ASet`) は M-generic ✓。
- 実装: SubcoherenceInputs:1231-1330 の逐語 mirror (hPeq → hQle、S→T、P→Q、~180 行) +
  `sSet_member_support_subset`-T + `sSet_caseB_member_diff_supported`-T (~60 行)。
  A(T) = honestTypeP2ASet hyp.T (M-generic def) で S-side と同形。

次 iteration: この 3 本 mirror → (5.7) engine assembly (`sSet_coherent_dade_caseB`-T)。

## 2026-07-14 更新 #48 (lane b, /loop iter 9) — (4.7)-T support 3 本 landed

TSideDegrees (sorry-free、一発 build):
- **`sSet_member_support_subset_A_T`**: 𝒯-member source の support ⊆ A(T) ∪ {1}。#47 の経路
  通り — type-II 等号の代わりに `maxNilpotentNormalHall_le_Msigma` (≤ で十分、type III OK)。
- **`sSet_member_support_subset_T`** (full-family form)
- **`sSet_caseB_member_diff_supported_T`**: uniform degree #45 + support → member 差は
  A(T)-supported ((5.7) engine の hsuppdiff 入力)。

caseB-T 残り: per-member R-family (S-side `S15_SSetMemberRFamily` — irr branch =
dadeOrthonormalCharacterImageFamilyOfDiff 系、red branch = route-B tauS_mu_cross、S-side 自身に
residual あり) + `sSet_coherent_dade_caseB`-T ((5.7) engine) + congrMap Ind 再接地。
R-family は dadeHypT0 (hT2/Tdata パラメトリック) 依存の可能性 — S-side の dadeHypS 依存構造の
確認から。

## 2026-07-14 更新 #49 (lane b, /loop iter 10) — (5.7)-T assembly の残入力精査: Dade 基盤の設計分岐

`sSet_coherent_dade_caseB` (S-side、全文精査) の (5.7) engine 入力 11 個の T-side 状況:
- ✓ 済/generic: finiteness、pivot (nu_rowSum_mem_sOf_H0_T + sOf_subset_sSet)、pivot norm = p
  (pins.nu_orthonormal、S-side hN と同計算)、pairwiseOrthogonal/closedUnderConjugate/
  hasNoRealCharacters (generic; oddCardS → oddCardT mirror 要 ~5 行)、diff_supported (#48)、
  uniform degree (#45)。
- **残 1: `dadeHypT` (A(T)-Dade datum)** — S-side `dadeHypS` =
  `(dadeSupportHypothesisData_honestTypeP2ASet hG S_maximal S_typeP2).some.dade`
  (generic 構成 + **IsTypeP2 carrier**)。T 版の設計分岐:
  (a) hT2-パラメトリック (dadeHypT0/tauTbetaGrid の既存パターン) — ただし (13.4) は (14.9) 前に
      使われるため hT2 供給が S16.T_isTypeP2 (sorried、hub 指摘の循環リスク) になる懸念。
      **要確認**: tSide_theta_package の消費文脈に hT2 があるか。
  (b) `dadeSupportHypothesisData_honestTypeP2ASet` の実装を精査し、IsTypeP2 引数が実は
      IsTypeP (or type II∨III) で足りるなら **unconditional 化** (isTypeP_of_isTypeNonI +
      isTypeIII_of_hypothesis の世界)。(13.2.e) 原文は (8.13)+(12.7) の type-P 一般論。
- **残 2: per-member R-family** (`sSet_memberRFamily` T-mirror) — irr branch =
  `dadeCharacterDifferenceImageOfDiff` (dadeHypT 依存、上と同根)、red branch = route-B
  (`tauS_mu_cross` の T-mirror = tauT_nu_cross、S16_GridExpansion の eta_diff_rigidity T-instance;
  S-side 自身の residual と同形になる見込み)。

次 iteration: (b) の実装精査 (`dadeSupportHypothesisData_honestTypeP2ASet` の IsTypeP2 使用箇所)
→ 分岐決定 → dadeHypT + oddCardT + R-family irr branch。

## 2026-07-14 更新 #50 (lane b, /loop iter 11) — dadeHypT (設計決定 = hT2-パラメトリック) + oddCardT landed

**設計決定 (分岐 (a))**: `dadeSupportHypothesisData_honestTypeP2ASet` の hP2 使用を精査 —
本質使用は `typeP2_exists_matched_kappa_hall_pair` (matched κ/(κ∪σ)'-Hall pair、U₀ abelian 込み)
のみで、消費側 3 lemma ((8.13.a/b/c2)) は pair データだけ取る。type III 版 pair は E-setup chain
(BG §16 Thm A–E 級) の P₁ 対応 port が要り別戦線。**repo 確立済みの hT2-パラメトリック設計**
(dadeHypT0 / tauTbetaGrid / typeI_caseC_dual_dichotomy と同層) を採用。unconditional 化
(type-III pair port) は将来の独立 obligation。

**landed** (TSideDegrees、sorry-free): `oddCardT` (realness 入力) / `dadeHypT` (A(T)-Dade datum、
hT2 param) / `dadeHypT_hconj`。

残: per-member R-family (irr branch = `dadeCharacterDifferenceImageOfDiff` over dadeHypT +
`sSet_member_diffsupp`-T; red branch = route-B tauT_nu_cross) → `sSet_coherent_dade_caseB`-T
assembly (hT2-パラメトリック)。

## 2026-07-14 更新 #51 (lane b, /loop iter 12) — R-family irr-branch 入力 2 本 landed

TSideDegrees (sorry-free、一発 build): **`sSet_member_diffsupp_T`** ((5.3.a)-T per-member 差
support — support ⊆ A(T)∪{1} #48 + degree 実正値で 1 除去) + **`sSet_member_conjDiff_supported_T`**
(case-agnostic conjugate-diff support)。

⟹ irr branch の R-datum は `dadeOrthonormalCharacterImageFamilyOfDiff (dadeHypT hG hT2)
(dadeHypT_hconj) ⟨η,hirr⟩ (no-real via oddCardT) (conjDiff_supported_T)` で組める。
残: red branch (route-B `tauT_nu_cross` — S15_BridgeCharacter `tauS_mu_cross` の T-mirror、
pins.nu_apply_of_not_mem_W1 + eta_diff_rigidity 系; dadeHypT0 との dade=Ind 橋も) →
`sSet_memberRFamily_T` dispatch → `_orthogonal` → engine assembly。route-B は
S16_GridExpansion 下流ゆえ **置き場所は TSideDegrees 不可** (S16_GridExpansion → S15_SAndT_Setup
逆依存確認要) — S15_SSetMemberRFamily に同居 or 新 leaf `S15_TSetMemberRFamily`。

## 2026-07-14 更新 #52 (lane b, /loop iter 13) — red branch (tauT_nu_cross) の依存 5 点監査

`tauS_mu_cross` (S15_BridgeCharacter:917) の T-mirror `tauT_nu_cross`
(τ_T⁰(ν_{rj} − ν_{sj}) = η_{rj} − η_{sj}、行差・列固定) の依存対応:
1. irr/orthonormal → `pins.nu_irreducible`/`pins.nu_orthonormal` ✓
2. diff A₀-support → **`pins.nu_diff_support`** ((4.8)-T field、最初から行差形!Tdata param) +
   equal degree = `nu_apply_one_eq_v` (両方 v) ✓ — S-side の tauS_mu_diff_support 相当 wrapper 要
3. Dade ZIrr/isometry (generic S07) + `dadeHypT0` (既存、hT2/Tdata param) ✓
4. **`tauT_nu_vanish_on_V`** (regular set 上 τ⁰(ν-diff) = η-diff) — 唯一の実質新規 mirror。
   S-side `tauS_mu_vanish_on_V` の証明精査が次段 (dade0_apply_eq_zero_of_regular 系 +
   η vanish fields の組合せと推測)。
5. rigidity → **swap-instance transpose**: `eta_diff_rigidity (hyp.swap hT2 hV Tdata … pins)` で
   行固定形を transpose 適用 (swap.eta i j = hyp.eta j i、regular set は union_comm で同一、
   hV = isMulCommutative_V_unconditional ✓)。行差 rigidity の独立実装不要 (c-owned
   S16_GridExpansion への追記も不要)。
置き場所: S15_BridgeCharacter 同居 (S-cross と並置、rigidity/swap とも import 済、b 実績 file)。

## 2026-07-14 更新 #53 (lane b, /loop iter 14) — vanish-on-V-T 系 4 本 landed (cross-T 部材完備)

- hub 登録: `TSideDegrees` を `S15_SAndT_Setup` hub に追加 (未登録だった)。
- `deltaPrime_eq_one_pins` (TSideDegrees): 全 i の δ'=1、pins-パラメトリック。
- **HonestTypeP2A0 に T-mirror 4 本** (sorry-free、一発 build):
  `dadeHypT0_H_eq_ftSupportKernel` / `forall_dadeHypT0_H_eq_bot` (A₀(T) normedTI、
  generic escaping-empty の (hT2,Tdata)-instance) / `tauT_nu_diff_support` ((4.8)-T wrapper、
  pins.nu_diff_support + nu_apply_one_eq_v) / **`tauT_nu_vanish_on_V`** (regular set 上
  τ_T⁰(ν-行差) = η-行差; typePV 側は hW1/hW2 交換 + union_comm、値は
  nu_apply_of_not_mem_W1 + deltaPrime_eq_one_pins)。

⟹ `tauT_nu_cross` の依存 5 点が**全て**揃った (残るは本体 assembly + swap-transpose rigidity
のみ、~80 行、置き場所 = S15_BridgeCharacter)。次 iteration で cross-T 本体。

## 2026-07-14 更新 #54 (lane b, /loop iter 15) — ✅ tauT_nu_cross landed (red branch の核心)

**`tauT_nu_cross`** (S15_BridgeCharacter、sorry-free、一発 build):
τ_T⁰(ν_{r,j} − ν_{s,j}) = η_{r,j} − η_{s,j} (列固定・行差、r≠s 両方 ≠0)。
- norm-2 ZIrr: pins.nu_irreducible/nu_orthonormal + tauT_nu_diff_support + generic S07 isometry
- regular-set 一致: tauT_nu_vanish_on_V (#53)
- **(3.8) rigidity は swap-transpose**: `eta_diff_rigidity (hyp.swap hT2 hV Tdata … pins)` —
  swap の η-grid が transpose なので行固定形がそのまま列固定形に。swap 構造 field の
  coercion 同一性 (W/W1/W2) は **rfl で通った** (defeq)。hV = isMulCommutative_V_unconditional。

red branch 残り: rows_ne-T (conj 行相異) → `sSet_reducible_memberRFamily_T`
(cross の ν-row 総和 → 2p-element OrthonormalCharacterImageFamily、S-side
`sSet_reducible_memberRFamily_ofColumns` mirror) → dispatch (`sSet_memberRFamily_T`) →
`_orthogonal` → (5.7) engine assembly。

## 2026-07-14 更新 #55 (lane b, /loop iter 16) — T-side dade=Ind bridge chain 完備

HonestTypeP2A0 に 5 本追加 (sorry-free): `dadeHypT_H_eq_ftSupportKernel` /
`no_escaping_honestTypeP2ASet_T` (generic escaping-empty の hT2-instance) /
`forall_dadeHypT_H_eq_bot` ((13.2.e)-T stabilizer form) / **`tInstance_dade_eq_induce`**
(τ_T = Ind on A(T)-supported) / **`tInstance_dade0_eq_induce`** (τ_T⁰ = Ind on A₀(T)-supported、
forall_dadeHypT0_H_eq_bot #53 経由)。

⟹ `tauT_nuRow_diff_eq` (S-side `tauS_muColumn_diff_eq` mirror: τ_T(ν_r − ν̄_r) = ∑_j(η_{rj}−η_{sj})、
A/A₀ Dade 一致 + cross 総和) の部材完備。残: rows_ne-T + nuRow_diff_eq + ofRows family 本体 +
dispatch + orthogonal + engine。

## 2026-07-14 更新 #56 (lane b, /loop iter 17) — rows_ne-T + tauT_nuRow_diff_eq landed

- `sSet_reducible_conj_not_irr_T` / **`sSet_reducible_rows_ne`** (TSideDegrees): reducible
  𝒯-member とその conjugate の ν-行相異 (no-real 経由)。
- **`tauT_nuRow_diff_eq`** (BridgeCharacter): τ_T(η − η̄) = ∑_j(η_{rj} − η_{sj}) — A/A₀ Dade
  一致 (tInstance bridges #55) + `tauT_nu_cross` (#54) の列総和。

R-family 残: `ofRows` 本体 (S-side `sSet_reducible_memberRFamily_ofColumns` の
OrthonormalCharacterImageFamily 構築 mirror、~100 行) → dispatch → `_orthogonal` → (5.7) engine。

## 2026-07-14 更新 #57 (lane b, /loop iter 18) — ✅ T-side per-member R-family 完成

新 leaf **`S15_TSetMemberRFamily.lean`** (sorry-free、一発 build):
- `sSet_reducible_memberRFamily_ofRows`: 2p-element signed η-grid family (rows r≠s)、
  image_eq = `tauT_nuRow_diff_eq`、orthonormal = eta_orthonormal 行違い。
- `sSet_reducible_memberRFamily_T`: reverse-dichotomy dispatch wrapper。
- **`sSet_memberRFamily_T`**: case-agnostic 全 member dispatch (irr = 2-element Dade family
  over dadeHypT / red = route-B)。

(5.7)-T engine の入力残 1: **`sSet_memberRFamily_orthogonal` の T 版** ((5.2.e)
cross-orthogonality、S-side SSetMemberRFamily:794)。それで engine assembly
(`sSet_coherent_dade_caseB_T`) が組める。

## 2026-07-14 更新 #58 (lane b, /loop iter 19) — dadeT0_apply_eq_zero_of_regular landed + orthogonal-T 依存監査

- **`dadeT0_apply_eq_zero_of_regular`** (TSetMemberRFamily、sorry-free): A(T)-supported f の
  A₀(T)-Dade 像は regular set 上 0 (S 版 mirror; of_isConj の x→w 書き換えが必要だった)。
- orthogonal-T の依存監査完了: `eta_orthogonal_of_norm_one_pair_vanish` は **hyp-level で
  T にもそのまま適用可** (η/W grid は S/T 共有)。残 mirror: imageSet_of_irr/red-T (dispatch
  分解 rfl 系) / `sSet_irr_memberRFamily_eta_inner`-T (rigidity engine 適用、
  dadeT0_apply_eq_zero_of_regular + tInstance_dade{,0}_eq_induce で S 版逐語) /
  `dadeOfDiff_orthogonal_typeP_T` (S08 generic wrapper) / `nu_rowSum_ne_of_inner_zero` /
  orthogonal-T 本体 (2×2 分岐) → **(5.7) engine assembly**。

## 2026-07-14 更新 #59 (lane b, /loop iter 20) — orthogonal-T 部材 5 本 landed (残り本体のみ)

TSetMemberRFamily (sorry-free、一発 build): `sSet_reducible_memberRFamily_ofRows_imageSet` (rfl) /
`sSet_memberRFamily_T_imageSet_of_irr` / `_of_red` (dispatcher 分解) / `nu_rowSum_ne_of_inner_zero`
/ **`sSet_irr_memberRFamily_eta_inner_T`** (最大部材 — τ_T(φ−φ̄) の constituents が η-grid ⊥、
tInstance bridges + dadeT0_apply_eq_zero_of_regular + hyp-level
eta_orthogonal_of_norm_one_pair_vanish)。

残: `dadeOfDiff_orthogonal_typeP_T` wrapper + **`sSet_memberRFamily_orthogonal_T`** 本体 (2×2) →
(5.7) engine assembly `sSet_coherent_dade_caseB_T`。

## 2026-07-14 更新 #60 (lane b, /loop iter 21) — ✅ orthogonal-T 完成: (5.7)-T engine 入力 11/11 完備

TSetMemberRFamily (sorry-free、一発 build): `dadeOfDiff_orthogonal_typeP_T` (irr×irr wrapper) +
**`sSet_memberRFamily_orthogonal_T`** (2×2 本体 — irr×irr は S08 generic、irr×red/red×irr は
eta_inner-T、red×red は行相異 + eta_orthonormal)。

**(5.7)-T engine `uniform_degree_coherence_of_families` の入力が全部揃った**:
finiteness/pivot/pivot-norm/R-family/pairwiseOrth/closedConj/no-real/Dade-isometry(dadeHypT)/
diff-supported/uniform-degree/R-orthogonal。次 iteration: engine assembly
`sSet_coherent_dade_caseB_T` (S 版 sSet_coherent_dade_caseB の mirror、~100 行)。

## 2026-07-14 更新 #61 (lane b, /loop iter 22) — ✅✅ caseB-T (9.11) coherence 完成

**`sSet_coherent_dade_caseB_T`** (TSetMemberRFamily、sorry-free、一発 build、#print axioms clean):
Galois case の 𝒯 全 family coherence on dadeHypT — (5.7) uniform-degree engine への 11 入力
全て T-instance 部材で供給 (pivot = ν-row、norm p、uniform degree p·v、R-family、orthogonality)。
**#41 建設計画の step 1-2 (caseB-T) が完全達成** (pins/hT2/Tdata パラメトリック)。

残 (#41): step 3 caseA-T (base cut + generic reduction + M-common (9.11.7-8) refuter cite) /
step 4 dispatch + ν-row pin / step 5 τ₁T + (5.3.b)-T + conjunct 4 / step 6 conjunct 5 /
step 7 package assembly。

## 2026-07-14 更新 #62 (lane b, /loop iter 23) — caseA-T 設計監査 (次セッション引き継ぎ)

S 版 caseA 構造の精査結果:
- **base cut** `sSetIrrDeg_qa_coherent_indS_caseA` (HypothesisBasics:523): degree-q·a irr cut の
  coherence — T 版は degree-p·a cut (`sSetIrrDeg` は hyp.S 固定 def → T 版 def から要 mirror)。
- **reduction** `coherent_of_maximal_coherent_pair_refuted` (S07 generic) ✓ そのまま。
- **refuter** `sSet_caseA_nineElevenRefutation` (CaseACoherence:514): **S 版自体が sorried**
  (docstring に reuse map 記録済 — generic (9.11) apparatus は sOf-parametrized で T-instance
  直接適用可、S-specific residual = caseA per-member R-family + (5.6) pair-bound、
  M-common residual = (9.11.7-8)、issue 9083)。T 版は同構造の precisely-named sorried
  obligation として立てる (S 版が閉じれば同機構で T も閉じる)。

**caseA-T 実装順 (次セッション)**: sSetIrrDeg-T def + base cut mirror → dispatch
(`sSet_coherent_indT_A`: clifford_dichotomy at mkSection11CharacterDataT、caseB 分岐 =
`sSet_coherent_dade_caseB_T` ✓ + congrMap Ind 再接地 `tInstance_dade_eq_induce` ✓) →
refuter-T (sorried、S 版 signature mirror) → step 4 pin (ν-row formula) → step 5 τ₁T +
(5.3.b)-T + conjunct 4 → step 6-7 package。

## 📌 セッション総括 (2026-07-14、lane b、iter 1-23)

**T-side (13.3)/(13.4) 戦線の成果** (全 commit build green + axioms clean):
1. 9096 bundle split (NuGridSupplyData pure grid 化 + swap hV) — hub ruling 実施
2. (13.3.c) δ'ᵢ = 1 完全 assembly (v ≡ 1 mod p Frobenius 証明、|Q| 約分 counting)
3. **card_Q_eq_qp**: |Q| = q^p **無条件** ((11.7) chain + order relation + no-typeV/IV)
4. (13.3.a)-at-T: nu_i_isIndQD + nu_apply_one_eq_v (kernel collapse 込み)
5. (13.3.b)-at-T: θ-witness dichotomy (T_caseB_facts_no_theta / thetaWitness_of_not_caseB)
6. **isMulCommutative_V_unconditional** ((11.9.c) chain 発見による V-side (13.2.a) 完全 ungate)
7. (13.4) conjunct 1-3 + support estimate (K ⊴ T + Ind vanishing)
8. **caseB-T (9.11) coherence 完成** (`sSet_coherent_dade_caseB_T`): Dade 基盤 (dadeHypT/T0 +
   dade=Ind bridges + regular vanishing)、R-family (irr 2-element + red 2p-element route-B、
   tauT_nu_cross は swap-transpose rigidity)、(5.2.e) orthogonality、(5.7) engine — 全て
   sorry-free、pins/hT2/Tdata パラメトリック。
9. 重複 leaf 事故 (9086) の是正 + claim-before-build 教訓の memory 記録。

残 sorry (b 関連): nuGridSupply (a-owned producer)、tSide_theta_package (conjunct 4/5 待ち)、
lambda_forces_T_caseB_core、caseA-T refuter (次セッション立て)。

## 2026-07-14 更新 #63 (lane b, /loop iter 24) — sSetIrrDegT 基本層 landed

TSetMemberRFamily (sorry-free、一発 build): `sSetIrrDegT` def (uniform-degree irr cut of 𝒯) +
subset/closedUnderConjugate/hasNoRealCharacters/member_support_subset/member_diff_supported。

caseA-T 残 chain: `sSetIrrDegT_coherent` (cut 上の uniform engine — S 版 HypothesisBasics 260-440
の mirror、irr-only R-family で組む) → `_indT` (congrMap + tInstance_dade_eq_induce ✓) →
`sSetIrrDegT_pa_two_le_ncard` ((9.8.d) caseA_exists_irreducible_qa の T-instance + conj doubling)
→ `sSetIrrDegT_pa_coherent_indT_caseA` → dispatch `sSet_coherent_indT_A` → refuter-T (sorried、
S 版 signature mirror)。

## 2026-07-14 更新 #64 (lane b, /loop iter 25) — caseA-T base cut coherence 完成

TSetMemberRFamily (sorry-free、一発 build): `sSet_member_differenceImage_T` (irr per-member
R-datum over dadeHypT) / `sSetIrrDegT_finite` / **`sSetIrrDegT_subcoherent`** ((5.2)-subcoherence、
irrSubcoherent + T 部材) / **`sSetIrrDegT_coherent`** ((5.7)∘(5.3.a) uniform-degree producer、
base count h2 exposed — S 版と同じ honest pattern)。

caseA-T 残: base count `sSetIrrDegT_pa_two_le_ncard` (generic `caseA_exists_irreducible_qa` の
T-instance + conj doubling) → caseA assembly (`coherent_of_maximal_coherent_pair_refuted` +
refuter-T sorried) → dispatch `sSet_coherent_dadeT_A` (clifford_dichotomy、caseB 分岐 =
`sSet_coherent_dade_caseB_T` ✓)。

## 2026-07-14 更新 #65 (lane b, /loop iter 26-27) — ✅ caseA-T assembly + dispatch `sSet_coherent_indT_A`

TSetMemberRFamily (build green、AxiomsCheck 4190 jobs OK):
- **`sSetIrrDegT_pa_two_le_ncard`** (sorry-free、axiom-clean): (9.8.d) generic
  `caseA_exists_irreducible_qa` の T-instance + 共役倍加 → `2 ≤ |S₁(p·a)|`。
- **`sSetIrrDegT_coherent_indT`** (sorry-free、axiom-clean): (5.7) cut coherence を
  `tInstance_dade_eq_induce` congrMap で Ind_T^G に再接地。⚠ T-side instance 規約:
  `[Fintype G]`/`[Invertible]` 明示 binder は scoped FiniteInduce (`ambientFintype`/
  `natCardInvC`) と unify しない → S 版同様 `[Finite G]`-only で統一 (defeq trap 実例)。
- **`sSetIrrDegT_pa_coherent_indT_caseA`** (sorry-free、axiom-clean): caseA-T `h0`。
- **`sSet_caseA_nineElevenRefutation_T`** (意図した sorried obligation、S 版 signature の
  precise mirror + hT2): docstring に reuse map (generic (9.11) apparatus は data-parametrized
  で T 直接適用可 / S-specific residual = per-member R-family + (5.6) pair-bound / M-common
  = (9.11.7-8) issue 9083)。S 版 chain (`nineElevenSTwoExtractionS`/`nineElevenNormBoundS`/
  `nineElevenEqualityRefutationS`) が閉じれば S↦T dictionary 置換で閉じる。
- **`sSet_coherent_indT_caseA`**: generic `coherent_of_maximal_coherent_pair_refuted` +
  base ✓ + refuter-T (唯一の sorry 源)。
- **`sSet_coherent_indT_A`** (dispatch、#41 step 3 完): `clifford_dichotomy` at
  `mkSection11CharacterDataT` → caseA 分岐 = 上記 / caseB 分岐 = `sSet_coherent_dade_caseB_T`
  ✓ を congrMap 再接地。**caseB-T 側は完全 sorry-free で dispatch に接続済**。
- `indT`/`indT_apply` を CharacterDegreeSupply → SubcoherenceInputs (indS の隣) に移設。
- AxiomsCheck: clean 3 endpoint 登録 + `import S15_TSetMemberRFamily` 追加 (leaf ゆえ未 import だった)。

残 (#41): step 4 dispatch 済につき → ν-row pin (τ(μ-col)=η-col の T 版) → step 5 τ₁T +
(5.3.b)-T + conjunct 4 → step 6 conjunct 5 → step 7 package assembly。

## 2026-07-14 更新 #66 (lane b, /loop iter 28) — ν-row pin 機構 第 1 層 (S15_NuRowPin.lean 新設)

新 leaf `S15_NuRowPin.lean` (TSetMemberRFamily の上、全て sorry-free・axiom-clean、一発 build):
- `nuRow_apply_one` (p·v) / `nuRow_inner` (p·[r=s]) / `nuRow_not_irreducible` — pure grid 基礎
- `nuRow_diff_supported` — 任意行差の A(T)-support (muColumn_diff_supported mirror)
- **`coherentIndT_nuRow_diff`** — 行独立性 c(ν_r) − c(ν_s) = ∑η_r − ∑η_s
  (extends_on_supported → indT_apply → tInstance_dade0_eq_induce → per-column tauT_nu_cross)
- **`coherentIndT_image_inner_eta_eq_zero`** — **(5.3.b)-at-T** (family-generic;
  #41 step 5 の入力): coherent image ⊥ η-grid。S 版より短い —
  `dadeT0_apply_eq_zero_of_regular` (既設) が regular 消滅を丸ごと供給。
  ⚠ S 版の Fintype/Invertible subst juggling は [Finite G]-only 化で不要。

AxiomsCheck: import を S15_TSetMemberRFamily → S15_NuRowPin に置換 (推移含意) + 2 endpoint 登録。

残 (pin 完成まで): `coherentIndT_extension_irr_vanish_regular` (γ-trick 前半、mirror ~30 行) →
`coherentIndT_nuRow_vanish_regular` (γ-trick、mirror ~90 行; dadeT0 regular ✓ 流用) →
**`coherentIndT_nuRow_pin_of_irr`** (本体 ~270 行 mirror; 必要部材
`sSet_coherent_extension_eq_sum_memberRFamily`-T (R-family 分解、S 版は CaseBReducibleCoherence)
+ `sSet_reducible_eq_nuRowSum` ✓ + `sSet_memberRFamily_T_imageSet_of_red` ✓ +
`S16.inner_eta_grid_relation` (generic ✓) + eta_orthonormal ✓) → `..._eq_etaRow_of_pivot` →
all-reducible glue → `sSet_coherent_indT_A_pinned`。

## 2026-07-14 更新 #67 (lane b, /loop iter 29-30) — ✅✅ (13.3.c)-T ν-row pin 完成 (#41 step 4 完)

S15_NuRowPin.lean 836 行 (全 sorry-free・axiom-clean・各 build 一発 green):
- γ-trick pair: `coherentIndT_extension_irr_vanish_regular` (irr image の Ŵ^G 消滅) +
  `coherentIndT_nuRow_vanish_regular` (γ = ξ(1)·ν_i − (p·v)·ξ の A(T)-support + dadeT0 消滅)
- `etaRow_inner`/`etaRow_inner_self` (η-row p·[r=s])
- `sSet_coherent_extension_eq_sum_memberRFamily_T` ((5.5)-T、CharacterPsiDecomposition 経由)
- **`coherentIndT_nuRow_pin_of_irr`** (pin 本体 ~250 行): E ⊆ {η_{ij}} ∪ {−η_{sj}} 分解 →
  membership 指標 → **(3.7) rectangle relation は S/T 対称** (row-0 corner を消して
  column-uniform 化 — swap/transpose 不要が判明、tauT_nu_cross の swap 経由と対照的) →
  ‖c(ν_i)‖² = p で全行 pick。
- `coherentIndT_nuRow_eq_etaRow_of_pivot` (pivot 伝播、行独立性経由)

AxiomsCheck 2 endpoint 追加 (4192 jobs green)。main 再同期 (c レーン初 landing 取り込み、非競合)。

残 (#41 step 4 の pinned assembly → step 5): all-reducible glue
(`exists_pinned_coherent_sSet_of_all_reducible` の T-mirror、S 版 = CaseBReducibleCoherence:762)
→ `sSet_coherent_indT_A_pinned` (dispatch + pin bundling、S 版 = CaseACoherence:720) →
step 5 τ₁T 定義 + conjunct 4 assembly。

## 2026-07-14 更新 #68 (lane b, /loop iter 31) — ✅ #41 step 4 完全達成: pinned assembly

S15_NuRowPin.lean 1261 行 (⚠ 1500 接近 — 次の主結果で新 leaf 切り):
- **`exists_pinned_coherent_sSet_of_all_reducible_T`** (sorry-free・axiom-clean、一発 build):
  all-reducible glue — coherentImageMap over 直交 ν-row family、residual
  r = ηrow₁ − Ind(νrow₁) の行独立性 (per-column tauT_nu_cross)、A(T)-supported は x(1)=0 で
  residual 消滅。S 版の機械 mirror (index 転置のみ)。
- **`sSet_coherent_indT_A_pinned`** (唯一の sorry 源 = refuter-T 経由、S 版と同 profile):
  has-irr 分岐 = dispatch + pin dichotomy + pivot 伝播 + **flip は q = 3 を強制**
  (q ≥ 5 なら第 3 行 i₂ ∉ {0,1,s} で行差恒等式が flip と矛盾) + q=3 で 2 行 swap 転送 /
  all-reducible 分岐 = glue の clean pin。

**T-side (9.11) coherence 戦線がフル装備になった**: dispatch (indT) + Dade 版 (caseB) +
pin dichotomy + pinned carrier。residual は refuter-T (S 側 construction site と共通機構) と
a-owned nuGridSupply のみ。

次 = #41 step 5: `tau1T_ofHonest` (pinned carrier の bundling、S 版 = tau1S_ofHonest
CaseACoherence:870 — ⚠ [[lean-nonempty-some-erases-witness-pin]]: pin は Nonempty.some で
消える、bundle 必須) → (5.3.b)-T ✓ (coherentIndT_image_inner_eta_eq_zero 済) → conjunct 4
assembly (⟨η_{ij}, Ind(θT−ν_r)⟩ = −δ'[i=r])。

## 2026-07-14 更新 #69 (lane b, /loop iter 32) — #41 step 5 前半: τ₁T bundling (S15_Tau1T.lean 新設)

新 leaf S15_Tau1T.lean (build green; sorryAx = pinned carrier → refuter-T 経由の意図伝播、
S 側 tau1S_ofHonest と同 profile):
- `coherentIndT_pinned` (carrier .choose) / **`tau1T_ofHonest`** (.extension) /
  `tau1T_ofHonest_nuRow_formula` (.choose_spec pin)
- **`tau1T_ofHonest_nuRow_eta_row`** (per-row consumable 形): ∀ r ≠ 0, ∃ r' ≠ 0, δ' = ±1,
  τ₁T(ν_r) = δ'·∑_j η_{r'j}。**設計発見: (13.4) θ-package の conjunct 3 は η-row index を
  θ-row と別に量化する必要がある** — flip 分岐 (q=3) では τ₁T(ν_r) ≠ ±∑η_{rj} (行が真に
  swap する) ため same-index 形は unprovable。下流の eta_cross_expansion 矛盾は「どこかの
  nonzero 行」で足りるので split 量化が忠実 (consumer `lambda_forces_T_caseB_core` の
  expansion brick は r を自由引数で受けており r' 化は無害 — 要 restate)。
- `tau1T_ofHonest_extends_on_supported` ((13.2.e) 一致、conjunct 3 producer) /
  `tau1T_ofHonest_image_inner_eta_eq_zero` ((5.3.b)-T at τ₁T、conjunct 4 producer)

供給 producer 確認済: pins = hyp.nuGridSupply hG (sorried、a-owned 9096) / hvd =
hyp.vd_ne_one hG / Tdata+hU+hW1+hW2 = reconciled_typePData_T choose / hT2 = SAndTBasic:192
パターン / chief = exists_chiefFactorData。

次 = θ-package assembly: `tSide_theta_package_of_not_caseB_core` の conjunct 3 を r'-量化に
restate (consumer の expansion 呼び出しも r'-thread — 共に b-owned 同一 file) → ThetaWitness
(Ind_K θ) の 𝒯-membership 接続 (conjunct 4 の (5.3.b) 適用に必要) → conjunct 2
(indK_sub_nuRow_support ✓ #40) + 3 + 4 の組立。conjunct 5 (S/T cross) = step 6。

## 2026-07-14 更新 #70 (lane b, /loop iter 33) — (1.5.a)-T membership 層 (θ-package 部材)

S15_Tau1T.lean 376 行に追加 (全 sorry-free・axiom-clean・一発 build):
- `zSpan_sSet_support_subset_T` / **`zSpan_sSet_degree_zero_support_T`** — ℤ[𝒯] の
  A(T)∪{1} support + degree-0 ⟹ A(T)-support。**conjunct 3 の support 橋はこれで完結
  ((QD)# ⊆ A(T) の直接橋は不要 — S 側と同じ zSpan+degree-0 ルート)**。
- **`induce_K_mem_zSpan_T`** — Ind_K^T θ ∈ ℤ[𝒯] (θ irr on K=QD、Q ⊄ ker θ)。
  induce_H_mem_zSpan_S の mirror: K ≤ T' (T_deriv_eq_QV)、hInHu = Q.subgroupOf T'
  (toTypesIIIIIIVSetupT_H_eq)、constituent kernel 転送 (generic
  constituent_P_not_subset_characterKernel、CaseACoherence import 追加)。

残 (θ-package まで): `induce_K_mem_zSpan_sSet_irr_T` (irr 版 membership、S 版 =
CharacterDegreeSupply:55 の mirror ~100 行; 反例列 = ν-row との直交) →
`tau1T_ofHonest_zSpanIrr_inner_eta` (span 帰納 + (5.3.b)-T crux ✓) →
`tau1T_ofHonest_induce_inner_eta` (conjunct 4 producer) → `tau1T_ofHonest_apply_induce_sub`
(conjunct 3 producer; θ(1)=1 仮説版 — K-abelian 不要) → package 本体
(conjunct 3 の r' 量化 restate + consumer thread + 組立)。

## 2026-07-14 更新 #71 (lane b, /loop iter 34) — θ-package conjunct 2-4 producers 完備

S15_Tau1T.lean 700 行 (build 一発 green):
- **`induce_K_mem_zSpan_sSet_irr_T`** (sorry-free・axiom-clean): irr 版 membership —
  Ind_K^T θ 自身が irr なら全 nonzero 係数 constituent が irr member (反例 = ν-row との
  直交性 ⟨Ind θ, ν_i⟩ = 0 vs k·p > 0; S 版の μ→ν 機械 mirror)。
- `tau1T_ofHonest_zSpanIrr_inner_eta` (span 帰納 + (5.3.b)-T crux)
- **`tau1T_ofHonest_induce_inner_eta`** = conjunct 4 producer (τ₁T sorryAx profile)
- **`tau1T_ofHonest_apply_induce_sub`** = conjunct 3 producer (θ(1)=1 明示仮説版 —
  S 版の H-abelian 経由を回避、K-abelian 不要)

**θ-package の τ₁ 側部材が全て揃った**: conjunct 2 = indK_sub_nuRow_support ✓ (#40) /
conjunct 3 = apply_induce_sub ✓ + nuRow_eta_row ✓ (r'-形) / conjunct 4 = induce_inner_eta ✓。

次 = package 本体組立 (CharacterDegreeSupply): (a) `tSide_theta_package_of_not_caseB_core` の
conjunct 3 を「∃ r' ≠ 0」量化に restate + 供給 producer 束線 (pins = hyp.nuGridSupply hG
[sorried a-owned] / hvd = vd_ne_one / Tdata 系 = reconciled_typePData_T / hT2 = SAndTBasic:192
経由 / chief = exists_chiefFactorData / θ-witness = thetaWitness_of_not_caseB) →
(b) consumer `lambda_forces_T_caseB_core` の hβform r'-thread → (c) conjunct 5 (S/T cross
直交、step 6) は package 内で θG = τ₁T(θT) 形から導出予定 (τ₁λ ⊥ η-grid ✓ +
disjoint-support h0 パターン)。CharacterDegreeSupply に import S15_Tau1T 追加要 (DAG ✓ 無循環)。

## 2026-07-14 更新 #72 (lane b, /loop iter 35) — 原文 (13.4) 精読 + package restate + dirr bricks

**原文検証 (mmd 04.15 p.75-86)**: (13.4) の (13.3.c) cite は両側とも target index 自由
(μ₁^{τ₁} = ±∑_i η_{is}、ν₁^{τ₁} = ±∑_j η_{rj}) — #69 の r'-一般化は原文通りと確認。
conjunct 5 (⟨λ^{τ₁}, θ^{τ₁}⟩ = 0) の原文根拠 = 「(4.1)+(5.3.b) で η・λ^{τ₁}・θ^{τ₁} pairwise
直交」+ 中間表示 ((λ−λ̄)^τ, (θ−θ̄)^τ) = 0 (disjoint support)。

実施:
- **package restate**: `tSide_theta_package_of_not_caseB_core` conjunct 3 を ∃ r' 量化に変更
  + consumer `lambda_forces_T_caseB_core` の obtain/expansion を r'-thread (build green、
  expansion brick は η-row index を自由引数で受けるので無修正適合)。
- **dirr bricks (Tau1T、sorry-free・axiom-clean)**:
  `conj_eq_of_norm_one_conj_antisym` — A,B norm-1 ZIrr、⟨A,B⟩=0、Ā−B̄ = B−A ⟹ B = Ā ∧
  constituent 非実 (χA との inner で εA(real-ind + 1) = εB·[χ̄B=χA] を case bash)。
  `inner_eq_zero_of_conj_diff_orthogonal` — 2 対の conj-antisym pair + ⟨A−B, C−D⟩ = 0 ⟹
  ⟨A,C⟩ = 0 (共有 constituent なら h0 = ±2 ≠ 0)。
  ⚠ 実装注意: repo の ClassFunction.inner は**右 slot 共役** (inner_smul_left は star 無し);
  rw の if_neg は条件向きを show で明示 pin (逆向き ne は h.symm)。

残 = package 本体組立 (次 iteration): θ-witness → θT := Ind_K θ、r := 1、
conjunct 2 = indK_sub_nuRow_support / 3 = apply_induce_sub + nuRow_eta_row (τ₁T(ν_1) 経由、
θG := τ₁T θT) / 4 = induce_inner_eta / 5 = dirr bricks + core 側 (τ₁S λ の pair 供給:
core.tau1S_inner_induce 系 + λ 非実) + disjoint support ⟨Ind_S(λ−λ̄), Ind_T(θ−θ̄)⟩ = 0。
供給: pins = hyp.nuGridSupply hG (sorried a-owned) / hT2・Tdata 系 / hnoV = ?
(Hypothesis-level no-typeV producer 要確認 — card_Q_eq_qp chain が使った物)。

## 2026-07-14 更新 #73 (lane b, /loop iter 36) — package 組立部材 3 本 + 供給 producer 確定

CharacterDegreeSupply に追加 (build green):
- `indK_sub_indK_support` / `indH_sub_indH_support` (sorry-free・axiom-clean) — degree-1
  K/H-induction 差の (QD)#/H# support (conj pair λ−λ̄、θT−θ̄T 用)
- `inner_induce_H_QD_eq_zero` — (13.2.e) S/T cross 直交 producer 形 (sorryAx は既存上流
  QD_sharp_centralizer_le_T 系から継承 — consumer h0 と同 profile)

**供給 producer 全確定**:
- hnoV = `S12.no_typeV_maximal_unconditional` — **axiom-clean 確認** ✓✓
- pins = hyp.nuGridSupply hG (sorried、a-owned 9096) / hvd = vd_ne_one / Tdata 系 =
  reconciled_typePData_T / chief = exists_chiefFactorData
- **hT2 = 残る唯一の gate**: honest 供給 = S16.T_isTypeP2 (TTypeII:900) だが S16 は
  CharacterDegreeSupply の下流 (layer-inversion、issue 0116 と同類)。package 組立時に
  precisely-named sorried gate `T_typeP2_for_thetaPackage`-類として立て、0116 解決 or
  producer 移設で discharge する方針。

次 iteration = package 本体 (組立設計確定済):
θ-witness (thetaWitness_of_not_caseB) → θT := Ind_K θ、r := ⟨1⟩ / conjunct 2 =
indK_sub_nuRow_support / 3 = extends_on_supported + map_sub + nuRow_eta_row (θG := τ₁T θT、
apply_induce_sub 不要 — ν_r 側は zSpan+degree-0 で直接) / 4 = induce_inner_eta / 5 =
dirr bricks (A,B) = (core.tau1S λ, core.tau1S λ̄)、(C,D) = (τ₁T θT, τ₁T θ̄T)、
conj-antisym = induce_conj + characterKernel_conj (S03:395 ✓)、非実 =
not_isReal_of_ne_trivial_irreducible_of_odd_card (S03:156 ✓)、h0 = inner_induce_H_QD_eq_zero
+ indH/indK_sub 支持。

## 2026-07-14 更新 #74 (lane b, /loop iter 37) — ✅✅✅ θ-package 本体組立完了 (#41 step 5-6 の核心)

**`tSide_theta_package_of_not_caseB_core` の monolithic sorry を実証明 (~330 行) に置換**
(build green、full build 4209 jobs 9.8s、S16 下流 green):

- 供給: hnoV = no_typeV_maximal_unconditional (axiom-clean) / hvd = vd_ne_one / pins =
  nuGridSupply (sorried a-owned) / Tdata = reconciled_typePData_T / chief = exists_chief /
  **hT2 = 新 gate `T_isTypeP2_gate`** (precisely-named sorried、honest 供給 = S16.T_isTypeP2
  の layer-inversion 0116 類、docstring 記録済)。
- θ-witness (thetaWitness_of_not_caseB) → θT := Ind_K θ、anchor row r := ⟨1⟩。
- conjunct 2 = indK_sub_nuRow_support ✓ / conjunct 3 = zSpan+degree-0 → extends_on_supported
  → map_sub → nuRow_eta_row pin (r'、δ') / conjunct 4 = tau1T_ofHonest_induce_inner_eta /
  **conjunct 5 = dirr bricks 全結線**: (A,B) = (τ₁S λ, τ₁S λ̄) core fields 経由
  (inner_induce/apply_induce_sub/mem_ZIrr ×(thetaL, thetaL.conj))、(C,D) = (τ₁T θT, τ₁T θ̄T)
  carrier 直 (extension_inner_eq/mem_ZIrr)、非実 = not_isReal_of_ne_trivial_of_odd_card'
  (度数 uq/vp ≠ 1)、conj-antisym = induce_conj + conj algebra、h0 =
  inner_induce_H_QD_eq_zero (disjoint support)。
- **File 内 sorry 残 2 のみ**: T_isTypeP2_gate (新、0116 類) + T_caseB_facts_no_lambda
  (既存 no-λ Galois 分岐、T-mirror (13.9)-(13.12) gated)。
- 実装 lessons: (i) λ̄ = lam.lambda.conj は λ を部分項に含む → rw は conj-composite
  (hlamconj) を先に。 (ii) induce_conj の向き = (Ind θ).conj = Ind (θ.conj)。
  (iii) file 内前方参照 → package chain (package + lambda_forces + T_caseB_facts_unconditional)
  を θ-witness block の後方へ python 一括移設 ([[lean-systematic-refactor-script]])。

これで #41 step 5+6 が実質完了 (τ₁T bundling ✓ + conjunct 全結線 ✓ + S/T cross 直交 ✓)。
残 = step 7 package assembly は既存 consumer chain (lambda_forces → T_caseB_facts_unconditional
→ S16) が既に配線済みのため、**T-side campaign の残 gate は refuter-T / nuGridSupply (a) /
T_isTypeP2_gate (0116) / T_caseB_facts_no_lambda の 4 named-obligation に collapse**。

## 2026-07-14 更新 #75 (HUB、監視再開時 — 0116 調査からの b 宛 findings)

0116 relayer のトリガー成立 (#74 の θ-package 組立完了) を受け hub が全容調査
(wf_746d2ebb 5-agent + hub 自前検証)。**b の次行動に直接効く 3 findings** を通知:

1. **⚠ `T_isTypeP2_gate` (CDS:1052) は「0116 類の layer-inversion」ではなく証明循環** —
   honest 供給と目していた `T_isTypeP2` (TTypeII:900) の証明自体が
   `T_side_caseB_facts → T_caseB_facts_unconditional → lambda_forces_T_caseB_core →
   tSide_theta_package_of_not_caseB_core → T_isTypeP2_gate` を経由する (hub が TTypeII 読解で
   確認)。producer 移設や import 追加では**永遠に discharge できない**。さらに gate は `hG` のみを
   取る形で、producer 側が要る hnoV (proven ✓) + hncH0C refuter を欠く分**真に強い statement**。
   **honest fix = θ-package/τ₁T machinery (dadeHypT / tau1T_ofHonest / core θ-package) の
   `hT2 : IsTypeP2 hyp.T` 入力を、ungated な type-P facts (IsTypeP via T_nonI +
   reconciled_typePData_T) へ弱める**。Coq 裏付け: PFsection13 の section context は
   `of_typeP S U defW` + `FTtype ≠ 1,5` のみで FTtype = 2 を仮定しない
   (coq/theories/PFsection13.v:80,102-103; (13.4) 本体も :866 で同 context のまま)。
   TTypeII:188-190 に b 自身が書いた cycle-hazard 注記の一般形。**この弱化の設計裁定は b**
   (エンジンは b 所有)。hub の 0116 Route T threading は弱化後の型でパラメータを流すため、
   **b の裁定が 0116 実施の前提条件 (i)** になっている — 方針だけでも早めに 2035/0116 へ。

2. **`QD_sharp_centralizer_le_T` (CountingLayer:1615) の残る本質 = (QD)^# ⊆ A₀(T) membership
   補題 (repo に未存在、genuine math)**。A₀-TI 部材は揃っている: escaping_honestTypeP2ASet_eq_empty
   (SubcoherenceInputs:863、上流 ✓) / escaping_honestTypeP2A0Set_eq_empty +
   conjClassSetIn_typePV_centralizer_le_M (HonestTypeP2A0:203/:165、TypePData-generic で上移可能)。
   hT2 param 化 (弱化後の型) + 上移は 0116 Route T step 4 で hub が実施予定。membership 補題は b。

3. **size flag: S15_CharacterDegreeSupply 2239 行 = 2000 行上限超過** — 分割要 (dir 化 or
   prefix-split、mathlib 準拠)。0116 Route T は discharge 部材を CDS でなく新 leaf に置く設計に
   したので、分割は b の裁量タイミングでよい (hub 代行可、希望あれば 2035 で flag)。

(次 iteration の参考) #74 の 4 named obligation のうち T_isTypeP2_gate は上記 1 の弱化で
obligation 自体が消える型。refuter-T / T_caseB_facts_no_lambda は従来どおり。nuGridSupply は
a-owned 9096。

## 2026-07-14 更新 #76 (lane b, /loop 再開 iter 1 — 元 #75、hub #75 との番号衝突を合流時に振り直し) — refuter-T campaign 開始: PairBoundT + StepsT 着地

#74 の 4 named-obligation のうち **refuter-T (`sSet_caseA_nineElevenRefutation_T`,
S15_TSetMemberRFamily:1017 唯一の sorry) が文書順+依存の最上流 ungated b-work** と確定
(S-side (9.11) chain は 1017 #53-#55 で全討伐済 → docstring の「S↦T dictionary 置換のみ」が
現実になった)。mirror campaign を開始、2 brick 着地 (いずれも一発 green・sorry-free):

- **`825ebdd9` S15_NineElevenPairBoundT.lean** (642 行): 世界 bricks
  (`sSet_eq_sOf_H0Cprime_T` / `uprimeSub_eq_bot_T` / `sOf_H0_uprime_eq_sSet_T` /
  `sSet_subset_inducedKernelFamily_T` / `sSet_scaledDiff_support_T`) + ψ-分解
  (`sSet_memberPsiDecomp_T` / `sSet_breakPsiDecomp_T`) + **`nineElevenPairBoundT`**
  ((9.11.1)/(5.6) pair-bound、S08 engine 発火)。
- **`ef7efb5e` S15_NineElevenStepsT.lean** (678 行): `sOf_H0Uprime_subset_sSet_T` /
  `sSet_mem_Snorm_pos_T` / **`nineElevenSTwoExtractionT`** ((9.11.1) 抽出) /
  **`sSet_sThree_coherent_dade_T`** ((9.11.6) τ₃) /
  **`mem_honestTypeP2ASet_of_mem_H_sup_cuSubOf_T`** (Coq gap-patch mirror; 型 II 辞書
  Q = T_F = M_σ(T) は hT2 経由、T′ = Q⊔V は T_deriv_eq_QV) / **`nineElevenAlphaSupportT`** /
  **`nineElevenFourNormInputsT`**。(9.11.2) TI-witness bricks は {M}-generic ゆえ直 cite。

**T-side 引数規約**: 全 mirror は `pins hvd hT2 Tdata hU hW1 hW2` を `sSet_memberRFamily_T`
と同型で thread (T の ν-grid は pins 供給; S の μ-grid は carrier 供給という非対称)。
**最終 assembly 時に refuter + `sSet_coherent_indT_caseA` の signature を widen して
pins/Tdata を thread する** (b 所有 file 内、consumer = `sSet_coherent_indT_A` は既に全引数
保持 → pass-through のみ)。

残 bricks (文書順): (5.5)/(5.2.e)-T 前提 → `nineElevenSevenEightRefutationT` (~490 行 mirror)
→ `nineElevenNormBoundT` (~330 行) → `nineElevenEqualityRefutationT` (~90 行) → assembly
(refuter sorry 置換 + dispatch 移設 or signature widen + NuRowPin 接続確認)。

## 2026-07-14 更新 #76 (lane b, /loop iter 2) — ★★ refuter-T CLOSED — T-side (9.11) chain 全体 axiom-clean

campaign 完遂 (計 5 commit、全て一発 or 微修正 green):
- `aa5ecb5a` S15_NineElevenSevenEightT.lean (657 行): (5.5)-T を NuRowPin から移設 +
  (5.2.e)-T cross_orthogonal + **`nineElevenSevenEightRefutationT`** ((9.11.7)-(9.11.8)
  budget refutation、M→S→T の 3 段 mirror 完成)。
- `7576e198` S15_CaseACoherenceT.lean (702 行): **`nineElevenNormBoundT`** +
  **`nineElevenEqualityRefutationT`** + **`sSet_caseA_nineElevenRefutation_T` 実証明**
  (monolithic sorry 置換) + dispatch 2 本を TSetMemberRFamily から移設 (caseA 側は
  pins/Tdata thread で signature widen、`sSet_coherent_indT_A` は不変 pass-through)。
  TSetMemberRFamily 1092→973 行。NuRowPin import 切替。

**AxiomsCheck 12 assert 追加 — chain 全体が [propext, Classical.choice, Quot.sound] のみ**
(sorryAx ゼロ): PairBoundT / STwoExtractionT / AlphaSupportT / FourNormInputsT /
SevenEightRefutationT / NormBoundT / EqualityRefutationT / refuter / dispatch ×2 /
**pinned carrier `sSet_coherent_indT_A_pinned`** / **`tau1T_ofHonest_nuRow_eta_row`**。
⟹ (13.4) θ-package が thread する τ₁T carrier は入力仮説 (pins 等) を除き完全 clean。
full build 4213 jobs / AxiomsCheck 4198 jobs green。

**T-side campaign 残 gate (#74 の 4 → 3)**: nuGridSupply (a、9096) / T_isTypeP2_gate
(0116 layer-inversion、hub) / **T_caseB_facts_no_lambda (b、次 frontier — no-λ T-mirror
engine (13.9)-(13.12)-on-T + q<p ltqp、9094 RULING §4)**。

⚠ file 分割 TODO (次 iteration 先頭): CountingLayer 2002 行 / CharacterDegreeSupply 2240 行が
2000 上限超過 (linter warning 発火中、いずれも本 campaign 以前からの累積)。次の追記前に
prefix-split する。
