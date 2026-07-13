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
