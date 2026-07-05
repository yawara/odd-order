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
