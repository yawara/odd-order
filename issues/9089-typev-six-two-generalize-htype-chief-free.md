---
id: 9089
slug: typev-six-two-generalize-htype-chief-free
title: "(6.5) type-V h56: generalize sixTwoDecompositionData chain htype/chief-free (unused)"
created: 2026-07-12
---

# 9089 — CLAIM (lane a): htype/chief-free 一般化で型V h56 開通

> shared-infra claim (claim-before-build). 対象は既存 char-theory lemma の**証明で未使用の仮説
> 削除**による一般化 (新規 infra でなく refactor)。lane a の (6.5) type-V gates (issue 1027) の
> 唯一の残 frontier = h56-for-type-V を開通させる。

## 発見 (2026-07-12 lane-a session、検証済)

型V排除 (Peterfalvi 10.10) の Coq 証明 (`PFsection10.v:885 FTtype5_exclusion_main`) は
`non_coherent_chief` (6.5) を `calS = seqIndD H M H 1` (H=M'=M_F) に**直接**適用し、
per-member reducibility 解析も μ-column 分解も**一切しない** (`coherent_seqIndD_bound` /
`extend_coherent` で degree のみで回る)。型V case(c) の reducible member =
extraspecial p³ の degree-p 指標 = **μ_j columns (型III/IV と同一の muGrid 構造)**。

Lean 側の型III/IV h56 chain (`S13_SixTwoBridge`) は per-member `CharacterPsiDecomposition` route
で、reducible break/member を μ-column で discharge する。その htype/chief 依存を精査した結果:

- **`reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` (S12_HcBound:578) の証明本体
  (587–637) は `htype`/`hnt`/`chief` を一度も参照しない** — `toCertainTypeHypothesis` (任意の
  `Hypothesis M` で動く) 経由。signature 宣言のみ。p³ 仮定も不要。
- `sixTwoDecompositionData_of_reducible_break` (S13:336) / `sixTwoMemberDatum_of_reducible_member`
  (S13:630) / `sixTwoDecompositionData` (S13:814) の htype/chief は**上記 base lemma の呼び出しに
  のみ**流れ込む (`columnImageFamilyCohFree` は htype/chief 不要)。
- `exists_source_index_le_two_psi_of_ne_top` (S13:274) は既に htype/chief-free (hdatum を引数で取り、
  anchor は general な `hyp.exists_anchor`)。

⟹ base lemma の htype/chief を削除すると chain 全体が cascade で htype/chief-free になり、
型V (= TypePData with U=⊥) の `Hypothesis M` に直接適用できる。

## やること (bottom-up、build-driven)

- [x] 1. `reducible_mem_inducedKernelFamily_eq_muGrid_columnSum`: `htype hnt chief` 削除。✅ (build green)
- [x] 2. call sites (7): S13:378/529, S13:669, S12_Section9Counts:948,
      S11_NineElevenAlphaBound:196/439, S13_MaximalIII_IV:524 — 3 引数 drop。✅
- [x] 3. `sixTwoDecompositionData_of_reducible_break` / `sixTwoMemberDatum_of_reducible_member` /
      `sixTwoDecompositionData`: `htype hnt chief` 削除。✅ (`exists_source_of_coherence_dichotomy` /
      `sixTwoBound` は型III/IV 専用ゆえ signature 維持、内部 `sixTwoDecompositionData` 呼び出しのみ drop)。
- [x] 4. consumers: S13 内部 (914/870/873), S11_NineElevenCaseA:585 — drop。✅ **full build green (4178 jobs)**。
- [ ] 5. 型V h56 wiring: `six_three_of_six_two_oracle` を (L,K,H,H₁,M)=(M,M',M',M'',⊥) に
      instantiate (template = `S13_Lemmas113To115.coherent_S_of_coherent_SH0C` (11.3))、h56 は
      generalized `exists_source_index_le_two_psi_of_ne_top` + `sixTwoDecompositionData`
      (params = `hyp.exists_charParameters_full hG`)。hcoh = S(M'') coherent
      (`uniform_degree_coherence_of_subcoherent`、全 member linear-induced degree w₁)。対偶で
      `typeV_sixFiveA_bound`。→ (6.5.b)/(6.5.c) (S08_PGroupReduction infra、ただし quotient-Frobenius 版要検討)。

## 完了条件

`typeV_sixFiveA_bound` / `typeV_sixFiveB_pGroup` / `typeV_sixFiveC_not_dvd`
(S12_Noncoherence.lean) の 3 sorry が消え、`typeV_forces_coherence_v2` が honest 完成。
build-green (S12_Noncoherence 及び影響 file)。

## step 5 実装詳細 (次 iteration 用、全 lemma 名確定済)

**commit 6ce607ce で step 1-4 完了 (generalization、full build green)。** 残 = 型V h56 wiring。
`typeV_sixFiveA_bound` の証明構造 (template = `coherent_S_of_coherent_SH0C` S13_Lemmas113To115:35):

```
by_contra hgt; rw [not_le] at hgt   -- 4w₁²+1 < |Ab(K)|, K := (derivedInG M).subgroupOf M
apply hnc
obtain ⟨params, hmu, -, hζS, hζ1, hζne, hδpm, hδj⟩ := hyp.exists_charParameters_full hG
-- Sset = SOf ⊥:  inducedFamily_eq_inducedKernelFamily_bot (S12)
-- SOf := fun X => S08.inducedKernelFamily K X
-- instances: TypeVData.isNilpotent_derivedInG_subgroupOf (要 dV), IsSolvable, Invertible
-- hcoh: SOf ⁅K,K⁆ coherent   ← ★唯一の hard sub-piece (下記)
-- case ⁅K,K⁆ = ⊥ (M' abelian): rwa [hcomm] at hcoh   (SOf ⊥ = 𝒮 coherent、hnc 矛盾)
-- else: six_three_of_six_two_oracle (L:=M) (K:=K) (H:=K) (M:=⊥) (H₁:=⁅K,K⁆)
--   hHnorm, bot_le, hH₁H (⁅K,K⁆<K: |Ab|>1), hHK=le_rfl, hyp.tau, hyp.A0, SOf, h56, hcoh, hbound
-- hbound: commutator_subgroupOf_self ▸ hgt  (Nat.card(↥K⧸⁅K,K⁆.subgroupOf K)=|Ab(K)|),
--   K.index = w₁ (typeP.card_W1_eq_derived_index)
-- h56 (∀ A B): mirror S13_Lemmas:105-134 だが generalized 版:
--   hyp.exists_source_index_le_two_psi_of_ne_top hG hAne hBne
--     (hyp.sixTwoDecompositionData hG hmu hδpm hδj hζS hζ1 A B) hAcoh' hBncoh'
--   (htype/chief 不要! hAne/hBne: A,B ≤ ⁅K,K⁆ < K ⟹ subgroupOf K ≠ ⊤)
```

### ★ hcoh の hard sub-piece = irreducibility bridge

`SOf ⁅K,K⁆ = inducedKernelFamily K ⁅K,K⁆` の全 member `Ind_K θ` (θ trivial on ⁅K,K⁆ = θ linear,
θ≠1) が **irreducible** であることを示せば、`SHC_isCoherent` (S12_Prop109:687、degree-w₁ irreducible
族の coherence) に `inducedKernelFamily K ⁅K,K⁆ = SHCSet` で rewrite して hcoh 完成 (⊇ は degree のみで
easy: degree-w₁ ⟹ θ(1)=1 ⟹ θ trivial on ⁅K,K⁆)。

**bridge = 「θ nonprincipal linear (trivial on ⁅K,K⁆=M'') ⟹ Ind_K θ irreducible」**。数学的本質 =
Frobenius M/M'' (kernel M'/M'') の fpf action ⟹ θ は W₁-fixed でない ⟹ inertia=K ⟹ Ind irreducible。
Lean 経路候補:
- `induce_isIrreducible_of_forall_chiRestrict_ne` (S06:931): `∀ χ₂, h.chiRestrict χ₂ ≠ θ` ⟹ Ind θ irr
  (`h := (hyp.toCertainTypeHypothesis hG hG.odd).toHypothesis`, `h.K = K`)。
- 要: 「chiRestrict χ₂ (= restrict_K μ_{0}(χ₂), W₁-fixed) ≠ θ (θ trivial on ⁅K,K⁆)」。
  W₂.subgroupOf M ≤ ⁅K,K⁆ = `TypePData.W2_subgroupOf_le_commutator` (S12_TypeVSibley:175)。
  chiRestrict 1 = trivial (`chiRestrict_one_eq_trivial`), θ≠1 ⟹ χ₂=1 排除。
  **未解決の gap**: χ₂≠1 で「chiRestrict χ₂ が W₂ 上 nontrivial (∴ ⁅K,K⁆ 上 nontrivial ∴ ≠θ)」を
  与える certain-type lemma が直接には無い。S06 の chiRestrict は W₁-fixed-point 特徴付け
  (`chiRestrict_isFixedPt`/`inertia_eq_K_of_forall_chiRestrict_ne`) 中心で W₂-restriction 性質が薄い。
  → 次 iteration: (i) S06 に「chiRestrict χ₂ の W₂ 制限 = χ₂」補題を足すか、(ii) 型V の M/M'' Frobenius を
  `IsFrobeniusGroup` として取り出し Frobenius-kernel-induce-irreducible (cf. `S08_YsetConjugation:447
  isIrreducibleCharacter_induce_of_degree_one` の Sibley 版、`normOneFrobeniusKernel_induce_isIrreducible`
  BG/AppC:350) を非Sibley で適用。[[feedback-ask-chatgpt-for-elided-gaps]] 候補。

### (6.5.b)/(6.5.c)
(6.5.a) 完成後: (6.5.b) 非可換 = ¬coherent+hcoh から M''≠⊥ (M' abelian なら 𝒮 uniform→coherent 矛盾)、
p-group = (6.5.a)+Frobenius (`isPGroup_of_isFrobeniusGroup_of_card_le`、ただし型V は quotient-Frobenius
M/M'' ゆえ `S08_PGroupReduction` の full-Frobenius 版でなく quotient 版の導出要検討)、p=w₂ = W₂≤M''。
(6.5.c) = `six_five_c_arith` (S08_PGroupReduction:149) 対偶。

## territory / coordination

対象 file (S11/S12/S13 char-theory) は型III/IV coherence (lane b 隣接) を含むが、変更は
**証明で未使用の仮説削除** (build が安全性を保証) ゆえ semantics 不変。lane a が上流 shared infra に
降りて型V を開通させる (CLAUDE.md policy (A))。合流時 conflict は mechanical。

## 参照

1027 (type-V gates handoff), 2022 (six_two/(5.2.d) done), 1021 (typeV_forces_coherence)。
Coq: PFsection10.v:885 (FTtype5_exclusion_main), PFsection6.v:176 (non_coherent_chief)。
