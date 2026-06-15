---
id: 8004
slug: cor156-wiring
title: "BG Cor 15.6 typeP_kstar_in_mf: 全 conjunct 配線 (engine 済)"
created: 2026-06-14
---

# BG Cor 15.6 typeP_kstar_in_mf: 全 conjunct 配線 (engine 済)

## 背景

Lane G (bg-s13) が §15 endpoint `typeP_kstar_in_mf` (Cor 15.6, S15_MF.lean) を証明するための
配線 issue。conjunct 5 のエンジン `fittingInAmbient_cyclic_imp_derivedDerived_eq_bot`
(F(M) cyclic ⟹ M''=⊥) は **landing 済** (`dd10d84d`, §14 非依存・axiom-clean)。
全 friction を精査した結果、残るのは 2 つの sorry-neutral 強化 + conjunct 4 の Lemma 6.3 適用のみ。
詳細 = `notes/bg/s15_16_audit.md` section 9。mmd L4174。

監査 (section 7) の方針は「§14 landing 後が望ましい (fragile 依存回避)」。本 issue は §14 landing 後
または専用 focused session 用の **実行可能な完全 cite map**。

## やること

- [ ] **(i) Lemma 15.1 強化**: `typeP_auxiliary_structure` (S15_MF) の結論に
  `(K ≠ ⊥ → Subgroup.IsComplement' (derivedInG M) K)` を sorry-neutral 追加。
  mmd 15.1(a)「UM_σ⊴M=KUM_σ」+ (b)「K≠1⟹M'=UM_σ」⟹ M=K·M'、|K| κ-数/|M'| κ'-数 ⟹ K∩M'=1。
  これで §14 Thm 14.7(h) (未露出) を迂回し M=KM' を §14 非依存に供給。
- [ ] **(ii) Cor 15.5 強化**: `fitting_decomposition` (S15_MF) の結論に
  `(IsCyclic ↥(MF M) → IsCyclic ↥(fittingInAmbient M))` を sorry-neutral 追加 (mmd の
  「M_F cyclic ⟹ F(M) cyclic by Cor 15.5」)。
- [ ] **(iii) conjunct 4 補題**: type-P M で `Kstar ≤ derivedInG (derivedInG M)`。
  Lemma 6.3 第2結論 `centralizer_inf_le_derivedInG_of_isComplement'`
  (S06_Additional:396, **proved**) を ↥M 内で適用: H=M'.subgroupOf M, K=K.subgroupOf M,
  coprime(|M'|,|K|) (K の κ-Hall 性 + IsComplement' から [M:K]=|M'|), 出力を ambient へ移送。
  K*=C_{M_σ}(K) ⊆ C(K)⊓M' (M_σ⊆M' = `Msigma_le_derived`) ⊆ M''。
- [ ] **(iv) 組立**: 5 conjunct を assemble:
  - `Kstar≠⊥` ← `S14.typeP_structure ... hU` conjunct 3 (U = `Ch03.hall_E_exists (G:=↥M)
    ((kappa M ∪ sigma M)ᶜ)` を `map M.subtype`; pattern = `exists_hallAlphaSubgroup_isHallInG`)。
  - `IsCyclic Kstar` ← `S14.typeP_duality` の `IsCyclic(K⊔Kstar)` + `isCyclic_of_surjective`
    (Kstar ≅ Kstar.subgroupOf(K⊔Kstar) ≤ cyclic)。
  - `Kstar≤MF` ← `by_cases MF M = Msigma M`: eq は `hKstar ▸ inf_le_left`; ne は
    `mf_ne_msigma_typeP1_structure` の露出済 `Kstar≤MF`。
  - `Kstar≤M''` ← (iii)。
  - `¬IsCyclic MF` ← 反証: `IsCyclic(MF M)` → (ii) で F(M) cyclic →
    `fittingInAmbient_cyclic_imp_derivedDerived_eq_bot` で M''=⊥ → (iii) で Kstar≤M''=⊥ →
    `Kstar=⊥`、conjunct 1 と矛盾。

## 完了条件

- `OddOrder.BG.Ch4.S15.typeP_kstar_in_mf` の `sorry` が消える (S15_MF sorry 9→8)。
- `lake build OddOrder` green + AxiomsCheck OK (axiom-clean; cite 先 sorried は許容)。

## 参照

- `notes/bg/s15_16_audit.md` section 8-9 (cite map 完全版)。
- engine commit `dd10d84d` (Aut-abelian core)。
- mmd `references/bg/local-analysis.mmd` L4174 (Cor 15.6 本文+証明)。
- Lemma 6.3: `OddOrder/BG/Ch1_Preliminary/S06_Additional.lean:396`
  (`centralizer_inf_le_derivedInG_of_isComplement'`, proved)。
- §14 露出: `S14_TypePCounting.lean` `typeP_structure` (349) / `typeP_duality` (429)。
- ⚠ Thm 14.7(h) (M=KM') は §14 未露出 → (i) で迂回。Lane H が露出すれば (i) 不要。
