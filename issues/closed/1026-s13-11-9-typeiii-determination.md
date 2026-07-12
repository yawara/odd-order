---
id: 1026
slug: s13-11-9-typeiii-determination
title: "Pf (11.9) type-III determination: 型IV排除 = U abelian (b+c 共通 root gate)"
created: 2026-07-12
---

# Pf (11.9) type-III determination — honest `IsTypeIII M` (= U abelian)

> ## ⚠️ CORRECTION (2026-07-12, subagent 検証で判明) — 本 issue の target は既に達成済
> **(11.9) type-III determination は本日 (issue 1024) 既に完成**: `S13_NonGaloisExclusion.lean`
> (1017行, 実 sorry 0) に `U_isMulCommutative_of_hypothesis` (:951) = 本 issue の目標そのものが
> sorry-free で存在。`U_isCyclic_of_hypothesis`/`isTypeIII_of_hypothesis`/`no_typeIV_maximal` も済。
> 私が当初 frontier と誤認した `S13_CoreStructure.final_typeIII_conclusions`@1687 は **live chain が
> bypass する旧 vestigial `OrthogonalityData` packaging** (retire 対象、証明しない)。
>
> **∴ 本 issue は ACHIEVED (別 session)。残る axiom-clean gate は上流の (9.11) coherence =
> issue 7001 の honest route (Coq `Ptype_core_coherence` 8-step induction の port)。frontier は
> 7001 に移る。** 下記分析 (c の reduction, nilpotent bridge) は S13_NonGaloisExclusion の実装に
> 既に反映済 (`isCyclic_of_isNilpotent_of_ker_le_commutator` = NilpotentAbelianization:139)。
> → closed。real frontier = **[[7001-sibley-target-witnesses]] (9.11) 8-step induction port**。

> lane-a α frontier (2026-07-12 再開時、live トレースで確定)。最新 HUB ruling 4465c613
> ④「bottleneck = a の 9000 §13 char body が b+c 共通 root gate、user『Aで』」の実体。
> 9000 の残 = 「§13 (11.9) typeP_Galois char body (V-abelian 用)」。

## 2026-07-12 frontier 再確定 — stale note の訂正

再開時トレースで判明 (dated note は rot、git+grep が一次情報):

- **§9 (issue 1012) は完済**: 全 S11 files が comment-strip sorry-free (`caseA_character_counts`
  含む reducible count は landed)。「§9 caseA が gated」評価は stale。
- **(11.7) crux 完済**: `S13_ElementaryAbelianKernel.lean` sorry-free (`caseA_commutator_chain`
  済)。S13_CoreStructure:1201 の「the sole remaining sorry」comment は **stale**。
- **(11.8) main orthogonality 完済 (refuter route)**: `exists_zeta_residual_not_orthogonal_H0C_of_refuter`
  (S13_Orthogonality:1022) は **body 完全 sorry-free** で (11.8.1)-(11.8.6) を assemble。
  spine 唯一 bare sorry `card_kappaHall_lt_of_isTypeIIIorIV` の残 dirty は 1025 の
  import-DAG axiom-clean bookkeeping のみ (新規数学でない、honest heir 既存)。
- **S13_CoreStructure の (11.8) 直接形は vestigial**: `orthogonality_setup` (:1401) /
  `not_orthogonal_mu0_sub_zeta` (:1420) は **consumer 0** (spine は refuter route を使う)。
  `OrthogonalityData` carrier も同様。**証明対象でない**。

## 🎯 honest target — `IsTypeIII M` (= U abelian = ¬TypeIV)

**発見**: `IsTypeIV M = Nonempty (TypeIVData M)`、`TypeIVData` は field `U_not_commutative :
¬ IsMulCommutative ↥typeP.U`。∴ `IsTypeIII M` (型判定で型 IV を排除) **= U 可換** = まさに
- **lane c** の `T_not_isTypeIV_of_isTypeP1` (S16:1768) が要る `hVcomm : IsMulCommutative V`、
- **lane b** の S14 witness `typeIIIorIV_noncyclic_le_fitting` (WitnessSylowCyclic:956) が要る
  「(9.7.b)/(11.6) の U cyclic」。

現状 scaffold: S13 `Hypothesis` の `caseB_of_97 := True` / `finalOrthogonalityFormula := fun _ => True`
は **free placeholder field** (S13_MaximalIII_IVBasic:273-275)。`final_typeIII_conclusions` (:1687)
はこの vacuous carrier を経由 ⟹ honest でない。**honest deliverable = standalone 定理**
`isTypeIII_of_hypothesis (hyp : S12.Hypothesis M) (htype : IsTypeIII M ∨ IsTypeIV M) : IsTypeIII M`
(vestigial carrier を経由しない、consumer が直接 cite 可)。

## Coq source (Pf 11.9)

`PFsection11.v:1001 FTtype34_structure`: `[/\ (a) 対称 orthogonality, (b) (p<q), &
(c) FTtype M == 3 /\ typeP_Galois MtypeP]`。型判定 (c) の Lean 版 = `IsTypeIII M`。

## 証明 skeleton (available pieces)

型 IV 排除 ⟺ U 可換。chain:
1. **(11.9.b) `q > p`**: `w2_lt_w1_of_hypothesis_H0C_unconditional` (S13_TypeDetermination:55) ✅。
2. **(9.7) dichotomy**: `chiefFactor_clifford_U_dichotomy`
   (S11_MaximalII_III_IV/InertiaLift.lean:524) — U-action on H̄ が irreducible(Galois/case b) or
   imprimitive(case a、order-p U-invariant S₀ あり)✅。
3. **非 Galois (case a) 排除**: `card_uActionHom_range_modEq_one` (`|Ū|≡1 mod q` = q∣u−1,
   S11_ImprimitiveUBound:414) + 非 Galois の `u = a ≤ p−1` 構造 ⟹ `q ≤ u−1 < p` が `p < q` に矛盾
   (Pf 11.9.c、issue 1019/1024)。⚠ 要確認: `u ≤ (p−1)^{q−1}` (`u_le_cyclotomicQuotient`) は
   弱すぎ、`u = a ≤ p−1` の非 Galois specific bound が要る (a = single block scalar order)。
4. **Galois (case b) ⟹ U 可換**: Singer で Ū = U/C cyclic。⚠ 要検討: Ū cyclic → U abelian の gap
   (C = U' (11.6) `C_eq_derivedU`、U/U' cyclic → U abelian は一般には偽だが本構造で成立するか、
   or typeP_Galois が直接 U abelian を与えるか — Coq `typeP_Galois`/`FTtype` 定義精読要)。
5. **U 可換 ⟹ ¬TypeIV**: `TypeIVData.U_not_commutative` と矛盾 ⟹ `htype` から `IsTypeIII M`。

## 下流 consumer (landing 後に unblock)

- **b**: `typeIIIorIV_noncyclic_le_fitting` (S14 WitnessSylowCyclic:956) — U cyclic → Hall 埋め込み。
- **c**: `T_not_isTypeIV_of_isTypeP1` (S16:1768) `hVcomm` — cite-ready sorried-cite endpoint 済。

## ✅ c の documented reduction (S16 TTypeII:850-883、Coq PFsection{9,11}.v 照合済 2026-07-06)

c consumer `T_not_isTypeIV_of_isTypeP1` (TTypeII:883) は packaging 完備 — 要るのは
`hVcomm : IsMulCommutative ↥hyp.base.V` (T-side U-factor) のみ。EXACT REDUCTION:

- **core = `typeP_Galois`** (`acts_irreducibly U Hbar`, PFsection9.v:323) = U が H̄=Q/Φ(Q) に
  **既約作用**。これが b (U cyclic) と c (V abelian) 双方の genuine root。
- Coq chain (`FTtype34_structure` PFsection11.v:1139-1144):
  `suffices typeP_Galois` → `typeP_Galois_P` (PFsection9.v:501-511) で **cyclic Ūbar** →
  `nilpotent V + cyclic Ūbar ⟹ cyclic V` (`cyclic_nilpotent_quo_der1_cyclic`) → `cyclic ⟹ abelian`。
- **step-4 crux 解消**: 「Ū cyclic ↛ U abelian (一般)」の gap は **U nilpotent** (Frobenius kernel,
  `Hypothesis.isNilpotent_V`) で橋渡し (nilpotent 群で abelianization cyclic ⟹ 群自身 cyclic)。
  `C_U(H̄) = U'` は (11.6) `C_eq_derivedU` + (11.7) H₀=⊥ (⟹ Ūbar = U/U' = abelianization)。
- **⚠ S-side vs T-side**: S-side U は BG 15.1(b) `typeP_hall_derived_eq_and_abelian`
  (⁅U,U⁆≤U⊓M_σ=⊥, U=(κ∪σ)'-Hall) で **abelian が free**。T-side V (IsTypeP1, κ-Hall complement,
  V⊓M_σ≠⊥) は mechanism FAIL ⟹ genuine (11.9) 要。cyclic はどちらも typeP_Galois 要。

**∴ core deliverable = `typeP_Galois` (U 既約 = dichotomy case a 排除)。cyclic/abelian は Singer +
nilpotent bridge の corollary。**

## 進め方

core = **typeP_Galois の証明 = dichotomy case a (imprimitive) 排除**。
- **step 3 (case a 排除)**: q>p (済) + `card_uActionHom_range_modEq_one` (q∣u-1) + 非 Galois bound。
  ⚠ 正確な機構 (u≤p-1 か η-grid か) を Coq `PFsection11.v:1041-1144` で確定中 (subagent 調査)。
  c note は「η-grid projection a₁₁=a₁₀=0 (§3-§11 apparatus)」と言うが、(11.8) refuter route が
  grid 済ゆえ arithmetic 排除で足りるか要確認。
- **step 4-5 (corollary)**: typeP_Galois → Singer `typeP_Galois_P` 相当で Ū cyclic → nilpotent
  bridge → U cyclic → abelian。Lean 資産 (`cyclic_nilpotent_quo_der1_cyclic` 相当・nilpotent U・
  Singer) を subagent が確認中。
- impasse なら Coq 精読 ([[verify-port-state-by-number-not-coq-name]]) or ChatGPT
  ([[feedback-ask-chatgpt-for-elided-gaps]])。

## 参照

- issue 9000 (typeP_Galois foundation、u_bound engine 完成)、1019/1024 (非 Galois bound)、
  1025 (spine axiom-clean bookkeeping = 別件)。
- `chiefFactor_clifford_U_dichotomy` / `card_uActionHom_range_modEq_one` / `u_le_cyclotomicQuotient`
  / `w2_lt_w1_of_hypothesis_H0C_unconditional` / SingerField。
- Coq `PFsection11.v:1001` `FTtype34_structure`。
