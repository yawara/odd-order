---
id: 1026
slug: s13-11-9-typeiii-determination
title: "Pf (11.9) type-III determination: 型IV排除 = U abelian (b+c 共通 root gate)"
created: 2026-07-12
---

# Pf (11.9) type-III determination — honest `IsTypeIII M` (= U abelian)

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

## 進め方

deep multi-iteration char body。上流順で step 3 (非 Galois 排除、算術) → step 4 (Galois→abelian) →
assembly。step 4 の Ū-cyclic↔U-abelian gap が impasse なら Coq `PFsection11.v`/`FTsection*` 精読
([[verify-port-state-by-number-not-coq-name]]) or ChatGPT ([[feedback-ask-chatgpt-for-elided-gaps]])。

## 参照

- issue 9000 (typeP_Galois foundation、u_bound engine 完成)、1019/1024 (非 Galois bound)、
  1025 (spine axiom-clean bookkeeping = 別件)。
- `chiefFactor_clifford_U_dichotomy` / `card_uActionHom_range_modEq_one` / `u_le_cyclotomicQuotient`
  / `w2_lt_w1_of_hypothesis_H0C_unconditional` / SingerField。
- Coq `PFsection11.v:1001` `FTtype34_structure`。
