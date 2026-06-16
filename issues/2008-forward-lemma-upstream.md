---
id: 2008
slug: forward-lemma-upstream
title: "14.7 part(h): forward lemma (M'=UM_σ) を upstream 化して S14/S15 共用"
created: 2026-06-16
---

# 14.7 part(h): forward lemma (M'=UM_σ) を upstream 化して S14/S15 共用

## 背景 (2026-06-16, lane-h loop, ユーザー裁可 "Lane G と連携")

Thm 14.4 完成後、H-lane の long pole = **Thm 14.7 `typeP_duality`** (`S14_TypePCounting`)。その
**part(h)** = `IsComplement' (M'.subgroupOf M) (K.subgroupOf M)` + `Coprime |M'| |K|` は §16-independent で
**`S15_MF:785` が `⟨hcompl, hcop, _⟩` で直接 consume**。

part(h) の証明には **forward lemma**「`K≠⊥ → derivedInG M = U ⊔ Msigma M ∧ U abelian`」(M'=UM_σ) が要る。
これは現状 **`S15_MF.lean:683` に存在するが本体が `sorry`**(未証明)。さらに part(h) は K cyclic + M=KUM_σ も要す。

### 問題 (cross-lane)
- S15 は S14 を import するので、forward lemma chain を **S14 に同名 port すると重複定義エラー**。
- forward lemma の核 helper のうち `commutator_commutator_le_of_quotient_commutator_commutative`(S15:518) /
  `isMulCommutative_commutator_of_mulEquiv`(S15:543) は **abstract group lemma**(S15-local, FT 非依存)。
  `derivedDerived_le_Msigma`(S15:556, M''≤M_σ) は §12-based・**sorry-free**。
- ⟹ 14.7 を S14 で完成するには forward lemma chain が **S14 から見える upstream** に要る。

## やること
- [ ] **abstract helper 2 本**(518/543, FT 非依存)を upstream へ: `OddOrder/GroupTheory/` or `OddOrder/Mathlib/`
      (S14・S15 両 import 先)。S15 側は dedupe して cite に切替 (Lane G)。
- [ ] **`derivedDerived_le_Msigma`** を §12/§13 もしくは S14 の早い位置へ(両者 import 可)。
- [ ] **forward lemma の M'=UM_σ ∧ U abelian conjunct を証明**(現 S15:683 sorry の第1連言; §12-based,
      §16-independent)。→ S14 の 14.7 part(h) と S15 の Cor 15.6/Lem 15.1 が共に cite。
- [ ] S14 で **14.7 part(h)** (M' complements K + coprime) を証明。
- [ ] (covering(∃!) = §16 counting は別 gate = Lane G §16, 本 issue 対象外)。

## 完了条件
- forward lemma chain が単一 upstream に存在(重複なし)、S14 の 14.7 part(h) が sorry-free、S15:785 が
  un-taint(sorried typeP_duality 非依存化 or typeP_duality part(h) sorry-free)。

## 参照
- `notes/bg/s14_typeP_counting.md`「§14 frontier 確定」/ `OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF.lean:518,543,556,683,785`
- `OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting.lean:3224` (typeP_duality)
- 暫定: S14 側は helper を inline/別名で先行証明可(hub が後で upstream 統合)。
