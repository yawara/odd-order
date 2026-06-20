---
id: 1006
slug: typep-w1-hall
title: "Peterfalvi (4.2.a): W1 Hall in M (card_coprime) for §10->§6 bridge"
created: 2026-06-20
---

# Peterfalvi (4.2.a): W₁ Hall in M (`card_coprime`) — §10→§6 bridge obligation

## 背景

§10→§6 bridge `typePData_toS06Hypothesis` / `Hypothesis.toCertainTypeHypothesis`
(`OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean`) は `S06.Hypothesis ↥M` (Peterfalvi (4.2)) を
`TypePData M` から構成する。11 構造フィールド中 10 は `TypePData` から実証明で供給したが、
`card_coprime : Nat.Coprime (Nat.card K) (Nat.card W1)` (K = M' = derivedInG M) だけは導けない。

これは Peterfalvi (4.2.a)「W₁ は M の **Hall** 部分群」= `gcd(|M'|, |W₁|) = 1` の条件。
`TypePData.M_complement` は M = M' ⋊ W₁ (W₁ は M' の complement) を与えるが、
**complement は一般に Hall ではない** (例: C₂×C₂ で C₂ は C₂ の complement だが非 coprime)。
∴ `card_coprime` は `TypePData M` 単独からは導出不可ゆえ、bridge は入力 `hHall :
Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1)` でパラメータ化した
(honest factoring; issue 1005 の hVti と同じ扱い)。

## やること

- [ ] `hHall` を discharge する補題を証明する。攻略 = κ-Hall K 経由
      (`OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePComplement.lean:77-83` に precedent):
  - `typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hK` で M = M' ⋊ K (κ-Hall K) を取り、
  - `hidx : (K.subgroupOf M).index = |M'|` (complement の index = |M'|) と
    `hK.coprime_index` (Hall ⟹ coprime index) から `Coprime |K| |M'|` を得る。
  - `|W₁| = [M:M'] = |K|` (`TypePData.card_W1_eq_derived_index` + κ-Hall も complement) ゆえ
    `Coprime |M'| |W₁| = Coprime |M'| |K|`。
- [ ] 要 input: `hG : IsMinimalSimpleOdd G`, `hM : M ∈ maximalSubgroups G`, `hP : IsTypeP M`,
      cyclic κ-Hall K の存在。κ-Hall の存在補題 (type-P maximal が cyclic κ-Hall を持つ) を特定/構成。
- [ ] それを `typePData_W1_hall_coprime (hG) (hM) (data) : Nat.Coprime ...` 等で供給し、
      §10 consumer が `hHall` を外部入力せず bridge を使えるようにする。

## 完了条件

`Hypothesis.toCertainTypeHypothesis` の `hHall` パラメータが `IsMinimalSimpleOdd G` 等の既存仮説から
導出され、§10 consumer が unconditional に §6 certain-type 機構 ((10.2)/(10.3)/μ-grid) を使える。

## 参照

- `OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean` — `typePData_toS06Hypothesis` (bridge),
  `Hypothesis.toCertainTypeHypothesis`
- `OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePComplement.lean:77-83` — κ-Hall coprimality precedent
  (`Coprime |K| |M'|` via `typeP_derivedInG_isComplement_kappaHall` + `hK.coprime_index`)
- `OddOrder/GroupTheory/MaximalSubgroupType.lean` — `TypePData`,
  `TypePData.card_W1_eq_derived_index` (|W₁| = [M:M'])
- `OddOrder/Peterfalvi/S06_DadeIsometryCertain.lean:67` — `S06.Hypothesis` (4.2), `card_coprime` field
- `notes/peterfalvi/s12_s10_character_bridge.md` §6 — bridge field 対応表 + リスク
- 関連 issue: 1005 (hVti / ambient TI, 同型の obligation)

## 2026-06-20 調査: lane-f κ-Hall cyclicity に gate

上記「κ-Hall 経由」プランは **cyclic κ-Hall K の存在**を要するが、これが lane-f BG §14 に gate と判明:
- `typeP_derivedInG_isComplement_kappaHall` / `card_kappaHall_eq_derived_index` はいずれも
  `[IsCyclic ↥K]` を仮説に取る (S14_TypePCounting:8011 / S16_PairIntersection:191)。
- 単一 type-P maximal M の κ-Hall K の cyclicity は **`theoremA_maximal_structure` (S16_MainResults:144) が
  `IsCyclic ↥K` を主張するが SORRY** (line 164)。実証明は `typeP_duality` 経由 (S15_MF:1750 の `hconj2`)
  で、これは **partner Mstar との pairing を要する**深い §14 duality。
- ∴ `Coprime |M'| |W₁|` (= M' が M の Hall) は `TypePData` 単独・lane-b 単独では出ず、lane-f の
  κ-Hall cyclicity (theoremA or typeP_duality) 着地待ち。
- 代替: `typeP_structure` (Prop 14.2, sorry-free) から「M' = U·M_σ は κ(M)'-Hall」を抽出できれば
  prime-set disjointness (`kappa_subset_sigmaCompl`) で coprimality が出る可能性 — 要 lane-f 構造抽出。

**∴ issue 1006 は lane-f BG §14 待ち** (cross-lane gate)。lane-b 単独では closeable でない。
