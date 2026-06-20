---
id: 1005
slug: typep-ambient-v-ti
title: "Peterfalvi (4.6.b): ambient TI of V=W-(W1cupW2) for type-P W"
created: 2026-06-20
---

# Peterfalvi (4.6.b): ambient TI of V=W−(W₁∪W₂) for type-P W

## 背景

§10→§5 ω-grid bridge `typePData_toTICyclicHypothesis`
(`OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean`) を組み立てる際、`TICyclicHypothesis G`
の 17 フィールドのうち 16 は `TypePData` から実証明で供給できたが、最後の
`V_ti : IsTISubset (typePV M data) data.W` だけは `TypePData` のフィールドから導けない。

理由 (2026-06-20 lane B 調査、正本 `notes/peterfalvi/s12_s10_character_bridge.md` §3b):

- `IsTISubset A L := ∀ g, (∃ a ∈ A, g·a·g⁻¹ ∈ A) → g ∈ L` (`GroupTheory/TISubset.lean:72`)。
- `TypePData.normalizer_V` (∀ nonempty X⊆V, N_G(X)=W) は **strict に弱い**: 単集合 {a} で
  C_G(a)=W は出るが、a∈V・b=gag⁻¹∈V から C_G(b)=gC_G(a)g⁻¹ ⟹ gWg⁻¹=W ⟹ g∈N_G(W) までで、
  `g∈W` には `N_G(W)=W` が別途要る (repo に typeP 用の self-normalizing 事実は無い)。
- §6 の `isTISubset_sup_sdiff` (`S06_DadeIsometryCertain.lean:244`) は TI を **L 内**で証明するが、
  その機構は `L = K ⋊ W` (K ⊴ L, L/K abelian ⟹ [g,x]∈K⊓W₁=⊥) に依拠する。ambient `G` には
  `W` の normal complement が無く、この証明は転送できない。
- ∴ ambient TI は Peterfalvi (4.6.b) = (4.3.a) の `G`-版で、**独立した定理**。

既存 API でも同じ扱い: §5 `TICyclicHypothesis.mapOfInjective` (`S05_TICyclic.lean:97`, 引数
`hVti`) と §6 `toTICyclicHypothesisOfV` (`S06:375`, 引数 `hti`) はいずれも ambient TI を
**明示パラメータ**で取る。よって bridge も `hVti` をパラメータ化した (honest factoring;
scaffold ではない — V_ti は具体的 TI 事実)。

## やること

- [ ] Peterfalvi (4.6.b) / BG の対応する ambient-TI 定理を特定し、type-P の `W = W₁×W₂` が
      `G` の TI 部分群であること (従って `V = W−(W₁∪W₂)` が `IsTISubset V W`) を証明する。
- [ ] それを `typePData_V_ti (data : TypePData M) (hG : IsMinimalSimpleOdd G) :
      IsTISubset (typePV M data) data.W` 等として供給し、`typePData_toTICyclicHypothesis` の
      `hVti` 引数を discharge (または bridge から引数を除去) する。
- [ ] 上流 BG §1 σ-decomposition / TI-Hall 理論に gate されるか判定 (gate される場合は obligation を
      明記して別 issue へ)。

## 完了条件

`typePData_toTICyclicHypothesis` の `hVti` パラメータが `IsMinimalSimpleOdd G` (等の既存仮説) から
導出され、§10 consumer が ambient-TI を外部入力せずに ω-grid を使えるようになる。

## 参照

- `OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean` — `typePData_toTICyclicHypothesis` (bridge),
  `typePData_disjoint_W1_W2` / `typePData_coprime_card_W1_W2` / `typePData_W_card_odd` (prereqs)
- `OddOrder/Peterfalvi/S05_TICyclic.lean:97` — `mapOfInjective` (`hVti` 先例)
- `OddOrder/Peterfalvi/S06_DadeIsometryCertain.lean:244,375` — `isTISubset_sup_sdiff`,
  `toTICyclicHypothesisOfV` (`hti` 先例)
- `OddOrder/GroupTheory/TISubset.lean:72` — `IsTISubset` 定義
- `notes/peterfalvi/s12_s10_character_bridge.md` §3b — gap 分析 (正本)
