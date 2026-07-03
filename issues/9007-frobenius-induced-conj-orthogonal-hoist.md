---
id: 9007
slug: frobenius-induced-conj-orthogonal-hoist
title: "shared: hoist inner_induce_conj_eq_zero_of_frobenius_of_odd (S14→RepresentationTheory)"
created: 2026-07-04
kind: shared-infra
lanes: [a, b]
---

# shared: Frobenius 誘導指標の共役直交性を共有 leaf へ

## 背景

`inner_induce_conj_eq_zero_of_frobenius_of_odd` (odd Frobenius group Γ, kernel H, θ∈Irr H 非自明 ⟹
`⟨Ind_H^Γ θ, Ind_H^Γ θ̄⟩ = 0`) は現在 **lane-b の `Peterfalvi/S14_MaximalI.lean:5652`** にローカル定義。
純 rep-theory (§14 固有内容ゼロ) で、依存 (`isIrreducibleCharacter_induce_of_frobeniusGroup`,
`not_isReal_of_ne_trivial_of_odd_card'`, `ClassFunction.induce_conj`, `inner_induce_eq_inner_restrict`,
`irreducibleCharacter_inner_eq_ite`) は全て S14 の上流 (`GroupTheory/RepresentationTheory/*` +
`Isaacs/Ch06`)。**lane-a の (7.8.b) `zetaNuRhoNormSqGeOfDade` 適用 (issue 0044、hzeta0nu 経由) が
これを要する**が、S14 は S09 の下流ゆえ import 不可。claim-before-build スキャンで共有版は無し (2026-07-04)。

## やること

**⚠ 訂正 (2026-07-04)**: 共有 `RepresentationTheory/` ホストは **不可**と判明。`inner_induce_conj_...` は
`ClassFunction.induce_conj` に依存し、それは `OddOrder/Peterfalvi/S08_CoherenceCorePart1.lean:64` 定義
(依存 `induceTerm_conjStar` も S08)。ゆえ shared RepresentationTheory (S08 上流) からは到達不可。
真の共有化には `induce_conj`/`induceTerm_conjStar`/`induceSum_conj` を `InducedCharacter.lean` へ先行
relocate する別refactor が要 (deps は全て InducedCharacter/IsReal に有り、clean だが別作業; 低優先で defer)。

- [x] lane-a: 新 lane-a leaf `OddOrder/Peterfalvi/S09_FrobeniusEstimate.lean` に
  `inner_induce_conj_eq_zero_of_frobenius_of_odd` をホスト (S14 の証明を移送、S08 の induce_conj に到達可)。
  imports = `S09_FrobeniusHypothesis78` + `BrauerPermutationUnconditional`。namespace = `OddOrder.RepresentationTheory`
  (一般 rep-theory fact ゆえ; ファイルは Peterfalvi 下だが fact は汎用)。
- [ ] **defer (低優先)**: `induce_conj` chain を `InducedCharacter.lean` へ relocate → その後
  `inner_induce_conj_...` を真の shared RepresentationTheory leaf へ移動 → S09/S14 両方が cite (完全 dedup)。
  現状は S09 (lane-a) と S14 (lane-b) に 2 コピー併存 (証明同一、害小)。lane-b は必要なら S09 版を cite 可
  (S14 は S09_CertificateDischarge を import 済ゆえ S09 名前空間に到達可)。

## 完了条件

- lane-a: `S09_FrobeniusEstimate.lean` が build green、(7.8.b) hzeta0nu が cite。✅ 相当
- (defer) 完全 dedup: induce_conj relocate + shared 移動 + S14 cite 切替。

## 参照

- issue 0044 (card_G0_lower_bound、consumer)
- `Peterfalvi/S14_MaximalI.lean:5652` (移送元)
- `GroupTheory/RepresentationTheory/InducedIrreducible.lean:465`
  (`isIrreducibleCharacter_induce_of_frobeniusGroup`)
