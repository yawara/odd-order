---
id: 1046
slug: relayer-honest-typep-a0-to-s10
title: "S15_HonestTypeP2A0 (§8 の A₀(M) 論) を S10 へ移設 — 層の逆転是正"
created: 2026-07-20
---

# S15_HonestTypeP2A0 (§8 の A₀(M) 論) を S10 へ移設 — 層の逆転是正

## 背景

`OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean` (**1266 行**, namespace `OddOrder.Peterfalvi.S15`)
の内容は実質すべて **書籍 §8** — 型 `𝒫` の書籍忠実な支持集合
`A₀(M) = A(M) ∪ V^M` (`S10.typePACore0`) とその (8.13)/(8.15 claim 1) 級の性質 — であって
§13 (= repo S15「The Subgroups S and T」) の内容ではない。

同型の層の逆転は本日 1 件是正済: `sSet_finite` (§9 の事実が `S15_SAndT_Setup/HypothesisBasics`
に居た) → `S11_MaximalII_III_IV/CliffordData` へ移設 (commit 998d28af5)。

## 何が block されているか

issue 1042 の**型一様な (8.15.3) の具体化**。一般 producer
`S10.inducedNonKernelFamily_subcoherent` (commit 0f2c3c7bf、axiom-clean) は landed 済で、
`A = typePACore M` / `H = M_σ` を渡せば書籍逐語の (8.15.3) が全型で立つ。その入力 2 つが
**両方 S15 に居るため §10 から呼べない**:

| 部品 | 現在地 | 型仮定 |
|---|---|---|
| `S15.dadeSupportHypothesisData_typePACore` | `S15_SAndT_Setup/SubcoherenceInputs.lean:706` | `IsTypeP` のみ = 型一様 |
| `S15.dadeSupportHypothesisData_typePACore0` | `S15_HonestTypeP2A0.lean:538` | `IsTypeP` のみ = 型一様 |

どちらも書籍 **(8.15) claim 1** そのもの。

さらに下流の issue 1045 ((9.11) の §9 レベル化) も、同じく「§8/§9 の事実が §11/§13 の
packaging に埋まっている」ことが gate なので、本件はその先例・地ならしになる。

## やること

- [ ] `S15_HonestTypeP2A0.lean` の依存を実測 (`typePACore0_subset` / `_ne_one` / `_conj_mem` /
      `escaping_typePACore0_mem_typePACore` / `not_isConj_typePACore_typePV` ほか)。
      §8/§10/BG だけに閉じているかを確認する。
- [ ] ファイルを `OddOrder/Peterfalvi/S10_TypePSupportA0.lean` へ移し namespace を `S10` に変更。
      module 名が変わるので **importer 6 件**を更新:
      `FeitThompsonNuGrid` / `FeitThompsonCharacterData` (⚠ spine) /
      `S13_PrimeTIResidueBridge` / `S15_SAndTDefs` /
      `S15_SAndT_Setup/{SubcoherenceInputs,CoherenceEtaOrthogonality}`。
- [ ] `dadeSupportHypothesisData_typePACore` (SubcoherenceInputs 側) も同様に S10 へ。
- [ ] namespace 変更に伴う修飾の修正 (S15 内の call site は `S10.` 修飾が要る)。
- [ ] **edge ごとに `lake build` で検証**する。BFS で import cycle の消滅を見るだけでは不十分
      ([[relayer-verify-with-build-not-bfs]]: `Fintype`/`open scoped` の推移依存は import 名に
      出ず build でのみ露見)。spine file を触るので subagent に丸投げしない。
- [ ] 最後にフルビルド + AxiomsCheck + sorry 非退行を確認。

## 完了条件

- `S10.inducedNonKernelFamily_subcoherent` に `A = typePACore M` / `H = M_σ` を渡す具体化が
  §10 の file 内で書けること (issue 1042 の残件が解ける)。
- フルビルド green、AxiomsCheck OK、sorry 非退行。

## 参照

- issue 1042 ((8.15) instances; 本件が残件の gate)
- issue 1045 ((9.11) の §9 レベル化; 同型の層の逆転)
- commit 0f2c3c7bf (型一様 (8.15.3) の一般 producer)
- commit 998d28af5 (`sSet_finite` の同型移設、先例)
