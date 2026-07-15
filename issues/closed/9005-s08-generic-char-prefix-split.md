---
id: 9005
slug: s08-generic-char-prefix-split
title: "S08_CaseBCoherence2 の generic char 3 補題を GroupTheory shared leaf へ prefix-split (6.11 consumer)"
created: 2026-07-03
---

# S08_CaseBCoherence2 の generic char 3 補題を GroupTheory shared leaf へ prefix-split (6.11 consumer)

> **起票**: lane c (2026-07-03、issue 9002 (G3)=Isaacs 6.11 着手時)。**owner = hub** (prefix-split は
> hub 実施が規約; lane c は lane b 所有の S08 を編集しない)。lane c は relocate を待たずに
> 6.11 の relocate-非依存部分を進める (下記「lane c の並行対応」)。

## 背景

`OddOrder/Peterfalvi/S08_CaseBCoherence2.lean` (lane b 所有, 2187 行) の中腹に **完全 generic
(`{M : Type*} [Group M]` 抽象、Pf 非依存) な char 補題 3 本**が埋まっている:

- `induce_eq_sum_inner_restrict_smul` (L414 付近) — Ind の既約分解 `Ind φ = Σ ⟨Res χ,φ⟩ • χ`。
- `inner_compHom_of_mulEquiv` (L429) — 群同型に沿った pullback で inner 不変。
- `induce_induce_subgroupOf` (L454) — **induction in stages** `Ind_H^M (Ind_{K≤H} ψ) = Ind_K^M ψ`。

これらは lane c の **Isaacs 6.11 (Clifford correspondence: `Ind_{I(θ)}^G ψ` の既約性)** = issue 9002
(G3) の必須部品であり、6.11 は shared leaf (`GroupTheory/RepresentationTheory/**`) に置くため、
**GroupTheory/** → Peterfalvi/** の import 逆流は不可** → 3 補題の shared 化が必要。

再構築は禁止 ([[verify-port-state-by-number-not-coq-name]] claim-before-build) ゆえ、hub による
prefix-split (凍結済 generic 宣言を上流 GroupTheory leaf へ移し、S08 が import する) を依頼する。

## やること (hub)

- [x] 上記 3 補題を新 shared leaf `OddOrder/GroupTheory/RepresentationTheory/InducedTransport.lean`
      へ移動 (hub, 2026-07-03)。⚠ 2 適応: (1) namespace は `OddOrder.Peterfalvi.S08` →
      **`OddOrder.RepresentationTheory`** に変更 (S08 は `open OddOrder.RepresentationTheory` 済ゆえ
      参照は不変; generic 宣言の正しい所属)。(2) lemma 1 の Fourier 展開は Peterfalvi 側
      `classFunction_eq_sum_inner_smul` (S08_CoherenceCorePart1、import 逆流不可) の代わりに
      共有側の同内容 `sum_inner_irreducibleCharacter_smul` (CharacterCompleteness) を cite。
      `Fintype (IrreducibleCharacter M)` instance のため ColumnOrthogonality も import。
- [x] `S08_CaseBCoherence2.lean` は新 leaf を import (宣言削除 + 移設注記 + import 1 行)。
      Peterfalvi 文脈の docstring ((6.8.2.3) 対応) は S08 側に移設注記として温存。
- [x] `OddOrder.lean` root に新 leaf を追加。full build green (3903 jobs) + AxiomsCheck OK。
- [ ] **重複検出の付記 (残タスク: split 済み後の統合判定)**: `S11_MaximalII_III_IV.lean` に `inner_compHom_of_bijective` (current L11415) /
      `inner_compHom_mulEquiv` (current L11860) — S08 の `inner_compHom_of_mulEquiv` と同内容の可能性。
      split 後に S11 側を新 leaf cite に置換できるか lane a/hub で判定 (できれば統合)。S11 は lane a 所有のため、
      lane d は fresh carve-out なしに Lean 側の置換へ入らない。
      2026-07-06 D read-only audit: both S11 declarations still exist, so the residual stays open.
      Current API mismatch is precise: shared `InducedTransport.inner_compHom_of_mulEquiv` takes a
      `MulEquiv`, while S11 `inner_compHom_of_bijective` is an endomorphism + bijectivity lemma used
      with `hInHuConj`. A future cleanup needs lane-a/hub to either build the local `MulEquiv` bridge
      or generalize the shared lemma; this is not a thin cite replacement for lane d to perform.

## lane c の並行対応 (待たない)

6.11 本体 (新 leaf `CliffordCorrespondence.lean` 予定) は
- relocate 非依存部品 (degree-exhaustion helper、θ-part 下界の inner 分解、inertia-transport) を先に build、
- stages/inner-transport を使う箇所は split 完了後に cite (それまで当該 lemma は sorried-cite せず
  proof を後回しにする構成で進める)。

## 完了条件

3 補題が GroupTheory/** の leaf に移り、S08 は import 経由で不変、full build green。
lane c (6.11) と lane b (12.14 M-side) が新 leaf を cite できる。

## 参照

- issue 9002 (G3)/(1.7)(b) — consumer。issue 9002 の「次の frontier」節 (2026-07-03 更新)。
- CLAUDE.md「分割の owner と trigger」(prefix-split は hub 実施)。
- 前例: issue 9002 の HUB 裁定 (2026-07-02) — generic は shared leaf、S14 を lane c が編集しない。
