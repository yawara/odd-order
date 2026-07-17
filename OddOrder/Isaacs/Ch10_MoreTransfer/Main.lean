/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch10_MoreTransfer.WreathRecognition
import OddOrder.Isaacs.Ch10_MoreTransfer.Yoshida
import OddOrder.Isaacs.Ch10_MoreTransfer.TransferIndexPrime
import OddOrder.Isaacs.Ch10_MoreTransfer.PrincipalIdeal

/-!
# OddOrder.Isaacs.Ch10 — More Transfer Theory (hub)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 10
"More Transfer Theory" (pp. 295-320) の Lean 化 (pure re-export hub)。

## 章のセクション分割

**章完成 (2026-07-17)**: 全 28 結果 (10.1 – 10.28) が sorry-free で形式化済み。

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 10A | Yoshida の定理 + `C_p ≀ C_p` 認識 + transfer 連鎖 | 10.1 – 10.11 | ✅ 完全形式化 (2026-07-17) |
| 10B | Huppert metacyclic Sylow | 10.12 – 10.17 | ✅ 完全形式化 (2026-07-17) |
| 10C | 群環 Δ(G) + principal ideal theorem + Alperin-Kuo | 10.18 – 10.28 | ✅ 完全形式化 (2026-07-17) |

leaf 対応:

* 10A: `Yoshida` (10.1/10.2) + `WreathRecognition` (10.3–10.5) +
  `TransferIndexPrime` (10.6/10.7/10.9/10.11) +
  `OddOrder/GroupTheory/TransferTransitivity` (10.8) +
  `OddOrder/GroupTheory/MackeyTransfer` (10.10)
* 10B: `HuppertMetacyclic` (10.12/10.15) + `WreathRecognition` (10.14) +
  `OddOrder/GroupTheory/IsMetacyclic` (10.13) + `OperatorMaschke` (10.16-10.17)
* 10C: `PrincipalIdeal` (10.18/10.28) + `OddOrder/Algebra/AugmentationIdeal`
  (10.19–10.23) + `OddOrder/Algebra/PrincipalIdealTheorem` (10.24/10.25/10.27) +
  `OddOrder/Algebra/FiniteIndexAnnihilator` (10.26)

既存被覆: Cor 10.17 = `OddOrder/BG/Ch1_Preliminary/OperatorMaschke.lean` の
`exists_aInvariant_complement_of_isElementaryAbelian`;
Lem 10.13(b) = `OddOrder/GroupTheory/IsMetacyclic.lean` の `IsMetacyclic.subgroup`。

ノート: gap 調査 = `notes/meta/three_books_full_survey_2026_07_16.md` (Isaacs Ch.10 節)
-/
