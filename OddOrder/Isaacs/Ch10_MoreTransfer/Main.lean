/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch10_MoreTransfer.WreathRecognition
import OddOrder.Isaacs.Ch10_MoreTransfer.Yoshida
import OddOrder.Isaacs.Ch10_MoreTransfer.TransferIndexPrime

/-!
# OddOrder.Isaacs.Ch10 — More Transfer Theory (hub)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 10
"More Transfer Theory" (pp. 295-320) の Lean 化 (pure re-export hub)。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | leaf | 状態 |
|---|---|---|---|---|
| 10A | Yoshida の定理 + `C_p ≀ C_p` 認識 + transfer 連鎖 | 10.1 – 10.11 | `WreathRecognition` (10.3–10.5) ほか | 進行中 |
| 10B | Huppert metacyclic Sylow | 10.12 – 10.17 | ✅ 完全形式化 (2026-07-17) | `HuppertMetacyclic` (10.12/10.15) + `WreathRecognition` (10.13-10.14) + `OperatorMaschke` (10.16-10.17) |
| 10C | 群環 Δ(G) + principal ideal theorem + Alperin-Kuo | 10.18 – 10.28 | 未着手 | — |

既存被覆: Cor 10.17 = `OddOrder/BG/Ch1_Preliminary/OperatorMaschke.lean` の
`exists_aInvariant_complement_of_isElementaryAbelian`;
Lem 10.13(b) = `OddOrder/GroupTheory/IsMetacyclic.lean` の `IsMetacyclic.subgroup`。

ノート: gap 調査 = `notes/meta/three_books_full_survey_2026_07_16.md` (Isaacs Ch.10 節)
-/
