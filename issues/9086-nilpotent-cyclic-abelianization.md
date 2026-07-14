---
id: 9086
slug: nilpotent-cyclic-abelianization
title: "nilpotent + cyclic abelianization ⟹ cyclic (shared GroupTheory leaf)"
created: 2026-07-12
---

# nilpotent + cyclic abelianization ⟹ cyclic (shared GroupTheory leaf)

## 背景

**CLAIM (lane a, 2026-07-12)**: 新 shared leaf `OddOrder/GroupTheory/NilpotentAbelianization.lean`。

Pf (11.9.c) の caseB 帰結 (issue 1024 P3) が必要とする一般群論:
**G nilpotent + G/G′ cyclic ⟹ G cyclic** (Coq mathcomp `cyclic_nilpotent_quo_der1_cyclic`、
PFsection11.v:1144 で `FTtype34_structure` が cite)。mathlib に無し (2026-07-12 検索:
`commutative_of_cyclic_center_quotient` 系 = center-quotient 版のみ、ZGroup は逆方向)。
repo 内にも無し (`grep IsNilpotent` × cyclic 交差 0 件)。

consumer: lane a (11.9.c) `U/U′ cyclic (Singer) + U nilpotent (TypePData.U_nilpotent) → U cyclic
→ IsMulCommutative U → ¬TypeIV`。lane c の T-side (11.9) instantiate (`hVcomm`,
S16_NonExistenceG/TTypeII.lean:784) も同 route で cite 予定。

## やること

- [x] 9000 scan (claim 衝突なし、2026-07-12)
- [x] `OddOrder/GroupTheory/NilpotentAbelianization.lean` 新設 (2026-07-12, sorry-free):
  - `commutator_le_lowerCentralSeries_of_isCyclic_quotient` (γ₂ ≤ γ₃ = ⁅γ₂,⊤⁆;
    G/γ₃ の center-quotient cyclic → abelian → 生成元評価)
  - `commutator_eq_bot_of_isNilpotent_of_isCyclic_quotient` (安定化 + nilpotency 降下)
  - `isCyclic_of_isNilpotent_of_isCyclic_quotient` (G ≅ G/⊥)
  - `isCyclic_of_isNilpotent_of_ker_le_commutator` (application 形:
    f : G →* C cyclic, ker f ≤ commutator G)
- [x] build green + AxiomsCheck 登録 (3 本、axioms check OK)

## 完了条件

leaf が sorry-free で build green、issue 1024 P3 が cite。

## 参照

- issue 1024 (consumer)、Coq mathcomp `cyclic_nilpotent_quo_der1_cyclic` (odd_order 側 cite:
  PFsection11.v:1144)
- mathlib: `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`
  (Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:180)、`Subgroup.lowerCentralSeries` (Nilpotent.lean)

## ⚠ HUB RULING (2026-07-14, tick 38): lane b の dup 再構築 `2ca52edf` を差し戻し

lane b が 2035 #42-#43 の caseB-T route 用に新 leaf
`OddOrder/GroupTheory/NilpotentCyclicAbelianization.lean` (+120) を新設したが、hub 照合で
**本 claim (lane a, 2026-07-12 完了) の既存 leaf `NilpotentAbelianization.lean` の真部分複製**と確定:
- b `commutator_eq_bot_of_isCyclic_quotient` ≡ a `commutator_eq_bot_of_isNilpotent_of_isCyclic_quotient`
  (statement 同一)
- b `isMulCommutative_of_isNilpotent_of_isCyclic_quotient` ≡ a `isCyclic_of_isNilpotent_of_isCyclic_quotient`
  ∘ `isMulCommutative_of_isCyclic` (a 版は cyclic までの強い結論を既に持つ)
- b の新 leaf は consumer 0 の orphan (root closure 外)。a の既存 leaf は
  S13_NonGaloisExclusion + AxiomsCheck が live consume 中。
- 経緯: #42 で「所在要確認」を正しく flag したが、確認 grep が statement パターン検索で
  既存 leaf 名 (`NilpotentAbelianization`) を miss。**open 9000 claim scan (本 issue が open で
  leaf path 明記) をしていれば防げた** — claim-before-build 手順の遵守を再徹底。

**処置 (成果保全・通常継続、STOP でない)**:
1. b の `2ca52edf` (dup leaf) と `e1dea754` (dup 前提の docs #43) は**未合流** (genuine な
   `02a4f916` step 1 + `c3892668` #42 は合流済み `e68658ad`)。
2. **b への差し戻し**: branch b 上で `NilpotentCyclicAbelianization` leaf を撤去し、#43 の
   `V_commutative_of_caseB` 構築は既存 `OddOrder.GroupTheory.isCyclic_of_isNilpotent_of_isCyclic_quotient`
   (+ `isMulCommutative_of_isCyclic`) を cite する形に書き換え (route 自体は genuine — 変更は
   lemma の supply 元のみ)。#43 の記録は cite 修正後に再提出でよい。
3. 次 tick 以降: b の de-dup commit を通常ゲートで合流。`main..b` の 2ca52edf/e1dea754 残存は
   本裁定の既知状態として扱う (盲目的 merge をしない)。
