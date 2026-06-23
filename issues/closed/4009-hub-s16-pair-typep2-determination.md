---
id: 4009
slug: hub-s16-pair-typep2-determination
title: "HUB: §16 pair で mp.S を type-P2 と判定 (Pf 13.2.a, q<p で disjunction resolve) — carrier wiring の唯一 gate"
created: 2026-06-23
---

# HUB: §16 pair で mp.S を type-P2 と判定 (Pf 13.2.a) — carrier wiring の唯一 gate

## 背景

issue 4008 (option A) で lane-c が POLE-1 TypePData carrier を構築。**carrier 構成は完成
(全 sorry-free)**:

- `typePData_of_kappaHall_hallComplement` (engine, hP2 入力)
- `isHall_kappaSigmaCompl_of_isTypeP2_complement` (hUhall discharger)
- **`exists_typePData_W1_eq_of_isTypeP2`** (compose, commit `a6faa39c`):
  `type-P2 M + cyclic κ-Hall K → ∃ data : TypePData M, data.W1 = K`

これで「指定 κ-Hall を W1 に持つ matched TypePData」の構成が単一 sorry-free lemma に集約。
§15 `basic_structure` (13.2) の U-side blocker (UW1_frobenius/U_commutative) を解く carrier 機構。

## 問題: step 3 wiring の唯一の gate = mp.S が type-P2

producer `section16TypePStructure_of_isMinimalSimpleOdd` で `exists_typePData_W1_eq_of_isTypeP2`
を mp.S に適用するには **mp.S が type-P2** が要る。しかし:

- pair 構成 `exists_section16MaximalPair_data` (lane-f) は `IsTypeP2 S ∨ IsTypeP2 Mstar`
  (`FeitThompson.lean:356` の `hP2disj`) **disjunction のみ** carry し、どちらが type-P2 か未確定。
- `mp.K_lt_Kstar` (q < p、smaller κ-Hall = S) で「S が type-P2」を resolve するのが
  **Pf (13.2.a)「q<p ⟹ S type II」**。だが (13.2.a) は:
  - **producer 文脈で必要** (basic_structure の上流ゆえ basic_structure では供給不可 = 循環)
  - 証明に §15-16 type 構造を要する deep result (現状未形式化)

## 判断を仰ぐこと

- [ ] **(A)** lane-f が `exists_section16MaximalPair_data` を refine し、ordering (q<p) を使って
      **`S` を type-P2 の側に固定** (disjunction → `IsTypeP2 mp.S` field 化、または mp に `S_typeP2` 追加)。
      lane-f は Prop 16.1 進行中ゆえ自然な拡張の可能性。
- [ ] **(B)** (13.2.a)「q<p ⟹ S type-P2」を BG §16 / lane-c §15 で standalone 証明 (deep)。
- [ ] **(C)** その他 (carrier 機構は完成・consume 待ちなので、gate 解消まで wiring 保留)。

(A)/(B) いずれでも **`IsTypeP2 mp.S` が producer で得られれば wiring は機械的**
(`exists_typePData_W1_eq_of_isTypeP2` を呼び `Section16TypePStructure.Sdata` field へ → `S15.Hypothesis`
→ basic_structure)。

## 完了条件

`IsTypeP2 mp.S` (or mp に該当 field) が producer で利用可能になり、wiring 着手可能になったら closed。

## 参照

- carrier 機構: `OddOrder/FeitThompson.lean` (`exists_typePData_W1_eq_of_isTypeP2` 他、commit `a6faa39c`)
- pair 構成: `OddOrder/FeitThompson.lean:298` (`exists_section16MaximalPair_data`),
  `:356` (`hP2disj` disjunction)
- 設計: `notes/peterfalvi/s15_s_and_t.md`「POLE-1 TypePData carrier 構築」
- 関連: issue 4008 (option A), lane-f Prop 16.1 (hP2II COMPLETE)

---

## 解決 (2026-06-23, ユーザー裁可 = lane-h が (13.2.a) 担当, relane #4)

issue 2019 (lane-h starve) と issue 4009 (carrier wiring gate = IsTypeP2 mp.S) を **1 割当で同時解決**:
**lane-h が Pf (13.2.a)「q<p ⟹ mp.S は type-P2」を担当**。
- 作業場所 = `FeitThompson.lean` (mp 定義 + tp producer consume 地点、shared_re 内ゆえ lane-h 編集可、owned_re 変更なし)。
- (13.2.a) 証明 → `IsTypeP2 mp.S` 供給 → tp producer が `exists_typePData_W1_eq_of_isTypeP2` を mp.S に適用可能化
  → lane-c が carrier wiring (step 3) 機械的に進む → §15 basic_structure unblock + POLE-1 前進。
- type-determination ゆえ lane-h type 構造の延長、§6 char (ユーザー管理 B) と非衝突、critical path 直結。
- deep BG §15-16 下流補題が要れば lane-h が lane-f に notes/issue で依頼 (F が BG owner)。
- FeitThompson.lean は def 単位 F=mp+Prop16.1 / B=cd / C=tp / H=(13.2.a) の 4 者共有。
反映: lane-h/lane-f LAUNCH.md、merge_monitor.md (relane #4 note + FeitThompson F/B/C/H)、cron (6efde802)。CLOSED。
