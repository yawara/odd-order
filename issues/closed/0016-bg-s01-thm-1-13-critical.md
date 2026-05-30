---
id: 16
slug: bg-s01-thm-1-13-critical
title: "BG §1 Thm 1.13 Thompson critical subgroup を形式化する"
created: 2026-05-25
---

# BG §1 Thm 1.13 Thompson critical subgroup を形式化する

## 背景

BG Thm 1.13 は Thompson critical subgroup theorem。監査メモでは Isaacs 4.31
(Thompson P×Q lemma) との同一視が誤りで、別 theorem と整理済み。

後続 §13 で参照されるため、定義・存在定理・Aut_G(H) が p-group であることの表現を
独立 issue として扱う。

## やること

- [x] BG Thm 1.13 の原 statement を mmd で確認する。
- [x] critical subgroup の構造 (`[H,G] ≤ Z(H)`, class ≤ 2, exponent p, characteristic)
      を表す Lean 定義が必要か判断する。
- [x] `Aut_G(H)` の p-group 性の表現方法を決める。
- [x] 必要な shared module を `OddOrder.GroupTheory` 配下に最小追加する。
- [x] BG-facing theorem を `S01_Solvable.lean` に追加する。

## 完了 (2026-05-30, bg-thm113-impl workflow, commits 4aefbf5..37a6277)

BG Thm 1.13 を **sorry-free / axiom-clean で完成** (adversarial verify: genuinelyDone, scaffold trap clean):

- 新規 module `OddOrder/GroupTheory/CriticalSubgroup.lean` に Gorenstein 5.3.11/5.3.13 を full port:
  - `IsCritical` predicate (characteristic ∧ cl≤2 ∧ `[G,C]≤Z(C)` ∧ `C_G(C)=Z(C)`)
  - S1 `centralizer_eq_self_of_maximal_abelian_normal` (Lemma 5.3.12)
  - S2 `isCritical_exists` (Thm 5.3.11 critical 存在, two-case 構成) ← 最難
  - S6 `Omega.exponent_eq_of_class_le_two` (核心 `(xy)^p` class≤2 恒等式 `mul_pow_eq_commutator_pow_mul_of_class_le_two` 経由)
  - S3/S7 `IsCritical.actionCommutator_eq_bot_of_acts_trivially` + `autCentralizer` p-群 (engine = `isaacs_thm_4_36`; design が GAP とした stability は既存 Ch04 で代替=不要だった)
- BG-facing `thompson_critical_omega` を `S01_Solvable.lean:845` (§1D) に: `p` odd, 非自明 `p`-群 `G` ⇒ ∃ characteristic `H` で `[H,G]⊆Z(H)`, `cl(H)≤2`, `exp H = p`, `C_{Aut G}(H)` が `p`-群。
- `AxiomsCheck.lean:676` で axiom-clean (標準3公理) を CI ガード。全体 `lake build OddOrder` green (3347 jobs)。
- ルート: Gorenstein 原文 (Isaacs に critical subgroup 定理は無い)。設計 `notes/bg/thm113_design.md`。

**訂正**: 本 issue / `notes/bg/s01_solvable.md` の「§13 で参照」は誤り。実 grep の下流利用は **§3 (L1095) / §4 Lem4.17 (L1712) / §5 Thm5.5 (L1887) / §12 (L3468)**。Isaacs 4.31 (P×Q lemma) との同一視も誤り (別定理、`notes/meta/phase2_cross_refs.md:124` 要訂正)。

→ **§4 (Blackburn rank≤2) を gate していた唯一の §1 前提が解消**。closed。

## 完了条件

- BG Thm 1.13 の statement と依存定義が Lean 上で確定している。
- 証明が sorry-free、または未証明なら明確に別 issue へ分割されている。
- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` が通る。
- `lake build OddOrder.AxiomsCheck` が通る。

## 参照

- `notes/bg/s01_solvable.md`
- `references/bg/local-analysis.mmd` L461-L472 付近
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`
- `OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean`
