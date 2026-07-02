---
id: 11
slug: bg-s01-prop-1-2-1-4-fitting
title: "BG §1 Prop 1.2-1.4 Fitting/chief-factor block を形式化する"
created: 2026-05-25
---

# BG §1 Prop 1.2-1.4 Fitting/chief-factor block を形式化する

## 背景

BG §1A の Prop 1.2-1.4 は Fitting subgroup と chief factor centralizer を結ぶ block。
`notes/bg/s01_solvable.md` では Prop 1.2 が実測 6 回引用、Prop 1.3-1.4 も後続節で使われる
中頻度依存として整理されている。

mathlib/現行 OddOrder には chief factor / composition series 周辺の shared API がまだ薄いので、
必要なら `OddOrder.GroupTheory` 配下に小さく切り出す。

## やること

- [x] BG Prop 1.2 の正確な statement を `references/bg/local-analysis.mmd` で確認する。
- [x] chief factor / centralizer / Fitting の既存 API を棚卸しする。
- [x] Prop 1.2 を実装するか、必要な shared module の最小スコープを決める。
- [x] Prop 1.2 の前半包含 `F(G*) ≤ C_G(U/V)` for every chief factor を実装する。
- [x] Prop 1.2 の逆包含を chief series / normal interval induction で実装する。
- [x] Prop 1.3 `C_G(F(G)) ⊆ F(G)` を実装する。
- [ ] Prop 1.4 coprime automorphism faithful-on-Fitting を実装する。

## 進捗

2026-05-25 bg-s01:

- Prop 1.2 本文確認済み (`local-analysis.mmd` L360-L378)。mathlib には抽象
  `Order.JordanHolder.CompositionSeries` はあるが、BG Prop 1.2 に必要な群の
  chief factor centralizer API は未整備。
- Prop 1.3 は `centralizer_fitting_le_fitting` として sorry-free 実装済み。
  Prop 1.2 経由ではなく、`C_G(F(G))` 内の最小正規反例 + Fitting 最大性で証明。
- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` と
  `lake build OddOrder.AxiomsCheck` は成功。
- Prop 1.2 用の最小 shared module として `OddOrder.GroupTheory.ChiefFactor` を追加。
  現時点では `IsChiefFactor U V` と ambient `chiefFactorCentralizer U V = C_G(U/V)`、
  および map/comap 基本補題まで。
- Prop 1.2 の前半包含は `fitting_map_subtype_le_chiefFactorCentralizer` として
  sorry-free 実装済み。chief factor `U/V` を `G/V` の minimal normal subgroup に写し、
  Lemma 1.1 で `U/V ≤ Z(F(G/V))`、さらに `F(G*)` の quotient image が nilpotent
  normal なので `F(G/V)` に入る、という本の順序に沿う証明。
- Prop 1.2 逆包含の chief-series induction に向けて `OddOrder.GroupTheory.ChiefFactor`
  に `chiefFactorCentralizer.normal` と
  `chiefFactorCentralizer.le_iff_commutator_le` (`H ≤ C_G(U/V) ↔ ⁅U,H⁆ ≤ V`) を追加。
- Prop 1.2 の残りは、次に chief/composition series over normal intervals と
  逆包含 `⋂ C_{G*}(U/V) ≤ F(G*)` の induction から進める。
- Prop 1.4 は Prop 1.3 を使える状態になったが、semidirect product と Hall σ/core
  の形式化が残る。

2026-05-30 (bg-parallel-frontier workflow + 本人確認):

- **Prop 1.2 逆包含 `chiefFactorCentralizer_subset_le_fitting_of_isSolvable` (S01:378) は完成・axiom-clean** (#print axioms = propext/Classical.choice/Quot.sound)。上の checkbox は stale だったので [x] に更新。Prop 1.2 (両方向) + Prop 1.3 は DONE。
- **本 issue の残務は Prop 1.4 のみ** (= Prop 1.4-only に縮約)。Prop 1.4 (coprime auto faithful on F(G)) は X=G⋊A solvable + Hall σ + O_σ(F)=1 分解を要し、**§1B Prop 1.5 (issue 0012, A-invariant Hall π 一般版) に依存**。0012 完成後に着手 (本計画では Wave 2)。

## 完了条件

- BG Prop 1.2-1.4 の実装方針が `notes/bg/s01_solvable.md` と Lean コメントに反映される。
- 実装する theorem は sorry-free。
- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` が通る。
- `lake build OddOrder.AxiomsCheck` が通る。

## 参照

- `notes/bg/s01_solvable.md`
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `references/bg/local-analysis.mmd` L360-L398 付近

## ✅ CLOSE (2026-07-02 hub 全体レビュー)

Prop 1.2/1.4 落着。`S01_Solvable.lean` は comment-strip で実 sorry 0、Prop 1.4 は
`actionCommutator_eq_bot_of_fitting_le_fixedPoints` (S01_Solvable.lean:526) として証明済 (検証 2026-07-02)。
