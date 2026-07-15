---
id: 104
slug: deprecated-shim-cleanup
title: "返り値型が変わった deprecated shim 4 種 (~111 sites) の置換"
created: 2026-07-09
---

# 返り値型が変わった deprecated shim 4 種 (~111 sites) の置換

## 背景

mathlib v4.32 bump (branch mathlib-v432、notes/meta/mathlib_v432_migration.md) の deprecation
sweep で、**同 signature リネームは全置換済** (commit 68359993)。返り値型が変わった deprecated
shim は動作継続中のため据え置いた。次回 bump で削除される可能性があるので、それまでに置換する。

## やること

- [ ] `Subgroup.inf_eq_bot_of_coprime` (~68 sites) → `Subgroup.disjoint_of_coprime_natCard` + `.eq_bot` (H ⊓ K = ⊥ が要る site) / `Disjoint` のまま使える site は直接
- [ ] `commutative_of_cyclic_center_quotient` (~24 sites) → `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` + `.is_comm.comm` (wave 修正済み site のパターン参照: git log -S)
- [ ] `IsPGroup.commutative_of_card_eq_prime_sq` (~12 sites) → `isMulCommutative_of_card_eq_prime_sq` + `isMulCommutative_iff.mp` (wave2 ElementaryAbelian の置換例参照)
- [ ] `Subgroup.normal_of_comm` (~7 sites) → `Subgroup.normal_of_isMulCommutative` (wave5 Ch04 の置換例参照)
- [ ] 置換は形が site ごとに違うため機械置換不可 — file 単位で agent fan-out が適当
- [ ] 残存 deprecation warning ゼロ化の確認 (full build log から grep)

## 進捗 (2026-07-15)

- first wave: `OddOrder/Mathlib/SchurZassenhausConj.lean` と `OddOrder/Isaacs/**` の
  9 code sites + 2 doc references を新 API へ移行。
- wave 後の旧名は Mathlib/Isaacs 配下 0、repo 全体 59 occurrences
  (58 code sites + `SingerField.lean` の説明 comment 1件)。
- 検証: `lake build OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7B2_NormalJ_PComplement`
  成功 (2371 jobs)、`lake build OddOrder OddOrder.AxiomsCheck` 成功 (4234 jobs)。
- second wave: BG §3.6 (`S03f_Prelim` / `S03f_Thm36`) の 6 code sites と、
  `S03f_Thm36` / `SingerField` の 2 doc references を新 API へ移行。
- wave 後の raw Lean-source occurrences は
  `inf_eq_bot_of_coprime` 53、`commutative_of_cyclic_center_quotient` 23、
  `IsPGroup.commutative_of_card_eq_prime_sq` 12、`Subgroup.normal_of_comm` 6。
- focused 検証: `lake build OddOrder.BG.Ch1_Preliminary.S03f_Thm36`
  成功 (3064 jobs)、`lake build OddOrder OddOrder.AxiomsCheck` 成功 (4234 jobs)。
- third wave: shared `GroupTheory` (`IsExtraspecial` / `ExtraspecialSinger`) の
  3 code sites + 1 doc reference を新 API へ移行し、同ディレクトリの旧名をゼロ化。
- wave 後の raw Lean-source occurrences は
  `inf_eq_bot_of_coprime` 53、`commutative_of_cyclic_center_quotient` 20、
  `IsPGroup.commutative_of_card_eq_prime_sq` 11、`Subgroup.normal_of_comm` 6。
- focused 検証: 上記 2 modules を対象にした `lake build` 成功
  (2378 jobs)、`lake build OddOrder OddOrder.AxiomsCheck` 成功 (4234 jobs)。

- fourth wave: Isaacs Ch.4–6 の 8 code sites と 7 doc references を新 API へ
  移行し、`OddOrder/Isaacs/**` の対象旧名 4 種をゼロ化。
- wave 後の raw Lean-source occurrences は
  `inf_eq_bot_of_coprime` 53、`commutative_of_cyclic_center_quotient` 10、
  `IsPGroup.commutative_of_card_eq_prime_sq` 6、`Subgroup.normal_of_comm` 6。
- focused 検証:
  `lake build OddOrder.Isaacs.Ch06_FrobeniusActions.DQSDRecognition OddOrder.Isaacs.Ch06_FrobeniusActions.Lemma615`
  成功 (2282 jobs)。
- `lake build OddOrder OddOrder.AxiomsCheck` 成功 (4234 jobs)。
  `OddOrder.feitThompson` の依存公理は allowlist 内の 3 種のみ。

- fifth wave: BG Ch.1 §4 の 10 code sites と 3 doc/comment references を新 API へ
  移行し、`OddOrder/BG/Ch1_Preliminary/**` の対象旧名 4 種をゼロ化。
- wave 後の raw Lean-source occurrences は
  `inf_eq_bot_of_coprime` 53、`commutative_of_cyclic_center_quotient` 4、
  `IsPGroup.commutative_of_card_eq_prime_sq` 0、`Subgroup.normal_of_comm` 6。
- focused 検証:
  `lake build OddOrder.BG.Ch1_Preliminary.S04_PGroupsSmallRank OddOrder.BG.Ch1_Preliminary.S04_SmallRankBasic OddOrder.BG.Ch1_Preliminary.S04b_Thm412 OddOrder.BG.Ch1_Preliminary.S04c_Prop411 OddOrder.BG.Ch1_Preliminary.S04d_GorThm415 OddOrder.BG.Ch1_Preliminary.S04f_Omega1`
  成功 (2519 jobs)。
- `lake build OddOrder OddOrder.AxiomsCheck` 成功 (4234 jobs)。
  `OddOrder.feitThompson` の依存公理は allowlist 内の 3 種のみ。

- sixth wave: BG Ch.3 §§10–13 の 25 code sites を新 API へ移行し、
  `OddOrder/BG/Ch3_MaximalSubgroups/**` の対象旧名 4 種をゼロ化。
- wave 後の raw Lean-source occurrences は
  `inf_eq_bot_of_coprime` 30、`commutative_of_cyclic_center_quotient` 3、
  `IsPGroup.commutative_of_card_eq_prime_sq` 0、`Subgroup.normal_of_comm` 5。
- focused 検証: 上記 12 modules を対象にした `lake build` 成功
  (3154 jobs)。
- seventh wave: BG Ch.4 §§14–16 の 22 code sites を新 API へ移行し、
  `OddOrder/BG/Ch4_FamilyOfMaximal/**` の対象旧名 4 種をゼロ化。
- wave 後の raw Lean-source occurrences は
  `inf_eq_bot_of_coprime` 8、`commutative_of_cyclic_center_quotient` 3、
  `IsPGroup.commutative_of_card_eq_prime_sq` 0、`Subgroup.normal_of_comm` 5。
- focused 検証: 上記 14 modules を対象にした `lake build` 成功
  (3210 jobs)。

## 完了条件

full build green + `has been deprecated` warning が repo 由来 0 件。

## 参照

- notes/meta/mathlib_v432_migration.md「deprecation sweep」節
- 置換パターンの実例: bump waves の commits (git log --oneline main..mathlib-v432 相当領域)
