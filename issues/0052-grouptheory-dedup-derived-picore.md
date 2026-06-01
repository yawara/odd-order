---
id: 52
slug: grouptheory-dedup-derived-picore
title: "GroupTheory の derivedInAmbient/piCoreIn 重複を BG Ch2.S07 と統一する"
created: 2026-06-01
---

# GroupTheory の derivedInAmbient/piCoreIn 重複を BG Ch2.S07 と統一する

## 背景

2026-06-01 の BG+Peterfalvi scaffold (codex commits e89971d..cacaadc) で、共有 module
`OddOrder/GroupTheory/` に以下が新規定義された:

- `GroupTheory.derivedInAmbient M` (= `(commutator ↥M).map M.subtype`, `MaximalSubgroupType.lean`)
- `GroupTheory.piCoreIn pi M` / `pCoreIn p M` / `pPrimeCoreIn p M` (`MaxNilpotentNormalHall.lean`)

これらは既存の **`OddOrder.BG.Ch2.S07.derivedInG M`** (M' を G 内に) と
**`OddOrder.BG.Ch2.S07.opiCoreInG π M`** (O_π(M) を G 内に) と**同一概念の重複定義**。

重複の原因は層構造: `GroupTheory/` は `BG/Ch2_Uniqueness/` より下層なので、GroupTheory の
共有 module から BG.Ch2.S07 を import できない (循環)。そのため codex は GroupTheory 側に
並行コピーを作らざるを得なかった。

CLAUDE.md ラッパー方針「同事実が 2 名で呼ばれて証明が分裂」を proof フェーズで誘発するため、
canonical を一本化したい。現状は scaffold (statement のみ・全 sorry) なので**急がない**が、
proof 充填の前に解消すべき。

## やること

- [ ] canonical を **`GroupTheory/` 側に降ろす**: `derivedInG`/`opiCoreInG` の定義本体を
      GroupTheory の下層 module (例 `OpResidual.lean` 周辺 / 新 `SubgroupInAmbient.lean`) に移す。
- [ ] `BG.Ch2.S07.derivedInG`/`opiCoreInG` を canonical の薄い別名にする (または S07 から削除し
      呼び出し側を canonical に張り替え)。**純粋リネーム wrapper は CLAUDE.md 違反**なので、
      S07 側は削除して全 caller を GroupTheory canonical に向けるのが筋。
- [ ] `MaximalSubgroupType.derivedInAmbient` / `MaxNilpotentNormalHall.{piCoreIn,pCoreIn,pPrimeCoreIn}`
      を canonical に統合 (定義が一致するか確認: `derivedInAmbient` = `(commutator ↥M).map M.subtype`,
      `derivedInG` の定義と突合)。
- [ ] `Ch3.S10.{Msigma,Malpha,Mbeta}` (= `opiCoreInG` 再利用) と `piCoreIn` の関係も整理。
- [ ] `lake build OddOrder` green を維持。

## 完了条件

- `derivedInG`/`derivedInAmbient` および `opiCoreInG`/`piCoreIn`/`pCoreIn`/`pPrimeCoreIn` が
  **単一 canonical 定義**に統合され、重複が消える。
- 全 caller (BG Ch2/Ch3/Ch4, GroupTheory, Peterfalvi) が canonical を参照。
- `lake build OddOrder` green。

## 参照

- `OddOrder/GroupTheory/MaximalSubgroupType.lean` (derivedInAmbient, L32)
- `OddOrder/GroupTheory/MaxNilpotentNormalHall.lean` (piCoreIn/pCoreIn/pPrimeCoreIn, L30-39)
- `OddOrder/BG/Ch2_Uniqueness/S07_Transitivity.lean` (derivedInG, opiCoreInG)
- `notes/meta/scaffold_opaque_prop_convention.md` (同 scaffold の別フォローアップ)
- CLAUDE.md「ラッパー方針」「namespace」節
