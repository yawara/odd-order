---
id: 145
slug: lint-lane-b-owned
title: "lint backlog — lane b 所有分 (Higman/Suzuki2Groups / Pf Suzuki App / PrimeTIResidue) の解消"
created: 2026-07-23
---

# lint backlog — lane b 所有分の解消

親 issue = [0138](0138-zero-warning-gate.md)。本 issue は **lane b が territory 所有する file の残 lint 警告**を列挙。
方針は [0144](0144-lint-lane-a-owned.md) 冒頭「方針」節と共通 (owner が frontier 通過時に解消 /
commit 前 `bin/check-warnings` / show・longLine は per-site 判断)。

> ⚠ lane b の territory (Higman/Suzuki2Groups・Pf Suzuki Appendix) は **b の active zone**。
> hub/d は触らない (d の frozen wave は b の cold file のみ、既に一巡)。b が frontier 通過時に自分で消す。

## lane b 所有ファイルと残警告 (2026-07-23 fresh build 実測、計 45 件)

### Higman/Suzuki2Groups/HigmanLemmaTwelve/

| ファイル | カテゴリ×件数 |
|---|---|
| `XiLengthFromCard.lean` | `style.show` 6 / `style.longLine` 1 / `unusedSectionVars` 1 |
| `CaseDispatch.lean` | `style.show` 4 |
| `AmbientProductCoordinate.lean` | `style.show` 4 / `unusedFintypeInType` 1 (`homocyclicFourSquareSubgroupEquivFrattini_squareEquiv` L444) |
| `MixedEigenweights.lean` | `style.show` 2 |
| `CaseSplitBCD.lean` | `unusedSectionVars` 5 / `unusedVariables` 1 |

### Peterfalvi/Appendices/Suzuki/

| ファイル | カテゴリ×件数 |
|---|---|
| `WCyclicDivides.lean` | `style.show` 5 / `style.longLine` 1 |
| `FirstCase/StepOne.lean` | `style.show` 4 |
| `FirstCase/FieldAction.lean` | `style.show` 3 / `unnecessarySimpa` 1 |
| `FirstCase/StepThree.lean` | `style.show` 1 |

### Peterfalvi/Appendices/Suzuki2Groups/

| ファイル | カテゴリ×件数 |
|---|---|
| `ModelCenters.lean` | `style.show` 1 |
| `QuotientPlaneModel.lean` | `style.show` 1 / `unusedSectionVars` 1 |

### GroupTheory/RepresentationTheory/

| ファイル | カテゴリ×件数 |
|---|---|
| `PrimeTIResidue.lean` | `unusedFintypeInType` 1 (`PrimeTIResidueData.ofS06Hypothesis_mu2_apply_of_mem_V` L672) / `unusedSectionVars` 1 |

## 手法メモ

- **`style.show` (31 件、b 最多)**: `show` が **goal を変えるだけ**なら `change` に置換。
  中間 goal 表示 (可読性のための intermediate state) なら残す。**一律 sed 置換不可** — 個別に
  「この show は goal を変えているか」を確認 (issue 0138 の frozen wave 罠)。
- **`unusedSectionVars` (8 件)**: `omit <var> in` を該当宣言直前に。⚠ 型注意
  (0123 wave 2 の罠 — omit した変数が instance 経由で使われていると壊れる、full build 確認)。
- **`unusedVariables` (1)**: `_`-prefix。ただし **named-arg 呼び出し (`(name := ...)`) が
  他 file にあれば binder rename で壊れる** — 先に `grep -rn "<name>\s*:="` で確認。
- **`unusedFintypeInType` (2)**: `Fintype _ → Finite _` 一般化 (0123 RULING)、または併存 redundant なら削除。
- **`unnecessarySimpa` (1, FieldAction)**: `simpa` → `simp` か、simpa の引数が不要なら削る。owner 判断。
- **`style.longLine` (2)**: 折返し。長識別子/markdown 表なら skip。

## 完了条件

lane b 所有ファイルの非 sorry 警告ゼロ → `bin/check-warnings --update-baseline`。
