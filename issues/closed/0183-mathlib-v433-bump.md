---
id: 183
slug: mathlib-v433-bump
title: "mathlib v4.33.0 bump + 関連リファクタ (solvable→Group 名前空間 / setOf→ofPred / 命名追随)"
created: 2026-08-20
---

# mathlib v4.33.0 bump + 関連リファクタ (solvable→Group 名前空間 / setOf→ofPred / 命名追随)

## 背景

Lean **v4.33.0 final = 2026-08-10 リリース**、mathlib `stable` = tag `v4.33.0` (`db584cd6`)。
CLAUDE.md の「**v4.33.0 final を待って上げる** (rc に当てない)」という保留条件が満たされた。
現 pin = `v4.32.2` / `905b95818eb3` (2026-07-28, [issue 0165 相当の commit e20e313e5](../notes/meta/mathlib_v4322_migration.md))。

### 事前実測 (2026-08-20, 両 tag を展開して機械照合)

| 項目 | 値 |
|---|---|
| mathlib drift | 470 commits (v4.32.2 → v4.33.0) |
| 我々の直 import 面 | 407 module 中 **260 (64%)** が変更対象 |
| upstream の削除 | 宣言 1430 / うち deprecated alias 826。v4.33 で新規 deprecated 758 |
| **repo が実際に踏む数** | **21 名前 / 1,938 箇所 / 371 file** |
| 機械リネームで 100 桁超過する行 | 55 行 / 41 file (折返し必要) |
| ベースライン | sorry **0** (`bin/count-sorry`)、lint 純ゼロ、full build 5m47s / 5168 jobs |

linter 標準セット (`mathlibStandardSet`) の構成は**不変** — `linter.style.haveILetI` は新設されたが
セットに入っていないので haveI/letI (14k 箇所) の大量警告は起きない。ただし `linter.style.show` が
info-tree 後処理から tactic elaborator 実装へ変わったため、`show` 484 箇所から新規警告が出うる。

## やること

### 強制 (bump で壊れる/警告になる)

- [x] **A. solvable API → `Group` 名前空間** (2026-07-16/17、最大の塊)
  - [x] `IsSolvable` → `Group.IsSolvable` (1306 箇所 / 259 file)
  - [x] `solvable_of_solvable_injective` → `Group.isSolvable_of_isSolvable_injective` (98/58)
  - [x] `IsSolvable.commutator_lt_top_of_nontrivial` → `Group.IsSolvable.…` (58/40)
  - [x] `solvable_of_surjective` → `Group.isSolvable_of_surjective` (54/32)
  - [x] `isSolvable_of_comm` → `Group.isSolvable_of_comm` (46/36)
  - [x] `solvable_of_ker_le_range` → `Group.isSolvable_of_ker_le_range` (28/18)
  - [x] `IsSolvable.commutator_lt_of_ne_bot` → `Group.IsSolvable.…` (6/6)
  - [x] `isSolvable_def` → `Group.isSolvable_def` (2)、`not_solvable_of_mem_derivedSeries` → `not_isSolvable_of_mem_derivedSeries` (1)
  - [x] `subgroup_solvable_of_solvable` = **alias 無しで削除** (instance 化) → `OddOrder/Isaacs/Ch03_SplitExtensions/Basic.lean` の 2 箇所
- [x] **B. `setOf` → `ofPred` 改名** (2026-07-09): `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (301/130)、
      `Set.Finite.toFinset_setOf` → `toFinset_ofPred` (5)、`Polynomial.finite_setOf_isRoot` (1)
- [x] **C. `restrict` → `domRestrict`** (2026-07-19): `MonoidHom.ker_restrict`/`restrict_range`/`restrict_apply` (4)。
      ⚠ `MonoidHom.restrict` 本体は **alias 無しで削除** — dot 記法は静的検出できないので build で確定
- [x] **D. 小物**: `QuadraticMap.{smul,sum,zero,sub}_apply` (23/2)、`LinearEquiv.ofLinear` → `ofLinearMap` (4)、
      `Finsupp.mapDomain_notin_range` → `mapDomain_of_notMem_range` (1)
- [x] **E. 意味論的破壊** (build でのみ露見): 重点 = `GroupTheory/PGroup` (161 行差、`IsPGroup.iff_orderOf` 仮説変更 +
      `_root_.isPGroup_iff_*` 追加)、`QuadraticForm/Basic` (120)、`Order/Minimal` (104)、`Sylow` (84)、
      `Transfer` (61)、`MonoidAlgebra` 3 file
- [x] **G. 桁溢れ 55 行の折返し** + 1500 行境界の監視 (現状 1493/1492 行の file が 2 つ)

### 同時リファクタ (ユーザー裁定 2026-08-20: 強制 + R1 + R2 + R4。R3 は別 issue)

- [x] **R1** 自前 `solvable_of_*` / `*_solvable` 系 75 宣言を mathlib 新規約 `isSolvable_*` に追随 (呼び出し側込み)
- [x] **R2** `OddOrder/Mathlib/` の 7 shim (27 宣言) を v4.33 と機械照合し、upstream 化されたものを削除・置換
- [x] **R4** stale docstring: 削除された `Nat.succ_mul_choose_eq` 参照
      (`OddOrder/BG/Ch1_Preliminary/S04_CommutatorCollection.lean:559`) 他
- ~~R3 3 つ目の類和 `OddOrder.GroupAlgebra.classSum` 統合~~ → 別 issue (設計判断を含むため)

## 完了条件

- `lake build OddOrder` フル green (v4.33.0 pin)
- `bin/check-warnings --strict` OK (非 sorry 警告ゼロ)
- AxiomsCheck OK / `bin/count-sorry` = 0 (非退行)
- `notes/meta/mathlib_v433_migration.md` に API 変更一覧と手順を記録
- CLAUDE.md ツールチェイン節 (「v4.33 へは未着手」記述) を更新

## 参照

- 前回 bump: `notes/meta/mathlib_v4322_migration.md` (commit `e20e313e5`)
- mathlib tag `v4.33.0` = `db584cd6d46c92f209a44c0f1c829460d327499d` (= `stable` branch)
- 事前調査の生成物: 両 tag 展開ツリーでの removed/deprecated FQN 照合 (本 issue 冒頭の表)

## 結果 (2026-08-20 完了)

| gate | 結果 |
|---|---|
| `lake build OddOrder` | **green** (5,489 jobs) |
| `bin/check-warnings --strict` | **非 sorry 警告ゼロ** |
| AxiomsCheck | **OK** |
| `bin/count-sorry` | **0** (非退行) |
| 変更規模 | 1,293 file / +14,106 −13,817 (commit `a83105bba`) |

### 事前調査で見えていなかった 2 つの本丸

1. **Lean 4.33 の `isDefEq` が transparency を尊重**するようになった。mathlib 自身が
   `set_option backward.isDefEq.respectTransparency false in` を 10,906 箇所で使って移行しており、
   本リポも同じ手段 (**269 箇所 / 156 file**)。必要箇所は全 1,705 file をフラグ無しで個別
   elaborate して機械的に特定 (**47 file / 120 箇所**のみ)。
2. **`linter.style.haveILetI` が既定 ON** (`mathlibStandardSet` 非所属だが `defValue := true`)。
   `haveI`/`letI` を **12,169 箇所**置換 (14,508 → 2,339)。
   ⚠ 「セット非所属だから波は来ない」という事前判断は誤りだった。

その他: `MonoidHom.restrict` が alias 無しで消えて同名が別関数に再利用 /
`Ideal.mul_le_left` ↔ `mul_le_right` の名前交換 / `MonoidAlgebra.induction_on` のケース名と
motive 引数 / `Subgroup.IsComplement'.card_mul` → `card_mul_card` (dot 記法ゆえ静的スキャンの盲点)。

詳細は [`notes/meta/mathlib_v433_migration.md`](../notes/meta/mathlib_v433_migration.md)。

### 繰延

- R3 (3 つ目の類和 `OddOrder.GroupAlgebra.classSum` の統合) — 設計判断を含むため別 issue。
