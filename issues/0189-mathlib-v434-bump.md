---
id: 189
slug: mathlib-v434-bump
title: "mathlib v4.34.1 bump + 関連リファクタ (if_pos→ite_eq_left 系 / TensorProduct.inductionOn / deprecated module)"
created: 2026-09-27
---

# mathlib v4.34.1 bump + 関連リファクタ (if_pos→ite_eq_left 系 / TensorProduct.inductionOn / deprecated module)

## 背景

ユーザー指示 (2026-09-27): 「最新の mathlib の stable version にアップグレード。影響を受ける
ファイルはついでにリファクタリング、関連ファイルのモジュール分割も直してよい。stale な
ドキュメントや docstring も対象」。

- 最新 stable = **Lean v4.34.1 / mathlib tag `v4.34.1`** (`d13f23b723b8`, 2026-09-24)。
  v4.35.0 は rc3 止まりなので対象外 (CLAUDE.md「rc には当てない」)。
- 現 pin = `v4.33.0` / `db584cd6d46c` (2026-08-20, [issue 0183](closed/0183-mathlib-v433-bump.md))。

### 事前実測 (2026-09-27, 両 tag を展開して機械照合)

| 項目 | 値 |
|---|---|
| mathlib drift | **1,032 commits** (v4.33.0 → v4.34.1)、5,318 file / +96k −62k |
| 我々の直 import 面 | 408 module 中 **269 (66%)** が変更対象、削除 0、**deprecated module 2** |
| mathlib の新規 deprecated | 706 宣言 (repo が確実に踏むのは下表) |
| Lean core の新規 deprecated | 165 宣言 (repo が踏むのは下表) |
| ベースライン | sorry 0、lint 純ゼロ (`bin/check-warnings --strict`)、1,719 file / 844k 行 |

## やること

### 強制 (bump で壊れる/警告になる)

- [x] **A. Lean core の if-then-else 補題改名** (Lean #14501, `since := "2026-07-21"`)
  - [x] `if_pos` → `ite_eq_left` (945)、`if_neg` → `ite_eq_right` (1235)
  - [x] `dif_pos` → `dite_eq_left` (107)、`dif_neg` → `dite_eq_right` (74)
  - [x] `if_true` → `ite_true` (23)、`if_false` → `ite_false` (19)
- [x] **B. mathlib の改名**
  - [x] `TensorProduct.induction_on` → `TensorProduct.inductionOn` (**`zero` ケース消滅**、36 + 素の `induction` 2)
  - [x] `Subgroup.normalizer_inf_normalizer_le_normalizer_sup` → `Subgroup.inf_normalizer_le_normalizer_sup` (17)
  - [x] `List.prod_eq_pow_card` → `List.prod_eq_pow_length` (1)
- [x] **C. deprecated module**: `Mathlib.Data.Complex.Basic` → `Mathlib.Basic.Complex.Basic` (7)、
      `Mathlib.Data.Finite.Prod` → `Mathlib.Basic.Finite.Prod` (2)
- [x] **D. linter の変更**: `linter.style.nativeDecide` → `linter.style.native` (標準セット内の改名、repo 影響なし)、
      新設 `linter.internalConstructors` (`defValue := true`、**error**。repo 影響なし)
- [x] **E. 意味論的破壊** (build でのみ露見、4 ラウンドで 18 module)
  - [x] `List.TFAE.out` が **1-indexed** に (23 箇所。`.out 0 3` は "TFAE indices start at 1" で落ちるが、
        `.out 1 2` は**黙って意味が変わる**)
  - [x] `Finsupp.mapDomain_apply` (単射版) → `mapDomain_apply_of_injective`、**旧名は一般形に再利用** (2)
  - [x] `Equiv.setCongr (h : s = t)` → `Set.equivOfEq`、**旧名は `Equiv.Set.congr` の新名に再利用** (14)
  - [x] `Subgroup.isMulCommutative_closure` の仮説が `S.Pairwise Commute` に (10、ゴールが `Commute x y` になり `simpa` 不可)
  - [x] `isIntegral_algebraMap_iff`: 単射性引数 → `[FaithfulSMul A B]` instance (3)
  - [x] `DoubleCoset.eq`/`out_eq'` の `H K` が implicit、`mk_out_eq_mul` の結論が `∃ h ∈ H, ∃ k ∈ K, …` に (3)
  - [x] `Nat.multiplicity_eq_factorization` の `n ≠ 0` 仮説が消滅 (4)
  - [x] `IsWellFounded` deprecated → `WellFounded` (1)
  - [x] `Representation.isTrivial_def` の `@[simp]` 削除 (3)
  - [x] `IsArtinian` 系が推移 import されなくなった → `Mathlib.RingTheory.Artinian.Module` を明示 import (2)
  - [x] 余分になったステップ (`convert` 後の `congr 1`、`simp [Set.mem_image, eq_comm]` → `simp`)
- [x] **F. 桁溢れ・1500 行境界の監視** (改名で 100 桁超過した 54 行を折返し。1500 行超過なし)

### 同時リファクタ (ユーザー指示: 影響ファイルのリファクタ / モジュール分割 / stale doc)

- [ ] **R1** 影響を受けたファイルのリファクタ (改名に伴う自前命名の追随など)
- [ ] **R2** `OddOrder/Mathlib/` shim の棚卸し (v4.34.1 で upstream 化されたものを削除・置換)
- [ ] **R3** 関連ファイルのモジュール分割の是正
- [ ] **R4** stale docstring / ドキュメント (改名された補題名への言及、CLAUDE.md ツールチェイン節 等)

## 完了条件

- `lake build OddOrder` フル green (v4.34.1 pin)
- `bin/check-warnings --strict` OK (非 sorry 警告ゼロ)
- AxiomsCheck OK / `bin/count-sorry` = 0 (非退行)
- `bin/check-links` / `bin/check-doc-names` OK
- `notes/meta/mathlib_v434_migration.md` に API 変更一覧と手順を記録
- CLAUDE.md ツールチェイン節を更新

## 参照

- 前回 bump: [`notes/meta/mathlib_v433_migration.md`](../notes/meta/mathlib_v433_migration.md) (issue 0183)
- mathlib tag `v4.34.1` = `d13f23b723b8a846827a245b89c10fc7d3f11612`
- Lean v4.34.0 release notes: https://lean-lang.org/doc/reference/latest/releases/v4.34.0/
