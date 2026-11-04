---
id: 190
slug: mathlib-v435-module-system
title: "mathlib v4.35.0 bump + Lean module system 移行 + 関連リファクタ"
created: 2026-11-04
---

# mathlib v4.35.0 bump + Lean module system 移行 + 関連リファクタ

## 背景

ユーザー指示 (2026-11-04): 「mathlib を最新の stable にあげます。module システムにも対応し、
単に依存関係をアップデートするだけでなく、関連する部分のリファクタリングも一緒にやってください」。
検討結果 (使い捨て worktree での試行) を提示し、2026-11-05 に「推奨通り全部」で着手。

- 最新 stable = **Lean v4.35.0 / mathlib tag `v4.35.0`** (`56a005855ea1`, 2026-10-13)。
  v4.36.0 は rc2 止まりなので対象外 (CLAUDE.md「rc には当てない」)。
- 現 pin = `v4.34.1` / `d13f23b723b8` (2026-09-27, [issue 0189](closed/0189-mathlib-v434-bump.md))。
- **版上げと module 化は切り離せない**: mathlib v4.35.0 は `requiresModuleSystem := true` を立てる。
  非 module の file は mathlib の import 1 行ごとに Lake が warning を出し、`bin/check-warnings
  --strict` が CI を赤にする。版上げ単独の commit では一時的に `allowNonModules = true` を置く。
- Palomar の提出要件 (≥ v4.35.0-rc2、import される部分は module 必須) も満たす。

### 事前実測 (2026-11-04、使い捨て worktree で試行)

| 項目 | 値 |
|---|---|
| mathlib drift | 651 commits (v4.34.1 → v4.35.0) |
| module 化の試行 (162 file) | 153 file (94%) がヘッダ変換だけで通る。残り = private 参照 5 / import 消失 4 |
| 見えなくなる mathlib module | 1 file あたり中央値 46 (自前 import を全部 `public import` にした場合) |
| 再ビルドの省略 | 上流 file の証明だけを直すと、その file だけ再ビルド (下流は replay) |
| AxiomsCheck | 補助 def 2 本に `meta` を付けるだけで動き、module 境界越しに `sorryAx` も検出 |

## やること

- [ ] **A. 版上げ** (非 module のまま、`allowNonModules = true`)
  - [ ] pin (toolchain / lakefile / manifest)
  - [ ] API 変更の修正 (instance 引数化した補題、`Subgroup.FG` の class 化、`Cyclic.Basic` の分割 等)
  - [ ] deprecated の置換、強化された instance linter (`unusedFintypeInType` / `unusedDecidableInType`) 等の lint
- [ ] **B. module 化の前準備** (非 module のまま green)
  - [ ] 不足 import の事前計算 (olean の定数参照 + extraModUses から) と追加
  - [ ] 公開される文・def 本体から参照される `private` 宣言の解除
- [ ] **C. module 化** (全 file に `module` / `public import` / `@[expose] public section`)
  - [ ] AxiomsCheck の補助 def を `meta def` に
  - [ ] `allowNonModules` を外し `requiresModuleSystem = true` (非 module file の混入 gate)
- [ ] **D. 関連リファクタ**
  - [ ] `lake shake` で import を整理 (証明でしか使わない import を private に、未使用を削除)
  - [ ] 互換フラグ `backward.isDefEq.respectTransparency false` (231 箇所) の棚卸し
  - [ ] v4.35 で mathlib に入った補題との重複解消、「mathlib に無い」記述の再検証
  - [ ] CLAUDE.md (ツールチェイン節・新 leaf のヘッダ規約・private の制約・minimal import と shake の記述)
  - [ ] 移行記録 `notes/meta/mathlib_v435_migration.md`

## 完了条件

- `lake build OddOrder` green、`bin/check-warnings --strict` ゼロ、AxiomsCheck OK、sorry 非退行
- 全 `.lean` が module、lakefile に `requiresModuleSystem = true`
- 移行記録 note と CLAUDE.md の更新

## 参照

- 前回の移行: [issue 0189](closed/0189-mathlib-v434-bump.md)、[`notes/meta/mathlib_v434_migration.md`](../notes/meta/mathlib_v434_migration.md)
