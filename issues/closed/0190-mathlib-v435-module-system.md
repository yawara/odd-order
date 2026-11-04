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
- 旧 pin = `v4.34.1` / `d13f23b723b8` (2026-09-27, [issue 0189](0189-mathlib-v434-bump.md))。
- **版上げと module 化は切り離せない**: mathlib v4.35.0 は `requiresModuleSystem := true` を立てる。
  非 module の file は mathlib の import 1 行ごとに Lake が warning を出し、`bin/check-warnings
  --strict` が CI を赤にする。版上げ単独の commit では一時的に `allowNonModules = true` を置いた。
- Palomar の提出要件 (≥ v4.35.0-rc2、import される部分は module 必須) も満たす。

## やること

- [x] **A. 版上げ** (非 module のまま、`allowNonModules = true`)
  - [x] pin (toolchain / lakefile / manifest)
  - [x] API 変更 (正規性・`IsMulCommutative` の instance 引数化、`Subgroup.FG` の class 化、
        `Cyclic.Basic` の分割、`ULift.ext` 等)
  - [x] deprecated 11 名 (約 340 箇所)、統合された instance linter の抑制位置、no-op タクティク 14 件
- [x] **B. module 化** (全 1,721 file に `module` / `public import` / `@[expose] public section`)
  - [x] 不足 import の事前計算 (olean の定数参照 + extraModUses) → 23 file / 24 行
  - [x] 公開される文・def 本体から参照される `private` の解除 → 94 宣言 / 38 file
  - [x] AxiomsCheck の補助 def を `meta def` に
  - [x] `allowNonModules` を外し `requiresModuleSystem = true` (非 module file の混入 gate)
- [x] **C. 関連リファクタ**
  - [x] `lake shake` で import を整理 (2 回で不動点、盲点は `-- shake: keep` で保護)
  - [x] 互換フラグ `backward.isDefEq.respectTransparency false` の棚卸し (231 → 227)
  - [x] v4.35 で mathlib に入った補題との重複解消 (4 件)、「mathlib に無い」記述の再検証 (陳腐化 1 件)
  - [x] 既存の mathlib 重複のうち純粋な名前違い 17 件を削除
  - [x] CLAUDE.md (ツールチェイン節・「Lean module system」節・minimal import と shake・private の制約)
  - [x] 移行記録 [`notes/meta/mathlib_v435_migration.md`](../../notes/meta/mathlib_v435_migration.md)

## 完了条件

- `lake build OddOrder` green、`bin/check-warnings --strict` ゼロ、AxiomsCheck OK、sorry 非退行 — 達成
- 全 `.lean` が module、lakefile に `requiresModuleSystem = true` — 達成
- 移行記録 note と CLAUDE.md の更新 — 達成

## 消化記録 (2026-11-05)

branch `mathlib-v435` (作業は worktree `odd-order-v435mod` で並行):

1. `chore(0190): mathlib v4.35.0 に版上げ (非 module のまま)`
2. `refactor(0190): 全 file を Lean の module system へ移行`
3. `refactor(0190): lake shake で import を整理`
4. `refactor(0190): 互換フラグ respectTransparency を v4.35 で棚卸し (231 → 227)`
5. `refactor(0190): v4.35 で mathlib に入った補題との重複を解消`
6. `refactor(0190): mathlib と文・引数とも同一の自前定理 17 件を削除`
7. `docs(0190): …` (本 issue の close、CLAUDE.md、移行記録)

最終状態: sorry 0、AxiomsCheck 6,034 件 OK (DadeContradiction の `#print axioms` 5 本を検査に移して +5、
削除した自前定理の検査 1 件を外して −1)、lint 純ゼロ、`lake shake OddOrder` 提案ゼロ。

### 残したもの (意図的)

- mathlib と文が一致するが引数を instance 化・暗黙化した自前定理 15 件 (CLAUDE.md「ラッパー方針」の
  「引数順 / convention 適応」に当たる) と、実演定理 `BG.AppC.theoremC_sl2`。
- 互換フラグ 227 本 (v4.35 でも外すと落ちる)。

## 参照

- 前回の移行: [issue 0189](0189-mathlib-v434-bump.md)、[`notes/meta/mathlib_v434_migration.md`](../../notes/meta/mathlib_v434_migration.md)
