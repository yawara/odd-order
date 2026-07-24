---
id: 144
slug: lint-lane-a-owned
title: "lint backlog — lane a 所有分 (Pf FeitSibley / S11 / S13) の frontier 通過時解消"
created: 2026-07-23
---

# lint backlog — lane a 所有分の解消

親 issue = [0138](0138-zero-warning-gate.md) (ゼロ警告 gate / ratchet)。
本 issue は **lane a が territory 所有する file の残 lint 警告**を列挙し、解消方針を与える。

## 方針 (全 per-lane issue 共通)

- **owner が frontier 通過時に解消する** (owner が proof 文脈を持ち一番安全に直せる)。
- **commit 前に `bin/check-warnings`** を回す (baseline 超過で exit 1)。解消したら
  `bin/check-warnings --update-baseline` で baseline を下げ、理由を commit message に。
- **新規警告を増やさない** (ratchet が CI で赤にする)。
- `style.show` / `style.longLine` は **per-site 判断が要る** (機械置換不可、下記)。

## lane a 所有ファイルと残警告 (2026-07-23 fresh build 実測)

> ⚠ **d (hub 代行) が機械カテゴリの一部を先行解消済み** (commit は本 issue と同 tick、
> deprecation 1 / unusedSimpArgs 3 / unusedVariables 5)。下表は **d 解消後に owner に残る分**。

| ファイル | 残カテゴリ×件数 | 手法 |
|---|---|---|
| `Peterfalvi/Appendices/FeitSibley.lean` | `unusedFintypeInType` 3 | ⚠ 判断要 (下記) |
| `Peterfalvi/Appendices/FeitSibleyQ1Component.lean` | `style.show` 4 | show→change は goal 変更 show を個別確認 |
| `Peterfalvi/S11_NineElevenRFamily.lean` | `unusedFintypeInType` 1 | ⚠ 判断要 |
| `Peterfalvi/S11_MaximalII_III_IV/ChiefFactorCore.lean` | `style.longLine` 1 (L173) | 折返し (markdown 表/長識別子なら skip) |
| `Peterfalvi/S13_SixTwoBridge.lean` | `unusedVariables` 1 (L625 `A'`) | ⚠ 下記 (協調 remove 要) |

### `S13_SixTwoBridge.lean` L625 `A'` の解消 (⚠ 協調 remove)

`sixTwoMemberDatum_of_reducible_member` の `{A' B : Subgroup ↥M}` の `A'` が dead implicit。
d が `_A'` rename を試みたが **同 file L853 が `(A' := ...)` で named 供給**しており build error →
revert 済。正しい fix = **binder `A'` 削除 + L853 の `(A' := ...)` 除去の協調編集** (S03g の
`caseB_transfer` K 除去と同型)。owner が両サイト同時に直し full build 確認。

### `unusedFintypeInType` の解消 (⚠ owner 判断)

`FeitSibley.lean` の該当 (fresh build のシグネチャ名):
- `exists_ne_trivial_liesOver_of_not_forall_eq_one` (L75) — `[Finite K] [Fintype K]` **併存**。
  `[Fintype K]` が type で unused。**まず `[Fintype K]` 削除を試す** (`[Finite K]` は残す)。
  body が `Fintype K` を要求して壊れたら `[Finite K]` から `Fintype.ofFinite` を letI で供給。
- `apply_eq_zero_of_mem_Sset_of_not_mem_Q` (L1017), `zSpan_Sset_apply_eq_zero_of_not_mem_Q` (L1033)
  — 各 1 hypothesis が type で unused。`Fintype _ → Finite _` の一般化 (0123 RULING) か、
  併存なら redundant instance 削除。

`S11_NineElevenRFamily.lean` の `sOf_coherent_extension_cross_orthogonal` (L780) も同様。

d が先行解消しなかった理由 = **どの instance が flagged か / body が使うかは owner の proof 文脈判断が最も安全**
(併存 redundant なら削除、単独なら Fintype→Finite。誤ると body が壊れ full build 往復)。

### `style.show` の解消

`FeitSibleyQ1Component.lean` の 4 件。`show ...` が **goal を変えるだけの見出し** なら `change ...` に、
中間 goal 表示なら残す (一律置換不可)。issue 0138 の frozen wave 罠参照。

## 完了条件

lane a 所有ファイルの非 sorry 警告ゼロ → `bin/check-warnings --update-baseline`。

---

## ✅ 2026-07-24 close — lane a が全件解消済み

2026-07-24 の census (main、fresh full build) で lane a 所有分の警告は **0 件**。
FeitSibley unusedFintypeInType / FeitSibleyQ1Component show / S11_RFamily / ChiefFactorCore
longLine / S13 `A'` を含め全て解消済みを確認 (0138 の完了 wave と同 tick)。close。
