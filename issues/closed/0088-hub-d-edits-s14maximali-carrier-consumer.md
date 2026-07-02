---
id: 88
slug: hub-d-edits-s14maximali-carrier-consumer
title: "HUB: lane d が b 所有 S14_MaximalI の carrier consumer を編集 (範囲逸脱) — 承認 or 再分割の判断"
created: 2026-06-29
---

# HUB: lane d が b 所有 S14_MaximalI の carrier consumer を編集 (範囲逸脱) — 承認 or 再分割の判断

## 背景

2026-06-29 の合流 tick (:13) で **lane d (BG §14–16 + carrier)** の 3 commits を検査したところ、
レーン範囲逸脱を検出 → ⛔ 監視ループ停止 (cron 4d828eb7 を CronDelete)。a/b/c は同 tick で
クリーン合流済 (main `8982a4d4`)。

### lane d の 3 commits
- `70e6bdb9` feat(BG Thm E / Pf 8.17): faithful cover wiring — cover_card 実証 (issue 8021 gate 1 解消)
- `a16a7e93` Merge branch 'main' into d
- `6e8e1f70` feat(BG Cor 14.9): faithful cover identity — easy half + gated skeleton (gate 2 着手)

### 変更ファイル (3-dot `main...d`)
| ファイル | 所有 | 判定 |
|---|---|---|
| `OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting.lean` | d (BG/**) | ✅ 範囲内 |
| `OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean` | d (carve-out 0086: bgTheoremE carrier ブロック) | ✅ 範囲内 (hunk は line 488–660 = `BGTheoremECoverData` 構造 + `BGTheoremETypeICovering` + `bgTheoremE_cover_data` 定理) |
| **`OddOrder/Peterfalvi/S14_MaximalI.lean`** | **b** (S14_MaximalI = lane b 所有) | **⚠ 逸脱** |

### 逸脱の内容 (機械的・低リスク)

d は自所有の S10 carrier `BGTheoremECoverData` を **API リファクタ**した:
- 旧 `thickenedA1_card` フィールド → 新 `cover : ι → Set G` + `cover_card` フィールド
- `BGTheoremETypeICovering` に `cover_subset_kernels` フィールド追加 (旧 `thickenedA1` 直書きを置換)
- 動機: 旧 `thickenedA1 (M_i) (M_i)` の `(M_i)_F`-based kernel が per-`x` signalizer `(N[x])_F`
  (Pf (8.14)) と不一致 (issue 8021) → faithful BG cover `𝒞_G(M̃_i)` に差し替え。

この **breaking API change の consumer 更新**が b 所有 `S14_MaximalI.lean` の
`exists_typeICovering` に及んだ (34 行差分, `thickenedA1 (data.reps i) …` → `data.cover i`,
`data.thickenedA1_card` → `data.cover_card`, `thickenedSupport_subset_…` 手書き → `hTypeI.cover_subset_kernels`)。
新規 sorry・新規 axiom なし、純粋に carrier API rename の追従。

**現時点で b の pending 3 commits は S14_MaximalI を触っていない** (b は S07 + AxiomsCheck のみ) ので、
d の S14_MaximalI 編集を採れば b の現作業とは衝突しない。

## 裁定 (2026-06-29, ユーザー)

**判断 C — 恒久 carve-out 化** を採択。`exists_typeICovering` (S14_MaximalI line 2639–2798) の
**carrier-consumer 部分を lane d 所有**とする role split (b = covering math 8.13.c1/8.8.a 本体、
d = S10 carrier `BGTheoremECoverData` API 追従)。所有マップ更新済:
- `notes/meta/merge_monitor.md` 🔒 マップ + carve-out 0088 ブロック
- `notes/meta/ft_lane_reallocation_2026_06_28.md` carve-out 節

step 1.5: lane d が S14_MaximalI のうち `exists_typeICovering` のみ編集 → 逸脱としない。
これにより d の合流が解禁 → 監視ループ再開。

**恒久解 (本 issue は open 維持)**: carrier-consumer wiring を d 所有 helper 補題に抽出し
`exists_typeICovering` から cite する形にすれば、b/d が同一定理本体を共有編集する状態を解消できる
(将来 lane d の作業項目)。

## やること (= 判断待ち、裁定済)

- [ ] **判断 A — hub 承認の所有例外 (推奨候補)**: 過去の `[所有例外: hub 承認]` マージ
  (git log `c9e6a7bc`/`e28908aa` 等) と同様、d の S14_MaximalI consumer 更新を承認して d を
  `--no-ff` 合流 (build + sorry + axiom 検証通過なら)。最小手数・低リスク (機械的 rename 追従)。
- [ ] **判断 B — 再分割**: d は S10 carrier API change を backward-compat で出し、
  S14_MaximalI consumer 更新は b に委譲 (notes/issue で b へ依頼)。clean だが 2 レーン往復で遅い。
- [ ] **判断 C — 恒久 carve-out**: `exists_typeICovering` の carrier-consumer 部分を d 所有に
  carve-out (issue 0086/0087 と同型)。今後も carrier API 変更が consumer に波及するなら妥当。

## 完了条件

判断が下り、(A) なら d を合流 + push、(B/C) なら所有マップ (merge_monitor.md / 
ft_lane_reallocation_2026_06_28.md) を更新し該当レーンへ作業移譲。いずれも完了後に
**監視 cron を `13,43 * * * *` で再作成** (CronCreate) してループ再開。

## ⚖ 整合 (2026-06-29, hub): A と C の二重裁定 → **C を採択 (A を包含)**

lane d セッションと hub セッションが**独立にユーザーへ確認**し、別ラベルの裁定を得ていた:
- **lane d セッション → 判断 A** (hub 承認の所有例外、issue 8021 Option 1。下記 §「判断 A」)
- **hub セッション (本 tick, 後) → 判断 C** (恒久 carve-out。上記 §「裁定 (判断 C)」)

両者とも結論は「**d を今合流**」で一致。恒久 carve-out (C) は一回承認 (A) を**包含**する
(C ⊇ A) ため、最終採択は **C** とし所有マップを恒久更新済。lane d の A 裁定は「初回の越境を
承認」した記録として保持 (矛盾でなく、C がそれを恒久化した形)。lane d 側の「頻発するなら C へ
移行検討」という所見は、まさに本 tick で C に移行したことで解決済。

## (参考) lane d セッションの裁定 = 判断 A

**判断 A (hub 承認の所有例外) で確定** — lane d セッションの AskUserQuestion でユーザーが
「lane d が δ struct + lane-b consumer を 1 commit で実施 / 所有境界越えは過去の merge と同じ
hub 承認 (=ユーザー) 扱い」を明示選択 (issue 8021 の Option 1)。逸脱内容は機械的 carrier API
rename 追従 (新規 sorry・新規 axiom なし) ゆえ低リスク、判断 A の推奨条件を満たす。

**hub (main worktree) への依頼**: d を `--no-ff` 合流 (build/sorry/axiom 検証通過済 — lane d 側で
full build 3889 green 確認済) + 監視 cron `13,43 * * * *` 再作成。lane d worktree からは main の
checkout 不可ゆえ実マージは hub 側で実施。lane d はこの裁定後も S14_MaximalI の carrier-consumer
追従を継続する可能性があるため、頻発するなら判断 C (恒久 carve-out) への移行も検討余地あり
(現状は A で十分)。

その後の lane d commits (`5f962b5a` 以降) も同性質 (S14_TypePCounting = d 所有 + carrier API faithfulness 修正)。

## ✅ CLOSE (2026-07-02 3 レーン再編) — carve-out 解消、S14_MaximalI は全体 lane b

lane d 退役に伴い本 carve-out は**解消**。`exists_typeICovering` を含む `S14_MaximalI.lean`
**全体が lane b 所有** (merge_monitor 🔒 3 レーンマップ更新済)。恒久解 (carrier-consumer の
d 所有 helper 抽出) は不要化 — carrier 側 (S10) も a に fold されたため (issue 0086)、
今後の carrier API 変更は a→b の通常の cross-lane 通知 (notes/issue) で扱う。
(2026-07-02 hub、ユーザー委任レビュー)

## 参照
- 範囲逸脱検出 tick: main `8982a4d4` (a/b/c 合流済) の直後
- carve-out 先例: issue `0086` (S10 bgTheoremE carrier), `0087` (S07_RhoProjection)
- d の faithful cover 動機: issue `8021`
- 所有マップ正本: `notes/meta/ft_lane_reallocation_2026_06_28.md` / `notes/meta/merge_monitor.md`
