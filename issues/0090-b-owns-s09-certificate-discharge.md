---
id: 90
slug: b-owns-s09-certificate-discharge
title: "lane b owns S09_CertificateDischarge.lean (§7 (7.7.a) discharge infra carve-out)"
created: 2026-06-30
---

# lane b owns S09_CertificateDischarge.lean (§7 (7.7.a) discharge infra carve-out)

## 裁定 (ユーザー裁可 2026-06-30, hub tick)

`OddOrder/Peterfalvi/S09_CertificateDischarge.lean`（lane b が新規作成）は、ファイル名が
lane a の S09 namespace パターン (`S(0[3-9]|1[0-3])`) に掛かるが、**lane b 所有**として扱う
carve-out をユーザーが承認。step 1.5 範囲逸脱チェックで lane b がこのファイルを編集していても
**逸脱としない**（lane a がこのファイルを編集したら逸脱; lane b が他の S09 ファイル =
`S09_NonexistenceCertain.lean` 等を編集したら逸脱）。

## 根拠 (hub が merge tick で検証, genuine・非重複)

- S09 の `Hypothesis76.chiRho_decomp`（Pf (7.7.a)）は **opaque な structural certificate field**
  （未証明の posited Prop）。`S09_NonexistenceCertain.lean:101/1008-1010` 自身が「これを discharge
  するには CF(L,A) の induced/restricted-character decomposition theory が必要だが **this file には
  未だ無い**」と明記。
- lane b の新ファイルは**まさにその欠けている基盤**を供給: `induce_restrict_eq_index_smul`
  (Ind∘Res ψ = [L:K]·ψ, (7.7.a) spanning identity) / `eq_induce_restrict_of_supported`
  (CF(L,A) spanning) / `inner_self_eq_zero` / `eq_zero_of_mem_span_orthogonal`（直交性）。
- 以前削除された `S07_RhoProjection`（既存 chiRho 機構の**重複**、issue 0089）とは異なり、
  これは**重複でない genuine な不足インフラ**（[[s09-is-section7-chirho-complete]] の警告に該当せず）。
- lane b は衝突回避のため**別ファイルに隔離**済（lane a の `S09_NonexistenceCertain.lean` は不変）。
- FT 経路: S09 の opaque certificate を honest 化 → (7.7.a)/(7.8) coherence → lane b (12.16)
  `counterexample_contradiction` の §7 hard floor を支える。

## 経緯

lane b は commit `8b4f5b6b` で「§7 hard floor 解消に方向転換（ユーザー裁可、issue 1013）」と記録したが
issue 1013 は未起票・carve-out 未formalize だった。hub tick (2026-06-30) で範囲逸脱候補として検出 →
genuine・非重複を検証 → ユーザーが carve-out 承認。本 issue がその正式記録（issue 1013 を置換）。

## 完了条件 / 恒久解

carve-out は当面維持。恒久解の選択肢（将来）: (a) 現状維持（lane b 所有の S09_* ファイル）、
(b) `S07_*` 等 lane a namespace 外へ rename、(c) §7 discharge 完了後に S09 本体へ統合。
当面は (a)。

## 参照

- `OddOrder/Peterfalvi/S09_CertificateDischarge.lean`（対象ファイル）
- `OddOrder/Peterfalvi/S09_NonexistenceCertain.lean:101/1008-1073`（chiRho_decomp certificate）
- issue 0089（S07_RhoProjection 削除、重複ケース）、issue 0081（lane b (12.16)）
- `notes/meta/merge_monitor.md`（carve-out 0086/0088 と同列の所有マップ追記）
- 既存 carve-out: 0086 (S10 bgTheoremE carrier=d)、0088 (S14 exists_typeICovering=d)
