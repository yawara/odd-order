---
id: 91
slug: hub-b-weakens-hypothesis78-nu-isometry
title: "HUB: lane b の Hypothesis78.nu_isometry global→family 弱化 (cross-lane, ユーザー裁定=受理)"
created: 2026-07-01
---

# HUB: lane b の Hypothesis78.nu_isometry global→family 弱化 (cross-lane, ユーザー裁定=受理)

## 経緯

2026-07-01 hub 監視 第1 tick で lane b commit
`ea61e2a4 feat(Pf §7): weaken Hypothesis78.nu_isometry global→family (§12-bridge interface)`
を検出。**lane a 所有の `OddOrder/Peterfalvi/S09_NonexistenceCertain.lean`** の
`Hypothesis78` 構造フィールド `nu_isometry` を改変:

- **before (global)**: `∀ φ ψ : CF(L), ⟨ν φ, ν ψ⟩ = ⟨φ, ψ⟩`
- **after (family)**: `∀ i j, i ≠ ind1H → j ≠ ind1H → ⟨ν ζᵢ, ν ζⱼ⟩ = ⟨ζᵢ, ζⱼ⟩`

これは三重該当ゆえ hub は STOP + ユーザー裁定に回した:
1. **範囲逸脱** (step 1.5): `S09_NonexistenceCertain.lean` は lane a 所有。carve-out 0090 は
   `S09_CertificateDischarge.lean` のみ許可。
2. **signature contract 無断改変** (STOP 条件 d): `Hypothesis78` は §7→§12→§16 チェーンの interface。
3. **lane b 自身の issue 1013 charter 違反**: 「S09 を直接編集せず新ファイルで certificate proof」と明記。

## 裁定 (ユーザー 2026-07-01) = 受理して合流 (full build 検証後)

理由:
- Peterfalvi の coherent isometry ν は族 S の ℤ-span 上でのみ定義され、CF(L) 全体への global
  拡張は次元不整合 (dim CF(L) > dim CF(G)) で一般に存在しない。§12 producer
  (`exists_counterexample_dade_data`) が供給できるのは family isometry のみ。
- global 版を残すと (12.16) が構成不能 or `Hypothesis78` が unsatisfiable (下流 vacuous,
  scaffold 化) になる懸念。**family 版が Peterfalvi 忠実版** (soundness 修正)。
- hub が trial-merge + full build (`lake build OddOrder OddOrder.AxiomsCheck` = 3889 jobs
  green, AxiomsCheck OK, sorry ground-truth 107 不変) で下流無破壊を確認。
- 変更は両 S09 file (`S09_NonexistenceCertain` の field + `S09_CertificateDischarge` の
  constructor/helper 群) で一貫した意図的リファクタ。

## 影響 (lane a / lane c への通知)

- **lane a (owner)**: `Hypothesis78.nu_isometry` は現在 **family-form**。field は引き続き lane a 所有。
  派生定理 `nu_zeta_inner_self_eq_one` / `nu_zeta_inner_self_eq_one_of_irreducible` は
  `hi : i ≠ ind1H` 引数を追加取得する形に変更済 (S09_NonexistenceCertain 内で consistent)。
- **lane c (consumer)**: 14.11 h78 / (12.16) hB が cite する `Hypothesis78` interface が family-form に。
  field `nu_isometry` を直接 cite する箇所は現状なし (S09 内のみ)。global 内積保存を前提にした
  証明があれば family + support 直交で再構成が要る (full build では該当破綻なし)。

## 今後の規律

- 本件は **一度限りのユーザー承認 cross-lane 編集**。**standing carve-out ではない**。
  以後 lane b が `S09_NonexistenceCertain.lean` を編集したら**通常通り逸脱→STOP**。
- `Hypothesis78` field の今後の変更要求は **HUB issue 経由** (lane a が自ファイルで変更 or hub 裁定)。

## 状態

- [x] ユーザー裁定 = 受理
- [x] full build 検証 green (3889 jobs, sorry 107 不変)
- [x] 合流 commit (この issue と同 commit)
