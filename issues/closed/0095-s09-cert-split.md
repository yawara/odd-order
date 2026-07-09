---
id: 95
slug: s09-cert-split
title: "S09_CertificateDischarge.lean split (2696 行 >1500) — 凍結境界で prefix-split"
created: 2026-07-01
---

# S09_CertificateDischarge.lean split (2696 行 >1500) — 凍結境界で prefix-split

## 背景

`OddOrder/Peterfalvi/S09_CertificateDischarge.lean` が merge-monitor のサイズ watch
(粒度規約 1,500 行) を超過。2026-07-01 の lane b 合流 (`7bd1b774` Pf 7.8.a/12.16 hzeta0nu
discharge) 時点で **2696 行**。merge_monitor.md 手順 4 に従い flag + 起票。

本ファイルは lane b が新規作成した §7 (7.7.a) CF(L,A) spanning 基盤 = S09 の opaque
`chiRho_decomp` certificate discharge インフラ (carve-out [0090](0090-b-owns-s09-certificate-discharge.md)
で lane b 所有)。lane b の active frontier。

## やること

- [ ] §7 certificate-discharge のクラスタが proof レベルで凍結したら、凍結済 helper 群
      (線形代数 core `inner_constOne_eq_zero_of_orthonormal_pair` 等 + coherence transport 基盤)
      を上流 `S09_CertificateDischargeCore.lean` へ prefix-split し、active frontier を leaf に残す。
- [ ] 分割の実施 owner = hub。lane b の frontier と衝突しない凍結境界で切る。
- [ ] split 後 `OddOrder.lean` の import が root closure を保つことを確認 (手順 3b)。

## 完了条件

`S09_CertificateDischarge.lean` (および分割後の各ファイル) が 1,500 行以下になり、full build +
AxiomsCheck green を維持。

## 参照

- merge_monitor.md 手順 4 (サイズ watch)
- lane b 所有 carve-out: [0090](0090-b-owns-s09-certificate-discharge.md)
- 同種 deferred split issue: [0075](0075-s15-sandt-split.md), [0079](0079-feitthompson-split.md), [0084](0084-s14-maximali-split.md), [0094](0094-s15-setup-split.md)

## 完了 (2026-07-09)

dir 化分割を実施 (issue 0103 方式、lean_split.py による機械分割 + 宣言/namespace 文脈/sorry 保存検証 + full build green):
  - CoherenceFormula.lean (2368 行)
  - FrobeniusFamily.lean (2586 行)
  - Hypothesis71.lean (1005 行)
  - NormalCase.lean (456 行)
  - TwoFamilies.lean (537 行)
