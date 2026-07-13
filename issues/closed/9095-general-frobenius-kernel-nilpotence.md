---
id: 9095
slug: general-frobenius-kernel-nilpotence
title: "Audit: general Frobenius kernel nilpotence is not a new lane-a claim"
created: 2026-07-14
---

# Audit: general Frobenius kernel nilpotence is not a new lane-a claim

## 背景

Issue 0044 の (7.10) assembly 再開時、各 Frobenius kernel の nilpotence を新規 claim として起票した。
一般定理は Thompson normal-complement theorem を経由し、既存 issue 0031 が canonical owner である。
Coq `PFsection7.v` は Thompson theorem を避けるため各 `L_i` の solvability を明示仮定している。
FT consumer の kernel は `maxNilpotentNormalHall` であり、既存定理から nilpotence を直接構成できる。

## やること

- [x] owner・Coq仮定・FT-specific nilpotence supplyを確認し、新規shared claimではないと判定した。

## 完了条件

重複 claim を残さず、issue 0044 を per-member nilpotence 入力の S09 assembly として進める。

## 参照

- issue 0031; issue 0044; `coq/theories/PFsection7.v`; `S15_MF/SetupLemma151.lean`; `S14_MaximalI/TypeICovering.lean`
