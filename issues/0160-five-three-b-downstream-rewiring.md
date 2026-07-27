---
id: 160
slug: five-three-b-downstream-rewiring
title: "Pf (5.3)(b) の下流再配線と anchor dedup (0159 follow-up)"
created: 2026-07-27
---

# Pf (5.3)(b) の下流再配線と anchor dedup

[issue 0159](closed/0159-five-three-b-general-hypothesis.md) で **(5.3)(b) 本体 + rider** が
`S06_CertainTypeSubcoherent.lean` に (4.6) 一般・sorry-free・axiom-clean で landing した。
本 issue はその**下流側の整理**(0159 の完了条件外だった 2 件)。

## (1) anchor の 3 サイトを一般版の特殊化へ寄せる

`S06.dadeICM_apply_eq_zero_of_mem_ticVdiffV` (2026-07-27) が
「`A₀`-supported かつ `K` の外で消える `α` の (4.6) Dade 像は `V` 上で消える」を一般に述べる。
既存の 3 個別証明はその特殊化にあたる:

| サイト | 定理 | 備考 |
|---|---|---|
| type-II §12 | `S12.typeII_tau_apply_eq_zero_of_mem_ticVdiffV` (`S12_TypeIIFrobenius.lean:384`) | **同じ経路** (base-point 評価)。`α` の消滅条件が `v ∉ S'` 経由なので、一般版の `v ∉ K` 版へ橋渡しが要る |
| type-P §13 | `S13.tau_apply_eq_zero_of_mem_typePV` (`S13_MaximalIII_IV.lean:90` 付近) | 同上 |
| Sibley §8 | `S08.tau_apply_eq_zero_of_mem_ticVdiffV` (`S08_CaseBCoherence2/ConstituentPinning.lean:684`) | ⚠ **別の Dade datum** (`SibleyDadeHypothesis.tau`、`h46.dade0` ではない) ゆえ一般版がそのまま被らない。`hyp.dade_H_eq_bot` 経由の現行証明を残すか、両者を結ぶ補題が要るかを先に判定すること |

⟹ 着手手順: まず type-II / type-P の 2 件が一般版で置換できるか (支持集合の条件が
`v ∉ K` に落ちるか) を実測。Sibley は上記の理由で別途判断。

## (2) `S13_SixTwoImageData.inducedFamilyImageData` を本構成の特殊化へ

`S13_SixTwoImageData.inducedFamilyImageData` は §12 hypothesis から `InducedFamilyImageData`
を組む消費点で、実質 (5.3)(b) の §11 instance。`S06.toGeneralHypothesisOfInducedFamily` /
`memberR` に載る見込み (§13 側は 2 元固定でなく一般族を持つ)。

⚠ 3 サイトの再配線を伴うので、(1) と同じく**着手前に実測**すること
([[verify-port-state-by-number-not-coq-name]])。

## 完了条件

重複が実際に減る (個別証明が一般版の呼び出しに置換される) こと。build green +
AxiomsCheck OK + lint --strict clean。置換が数学的に不可能と判明した箇所は、
**理由を docstring に書いて残す** (「一般化できない」で終わらせない)。
