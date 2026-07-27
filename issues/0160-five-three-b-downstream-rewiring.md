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

### ✅ (1) 完了 (2026-07-27)

* **type-P / type-II の 2 件は置換した** (`c3d9db3db`)。`h46.dade0` / `h46.tau` は定義的に一致し、
  supported 条件は「`α` が `K^#`-supported ⟹ `K` の外で消える」へ素直に落ちた。
  各 ~25 行の重複証明が 1 行の呼び出しに (net −43/+28)。
* **Sibley 版は置換しない (数学的に別物)**。`SibleyDadeHypothesis.dade` は
  `S04.Hypothesis G (sharpImage H) L` で台が `H^#` のみ ⟹ `V` は**その外**にあり
  base point が無い。像が消えるのは「Dade 台の外だから」で、一般版の
  「base point 評価 → `α(v) = 0`」とは逆向きの理由。両者は相補的で冗長でない。
  ⟹ `ConstituentPinning.lean` の docstring に理由を明記した (0160 の完了条件どおり)。

## (2) `S13_SixTwoImageData.inducedFamilyImageData` — ⚠ 「置換」は誤った形 (2026-07-27 実測)

実測の結果、**当初の文言どおりの「本構成の特殊化に置換」はやってはいけない**と判明した。

* 構造は確かに同じ: `S13.memberRFamily` = `if IsIrreducibleCharacter χ then irrRFamily
  else colRFamily` で、`S06.memberR` の dispatch と 1:1。族も
  `inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥` = **広い方** (`θ ≠ 1_K`) なので、
  受け皿は `toGeneralHypothesis` (parametrized engine) の側で正しい。
* **しかし可約分岐が別物**: `colRFamily` は `columnImageFamilyCohFree`
  (`S12_MaximalIII_IV_V_Core/DadeCalculations.lean:139`) 経由で
  `imageSet := Finset.univ.image (hyp.columnRImage hG hG.odd params.delta j j')` を持つ。
  すなわち **`alignedOmegaSigmaGrid` + `params.delta` で符号を pin した族**であって、
  `certainTypeR` の生の `certainTypeRImage` (符号 = `(columnFamily χ₂).sign`) ではない。
* 下流 ((5.5) / (9.11) の column-pair adjunction 等) は **aligned な形を読む**。
  `S06.columnR` に置き換えると `imageSet` が生の σ-grid に変わり、その情報が失われる
  ⟹ **lossy な refactor**。「重複」ではなく、§13 側が符号 pin という**追加内容**を持っている。

### ⟹ 正しい成果物は「置換」でなく **bridge 定理**

両者が同じ member の (5.2.d) 族であることを、`imageSet` の一致として述べる定理を足すのが正しい:

```
S13.memberRFamily … hχ |>.imageSet = (S06.memberR … hχ).imageSet
```

材料は在る: **`S13.certainTypeOmegaSigma_muColumnChar_eq_aligned`**
(`S13_Orthogonality.lean:298`) が σ-grid ↔ aligned grid を繋ぎ、符号側は `hδj`
(`muColumnSign j = params.delta`) が担う。列添字の同定 (`j` ↔ `χ₂`) は
`S12.Hypothesis.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` +
`S06.columnSum_injective` (0159 で新設) から。

⚠ 下流は**書き換えない** — bridge は関係の記録であって、置換ではない。

## 完了条件

重複が実際に減る (個別証明が一般版の呼び出しに置換される) こと。build green +
AxiomsCheck OK + lint --strict clean。置換が数学的に不可能と判明した箇所は、
**理由を docstring に書いて残す** (「一般化できない」で終わらせない)。
