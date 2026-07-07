---
id: 9072
slug: typep2-dade-base-missing
title: "char-core prerequisite: T-side type-P₂/III Dade isometry base (FTtypeP_coh_base) missing — blocks Pf 14.9 coherence"
created: 2026-07-07
---

# char-core prerequisite: T-side type-P₂/III Dade isometry base (FTtypeP_coh_base) missing — blocks Pf 14.9 coherence

**起票者**: lane c (ユーザー「C レーン再開」+「見落としタスクは hub に報告」)。**判断者**: hub / char-core lane。
**種別**: cross-lane prerequisite (char-core §4/§5 Dade)。

## 背景 (2026-07-07 lane c, 徹底調査で root-cause 確定)

C の (14.9) char body `T_typeIII_ratio_le` (`S16_NonExistenceG.lean:906`) の唯一の実質的残 carrier =
**`calT1` coherence**。coherence engine 自体は proven: `T_typeIII_calT1_coherent` (`:704`) は
`S07.coherent_of_constant_degree` に正しく還元し、in-lane part (`hirr`/`hdeg`/`hSfin`/degree-p/count
`T_typeIII_calT1_card_eq`) を全て ungated で discharge 済み。**唯一 sorry ゆえん = 入力
`hyp07 : S07.Hypothesis calT1_set A` (T-side type-P Dade package) の構築**。

### root-cause: T-side type-P Dade isometry base が repo に不在 (char-core gap)

- **`hyp.base.tauT` (`S15_SAndT_Setup.lean:178`) は property 0 個の bare free field**。対照的に `tau3`
  (`:203`) は直後に ~15 property field (`tau3_isometry` 等)。`tauS`/`tauT` は isometry/ZIrr/support 一切なし。
  instantiation site (`FeitThompson.lean:2587`) では **`tauT := 0`** (placeholder) or opaque threading。
  ⟹ `tauT` は Dade map として機能しない。
- **type-P Dade support builder `dadeSupportHypotheses_typeP` (`S10_MinimalSimpleStructure.lean:2451`) は
  `IsTypeP1 M` gated** — type-P₁ (`A(M)=(M')^# =M_σ^#`) のみ扱い、**type-P₂/type-III 版が存在しない**。
  これが docstring の「from-scratch §4/§5 build with no existing type-P Dade base」= Coq `FTtypeP_coh_base`。
- S07.Hypothesis の 7 field (`S07_Coherence.lean:1767`) の内、Dade map に依存する `tau`/`tau_isometry_diff`
  /`difference_image`/`difference_images_orthogonal` + 別 hyp `hZIrr` は**全て concrete Dade map の定理**
  (S14 型-I は `hyp.dadeData.dade` = genuine Dade isometry から `dadeIntegralCharacterMap_*` で discharge)。
  contentless `tauT` では posit するしかなく gated。**在庫 assembler `irrSubcoherent` (`S07_Subcoherent.lean:148`)
  は τ + per-member Rdatum + hiso を与えれば 1-shot で package 可能** ⟹ 欠けているのは **concrete τ とその
  difference-image/isometry data** のみ = type-P₂/III Dade base。

### settled cross-lane verdict と整合

- **issue 4001** (2026-06-30 HUB): base `Hypothesis` は意図的に非対称 (`Sdata : TypePData S` あり、**Tdata
  なし** — T は larger-κ で type-P₂ とは限らない、`FeitThompson.lean:276`)。Tdata 入力 carrier 追加は
  design 違反/dead-end と裁定済み。
- **issue 9013**: T-side residual (v-value + Dade package) = lane-b §13 char cascade gated。
- **note `s16_w4_char_cascade.md`**: common bottom-out = "concrete §3/§4 Dade-isometry construction +
  (7.5) Frobenius/TI norm formula (repo unimplemented)"。

## やること

- [ ] char-core lane (or hub 裁定) が **type-P₂/III Dade support base** を build する:
  `dadeSupportHypotheses_typeP` を type-P₁ 専用から一般 type-P (P₂/III 含む) に拡張、または T-side 専用の
  `DadeSupportHypothesisData T` を新設 (Coq `FTtypeP_coh_base` 相当、PFsection14)。
- [ ] それを `hyp.base.tauT` に genuine Dade map として供給 (現 `tauT := 0` free field を実構成に置換)、
  または C が cite 可能な形で export。

## 完了条件

char-core lane が type-P Dade base を landing → C が `irrSubcoherent` で `hyp07 : S07.Hypothesis calT1_set A`
を構築 → `T_typeIII_ratio_le` (`:942` sorry) の coherence carrier を close (残 carrier = v=|V| (13.12 d=1) +
S-side βₛ bridge + norm)。

## 参照

- `OddOrder/Peterfalvi/S16_NonExistenceG.lean:704` (`T_typeIII_calT1_coherent`, proven engine),
  `:906`/`:942` (`T_typeIII_ratio_le` + sorry call site)
- `OddOrder/Peterfalvi/S07_Coherence.lean:1767` (`S07.Hypothesis`), `S07_Subcoherent.lean:148` (`irrSubcoherent`)
- `OddOrder/Peterfalvi/S15_SAndT_Setup.lean:178` (`tauT` free field), `:819` (`dadeHypS`, S-side genuine base)
- `OddOrder/Peterfalvi/S14_MaximalI.lean:153` (type-I genuine Dade map pattern)
- `OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean:2451` (`dadeSupportHypotheses_typeP`, IsTypeP1-gated)
- 関連: issue 4001 (Tdata 非対称裁定), 9013 (T-side residual), 9000 (typeP_Galois), note `s16_w4_char_cascade.md`
