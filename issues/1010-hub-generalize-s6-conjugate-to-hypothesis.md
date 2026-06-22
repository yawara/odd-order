---
id: 1010
slug: hub-generalize-s6-conjugate-to-hypothesis
title: "HUB: §6 conjugate 補題群を Hypothesis46→Hypothesis に一般化 (§10 (5.8)/(10.6.a) unblock)"
created: 2026-06-23
---

# HUB: §6 conjugate 補題群を Hypothesis46→Hypothesis に一般化 (§10 (5.8)/(10.6.a) unblock)

## 背景

lane-b で Pf (10.6.a) の (5.8) full-column endgame を進める過程 (issue 1009) で確定した構造的
gate。§10 (5.8)/(10.6.a) は certain-type **column 用 `OrthonormalCharacterImageFamily`** を組む必要が
あり、その `image_eq` 材料 = **conjugate-column 恒等式** `(∑_i μ_ij).conj = ∑_i μ_ij'` を要する。

これは §6 `columnSum_conj_eq` (`(columnSum h χ₂).conj = columnSum h χ₂⁻¹`) そのものだが、§10 の muGrid
host は **`CertainTypeHypothesis` (`(hyp.toCertainTypeHypothesis hG hodd).toHypothesis : S06.Hypothesis ↥M`)**
であり、§6 の conjugate 補題群は全て **`Hypothesis46 A L`** 上で stated されている (構造階層
`Hypothesis46 extends CertainTypeHypothesis extends Hypothesis`)。**§10 用 `Hypothesis46` builder は不在**
ゆえ §6 補題を §10 host に直接適用できない。

**🔑 重要な事実 (lane-b 調査済)**: これら conjugate 補題群は **実際には `Hypothesis` レベルの構造しか使わない**
(`Hypothesis46` 固有の field = tic/dade0/tau/subH/A_covers を一切参照しない)。根拠:
- `chiColumn` / `sigma_chiColumn_eq_certainType` / `columnFamily` / `sdiffTICyclicHypothesis` /
  `toTICyclicHypothesis` は全て `S06_CertainTypeCharacters.lean` の `namespace Hypothesis` +
  `variable (h : Hypothesis L)` ブロックで定義 (= Hypothesis-level)。
- `W_odd` は `S06.Hypothesis` の field (`S06_DadeIsometryCertain.lean:89`)、`card_charGroup_W2` も
  Hypothesis-level。
- ∴ `certainType_mu_conj_bridge` (`sigma_chiColumn_eq_certainType` 経由) や `column_inv_ne_self`
  (`W_odd`/`card_charGroup_W2` 経由) は Hypothesis レベルで証明可能。Hypothesis46 で stated されているのは
  S06_CertainTypeConjugation.lean の working context が Hypothesis46 だっただけ。

## やること

- [ ] **§6 conjugate 補題群の `(h : Hypothesis46 A L)` を `(h : Hypothesis L)` に一般化** (証明本体は不変、
  binder 型のみ変更):
  - `S06_CertainTypeConjugation.lean`: `certainTypeOmegaSigma_conj` / `rowInv` / `rowInvEquiv` /
    `w1CharEquiv_rowInv` / `rowInv_rowInv` / `omegaProdCharTic_inv` / `certainTypeOmegaSigma_conj_eq` /
    `chiColumn_conj` / `sigma_chiColumn_conj` / `certainType_mu_conj_bridge` / `certainType_mu_conj_eq` /
    `certainType_columnSum_conj` / `column_inv_ne_self` / `certainType_columnSum_conj_ne`
  - `S06_CertainTypeCoherence.lean`: `columnSum_conj_eq` (`certainTypeR` の image_eq で使用; これ自体は
    Hypothesis46 のままでよいが `columnSum_conj_eq` は Hypothesis 化が望ましい)
- [ ] **caller の修正** (signature 変更で `h46` → `h46.toHypothesis` が必要になる ~15 箇所): §6 内
  (`certainTypeR` 等) + `S08_CaseBEnumeration.lean` (多数) / `S08_CaseBCoherence2.lean:1853-1855` /
  `S08_CaseBWeightedEndgame.lean:375-379`。dot-notation の defeq で `h46.toHypothesis.columnFamily =
  h46.columnFamily` ゆえ rw は通るはず (要 build 確認)。
- [ ] AxiomsCheck の登録名 (`certainType_mu_conj_eq` 等 4 件、`AxiomsCheck.lean:912-922`) は不変。
- [ ] full build + AxiomsCheck green 確認。

## 完了条件

§6 conjugate 補題群が `Hypothesis L` を取る → lane-b が S12 の §10 muGrid host
(`(hyp.toCertainTypeHypothesis hG hodd).toHypothesis`) に直接 `columnSum_conj_eq` /
`column_inv_ne_self` を適用でき、§10 conjugate-column 恒等式 (issue 1009 の column image family の
`image_eq` 材料) が組める。build-green。

## 代替案 (hub 判断用)

1. **(推奨) §6 を Hypothesis に一般化** (本 issue): 1 回の機械的 refactor で全 §10 column 機構
   (conjugate + certainTypeR image family + ν=certainTypeExtension) が解禁。
2. **lane-b が S12 内で chain を Hypothesis レベルに複製**: ~200 行の重複 (chiColumn_conj/
   certainTypeOmegaSigma_conj 等 deep chain も要複製)、DRY 違反、§6 一般化で将来 orphan 化。非推奨。
3. **§10 `Hypothesis46` 組立** (route A): tic(在)/dade0/tau/subH/A_covers/tic_W1-W2-V proofs を
   §10 type-P から供給。大物 multi-session だが conjugate + ν + certainTypeR + 2D σ-structure を
   一気解禁。§6 凍結を崩さない利点。

→ hub の判断を仰ぐ。1 が最小コストの unblock。lane-b は hub 解決まで (10.6.a) の image-family 段は保留
(column-independence `muColumn_tau1_diff_eq` までは landed = issue 1009)。

## 参照

- issue 1009 (Pf (10.6) summed isometry; 本 gate の発生源、column-independence landed)。
- §6 conjugate: `OddOrder/Peterfalvi/S06_CertainTypeConjugation.lean`、
  `S06_CertainTypeCoherence.lean:621` (`columnSum_conj_eq`)。
- §10 host: `S12_MaximalIII_IV_V.lean` `Hypothesis.muGrid` (`(hyp.toCertainTypeHypothesis …).toHypothesis`)。
- 構造階層: `Hypothesis46` (`S06_CertainHypothesis46.lean:39`) extends `CertainTypeHypothesis`
  (`S06_DadeIsometryCertain.lean:469`) extends `Hypothesis ↥L`。
- notes: `notes/peterfalvi/s12_s10_character_bridge.md` 更新¹⁰。
