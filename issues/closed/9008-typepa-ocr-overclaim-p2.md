---
id: 9008
slug: typepa-ocr-overclaim-p2
title: "typePA=(M')# is an OCR-error over-claim for type-P2; correct A(M)=⋃_{x∈M_σ#} C_{M'}(x)#"
created: 2026-07-04
---

# `typePA = (M')#` は type-P2 で over-claim（mmd の OCR 誤り由来）

## 結論（先に）

lane-b の loop¹⁰⁷–¹⁹³ が「deep type-P2 K-structure geometry」として追っていた
`dadeSupportHypotheses_typeP` の **P2 sorry 2 本（S10:2496 typePA0 / S10:2504 typePA）は、
false-as-stated かつ consumer 0 の over-claim** であり、埋めるべき deep geometry は**存在しない
（phantom）**。原因は **Peterfalvi (8.10) の mmd 抽出の OCR 誤り**：本文 `⋃_{x∈M_s#}`（core = M_σ#）が
`.mmd` で `⋃_{x∈M#}` に化けており、それを基に `typePA` が `(M')#` と定義されている。

- **PDF 確認済**（`references/peterfalvi/pdf/04.10_...pdf` p.47, (8.10)）:
  > If M is of type 𝒫, set **A(M) = ⋃_{x∈M_s#} C_{M'}(x)#** and A₀(M) = A(M) ∪ V^M.

  ここで `M_s = H` (type I/II/V) / `M'` (type III/IV)。`M_s = M_σ`（(8.11) ref [BG] Prop 16.1）。
- **`.mmd` (`04.10:117`) の抽出**: `A(M)=\bigcup_{x\in M\#}C_{M'}(x)^{\#}` ← 添字 `s` が脱落
  （`M_s#`→`M#`）。type-I 側は `\bigcup_{x\in H\#}` と正しく出ており、type-P だけ落ちた。

## 正しい A(M) と Lean の乖離

| | Peterfalvi 本文 (8.10) | mathcomp `FTsupport` | Lean `typePA` (現状) |
|---|---|---|---|
| type-P `A(M)` | `⋃_{x∈M_σ#} C_{M'}(x)#` | `⋃_{x∈'A1=M_σ#} 'C_{M'}[x]#` | `(M')#` (`centralizerSupport (sharpSubgroup M) (derivedInG M)`, 添字 M#) |

- **集合として** `⋃_{x∈M_σ#} C_{M'}(x)# = { a∈(M')# | C_{M_σ}(a) ≠ 1 } = (M')# ∩ hatMsigma`。
  σ'-元 `a∈(M')#` で `C_{M_σ}(a)=1` のもの（＝ Frobenius 補元 U# 系）を**除外**する。
- **P1（type III/IV/V, `M_σ=M'`）では一致**: `M_σ#=(M')#` ゆえ両者とも `(M')#`。**現 typePA は P1 で正しい**。
- **P2（type II, `M_σ=M_F=H ⊊ M'`）で乖離**: type II は `C_H(U)=1`（U は H 上 Frobenius 補、
  `maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2` で `M_σ=H`）ゆえ `U#⊆(M')#` は
  `C_{M_σ}(a)=1` → 正しい A(M) から**除外**されるが、現 `typePA=(M')#` は**含む**。

## なぜ P2 sorry は埋まらない（false-as-stated）

`DadeSupportHypothesisData M (typePA M data)` は engine
(`dadeSupportHypothesisData_of_subset_escaping_sigmaSharp`) 経由で **escaping 点 → σ-sharp**
(`hXesc`, = Pf (8.13.b)) を要求する。だが `typePA=(M')#` の U#-元は
- **escaping し得る**（type II: `normalizer_not_le : ¬N_G(U)≤M`、U-系は M を出る）、かつ
- **σ-sharp でない**（`a∉M_σ`）。

∴ (8.13.b) が破れる → hypothesis は**偽**。mathcomp は `'A(M)` を `⋃_{x∈M_σ#}`（U# を除外）と
定義することでこの問題を回避しており、**mathcomp の (8.13) `FTsupport_facts` は `X:='A0(M)`
（= 小さい方 ∪ V^M）に specialize** して `D ⊆ 'A1(M)` を証明する（`(M')#` では**証明していない**）。

**逆に、typePA を正しい `⋃_{x∈M_σ#}` に直すと P2 escape は type-I と同一の ASet bridge で証明可能**:
escaping `a` ⟹ `a∈hatMsigma∩(U⊔M_σ)=ASet M U`、`a∉M_σ` ⟹ `theoremB_A_minus_Msigma_isTISubset`
(TI) ⟹ `C_G(a)≤M` 矛盾。**「deep type-P2 geometry」は不要**だった。

## consumer 精査（P2 は消費されていない）

- `dadeSupportHypotheses_typeP` (S10:2466): **live caller 0**（自宣言のみ）。
- 唯一の intent consumer = `S12_MaximalIII_IV_V_Core.Hypothesis.dadeData`
  (`DadeSupportHypothesisData M (typePA0 M typeP)`), `type_alt : IsTypeIII∨IsTypeIV∨IsTypeV` = **P1 限定**。
- type-II (P2) の Dade は `Section16CharacterData.A0S : Set ↥S`（抽象集合、S15）で、
  `S15_SAndT_Setup:408` に **"S-side maximal-coherent Dade route (tauS/Sset/A0S) is off the FT path"**、
  `FeitThompson:1739` に **"Vestigial fields ... carry honest placeholders (∅,0)"**。typePA0 経由でない。

⟹ **P2 の typePA0/typePA Dade support を必要とする on-path consumer は存在しない。**

## やること

- [x] **Option B（narrow, 採用）**: `dadeSupportHypotheses_typeP` に `hP1 : IsTypeP1 M` を追加し、
  P2 の 2 sorry を削除（by_cases 崩壊、P1 branch は既 proven）。typePA 定義は**据置**（P1 で正しく、
  consumed は全て P1）。typePA の docstring に「= A(M) は P1 限定; P2 は `⋃_{x∈M_σ#}` が正」と明記。
  S10 のみ変更、live caller 0 ゆえ cross-lane 破壊なし。
- [ ] **hub 裁定待ち**: 下記「hub への確認事項」。

**Option A（deep, 見送り）**: `typePA` 定義を `centralizerSupport (sharpSubgroup (Msigma M)) (derivedInG M)`
に訂正。P1 値不変・P2 で正しく縮小し P2 sorry も証明可能になるが、(1) `typePA_eq_sharpSubgroup_derivedInG`
が P2 で偽になり ~6 cite（S10 自 + S12 lane-a）を P1-conditional 化要、(2) 訂正後の type-P2 Dade support
は**現状 consumer 0**（type-II char は A0S 抽象/vestigial）ゆえ FT 前進ゼロ。→ hub 裁定で必要と判れば実施。

## hub への確認事項

1. type-II (S) の Dade isometry が将来 `DadeSupportHypothesisData S (正しい A(S))` を**実際に必要とするか**
   （S15/S16 の S-side が vestigial のままか、honest 化で typePA-Dade を消費するか）。必要なら Option A の
   typePA 定義訂正を実施（cross-lane cite 更新込み、lane-a S12 と協調）。不要なら Option B で確定。
2. 現状 lane-b の char/support frontier は本件で **確定的に枯渇**（loop¹⁹² 精査 + 本 OCR 訂正で
   type-P2 phantom 解消）。残 on-path は §8 III/IV (BG§14-15 gate) / (7.9)(11.8) (lane a gate) のみ。
   次配分を要検討（9003 の frontier map 更新済）。

## 完了条件

Option B landing + build green（S10 の P2 sorry 2 本消滅、typePA docstring 訂正）。hub が確認事項 1 に
回答 → Option A 要否確定で closed。

## 参照

- PDF: `references/peterfalvi/pdf/04.10_pp_44_49_...pdf` p.45-47（(8.4)-(8.13)）
- mmd OCR: `references/peterfalvi/04.10_...mmd:117`（`M#` ← 正 `M_s#`）
- mathcomp: `coq/theories/BGsection16.v:184-209`（FTcore/FTsupport 定義）, `PFsection8.v:555-576`
  (`FTsupport_facts` = (8.13), `X:='A0(M)`)
- Lean: `GroupTheory/MaximalSubgroupType.lean:301`（typePA 定義）,
  `S10_MinimalSimpleStructure.lean:2466`（dadeSupportHypotheses_typeP）
- 関連: 9003（type-P2 の従来 gate map）, [[ft-settled-findings]]（type-II support の over-claim 系列:
  typeII_A_sets_TI / typeI_or_typeII_centralizer_unique / 15.7(c)）

## ✅ HUB 裁定 (2026-07-04, cron tick): 確認事項 1 = Option B で確定 (Option A 不要)

hub 検証で b の「S-side type-II Dade は off-path/vestigial」を確定:
- `S15_SAndT_Setup:408` (2026-07-02 hub ruling): S-side maximal-coherent Dade route (tauS/Sset/A0S) は
  **off the FT path**、carrier は tauS=0 placeholder を供給、spine は消費しない。§13/§16 矛盾は W-side grid
  `eta = τ₃∘ω` 経由。
- `FeitThompson:1739`: vestigial fields (Sset/Tset/A0S/A0T/tauS/tauT) は honest placeholder (∅/0)、
  FT critical path 非消費。
- `dadeSupportHypotheses_typeP` の live consumer = `S12_MaximalIII_IV_V_Core` (type III/IV/V = P1) のみ。P2 consumer 0。

⟹ **正しい A(S) を必要とする on-path consumer は存在せず、将来も (S-side vestigial 設計が standing) 生じない
→ Option A (typePA 定義訂正) は不要。Option B (IsTypeP1 narrow, 実施済 `cefdfc3b`) で確定・close 可**。
将来 S-side を honest 化 (W-side restate でなく) する設計変更が起きた場合のみ Option A を再検討 (その時は
本 issue を re-open)。→ **本 issue は Option B landing + build green で解決済 (sorry 118→115 の一部)**。

## 📋 確認事項 2 (lane-b frontier 再配分) は 9003 で継続

lane-b の char/support frontier は本 OCR 訂正で type-P2 phantom が解消し**確定的に枯渇**。残 on-path =
§8 III/IV (BG§14-15 gate) / (7.9)(11.8) (lane a gate) / §12 endgame (Cluster A gated + DadeNotation
de-scaffold 設計判断)。次配分は 9003 の frontier map + hub/ユーザー裁定で継続。

## ✅ CLOSED (2026-07-04, lane b): hub 裁定どおり Option B で確定

hub 裁定「Option A 不要・Option B (cefdfc3b) で確定・close 可」を受けて close。type-P2 phantom は
解消、fix は main 取り込み済 (b2c5e25a)、build green。frontier 再配分 (確認事項 2) は 9003 で継続。
