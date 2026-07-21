---
id: 3023
slug: dedup-nonti-rederivation
title: "isTypeI_of_isTypeF / isTypeV_of_isTypeP1 の非TI分岐再導出を 15.7(e) の cite に置換"
created: 2026-07-19
---

# isTypeI_of_isTypeF / isTypeV_of_isTypeP1 の非TI分岐再導出を 15.7(e) の cite に置換

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 背景

issue 3022 で BG Thm 15.7(e) を Coq 同形の `fitting_not_ti_structure_e`
(`S16_MainResults/FittingNonTITrichotomy.lean`) として形式化した。しかし既存の下流 2 定理は
**(e) を cite せず非TI分岐を自前で再導出している** (3022 着手前からの状態; 3022 では
「既存定理を一切変更しない」方針を取ったため手を付けていない)。

| 定理 | 所在 | 現状 |
|---|---|---|
| `isTypeI_of_isTypeF` | `S16_MainResults/TypeP1Criteria.lean:840` | 非TI分岐で witness を自前 obtain し、rank=2 分岐と exponent/cyclic 分岐を再導出 |
| `isTypeV_of_isTypeP1_mf_eq_msigma` | `S16_MainResults/TypeVSinger.lean:395` | 同上。`\|W₁\| ∣ p−1` で場合分けし (e2)/(e3) を再導出 |

いずれも sorry-free・axiom-clean で**正しい**ので緊急性は無い。重複の解消は
maintainability の改善 (同じ数学が 2〜3 箇所に分岐して将来ずれる risk を消す)。

## やること

- [ ] `isTypeV_of_isTypeP1_mf_eq_msigma` の非TI分岐を
      `typeP1_kappaHall_dvd_sub_one_or_singer_of_not_fittingIsTI` (`TypeVSinger.lean:602`) の
      cite に置換。両者は同じファイルに在り、後者は前者の場合分け (`\|W₁\| ∣ p−1`) の
      refinement (含意 `K* = Z₀ → \|K\| ∣ p−1` で切る) なので、置換は
      「refinement の左枝から元の弱い枝を導く」だけで済むはず。
- [ ] `isTypeI_of_isTypeF` の非TI分岐を `fitting_not_ti_structure_e` の cite に置換。
      ⚠ **import 方向に注意**: `FittingNonTITrichotomy` は `TypeVSinger` を import し、
      `TypeVSinger` は `TypeP1Criteria` を import する。`isTypeI_of_isTypeF` は
      `TypeP1Criteria` に在るので、**そのままでは cite できない** (循環)。
      `isTypeI_of_isTypeF` を下流へ移すか、(e) の type-`F` 部分だけを上流に切り出すかの
      設計判断が要る。こちらは後回しでよい。
- [ ] 置換後、`lake build OddOrder` + AxiomsCheck が green のままであることを確認。

## 参照

- issue 3022 (closed) — 15.7(e) の形式化本体。
- Coq `coq/theories/BGsection15.v` `nonTI_Fitting_structure` :947-950 (statement)、
  :1185-1204 ((e2)/(e3) の分岐)。

## ✅ 調査の結果 close (2026-07-21, lane c) — 実質重複は 3022 で解消済み

起票時 (2026-07-19) の意図 = `isTypeI_of_isTypeF` (TypeP1Criteria.lean) /
`isTypeV_of_isTypeP1_mf_eq_msigma` (TypeVSinger.lean) の非 TI 分岐が
BG 15.7(e) の論法を「自前再導出」している重複の解消。3022 close
(`fitting_not_ti_structure_e` が (e1)/(e2)/(e3) 全条項で完成) を受けて実測:

1. **本質的 dedup は 3022 の時点で完了している**。両 consumer の非 TI 分岐は
   すでに S15 の共有補題群 (`exists_inf_conj_fitting_orderP_witness` /
   `rank_mf_eq_two_of_isMulCommutative_of_not_fittingIsTI` /
   `typeF_nonabelian_cyclic_opiCore_compl` /
   `exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI` 等) を cite しており、
   論法本体の二重管理は無い。残る「重複」は補題を並べる薄い assembly 層のみ。
2. **TypeVSinger 側は bundled (e) の cite に置換不可**: type V の組み立ては
   witness の具体形 (`Z = Ω₁(Z(O_p(M_F)))` = Coq `Z0`、`K* = M_σ ⊓ C(K)` との
   Singer 分岐、`|W₁| ∣ p−1` の dichotomy) を使う。
   `fitting_not_ti_structure_e` はこれらを existential の内側に隠すため、
   cite すると必要な等式が取り出せない。
3. **TypeP1Criteria 側は置換可能だが正味中立**: (e1)→(b), (e2)→(c) の変換に
   quotient↔complement 橋 (`exponent_quotient_mf_eq_exponent_typeFData_U`) の
   逆向き rw と (e3) の型排他排除が要り、現在の直接 assembly (~15 行) と
   同程度の plumbing になる。churn に見合う利得なし。

⟹ **wontfix 相当で close**。将来 (e) の statement 変更があれば assembly 層は
build エラーで追従を強制されるので、隠れた二重管理リスクも無い。
