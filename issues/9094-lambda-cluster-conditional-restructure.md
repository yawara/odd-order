# 9094: CharacterDegreeData lambda 無条件 field は no-λ case で uninhabitable — 条件付き restructure の hub 裁定

- 起票: lane b, 2026-07-13 (issue 2035 更新 #20 の分析より)
- 種別: HUB 裁定依頼 (cross-lane API — TTypeII (lane c) が consumer)

## 発見 (確定)

`S15.CharacterDegreeData` (Machinery135) の `lambda` cluster (irr・度数 uq・H=PC 線型誘導) は
**無条件 field** だが、原文 Pf (13.3.b) は **dichotomy**:

> If 𝒮 contains no irreducible character of degree uq induced from a linear character of PC,
> then case (9.7.b) holds for M = S, C = 1 and u = (p^q−1)/(p−1).

- Coq PFsection13:307-310 も同形 (`~~ has irrIndH calS → [typeP_Galois, C=1, u=(p^q−1)/(p−1)]`)。
  Coq の (13.5-8) は λ を **引数に取る条件付き** (calS1 member; S1cases :402)。
- no-λ case (Galois, C=1, u=(p^q−1)/(p−1)) は S15.Hypothesis で排除されない
  (C は定義 field `C = U ⊓ C_G(P)` のみ、C=⊥ 可)。book は (13.15) 等の算術
  (x ≥ 2q+1 の場合) で初めて no-λ を refute — (13.3) 時点では live。
- ⟹ no-λ 配置では λ の要求性質を満たす character が存在せず
  `character_degree_analysis : Nonempty (CharacterDegreeData hyp)` は**証明不能**
  (2034 lambda_mem・2035 更新 #19 tau1S_induce_inner_eta に続く同型 carrier bug 第 3 例)。

## 提案 (lane b 推奨 = 案 A)

**(A) λ-free core + 条件付き λ-cluster に分割**:
- `CharacterDegreeCore` (新): tau1S/tau1T/μ-系/δ-系/formula field 群 — 全て landed engine で
  無条件供給可 (tau1S_ofHonest + muColumn_formula + mu_col_eta_col_one + mu_j_isIndPC +
  delta_eq_one_S + inner_induce + mem_ZIrr + …)。
- `CharacterDegreeData` = core + λ-cluster、producer は **dichotomy**:
  `Nonempty (CharacterDegreeData hyp) ∨ (typeP_Galois ∧ C = ⊥ ∧ u = (p^q−1)/(p−1))`
  (右分岐の Lean 表現は要設計 — (9.7.b)/CliffordCaseB データで表すのが自然)。
- 消費側: NormEstimates ×5 は (13.4)→(13.8)-T 系で λ 前提が本来の姿 → dichotomy を thread。
  **TTypeII:194 (lane c 所有)** の `obtain ⟨chars⟩ := character_degree_analysis hG hyp.base` は
  restructure 後に両分岐対応が必要 → **cross-lane ゆえ hub 裁定・調整を依頼**。

(B) 代替: producer statement のみ dichotomy 化し structure は不変 (consumer 側の case 分岐は同じ)。

## 裁定依頼事項

1. 案 A/B (または他案) の選択と、TTypeII (lane c) 側の対応方針 (hub 実施 or lane c 依頼)。
2. no-λ 分岐の Lean 表現の正本置き場 (CliffordCaseBData の拡張 vs 新 structure)。

## 関連

- issue 2035 更新 #17-#20 (発見の経緯・材料化 inventory)
- 先行同型例: 2034 W-side restate (lambda_mem 削除)、2035 更新 #19 (tau1S_induce_inner_eta 分割)

## 2026-07-13 追記 (lane b) — 訂正: dichotomy の数学は landed 済、裁定対象は carrier 形状のみ

(13.3.b) の数学本体は **既に sorry-free で landed**:
`caseB_of_no_irreducible_sOf_H0Cprime` (CountingLayer:1042, §9-generic) =
「𝒮(H₀C′) に irr member 無し → CliffordCaseBData + C = ⊥ + u = (p^q−1)/(p−1)」
(clifford_dichotomy + (9.8.c) caseA_character_counts + (9.9.c) caseB_character_counts の組立)。
(9.10) 相当も `exceptional_case_frobenius_realization` (ThetaCountAssembly:993) に landed。

⟹ 裁定は純粋に **carrier/API 形状** (案 A/B) と TTypeII 調整のみ。lane b は裁定を待たず
両案共通の部品 (conditional producer `∃λ-witness → Nonempty CDD`、λ-free field 供給
theorem 群) を先行 build する。
