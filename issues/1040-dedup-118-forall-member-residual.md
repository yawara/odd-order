---
id: 1040
slug: dedup-118-forall-member-residual
title: "(11.8) ∀ 形の重複: S13.zeta_residual_... と S16.member_residual_... を統合"
created: 2026-07-19
---

# (11.8) ∀ 形の重複: `S13.zeta_residual_...` と `S16.member_residual_...` を統合

## 背景 (正直な記録)

2026-07-19 lane a が Peterfalvi (11.8) を教科書どおりの `∀ ζ` 形へ一般化し
`S13.zeta_residual_not_orthogonal_H0C_of_refuter` (S13_Orthogonality.lean) を追加した
(commit `f59cf17ae`)。**その後に、同内容の定理が既に S16 に存在すると判明した** —
`S16.member_residual_not_orthogonal_H0C_of_refuter`
(S16_NonExistenceG/TGapMemberResidual.lean:321)。

**着手前に探さなかったのが原因** ([[verify-port-state-by-number-not-coq-name]] の再発)。
`exists_zeta_residual_not_orthogonal_H0C_of_refuter` の consumer は grep したが、
「同じ結論を持つ**別名**の定理」は探していなかった。

## 現状 (実測)

2 つは**文が同一** (ζ が implicit / explicit の違いのみ):

| | `S13.zeta_residual_not_orthogonal_H0C_of_refuter` | `S16.member_residual_not_orthogonal_H0C_of_refuter` |
|---|---|---|
| 位置 | S13_Orthogonality.lean (= 教科書 §11、(11.8) の居場所) | S16_NonExistenceG/TGapMemberResidual.lean:321 |
| ζ | implicit `{ζ}` | explicit `(zeta)` |
| 仮説 | `hG` `hyp` `htype` `hM2` `hHcard` `hrefute` + `hζS` `hζirr` `hζdeg` | 同一 |
| 結論 | `¬ ∀ i j, ⟨(τ(∑μ_{i'0} − ζ)) − ∑ω^σ_{i'0}, ω^σ_{ij}⟩ = 0` | 同一 |
| ζ 固定の機構 | `S12.Hypothesis.exists_charParameters_full_of_zeta` (CharacterParameters を与えられた ζ の周りで組む) | `exists_s13Hypothesis_for_member` (member に pin した S13 `Hypothesis` を作る) |
| consumer | `S13.exists_zeta_residual_...` (witness packaging) | S16 内 2 件 (TGapMemberResidual.lean:463 / TGapGridAlignment.lean:1312) |

依存方向は **S13 → S16** (S16 が S13 を import) なので S13 側が上流。

## やること

- [ ] `S16.member_residual_not_orthogonal_H0C_of_refuter` の証明本体を
      `S13.zeta_residual_not_orthogonal_H0C_of_refuter` の cite に置換する
      (statement 不変なので S16 の consumer 2 件は無変更のはず)。
- [ ] その後 `exists_s13Hypothesis_for_member` (S16_NonExistenceG/TGapMemberResidual.lean:270、
      AxiomsCheck:4963 で pin 済) に**独立した価値が残るか**を判定する。
      「member に pin した S13 `Hypothesis` を作る」こと自体は
      `exists_charParameters_full_of_zeta` (parameters レベル) より強い主張なので、
      他所で要るなら残す。要らなければ削除を検討 (⚠ AxiomsCheck の pin も併せて更新)。

## 判断が要る点

`exists_s13Hypothesis_for_member` の去就は、S16 の他の証明が「member に pin した S13
Hypothesis」を必要とするかで決まる。着手時に grep で確認すること
(現状の consumer は `member_residual_...` のみ = 上記置換で 0 になる)。

## 完了条件

- 同一命題の証明が repo 内で 1 本になる (S13 側を正本 — (11.8) は教科書 §11 = S13 が居場所)。
- `lake build OddOrder` green / AxiomsCheck OK / sorry 非退行。
- S16 側 docstring の「⚠ DUPLICATE ... issue 1040」注記を削除。

## 参照

- 一般化 commit: `f59cf17ae` (feat(pf 11.8): 教科書どおりの ∀ ζ 形へ一般化)
- 新規 producer: `S12.Hypothesis.exists_charParameters_full_of_zeta`
  (S12_MaximalIII_IV_V_Core/CharacterParameters.lean)
- frontier note: `notes/peterfalvi/frontier_measured_2026_07_19.md` の §11 (11.8) 行
