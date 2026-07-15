---
id: 4004
slug: s15-tv-side-duals-for-s16
title: "lane-h ask: S15 T/V-side duals (typeII_overNormalizer_frobenius_T, T-side 13.13/13.15) for §16"
created: 2026-06-22
---

# lane-h ask: S15 T/V-side duals (typeII_overNormalizer_frobenius_T, T-side 13.13/13.15) for §16

> 宛先 = lane-h (`S15_SAndT.lean` 所有)。発信 = lane-c (Pf §16)。cross-lane sync は notes/issue 経由。
> 正本 = `notes/peterfalvi/s16_nonexistence_gate_map.md`「更新 (2026-06-22, resume session)」。

## 背景

lane-c の §16 (`S16_NonExistenceG.lean`) は 2026-06-22 resume で文書順最上流の 2 sorry を着地
(`caseB_for_S` 14.6 / `K_eq_V_index_pq` index 半 14.11、commit `aff0bc2a`)。原文 (14.4)/(14.10)/(14.11)
+ S15 export を signature レベルまで精読した結果、**残 sorry の構造側 2 本が S15 の S/U-side ハードコード
で詰まっている**ことを特定。S15 に T/V-side dual を足せば lane-c が機械的 dual で実証明化できる。

## やること (lane-h、S15 に T/V-side dual を export)

### ① `typeII_overNormalizer_frobenius` の T/V-side 版 (→ `exists_MHypothesis` 14.10 解禁)

現状 (S15:1712) は S/U-side ハードコード:
```
theorem typeII_overNormalizer_frobenius (_hG) (hyp) (hSTypeII : IsTypeII hyp.S) :
    ∃ data : TypeIOverNormalizerData hyp,
      data.frobenius.kernel_eq_MF ∧ (hyp.U ≤ data.H)
```
`exists_LHypothesis` (S16, **sorry-free**) はこれを cite して U-side carrier を組む。V-side dual
`exists_MHypothesis` (S16:現 sorry) は対応する **T/V-side 版**が無いと構造部すら組めない:
- [ ] `(hTTypeII : IsTypeII hyp.T) → ∃ data, … ∧ (hyp.V ≤ data.H)`
      (`normalizer_V_le_M` / `K = M_F` / Frobenius complement 位数 `p*q` を carry; signature が
      正しければ producer は sorried 可 [[feedback-cite-sorried-lemmas-if-signature-correct]])。

これが在れば lane-c が `exists_MHypothesis` を `exists_LHypothesis` の機械的 dual として書き、
`MHypothesis.complement_card_eq_pq` (今 `aff0bc2a` で carrier field 化済) も供給される。

### ② T-side (13.13)/(13.15) + `D=⊥`/`v=full` (→ `T_side_caseB_facts` 14.4 解禁)

S15 は S-side のみ持つ: `caseA_parameters` (13.13, `caseA_for_S → q=3 ∧ u=(p-1)²/4`),
`caseB_order_u` (13.15, S-side `u`-value), `c_eq_one` (13.12, S-side `c=1`)。
`T_side_caseB_facts` (S16:136, `hyp.base.D = ⊥ ∧ v = (q^p-1)/(q-1)`) は T-side dual を要する:
- [ ] T-side (13.13): `caseA_for_T → p = 3 ∧ v = (q-1)²/4` (caseA_parameters の dual)。
- [ ] (9.7)-for-T dichotomy (caseA_for_T ∨ caseB_for_T)。
- [ ] T-side `D=⊥` (case (9.7.b)-for-T、c_eq_one の dual) + T-side `v`-value (caseB_order_u の dual)。

> 注: 既存 `lambda_forces_T_caseB` (S15:305) は結論 `D=⊥ ∧ v=full` を出すが仮説
> `chars.lambda_induced_from_PC_linear` が discharge 不能 (`character_degree_analysis` は逆の
> `no_lambda_forces_caseB_S` を出す) ゆえ cite できない。原文 (14.4) は (13.13) p≠3 経由で証明する。

## 完了条件

S15 に上記 dual が (sorried でも) **faithful signature** として存在し、lane-c が cite して
`exists_MHypothesis` の構造部 + `T_side_caseB_facts` を実証明化できる。

## 参照

- `notes/peterfalvi/s16_nonexistence_gate_map.md` (正本)
- issue 4001 (lane-c §16 frontier)、issue 4003 (η-carrier ask, 別の lane-h gate)
- commit `aff0bc2a` (lane-c resume: caseB_for_S + K_eq_V index 半)
- S15:1712 `typeII_overNormalizer_frobenius` / S15:533 `caseA_parameters` / S15:693 `caseB_order_u`

## 🧾 注記 (2026-07-02 hub 全体レビュー): ① landed / 残 = lane c intra-lane

- **① は landed**: `typeII_overNormalizer_frobenius_V` が `S15_SAndT.lean:3541` に存在
  (V-side producer、`exists_MHypothesis` 側 assembly も同ファイル ~3567-3581 で cite 済。
  2026-07-02 grep 確認)。
- **残 = ② T-side (13.13)/(13.15) 系** — 宛先 (lane-h) は退役済で、`S15_SAndT.lean` は
  現在 **lane c 所有** (正本 `notes/meta/ft_lane_reallocation_2026_06_28.md`)。残作業は
  **lane c 自身の §13/§16 char 作業** (issue 9001 cont.⁴⁴ 参照) であり cross-lane ask
  ではない。
