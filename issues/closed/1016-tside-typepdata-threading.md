---
id: 1016
slug: tside-typepdata-threading
title: "S15.Hypothesis に T-side TypePData (Tdata) を thread — W₁-side + T-side §15 群を unblock"
created: 2026-07-01
---

# S15.Hypothesis に T-side TypePData (Tdata) を thread — W₁-side + T-side §15 群を unblock

**owner**: hub 調整 (S15_SAndT_Setup.lean = lane d 所有 + FeitThompson.lean constructor = cross-lane)
**consumer**: lane c (§13.16 W₁-side + §13.17 T-side)

## 背景 (2026-07-01)

lane c が **(13.16) W₂-side を gate ゼロで完全 proven** (`normalizer_U_inf_W2_eq_bot` 他、
commit `e025cf7b`)。これは S-side の `Sdata : TypePData S` + reconciliation fields
(`Sdata_U_eq`/`Sdata_W1_eq`/`Sdata_W2_eq`) を使う。

**W₁-side (13.16 T-side) = 完全な S↔T,P↔Q,U↔V,W₁↔W₂ dual**。残り §15 sorry の大半
(`normalizer_W1_structure`/`reconciled_typePData_T`/`card_Q_eq`/`tConjugate_fitting_data`/
`complement_inf_Q_structure` 等) は **T-side type-P 構造が S15.Hypothesis に無いため gated**:
現状 `S15.Hypothesis` は `S_typeP2 : IsTypeP2 S` のみで `T` の type-P を assert しない
(`T_nonI` + `one_typeII` のみ)。

## やること

FeitThompson レベルには **T が canonical partner = type-P** の witness が存在
(BG Theorem 14.7 / `typeP_duality`, FeitThompson.lean:209-217 付近)。これを S15 に thread:

- [ ] **S15.Hypothesis に追加** (S15_SAndT_Setup.lean, Sdata と対称):
  - `Tdata : TypePData T`
  - `Tdata_V_eq : Tdata.U = V` / `Tdata_W2_eq : Tdata.W1 = W2` / `Tdata_W1_eq : Tdata.W2 = W1`
    (T-side cyclic factor = W₂, intrinsic dual factor = W₁ = C_{T'}(W₂#))
- [ ] **FeitThompson constructor** がこれらを supply (`typeP_duality` / BG 14.7 canonical-partner 経由、
  S_typeP2/Sdata と同様)
- [ ] **T-side basic_structure** (Q elementary abelian, |Q|=q^p, V⋊W₂ Frobenius) — S-side
  `basic_structure` の dual (または `basic_structure` を typeP data 一般で parameterize)

## 完了条件

`Tdata` + T-side basic_structure 導入後、lane c が **(13.16) W₂-side 全補題を S↔T swap で dual 化**して
`normalizer_W1_structure` → `normalizer_W1` → (13.17.c) を実証明 (crux `V⊓N(W₁)=⊥` の coprime FPF
lifting + Gorenstein/Wielandt assembly + `coprime_card_Q_card_VW2` dual)。該当 §15 sorry 群が消える。

## 参照

- W₂-side proven テンプレート: `normalizer_U_inf_W2_eq_bot` / `_of_data` / `coprime_card_P_card_UW1`
  / `normalizer_U_inf_W2_le_centralizer_W2` (S15_SAndT.lean, commit `e025cf7b`/`d54a56a1`)
- 代替: (13.16) 核を抽象 type-P config 上に generalize (S/T 双方 instantiate)。現 S-side proven 群の
  re-instantiation refactor が要 (リスク) ゆえ thread 案が素直。
- notes/peterfalvi/s15_s_and_t.md の MILESTONE ブロック

## 🧾 注記 (2026-07-02 hub 全体レビュー): owner 更新

- 検証: `grep Tdata OddOrder/Peterfalvi/S15_SAndT_Setup.lean` = **0 hits** (2026-07-02) —
  Tdata threading は未実施、本 issue は依然 live。
- **owner 更新** (3 レーン再編、正本 `notes/meta/ft_lane_reallocation_2026_06_28.md`):
  - `S15_SAndT_Setup.lean` の Hypothesis 変更 (Tdata fields + T-side basic_structure) =
    **lane c の自己所有作業** (旧「lane d 所有 + hub 調整」は stale — S15_SAndT_Setup は
    現在 lane c 所有ゆえ cross-lane 調整は不要)。
  - 残る cross-lane は **FeitThompson.lean constructor の供給のみ** (lane a 所有) —
    lane a への手渡し 1 点で済み、**hub tick でも代行可**。

## ✅ CLOSED (2026-07-14 lane a audit): 恒久 carrier 案を撤回し、honest witness route へ置換済み

本 issue が提案した `S15.Hypothesis.Tdata` の恒久 field 追加は採用しない。spine 上の free carrier を
増やす設計は撤回され、必要な T-side type-`P` datum は定理
`OddOrder.Peterfalvi.S15.reconciled_typePData_T` がその都度**実構成**する設計に置換された。
この witness と直接の配置結果 `W1_le_Q` は 2026-07-14 の `#print axioms` 再検査でいずれも
`[propext, Classical.choice, Quot.sound]` のみ (`sorryAx` なし)。実構成の完了履歴と Coq 対応は
closed issue 9073 に集約されている。したがって FeitThompson constructor に `Tdata` を thread する
本 issue 固有の checklist は **superseded** であり、未実施作業として残さない。

ただし旧「完了条件」に併記した (13.16) 全体まで完了した、という判定ではない。
`normalizer_W1_structure` / `normalizer_W1` は現在も `sorryAx` を継承し、その最小 local root は
(13.12) T-side の `V_inf_centralizer_Q_eq_bot` (`normalizer_V_inf_W1_eq_bot` 経由) である。
これは carrier threading とは独立の character/centralizer obligation として open issue 9013
(`t-side-13-15-general`) が追跡している。よって本 issue は「完了」ではなく
**設計撤回 + honest route への置換 + 残責務の既存 issue への分離確認**として閉じる。
