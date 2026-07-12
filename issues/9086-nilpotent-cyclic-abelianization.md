---
id: 9086
slug: nilpotent-cyclic-abelianization
title: "nilpotent + cyclic abelianization ⟹ cyclic (shared GroupTheory leaf)"
created: 2026-07-12
---

# nilpotent + cyclic abelianization ⟹ cyclic (shared GroupTheory leaf)

## 背景

**CLAIM (lane a, 2026-07-12)**: 新 shared leaf `OddOrder/GroupTheory/NilpotentAbelianization.lean`。

Pf (11.9.c) の caseB 帰結 (issue 1024 P3) が必要とする一般群論:
**G nilpotent + G/G′ cyclic ⟹ G cyclic** (Coq mathcomp `cyclic_nilpotent_quo_der1_cyclic`、
PFsection11.v:1144 で `FTtype34_structure` が cite)。mathlib に無し (2026-07-12 検索:
`commutative_of_cyclic_center_quotient` 系 = center-quotient 版のみ、ZGroup は逆方向)。
repo 内にも無し (`grep IsNilpotent` × cyclic 交差 0 件)。

consumer: lane a (11.9.c) `U/U′ cyclic (Singer) + U nilpotent (TypePData.U_nilpotent) → U cyclic
→ IsMulCommutative U → ¬TypeIV`。lane c の T-side (11.9) instantiate (`hVcomm`,
S16_NonExistenceG/TTypeII.lean:784) も同 route で cite 予定。

## やること

- [x] 9000 scan (claim 衝突なし、2026-07-12)
- [x] `OddOrder/GroupTheory/NilpotentAbelianization.lean` 新設 (2026-07-12, sorry-free):
  - `commutator_le_lowerCentralSeries_of_isCyclic_quotient` (γ₂ ≤ γ₃ = ⁅γ₂,⊤⁆;
    G/γ₃ の center-quotient cyclic → abelian → 生成元評価)
  - `commutator_eq_bot_of_isNilpotent_of_isCyclic_quotient` (安定化 + nilpotency 降下)
  - `isCyclic_of_isNilpotent_of_isCyclic_quotient` (G ≅ G/⊥)
  - `isCyclic_of_isNilpotent_of_ker_le_commutator` (application 形:
    f : G →* C cyclic, ker f ≤ commutator G)
- [x] build green + AxiomsCheck 登録 (3 本、axioms check OK)

## 完了条件

leaf が sorry-free で build green、issue 1024 P3 が cite。

## 参照

- issue 1024 (consumer)、Coq mathcomp `cyclic_nilpotent_quo_der1_cyclic` (odd_order 側 cite:
  PFsection11.v:1144)
- mathlib: `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`
  (Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:180)、`Subgroup.lowerCentralSeries` (Nilpotent.lean)
