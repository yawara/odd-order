---
id: 3012
slug: prop44b-scn-centralizer-dprod
title: "BG Prop 4.4(b): A∈SCN(Sylow R) ⟹ C_G(A) = A × H (H p'-group)"
created: 2026-07-18
---

# BG Prop 4.4(b): A∈SCN(Sylow R) ⟹ C_G(A) = A × H (H p'-group)

## 背景

BG §4 の document 順で最上流の残ギャップ (survey L330: 4.4(a) は `isSCN_iff_isMaximalAbelianNormal`
で済、(b) は MISSING、= Gorenstein Thm 7.6.5 / Coq `SCN_Sylow_cent_dprod`)。BG §1・§2・§3 完成後の
BG §4 着手 (2026-07-18)。

## statement (BG mmd L1494)

> (b) if `R` is a Sylow `p`-subgroup of a group `G` and `A ∈ SCN(R)`, then `C_G(A) = A × H`
> for some `p'`-subgroup `H` of `G`.

## 証明 (Gorenstein 7.6.5)

`A ∈ SCN(R)`: A abelian, A ◁ R, `C_R(A) = A`。R Sylow-p of G。
1. **A ≤ Z(C_G(A))**: C_G(A) の全元が A を中心化、A abelian ⟹ A ≤ Z(C_G(A)) ⟹ A ◁ C_G(A)。
2. **A = C_R(A) = R ⊓ C_G(A)**: `R ⊓ C_G(A) = C_R(A) = A` (SCN)。
3. **A は C_G(A) の normal Sylow-p**: R ≤ N_G(A) (A◁R) かつ R Sylow-p of G ⟹ R Sylow-p of N_G(A)。
   C_G(A) ◁ N_G(A)。「P Sylow-p of K, N◁K ⟹ P⊓N Sylow-p of N」(mathlib Sylow-in-normal) を
   K=N_G(A), P=R, N=C_G(A) に ⟹ `R ⊓ C_G(A) = A` が C_G(A) の Sylow-p。A central ゆえ normal。
4. **C_G(A) = A × H**: A normal Sylow-p、[C_G(A):A] は p'-数 (coprime to |A|)。Schur–Zassenhaus
   (`Subgroup.exists_right_complement'_of_coprime`) で補群 H, |H| p'-group。A ≤ Z(C_G(A)) ⟹
   [A,H]=1 ⟹ A ⋊ H = A × H (internal direct product)。

## 既存 infra (reuse)

- `OddOrder.GroupTheory.IsSCN A` (`GroupTheory/SCN.lean`): `isNormal`, `isMulCommutative`,
  `selfCentralizing` (`centralizer (A:Set G) = A`)。
- mathlib Sylow API (`Sylow`, Sylow-in-normal-subgroup `Sylow.subgroupOf`/類似), Schur–Zassenhaus
  `Subgroup.exists_right_complement'_of_coprime` + `isComplement'_of_coprime`。
- 「central complement ⟹ internal direct product」(mathlib `Subgroup.isComplement'` + commute)。

## 完了条件

`OddOrder.GroupTheory` or BG §4 leaf に BG Prop 4.4(b) を book strength (C_G(A) = A × H,
H p'-group; internal direct product 形 or `∃ H, ...`) で sorry-free・axiom-clean。AxiomsCheck
登録、survey 正本 Prop 4.4 行「済」更新。

## 参照

- BG mmd L1489-1494、Gorenstein Thm 7.6.5、Coq `SCN_Sylow_cent_dprod`
- 既存: `GroupTheory/SCN.lean` (IsSCN, 4.4(a))

## ✅ 完了 (2026-07-18)

`S04_Prop44b.centralizer_eq_dprod_of_isSCN_of_sylow` — sorry-free・axiom-clean・AxiomsCheck 登録・
full build green (4308 jobs)。新 reusable helper `sylow_relIndex_normal_not_dvd` (Sylow-in-normal、
mathlib 未収載) 追加。survey 正本 Prop 4.4「済」。BG §4 の次 = Lem 4.5 (M)。
