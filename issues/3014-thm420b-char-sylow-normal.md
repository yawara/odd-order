---
id: 3014
slug: thm420b-char-sylow-normal
title: "BG Thm 4.20(b): S Sylow, T char S, T⊆S' ⟹ T◁G"
created: 2026-07-18
---

# BG Thm 4.20(b): S Sylow, T char S, T⊆S' ⟹ T◁G

## 背景

BG §4 の残 numbered gap (survey L333: (a)(c) 済、(b) 未; grep で 4.20(b) 未形式化を再確認)。
Prop 4.4 / Lem 4.5 全 / Prop 4.6 完成後の §4 last。

## statement (BG mmd L1783)

> G solvable odd, r(G)≤2 or r(F(G))≤2。(b) if S is a Sylow subgroup of G, T is a characteristic
> subgroup of S, and T ⊆ S', then T ◁ G。

## 証明 (BG mmd L1793)

(a) より G' ⊆ F、ゆえ G/F abelian。
1. FS ◁ G (F◁G + G/F abelian で FS = F·S の像が normal)、Frattini で G = FS·N_G(S) = F·N_G(S)。
2. T char S ⟹ N_G(S) ≤ N_G(T)、ゆえ T ◁ N_G(S)。
3. T ⊆ S' ⊆ G' ⊆ F かつ T ⊆ S ⟹ T ⊆ F∩S (Sylow-p of F)。F nilpotent = (F∩S) × O_{p'}(F)。
   F∩S normalizes T (T char S ⟹ T◁S ⊇ F∩S)、O_{p'}(F) centralizes T (direct product coprime)
   ⟹ F ≤ N_G(T)。
4. G = F·N_G(S) ≤ N_G(T) ⟹ T ◁ G。

## 既存 infra (reuse)

- **4.20(a)** `derived_le_fitting_of_rank_fitting_le_two [IsSolvable G][Nontrivial G] (hodd : Odd (Nat.card G)) (hrank : rank ↥(Ch01.fitting G) ≤ 2) : commutator G ≤ Ch01.fitting G` (S05_NarrowPGroups)。
- **Frattini**: mathlib `Sylow.normalizer_sup_eq_top` (N◁G, P Sylow ⟹ N ⊔ N_G(P) = ⊤)。
- **Fitting** `Ch01.fitting G` (nilpotent); nilpotent ⟹ Sylow の direct product (mathlib
  `IsNilpotent` / `Group.isNilpotent_iff` の direct-product 形、`Sylow` の product)。
- `T char S ⟹ N_G(S) ≤ N_G(T)` (characteristic transport)。

## 完了条件

BG Thm 4.20(b) を book strength・sorry-free・axiom-clean。AxiomsCheck 登録、survey 正本
Thm 4.20 行「済」(⟹ 全 (a)(b)(c) 完成)。

## 参照

- BG mmd L1779-1793、既存 S05_NarrowPGroups (4.20(a)(c))
