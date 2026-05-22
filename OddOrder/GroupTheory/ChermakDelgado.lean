/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Tactic.Ring
import OddOrder.Mathlib.Subgroup

/-!
# Chermak-Delgado measure, lattice, and subgroup

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), §1G (pp. 41-44, Theorems 1.41-1.46) の Lean 化.

mathlib upstream 候補として `OddOrder/GroupTheory/` 配下に shared module 化 (`IsElementaryAbelian`,
`Subgroup.thompsonJ` 系の慣用).

## Main definitions

* `Subgroup.chermakDelgadoMeasure H` (`m_G(H)`): `|H| · |C_G(H)|`.
* `Subgroup.chermakDelgadoLattice G` (`L(G)`): the set of subgroups attaining the maximum measure.
* `Subgroup.chermakDelgadoSubgroup G` (`M`): the minimal element of `L(G)` (= ⨅ L).

## Main results (this file: Lemmas 1.42, 1.43)

* `chermakDelgadoMeasure_le_centralizer` (Lemma 1.42): `m_G(H) ≤ m_G(C_G(H))`.
* `chermakDelgadoMeasure_mul_le` (Lemma 1.43): `m_G(H) · m_G(K) ≤ m_G(D) · m_G(J)`
  for `D = H ⊓ K`, `J = H ⊔ K`.

Thm 1.44 / Cor 1.45 / Thm 1.41 / Cor 1.46 は同ファイル後半 (本コミットで追加予定).

## References

* Isaacs, M.: *Finite Group Theory* (AMS GSM 92, 2008), §1G, pp. 41-44.
* mathlib 不在の補助補題は [`OddOrder.Mathlib.Subgroup`](../Mathlib/Subgroup.lean):
  H1 (`card_HK_mul_card_inf_eq_card_mul_card`), H2 (`le_centralizer_centralizer`),
  `centralizer_sup` を使用.
-/

namespace Subgroup

variable {G : Type*} [Group G]

open scoped Pointwise

/-- **Chermak-Delgado measure** of a subgroup: `m_G(H) := |H| · |C_G(H)|`.

Isaacs §1G p.41 の定義. 無限群でも well-defined だが (`Nat.card` が 0 を返す),
実質的に意味があるのは [Finite G] 下. -/
noncomputable def chermakDelgadoMeasure (H : Subgroup G) : ℕ :=
  Nat.card H * Nat.card (centralizer (H : Set G) : Subgroup G)

@[simp]
theorem chermakDelgadoMeasure_def (H : Subgroup G) :
    H.chermakDelgadoMeasure = Nat.card H * Nat.card (centralizer (H : Set G) : Subgroup G) :=
  rfl

/-- **Chermak-Delgado lattice** `L(G)`: the collection of subgroups attaining the maximum
Chermak-Delgado measure. Isaacs §1G p.42 (Thm 1.44 statement). -/
def chermakDelgadoLattice (G : Type*) [Group G] : Set (Subgroup G) :=
  {H | ∀ K : Subgroup G, K.chermakDelgadoMeasure ≤ H.chermakDelgadoMeasure}

theorem mem_chermakDelgadoLattice {H : Subgroup G} :
    H ∈ chermakDelgadoLattice G ↔
      ∀ K : Subgroup G, K.chermakDelgadoMeasure ≤ H.chermakDelgadoMeasure :=
  Iff.rfl

/-- **Chermak-Delgado subgroup** `M`: the minimal element of the maximum-measure lattice.
Isaacs Cor 1.45 で唯一の極小元として定義される (本ファイルで Cor 1.45 として証明). -/
noncomputable def chermakDelgadoSubgroup (G : Type*) [Group G] : Subgroup G :=
  ⨅ H ∈ chermakDelgadoLattice G, H

/-- **Isaacs Lemma 1.42**: `m_G(H) ≤ m_G(C_G(H))`.
等号成立は `H = C_G(C_G(H))` のとき (本ファイル `..._eq_iff` 系で別途扱う).

証明: `H ≤ C_G(C_G(H))` (`le_centralizer_centralizer`, mathlib 拡張) から
`|H| ≤ |C_G(C_G(H))|`, 両辺に `|C_G(H)|` を掛けて結論. -/
theorem chermakDelgadoMeasure_le_centralizer [Finite G] (H : Subgroup G) :
    H.chermakDelgadoMeasure
      ≤ (centralizer (H : Set G) : Subgroup G).chermakDelgadoMeasure := by
  rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def]
  -- Goal: |H| * |C_H| ≤ |C_H| * |C_(C_H)|
  rw [Nat.mul_comm (Nat.card ↥(centralizer (H : Set G)))]
  -- Goal: |H| * |C_H| ≤ |C_(C_H)| * |C_H|
  exact Nat.mul_le_mul_right _
    (Nat.card_le_card_of_injective (Subgroup.inclusion H.le_centralizer_centralizer)
      (Subgroup.inclusion_injective _))

/-- **Isaacs Lemma 1.43**: `m_G(H) · m_G(K) ≤ m_G(D) · m_G(J)` for `D = H ⊓ K`, `J = H ⊔ K`.

証明戦略 (Isaacs p.42):
- `|H|·|K| = |HK|·|D|` (H1).
- `|C_H|·|C_K| = |C_H·C_K|·|C_H ∩ C_K| = |C_H·C_K|·|C_J|` (H1 + `centralizer_sup`).
- `HK ⊆ J` ⟹ `|HK| ≤ |J|`.
- `C_H·C_K ⊆ C_D` ⟹ `|C_H·C_K| ≤ |C_D|`.
- 組合せて `|HK|·|C_H·C_K| ≤ |J|·|C_D|`, 両辺に `|D|·|C_J|` を掛けて結論. -/
theorem chermakDelgadoMeasure_mul_le [Finite G] (H K : Subgroup G) :
    H.chermakDelgadoMeasure * K.chermakDelgadoMeasure
      ≤ (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure := by
  set D := H ⊓ K with hD_def
  set J := H ⊔ K with hJ_def
  set C_H : Subgroup G := centralizer (H : Set G) with hCH_def
  set C_K : Subgroup G := centralizer (K : Set G) with hCK_def
  set C_D : Subgroup G := centralizer (D : Set G) with hCD_def
  set C_J : Subgroup G := centralizer (J : Set G) with hCJ_def
  -- 核心等式: C_J = C_H ⊓ C_K
  have hCJ_inf : C_J = C_H ⊓ C_K := centralizer_sup H K
  -- H1 for H, K
  have h1_HK : Nat.card (↑H * ↑K : Set G) * Nat.card ↥D = Nat.card H * Nat.card K :=
    card_HK_mul_card_inf_eq_card_mul_card H K
  -- H1 for C_H, C_K
  have h1_CHCK :
      Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) * Nat.card ↥(C_H ⊓ C_K)
        = Nat.card C_H * Nat.card C_K :=
    card_HK_mul_card_inf_eq_card_mul_card C_H C_K
  rw [← hCJ_inf] at h1_CHCK
  -- HK ⊆ J (集合包含)
  have hHK_sub_J : (↑H * ↑K : Set G) ⊆ (J : Set G) := by
    rintro _ ⟨h, hh, k, hk, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hk)
  -- C_H * C_K ⊆ C_D (集合包含); C_H ⊆ C_D, C_K ⊆ C_D ⟹ 積も ⊆
  have hC_sub_CD : (C_H : Set G) ⊆ (C_D : Set G) :=
    SetLike.coe_subset_coe.mpr (centralizer_le (SetLike.coe_subset_coe.mpr (inf_le_left : D ≤ H)))
  have hCK_sub_CD : (C_K : Set G) ⊆ (C_D : Set G) :=
    SetLike.coe_subset_coe.mpr (centralizer_le (SetLike.coe_subset_coe.mpr (inf_le_right : D ≤ K)))
  have hCHCK_sub_CD : ((C_H : Set G) * (C_K : Set G) : Set G) ⊆ (C_D : Set G) := by
    rintro _ ⟨h, hh, k, hk, rfl⟩
    exact mul_mem (hC_sub_CD hh) (hCK_sub_CD hk)
  -- cardinality monotonicity (with [Finite G])
  have hHK_le_J : Nat.card (↑H * ↑K : Set G) ≤ Nat.card J :=
    Nat.card_mono (Set.toFinite _) hHK_sub_J
  have hCHCK_le_CD : Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) ≤ Nat.card C_D :=
    Nat.card_mono (Set.toFinite _) hCHCK_sub_CD
  have main_ineq :
      Nat.card (↑H * ↑K : Set G) * Nat.card ((C_H : Set G) * (C_K : Set G) : Set G)
        ≤ Nat.card J * Nat.card C_D :=
    Nat.mul_le_mul hHK_le_J hCHCK_le_CD
  -- 仕上げ: 代数的整理
  rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def, chermakDelgadoMeasure_def,
      chermakDelgadoMeasure_def]
  calc Nat.card H * Nat.card C_H * (Nat.card K * Nat.card C_K)
      = (Nat.card H * Nat.card K) * (Nat.card C_H * Nat.card C_K) := by ring
    _ = (Nat.card (↑H * ↑K : Set G) * Nat.card ↥D)
          * (Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) * Nat.card C_J) := by
          rw [h1_HK, h1_CHCK]
    _ = (Nat.card (↑H * ↑K : Set G) * Nat.card ((C_H : Set G) * (C_K : Set G) : Set G))
          * (Nat.card ↥D * Nat.card C_J) := by ring
    _ ≤ (Nat.card J * Nat.card C_D) * (Nat.card ↥D * Nat.card C_J) :=
          Nat.mul_le_mul_right _ main_ineq
    _ = Nat.card ↥D * Nat.card C_D * (Nat.card J * Nat.card C_J) := by ring

end Subgroup
