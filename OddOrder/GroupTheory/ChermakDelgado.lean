/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Finite.Card
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

/-! ### Thm 1.44 (a)(b)(c): `L(G)` is a lattice; structure properties.

主要 helper: Lemma 1.43 の等式条件 `m_G(H) * m_G(K) = m_G(D) * m_G(J)` から
`|HK| = |J|` と `|C_H * C_K| = |C_D|` を導出する. `H, K ∈ L` のとき equality を取る. -/

/-- 数論的補助: `a * b = c * d`, `a ≤ c`, `b ≤ d`, `c, b > 0` のとき `a = c ∧ b = d`. -/
private lemma _eq_of_mul_eq_of_le {a b c d : ℕ} (h_eq : a * b = c * d)
    (ha : a ≤ c) (hb : b ≤ d) (hc : 0 < c) (hb_pos : 0 < b) :
    a = c ∧ b = d := by
  have h1 : a * b ≤ c * b := Nat.mul_le_mul_right b ha
  have h2 : c * b ≤ c * d := Nat.mul_le_mul_left c hb
  have h_cb : a * b = c * b := le_antisymm h1 (h_eq ▸ h2)
  have ha_eq : a = c := Nat.eq_of_mul_eq_mul_right hb_pos h_cb
  subst ha_eq
  have hb_eq : b = d := Nat.eq_of_mul_eq_mul_left hc h_eq
  exact ⟨rfl, hb_eq⟩

/-- 数論的補助 (対称): `a * b = m * m`, `a ≤ m`, `b ≤ m` のとき `a = m ∧ b = m`. -/
private lemma _eq_of_mul_eq_sq_of_le {a b m : ℕ} (h_eq : a * b = m * m)
    (ha : a ≤ m) (hb : b ≤ m) : a = m ∧ b = m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; exact ⟨Nat.le_zero.mp ha, Nat.le_zero.mp hb⟩
  · rcases Nat.eq_zero_or_pos b with hb_z | hb_pos
    · subst hb_z
      rw [Nat.mul_zero] at h_eq
      have : m = 0 := by
        rcases Nat.mul_eq_zero.mp h_eq.symm with h | h <;> exact h
      omega
    · exact _eq_of_mul_eq_of_le h_eq ha hb hm hb_pos

/-- **Isaacs Thm 1.44 (a)**: `L(G)` is closed under intersection. -/
theorem chermakDelgadoLattice_inf_mem [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    H ⊓ K ∈ chermakDelgadoLattice G := by
  intro L
  have hsame : H.chermakDelgadoMeasure = K.chermakDelgadoMeasure := le_antisymm (hK H) (hH K)
  have h_le_HK : (H ⊓ K).chermakDelgadoMeasure ≤ H.chermakDelgadoMeasure := hH _
  have h_le_J : (H ⊔ K).chermakDelgadoMeasure ≤ H.chermakDelgadoMeasure := hH _
  have h_43 := chermakDelgadoMeasure_mul_le H K
  rw [← hsame] at h_43
  have h_prod_eq : (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure
                 = H.chermakDelgadoMeasure * H.chermakDelgadoMeasure :=
    le_antisymm (Nat.mul_le_mul h_le_HK h_le_J) h_43
  have hHK_eq : (H ⊓ K).chermakDelgadoMeasure = H.chermakDelgadoMeasure :=
    (_eq_of_mul_eq_sq_of_le h_prod_eq h_le_HK h_le_J).1
  rw [hHK_eq]
  exact hH L

/-- **Isaacs Thm 1.44 (a)**: `L(G)` is closed under join. -/
theorem chermakDelgadoLattice_sup_mem [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    H ⊔ K ∈ chermakDelgadoLattice G := by
  intro L
  have hsame : H.chermakDelgadoMeasure = K.chermakDelgadoMeasure := le_antisymm (hK H) (hH K)
  have h_le_HK : (H ⊓ K).chermakDelgadoMeasure ≤ H.chermakDelgadoMeasure := hH _
  have h_le_J : (H ⊔ K).chermakDelgadoMeasure ≤ H.chermakDelgadoMeasure := hH _
  have h_43 := chermakDelgadoMeasure_mul_le H K
  rw [← hsame] at h_43
  have h_prod_eq : (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure
                 = H.chermakDelgadoMeasure * H.chermakDelgadoMeasure :=
    le_antisymm (Nat.mul_le_mul h_le_HK h_le_J) h_43
  have hJ_eq : (H ⊔ K).chermakDelgadoMeasure = H.chermakDelgadoMeasure :=
    (_eq_of_mul_eq_sq_of_le h_prod_eq h_le_HK h_le_J).2
  rw [hJ_eq]
  exact hH L

/-- **Isaacs Thm 1.44 (b)**: For `H, K ∈ L`: `⟨H, K⟩ = HK` (as sets). -/
theorem chermakDelgadoLattice_sup_eq_mul [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    ((H ⊔ K : Subgroup G) : Set G) = ↑H * ↑K := by
  set D := H ⊓ K with hD_def
  set J := H ⊔ K with hJ_def
  set C_H : Subgroup G := centralizer (H : Set G) with hCH_def
  set C_K : Subgroup G := centralizer (K : Set G) with hCK_def
  set C_D : Subgroup G := centralizer (D : Set G) with hCD_def
  set C_J : Subgroup G := centralizer (J : Set G) with hCJ_def
  -- Step 1: m_G(H) * m_G(K) = m_G(D) * m_G(J) (from H, K ∈ L)
  have hsame : H.chermakDelgadoMeasure = K.chermakDelgadoMeasure := le_antisymm (hK H) (hH K)
  have h_le_HK : D.chermakDelgadoMeasure ≤ H.chermakDelgadoMeasure := hH _
  have h_le_J : J.chermakDelgadoMeasure ≤ H.chermakDelgadoMeasure := hH _
  have h_43 := chermakDelgadoMeasure_mul_le H K
  have h_prod_le : D.chermakDelgadoMeasure * J.chermakDelgadoMeasure
                ≤ H.chermakDelgadoMeasure * K.chermakDelgadoMeasure := by
    calc D.chermakDelgadoMeasure * J.chermakDelgadoMeasure
        ≤ H.chermakDelgadoMeasure * H.chermakDelgadoMeasure :=
          Nat.mul_le_mul h_le_HK h_le_J
      _ = H.chermakDelgadoMeasure * K.chermakDelgadoMeasure := by rw [hsame]
  have h_measure_eq : H.chermakDelgadoMeasure * K.chermakDelgadoMeasure
                    = D.chermakDelgadoMeasure * J.chermakDelgadoMeasure :=
    le_antisymm h_43 h_prod_le
  -- Step 2: 両辺を H1 で分解 (Lemma 1.43 proof と同じ計算)
  have hCJ_inf : C_J = C_H ⊓ C_K := centralizer_sup H K
  have h1_HK : Nat.card (↑H * ↑K : Set G) * Nat.card ↥D = Nat.card H * Nat.card K :=
    card_HK_mul_card_inf_eq_card_mul_card H K
  have h1_CHCK :
      Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) * Nat.card ↥(C_H ⊓ C_K)
        = Nat.card C_H * Nat.card C_K :=
    card_HK_mul_card_inf_eq_card_mul_card C_H C_K
  rw [← hCJ_inf] at h1_CHCK
  -- LHS の分解
  have h_LHS_decomp : H.chermakDelgadoMeasure * K.chermakDelgadoMeasure
      = (Nat.card (↑H * ↑K : Set G) * Nat.card ((C_H : Set G) * (C_K : Set G) : Set G))
        * (Nat.card ↥D * Nat.card C_J) := by
    rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def]
    calc Nat.card H * Nat.card C_H * (Nat.card K * Nat.card C_K)
        = (Nat.card H * Nat.card K) * (Nat.card C_H * Nat.card C_K) := by ring
      _ = (Nat.card (↑H * ↑K : Set G) * Nat.card ↥D)
            * (Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) * Nat.card C_J) := by
            rw [h1_HK, h1_CHCK]
      _ = _ := by ring
  -- RHS の分解
  have h_RHS_decomp : D.chermakDelgadoMeasure * J.chermakDelgadoMeasure
      = (Nat.card J * Nat.card C_D) * (Nat.card ↥D * Nat.card C_J) := by
    rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def]
    ring
  -- 等式を等式に: `(|HK| * |C_H * C_K|) * (|D| * |C_J|) = (|J| * |C_D|) * (|D| * |C_J|)`
  rw [h_LHS_decomp, h_RHS_decomp] at h_measure_eq
  -- |D| * |C_J| > 0 でキャンセル
  have hD_pos : 0 < Nat.card ↥D := Nat.card_pos
  have hCJ_pos : 0 < Nat.card C_J := Nat.card_pos
  have hDCJ_pos : 0 < Nat.card ↥D * Nat.card C_J := Nat.mul_pos hD_pos hCJ_pos
  have h_cancelled :
      Nat.card (↑H * ↑K : Set G) * Nat.card ((C_H : Set G) * (C_K : Set G) : Set G)
        = Nat.card J * Nat.card C_D :=
    Nat.eq_of_mul_eq_mul_right hDCJ_pos h_measure_eq
  -- |HK| ≤ |J|, |C_H * C_K| ≤ |C_D|, 全て正
  have hHK_sub_J : (↑H * ↑K : Set G) ⊆ (J : Set G) := by
    rintro _ ⟨h, hh, k, hk, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hk)
  have hC_sub_CD : (C_H : Set G) ⊆ (C_D : Set G) :=
    SetLike.coe_subset_coe.mpr (centralizer_le (SetLike.coe_subset_coe.mpr (inf_le_left : D ≤ H)))
  have hCK_sub_CD : (C_K : Set G) ⊆ (C_D : Set G) :=
    SetLike.coe_subset_coe.mpr (centralizer_le (SetLike.coe_subset_coe.mpr (inf_le_right : D ≤ K)))
  have hCHCK_sub_CD : ((C_H : Set G) * (C_K : Set G) : Set G) ⊆ (C_D : Set G) := by
    rintro _ ⟨h, hh, k, hk, rfl⟩
    exact mul_mem (hC_sub_CD hh) (hCK_sub_CD hk)
  have hHK_le_J : Nat.card (↑H * ↑K : Set G) ≤ Nat.card J :=
    Nat.card_mono (Set.toFinite _) hHK_sub_J
  have hCHCK_le_CD : Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) ≤ Nat.card C_D :=
    Nat.card_mono (Set.toFinite _) hCHCK_sub_CD
  -- positivity: |J|, |C_H * C_K|, both > 0
  have hJ_pos : 0 < Nat.card J := Nat.card_pos
  have hCHCK_pos : 0 < Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) := by
    rw [Nat.card_pos_iff]
    refine ⟨⟨1, ?_⟩, Set.toFinite _⟩
    exact ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
  -- |HK| * |C_H * C_K| = |J| * |C_D|, both inequalities and positivity ⟹ |HK| = |J|
  have hHK_eq : Nat.card (↑H * ↑K : Set G) = Nat.card J :=
    (_eq_of_mul_eq_of_le h_cancelled hHK_le_J hCHCK_le_CD hJ_pos hCHCK_pos).1
  -- Step 3: HK ⊆ J + |HK| = |J| (finite) ⟹ HK = J
  exact (Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hHK_sub_J hHK_eq.symm.le).symm

/-- **Isaacs Lemma 1.42 (equality condition)**: `m_G(H) = m_G(C_G(H))` iff
`C_G(C_G(H)) = H`. Cor 1.45 + Thm 1.44(c) で使用. -/
theorem chermakDelgadoMeasure_eq_centralizer_iff [Finite G] (H : Subgroup G) :
    H.chermakDelgadoMeasure
        = (centralizer (H : Set G) : Subgroup G).chermakDelgadoMeasure
      ↔ centralizer ((centralizer (H : Set G) : Subgroup G) : Set G) = H := by
  rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def]
  constructor
  · intro h_eq
    -- |H| * |C_H| = |C_H| * |C(C_H)|, |C_H| > 0 ⟹ |H| = |C(C_H)|
    rw [Nat.mul_comm (Nat.card ↥(centralizer (H : Set G) : Subgroup G))
        (Nat.card ↥(centralizer ((centralizer (H : Set G) : Subgroup G) : Set G)))] at h_eq
    have hCH_pos : 0 < Nat.card ↥(centralizer (H : Set G) : Subgroup G) := Nat.card_pos
    have h_card :
        Nat.card ↥H
          = Nat.card ↥(centralizer ((centralizer (H : Set G) : Subgroup G) : Set G)) :=
      Nat.eq_of_mul_eq_mul_right hCH_pos h_eq
    -- H ≤ C(C_H), |H| = |C(C_H)|, finite ⟹ H = C(C_H)
    symm
    apply SetLike.coe_injective
    exact Set.Finite.eq_of_subset_of_card_le (Set.toFinite _)
      (SetLike.coe_subset_coe.mpr H.le_centralizer_centralizer) h_card.ge
  · intro h_eq
    -- C(C(H)) = H ⟹ |H| = |C(C(H))| ⟹ 等式
    rw [show Nat.card ↥H
          = Nat.card ↥(centralizer ((centralizer (H : Set G) : Subgroup G) : Set G)) by rw [h_eq]]
    ring

/-- **Isaacs Thm 1.44 (c)**: For `H ∈ L`: `C_G(H) ∈ L`. -/
theorem chermakDelgadoLattice_centralizer_mem [Finite G] {H : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) :
    (centralizer (H : Set G) : Subgroup G) ∈ chermakDelgadoLattice G := by
  intro L
  have h_eq : (centralizer (H : Set G) : Subgroup G).chermakDelgadoMeasure
            = H.chermakDelgadoMeasure :=
    le_antisymm (hH _) (chermakDelgadoMeasure_le_centralizer H)
  rw [h_eq]
  exact hH L

/-- **Isaacs Thm 1.44 (c)**: For `H ∈ L`: `C_G(C_G(H)) = H`. -/
theorem chermakDelgadoLattice_centralizer_centralizer_eq [Finite G] {H : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) :
    centralizer ((centralizer (H : Set G) : Subgroup G) : Set G) = H := by
  have h_eq : H.chermakDelgadoMeasure
            = (centralizer (H : Set G) : Subgroup G).chermakDelgadoMeasure :=
    le_antisymm (chermakDelgadoMeasure_le_centralizer H) (hH _)
  exact (chermakDelgadoMeasure_eq_centralizer_iff H).mp h_eq

end Subgroup
