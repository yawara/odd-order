/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Fintype.Lattice
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Simple
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

/-- **Isaacs Lemma 1.43 (等号条件)** (p. 41): `m_G(H)·m_G(K) = m_G(D)·m_G(J)`
(`D = H ⊓ K`, `J = H ⊔ K`) が成り立つならば **`J = HK` かつ `C_G(D) = C_G(H)·C_G(K)`**
(いずれも集合としての等式).

書籍の証明そのまま. 不等式 `chermakDelgadoMeasure_mul_le` の導出では
`|HK| ≤ |J|` と `|C_H·C_K| ≤ |C_D|` の 2 箇所でしか緩みが生じないので, 等号成立時は
両方が等号になる. あとは有限集合の包含 + 濃度一致から集合等式が出る.

(配置: 書籍では主不等式 `chermakDelgadoMeasure_mul_le` の直後だが, 証明が下の私的補助
`_eq_of_mul_eq_of_le` を使うのでここに置く.) -/
theorem chermakDelgadoMeasure_mul_eq_conditions [Finite G] (H K : Subgroup G)
    (heq : H.chermakDelgadoMeasure * K.chermakDelgadoMeasure
      = (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure) :
    ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G) ∧
      ((centralizer ((H ⊓ K : Subgroup G) : Set G) : Subgroup G) : Set G)
        = (centralizer (H : Set G) : Set G) * (centralizer (K : Set G) : Set G) := by
  set D := H ⊓ K with hD_def
  set J := H ⊔ K with hJ_def
  set C_H : Subgroup G := centralizer (H : Set G) with hCH_def
  set C_K : Subgroup G := centralizer (K : Set G) with hCK_def
  set C_D : Subgroup G := centralizer (D : Set G) with hCD_def
  set C_J : Subgroup G := centralizer (J : Set G) with hCJ_def
  -- 主不等式の証明と同じ H1 分解.
  have hCJ_inf : C_J = C_H ⊓ C_K := centralizer_sup H K
  have h1_HK : Nat.card (↑H * ↑K : Set G) * Nat.card ↥D = Nat.card H * Nat.card K :=
    card_HK_mul_card_inf_eq_card_mul_card H K
  have h1_CHCK :
      Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) * Nat.card ↥(C_H ⊓ C_K)
        = Nat.card C_H * Nat.card C_K :=
    card_HK_mul_card_inf_eq_card_mul_card C_H C_K
  rw [← hCJ_inf] at h1_CHCK
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
  have h_RHS_decomp : D.chermakDelgadoMeasure * J.chermakDelgadoMeasure
      = (Nat.card J * Nat.card C_D) * (Nat.card ↥D * Nat.card C_J) := by
    rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def]
    ring
  rw [h_LHS_decomp, h_RHS_decomp] at heq
  -- `|D|·|C_J| > 0` で両辺からキャンセル.
  have hDCJ_pos : 0 < Nat.card ↥D * Nat.card C_J := Nat.mul_pos Nat.card_pos Nat.card_pos
  have h_cancelled :
      Nat.card (↑H * ↑K : Set G) * Nat.card ((C_H : Set G) * (C_K : Set G) : Set G)
        = Nat.card J * Nat.card C_D :=
    Nat.eq_of_mul_eq_mul_right hDCJ_pos heq
  -- 2 本の包含と, それぞれの濃度不等式.
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
  have hCHCK_pos : 0 < Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) := by
    rw [Nat.card_pos_iff]
    refine ⟨⟨1, ?_⟩, Set.toFinite _⟩
    exact ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
  -- 積が等しく各因子が `≤` なら各因子が等しい — ここで両方の等号を取る.
  obtain ⟨hHK_eq, hC_eq⟩ :=
    _eq_of_mul_eq_of_le h_cancelled hHK_le_J hCHCK_le_CD Nat.card_pos hCHCK_pos
  exact ⟨(Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hHK_sub_J hHK_eq.symm.le).symm,
    (Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hCHCK_sub_CD hC_eq.symm.le).symm⟩

/-- `H, K ∈ L(G)` ならば Lemma 1.43 の不等式は**等号**になる: measure の最大性から
`m_G(D)·m_G(J) ≤ m_G(H)²= m_G(H)·m_G(K)` で、逆向きが 1.43。

Thm 1.44 (a)(b) が共通して使う入口。 -/
theorem chermakDelgadoLattice_measure_mul_eq [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    H.chermakDelgadoMeasure * K.chermakDelgadoMeasure
      = (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure := by
  have hsame : H.chermakDelgadoMeasure = K.chermakDelgadoMeasure := le_antisymm (hK H) (hH K)
  refine le_antisymm (chermakDelgadoMeasure_mul_le H K) ?_
  calc (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure
      ≤ H.chermakDelgadoMeasure * H.chermakDelgadoMeasure := Nat.mul_le_mul (hH _) (hH _)
    _ = H.chermakDelgadoMeasure * K.chermakDelgadoMeasure := by rw [hsame]

/-- `H, K ∈ L(G)` のとき `m_G(H⊓K) = m_G(H) = m_G(H⊔K)` (Thm 1.44 (a) の中身)。 -/
private theorem _lattice_measure_inf_and_sup_eq [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    (H ⊓ K).chermakDelgadoMeasure = H.chermakDelgadoMeasure ∧
      (H ⊔ K).chermakDelgadoMeasure = H.chermakDelgadoMeasure := by
  have hsame : H.chermakDelgadoMeasure = K.chermakDelgadoMeasure := le_antisymm (hK H) (hH K)
  have h_prod_eq : (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure
                 = H.chermakDelgadoMeasure * H.chermakDelgadoMeasure := by
    rw [← chermakDelgadoLattice_measure_mul_eq hH hK, hsame]
  exact _eq_of_mul_eq_sq_of_le h_prod_eq (hH _) (hH _)

/-- **Isaacs Thm 1.44 (a)**: `L(G)` is closed under intersection. -/
theorem chermakDelgadoLattice_inf_mem [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    H ⊓ K ∈ chermakDelgadoLattice G := by
  intro L
  rw [(_lattice_measure_inf_and_sup_eq hH hK).1]
  exact hH L

/-- **Isaacs Thm 1.44 (a)**: `L(G)` is closed under join. -/
theorem chermakDelgadoLattice_sup_mem [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    H ⊔ K ∈ chermakDelgadoLattice G := by
  intro L
  rw [(_lattice_measure_inf_and_sup_eq hH hK).2]
  exact hH L

/-- **Isaacs Thm 1.44 (b)**: For `H, K ∈ L`: `⟨H, K⟩ = HK` (as sets).

Lemma 1.43 の等号条件 (`chermakDelgadoMeasure_mul_eq_conditions`) の `J = HK` 節そのもの。
`H, K ∈ L` は等号成立 (`chermakDelgadoLattice_measure_mul_eq`) を保証するためだけに使う。 -/
theorem chermakDelgadoLattice_sup_eq_mul [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    ((H ⊔ K : Subgroup G) : Set G) = ↑H * ↑K :=
  (chermakDelgadoMeasure_mul_eq_conditions H K
    (chermakDelgadoLattice_measure_mul_eq hH hK)).1

/-- **Isaacs Thm 1.44 (b) の対**: `H, K ∈ L` なら `C_G(H ⊓ K) = C_G(H)·C_G(K)`.

書籍 Lem 1.43 の等号条件のもう一方の節。Thm 1.44 の本文では明示されないが、
1.43 が保証する内容なので lattice でも成り立つ。 -/
theorem chermakDelgadoLattice_centralizer_inf_eq_mul [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    ((centralizer ((H ⊓ K : Subgroup G) : Set G) : Subgroup G) : Set G)
      = (centralizer (H : Set G) : Set G) * (centralizer (K : Set G) : Set G) :=
  (chermakDelgadoMeasure_mul_eq_conditions H K
    (chermakDelgadoLattice_measure_mul_eq hH hK)).2

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

/-! ### Cor 1.45 + Thm 1.41: properties of `M = chermakDelgadoSubgroup G`. -/

/-- L(G) is nonempty (max measure exists for finite G). -/
theorem chermakDelgadoLattice_nonempty [Finite G] :
    (chermakDelgadoLattice G).Nonempty := by
  haveI : Nonempty (Subgroup G) := ⟨⊥⟩
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨H_max, h_max⟩ :=
    Finite.exists_max (fun H : Subgroup G => H.chermakDelgadoMeasure)
  exact ⟨H_max, h_max⟩

/-- L(G) is finite. -/
theorem chermakDelgadoLattice_finite [Finite G] :
    (chermakDelgadoLattice G).Finite := by
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  exact Set.toFinite _

/-- M = sInf L (alternative form of `chermakDelgadoSubgroup`). -/
theorem chermakDelgadoSubgroup_eq_sInf :
    chermakDelgadoSubgroup G = sInf (chermakDelgadoLattice G) := by
  rw [chermakDelgadoSubgroup, sInf_eq_iInf]

/-- 補助: 有限・閉じた sublattice の `sInf` は中身に入っている. -/
private theorem _sInf_mem_of_finite_subset [Finite G] (S : Set (Subgroup G))
    (hfin : S.Finite) :
    S.Nonempty → S ⊆ chermakDelgadoLattice G → sInf S ∈ chermakDelgadoLattice G := by
  induction S, hfin using Set.Finite.induction_on with
  | empty => intro hne _; exact (Set.not_nonempty_empty hne).elim
  | @insert a t hat ht_fin ih =>
    intro _hne hsub
    rcases t.eq_empty_or_nonempty with rfl | ht_ne
    · -- t = ∅, so S = {a}. sInf {a} = a, and a ∈ L
      rw [Set.insert_eq, Set.union_empty, sInf_singleton]
      exact hsub (Set.mem_insert _ _)
    · -- t nonempty
      have hsub_t : t ⊆ chermakDelgadoLattice G :=
        fun H hH => hsub (Set.mem_insert_of_mem _ hH)
      have ha_in : a ∈ chermakDelgadoLattice G := hsub (Set.mem_insert _ _)
      have h_ih := ih ht_ne hsub_t
      rw [sInf_insert]
      exact chermakDelgadoLattice_inf_mem ha_in h_ih

/-- **Isaacs Cor 1.45 part 1**: `M = chermakDelgadoSubgroup G ∈ L(G)`. -/
theorem chermakDelgadoSubgroup_mem_lattice [Finite G] :
    chermakDelgadoSubgroup G ∈ chermakDelgadoLattice G := by
  rw [chermakDelgadoSubgroup_eq_sInf]
  exact _sInf_mem_of_finite_subset _ chermakDelgadoLattice_finite
    chermakDelgadoLattice_nonempty Set.Subset.rfl

/-- `M ≤ H` for any `H ∈ L`. -/
theorem chermakDelgadoSubgroup_le_of_mem [Finite G] {H : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) :
    chermakDelgadoSubgroup G ≤ H := by
  rw [chermakDelgadoSubgroup_eq_sInf]
  exact sInf_le hH

/-- `M ≤ C_G(M)` ── M ∈ L で `C_G(M) ∈ L` (Thm 1.44(c)) なので `M ≤ C_G(M)`. -/
theorem chermakDelgadoSubgroup_le_centralizer [Finite G] :
    chermakDelgadoSubgroup G
      ≤ (centralizer ((chermakDelgadoSubgroup G : Subgroup G) : Set G) : Subgroup G) :=
  chermakDelgadoSubgroup_le_of_mem
    (chermakDelgadoLattice_centralizer_mem chermakDelgadoSubgroup_mem_lattice)

/-- **Isaacs Cor 1.45 part 2**: `M` is abelian (`IsMulCommutative`). -/
instance chermakDelgadoSubgroup_isMulCommutative [Finite G] :
    IsMulCommutative (chermakDelgadoSubgroup G) :=
  le_centralizer_iff_isMulCommutative.mp chermakDelgadoSubgroup_le_centralizer

/-- **Isaacs Cor 1.45 part 3**: `Z(G) ≤ M`.

`M = C_G(C_G(M))` (Thm 1.44(c)) で `Z(G) ≤ C_G(X)` (任意 X) を組み合わせる. -/
theorem center_le_chermakDelgadoSubgroup [Finite G] :
    center G ≤ chermakDelgadoSubgroup G := by
  rw [← chermakDelgadoLattice_centralizer_centralizer_eq chermakDelgadoSubgroup_mem_lattice]
  exact center_le_centralizer _

/-- Chermak-Delgado 測度は群自己同型の下で不変. -/
private lemma chermakDelgadoMeasure_map_equiv (ϕ : G ≃* G) (K : Subgroup G) :
    (K.map ϕ.toMonoidHom).chermakDelgadoMeasure = K.chermakDelgadoMeasure := by
  rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def]
  have h_card_K : Nat.card (K.map ϕ.toMonoidHom : Subgroup G) = Nat.card K :=
    Nat.card_congr
      (Subgroup.equivMapOfInjective K ϕ.toMonoidHom ϕ.injective).symm.toEquiv
  have h_centralizer :
      (centralizer ((K.map ϕ.toMonoidHom : Subgroup G) : Set G) : Subgroup G)
        = (centralizer (K : Set G) : Subgroup G).map ϕ.toMonoidHom := by
    apply SetLike.coe_injective
    ext g
    simp only [Subgroup.coe_map, Set.mem_image, mem_centralizer_iff, SetLike.mem_coe]
    constructor
    · intro hg
      refine ⟨ϕ.symm g, ?_, by simp⟩
      intro k hk
      -- hg (ϕ k) hkmap : ϕ k * g = g * ϕ k
      have h1 : ϕ k * g = g * ϕ k :=
        hg (ϕ k) (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
      have h2 := congrArg ϕ.symm h1
      simp only [MulEquiv.map_mul, MulEquiv.symm_apply_apply] at h2
      -- h2 : k * ϕ.symm g = ϕ.symm g * k
      exact h2
    · rintro ⟨a, ha, rfl⟩ y hy
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
      -- ha k hk : k * a = a * k
      have h1 : k * a = a * k := ha k hk
      have h2 := congrArg ϕ h1
      simp only [MulEquiv.map_mul] at h2
      -- h2 : ϕ k * ϕ a = ϕ a * ϕ k
      exact h2
  rw [h_card_K, h_centralizer]
  congr 1
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective
      (centralizer (K : Set G) : Subgroup G) ϕ.toMonoidHom ϕ.injective).symm.toEquiv

/-- comap 版の不変性. -/
private lemma chermakDelgadoMeasure_comap_equiv (ϕ : G ≃* G) (K : Subgroup G) :
    (K.comap ϕ.toMonoidHom).chermakDelgadoMeasure = K.chermakDelgadoMeasure := by
  rw [comap_equiv_eq_map_symm', chermakDelgadoMeasure_map_equiv]

/-- 自己同型は L(G) を保つ (comap 形式). -/
private lemma chermakDelgadoLattice_comap_mem (ϕ : G ≃* G) {K : Subgroup G}
    (hK : K ∈ chermakDelgadoLattice G) :
    K.comap ϕ.toMonoidHom ∈ chermakDelgadoLattice G := by
  intro J
  rw [chermakDelgadoMeasure_comap_equiv]
  exact hK J

/-- **Isaacs Cor 1.45 part 4**: `M` is characteristic.

`L(G)` は自己同型で不変 ⟹ `M = sInf L(G)` も不変. -/
instance chermakDelgadoSubgroup_characteristic [Finite G] :
    (chermakDelgadoSubgroup G).Characteristic := by
  rw [characteristic_iff_le_comap]
  intro ϕ
  rw [chermakDelgadoSubgroup_eq_sInf]
  -- 目標: sInf L ≤ (sInf L).comap ϕ
  -- 各 x ∈ sInf L について, ϕ x ∈ sInf L を示せばよい
  intro x hx
  rw [mem_comap, Subgroup.mem_sInf]
  intro K hK
  -- K ∈ L. ϕ x ∈ K ↔ x ∈ K.comap ϕ. K.comap ϕ ∈ L (measure-invariant).
  -- x ∈ sInf L ≤ K.comap ϕ. ✓
  have hKcomap : K.comap ϕ.toMonoidHom ∈ chermakDelgadoLattice G :=
    chermakDelgadoLattice_comap_mem ϕ hK
  rw [Subgroup.mem_sInf] at hx
  exact hx _ hKcomap

/-! ### Thm 1.41 (Chermak-Delgado main theorem). -/

/-- **Isaacs Thm 1.41 (Chermak-Delgado)**: There exists a characteristic abelian subgroup `N` with
`|G : N| ≤ |G : A|²` for every abelian subgroup `A`.

具体的には `N = chermakDelgadoSubgroup G` を取る. -/
theorem chermakDelgado [Finite G] :
    ∃ N : Subgroup G, N.Characteristic ∧ IsMulCommutative N ∧
      ∀ A : Subgroup G, IsMulCommutative A → N.index ≤ A.index ^ 2 := by
  refine ⟨chermakDelgadoSubgroup G, inferInstance, inferInstance, ?_⟩
  intro A hA
  set M := chermakDelgadoSubgroup G with hM_def
  -- Step 1: |A| ≤ |C_G(A)| (since A ≤ C_G(A) for abelian A)
  haveI : IsMulCommutative A := hA
  have hA_le_CA : Nat.card A ≤ Nat.card (centralizer (A : Set G) : Subgroup G) :=
    Nat.card_le_card_of_injective
      (Subgroup.inclusion A.le_centralizer) (Subgroup.inclusion_injective _)
  -- Step 2: |A|² ≤ m_G(A) = |A|·|C_G(A)|
  have hA_sq_le : Nat.card A ^ 2 ≤ A.chermakDelgadoMeasure := by
    rw [chermakDelgadoMeasure_def, sq]
    exact Nat.mul_le_mul_left _ hA_le_CA
  -- Step 3: m_G(A) ≤ m_G(M) (M ∈ L)
  have hA_le_M : A.chermakDelgadoMeasure ≤ M.chermakDelgadoMeasure :=
    chermakDelgadoSubgroup_mem_lattice A
  have hA_sq_le_M : Nat.card A ^ 2 ≤ M.chermakDelgadoMeasure := hA_sq_le.trans hA_le_M
  -- Step 4: Lagrange |G| = |M|·M.index = |A|·A.index
  have hM_card : Nat.card M * M.index = Nat.card G := M.card_mul_index
  have hA_card : Nat.card A * A.index = Nat.card G := A.card_mul_index
  -- Step 5: |G|² = |A|² · A.index² (rearrange Lagrange)
  have hG_sq : Nat.card G ^ 2 = Nat.card A ^ 2 * A.index ^ 2 := by
    rw [← hA_card]; ring
  -- Step 6: M.index · |A|² ≤ M.index · m_G(M) = |G| · |C_G(M)| ≤ |G|²
  have h1 : M.index * Nat.card A ^ 2 ≤ M.index * M.chermakDelgadoMeasure :=
    Nat.mul_le_mul_left _ hA_sq_le_M
  have h2 : M.index * M.chermakDelgadoMeasure
          = Nat.card G * Nat.card (centralizer (M : Set G) : Subgroup G) := by
    rw [chermakDelgadoMeasure_def]
    -- M.index · (|M| · |C_G(M)|) = (M.index · |M|) · |C_G(M)| = (|M| · M.index) · |C_G(M)|
    rw [← Nat.mul_assoc, Nat.mul_comm M.index (Nat.card M), hM_card]
  have h3 : Nat.card (centralizer (M : Set G) : Subgroup G) ≤ Nat.card G :=
    Nat.card_le_card_of_injective
      (centralizer (M : Set G) : Subgroup G).subtype
      ((centralizer (M : Set G) : Subgroup G).subtype_injective)
  have h4 : Nat.card G * Nat.card (centralizer (M : Set G) : Subgroup G) ≤ Nat.card G ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul_left _ h3
  have h5 : M.index * Nat.card A ^ 2 ≤ Nat.card G ^ 2 := h1.trans (h2.le.trans h4)
  -- Step 7: |G|² = |A|² · A.index² ⟹ M.index · |A|² ≤ A.index² · |A|²
  rw [hG_sq, Nat.mul_comm (Nat.card A ^ 2) (A.index ^ 2)] at h5
  -- Step 8: Cancel |A|² (positive)
  exact Nat.le_of_mul_le_mul_right h5 (pow_pos Nat.card_pos 2)

/-! ### Cor 1.46. -/

/-- **Isaacs Cor 1.46**: If `H ≤ G` with `|H| · |C_G(H)| > |G|`, then `G` is not a nonabelian simple
group. -/
theorem not_isSimpleGroup_and_nonabelian_of_chermakDelgadoMeasure_gt [Finite G]
    {H : Subgroup G} (h : H.chermakDelgadoMeasure > Nat.card G) :
    ¬ (IsSimpleGroup G ∧ ¬ IsMulCommutative G) := by
  rintro ⟨h_simple, h_nonab⟩
  set M := chermakDelgadoSubgroup G with hM_def
  -- m_G(M) > |G|
  have h_M_gt : Nat.card G < M.chermakDelgadoMeasure :=
    lt_of_lt_of_le h (chermakDelgadoSubgroup_mem_lattice H)
  -- m_G(⊥) = |G|
  have h_bot_measure : (⊥ : Subgroup G).chermakDelgadoMeasure = Nat.card G := by
    rw [chermakDelgadoMeasure_def, Subgroup.card_bot, one_mul]
    have hC : (centralizer ((⊥ : Subgroup G) : Set G) : Subgroup G) = ⊤ := by
      ext x
      rw [Subgroup.coe_bot]
      simp [mem_centralizer_iff]
    rw [hC]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  -- M ≠ ⊥
  have h_M_ne_bot : M ≠ ⊥ := by
    intro h_eq
    rw [h_eq, h_bot_measure] at h_M_gt
    exact (lt_irrefl _) h_M_gt
  -- M is normal (characteristic ⟹ normal)
  haveI : M.Normal := inferInstance
  -- G simple ⟹ M = ⊥ or M = ⊤. M ≠ ⊥ ⟹ M = ⊤
  have h_M_top : M = ⊤ :=
    (h_simple.eq_bot_or_eq_top_of_normal M ‹M.Normal›).resolve_left h_M_ne_bot
  -- M abelian
  haveI hM_comm : IsMulCommutative M := inferInstance
  -- IsMulCommutative G derivation
  apply h_nonab
  refine ⟨⟨fun a b => ?_⟩⟩
  have h_top_comm := h_M_top ▸ hM_comm
  exact congrArg Subtype.val
    (h_top_comm.is_comm.comm
      (⟨a, Subgroup.mem_top _⟩ : (⊤ : Subgroup G)) ⟨b, Subgroup.mem_top _⟩)

end Subgroup
