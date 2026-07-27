/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.ChermakDelgado

/-!
# Isaacs Problems 1G (書籍 p. 43) — Chermak–Delgado 周辺

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 1G の形式化
(campaign issue 1055)。§1G は Chermak–Delgado の定理 (Thm 1.41) と最大測度束 `L(G)`
(Thm 1.44) の節で, 本文の定理は `OddOrder/GroupTheory/ChermakDelgado.lean` に landing 済。

⚠ **文言は PDF ページ画像で確定** (`references/isaacs/pages/isaacs-p043-056.png`)。
pdftotext は `<` と `≤` を潰すが, **1G.1 と 1G.4 の不等号は厳密 `<`** である
(`≤` なら Thm 1.41 そのもので自明になってしまう)。

* **1G.1**: `A ≤ G` 可換で, `|G : N| < |G : A|²` なる特性可換部分群 `N` が存在しないなら,
  `A = C_G(A)` は `L(G)` に属し `|G : Z(G)| = |G : A|²`。
* **1G.2**: `H ∈ L(G)`, `H < G` なら `H ⊆ M < G` なる正規部分群 `M` が存在する。
* **1G.3**: `G` 単純, `H ≤ G`, `|H|·|C_G(H)| = |G|` なら `H = 1` または `H = G`。
* **1G.4**: `A ≤ G` 可換, `G` 非可換なら `|G : N| < |G : A|²` なる**正規**可換部分群 `N`
  が存在する。

## Main results

- `eq_centralizer_and_mem_lattice_of_no_smaller_characteristic` — **Problem 1G.1**。
-/

namespace OddOrder.Isaacs.Ch01

open Subgroup

section /- 1G: Problem 1G.1 (p. 43) -/

variable {G : Type*} [Group G] [Finite G]

/-- **Isaacs Problem 1G.1** (p. 43)。可換部分群 `A` について,
`|G : N| < |G : A|²` を満たす特性可換部分群 `N` が存在しないならば
`A = C_G(A)`, `A ∈ L(G)`, `|G : Z(G)| = |G : A|²` の 3 つが同時に成り立つ。

Thm 1.41 の証明の不等式の連鎖

  `|G : M| · |A|² ≤ |G : M| · m_G(A) ≤ |G : M| · m_G(M) = |G| · |C_G(M)| ≤ |G|²
     = |G : A|² · |A|²`

において, 仮定より `|G : M| = |G : A|²` (`M` = Chermak–Delgado 部分群) なので**全ての
不等号が等号**になる。それぞれの等号が

* `|A|² = m_G(A)` ⟹ `|C_G(A)| = |A|` ⟹ `A = C_G(A)`,
* `m_G(A) = m_G(M)` ⟹ `A ∈ L(G)`,
* `|C_G(M)| = |G|` ⟹ `C_G(M) = ⊤` ⟹ `M ≤ Z(G)`, `Z(G) ≤ M` と合わせて `M = Z(G)`

を与える。 -/
theorem eq_centralizer_and_mem_lattice_of_no_smaller_characteristic {A : Subgroup G}
    [IsMulCommutative A]
    (hno : ∀ N : Subgroup G, N.Characteristic → IsMulCommutative N →
      ¬ N.index < A.index ^ 2) :
    A = centralizer (A : Set G) ∧ A ∈ chermakDelgadoLattice G ∧
      (center G).index = A.index ^ 2 := by
  set M : Subgroup G := chermakDelgadoSubgroup G with hMdef
  have hMmem : M ∈ chermakDelgadoLattice G := chermakDelgadoSubgroup_mem_lattice
  have hApos : 0 < Nat.card ↥A := Nat.card_pos
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hMipos : 0 < M.index := Nat.pos_of_ne_zero (by
    have := Subgroup.card_mul_index M
    intro hc
    rw [hc, mul_zero] at this
    omega)
  -- `|A| ≤ |C_G(A)|` から `|A|² ≤ m_G(A)`
  have hAle : Nat.card ↥A ≤ Nat.card ↥(centralizer (A : Set G)) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion A.le_centralizer)
      (Subgroup.inclusion_injective _)
  have hAsq : Nat.card ↥A ^ 2 ≤ A.chermakDelgadoMeasure := by
    rw [chermakDelgadoMeasure_def, sq]
    exact Nat.mul_le_mul_left _ hAle
  have hAM : A.chermakDelgadoMeasure ≤ M.chermakDelgadoMeasure := hMmem A
  have hCM : Nat.card ↥(centralizer ((M : Subgroup G) : Set G)) ≤ Nat.card G :=
    Nat.le_of_dvd hGpos (Subgroup.card_subgroup_dvd_card _)
  have hGM : Nat.card ↥M * M.index = Nat.card G := Subgroup.card_mul_index M
  have hGA : Nat.card ↥A * A.index = Nat.card G := Subgroup.card_mul_index A
  -- 連鎖の各段
  have e1 : M.index * Nat.card ↥A ^ 2 ≤ M.index * A.chermakDelgadoMeasure :=
    Nat.mul_le_mul_left _ hAsq
  have e2 : M.index * A.chermakDelgadoMeasure ≤ M.index * M.chermakDelgadoMeasure :=
    Nat.mul_le_mul_left _ hAM
  have e3 : M.index * M.chermakDelgadoMeasure
      = Nat.card G * Nat.card ↥(centralizer ((M : Subgroup G) : Set G)) := by
    rw [chermakDelgadoMeasure_def, ← mul_assoc, mul_comm M.index, hGM]
  have e4 : Nat.card G * Nat.card ↥(centralizer ((M : Subgroup G) : Set G))
      ≤ Nat.card G * Nat.card G := Nat.mul_le_mul_left _ hCM
  have hGsq : Nat.card G * Nat.card G = A.index ^ 2 * Nat.card ↥A ^ 2 := by
    rw [← hGA]; ring
  -- `|G : M| ≤ |G : A|²`, 仮定より等号
  have hle : M.index ≤ A.index ^ 2 := by
    refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hApos 2)
    calc M.index * Nat.card ↥A ^ 2 ≤ Nat.card G * Nat.card G := by omega
      _ = A.index ^ 2 * Nat.card ↥A ^ 2 := hGsq
  have heq : M.index = A.index ^ 2 := by
    have := hno M inferInstance inferInstance
    omega
  -- 等号なので連鎖は全て等号
  have hall : M.index * Nat.card ↥A ^ 2 = Nat.card G * Nat.card G := by
    rw [hGsq, heq]
  have hAsq' : Nat.card ↥A ^ 2 = A.chermakDelgadoMeasure := by
    have : M.index * Nat.card ↥A ^ 2 = M.index * A.chermakDelgadoMeasure := by omega
    exact Nat.eq_of_mul_eq_mul_left hMipos this
  have hAM' : A.chermakDelgadoMeasure = M.chermakDelgadoMeasure := by
    have : M.index * A.chermakDelgadoMeasure = M.index * M.chermakDelgadoMeasure := by omega
    exact Nat.eq_of_mul_eq_mul_left hMipos this
  have hCM' : Nat.card ↥(centralizer ((M : Subgroup G) : Set G)) = Nat.card G := by
    have : Nat.card G * Nat.card ↥(centralizer ((M : Subgroup G) : Set G))
        = Nat.card G * Nat.card G := by omega
    exact Nat.eq_of_mul_eq_mul_left hGpos this
  refine ⟨?_, ?_, ?_⟩
  · -- `A = C_G(A)`
    refine Subgroup.eq_of_le_of_card_ge A.le_centralizer (le_of_eq ?_)
    have : Nat.card ↥A * Nat.card ↥A
        = Nat.card ↥A * Nat.card ↥(centralizer (A : Set G)) := by
      rw [← sq, hAsq', chermakDelgadoMeasure_def]
    exact (Nat.eq_of_mul_eq_mul_left hApos this).symm
  · -- `A ∈ L(G)`
    intro K
    exact hAM' ▸ hMmem K
  · -- `M = Z(G)`
    have hCtop : centralizer ((M : Subgroup G) : Set G) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ hCM'
    have hMZ : M ≤ center G :=
      Subgroup.centralizer_eq_top_iff_subset.mp hCtop
    have hZM : M = center G := le_antisymm hMZ center_le_chermakDelgadoSubgroup
    rw [← hZM]; exact heq

end -- Problem 1G.1

end OddOrder.Isaacs.Ch01
