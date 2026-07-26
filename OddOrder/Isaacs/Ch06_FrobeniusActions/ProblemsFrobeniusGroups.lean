/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.FittingSelfCentralizing
import OddOrder.Isaacs.Ch06_FrobeniusActions.KernelComplement

/-!
# Isaacs Problems 6A — Frobenius 群そのものの演習 (書籍 p. 185)

## 6A.4

**主張**: Frobenius 群 `G` (Frobenius 核 `N`) の, `N` 自身**以外**の剰余類 `Ng` は
`G` の**単一の共役類**に含まれる。

**証明**: `g ∉ N` とする。Thm 6.4 (4) (`IsFrobeniusGroup.centralizer_kernel_le`) より
`1 ≠ m ∈ N` なら `C_G(m) ⊆ N` なので, `g ∉ N` から **`C_N(g) = 1`**。したがって
`f : N → N`, `f(m) = m g m⁻¹ g⁻¹` は単射 (`f(m₁) = f(m₂)` ⟹ `m₂⁻¹m₁ ∈ C_N(g) = 1`)。
`N` は有限なので `f` は**全射**でもあり, 任意の `n ∈ N` に対し `m g m⁻¹ = n g` なる
`m ∈ N` が取れる — すなわち `n g` は `g` に共役。

## 6A.5

**主張**: 非可換**可解**群 `G` で任意の非単位元の中心化群が可換 (**CA 群**) なら, `G` は
Frobenius 群であり Frobenius 核は `F(G)`。証明は `F(G)` が可換になること
(`Z(F(G)) ≠ 1` の元の中心化群が可換) と, 可解群での自己中心化性 `C_G(F(G)) ⊆ F(G)`
(P. Hall) を Thm 6.7 に流し込む。
-/

namespace OddOrder.Isaacs.Ch06

open Pointwise

section /- 6A.4: `N` 以外の剰余類は単一の共役類 (p. 185) -/

variable {G : Type*} [Group G] [Finite G] {N A : Subgroup G}

/-- Frobenius 群の核 `N` の外の元 `g` は, `N` の非単位元と可換にならない (`C_N(g) = 1`)。

Thm 6.4 (4) (`centralizer_kernel_le`) の対偶。 -/
theorem eq_one_of_mem_kernel_of_commute (hF : IsFrobeniusGroup G N A) {g : G} (hg : g ∉ N)
    {m : G} (hm : m ∈ N) (hcomm : m * g = g * m) : m = 1 := by
  by_contra hmne
  exact hg (hF.centralizer_kernel_le m hm hmne
    (Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm))

/-- **Isaacs Problem 6A.4** (p. 185) ⭐: Frobenius 群 `G` (核 `N`) で `g ∉ N` なら,
剰余類 `Ng` の元はすべて `g` に共役 — すなわち `Ng` は単一の共役類に含まれる。 -/
theorem isConj_mul_of_notMem_kernel (hF : IsFrobeniusGroup G N A) {g : G} (hg : g ∉ N)
    {n : G} (hn : n ∈ N) : IsConj g (n * g) := by
  classical
  haveI := hF.isNormal
  -- `m ↦ m g m⁻¹ g⁻¹` は `N` から `N` への写像
  have hmem : ∀ m : ↥N, (m : G) * g * (m : G)⁻¹ * g⁻¹ ∈ N := by
    intro m
    have h1 : g * ((m : G)⁻¹) * g⁻¹ ∈ N := hF.isNormal.conj_mem _ (inv_mem m.2) g
    have h2 : (m : G) * g * (m : G)⁻¹ * g⁻¹ = (m : G) * (g * (m : G)⁻¹ * g⁻¹) := by group
    rw [h2]
    exact Subgroup.mul_mem _ m.2 h1
  set f : ↥N → ↥N := fun m => ⟨(m : G) * g * (m : G)⁻¹ * g⁻¹, hmem m⟩ with hfdef
  -- `C_N(g) = 1` から単射
  have hinj : Function.Injective f := by
    intro m₁ m₂ h
    have hval : (m₁ : G) * g * (m₁ : G)⁻¹ * g⁻¹ = (m₂ : G) * g * (m₂ : G)⁻¹ * g⁻¹ :=
      congrArg Subtype.val h
    have h' : (m₁ : G) * g * (m₁ : G)⁻¹ = (m₂ : G) * g * (m₂ : G)⁻¹ := mul_right_cancel hval
    have hc : ((m₂ : G)⁻¹ * (m₁ : G)) * g = g * ((m₂ : G)⁻¹ * (m₁ : G)) := by
      calc ((m₂ : G)⁻¹ * (m₁ : G)) * g
          = (m₂ : G)⁻¹ * ((m₁ : G) * g * (m₁ : G)⁻¹) * (m₁ : G) := by group
        _ = (m₂ : G)⁻¹ * ((m₂ : G) * g * (m₂ : G)⁻¹) * (m₁ : G) := by rw [h']
        _ = g * ((m₂ : G)⁻¹ * (m₁ : G)) := by group
    have hone := eq_one_of_mem_kernel_of_commute hF hg
      (Subgroup.mul_mem _ (inv_mem m₂.2) m₁.2) hc
    exact (Subtype.ext (inv_mul_eq_one.mp hone)).symm
  -- 有限性から全射, その原像が求める共役元
  obtain ⟨m, hm⟩ := Finite.injective_iff_surjective.mp hinj ⟨n, hn⟩
  refine isConj_iff.mpr ⟨(m : G), ?_⟩
  have hval : (m : G) * g * (m : G)⁻¹ * g⁻¹ = n := congrArg Subtype.val hm
  calc (m : G) * g * (m : G)⁻¹ = ((m : G) * g * (m : G)⁻¹ * g⁻¹) * g := by group
    _ = n * g := by rw [hval]

/-- **Isaacs Problem 6A.4** の集合形: `g ∉ N` なら剰余類 `N · g` は `g` の共役類に含まれる。 -/
theorem coset_subset_setOf_isConj (hF : IsFrobeniusGroup G N A) {g : G} (hg : g ∉ N) :
    (N : Set G) * {g} ⊆ {y | IsConj g y} := by
  rintro _ ⟨n, hn, _, rfl, rfl⟩
  exact isConj_mul_of_notMem_kernel hF hg hn

end

section /- 6A.5: CA 群 (中心化群がすべて可換) は Frobenius 群 (p. 185) -/

/-- **Isaacs Problem 6A.5** (p. 185) ⭐: 非可換**可解**群 `G` で, 任意の非単位元の中心化群が
可換 (いわゆる **CA 群**) なら, `G` は Frobenius 群であり Frobenius 核は `F(G)`。

**証明**:
1. `F := F(G)` は非自明 (可解非自明) で冪零ゆえ `Z(F) ≠ 1`。`1 ≠ z ∈ Z(F)` を取ると
   `F ⊆ C_G(z)` で `C_G(z)` は可換 ⟹ **`F` は可換**。
2. `1 ≠ n ∈ F` について `F ⊆ C_G(n)` (可換性) で, `C_G(n)` の元は `F` の元と可換
   (どちらも `C_G(n)` に入り `C_G(n)` は可換) ⟹ `C_G(n) ⊆ C_G(F) ⊆ F`
   (P. Hall: 可解群では Fitting 部分群は自己中心化的)。
3. `F ≠ ⊤` (さもないと `G = F` は可換), `F ≠ ⊥` ⟹ **Thm 6.7**
   (`exists_isComplement'_of_centralizer_le`) が Frobenius 構造を与える。 -/
theorem exists_isFrobeniusGroup_fitting_of_centralizer_comm
    {G : Type*} [Group G] [Finite G] [IsSolvable G]
    (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hCA : ∀ x : G, x ≠ 1 → ∀ u v : G, u ∈ Subgroup.centralizer ({x} : Set G) →
      v ∈ Subgroup.centralizer ({x} : Set G) → u * v = v * u) :
    ∃ A : Subgroup G, IsFrobeniusGroup G (Ch01.fitting G) A := by
  classical
  haveI : Nontrivial G := by
    obtain ⟨x, y, hxy⟩ := hnonab
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hxy (by rw [Subsingleton.elim x (1 : G), Subsingleton.elim y (1 : G)])
  set F : Subgroup G := Ch01.fitting G with hFdef
  have hFbot : F ≠ ⊥ := Ch01.fitting_ne_bot_of_solvable_nontrivial G
  haveI : Nontrivial ↥F := (Subgroup.nontrivial_iff_ne_bot F).mpr hFbot
  -- (1) `Z(F) ≠ 1` の元を取って `F` が可換であることを出す
  haveI hZ : Nontrivial (Subgroup.center ↥F) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (Group.IsNilpotent.center_ne_bot ↥F)
  obtain ⟨z₀, hz₀ne⟩ := exists_ne (1 : Subgroup.center ↥F)
  set z : G := ((z₀ : ↥F) : G) with hzdef
  have hzF : z ∈ F := (z₀ : ↥F).2
  have hzne : z ≠ 1 := by
    intro h
    exact hz₀ne (Subtype.ext (Subtype.ext h))
  have hFcentz : ∀ w ∈ F, w ∈ Subgroup.centralizer ({z} : Set G) := by
    intro w hw
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hcz := (Subgroup.mem_center_iff.mp (z₀ : Subgroup.center ↥F).2) ⟨w, hw⟩
    simpa [hzdef] using congrArg Subtype.val hcz
  have hFcomm : ∀ u ∈ F, ∀ v ∈ F, u * v = v * u := fun u hu v hv =>
    hCA z hzne u v (hFcentz u hu) (hFcentz v hv)
  -- (2) `1 ≠ n ∈ F` について `C_G(n) ≤ F`
  have hCF : ∀ n ∈ F, n ≠ 1 → Subgroup.centralizer ({n} : Set G) ≤ F := by
    intro n hnF hnne c hc
    refine OddOrder.GroupTheory.centralizer_fitting_le_fitting ?_
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro w hw
    refine (hCA n hnne c w hc ?_).symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hFcomm w hw n hnF)
  -- (3) `F ≠ ⊤` (さもないと `G` が可換)
  have hFtop : F ≠ ⊤ := by
    intro htop
    obtain ⟨x, y, hxy⟩ := hnonab
    exact hxy (hFcomm x (htop ▸ Subgroup.mem_top x) y (htop ▸ Subgroup.mem_top y))
  obtain ⟨A, _, hfrob⟩ := exists_isComplement'_of_centralizer_le (N := F) hCF
  exact ⟨A, hfrob hFbot hFtop⟩

end

end OddOrder.Isaacs.Ch06
