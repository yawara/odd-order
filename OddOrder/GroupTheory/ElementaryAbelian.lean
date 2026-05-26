/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import OddOrder.Mathlib.Subgroup

/-!
# Elementary Abelian Groups

`OddOrder.GroupTheory` shared module: 'elementary abelian p-group' の概念.

mathlib v4.29.1 にはこの概念 ("G abelian かつ ∀ x, x^p = 1") が無いため, 本リポジトリの
Ch.3 (Isaacs Thm 3.11), Ch.6 (6.9/6.15), Ch.7 (J(P) 定義) 共通の shared concept として
独立 module に切り出す. BG App.A, App.B (Puig L(S)) も将来再利用する.

## Main definitions

* `OddOrder.GroupTheory.IsElementaryAbelian p G`: 群 `G` が `p`-elementary abelian.
* `Subgroup.IsElementaryAbelian H p`: 部分群 `H ≤ G` が `p`-elementary abelian
  (whole-group form を `↥H` に適用; dot-notation friendly).

## Design notes

* `p` prime 仮定は def 段階では入れない (mathlib 慣用). 主結果記述時に `[Fact p.Prime]` 付与.
* def 形式は **(commute) ∧ (∀ x, x^p = 1)** を採用 (Ch.3 既存実装と整合). 別形式
  `IsPGroup p G ∧ Monoid.exponent G ∣ p` への bridge は将来追加可.
* 将来 mathlib upstream 視野で `OddOrder/Mathlib/ElementaryAbelian.lean` 候補.
-/

namespace OddOrder.GroupTheory

/-- **Elementary Abelian p-Group** (type-level): `G` is `p`-elementary abelian iff
`G` is abelian and `∀ x : G, x ^ p = 1`. -/
def IsElementaryAbelian (p : ℕ) (G : Type*) [Group G] : Prop :=
  (∀ x y : G, x * y = y * x) ∧ (∀ x : G, x ^ p = 1)

namespace IsElementaryAbelian

variable {p : ℕ} {G : Type*} [Group G]

/-- Commutativity projection. -/
theorem comm (h : IsElementaryAbelian p G) (x y : G) : x * y = y * x := h.1 x y

/-- `p`-th power projection. -/
theorem pow_eq_one (h : IsElementaryAbelian p G) (x : G) : x ^ p = 1 := h.2 x

/-- An elementary abelian `p`-group is a `p`-group. -/
theorem isPGroup (h : IsElementaryAbelian p G) : IsPGroup p G := fun x =>
  ⟨1, by simpa using h.pow_eq_one x⟩

/-- Subgroups of elementary abelian groups are elementary abelian. -/
theorem to_subgroup (h : IsElementaryAbelian p G) (H : Subgroup G) :
    IsElementaryAbelian p H := by
  refine ⟨?_, ?_⟩
  · intro x y
    ext
    exact h.comm (x : G) (y : G)
  · intro x
    ext
    exact h.pow_eq_one (x : G)

/-- A noncyclic finite group of order `p^2` is elementary abelian. -/
theorem of_card_prime_sq_of_not_isCyclic
    [Finite G] (hp : p.Prime) (hCard : Nat.card G = p ^ 2)
    (hNotCyclic : ¬ IsCyclic G) :
    IsElementaryAbelian p G := by
  letI : Fact p.Prime := ⟨hp⟩
  have hExp : Monoid.exponent G = p :=
    (not_isCyclic_iff_exponent_eq_prime hp hCard).mp hNotCyclic
  refine ⟨IsPGroup.commutative_of_card_eq_prime_sq (p := p) hCard, ?_⟩
  intro x
  simpa [hExp] using (Monoid.pow_exponent_eq_one x)

/-- A finite elementary abelian group of order `p^2` is not cyclic. -/
theorem not_isCyclic_of_card_prime_sq
    [Finite G] (hp : p.Prime) (h : IsElementaryAbelian p G)
    (hCard : Nat.card G = p ^ 2) :
    ¬ IsCyclic G := by
  intro hcyc
  haveI : IsCyclic G := hcyc
  have hExp_eq : Monoid.exponent G = Nat.card G := IsCyclic.exponent_eq_card
  have hExp_dvd_p : Monoid.exponent G ∣ p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    exact h.pow_eq_one
  rw [hCard] at hExp_eq
  rw [hExp_eq] at hExp_dvd_p
  have hp_lt_sq : p < p ^ 2 := by
    have hp_pow : p ^ 1 < p ^ 2 :=
      pow_lt_pow_right₀ hp.one_lt (by norm_num : (1 : ℕ) < 2)
    simpa using hp_pow
  exact (Nat.not_dvd_of_pos_of_lt hp.pos hp_lt_sq) hExp_dvd_p

/-- An elementary abelian group of order `p^2` has at least two distinct subgroups of order `p`.
-/
theorem exists_distinct_subgroups_card_prime_of_card_prime_sq
    [Finite G] (hp : p.Prime) (h : IsElementaryAbelian p G)
    (hCard : Nat.card G = p ^ 2) :
    ∃ H K : Subgroup G, Nat.card H = p ∧ Nat.card K = p ∧ H ≠ K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hNotCyclic : ¬ IsCyclic G := h.not_isCyclic_of_card_prime_sq hp hCard
  have hCard_gt_one : 1 < Nat.card G := by
    rw [hCard]
    exact one_lt_pow₀ hp.one_lt two_ne_zero
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hCard_gt_one
  obtain ⟨x, hx_ne⟩ := exists_ne (1 : G)
  let H : Subgroup G := Subgroup.zpowers x
  have hx_order : orderOf x = p := orderOf_eq_prime (h.pow_eq_one x) hx_ne
  have hH_card : Nat.card H = p := by
    rw [show H = Subgroup.zpowers x from rfl, Nat.card_zpowers, hx_order]
  have hH_ne_top : H ≠ ⊤ := by
    intro hH_top
    exact hNotCyclic ((isCyclic_iff_exists_zpowers_eq_top (α := G)).mpr ⟨x, hH_top⟩)
  have h_exists_not_mem : ∃ y : G, y ∉ H := by
    by_contra hAll
    apply hH_ne_top
    ext y
    constructor
    · intro hy
      exact Subgroup.mem_top y
    · intro _hy
      by_contra hyH
      exact hAll ⟨y, hyH⟩
  obtain ⟨y, hy_not_mem⟩ := h_exists_not_mem
  let K : Subgroup G := Subgroup.zpowers y
  have hy_ne : y ≠ 1 := by
    intro hy
    exact hy_not_mem (hy ▸ H.one_mem)
  have hy_order : orderOf y = p := orderOf_eq_prime (h.pow_eq_one y) hy_ne
  have hK_card : Nat.card K = p := by
    rw [show K = Subgroup.zpowers y from rfl, Nat.card_zpowers, hy_order]
  refine ⟨H, K, hH_card, hK_card, ?_⟩
  intro hHK
  exact hy_not_mem (hHK ▸ Subgroup.mem_zpowers y)

/-- A finite elementary abelian group of cardinality at least `p^2` contains an elementary
abelian subgroup of order `p^2`. -/
theorem exists_subgroup_card_prime_sq
    [Finite G] (hp : p.Prime) (h : IsElementaryAbelian p G)
    (hCard : p ^ 2 ≤ Nat.card G) :
    ∃ H : Subgroup G, IsElementaryAbelian p H ∧ Nat.card H = p ^ 2 := by
  obtain ⟨H, hH_card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card (n := 2) hp h.isPGroup hCard
  exact ⟨H, h.to_subgroup H, hH_card⟩

end IsElementaryAbelian

end OddOrder.GroupTheory

namespace IsPGroup

variable {p : ℕ} {G : Type*} [Group G]

open scoped Pointwise

private theorem subgroup_normal_of_le_center {H : Subgroup G} (hH : H ≤ Subgroup.center G) :
    H.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn_center : n ∈ Subgroup.center G := hH hn
  have hgn : g * n = n * g := Subgroup.mem_center_iff.mp hn_center g
  have hconj : g * n * g⁻¹ = n := by
    calc
      g * n * g⁻¹ = n * g * g⁻¹ := by rw [hgn]
      _ = n := by simp
  rwa [hconj]

/-- A nontrivial finite `p`-group contains a central subgroup of order `p`. -/
theorem exists_subgroup_le_center_card_prime
    [Finite G] [Fact p.Prime] (hG : IsPGroup p G) [Nontrivial G] :
    ∃ Z : Subgroup G, Z ≤ Subgroup.center G ∧ Nat.card Z = p := by
  haveI hCenter_nontrivial : Nontrivial (Subgroup.center G) := hG.center_nontrivial
  have hCenter_card_gt : 1 < Nat.card (Subgroup.center G) :=
    Finite.one_lt_card_iff_nontrivial.mpr hCenter_nontrivial
  have hCenter_pgroup : IsPGroup p (Subgroup.center G) := hG.to_subgroup _
  have hp_dvd_center : p ∣ Nat.card (Subgroup.center G) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hCenter_pgroup
    rw [hn] at hCenter_card_gt ⊢
    have hn_pos : 0 < n := by
      cases n with
      | zero =>
          simp at hCenter_card_gt
      | succ n =>
          exact Nat.succ_pos n
    exact dvd_pow_self p hn_pos.ne'
  obtain ⟨z, hz_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.center G) p hp_dvd_center
  let Z : Subgroup G := Subgroup.zpowers (z : G)
  have hZ_le_center : Z ≤ Subgroup.center G := Subgroup.zpowers_le.mpr z.2
  have hZ_card : Nat.card Z = p := by
    rw [show Z = Subgroup.zpowers (z : G) from rfl, Nat.card_zpowers]
    exact (Subgroup.orderOf_coe z).trans hz_order
  exact ⟨Z, hZ_le_center, hZ_card⟩

/-- If a finite `p`-group has two distinct subgroups of order `p`, then it contains an
elementary abelian subgroup of order `p^2`. -/
theorem exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_ne
    [Finite G] [Fact p.Prime] (hG : IsPGroup p G)
    {K L : Subgroup G} (hK_card : Nat.card K = p) (hL_card : Nat.card L = p)
    (hKL_ne : K ≠ L) :
    ∃ E : Subgroup G, OddOrder.GroupTheory.IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 := by
  classical
  haveI : Nontrivial K := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hK_card]
    exact (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk_ne⟩ := exists_ne (1 : K)
  haveI : Nontrivial G := ⟨⟨(k : G), 1, fun hk => hk_ne (Subtype.ext hk)⟩⟩
  obtain ⟨Z, hZ_le_center, hZ_card⟩ := hG.exists_subgroup_le_center_card_prime
  let U : Subgroup G := if Z = K then L else K
  have hU_card : Nat.card U = p := by
    by_cases hZK : Z = K
    · simp [U, hZK, hL_card]
    · simp [U, hZK, hK_card]
  have hZU_ne : Z ≠ U := by
    by_cases hZK : Z = K
    · simp [U, hZK, hKL_ne]
    · simp [U, hZK]
  have hInf_bot : Z ⊓ U = ⊥ := by
    have hInf_dvd : Nat.card (Z ⊓ U : Subgroup G) ∣ p := by
      rw [← hU_card]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Fact.out).mp hInf_dvd with hInf_card | hInf_card
    · exact Subgroup.eq_bot_of_card_eq _ hInf_card
    · exfalso
      have hInf_eq_Z : Z ⊓ U = Z :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hInf_card, hZ_card])
      have hInf_eq_U : Z ⊓ U = U :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hInf_card, hU_card])
      exact hZU_ne (hInf_eq_Z.symm.trans hInf_eq_U)
  haveI hZ_normal : Z.Normal := subgroup_normal_of_le_center hZ_le_center
  let E : Subgroup G := Z ⊔ U
  have hE_card : Nat.card E = p ^ 2 := by
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card Z U
    rw [← Subgroup.normal_mul Z U, hInf_bot, Subgroup.card_bot, hZ_card, hU_card, mul_one] at hcard
    simpa [E, pow_two] using hcard
  have hE_set : (E : Set G) = (Z : Set G) * (U : Set G) := by
    simpa [E] using (Subgroup.normal_mul Z U)
  have hZ_pow : ∀ z ∈ Z, z ^ p = 1 := by
    intro z hz
    have hz_pow := pow_card_eq_one' (G := Z) (x := (⟨z, hz⟩ : Z))
    have hz_pow_coe := congrArg Subtype.val hz_pow
    simpa [hZ_card] using hz_pow_coe
  have hU_pow : ∀ u ∈ U, u ^ p = 1 := by
    intro u hu
    have hu_pow := pow_card_eq_one' (G := U) (x := (⟨u, hu⟩ : U))
    have hu_pow_coe := congrArg Subtype.val hu_pow
    simpa [hU_card] using hu_pow_coe
  have hZ_comm : ∀ z ∈ Z, ∀ g : G, z * g = g * z := by
    intro z hz g
    exact (Subgroup.mem_center_iff.mp (hZ_le_center hz) g).symm
  have hU_comm : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ * u₂ = u₂ * u₁ := by
    haveI : IsCyclic U := isCyclic_of_prime_card hU_card
    letI : CommGroup U := IsCyclic.commGroup
    intro u₁ hu₁ u₂ hu₂
    have hcomm : (⟨u₁, hu₁⟩ : U) * ⟨u₂, hu₂⟩ = ⟨u₂, hu₂⟩ * ⟨u₁, hu₁⟩ :=
      mul_comm _ _
    exact congrArg Subtype.val hcomm
  refine ⟨E, ?_, hE_card⟩
  constructor
  · intro x y
    obtain ⟨zx, hzx, ux, hux, hx_prod⟩ : ∃ zx ∈ Z, ∃ ux ∈ U, zx * ux = (x : G) := by
      have hx_mem : (x : G) ∈ (Z : Set G) * (U : Set G) := by
        rw [← hE_set]
        exact x.2
      simpa only [Set.mem_mul] using hx_mem
    obtain ⟨zy, hzy, uy, huy, hy_prod⟩ : ∃ zy ∈ Z, ∃ uy ∈ U, zy * uy = (y : G) := by
      have hy_mem : (y : G) ∈ (Z : Set G) * (U : Set G) := by
        rw [← hE_set]
        exact y.2
      simpa only [Set.mem_mul] using hy_mem
    apply Subtype.ext
    change (x : G) * (y : G) = (y : G) * (x : G)
    rw [← hx_prod, ← hy_prod]
    have hux_zy : Commute ux zy := (hZ_comm zy hzy ux).symm
    have hzx_zy : Commute zx zy := hZ_comm zx hzx zy
    have hux_uy : Commute ux uy := hU_comm ux hux uy huy
    have hzx_uy : Commute zx uy := hZ_comm zx hzx uy
    calc
      (zx * ux) * (zy * uy) = zx * ux * (zy * uy) := by rw [mul_assoc]
      _ = zx * zy * (ux * uy) := hux_zy.mul_mul_mul_comm zx uy
      _ = zy * zx * (uy * ux) := by rw [hzx_zy.eq, hux_uy.eq]
      _ = zy * uy * (zx * ux) := hzx_uy.mul_mul_mul_comm zy ux
      _ = (zy * uy) * (zx * ux) := by rw [mul_assoc]
  · intro x
    obtain ⟨z, hz, u, hu, hx_prod⟩ : ∃ z ∈ Z, ∃ u ∈ U, z * u = (x : G) := by
      have hx_mem : (x : G) ∈ (Z : Set G) * (U : Set G) := by
        rw [← hE_set]
        exact x.2
      simpa only [Set.mem_mul] using hx_mem
    apply Subtype.ext
    change ((x : G) ^ p) = 1
    rw [← hx_prod]
    have hzu : Commute z u := hZ_comm z hz u
    rw [hzu.mul_pow, hZ_pow z hz, hU_pow u hu, one_mul]

end IsPGroup

namespace Subgroup

variable {G : Type*} [Group G]

/-- **Subgroup is Elementary Abelian**: subgroup `H ≤ G` is `p`-elementary abelian iff
the subtype `↥H` is `p`-elementary abelian as a group. -/
def IsElementaryAbelian (H : Subgroup G) (p : ℕ) : Prop :=
  OddOrder.GroupTheory.IsElementaryAbelian p ↥H

/-- An elementary abelian subgroup of order `p^2` contains two distinct ambient subgroups of
order `p`. -/
theorem exists_distinct_subgroups_card_prime_of_isElementaryAbelian_card_prime_sq
    {H : Subgroup G} [Finite H] {p : ℕ} (hp : p.Prime)
    (hH : H.IsElementaryAbelian p) (hCard : Nat.card H = p ^ 2) :
    ∃ K L : Subgroup G, K ≤ H ∧ L ≤ H ∧
      Nat.card K = p ∧ Nat.card L = p ∧ K ≠ L := by
  obtain ⟨K₀, L₀, hK₀_card, hL₀_card, hK₀L₀_ne⟩ :=
    hH.exists_distinct_subgroups_card_prime_of_card_prime_sq hp hCard
  let K : Subgroup G := K₀.map H.subtype
  let L : Subgroup G := L₀.map H.subtype
  have hK_card : Nat.card K = p := by
    rw [show K = K₀.map H.subtype from rfl,
      Subgroup.card_map_of_injective H.subtype_injective, hK₀_card]
  have hL_card : Nat.card L = p := by
    rw [show L = L₀.map H.subtype from rfl,
      Subgroup.card_map_of_injective H.subtype_injective, hL₀_card]
  have hKL_ne : K ≠ L := by
    intro hKL
    exact hK₀L₀_ne (Subgroup.map_injective H.subtype_injective hKL)
  exact ⟨K, L, Subgroup.map_subtype_le K₀, Subgroup.map_subtype_le L₀,
    hK_card, hL_card, hKL_ne⟩

/-- If `G` contains an elementary abelian subgroup of order `p^2`, then `G` contains two
distinct subgroups of order `p`. -/
theorem exists_distinct_subgroups_card_prime_of_exists_isElementaryAbelian_card_prime_sq
    {p : ℕ} (hp : p.Prime)
    (hExists : ∃ H : Subgroup G, H.IsElementaryAbelian p ∧ Nat.card H = p ^ 2) :
    ∃ K L : Subgroup G, Nat.card K = p ∧ Nat.card L = p ∧ K ≠ L := by
  obtain ⟨H, hH_elem, hH_card⟩ := hExists
  haveI : Finite H := Nat.finite_of_card_ne_zero (by
    rw [hH_card]
    exact pow_ne_zero 2 hp.ne_zero)
  obtain ⟨K, L, _hK_le, _hL_le, hK_card, hL_card, hKL_ne⟩ :=
    exists_distinct_subgroups_card_prime_of_isElementaryAbelian_card_prime_sq
      hp hH_elem hH_card
  exact ⟨K, L, hK_card, hL_card, hKL_ne⟩

/-- If `G` has at most one subgroup of order `p`, then it contains no elementary abelian
subgroup of order `p^2`. -/
theorem not_exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_unique
    {p : ℕ} (hp : p.Prime)
    (hUnique : ∀ K L : Subgroup G, Nat.card K = p → Nat.card L = p → K = L) :
    ¬ ∃ H : Subgroup G, H.IsElementaryAbelian p ∧ Nat.card H = p ^ 2 := by
  intro hExists
  obtain ⟨K, L, hK_card, hL_card, hKL_ne⟩ :=
    exists_distinct_subgroups_card_prime_of_exists_isElementaryAbelian_card_prime_sq
      hp hExists
  exact hKL_ne (hUnique K L hK_card hL_card)

end Subgroup
