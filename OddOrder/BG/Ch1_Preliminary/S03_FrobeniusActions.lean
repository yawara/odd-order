/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main

/-!
# BG §3: Actions of Frobenius Groups and Related Results

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §3 (pp. 17-32), mmd
`references/bg/local-analysis.mmd` L795-1358, **10 結果** (Lemma 3.1-3.10).

## 構造 (BG §3 全 10 結果)

- **§3A** Frobenius group basics (Lemma 3.1, Lemma 3.2)
- **§3B** Representation-theoretic Frobenius action (Lemma 3.3, Theorem 3.4,
  Theorem 3.5)
- **§3C** Z-group centralizer and p-length (Theorem 3.6)
- **§3D** Frobenius kernel nilpotence and Fitting control (Theorem 3.7,
  Theorem 3.8)
- **§3E** Regular actions and nilpotent targets (Proposition 3.9, Theorem 3.10)

## Current status

This file starts the BG §3 layer over the existing Isaacs Ch.6 Frobenius API.
The first implemented results are the BG Lemma 3.1 equivalence between the
Frobenius group structure on `G = K R` and the fixed-point-free conjugation
condition `C_K(x) = 1` for every nonidentity `x ∈ R`, plus quotient setup
lemmas for the `N ≤ K` branch of BG Lemma 3.2.

The representation-dependent results 3.3-3.6 and 3.10 will later depend on
BG §2 representation infrastructure; this initial file intentionally imports
only the Frobenius infrastructure needed for 3.1 and the first quotient setup
for 3.2.

References:
- BG mmd `references/bg/local-analysis.mmd` L795-1358.
- Section note: `notes/bg/s03_frobenius_actions.md`.
- Isaacs Ch.6 Frobenius API:
  `OddOrder/Isaacs/Ch06_FrobeniusActions/Main.lean`.
-/

namespace OddOrder.BG.Ch1.S03

open OddOrder.Isaacs.Ch06

/-! ## §3A: Frobenius group basics (Lemma 3.1, Lemma 3.2) -/

/-- **BG Lemma 3.1 (centralizer direction)**: in a Frobenius group `G = K R`,
the `K`-centralizer of every nonidentity `x ∈ R` is trivial.

The BG notation `C_K(x)=1` is represented as
`Subgroup.centralizer ({x} : Set G) ⊓ K = ⊥`. -/
theorem centralizer_complement_inf_kernel_eq_bot
    {G : Type*} [Group G] {K R : Subgroup G}
    (h : IsFrobeniusGroup G K R) :
    ∀ x ∈ R, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ⊓ K = ⊥ := by
  intro x hxR hx_ne
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_inf] at hy
  obtain ⟨hy_centralizes, hyK⟩ := hy
  rw [Subgroup.mem_bot]
  by_contra hy_ne
  rw [Subgroup.mem_centralizer_singleton_iff] at hy_centralizes
  have h_conj : x * y * x⁻¹ = y := by
    calc
      x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [← hy_centralizes]
      _ = y := mul_inv_cancel_right y x
  exact h.conj_frobenius x hxR hx_ne y hyK hy_ne h_conj

/-- **BG Lemma 3.1**: for nonidentity subgroups `K` and `R` with `K ⊴ G`,
`K` complemented by `R`, the Frobenius group structure on `G = K R` is
equivalent to `C_K(x)=1` for every nonidentity `x ∈ R`.

This is the local BG form of Isaacs Thm 6.4, specialized to a named kernel
`K` and complement `R`. -/
theorem isFrobeniusGroup_iff_complement_centralizer_inf_kernel_eq_bot
    {G : Type*} [Group G] {K R : Subgroup G}
    (hK : K.Normal) (hC : Subgroup.IsComplement' K R)
    (hK_ne : K ≠ ⊥) (hR_ne : R ≠ ⊥) :
    IsFrobeniusGroup G K R ↔
      ∀ x ∈ R, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ⊓ K = ⊥ := by
  refine ⟨centralizer_complement_inf_kernel_eq_bot, ?_⟩
  intro hcentral
  exact
    { isNormal := hK
      isComplement := hC
      ne_bot_kernel := hK_ne
      ne_bot_complement := hR_ne
      conj_frobenius := by
        intro x hxR hx_ne y hyK hy_ne h_conj
        have h_comm : y * x = x * y := by
          have h_mul := congrArg (fun z => z * x) h_conj
          simpa only [mul_assoc, inv_mul_cancel, mul_one] using h_mul.symm
        have hy_centralizes : y ∈ Subgroup.centralizer ({x} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr h_comm
        have hy_inf : y ∈ Subgroup.centralizer ({x} : Set G) ⊓ K :=
          Subgroup.mem_inf.mpr ⟨hy_centralizes, hyK⟩
        rw [hcentral x hxR hx_ne, Subgroup.mem_bot] at hy_inf
        exact hy_ne hy_inf }

/-! ### BG Lemma 3.2 quotient setup: the case `N ≤ K` -/

/-- **BG Lemma 3.2 (quotient setup, `N ≤ K`)**: if `K` and `R` complement each
other in `G`, and `N ⊴ G` lies in `K`, then their images in `G/N` still
complement each other.

This is the elementary complement part of the `N ≤ K` branch of BG Lemma 3.2.
The fixed-point-free centralizer condition in the quotient is supplied by
BG Prop. 1.5(d) / Isaacs Cor. 3.28 in the next step. -/
theorem quotient_complement_of_normal_le_kernel
    {G : Type*} [Group G] {K R N : Subgroup G} [K.Normal] [N.Normal]
    (hC : Subgroup.IsComplement' K R) (hNK : N ≤ K) :
    Subgroup.IsComplement'
      (K.map (QuotientGroup.mk' N)) (R.map (QuotientGroup.mk' N)) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff]
    ext q
    constructor
    · intro hq
      rw [Subgroup.mem_inf] at hq
      obtain ⟨hqK, hqR⟩ := hq
      obtain ⟨k, hkK, hkq⟩ := hqK
      obtain ⟨r, hrR, hrq⟩ := hqR
      rw [Subgroup.mem_bot]
      have h_eq : (QuotientGroup.mk' N) k = (QuotientGroup.mk' N) r := by
        rw [hkq, hrq]
      have h_div : k / r ∈ N :=
        (QuotientGroup.eq_iff_div_mem (N := N)).mp h_eq
      have h_divK : k / r ∈ K := hNK h_div
      have hrK : r ∈ K := by
        have hrinvK : r⁻¹ ∈ K := by
          have hmem : k⁻¹ * (k / r) ∈ K :=
            K.mul_mem (K.inv_mem hkK) h_divK
          have h_eq_inv : k⁻¹ * (k / r) = r⁻¹ := by
            rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel, one_mul]
          rwa [h_eq_inv] at hmem
        simpa using K.inv_mem hrinvK
      have hr_one : r = 1 := Subgroup.disjoint_def.mp hC.disjoint hrK hrR
      rw [← hrq, hr_one]
      simp
    · intro hq
      rw [Subgroup.mem_bot] at hq
      rw [hq]
      exact Subgroup.one_mem _
  · rw [Set.eq_univ_iff_forall]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg_top : g ∈ (K ⊔ R : Subgroup G) := by
      rw [hC.sup_eq_top]
      trivial
    rw [Subgroup.mem_sup_of_normal_left] at hg_top
    obtain ⟨k, hkK, r, hrR, hkr⟩ := hg_top
    refine ⟨QuotientGroup.mk k, ?_, QuotientGroup.mk r, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩
    · exact Subgroup.mem_map.mpr ⟨r, hrR, rfl⟩
    · change (QuotientGroup.mk k : G ⧸ N) * QuotientGroup.mk r = QuotientGroup.mk g
      rw [← QuotientGroup.mk_mul, hkr]

/-- If `K` is not contained in `N`, then the image of `K` in `G/N` is
nontrivial. -/
theorem quotient_kernel_map_ne_bot_of_not_le
    {G : Type*} [Group G] {K N : Subgroup G} [N.Normal]
    (hKN : ¬ K ≤ N) :
    K.map (QuotientGroup.mk' N) ≠ ⊥ := by
  intro hbot
  apply hKN
  intro k hkK
  have hkmap : (QuotientGroup.mk' N) k ∈ K.map (QuotientGroup.mk' N) :=
    Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hkmap
  exact (QuotientGroup.eq_one_iff k).mp hkmap

/-- If `R` is nontrivial and complements `K`, then the image of `R` in `G/N`
is still nontrivial whenever `N ≤ K`. -/
theorem quotient_complement_map_ne_bot_of_le_kernel
    {G : Type*} [Group G] {K R N : Subgroup G} [N.Normal]
    (hC : Subgroup.IsComplement' K R) (hNK : N ≤ K) (hR_ne : R ≠ ⊥) :
    R.map (QuotientGroup.mk' N) ≠ ⊥ := by
  intro hbot
  apply hR_ne
  rw [← le_bot_iff]
  intro r hrR
  have hrmap : (QuotientGroup.mk' N) r ∈ R.map (QuotientGroup.mk' N) :=
    Subgroup.mem_map.mpr ⟨r, hrR, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hrmap
  have hrN : r ∈ N := (QuotientGroup.eq_one_iff r).mp hrmap
  have hrK : r ∈ K := hNK hrN
  exact Subgroup.disjoint_def.mp hC.disjoint hrK hrR

/-- **BG Lemma 3.2 / Prop. 1.5(d) bridge**: if the cyclic group generated by
`x` fixes the coset `yN` in `K/N`, then coprime action lifts this to an
actual `x`-fixed representative in the same coset.

This is a direct wrapper around Isaacs Cor. 3.28
`OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient`, specialized to the
conjugation action of `Subgroup.zpowers x` on the normal subgroup `K`. -/
theorem fixedPoint_lift_of_zpowers_quotient_fixed
    {G : Type*} [Group G] [Finite G] {K N : Subgroup G} [K.Normal] [N.Normal]
    (hNK : N ≤ K) {x y : G}
    (hCop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥K))
    (hSolv : IsSolvable ↥(Subgroup.zpowers x) ∨ IsSolvable ↥K)
    (hyK : y ∈ K)
    (hfixed_all :
      ∀ a ∈ Subgroup.zpowers x,
        (QuotientGroup.mk' N) (a * y * a⁻¹) = (QuotientGroup.mk' N) y) :
    ∃ c : G,
      c ∈ K ∧ (QuotientGroup.mk' N) c = (QuotientGroup.mk' N) y ∧
        x * c * x⁻¹ = c := by
  let A : Subgroup G := Subgroup.zpowers x
  let φ : A →* MulAut K := (MulAut.conjNormal : G →* MulAut K).comp A.subtype
  let N_K : Subgroup K := N.subgroupOf K
  haveI hN_K_normal : N_K.Normal := (inferInstance : N.Normal).subgroupOf K
  have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ N_K := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a n hn
    change ((MulAut.conjNormal (a : G)) n).val ∈ N
    rw [MulAut.conjNormal_apply]
    exact (inferInstance : N.Normal).conj_mem n.val hn (a : G)
  let yK : K := ⟨y, hyK⟩
  have hy_fix :
      ∀ a : A, ∃ n ∈ N_K, (φ a) yK = yK * n := by
    intro a
    have hq : (QuotientGroup.mk' N) ((a : G) * y * (a : G)⁻¹) =
        (QuotientGroup.mk' N) y :=
      hfixed_all (a : G) a.property
    obtain ⟨z, hzN, hz_eq⟩ := (QuotientGroup.mk'_eq_mk' (N := N)).mp hq
    have hz_inv_N : z⁻¹ ∈ N := N.inv_mem hzN
    refine ⟨⟨z⁻¹, hNK hz_inv_N⟩, ?_, ?_⟩
    · exact hz_inv_N
    · apply Subtype.ext
      change (a : G) * y * (a : G)⁻¹ = y * z⁻¹
      exact eq_mul_inv_of_mul_eq hz_eq
  obtain ⟨cK, hc_fixed, ⟨nK, hnK, hc_coset⟩⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient
      (G := K) (A := A) (φ := φ) hCop hSolv hN_inv (g := yK) hy_fix
  refine ⟨cK, cK.property, ?_, ?_⟩
  · have hc_val : (cK : G) = y * (nK : G) := congrArg Subtype.val hc_coset
    rw [hc_val]
    change (y : G ⧸ N) * ((nK : G) : G ⧸ N) = (y : G ⧸ N)
    have hn_one : ((nK : G) : G ⧸ N) = 1 :=
      (QuotientGroup.eq_one_iff (nK : G)).mpr hnK
    rw [hn_one, mul_one]
  · have hx_mem : x ∈ A := Subgroup.mem_zpowers x
    have hx_fixed := hc_fixed ⟨x, hx_mem⟩
    have hx_fixed_val := congrArg Subtype.val hx_fixed
    simpa [φ, A, MulAut.conjNormal_apply] using hx_fixed_val

/-- If the generator `x` fixes the quotient coset `yN` by conjugation, then
every element of the cyclic subgroup generated by `x` fixes the same quotient
coset. -/
theorem zpowers_quotient_fixed_of_generator_quotient_fixed
    {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {x y : G}
    (hgen : (QuotientGroup.mk' N) (x * y * x⁻¹) = (QuotientGroup.mk' N) y) :
    ∀ a ∈ Subgroup.zpowers x,
      (QuotientGroup.mk' N) (a * y * a⁻¹) = (QuotientGroup.mk' N) y := by
  intro a ha
  obtain ⟨n, ha_eq⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [← ha_eq]
  have hgenQ :
      (x : G ⧸ N) * (y : G ⧸ N) * (x : G ⧸ N)⁻¹ = (y : G ⧸ N) := by
    change (x : G ⧸ N) * (y : G ⧸ N) * (x : G ⧸ N)⁻¹ = (y : G ⧸ N)
    exact hgen
  have hxy_comm : Commute (x : G ⧸ N) (y : G ⧸ N) := by
    have hmul := congrArg (fun z => z * (x : G ⧸ N)) hgenQ
    simpa only [commute_iff_eq, mul_assoc, inv_mul_cancel, mul_one] using hmul
  have hxpow_comm : Commute ((x : G ⧸ N) ^ n) (y : G ⧸ N) :=
    hxy_comm.zpow_left n
  have hconj :
      ((x : G ⧸ N) ^ n) * (y : G ⧸ N) * ((x : G ⧸ N) ^ n)⁻¹ =
        (y : G ⧸ N) := by
    have hmul := congrArg (fun z => z * (((x : G ⧸ N) ^ n)⁻¹)) hxpow_comm.eq
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using hmul
  have hmap : ((x ^ n : G) : G ⧸ N) = (x : G ⧸ N) ^ n := by
    simp
  change ((x ^ n : G) : G ⧸ N) * (y : G ⧸ N) *
      ((x ^ n : G) : G ⧸ N)⁻¹ = (y : G ⧸ N)
  rw [hmap]
  exact hconj

/-- **BG Lemma 3.2 / Prop. 1.5(d) bridge, generator form**: if `x` fixes
the quotient coset `yN`, then coprime action gives an actual `x`-fixed
representative in the same coset. -/
theorem fixedPoint_lift_of_generator_quotient_fixed
    {G : Type*} [Group G] [Finite G] {K N : Subgroup G} [K.Normal] [N.Normal]
    (hNK : N ≤ K) {x y : G}
    (hCop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥K))
    (hSolv : IsSolvable ↥(Subgroup.zpowers x) ∨ IsSolvable ↥K)
    (hyK : y ∈ K)
    (hgen : (QuotientGroup.mk' N) (x * y * x⁻¹) = (QuotientGroup.mk' N) y) :
    ∃ c : G,
      c ∈ K ∧ (QuotientGroup.mk' N) c = (QuotientGroup.mk' N) y ∧
        x * c * x⁻¹ = c :=
  fixedPoint_lift_of_zpowers_quotient_fixed hNK hCop hSolv hyK
    (zpowers_quotient_fixed_of_generator_quotient_fixed hgen)

/-- **BG Lemma 3.2 (quotient centralizer bridge)**: to prove
`C_{K/N}(\bar x)=1`, it is enough to know that every quotient-fixed coset in
`K/N` contains an actual `x`-fixed element of `K`.

The `hlift` hypothesis is the exact point where BG Prop. 1.5(d) / Isaacs Cor.
3.28 enters: quotient fixed points are images of fixed points upstairs. -/
theorem quotient_centralizer_inf_kernel_eq_bot_of_fixedPoint_lift
    {G : Type*} [Group G] {K R N : Subgroup G} [N.Normal]
    (hcentral :
      ∀ x ∈ R, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ⊓ K = ⊥)
    (hlift :
      ∀ x ∈ R, x ≠ 1 → ∀ y ∈ K,
        (QuotientGroup.mk' N) (x * y * x⁻¹) = (QuotientGroup.mk' N) y →
          ∃ c : G,
            c ∈ K ∧ (QuotientGroup.mk' N) c = (QuotientGroup.mk' N) y ∧
              x * c * x⁻¹ = c) :
    ∀ qx ∈ R.map (QuotientGroup.mk' N), qx ≠ 1 →
      Subgroup.centralizer ({qx} : Set (G ⧸ N)) ⊓ K.map (QuotientGroup.mk' N) = ⊥ := by
  intro qx hqxR hqx_ne
  rw [eq_bot_iff]
  intro qy hqy
  rw [Subgroup.mem_inf] at hqy
  obtain ⟨hqy_centralizes, hqyK⟩ := hqy
  obtain ⟨x, hxR, hxq⟩ := hqxR
  obtain ⟨y, hyK, hyq⟩ := hqyK
  rw [Subgroup.mem_bot]
  have hx_ne : x ≠ 1 := by
    intro hx_one
    apply hqx_ne
    rw [← hxq, hx_one]
    simp
  rw [Subgroup.mem_centralizer_singleton_iff] at hqy_centralizes
  have hq_conj : qx * qy * qx⁻¹ = qy := by
    calc
      qx * qy * qx⁻¹ = (qy * qx) * qx⁻¹ := by rw [← hqy_centralizes]
      _ = qy := mul_inv_cancel_right qy qx
  have h_conj_mod :
      (QuotientGroup.mk' N) (x * y * x⁻¹) = (QuotientGroup.mk' N) y := by
    have hxq_coe : (x : G ⧸ N) = qx := hxq
    have hyq_coe : (y : G ⧸ N) = qy := hyq
    change (x : G ⧸ N) * (y : G ⧸ N) * (x : G ⧸ N)⁻¹ = (y : G ⧸ N)
    rw [hxq_coe, hyq_coe]
    exact hq_conj
  obtain ⟨c, hcK, hcy, hc_fixed⟩ := hlift x hxR hx_ne y hyK h_conj_mod
  have hc_centralizes : c ∈ Subgroup.centralizer ({x} : Set G) := by
    have h_comm : c * x = x * c := by
      have h_mul := congrArg (fun z => z * x) hc_fixed
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h_mul.symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr h_comm
  have hc_inf : c ∈ Subgroup.centralizer ({x} : Set G) ⊓ K :=
    Subgroup.mem_inf.mpr ⟨hc_centralizes, hcK⟩
  rw [hcentral x hxR hx_ne, Subgroup.mem_bot] at hc_inf
  rw [← hyq, ← hcy, hc_inf]
  simp

/-- **BG Lemma 3.2 (quotient centralizer bridge, `C_K(x) ≤ N` form)**: a relaxation of
`quotient_centralizer_inf_kernel_eq_bot_of_fixedPoint_lift` in which the upstairs centralizers
`C_G(x) ⊓ K` need not be trivial, only land *inside the normal subgroup `N` being quotiented out*.
This still forces `C_{K/N}(\bar x) = 1`, because the lifted `x`-fixed representative `c` lies in
`C_G(x) ⊓ K ≤ N`, hence maps to `1` in `G/N`.

This is exactly the Peterfalvi (6.8)(c2) situation: there `C_K(x) = W₂ ⊆ ⁅K,K⁆ = N` (nontrivial),
so the `= ⊥` hypothesis of the original lemma fails, but the `≤ N` hypothesis holds and the
quotient `K/⁅K,K⁆` still has fixed-point-free `\bar x`-action. -/
theorem quotient_centralizer_inf_kernel_eq_bot_of_fixedPoint_lift_of_le
    {G : Type*} [Group G] {K R N : Subgroup G} [N.Normal]
    (hcentral :
      ∀ x ∈ R, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ⊓ K ≤ N)
    (hlift :
      ∀ x ∈ R, x ≠ 1 → ∀ y ∈ K,
        (QuotientGroup.mk' N) (x * y * x⁻¹) = (QuotientGroup.mk' N) y →
          ∃ c : G,
            c ∈ K ∧ (QuotientGroup.mk' N) c = (QuotientGroup.mk' N) y ∧
              x * c * x⁻¹ = c) :
    ∀ qx ∈ R.map (QuotientGroup.mk' N), qx ≠ 1 →
      Subgroup.centralizer ({qx} : Set (G ⧸ N)) ⊓ K.map (QuotientGroup.mk' N) = ⊥ := by
  intro qx hqxR hqx_ne
  rw [eq_bot_iff]
  intro qy hqy
  rw [Subgroup.mem_inf] at hqy
  obtain ⟨hqy_centralizes, hqyK⟩ := hqy
  obtain ⟨x, hxR, hxq⟩ := hqxR
  obtain ⟨y, hyK, hyq⟩ := hqyK
  rw [Subgroup.mem_bot]
  have hx_ne : x ≠ 1 := by
    intro hx_one
    apply hqx_ne
    rw [← hxq, hx_one]
    simp
  rw [Subgroup.mem_centralizer_singleton_iff] at hqy_centralizes
  have hq_conj : qx * qy * qx⁻¹ = qy := by
    calc
      qx * qy * qx⁻¹ = (qy * qx) * qx⁻¹ := by rw [← hqy_centralizes]
      _ = qy := mul_inv_cancel_right qy qx
  have h_conj_mod :
      (QuotientGroup.mk' N) (x * y * x⁻¹) = (QuotientGroup.mk' N) y := by
    have hxq_coe : (x : G ⧸ N) = qx := hxq
    have hyq_coe : (y : G ⧸ N) = qy := hyq
    change (x : G ⧸ N) * (y : G ⧸ N) * (x : G ⧸ N)⁻¹ = (y : G ⧸ N)
    rw [hxq_coe, hyq_coe]
    exact hq_conj
  obtain ⟨c, hcK, hcy, hc_fixed⟩ := hlift x hxR hx_ne y hyK h_conj_mod
  have hc_centralizes : c ∈ Subgroup.centralizer ({x} : Set G) := by
    have h_comm : c * x = x * c := by
      have h_mul := congrArg (fun z => z * x) hc_fixed
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h_mul.symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr h_comm
  have hc_inf : c ∈ Subgroup.centralizer ({x} : Set G) ⊓ K :=
    Subgroup.mem_inf.mpr ⟨hc_centralizes, hcK⟩
  have hc_N : c ∈ N := hcentral x hxR hx_ne hc_inf
  have hc_mk : (QuotientGroup.mk' N) c = 1 := (QuotientGroup.eq_one_iff c).mpr hc_N
  rw [← hyq, ← hcy, hc_mk]

/-- **BG Lemma 3.2 (quotient Frobenius assembly, `N ≤ K`)**: in the easy branch
where `N ⊴ G` lies in the Frobenius kernel `K`, the quotient is a Frobenius
group as soon as the quotient centralizer condition is known.

The missing input is exactly the BG Prop. 1.5(d) / Isaacs Cor. 3.28 step:
`C_{K/N}(\bar x)=1` for every nonidentity `\bar x ∈ RN/N`. -/
theorem quotient_isFrobeniusGroup_of_le_kernel_of_centralizer
    {G : Type*} [Group G] {K R N : Subgroup G} [N.Normal]
    (h : IsFrobeniusGroup G K R) (hNK : N ≤ K) (hKN : ¬ K ≤ N)
    (hcentral :
      ∀ x ∈ R.map (QuotientGroup.mk' N), x ≠ 1 →
        Subgroup.centralizer ({x} : Set (G ⧸ N)) ⊓
          K.map (QuotientGroup.mk' N) = ⊥) :
    IsFrobeniusGroup
      (G ⧸ N) (K.map (QuotientGroup.mk' N)) (R.map (QuotientGroup.mk' N)) := by
  letI : K.Normal := h.isNormal
  have hK_normal : (K.map (QuotientGroup.mk' N)).Normal := inferInstance
  have hC :
      Subgroup.IsComplement'
        (K.map (QuotientGroup.mk' N)) (R.map (QuotientGroup.mk' N)) :=
    quotient_complement_of_normal_le_kernel h.isComplement hNK
  have hK_ne : K.map (QuotientGroup.mk' N) ≠ ⊥ :=
    quotient_kernel_map_ne_bot_of_not_le hKN
  have hR_ne : R.map (QuotientGroup.mk' N) ≠ ⊥ :=
    quotient_complement_map_ne_bot_of_le_kernel h.isComplement hNK h.ne_bot_complement
  exact
    (isFrobeniusGroup_iff_complement_centralizer_inf_kernel_eq_bot
      hK_normal hC hK_ne hR_ne).mpr hcentral

/-- **BG Lemma 3.2 (quotient Frobenius, `N ≤ K`, fixed-point-lift form)**:
the `N ≤ K` branch reduces to the fixed-point lifting input supplied by
BG Prop. 1.5(d) / Isaacs Cor. 3.28.

This is the strongest currently packaged form of the first branch: complement
and nontriviality are proved here, while the remaining mathematical input is
isolated in `hlift`. -/
theorem quotient_isFrobeniusGroup_of_le_kernel_of_fixedPoint_lift
    {G : Type*} [Group G] {K R N : Subgroup G} [N.Normal]
    (h : IsFrobeniusGroup G K R) (hNK : N ≤ K) (hKN : ¬ K ≤ N)
    (hlift :
      ∀ x ∈ R, x ≠ 1 → ∀ y ∈ K,
        (QuotientGroup.mk' N) (x * y * x⁻¹) = (QuotientGroup.mk' N) y →
          ∃ c : G,
            c ∈ K ∧ (QuotientGroup.mk' N) c = (QuotientGroup.mk' N) y ∧
              x * c * x⁻¹ = c) :
    IsFrobeniusGroup
      (G ⧸ N) (K.map (QuotientGroup.mk' N)) (R.map (QuotientGroup.mk' N)) := by
  refine quotient_isFrobeniusGroup_of_le_kernel_of_centralizer h hNK hKN ?_
  exact
    quotient_centralizer_inf_kernel_eq_bot_of_fixedPoint_lift
      (centralizer_complement_inf_kernel_eq_bot h) hlift

/-- **BG Lemma 3.2 (quotient Frobenius, `N ≤ K`, coprime-action form)**:
the first branch follows once each nonidentity complement element has cyclic
order coprime to `K` and the kernel side is solvable.

This packages the fixed-point lifting input via Isaacs Cor. 3.28; deriving the
coprimality hypothesis from the Frobenius setup is left as a separate lemma. -/
theorem quotient_isFrobeniusGroup_of_le_kernel_of_coprime_zpowers
    {G : Type*} [Group G] [Finite G] {K R N : Subgroup G} [N.Normal]
    (h : IsFrobeniusGroup G K R) (hNK : N ≤ K) (hKN : ¬ K ≤ N)
    (hCop : ∀ x, x ∈ R → x ≠ 1 →
      Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥K))
    (hSolvK : IsSolvable ↥K) :
    IsFrobeniusGroup
      (G ⧸ N) (K.map (QuotientGroup.mk' N)) (R.map (QuotientGroup.mk' N)) := by
  letI : K.Normal := h.isNormal
  refine quotient_isFrobeniusGroup_of_le_kernel_of_fixedPoint_lift h hNK hKN ?_
  intro x hxR hx_ne y hyK hgen
  exact
    fixedPoint_lift_of_generator_quotient_fixed hNK (hCop x hxR hx_ne)
      (Or.inr hSolvK) hyK hgen

/-! ### BG Lemma 3.2: the general branch `K ⊄ N`

The `N ≤ K` branch above produces the Frobenius quotient as soon as `N ≤ K`.  The full
statement of BG Lemma 3.2 reduces the *arbitrary* normal subgroup `N` (with `K ⊄ N`) to that
branch by first proving `N ⊆ K`.  The crux is that `N` meets the complement `R` trivially. -/

/-- **BG Lemma 3.2, crux step** (mmd L837-843): in a finite Frobenius group `G = K R` with
solvable kernel `K`, if `N ⊴ G` and `K ⊄ N`, then `N ⊓ R = ⊥`.

*Proof.*  Pass to `Ĝ = G / (N ⊓ K)`, which is a Frobenius group with kernel `K̂` and complement
`R̂` by the `N ≤ K` branch (`quotient_isFrobeniusGroup_of_le_kernel_of_coprime_zpowers`, applied
with the quotient subgroup `N ⊓ K ≤ K`).  The image `Ĵ` of `N ⊓ R` lies in `R̂` and is
centralized by `K̂`, because `[N ⊓ R, K] ⊆ N ⊓ K`: for `x ∈ K`, `j ∈ N ⊓ R`, the element
`x j x⁻¹ j⁻¹` lies in `N` (normality of `N`) and in `K` (normality of `K`).  Hence for any
nonidentity `x̂ ∈ K̂` the conjugate `Ĵ^x̂` equals `Ĵ`, so `Ĵ ⊆ R̂ ⊓ R̂^x̂ = ⊥`
(`trivialIntersection`).  Therefore `N ⊓ R ⊆ N ⊓ K ⊆ K`, and as `N ⊓ R ⊆ R` with
`K ⊓ R = ⊥`, we get `N ⊓ R = ⊥`. -/
theorem inf_complement_eq_bot_of_normal_not_le_kernel
    {G : Type*} [Group G] [Finite G] {K R N : Subgroup G} [hN : N.Normal]
    (h : IsFrobeniusGroup G K R) (hKN : ¬ K ≤ N) (hSolvK : IsSolvable ↥K) :
    N ⊓ R = ⊥ := by
  letI : K.Normal := h.isNormal
  -- `N ⊓ K` is normal.
  haveI hHnormal : (N ⊓ K).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_inf] at hn ⊢
    exact ⟨hN.conj_mem n hn.1 g, (inferInstance : K.Normal).conj_mem n hn.2 g⟩
  -- Coprimality input for the quotient Frobenius assembly: every complement element generates a
  -- cyclic group whose order divides `|R|`, hence is coprime to `|K|`.
  have hCop : ∀ x, x ∈ R → x ≠ 1 →
      Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥K) := by
    intro x hxR _
    have hdvd : Nat.card ↥(Subgroup.zpowers x) ∣ Nat.card ↥R :=
      Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxR)
    exact Nat.Coprime.coprime_dvd_left hdvd (h.coprime_card_kernel_complement).symm
  -- `K ⊄ N ⊓ K` (else `K ≤ N`).
  have hKH : ¬ K ≤ N ⊓ K := fun hKle => hKN (hKle.trans inf_le_left)
  -- `Ĝ = G / (N ⊓ K)` is a Frobenius group with kernel `K̂` and complement `R̂`.
  set mkH := QuotientGroup.mk' (N ⊓ K) with hmkH
  have hFrobQ : IsFrobeniusGroup (G ⧸ (N ⊓ K)) (K.map mkH) (R.map mkH) :=
    quotient_isFrobeniusGroup_of_le_kernel_of_coprime_zpowers h inf_le_right hKH hCop hSolvK
  -- A nonidentity `x̂ ∈ K̂`, lifted to `x ∈ K`.
  obtain ⟨xh, hxh_mem, hxh_ne⟩ :=
    (K.map mkH).bot_or_exists_ne_one.resolve_left hFrobQ.ne_bot_kernel
  obtain ⟨x, hxK, hx_eq⟩ := Subgroup.mem_map.mp hxh_mem
  -- `x̂ ∉ R̂` (complement).
  have hxh_not_R : xh ∉ R.map mkH := fun hmem =>
    hxh_ne (Subgroup.disjoint_def.mp hFrobQ.isComplement.disjoint hxh_mem hmem)
  -- Trivial intersection of `R̂` with its `x̂`-conjugate.
  have hTI : R.map mkH ⊓ Subgroup.map (MulAut.conj xh).toMonoidHom (R.map mkH) = ⊥ :=
    hFrobQ.trivialIntersection xh hxh_not_R
  -- The image of `N ⊓ R` lands in `R̂ ⊓ R̂^x̂ = ⊥`.
  have hJ_bot : (N ⊓ R).map mkH = ⊥ := by
    rw [eq_bot_iff, ← hTI]
    refine le_inf (Subgroup.map_mono inf_le_right) ?_
    intro yh hyh
    obtain ⟨j, hj, hj_eq⟩ := Subgroup.mem_map.mp hyh
    have hjN : j ∈ N := (Subgroup.mem_inf.mp hj).1
    have hjR : j ∈ R := (Subgroup.mem_inf.mp hj).2
    -- `x j x⁻¹ j⁻¹ ∈ N ⊓ K`, so `x̂` centralizes the image `ŷ = mkH j`.
    have hcomm : (x * j * x⁻¹) * j⁻¹ ∈ N ⊓ K := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact N.mul_mem (hN.conj_mem j hjN x) (N.inv_mem hjN)
      · have hconjK : j * x⁻¹ * j⁻¹ ∈ K :=
          (inferInstance : K.Normal).conj_mem x⁻¹ (K.inv_mem hxK) j
        have hrw : x * j * x⁻¹ * j⁻¹ = x * (j * x⁻¹ * j⁻¹) := by group
        rw [hrw]; exact K.mul_mem hxK hconjK
    have hcent : mkH (x * j * x⁻¹) = mkH j := by
      have h1 : mkH ((x * j * x⁻¹) * j⁻¹) = 1 := by
        rw [hmkH, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hcomm
      rw [map_mul, map_inv] at h1
      exact mul_inv_eq_one.mp h1
    rw [Subgroup.mem_map]
    refine ⟨yh, Subgroup.mem_map.mpr ⟨j, hjR, hj_eq⟩, ?_⟩
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    rw [← hx_eq, ← hj_eq, ← map_inv, ← map_mul, ← map_mul]
    exact hcent
  -- Conclude `N ⊓ R ⊆ N ⊓ K ⊆ K`, hence `N ⊓ R ⊆ K ⊓ R = ⊥`.
  have hNR_le_H : N ⊓ R ≤ N ⊓ K := by
    intro a ha
    have hmk : mkH a = 1 := by
      have hmem : mkH a ∈ (N ⊓ R).map mkH := Subgroup.mem_map_of_mem mkH ha
      rw [hJ_bot, Subgroup.mem_bot] at hmem
      exact hmem
    rwa [hmkH, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmk
  have hNR_le_K : N ⊓ R ≤ K := hNR_le_H.trans inf_le_right
  exact disjoint_self.mp (Disjoint.mono hNR_le_K inf_le_right h.isComplement.disjoint)

/-- **BG Lemma 3.2 (a)** (mmd L820-822, L837-843): in a finite Frobenius group `G = K R` with
solvable kernel `K`, every normal subgroup `N ⊴ G` with `K ⊄ N` is contained in `K`.

*Proof.*  By `inf_complement_eq_bot_of_normal_not_le_kernel`, `N ⊓ R = ⊥`.  By Cor 6.6
(`kernel_eq_notConjugateSet`), `K` is the set of elements not conjugate to any nonidentity
element of `R`.  If some `n ∈ N` were not in `K`, it would be conjugate to a nonidentity
`a ∈ R`; but then `a ∈ N` (normality), so `a ∈ N ⊓ R = ⊥`, a contradiction. -/
theorem normal_le_kernel_of_not_le
    {G : Type*} [Group G] [Finite G] {K R N : Subgroup G} [hN : N.Normal]
    (h : IsFrobeniusGroup G K R) (hKN : ¬ K ≤ N) (hSolvK : IsSolvable ↥K) :
    N ≤ K := by
  have hNR : N ⊓ R = ⊥ := inf_complement_eq_bot_of_normal_not_le_kernel h hKN hSolvK
  intro n hn
  by_contra hnK
  have hn_notin : (n : G) ∉ notConjugateSet R := by
    rw [← h.kernel_eq_notConjugateSet]
    exact fun hc => hnK hc
  simp only [notConjugateSet, Set.mem_setOf_eq, not_forall, not_not] at hn_notin
  obtain ⟨a, haR, ha_ne, hconj⟩ := hn_notin
  rw [isConj_iff] at hconj
  obtain ⟨g, hg⟩ := hconj
  have hag : a = g⁻¹ * n * g := by rw [← hg]; group
  have ha_in_N : a ∈ N := by
    rw [hag]
    have := hN.conj_mem n hn g⁻¹
    simpa using this
  have hmem : a ∈ N ⊓ R := Subgroup.mem_inf.mpr ⟨ha_in_N, haR⟩
  rw [hNR, Subgroup.mem_bot] at hmem
  exact ha_ne hmem

/-- **BG Lemma 3.2** (mmd L820-843): in a finite Frobenius group `G = K R` with solvable kernel
`K`, every normal subgroup `N ⊴ G` with `K ⊄ N` satisfies `N < K`, and the quotient
`Ḡ = G / N` is a Frobenius group with kernel `K̄ = K N / N` and complement `R̄ = R N / N`.

This combines part (a) (`normal_le_kernel_of_not_le`) with the `N ≤ K` branch
(`quotient_isFrobeniusGroup_of_le_kernel_of_coprime_zpowers`). -/
theorem isFrobeniusGroup_quotient_of_normal_not_le_kernel
    {G : Type*} [Group G] [Finite G] {K R N : Subgroup G} [N.Normal]
    (h : IsFrobeniusGroup G K R) (hKN : ¬ K ≤ N) (hSolvK : IsSolvable ↥K) :
    N < K ∧
      IsFrobeniusGroup (G ⧸ N) (K.map (QuotientGroup.mk' N)) (R.map (QuotientGroup.mk' N)) := by
  letI : K.Normal := h.isNormal
  have hNK : N ≤ K := normal_le_kernel_of_not_le h hKN hSolvK
  have hne : N ≠ K := by rintro rfl; exact hKN le_rfl
  refine ⟨hNK.lt_of_ne hne, ?_⟩
  have hCop : ∀ x, x ∈ R → x ≠ 1 →
      Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥K) := by
    intro x hxR _
    have hdvd : Nat.card ↥(Subgroup.zpowers x) ∣ Nat.card ↥R :=
      Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxR)
    exact Nat.Coprime.coprime_dvd_left hdvd (h.coprime_card_kernel_complement).symm
  exact quotient_isFrobeniusGroup_of_le_kernel_of_coprime_zpowers h hNK hKN hCop hSolvK

end OddOrder.BG.Ch1.S03
