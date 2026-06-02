/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
import OddOrder.BG.Ch1_Preliminary.S04_PGroupsSmallRank
import OddOrder.BG.Ch1_Preliminary.S04d_GorThm415
import OddOrder.BG.Ch1_Preliminary.S04f_Blackburn
import OddOrder.BG.Ch1_Preliminary.S04g_Thm418
import OddOrder.BG.Ch1_Preliminary.PLength
import OddOrder.GroupTheory.NarrowPGroup
import OddOrder.GroupTheory.SCN
import OddOrder.GroupTheory.OmegaSubgroup
import OddOrder.GroupTheory.OpResidual
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.Isaacs.Ch05_Transfer.Main

/-!
# BG §5: Narrow `p`-Groups

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §5 (pp. 44-49), mmd `references/bg/local-analysis.mmd`
L1789-1968, **7 結果** (Lem 5.1, 5.2 + Thm 5.3, 5.5, 5.6, 5.7 + Cor 5.4).

§5 は rank `≥ 3` の **narrow `p`-群** ("ほぼ rank `≤ 2` 並みに行儀がよい" 群) を扱う。
中核は **Thm 5.3** (`r(R)≥3` で `narrow ↔ ℰ²(R)∩ℰ*(R)≠∅`) と **Thm 5.5** (narrow `R` の
solvable odd 自己同型群 `A` の構造)。下流 §6/§10/§16 + Peterfalvi §9 で narrow Sylow が多用される。

## 記法 (BG → repo)

- `r(R)` (p-群 `R` の rank) = `pRank R p` (`GroupTheory.PRank`)。`m(U)` = `pRank ↥U p`。
- narrow = `OddOrder.GroupTheory.IsNarrow p R`。
- `ℰ²(R)∩ℰ*(R)` (位数 `p²` の maximal elem-ab) =
  `Nat.card ↥E = p^2 ∧ IsMaximalElementaryAbelian p E`。
- `W = Ω₁(Z₂(R))` = `omega1UpperCentralTwo R p`; `T = C_R(W)` =
  `Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)`; `Ω₁(Z(R))` =
  `omega1OfAbelian R (Subgroup.center R) p`。
- 自己同型作用 `A ≤ Aut R` = `φ : A →* MulAut R` (faithful: `Function.Injective φ`),
  `R=[R,A]` = `actionCommutator φ = ⊤`, `O_p(A)` = `Ch01.opCore p A` (§4 流儀 S04b に合わせる)。
- `F(G)` = `Ch01.fitting G`。

## 定義インフラの所在

§5 の述語層 (`IsNarrow`, `IsMaximalElementaryAbelian` = `E*(R)`, `omega1UpperCentralTwo` = `W`,
`T = C_R(W)` の characteristic 性) は **共有モジュール `OddOrder/GroupTheory/NarrowPGroup.lean`
に実装済 (sorry-free)**。本ファイルは §5 の 7 numbered result を faithful に述べる section file。

## 証明の前提

§5 の hard 結果は **§4 capstone** に依存する: Lem 5.1(a)=Lem 4.7 hard dir (✅ `pRank_le_two_of_scn3_empty`),
Lem 4.5(c) noncyclic 半 (TODO), Lem 4.14 ✅, Thm 4.16 (Blackburn) ✅, Lem 4.17 ✅,
Thm 4.18 ✅ (`S04.solvable_structure_of_pRank_le_two`, S04g)。

**現況**: Lem 5.1/5.2, Thm 5.3/5.3(d), Cor 5.4, Thm 5.5, Thm 5.6 は **証明済 (sorry-free)**。
残 sorry = **Thm 5.7** (`derived_le_fitting_of_centralizer_pRank_le_two`) のみ。
-/

namespace OddOrder.BG.Ch1.S05

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped IsMulCommutative commutatorElement

variable {R : Type*} [Group R]

/-- `Ω₁(Z(R))`: 中心 `Z(R)` の位数 `p` 元が生成する部分群。中心は可換なので
`omega1OfAbelian` で `Subgroup R` として実現できる (BG §5 で `|Ω₁(Z(R))| = p` を述べるため)。 -/
private def omega1Center (R : Type*) [Group R] (p : ℕ) : Subgroup R :=
  omega1OfAbelian R (Subgroup.center R) p
    (fun _ hx _ _ => (Subgroup.mem_center_iff.mp hx _).symm)

private theorem omega1Center_le_center {p : ℕ} : omega1Center R p ≤ Subgroup.center R :=
  fun _ hg => hg.1

private theorem mem_omega1Center {p : ℕ} {g : R} :
    g ∈ omega1Center R p ↔ g ∈ Subgroup.center R ∧ g ^ p = 1 := Iff.rfl

/-- `Ω₁(Z(R))` is elementary abelian: it is central and every element has
`p`-th power `1` by definition. -/
private theorem omega1Center_isElementaryAbelian {p : ℕ} :
    (omega1Center R p).IsElementaryAbelian p := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (omega1Center_le_center x.2) (y : R)).symm
  · apply Subtype.ext
    have : (x : R) ^ p = 1 := (mem_omega1Center.mp x.2).2
    simpa using this

/-- **BG Lemma 5.2 support**: the central subgroup `Ω₁(Z(R))` is contained in any
maximal elementary abelian subgroup `E`. This packages the textbook step `EZ = E`
from `E ∈ E*(R)`. -/
theorem omega1Center_le_of_maximalElementaryAbelian {p : ℕ} {E : Subgroup R}
    (hEstar : IsMaximalElementaryAbelian p E) :
    omega1Center R p ≤ E := by
  have hE_le_cent : E ≤ Subgroup.centralizer (omega1Center R p : Set R) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_center_iff.mp (omega1Center_le_center hz) x).symm
  exact hEstar.le_of_le_centralizer omega1Center_isElementaryAbelian hE_le_cent

/-- **BG Lemma 5.2 support**: `Ω₁(Z(R)) ≤ Ω₁(Z₂(R))`. -/
theorem omega1Center_le_omega1UpperCentralTwo {p : ℕ} :
    omega1Center R p ≤ omega1UpperCentralTwo R p := by
  intro z hz
  rw [omega1UpperCentralTwo, Subgroup.mem_map]
  have hz_pow : z ^ p = 1 := (mem_omega1Center.mp hz).2
  have hzZ2 : z ∈ upperCentralSeries R 2 := by
    exact (upperCentralSeries_mono R (by norm_num : (1 : ℕ) ≤ 2))
      (by
        rw [upperCentralSeries_one]
        exact (mem_omega1Center.mp hz).1)
  refine ⟨⟨z, hzZ2⟩, ?_, rfl⟩
  refine Omega.mem_of_pow_eq_one ?_
  rw [pow_one]
  exact Subtype.ext (by simpa using hz_pow)

/-- **BG Lemma 5.2 support**: once Lemma 4.5(c) supplies noncyclicity of
`Ω₁(Z₂(R))`, the inclusion `Ω₁(Z(R)) ≤ Ω₁(Z₂(R))` is strict whenever
`|Ω₁(Z(R))| = p`. -/
theorem omega1Center_lt_omega1UpperCentralTwo_of_not_isCyclic
    [Finite R] {p : ℕ} [Fact p.Prime]
    (hZcard : Nat.card ↥(omega1Center R p) = p)
    (hWnc : ¬ IsCyclic ↥(omega1UpperCentralTwo R p)) :
    omega1Center R p < omega1UpperCentralTwo R p := by
  refine lt_of_le_of_ne omega1Center_le_omega1UpperCentralTwo ?_
  intro hZW
  have hZcyc : IsCyclic ↥(omega1Center R p) := isCyclic_of_prime_card hZcard
  have hWcyc : IsCyclic ↥(omega1UpperCentralTwo R p) := by
    haveI : IsCyclic ↥(omega1Center R p) := hZcyc
    exact isCyclic_of_surjective (MulEquiv.subgroupCongr hZW).toMonoidHom
      (MulEquiv.subgroupCongr hZW).surjective
  exact hWnc hWcyc

/-- **BG Lemma 5.2 support**: `[Ω₁(Z₂(R)), R] ≤ Ω₁(Z(R))`.
For `w ∈ Ω₁(Z₂(R))`, the inclusion `w ∈ Z₂(R)` puts `⁅w, r⁆` in the centre.
The odd-prime exponent statement for `Ω₁(Z₂(R))`, together with the central
commutator power identity, gives `(⁅w, r⁆)^p = 1`. -/
theorem commutator_omega1UpperCentralTwo_le_omega1Center {p : ℕ} (hp : Odd p) :
    ⁅omega1UpperCentralTwo R p, (⊤ : Subgroup R)⁆ ≤ omega1Center R p := by
  rw [Subgroup.commutator_le]
  intro w hw r _
  have hwZ2 : w ∈ upperCentralSeries R 2 := omega1UpperCentralTwo_le R p hw
  have hcomm_center : ⁅w, r⁆ ∈ Subgroup.center R := by
    have hmem : w * r * w⁻¹ * r⁻¹ ∈ upperCentralSeries R 1 :=
      mem_upperCentralSeries_succ_iff.mp hwZ2 r
    rwa [upperCentralSeries_one, ← commutatorElement_def] at hmem
  refine (mem_omega1Center).mpr ⟨hcomm_center, ?_⟩
  have hwpow : w ^ p = 1 := pow_eq_one_of_mem_omega1UpperCentralTwo hp hw
  have hpow := S04.commutatorElement_pow_left_of_central hcomm_center p
  rw [← hpow, hwpow, commutatorElement_one_left]

/-! ## Lemma 5.1 — SCN₃ の非空性と normal `ℰ²` の埋め込み (mmd L1795-1806) -/

/-- **BG Lemma 5.1(a)**: 奇素数 `p`, 有限 `p`-群 `R`, `r(R) ≥ 3` ⇒ `SCN₃(R) ≠ ∅`。

`SCN₃(R) = ∅ ⇒ r(R) ≤ 2` (= Lem 4.7 hard dir, `pRank_le_two_of_scn3_empty`) の対偶。
本リポでは §4d に hard dir が在るので、本補題は純論理で **証明済 (sorry なし)**。 -/
theorem scn3_nonempty_of_three_le_pRank [Finite R] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hpg : IsPGroup p R) (h3 : 3 ≤ pRank R p) :
    ∃ A : Subgroup R, IsSCN₃ p A := by
  by_contra hcon
  rw [not_exists] at hcon
  exact absurd (S04.pRank_le_two_of_scn3_empty hp hpg hcon) (by omega)

/-- **BG Lemma 5.1(b), first construction step**: from an `SCN₃` subgroup `A`,
BG Lemma 1.22 produces a normal elementary abelian subgroup of order `p³`.

This packages the textbook line “by (a) and Lemma 1.22, there exists a normal elementary
abelian subgroup `B` of order `p³` in `R`”: use `3 ≤ pRank A p` to see that `p³` divides
`|Ω₁(A)|`, then apply Lemma 1.22 inside the normal subgroup `Ω₁(A)`. -/
theorem exists_normal_isElementaryAbelian_card_prime_cube_of_scn3
    [Finite R] {p : ℕ} [Fact p.Prime] (hpg : IsPGroup p R)
    {A : Subgroup R} (hA : IsSCN₃ p A) :
    ∃ B : Subgroup R, B.Normal ∧ B.IsElementaryAbelian p ∧ Nat.card B = p ^ 3 := by
  have hA_scn : IsSCN A := hA.isSCN
  have hA_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    letI : IsMulCommutative A := hA_scn.isMulCommutative
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  set H : Subgroup R := omega1OfAbelian R A p hA_comm with hHdef
  have hH_le_A : H ≤ A := by
    simpa [hHdef] using
      (omega1OfAbelian_le (G := R) (H := A) (p := p) (hH := hA_comm))
  have hH_normal : H.Normal := by
    refine { conj_mem := fun h hh g => ?_ }
    have hh' : h ∈ A ∧ h ^ p = 1 := by simpa [hHdef] using hh
    rw [hHdef]
    refine (mem_omega1OfAbelian).mpr ⟨hA_scn.isNormal.conj_mem h hh'.1 g, ?_⟩
    calc (g * h * g⁻¹) ^ p = g * h ^ p * g⁻¹ := conj_pow
      _ = 1 := by rw [hh'.2, mul_one, mul_inv_cancel]
  have hH_elem : H.IsElementaryAbelian p := by
    rw [hHdef]
    exact
      ⟨fun x y => Subtype.ext (hA_comm x.val x.2.1 y.val y.2.1),
       fun x => Subtype.ext (by simpa using pow_eq_one_of_mem_omega1OfAbelian x.2)⟩
  have hH_dvd : p ^ 3 ∣ Nat.card H := by
    simpa [hHdef] using
      (pow_dvd_card_omega1OfAbelian_of_pos_le_pRank (G := R) (H := A)
        (p := p) (hH := hA_comm) (n := 3) (by norm_num) hA.le_pRank)
  haveI : H.Normal := hH_normal
  obtain ⟨B, hB_normal, hB_le_H, hB_card⟩ :=
    OddOrder.BG.Ch1.S01.normal_subgroup_card_pow_le_of_pGroup
      (G := R) (p := p) hpg (N := H) (r := 3) hH_dvd
  have hB_elem : B.IsElementaryAbelian p := by
    have hB_sub_elem : (B.subgroupOf H).IsElementaryAbelian p :=
      hH_elem.to_subgroup (B.subgroupOf H)
    exact IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hB_le_H) hB_sub_elem
  exact ⟨B, hB_normal, hB_elem, hB_card⟩

/-- **BG Lemma 5.1(b), `B* = E C_B(E)` support**: if `E` and `B` are normal
elementary abelian `p`-subgroups, then the Lean encoding
`E ⊔ (B ⊓ C_R(E))` of the textbook product `E C_B(E)` is again normal and elementary
abelian. -/
theorem bStar_normal_isElementaryAbelian_of_normal_isElementaryAbelian
    {p : ℕ} {E B : Subgroup R} [E.Normal] [B.Normal]
    (hE : E.IsElementaryAbelian p) (hB : B.IsElementaryAbelian p) :
    (E ⊔ (B ⊓ Subgroup.centralizer (E : Set R))).Normal ∧
      (E ⊔ (B ⊓ Subgroup.centralizer (E : Set R))).IsElementaryAbelian p := by
  constructor
  · haveI : (Subgroup.centralizer (E : Set R)).Normal := Subgroup.normal_centralizer
    infer_instance
  · let K : Subgroup R := B ⊓ Subgroup.centralizer (E : Set R)
    have hK_le_B : K ≤ B := by
      dsimp [K]
      exact inf_le_left
    have hK_elem : K.IsElementaryAbelian p := by
      have hK_sub_elem : (K.subgroupOf B).IsElementaryAbelian p :=
        hB.to_subgroup (K.subgroupOf B)
      exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hK_le_B) hK_sub_elem
    have hE_le_cent_K : E ≤ Subgroup.centralizer (K : Set R) := by
      dsimp [K]
      exact Subgroup.le_centralizer_iff.mpr inf_le_right
    exact Subgroup.IsElementaryAbelian.sup_of_le_centralizer hE hK_elem hE_le_cent_K

/-- **BG Lemma 5.1(b), large `B*` branch**: if the subgroup
`B* = E ⊔ (B ⊓ C_R(E))` constructed from normal elementary abelian `E` and `B` has
cardinality at least `p^3`, then `E` is contained in some `SCN₃` subgroup. -/
theorem exists_scn3_ge_of_bStar_card_ge_prime_cube
    [Finite R] {p : ℕ} [Fact p.Prime] (hpg : IsPGroup p R)
    {E B : Subgroup R} [E.Normal] [B.Normal]
    (hE : E.IsElementaryAbelian p) (hB : B.IsElementaryAbelian p)
    (hcard : p ^ 3 ≤ Nat.card ↥(E ⊔ (B ⊓ Subgroup.centralizer (E : Set R)))) :
    ∃ A : Subgroup R, IsSCN₃ p A ∧ E ≤ A := by
  let Bstar : Subgroup R := E ⊔ (B ⊓ Subgroup.centralizer (E : Set R))
  have hBstar := bStar_normal_isElementaryAbelian_of_normal_isElementaryAbelian
    (E := E) (B := B) hE hB
  have hBstar_norm : Bstar.Normal := by
    simpa [Bstar] using hBstar.1
  have hBstar_elem : Bstar.IsElementaryAbelian p := by
    simpa [Bstar] using hBstar.2
  have hBstar_comm : IsMulCommutative Bstar :=
    IsMulCommutative.of_comm hBstar_elem.comm
  have hcard' : p ^ 3 ≤ Nat.card Bstar := by
    simpa [Bstar] using hcard
  have hlog : 3 ≤ Nat.log p (Nat.card Bstar) :=
    Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt hcard'
  have hBrank : 3 ≤ pRank Bstar p :=
    hlog.trans hBstar_elem.log_card_le_pRank
  obtain ⟨A, hA, hBstar_le_A⟩ :=
    exists_scn3_ge_of_normal_abelian_pRank_ge_three hpg hBstar_norm hBstar_comm hBrank
  refine ⟨A, hA, ?_⟩
  have hE_le_Bstar : E ≤ Bstar := by
    dsimp [Bstar]
    exact le_sup_left
  exact hE_le_Bstar.trans hBstar_le_A

/-- **BG Lemma 5.1(b), centralizer-count support**: if `E` has order `p^2` and
`B` has order `p^3`, both elementary abelian, then the centralizer of `E` inside `B`
has order at least `p^2`. This is the Lean form of the textbook estimate
`|B / C_B(E)| ≤ p`, obtained from the conjugation action of `B` on `E`. -/
theorem card_inf_centralizer_ge_prime_sq_of_card_prime_cube
    [Finite R] {p : ℕ} [Fact p.Prime]
    {E B : Subgroup R} [E.Normal]
    (hE : E.IsElementaryAbelian p) (hEcard : Nat.card E = p ^ 2)
    (hB : B.IsElementaryAbelian p) (hBcard : Nat.card B = p ^ 3) :
    p ^ 2 ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (E : Set R)) := by
  let φ : B →* MulAut E := (MulAut.conjNormal (H := E)).comp B.subtype
  have hrange_pg : IsPGroup p φ.range :=
    hB.isPGroup.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hEcard_le : Nat.card E ≤ p ^ 2 := by
    rw [hEcard]
  have hrange_le : Nat.card φ.range ≤ p :=
    card_pSubgroup_mulAut_le_prime_of_card_le_prime_sq hE hEcard_le hrange_pg
  have hLagrange : Nat.card B = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hker_map_eq : φ.ker.map B.subtype = B ⊓ Subgroup.centralizer (E : Set R) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨b, hbker, rfl⟩ := hx
      refine ⟨b.2, ?_⟩
      change B.subtype b ∈ Subgroup.centralizer (E : Set R)
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hfix : (MulAut.conjNormal (H := E) (B.subtype b)) ⟨e, he⟩ = ⟨e, he⟩ := by
        have hφb : φ b = 1 := MonoidHom.mem_ker.mp hbker
        simpa [φ] using congrArg (fun σ : MulAut E => σ ⟨e, he⟩) hφb
      have hfix_val := congrArg Subtype.val hfix
      rw [MulAut.conjNormal_apply] at hfix_val
      exact (mul_inv_eq_iff_eq_mul.mp hfix_val).symm
    · intro hx
      obtain ⟨hxB, hxC⟩ := hx
      rw [Subgroup.mem_map]
      refine ⟨⟨x, hxB⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      ext e
      change x * (e : R) * x⁻¹ = (e : R)
      have hcomm : (e : R) * x = x * (e : R) :=
        Subgroup.mem_centralizer_iff.mp hxC (e : R) e.2
      rw [← hcomm]
      group
  have hker_card : Nat.card ↥(B ⊓ Subgroup.centralizer (E : Set R)) = Nat.card φ.ker := by
    rw [← hker_map_eq, Subgroup.card_map_of_injective B.subtype_injective]
  have hB_le : Nat.card B ≤ p * Nat.card φ.ker := by
    rw [hLagrange]
    exact Nat.mul_le_mul_right _ hrange_le
  have hp3_le : p ^ 3 ≤ p * Nat.card φ.ker := by
    rw [← hBcard]
    exact hB_le
  have hp3_eq : p ^ 3 = p * p ^ 2 := by ring
  have hp2_le_ker : p ^ 2 ≤ Nat.card φ.ker := by
    have hmul : p * p ^ 2 ≤ p * Nat.card φ.ker := by
      rwa [← hp3_eq]
    exact Nat.le_of_mul_le_mul_left hmul (Fact.out : p.Prime).pos
  rwa [hker_card]

/-- **BG Lemma 5.1(b), small-branch contradiction packaged as a lower bound**:
if `E` has order `p^2` and `B` has order `p^3`, both elementary abelian, then
the Lean encoding `E ⊔ (B ⊓ C_R(E))` of `E C_B(E)` has order at least `p^3`.
This is the formal version of BG's argument that the alternative `|E C_B(E)| < p^3`
would force `C_B(E)=E` and then, since `B` is abelian, `B=C_B(E)`, contradicting
`|B|=p^3` and `|E|=p^2`. -/
theorem bStar_card_ge_prime_cube_of_card_prime_cube
    [Finite R] {p : ℕ} [Fact p.Prime]
    {E B : Subgroup R} [E.Normal]
    (hE : E.IsElementaryAbelian p) (hEcard : Nat.card E = p ^ 2)
    (hB : B.IsElementaryAbelian p) (hBcard : Nat.card B = p ^ 3) :
    p ^ 3 ≤ Nat.card ↥(E ⊔ (B ⊓ Subgroup.centralizer (E : Set R))) := by
  let K : Subgroup R := B ⊓ Subgroup.centralizer (E : Set R)
  let Bstar : Subgroup R := E ⊔ K
  by_contra hnot
  have hsmall : Nat.card Bstar < p ^ 3 := Nat.lt_of_not_ge hnot
  have hK_le_B : K ≤ B := by
    intro x hx
    dsimp [K] at hx
    exact hx.1
  have hK_elem : K.IsElementaryAbelian p := by
    have hK_sub_elem : (K.subgroupOf B).IsElementaryAbelian p :=
      hB.to_subgroup (K.subgroupOf B)
    exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hK_le_B) hK_sub_elem
  have hE_le_cent_K : E ≤ Subgroup.centralizer (K : Set R) := by
    dsimp [K]
    exact Subgroup.le_centralizer_iff.mpr inf_le_right
  have hBstar_elem : Bstar.IsElementaryAbelian p := by
    simpa [Bstar] using
      Subgroup.IsElementaryAbelian.sup_of_le_centralizer hE hK_elem hE_le_cent_K
  letI : IsMulCommutative Bstar := IsMulCommutative.of_comm hBstar_elem.comm
  letI := hBstar_elem.zmodModule
  let m : ℕ := Module.finrank (ZMod p) (Additive Bstar)
  have hBstar_card_pow : Nat.card Bstar = p ^ m := by
    dsimp [m]
    simpa using hBstar_elem.card_eq_pow_finrank
  have hE_le_Bstar : E ≤ Bstar := by
    dsimp [Bstar]
    exact le_sup_left
  have hK_le_Bstar : K ≤ Bstar := by
    dsimp [Bstar]
    exact le_sup_right
  have hE_card_le_Bstar : Nat.card E ≤ Nat.card Bstar :=
    Nat.card_le_card_of_injective
      (fun x : E => (⟨x.1, hE_le_Bstar x.2⟩ : Bstar))
      (fun x y hxy => Subtype.ext (congrArg (fun z : Bstar => (z : R)) hxy))
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hm_lt : m < 3 := by
    have hp_lt : p ^ m < p ^ 3 := by
      simpa [hBstar_card_pow] using hsmall
    exact (Nat.pow_lt_pow_iff_right hp1).mp hp_lt
  have hm_ge : 2 ≤ m := by
    have hp_le : p ^ 2 ≤ p ^ m := by
      simpa [hEcard, hBstar_card_pow] using hE_card_le_Bstar
    exact (Nat.pow_le_pow_iff_right hp1).mp hp_le
  have hm_eq : m = 2 := by omega
  have hBstar_card_eq : Nat.card Bstar = p ^ 2 := by
    rw [hBstar_card_pow, hm_eq]
  have hBstar_card_le_E : Nat.card Bstar ≤ Nat.card E := by
    simp [hBstar_card_eq, hEcard]
  have hE_eq_Bstar : E = Bstar :=
    Subgroup.eq_of_le_of_card_ge hE_le_Bstar hBstar_card_le_E
  have hK_card : p ^ 2 ≤ Nat.card K := by
    simpa [K] using
      card_inf_centralizer_ge_prime_sq_of_card_prime_cube
        (E := E) (B := B) hE hEcard hB hBcard
  have hBstar_card_le_K : Nat.card Bstar ≤ Nat.card K :=
    hBstar_card_eq.le.trans hK_card
  have hK_eq_Bstar : K = Bstar :=
    Subgroup.eq_of_le_of_card_ge hK_le_Bstar hBstar_card_le_K
  have hE_eq_K : E = K := hE_eq_Bstar.trans hK_eq_Bstar.symm
  have hE_le_B : E ≤ B := by
    intro x hx
    have hxK : x ∈ K := by
      simpa [hE_eq_K] using hx
    dsimp [K] at hxK
    exact hxK.1
  have hB_le_cent : B ≤ Subgroup.centralizer (E : Set R) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have heB : e ∈ B := hE_le_B he
    have hcomm : x * e = e * x :=
      congrArg (fun z : B => (z : R)) (hB.comm ⟨x, hx⟩ ⟨e, heB⟩)
    exact hcomm.symm
  have hB_le_K : B ≤ K := by
    intro x hx
    dsimp [K]
    exact ⟨hx, hB_le_cent hx⟩
  have hB_eq_K : B = K := le_antisymm hB_le_K hK_le_B
  have hB_eq_E : B = E := hB_eq_K.trans hE_eq_K.symm
  have hp32_ne : p ^ 3 ≠ p ^ 2 := by
    exact ne_of_gt ((Nat.pow_lt_pow_iff_right hp1).mpr (by norm_num : (2 : ℕ) < 3))
  have hp32_eq : p ^ 3 = p ^ 2 := by
    rw [← hBcard, hB_eq_E, hEcard]
  exact hp32_ne hp32_eq

/-- **BG Lemma 5.1(b)**: 奇素数 `p`, 有限 `p`-群 `R`, `r(R) ≥ 3`。`E ∈ ℰ²(R)` (elem-ab,
位数 `p²`) かつ `E ⊴ R` ⇒ `E` は `SCN₃(R)` のある元に含まれる。

mmd L1800-1806: (a) + Lem 1.22 で normal elem-ab `B` (位数 `p³`) を取り、`B* = E·C_B(E)` の
位数で場合分け (`≥ p³` なら Prop 4.4、`< p³` は `B` abelian で矛盾)。 -/
theorem mem_scn3_of_normal_isElementaryAbelian_card_prime_sq [Finite R] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hpg : IsPGroup p R) (h3 : 3 ≤ pRank R p)
    (E : Subgroup R) (hE : E.IsElementaryAbelian p) (hEcard : Nat.card ↥E = p ^ 2)
    [E.Normal] :
    ∃ A : Subgroup R, IsSCN₃ p A ∧ E ≤ A := by
  obtain ⟨A, hA⟩ := scn3_nonempty_of_three_le_pRank hp hpg h3
  obtain ⟨B, hB_normal, hB, hBcard⟩ :=
    exists_normal_isElementaryAbelian_card_prime_cube_of_scn3 hpg hA
  haveI : B.Normal := hB_normal
  have hBstar_card : p ^ 3 ≤ Nat.card ↥(E ⊔ (B ⊓ Subgroup.centralizer (E : Set R))) :=
    bStar_card_ge_prime_cube_of_card_prime_cube hE hEcard hB hBcard
  exact exists_scn3_ge_of_bStar_card_ge_prime_cube hpg hE hB hBstar_card

/-! ## Lemma 5.2 — `T = C_R(W)` の中心構造 (mmd L1808-1836) -/

/-- **BG Lemma 5.2 support / Lemma 4.5(c) in the `r(R) ≥ 3` context**:
`W = Ω₁(Z₂(R))` is noncyclic.

We avoid the still-deferred general Lemma 4.5(a) by using the stronger local hypothesis
`r(R) ≥ 3`: Lemma 5.1's SCN₃ construction gives a normal elementary abelian subgroup
of order `p³`; BG Lemma 1.22 extracts a normal elementary abelian subgroup `S` of
order `p²`. Since `R` is nilpotent, `[S,R]` is a proper subgroup of `S`; hence it has
order `1` or `p`, and in the latter case it is central. Thus `S ≤ Z₂(R)`, and since
`S` has exponent `p`, `S ≤ W`. A cyclic `W` would make its subgroup `S` cyclic,
contradicting `|S| = p²` and elementary abelianness. -/
theorem omega1UpperCentralTwo_not_isCyclic_of_three_le_pRank
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) :
    ¬ IsCyclic ↥(omega1UpperCentralTwo R p) := by
  obtain ⟨A, hA⟩ := scn3_nonempty_of_three_le_pRank hp hpg h3
  obtain ⟨B, hB_normal, hB_elem, hBcard⟩ :=
    exists_normal_isElementaryAbelian_card_prime_cube_of_scn3 hpg hA
  haveI : B.Normal := hB_normal
  have hB_dvd : p ^ 2 ∣ Nat.card B := by
    rw [hBcard]
    exact pow_dvd_pow p (by norm_num : 2 ≤ 3)
  obtain ⟨S, hS_normal, hS_le_B, hScard⟩ :=
    OddOrder.BG.Ch1.S01.normal_subgroup_card_pow_le_of_pGroup
      (G := R) (p := p) hpg (N := B) (r := 2) hB_dvd
  haveI : S.Normal := hS_normal
  have hS_elem : S.IsElementaryAbelian p := by
    have hS_sub_elem : (S.subgroupOf B).IsElementaryAbelian p :=
      hB_elem.to_subgroup (S.subgroupOf B)
    exact IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hS_le_B) hS_sub_elem
  have hS_ne_bot : S ≠ ⊥ := by
    intro hSbot
    have hcard_one : Nat.card S = 1 := by rw [hSbot, Subgroup.card_bot]
    have hp_sq_gt_one : 1 < p ^ 2 :=
      one_lt_pow₀ (Fact.out : p.Prime).one_lt two_ne_zero
    exact (ne_of_gt hp_sq_gt_one) (by rw [← hScard, hcard_one])
  haveI : Group.IsNilpotent R := IsPGroup.isNilpotent hpg
  let H : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  have hHlt : H < S := by
    dsimp [H]
    exact OddOrder.Isaacs.Ch04.commutator_lt_self_of_isNilpotent_ambient
      (E := S) (F := (⊤ : Subgroup R)) hS_ne_bot
  have hH_le_S : H ≤ S := hHlt.le
  haveI hH_normal : H.Normal := by
    dsimp [H]
    infer_instance
  have hH_le_center : H ≤ Subgroup.center R := by
    by_cases hHbot : H = ⊥
    · rw [hHbot]
      exact bot_le
    · have hH_dvd : Nat.card H ∣ p ^ 2 := by
        rw [← hScard]
        exact Subgroup.card_dvd_of_le hH_le_S
      obtain ⟨j, hj_le, hj_eq⟩ :=
        (Nat.dvd_prime_pow (p := p) (Fact.out (p := p.Prime))).mp hH_dvd
      have hj_ne_zero : j ≠ 0 := by
        intro hj0
        have hHcard_one : Nat.card H = 1 := by simpa [hj0] using hj_eq
        exact hHbot ((Subgroup.card_eq_one (H := H)).mp hHcard_one)
      have hj_ne_two : j ≠ 2 := by
        intro hj2
        have hHcard_eq_S : Nat.card H = Nat.card S := by
          rw [hj_eq, hj2, hScard]
        have hHS : H = S :=
          Subgroup.eq_of_le_of_card_ge hH_le_S (le_of_eq hHcard_eq_S.symm)
        exact hHlt.ne hHS
      have hj_eq_one : j = 1 := by omega
      have hHcard : Nat.card H = p := by simpa [hj_eq_one] using hj_eq
      exact S04.le_center_of_card_eq_prime_of_normal hpg hHcard
  have hS_le_Z2 : S ≤ upperCentralSeries R 2 := by
    intro s hs
    rw [mem_upperCentralSeries_succ_iff]
    intro r
    have hcomm_center : ⁅s, r⁆ ∈ Subgroup.center R := by
      exact hH_le_center (by
        dsimp [H]
        exact Subgroup.commutator_mem_commutator hs trivial)
    simpa [upperCentralSeries_one, commutatorElement_def] using hcomm_center
  let W : Subgroup R := omega1UpperCentralTwo R p
  have hS_le_W : S ≤ W := by
    intro s hs
    dsimp [W]
    rw [omega1UpperCentralTwo, Subgroup.mem_map]
    have hs_pow_sub := hS_elem.pow_eq_one (⟨s, hs⟩ : S)
    have hs_pow : s ^ p = 1 := by
      simpa using congrArg Subtype.val hs_pow_sub
    refine ⟨⟨s, hS_le_Z2 hs⟩, ?_, rfl⟩
    refine Omega.mem_of_pow_eq_one ?_
    rw [pow_one]
    exact Subtype.ext (by simpa using hs_pow)
  have hS_not_cyclic : ¬ IsCyclic ↥S :=
    hS_elem.not_isCyclic_of_card_prime_sq (Fact.out : p.Prime) hScard
  intro hWcyc
  have hSsub_cyc : IsCyclic ↥(S.subgroupOf W) := by
    haveI : IsCyclic ↥W := by simpa [W] using hWcyc
    exact Subgroup.isCyclic _
  have hS_cyc : IsCyclic ↥S := by
    haveI : IsCyclic ↥(S.subgroupOf W) := hSsub_cyc
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS_le_W).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hS_le_W).surjective
  exact hS_not_cyclic hS_cyc

/-- **BG Lemma 5.2 support**: if `E ∈ E*(R)` has order `p²`, then
`C_R(E)` has `p`-rank at most `2`.

Indeed, any elementary abelian `p`-subgroup of `C_R(E)` centralizes `E`; adjoining it
to `E` is still elementary abelian, so maximality of `E` forces the subgroup back
inside `E`. -/
theorem pRank_centralizer_le_two_of_maximalElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] {E : Subgroup R}
    (hEcard : Nat.card ↥E = p ^ 2) (hEstar : IsMaximalElementaryAbelian p E) :
    pRank ↥(Subgroup.centralizer (E : Set R)) p ≤ 2 := by
  rw [pRank_le_iff]
  intro A hA
  let C : Subgroup R := Subgroup.centralizer (E : Set R)
  let F : Subgroup R := A.map C.subtype
  have hF : F.IsElementaryAbelian p := by
    dsimp [F, C]
    exact Subgroup.IsElementaryAbelian.map C.subtype_injective hA
  have hE_le_cent_F : E ≤ Subgroup.centralizer (F : Set R) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro x hxF
    change x ∈ A.map C.subtype at hxF
    rw [Subgroup.mem_map] at hxF
    obtain ⟨a, _, rfl⟩ := hxF
    exact (Subgroup.mem_centralizer_iff.mp a.2 e he).symm
  have hF_le_E : F ≤ E :=
    hEstar.le_of_le_centralizer (F := F) hF hE_le_cent_F
  calc
    Nat.log p (Nat.card A) = Nat.log p (Nat.card F) := by
      dsimp [F, C]
      rw [Subgroup.card_map_of_injective C.subtype_injective]
    _ ≤ Nat.log p (Nat.card E) :=
      Nat.log_mono_right (Subgroup.card_le_of_le hF_le_E)
    _ = 2 := by
      rw [hEcard, Nat.log_pow (Fact.out : p.Prime).one_lt]

/-- **BG Lemma 5.2 support**: in the same situation, `Ω₁(Z(R))` is a proper
subgroup of `E`, and hence has order `p`.

This is the textbook step after `Z ≤ E`: if `Z = E`, then `E` is central, so
`C_R(E) = R`, contradicting `r(R) ≥ 3` and the rank bound for `C_R(E)`. The
order calculation uses the central subgroup of order `p` in a nontrivial finite
`p`-group and the divisibility `|Z| ∣ |E| = p²`. -/
theorem omega1Center_lt_and_card_eq_prime_of_maximalElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) {E : Subgroup R} (hEcard : Nat.card ↥E = p ^ 2)
    (hEstar : IsMaximalElementaryAbelian p E) :
    omega1Center R p < E ∧ Nat.card ↥(omega1Center R p) = p := by
  have hZleE : omega1Center R p ≤ E :=
    omega1Center_le_of_maximalElementaryAbelian hEstar
  have hZ_ne_E : omega1Center R p ≠ E := by
    intro hZE
    have hE_le_center : E ≤ Subgroup.center R := by
      intro x hx
      rw [← hZE] at hx
      exact omega1Center_le_center hx
    have hCtop : Subgroup.centralizer (E : Set R) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (Subgroup.mem_center_iff.mp (hE_le_center he) x).symm
    let C : Subgroup R := Subgroup.centralizer (E : Set R)
    let toC : R →* C :=
      { toFun := fun r => ⟨r, by
          dsimp [C]
          rw [hCtop]
          exact Subgroup.mem_top r⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun _ _ => Subtype.ext rfl }
    have hR_le_C : pRank R p ≤ pRank C p :=
      pRank_le_of_injective (G := C) (H := R) (f := toC)
        (fun _ _ hxy => congrArg Subtype.val hxy)
    have h3C : 3 ≤ pRank ↥(Subgroup.centralizer (E : Set R)) p := by
      simpa [C] using h3.trans hR_le_C
    have hC_le_two :
        pRank ↥(Subgroup.centralizer (E : Set R)) p ≤ 2 :=
      pRank_centralizer_le_two_of_maximalElementaryAbelian_card_prime_sq hEcard hEstar
    have : (3 : ℕ) ≤ 2 := h3C.trans hC_le_two
    omega
  have hZltE : omega1Center R p < E := lt_of_le_of_ne hZleE hZ_ne_E
  have hE_card_gt_one : 1 < Nat.card E := by
    rw [hEcard]
    exact one_lt_pow₀ (Fact.out : p.Prime).one_lt two_ne_zero
  haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp hE_card_gt_one
  obtain ⟨e, he_ne⟩ := exists_ne (1 : E)
  haveI : Nontrivial R := ⟨⟨(e : R), 1, fun heq => he_ne (Subtype.ext heq)⟩⟩
  obtain ⟨K, hK_le_center, hKcard⟩ := hpg.exists_subgroup_le_center_card_prime
  have hK_le_Z : K ≤ omega1Center R p := by
    intro x hx
    refine ⟨hK_le_center hx, ?_⟩
    have hxpow := pow_card_eq_one' (G := K) (x := (⟨x, hx⟩ : K))
    have hxpow_coe := congrArg Subtype.val hxpow
    simpa [hKcard] using hxpow_coe
  have hp_le_Z : p ≤ Nat.card (omega1Center R p) := by
    simpa [hKcard] using (Subgroup.card_le_of_le hK_le_Z)
  have hZdvd : Nat.card (omega1Center R p) ∣ p ^ 2 := by
    rw [← hEcard]
    exact Subgroup.card_dvd_of_le hZleE
  obtain ⟨j, hj_le, hj_eq⟩ :=
    (Nat.dvd_prime_pow (p := p) (Fact.out (p := p.Prime))).mp hZdvd
  have hj_ne_zero : j ≠ 0 := by
    intro hj0
    have hp_le_one : p ≤ 1 := by
      simpa [hj0, hj_eq] using hp_le_Z
    exact (not_lt_of_ge hp_le_one) (Fact.out : p.Prime).one_lt
  have hj_ne_two : j ≠ 2 := by
    intro hj2
    have hZcard_eq_E : Nat.card (omega1Center R p) = Nat.card E := by
      rw [hj_eq, hj2, hEcard]
    have hZE : omega1Center R p = E :=
      Subgroup.eq_of_le_of_card_ge hZleE (le_of_eq hZcard_eq_E.symm)
    exact hZ_ne_E hZE
  have hj_eq_one : j = 1 := by omega
  refine ⟨hZltE, ?_⟩
  simpa [hj_eq_one] using hj_eq

/-- **BG Lemma 5.2 support**: under `r(R) ≥ 3` and `E ∈ E*(R)` with `|E| = p²`,
`Ω₁(Z(R))` is a proper subgroup of `Ω₁(Z₂(R))`, and `|Ω₁(Z(R))| = p`.
This packages the textbook transition from `Z < E`, `|Z| = p`, and Lemma 4.5(c)'s
noncyclicity of `W = Ω₁(Z₂(R))` to `Z < W`. -/
theorem omega1Center_lt_omega1UpperCentralTwo_and_card_eq_prime
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) {E : Subgroup R} (hEcard : Nat.card ↥E = p ^ 2)
    (hEstar : IsMaximalElementaryAbelian p E) :
    omega1Center R p < omega1UpperCentralTwo R p ∧
      Nat.card ↥(omega1Center R p) = p := by
  have hZ :=
    omega1Center_lt_and_card_eq_prime_of_maximalElementaryAbelian_card_prime_sq
      hpg h3 hEcard hEstar
  have hWnc := omega1UpperCentralTwo_not_isCyclic_of_three_le_pRank hp hpg h3
  exact ⟨omega1Center_lt_omega1UpperCentralTwo_of_not_isCyclic hZ.2 hWnc, hZ.2⟩

/-- **BG Lemma 5.2 front-half support**: the portion of the proof up through
`Z < W` and `[W, R] ≤ Z`, together with the centralizer rank bound.

This is the reusable sorry-free package for the initial paragraphs of Lemma 5.2:
from `E ∈ E*(R)` and `|E| = p²`, `C_R(E)` has `p`-rank at most `2`; then
`Z = Ω₁(Z(R))` is a proper subgroup of `E` of order `p`; Lemma 4.5(c) in the
`r(R) ≥ 3` context makes `W = Ω₁(Z₂(R))` noncyclic, hence `Z < W`, and the
upper-central-series argument gives `[W, R] ≤ Z`. -/
theorem lemma52_frontHalf_support
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) {E : Subgroup R} (hEcard : Nat.card ↥E = p ^ 2)
    (hEstar : IsMaximalElementaryAbelian p E) :
    pRank ↥(Subgroup.centralizer (E : Set R)) p ≤ 2 ∧
      omega1Center R p < E ∧
      Nat.card ↥(omega1Center R p) = p ∧
      ¬ IsCyclic ↥(omega1UpperCentralTwo R p) ∧
      omega1Center R p < omega1UpperCentralTwo R p ∧
      ⁅omega1UpperCentralTwo R p, (⊤ : Subgroup R)⁆ ≤ omega1Center R p := by
  have hC : pRank ↥(Subgroup.centralizer (E : Set R)) p ≤ 2 :=
    pRank_centralizer_le_two_of_maximalElementaryAbelian_card_prime_sq hEcard hEstar
  have hZ :=
    omega1Center_lt_and_card_eq_prime_of_maximalElementaryAbelian_card_prime_sq
      hpg h3 hEcard hEstar
  have hWnc := omega1UpperCentralTwo_not_isCyclic_of_three_le_pRank hp hpg h3
  have hZW : omega1Center R p < omega1UpperCentralTwo R p :=
    omega1Center_lt_omega1UpperCentralTwo_of_not_isCyclic hZ.2 hWnc
  exact ⟨hC, hZ.1, hZ.2, hWnc, hZW, commutator_omega1UpperCentralTwo_le_omega1Center hp⟩

/-- **BG Lemma 5.2 support**: `W = Ω₁(Z₂(R))` normalizes `E`.

This is the textbook step following `(5.1)` and `(5.2)`: from
`[W, R] ≤ Z = Ω₁(Z(R)) < E`, in particular `[E, W] ≤ E`, so `W ≤ N_R(E)`. -/
theorem omega1UpperCentralTwo_le_normalizer_of_maximalElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) {E : Subgroup R} (hEcard : Nat.card ↥E = p ^ 2)
    (hEstar : IsMaximalElementaryAbelian p E) :
    omega1UpperCentralTwo R p ≤ Subgroup.normalizer (E : Set R) := by
  rcases lemma52_frontHalf_support hp hpg h3 hEcard hEstar with
    ⟨_, hZltE, _, _, _, hWR_le_Z⟩
  have hWE_le_Z : ⁅omega1UpperCentralTwo R p, E⁆ ≤ omega1Center R p := by
    exact (Subgroup.commutator_mono le_rfl (show E ≤ (⊤ : Subgroup R) from le_top)).trans
      hWR_le_Z
  have hEW_le_E : ⁅E, omega1UpperCentralTwo R p⁆ ≤ E := by
    rw [Subgroup.commutator_comm]
    exact hWE_le_Z.trans hZltE.le
  exact OddOrder.Isaacs.Ch04.le_normalizer_of_commutator_le hEW_le_E

private theorem zpowers_isElementaryAbelian_of_pow_eq_one {p : ℕ} {x : R} (hxp : x ^ p = 1) :
    (Subgroup.zpowers x).IsElementaryAbelian p := by
  letI : IsMulCommutative (Subgroup.zpowers x) := Subgroup.zpowers_isMulCommutative x
  refine ⟨?_, ?_⟩
  · intro a b
    exact Subtype.ext (congrArg Subtype.val (mul_comm a b))
  · intro a
    apply Subtype.ext
    change (a : R) ^ p = 1
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    rw [← hi, ← zpow_natCast (x ^ i) p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hxp, one_zpow]

/-- **BG Lemma 5.2 support**: an order-`p` element centralizing a maximal elementary
abelian subgroup already lies in it. This is the elementwise form used for
`C_W(E) ≤ E`; it avoids assuming `W` is elementary abelian. -/
theorem mem_of_mem_centralizer_pow_eq_one_of_maximalElementaryAbelian {p : ℕ}
    {E : Subgroup R} (hEstar : IsMaximalElementaryAbelian p E) {x : R}
    (hxC : x ∈ Subgroup.centralizer (E : Set R)) (hxp : x ^ p = 1) :
    x ∈ E := by
  let X : Subgroup R := Subgroup.zpowers x
  have hX : X.IsElementaryAbelian p := by
    dsimp [X]
    exact zpowers_isElementaryAbelian_of_pow_eq_one hxp
  have hE_le_cent_X : E ≤ Subgroup.centralizer (X : Set R) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    change y ∈ Subgroup.zpowers x at hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hex : e * x = x * e := Subgroup.mem_centralizer_iff.mp hxC e he
    exact ((show Commute e x from hex).zpow_right i).eq.symm
  exact hEstar.le_of_le_centralizer (F := X) hX hE_le_cent_X (Subgroup.mem_zpowers x)

/-- **BG Lemma 5.2 support**: `Z = Ω₁(Z(R))` lies in `C_W(E)`, where
`W = Ω₁(Z₂(R))`. -/
theorem omega1Center_le_omega1UpperCentralTwo_inf_centralizer {p : ℕ} {E : Subgroup R} :
    omega1Center R p ≤ omega1UpperCentralTwo R p ⊓ Subgroup.centralizer (E : Set R) := by
  intro z hz
  refine ⟨omega1Center_le_omega1UpperCentralTwo hz, ?_⟩
  change z ∈ Subgroup.centralizer (E : Set R)
  rw [Subgroup.mem_centralizer_iff]
  intro e _
  exact Subgroup.mem_center_iff.mp (omega1Center_le_center hz) e

/-- **BG Lemma 5.2 support**: `C_W(E) ≤ E`, where `W = Ω₁(Z₂(R))`.
Every element of `W` has `p`-th power `1`, and any element in `C_W(E)` centralizes
`E`; maximality of `E` then absorbs the cyclic elementary abelian subgroup it
generates. -/
theorem omega1UpperCentralTwo_inf_centralizer_le_of_maximalElementaryAbelian
    {p : ℕ} (hp : Odd p) {E : Subgroup R} (hEstar : IsMaximalElementaryAbelian p E) :
    omega1UpperCentralTwo R p ⊓ Subgroup.centralizer (E : Set R) ≤ E := by
  intro x hx
  exact mem_of_mem_centralizer_pow_eq_one_of_maximalElementaryAbelian hEstar hx.2
    (pow_eq_one_of_mem_omega1UpperCentralTwo hp hx.1)

/-- **BG Lemma 5.2 support**: the centralizer `C_W(E)` is squeezed between
`Ω₁(Z(R))` and `E`. -/
theorem omega1Center_le_inf_centralizer_le_of_maximalElementaryAbelian
    {p : ℕ} (hp : Odd p) {E : Subgroup R} (hEstar : IsMaximalElementaryAbelian p E) :
    omega1Center R p ≤ omega1UpperCentralTwo R p ⊓ Subgroup.centralizer (E : Set R) ∧
      omega1UpperCentralTwo R p ⊓ Subgroup.centralizer (E : Set R) ≤ E :=
  ⟨omega1Center_le_omega1UpperCentralTwo_inf_centralizer,
    omega1UpperCentralTwo_inf_centralizer_le_of_maximalElementaryAbelian hp hEstar⟩

/-- **BG Lemma 5.2 support**: if `C_W(E) = E`, then `E` is normal in `R`.
Indeed, the equality puts `E` inside `W`; hence `[E,R] ≤ [W,R] ≤ Z < E`, and the
commutator-normalizer criterion gives normality. -/
theorem normal_of_omega1UpperCentralTwo_inf_centralizer_eq
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) {E : Subgroup R} (hEcard : Nat.card ↥E = p ^ 2)
    (hEstar : IsMaximalElementaryAbelian p E)
    (hCW_eq : omega1UpperCentralTwo R p ⊓ Subgroup.centralizer (E : Set R) = E) :
    E.Normal := by
  rcases lemma52_frontHalf_support hp hpg h3 hEcard hEstar with
    ⟨_, hZltE, _, _, _, hWR_le_Z⟩
  have hE_le_W : E ≤ omega1UpperCentralTwo R p := by
    rw [← hCW_eq]
    exact inf_le_left
  have hER_le_Z : ⁅E, (⊤ : Subgroup R)⁆ ≤ omega1Center R p := by
    exact (Subgroup.commutator_mono hE_le_W le_rfl).trans hWR_le_Z
  have hER_le_E : ⁅E, (⊤ : Subgroup R)⁆ ≤ E := hER_le_Z.trans hZltE.le
  have htop_le_norm : (⊤ : Subgroup R) ≤ Subgroup.normalizer (E : Set R) :=
    OddOrder.Isaacs.Ch04.le_normalizer_of_commutator_le hER_le_E
  exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr htop_le_norm)


/-- **BG Lemma 5.2 support**: the branch `C_W(E) = E` is impossible.

If `C_W(E) = E`, the preceding support lemma makes `E` normal in `R`. Lemma 5.1(b)
then embeds `E` in an `SCN₃` subgroup `A`. The elementary abelian subgroup
`Ω₁(A)` contains `E`, so maximality collapses it back to `E`; but the `SCN₃`
rank condition forces `p³ ∣ |Ω₁(A)|`, contradicting `|E| = p²`. -/
theorem omega1UpperCentralTwo_inf_centralizer_ne_of_maximalElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) {E : Subgroup R} (hEcard : Nat.card ↥E = p ^ 2)
    (hEstar : IsMaximalElementaryAbelian p E) :
    omega1UpperCentralTwo R p ⊓ Subgroup.centralizer (E : Set R) ≠ E := by
  intro hCW_eq
  have hE_normal : E.Normal :=
    normal_of_omega1UpperCentralTwo_inf_centralizer_eq hp hpg h3 hEcard hEstar hCW_eq
  letI : E.Normal := hE_normal
  obtain ⟨A, hA, hEA⟩ :=
    mem_scn3_of_normal_isElementaryAbelian_card_prime_sq hp hpg h3 E
      hEstar.isElementaryAbelian hEcard
  have hA_scn : IsSCN A := hA.isSCN
  have hA_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    letI : IsMulCommutative A := hA_scn.isMulCommutative
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  let F : Subgroup R := omega1OfAbelian R A p hA_comm
  have hF_elem : F.IsElementaryAbelian p := by
    dsimp [F]
    exact
      ⟨fun x y => Subtype.ext (hA_comm x.val x.2.1 y.val y.2.1),
       fun x => Subtype.ext (by simpa using pow_eq_one_of_mem_omega1OfAbelian x.2)⟩
  have hE_le_F : E ≤ F := by
    intro e he
    dsimp [F]
    refine (mem_omega1OfAbelian).mpr ⟨hEA he, ?_⟩
    have hep := hEstar.isElementaryAbelian.pow_eq_one (⟨e, he⟩ : E)
    simpa using congrArg Subtype.val hep
  have hF_eq_E : F = E := hEstar.eq_of_le hF_elem hE_le_F
  have hF_dvd : p ^ 3 ∣ Nat.card F := by
    simpa [F] using
      (pow_dvd_card_omega1OfAbelian_of_pos_le_pRank (G := R) (H := A)
        (p := p) (hH := hA_comm) (n := 3) (by norm_num) hA.le_pRank)
  have hF_ge : p ^ 3 ≤ Nat.card F := Nat.le_of_dvd (Nat.card_pos : 0 < Nat.card F) hF_dvd
  have hle : p ^ 3 ≤ p ^ 2 := by
    rw [hF_eq_E, hEcard] at hF_ge
    exact hF_ge
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hp_sq_lt_cube : p ^ 2 < p ^ 3 :=
    (Nat.pow_lt_pow_iff_right hp1).mpr (by norm_num : (2 : ℕ) < 3)
  exact (not_le_of_gt hp_sq_lt_cube) hle

/-- **BG Lemma 5.2 support**: `C_W(E)` is exactly `Ω₁(Z(R))`.

The squeeze `Z ≤ C_W(E) ≤ E`, the preceding exclusion of `C_W(E)=E`, and
`|Z| = p`, `|E| = p²` leave only the order-`p` possibility. -/
theorem omega1UpperCentralTwo_inf_centralizer_eq_omega1Center
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) {E : Subgroup R} (hEcard : Nat.card ↥E = p ^ 2)
    (hEstar : IsMaximalElementaryAbelian p E) :
    omega1UpperCentralTwo R p ⊓ Subgroup.centralizer (E : Set R) = omega1Center R p := by
  let K : Subgroup R := omega1UpperCentralTwo R p ⊓ Subgroup.centralizer (E : Set R)
  have hZleK : omega1Center R p ≤ K := omega1Center_le_omega1UpperCentralTwo_inf_centralizer
  have hKleE : K ≤ E := by
    dsimp [K]
    exact omega1UpperCentralTwo_inf_centralizer_le_of_maximalElementaryAbelian hp hEstar
  have hK_ne_E : K ≠ E := by
    dsimp [K]
    exact omega1UpperCentralTwo_inf_centralizer_ne_of_maximalElementaryAbelian_card_prime_sq
      hp hpg h3 hEcard hEstar
  have hZcard : Nat.card ↥(omega1Center R p) = p :=
    (omega1Center_lt_and_card_eq_prime_of_maximalElementaryAbelian_card_prime_sq
      hpg h3 hEcard hEstar).2
  have hp_le_K : p ≤ Nat.card K := by
    simpa [hZcard] using Subgroup.card_le_of_le hZleK
  have hKdvd : Nat.card K ∣ p ^ 2 := by
    rw [← hEcard]
    exact Subgroup.card_dvd_of_le hKleE
  obtain ⟨j, hj_le, hj_eq⟩ :=
    (Nat.dvd_prime_pow (p := p) (Fact.out (p := p.Prime))).mp hKdvd
  have hj_ne_zero : j ≠ 0 := by
    intro hj0
    have hp_le_one : p ≤ 1 := by
      simpa [hj0, hj_eq] using hp_le_K
    exact (not_lt_of_ge hp_le_one) (Fact.out : p.Prime).one_lt
  have hj_ne_two : j ≠ 2 := by
    intro hj2
    have hKcard_eq_E : Nat.card K = Nat.card E := by
      rw [hj_eq, hj2, hEcard]
    have hKE : K = E :=
      Subgroup.eq_of_le_of_card_ge hKleE (le_of_eq hKcard_eq_E.symm)
    exact hK_ne_E hKE
  have hj_eq_one : j = 1 := by omega
  have hKcard : Nat.card K = p := by
    simpa [hj_eq_one] using hj_eq
  have hZ_eq_K : omega1Center R p = K :=
    Subgroup.eq_of_le_of_card_ge hZleK (by rw [hKcard, hZcard])
  simpa [K] using hZ_eq_K.symm


/-- **BG Lemma 5.2 support**: the conjugation action of
`W = Ω₁(Z₂(R))` on `E` gives `|W| ≤ p²`.

Since `W ≤ N_R(E)`, restrict the normalizer action `N_R(E) → Aut(E)` to `W`.
Its kernel is `C_W(E) = Ω₁(Z(R))`, already proved above, hence has order `p`; the
image is a `p`-subgroup of `Aut(E)` and has order at most `p` because `|E| = p²`. -/
theorem omega1UpperCentralTwo_card_le_prime_sq_of_maximalElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) {E : Subgroup R} (hEcard : Nat.card ↥E = p ^ 2)
    (hEstar : IsMaximalElementaryAbelian p E) :
    Nat.card ↥(omega1UpperCentralTwo R p) ≤ p ^ 2 := by
  let W : Subgroup R := omega1UpperCentralTwo R p
  let Z : Subgroup R := omega1Center R p
  let N : Subgroup R := Subgroup.normalizer (E : Set R)
  let C : Subgroup R := Subgroup.centralizer (E : Set R)
  have hWleN : W ≤ N := by
    dsimp [W, N]
    exact omega1UpperCentralTwo_le_normalizer_of_maximalElementaryAbelian_card_prime_sq
      hp hpg h3 hEcard hEstar
  let WN : Subgroup N := W.subgroupOf N
  let φ : WN →* MulAut E := E.normalizerMonoidHom.comp WN.subtype
  have hZcard : Nat.card ↥Z = p := by
    dsimp [Z]
    exact (omega1Center_lt_and_card_eq_prime_of_maximalElementaryAbelian_card_prime_sq
      hpg h3 hEcard hEstar).2
  have hCW_eq_Z : W ⊓ C = Z := by
    dsimp [W, C, Z]
    exact omega1UpperCentralTwo_inf_centralizer_eq_omega1Center hp hpg h3 hEcard hEstar
  let incl : WN →* R := N.subtype.comp WN.subtype
  have hincl : Function.Injective incl := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  have hker_map : φ.ker.map incl = Z := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨w, hwker, rfl⟩ := hx
      rw [← hCW_eq_Z]
      have hwW : (w : R) ∈ W := w.2
      have hwC : (w : R) ∈ C := by
        have hwNker : WN.subtype w ∈ E.normalizerMonoidHom.ker := by
          rw [MonoidHom.mem_ker]
          have hφw : φ w = 1 := MonoidHom.mem_ker.mp hwker
          simpa [φ] using hφw
        have hwC_N : WN.subtype w ∈ C.subgroupOf N := by
          simpa [Subgroup.normalizerMonoidHom_ker, C] using hwNker
        exact hwC_N
      exact ⟨hwW, hwC⟩
    · intro hxZ
      have hxK : x ∈ W ⊓ C := by
        rw [hCW_eq_Z]
        exact hxZ
      rw [Subgroup.mem_map]
      have hxN : x ∈ N := hWleN hxK.1
      let n : N := ⟨x, hxN⟩
      have hnWN : n ∈ WN := by
        change (n : R) ∈ W
        exact hxK.1
      let w : WN := ⟨n, hnWN⟩
      refine ⟨w, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      have hwNker : WN.subtype w ∈ E.normalizerMonoidHom.ker := by
        rw [Subgroup.normalizerMonoidHom_ker]
        change (x : R) ∈ C
        exact hxK.2
      simpa [φ] using MonoidHom.mem_ker.mp hwNker
  have hker_card : Nat.card φ.ker = p := by
    have hmap_card : Nat.card (φ.ker.map incl) = Nat.card φ.ker := by
      rw [Subgroup.card_map_of_injective hincl]
    rw [← hmap_card, hker_map, hZcard]
  have hWN_pg : IsPGroup p WN := by
    exact (hpg.to_subgroup W).of_equiv (Subgroup.subgroupOfEquivOfLe hWleN).symm
  have hrange_pg : IsPGroup p φ.range :=
    hWN_pg.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hEcard_le : Nat.card E ≤ p ^ 2 := by
    rw [hEcard]
  have hrange_le : Nat.card φ.range ≤ p :=
    card_pSubgroup_mulAut_le_prime_of_card_le_prime_sq hEstar.isElementaryAbelian hEcard_le
      hrange_pg
  have hLagrange : Nat.card WN = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hWN_le : Nat.card WN ≤ p ^ 2 := by
    rw [hLagrange, hker_card, pow_two]
    exact Nat.mul_le_mul_right p hrange_le
  have hW_card : Nat.card W = Nat.card WN :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWleN).toEquiv).symm
  simpa [W] using hW_card.trans_le hWN_le

/-- **BG Lemma 5.2 support**: `W = Ω₁(Z₂(R))` has order `p²`. -/
theorem omega1UpperCentralTwo_card_eq_prime_sq_of_maximalElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) {E : Subgroup R} (hEcard : Nat.card ↥E = p ^ 2)
    (hEstar : IsMaximalElementaryAbelian p E) :
    Nat.card ↥(omega1UpperCentralTwo R p) = p ^ 2 := by
  let W : Subgroup R := omega1UpperCentralTwo R p
  let Z : Subgroup R := omega1Center R p
  change Nat.card W = p ^ 2
  have hWle : Nat.card W ≤ p ^ 2 := by
    simpa [W] using
      omega1UpperCentralTwo_card_le_prime_sq_of_maximalElementaryAbelian_card_prime_sq
        hp hpg h3 hEcard hEstar
  rcases lemma52_frontHalf_support hp hpg h3 hEcard hEstar with
    ⟨_, _, hZcard, _, hZltW, _⟩
  have hZcard' : Nat.card Z = p := by
    simpa [Z] using hZcard
  have hZltW' : Z < W := by
    simpa [Z, W] using hZltW
  have hZ_card_lt_W : Nat.card Z < Nat.card W :=
    Set.Finite.card_lt_card (Set.toFinite _) (hZltW' : (Z : Set R) ⊂ (W : Set R))
  have hp_lt_W : p < Nat.card W := by
    simpa [hZcard'] using hZ_card_lt_W
  have hW_pg : IsPGroup p W := hpg.to_subgroup W
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hW_pg
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hj_le_two : j ≤ 2 := by
    have hpow_le : p ^ j ≤ p ^ 2 := by
      rw [← hj]
      exact hWle
    exact (Nat.pow_le_pow_iff_right hp1).mp hpow_le
  have hj_ne_zero : j ≠ 0 := by
    intro hj0
    have hp_lt_one : p < 1 := by
      rw [hj, hj0, pow_zero] at hp_lt_W
      exact hp_lt_W
    exact (not_lt_of_ge hp1.le) hp_lt_one
  have hj_ne_one : j ≠ 1 := by
    intro hj1
    have hp_lt_self : p < p := by
      rw [hj, hj1, pow_one] at hp_lt_W
      exact hp_lt_W
    exact (lt_irrefl p) hp_lt_self
  have hj_eq_two : j = 2 := by omega
  rw [hj, hj_eq_two]

/-- **BG Lemma 5.2 support**: `W = Ω₁(Z₂(R))` is elementary abelian. -/
theorem omega1UpperCentralTwo_isElementaryAbelian_of_maximalElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) {E : Subgroup R} (hEcard : Nat.card ↥E = p ^ 2)
    (hEstar : IsMaximalElementaryAbelian p E) :
    (omega1UpperCentralTwo R p).IsElementaryAbelian p := by
  let W : Subgroup R := omega1UpperCentralTwo R p
  change W.IsElementaryAbelian p
  have hWcard : Nat.card W = p ^ 2 := by
    simpa [W] using
      omega1UpperCentralTwo_card_eq_prime_sq_of_maximalElementaryAbelian_card_prime_sq
        hp hpg h3 hEcard hEstar
  refine ⟨?_, ?_⟩
  · intro x y
    exact IsPGroup.commutative_of_card_eq_prime_sq (p := p) (G := W) hWcard x y
  · intro x
    apply Subtype.ext
    exact pow_eq_one_of_mem_omega1UpperCentralTwo hp x.2

/-- **BG Lemma 5.2 support**: `E` does not centralize `W = Ω₁(Z₂(R))`. -/
theorem not_le_centralizer_omega1UpperCentralTwo_of_maximalElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) {E : Subgroup R} (hEcard : Nat.card ↥E = p ^ 2)
    (hEstar : IsMaximalElementaryAbelian p E) :
    ¬ E ≤ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) := by
  intro hE_le_T
  let W : Subgroup R := omega1UpperCentralTwo R p
  let Z : Subgroup R := omega1Center R p
  let C : Subgroup R := Subgroup.centralizer (E : Set R)
  have hCW_eq_Z : W ⊓ C = Z := by
    dsimp [W, C, Z]
    exact omega1UpperCentralTwo_inf_centralizer_eq_omega1Center hp hpg h3 hEcard hEstar
  rcases lemma52_frontHalf_support hp hpg h3 hEcard hEstar with
    ⟨_, _, _, _, hZltW, _⟩
  have hZltW' : Z < W := by
    simpa [Z, W] using hZltW
  have hW_le_C : W ≤ C := by
    intro w hw
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have heT : e ∈ Subgroup.centralizer (W : Set R) := by
      simpa [W] using hE_le_T he
    exact (Subgroup.mem_centralizer_iff.mp heT w hw).symm
  have hW_le_Z : W ≤ Z := by
    intro w hw
    rw [← hCW_eq_Z]
    exact ⟨hw, hW_le_C hw⟩
  exact hZltW'.ne (le_antisymm hZltW'.le hW_le_Z)

private theorem conjNormal_ker_eq_centralizer_for_subgroup
    {G : Type*} [Group G] {V : Subgroup G} [V.Normal] :
    (MulAut.conjNormal (H := V)).ker = Subgroup.centralizer (V : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg v hv
    have hfix : (MulAut.conjNormal g (⟨v, hv⟩ : V) : G) = ((⟨v, hv⟩ : V) : G) := by
      rw [hg]
      rfl
    rw [MulAut.conjNormal_apply] at hfix
    have hcomm : g * v = v * g := by
      have : g * v * g⁻¹ * g = v * g := by rw [hfix]
      simpa [mul_assoc] using this
    exact hcomm.symm
  · intro hg
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    simp only [MulAut.one_apply]
    rw [MulAut.conjNormal_apply]
    have hcomm : (v : G) * g = g * (v : G) := hg (v : G) v.property
    rw [← hcomm]
    group

/-- **BG Lemma 5.2 support**: `T = C_R(W)` has index `p`. -/
theorem centralizer_omega1UpperCentralTwo_index_eq_prime_of_maximalElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) {E : Subgroup R} (hEcard : Nat.card ↥E = p ^ 2)
    (hEstar : IsMaximalElementaryAbelian p E) :
    (Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)).index = p := by
  let W : Subgroup R := omega1UpperCentralTwo R p
  let T : Subgroup R := Subgroup.centralizer (W : Set R)
  haveI hW_normal : W.Normal := by
    dsimp [W]
    infer_instance
  haveI hT_normal : T.Normal := by
    dsimp [T, W]
    infer_instance
  have hWcard : Nat.card W = p ^ 2 := by
    simpa [W] using
      omega1UpperCentralTwo_card_eq_prime_sq_of_maximalElementaryAbelian_card_prime_sq
        hp hpg h3 hEcard hEstar
  have hWelem : W.IsElementaryAbelian p := by
    simpa [W] using
      omega1UpperCentralTwo_isElementaryAbelian_of_maximalElementaryAbelian_card_prime_sq
        hp hpg h3 hEcard hEstar
  let φ : R →* MulAut W := MulAut.conjNormal (H := W)
  have hker : φ.ker = T := by
    simpa [φ, T] using conjNormal_ker_eq_centralizer_for_subgroup (G := R) (V := W)
  have hquot_range : Nat.card (R ⧸ T) = Nat.card φ.range := by
    rw [← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hrange_pg : IsPGroup p φ.range :=
    hpg.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hWcard_le : Nat.card W ≤ p ^ 2 := by
    rw [hWcard]
  have hrange_le : Nat.card φ.range ≤ p :=
    card_pSubgroup_mulAut_le_prime_of_card_le_prime_sq hWelem hWcard_le hrange_pg
  have hquot_le : Nat.card (R ⧸ T) ≤ p := by
    rw [hquot_range]
    exact hrange_le
  have hT_ne_top : T ≠ ⊤ := by
    intro hTtop
    have hE_le_T : E ≤ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) := by
      intro e he
      change e ∈ T
      rw [hTtop]
      exact trivial
    exact not_le_centralizer_omega1UpperCentralTwo_of_maximalElementaryAbelian_card_prime_sq
      hp hpg h3 hEcard hEstar hE_le_T
  have hquot_nontriv : Nontrivial (R ⧸ T) :=
    Subgroup.nontrivial_quotient_of_ne_top hT_ne_top
  have hquot_gt_one : 1 < Nat.card (R ⧸ T) :=
    Finite.one_lt_card_iff_nontrivial.mpr hquot_nontriv
  have hquot_pg : IsPGroup p (R ⧸ T) := hpg.to_quotient T
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hquot_pg
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hj_le_one : j ≤ 1 := by
    have hpow_le : p ^ j ≤ p ^ 1 := by
      rw [← hj, pow_one]
      exact hquot_le
    exact (Nat.pow_le_pow_iff_right hp1).mp hpow_le
  have hj_ne_zero : j ≠ 0 := by
    intro hj0
    have hone_lt_one : 1 < 1 := by
      rw [hj, hj0, pow_zero] at hquot_gt_one
      exact hquot_gt_one
    exact (lt_irrefl 1) hone_lt_one
  have hj_eq_one : j = 1 := by omega
  have hquot_card : Nat.card (R ⧸ T) = p := by
    rw [hj, hj_eq_one, pow_one]
  rw [Subgroup.index_eq_card]
  exact hquot_card

/-- **BG Lemma 5.2**: 奇素数 `p`, 有限 `p`-群 `R`, `r(R) ≥ 3`, `E ∈ ℰ²(R) ∩ ℰ*(R)` (位数 `p²`
の maximal elem-ab)。`T = C_R(Ω₁(Z₂(R)))` とおくと:

* (a) `E ⊄ T`,
* (b) `|Ω₁(Z(R))| = p` かつ `Ω₁(Z₂(R)) ∈ ℰ²(R)` (= `W` が位数 `p²` の elem-ab),
* (c) `T` は `R` の指数 `p` の characteristic 部分群 (char は `NarrowPGroup` で既証, 指数 `p`)。

mmd L1814-1836: `Z=Ω₁(Z(R))⊆E` + `W=Ω₁(Z₂(R))` exp `p` (Lem 4.5c) + `W/C_W(E) ↪ Aut E` の
位数評価 (≤ `p`)。Thm 5.3 の中核。 -/
theorem lemma52 [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) (E : Subgroup R) (hEcard : Nat.card ↥E = p ^ 2)
    (hEstar : IsMaximalElementaryAbelian p E) :
    ¬ E ≤ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) ∧
    (Nat.card ↥(omega1Center R p) = p ∧
      (omega1UpperCentralTwo R p).IsElementaryAbelian p ∧
      Nat.card ↥(omega1UpperCentralTwo R p) = p ^ 2) ∧
    (Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)).index = p := by
  exact
    ⟨not_le_centralizer_omega1UpperCentralTwo_of_maximalElementaryAbelian_card_prime_sq
        hp hpg h3 hEcard hEstar,
      ⟨(omega1Center_lt_and_card_eq_prime_of_maximalElementaryAbelian_card_prime_sq
          hpg h3 hEcard hEstar).2,
        omega1UpperCentralTwo_isElementaryAbelian_of_maximalElementaryAbelian_card_prime_sq
          hp hpg h3 hEcard hEstar,
        omega1UpperCentralTwo_card_eq_prime_sq_of_maximalElementaryAbelian_card_prime_sq
          hp hpg h3 hEcard hEstar⟩,
      centralizer_omega1UpperCentralTwo_index_eq_prime_of_maximalElementaryAbelian_card_prime_sq
        hp hpg h3 hEcard hEstar⟩

/-- **BG §5 narrow witness extraction**: when `r(R) ≥ 3`, the first disjunct in the
definition of `IsNarrow` is impossible, so a narrow group supplies BG's order-`p`
witness `R₀` and cyclic complement `R₁` inside `C_R(R₀)`.

This is the definition-level forward support for Corollary 5.4; it does not assert the
hard rank/decomposition conclusions of Theorem 5.3. -/
theorem exists_narrow_witness_of_three_le_pRank {p : ℕ}
    (h3 : 3 ≤ pRank R p) (hnarrow : IsNarrow p R) :
    ∃ R₀ R₁ : Subgroup R, Nat.card R₀ = p ∧ IsCyclic R₁ ∧
      R₀ ⊓ R₁ = ⊥ ∧ Subgroup.centralizer (R₀ : Set R) = R₀ ⊔ R₁ := by
  rcases hnarrow with hrank | hwitness
  · omega
  · exact hwitness

private theorem pRank_centralizer_le_two_of_narrow_witness
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    {S K : Subgroup R} (hScard : Nat.card S = p) (hKcyc : IsCyclic K)
    (hSKinf : S ⊓ K = ⊥) (hCeq : Subgroup.centralizer (S : Set R) = S ⊔ K) :
    pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2 := by
  classical
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  have hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    have hScyc : IsCyclic S := isCyclic_of_prime_card hScard
    haveI : IsCyclic S := hScyc
    letI : CommGroup S := IsCyclic.commGroup
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : S) (⟨b, hb⟩ : S))
  have hSleC : S ≤ C := by
    intro s hs
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (hScomm s hs t ht).symm
  have hKleC : K ≤ C := by
    dsimp [C]
    rw [hCeq]
    exact le_sup_right
  let Ssub : Subgroup C := S.subgroupOf C
  let Ksub : Subgroup C := K.subgroupOf C
  have hSsub_card : Nat.card Ssub = p := by
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSleC).toEquiv).trans hScard
  have hKsub_cyc : IsCyclic Ksub := by
    haveI : IsCyclic K := hKcyc
    exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hKleC).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hKleC).injective
  have hSsub_inf : Ssub ⊓ Ksub = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    change (x : R) = 1
    have hxR : (x : R) ∈ S ⊓ K := by
      exact ⟨hx.1, hx.2⟩
    rwa [hSKinf, Subgroup.mem_bot] at hxR
  have hSsub_le_center : Ssub ≤ Subgroup.center C := by
    intro s hs
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp c.2 (s : R) hs).symm
  haveI hSsub_normal : Ssub.Normal := by
    refine { conj_mem := fun x hx g => ?_ }
    have hx_center : x ∈ Subgroup.center C := hSsub_le_center hx
    have hconj : g * x * g⁻¹ = x := by
      have hcomm := Subgroup.mem_center_iff.mp hx_center g
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hcomm]
        _ = x := by group
    rwa [hconj]
  have hSup_top : Ssub ⊔ Ksub = ⊤ := by
    calc
      Ssub ⊔ Ksub = (S ⊔ K).subgroupOf C :=
        (Subgroup.subgroupOf_sup hSleC hKleC).symm
      _ = ⊤ := by
        rw [← hCeq]
        exact Subgroup.subgroupOf_self C
  have hCcard : Nat.card C = p * Nat.card Ksub := by
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card Ssub Ksub
    rw [← Subgroup.normal_mul Ssub Ksub, hSsub_inf, Subgroup.card_bot, hSsub_card,
      mul_one, hSup_top] at hcard
    simpa [Subgroup.coe_top] using hcard
  have hKsub_index : Ksub.index = p := by
    have hmul : Ksub.index * Nat.card Ksub = Nat.card C := Ksub.index_mul_card
    have hmul' : Ksub.index * Nat.card Ksub = p * Nat.card Ksub := by
      simpa [hCcard] using hmul
    exact Nat.mul_right_cancel (Nat.card_pos (α := Ksub)) hmul'
  obtain ⟨x, hx⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Ksub).mp hKsub_cyc
  have hidx : (Subgroup.zpowers x).index = p := by
    rw [hx]
    exact hKsub_index
  have hOmega_le : Nat.card (Omega C p 1) ≤ p ^ 2 :=
    OddOrder.BG.Ch1.S04.card_omega1_le_prime_sq_of_cyclic_index_prime
      (hpg.to_subgroup C) hp hidx
  rw [pRank_le_iff]
  intro A hA
  have hA_le_omega : A ≤ Omega C p 1 := by
    rw [Omega]
    intro a ha
    exact Subgroup.subset_closure (by
      rw [Set.mem_setOf_eq, pow_one]
      exact congrArg Subtype.val (hA.pow_eq_one ⟨a, ha⟩))
  have hAcard_le : Nat.card A ≤ Nat.card (Omega C p 1) := Subgroup.card_le_of_le hA_le_omega
  have hlog_le : Nat.log p (Nat.card A) ≤ Nat.log p (p ^ 2) :=
    Nat.log_mono_right (hAcard_le.trans hOmega_le)
  simpa [Nat.log_pow (Fact.out : p.Prime).one_lt] using hlog_le

/-- **BG Theorem 5.3(d) support**: if an order-p subgroup has centralizer
p-rank at most two, then it meets Omega_1 of the center trivially under the
standing rank-at-least-three hypothesis. -/
private theorem inf_omega1Center_eq_bot_of_card_prime_centralizer_pRank_le_two
    [Finite R] {p : ℕ} [Fact p.Prime] (h3 : 3 ≤ pRank R p)
    {S : Subgroup R} (hScard : Nat.card S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2) :
    S ⊓ omega1Center R p = ⊥ := by
  classical
  let Z : Subgroup R := omega1Center R p
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  have hS_not_le_Z : ¬ S ≤ Z := by
    intro hSleZ
    have hCtop : C = ⊤ := by
      rw [eq_top_iff]
      intro x _
      dsimp [C]
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact (Subgroup.mem_center_iff.mp (omega1Center_le_center (hSleZ hs)) x).symm
    let toC : R →* C :=
      { toFun := fun r => ⟨r, by rw [hCtop]; exact trivial⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have htoC_inj : Function.Injective toC := by
      intro x y hxy
      exact congrArg Subtype.val hxy
    have hRrank_le_C : pRank R p ≤ pRank C p :=
      pRank_le_of_injective (G := C) (H := R) (f := toC) htoC_inj
    exact absurd (hRrank_le_C.trans hSrank) (by omega)
  let H : Subgroup S := (S ⊓ Z).subgroupOf S
  haveI : Fact (Nat.card S).Prime := ⟨by rw [hScard]; exact (Fact.out : p.Prime)⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card H with hHbot | hHtop
  · refine le_antisymm ?_ bot_le
    intro x hx
    have hxH : (⟨x, hx.1⟩ : S) ∈ H := by
      dsimp [H]
      rw [Subgroup.mem_subgroupOf]
      exact hx
    rw [hHbot, Subgroup.mem_bot] at hxH
    exact Subtype.ext_iff.mp hxH
  · exfalso
    apply hS_not_le_Z
    intro s hs
    have hsH : (⟨s, hs⟩ : S) ∈ H := by
      rw [hHtop]
      exact trivial
    exact (Subgroup.mem_subgroupOf.mp hsH).2

/-- **BG Corollary 5.4 forward support**: under rank at least three, a definitional
narrow witness has centralizer p-rank at most two. This is the direct Lean version
of the first sentence of BG Corollary 5.4, using the cyclic-complement form of narrowness. -/
theorem exists_card_prime_centralizer_pRank_le_two_of_narrow
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) (hnarrow : IsNarrow p R) :
    ∃ S : Subgroup R, Nat.card S = p ∧
      pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2 := by
  obtain ⟨S, K, hScard, hKcyc, hSKinf, hCeq⟩ :=
    exists_narrow_witness_of_three_le_pRank h3 hnarrow
  exact ⟨S, hScard,
    pRank_centralizer_le_two_of_narrow_witness hp hpg hScard hKcyc hSKinf hCeq⟩

/-! ## Theorem 5.3 / Corollary 5.4 — narrow の特徴づけ (mmd L1838-1879) -/

/-- **BG Theorem 5.3(d) support**: since `R' ≤ T = C_R(Ω₁(Z₂(R)))`,
the disjointness `S ∩ T = 1` implies `S ∩ R' = 1`.

This isolates the already-green commutator-to-`T` input from the remaining hard
centralizer decomposition proof. -/
theorem inf_commutator_eq_bot_of_inf_centralizer_omega1UpperCentralTwo_eq_bot
    {p : ℕ} {S : Subgroup R}
    (hST : S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) = ⊥) :
    S ⊓ commutator R = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [← hST]
  exact ⟨hx.1, commutator_le_centralizer_omega1UpperCentralTwo hx.2⟩

private theorem isElementaryAbelian_of_card_prime [Finite R] {p : ℕ} [Fact p.Prime]
    {S : Subgroup R} (hS : Nat.card S = p) : S.IsElementaryAbelian p := by
  have hScyc : IsCyclic S := isCyclic_of_prime_card hS
  constructor
  · haveI : IsCyclic S := hScyc
    letI : CommGroup S := IsCyclic.commGroup
    intro x y
    exact mul_comm x y
  · intro x
    have hx := pow_card_eq_one' (G := S) (x := x)
    simpa [hS] using hx

private theorem sup_eq_of_card_prime_ne_of_le_isElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] {E H K : Subgroup R}
    (hE : E.IsElementaryAbelian p) (hEcard : Nat.card E = p ^ 2)
    (hHE : H ≤ E) (hKE : K ≤ E) (hHcard : Nat.card H = p) (hKcard : Nat.card K = p)
    (hHKne : H ≠ K) : H ⊔ K = E := by
  classical
  let H' : Subgroup E := H.subgroupOf E
  let K' : Subgroup E := K.subgroupOf E
  have hH'card : Nat.card H' = p := by
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHE).toEquiv).trans hHcard
  have hK'card : Nat.card K' = p := by
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE).toEquiv).trans hKcard
  have hH'K'ne : H' ≠ K' := by
    intro h'
    apply hHKne
    calc H = H'.map E.subtype := (Subgroup.map_subgroupOf_eq_of_le hHE).symm
      _ = K'.map E.subtype := by rw [h']
      _ = K := Subgroup.map_subgroupOf_eq_of_le hKE
  have hInf_bot : H' ⊓ K' = ⊥ := by
    have hInf_dvd : Nat.card ↥(H' ⊓ K') ∣ p := by
      rw [← hH'card]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hInf_dvd with hInf_card | hInf_card
    · exact Subgroup.eq_bot_of_card_eq _ hInf_card
    · exfalso
      have hInf_eq_H : H' ⊓ K' = H' :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hInf_card, hH'card])
      have hInf_eq_K : H' ⊓ K' = K' :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hInf_card, hK'card])
      exact hH'K'ne (hInf_eq_H.symm.trans hInf_eq_K)
  letI : IsMulCommutative E := IsMulCommutative.of_comm hE.comm
  haveI : H'.Normal := by infer_instance
  have hsup_card : Nat.card ↥(H' ⊔ K') = p ^ 2 := by
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card H' K'
    rw [← Subgroup.normal_mul H' K', hInf_bot, Subgroup.card_bot, hH'card, hK'card,
      mul_one] at hcard
    simpa [pow_two] using hcard
  have hsup_top : H' ⊔ K' = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    simpa [Subgroup.card_top, hEcard] using hsup_card
  have hmap : (H' ⊔ K').map E.subtype = H ⊔ K := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hHE,
      Subgroup.map_subgroupOf_eq_of_le hKE]
  calc H ⊔ K = (H' ⊔ K').map E.subtype := hmap.symm
    _ = (⊤ : Subgroup E).map E.subtype := by rw [hsup_top]
    _ = E := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨e, _, rfl⟩ := hx
        exact e.2
      · intro hx
        rw [Subgroup.mem_map]
        exact ⟨⟨x, hx⟩, trivial, rfl⟩

private theorem centralizer_le_centralizer_of_sup_omega1Center_eq
    {p : ℕ} {S E : Subgroup R} (hE : omega1Center R p ⊔ S = E) :
    Subgroup.centralizer (S : Set R) ≤ Subgroup.centralizer (E : Set R) := by
  rw [← hE, Subgroup.centralizer_sup]
  refine le_inf ?_ le_rfl
  intro x _
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_center_iff.mp (omega1Center_le_center hz) x).symm

private theorem exists_card_prime_centralizer_pRank_le_two_of_maximalElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] (hpg : IsPGroup p R) (h3 : 3 ≤ pRank R p)
    (hExists : ∃ E : Subgroup R, Nat.card E = p ^ 2 ∧ IsMaximalElementaryAbelian p E) :
    ∃ S : Subgroup R, Nat.card S = p ∧
      pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2 := by
  obtain ⟨E, hEcard, hEstar⟩ := hExists
  have hEelem : E.IsElementaryAbelian p := hEstar.isElementaryAbelian
  obtain ⟨K, L, hKle, hLle, hKcard, hLcard, hKLne⟩ :=
    Subgroup.exists_distinct_subgroups_card_prime_of_isElementaryAbelian_card_prime_sq
      (G := R) (H := E) (Fact.out : p.Prime) hEelem hEcard
  have hZleE : omega1Center R p ≤ E := omega1Center_le_of_maximalElementaryAbelian hEstar
  have hZcard : Nat.card (omega1Center R p) = p :=
    (omega1Center_lt_and_card_eq_prime_of_maximalElementaryAbelian_card_prime_sq
      hpg h3 hEcard hEstar).2
  have hCErank : pRank ↥(Subgroup.centralizer (E : Set R)) p ≤ 2 :=
    pRank_centralizer_le_two_of_maximalElementaryAbelian_card_prime_sq hEcard hEstar
  by_cases hKZ : K = omega1Center R p
  · have hLZ : L ≠ omega1Center R p := by
      intro hLZ
      exact hKLne (hKZ.trans hLZ.symm)
    have hZE_sup : omega1Center R p ⊔ L = E :=
      sup_eq_of_card_prime_ne_of_le_isElementaryAbelian_card_prime_sq
        hEelem hEcard hZleE hLle hZcard hLcard (fun h => hLZ h.symm)
    have hC_le : Subgroup.centralizer (L : Set R) ≤ Subgroup.centralizer (E : Set R) :=
      centralizer_le_centralizer_of_sup_omega1Center_eq hZE_sup
    have hLrank : pRank ↥(Subgroup.centralizer (L : Set R)) p ≤ 2 :=
      (pRank_le_of_injective (G := ↥(Subgroup.centralizer (E : Set R)))
        (H := ↥(Subgroup.centralizer (L : Set R)))
        (f := Subgroup.inclusion hC_le) (Subgroup.inclusion_injective hC_le)).trans hCErank
    exact ⟨L, hLcard, hLrank⟩
  · have hZE_sup : omega1Center R p ⊔ K = E :=
      sup_eq_of_card_prime_ne_of_le_isElementaryAbelian_card_prime_sq
        hEelem hEcard hZleE hKle hZcard hKcard (fun h => hKZ h.symm)
    have hC_le : Subgroup.centralizer (K : Set R) ≤ Subgroup.centralizer (E : Set R) :=
      centralizer_le_centralizer_of_sup_omega1Center_eq hZE_sup
    have hKrank : pRank ↥(Subgroup.centralizer (K : Set R)) p ≤ 2 :=
      (pRank_le_of_injective (G := ↥(Subgroup.centralizer (E : Set R)))
        (H := ↥(Subgroup.centralizer (K : Set R)))
        (f := Subgroup.inclusion hC_le) (Subgroup.inclusion_injective hC_le)).trans hCErank
    exact ⟨K, hKcard, hKrank⟩

private theorem exists_elementaryAbelian_card_prime_sq_le_centralizer_of_card_prime
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) {S : Subgroup R} (hScard : Nat.card S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2) :
    ∃ E : Subgroup R, E.IsElementaryAbelian p ∧ Nat.card E = p ^ 2 ∧
      S ≤ E ∧ E ≤ Subgroup.centralizer (S : Set R) := by
  classical
  obtain ⟨A, hA⟩ := scn3_nonempty_of_three_le_pRank hp hpg h3
  obtain ⟨B, hB_normal, hB_elem, hBcard⟩ :=
    exists_normal_isElementaryAbelian_card_prime_cube_of_scn3 hpg hA
  haveI : B.Normal := hB_normal
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  have hS_elem : S.IsElementaryAbelian p := isElementaryAbelian_of_card_prime hScard
  have hB_ne_bot : B ≠ ⊥ := by
    intro hBbot
    have hcard_one : Nat.card B = 1 := by rw [hBbot, Subgroup.card_bot]
    have hp3_gt_one : 1 < p ^ 3 := one_lt_pow₀ (Fact.out : p.Prime).one_lt (by norm_num)
    exact (ne_of_gt hp3_gt_one) (by rw [← hBcard, hcard_one])
  have hnotSB : ¬ S ≤ B := by
    intro hSB
    have hB_le_C : B ≤ C := by
      intro b hb
      dsimp [C]
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val (hB_elem.comm ⟨s, hSB hs⟩ ⟨b, hb⟩)
    let Bsub : Subgroup C := B.subgroupOf C
    have hBsub_elem : Bsub.IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hB_le_C).symm hB_elem
    have hBsub_card : Nat.card Bsub = p ^ 3 := by
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_C).toEquiv).trans hBcard
    have hBrank : 3 ≤ pRank C p :=
      pow_le_card_of_le_pRank Bsub hBsub_elem hBsub_card
    have : 3 ≤ 2 := hBrank.trans hSrank
    omega
  have hSBinf : S ⊓ B = ⊥ := by
    have hInf_dvd : Nat.card ↥(S ⊓ B) ∣ p := by
      rw [← hScard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hInf_dvd with hInf_card | hInf_card
    · exact Subgroup.eq_bot_of_card_eq _ hInf_card
    · exfalso
      have hInf_eq_S : S ⊓ B = S :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hInf_card, hScard])
      have hSB : S ≤ B := by
        intro x hx
        have hxInf : x ∈ S ⊓ B := by simpa [hInf_eq_S] using hx
        exact hxInf.2
      exact hnotSB hSB
  obtain ⟨b, hbB, hbZ, hbne⟩ :=
    OddOrder.GroupTheory.exists_mem_center_of_normal_ne_bot hpg (K := B) hB_ne_bot
  let U : Subgroup R := Subgroup.zpowers b
  have hb_pow : b ^ p = 1 := by
    simpa using congrArg Subtype.val (hB_elem.pow_eq_one (⟨b, hbB⟩ : B))
  have hb_order : orderOf b = p := orderOf_eq_prime hb_pow hbne
  have hUcard : Nat.card U = p := by
    rw [show U = Subgroup.zpowers b from rfl, Nat.card_zpowers, hb_order]
  have hU_elem : U.IsElementaryAbelian p := isElementaryAbelian_of_card_prime hUcard
  have hU_le_B : U ≤ B := Subgroup.zpowers_le.mpr hbB
  have hU_le_center : U ≤ Subgroup.center R := Subgroup.zpowers_le.mpr hbZ
  have hSUinf : S ⊓ U = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hxSB : x ∈ S ⊓ B := ⟨hx.1, hU_le_B hx.2⟩
    rwa [hSBinf] at hxSB
  have hS_le_cent_U : S ≤ Subgroup.centralizer (U : Set R) := by
    intro s _
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_center_iff.mp (hU_le_center hu) s).symm
  let E0 : Subgroup R := S ⊔ U
  have hE0_elem : E0.IsElementaryAbelian p := by
    simpa [E0] using
      Subgroup.IsElementaryAbelian.sup_of_le_centralizer hS_elem hU_elem hS_le_cent_U
  haveI hU_normal : U.Normal := by
    refine { conj_mem := fun x hx g => ?_ }
    have hx_center : x ∈ Subgroup.center R := hU_le_center hx
    have hconj : g * x * g⁻¹ = x := by
      have hcomm := Subgroup.mem_center_iff.mp hx_center g
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hcomm]
        _ = x := by group
    rwa [hconj]
  have hE0card : Nat.card E0 = p ^ 2 := by
    have hUSinf : U ⊓ S = ⊥ := by rwa [inf_comm]
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card U S
    rw [← Subgroup.normal_mul U S, hUSinf, Subgroup.card_bot, hUcard, hScard, mul_one] at hcard
    simpa [E0, sup_comm, pow_two, mul_comm] using hcard
  have hS_le_C : S ≤ C := by
    intro s hs
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (hS_elem.comm ⟨t, ht⟩ ⟨s, hs⟩)
  have hU_le_C : U ≤ C := by
    intro u hu
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro s _
    exact Subgroup.mem_center_iff.mp (hU_le_center hu) s
  have hE0_le_C : E0 ≤ C := by
    dsimp [E0]
    exact sup_le hS_le_C hU_le_C
  exact ⟨E0, hE0_elem, hE0card, le_sup_left, hE0_le_C⟩

private theorem exists_maximalElementaryAbelian_card_prime_sq_of_card_prime_centralizer_pRank_le_two
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p)
    (hExists : ∃ S : Subgroup R, Nat.card S = p ∧
      pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2) :
    ∃ E : Subgroup R, Nat.card E = p ^ 2 ∧ IsMaximalElementaryAbelian p E := by
  obtain ⟨S, hScard, hSrank⟩ := hExists
  obtain ⟨E0, hE0elem, hE0card, hSleE0, hE0leC⟩ :=
    exists_elementaryAbelian_card_prime_sq_le_centralizer_of_card_prime hp hpg h3 hScard hSrank
  obtain ⟨F, hE0F, hFstar⟩ := exists_maximalElementaryAbelian_ge hE0elem
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  have hFelem : F.IsElementaryAbelian p := hFstar.isElementaryAbelian
  have hSleF : S ≤ F := hSleE0.trans hE0F
  have hFleC : F ≤ C := by
    intro f hf
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val (hFelem.comm ⟨s, hSleF hs⟩ ⟨f, hf⟩)
  let Fsub : Subgroup C := F.subgroupOf C
  have hFsub_elem : Fsub.IsElementaryAbelian p :=
    IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFleC).symm hFelem
  have hFsub_card : Nat.card Fsub = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFleC).toEquiv
  have hlogFsub_le : Nat.log p (Nat.card Fsub) ≤ 2 :=
    (pRank_le_iff.mp hSrank) Fsub hFsub_elem
  have hlogF_le : Nat.log p (Nat.card F) ≤ 2 := by
    simpa [Fsub, hFsub_card] using hlogFsub_le
  have hE0_card_le_F : Nat.card E0 ≤ Nat.card F :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hE0F) (Subgroup.inclusion_injective hE0F)
  have hpow_le : p ^ 2 ≤ Nat.card F := by
    simpa [hE0card] using hE0_card_le_F
  have hlogF_ge : 2 ≤ Nat.log p (Nat.card F) :=
    Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt hpow_le
  have hlogF_eq : Nat.log p (Nat.card F) = 2 := le_antisymm hlogF_le hlogF_ge
  have hFcard : Nat.card F = p ^ 2 := by
    have hcard_pow := hFelem.card_eq_pow_finrank
    have hlog_fin := hFelem.log_card_eq_finrank
    rw [hcard_pow, ← hlog_fin, hlogF_eq]
  exact ⟨F, hFcard, hFstar⟩

private theorem le_of_inf_ne_bot_of_card_prime
    [Finite R] {p : ℕ} [Fact p.Prime] {S H : Subgroup R}
    (hScard : Nat.card S = p) (hInf_ne : S ⊓ H ≠ ⊥) : S ≤ H := by
  classical
  let L : Subgroup S := (S ⊓ H).subgroupOf S
  haveI : Fact (Nat.card S).Prime := ⟨by rw [hScard]; exact (Fact.out : p.Prime)⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card L with hLbot | hLtop
  · exfalso
    apply hInf_ne
    refine le_antisymm ?_ bot_le
    intro x hx
    have hxL : (⟨x, hx.1⟩ : S) ∈ L := by
      dsimp [L]
      rw [Subgroup.mem_subgroupOf]
      exact hx
    rw [hLbot, Subgroup.mem_bot] at hxL
    exact Subtype.ext_iff.mp hxL
  · intro s hs
    have hsL : (⟨s, hs⟩ : S) ∈ L := by
      rw [hLtop]
      exact trivial
    exact (Subgroup.mem_subgroupOf.mp hsL).2

/-- **BG Theorem 5.3(d) support**: with centralizer p-rank at most two,
the subgroup generated by an order-p subgroup S and Omega_1 of the center is
itself a maximal elementary abelian subgroup of order p squared. -/
private theorem sup_omega1Center_maximalElementaryAbelian_of_centralizer_pRank_le_two
    [Finite R] {p : ℕ} [Fact p.Prime] (h3 : 3 ≤ pRank R p)
    {S : Subgroup R} (hScard : Nat.card S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2)
    (hZcard : Nat.card (omega1Center R p) = p) :
    Nat.card ↥(S ⊔ omega1Center R p) = p ^ 2 ∧
      IsMaximalElementaryAbelian p (S ⊔ omega1Center R p) := by
  classical
  let Z : Subgroup R := omega1Center R p
  let E : Subgroup R := S ⊔ Z
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  have hS_elem : S.IsElementaryAbelian p := isElementaryAbelian_of_card_prime hScard
  have hZ_elem : Z.IsElementaryAbelian p := by
    dsimp [Z]
    exact omega1Center_isElementaryAbelian
  have hS_le_cent_Z : S ≤ Subgroup.centralizer (Z : Set R) := by
    intro s _
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_center_iff.mp (omega1Center_le_center hz) s).symm
  have hE_elem : E.IsElementaryAbelian p := by
    dsimp [E]
    exact Subgroup.IsElementaryAbelian.sup_of_le_centralizer hS_elem hZ_elem hS_le_cent_Z
  have hSZinf : S ⊓ Z = ⊥ := by
    simpa [Z] using
      inf_omega1Center_eq_bot_of_card_prime_centralizer_pRank_le_two
        h3 hScard hSrank
  haveI hZ_normal : Z.Normal := by
    refine { conj_mem := fun x hx g => ?_ }
    have hx_center : x ∈ Subgroup.center R := omega1Center_le_center hx
    have hconj : g * x * g⁻¹ = x := by
      have hcomm := Subgroup.mem_center_iff.mp hx_center g
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hcomm]
        _ = x := by group
    rwa [hconj]
  have hEcard : Nat.card E = p ^ 2 := by
    have hZSinf : Z ⊓ S = ⊥ := by rwa [inf_comm]
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card Z S
    rw [← Subgroup.normal_mul Z S, hZSinf, Subgroup.card_bot, hZcard, hScard,
      mul_one] at hcard
    simpa [E, sup_comm, pow_two, mul_comm] using hcard
  obtain ⟨F, hE_le_F, hFstar⟩ := exists_maximalElementaryAbelian_ge hE_elem
  have hFelem : F.IsElementaryAbelian p := hFstar.isElementaryAbelian
  have hSleE : S ≤ E := by
    dsimp [E]
    exact le_sup_left
  have hSleF : S ≤ F := hSleE.trans hE_le_F
  have hFleC : F ≤ C := by
    intro f hf
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val (hFelem.comm ⟨s, hSleF hs⟩ ⟨f, hf⟩)
  let Fsub : Subgroup C := F.subgroupOf C
  have hFsub_elem : Fsub.IsElementaryAbelian p :=
    IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFleC).symm hFelem
  have hFsub_card : Nat.card Fsub = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFleC).toEquiv
  have hlogFsub_le : Nat.log p (Nat.card Fsub) ≤ 2 :=
    (pRank_le_iff.mp hSrank) Fsub hFsub_elem
  have hlogF_le : Nat.log p (Nat.card F) ≤ 2 := by
    simpa [Fsub, hFsub_card] using hlogFsub_le
  have hE_card_le_F : Nat.card E ≤ Nat.card F :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hE_le_F)
      (Subgroup.inclusion_injective hE_le_F)
  have hpow_le : p ^ 2 ≤ Nat.card F := by
    simpa [hEcard] using hE_card_le_F
  have hlogF_ge : 2 ≤ Nat.log p (Nat.card F) :=
    Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt hpow_le
  have hlogF_eq : Nat.log p (Nat.card F) = 2 := le_antisymm hlogF_le hlogF_ge
  have hFcard : Nat.card F = p ^ 2 := by
    have hcard_pow := hFelem.card_eq_pow_finrank
    have hlog_fin := hFelem.log_card_eq_finrank
    rw [hcard_pow, ← hlog_fin, hlogF_eq]
  have hE_eq_F : E = F :=
    Subgroup.eq_of_le_of_card_ge hE_le_F (by rw [hEcard, hFcard])
  have hEstar : IsMaximalElementaryAbelian p E := by
    rw [hE_eq_F]
    exact hFstar
  exact ⟨by simpa [E] using hEcard, by simpa [E] using hEstar⟩


private theorem centralizer_eq_sup_inf_of_card_prime_inf_bot_index_prime
    [Finite R] {p : ℕ} [Fact p.Prime] {S T : Subgroup R} [T.Normal]
    (hScard : Nat.card S = p) (hST : S ⊓ T = ⊥) (hTindex : T.index = p) :
    Subgroup.centralizer (S : Set R) =
      S ⊔ (Subgroup.centralizer (S : Set R) ⊓ T) := by
  classical
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  let K : Subgroup R := C ⊓ T
  have hS_elem : S.IsElementaryAbelian p := isElementaryAbelian_of_card_prime hScard
  have hSleC : S ≤ C := by
    intro s hs
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (hS_elem.comm ⟨t, ht⟩ ⟨s, hs⟩)
  let Ssub : Subgroup C := S.subgroupOf C
  let Ksub : Subgroup C := K.subgroupOf C
  have hSsub_card : Nat.card Ssub = p := by
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSleC).toEquiv).trans hScard
  have hSsub_inf : Ssub ⊓ Ksub = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    change (x : R) = 1
    have hxST : (x : R) ∈ S ⊓ T := ⟨hx.1, hx.2.2⟩
    rwa [hST, Subgroup.mem_bot] at hxST
  have hSsub_le_center : Ssub ≤ Subgroup.center C := by
    intro s hs
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp c.2 (s : R) hs).symm
  haveI hSsub_normal : Ssub.Normal := by
    refine { conj_mem := fun x hx g => ?_ }
    have hx_center : x ∈ Subgroup.center C := hSsub_le_center hx
    have hconj : g * x * g⁻¹ = x := by
      have hcomm := Subgroup.mem_center_iff.mp hx_center g
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hcomm]
        _ = x := by group
    rwa [hconj]
  have hrel_dvd : K.relIndex C ∣ p := by
    have hrel : K.relIndex C = T.relIndex C := by
      dsimp [K]
      rw [inf_comm]
      exact Subgroup.inf_relIndex_right T C
    rw [hrel, ← hTindex]
    exact Subgroup.relIndex_dvd_index_of_normal T C
  have hrel_ne_one : K.relIndex C ≠ 1 := by
    intro hrel_one
    have hCleK : C ≤ K := Subgroup.relIndex_eq_one.mp hrel_one
    have hSleT : S ≤ T := by
      intro s hs
      exact (hCleK (hSleC hs)).2
    have hSbot : S = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro s hs
      have hsST : s ∈ S ⊓ T := ⟨hs, hSleT hs⟩
      rwa [hST] at hsST
    have hcard_one : Nat.card S = 1 := by rw [hSbot, Subgroup.card_bot]
    have hp_gt_one : 1 < p := (Fact.out : p.Prime).one_lt
    omega
  have hKrel : K.relIndex C = p := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hrel_dvd with h | h
    · exact absurd h hrel_ne_one
    · exact h
  have hKsub_index : Ksub.index = p := by
    change K.relIndex C = p
    exact hKrel
  have hCcard : Nat.card C = p * Nat.card Ksub := by
    have hmul : Ksub.index * Nat.card Ksub = Nat.card C := Ksub.index_mul_card
    rw [hKsub_index] at hmul
    exact hmul.symm
  have hSup_card : Nat.card ↥(Ssub ⊔ Ksub) = p * Nat.card Ksub := by
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card Ssub Ksub
    rw [← Subgroup.normal_mul Ssub Ksub, hSsub_inf, Subgroup.card_bot, hSsub_card,
      mul_one] at hcard
    simpa [SetLike.coe_sort_coe, Subgroup.coe_mul] using hcard
  have hSup_top : Ssub ⊔ Ksub = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    simpa [Subgroup.card_top, hCcard] using hSup_card
  calc
    C = (⊤ : Subgroup C).map C.subtype := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_map]
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
      · intro hx
        rw [Subgroup.mem_map] at hx
        rcases hx with ⟨x, _, rfl⟩
        exact x.2
    _ = (Ssub ⊔ Ksub).map C.subtype := by rw [hSup_top]
    _ = S ⊔ (C ⊓ T) := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hSleC,
        Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    _ = S ⊔ (Subgroup.centralizer (S : Set R) ⊓ T) := by rfl

/-- **BG Theorem 5.3(d) support**: under `r(R) ≥ 3` and the existence of some
`E ∈ ℰ²(R) ∩ ℰ*(R)` (so that Lemma 5.2 applies), every order-`p` subgroup `S` with
`r(C_R(S)) ≤ 2` satisfies `S ∩ T = 1` for `T = C_R(Ω₁(Z₂(R)))` (mmd L1862:
`SZ ⊄ T` together with `Z ≤ T` forces `S ∩ T = 1`). -/
private theorem inf_centralizer_omega1UpperCentralTwo_eq_bot_of_exists_maximalElementaryAbelian
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p)
    (hEx : ∃ E : Subgroup R, Nat.card E = p ^ 2 ∧ IsMaximalElementaryAbelian p E)
    {S : Subgroup R} (hScard : Nat.card S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2) :
    S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) = ⊥ := by
  classical
  let Z : Subgroup R := omega1Center R p
  let T : Subgroup R := Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)
  obtain ⟨Ew, hEwcard, hEwstar⟩ := hEx
  have hZcard : Nat.card Z = p := by
    dsimp [Z]
    exact (omega1Center_lt_and_card_eq_prime_of_maximalElementaryAbelian_card_prime_sq
      hpg h3 hEwcard hEwstar).2
  rcases sup_omega1Center_maximalElementaryAbelian_of_centralizer_pRank_le_two
      h3 hScard hSrank hZcard with ⟨hEcard, hEstar⟩
  let E : Subgroup R := S ⊔ Z
  have hEnot_le_T : ¬ E ≤ T := by
    dsimp [E, T]
    exact (lemma52 hp hpg h3 (S ⊔ omega1Center R p) hEcard hEstar).1
  by_contra hST_ne_bot
  have hSleT : S ≤ T := by
    dsimp [T] at hST_ne_bot ⊢
    exact le_of_inf_ne_bot_of_card_prime hScard hST_ne_bot
  have hZleT : Z ≤ T := by
    intro z hz
    dsimp [Z, T]
    exact center_le_centralizer_omega1UpperCentralTwo (omega1Center_le_center hz)
  have hEleT : E ≤ T := by
    dsimp [E]
    exact sup_le hSleT hZleT
  exact hEnot_le_T hEleT

private theorem inf_centralizer_omega1UpperCentralTwo_eq_bot_of_narrow
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) (hnarrow : IsNarrow p R)
    {S : Subgroup R} (hScard : Nat.card S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2) :
    S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) = ⊥ :=
  inf_centralizer_omega1UpperCentralTwo_eq_bot_of_exists_maximalElementaryAbelian
    hp hpg h3
    (exists_maximalElementaryAbelian_card_prime_sq_of_card_prime_centralizer_pRank_le_two
      hp hpg h3 (exists_card_prime_centralizer_pRank_le_two_of_narrow hp hpg h3 hnarrow))
    hScard hSrank

/-- **Rank-2 centralizer squeeze (general form)**: if `|S| = p`, `r(C_R(S)) ≤ 2`, and
`K ≤ C_R(S)` meets `S` trivially, then `K` is cyclic. Otherwise `K` contains an
`E_{p²}` (existence half of Lemma 4.5(a),
`S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic`); joining it with the
order-`p` factor `S` — which centralizes it — yields an elementary abelian subgroup of
order `p³` inside `C_R(S)`, contradicting `r(C_R(S)) ≤ 2`.

Instances: `C_T(S)` for Thm 5.3(d) (mmd L1865-1867) and `C_H(R₀)` for Thm 5.5
(mmd L1901-1904). -/
private theorem isCyclic_of_le_centralizer_of_inf_eq_bot_of_pRank_le_two
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    {S K : Subgroup R} (hScard : Nat.card S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2)
    (hK_le : K ≤ Subgroup.centralizer (S : Set R)) (hSK : S ⊓ K = ⊥) :
    IsCyclic ↥K := by
  classical
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  by_contra hnc
  -- `Ω₁`-level input: an `E_{p²}` inside the noncyclic `p`-group `K` (Lem 4.5(a) half).
  obtain ⟨E', hE'_elem, hE'_card⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
      (hpg.to_subgroup K) hp hnc
  -- Push `E'` down to a subgroup of `R`.
  let E : Subgroup R := E'.map K.subtype
  have hE_le_K : E ≤ K := Subgroup.map_subtype_le E'
  have hE_elem : E.IsElementaryAbelian p := hE'_elem.map K.subtype_injective
  have hE_card : Nat.card E = p ^ 2 := by
    have h := Nat.card_congr
      (Subgroup.equivMapOfInjective E' K.subtype K.subtype_injective).toEquiv
    dsimp [E]
    rw [← h]
    exact hE'_card
  have hS_elem : S.IsElementaryAbelian p := isElementaryAbelian_of_card_prime hScard
  -- `S` centralizes `E` since `E ≤ C_R(S)`.
  have hS_le_cent_E : S ≤ Subgroup.centralizer (E : Set R) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp (hK_le (hE_le_K he)) s hs).symm
  let F : Subgroup R := S ⊔ E
  have hF_elem : F.IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.sup_of_le_centralizer hS_elem hE_elem hS_le_cent_E
  have hS_le_C : S ≤ C := by
    intro s hs
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (hS_elem.comm ⟨t, ht⟩ ⟨s, hs⟩)
  have hE_le_C : E ≤ C := fun e he => hK_le (hE_le_K he)
  have hF_le_C : F ≤ C := sup_le hS_le_C hE_le_C
  have hSE_inf : S ⊓ E = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hxSK : x ∈ S ⊓ K := ⟨hx.1, hE_le_K hx.2⟩
    rwa [hSK] at hxSK
  -- Compute `p³ ≤ |F|` inside the commutative group `F`.
  have hS_le_F : S ≤ F := le_sup_left
  have hE_le_F : E ≤ F := le_sup_right
  let Ssub : Subgroup F := S.subgroupOf F
  let Esub : Subgroup F := E.subgroupOf F
  have hSsub_card : Nat.card Ssub = p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS_le_F).toEquiv).trans hScard
  have hEsub_card : Nat.card Esub = p ^ 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le_F).toEquiv).trans hE_card
  have hsub_inf : Ssub ⊓ Esub = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    change (x : R) = 1
    have hxR : (x : R) ∈ S ⊓ E := ⟨hx.1, hx.2⟩
    rwa [hSE_inf, Subgroup.mem_bot] at hxR
  letI : IsMulCommutative F := IsMulCommutative.of_comm hF_elem.comm
  haveI : Ssub.Normal := by infer_instance
  have hsup_card : Nat.card ↥(Ssub ⊔ Esub) = p * p ^ 2 := by
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card Ssub Esub
    rw [← Subgroup.normal_mul Ssub Esub, hsub_inf, Subgroup.card_bot, hSsub_card,
      hEsub_card, mul_one] at hcard
    simpa using hcard
  have hF_card_ge : p ^ 3 ≤ Nat.card F := by
    have hle : Nat.card ↥(Ssub ⊔ Esub) ≤ Nat.card (⊤ : Subgroup F) :=
      Subgroup.card_le_of_le le_top
    rw [Subgroup.card_top] at hle
    calc p ^ 3 = p * p ^ 2 := by ring
      _ = Nat.card ↥(Ssub ⊔ Esub) := hsup_card.symm
      _ ≤ Nat.card F := hle
  -- Transport into `C_R(S)` and contradict the rank bound.
  let Fsub : Subgroup C := F.subgroupOf C
  have hFsub_elem : Fsub.IsElementaryAbelian p :=
    IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hF_le_C).symm hF_elem
  have hFsub_card : Nat.card Fsub = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF_le_C).toEquiv
  have hlog_ge : 3 ≤ Nat.log p (Nat.card Fsub) := by
    rw [hFsub_card]
    exact Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt hF_card_ge
  have h3rank : 3 ≤ pRank C p := hlog_ge.trans (le_pRank Fsub hFsub_elem)
  have : (3 : ℕ) ≤ 2 := h3rank.trans hSrank
  omega

/-- **BG Theorem 5.3(d) core (cyclicity)**: `C_T(S) = C_R(S) ∩ T` is cyclic
(mmd L1865-1867); instance of the general rank-2 squeeze with `K := C_R(S) ⊓ T`. -/
private theorem isCyclic_inf_centralizer_omega1UpperCentralTwo_of_centralizer_pRank_le_two
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    {S : Subgroup R} (hScard : Nat.card S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2)
    (hST : S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) = ⊥) :
    IsCyclic ↥(Subgroup.centralizer (S : Set R) ⊓
      Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)) := by
  refine isCyclic_of_le_centralizer_of_inf_eq_bot_of_pRank_le_two hp hpg hScard hSrank
    inf_le_left ?_
  refine le_antisymm ?_ bot_le
  intro x hx
  have hxST : x ∈ S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) :=
    ⟨hx.1, hx.2.2⟩
  rwa [hST] at hxST

/-- **BG Theorem 5.3** (narrow 特徴づけ): 奇素数 `p`, 有限 `p`-群 `R`, `r(R) ≥ 3`。すると
`R` が narrow ⇔ `ℰ²(R) ∩ ℰ*(R) ≠ ∅` (位数 `p²` の elem-ab で位数 `p³` の elem-ab に含まれない
ものが存在)。

mmd L1838-1873。⇒ は narrow witness `R₀` から `r(C_R(R₀)) ≤ 2`
(`exists_card_prime_centralizer_pRank_le_two_of_narrow`) を経て `SZ ∈ ℰ²∩ℰ*` を構成
(`exists_maximalElementaryAbelian_card_prime_sq_of_card_prime_centralizer_pRank_le_two`)。
⇐ は `E = Z×S` 分解で位数 `p` の `S` (`r(C_R(S)) ≤ 2`) を取り、Thm 5.3(d) の分解
`C_R(S) = S × C_T(S)`, `C_T(S)` cyclic から narrow witness を得る。 -/
theorem narrow_iff_exists_maximalElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R) (h3 : 3 ≤ pRank R p) :
    IsNarrow p R ↔
      ∃ E : Subgroup R, Nat.card ↥E = p ^ 2 ∧ IsMaximalElementaryAbelian p E := by
  constructor
  · intro hnarrow
    exact exists_maximalElementaryAbelian_card_prime_sq_of_card_prime_centralizer_pRank_le_two
      hp hpg h3 (exists_card_prime_centralizer_pRank_le_two_of_narrow hp hpg h3 hnarrow)
  · intro hEx
    obtain ⟨S, hScard, hSrank⟩ :=
      exists_card_prime_centralizer_pRank_le_two_of_maximalElementaryAbelian_card_prime_sq
        hpg h3 hEx
    have hST : S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) = ⊥ :=
      inf_centralizer_omega1UpperCentralTwo_eq_bot_of_exists_maximalElementaryAbelian
        hp hpg h3 hEx hScard hSrank
    obtain ⟨Ew, hEwcard, hEwstar⟩ := hEx
    have hTindex : (Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)).index = p :=
      (lemma52 hp hpg h3 Ew hEwcard hEwstar).2.2
    have hdecomp :=
      centralizer_eq_sup_inf_of_card_prime_inf_bot_index_prime hScard hST hTindex
    have hcyc :=
      isCyclic_inf_centralizer_omega1UpperCentralTwo_of_centralizer_pRank_le_two
        hp hpg hScard hSrank hST
    refine Or.inr ⟨S, Subgroup.centralizer (S : Set R) ⊓
      Subgroup.centralizer (omega1UpperCentralTwo R p : Set R), hScard, hcyc, ?_, hdecomp⟩
    refine le_antisymm ?_ bot_le
    intro x hx
    have hxST : x ∈ S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) :=
      ⟨hx.1, hx.2.2⟩
    rwa [hST] at hxST

/-- **BG Theorem 5.3(d)** (narrow の centralizer 分解, 下流 App.E E.3 が cite): narrow な
有限 `p`-群 `R` (`r(R)≥3`) と位数 `p` の `S ≤ R` で `r(C_R(S)) ≤ 2` なら、`T = C_R(Ω₁(Z₂(R)))`
に対し `C_T(S)` は cyclic, `S ∩ R' = S ∩ T = 1`, かつ `C_R(S) = S × C_T(S)`。

mmd L1859-1867。`C_T(S) = C_R(S) ⊓ T`。内部直積 `C_R(S)=S×C_T(S)` は
`S ⊓ T = ⊥` と `centralizer S = S ⊔ (C_R(S)⊓T)` で表す。 -/
theorem narrow_centralizer_decomp [Finite R] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hpg : IsPGroup p R) (h3 : 3 ≤ pRank R p) (hnarrow : IsNarrow p R)
    (S : Subgroup R) (hScard : Nat.card ↥S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2) :
    IsCyclic ↥(Subgroup.centralizer (S : Set R) ⊓
        Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)) ∧
    S ⊓ commutator R = ⊥ ∧
    S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) = ⊥ ∧
    Subgroup.centralizer (S : Set R) =
      S ⊔ (Subgroup.centralizer (S : Set R) ⊓
        Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)) := by
  classical
  have hST : S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) = ⊥ :=
    inf_centralizer_omega1UpperCentralTwo_eq_bot_of_narrow hp hpg h3 hnarrow hScard hSrank
  obtain ⟨Ew, hEwcard, hEwstar⟩ :=
    exists_maximalElementaryAbelian_card_prime_sq_of_card_prime_centralizer_pRank_le_two
      hp hpg h3 (exists_card_prime_centralizer_pRank_le_two_of_narrow hp hpg h3 hnarrow)
  have hTindex : (Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)).index = p :=
    (lemma52 hp hpg h3 Ew hEwcard hEwstar).2.2
  exact ⟨isCyclic_inf_centralizer_omega1UpperCentralTwo_of_centralizer_pRank_le_two
      hp hpg hScard hSrank hST,
    inf_commutator_eq_bot_of_inf_centralizer_omega1UpperCentralTwo_eq_bot hST,
    hST,
    centralizer_eq_sup_inf_of_card_prime_inf_bot_index_prime hScard hST hTindex⟩

/-- **BG Corollary 5.4**: 奇素数 `p`, 有限 `p`-群 `R`, `r(R) ≥ 3`。すると `R` が narrow ⇔
位数 `p` の `S ≤ R` で `r(C_R(S)) ≤ 2` となるものが存在。

mmd L1875-1879。Thm 5.3 + `S↦SZ ∈ ℰ²∩ℰ*` から。 -/
theorem narrow_iff_exists_card_prime_centralizer_pRank_le_two
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R) (h3 : 3 ≤ pRank R p) :
    IsNarrow p R ↔
      ∃ S : Subgroup R, Nat.card ↥S = p ∧
        pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2 := by
  constructor
  · intro hnarrow
    exact exists_card_prime_centralizer_pRank_le_two_of_narrow hp hpg h3 hnarrow
  · intro h
    exact (narrow_iff_exists_maximalElementaryAbelian_card_prime_sq hp hpg h3).2
      (exists_maximalElementaryAbelian_card_prime_sq_of_card_prime_centralizer_pRank_le_two
        hp hpg h3 h)

/-! ## Theorem 5.5 — narrow `p`-群の solvable odd 自己同型群 (mmd L1881-1941) -/

/-- **BG Theorem 5.5(a) core (generic)**: if `A'` is a `p`-group then `A/O_p(A)` is an
abelian `p'`-group. Abelian: `A' ⊴ A` is a normal `p`-subgroup, so `A' ≤ O_p(A)`.
`p'`: an order-`p` element of the abelian quotient (Cauchy) would generate a normal
`p`-subgroup whose pullback is a normal `p`-subgroup of `A` not inside `O_p(A)`'s kernel.

Both branches of Thm 5.5 (`r(R) ≤ 2` via Lemma 4.17, `r(R) ≥ 3` via the `H_i` chain)
land here once `A'` is known to be a `p`-group. -/
private theorem quotient_opCore_comm_and_not_dvd_of_isPGroup_commutator
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (hA' : IsPGroup p (_root_.commutator A)) :
    (∀ x y : A ⧸ Ch01.opCore p A, x * y = y * x) ∧
      ¬ p ∣ Nat.card (A ⧸ Ch01.opCore p A) := by
  classical
  have hA'_le : _root_.commutator A ≤ Ch01.opCore p A :=
    Ch01.normal_pgroup_le_opCore hA'
  have hcomm : ∀ x y : A ⧸ Ch01.opCore p A, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hrw : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [hrw]
    exact hA'_le (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
      (Subgroup.mem_top _))
  refine ⟨hcomm, ?_⟩
  intro hp_dvd
  obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  have hx_ne : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx_ord
    exact (Fact.out : p.Prime).one_lt.ne' hx_ord.symm
  -- `⟨x⟩` is a normal `p`-subgroup of the abelian quotient.
  have hS_pg : IsPGroup p (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx_ord, pow_one]
  haveI hS_norm : (Subgroup.zpowers x).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hgn : g * n * g⁻¹ = n := by
      rw [hcomm g n]
      group
    rwa [hgn]
  -- Pull back along `mk'`: a normal `p`-subgroup of `A`, hence `≤ O_p(A)`.
  have hP_pg : IsPGroup p
      ((Subgroup.zpowers x).comap (QuotientGroup.mk' (Ch01.opCore p A))) := by
    refine hS_pg.comap_of_ker_isPGroup _ ?_
    rw [QuotientGroup.ker_mk']
    exact Ch01.opCore_isPGroup p A
  haveI hP_norm :
      ((Subgroup.zpowers x).comap (QuotientGroup.mk' (Ch01.opCore p A))).Normal :=
    Subgroup.Normal.comap hS_norm _
  have hP_le := Ch01.normal_pgroup_le_opCore hP_pg
  -- `x` lifts into `O_p(A)`, so it dies in the quotient: contradiction with `orderOf x = p`.
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Ch01.opCore p A) x
  have ha_mem : a ∈ (Subgroup.zpowers x).comap (QuotientGroup.mk' (Ch01.opCore p A)) := by
    rw [Subgroup.mem_comap, ha]
    exact Subgroup.mem_zpowers x
  have hx_one : x = 1 := by
    rw [← ha]
    exact (QuotientGroup.eq_one_iff a).mpr (hP_le ha_mem)
  exact hx_ne hx_one

/-- A characteristic subgroup of exponent `p` is nontrivial as a subgroup
(`exponent ⊥ = 1 ≠ p`). Shared input for the `H ∩ Z(R) ≠ 1` steps of Thm 5.5. -/
private theorem ne_bot_of_exponent_eq_prime
    {p : ℕ} [Fact p.Prime] {H : Subgroup R} (hHexp : Monoid.exponent ↥H = p) :
    H ≠ ⊥ := by
  intro hbot
  have h1 : Monoid.exponent ↥H = 1 := by
    haveI : Subsingleton ↥H := by rw [hbot]; infer_instance
    exact Monoid.exp_eq_one_of_subsingleton
  rw [hHexp] at h1
  exact (Fact.out : p.Prime).one_lt.ne' h1

/-- **BG Theorem 5.5 support (Brick A)**: under `r(R) ≥ 3`, a narrow witness `S = R₀`
(order `p`, `C_R(S) = S ⊔ K` with `K` cyclic) cannot lie inside the Thompson critical
subgroup `H` (characteristic, `⁅H,⊤⁆ ≤ Z(H)`, exponent `p`).

Otherwise `U = S ⊔ Z(H)` is a normal (via `⁅H,⊤⁆ ≤ Z(H) ≤ U`) elementary abelian
subgroup of `C_R(S)` of order `p` — forcing `S = U ⊇ H ∩ Z(R) ≠ 1`, so `S ≤ Z(R)` and
`C_R(S) = R` has rank `≥ 3` — or of order `p²` — feeding Lemma 5.1(b) and producing an
`SCN₃` element inside `C_R(S)`. Both contradict `r(C_R(S)) ≤ 2`. mmd L1893-1900. -/
private theorem not_narrow_witness_le_critical
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p)
    {S K H : Subgroup R} (hScard : Nat.card S = p) (hKcyc : IsCyclic K)
    (hSKinf : S ⊓ K = ⊥) (hCeq : Subgroup.centralizer (S : Set R) = S ⊔ K)
    (hHchar : H.Characteristic)
    (hHcomm : ⁅H, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center ↥H).map H.subtype)
    (hHexp : Monoid.exponent ↥H = p) :
    ¬ S ≤ H := by
  classical
  haveI : H.Characteristic := hHchar
  intro hSH
  have hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2 :=
    pRank_centralizer_le_two_of_narrow_witness hp hpg hScard hKcyc hSKinf hCeq
  have hS_elem : S.IsElementaryAbelian p := isElementaryAbelian_of_card_prime hScard
  -- `Z(H)` mapped into `R`, and `U = S ⊔ Z(H)`.
  set ZH : Subgroup R := (Subgroup.center ↥H).map H.subtype with hZH_def
  have hZH_le_H : ZH ≤ H := Subgroup.map_subtype_le _
  have hZH_elem : ZH.IsElementaryAbelian p := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩
      obtain ⟨x', hx'_center, rfl⟩ := hx
      obtain ⟨y', hy'_center, rfl⟩ := hy
      apply Subtype.ext
      show (x' : R) * (y' : R) = (y' : R) * (x' : R)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy'_center x')
    · rintro ⟨x, hx⟩
      apply Subtype.ext
      obtain ⟨x', _, rfl⟩ := hx
      have : x' ^ p = 1 := by
        rw [← hHexp]
        exact Monoid.pow_exponent_eq_one x'
      calc ((⟨(x' : R), _⟩ : ↥ZH) ^ p : ↥ZH).val = (x' : R) ^ p := rfl
        _ = ((x' ^ p : ↥H) : R) := rfl
        _ = 1 := by rw [this]; rfl
  have hS_le_cent_ZH : S ≤ Subgroup.centralizer (ZH : Set R) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    rintro z hz
    obtain ⟨z', hz'_center, rfl⟩ := hz
    exact (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hz'_center ⟨s, hSH hs⟩)).symm
  set U : Subgroup R := S ⊔ ZH with hU_def
  have hU_elem : U.IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.sup_of_le_centralizer hS_elem hZH_elem hS_le_cent_ZH
  have hS_le_C : S ≤ Subgroup.centralizer (S : Set R) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (hS_elem.comm ⟨t, ht⟩ ⟨s, hs⟩)
  have hZH_le_C : ZH ≤ Subgroup.centralizer (S : Set R) := by
    rintro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨z', hz'_center, rfl⟩ := hz
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hz'_center ⟨s, hSH hs⟩)
  have hU_le_C : U ≤ Subgroup.centralizer (S : Set R) := sup_le hS_le_C hZH_le_C
  -- `U ⊴ R` via `⁅U,⊤⁆ ≤ ⁅H,⊤⁆ ≤ Z(H) ≤ U`.
  have hU_le_H : U ≤ H := sup_le hSH hZH_le_H
  haveI hU_normal : U.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    rw [eq_top_iff]
    apply OddOrder.Isaacs.Ch04.le_normalizer_of_commutator_le
    calc ⁅U, (⊤ : Subgroup R)⁆ ≤ ⁅H, (⊤ : Subgroup R)⁆ :=
          Subgroup.commutator_mono hU_le_H le_rfl
      _ ≤ ZH := hHcomm
      _ ≤ U := le_sup_right
  -- `|U| = p ^ d` with `1 ≤ d ≤ 2`.
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp (hpg.to_subgroup U)
  have hd_ge : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h
    · exfalso
      rw [h0, pow_zero] at hd
      have hcard_le : Nat.card S ≤ 1 := by
        rw [← hd]
        exact Subgroup.card_le_of_le le_sup_left
      rw [hScard] at hcard_le
      have := (Fact.out : p.Prime).one_lt
      omega
    · exact h
  have hd_le : d ≤ 2 := by
    let Usub : Subgroup ↥(Subgroup.centralizer (S : Set R)) :=
      U.subgroupOf (Subgroup.centralizer (S : Set R))
    have hUsub_elem : Usub.IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hU_le_C).symm hU_elem
    have hUsub_card : Nat.card Usub = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU_le_C).toEquiv
    have hlog := (pRank_le_iff.mp hSrank) Usub hUsub_elem
    rw [hUsub_card, hd, Nat.log_pow (Fact.out : p.Prime).one_lt] at hlog
    exact hlog
  -- `H ∩ Z(R) ≠ 1` supplies a nontrivial central element of `H`.
  obtain ⟨z, hzH, hzZR, hz_ne⟩ :=
    OddOrder.GroupTheory.exists_mem_center_of_normal_ne_bot hpg (K := H)
      (ne_bot_of_exponent_eq_prime hHexp)
  have hz_ZH : z ∈ ZH := by
    have hz_center : (⟨z, hzH⟩ : ↥H) ∈ Subgroup.center ↥H := by
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext (Subgroup.mem_center_iff.mp hzZR (h : R))
    exact ⟨⟨z, hzH⟩, hz_center, rfl⟩
  interval_cases d
  -- `d = 1`: `U = S`, so `S` contains `z`, is central, and `C_R(S) = ⊤` has rank ≥ 3.
  · have hUS : S = U := by
      refine Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq ?_)
      rw [hd, pow_one, hScard]
    have hzU : z ∈ U := Subgroup.mem_sup_right hz_ZH
    have hzS : z ∈ S := by rw [hUS]; exact hzU
    have hzpow_eq : Subgroup.zpowers z = S := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzS) ?_
      have hdvd : Nat.card (Subgroup.zpowers z) ∣ Nat.card S :=
        Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hzS)
      have hne1 : Nat.card (Subgroup.zpowers z) ≠ 1 := by
        rw [Nat.card_zpowers]
        intro h1
        exact hz_ne (orderOf_eq_one_iff.mp h1)
      rw [hScard] at hdvd ⊢
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h | h
      · exact absurd h hne1
      · omega
    have hS_le_center : S ≤ Subgroup.center R := by
      rw [← hzpow_eq]
      exact Subgroup.zpowers_le.mpr hzZR
    have hCtop : Subgroup.centralizer (S : Set R) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact (Subgroup.mem_center_iff.mp (hS_le_center hs) x).symm
    let toC : R →* ↥(Subgroup.centralizer (S : Set R)) :=
      { toFun := fun r => ⟨r, by rw [hCtop]; exact trivial⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have htoC_inj : Function.Injective toC := fun x y hxy => congrArg Subtype.val hxy
    have hRrank_le : pRank R p ≤ pRank ↥(Subgroup.centralizer (S : Set R)) p :=
      pRank_le_of_injective (f := toC) htoC_inj
    omega
  -- `d = 2`: `U` is a normal `E_{p²}`, so Lemma 5.1(b) puts an `SCN₃` element in `C_R(S)`.
  · obtain ⟨A, hA_scn3, hUA⟩ :=
      mem_scn3_of_normal_isElementaryAbelian_card_prime_sq hp hpg h3 U hU_elem hd
    have hA_le_CS : A ≤ Subgroup.centralizer (S : Set R) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hsA : s ∈ A := hUA (Subgroup.mem_sup_left hs)
      haveI := hA_scn3.isSCN.isMulCommutative
      exact congrArg Subtype.val (mul_comm (⟨s, hsA⟩ : ↥A) ⟨a, ha⟩)
    have hArank_le : pRank ↥A p ≤ pRank ↥(Subgroup.centralizer (S : Set R)) p :=
      pRank_le_of_injective (f := Subgroup.inclusion hA_le_CS)
        (Subgroup.inclusion_injective hA_le_CS)
    have h3A : 3 ≤ pRank ↥A p := hA_scn3.le_pRank
    omega

/-- **BG (5.5) `|C_H(S)| = p`** (Brick B): for a narrow witness `S` not inside the
Thompson critical `H` (exponent `p`), the centralizer `C_H(S) = H ⊓ C_R(S)` has order
exactly `p`: it is cyclic of exponent `p` (rank-2 squeeze), and contains the
nontrivial `H ∩ Z(R)`. mmd L1901-1904, (5.5). -/
private theorem card_inf_critical_centralizer_eq_prime
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    {S K H : Subgroup R} (hScard : Nat.card S = p) (hKcyc : IsCyclic K)
    (hSKinf : S ⊓ K = ⊥) (hCeq : Subgroup.centralizer (S : Set R) = S ⊔ K)
    (hHchar : H.Characteristic) (hHexp : Monoid.exponent ↥H = p)
    (hSH : ¬ S ≤ H) :
    Nat.card ↥(H ⊓ Subgroup.centralizer (S : Set R)) = p := by
  classical
  haveI : H.Characteristic := hHchar
  have hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2 :=
    pRank_centralizer_le_two_of_narrow_witness hp hpg hScard hKcyc hSKinf hCeq
  have hSH_bot : S ⊓ H = ⊥ := by
    by_contra hne
    exact hSH (le_of_inf_ne_bot_of_card_prime hScard hne)
  have hScap : S ⊓ (H ⊓ Subgroup.centralizer (S : Set R)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have : x ∈ S ⊓ H := ⟨hx.1, hx.2.1⟩
    rwa [hSH_bot] at this
  have hcyc : IsCyclic ↥(H ⊓ Subgroup.centralizer (S : Set R)) :=
    isCyclic_of_le_centralizer_of_inf_eq_bot_of_pRank_le_two hp hpg hScard hSrank
      inf_le_right hScap
  -- cyclic of exponent dividing `p` ⇒ order divides `p`
  have hexp_dvd : Monoid.exponent ↥(H ⊓ Subgroup.centralizer (S : Set R)) ∣ p := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    apply Subtype.ext
    have hxH : (x : R) ∈ H := x.2.1
    have : ((⟨(x : R), hxH⟩ : ↥H) ^ p : ↥H) = 1 := by
      rw [← hHexp]
      exact Monoid.pow_exponent_eq_one _
    calc ((x ^ p : ↥(H ⊓ Subgroup.centralizer (S : Set R))) : R)
        = (x : R) ^ p := rfl
      _ = ((⟨(x : R), hxH⟩ : ↥H) ^ p : ↥H) := rfl
      _ = 1 := by rw [this]; rfl
  have hcard_dvd : Nat.card ↥(H ⊓ Subgroup.centralizer (S : Set R)) ∣ p := by
    haveI := hcyc
    calc Nat.card ↥(H ⊓ Subgroup.centralizer (S : Set R))
        = Monoid.exponent ↥(H ⊓ Subgroup.centralizer (S : Set R)) :=
          IsCyclic.exponent_eq_card.symm
      _ ∣ p := hexp_dvd
  -- the nontrivial `H ∩ Z(R)` lands in `C_H(S)`
  obtain ⟨z, hzH, hzZR, hz_ne⟩ :=
    OddOrder.GroupTheory.exists_mem_center_of_normal_ne_bot hpg (K := H)
      (ne_bot_of_exponent_eq_prime hHexp)
  have hz_mem : z ∈ H ⊓ Subgroup.centralizer (S : Set R) := by
    refine ⟨hzH, ?_⟩
    show z ∈ Subgroup.centralizer (S : Set R)
    rw [Subgroup.mem_centralizer_iff]
    intro s _
    exact Subgroup.mem_center_iff.mp hzZR s
  have hcard_ne1 : Nat.card ↥(H ⊓ Subgroup.centralizer (S : Set R)) ≠ 1 := by
    intro h1
    have hbot : H ⊓ Subgroup.centralizer (S : Set R) = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ h1
    rw [hbot, Subgroup.mem_bot] at hz_mem
    exact hz_ne hz_mem
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hcard_dvd with h | h
  · exact absurd h hcard_ne1
  · exact h

/-- **Chain factor counting (BG (5.6) step)**: if every `⁅v,·⁆`-commutator of `M` lands
in `N` and the `v`-centralizer inside `M` has order at most `m`, then `|M| ≤ |N| · m`:
the map `x ↦ ⁅v, x⁆` is constant exactly on left cosets of `C_M(v)`, hence induces an
injection `M ⧸ C_M(v) ↪ N`. mmd L1907-1913. -/
private theorem card_le_card_mul_of_commutator_mem_of_card_centralizer_le
    [Finite R] {M N : Subgroup R} {v : R} {m : ℕ}
    (hcomm : ∀ x ∈ M, ⁅v, x⁆ ∈ N)
    (hcent : Nat.card ↥(Subgroup.centralizer ({v} : Set R) ⊓ M) ≤ m) :
    Nat.card ↥M ≤ Nat.card ↥N * m := by
  classical
  set C' : Subgroup ↥M :=
    (Subgroup.centralizer ({v} : Set R) ⊓ M).subgroupOf M with hC'_def
  -- the commutator map is constant exactly on left cosets of `C'`
  have key : ∀ x y : ↥M, ⁅v, (x : R)⁆ = ⁅v, (y : R)⁆ ↔ x⁻¹ * y ∈ C' := by
    intro x y
    have hmem_iff : x⁻¹ * y ∈ C' ↔
        v * ((x : R)⁻¹ * (y : R)) = ((x : R)⁻¹ * (y : R)) * v := by
      rw [hC'_def, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have h1 : ((x⁻¹ * y : ↥M) : R) ∈ Subgroup.centralizer ({v} : Set R) := h.1
        rw [Subgroup.mem_centralizer_iff] at h1
        exact h1 v (Set.mem_singleton v)
      · intro h
        refine ⟨?_, (x⁻¹ * y).2⟩
        show ((x⁻¹ * y : ↥M) : R) ∈ Subgroup.centralizer ({v} : Set R)
        rw [Subgroup.mem_centralizer_iff]
        intro h' hh'
        rw [Set.mem_singleton_iff] at hh'
        subst hh'
        exact h
    rw [hmem_iff]
    constructor
    · intro h
      rw [commutatorElement_def, commutatorElement_def] at h
      have h2 : (x : R) * v⁻¹ * (x : R)⁻¹ = (y : R) * v⁻¹ * (y : R)⁻¹ := by
        refine mul_left_cancel (a := v) ?_
        calc v * ((x : R) * v⁻¹ * (x : R)⁻¹)
            = v * (x : R) * v⁻¹ * ((x : R))⁻¹ := by group
          _ = v * (y : R) * v⁻¹ * ((y : R))⁻¹ := h
          _ = v * ((y : R) * v⁻¹ * (y : R)⁻¹) := by group
      have h3 : v⁻¹ * ((x : R)⁻¹ * (y : R)) = ((x : R)⁻¹ * (y : R)) * v⁻¹ := by
        calc v⁻¹ * ((x : R)⁻¹ * (y : R))
            = (x : R)⁻¹ * ((x : R) * v⁻¹ * (x : R)⁻¹) * (y : R) := by group
          _ = (x : R)⁻¹ * ((y : R) * v⁻¹ * (y : R)⁻¹) * (y : R) := by rw [h2]
          _ = ((x : R)⁻¹ * (y : R)) * v⁻¹ := by group
      have h4 : Commute v⁻¹ ((x : R)⁻¹ * (y : R)) := h3
      exact (Commute.inv_left_iff.mp h4).eq
    · intro h
      have hgv : ((x : R)⁻¹ * (y : R)) * v⁻¹ = v⁻¹ * ((x : R)⁻¹ * (y : R)) := by
        calc ((x : R)⁻¹ * (y : R)) * v⁻¹
            = v⁻¹ * (v * ((x : R)⁻¹ * (y : R))) * v⁻¹ := by group
          _ = v⁻¹ * (((x : R)⁻¹ * (y : R)) * v) * v⁻¹ := by rw [h]
          _ = v⁻¹ * ((x : R)⁻¹ * (y : R)) := by group
      rw [commutatorElement_def, commutatorElement_def]
      calc v * (x : R) * v⁻¹ * ((x : R))⁻¹
          = v * (x : R) * (v⁻¹ * ((x : R)⁻¹ * (y : R)))
              * (((x : R)⁻¹ * (y : R)))⁻¹ * ((x : R))⁻¹ := by group
        _ = v * (x : R) * (((x : R)⁻¹ * (y : R)) * v⁻¹)
              * (((x : R)⁻¹ * (y : R)))⁻¹ * ((x : R))⁻¹ := by rw [hgv]
        _ = v * (y : R) * v⁻¹ * ((y : R))⁻¹ := by group
  -- the induced injection `↥M ⧸ C' ↪ ↥N`
  let F : (↥M ⧸ C') → ↥N := Quotient.lift
    (fun x : ↥M => (⟨⁅v, (x : R)⁆, hcomm _ x.2⟩ : ↥N))
    (by
      intro x y hxy
      have hmem : x⁻¹ * y ∈ C' := (QuotientGroup.leftRel_apply).mp hxy
      exact Subtype.ext ((key x y).mpr hmem))
  have hF_inj : Function.Injective F := by
    intro q₁ q₂
    refine Quotient.inductionOn₂ q₁ q₂ ?_
    intro x y h
    have hxy : ⁅v, (x : R)⁆ = ⁅v, (y : R)⁆ := congrArg Subtype.val h
    exact Quotient.sound ((QuotientGroup.leftRel_apply).mpr ((key x y).mp hxy))
  have hindex_le : C'.index ≤ Nat.card ↥N := by
    have : Nat.card (↥M ⧸ C') ≤ Nat.card ↥N := Nat.card_le_card_of_injective F hF_inj
    simpa [Subgroup.index] using this
  have hC'_card : Nat.card C' ≤ m := by
    rw [hC'_def]
    calc Nat.card ↥((Subgroup.centralizer ({v} : Set R) ⊓ M).subgroupOf M)
        = Nat.card ↥(Subgroup.centralizer ({v} : Set R) ⊓ M) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
      _ ≤ m := hcent
  calc Nat.card ↥M = C'.index * Nat.card C' := (C'.index_mul_card).symm
    _ ≤ Nat.card ↥N * m := Nat.mul_le_mul hindex_le hC'_card

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **BG Theorem 5.5, `r(R) ≥ 3` chain machinery** (mmd L1905-1917): for a narrow
witness `S` and any faithful action `φ : A →* MulAut R`, the descending chain
`H_0 = H` (Thompson critical), `H_{i+1} = ⁅H_i, R⁆` is characteristic with factors of
order dividing `p` (counting against `|C_H(S)| = p`) and reaches `⊥` (nilpotency).
Each factor has automorphism group of order dividing `p - 1`, so `A'` and every
`α^(p-1)` stabilize the chain; a `p'`-order stabilizing element acts trivially on `H`
(BG Lem 1.9, `coprime_stabilizes_chain_trivial`), lands in the `p`-group `C_A(H)`
(Thm 1.13), and is trivial. Hence `A'` is a `p`-group and every `p'`-element of `A`
has order dividing `p - 1` (= Thm 5.5(a)(b) inputs for `r(R) ≥ 3`). -/
private theorem isPGroup_commutator_and_orderOf_dvd_of_narrow_witness
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p)
    {S K : Subgroup R} (hScard : Nat.card S = p) (hKcyc : IsCyclic K)
    (hSKinf : S ⊓ K = ⊥) (hCeq : Subgroup.centralizer (S : Set R) = S ⊔ K)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hφ : Function.Injective φ) :
    IsPGroup p (_root_.commutator A) ∧
      ∀ a : A, Nat.Coprime (orderOf a) p → orderOf a ∣ (p - 1) := by
  classical
  have hprime : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hp
    norm_num at hp
  -- `R` is nontrivial since `pRank R ≥ 3`.
  haveI hRnt : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with hsub | hnt
    · exfalso
      have h0 : pRank R p ≤ 0 := by
        rw [pRank_le_iff]
        intro B hB
        have hcard1 : Nat.card ↥B = 1 := by
          have h1 : Nat.card R = 1 := by
            haveI : Unique R := ⟨⟨1⟩, fun a => Subsingleton.elim a 1⟩
            exact Nat.card_unique
          have h2 := Subgroup.card_subgroup_dvd_card B
          rw [h1] at h2
          exact Nat.dvd_one.mp h2
        rw [hcard1, Nat.log_one_right]
      omega
    · exact hnt
  -- Thompson critical subgroup.
  obtain ⟨H, hHchar, hHcommtop, hHcommcenter, hHexp, hHaut⟩ :=
    OddOrder.BG.Ch1.S01.thompson_critical_omega (p := p) hp2 hpg
  haveI : H.Characteristic := hHchar
  have hH_pg : IsPGroup p ↥H := hpg.to_subgroup H
  have hSH : ¬ S ≤ H :=
    not_narrow_witness_le_critical hp hpg h3 hScard hKcyc hSKinf hCeq hHchar
      hHcommtop hHexp
  have hCH_card : Nat.card ↥(H ⊓ Subgroup.centralizer (S : Set R)) = p :=
    card_inf_critical_centralizer_eq_prime hp hpg hScard hKcyc hSKinf hCeq hHchar
      hHexp hSH
  -- generator of `S`.
  haveI hS_nt : Nontrivial ↥S := by
    rw [← Finite.one_lt_card_iff_nontrivial, hScard]
    exact hprime.one_lt
  obtain ⟨⟨v, hvS⟩, hv_ne⟩ := exists_ne (1 : ↥S)
  have hv_ne1 : v ≠ 1 := fun h => hv_ne (Subtype.ext h)
  have hzpow_v : Subgroup.zpowers v = S := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hvS) ?_
    have hdvd : Nat.card (Subgroup.zpowers v) ∣ Nat.card S :=
      Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hvS)
    have hne1 : Nat.card (Subgroup.zpowers v) ≠ 1 := by
      rw [Nat.card_zpowers]
      intro h1
      exact hv_ne1 (orderOf_eq_one_iff.mp h1)
    rw [hScard] at hdvd ⊢
    rcases (Nat.dvd_prime hprime).mp hdvd with h | h
    · exact absurd h hne1
    · omega
  -- the `v`-centralizer inside `H` sits in `C_H(S)`.
  have hCv_le : ∀ {M : Subgroup R}, M ≤ H →
      Subgroup.centralizer ({v} : Set R) ⊓ M ≤
        H ⊓ Subgroup.centralizer (S : Set R) := by
    intro M hMH x hx
    refine ⟨hMH hx.2, ?_⟩
    show x ∈ Subgroup.centralizer (S : Set R)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [← hzpow_v] at hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    have hxv : Commute v x := by
      have h1 : x ∈ Subgroup.centralizer ({v} : Set R) := hx.1
      rw [Subgroup.mem_centralizer_iff] at h1
      exact h1 v (Set.mem_singleton v)
    exact (hxv.zpow_left k).eq
  -- the descending characteristic chain `s 0 = H`, `s (i+1) = ⁅s i, R⁆`.
  set s : ℕ → Subgroup R := fun i => (fun B => ⁅B, (⊤ : Subgroup R)⁆)^[i] H with hs_def
  have hs0 : s 0 = H := rfl
  have hs_succ : ∀ i, s (i + 1) = ⁅s i, (⊤ : Subgroup R)⁆ := by
    intro i
    rw [hs_def]
    exact Function.iterate_succ_apply' _ i H
  have hchar : ∀ i, (s i).Characteristic := by
    intro i
    induction i with
    | zero => exact hHchar
    | succ i ih =>
      rw [hs_succ]
      haveI := ih
      infer_instance
  have hnormal : ∀ i, (s i).Normal := fun i => by haveI := hchar i; infer_instance
  have hs_step : ∀ i, s (i + 1) ≤ s i := by
    intro i
    rw [hs_succ, Subgroup.commutator_comm]
    haveI := hnormal i
    exact Subgroup.commutator_le_right ⊤ (s i)
  have hs_le_H : ∀ i, s i ≤ H := by
    intro i
    induction i with
    | zero => exact le_of_eq hs0
    | succ i ih => exact (hs_step i).trans ih
  have hanti : Antitone s := antitone_nat_of_succ_le hs_step
  obtain ⟨n, hn⟩ : ∃ n, lowerCentralSeries R n = ⊥ := by
    haveI := hpg.isNilpotent
    exact nilpotent_iff_lowerCentralSeries.mp inferInstance
  have hsn : s n = ⊥ := by
    have hLCS : ∀ i, s i ≤ lowerCentralSeries R i := by
      intro i
      induction i with
      | zero =>
        rw [lowerCentralSeries_zero]
        exact le_top
      | succ i ih =>
        rw [hs_succ, lowerCentralSeries_succ]
        exact Subgroup.commutator_mono ih le_rfl
    exact le_bot_iff.mp (hn ▸ hLCS n)
  -- factor bound `|s i| ≤ |s (i+1)| · p`.
  have hfactor : ∀ i, Nat.card ↥(s i) ≤ Nat.card ↥(s (i + 1)) * p := by
    intro i
    refine card_le_card_mul_of_commutator_mem_of_card_centralizer_le (v := v) ?_ ?_
    · intro x hx
      rw [hs_succ, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top v) hx
    · calc Nat.card ↥(Subgroup.centralizer ({v} : Set R) ⊓ s i)
          ≤ Nat.card ↥(H ⊓ Subgroup.centralizer (S : Set R)) :=
            Subgroup.card_le_of_le (hCv_le (hs_le_H i))
        _ = p := hCH_card
  -- factor cards divide `p`.
  have hQcard : ∀ i, Nat.card (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) ∣ p := by
    intro i
    haveI : ((s (i + 1)).subgroupOf (s i)).Normal :=
      (hnormal (i + 1)).subgroupOf (s i)
    have hmul : Nat.card (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) *
        Nat.card ((s (i + 1)).subgroupOf (s i)) = Nat.card ↥(s i) := by
      have := ((s (i + 1)).subgroupOf (s i)).index_mul_card
      simpa [Subgroup.index] using this
    have hN'card : Nat.card ((s (i + 1)).subgroupOf (s i)) = Nat.card ↥(s (i + 1)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hs_step i)).toEquiv
    have hQ_le : Nat.card (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) ≤ p := by
      have h1 : Nat.card (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) *
          Nat.card ((s (i + 1)).subgroupOf (s i)) ≤
          p * Nat.card ((s (i + 1)).subgroupOf (s i)) := by
        calc Nat.card (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) *
            Nat.card ((s (i + 1)).subgroupOf (s i)) = Nat.card ↥(s i) := hmul
          _ ≤ Nat.card ↥(s (i + 1)) * p := hfactor i
          _ = p * Nat.card ((s (i + 1)).subgroupOf (s i)) := by
              rw [hN'card]; ring
      exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos
    obtain ⟨e, he⟩ :=
      IsPGroup.iff_card.mp
        ((hpg.to_subgroup (s i)).to_quotient ((s (i + 1)).subgroupOf (s i)))
    rw [he] at hQ_le ⊢
    have he_le : e ≤ 1 := by
      have h2 : p ^ e ≤ p ^ 1 := by
        rw [pow_one]
        exact hQ_le
      exact (Nat.pow_le_pow_iff_right hprime.one_lt).mp h2
    calc p ^ e ∣ p ^ 1 := pow_dvd_pow p he_le
      _ = p := pow_one p
  -- `A` acts on each `s i` and on each factor.
  have hsi_inv : ∀ i, OddOrder.Isaacs.Ch03.IsAInvariant φ (s i) := fun i => by
    haveI := hchar i
    exact OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ
  set ψs : (i : ℕ) → A →* MulAut ↥(s i) := fun i =>
    OddOrder.BG.Ch1.S01.restrictAction (hsi_inv i) with hψs_def
  have hNi_inv : ∀ i, OddOrder.Isaacs.Ch03.IsAInvariant (ψs i)
      ((s (i + 1)).subgroupOf (s i)) := by
    intro i
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a g hg
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    have hval : (((ψs i) a g : ↥(s i)) : R) = φ a (g : R) := by
      rw [hψs_def]
      rfl
    rw [hval]
    exact (hsi_inv (i + 1)).smul_mem a hg
  set ψQ : (i : ℕ) → A →* MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) := fun i =>
    letI := (hnormal (i + 1)).subgroupOf (s i)
    quotientMulAutHom (hNi_inv i) with hψQ_def
  -- the chain stabilizer.
  set Stab : Subgroup A := ⨅ i, (ψQ i).ker with hStab_def
  have hStab_mem : ∀ a : A, a ∈ Stab ↔ ∀ i, (ψQ i) a = 1 := by
    intro a
    rw [hStab_def]
    simp [Subgroup.mem_iInf, MonoidHom.mem_ker]
  -- each factor automorphism group has order dividing `p - 1`.
  have hMulAutQ : ∀ i,
      Nat.card (MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))) ∣ (p - 1) := by
    intro i
    haveI : ((s (i + 1)).subgroupOf (s i)).Normal :=
      (hnormal (i + 1)).subgroupOf (s i)
    rcases (Nat.dvd_prime hprime).mp (hQcard i) with h1 | hp'
    · haveI : Subsingleton (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) :=
        ((Nat.card_eq_one_iff_unique).mp h1).1
      haveI : Subsingleton (MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))) :=
        ⟨fun f g => by ext x; exact Subsingleton.elim _ _⟩
      have hone : Nat.card (MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))) = 1 := by
        haveI : Unique (MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))) :=
          ⟨⟨1⟩, fun a => Subsingleton.elim a 1⟩
        exact Nat.card_unique
      rw [hone]
      exact one_dvd _
    · haveI : IsCyclic (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) :=
        isCyclic_of_prime_card hp'
      rw [IsCyclic.card_mulAut, hp', Nat.totient_prime hprime]
  -- `A'` and all `α^(p-1)` stabilize the chain.
  have hcomm_mem_Stab : _root_.commutator A ≤ Stab := by
    rw [_root_.commutator, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [hStab_mem]
    intro i
    haveI : ((s (i + 1)).subgroupOf (s i)).Normal :=
      (hnormal (i + 1)).subgroupOf (s i)
    rcases (Nat.dvd_prime hprime).mp (hQcard i) with h1 | hp'
    · haveI : Subsingleton (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) :=
        ((Nat.card_eq_one_iff_unique).mp h1).1
      haveI : Subsingleton (MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))) :=
        ⟨fun f g => by ext x; exact Subsingleton.elim _ _⟩
      exact Subsingleton.elim _ _
    · haveI : IsCyclic (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) :=
        isCyclic_of_prime_card hp'
      let e := IsCyclic.mulAutMulEquiv (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))
      letI : CommGroup (MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))) :=
        e.toMonoidHom.commGroupOfInjective e.injective
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)
  have hpow_mem_Stab : ∀ α : A, α ^ (p - 1) ∈ Stab := by
    intro α
    rw [hStab_mem]
    intro i
    haveI : ((s (i + 1)).subgroupOf (s i)).Normal :=
      (hnormal (i + 1)).subgroupOf (s i)
    rw [map_pow]
    have hdvd : orderOf ((ψQ i) α) ∣ p - 1 :=
      dvd_trans (orderOf_dvd_natCard _) (hMulAutQ i)
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  -- a `p'`-order chain stabilizer is trivial.
  have hStab_p' : ∀ b ∈ Stab, Nat.Coprime (orderOf b) p → b = 1 := by
    intro b hb hbcop
    set ψB : ↥(Subgroup.zpowers b) →* MulAut ↥H :=
      (ψs 0).comp (Subgroup.zpowers b).subtype with hψB_def
    have htriv_chain : ∀ a' : ↥(Subgroup.zpowers b), ψB a' = 1 := by
      refine OddOrder.BG.Ch1.S01.coprime_stabilizes_chain_trivial ψB ?_ (Or.inr ?_)
        (fun i => (s i).subgroupOf H) ?_ ?_ (n := n) ?_ ?_ ?_ ?_
      · rw [Nat.card_zpowers]
        obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hH_pg
        rw [hj]
        exact Nat.Coprime.pow_right j hbcop
      · haveI := hH_pg.isNilpotent
        infer_instance
      · intro i j hij
        exact Subgroup.comap_mono (hanti hij)
      · exact Subgroup.subgroupOf_self H
      · show (s n).subgroupOf H = ⊥
        rw [hsn]
        exact Subgroup.bot_subgroupOf H
      · intro i
        exact (hnormal i).subgroupOf H
      · intro i
        rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
        intro a' g hg
        rw [Subgroup.mem_subgroupOf] at hg ⊢
        have hval : (((ψB a') g : ↥H) : R) = φ (a' : A) (g : R) := by
          rw [hψB_def, hψs_def]
          rfl
        rw [hval]
        exact (hsi_inv i).smul_mem _ hg
      · intro i a' x hx
        haveI : ((s (i + 1)).subgroupOf (s i)).Normal :=
      (hnormal (i + 1)).subgroupOf (s i)
        rw [Subgroup.mem_subgroupOf] at hx
        obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp a'.2
        have hker : (ψQ i) (a' : A) = 1 := by
          rw [← hz, map_zpow]
          have h1 : (ψQ i) b = 1 := (hStab_mem b).mp hb i
          rw [h1, one_zpow]
        rw [hψQ_def] at hker
        have hker_app := congrArg
          (fun e : MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) =>
            e ((⟨(x : R), hx⟩ : ↥(s i)) : ↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))) hker
        simp only [MulAut.one_apply] at hker_app
        have hmem : (⟨(x : R), hx⟩ : ↥(s i))⁻¹ *
            (ψs i (a' : A)) ⟨(x : R), hx⟩ ∈ (s (i + 1)).subgroupOf (s i) := by
          rw [← QuotientGroup.eq]
          exact hker_app.symm
        rw [Subgroup.mem_subgroupOf] at hmem
        refine ⟨x⁻¹ * (ψB a') x, ?_, by group⟩
        rw [Subgroup.mem_subgroupOf]
        have hval : ((x⁻¹ * (ψB a') x : ↥H) : R) =
            (((⟨(x : R), hx⟩ : ↥(s i))⁻¹ *
              (ψs i (a' : A)) ⟨(x : R), hx⟩ : ↥(s i)) : R) := by
          rw [hψB_def, hψs_def]
          rfl
        show ((x⁻¹ * (ψB a') x : ↥H) : R) ∈ s (i + 1)
        rw [hval]
        exact hmem
    have hbH : (ψs 0) b = 1 := by
      have h := htriv_chain ⟨b, Subgroup.mem_zpowers b⟩
      rw [hψB_def] at h
      exact h
    have hker_le : (ψs 0).ker ≤ (autCentralizer H).comap φ := by
      intro a ha
      rw [Subgroup.mem_comap, mem_autCentralizer]
      intro h hh
      have happ := congrArg (fun e : MulAut ↥H => ((e ⟨h, hh⟩ : ↥H) : R)) ha
      calc φ a h = (((ψs 0) a ⟨h, hh⟩ : ↥H) : R) := rfl
        _ = (((1 : MulAut ↥H) ⟨h, hh⟩ : ↥H) : R) := happ
        _ = h := rfl
    have hker_pg : IsPGroup p (ψs 0).ker :=
      (hHaut.comap_of_injective φ hφ).to_le hker_le
    obtain ⟨j, hj⟩ := hker_pg ⟨b, hbH⟩
    have hj' : b ^ p ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right j hbcop) dvd_rfl
      (orderOf_dvd_of_pow_eq_one hj')
  -- conclusions.
  constructor
  · intro g
    have hn_pos : 0 < orderOf (g : A) := orderOf_pos _
    obtain ⟨k, m, hpm, hmn⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd hn_pos.ne' p hprime.ne_one
    have hm_cop : Nat.Coprime p m := hprime.coprime_iff_not_dvd.mpr hpm
    have ha'_pow_m : ((g : A) ^ p ^ k) ^ m = 1 := by
      rw [← pow_mul, ← hmn, pow_orderOf_eq_one]
    have ha'_mem : (g : A) ^ p ^ k ∈ Stab :=
      hcomm_mem_Stab ((_root_.commutator A).pow_mem g.2 _)
    have ha'_cop : Nat.Coprime (orderOf ((g : A) ^ p ^ k)) p :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one ha'_pow_m) hm_cop.symm
    have ha'_one : (g : A) ^ p ^ k = 1 := hStab_p' _ ha'_mem ha'_cop
    exact ⟨k, Subtype.ext (by simpa using ha'_one)⟩
  · intro α hα_cop
    have hα_mem : α ^ (p - 1) ∈ Stab := hpow_mem_Stab α
    have hα_pow_dvd : orderOf (α ^ (p - 1)) ∣ orderOf α := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    have hα_pow_cop : Nat.Coprime (orderOf (α ^ (p - 1))) p :=
      Nat.Coprime.coprime_dvd_left hα_pow_dvd hα_cop
    exact orderOf_dvd_of_pow_eq_one (hStab_p' _ hα_mem hα_pow_cop)

open scoped Pointwise in
open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **BG Theorem 5.5(c)** (`r(R) ≤ 2` assembly, mmd L1919-1941): if `|A| = q` is a
prime not dividing `p(p-1)`, then `q ∣ (p+1)/2` (Lemma 4.14 under `SCN₃(R) = ∅`);
if moreover `R = [R,A]` and `R` is nonabelian, then `|R| = p³`: Thm 4.16 (Blackburn)
gives the central product `R = R₁ ∘ R₂` with `Ω₁(R) = R₁` of order `p³` and `R/Ω₁(R)`
cyclic; `A` centralizes `R/Ω₁(R)` since `|Aut(C_{p^t})| = p^{t-1}(p-1)` is prime to
`q` (the **G** Thm 5.4.1 step via `Nat.totient_prime_pow`), so
`R = [R,A] ≤ Ω₁(R) = R₁`. -/
private theorem thm55c_of_pRank_le_two
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (hrank : pRank R p ≤ 2)
    {A : Type*} [Group A] [Finite A] (φ : A →* MulAut R)
    (hφ : Function.Injective φ) (hAodd : Odd (Nat.card A))
    (hq_prime : (Nat.card A).Prime) (hq_ndvd : ¬ Nat.card A ∣ p * (p - 1)) :
    Nat.card A ∣ (p + 1) / 2 ∧
      (OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤ →
        (¬ ∀ x y : R, x * y = y * x) → Nat.card R = p ^ 3) := by
  classical
  have hprime : p.Prime := Fact.out
  have hq_ne_p : Nat.card A ≠ p := by
    intro h
    exact hq_ndvd (h ▸ dvd_mul_right p (p - 1))
  have hSCN : ∀ B : Subgroup R, ¬ OddOrder.GroupTheory.IsSCN₃ p B := by
    intro B hB
    have h3 : 3 ≤ pRank ↥B p := hB.le_pRank
    have hle : pRank ↥B p ≤ pRank R p :=
      pRank_le_of_injective (f := B.subtype) B.subtype_injective
    omega
  have hq_dvd_aut : Nat.card A ∣ Nat.card (MulAut R) := by
    have h1 : Nat.card A = Nat.card φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
    rw [h1]
    exact Subgroup.card_subgroup_dvd_card φ.range
  have h2dvd : (2 : ℕ) ∣ p - 1 := by
    obtain ⟨t, ht⟩ := hp
    exact ⟨t, by omega⟩
  constructor
  · rcases OddOrder.BG.Ch1.S04.dvd_half_prime_add_or_sub_of_prime_dvd_aut_of_scn3_empty
      hp hpg hSCN hq_prime hq_ne_p hq_dvd_aut with h | h
    · exact h
    · exfalso
      have hq_dvd_pm1 : Nat.card A ∣ p - 1 :=
        dvd_trans h ⟨2, (Nat.div_mul_cancel h2dvd).symm⟩
      exact hq_ndvd (Dvd.dvd.mul_left hq_dvd_pm1 p)
  · intro hRA hnab
    haveI : Nontrivial R := by
      rcases subsingleton_or_nontrivial R with hs | hn
      · exact absurd (fun x y => Subsingleton.elim _ _) hnab
      · exact hn
    have hcop : Nat.Coprime (Nat.card A) (Nat.card R) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
      rw [hn]
      exact Nat.Coprime.pow_right n
        ((Nat.coprime_primes hq_prime hprime).mpr hq_ne_p)
    obtain ⟨hp3, hcase⟩ :=
      OddOrder.BG.Ch1.S04.blackburnRankTwoClassification hp hpg hcop hrank hRA hAodd
    rcases hcase with hcomm | hcp
    · exfalso
      haveI := hcomm
      exact hnab fun x y => mul_comm x y
    · obtain ⟨R₁, R₂, hcp', hR₁nab, hR₁card, hR₁exp, hR₂cyc, hΩeq⟩ := hcp
      -- `R₁ ⊴ R` (it is centralized by `R₂` and normalized by itself).
      haveI hR₁_normal : R₁.Normal := by
        rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
        rw [hcp'.sup_eq]
        refine sup_le Subgroup.le_normalizer ?_
        intro g hg
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          have hc : Commute x g := hcp'.commute_of_mem hx hg
          have hfix : g * x * g⁻¹ = x := by
            calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [← hc.eq]
              _ = x := by group
          rw [hfix]
          exact hx
        · intro hx
          have hc : Commute (g * x * g⁻¹) g := hcp'.commute_of_mem hx hg
          have hfix : x = g * x * g⁻¹ := by
            calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
              _ = g⁻¹ * ((g * x * g⁻¹) * g) := by group
              _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [hc.eq]
              _ = g * x * g⁻¹ := by group
          rw [hfix]
          exact hx
      -- element decomposition along the central product.
      have hdecomp : ∀ x : R, ∃ u ∈ R₁, ∃ v ∈ R₂, x = u * v := by
        intro x
        have hx : x ∈ R₁ ⊔ R₂ := by
          rw [← hcp'.sup_eq]
          exact Subgroup.mem_top x
        have hx' : x ∈ (R₁ : Set R) * (R₂ : Set R) := by
          rw [← Subgroup.normal_mul]
          exact hx
        obtain ⟨u, hu, v, hv, huv⟩ := hx'
        exact ⟨u, hu, v, hv, huv.symm⟩
      -- `Ω₁(R) = R₁`.
      have hΩR : Omega R p 1 = R₁ := by
        apply le_antisymm
        · rw [Omega]
          refine (Subgroup.closure_le _).mpr ?_
          rintro x hx
          rw [Set.mem_setOf_eq, pow_one] at hx
          obtain ⟨u, hu, v, hv, huv⟩ := hdecomp x
          subst huv
          have hcomm_uv : Commute u v := hcp'.commute_of_mem hu hv
          have hup : u ^ p = 1 := by
            have h1 := Monoid.pow_exponent_eq_one (⟨u, hu⟩ : ↥R₁)
            rw [hR₁exp] at h1
            exact congrArg Subtype.val h1
          have hvp : v ^ p = 1 := by
            have hxp : (u * v) ^ p = u ^ p * v ^ p := hcomm_uv.mul_pow p
            have h1 : u ^ p * v ^ p = 1 := by
              rw [← hxp]
              exact hx
            rw [hup, one_mul] at h1
            exact h1
          have hv_mem : v ∈ (Omega ↥R₂ p 1).map R₂.subtype := by
            refine ⟨⟨v, hv⟩, ?_, rfl⟩
            apply Omega.mem_of_pow_eq_one
            apply Subtype.ext
            show v ^ p ^ 1 = 1
            rw [pow_one]
            exact hvp
          rw [hΩeq] at hv_mem
          exact R₁.mul_mem hu (Subgroup.map_subtype_le _ hv_mem)
        · intro x hx
          apply Omega.mem_of_pow_eq_one
          rw [pow_one]
          have h1 := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : ↥R₁)
          rw [hR₁exp] at h1
          exact congrArg Subtype.val h1
      -- the quotient `R ⧸ Ω₁(R)` is cyclic (image of `R₂`).
      haveI : (Omega R p 1).Normal := inferInstance
      have hΩ_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ (Omega R p 1) :=
        OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ
      haveI hQcyc : IsCyclic (R ⧸ Omega R p 1) := by
        apply isCyclic_of_surjective
          ((QuotientGroup.mk' (Omega R p 1)).comp R₂.subtype)
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
        obtain ⟨u, hu, v, hv, huv⟩ := hdecomp x
        refine ⟨⟨v, hv⟩, ?_⟩
        show ((v : R) : R ⧸ Omega R p 1) = ((x : R) : R ⧸ Omega R p 1)
        rw [QuotientGroup.eq, hΩR]
        have hcomm_uv : Commute u v := hcp'.commute_of_mem hu hv
        have hval : v⁻¹ * x = u := by
          rw [huv, hcomm_uv.eq]
          group
        rw [hval]
        exact hu
      -- `A` centralizes the cyclic `p`-group `R ⧸ Ω₁(R)`.
      have hψQ_triv : ∀ a : A, quotientMulAutHom hΩ_inv a = 1 := by
        intro a
        rcases eq_or_ne (quotientMulAutHom hΩ_inv a) 1 with h | hne
        · exact h
        · exfalso
          have ho_dvd_q : orderOf (quotientMulAutHom hΩ_inv a) ∣ Nat.card A :=
            dvd_trans (orderOf_map_dvd _ a) (orderOf_dvd_natCard a)
          have ho_dvd_aut : orderOf (quotientMulAutHom hΩ_inv a) ∣
              Nat.card (MulAut (R ⧸ Omega R p 1)) := orderOf_dvd_natCard _
          rcases (Nat.dvd_prime hq_prime).mp ho_dvd_q with h1 | hq
          · exact hne (orderOf_eq_one_iff.mp h1)
          · rw [hq] at ho_dvd_aut
            obtain ⟨t, ht⟩ := IsPGroup.iff_card.mp (hpg.to_quotient (Omega R p 1))
            rw [IsCyclic.card_mulAut, ht] at ho_dvd_aut
            rcases Nat.eq_zero_or_pos t with ht0 | htpos
            · rw [ht0, pow_zero, Nat.totient_one] at ho_dvd_aut
              exact hq_prime.one_lt.ne' (Nat.dvd_one.mp ho_dvd_aut)
            · rw [Nat.totient_prime_pow hprime htpos] at ho_dvd_aut
              rcases (Nat.Prime.dvd_mul hq_prime).mp ho_dvd_aut with h | h
              · have hqp : Nat.card A ∣ p := hq_prime.dvd_of_dvd_pow h
                rcases (Nat.dvd_prime hprime).mp hqp with h1 | h1
                · exact hq_prime.one_lt.ne' h1
                · exact hq_ne_p h1
              · exact hq_ndvd (Dvd.dvd.mul_left h p)
      -- `[R,A] ≤ Ω₁(R)`, but `[R,A] = R`.
      have hAC_le : OddOrder.Isaacs.Ch04.actionCommutator φ ≤ Omega R p 1 := by
        have hψ_one : quotientMulAutHom hΩ_inv = 1 :=
          MonoidHom.ext fun a => hψQ_triv a
        have hmap : (OddOrder.Isaacs.Ch04.actionCommutator φ).map
            (QuotientGroup.mk' (Omega R p 1)) = ⊥ := by
          rw [← OddOrder.Isaacs.Ch04.actionCommutator_quotient_eq_map hΩ_inv, hψ_one]
          exact OddOrder.Isaacs.Ch04.actionCommutator_one_eq_bot
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
        exact hmap
      rw [hRA] at hAC_le
      have hΩtop : R₁ = ⊤ := by
        rw [← hΩR]
        exact le_antisymm le_top hAC_le
      calc Nat.card R = Nat.card ↥(⊤ : Subgroup R) := Subgroup.card_top.symm
        _ = Nat.card ↥R₁ := by rw [hΩtop]
        _ = p ^ 3 := hR₁card

/-- **BG Theorem 5.5**: 奇素数 `p`, narrow な有限 `p`-群 `R`, `A` を `R` の自己同型群の solvable
odd 位数部分群 (`φ : A →* MulAut R` faithful, `[IsSolvable A]`, `Odd |A|`) とする。すると:

* (a) `A/O_p(A)` は abelian な `p'`-群,
* (b) `r(R) ≥ 3` なら `A` の各 `p'`-元の位数は `p-1` を割る,
* (c) `|A|` が `p(p-1)` を割らない素数なら `|A| ∣ (p+1)/2`; さらに `R=[R,A]` かつ `R` 非可換なら
  `|R| = p³`。

mmd L1887-1941。Thm 1.13 (critical Ω) + Lem 1.9 (stability) + (rank≤2 で) Lem 4.17/4.14/Thm 4.16
+ **G** Thm 5.4.1。§5 で最も重い結果。 -/
theorem solvableAut_of_narrow [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (hnarrow : IsNarrow p R) {A : Type*} [Group A] [Finite A] (φ : A →* MulAut R)
    (hφ : Function.Injective φ) [IsSolvable A] (hAodd : Odd (Nat.card A)) :
    (∀ x y : A ⧸ Ch01.opCore p A, x * y = y * x) ∧
      ¬ p ∣ Nat.card (A ⧸ Ch01.opCore p A) ∧
    (3 ≤ pRank R p → ∀ a : A, Nat.Coprime (orderOf a) p → orderOf a ∣ (p - 1)) ∧
    ((Nat.card A).Prime → ¬ Nat.card A ∣ p * (p - 1) →
      Nat.card A ∣ (p + 1) / 2 ∧
        (Ch04.actionCommutator φ = ⊤ → (¬ ∀ x y : R, x * y = y * x) → Nat.card R = p ^ 3)) := by
  classical
  by_cases hrank : pRank R p ≤ 2
  · -- `r(R) ≤ 2`: `A'` is a `p`-group by Lemma 4.17; (b) is vacuous; (c) by assembly.
    have hA' : IsPGroup p (_root_.commutator A) :=
      OddOrder.BG.Ch1.S04.isPGroup_commutator_of_mulAut_odd_of_pRank_le_two hp hpg
        hrank hφ hAodd
    obtain ⟨hcomm, hndvd⟩ := quotient_opCore_comm_and_not_dvd_of_isPGroup_commutator hA'
    refine ⟨hcomm, hndvd, ?_, ?_⟩
    · intro h3
      exfalso
      omega
    · intro hq hndvd'
      exact thm55c_of_pRank_le_two hp hpg hrank φ hφ hAodd hq hndvd'
  · -- `r(R) ≥ 3`: chain machinery; the hypotheses of (c) cannot occur.
    have h3 : 3 ≤ pRank R p := by omega
    obtain ⟨S, K, hScard, hKcyc, hSKinf, hCeq⟩ :=
      exists_narrow_witness_of_three_le_pRank h3 hnarrow
    obtain ⟨hA', hb⟩ := isPGroup_commutator_and_orderOf_dvd_of_narrow_witness hp hpg h3
      hScard hKcyc hSKinf hCeq hφ
    obtain ⟨hcomm, hndvd⟩ := quotient_opCore_comm_and_not_dvd_of_isPGroup_commutator hA'
    refine ⟨hcomm, hndvd, fun _ => hb, ?_⟩
    intro hq hndvd'
    exfalso
    have hq_ne_p : Nat.card A ≠ p := by
      intro h
      exact hndvd' (h ▸ dvd_mul_right p (p - 1))
    haveI : Fact (Nat.card A).Prime := ⟨hq⟩
    obtain ⟨α, hα⟩ := exists_prime_orderOf_dvd_card' (Nat.card A) dvd_rfl
    have hα_cop : Nat.Coprime (orderOf α) p := by
      rw [hα]
      exact (Nat.coprime_primes hq (Fact.out : p.Prime)).mpr hq_ne_p
    have hα_dvd := hb α hα_cop
    rw [hα] at hα_dvd
    exact hndvd' (Dvd.dvd.mul_left hα_dvd p)

/-! ## Theorem 5.6 / 5.7 — solvable group での narrow Sylow (mmd L1945-1967) -/

section Thm56

variable {G : Type*} [Group G] [Finite G]

/-- **Sylow-rank 橋**: `r_p(G) ≤ r(S)` (`S : Sylow p G`)。任意の elementary abelian
`p`-部分群はある Sylow `Q` に含まれ (`IsPGroup.exists_le_sylow`)、Sylow 同士は共役
(`Sylow.equiv`) なので rank は `S` 内で実現される。逆向き `r(S) ≤ r_p(G)` は
`pRank_le_of_injective` で自明なので実は等号だが、Thm 5.6 では `≤` だけ使う。
`PRank.lean` への昇格候補。 -/
theorem pRank_le_pRank_sylow {p : ℕ} [Fact p.Prime] (S : Sylow p G) :
    pRank G p ≤ pRank ↥(S : Subgroup G) p := by
  classical
  rw [pRank_le_iff]
  intro E hE
  have hE_pg : IsPGroup p ↥E := fun x => ⟨1, by rw [pow_one]; exact hE.pow_eq_one x⟩
  obtain ⟨Q, hQle⟩ := hE_pg.exists_le_sylow
  have h1 : Nat.log p (Nat.card ↥E) ≤ pRank ↥(Q : Subgroup G) p := by
    have hsub : (E.subgroupOf (Q : Subgroup G)).IsElementaryAbelian p :=
      OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hQle).symm hE
    have hcard : Nat.card ↥(E.subgroupOf (Q : Subgroup G)) = Nat.card ↥E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv
    rw [← hcard]
    exact le_pRank _ hsub
  refine le_trans h1 (pRank_le_of_injective (f := (Sylow.equiv Q S).toMonoidHom) ?_)
  exact (Sylow.equiv Q S).injective

/-- **Thm 5.6 narrow core** (`O_{p'}(G) = 1`, `r(S) ≥ 3` の場合): `G' ≤ O_p(G)` と
最大素因子評価。`p`-length one から `p ∤ |G/O_p(G)|` なので `R = O_p(G)` が唯一の
Sylow `p`-部分群、ゆえに `S = R` で `R` は narrow of rank ≥ 3。Hall–Higman 1.2.3 で
`C := C_G(R) ≤ R`; **Thm 5.5(a)** で `(G/C)/O_p(G/C)` が abelian、すなわち `(G/C)'` が
`p`-群 (Thm 4.18 core での Lemma 4.17 の代替) → `G' ≤ O_p(G)`; **Thm 5.5(b)** で
`q ≠ p` 素因子は `q ∣ p - 1 < p` (Lemma 4.13 の代替)。組み立ては `core418` と同型。 -/
private theorem core56 {p : ℕ} [Fact p.Prime] [IsSolvable G]
    (hp : Odd p) (hodd : Odd (Nat.card G)) (S : Sylow p G)
    (hSnarrow : IsNarrow p ↥S) (h3 : 3 ≤ pRank ↥(S : Subgroup G) p)
    (hredu : Ch03.oPiCore {r : ℕ | r ≠ p} G = ⊥)
    (hpOp : ¬ p ∣ Nat.card (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G)) :
    _root_.commutator G ≤ Ch03.oPiCore ({p} : Set ℕ) G ∧
      ∀ q ∈ (Nat.card G).primeFactors, q ≤ p := by
  classical
  have hprime : p.Prime := Fact.out
  set R : Subgroup G := Ch03.oPiCore ({p} : Set ℕ) G with hR_def
  haveI hR_normal : R.Normal := by rw [hR_def]; infer_instance
  have hR_pg : IsPGroup p ↥R :=
    S04.isPGroup_of_isPiGroup_singleton (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))
  -- `R` is a normal Sylow `p`-subgroup (`p ∤ |G/R|`), hence the unique one: `S = R`
  have hR_idx : ¬ p ∣ R.index := by
    simpa [Subgroup.index] using hpOp
  have hSR : (S : Subgroup G) = R := by
    have hnorm : ((hR_pg.toSylow hR_idx) : Subgroup G).Normal := by
      rw [hR_pg.toSylow_coe hR_idx]
      exact hR_normal
    haveI := Sylow.unique_of_normal (hR_pg.toSylow hR_idx) hnorm
    have h1 : S = hR_pg.toSylow hR_idx := Subsingleton.elim _ _
    rw [h1]
    exact hR_pg.toSylow_coe hR_idx
  -- transport narrowness and rank from `S` to `R`
  have eSR : ↥(S : Subgroup G) ≃* ↥R := MulEquiv.subgroupCongr hSR
  have hR_narrow : IsNarrow p ↥R := IsNarrow.of_mulEquiv eSR hSnarrow
  have hR_rank3 : 3 ≤ pRank ↥R p :=
    le_trans h3 (pRank_le_of_injective (f := eSR.toMonoidHom) eSR.injective)
  -- Hall–Higman 1.2.3: `C := C_G(R) ≤ R`
  have hCR : Subgroup.centralizer (R : Set G) ≤ R := by
    refine Ch03.hall_higman_1_2_3 ({p} : Set ℕ) ?_
    rw [show {q : ℕ | q ∉ ({p} : Set ℕ)} = {r : ℕ | r ≠ p} from S04.compl_singleton_eq]
    exact hredu
  have hC_pg : IsPGroup p ↥(Subgroup.centralizer (R : Set G)) := hR_pg.to_le hCR
  -- the conjugation action of `G` on `R`, with kernel `C`
  set ψ : G →* MulAut ↥R := MulAut.conjNormal with hψ_def
  have hker : ψ.ker = Subgroup.centralizer (R : Set G) := by
    rw [hψ_def]
    exact S04.conjNormal_ker
  have hker_pg : IsPGroup p ↥ψ.ker := by
    rw [hker]
    exact hC_pg
  have hquot_dvd : Nat.card (G ⧸ ψ.ker) ∣ Nat.card G := by
    have := Subgroup.index_dvd_card ψ.ker
    simpa [Subgroup.index] using this
  have hquot_odd : Odd (Nat.card (G ⧸ ψ.ker)) := by
    rcases Nat.even_or_odd (Nat.card (G ⧸ ψ.ker)) with he | ho
    · exfalso
      have h2 : (2 : ℕ) ∣ Nat.card G := dvd_trans he.two_dvd hquot_dvd
      rw [Nat.odd_iff] at hodd
      omega
    · exact ho
  -- Theorem 5.5 for `A := G ⧸ C` acting faithfully on the narrow `R` of rank ≥ 3
  obtain ⟨hcomm, -, hb, -⟩ := solvableAut_of_narrow hp hR_pg hR_narrow
    (QuotientGroup.kerLift ψ) (QuotientGroup.kerLift_injective ψ) hquot_odd
  -- 5.5(a): `(G ⧸ C)'` is a `p`-group (the Lemma 4.17 substitute)
  have hA' : IsPGroup p (_root_.commutator (G ⧸ ψ.ker)) := by
    have hle : _root_.commutator (G ⧸ ψ.ker) ≤ Ch01.opCore p (G ⧸ ψ.ker) := by
      rw [_root_.commutator, Subgroup.commutator_le]
      intro x _ y _
      have h1 : QuotientGroup.mk' (Ch01.opCore p (G ⧸ ψ.ker)) ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcomm _ _
      exact (QuotientGroup.eq_one_iff _).mp h1
    exact (Ch01.opCore_isPGroup p _).to_le hle
  -- pull back: `G' ≤ R` (identical to the Thm 4.18 core assembly)
  have hG'R : _root_.commutator G ≤ R := by
    have hW_pg : IsPGroup p
        ↥((_root_.commutator (G ⧸ ψ.ker)).comap (QuotientGroup.mk' ψ.ker)) := by
      refine IsPGroup.comap_of_ker_isPGroup hA' _ ?_
      rw [QuotientGroup.ker_mk']
      exact hker_pg
    haveI hW_norm :
        ((_root_.commutator (G ⧸ ψ.ker)).comap (QuotientGroup.mk' ψ.ker)).Normal :=
      Subgroup.Normal.comap inferInstance _
    have hW_le_R :
        (_root_.commutator (G ⧸ ψ.ker)).comap (QuotientGroup.mk' ψ.ker) ≤ R :=
      Ch03.Subgroup.IsPiGroup.le_oPiCore (S04.isPiGroup_singleton_of_isPGroup hW_pg)
    refine le_trans ?_ hW_le_R
    have hmap : (_root_.commutator G).map (QuotientGroup.mk' ψ.ker) =
        _root_.commutator (G ⧸ ψ.ker) := by
      rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective ψ.ker)]
    rw [← hmap]
    exact Subgroup.le_comap_map _ _
  refine ⟨hG'R, ?_⟩
  -- 5.5(b): a prime `q ≠ p` dividing `|G|` divides `p - 1` (the Lemma 4.13 substitute)
  intro q hq
  rw [Nat.mem_primeFactors] at hq
  obtain ⟨hq_prime, hq_dvd, -⟩ := hq
  rcases eq_or_ne q p with rfl | hq_ne
  · exact le_rfl
  · have hq_dvd_quot : q ∣ Nat.card (G ⧸ ψ.ker) := by
      have hmul : Nat.card ↥ψ.ker * Nat.card (G ⧸ ψ.ker) = Nat.card G := by
        have := Subgroup.card_mul_index ψ.ker
        simpa [Subgroup.index] using this
      rcases (Nat.Prime.dvd_mul hq_prime).mp (hmul ▸ hq_dvd) with h | h
      · exfalso
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hker_pg
        rw [hk] at h
        exact hq_ne ((Nat.prime_dvd_prime_iff_eq hq_prime hprime).mp
          (hq_prime.dvd_of_dvd_pow h))
      · exact h
    haveI : Fact q.Prime := ⟨hq_prime⟩
    obtain ⟨α, hα⟩ := exists_prime_orderOf_dvd_card' q hq_dvd_quot
    have hα_cop : Nat.Coprime (orderOf α) p := by
      rw [hα]
      exact (Nat.coprime_primes hq_prime hprime).mpr hq_ne
    have hα_dvd := hb hR_rank3 α hα_cop
    rw [hα] at hα_dvd
    have hp3 : 3 ≤ p := by
      have h2 := hprime.two_le
      rcases hp with ⟨k, hk⟩
      omega
    have hqle : q ≤ p - 1 := Nat.le_of_dvd (by omega) hα_dvd
    omega

end Thm56

/-- **BG Theorem 5.6**: `G` solvable odd, `p ∈ π(G)`, `S` を narrow Sylow `p`-subgroup と
する。`r(S) ≥ 3` なら、さらに `G` が `p`-length one (`hasPLengthOne`) と仮定する。すると:

* (a) `p` は `|G/O_{p'}(G)|` の最大素因子;
* (b) `p = 3` または `p` が `|G|` の最小素因子なら、`G` は normal `p`-complement を持つ;
* (c) `G'` は normal `p`-complement を持つ;
* (d) `G'` の任意の `p'`-subgroup は `O_{p'}(G')` に含まれる;
* (e) `G/O_{p',p}(G)` は abelian `p'`-群 (`p'` 部は `hasPLengthOne p G`)。

mmd L1945-1953。`r(S)≤2` で Thm 4.18, `r(S)≥3` で Thm 5.5 + Thm 4.18 の方法。 -/
theorem narrow_sylow_solvable_structure {G : Type*} [Group G] [Finite G] [IsSolvable G]
    (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime] (hp_mem : p ∣ Nat.card G)
    (S : Sylow p G) (hSnarrow : IsNarrow p ↥S)
    (hpl : 3 ≤ pRank ↥S p → hasPLengthOne p G) :
    (∀ q ∈ (Nat.card (G ⧸ Ch03.oPiCore {r | r ≠ p} G)).primeFactors, q ≤ p) ∧
    ((p = 3 ∨ ∀ q ∈ (Nat.card G).primeFactors, p ≤ q) → Ch05.HasNormalPComplement p G) ∧
    Ch05.HasNormalPComplement p ↥(commutator G) ∧
    (∀ K : Subgroup ↥(commutator G), Subgroup.IsPiSubgroup {r | r ≠ p} K →
      K ≤ Ch03.oPiCore {r | r ≠ p} ↥(commutator G)) ∧
    ((∀ x y : G ⧸ Ch03.oPiPrimePiCore {p} G, x * y = y * x) ∧ hasPLengthOne p G) := by
  classical
  by_cases hrank : pRank ↥(S : Subgroup G) p ≤ 2
  · -- `r(S) ≤ 2`: the Sylow-rank bridge gives `r_p(G) ≤ 2`; conclude by Theorem 4.18
    exact S04.solvable_structure_of_pRank_le_two hodd hp_mem
      (le_trans (pRank_le_pRank_sylow S) hrank)
  · -- `r(S) ≥ 3`: `p`-length one holds; run the Thm 5.5 narrow core on `Ḡ = G/O_{p'}(G)`
    have h3 : 3 ≤ pRank ↥(S : Subgroup G) p := by omega
    have hpl' : hasPLengthOne p G := hpl h3
    have hp_odd : Odd p := by
      rcases Nat.even_or_odd p with he | ho
      · exfalso
        have h2 : (2 : ℕ) ∣ Nat.card G := dvd_trans he.two_dvd hp_mem
        rw [Nat.odd_iff] at hodd
        omega
      · exact ho
    set N : Subgroup G := Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G with hN_def
    haveI hN_norm : N.Normal := by rw [hN_def]; infer_instance
    have hN_p' : ¬ p ∣ Nat.card ↥N := S04.not_dvd_card_oPiCore (by simp)
    have hquot_dvd_G : Nat.card (G ⧸ N) ∣ Nat.card G := by
      have := Subgroup.index_dvd_card N
      simpa [Subgroup.index] using this
    have hodd_bar : Odd (Nat.card (G ⧸ N)) := by
      rcases Nat.even_or_odd (Nat.card (G ⧸ N)) with he | ho
      · exfalso
        have h2 : (2 : ℕ) ∣ Nat.card G := dvd_trans he.two_dvd hquot_dvd_G
        rw [Nat.odd_iff] at hodd
        omega
      · exact ho
    -- the image Sylow `S̄ = SN/N` of `Ḡ`, isomorphic to `S` (`p ∤ |N|`)
    set Sbar : Sylow p (G ⧸ N) := S.mapSurjective (QuotientGroup.mk'_surjective N)
      with hSbar_def
    have hinj : Function.Injective
        ((QuotientGroup.mk' N).subgroupMap (S : Subgroup G)) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxN : (x : G) ∈ N := by
        have h1 : QuotientGroup.mk' N (x : G) = 1 := congrArg Subtype.val hx
        exact (QuotientGroup.eq_one_iff _).mp h1
      obtain ⟨k, hk⟩ := S.2 x
      have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
      have h2 : orderOf x ∣ Nat.card ↥N := by
        have he1 : orderOf ((S : Subgroup G).subtype x) = orderOf x :=
          orderOf_injective (S : Subgroup G).subtype
            (Subgroup.subtype_injective _) x
        have he2 : orderOf (N.subtype ⟨(x : G), hxN⟩) =
            orderOf (⟨(x : G), hxN⟩ : ↥N) :=
          orderOf_injective N.subtype N.subtype_injective _
        have he3 : orderOf ((x : G)) = orderOf (⟨(x : G), hxN⟩ : ↥N) := he2
        calc orderOf x = orderOf (⟨(x : G), hxN⟩ : ↥N) := by
              rw [← he1]
              exact he3
          _ ∣ Nat.card ↥N := orderOf_dvd_natCard _
      have hcop : Nat.Coprime (p ^ k) (Nat.card ↥N) :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN_p')
      have h3' : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
      exact orderOf_eq_one_iff.mp h3'
    have hSbar_coe : (Sbar : Subgroup (G ⧸ N)) =
        (S : Subgroup G).map (QuotientGroup.mk' N) := rfl
    have e : ↥(S : Subgroup G) ≃* ↥(Sbar : Subgroup (G ⧸ N)) :=
      (MulEquiv.ofBijective ((QuotientGroup.mk' N).subgroupMap (S : Subgroup G))
        ⟨hinj, (QuotientGroup.mk' N).subgroupMap_surjective (S : Subgroup G)⟩).trans
        (MulEquiv.subgroupCongr hSbar_coe.symm)
    have hSbar_narrow : IsNarrow p ↥(Sbar : Subgroup (G ⧸ N)) :=
      IsNarrow.of_mulEquiv e hSnarrow
    have h3bar : 3 ≤ pRank ↥(Sbar : Subgroup (G ⧸ N)) p :=
      le_trans h3 (pRank_le_of_injective (f := e.toMonoidHom) e.injective)
    have hredu_bar : Ch03.oPiCore {r : ℕ | r ≠ p} (G ⧸ N) = ⊥ := by
      rw [show {r : ℕ | r ≠ p} = {q : ℕ | q ∉ ({p} : Set ℕ)} from
        S04.compl_singleton_eq.symm]
      exact Ch03.oPiCore_quotient_self_eq_bot _
    -- `p`-length one transports to `p ∤ |Ḡ/O_p(Ḡ)|` by the third isomorphism theorem
    have hpOp_bar : ¬ p ∣ Nat.card ((G ⧸ N) ⧸ Ch03.oPiCore ({p} : Set ℕ) (G ⧸ N)) := by
      rw [hasPLengthOne, S04.card_quotient_oPiPrimePiCore (G := G) (p := p)] at hpl'
      exact hpl'
    obtain ⟨hG'bar, hlargest⟩ :=
      core56 hp_odd hodd_bar Sbar hSbar_narrow h3bar hredu_bar hpOp_bar
    exact S04.structure_of_quotient_commutator_le_opCore hodd hG'bar hlargest hpOp_bar

/-- **BG Theorem 5.7**: `G` solvable odd, `p ∈ π(G)`, `E` を `F(G)` の elem-ab `p`-subgroup と
し、`r(C_{F(G)}(E)) ≤ 2` を仮定。すると `G' ⊆ F(G)`。

mmd L1955-1967。Prop 1.2 (chief factor 還元) + 各 chief factor `U/V ⊆ F(G)` で
`O_q(G)` が narrow ⇒ Thm 5.5 ⇒ `G'` が `q`-自己同型を誘導 ⇒ `G' ⊆ C_G(U/V)`。 -/
theorem derived_le_fitting_of_centralizer_pRank_le_two {G : Type*} [Group G] [Finite G]
    [IsSolvable G] (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime]
    (E : Subgroup G) (hE : E.IsElementaryAbelian p) (hEF : E ≤ Ch01.fitting G)
    (hrank : pRank ↥(Subgroup.centralizer (E : Set G) ⊓ Ch01.fitting G) p ≤ 2) :
    commutator G ≤ Ch01.fitting G := by
  sorry

end OddOrder.BG.Ch1.S05
