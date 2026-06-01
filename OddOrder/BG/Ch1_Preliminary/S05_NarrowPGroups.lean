/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
import OddOrder.BG.Ch1_Preliminary.S04_PGroupsSmallRank
import OddOrder.BG.Ch1_Preliminary.S04d_GorThm415
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

## 証明の前提 (proof は後続)

§5 の hard 結果は **§4 capstone** に依存する: Lem 5.1(a)=Lem 4.7 hard dir (✅ `pRank_le_two_of_scn3_empty`),
Lem 4.5(c) noncyclic 半 (TODO), Lem 4.14 (`q∣(p+1)/2`, §4 active frontier), Thm 4.16 (Blackburn),
Lem 4.17, Thm 4.18 (= §5.5/5.6 が cite, repo 未命名)。statement は今 faithful に書けるが、proof は
これら §4 capstone 完成後 (一部は本ファイルで close 可)。
-/

namespace OddOrder.BG.Ch1.S05

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped IsMulCommutative

variable {R : Type*} [Group R]

/-- `Ω₁(Z(R))`: 中心 `Z(R)` の位数 `p` 元が生成する部分群。中心は可換なので
`omega1OfAbelian` で `Subgroup R` として実現できる (BG §5 で `|Ω₁(Z(R))| = p` を述べるため)。 -/
private def omega1Center (R : Type*) [Group R] (p : ℕ) : Subgroup R :=
  omega1OfAbelian R (Subgroup.center R) p
    (fun _ hx _ _ => (Subgroup.mem_center_iff.mp hx _).symm)

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
  sorry

/-! ## Theorem 5.3 / Corollary 5.4 — narrow の特徴づけ (mmd L1838-1879) -/

/-- **BG Theorem 5.3** (narrow 特徴づけ): 奇素数 `p`, 有限 `p`-群 `R`, `r(R) ≥ 3`。すると
`R` が narrow ⇔ `ℰ²(R) ∩ ℰ*(R) ≠ ∅` (位数 `p²` の elem-ab で位数 `p³` の elem-ab に含まれない
ものが存在)。

mmd L1838-1873。⇒ は narrow の定義から `E = Ω₁(C_R(R₀))` を作り、⇐ は `E = Z×S` 分解 +
Thm 5.3(d) の `C_R(S) = S×C_T(S)` から narrow を得る。 -/
theorem narrow_iff_exists_maximalElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R) (h3 : 3 ≤ pRank R p) :
    IsNarrow p R ↔
      ∃ E : Subgroup R, Nat.card ↥E = p ^ 2 ∧ IsMaximalElementaryAbelian p E := by
  sorry

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
  sorry

/-- **BG Corollary 5.4**: 奇素数 `p`, 有限 `p`-群 `R`, `r(R) ≥ 3`。すると `R` が narrow ⇔
位数 `p` の `S ≤ R` で `r(C_R(S)) ≤ 2` となるものが存在。

mmd L1875-1879。Thm 5.3 + `S↦SZ ∈ ℰ²∩ℰ*` から。 -/
theorem narrow_iff_exists_card_prime_centralizer_pRank_le_two
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R) (h3 : 3 ≤ pRank R p) :
    IsNarrow p R ↔
      ∃ S : Subgroup R, Nat.card ↥S = p ∧
        pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2 := by
  sorry

/-! ## Theorem 5.5 — narrow `p`-群の solvable odd 自己同型群 (mmd L1881-1941) -/

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
  sorry

/-! ## Theorem 5.6 / 5.7 — solvable group での narrow Sylow (mmd L1945-1967) -/

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
  sorry

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
