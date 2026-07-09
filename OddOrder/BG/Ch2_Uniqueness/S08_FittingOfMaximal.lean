/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch2_Uniqueness.Setup
import OddOrder.BG.Ch2_Uniqueness.S07_Transitivity
import OddOrder.BG.AppB_Thm62
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.GroupTheory.MaximalSubgroup
import OddOrder.GroupTheory.SCN
import OddOrder.GroupTheory.PRank
import OddOrder.GroupTheory.ElementaryAbelian
import OddOrder.Isaacs.Ch01_Sylow.Main

/-!
# BG §8: The Fitting Subgroup of a Maximal Subgroup

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter II §8 (pp. 60-62), mmd `references/bg/local-analysis.mmd`
L2315-2485, **1 結果** (Thm 8.1, (a)(b) 2 部).

§8 は Uniqueness Theorem への第一歩: maximal subgroup `M` が *large* (`r(F(M)) ≥ 3`) なら
`F(M)` の *large* な部分群が `𝒰` に入る。`G` の単純性から「`L ⊴ M` 非自明 ⇒ `N_G(L) = M`」を多用。

## 記法 (BG → repo)

- `M ∈ ℳ` = `M ∈ maximalSubgroups G` (`IsCoatom M`); `𝒰` = `IsUniquelyMaximal`。
- `F(M)` を `G` 内に戻したもの = `fittingInG M` (`(Ch01.fitting ↥M).map M.subtype`)。
- `ℰ_p^*(F(M))` (F(M) 内の極大 elem-ab) = `isMaxElemAbelianIn p A₀ (fittingInG M)`。
- `m(A₀)` = `rank ↥A₀`; `C_{F(M)}(A₀)` = `Subgroup.centralizer (A₀:Set G) ⊓ fittingInG M`。
- `SCN₃(P)` (Sylow `P` of `M` 内) = `IsSCN₃ p (A.subgroupOf (P:Subgroup ↥M))`。
- 固定 G は `(hG : IsMinimalSimpleOdd G)` を明示 thread。

## Lane C proof-gate notes

`sylow_isSylow_and_scn3_isUniquelyMaximal_of_pGroup` は sorry-free。proof は §7
(Thm 7.2/7.4/7.6) + §6 Thm 6.2 一般形 + Prop 1.10/1.3 に依存。
§5 Lem 5.1 is only the nonemptiness remark for `SCN₃(P)`
(mmd L2324); the part (b) statement is universal over all `A ∈ SCN₃(P)` and should not
carry Lem 5.1 as an extra assumption. No §5 narrow classification theorem or BG Thm 4.16
assumption belongs in §8.
-/

namespace OddOrder.BG.Ch2.S08

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-- `F(M)` (maximal subgroup `M` の Fitting 部分群) を `G` 内の部分群として実現したもの。 -/
def fittingInG (M : Subgroup G) : Subgroup G :=
  (Ch01.fitting ↥M).map M.subtype

/-- `F(M)`, realized in `G`, lies inside `M`. -/
theorem fittingInG_le (M : Subgroup G) : fittingInG M ≤ M :=
  Subgroup.map_subtype_le _

/-- The ambient q-core `O_q(M)` lies inside `F(M)`. -/
theorem opiCoreInG_singleton_le_fittingInG [Finite G] {q : ℕ} [Fact q.Prime]
    (M : Subgroup G) :
    opiCoreInG ({q} : Set ℕ) M ≤ fittingInG M := by
  rw [opiCoreInG, fittingInG]
  refine Subgroup.map_mono ?_
  rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := ↥M) q]
  exact Ch01.opCore_le_fitting ⟨q, Fact.out⟩ ↥M

/-- A normal ambient q-subgroup of `M` lies inside `F(M)`. -/
theorem le_fittingInG_of_normal_isPiSubgroup_singleton [Finite G]
    {q : ℕ} [Fact q.Prime] {M Q : Subgroup G}
    (hQM : Q ≤ M) (hQnorm : (Q.subgroupOf M).Normal)
    (hQpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) Q) :
    Q ≤ fittingInG M :=
  (le_opiCoreInG_of_normal_of_isPiSubgroup hQM hQnorm hQpi).trans
    (opiCoreInG_singleton_le_fittingInG M)

/-- The relative centralizer C_{F(M)}(A0), realized in the ambient group G. -/
def cFittingInG (M A0 : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M

/-- Realizing `F(M)` in `G` and then restricting back to `M` recovers the original
Fitting subgroup of the group `↥M`. -/
theorem fittingInG_subgroupOf_eq (M : Subgroup G) :
    (fittingInG M).subgroupOf M = Ch01.fitting ↥M := by
  ext x
  rw [Subgroup.mem_subgroupOf, fittingInG, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hy_eq⟩
    have hyx : y = x := Subtype.ext hy_eq
    rwa [← hyx]
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Ambient form of BG Proposition 1.3 for a subgroup M: elements of M centralizing
F(M) lie in F(M). -/
theorem mem_fittingInG_of_mem_centralizer_fittingInG [Finite G] {M : Subgroup G}
    [IsSolvable ↥M] {x : G} (hxM : x ∈ M)
    (hxC : x ∈ Subgroup.centralizer (fittingInG M : Set G)) :
    x ∈ fittingInG M := by
  have hxC_M : (⟨x, hxM⟩ : ↥M) ∈
      Subgroup.centralizer ((Ch01.fitting ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hyF : (y : G) ∈ fittingInG M := by
      have hySub : y ∈ (fittingInG M).subgroupOf M := by
        rwa [fittingInG_subgroupOf_eq M]
      exact Subgroup.mem_subgroupOf.mp hySub
    exact Subgroup.mem_centralizer_iff.mp hxC (y : G) hyF
  have hxF_M : (⟨x, hxM⟩ : ↥M) ∈ Ch01.fitting ↥M :=
    OddOrder.BG.Ch1.S01.centralizer_fitting_le_fitting hxC_M
  have hxSub : (⟨x, hxM⟩ : ↥M) ∈ (fittingInG M).subgroupOf M := by
    rwa [fittingInG_subgroupOf_eq M]
  exact Subgroup.mem_subgroupOf.mp hxSub

/-- Subgroup form of the ambient self-centralizing property for F(M). -/
theorem centralizer_fittingInG_inf_le_fittingInG [Finite G] {M : Subgroup G}
    [IsSolvable ↥M] :
    Subgroup.centralizer (fittingInG M : Set G) ⊓ M ≤ fittingInG M := by
  intro x hx
  exact mem_fittingInG_of_mem_centralizer_fittingInG hx.2 hx.1

/-- If x lies in F(M) and generates a pi(F(M))-complement subgroup, then x is trivial. -/
theorem eq_one_of_mem_fittingInG_of_zpowers_isPiSubgroup_primesOf_compl [Finite G]
    {M : Subgroup G} {x : G} (hxF : x ∈ fittingInG M)
    (hxpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ
      (Subgroup.zpowers x)) :
    x = 1 :=
  eq_one_of_mem_of_isPiSubgroup_of_zpowers_isPiSubgroup_compl
    (π := OddOrder.BG.Ch2.S07.primesOf (fittingInG M)) (H := fittingInG M)
    (fun r hr => by simpa [OddOrder.BG.Ch2.S07.primesOf] using hr) hxF hxpi

/-- `F(M)`, viewed as a subgroup of `M`, is characteristic. -/
theorem fittingInG_subgroupOf_characteristic (M : Subgroup G) :
    ((fittingInG M).subgroupOf M).Characteristic := by
  rw [fittingInG_subgroupOf_eq]
  exact Ch01.fitting.characteristic ↥M

/-- `F(M)`, viewed as a subgroup of `M`, is normal. -/
theorem fittingInG_subgroupOf_normal (M : Subgroup G) :
    ((fittingInG M).subgroupOf M).Normal := by
  rw [fittingInG_subgroupOf_eq]
  exact Ch01.fitting.normal ↥M

/-- Any element of M normalizes F(M), viewed in the ambient group G. -/
theorem mem_normalizer_fittingInG_of_mem {M : Subgroup G} {x : G} (hxM : x ∈ M) :
    x ∈ Subgroup.normalizer (fittingInG M : Set G) := by
  have hM_norm_F : M ≤ Subgroup.normalizer (fittingInG M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (fittingInG_le M)).mp
      (fittingInG_subgroupOf_normal M)
  exact hM_norm_F hxM

/-- The cyclic subgroup generated by an element of M normalizes F(M). -/
theorem zpowers_le_normalizer_fittingInG_of_mem {M : Subgroup G} {x : G} (hxM : x ∈ M) :
    Subgroup.zpowers x ≤ Subgroup.normalizer (fittingInG M : Set G) :=
  Subgroup.zpowers_le.mpr (mem_normalizer_fittingInG_of_mem hxM)

/-- Conjugation action of the cyclic subgroup generated by x on F(M), for x in M. -/
def conjActionOnFittingInG {M : Subgroup G} {x : G} (hxM : x ∈ M) :
    ↥(Subgroup.zpowers x) →* MulAut ↥(fittingInG M) :=
  (fittingInG M).normalizerMonoidHom.comp
    (Subgroup.inclusion (zpowers_le_normalizer_fittingInG_of_mem hxM))

/-- The action on F(M) above is ambient conjugation. -/
theorem conjActionOnFittingInG_apply {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (a : ↥(Subgroup.zpowers x)) (f : ↥(fittingInG M)) :
    ((conjActionOnFittingInG hxM a) f : G) = (a : G) * (f : G) * (a : G)⁻¹ := by
  rw [conjActionOnFittingInG]
  rfl

/-- Fixed points of the cyclic conjugation action on F(M) are the elements of F(M)
centralizing the cyclic subgroup. -/
theorem fixedPoints_conjActionOnFittingInG_eq {M : Subgroup G} {x : G} (hxM : x ∈ M) :
    Subgroup.fixedPointsOfMulAut (conjActionOnFittingInG hxM) =
      (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
        (fittingInG M) := by
  ext f
  constructor
  · intro hf
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, f.2⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    have hfix := Subgroup.mem_fixedPointsOfMulAut.mp hf ⟨y, hy⟩
    have hfixG := congrArg Subtype.val hfix
    rw [conjActionOnFittingInG_apply] at hfixG
    calc y * (f : G) = (y * (f : G) * y⁻¹) * y := by group
      _ = (f : G) * y := by rw [hfixG]
  · intro hf
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    apply Subtype.ext
    rw [conjActionOnFittingInG_apply]
    have hfcent : (f : G) ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
      (Subgroup.mem_subgroupOf.mp hf).1
    have hcomm : (a : G) * (f : G) = (f : G) * (a : G) :=
      Subgroup.mem_centralizer_iff.mp hfcent (a : G) a.2
    calc (a : G) * (f : G) * (a : G)⁻¹ = (f : G) * (a : G) * (a : G)⁻¹ := by rw [hcomm]
      _ = (f : G) := by group

/-- Ambient form of BG Proposition 1.4: if a coprime subgroup `B` normalizes a
finite solvable subgroup `N` and centralizes `F(N)`, then `B` centralizes `N`. -/
theorem le_centralizer_of_coprime_normalizes_of_le_centralizer_fittingInG
    [Finite G] {B N : Subgroup G} [IsSolvable ↥N]
    (hBN : B ≤ Subgroup.normalizer (N : Set G))
    (hCop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥N))
    (hBF : B ≤ Subgroup.centralizer (fittingInG N : Set G)) :
    B ≤ Subgroup.centralizer (N : Set G) := by
  let φ : ↥B →* MulAut ↥N :=
    N.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hφcoe : ∀ (b : ↥B) (n : ↥N),
      ((φ b) n : G) = (b : G) * (n : G) * (b : G)⁻¹ := by
    intro b n
    dsimp [φ]
    rfl
  have hF_le_fixed : Ch01.fitting ↥N ≤ Subgroup.fixedPointsOfMulAut φ := by
    intro f hf
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro b
    refine Subtype.ext ?_
    rw [hφcoe]
    have hfG : (f : G) ∈ fittingInG N := by
      have hfSub : f ∈ (fittingInG N).subgroupOf N := by
        rwa [fittingInG_subgroupOf_eq N]
      exact Subgroup.mem_subgroupOf.mp hfSub
    have hcomm : Commute (f : G) (b : G) :=
      Subgroup.mem_centralizer_iff.mp (hBF b.2) (f : G) hfG
    rw [hcomm.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hAC_bot : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
    OddOrder.BG.Ch1.S01.actionCommutator_eq_bot_of_fitting_le_fixedPoints
      hCop hF_le_fixed
  have htriv : ∀ b : ↥B, ∀ n : ↥N, (φ b) n = n :=
    (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially φ).mp hAC_bot
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hval := congrArg Subtype.val (htriv ⟨b, hb⟩ ⟨n, hn⟩)
  rw [hφcoe] at hval
  exact (mul_inv_eq_iff_eq_mul.mp hval).symm

/-- Fitting M, realized in G, is nilpotent. -/
theorem fittingInG_isNilpotent [Finite G] (M : Subgroup G) :
    Group.IsNilpotent ↥(fittingInG M) := by
  rw [fittingInG]
  haveI : Group.IsNilpotent ↥(Ch01.fitting ↥M) := Ch01.fitting.isNilpotent
  exact Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective (Ch01.fitting ↥M)
    M.subtype M.subtype_injective)

/-- An element normalizing `N` also normalizes the ambient realization of `F(N)`. -/
theorem mem_normalizer_fittingInG_of_mem_normalizer {N : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (N : Set G)) :
    x ∈ Subgroup.normalizer (fittingInG N : Set G) := by
  have hforward : ∀ {z : G}, z ∈ Subgroup.normalizer (N : Set G) →
      ∀ y : G, y ∈ fittingInG N → z * y * z⁻¹ ∈ fittingInG N := by
    intro z hz y hy
    have hyN : y ∈ N := fittingInG_le N hy
    let φ : MulAut ↥N := N.normalizerMonoidHom ⟨z, hz⟩
    have hchar : ((fittingInG N).subgroupOf N).map (φ : ↥N →* ↥N) =
        (fittingInG N).subgroupOf N :=
      Subgroup.characteristic_iff_map_eq.mp (fittingInG_subgroupOf_characteristic N) φ
    have hySub : (⟨y, hyN⟩ : ↥N) ∈ (fittingInG N).subgroupOf N := by
      simpa [Subgroup.mem_subgroupOf] using hy
    have hmap : φ ⟨y, hyN⟩ ∈ ((fittingInG N).subgroupOf N).map (φ : ↥N →* ↥N) := by
      rw [Subgroup.mem_map]
      exact ⟨⟨y, hyN⟩, hySub, rfl⟩
    rw [hchar] at hmap
    have hmem : ((φ ⟨y, hyN⟩ : ↥N) : G) ∈ fittingInG N := by
      exact Subgroup.mem_subgroupOf.mp hmap
    simpa [φ] using hmem
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hforward hxN y
  · intro hy
    have hxN_inv : x⁻¹ ∈ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normalizer (N : Set G)).inv_mem hxN
    have hback : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ ∈ fittingInG N :=
      hforward hxN_inv (x * y * x⁻¹) hy
    have hEq : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    simpa [hEq] using hback

/-- If `N ≤ H` and `H` normalizes `N`, then the ambient realization of `F(N)`
lies in the ambient realization of `F(H)`. -/
theorem fittingInG_le_fittingInG_of_le_normalizer [Finite G] {N H : Subgroup G}
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    fittingInG N ≤ fittingInG H := by
  have hFN_H : fittingInG N ≤ H := (fittingInG_le N).trans hNH
  have hFN_norm_H : ((fittingInG N).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hFN_H]
    intro x hx
    exact mem_normalizer_fittingInG_of_mem_normalizer (hHN hx)
  have hFN_nilp_H : Group.IsNilpotent ↥((fittingInG N).subgroupOf H) := by
    haveI : Group.IsNilpotent ↥(fittingInG N) := fittingInG_isNilpotent N
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFN_H).symm
  have hSub_le_fitH : (fittingInG N).subgroupOf H ≤ Ch01.fitting ↥H := by
    haveI : ((fittingInG N).subgroupOf H).Normal := hFN_norm_H
    haveI : Group.IsNilpotent ↥((fittingInG N).subgroupOf H) := hFN_nilp_H
    exact Ch01.nilpotent_normal_le_fitting
  calc fittingInG N = ((fittingInG N).subgroupOf H).map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hFN_H).symm
    _ ≤ (Ch01.fitting ↥H).map H.subtype := Subgroup.map_mono hSub_le_fitH
    _ = fittingInG H := rfl

/-- BG (8.7) Fitting-core bridge: `F(O_{p'}(H))` lies in `O_{p'}(F(H))`. -/
theorem fittingInG_opiCoreInG_singleton_compl_le_opiCoreInG_singleton_compl_fittingInG
    [Finite G] {p : ℕ} [Fact p.Prime] (H : Subgroup G) :
    fittingInG (opiCoreInG ({p} : Set ℕ)ᶜ H) ≤
      opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG H) := by
  let N : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ H
  change fittingInG N ≤ opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG H)
  have hN_H : N ≤ H := by
    dsimp [N]
    exact opiCoreInG_le ({p} : Set ℕ)ᶜ H
  have hH_norm_N : H ≤ Subgroup.normalizer (N : Set G) := by
    dsimp [N]
    exact le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ H
  have hFN_FH : fittingInG N ≤ fittingInG H :=
    fittingInG_le_fittingInG_of_le_normalizer hN_H hH_norm_N
  have hFN_norm_FH : ((fittingInG N).subgroupOf (fittingInG H)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hFN_FH]
    intro x hx
    have hxH : x ∈ H := fittingInG_le H hx
    exact mem_normalizer_fittingInG_of_mem_normalizer (hH_norm_N hxH)
  have hFN_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ (fittingInG N) := by
    intro r hr
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ H r
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le (fittingInG_le N))
        Nat.card_pos.ne' hr)
  exact le_opiCoreInG_of_normal_of_isPiSubgroup hFN_FH hFN_norm_FH hFN_pi

/-- For a finite solvable subgroup `H`, its `π(F(H))`-complement core is trivial.

This is the ambient form of the BG §8 step `O_{σ'}(H)=1`, where `σ=π(F(H))`.
If the core were nontrivial, the Fitting subgroup of that normal solvable subgroup would
map to a nontrivial subgroup of both `F(H)` and the `σ`-complement core. -/
theorem opiCoreInG_primesOf_fittingInG_compl_eq_bot [Finite G]
    {H : Subgroup G} [IsSolvable ↥H] :
    opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (fittingInG H))ᶜ H = ⊥ := by
  classical
  let σ : Set ℕ := OddOrder.BG.Ch2.S07.primesOf (fittingInG H)
  let N : Subgroup G := opiCoreInG σᶜ H
  suffices N = ⊥ by simpa [N, σ]
  by_contra hN_ne_bot
  have hNH : N ≤ H := by
    dsimp [N]
    exact opiCoreInG_le σᶜ H
  let NH : Subgroup H := N.subgroupOf H
  haveI hNH_normal : NH.Normal := by
    dsimp [NH]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr (by
      dsimp [N]
      exact le_normalizer_opiCoreInG σᶜ H)
  have hNH_ne_bot : NH ≠ ⊥ := by
    intro hbot
    apply hN_ne_bot
    have hmap : NH.map H.subtype = N := by
      dsimp [NH]
      exact Subgroup.map_subgroupOf_eq_of_le hNH
    rw [← hmap, hbot, Subgroup.map_bot]
  haveI hNH_nontrivial : Nontrivial ↥NH :=
    (Subgroup.nontrivial_iff_ne_bot NH).mpr hNH_ne_bot
  have hFNH_ne_bot : Ch01.fitting ↥NH ≠ ⊥ :=
    Ch01.fitting_ne_bot_of_solvable_nontrivial ↥NH
  let FNH : Subgroup H := (Ch01.fitting ↥NH).map NH.subtype
  have hFNH_ne_bot : FNH ≠ ⊥ := by
    intro hbot
    apply hFNH_ne_bot
    exact (Subgroup.map_eq_bot_iff_of_injective (Ch01.fitting ↥NH)
      NH.subtype_injective).mp hbot
  let B : Subgroup G := FNH.map H.subtype
  have hB_ne_bot : B ≠ ⊥ := by
    intro hbot
    apply hFNH_ne_bot
    exact (Subgroup.map_eq_bot_iff_of_injective FNH H.subtype_injective).mp hbot
  have hFNH_le_fittingH : FNH ≤ Ch01.fitting ↥H := by
    dsimp [FNH]
    exact Ch01.fitting_map_subtype_le_fitting
  have hB_le_fittingH : B ≤ fittingInG H := by
    dsimp [B, fittingInG]
    exact Subgroup.map_mono hFNH_le_fittingH
  have hFNH_le_NH : FNH ≤ NH := by
    dsimp [FNH]
    exact Subgroup.map_subtype_le _
  have hB_le_N : B ≤ N := by
    dsimp [B]
    calc FNH.map H.subtype
        ≤ NH.map H.subtype := Subgroup.map_mono hFNH_le_NH
      _ = N := by
        dsimp [NH]
        exact Subgroup.map_subgroupOf_eq_of_le hNH
  have hN_pi_compl : Subgroup.IsPiSubgroup σᶜ N := by
    dsimp [N]
    exact isPiSubgroup_opiCoreInG σᶜ H
  have hB_pi_compl : Subgroup.IsPiSubgroup σᶜ B := by
    intro r hr
    exact hN_pi_compl r
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hB_le_N) Nat.card_pos.ne' hr)
  have hFittingH_pi : Subgroup.IsPiSubgroup σ (fittingInG H) := by
    intro r hr
    simpa [σ, OddOrder.BG.Ch2.S07.primesOf] using hr
  have hB_bot : B = ⊥ :=
    eq_bot_of_le_of_isPiSubgroup_of_isPiSubgroup_compl hB_le_fittingH hFittingH_pi
      hB_pi_compl
  exact hB_ne_bot hB_bot

/-- Ambient core commutation: `O_π(H)` centralizes `O_{π'}(H)` inside `H`.
This is the core form of the `[O_q(H), O_{q'}(H)] = 1` step used in BG (8.7). -/
theorem opiCoreInG_commutator_compl_eq_bot [Finite G]
    (π : Set ℕ) (H : Subgroup G) :
    ⁅opiCoreInG π H, opiCoreInG πᶜ H⁆ = ⊥ := by
  have hleft : ⁅opiCoreInG π H, opiCoreInG πᶜ H⁆ ≤ opiCoreInG π H :=
    OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer
      ((opiCoreInG_le πᶜ H).trans (le_normalizer_opiCoreInG π H))
  have hright : ⁅opiCoreInG π H, opiCoreInG πᶜ H⁆ ≤ opiCoreInG πᶜ H := by
    rw [Subgroup.commutator_comm]
    exact OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer
      ((opiCoreInG_le π H).trans (le_normalizer_opiCoreInG πᶜ H))
  have hinf : opiCoreInG π H ⊓ opiCoreInG πᶜ H = ⊥ :=
    inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl
      (isPiSubgroup_opiCoreInG π H)
      (isPiSubgroup_opiCoreInG πᶜ H)
  exact le_bot_iff.mp (by
    rw [← hinf]
    exact le_inf hleft hright)

/-- The `π`-core of `F(H)`, viewed as a subgroup of `H`, is normal. -/
theorem opiCoreInG_fittingInG_subgroupOf_normal [Finite G]
    (π : Set ℕ) (H : Subgroup G) :
    ((opiCoreInG π (fittingInG H)).subgroupOf H).Normal := by
  have hNH : opiCoreInG π (fittingInG H) ≤ H :=
    (opiCoreInG_le π (fittingInG H)).trans (fittingInG_le H)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNH]
  have hH_norm_F : H ≤ Subgroup.normalizer (fittingInG H : Set G) := by
    intro x hx
    exact mem_normalizer_fittingInG_of_mem hx
  exact le_normalizer_opiCoreInG_of_le_normalizer π hH_norm_F

/-- The `π`-core of `F(H)` is absorbed by the `π`-core of `H`.
This is the formal `D_q ≤ O_q(H)` bridge for BG (8.7), with `D = F(H)`. -/
theorem opiCoreInG_fittingInG_le_opiCoreInG [Finite G]
    (π : Set ℕ) (H : Subgroup G) :
    opiCoreInG π (fittingInG H) ≤ opiCoreInG π H := by
  have hNH : opiCoreInG π (fittingInG H) ≤ H :=
    (opiCoreInG_le π (fittingInG H)).trans (fittingInG_le H)
  exact le_opiCoreInG_of_normal_of_isPiSubgroup hNH
    (opiCoreInG_fittingInG_subgroupOf_normal π H)
    (isPiSubgroup_opiCoreInG π (fittingInG H))

/-- Monotonicity of the ambient `π`-core in the set of primes. -/
theorem opiCoreInG_mono [Finite G] {π ρ : Set ℕ}
    (hπρ : π ⊆ ρ) (H : Subgroup G) :
    opiCoreInG π H ≤ opiCoreInG ρ H := by
  rw [opiCoreInG, opiCoreInG]
  exact Subgroup.map_mono (Ch03.oPiCore_mono hπρ ↥H)

/-- In a finite nilpotent subgroup `K`, every ambient p-subgroup of `K` lies in
`O_p(K)`. -/
theorem le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent [Finite G]
    {p : ℕ} [Fact p.Prime] {K P : Subgroup G}
    (hKnilp : Group.IsNilpotent ↥K)
    (hPK : P ≤ K) (hPp : IsPGroup p ↥P) :
    P ≤ opiCoreInG ({p} : Set ℕ) K := by
  haveI : Group.IsNilpotent ↥K := hKnilp
  have hPsub_p : IsPGroup p ↥(P.subgroupOf K) := by
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    exact IsPGroup.of_card (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv]
      exact hn)
  obtain ⟨S, hPS⟩ := hPsub_p.exists_le_sylow
  haveI hSnormal : (S : Subgroup ↥K).Normal := Ch01.Sylow.normal_of_isNilpotent S
  have hSpi : Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) (S : Subgroup ↥K) := by
    intro r hr
    exact (isPiSubgroup_singleton_of_isPGroup (G := ↥K) S.isPGroup') r hr
  have hSleCore : (S : Subgroup ↥K) ≤ Ch03.oPiCore ({p} : Set ℕ) ↥K :=
    hSpi.le_oPiCore
  calc P = (P.subgroupOf K).map K.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hPK).symm
    _ ≤ (S : Subgroup ↥K).map K.subtype := Subgroup.map_mono hPS
    _ ≤ opiCoreInG ({p} : Set ℕ) K := Subgroup.map_mono hSleCore

/-- A finite nilpotent ambient subgroup is generated by the images of its default
Sylow subgroups. This packages the Ch. 1 Sylow-generation theorem in the form
needed for subgroup containments in `G`. -/
theorem le_of_sylow_le_of_nilpotent [Finite G] {K X : Subgroup G}
    (hKnilp : Group.IsNilpotent ↥K)
    (hSyl : ∀ r : (Nat.card ↥K).primeFactors,
      ((default : Sylow (r : ℕ) ↥K) : Subgroup ↥K).map K.subtype ≤ X) :
    K ≤ X := by
  haveI : Group.IsNilpotent ↥K := hKnilp
  have htop_map : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← htop_map, ← Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥K, Subgroup.map_iSup]
  exact iSup_le hSyl

/-- The r-core of `C_F(M)(A0)` lies in the r-core of `F(M)`. -/
theorem opiCoreInG_singleton_cFittingInG_le_opiCoreInG_fittingInG [Finite G]
    {q : ℕ} [Fact q.Prime] {M A0 : Subgroup G} :
    opiCoreInG ({q} : Set ℕ) (cFittingInG M A0) ≤
      opiCoreInG ({q} : Set ℕ) (fittingInG M) := by
  have hcore_le_F : opiCoreInG ({q} : Set ℕ) (cFittingInG M A0) ≤ fittingInG M :=
    (opiCoreInG_le ({q} : Set ℕ) (cFittingInG M A0)).trans (by
      dsimp [cFittingInG]
      exact inf_le_right)
  exact le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
    (fittingInG_isNilpotent M) hcore_le_F
    (isPGroup_opiCoreInG_singleton (cFittingInG M A0))

/-- If `r ≠ q`, then the r-core of `C_F(M)(A0)` lies in `O_{q'}(M)`. -/
theorem opiCoreInG_singleton_cFittingInG_le_opiCoreInG_singleton_compl_maximal_of_ne
    [Finite G] {q r : ℕ} [Fact q.Prime] [Fact r.Prime] {M A0 : Subgroup G}
    (hqr : q ≠ r) :
    opiCoreInG ({r} : Set ℕ) (cFittingInG M A0) ≤ opiCoreInG ({q} : Set ℕ)ᶜ M := by
  have hArF : opiCoreInG ({r} : Set ℕ) (cFittingInG M A0) ≤
      opiCoreInG ({r} : Set ℕ) (fittingInG M) :=
    opiCoreInG_singleton_cFittingInG_le_opiCoreInG_fittingInG
  have hArM : opiCoreInG ({r} : Set ℕ) (cFittingInG M A0) ≤
      opiCoreInG ({r} : Set ℕ) M :=
    hArF.trans (opiCoreInG_fittingInG_le_opiCoreInG ({r} : Set ℕ) M)
  have hsubset : ({r} : Set ℕ) ⊆ ({q} : Set ℕ)ᶜ := by
    intro s hs hsq
    rw [Set.mem_singleton_iff] at hs hsq
    exact hqr (hsq.symm.trans hs)
  exact hArM.trans (opiCoreInG_mono hsubset M)

/-- The `π`-core of `F(H)` centralizes the `π`-complement core of `H`.

This is the `D_q` versus `O_{q'}(H)` commutation part of BG (8.7), with
`D = F(H)`. -/
theorem opiCoreInG_fittingInG_commutator_compl_eq_bot [Finite G]
    (π : Set ℕ) (H : Subgroup G) :
    ⁅opiCoreInG π (fittingInG H), opiCoreInG πᶜ H⁆ = ⊥ := by
  have hD_le : opiCoreInG π (fittingInG H) ≤ opiCoreInG π H :=
    opiCoreInG_fittingInG_le_opiCoreInG π H
  have hbig_bot : ⁅opiCoreInG π H, opiCoreInG πᶜ H⁆ ≤ ⊥ := by
    rw [opiCoreInG_commutator_compl_eq_bot π H]
  exact le_bot_iff.mp ((Subgroup.commutator_mono hD_le le_rfl).trans hbig_bot)

/-- If a subgroup lies in `O_{π'}(H)`, then `O_π(F(H))` centralizes it. -/
theorem opiCoreInG_fittingInG_le_centralizer_of_le_opiCoreInG_compl [Finite G]
    (π : Set ℕ) {H K : Subgroup G}
    (hK : K ≤ opiCoreInG πᶜ H) :
    opiCoreInG π (fittingInG H) ≤ Subgroup.centralizer (K : Set G) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hcomm_le :
      ⁅opiCoreInG π (fittingInG H), K⁆ ≤
        ⁅opiCoreInG π (fittingInG H), opiCoreInG πᶜ H⁆ :=
    Subgroup.commutator_mono le_rfl hK
  have hbig_bot :
      ⁅opiCoreInG π (fittingInG H), opiCoreInG πᶜ H⁆ ≤ ⊥ := by
    rw [opiCoreInG_fittingInG_commutator_compl_eq_bot π H]
  exact le_bot_iff.mp (hcomm_le.trans hbig_bot)

/-- BG Proposition 1.10, packaged for the cyclic conjugation action on `F(M)`.

If the fixed subgroup `C_{F(M)}(<x>)` is self-centralizing in `F(M)` and `<x>` has
order coprime to `|F(M)|`, then `<x>` acts trivially on `F(M)`. -/
theorem zpowers_acts_trivially_on_fittingInG_of_centralizer_self [Finite G]
    {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥(fittingInG M)))
    (hCC :
      Subgroup.centralizer
        ((Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) : Set ↥(fittingInG M))
        ≤ (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M)) :
    ∀ a : ↥(Subgroup.zpowers x), ∀ f : ↥(fittingInG M),
      (conjActionOnFittingInG hxM a) f = f := by
  haveI : Group.IsNilpotent ↥(fittingInG M) := fittingInG_isNilpotent M
  have hCC_fixed : Subgroup.centralizer
      (Subgroup.fixedPointsOfMulAut (conjActionOnFittingInG hxM) : Set ↥(fittingInG M))
      ≤ Subgroup.fixedPointsOfMulAut (conjActionOnFittingInG hxM) := by
    rw [fixedPoints_conjActionOnFittingInG_eq hxM]
    exact hCC
  exact OddOrder.BG.Ch1.S01.coprime_nilpotent_acts_trivially_of_centralizer_self
    (A := ↥(Subgroup.zpowers x)) (G := ↥(fittingInG M))
    (φ := conjActionOnFittingInG hxM) hcop hCC_fixed

/-- If `<x>` acts trivially on `F(M)`, then its generator centralizes `F(M)`. -/
theorem mem_centralizer_fittingInG_of_zpowers_action_trivial {M : Subgroup G} {x : G}
    (hxM : x ∈ M)
    (htriv : ∀ a : ↥(Subgroup.zpowers x), ∀ f : ↥(fittingInG M),
      (conjActionOnFittingInG hxM a) f = f) :
    x ∈ Subgroup.centralizer (fittingInG M : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro y hy
  let a : ↥(Subgroup.zpowers x) := ⟨x, Subgroup.mem_zpowers x⟩
  let f : ↥(fittingInG M) := ⟨y, hy⟩
  have hfix := htriv a f
  have hfixG := congrArg Subtype.val hfix
  rw [conjActionOnFittingInG_apply] at hfixG
  have hcomm : x * y = y * x := by
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [hfixG]
  exact hcomm.symm

/-- The Prop 1.10 bridge in the form used in BG (8.3): the generator of a cyclic
subgroup satisfying the self-centralizer condition centralizes `F(M)`. -/
theorem mem_centralizer_fittingInG_of_centralizer_self_zpowers [Finite G]
    {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥(fittingInG M)))
    (hCC :
      Subgroup.centralizer
        ((Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) : Set ↥(fittingInG M))
        ≤ (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M)) :
    x ∈ Subgroup.centralizer (fittingInG M : Set G) :=
  mem_centralizer_fittingInG_of_zpowers_action_trivial hxM
    (zpowers_acts_trivially_on_fittingInG_of_centralizer_self hxM hcop hCC)

/-- With solvability of `M`, the same Prop 1.10 bridge places the generator inside
`F(M)` by the ambient self-centralizer of the Fitting subgroup. -/
theorem mem_fittingInG_of_centralizer_self_zpowers [Finite G]
    {M : Subgroup G} [IsSolvable ↥M] {x : G} (hxM : x ∈ M)
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥(fittingInG M)))
    (hCC :
      Subgroup.centralizer
        ((Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) : Set ↥(fittingInG M))
        ≤ (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M)) :
    x ∈ fittingInG M := by
  exact mem_fittingInG_of_mem_centralizer_fittingInG hxM
    (mem_centralizer_fittingInG_of_centralizer_self_zpowers hxM hcop hCC)

/-- A cyclic `π(F(M))`-complement subgroup has order coprime to `|F(M)|`. -/
theorem coprime_card_zpowers_fittingInG_of_isPiSubgroup_primesOf_compl [Finite G]
    {M : Subgroup G} {x : G}
    (hxpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ
      (Subgroup.zpowers x)) :
    Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥(fittingInG M)) :=
  (coprime_card_of_isPiSubgroup_of_isPiSubgroup_compl
    (π := OddOrder.BG.Ch2.S07.primesOf (fittingInG M)) (H := fittingInG M)
    (K := Subgroup.zpowers x)
    (fun r hr => by simpa [OddOrder.BG.Ch2.S07.primesOf] using hr) hxpi).symm

/-- BG (8.3) endpoint for a cyclic pi-complement element: under the Prop 1.10
self-centralizer condition, such an element is trivial. -/
theorem eq_one_of_centralizer_self_zpowers_of_isPiSubgroup_primesOf_compl [Finite G]
    {M : Subgroup G} [IsSolvable ↥M] {x : G} (hxM : x ∈ M)
    (hCC :
      Subgroup.centralizer
        ((Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) : Set ↥(fittingInG M))
        ≤ (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M))
    (hxpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ
      (Subgroup.zpowers x)) :
    x = 1 :=
  eq_one_of_mem_fittingInG_of_zpowers_isPiSubgroup_primesOf_compl
    (mem_fittingInG_of_centralizer_self_zpowers hxM
      (coprime_card_zpowers_fittingInG_of_isPiSubgroup_primesOf_compl hxpi) hCC) hxpi

/-- BG (8.3) criterion: if every cyclic pi-complement element in the ambient centralizer
satisfies the Prop 1.10 self-centralizer hypothesis, then the centralizer is a
`π(F(M))`-subgroup. -/
theorem centralizer_cFitting_isPiSubgroup_of_zpowers_centralizer_self [Finite G]
    {M A0 : Subgroup G} [IsSolvable ↥M]
    (hCentM : Subgroup.centralizer (cFittingInG M A0 : Set G) ≤ M)
    (hCC : ∀ {x : G}, x ∈ Subgroup.centralizer (cFittingInG M A0 : Set G) →
      Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ
        (Subgroup.zpowers x) →
      Subgroup.centralizer
        ((Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) : Set ↥(fittingInG M))
        ≤ (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M)) :
    Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))
      (Subgroup.centralizer (cFittingInG M A0 : Set G)) := by
  refine isPiSubgroup_of_forall_zpowers_isPiSubgroup_compl_eq_one ?_
  intro x hxC hxpi
  exact eq_one_of_centralizer_self_zpowers_of_isPiSubgroup_primesOf_compl
    (hCentM hxC) (hCC hxC hxpi) hxpi

/-- The center of `F(M)`, realized as a subgroup of the ambient group `G`. -/
def centerFittingInG (M : Subgroup G) : Subgroup G :=
  (Subgroup.center ↥(fittingInG M)).map (fittingInG M).subtype

/-- `Z(F(M))`, realized in `G`, lies inside `F(M)`. -/
theorem centerFittingInG_le_fittingInG (M : Subgroup G) :
    centerFittingInG M ≤ fittingInG M :=
  Subgroup.map_subtype_le _

/-- `Z(F(M))`, realized in `G`, lies inside `M`. -/
theorem centerFittingInG_le (M : Subgroup G) :
    centerFittingInG M ≤ M :=
  (centerFittingInG_le_fittingInG M).trans (fittingInG_le M)

/-- Elements of `F(M)` centralize the ambient center `Z(F(M))`. -/
theorem fittingInG_le_centralizer_centerFittingInG (M : Subgroup G) :
    fittingInG M ≤ Subgroup.centralizer (centerFittingInG M : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨zc, hzc, hzc_eq⟩ := hz
  have hzc_eqG : (zc : G) = z := hzc_eq
  have hcomm :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨x, hx⟩)
  simpa [hzc_eqG] using hcomm.symm

/-- The ambient realization of Z(F(M)) is commutative. -/
theorem centerFittingInG_isMulCommutative (M : Subgroup G) :
    IsMulCommutative ↥(centerFittingInG M) := by
  rw [centerFittingInG]
  exact Subgroup.map_isMulCommutative (Subgroup.center ↥(fittingInG M))
    (fittingInG M).subtype

/-- Every prime divisor of Fitting M divides the center of Fitting M. -/
theorem mem_primeFactors_centerFittingInG_of_mem_primeFactors_fittingInG [Finite G]
    {q : ℕ} [Fact q.Prime] {M : Subgroup G}
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors) :
    q ∈ (Nat.card ↥(centerFittingInG M)).primeFactors := by
  haveI : Group.IsNilpotent ↥(fittingInG M) := fittingInG_isNilpotent M
  rw [centerFittingInG, Subgroup.card_map_of_injective (fittingInG M).subtype_injective]
  exact Ch01.mem_primeFactors_center_of_isNilpotent hq

/-- The center of `F(M)`, viewed as a subgroup of `M`, is normal in `M`.

This is the ambient form of the elementary fact that the center of a normal subgroup is
normal.  It is used in BG (8.2), where nontrivial characteristic subgroups of `Z(F(M))`
have normalizer exactly `M`. -/
theorem centerFittingInG_subgroupOf_normal (M : Subgroup G) :
    ((centerFittingInG M).subgroupOf M).Normal := by
  let F : Subgroup G := fittingInG M
  let Z : Subgroup G := centerFittingInG M
  have hZF : Z ≤ F := by
    dsimp [Z]
    exact centerFittingInG_le_fittingInG M
  have hZM : Z ≤ M := by
    dsimp [Z]
    exact centerFittingInG_le M
  have hF_norm_M : M ≤ Subgroup.normalizer (F : Set G) := by
    dsimp [F]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (fittingInG_le M)).mp
      (fittingInG_subgroupOf_normal M)
  have hconj_mem : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := by
    intro m hm z hz
    have hzF : z ∈ F := hZF hz
    have hconjF : m * z * m⁻¹ ∈ F :=
      (Subgroup.mem_normalizer_iff.mp (hF_norm_M hm) z).mp hzF
    obtain ⟨zc, hzc, hzc_eq⟩ := hz
    have hzc_eqG : (zc : G) = z := hzc_eq
    refine ⟨⟨m * z * m⁻¹, hconjF⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro y
    apply Subtype.ext
    have hyF : (y : G) ∈ F := y.2
    have hyPrimeF : m⁻¹ * (y : G) * m ∈ F := by
      have hm_inv : m⁻¹ ∈ M := M.inv_mem hm
      simpa using (Subgroup.mem_normalizer_iff.mp (hF_norm_M hm_inv) (y : G)).mp hyF
    have hcomm :
        (m⁻¹ * (y : G) * m) * z = z * (m⁻¹ * (y : G) * m) := by
      have hcommPrime :
          (m⁻¹ * (y : G) * m) * (zc : G) =
            (zc : G) * (m⁻¹ * (y : G) * m) := by
        simpa using
          congrArg Subtype.val
            (Subgroup.mem_center_iff.mp hzc ⟨m⁻¹ * (y : G) * m, hyPrimeF⟩)
      simpa [hzc_eqG] using hcommPrime
    calc
      (y : G) * (m * z * m⁻¹) = m * ((m⁻¹ * (y : G) * m) * z) * m⁻¹ := by
        group
      _ = m * (z * (m⁻¹ * (y : G) * m)) * m⁻¹ := by rw [hcomm]
      _ = m * z * m⁻¹ * (y : G) := by group
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZM]
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact hconj_mem m hm z
  · intro hz
    have hback := hconj_mem m⁻¹ (M.inv_mem hm) (m * z * m⁻¹) hz
    have heq : m⁻¹ * (m * z * m⁻¹) * m⁻¹⁻¹ = z := by group
    rwa [heq] at hback

/-- The `q`-core of `Z(F(M))`, realized as a subgroup of the ambient group `G`. -/
def centerFittingOpCoreInG (q : ℕ) (M : Subgroup G) : Subgroup G :=
  opiCoreInG ({q} : Set ℕ) (centerFittingInG M)

/-- `O_q(Z(F(M)))`, realized in `G`, lies inside `Z(F(M))`. -/
theorem centerFittingOpCoreInG_le_centerFittingInG (q : ℕ) (M : Subgroup G) :
    centerFittingOpCoreInG q M ≤ centerFittingInG M :=
  opiCoreInG_le ({q} : Set ℕ) (centerFittingInG M)

/-- `O_q(Z(F(M)))`, realized in `G`, lies inside `M`. -/
theorem centerFittingOpCoreInG_le (q : ℕ) (M : Subgroup G) :
    centerFittingOpCoreInG q M ≤ M :=
  (centerFittingOpCoreInG_le_centerFittingInG q M).trans (centerFittingInG_le M)

/-- `O_q(Z(F(M)))`, viewed as a subgroup of `M`, is normal in `M`. -/
theorem centerFittingOpCoreInG_subgroupOf_normal (q : ℕ) (M : Subgroup G) :
    ((centerFittingOpCoreInG q M).subgroupOf M).Normal := by
  have hOM : centerFittingOpCoreInG q M ≤ M := centerFittingOpCoreInG_le q M
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hOM]
  have hMZ : M ≤ Subgroup.normalizer (centerFittingInG M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (centerFittingInG_le M)).mp
      (centerFittingInG_subgroupOf_normal M)
  exact le_normalizer_opiCoreInG_of_le_normalizer ({q} : Set ℕ) hMZ

/-- If q divides the order of Z(F(M)), then O_q(Z(F(M))) is nontrivial. -/
theorem centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_center [Finite G]
    {q : ℕ} [Fact q.Prime] {M : Subgroup G}
    (hq : q ∈ (Nat.card ↥(centerFittingInG M)).primeFactors) :
    centerFittingOpCoreInG q M ≠ ⊥ := by
  let Z : Subgroup G := centerFittingInG M
  let P : Sylow q ↥Z := default
  let N : Subgroup G := (P : Subgroup ↥Z).map Z.subtype
  have hq_dvd : q ∣ Nat.card ↥Z := (Nat.mem_primeFactors.mp hq).2.1
  have hP_ne : (P : Subgroup ↥Z) ≠ ⊥ := P.ne_bot_of_dvd_card hq_dvd
  have hN_ne : N ≠ ⊥ := by
    intro hN_bot
    exact hP_ne ((Subgroup.map_eq_bot_iff_of_injective (P : Subgroup ↥Z)
      Z.subtype_injective).mp hN_bot)
  haveI hZ_comm : IsMulCommutative ↥Z := by
    dsimp [Z]
    exact centerFittingInG_isMulCommutative M
  have hNZ : N ≤ Z := by
    dsimp [N]
    exact Subgroup.map_subtype_le _
  have hNnorm : (N.subgroupOf Z).Normal :=
    Subgroup.normal_of_isMulCommutative (N.subgroupOf Z)
  have hNpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) N := by
    dsimp [N]
    exact isPiSubgroup_singleton_of_isPGroup (P.isPGroup'.map Z.subtype)
  have hNle : N ≤ centerFittingOpCoreInG q M := by
    dsimp [centerFittingOpCoreInG, Z]
    exact le_opiCoreInG_of_normal_of_isPiSubgroup hNZ hNnorm hNpi
  intro hcore_bot
  apply hN_ne
  exact le_bot_iff.mp (by rw [← hcore_bot]; exact hNle)

/-- If q divides the order of Fitting M, then the q-core of its center is nontrivial. -/
theorem centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG [Finite G]
    {q : ℕ} [Fact q.Prime] {M : Subgroup G}
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors) :
    centerFittingOpCoreInG q M ≠ ⊥ :=
  centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_center
    (mem_primeFactors_centerFittingInG_of_mem_primeFactors_fittingInG hq)

/-- **BG (8.1), left inclusion**: `Z(F(M))` centralizes every subgroup contained in
`F(M)`, hence lies in the relative centralizer `C_{F(M)}(A₀)`. -/
theorem centerFittingInG_le_centralizer_inf {M A₀ : Subgroup G}
    (hA₀F : A₀ ≤ fittingInG M) :
    centerFittingInG M ≤ Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M := by
  refine le_inf ?_ (centerFittingInG_le_fittingInG M)
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨zc, hzc, hzc_eq⟩ := hz
  have hzc_eqG : (zc : G) = z := hzc_eq
  have hcomm :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨y, hA₀F hy⟩)
  simpa [hzc_eqG] using hcomm

/-- **BG (8.1), prime-support form**: `C_F(M)(A₀)` and `F(M)` have the same
prime divisors when `A₀ ≤ F(M)`. -/
theorem mem_primeFactors_cFitting_iff_mem_primeFactors_fittingInG [Finite G]
    {M A₀ : Subgroup G} (hA₀F : A₀ ≤ fittingInG M) {q : ℕ} :
    q ∈ (Nat.card ↥(Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M)).primeFactors ↔
      q ∈ (Nat.card ↥(fittingInG M)).primeFactors := by
  constructor
  · intro hq
    exact Nat.primeFactors_mono
      (Subgroup.card_dvd_of_le
        (inf_le_right : Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M ≤ fittingInG M))
      Nat.card_pos.ne' hq
  · intro hqF
    haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqF⟩
    have hqZ : q ∈ (Nat.card ↥(centerFittingInG M)).primeFactors :=
      mem_primeFactors_centerFittingInG_of_mem_primeFactors_fittingInG hqF
    exact Nat.primeFactors_mono
      (Subgroup.card_dvd_of_le (centerFittingInG_le_centralizer_inf hA₀F))
      Nat.card_pos.ne' hqZ

/-- **BG (8.1), `π`-notation form**: `π(C_F(M)(A₀)) = π(F(M))`. -/
theorem primesOf_cFitting_eq_primesOf_fittingInG [Finite G]
    {M A₀ : Subgroup G} (hA₀F : A₀ ≤ fittingInG M) :
    OddOrder.BG.Ch2.S07.primesOf
        (Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M) =
      OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
  ext q
  exact mem_primeFactors_cFitting_iff_mem_primeFactors_fittingInG hA₀F

/-- **`ℰ_p^*(H)` membership**: `A₀` は `H` の中で極大な `p`-elementary abelian 部分群
(`A₀ ≤ H` elem-ab で、`H` 内の elem-ab `B ⊇ A₀` は `A₀` に戻る)。 -/
def isMaxElemAbelianIn (p : ℕ) (A₀ H : Subgroup G) : Prop :=
  A₀.IsElementaryAbelian p ∧ A₀ ≤ H ∧
    ∀ B : Subgroup G, B.IsElementaryAbelian p → B ≤ H → A₀ ≤ B → B = A₀

/-- A maximal elementary abelian subgroup is elementary abelian. -/
theorem isMaxElemAbelianIn_isElementaryAbelian {p : ℕ} {A₀ H : Subgroup G}
    (hA₀ : isMaxElemAbelianIn p A₀ H) :
    A₀.IsElementaryAbelian p :=
  hA₀.1

/-- A maximal elementary abelian subgroup of `H` lies in `H`. -/
theorem isMaxElemAbelianIn_le {p : ℕ} {A₀ H : Subgroup G}
    (hA₀ : isMaxElemAbelianIn p A₀ H) :
    A₀ ≤ H :=
  hA₀.2.1

/-- A maximal elementary abelian subgroup of `F(M)` lies in its own centralizer inside
`F(M)`.  This is the formal start of BG (8.1). -/
theorem isMaxElemAbelianIn_le_centralizer_inf {p : ℕ} {M A₀ : Subgroup G}
    (hA₀ : isMaxElemAbelianIn p A₀ (fittingInG M)) :
    A₀ ≤ Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M := by
  refine le_inf ?_ (isMaxElemAbelianIn_le hA₀)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (hA₀.1.comm ⟨y, hy⟩ ⟨x, hx⟩)

/-- The `p`-complement core of `F(M)` is absorbed by the `p`-complement core of
`A = C_F(M)(A0)`. This is the formal `O_{p'}(F) ≤ O_{p'}(A)` part of BG (8.8). -/
theorem opiCoreInG_singleton_compl_fittingInG_le_opiCoreInG_singleton_compl_cFittingInG
    [Finite G] {p : ℕ} [Fact p.Prime] {M A0 : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M)) :
    opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M) ≤
      opiCoreInG ({p} : Set ℕ)ᶜ (cFittingInG M A0) := by
  let K : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M)
  change K ≤ opiCoreInG ({p} : Set ℕ)ᶜ (cFittingInG M A0)
  have hA0_le_OpF : A0 ≤ opiCoreInG ({p} : Set ℕ) (fittingInG M) :=
    le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
      (fittingInG_isNilpotent M) (isMaxElemAbelianIn_le hA0)
      hA0.1.isPGroup
  have hOpF_cent_K : opiCoreInG ({p} : Set ℕ) (fittingInG M) ≤
      Subgroup.centralizer (K : Set G) := by
    dsimp [K]
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact opiCoreInG_commutator_compl_eq_bot ({p} : Set ℕ) (fittingInG M)
  have hK_cent_A0 : K ≤ Subgroup.centralizer (A0 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hOpF_cent_K (hA0_le_OpF ha)) x hx).symm
  have hK_A : K ≤ cFittingInG M A0 := by
    refine le_inf hK_cent_A0 ?_
    dsimp [K]
    exact opiCoreInG_le ({p} : Set ℕ)ᶜ (fittingInG M)
  have hK_norm_A : (K.subgroupOf (cFittingInG M A0)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hK_A]
    have hA_le_F : cFittingInG M A0 ≤ fittingInG M := by
      dsimp [cFittingInG]
      exact inf_le_right
    have hF_norm_K : fittingInG M ≤ Subgroup.normalizer (K : Set G) := by
      dsimp [K]
      exact le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M)
    exact hA_le_F.trans hF_norm_K
  have hK_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ K := by
    dsimp [K]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M)
  exact le_opiCoreInG_of_normal_of_isPiSubgroup hK_A hK_norm_A hK_pi

/-- If `x` centralizes `C_F(M)(A0)`, then `C_F(M)(A0)` lies in
`C_F(M)(<x>)`. -/
theorem cFitting_le_centralizer_zpowers_inf_fittingInG_of_mem_centralizer
    {M A0 : Subgroup G} {x : G}
    (hxC : x ∈ Subgroup.centralizer (cFittingInG M A0 : Set G)) :
    cFittingInG M A0 ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M := by
  intro a haA
  have haA_saved : a ∈ cFittingInG M A0 := haA
  rw [cFittingInG, Subgroup.mem_inf] at haA
  refine ⟨?_, haA.2⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hcomm_eq : (a : G) * x = x * (a : G) :=
    Subgroup.mem_centralizer_iff.mp hxC (a : G) haA_saved
  have hcomm : Commute (a : G) x := hcomm_eq
  exact (hcomm.symm.zpow_left n).eq

/-- BG (8.3) self-centralizer bridge: for `A = C_F(M)(A0)`, an element of `C_G(A)`
satisfies the `C_F(C_F(<x>)) ≤ C_F(<x>)` input needed for Proposition 1.10. -/
theorem centralizer_zpowers_inf_fittingInG_self_of_mem_centralizer_cFitting
    {p : ℕ} {M A0 : Subgroup G} {x : G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hxC : x ∈ Subgroup.centralizer (cFittingInG M A0 : Set G)) :
    Subgroup.centralizer
        ((Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) : Set ↥(fittingInG M))
      ≤ (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) := by
  let C : Subgroup G := Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M
  have hA_le_C : cFittingInG M A0 ≤ C := by
    dsimp [C]
    exact cFitting_le_centralizer_zpowers_inf_fittingInG_of_mem_centralizer hxC
  have hA0A : A0 ≤ Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M :=
    isMaxElemAbelianIn_le_centralizer_inf hA0
  intro y hy
  rw [Subgroup.mem_subgroupOf]
  have hyA : (y : G) ∈ cFittingInG M A0 := by
    rw [cFittingInG, Subgroup.mem_inf]
    refine ⟨?_, y.2⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro a0 ha0
    let a0F : ↥(fittingInG M) := ⟨a0, (hA0A ha0).2⟩
    have ha0C : a0F ∈ C.subgroupOf (fittingInG M) := by
      rw [Subgroup.mem_subgroupOf]
      exact hA_le_C (by simpa [cFittingInG] using (hA0A ha0).1)
    have hcommF := Subgroup.mem_centralizer_iff.mp hy a0F ha0C
    exact congrArg Subtype.val hcommF
  exact hA_le_C hyA

/-- BG (8.3) packaged with the self-centralizer bridge for
`A = C_F(M)(A0)`: once the ambient centralizer is known to lie in `M`, it is a
`π(F(M))`-subgroup. -/
theorem centralizer_cFitting_isPiSubgroup_primesOf_fittingInG_of_le_maximal [Finite G]
    {p : ℕ} {M A0 : Subgroup G} [IsSolvable ↥M]
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hCentM : Subgroup.centralizer (cFittingInG M A0 : Set G) ≤ M) :
    Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))
      (Subgroup.centralizer (cFittingInG M A0 : Set G)) :=
  centralizer_cFitting_isPiSubgroup_of_zpowers_centralizer_self hCentM
    (fun hxC _hxpi =>
      centralizer_zpowers_inf_fittingInG_self_of_mem_centralizer_cFitting hA0 hxC)

/-- Maximality clause for `isMaxElemAbelianIn`. -/
theorem isMaxElemAbelianIn_eq_of_isElementaryAbelian_of_le {p : ℕ} {A₀ H B : Subgroup G}
    (hA₀ : isMaxElemAbelianIn p A₀ H) (hB : B.IsElementaryAbelian p) (hBH : B ≤ H)
    (hA₀B : A₀ ≤ B) :
    B = A₀ :=
  hA₀.2.2 B hB hBH hA₀B

/-- A maximal elementary abelian subgroup of `F(M)` is nontrivial when `p` divides
`|F(M)|`. -/
theorem isMaxElemAbelianIn_ne_bot_of_mem_primeFactors_fittingInG [Finite G]
    {p : ℕ} [Fact p.Prime] {M A₀ : Subgroup G}
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA₀ : isMaxElemAbelianIn p A₀ (fittingInG M)) :
    A₀ ≠ ⊥ := by
  intro hA₀_bot
  have hp_dvd : p ∣ Nat.card ↥(fittingInG M) := (Nat.mem_primeFactors.mp hp).2.1
  obtain ⟨x, hx_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(fittingInG M)) p hp_dvd
  let B₀ : Subgroup ↥(fittingInG M) := Subgroup.zpowers x
  let B : Subgroup G := B₀.map (fittingInG M).subtype
  have hB_card : Nat.card B = p := by
    rw [show B = B₀.map (fittingInG M).subtype from rfl,
      Subgroup.card_map_of_injective (fittingInG M).subtype_injective,
      show B₀ = Subgroup.zpowers x from rfl, Nat.card_zpowers, hx_order]
  have hB_elem : B.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hB_card
  have hB_le_F : B ≤ fittingInG M := by
    exact Subgroup.map_subtype_le B₀
  have hA₀_le_B : A₀ ≤ B := by
    rw [hA₀_bot]
    exact bot_le
  have hB_eq_A₀ : B = A₀ :=
    isMaxElemAbelianIn_eq_of_isElementaryAbelian_of_le hA₀ hB_elem hB_le_F hA₀_le_B
  have hB_ne_bot : B ≠ ⊥ := by
    intro hB_bot
    have hp_one : p = 1 := by
      rw [hB_bot, Subgroup.card_bot] at hB_card
      exact hB_card.symm
    exact (Fact.out : p.Prime).ne_one hp_one
  exact hB_ne_bot (hB_eq_A₀.trans hA₀_bot)

/-- The relative centralizer `C_F(M)(A₀)` is nontrivial under the hypotheses of BG (8.1). -/
theorem cFitting_ne_bot_of_isMaxElemAbelianIn [Finite G]
    {p : ℕ} [Fact p.Prime] {M A₀ : Subgroup G}
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA₀ : isMaxElemAbelianIn p A₀ (fittingInG M)) :
    Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M ≠ ⊥ := by
  have hA₀_ne : A₀ ≠ ⊥ :=
    isMaxElemAbelianIn_ne_bot_of_mem_primeFactors_fittingInG hp hA₀
  have hA₀_le :
      A₀ ≤ Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M :=
    isMaxElemAbelianIn_le_centralizer_inf hA₀
  intro hbot
  apply hA₀_ne
  exact le_bot_iff.mp (by simpa [hbot] using hA₀_le)

/-- The subgroup A0, restricted to C_F(M)(A0), lies in that relative centralizer's center. -/
theorem subgroupOf_cFitting_le_center (M A0 : Subgroup G) :
    A0.subgroupOf (Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M) ≤
      Subgroup.center ↥(Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M) := by
  let A : Subgroup G := Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M
  change A0.subgroupOf A ≤ Subgroup.center ↥A
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  rw [Subgroup.mem_subgroupOf] at hx
  have hycent : (y : G) ∈ Subgroup.centralizer (A0 : Set G) := y.2.1
  exact (Subgroup.mem_centralizer_iff.mp hycent (x : G) hx).symm

/-- If m(A0) >= 3, then m(Z(C_F(M)(A0))) >= 3. -/
theorem three_le_rank_center_cFitting_of_isMaxElemAbelianIn [Finite G]
    {p : ℕ} {M A0 : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0) :
    3 ≤ rank ↥(Subgroup.center ↥(Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M)) := by
  let A : Subgroup G := Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M
  have hA0A : A0 ≤ A := by
    dsimp [A]
    exact isMaxElemAbelianIn_le_centralizer_inf hA0
  have hA0sub_le_center : A0.subgroupOf A ≤ Subgroup.center ↥A := by
    dsimp [A]
    exact subgroupOf_cFitting_le_center M A0
  have hsub_rank : rank ↥(A0.subgroupOf A) ≤ rank ↥(Subgroup.center ↥A) :=
    rank_le_of_injective (Subgroup.inclusion_injective hA0sub_le_center)
  have hA0_rank_le_sub : rank ↥A0 ≤ rank ↥(A0.subgroupOf A) :=
    rank_le_of_injective
      (f := (Subgroup.subgroupOfEquivOfLe hA0A).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hA0A).symm.injective
  exact hm.trans (hA0_rank_le_sub.trans hsub_rank)

/-- **Simplicity normalizer fact**: in a minimal simple odd group, the normalizer of a nonidentity
subgroup `L` that is normal in a maximal subgroup `M` (and contained in `M`) is exactly `M`.  If
`N_G(L) = G` then `L ⊴ G`, contradicting simplicity (`L ≠ ⊥`, `L ≤ M < ⊤`); else `N_G(L)` lies in a
maximal, which must be `M` since `M ≤ N_G(L)`. -/
theorem normalizer_eq_of_normal_of_mem_maximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M L : Subgroup G} (hM : M ∈ maximalSubgroups G) (hLM : (L.subgroupOf M).Normal)
    (hLne : L ≠ ⊥) (hLleM : L ≤ M) :
    Subgroup.normalizer (L : Set G) = M := by
  haveI : IsSimpleGroup G := hG.simple
  have hMco : IsCoatom M := mem_maximalSubgroups.mp hM
  have hMleN : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLleM).mp hLM
  have hNne : Subgroup.normalizer (L : Set G) ≠ ⊤ := by
    intro hNtop
    have hLnormal : L.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases hLnormal.eq_bot_or_eq_top with hLbot | hLtop
    · exact hLne hLbot
    · have htop_le_M : ⊤ ≤ M := by
        rw [← hLtop]
        exact hLleM
      exact hMco.lt_top.ne (eq_top_iff.mpr htop_le_M)
  have hNleM : Subgroup.normalizer (L : Set G) ≤ M :=
    (isCoatom_iff_ge_of_le.mp hMco).2 _ hNne hMleN
  exact le_antisymm hNleM hMleN

/-- If a maximal subgroup `M` normalizes a nontrivial q-subgroup `Q`, then `Q` lies
inside `M`. -/
theorem le_maximal_of_le_normalizer_of_ne_bot_isPiSubgroup_singleton [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime]
    {M Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hQne : Q ≠ ⊥) (hQpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) Q) :
    Q ≤ M := by
  by_contra hQnot_le
  have hMco : IsCoatom M := mem_maximalSubgroups.mp hM
  have hMQtop : M ⊔ Q = ⊤ := by
    rcases hMco.le_iff.mp (le_sup_left : M ≤ M ⊔ Q) with htop | hsup_eq
    · exact htop
    · exfalso
      apply hQnot_le
      rw [← hsup_eq]
      exact le_sup_right
  have hsup_le_NQ : M ⊔ Q ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le hMQ Subgroup.le_normalizer
  have hNQtop : Subgroup.normalizer (Q : Set G) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hMQtop]
    exact hsup_le_NQ
  haveI : Q.Normal := Subgroup.normalizer_eq_top_iff.mp hNQtop
  rcases hG.simple.eq_bot_or_eq_top_of_normal Q inferInstance with hQbot | hQtop
  · exact hQne hQbot
  · have hQp : IsPGroup q ↥Q :=
      OddOrder.GroupTheory.isPGroup_of_isPiSubgroup_singleton hQpi
    have hGp : IsPGroup q G :=
      (hQtop ▸ hQp : IsPGroup q ↥(⊤ : Subgroup G)).of_surjective
        (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom
        Subgroup.topEquiv.surjective
    haveI : Group.IsNilpotent G := hGp.isNilpotent
    exact hG.notSolvable inferInstance

/-- **BG (8.2) normalizer localization**: if `O_q(Z(F(M)))` is nontrivial, then its
normalizer in the ambient minimal simple group is exactly the maximal subgroup `M`. -/
theorem normalizer_centerFittingOpCoreInG_eq_of_ne_bot [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hO_ne : centerFittingOpCoreInG q M ≠ ⊥) :
    Subgroup.normalizer (centerFittingOpCoreInG q M : Set G) = M :=
  normalizer_eq_of_normal_of_mem_maximal hG hM
    (centerFittingOpCoreInG_subgroupOf_normal q M) hO_ne (centerFittingOpCoreInG_le q M)

/-- BG (8.2), general centralizer localization: any subgroup containing a nontrivial
`O_q(Z(F(M)))` has ambient centralizer contained in `M`. -/
theorem centralizer_le_maximal_of_centerFittingOpCoreInG_le [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} {M B : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hO_ne : centerFittingOpCoreInG q M ≠ ⊥)
    (hOB : centerFittingOpCoreInG q M ≤ B) :
    Subgroup.centralizer (B : Set G) ≤ M := by
  have hcent_le_norm :
      Subgroup.centralizer (B : Set G) ≤
        Subgroup.normalizer (centerFittingOpCoreInG q M : Set G) :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hOB)).trans
      (Subgroup.centralizer_le_normalizer (centerFittingOpCoreInG q M : Set G))
  simpa [normalizer_centerFittingOpCoreInG_eq_of_ne_bot hG hM hO_ne]
    using hcent_le_norm

/-- BG (8.2), prime-factor form of the general centralizer localization. -/
theorem centralizer_le_maximal_of_centerFittingOpCoreInG_le_fitting_primeFactor [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M B : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hOB : centerFittingOpCoreInG q M ≤ B) :
    Subgroup.centralizer (B : Set G) ≤ M :=
  centralizer_le_maximal_of_centerFittingOpCoreInG_le hG hM
    (centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hq) hOB

/-- **BG (8.2), centralizer localization form**: if `O_q(Z(F(M)))` is nontrivial,
then the ambient centralizer of `C_{F(M)}(A₀)` lies in `M`. -/
theorem centralizer_cFitting_le_maximal_of_centerFittingOpCore_ne [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} {M A₀ : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hA₀F : A₀ ≤ fittingInG M)
    (hO_ne : centerFittingOpCoreInG q M ≠ ⊥) :
    Subgroup.centralizer ((Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M : Subgroup G) : Set G)
      ≤ M := by
  let A : Subgroup G := Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M
  have hO_le_A : centerFittingOpCoreInG q M ≤ A :=
    (centerFittingOpCoreInG_le_centerFittingInG q M).trans
      (centerFittingInG_le_centralizer_inf hA₀F)
  have hcent_le_norm :
      Subgroup.centralizer (A : Set G) ≤
        Subgroup.normalizer (centerFittingOpCoreInG q M : Set G) := by
    exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hO_le_A)).trans
      (Subgroup.centralizer_le_normalizer (centerFittingOpCoreInG q M : Set G))
  simpa [A, normalizer_centerFittingOpCoreInG_eq_of_ne_bot hG hM hO_ne]
    using hcent_le_norm

/-- BG (8.2), prime-factor form: if q divides |Z(F(M))|, then the ambient
centralizer of C_F(M)(A0) lies in M. -/
theorem centralizer_cFitting_le_maximal_of_centerFitting_primeFactor [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hA0F : A0 ≤ fittingInG M)
    (hq : q ∈ (Nat.card ↥(centerFittingInG M)).primeFactors) :
    Subgroup.centralizer ((Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M : Subgroup G) : Set G)
      ≤ M :=
  centralizer_cFitting_le_maximal_of_centerFittingOpCore_ne hG hM hA0F
    (centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_center hq)

/-- BG (8.2), Fitting-prime-factor form. -/
theorem centralizer_cFitting_le_maximal_of_fitting_primeFactor [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hA0F : A0 ≤ fittingInG M)
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors) :
    Subgroup.centralizer ((Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M : Subgroup G) : Set G)
      ≤ M :=
  centralizer_cFitting_le_maximal_of_centerFitting_primeFactor hG hM hA0F
    (mem_primeFactors_centerFittingInG_of_mem_primeFactors_fittingInG hq)

private theorem exists_primeFactor_ne_of_not_isPGroup {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (hHnot : ¬ IsPGroup p H) :
    ∃ q, q ∈ (Nat.card H).primeFactors ∧ q ≠ p := by
  by_contra h
  apply hHnot
  rw [IsPGroup.iff_card]
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
  intro q hq_prime hq_dvd
  by_contra hq_ne
  exact h ⟨q, Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd, Nat.card_pos.ne'⟩, hq_ne⟩

private theorem exists_primeFactor_ne_of_mem_primeFactor_not_isPGroup {H : Type*}
    [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card H).primeFactors) (hHnot : ¬ IsPGroup p H) (q : ℕ) :
    ∃ r, r ∈ (Nat.card H).primeFactors ∧ r ≠ q := by
  by_cases hqp : q = p
  · obtain ⟨r, hr, hrp⟩ := exists_primeFactor_ne_of_not_isPGroup hHnot
    exact ⟨r, hr, fun hrq => hrp (hrq.trans hqp)⟩
  · exact ⟨p, hp, fun hpq => hqp hpq.symm⟩

/-- If Fitting M is not a p-group, BG (8.2) supplies a prime q whose center-core
localizes the ambient centralizer of C_F(M)(A0) inside M. -/
theorem centralizer_cFitting_le_maximal_of_not_isPGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hA0F : A0 ≤ fittingInG M)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M)) :
    Subgroup.centralizer ((Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M : Subgroup G) : Set G)
      ≤ M := by
  obtain ⟨q, hqF, _⟩ := exists_primeFactor_ne_of_not_isPGroup hFnp
  haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqF⟩
  exact centralizer_cFitting_le_maximal_of_fitting_primeFactor hG hM hA0F hqF

/-- BG (8.3) under the hypotheses used in Theorem 8.1(a): in the non-`p`-group case,
the ambient centralizer of `C_F(M)(A0)` is a `π(C_F(M)(A0))`-subgroup. -/
theorem centralizer_cFitting_isPiSubgroup_of_not_pGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M)) :
    Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))
      (Subgroup.centralizer (cFittingInG M A0 : Set G)) := by
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hA0F : A0 ≤ fittingInG M := isMaxElemAbelianIn_le hA0
  have hPrimes :
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) =
        OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    dsimp [cFittingInG]
    exact primesOf_cFitting_eq_primesOf_fittingInG hA0F
  have hCentM : Subgroup.centralizer (cFittingInG M A0 : Set G) ≤ M :=
    centralizer_cFitting_le_maximal_of_not_isPGroup hG hM hA0F hFnp
  rw [hPrimes]
  exact centralizer_cFitting_isPiSubgroup_primesOf_fittingInG_of_le_maximal hA0 hCentM

/-- BG (8.3) in `K`-notation: in the non-`p`-group case, the complement core
`O_{π(A)^c}(C_G(A))` is trivial for `A = C_F(M)(A0)`. -/
theorem kSubgroup_cFittingInG_eq_bot_of_not_pGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M)) :
    OddOrder.BG.Ch2.S07.kSubgroup (cFittingInG M A0) = ⊥ :=
  OddOrder.BG.Ch2.S07.kSubgroup_eq_bot_of_centralizer_isPiSubgroup
    (centralizer_cFitting_isPiSubgroup_of_not_pGroup hG hM hA0 hFnp)

/-- If `H` is a `π`-subgroup, then every member of `ℋ_X(A;π-complement)`
meets `H` trivially. -/
theorem hInvariant_inf_eq_bot_of_isPiSubgroup [Finite G] {π : Set ℕ}
    {A H X Y : Subgroup G} (hHpi : Subgroup.IsPiSubgroup π H)
    (hY : Y ∈ hInvariant X A πᶜ) :
    Y ⊓ H = ⊥ := by
  have hHY : H ⊓ Y = ⊥ :=
    inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl hHpi (hInvariant_isPiSubgroup hY)
  simpa [inf_comm] using hHY

/-- If `C_G(A)` is a `π(A)`-subgroup, then every member of `ℋ_X(A;π(A)-complement)`
meets `C_G(A)` trivially. -/
theorem hInvariant_inf_centralizer_eq_bot_of_centralizer_isPiSubgroup [Finite G]
    {A X Y : Subgroup G}
    (hCpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf A)
      (Subgroup.centralizer (A : Set G)))
    (hY : Y ∈ hInvariant X A (OddOrder.BG.Ch2.S07.primesOf A)ᶜ) :
    Y ⊓ Subgroup.centralizer (A : Set G) = ⊥ :=
  hInvariant_inf_eq_bot_of_isPiSubgroup hCpi hY

/-- BG (8.4), first intersection form: in the non-p-group case, every
`A = C_F(M)(A0)`-invariant `π(A)`-complement subgroup has trivial intersection with `C_G(A)`. -/
theorem hInvariant_inf_centralizer_cFittingInG_eq_bot_of_not_pGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {M A0 X Y : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Y ⊓ Subgroup.centralizer (cFittingInG M A0 : Set G) = ⊥ :=
  hInvariant_inf_centralizer_eq_bot_of_centralizer_isPiSubgroup
    (centralizer_cFitting_isPiSubgroup_of_not_pGroup hG hM hA0 hFnp) hY

/-- BG (8.4), Fitting intersection form: every `A = C_F(M)(A0)`-invariant
`π(A)`-complement subgroup has trivial intersection with `F(M)`. -/
theorem hInvariant_inf_fittingInG_cFittingInG_eq_bot [Finite G]
    {p : ℕ} {M A0 X Y : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Y ⊓ fittingInG M = ⊥ := by
  have hA0F : A0 ≤ fittingInG M := isMaxElemAbelianIn_le hA0
  have hPrimes :
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) =
        OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    dsimp [cFittingInG]
    exact primesOf_cFitting_eq_primesOf_fittingInG hA0F
  have hFpi : Subgroup.IsPiSubgroup
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0)) (fittingInG M) := by
    rw [hPrimes]
    intro r hr
    simpa [OddOrder.BG.Ch2.S07.primesOf] using hr
  exact hInvariant_inf_eq_bot_of_isPiSubgroup hFpi hY

/-- BG (8.4), centralizer step: for `q ∈ π(F(M))`, the subgroup
`C_Y(O_q(Z(F(M))))` centralizes `A = C_F(M)(A0)` for every `A`-invariant
`π(A)`-complement subgroup `Y`. -/
theorem centralizer_centerFittingOpCoreInG_inf_hInvariant_le_centralizer_cFittingInG
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact q.Prime]
    {M A0 X Y : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Subgroup.centralizer (centerFittingOpCoreInG q M : Set G) ⊓ Y ≤
      Subgroup.centralizer (cFittingInG M A0 : Set G) := by
  let A : Subgroup G := cFittingInG M A0
  let C : Subgroup G := Subgroup.centralizer (centerFittingOpCoreInG q M : Set G) ⊓ Y
  change C ≤ Subgroup.centralizer (A : Set G)
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hC_le_M : C ≤ M := by
    dsimp [C]
    exact inf_le_left.trans
      (centralizer_le_maximal_of_centerFittingOpCoreInG_le_fitting_primeFactor
        hG hM hq le_rfl)
  have hA_le_F : A ≤ fittingInG M := by
    dsimp [A, cFittingInG]
    exact inf_le_right
  have hM_norm_F : M ≤ Subgroup.normalizer (fittingInG M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (fittingInG_le M)).mp
      (fittingInG_subgroupOf_normal M)
  have hC_norm_F : C ≤ Subgroup.normalizer (fittingInG M : Set G) :=
    hC_le_M.trans hM_norm_F
  have hcomm_le_Y : ⁅C, A⁆ ≤ Y := by
    have hYA : ⁅Y, A⁆ ≤ Y :=
      OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer (hInvariant_le_normalizer hY)
    exact (Subgroup.commutator_mono (by dsimp [C]; exact inf_le_right) le_rfl).trans hYA
  have hcomm_le_F : ⁅C, A⁆ ≤ fittingInG M := by
    rw [Subgroup.commutator_comm C A]
    exact (Subgroup.commutator_mono hA_le_F le_rfl).trans
      (OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hC_norm_F)
  have hcomm_le_YF : ⁅C, A⁆ ≤ Y ⊓ fittingInG M := by
    intro x hx
    exact ⟨hcomm_le_Y hx, hcomm_le_F hx⟩
  exact le_bot_iff.mp (by
    rw [← hInvariant_inf_fittingInG_cFittingInG_eq_bot hA0 hY]
    exact hcomm_le_YF)

/-- BG (8.4), centralizer vanishing in the non-p-group case: for `q ∈ π(F(M))`,
`C_Y(O_q(Z(F(M)))) = 1`. -/
theorem centralizer_centerFittingOpCoreInG_inf_hInvariant_eq_bot_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 X Y : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Subgroup.centralizer (centerFittingOpCoreInG q M : Set G) ⊓ Y = ⊥ := by
  have hC_le_cent :=
    centralizer_centerFittingOpCoreInG_inf_hInvariant_le_centralizer_cFittingInG
      hG hM hA0 hq hY
  have hY_cent_bot :=
    hInvariant_inf_centralizer_cFittingInG_eq_bot_of_not_pGroup hG hM hA0 hFnp hY
  exact le_bot_iff.mp (by
    rw [← hY_cent_bot]
    exact le_inf inf_le_right hC_le_cent)

/-- Coprime fixed-point decomposition in ambient subgroup form: if `B` normalizes `Y`,
acts coprimely on it, and has no nontrivial fixed point in `Y`, then
`Y <= ⁅B, Y⁆`. This is the subgroup version of BG Prop. 1.6(a) used in BG (8.4). -/
theorem le_commutator_of_coprime_inf_centralizer_eq_bot [Finite G]
    {B Y : Subgroup G} [IsSolvable ↥B] (hBY : B ≤ Subgroup.normalizer Y)
    (hcop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥Y))
    (hfixed : Y ⊓ Subgroup.centralizer (B : Set G) = ⊥) :
    Y ≤ ⁅B, Y⁆ := by
  classical
  have hY_inv : Ch03.IsAInvariant (OddOrder.BG.Ch2.S07.conjAction B) Y :=
    OddOrder.BG.Ch2.S07.isAInvariant_conjAction_iff.mpr hBY
  have htop := OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
    (φ := hY_inv.restrict) hcop (Or.inl inferInstance)
  rw [← Subgroup.subgroupOf_eq_top, eq_top_iff, ← htop, sup_le_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx_fixed : (x : G) ∈ Y ⊓ Subgroup.centralizer (B : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hval := congrArg Subtype.val
        (Subgroup.mem_fixedPointsOfMulAut.mp hx ⟨b, hb⟩)
      rw [Ch03.IsAInvariant.restrict_apply_val] at hval
      simp only [OddOrder.BG.Ch2.S07.conjAction, MonoidHom.comp_apply,
        Subgroup.coe_subtype, MulAut.conj_apply] at hval
      exact mul_inv_eq_iff_eq_mul.mp hval
    have hx_one : (x : G) = 1 := by
      simpa [hfixed] using hx_fixed
    rw [hx_one]
    exact Subgroup.one_mem _
  · rw [OddOrder.Isaacs.Ch04.actionCommutator_le_iff]
    intro a g
    rw [Subgroup.mem_subgroupOf]
    have hgen : (((hY_inv.restrict a) g * g⁻¹ : ↥Y) : G)
        = (a : G) * (g : G) * (a : G)⁻¹ * (g : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Ch03.IsAInvariant.restrict_apply_val]
      simp only [OddOrder.BG.Ch2.S07.conjAction, MonoidHom.comp_apply,
        Subgroup.coe_subtype, MulAut.conj_apply]
    rw [hgen]
    exact Subgroup.commutator_mem_commutator a.2 g.2

/-- The central q-core `O_q(Z(F(M)))` is solvable, since it lies in the center of `F(M)`. -/
theorem centerFittingOpCoreInG_isSolvable (q : ℕ) (M : Subgroup G) :
    IsSolvable ↥(centerFittingOpCoreInG q M) := by
  haveI : IsMulCommutative ↥(centerFittingInG M) := centerFittingInG_isMulCommutative M
  exact isSolvable_of_comm fun a b => by
    apply Subtype.ext
    exact setLike_mul_comm
      (centerFittingOpCoreInG_le_centerFittingInG q M a.2)
      (centerFittingOpCoreInG_le_centerFittingInG q M b.2)

/-- `O_q(Z(F(M)))` lies in `C_F(M)(A0)` whenever `A0 ≤ F(M)`. -/
theorem centerFittingOpCoreInG_le_cFittingInG {p q : ℕ} {M A0 : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M)) :
    centerFittingOpCoreInG q M ≤ cFittingInG M A0 :=
  (centerFittingOpCoreInG_le_centerFittingInG q M).trans
    (centerFittingInG_le_centralizer_inf (isMaxElemAbelianIn_le hA0))

/-- `O_q(Z(F(M)))` lies in the q-core of `C_F(M)(A0)`. -/
theorem centerFittingOpCoreInG_le_opiCoreInG_cFittingInG_singleton
    [Finite G] {p q : ℕ} {M A0 : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M)) :
    centerFittingOpCoreInG q M ≤ opiCoreInG ({q} : Set ℕ) (cFittingInG M A0) := by
  have hBA : centerFittingOpCoreInG q M ≤ cFittingInG M A0 :=
    centerFittingOpCoreInG_le_cFittingInG (q := q) hA0
  have hBnorm : ((centerFittingOpCoreInG q M).subgroupOf (cFittingInG M A0)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBA]
    have hA_le_M : cFittingInG M A0 ≤ M := by
      dsimp [cFittingInG]
      exact inf_le_right.trans (fittingInG_le M)
    have hM_norm_B : M ≤ Subgroup.normalizer (centerFittingOpCoreInG q M : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (centerFittingOpCoreInG_le q M)).mp
        (centerFittingOpCoreInG_subgroupOf_normal q M)
    exact hA_le_M.trans hM_norm_B
  have hBpi_q : Subgroup.IsPiSubgroup ({q} : Set ℕ) (centerFittingOpCoreInG q M) := by
    dsimp [centerFittingOpCoreInG]
    exact isPiSubgroup_opiCoreInG ({q} : Set ℕ) (centerFittingInG M)
  exact le_opiCoreInG_of_normal_of_isPiSubgroup hBA hBnorm hBpi_q

/-- If `r ≠ q`, then the central `r`-core of `F(M)` lies in the `q`-complement
core of `C_F(M)(A0)`. This is the `A_r ≤ O_{q'}(A)` input for BG (8.7). -/
theorem centerFittingOpCoreInG_le_opiCoreInG_cFittingInG_singleton_compl_of_ne
    [Finite G] {p q r : ℕ} {M A0 : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M)) (hqr : q ≠ r) :
    centerFittingOpCoreInG r M ≤ opiCoreInG ({q} : Set ℕ)ᶜ (cFittingInG M A0) := by
  have hBA : centerFittingOpCoreInG r M ≤ cFittingInG M A0 :=
    centerFittingOpCoreInG_le_cFittingInG (q := r) hA0
  have hBnorm : ((centerFittingOpCoreInG r M).subgroupOf (cFittingInG M A0)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBA]
    have hA_le_M : cFittingInG M A0 ≤ M := by
      dsimp [cFittingInG]
      exact inf_le_right.trans (fittingInG_le M)
    have hM_norm_B : M ≤ Subgroup.normalizer (centerFittingOpCoreInG r M : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (centerFittingOpCoreInG_le r M)).mp
        (centerFittingOpCoreInG_subgroupOf_normal r M)
    exact hA_le_M.trans hM_norm_B
  have hBpi_r : Subgroup.IsPiSubgroup ({r} : Set ℕ) (centerFittingOpCoreInG r M) := by
    dsimp [centerFittingOpCoreInG]
    exact isPiSubgroup_opiCoreInG ({r} : Set ℕ) (centerFittingInG M)
  have hBpi_qcompl : Subgroup.IsPiSubgroup ({q} : Set ℕ)ᶜ (centerFittingOpCoreInG r M) := by
    refine hBpi_r.mono ?_
    intro s hs hsq
    rw [Set.mem_singleton_iff] at hs hsq
    exact hqr (hsq.symm.trans hs)
  exact le_opiCoreInG_of_normal_of_isPiSubgroup hBA hBnorm hBpi_qcompl

/-- BG (8.2) applied to `O_{q'}(C_F(M)(A0))`: if `r ≠ q` is another Fitting
prime, then the centralizer of this `q`-complement core lies in `M`. -/
theorem centralizer_opiCoreInG_cFittingInG_singleton_compl_le_maximal_of_ne
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q r : ℕ} {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hr : r ∈ (Nat.card ↥(fittingInG M)).primeFactors) (hqr : q ≠ r) :
    Subgroup.centralizer (opiCoreInG ({q} : Set ℕ)ᶜ (cFittingInG M A0) : Set G) ≤ M := by
  haveI : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
  exact centralizer_le_maximal_of_centerFittingOpCoreInG_le hG hM
    (centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hr)
    (centerFittingOpCoreInG_le_opiCoreInG_cFittingInG_singleton_compl_of_ne hA0 hqr)

/-- BG (8.2) applied to `O_{q'}(C_F(M)(A0))` in the non-`p`-group case. -/
theorem centralizer_opiCoreInG_cFittingInG_singleton_compl_le_maximal_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime]
    {M A0 : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (_hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors) :
    Subgroup.centralizer (opiCoreInG ({q} : Set ℕ)ᶜ (cFittingInG M A0) : Set G) ≤ M := by
  obtain ⟨r, hr, hrq⟩ :=
    exists_primeFactor_ne_of_mem_primeFactor_not_isPGroup
      (H := ↥(fittingInG M)) hp hFnp q
  exact centralizer_opiCoreInG_cFittingInG_singleton_compl_le_maximal_of_ne
    hG hM hA0 hr (fun hqr => hrq hqr.symm)

/-- BG (8.7), conditional endpoint: once `O_{q'}(C_F(M)(A0))` is absorbed by
`O_{q'}(H)`, the q-core of `F(H)` lies in the original maximal subgroup `M`. -/
theorem opiCoreInG_fittingInG_singleton_le_maximal_of_cFittingInG_compl_le_opiCoreInG_compl
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hcore : opiCoreInG ({q} : Set ℕ)ᶜ (cFittingInG M A0) ≤
      opiCoreInG ({q} : Set ℕ)ᶜ H) :
    opiCoreInG ({q} : Set ℕ) (fittingInG H) ≤ M := by
  have hcent :
      opiCoreInG ({q} : Set ℕ) (fittingInG H) ≤
        Subgroup.centralizer
          (opiCoreInG ({q} : Set ℕ)ᶜ (cFittingInG M A0) : Set G) :=
    opiCoreInG_fittingInG_le_centralizer_of_le_opiCoreInG_compl ({q} : Set ℕ) hcore
  exact hcent.trans
    (centralizer_opiCoreInG_cFittingInG_singleton_compl_le_maximal_of_not_pGroup
      hG hM hp hA0 hFnp hq)

/-- Members of `ℋ_X(C_F(M)(A0); π(C_F(M)(A0))^c)` are normalized by
`O_q(Z(F(M)))`. -/
theorem centerFittingOpCoreInG_le_normalizer_of_hInvariant
    {p q : ℕ} {M A0 X Y : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    centerFittingOpCoreInG q M ≤ Subgroup.normalizer Y :=
  (centerFittingOpCoreInG_le_cFittingInG (q := q) hA0).trans
    (hInvariant_le_normalizer hY)

/-- For `q ∈ π(F(M))`, the central q-core `O_q(Z(F(M)))` is a
`π(C_F(M)(A0))`-subgroup. -/
theorem centerFittingOpCoreInG_isPiSubgroup_primesOf_cFittingInG [Finite G]
    {p q : ℕ} [Fact q.Prime] {M A0 : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors) :
    Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))
      (centerFittingOpCoreInG q M) := by
  have hA0F : A0 ≤ fittingInG M := isMaxElemAbelianIn_le hA0
  have hPrimes :
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) =
        OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    dsimp [cFittingInG]
    exact primesOf_cFitting_eq_primesOf_fittingInG hA0F
  have hBq : Subgroup.IsPiSubgroup ({q} : Set ℕ) (centerFittingOpCoreInG q M) := by
    dsimp [centerFittingOpCoreInG]
    exact isPiSubgroup_opiCoreInG ({q} : Set ℕ) (centerFittingInG M)
  intro r hr
  have hrq : r ∈ ({q} : Set ℕ) := hBq r hr
  rw [Set.mem_singleton_iff] at hrq
  rw [hrq, hPrimes]
  simpa [OddOrder.BG.Ch2.S07.primesOf] using hq

/-- The action of `O_q(Z(F(M)))` on an `ℋ`-member for the complementary prime set is
coprime. -/
theorem coprime_card_centerFittingOpCoreInG_hInvariant [Finite G]
    {p q : ℕ} [Fact q.Prime] {M A0 X Y : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Nat.Coprime (Nat.card ↥(centerFittingOpCoreInG q M)) (Nat.card ↥Y) :=
  coprime_card_of_isPiSubgroup_of_isPiSubgroup_compl
    (centerFittingOpCoreInG_isPiSubgroup_primesOf_cFittingInG hA0 hq)
    (hInvariant_isPiSubgroup hY)

/-- BG (8.4), commutator form: in the non-p-group case, every
`π(C_F(M)(A0))`-complement `ℋ`-member is generated by its commutators with
`O_q(Z(F(M)))`, for each `q ∈ π(F(M))`. -/
theorem hInvariant_le_commutator_centerFittingOpCoreInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 X Y : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Y ≤ ⁅centerFittingOpCoreInG q M, Y⁆ := by
  have hfixed : Y ⊓
      Subgroup.centralizer (centerFittingOpCoreInG q M : Set G) = ⊥ := by
    simpa [inf_comm] using
      centralizer_centerFittingOpCoreInG_inf_hInvariant_eq_bot_of_not_pGroup
        hG hM hA0 hFnp hq hY
  haveI : IsSolvable ↥(centerFittingOpCoreInG q M) :=
    centerFittingOpCoreInG_isSolvable q M
  exact le_commutator_of_coprime_inf_centralizer_eq_bot
    (centerFittingOpCoreInG_le_normalizer_of_hInvariant (q := q) hA0 hY)
    (coprime_card_centerFittingOpCoreInG_hInvariant hA0 hq hY) hfixed

/-- If `R` is a q-subgroup of `X`, then the q'-core of `N_X(R)` lies in the q'-core
of `C_X(R)`. The point is that `K = O_{q'}(N_X(R))` normalizes `R`, while `R`
normalizes `K`; hence `[K,R]` lies in both the q'-group `K` and the q-group `R`. -/
theorem opiCoreInG_singleton_compl_normalizer_inf_le_centralizer_inf
    [Finite G] {q : ℕ} [Fact q.Prime] {R X : Subgroup G}
    (hRX : R ≤ X) (hRpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) R) :
    opiCoreInG ({q} : Set ℕ)ᶜ (Subgroup.normalizer (R : Set G) ⊓ X) ≤
      opiCoreInG ({q} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G) ⊓ X) := by
  let N : Subgroup G := Subgroup.normalizer (R : Set G) ⊓ X
  let C : Subgroup G := Subgroup.centralizer (R : Set G) ⊓ X
  let K : Subgroup G := opiCoreInG ({q} : Set ℕ)ᶜ N
  have hKN : K ≤ N := opiCoreInG_le ({q} : Set ℕ)ᶜ N
  have hKX : K ≤ X := hKN.trans inf_le_right
  have hK_norm_R : K ≤ Subgroup.normalizer (R : Set G) := hKN.trans inf_le_left
  have hRN : R ≤ N := by
    intro r hr
    exact ⟨Subgroup.le_normalizer hr, hRX hr⟩
  have hN_norm_K : N ≤ Subgroup.normalizer (K : Set G) := by
    dsimp [K]
    exact le_normalizer_opiCoreInG ({q} : Set ℕ)ᶜ N
  have hR_norm_K : R ≤ Subgroup.normalizer (K : Set G) := hRN.trans hN_norm_K
  have hcomm_le_K : ⁅K, R⁆ ≤ K :=
    OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hR_norm_K
  have hcomm_le_R : ⁅K, R⁆ ≤ R := by
    rw [Subgroup.commutator_comm K R]
    exact OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hK_norm_R
  have hKpi : Subgroup.IsPiSubgroup ({q} : Set ℕ)ᶜ K := by
    dsimp [K]
    exact isPiSubgroup_opiCoreInG ({q} : Set ℕ)ᶜ N
  have hcomm_pi : Subgroup.IsPiSubgroup ({q} : Set ℕ)ᶜ ⁅K, R⁆ := by
    intro s hs
    exact hKpi s
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hcomm_le_K) Nat.card_pos.ne' hs)
  have hcomm_bot : ⁅K, R⁆ = ⊥ :=
    eq_bot_of_le_of_isPiSubgroup_of_isPiSubgroup_compl hcomm_le_R hRpi hcomm_pi
  have hK_cent : K ≤ Subgroup.centralizer (R : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hcomm_bot
  have hKC : K ≤ C := by
    intro x hx
    exact ⟨hK_cent hx, hKX hx⟩
  have hC_le_N : C ≤ N := by
    intro x hx
    exact ⟨Subgroup.centralizer_le_normalizer (R : Set G) hx.1, hx.2⟩
  have hKnormC : (K.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKC]
    exact hC_le_N.trans hN_norm_K
  exact le_opiCoreInG_of_normal_of_isPiSubgroup hKC hKnormC hKpi

/-- BG (8.5), central-core form: for distinct primes `q,r ∈ π(F(M))`, the central
r-core `O_r(Z(F(M)))` lies in `O_{q'}(X)` whenever `X` is solvable and contains
`C_F(M)(A0)`. -/
theorem centerFittingOpCoreInG_le_opiCoreInG_singleton_compl_of_ne
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q r : ℕ}
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] {M A0 X : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hXsolv : IsSolvable ↥X)
    (hAX : cFittingInG M A0 ≤ X)
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hr : r ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hqr : q ≠ r) :
    centerFittingOpCoreInG r M ≤ opiCoreInG ({q} : Set ℕ)ᶜ X := by
  let Rq : Subgroup G := centerFittingOpCoreInG q M
  let Br : Subgroup G := centerFittingOpCoreInG r M
  let Nq : Subgroup G := Subgroup.normalizer (Rq : Set G) ⊓ X
  have hRqX : Rq ≤ X :=
    (centerFittingOpCoreInG_le_cFittingInG (q := q) hA0).trans hAX
  have hBrX : Br ≤ X :=
    (centerFittingOpCoreInG_le_cFittingInG (q := r) hA0).trans hAX
  have hRqpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) Rq := by
    dsimp [Rq, centerFittingOpCoreInG]
    exact isPiSubgroup_opiCoreInG ({q} : Set ℕ) (centerFittingInG M)
  have hBrpi_r : Subgroup.IsPiSubgroup ({r} : Set ℕ) Br := by
    dsimp [Br, centerFittingOpCoreInG]
    exact isPiSubgroup_opiCoreInG ({r} : Set ℕ) (centerFittingInG M)
  have hBrpi_qcompl : Subgroup.IsPiSubgroup ({q} : Set ℕ)ᶜ Br := by
    refine hBrpi_r.mono ?_
    intro s hs hsq
    rw [Set.mem_singleton_iff] at hs hsq
    exact hqr (hsq.symm.trans hs)
  have hNq_eq_M : Subgroup.normalizer (Rq : Set G) = M := by
    dsimp [Rq]
    exact normalizer_centerFittingOpCoreInG_eq_of_ne_bot hG hM
      (centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hq)
  have hBrNq : Br ≤ Nq := by
    refine le_inf ?_ hBrX
    intro x hx
    simpa [hNq_eq_M] using centerFittingOpCoreInG_le r M hx
  have hBrnormNq : (Br.subgroupOf Nq).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBrNq]
    have hNq_le_M : Nq ≤ M := by
      intro x hx
      simpa [hNq_eq_M] using hx.1
    have hBr_norm_eq_M : Subgroup.normalizer (Br : Set G) = M := by
      dsimp [Br]
      exact normalizer_centerFittingOpCoreInG_eq_of_ne_bot hG hM
        (centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hr)
    have hM_norm_Br : M ≤ Subgroup.normalizer (Br : Set G) := by
      rw [hBr_norm_eq_M]
    exact hNq_le_M.trans hM_norm_Br
  have hBr_le_core_Nq : Br ≤ opiCoreInG ({q} : Set ℕ)ᶜ Nq :=
    le_opiCoreInG_of_normal_of_isPiSubgroup hBrNq hBrnormNq hBrpi_qcompl
  have hcore_Nq_le_core_CX :
      opiCoreInG ({q} : Set ℕ)ᶜ Nq ≤
        opiCoreInG ({q} : Set ℕ)ᶜ (Subgroup.centralizer (Rq : Set G) ⊓ X) := by
    dsimp [Nq]
    exact opiCoreInG_singleton_compl_normalizer_inf_le_centralizer_inf hRqX hRqpi
  have hRqP : IsPGroup q ↥Rq :=
    OddOrder.GroupTheory.isPGroup_of_isPiSubgroup_singleton hRqpi
  have hcore_CX_le_core_X :
      opiCoreInG ({q} : Set ℕ)ᶜ (Subgroup.centralizer (Rq : Set G) ⊓ X) ≤
        opiCoreInG ({q} : Set ℕ)ᶜ X :=
    OddOrder.BG.Ch2.S07.opiCoreInG_centralizer_inf_le_opiCoreInG hXsolv hRqX hRqP
  exact hBr_le_core_Nq.trans (hcore_Nq_le_core_CX.trans hcore_CX_le_core_X)

/-- BG (8.5), full cFitting-core form: for distinct primes `q,r`, the r-core
of `A = C_F(M)(A0)` lies in `O_{q'}(X)` whenever `X` is solvable and contains `A`. -/
theorem opiCoreInG_singleton_cFittingInG_le_opiCoreInG_singleton_compl_of_ne
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q r : ℕ}
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] {M A0 X : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hXsolv : IsSolvable ↥X)
    (hAX : cFittingInG M A0 ≤ X)
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hqr : q ≠ r) :
    opiCoreInG ({r} : Set ℕ) (cFittingInG M A0) ≤ opiCoreInG ({q} : Set ℕ)ᶜ X := by
  let Rq : Subgroup G := centerFittingOpCoreInG q M
  let Ar : Subgroup G := opiCoreInG ({r} : Set ℕ) (cFittingInG M A0)
  let Nq : Subgroup G := Subgroup.normalizer (Rq : Set G) ⊓ X
  have hRqX : Rq ≤ X :=
    (centerFittingOpCoreInG_le_cFittingInG (q := q) hA0).trans hAX
  have hRqpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) Rq := by
    dsimp [Rq, centerFittingOpCoreInG]
    exact isPiSubgroup_opiCoreInG ({q} : Set ℕ) (centerFittingInG M)
  have hNq_eq_M : Subgroup.normalizer (Rq : Set G) = M := by
    dsimp [Rq]
    exact normalizer_centerFittingOpCoreInG_eq_of_ne_bot hG hM
      (centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hq)
  have hNq_le_M : Nq ≤ M := by
    intro x hx
    simpa [hNq_eq_M] using hx.1
  have hArX : Ar ≤ X :=
    (opiCoreInG_le ({r} : Set ℕ) (cFittingInG M A0)).trans hAX
  have hArF : Ar ≤ fittingInG M := by
    dsimp [Ar]
    exact opiCoreInG_singleton_cFittingInG_le_opiCoreInG_fittingInG.trans
      (opiCoreInG_le ({r} : Set ℕ) (fittingInG M))
  have hAr_cent_Rq : Ar ≤ Subgroup.centralizer (Rq : Set G) := by
    intro x hx
    have hxF : x ∈ fittingInG M := hArF hx
    have hxC := fittingInG_le_centralizer_centerFittingInG M hxF
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp hxC y
      (centerFittingOpCoreInG_le_centerFittingInG q M hy)
  have hArNq : Ar ≤ Nq := by
    refine le_inf ?_ hArX
    exact hAr_cent_Rq.trans (Subgroup.centralizer_le_normalizer (Rq : Set G))
  let L : Subgroup G := opiCoreInG ({q} : Set ℕ)ᶜ M ⊓ Nq
  have hArOqM : Ar ≤ opiCoreInG ({q} : Set ℕ)ᶜ M := by
    dsimp [Ar]
    exact opiCoreInG_singleton_cFittingInG_le_opiCoreInG_singleton_compl_maximal_of_ne
      hqr
  have hArL : Ar ≤ L := le_inf hArOqM hArNq
  have hLNq : L ≤ Nq := inf_le_right
  have hLnorm : (L.subgroupOf Nq).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLNq]
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyInf : y ∈ opiCoreInG ({q} : Set ℕ)ᶜ M ⊓ Nq := by simpa [L] using hy
      have hxM : x ∈ M := hNq_le_M hx
      have hnormO :=
        Subgroup.mem_normalizer_iff.mp
          (le_normalizer_opiCoreInG ({q} : Set ℕ)ᶜ M hxM) y
      have hnormN := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y
      simpa [L] using Subgroup.mem_inf.mpr ⟨hnormO.mp hyInf.1, hnormN.mp hyInf.2⟩
    · intro hy
      have hyInf : x * y * x⁻¹ ∈ opiCoreInG ({q} : Set ℕ)ᶜ M ⊓ Nq := by
        simpa [L] using hy
      have hxM : x ∈ M := hNq_le_M hx
      have hnormO :=
        Subgroup.mem_normalizer_iff.mp
          (le_normalizer_opiCoreInG ({q} : Set ℕ)ᶜ M hxM) y
      have hnormN := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y
      simpa [L] using Subgroup.mem_inf.mpr ⟨hnormO.mpr hyInf.1, hnormN.mpr hyInf.2⟩
  have hLpi : Subgroup.IsPiSubgroup ({q} : Set ℕ)ᶜ L := by
    intro s hs
    exact isPiSubgroup_opiCoreInG ({q} : Set ℕ)ᶜ M s
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le (inf_le_left : L ≤ _))
        Nat.card_pos.ne' hs)
  have hL_core_Nq : L ≤ opiCoreInG ({q} : Set ℕ)ᶜ Nq :=
    le_opiCoreInG_of_normal_of_isPiSubgroup hLNq hLnorm hLpi
  have hAr_core_Nq : Ar ≤ opiCoreInG ({q} : Set ℕ)ᶜ Nq := hArL.trans hL_core_Nq
  have hcore_Nq_le_core_CX :
      opiCoreInG ({q} : Set ℕ)ᶜ Nq ≤
        opiCoreInG ({q} : Set ℕ)ᶜ (Subgroup.centralizer (Rq : Set G) ⊓ X) := by
    dsimp [Nq]
    exact opiCoreInG_singleton_compl_normalizer_inf_le_centralizer_inf hRqX hRqpi
  have hRqP : IsPGroup q ↥Rq :=
    OddOrder.GroupTheory.isPGroup_of_isPiSubgroup_singleton hRqpi
  have hcore_CX_le_core_X :
      opiCoreInG ({q} : Set ℕ)ᶜ (Subgroup.centralizer (Rq : Set G) ⊓ X) ≤
        opiCoreInG ({q} : Set ℕ)ᶜ X :=
    OddOrder.BG.Ch2.S07.opiCoreInG_centralizer_inf_le_opiCoreInG hXsolv hRqX hRqP
  exact hAr_core_Nq.trans (hcore_Nq_le_core_CX.trans hcore_CX_le_core_X)

/-- BG (8.7) input: `O_{q'}(C_F(M)(A0))` is absorbed by `O_{q'}(H)`
whenever `H` is solvable and contains `C_F(M)(A0)`. -/
theorem opiCoreInG_cFittingInG_singleton_compl_le_opiCoreInG_singleton_compl
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hHsolv : IsSolvable ↥H)
    (hAH : cFittingInG M A0 ≤ H)
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors) :
    opiCoreInG ({q} : Set ℕ)ᶜ (cFittingInG M A0) ≤ opiCoreInG ({q} : Set ℕ)ᶜ H := by
  let A : Subgroup G := cFittingInG M A0
  let K : Subgroup G := opiCoreInG ({q} : Set ℕ)ᶜ A
  have hA_le_F : A ≤ fittingInG M := by
    dsimp [A, cFittingInG]
    exact inf_le_right
  have hA_nilp : Group.IsNilpotent ↥A := by
    haveI : Group.IsNilpotent ↥(fittingInG M) := fittingInG_isNilpotent M
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hA_le_F)
  have hK_nilp : Group.IsNilpotent ↥K := by
    have hK_A : K ≤ A := by
      dsimp [K]
      exact opiCoreInG_le ({q} : Set ℕ)ᶜ A
    haveI : Group.IsNilpotent ↥A := hA_nilp
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK_A)
  refine le_of_sylow_le_of_nilpotent hK_nilp ?_
  intro r
  haveI : Fact (r : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors r.2⟩
  let S : Subgroup G := ((default : Sylow (r : ℕ) ↥K) : Subgroup ↥K).map K.subtype
  have hS_le_K : S ≤ K := by
    dsimp [S]
    exact Subgroup.map_subtype_le _
  have hS_le_A : S ≤ A := hS_le_K.trans (by
    dsimp [K]
    exact opiCoreInG_le ({q} : Set ℕ)ᶜ A)
  have hS_p : IsPGroup (r : ℕ) ↥S := by
    dsimp [S]
    exact (default : Sylow (r : ℕ) ↥K).isPGroup'.map K.subtype
  have hS_le_OrA : S ≤ opiCoreInG ({(r : ℕ)} : Set ℕ) A :=
    le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hA_nilp hS_le_A hS_p
  have hr_not_q : q ≠ (r : ℕ) := by
    have hKpi : Subgroup.IsPiSubgroup ({q} : Set ℕ)ᶜ K := by
      dsimp [K]
      exact isPiSubgroup_opiCoreInG ({q} : Set ℕ)ᶜ A
    have hrcomp : (r : ℕ) ∈ ({q} : Set ℕ)ᶜ := hKpi (r : ℕ) r.2
    intro hqr
    exact hrcomp (by simp [hqr])
  exact hS_le_OrA.trans (by
    dsimp [A]
    exact opiCoreInG_singleton_cFittingInG_le_opiCoreInG_singleton_compl_of_ne
      hG hM hA0 hHsolv hAH hq hr_not_q)

/-- BG (8.7), complement-centralizer form: after `π(F(H)) = π(F(M))`, the
`p`-core of `C_F(M)(A0)` centralizes `O_{p'}(F(H))`. -/
theorem opiCoreInG_singleton_cFittingInG_le_centralizer_opiCoreInG_singleton_compl_fittingInG
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hHsolv : IsSolvable ↥H)
    (hAH : cFittingInG M A0 ≤ H)
    (hPrimes : OddOrder.BG.Ch2.S07.primesOf (fittingInG H) =
      OddOrder.BG.Ch2.S07.primesOf (fittingInG M)) :
    opiCoreInG ({p} : Set ℕ) (cFittingInG M A0) ≤
      Subgroup.centralizer (opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG H) : Set G) := by
  let Ap : Subgroup G := opiCoreInG ({p} : Set ℕ) (cFittingInG M A0)
  let K : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG H)
  have hK_le_cent_Ap : K ≤ Subgroup.centralizer (Ap : Set G) := by
    have hK_le_FH : K ≤ fittingInG H := by
      dsimp [K]
      exact opiCoreInG_le ({p} : Set ℕ)ᶜ (fittingInG H)
    have hK_nilp : Group.IsNilpotent ↥K := by
      haveI : Group.IsNilpotent ↥(fittingInG H) := fittingInG_isNilpotent H
      exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK_le_FH)
    refine le_of_sylow_le_of_nilpotent hK_nilp ?_
    intro r
    haveI : Fact (r : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors r.2⟩
    let S : Subgroup G := ((default : Sylow (r : ℕ) ↥K) : Subgroup ↥K).map K.subtype
    have hS_le_K : S ≤ K := by
      dsimp [S]
      exact Subgroup.map_subtype_le _
    have hS_le_FH : S ≤ fittingInG H := hS_le_K.trans hK_le_FH
    have hS_p : IsPGroup (r : ℕ) ↥S := by
      dsimp [S]
      exact (default : Sylow (r : ℕ) ↥K).isPGroup'.map K.subtype
    have hS_le_OrFH : S ≤ opiCoreInG ({(r : ℕ)} : Set ℕ) (fittingInG H) :=
      le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
        (fittingInG_isNilpotent H) hS_le_FH hS_p
    have hrFH : (r : ℕ) ∈ (Nat.card ↥(fittingInG H)).primeFactors :=
      Nat.primeFactors_mono (Subgroup.card_dvd_of_le hK_le_FH) Nat.card_pos.ne' r.2
    have hrFM_primes : (r : ℕ) ∈ OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
      rw [← hPrimes]
      exact hrFH
    have hKpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ K := by
      dsimp [K]
      exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG H)
    have hr_not_p : (r : ℕ) ≠ p := by
      have hrcomp : (r : ℕ) ∈ ({p} : Set ℕ)ᶜ := hKpi (r : ℕ) r.2
      intro hrp
      exact hrcomp (by simp [hrp])
    have hAp_le_OrH_compl : Ap ≤ opiCoreInG ({(r : ℕ)} : Set ℕ)ᶜ H := by
      dsimp [Ap]
      exact opiCoreInG_singleton_cFittingInG_le_opiCoreInG_singleton_compl_of_ne
        (p := p) (q := (r : ℕ)) (r := p) hG hM hA0 hHsolv hAH hrFM_primes hr_not_p
    have hOrFH_cent_Ap :
        opiCoreInG ({(r : ℕ)} : Set ℕ) (fittingInG H) ≤
          Subgroup.centralizer (Ap : Set G) :=
      opiCoreInG_fittingInG_le_centralizer_of_le_opiCoreInG_compl
        ({(r : ℕ)} : Set ℕ) hAp_le_OrH_compl
    exact hS_le_OrFH.trans hOrFH_cent_Ap
  change Ap ≤ Subgroup.centralizer (K : Set G)
  intro x hx
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (hK_le_cent_Ap hy) x hx).symm

/-- BG (8.7) plus Proposition 1.4: after `π(F(H)) = π(F(M))`, the `p`-core of
`C_F(M)(A0)` centralizes `O_{p'}(H)`. -/
theorem opiCoreInG_singleton_cFittingInG_le_centralizer_opiCoreInG_singleton_compl
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hHsolv : IsSolvable ↥H)
    (hAH : cFittingInG M A0 ≤ H)
    (hPrimes : OddOrder.BG.Ch2.S07.primesOf (fittingInG H) =
      OddOrder.BG.Ch2.S07.primesOf (fittingInG M)) :
    opiCoreInG ({p} : Set ℕ) (cFittingInG M A0) ≤
      Subgroup.centralizer (opiCoreInG ({p} : Set ℕ)ᶜ H : Set G) := by
  let Ap : Subgroup G := opiCoreInG ({p} : Set ℕ) (cFittingInG M A0)
  let N : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ H
  change Ap ≤ Subgroup.centralizer (N : Set G)
  have hN_H : N ≤ H := by
    dsimp [N]
    exact opiCoreInG_le ({p} : Set ℕ)ᶜ H
  have hH_norm_N : H ≤ Subgroup.normalizer (N : Set G) := by
    dsimp [N]
    exact le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ H
  have hAp_cent_FN : Ap ≤ Subgroup.centralizer (fittingInG N : Set G) := by
    have hAp_cent_OFH : Ap ≤
        Subgroup.centralizer (opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG H) : Set G) := by
      dsimp [Ap]
      exact
        opiCoreInG_singleton_cFittingInG_le_centralizer_opiCoreInG_singleton_compl_fittingInG
          hG hM hA0 hHsolv hAH hPrimes
    have hFN_le_OFH : fittingInG N ≤ opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG H) := by
      dsimp [N]
      exact fittingInG_opiCoreInG_singleton_compl_le_opiCoreInG_singleton_compl_fittingInG H
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (hAp_cent_OFH ha) y (hFN_le_OFH hy)
  have hAp_H : Ap ≤ H := by
    dsimp [Ap]
    exact (opiCoreInG_le ({p} : Set ℕ) (cFittingInG M A0)).trans hAH
  have hAp_norm_N : Ap ≤ Subgroup.normalizer (N : Set G) := hAp_H.trans hH_norm_N
  have hAp_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ) Ap := by
    dsimp [Ap]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ) (cFittingInG M A0)
  have hN_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ N := by
    dsimp [N]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ H
  have hCop : Nat.Coprime (Nat.card ↥Ap) (Nat.card ↥N) :=
    coprime_card_of_isPiSubgroup_of_isPiSubgroup_compl hAp_pi hN_pi
  haveI : IsSolvable ↥H := hHsolv
  haveI hNsolv : IsSolvable ↥N :=
    solvable_of_solvable_injective (f := Subgroup.inclusion hN_H)
      (Subgroup.inclusion_injective hN_H)
  exact le_centralizer_of_coprime_normalizes_of_le_centralizer_fittingInG
    hAp_norm_N hCop hAp_cent_FN

/-- BG (8.7) with (8.2): after `π(F(H)) = π(F(M))`, the `p`-complement core of
`H` lies in the original maximal subgroup `M`. -/
theorem opiCoreInG_singleton_compl_le_maximal_of_cFittingInG_le_of_primes_eq
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hHsolv : IsSolvable ↥H)
    (hAH : cFittingInG M A0 ≤ H)
    (hPrimes : OddOrder.BG.Ch2.S07.primesOf (fittingInG H) =
      OddOrder.BG.Ch2.S07.primesOf (fittingInG M)) :
    opiCoreInG ({p} : Set ℕ)ᶜ H ≤ M := by
  let Ap : Subgroup G := opiCoreInG ({p} : Set ℕ) (cFittingInG M A0)
  let N : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ H
  change N ≤ M
  have hN_cent_Ap : N ≤ Subgroup.centralizer (Ap : Set G) := by
    have hAp_cent_N : Ap ≤ Subgroup.centralizer (N : Set G) := by
      dsimp [Ap, N]
      exact opiCoreInG_singleton_cFittingInG_le_centralizer_opiCoreInG_singleton_compl
        hG hM hA0 hHsolv hAH hPrimes
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hAp_cent_N hy) x hx).symm
  have hCentAp_le_M : Subgroup.centralizer (Ap : Set G) ≤ M := by
    have hOp_ne : centerFittingOpCoreInG p M ≠ ⊥ :=
      centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hp
    have hOp_le_Ap : centerFittingOpCoreInG p M ≤ Ap := by
      dsimp [Ap]
      exact centerFittingOpCoreInG_le_opiCoreInG_cFittingInG_singleton hA0
    exact centralizer_le_maximal_of_centerFittingOpCoreInG_le hG hM hOp_ne hOp_le_Ap
  exact hN_cent_Ap.trans hCentAp_le_M

/-- BG (8.7): in the non-`p`-group case, each q-core of `F(H)` lies in the
original maximal subgroup `M` whenever `H` contains `C_F(M)(A0)`. -/
theorem opiCoreInG_fittingInG_singleton_le_maximal_of_cFittingInG_le_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hHsolv : IsSolvable ↥H)
    (hAH : cFittingInG M A0 ≤ H)
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors) :
    opiCoreInG ({q} : Set ℕ) (fittingInG H) ≤ M := by
  exact
    opiCoreInG_fittingInG_singleton_le_maximal_of_cFittingInG_compl_le_opiCoreInG_compl
      hG hM hp hA0 hFnp hq
      (opiCoreInG_cFittingInG_singleton_compl_le_opiCoreInG_singleton_compl
        hG hM hA0 hHsolv hAH hq)

/-- BG (8.5) applied to the commutator form (8.4): if `q ∈ π(F(M))`, every
`A = C_F(M)(A0)`-invariant `π(A)`-complement subgroup lies in `O_{q'}(X)`. -/
theorem hInvariant_le_opiCoreInG_singleton_compl_of_mem_primeFactors_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 X Y : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hXsolv : IsSolvable ↥X)
    (hAX : cFittingInG M A0 ≤ X)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Y ≤ opiCoreInG ({q} : Set ℕ)ᶜ X := by
  obtain ⟨r, hr, hrq⟩ :=
    exists_primeFactor_ne_of_mem_primeFactor_not_isPGroup
      (H := ↥(fittingInG M)) hp hFnp q
  haveI : Fact r.Prime := ⟨(Nat.mem_primeFactors.mp hr).1⟩
  let Br : Subgroup G := centerFittingOpCoreInG r M
  have hY_comm : Y ≤ ⁅Br, Y⁆ := by
    dsimp [Br]
    exact hInvariant_le_commutator_centerFittingOpCoreInG_of_not_pGroup
      hG hM hA0 hFnp hr hY
  have hBr_core : Br ≤ opiCoreInG ({q} : Set ℕ)ᶜ X := by
    dsimp [Br]
    exact centerFittingOpCoreInG_le_opiCoreInG_singleton_compl_of_ne
      hG hM hA0 hXsolv hAX hq hr (fun hqr => hrq hqr.symm)
  have hY_X : Y ≤ X := hY.1
  have hY_norm_core : Y ≤ Subgroup.normalizer (opiCoreInG ({q} : Set ℕ)ᶜ X : Set G) :=
    hY_X.trans (le_normalizer_opiCoreInG ({q} : Set ℕ)ᶜ X)
  have hcomm_core : ⁅Br, Y⁆ ≤ opiCoreInG ({q} : Set ℕ)ᶜ X :=
    (Subgroup.commutator_mono hBr_core le_rfl).trans
      (OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hY_norm_core)
  exact hY_comm.trans hcomm_core

/-- If `Y ≤ X` and `Y` lies in `O_{q'}(X)` for every `q ∈ π`, then `Y` lies in
`O_{π'}(X)`. This packages the BG (8.5) intersection step
`⋂_{q∈π} O_{q'}(X) = O_{π'}(X)` in the direction needed for Hypothesis 7.1. -/
theorem le_opiCoreInG_compl_of_forall_le_opiCoreInG_singleton_compl
    [Finite G] {π : Set ℕ} {X Y : Subgroup G} (hYX : Y ≤ X)
    (hYq : ∀ q, q ∈ π → Y ≤ opiCoreInG ({q} : Set ℕ)ᶜ X) :
    Y ≤ opiCoreInG πᶜ X := by
  let K : Subgroup G :=
    X ⊓ ⨅ q : {q : ℕ // q ∈ π}, opiCoreInG ({q.1} : Set ℕ)ᶜ X
  have hYK : Y ≤ K := by
    refine le_inf hYX ?_
    refine le_iInf ?_
    intro q
    exact hYq q.1 q.2
  have hKX : K ≤ X := inf_le_left
  have hKnorm : (K.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKX]
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hnormX := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y
    constructor
    · intro hy
      simp only [K, Subgroup.mem_inf, Subgroup.mem_iInf] at hy ⊢
      refine ⟨hnormX.mp hy.1, ?_⟩
      intro q
      have hnormCore :=
        Subgroup.mem_normalizer_iff.mp
          (le_normalizer_opiCoreInG ({q.1} : Set ℕ)ᶜ X hx) y
      exact hnormCore.mp (hy.2 q)
    · intro hy
      simp only [K, Subgroup.mem_inf, Subgroup.mem_iInf] at hy ⊢
      refine ⟨hnormX.mpr hy.1, ?_⟩
      intro q
      have hnormCore :=
        Subgroup.mem_normalizer_iff.mp
          (le_normalizer_opiCoreInG ({q.1} : Set ℕ)ᶜ X hx) y
      exact hnormCore.mpr (hy.2 q)
  have hKpi : Subgroup.IsPiSubgroup πᶜ K := by
    intro s hs hsπ
    have hK_le_core_s : K ≤ opiCoreInG ({s} : Set ℕ)ᶜ X := by
      dsimp [K]
      exact inf_le_right.trans
        (iInf_le (fun q : {q : ℕ // q ∈ π} =>
          opiCoreInG ({q.1} : Set ℕ)ᶜ X) ⟨s, hsπ⟩)
    have hs_core : s ∈ ({s} : Set ℕ)ᶜ :=
      isPiSubgroup_opiCoreInG ({s} : Set ℕ)ᶜ X s
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hK_le_core_s)
          Nat.card_pos.ne' hs)
    exact hs_core (by simp)
  exact hYK.trans (le_opiCoreInG_of_normal_of_isPiSubgroup hKX hKnorm hKpi)

/-- BG (8.5), support-detection form: if the `σ`-complement core of a solvable
subgroup `X` containing `C_F(M)(A0)` is trivial and `σ ⊆ π(F(M))`, then every prime
of `F(M)` lies in `σ`. -/
theorem primesOf_fittingInG_subset_of_opiCoreInG_compl_eq_bot
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 X : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hXsolv : IsSolvable ↥X)
    (hAX : cFittingInG M A0 ≤ X)
    {σ : Set ℕ}
    (hσπ : σ ⊆ OddOrder.BG.Ch2.S07.primesOf (fittingInG M))
    (hOσ : opiCoreInG σᶜ X = ⊥) :
    OddOrder.BG.Ch2.S07.primesOf (fittingInG M) ⊆ σ := by
  intro r hrπ
  by_contra hrσ
  have hrF : r ∈ (Nat.card ↥(fittingInG M)).primeFactors := by
    simpa [OddOrder.BG.Ch2.S07.primesOf] using hrπ
  haveI : Fact r.Prime := ⟨(Nat.mem_primeFactors.mp hrF).1⟩
  have hBrX : centerFittingOpCoreInG r M ≤ X :=
    (centerFittingOpCoreInG_le_cFittingInG (q := r) hA0).trans hAX
  have hBr_core : centerFittingOpCoreInG r M ≤ opiCoreInG σᶜ X := by
    refine le_opiCoreInG_compl_of_forall_le_opiCoreInG_singleton_compl hBrX ?_
    intro q hqσ
    have hqπ : q ∈ OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := hσπ hqσ
    have hqF : q ∈ (Nat.card ↥(fittingInG M)).primeFactors := by
      simpa [OddOrder.BG.Ch2.S07.primesOf] using hqπ
    haveI : Fact q.Prime := ⟨(Nat.mem_primeFactors.mp hqF).1⟩
    have hqr : q ≠ r := by
      intro hqr
      exact hrσ (by simpa [hqr] using hqσ)
    exact centerFittingOpCoreInG_le_opiCoreInG_singleton_compl_of_ne
      hG hM hA0 hXsolv hAX hqF hrF hqr
  have hBr_bot : centerFittingOpCoreInG r M = ⊥ :=
    le_bot_iff.mp (by
      rw [← hOσ]
      exact hBr_core)
  exact (centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hrF) hBr_bot

/-- BG (8.5), generated-condition form: in the non-p-group case, every member of
`ℋ_X(C_F(M)(A0); π(C_F(M)(A0))^c)` lies in `O_{π(C_F(M)(A0))^c}(X)`. -/
theorem hInvariant_le_opiCoreInG_primesOf_cFittingInG_compl_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 X Y : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hXsolv : IsSolvable ↥X)
    (hAX : cFittingInG M A0 ≤ X)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Y ≤ opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ X := by
  have hA0F : A0 ≤ fittingInG M := isMaxElemAbelianIn_le hA0
  have hPrimes :
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) =
        OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    dsimp [cFittingInG]
    exact primesOf_cFitting_eq_primesOf_fittingInG hA0F
  refine le_opiCoreInG_compl_of_forall_le_opiCoreInG_singleton_compl hY.1 ?_
  intro q hqA
  have hqF_primes : q ∈ OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    simpa [hPrimes] using hqA
  have hqF : q ∈ (Nat.card ↥(fittingInG M)).primeFactors := by
    simpa [OddOrder.BG.Ch2.S07.primesOf] using hqF_primes
  haveI : Fact q.Prime := ⟨(Nat.mem_primeFactors.mp hqF).1⟩
  exact hInvariant_le_opiCoreInG_singleton_compl_of_mem_primeFactors_not_pGroup
    hG hM hA0 hXsolv hAX hp hFnp hqF hY

/-- BG (8.5) verifies Hypothesis 7.1 for `A = C_F(M)(A0)` in the non-p-group case. -/
theorem hypothesis71_cFittingInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M)) :
    OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact cFitting_ne_bot_of_isMaxElemAbelianIn hp hA0
  · exact lt_of_le_of_lt (inf_le_right.trans (fittingInG_le M))
      (mem_maximalSubgroups.mp hM).lt_top
  · intro X hAX hXlt
    refine OddOrder.BG.Ch2.S07.generated_eq_of_forall_le_opiCoreInG hAX ?_
    intro Y hY
    exact hInvariant_le_opiCoreInG_primesOf_cFittingInG_compl_of_not_pGroup
      hG hM hA0 (hG.solvable_of_lt_top X hXlt) hAX hp hFnp hY

/-- Theorem 7.2 specialized to `A = C_F(M)(A0)`: once Hypothesis 7.1 is verified,
`K = O_{π(A)^c}(C_G(A))` acts transitively on `ℋ_G*(A;q)`. -/
theorem transitive_cFittingInG_of_hypothesis71 [Finite G]
    (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact q.Prime] {M A0 : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    OddOrder.BG.Ch2.S07.ConjTransitiveOn
      (OddOrder.BG.Ch2.S07.kSubgroup (cFittingInG M A0))
      (hInvariantStar ⊤ (cFittingInG M A0) {q}) :=
  OddOrder.BG.Ch2.S07.transitive_of_three_le_rank_center hG hA hq (by
    dsimp [cFittingInG]
    exact three_le_rank_center_cFitting_of_isMaxElemAbelianIn hA0 hm)

/-- The subgroup `C_F(M)(A0)` is subnormal inside `F(M)`, because `F(M)` is nilpotent. -/
theorem cFittingInG_subgroupOf_fittingInG_isSubnormal [Finite G] {M A0 : Subgroup G} :
    ((cFittingInG M A0).subgroupOf (fittingInG M)).IsSubnormal := by
  haveI : Group.IsNilpotent ↥(fittingInG M) := fittingInG_isNilpotent M
  exact OddOrder.Isaacs.Ch02.isSubnormal_of_isNilpotent_finite _

/-- Theorem 7.4 specialized to the propagation step in BG (8.6), with
`A = C_F(M)(A0)` and `P = F(M)`. -/
theorem transitivity_propagates_to_fittingInG_of_cFittingInG [Finite G]
    (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact q.Prime] {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Subgroup.centralizer (fittingInG M : Set G) ⊓
        OddOrder.BG.Ch2.S07.kSubgroup (cFittingInG M A0) =
      opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ
        (Subgroup.centralizer (fittingInG M : Set G)) ∧
    OddOrder.BG.Ch2.S07.ConjTransitiveOn
      (opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ
        (Subgroup.centralizer (fittingInG M : Set G)))
      (hInvariantStar ⊤ (fittingInG M) {q}) ∧
    hInvariantStar ⊤ (fittingInG M) {q} ⊆
      hInvariantStar ⊤ (cFittingInG M A0) {q} ∧
    (∀ Q ∈ hInvariantStar ⊤ (fittingInG M) {q},
      fittingInG M ⊓ derivedInG (Subgroup.normalizer (fittingInG M)) ≤
        derivedInG (Subgroup.normalizer Q) ∧
      ∀ n : G, n ∈ Subgroup.normalizer (fittingInG M) →
        ∃ c ∈ opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ
            (Subgroup.centralizer (fittingInG M : Set G)),
          ∃ m ∈ Subgroup.normalizer (fittingInG M) ⊓ Subgroup.normalizer Q, n = c * m) := by
  have hA0F : A0 ≤ fittingInG M := isMaxElemAbelianIn_le hA0
  have hPrimes :
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) =
        OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    dsimp [cFittingInG]
    exact primesOf_cFitting_eq_primesOf_fittingInG hA0F
  have hPproper : fittingInG M < ⊤ :=
    lt_of_le_of_lt (fittingInG_le M) (mem_maximalSubgroups.mp hM).lt_top
  have hPpi : Subgroup.IsPiSubgroup
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0)) (fittingInG M) := by
    rw [hPrimes]
    intro r hr
    simpa [OddOrder.BG.Ch2.S07.primesOf] using hr
  have hAP : cFittingInG M A0 ≤ fittingInG M := by
    dsimp [cFittingInG]
    exact inf_le_right
  exact OddOrder.BG.Ch2.S07.transitivity_propagates hG hA hq (fittingInG M)
    hPproper hPpi hAP cFittingInG_subgroupOf_fittingInG_isSubnormal
    (transitive_cFittingInG_of_hypothesis71 hG hA0 hm hA hq)

/-- The relative centralizer C_F(M)(A0) is proper whenever M is maximal. -/
theorem cFitting_lt_top_of_mem_maximal {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) :
    Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M < ⊤ :=
  lt_of_le_of_lt (inf_le_right.trans (fittingInG_le M))
    (mem_maximalSubgroups.mp hM).lt_top

/-- BG (8.6) packaged for A = C_{F(M)}(A0): once Hypothesis 7.1 and the
centralizer pi-subgroup condition are known, H_G*(A;q) is a singleton. -/
theorem hInvariantStar_eq_of_cFittingInG_of_hypothesis71_of_centralizer_isPiSubgroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact q.Prime]
    {M A0 : Subgroup G} (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hCpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))
      (Subgroup.centralizer (cFittingInG M A0 : Set G)))
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar ⊤ (cFittingInG M A0) {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ (cFittingInG M A0) {q}) :
    Q₁ = Q₂ :=
  OddOrder.BG.Ch2.S07.hInvariantStar_eq_of_three_le_rank_center_of_centralizer_isPiSubgroup
    hG hA hq (by
      dsimp [cFittingInG]
      exact three_le_rank_center_cFitting_of_isMaxElemAbelianIn hA0 hm) hCpi hQ₁ hQ₂

/-- BG (8.6) for `A = C_F(M)(A0)` in the non-`p`-group case: once Hypothesis 7.1
is verified for `A`, the star family `ℋ_G*(A;q)` is a singleton for every
`q` in the complement of `π(A)`. -/
theorem hInvariantStar_eq_of_cFittingInG_of_hypothesis71_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar ⊤ (cFittingInG M A0) {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ (cFittingInG M A0) {q}) :
    Q₁ = Q₂ :=
  hInvariantStar_eq_of_cFittingInG_of_hypothesis71_of_centralizer_isPiSubgroup
    hG hA0 hm hA hq
    (centralizer_cFitting_isPiSubgroup_of_not_pGroup hG hM hA0 hFnp) hQ₁ hQ₂

/-- BG (8.6) after propagation to `F(M)`: in the non-`p`-group case, once
Hypothesis 7.1 is verified for `C_F(M)(A0)`, the family `ℋ_G*(F(M);q)` is a
singleton for every `q` outside `π(C_F(M)(A0))`. -/
theorem hInvariantStar_eq_of_fittingInG_of_cFittingInG_hypothesis71_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar ⊤ (fittingInG M) {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ (fittingInG M) {q}) :
    Q₁ = Q₂ := by
  have hprop := transitivity_propagates_to_fittingInG_of_cFittingInG
    hG hM hA0 hm hA hq
  exact hInvariantStar_eq_of_cFittingInG_of_hypothesis71_of_not_pGroup
    hG hM hA0 hm hFnp hA hq (hprop.2.2.1 hQ₁) (hprop.2.2.1 hQ₂)

/-- BG (8.6), normalizer bridge: in the non-p-group case, the propagation
 decomposition forces every element normalizing F(M) to normalize each member of
 `H_G*(F(M);q)`. -/
theorem normalizer_fittingInG_le_normalizer_of_hInvariantStar_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hQ : Q ∈ hInvariantStar ⊤ (fittingInG M) {q}) :
    Subgroup.normalizer (fittingInG M : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  have hprop := transitivity_propagates_to_fittingInG_of_cFittingInG
    hG hM hA0 hm hA hq
  have hKbot :
      OddOrder.BG.Ch2.S07.kSubgroup (cFittingInG M A0) = ⊥ :=
    kSubgroup_cFittingInG_eq_bot_of_not_pGroup hG hM hA0 hFnp
  have hopi_bot :
      opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ
        (Subgroup.centralizer (fittingInG M : Set G)) = ⊥ := by
    have hfirst := hprop.1
    rw [hKbot, inf_bot_eq] at hfirst
    exact hfirst.symm
  intro n hn
  obtain ⟨c, hc, m, hmN, hn_eq⟩ := (hprop.2.2.2 Q hQ).2 n hn
  have hc_one : c = 1 := by
    have hc_bot : c ∈ (⊥ : Subgroup G) := by
      rwa [hopi_bot] at hc
    exact Subgroup.mem_bot.mp hc_bot
  have hmQ : m ∈ Subgroup.normalizer (Q : Set G) := hmN.2
  rw [hn_eq, hc_one, one_mul]
  exact hmQ

/-- BG (8.6), maximal-subgroup form of the normalizer bridge: in the non-p-group
 case, M normalizes every member of `H_G*(F(M);q)`. -/
theorem maximal_le_normalizer_of_hInvariantStar_fittingInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hQ : Q ∈ hInvariantStar ⊤ (fittingInG M) {q}) :
    M ≤ Subgroup.normalizer (Q : Set G) := by
  intro x hxM
  exact normalizer_fittingInG_le_normalizer_of_hInvariantStar_of_not_pGroup
    hG hM hA0 hm hFnp hA hq hQ (mem_normalizer_fittingInG_of_mem hxM)

/-- BG (8.6): a nontrivial member of `H_G*(F(M);q)` lies in the maximal subgroup
`M` once `M` is known to normalize it. -/
theorem hInvariantStar_le_maximal_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hQ : Q ∈ hInvariantStar ⊤ (fittingInG M) {q}) (hQne : Q ≠ ⊥) :
    Q ≤ M :=
  le_maximal_of_le_normalizer_of_ne_bot_isPiSubgroup_singleton hG hM
    (maximal_le_normalizer_of_hInvariantStar_fittingInG_of_not_pGroup
      hG hM hA0 hm hFnp hA hq hQ)
    hQne (hInvariantStar_isPiSubgroup hQ)

/-- BG (8.6): a nontrivial member of `H_G*(F(M);q)` is absorbed by `F(M)`. -/
theorem hInvariantStar_le_fittingInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hQ : Q ∈ hInvariantStar ⊤ (fittingInG M) {q}) (hQne : Q ≠ ⊥) :
    Q ≤ fittingInG M := by
  have hQM : Q ≤ M :=
    hInvariantStar_le_maximal_of_not_pGroup hG hM hA0 hm hFnp hA hq hQ hQne
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    maximal_le_normalizer_of_hInvariantStar_fittingInG_of_not_pGroup
      hG hM hA0 hm hFnp hA hq hQ
  have hQnorm : (Q.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hMQ
  exact le_fittingInG_of_normal_isPiSubgroup_singleton hQM hQnorm
    (hInvariantStar_isPiSubgroup hQ)

/-- BG (8.6) endpoint for `F(M)`: every member of `H_G*(F(M);q)` is trivial for
`q` outside `π(C_F(M)(A0))` in the non-p-group case. -/
theorem hInvariantStar_eq_bot_of_fittingInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hQ : Q ∈ hInvariantStar ⊤ (fittingInG M) {q}) :
    Q = ⊥ := by
  by_cases hQbot : Q = ⊥
  · exact hQbot
  have hQleF : Q ≤ fittingInG M :=
    hInvariantStar_le_fittingInG_of_not_pGroup hG hM hA0 hm hFnp hA hq hQ hQbot
  have hA0F : A0 ≤ fittingInG M := isMaxElemAbelianIn_le hA0
  have hPrimes :
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) =
        OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    dsimp [cFittingInG]
    exact primesOf_cFitting_eq_primesOf_fittingInG hA0F
  have hFpi : Subgroup.IsPiSubgroup
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0)) (fittingInG M) := by
    rw [hPrimes]
    intro r hr
    simpa [OddOrder.BG.Ch2.S07.primesOf] using hr
  have hQpi_compl : Subgroup.IsPiSubgroup
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ Q := by
    intro r hr
    have hrq : r = q := Set.mem_singleton_iff.mp ((hInvariantStar_isPiSubgroup hQ) r hr)
    rw [hrq]
    exact hq
  exact eq_bot_of_le_of_isPiSubgroup_of_isPiSubgroup_compl hQleF hFpi hQpi_compl

/-- BG (8.6) endpoint for `A = C_F(M)(A0)`: every member of `H_G*(A;q)` is
trivial for `q` outside `π(A)` in the non-p-group case. -/
theorem hInvariantStar_eq_bot_of_cFittingInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hQ : Q ∈ hInvariantStar ⊤ (cFittingInG M A0) {q}) :
    Q = ⊥ := by
  have hBotInvF : (⊥ : Subgroup G) ∈ hInvariant ⊤ (fittingInG M) {q} := by
    rw [mem_hInvariant]
    refine ⟨bot_le, ?_, ?_⟩
    · intro x _
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp
    · intro r hr
      rw [Subgroup.card_bot] at hr
      simp at hr
  obtain ⟨R, hRstar, _hBotR⟩ := exists_le_hInvariantStar hBotInvF
  have hRbot : R = ⊥ :=
    hInvariantStar_eq_bot_of_fittingInG_of_not_pGroup hG hM hA0 hm hFnp hA hq hRstar
  have hprop := transitivity_propagates_to_fittingInG_of_cFittingInG
    hG hM hA0 hm hA hq
  have hRstarA : R ∈ hInvariantStar ⊤ (cFittingInG M A0) {q} := hprop.2.2.1 hRstar
  have hQR : Q = R :=
    hInvariantStar_eq_of_cFittingInG_of_hypothesis71_of_not_pGroup
      hG hM hA0 hm hFnp hA hq hQ hRstarA
  exact hQR.trans hRbot

/-- BG (8.6), non-star form: every `A`-invariant q-subgroup is trivial for
`A = C_F(M)(A0)` and `q` outside `π(A)` in the non-p-group case. -/
theorem hInvariant_eq_bot_of_cFittingInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hQ : Q ∈ hInvariant ⊤ (cFittingInG M A0) {q}) :
    Q = ⊥ := by
  obtain ⟨R, hRstar, hQR⟩ := exists_le_hInvariantStar hQ
  have hRbot : R = ⊥ :=
    hInvariantStar_eq_bot_of_cFittingInG_of_not_pGroup hG hM hA0 hm hFnp hA hq hRstar
  exact le_bot_iff.mp (by simpa [hRbot] using hQR)

/-- BG (8.6), q-core form: if `A = C_F(M)(A0)` lies in `H`, then the ambient
q-core of `H` is trivial for `q` outside `π(A)` in the non-p-group case. -/
theorem opiCoreInG_singleton_eq_bot_of_cFittingInG_le_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hAH : cFittingInG M A0 ≤ H) :
    opiCoreInG ({q} : Set ℕ) H = ⊥ := by
  have hQ : opiCoreInG ({q} : Set ℕ) H ∈ hInvariant ⊤ (cFittingInG M A0) {q} := by
    rw [mem_hInvariant]
    exact ⟨le_top,
      hAH.trans (le_normalizer_opiCoreInG ({q} : Set ℕ) H),
      isPiSubgroup_opiCoreInG ({q} : Set ℕ) H⟩
  exact hInvariant_eq_bot_of_cFittingInG_of_not_pGroup hG hM hA0 hm hFnp hA hq hQ

/-- If q divides `|F(H)|`, then the ambient q-core `O_q(H)` is nontrivial. -/
theorem opiCoreInG_singleton_ne_bot_of_mem_primeFactors_fittingInG [Finite G]
    {q : ℕ} [Fact q.Prime] {H : Subgroup G}
    (hq : q ∈ (Nat.card ↥(fittingInG H)).primeFactors) :
    opiCoreInG ({q} : Set ℕ) H ≠ ⊥ := by
  have hZne : centerFittingOpCoreInG q H ≠ ⊥ :=
    centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hq
  have hZpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) (centerFittingOpCoreInG q H) := by
    dsimp [centerFittingOpCoreInG]
    exact isPiSubgroup_opiCoreInG ({q} : Set ℕ) (centerFittingInG H)
  have hZleO : centerFittingOpCoreInG q H ≤ opiCoreInG ({q} : Set ℕ) H :=
    le_opiCoreInG_of_normal_of_isPiSubgroup (centerFittingOpCoreInG_le q H)
      (centerFittingOpCoreInG_subgroupOf_normal q H) hZpi
  intro hObot
  apply hZne
  exact le_bot_iff.mp (by
    rw [← hObot]
    exact hZleO)

/-- If q divides `|F(H)|`, then the ambient q-core of `F(H)` is nontrivial. -/
theorem opiCoreInG_singleton_fittingInG_ne_bot_of_mem_primeFactors [Finite G]
    {q : ℕ} [Fact q.Prime] {H : Subgroup G}
    (hq : q ∈ (Nat.card ↥(fittingInG H)).primeFactors) :
    opiCoreInG ({q} : Set ℕ) (fittingInG H) ≠ ⊥ := by
  have hZne : centerFittingOpCoreInG q H ≠ ⊥ :=
    centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hq
  have hZleF : centerFittingOpCoreInG q H ≤ fittingInG H :=
    (centerFittingOpCoreInG_le_centerFittingInG q H).trans
      (centerFittingInG_le_fittingInG H)
  have hZnormF : ((centerFittingOpCoreInG q H).subgroupOf (fittingInG H)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZleF]
    have hH_norm_Z : H ≤ Subgroup.normalizer (centerFittingOpCoreInG q H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (centerFittingOpCoreInG_le q H)).mp
        (centerFittingOpCoreInG_subgroupOf_normal q H)
    exact (fittingInG_le H).trans hH_norm_Z
  have hZpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) (centerFittingOpCoreInG q H) := by
    dsimp [centerFittingOpCoreInG]
    exact isPiSubgroup_opiCoreInG ({q} : Set ℕ) (centerFittingInG H)
  have hZleO : centerFittingOpCoreInG q H ≤
      opiCoreInG ({q} : Set ℕ) (fittingInG H) :=
    le_opiCoreInG_of_normal_of_isPiSubgroup hZleF hZnormF hZpi
  intro hObot
  apply hZne
  exact le_bot_iff.mp (by
    rw [← hObot]
    exact hZleO)

/-- BG (8.8), Prop 1.4 bridge: once `D_p = O_p(F(H))` is inside `M`,
`D_p` centralizes the `p`-complement core of `M`. -/
theorem opiCoreInG_fittingInG_singleton_le_centralizer_opiCoreInG_singleton_compl_maximal
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hHsolv : IsSolvable ↥H)
    (hAH : cFittingInG M A0 ≤ H)
    (hDpM : opiCoreInG ({p} : Set ℕ) (fittingInG H) ≤ M) :
    opiCoreInG ({p} : Set ℕ) (fittingInG H) ≤
      Subgroup.centralizer (opiCoreInG ({p} : Set ℕ)ᶜ M : Set G) := by
  let Dp : Subgroup G := opiCoreInG ({p} : Set ℕ) (fittingInG H)
  let N : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ M
  change Dp ≤ Subgroup.centralizer (N : Set G)
  have hOFM_le_OA : opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M) ≤
      opiCoreInG ({p} : Set ℕ)ᶜ (cFittingInG M A0) :=
    opiCoreInG_singleton_compl_fittingInG_le_opiCoreInG_singleton_compl_cFittingInG
      hA0
  have hOA_le_OH : opiCoreInG ({p} : Set ℕ)ᶜ (cFittingInG M A0) ≤
      opiCoreInG ({p} : Set ℕ)ᶜ H :=
    opiCoreInG_cFittingInG_singleton_compl_le_opiCoreInG_singleton_compl
      hG hM hA0 hHsolv hAH hp
  have hOFM_le_OH : opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M) ≤
      opiCoreInG ({p} : Set ℕ)ᶜ H :=
    hOFM_le_OA.trans hOA_le_OH
  have hDp_cent_OFM : Dp ≤
      Subgroup.centralizer (opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M) : Set G) := by
    dsimp [Dp]
    exact opiCoreInG_fittingInG_le_centralizer_of_le_opiCoreInG_compl
      ({p} : Set ℕ) hOFM_le_OH
  have hN_M : N ≤ M := by
    dsimp [N]
    exact opiCoreInG_le ({p} : Set ℕ)ᶜ M
  have hDp_norm_N : Dp ≤ Subgroup.normalizer (N : Set G) := by
    dsimp [N]
    exact hDpM.trans (le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ M)
  have hDp_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ) Dp := by
    dsimp [Dp]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ) (fittingInG H)
  have hN_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ N := by
    dsimp [N]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ M
  have hCop : Nat.Coprime (Nat.card ↥Dp) (Nat.card ↥N) :=
    coprime_card_of_isPiSubgroup_of_isPiSubgroup_compl hDp_pi hN_pi
  haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  haveI hNsolv : IsSolvable ↥N :=
    solvable_of_solvable_injective (f := Subgroup.inclusion hN_M)
      (Subgroup.inclusion_injective hN_M)
  have hFN_le_OFM : fittingInG N ≤ opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M) := by
    dsimp [N]
    exact fittingInG_opiCoreInG_singleton_compl_le_opiCoreInG_singleton_compl_fittingInG M
  have hDp_cent_FN : Dp ≤ Subgroup.centralizer (fittingInG N : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (hDp_cent_OFM hd) y (hFN_le_OFM hy)
  exact le_centralizer_of_coprime_normalizes_of_le_centralizer_fittingInG
    hDp_norm_N hCop hDp_cent_FN

/-- BG (8.8): the `p`-complement core of `M` lies in `H` once `D_p` lies in
`M` and the Prop 1.4 centralizer bridge is available. -/
theorem opiCoreInG_singleton_compl_maximal_le_of_fittingInG_singleton_le_maximal
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G) (hH : H ∈ maximalSubgroups G)
    (hpM : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hpH : p ∈ (Nat.card ↥(fittingInG H)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hHsolv : IsSolvable ↥H)
    (hAH : cFittingInG M A0 ≤ H)
    (hDpM : opiCoreInG ({p} : Set ℕ) (fittingInG H) ≤ M) :
    opiCoreInG ({p} : Set ℕ)ᶜ M ≤ H := by
  let Dp : Subgroup G := opiCoreInG ({p} : Set ℕ) (fittingInG H)
  let K : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ M
  change K ≤ H
  have hDp_H : Dp ≤ H := by
    dsimp [Dp]
    exact (opiCoreInG_le ({p} : Set ℕ) (fittingInG H)).trans (fittingInG_le H)
  have hDp_norm_H : (Dp.subgroupOf H).Normal := by
    dsimp [Dp]
    exact opiCoreInG_fittingInG_subgroupOf_normal ({p} : Set ℕ) H
  have hDp_ne : Dp ≠ ⊥ := by
    dsimp [Dp]
    exact opiCoreInG_singleton_fittingInG_ne_bot_of_mem_primeFactors hpH
  have hNormalizer_Dp_eq_H : Subgroup.normalizer (Dp : Set G) = H :=
    normalizer_eq_of_normal_of_mem_maximal hG hH hDp_norm_H hDp_ne hDp_H
  have hDp_cent_K : Dp ≤ Subgroup.centralizer (K : Set G) := by
    dsimp [Dp, K]
    exact opiCoreInG_fittingInG_singleton_le_centralizer_opiCoreInG_singleton_compl_maximal
      hG hM hpM hA0 hHsolv hAH hDpM
  have hK_cent_Dp : K ≤ Subgroup.centralizer (Dp : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (Subgroup.mem_centralizer_iff.mp (hDp_cent_K hd) x hx).symm
  exact hK_cent_Dp.trans (by
    simpa [hNormalizer_Dp_eq_H] using Subgroup.centralizer_le_normalizer (Dp : Set G))

/-- BG (8.8), reverse inclusion: once `O_{p'}(M)` lies in `H`, it is absorbed by
`O_{p'}(H)`. -/
theorem opiCoreInG_singleton_compl_maximal_le_opiCoreInG_singleton_compl_of_le_maximal
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hHsolv : IsSolvable ↥H)
    (hAH : cFittingInG M A0 ≤ H)
    (hOMH : opiCoreInG ({p} : Set ℕ)ᶜ M ≤ H) :
    opiCoreInG ({p} : Set ℕ)ᶜ M ≤ opiCoreInG ({p} : Set ℕ)ᶜ H := by
  let R : Subgroup G := centerFittingOpCoreInG p M
  let K : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ M
  let NH : Subgroup G := Subgroup.normalizer (R : Set G) ⊓ H
  let CH : Subgroup G := Subgroup.centralizer (R : Set G) ⊓ H
  change K ≤ opiCoreInG ({p} : Set ℕ)ᶜ H
  have hR_H : R ≤ H := by
    dsimp [R]
    exact (centerFittingOpCoreInG_le_cFittingInG (q := p) hA0).trans hAH
  have hR_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ) R := by
    dsimp [R, centerFittingOpCoreInG]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ) (centerFittingInG M)
  have hR_ne : R ≠ ⊥ := by
    dsimp [R]
    exact centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hp
  have hNormalizer_R_eq_M : Subgroup.normalizer (R : Set G) = M := by
    dsimp [R]
    exact normalizer_centerFittingOpCoreInG_eq_of_ne_bot hG hM hR_ne
  have hK_NH : K ≤ NH := by
    intro x hx
    refine ⟨?_, hOMH hx⟩
    have hxM : x ∈ M := by
      dsimp [K] at hx
      exact opiCoreInG_le ({p} : Set ℕ)ᶜ M hx
    simpa [hNormalizer_R_eq_M] using hxM
  have hK_norm_NH : (K.subgroupOf NH).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hK_NH]
    intro x hx
    have hxM : x ∈ M := by
      have hxN : x ∈ Subgroup.normalizer (R : Set G) := hx.1
      simpa [hNormalizer_R_eq_M] using hxN
    dsimp [K]
    exact le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ M hxM
  have hK_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ K := by
    dsimp [K]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ M
  have hK_le_ONH : K ≤ opiCoreInG ({p} : Set ℕ)ᶜ NH :=
    le_opiCoreInG_of_normal_of_isPiSubgroup hK_NH hK_norm_NH hK_pi
  have hONH_le_OCH : opiCoreInG ({p} : Set ℕ)ᶜ NH ≤ opiCoreInG ({p} : Set ℕ)ᶜ CH := by
    dsimp [NH, CH]
    exact opiCoreInG_singleton_compl_normalizer_inf_le_centralizer_inf hR_H hR_pi
  have hR_p : IsPGroup p ↥R :=
    OddOrder.GroupTheory.isPGroup_of_isPiSubgroup_singleton hR_pi
  have hOCH_le_OH : opiCoreInG ({p} : Set ℕ)ᶜ CH ≤ opiCoreInG ({p} : Set ℕ)ᶜ H := by
    dsimp [CH]
    exact OddOrder.BG.Ch2.S07.opiCoreInG_centralizer_inf_le_opiCoreInG
      hHsolv hR_H hR_p
  exact hK_le_ONH.trans (hONH_le_OCH.trans hOCH_le_OH)

/-- BG (8.8), first inclusion: if `D = F(H)` is already contained in `M`, then
`O_{p'}(H)` is contained in `O_{p'}(M)`. -/
theorem opiCoreInG_singleton_compl_le_opiCoreInG_singleton_compl_of_fittingInG_le_maximal
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M H : Subgroup G} (hM : M ∈ maximalSubgroups G) (hH : H ∈ maximalSubgroups G)
    (hpH : p ∈ (Nat.card ↥(fittingInG H)).primeFactors)
    (hFH_le_M : fittingInG H ≤ M)
    (hOpComplH_le_M : opiCoreInG ({p} : Set ℕ)ᶜ H ≤ M) :
    opiCoreInG ({p} : Set ℕ)ᶜ H ≤ opiCoreInG ({p} : Set ℕ)ᶜ M := by
  let Dp : Subgroup G := opiCoreInG ({p} : Set ℕ) (fittingInG H)
  let K : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ H
  let NM : Subgroup G := Subgroup.normalizer (Dp : Set G) ⊓ M
  let CM : Subgroup G := Subgroup.centralizer (Dp : Set G) ⊓ M
  change K ≤ opiCoreInG ({p} : Set ℕ)ᶜ M
  have hDp_H : Dp ≤ H := by
    dsimp [Dp]
    exact (opiCoreInG_le ({p} : Set ℕ) (fittingInG H)).trans (fittingInG_le H)
  have hDp_norm_H : (Dp.subgroupOf H).Normal := by
    dsimp [Dp]
    exact opiCoreInG_fittingInG_subgroupOf_normal ({p} : Set ℕ) H
  have hDp_ne : Dp ≠ ⊥ := by
    dsimp [Dp]
    exact opiCoreInG_singleton_fittingInG_ne_bot_of_mem_primeFactors hpH
  have hNormalizer_Dp_eq_H : Subgroup.normalizer (Dp : Set G) = H :=
    normalizer_eq_of_normal_of_mem_maximal hG hH hDp_norm_H hDp_ne hDp_H
  have hK_le_NM : K ≤ NM := by
    intro x hx
    refine ⟨?_, hOpComplH_le_M hx⟩
    have hxH : x ∈ H := by
      dsimp [K] at hx
      exact opiCoreInG_le ({p} : Set ℕ)ᶜ H hx
    simpa [hNormalizer_Dp_eq_H] using hxH
  have hK_norm_NM : (K.subgroupOf NM).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hK_le_NM]
    intro x hx
    have hxH : x ∈ H := by
      have hxN : x ∈ Subgroup.normalizer (Dp : Set G) := hx.1
      simpa [hNormalizer_Dp_eq_H] using hxN
    dsimp [K]
    exact le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ H hxH
  have hK_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ K := by
    dsimp [K]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ H
  have hK_le_ONM : K ≤ opiCoreInG ({p} : Set ℕ)ᶜ NM :=
    le_opiCoreInG_of_normal_of_isPiSubgroup hK_le_NM hK_norm_NM hK_pi
  have hDp_M : Dp ≤ M := by
    dsimp [Dp]
    exact (opiCoreInG_le ({p} : Set ℕ) (fittingInG H)).trans hFH_le_M
  have hDp_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ) Dp := by
    dsimp [Dp]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ) (fittingInG H)
  have hONM_le_OCM : opiCoreInG ({p} : Set ℕ)ᶜ NM ≤ opiCoreInG ({p} : Set ℕ)ᶜ CM := by
    dsimp [NM, CM]
    exact opiCoreInG_singleton_compl_normalizer_inf_le_centralizer_inf hDp_M hDp_pi
  haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hDp_p : IsPGroup p ↥Dp := by
    dsimp [Dp]
    exact isPGroup_opiCoreInG_singleton (fittingInG H)
  have hOCM_le_OM : opiCoreInG ({p} : Set ℕ)ᶜ CM ≤ opiCoreInG ({p} : Set ℕ)ᶜ M := by
    dsimp [CM]
    exact OddOrder.BG.Ch2.S07.opiCoreInG_centralizer_inf_le_opiCoreInG
      hMsolv hDp_M hDp_p
  exact hK_le_ONM.trans (hONM_le_OCM.trans hOCM_le_OM)

/-- BG (8.6), Fitting-prime support form: if `A = C_F(M)(A0)` lies in `H`, then
`π(F(H)) ⊆ π(A)` in the non-p-group case. -/
theorem primesOf_fittingInG_subset_primesOf_cFittingInG_of_cFittingInG_le_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hAH : cFittingInG M A0 ≤ H) :
    OddOrder.BG.Ch2.S07.primesOf (fittingInG H) ⊆
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) := by
  intro q hqF
  have hqF_mem : q ∈ (Nat.card ↥(fittingInG H)).primeFactors := by
    simpa [OddOrder.BG.Ch2.S07.primesOf] using hqF
  haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqF_mem⟩
  by_contra hqA
  have hqcomp : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ := hqA
  have hObot : opiCoreInG ({q} : Set ℕ) H = ⊥ :=
    opiCoreInG_singleton_eq_bot_of_cFittingInG_le_of_not_pGroup
      hG hM hA0 hm hFnp hA hqcomp hAH
  exact opiCoreInG_singleton_ne_bot_of_mem_primeFactors_fittingInG hqF_mem hObot

/-- BG (8.6), pi-subgroup form: if `A = C_F(M)(A0)` lies in `H`, then `F(H)`
is a `π(F(M))`-subgroup in the non-p-group case. -/
theorem fittingInG_isPiSubgroup_primesOf_fittingInG_of_cFittingInG_le_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hAH : cFittingInG M A0 ≤ H) :
    Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))
      (fittingInG H) := by
  have hA0F : A0 ≤ fittingInG M := isMaxElemAbelianIn_le hA0
  have hPrimes :
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) =
        OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    dsimp [cFittingInG]
    exact primesOf_cFitting_eq_primesOf_fittingInG hA0F
  rw [← hPrimes]
  exact primesOf_fittingInG_subset_primesOf_cFittingInG_of_cFittingInG_le_of_not_pGroup
    hG hM hA0 hm hFnp hA hAH

/-- BG (8.6), Fitting-prime support form with Hypothesis 7.1 supplied by BG (8.5). -/
theorem primesOf_fittingInG_subset_primesOf_cFittingInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hAH : cFittingInG M A0 ≤ H) :
    OddOrder.BG.Ch2.S07.primesOf (fittingInG H) ⊆
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) :=
  primesOf_fittingInG_subset_primesOf_cFittingInG_of_cFittingInG_le_of_not_pGroup
    hG hM hA0 hm hFnp
    (hypothesis71_cFittingInG_of_not_pGroup hG hM hp hA0 hFnp) hAH

/-- BG (8.6), pi-subgroup form with Hypothesis 7.1 supplied by BG (8.5). -/
theorem fittingInG_isPiSubgroup_primesOf_fittingInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hAH : cFittingInG M A0 ≤ H) :
    Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))
      (fittingInG H) :=
  fittingInG_isPiSubgroup_primesOf_fittingInG_of_cFittingInG_le_of_not_pGroup
    hG hM hA0 hm hFnp
    (hypothesis71_cFittingInG_of_not_pGroup hG hM hp hA0 hFnp) hAH

/-- **BG Theorem 8.1(a)** (mmd L2319-2321): `M ∈ ℳ`, `p ∈ π(F(M))`, `A₀ ∈ ℰ_p^*(F(M))`,
`m(A₀) ≥ 3`。`F(M)` が `p`-群でなければ `C_{F(M)}(A₀) ∈ 𝒰`。 -/
theorem cFitting_isUniquelyMaximal_of_not_pGroup [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    {A₀ : Subgroup G} (hA₀ : isMaxElemAbelianIn p A₀ (fittingInG M))
    (hm : 3 ≤ rank ↥A₀)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M)) :
    IsUniquelyMaximal (Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M) := by
  let A : Subgroup G := Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M
  change IsUniquelyMaximal A
  have hA0F : A₀ ≤ fittingInG M := isMaxElemAbelianIn_le hA₀
  have hA_le_M : A ≤ M := by
    dsimp [A]
    exact inf_le_right.trans (fittingInG_le M)
  have hA_proper : A < ⊤ := by
    dsimp [A]
    exact cFitting_lt_top_of_mem_maximal hM
  have hA_ne : A ≠ ⊥ := by
    dsimp [A]
    exact cFitting_ne_bot_of_isMaxElemAbelianIn hp hA₀
  have hPrimesA :
      OddOrder.BG.Ch2.S07.primesOf A = OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    dsimp [A]
    exact primesOf_cFitting_eq_primesOf_fittingInG hA0F
  have hCentralizer_le_M : Subgroup.centralizer (A : Set G) ≤ M := by
    dsimp [A]
    exact centralizer_cFitting_le_maximal_of_not_isPGroup hG hM hA0F hFnp
  have hCpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf A)
      (Subgroup.centralizer (A : Set G)) := by
    dsimp [A]
    exact centralizer_cFitting_isPiSubgroup_of_not_pGroup hG hM hA₀ hFnp
  have hCenterRank : 3 ≤ rank ↥(Subgroup.center ↥A) := by
    dsimp [A]
    exact three_le_rank_center_cFitting_of_isMaxElemAbelianIn hA₀ hm
  refine IsUniquelyMaximal.of_unique_maximal hA_proper hM hA_le_M ?_
  intro H hH hAH
  have hHco : IsCoatom H := hH
  have hH_mem : H ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hH
  have hAH_cFitting : cFittingInG M A₀ ≤ H := by
    dsimp [A] at hAH
    exact hAH
  have hFittingH_pi : Subgroup.IsPiSubgroup
      (OddOrder.BG.Ch2.S07.primesOf (fittingInG M)) (fittingInG H) :=
    fittingInG_isPiSubgroup_primesOf_fittingInG_of_not_pGroup
      hG hM hp hA₀ hm hFnp hAH_cFitting
  have hSigma_subset_pi : OddOrder.BG.Ch2.S07.primesOf (fittingInG H) ⊆
      OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    intro q hq
    exact hFittingH_pi q (by simpa [OddOrder.BG.Ch2.S07.primesOf] using hq)
  haveI hH_solvable : IsSolvable ↥H := hG.solvable_of_lt_top H hHco.lt_top
  have hO_sigma_compl_bot :
      opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (fittingInG H))ᶜ H = ⊥ :=
    opiCoreInG_primesOf_fittingInG_compl_eq_bot
  have hO_pi_compl_le_sigma :
      opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ H ≤
        opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (fittingInG H))ᶜ H := by
    rw [opiCoreInG, opiCoreInG]
    refine Subgroup.map_mono (Ch03.oPiCore_mono ?_ ↥H)
    intro q hq_not_pi hq_sigma
    exact hq_not_pi (hSigma_subset_pi hq_sigma)
  have hO_pi_compl_bot :
      opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ H = ⊥ := by
    exact le_bot_iff.mp (by rw [← hO_sigma_compl_bot]; exact hO_pi_compl_le_sigma)
  have hPi_subset_sigma : OddOrder.BG.Ch2.S07.primesOf (fittingInG M) ⊆
      OddOrder.BG.Ch2.S07.primesOf (fittingInG H) :=
    primesOf_fittingInG_subset_of_opiCoreInG_compl_eq_bot
      hG hM hA₀ hH_solvable hAH_cFitting hSigma_subset_pi hO_sigma_compl_bot
  have hSigma_eq_pi : OddOrder.BG.Ch2.S07.primesOf (fittingInG H) =
      OddOrder.BG.Ch2.S07.primesOf (fittingInG M) :=
    Set.Subset.antisymm hSigma_subset_pi hPi_subset_sigma
  have hFittingH_le_M : fittingInG H ≤ M := by
    have hFH_nilp : Group.IsNilpotent ↥(fittingInG H) := fittingInG_isNilpotent H
    refine le_of_sylow_le_of_nilpotent hFH_nilp ?_
    intro r
    haveI : Fact (r : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors r.2⟩
    let S : Subgroup G := ((default : Sylow (r : ℕ) ↥(fittingInG H)) :
      Subgroup ↥(fittingInG H)).map (fittingInG H).subtype
    have hS_le_core : S ≤ opiCoreInG ({(r : ℕ)} : Set ℕ) (fittingInG H) := by
      dsimp [S]
      exact le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
        hFH_nilp (Subgroup.map_subtype_le _)
        ((default : Sylow (r : ℕ) ↥(fittingInG H)).isPGroup'.map
          (fittingInG H).subtype)
    have hrFH : (r : ℕ) ∈ (Nat.card ↥(fittingInG H)).primeFactors := r.2
    have hrFM_primes : (r : ℕ) ∈ OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
      rw [← hSigma_eq_pi]
      exact hrFH
    have hrFM : (r : ℕ) ∈ (Nat.card ↥(fittingInG M)).primeFactors := hrFM_primes
    exact hS_le_core.trans
      (opiCoreInG_fittingInG_singleton_le_maximal_of_cFittingInG_le_of_not_pGroup
        hG hM hp hA₀ hFnp hH_solvable hAH_cFitting hrFM)
  have hOpComplH_le_M : opiCoreInG ({p} : Set ℕ)ᶜ H ≤ M :=
    opiCoreInG_singleton_compl_le_maximal_of_cFittingInG_le_of_primes_eq
      hG hM hp hA₀ hH_solvable hAH_cFitting hSigma_eq_pi
  have hpFittingH : p ∈ (Nat.card ↥(fittingInG H)).primeFactors := by
    have hpFH_primes : p ∈ OddOrder.BG.Ch2.S07.primesOf (fittingInG H) := by
      rw [hSigma_eq_pi]
      exact hp
    simpa [OddOrder.BG.Ch2.S07.primesOf] using hpFH_primes
  have hOpComplH_le_OpComplM : opiCoreInG ({p} : Set ℕ)ᶜ H ≤
      opiCoreInG ({p} : Set ℕ)ᶜ M :=
    opiCoreInG_singleton_compl_le_opiCoreInG_singleton_compl_of_fittingInG_le_maximal
      hG hM hH_mem hpFittingH hFittingH_le_M hOpComplH_le_M
  have hDpH_le_M : opiCoreInG ({p} : Set ℕ) (fittingInG H) ≤ M :=
    (opiCoreInG_le ({p} : Set ℕ) (fittingInG H)).trans hFittingH_le_M
  have hOpComplM_le_H : opiCoreInG ({p} : Set ℕ)ᶜ M ≤ H :=
    opiCoreInG_singleton_compl_maximal_le_of_fittingInG_singleton_le_maximal
      hG hM hH_mem hp hpFittingH hA₀ hH_solvable hAH_cFitting hDpH_le_M
  have hOpComplM_le_OpComplH : opiCoreInG ({p} : Set ℕ)ᶜ M ≤
      opiCoreInG ({p} : Set ℕ)ᶜ H :=
    opiCoreInG_singleton_compl_maximal_le_opiCoreInG_singleton_compl_of_le_maximal
      hG hM hp hA₀ hH_solvable hAH_cFitting hOpComplM_le_H
  have hOpCompl_eq : opiCoreInG ({p} : Set ℕ)ᶜ H =
      opiCoreInG ({p} : Set ℕ)ᶜ M :=
    le_antisymm hOpComplH_le_OpComplM hOpComplM_le_OpComplH
  obtain ⟨r, hrFM, hrp⟩ :=
    exists_primeFactor_ne_of_mem_primeFactor_not_isPGroup
      (H := ↥(fittingInG M)) hp hFnp p
  haveI hRprime : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hrFM⟩
  have hBr_ne : centerFittingOpCoreInG r M ≠ ⊥ :=
    centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hrFM
  have hBr_le_OpComplM : centerFittingOpCoreInG r M ≤
      opiCoreInG ({p} : Set ℕ)ᶜ M :=
    centerFittingOpCoreInG_le_opiCoreInG_singleton_compl_of_ne
      hG hM hA₀ (hG.solvable_of_mem_maximalSubgroups hM) (by
        dsimp [cFittingInG]
        exact inf_le_right.trans (fittingInG_le M)) hp hrFM (fun hpr => hrp hpr.symm)
  have hOpComplM_ne : opiCoreInG ({p} : Set ℕ)ᶜ M ≠ ⊥ := by
    intro hbot
    exact hBr_ne (le_bot_iff.mp (by
      rw [← hbot]
      exact hBr_le_OpComplM))
  have hOpComplH_ne : opiCoreInG ({p} : Set ℕ)ᶜ H ≠ ⊥ := by
    rw [hOpCompl_eq]
    exact hOpComplM_ne
  have hOpComplH_H : opiCoreInG ({p} : Set ℕ)ᶜ H ≤ H :=
    opiCoreInG_le ({p} : Set ℕ)ᶜ H
  have hOpComplH_norm_H : ((opiCoreInG ({p} : Set ℕ)ᶜ H).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hOpComplH_H]
    exact le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ H
  have hNormalizer_OpComplH_eq_H :
      Subgroup.normalizer (opiCoreInG ({p} : Set ℕ)ᶜ H : Set G) = H :=
    normalizer_eq_of_normal_of_mem_maximal hG hH_mem hOpComplH_norm_H
      hOpComplH_ne hOpComplH_H
  have hOpComplM_M : opiCoreInG ({p} : Set ℕ)ᶜ M ≤ M :=
    opiCoreInG_le ({p} : Set ℕ)ᶜ M
  have hOpComplM_norm_M : ((opiCoreInG ({p} : Set ℕ)ᶜ M).subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hOpComplM_M]
    exact le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ M
  have hNormalizer_OpComplM_eq_M :
      Subgroup.normalizer (opiCoreInG ({p} : Set ℕ)ᶜ M : Set G) = M :=
    normalizer_eq_of_normal_of_mem_maximal hG hM hOpComplM_norm_M
      hOpComplM_ne hOpComplM_M
  calc
    H = Subgroup.normalizer (opiCoreInG ({p} : Set ℕ)ᶜ H : Set G) :=
      hNormalizer_OpComplH_eq_H.symm
    _ = Subgroup.normalizer (opiCoreInG ({p} : Set ℕ)ᶜ M : Set G) := by
      rw [hOpCompl_eq]
    _ = M := hNormalizer_OpComplM_eq_M

/-- If `F(M)` is a nontrivial `p`-group, then its prime support is exactly `{p}`. -/
theorem primesOf_fittingInG_eq_singleton_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {M : Subgroup G} (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hFp : IsPGroup p ↥(fittingInG M)) :
    OddOrder.BG.Ch2.S07.primesOf (fittingInG M) = ({p} : Set ℕ) := by
  have hF_ne_bot : fittingInG M ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥(fittingInG M) = 1 := Subgroup.card_eq_one.mpr hbot
    rw [hcard, Nat.primeFactors_one] at hp
    exact Finset.notMem_empty p hp
  obtain ⟨n, hn⟩ := hFp.exists_card_eq
  have hn0 : n ≠ 0 := by
    intro hn_zero
    apply hF_ne_bot
    rw [Subgroup.eq_bot_iff_card, hn, hn_zero, pow_zero]
  ext q
  simp only [OddOrder.BG.Ch2.S07.primesOf, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [hn, Nat.primeFactors_prime_pow hn0 (Fact.out : p.Prime), Finset.mem_singleton]

/-- BG 8.1(b), first p-group bridge: if `F(M)` is a `p`-group, then
`O_{p'}(M)=1`. This is the formal version of
`F(O_{p'}(M)) ≤ O_{p'}(F(M)) = 1`. -/
theorem opiCoreInG_singleton_compl_eq_bot_of_fittingInG_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] {M : Subgroup G} [IsSolvable ↥M]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hFp : IsPGroup p ↥(fittingInG M)) :
    opiCoreInG ({p} : Set ℕ)ᶜ M = ⊥ := by
  have hπ : OddOrder.BG.Ch2.S07.primesOf (fittingInG M) = ({p} : Set ℕ) :=
    primesOf_fittingInG_eq_singleton_of_isPGroup hp hFp
  have hcore : opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ M = ⊥ :=
    opiCoreInG_primesOf_fittingInG_compl_eq_bot
  simpa [hπ] using hcore

/-- BG 8.1(b), second p-group bridge: if `F(M)` is a `p`-group, then
`F(M)=O_p(M)` in the ambient group. -/
theorem fittingInG_eq_opiCoreInG_singleton_of_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hFp : IsPGroup p ↥(fittingInG M)) :
    fittingInG M = opiCoreInG ({p} : Set ℕ) M := by
  apply le_antisymm
  · have hFpi : Subgroup.IsPiSubgroup ({p} : Set ℕ) (fittingInG M) :=
      OddOrder.GroupTheory.isPiSubgroup_singleton_of_isPGroup hFp
    exact le_opiCoreInG_of_normal_of_isPiSubgroup (fittingInG_le M)
      (fittingInG_subgroupOf_normal M) hFpi
  · exact opiCoreInG_singleton_le_fittingInG M

/-- If the `p'`-core is trivial, the `O_{p',p}` layer collapses to the `p`-core. -/
theorem oPiPrimePiCore_singleton_eq_oPiCore_singleton_of_compl_bot
    {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (h : Ch03.oPiCore (({p} : Set ℕ)ᶜ) X = ⊥) :
    Ch03.oPiPrimePiCore ({p} : Set ℕ) X = Ch03.oPiCore ({p} : Set ℕ) X := by
  have key : ∀ (N : Subgroup X) [N.Normal], N = ⊥ →
      Subgroup.comap (QuotientGroup.mk' N) (Ch03.oPiCore ({p} : Set ℕ) (X ⧸ N))
        = Ch03.oPiCore ({p} : Set ℕ) X := by
    intro N _ hN
    subst hN
    rw [show (QuotientGroup.mk' (⊥ : Subgroup X))
        = (QuotientGroup.quotientBot (G := X)).symm.toMonoidHom from rfl]
    rw [Subgroup.comap_equiv_eq_map_symm']
    simp only [MulEquiv.symm_symm]
    exact Ch03.oPiCore.map_eq_of_mulEquiv ({p} : Set ℕ) (QuotientGroup.quotientBot (G := X))
  -- `oPiPrimePiCore {p} X` unfolds definitionally to the `comap` at `{q | q ∉ {p}} = {p}ᶜ`.
  exact key _ h

/-- BG 8.1(b), third p-group bridge: when `F(M)` is a `p`-group, `O_{p',p}(M)`,
viewed in `G`, lies in `F(M)`. -/
theorem oPiPrimePiCore_singleton_map_le_fittingInG_of_fittingInG_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] {M : Subgroup G} [IsSolvable ↥M]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hFp : IsPGroup p ↥(fittingInG M)) :
    (Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥M).map M.subtype ≤ fittingInG M := by
  have hmap_bot : (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥M).map M.subtype = ⊥ := by
    simpa [opiCoreInG] using
      (opiCoreInG_singleton_compl_eq_bot_of_fittingInG_isPGroup (M := M) hp hFp)
  have hbot : Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥M = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective
      (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥M) M.subtype_injective).mp hmap_bot
  have hcollapse :
      Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥M = Ch03.oPiCore ({p} : Set ℕ) ↥M :=
    oPiPrimePiCore_singleton_eq_oPiCore_singleton_of_compl_bot hbot
  calc
    (Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥M).map M.subtype
        = (Ch03.oPiCore ({p} : Set ℕ) ↥M).map M.subtype := by rw [hcollapse]
    _ = opiCoreInG ({p} : Set ℕ) M := rfl
    _ ≤ fittingInG M := opiCoreInG_singleton_le_fittingInG M

/-- BG 8.1(b), fourth p-group bridge: Theorem 6.1 puts every `SCN₃(P)` subgroup in
`O_{p',p}(M)`, hence in `F(M)` when `F(M)` is a `p`-group. -/
theorem scn3_map_le_fittingInG_of_fittingInG_isPGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    A.map M.subtype ≤ fittingInG M := by
  have hp_dvd_G : p ∣ Nat.card G :=
    (Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.card_subgroup_dvd_card (fittingInG M))
  have hp_odd_prop : Odd p := hG.odd.of_dvd_nat hp_dvd_G
  have hp_odd : p ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hp_odd_prop
    omega
  have hsolvM : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hoddM : Odd (Nat.card ↥M) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  haveI hAcomm : IsMulCommutative A :=
    IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
      congrArg Subtype.val (isMulCommutative_iff_of_setLike.mp hA.1.isMulCommutative
        (⟨a, hAP ha⟩ : ↥(P : Subgroup ↥M)) (Subgroup.mem_subgroupOf.mpr ha)
        ⟨b, hAP hb⟩ (Subgroup.mem_subgroupOf.mpr hb))
  have hA_norm : (P : Subgroup ↥M) ≤ Subgroup.normalizer (A : Set ↥M) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mp hA.1.isNormal
  have hA_le_OPP : A ≤ Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥M :=
    OddOrder.BG.AppA.thmA4b hp_odd hsolvM hoddM P hAP hA_norm
  exact (Subgroup.map_mono hA_le_OPP).trans
    (oPiPrimePiCore_singleton_map_le_fittingInG_of_fittingInG_isPGroup (M := M) hp hFp)

/-- If a nontrivial subgroup `K ≤ S.map subtype` has normalizer exactly controlled by a
maximal subgroup `M`, then the image of the Sylow subgroup `S` of `M` is a full Sylow
subgroup of the ambient minimal simple group. -/
theorem sylow_map_mem_range_of_normalizer_le_normalizer [Finite G]
    (hG : IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime] (S : Sylow p ↥M)
    (hK_ne_bot : K ≠ ⊥) (hK_le_SH : K ≤ (S : Subgroup ↥M).map M.subtype)
    (hM_norm_K : M ≤ Subgroup.normalizer (K : Set G))
    (hN_SH_le_NK : Subgroup.normalizer (((S : Subgroup ↥M).map M.subtype : Subgroup G) : Set G) ≤
      Subgroup.normalizer (K : Set G)) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = (S : Subgroup ↥M).map M.subtype := by
  classical
  haveI : IsSimpleGroup G := hG.simple
  set SH : Subgroup G := (S : Subgroup ↥M).map M.subtype with hSH_def
  have hSH_p : IsPGroup p SH := S.isPGroup'.map M.subtype
  obtain ⟨PH, hSH_le_PH⟩ := IsPGroup.exists_le_sylow hSH_p
  have hK_le_M : K ≤ M := by
    exact hK_le_SH.trans (hSH_def ▸ Subgroup.map_subtype_le _)
  have hNK_eq_M : Subgroup.normalizer K = M :=
    OddOrder.Isaacs.Ch07.maximal_eq_normalizer_of_M_normalizes
      (mem_maximalSubgroups.mp hM) hK_ne_bot hK_le_M hM_norm_K
  have hPH_subOf_p : IsPGroup p ((PH : Subgroup G).subgroupOf M) :=
    PH.isPGroup'.comap_subtype
  have hS_le_PH_subOf : (S : Subgroup ↥M) ≤ (PH : Subgroup G).subgroupOf M := by
    intro s hs
    have : M.subtype s ∈ SH := ⟨s, hs, rfl⟩
    exact hSH_le_PH this
  have hS_eq : (PH : Subgroup G).subgroupOf M = (S : Subgroup ↥M) :=
    S.is_maximal' hPH_subOf_p hS_le_PH_subOf
  suffices hSH_eq : SH = (PH : Subgroup G) by
    exact ⟨PH, hSH_eq.symm.trans hSH_def⟩
  refine le_antisymm hSH_le_PH ?_
  by_contra hPH_not_le
  have hSH_lt_PH : SH < (PH : Subgroup G) := lt_of_le_of_ne hSH_le_PH (by
    intro h
    exact hPH_not_le (le_of_eq h.symm))
  haveI : Group.IsNilpotent ↥(PH : Subgroup G) := PH.isPGroup'.isNilpotent
  have hNC : NormalizerCondition ↥(PH : Subgroup G) :=
    Group.normalizerCondition_of_isNilpotent (G := ↥(PH : Subgroup G))
  have hSH_subOf_lt_top : SH.subgroupOf (PH : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hPH_not_le htop
  have hlt := hNC (SH.subgroupOf (PH : Subgroup G)) hSH_subOf_lt_top
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hSH_le_PH, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  set tG : G := (t : G) with htG_def
  have htG_norm_K : tG ∈ Subgroup.normalizer (K : Set G) := hN_SH_le_NK ht_norm
  have htG_in_M : tG ∈ M := hNK_eq_M ▸ htG_norm_K
  have htG_in_PH : tG ∈ (PH : Subgroup G) := t.2
  have htM_in_S : (⟨tG, htG_in_M⟩ : ↥M) ∈ (S : Subgroup ↥M) := by
    rw [← hS_eq, Subgroup.mem_subgroupOf]
    exact htG_in_PH
  have htG_in_SH : tG ∈ SH := ⟨⟨tG, htG_in_M⟩, htM_in_S, rfl⟩
  exact ht_not htG_in_SH

/-- If `F(M)` is a `p`-group, it lies in every Sylow `p`-subgroup of `M`, viewed in
`G`. -/
theorem fittingInG_le_sylow_map_of_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] {M : Subgroup G} (P : Sylow p ↥M)
    (hFp : IsPGroup p ↥(fittingInG M)) :
    fittingInG M ≤ (P : Subgroup ↥M).map M.subtype := by
  rw [fittingInG_eq_opiCoreInG_singleton_of_isPGroup (M := M) hFp, opiCoreInG]
  rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := ↥M) p]
  exact Subgroup.map_mono (OddOrder.Isaacs.Ch01.opCore_le P)

/-- A subgroup of the image of a Sylow subgroup that centralizes the image of an
`SCN₃(P)` subgroup already lies in that image. -/
theorem le_scn3_map_of_le_sylow_map_of_le_centralizer_map
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) {A : Subgroup ↥M} {B : Subgroup G}
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M)))
    (hB_le_P : B ≤ (P : Subgroup ↥M).map M.subtype)
    (hB_le_cent : B ≤ Subgroup.centralizer (A.map M.subtype : Set G)) :
    B ≤ A.map M.subtype := by
  intro b hb
  obtain ⟨y, hyP, hy_eq⟩ := Subgroup.mem_map.mp (hB_le_P hb)
  have hy_cent : (⟨y, hyP⟩ : ↥(P : Subgroup ↥M)) ∈
      Subgroup.centralizer ((A.subgroupOf (P : Subgroup ↥M)) : Set ↥(P : Subgroup ↥M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzA : ((z : ↥(P : Subgroup ↥M)) : ↥M) ∈ A :=
      Subgroup.mem_subgroupOf.mp hz
    have hz_map : M.subtype ((z : ↥(P : Subgroup ↥M)) : ↥M) ∈ A.map M.subtype :=
      Subgroup.mem_map.mpr ⟨((z : ↥(P : Subgroup ↥M)) : ↥M), hzA, rfl⟩
    have hb_cent : b ∈ Subgroup.centralizer (A.map M.subtype : Set G) := hB_le_cent hb
    have hcommG :=
      Subgroup.mem_centralizer_iff.mp hb_cent
        (M.subtype ((z : ↥(P : Subgroup ↥M)) : ↥M)) hz_map
    have hcommM : ((z : ↥(P : Subgroup ↥M)) : ↥M) * y =
        y * ((z : ↥(P : Subgroup ↥M)) : ↥M) := by
      apply M.subtype_injective
      simpa [map_mul, hy_eq] using hcommG
    exact Subtype.ext hcommM
  have hyA_sub : (⟨y, hyP⟩ : ↥(P : Subgroup ↥M)) ∈
      A.subgroupOf (P : Subgroup ↥M) :=
    hA.1.centralizer_le hy_cent
  have hyA : y ∈ A := Subgroup.mem_subgroupOf.mp hyA_sub
  exact Subgroup.mem_map.mpr ⟨y, hyA, hy_eq⟩

/-- BG (8.10), first p-group form: when `F(M)` is a `p`-group, the nontrivial
`p`-core of `Z(F(M))` is absorbed by every local `SCN₃(P)` subgroup. -/
theorem centerFittingOpCoreInG_le_scn3_map_of_fittingInG_isPGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    centerFittingOpCoreInG p M ≤ A.map M.subtype := by
  apply le_scn3_map_of_le_sylow_map_of_le_centralizer_map P hA
  · exact ((centerFittingOpCoreInG_le_centerFittingInG p M).trans
        (centerFittingInG_le_fittingInG M)).trans
      (fittingInG_le_sylow_map_of_isPGroup P hFp)
  · intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hAF : A.map M.subtype ≤ fittingInG M :=
      scn3_map_le_fittingInG_of_fittingInG_isPGroup hG hM hp P hFp hAP hA
    have haF : a ∈ fittingInG M := hAF ha
    have hzZ : z ∈ centerFittingInG M :=
      centerFittingOpCoreInG_le_centerFittingInG p M hz
    exact (Subgroup.mem_centralizer_iff.mp
      (fittingInG_le_centralizer_centerFittingInG M haF) z hzZ).symm

/-- BG (8.10), centralizer form: when `F(M)` is a `p`-group, the ambient centralizer
of every local `SCN₃(P)` image is contained in `M`. -/
theorem centralizer_scn3_map_le_maximal_of_fittingInG_isPGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    Subgroup.centralizer (A.map M.subtype : Set G) ≤ M :=
  centralizer_le_maximal_of_centerFittingOpCoreInG_le hG hM
    (centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hp)
    (centerFittingOpCoreInG_le_scn3_map_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA)

/-- Inside `F(M)`, the centralizer of a local `SCN₃(P)` image is contained in that
image when `F(M)` is a `p`-group. -/
theorem centralizer_scn3_map_inf_fittingInG_le_scn3_map_of_fittingInG_isPGroup
    [Finite G] {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    Subgroup.centralizer (A.map M.subtype : Set G) ⊓ fittingInG M ≤ A.map M.subtype := by
  apply le_scn3_map_of_le_sylow_map_of_le_centralizer_map P hA
  · exact inf_le_right.trans (fittingInG_le_sylow_map_of_isPGroup P hFp)
  · exact inf_le_left

/-- If `x` centralizes the image of a local `SCN₃(P)` subgroup, that image lies in
`C_{F(M)}(<x>)`. -/
theorem scn3_map_le_centralizer_zpowers_inf_fittingInG_of_mem_centralizer
    {M : Subgroup G} {A : Subgroup ↥M} {x : G}
    (hAF : A.map M.subtype ≤ fittingInG M)
    (hxC : x ∈ Subgroup.centralizer (A.map M.subtype : Set G)) :
    A.map M.subtype ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M := by
  intro a haA
  refine ⟨?_, hAF haA⟩
  change a ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hcomm_eq : (a : G) * x = x * (a : G) :=
    Subgroup.mem_centralizer_iff.mp hxC (a : G) haA
  have hcomm : Commute (a : G) x := hcomm_eq
  exact (hcomm.symm.zpow_left n).eq

/-- BG (8.11), Prop 1.10 input for the p-group case: an element of `C_G(A)` satisfies
the self-centralizer condition on `C_{F(M)}(<x>)`. -/
theorem centralizer_zpowers_inf_fittingInG_self_of_mem_centralizer_scn3_map
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M)))
    {x : G} (hxC : x ∈ Subgroup.centralizer (A.map M.subtype : Set G)) :
    Subgroup.centralizer
        ((Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) : Set ↥(fittingInG M))
      ≤ (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) := by
  let Amap : Subgroup G := A.map M.subtype
  let C : Subgroup G := Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M
  have hAF : Amap ≤ fittingInG M := by
    dsimp [Amap]
    exact scn3_map_le_fittingInG_of_fittingInG_isPGroup hG hM hp P hFp hAP hA
  have hCFA : Subgroup.centralizer (Amap : Set G) ⊓ fittingInG M ≤ Amap := by
    dsimp [Amap]
    exact centralizer_scn3_map_inf_fittingInG_le_scn3_map_of_fittingInG_isPGroup
      P hFp hA
  have hA_le_C : Amap ≤ C := by
    dsimp [Amap, C]
    exact scn3_map_le_centralizer_zpowers_inf_fittingInG_of_mem_centralizer hAF hxC
  intro y hy
  rw [Subgroup.mem_subgroupOf]
  have hyA : (y : G) ∈ Amap := by
    apply hCFA
    rw [Subgroup.mem_inf]
    refine ⟨?_, y.2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    let aF : ↥(fittingInG M) := ⟨a, hAF ha⟩
    have haC : aF ∈ C.subgroupOf (fittingInG M) := by
      rw [Subgroup.mem_subgroupOf]
      exact hA_le_C ha
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy aF haC)
  exact hA_le_C hyA

/-- BG (8.11), containment form: `O_{p'}(C_G(A))` lies in `F(M)` in the p-group
case. -/
theorem opiCoreInG_singleton_compl_centralizer_scn3_map_le_fittingInG_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (A.map M.subtype : Set G)) ≤
      fittingInG M := by
  haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  let C : Subgroup G := Subgroup.centralizer (A.map M.subtype : Set G)
  let K : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ C
  change K ≤ fittingInG M
  intro x hxK
  have hxC : x ∈ C := by
    dsimp [K] at hxK
    exact opiCoreInG_le ({p} : Set ℕ)ᶜ C hxK
  have hxM : x ∈ M :=
    centralizer_scn3_map_le_maximal_of_fittingInG_isPGroup hG hM hp P hFp hAP hA hxC
  have hxpi_singleton : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ (Subgroup.zpowers x) := by
    intro r hr
    have hz_le_K : Subgroup.zpowers x ≤ K := Subgroup.zpowers_le.mpr hxK
    have hrK : r ∈ (Nat.card ↥K).primeFactors :=
      Nat.primeFactors_mono (Subgroup.card_dvd_of_le hz_le_K) Nat.card_pos.ne' hr
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ C r hrK
  have hxpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ
      (Subgroup.zpowers x) := by
    have hπ : OddOrder.BG.Ch2.S07.primesOf (fittingInG M) = ({p} : Set ℕ) :=
      primesOf_fittingInG_eq_singleton_of_isPGroup hp hFp
    simpa [hπ] using hxpi_singleton
  exact mem_fittingInG_of_centralizer_self_zpowers hxM
    (coprime_card_zpowers_fittingInG_of_isPiSubgroup_primesOf_compl hxpi)
    (centralizer_zpowers_inf_fittingInG_self_of_mem_centralizer_scn3_map
      hG hM hp P hFp hAP hA hxC)

/-- BG (8.11): if `F(M)` is a `p`-group, then
`O_{p'}(C_G(A)) = 1` for every local `SCN₃(P)` image `A`. -/
theorem opiCoreInG_singleton_compl_centralizer_scn3_map_eq_bot_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (A.map M.subtype : Set G)) = ⊥ := by
  exact eq_bot_of_le_of_isPiSubgroup_of_isPiSubgroup_compl
    (opiCoreInG_singleton_compl_centralizer_scn3_map_le_fittingInG_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA)
    (isPiSubgroup_singleton_of_isPGroup hFp)
    (isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ
      (Subgroup.centralizer (A.map M.subtype : Set G)))

/-- In a nontrivial finite `p`-group, `Z(L(G))` is nontrivial. -/
theorem zCenterLOdd_top_ne_bot_of_isPGroup
    {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] [Nontrivial X]
    (hX : IsPGroup p X) :
    OddOrder.BG.AppB.zCenterLOdd (⊤ : Subgroup X) ≠ ⊥ := by
  have hL_ne : OddOrder.BG.AppB.lOddIn (⊤ : Subgroup X) ≠ ⊥ :=
    OddOrder.BG.AppB.lOddIn_ne_bot hX
  have hL_pg : IsPGroup p (OddOrder.BG.AppB.lOddIn (⊤ : Subgroup X)) :=
    hX.to_subgroup _
  haveI hL_nontriv : Nontrivial ↥(OddOrder.BG.AppB.lOddIn (⊤ : Subgroup X)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hL_ne
  have hcenter_ne :
      Subgroup.center (OddOrder.BG.AppB.lOddIn (⊤ : Subgroup X) : Subgroup X) ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp hL_pg.center_nontrivial
  intro hZ
  rw [OddOrder.BG.AppB.zCenterLOdd] at hZ
  exact hcenter_ne ((Subgroup.map_eq_bot_iff_of_injective
    (Subgroup.center (OddOrder.BG.AppB.lOddIn (⊤ : Subgroup X) : Subgroup X))
    (OddOrder.BG.AppB.lOddIn (⊤ : Subgroup X)).subtype_injective).mp hZ)

/-- If `H` is a nontrivial finite `p`-subgroup, then `Z(L(H))`, realized in the ambient
group, is nontrivial. -/
theorem zCenterLOdd_ne_bot_of_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} (hHp : IsPGroup p H) (hH_ne : H ≠ ⊥) :
    OddOrder.BG.AppB.zCenterLOdd H ≠ ⊥ := by
  haveI hH_nontriv : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH_ne
  have htop_ne : OddOrder.BG.AppB.zCenterLOdd (⊤ : Subgroup ↥H) ≠ ⊥ :=
    zCenterLOdd_top_ne_bot_of_isPGroup (X := ↥H) hHp
  have hinj : Function.Injective (H.subtype.comp (⊤ : Subgroup ↥H).subtype) := by
    intro x y hxy
    exact Subtype.ext (H.subtype_injective hxy)
  have hmap := OddOrder.BG.AppB.map_zCenterLOdd_of_injOn
    (G := ↥H) (G' := G) H.subtype (H := (⊤ : Subgroup ↥H)) hinj
  have htop_map : ((⊤ : Subgroup ↥H).map H.subtype) = H := by
    rw [← MonoidHom.range_eq_map, H.range_subtype]
  rw [htop_map] at hmap
  intro hbot
  have hmap_bot : (OddOrder.BG.AppB.zCenterLOdd (⊤ : Subgroup ↥H)).map H.subtype = ⊥ := by
    rw [hmap, hbot]
  exact htop_ne ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hmap_bot)

/-- The normalizer of `H` normalizes the characteristic subgroup `Z(L(H))`. -/
theorem normalizer_le_normalizer_zCenterLOdd (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (OddOrder.BG.AppB.zCenterLOdd H : Set G) := by
  intro g hg
  have hHmap : H.map (MulAut.conj g).toMonoidHom = H :=
    OddOrder.BG.AppB.map_conj_eq_iff_mem_normalizer.mpr hg
  have hinj : Function.Injective ((MulAut.conj g).toMonoidHom.comp H.subtype) :=
    (MulAut.conj g).injective.comp H.subtype_injective
  have hmap : (OddOrder.BG.AppB.zCenterLOdd H).map (MulAut.conj g).toMonoidHom =
      OddOrder.BG.AppB.zCenterLOdd (H.map (MulAut.conj g).toMonoidHom) :=
    OddOrder.BG.AppB.map_zCenterLOdd_of_injOn
      (G := G) (G' := G) (MulAut.conj g).toMonoidHom (H := H) hinj
  have hZmap : (OddOrder.BG.AppB.zCenterLOdd H).map (MulAut.conj g).toMonoidHom =
      OddOrder.BG.AppB.zCenterLOdd H := by
    calc
      (OddOrder.BG.AppB.zCenterLOdd H).map (MulAut.conj g).toMonoidHom
          = OddOrder.BG.AppB.zCenterLOdd (H.map (MulAut.conj g).toMonoidHom) := hmap
      _ = OddOrder.BG.AppB.zCenterLOdd H := by rw [hHmap]
  exact OddOrder.BG.AppB.map_conj_eq_iff_mem_normalizer.mp hZmap

/-- The ambient image of `Z(L(K))` is normalized by the normalizer of the ambient image
of `K`. -/
theorem normalizer_map_le_normalizer_zCenterLOdd_map {H : Subgroup G} (K : Subgroup ↥H) :
    Subgroup.normalizer ((K.map H.subtype) : Set G) ≤
      Subgroup.normalizer (((OddOrder.BG.AppB.zCenterLOdd K).map H.subtype) : Set G) := by
  have hinj : Function.Injective (H.subtype.comp K.subtype) := by
    intro x y hxy
    exact K.subtype_injective (H.subtype_injective hxy)
  have hZmap :
      (OddOrder.BG.AppB.zCenterLOdd K).map H.subtype =
        OddOrder.BG.AppB.zCenterLOdd (K.map H.subtype) :=
    OddOrder.BG.AppB.map_zCenterLOdd_of_injOn
      (G := ↥H) (G' := G) H.subtype (H := K) hinj
  simpa [hZmap] using normalizer_le_normalizer_zCenterLOdd (K.map H.subtype)

/-- The ambient image of `Z(L(K))` lies in the ambient image of `K`. -/
theorem zCenterLOdd_map_le_map {H : Subgroup G} (K : Subgroup ↥H) :
    (OddOrder.BG.AppB.zCenterLOdd K).map H.subtype ≤ K.map H.subtype :=
  Subgroup.map_mono ((OddOrder.BG.AppB.zCenterLOdd_le_lOddIn K).trans
    (OddOrder.BG.AppB.lOddIn_le_self K))

/-- The ambient image of `Z(L(K))` depends only on the ambient image of `K`. -/
theorem zCenterLOdd_map_eq_of_map_eq {H₁ H₂ : Subgroup G}
    {K₁ : Subgroup ↥H₁} {K₂ : Subgroup ↥H₂}
    (hK : K₁.map H₁.subtype = K₂.map H₂.subtype) :
    (OddOrder.BG.AppB.zCenterLOdd K₁).map H₁.subtype =
      (OddOrder.BG.AppB.zCenterLOdd K₂).map H₂.subtype := by
  have hinj₁ : Function.Injective (H₁.subtype.comp K₁.subtype) := by
    intro x y hxy
    exact K₁.subtype_injective (H₁.subtype_injective hxy)
  have hinj₂ : Function.Injective (H₂.subtype.comp K₂.subtype) := by
    intro x y hxy
    exact K₂.subtype_injective (H₂.subtype_injective hxy)
  have hZ₁ :
      (OddOrder.BG.AppB.zCenterLOdd K₁).map H₁.subtype =
        OddOrder.BG.AppB.zCenterLOdd (K₁.map H₁.subtype) :=
    OddOrder.BG.AppB.map_zCenterLOdd_of_injOn
      (G := ↥H₁) (G' := G) H₁.subtype (H := K₁) hinj₁
  have hZ₂ :
      (OddOrder.BG.AppB.zCenterLOdd K₂).map H₂.subtype =
        OddOrder.BG.AppB.zCenterLOdd (K₂.map H₂.subtype) :=
    OddOrder.BG.AppB.map_zCenterLOdd_of_injOn
      (G := ↥H₂) (G' := G) H₂.subtype (H := K₂) hinj₂
  rw [hZ₁, hZ₂, hK]

/-- BG 8.1(b), fifth p-group bridge: Theorem 6.2 applied to `M` gives enough
normalizer control on `Z(L(P))` to make the image of `P` a Sylow `p`-subgroup of `G`. -/
theorem sylow_map_mem_range_of_fittingInG_isPGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M)) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = (P : Subgroup ↥M).map M.subtype := by
  classical
  set SH : Subgroup G := (P : Subgroup ↥M).map M.subtype with hSH_def
  set K : Subgroup G := OddOrder.BG.AppB.zCenterLOdd SH with hK_def
  have hF_ne_bot : fittingInG M ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥(fittingInG M) = 1 := Subgroup.card_eq_one.mpr hbot
    rw [hcard, Nat.primeFactors_one] at hp
    exact Finset.notMem_empty p hp
  have hF_le_SH : fittingInG M ≤ SH := by
    rw [hSH_def]
    exact fittingInG_le_sylow_map_of_isPGroup P hFp
  have hSH_ne_bot : SH ≠ ⊥ := by
    intro hbot
    exact hF_ne_bot (le_bot_iff.mp (hF_le_SH.trans (le_of_eq hbot)))
  have hSH_p : IsPGroup p SH := by
    rw [hSH_def]
    exact P.isPGroup'.map M.subtype
  have hK_ne_bot : K ≠ ⊥ := by
    rw [hK_def]
    exact zCenterLOdd_ne_bot_of_isPGroup hSH_p hSH_ne_bot
  have hK_le_SH : K ≤ SH := by
    rw [hK_def]
    exact (OddOrder.BG.AppB.zCenterLOdd_le_lOddIn SH).trans
      (OddOrder.BG.AppB.lOddIn_le_self SH)
  have hp_dvd_G : p ∣ Nat.card G :=
    (Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.card_subgroup_dvd_card (fittingInG M))
  have hp_odd_prop : Odd p := hG.odd.of_dvd_nat hp_dvd_G
  have hp_odd : p ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hp_odd_prop
    omega
  have hsolvM : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hoddM : Odd (Nat.card ↥M) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hmap_bot : (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥M).map M.subtype = ⊥ := by
    simpa [opiCoreInG] using
      (opiCoreInG_singleton_compl_eq_bot_of_fittingInG_isPGroup (M := M) hp hFp)
  have hcore_bot_compl : Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥M = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective
      (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥M) M.subtype_injective).mp hmap_bot
  -- `{q | q ≠ p}` is definitionally `({p} : Set ℕ)ᶜ`.
  have hcore_bot : Ch03.oPiCore {q | q ≠ p} ↥M = ⊥ := hcore_bot_compl
  have hZ_norm_M : (OddOrder.BG.AppB.zCenterLOdd (P : Subgroup ↥M)).Normal := by
    have h := OddOrder.BG.AppB.zCenter_lOdd_sup_oPiCore_normal hp_odd hsolvM hoddM P
    rwa [hcore_bot, sup_bot_eq] at h
  have hinjP : Function.Injective (M.subtype.comp (P : Subgroup ↥M).subtype) := by
    intro x y hxy
    exact Subtype.ext (M.subtype_injective hxy)
  have hZmap : (OddOrder.BG.AppB.zCenterLOdd (P : Subgroup ↥M)).map M.subtype = K := by
    have h := OddOrder.BG.AppB.map_zCenterLOdd_of_injOn
      (G := ↥M) (G' := G) M.subtype (H := (P : Subgroup ↥M)) hinjP
    rw [← hSH_def] at h
    simpa [hK_def] using h
  have hM_norm_K : M ≤ Subgroup.normalizer (K : Set G) := by
    have h1 : (Subgroup.normalizer (OddOrder.BG.AppB.zCenterLOdd (P : Subgroup ↥M) : Set ↥M)).map
        M.subtype ≤ Subgroup.normalizer (((OddOrder.BG.AppB.zCenterLOdd (P : Subgroup ↥M)).map
          M.subtype) : Set G) :=
      Subgroup.le_normalizer_map M.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr hZ_norm_M] at h1
    have htop_map : (⊤ : Subgroup ↥M).map M.subtype = M := by
      rw [← MonoidHom.range_eq_map, M.range_subtype]
    rw [htop_map, hZmap] at h1
    exact h1
  have hN_SH_le_NK : Subgroup.normalizer (SH : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    rw [hK_def]
    exact normalizer_le_normalizer_zCenterLOdd SH
  exact sylow_map_mem_range_of_normalizer_le_normalizer hG hM P hK_ne_bot hK_le_SH
    hM_norm_K (by simpa [hSH_def] using hN_SH_le_NK)

/-- BG 8.1(b), SCN3 bridge: if the image of a Sylow subgroup of `M` is the Sylow
`Q` of `G`, then the image of every local `SCN₃(P)` subgroup is a global
`SCN₃(p)` subgroup in the sense of §7. -/
theorem scn3_map_mem_scn3Global_of_sylow_map [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) {Q : Sylow p G}
    (hQ : (Q : Subgroup G) = (P : Subgroup ↥M).map M.subtype)
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    A.map M.subtype ∈ OddOrder.BG.Ch2.S07.scn3Global p G := by
  classical
  let Pm : Subgroup ↥M := (P : Subgroup ↥M)
  let SH : Subgroup G := Pm.map M.subtype
  have hQSH : (Q : Subgroup G) = SH := by
    simpa [SH, Pm] using hQ
  let e0 : ↥Pm ≃* ↥SH :=
    Subgroup.equivMapOfInjective Pm M.subtype M.subtype_injective
  let eQ : ↥SH ≃* ↥(Q : Subgroup G) := (MulEquiv.subgroupCongr hQSH).symm
  let e : ↥Pm ≃* ↥(Q : Subgroup G) := e0.trans eQ
  have hAQ : A.map M.subtype ≤ (Q : Subgroup G) := by
    rw [hQ]
    exact Subgroup.map_mono hAP
  have htarget :
      (A.subgroupOf Pm).map e.toMonoidHom =
        (A.map M.subtype).subgroupOf (Q : Subgroup G) := by
    apply (Subgroup.map_subtype_inj (H := (Q : Subgroup G))).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hAQ]
    rw [Subgroup.map_map]
    have hcomp : (Q : Subgroup G).subtype.comp e.toMonoidHom = M.subtype.comp Pm.subtype := by
      ext x
      simp [e, e0, eQ, SH, Pm]
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hAP]
  exact ⟨Q, hAQ, by
    rw [← htarget]
    exact hA.map_equiv e⟩

/-- BG (8.12), uniqueness part: for `q ≠ p`, `H_G^*(A;q)` has at most one member
for every local `SCN₃(P)` image `A` in the p-group case. -/
theorem hInvariantStar_scn3_map_eq_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) (hq : q ≠ p)
    {Q₁ Q₂ : Subgroup G}
    (hQ₁ : Q₁ ∈ hInvariantStar ⊤ (A.map M.subtype) {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ (A.map M.subtype) {q}) :
    Q₁ = Q₂ := by
  have hp_dvd_G : p ∣ Nat.card G :=
    (Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.card_subgroup_dvd_card (fittingInG M))
  obtain ⟨Q, hQ⟩ := sylow_map_mem_range_of_fittingInG_isPGroup hG hM hp P hFp
  have hAglobal : A.map M.subtype ∈ OddOrder.BG.Ch2.S07.scn3Global p G :=
    scn3_map_mem_scn3Global_of_sylow_map P hQ hAP hA
  have hKbot :
      opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (A.map M.subtype : Set G)) = ⊥ :=
    opiCoreInG_singleton_compl_centralizer_scn3_map_eq_bot_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA
  exact OddOrder.BG.Ch2.S07.hInvariantStar_eq_of_conjTransitiveOn_bot hKbot
    (OddOrder.BG.Ch2.S07.thompsonTransitivity hG hp_dvd_G hAglobal hq) hQ₁ hQ₂

/-- BG (8.12), existence-and-uniqueness part: for `q ≠ p`, `H_G^*(A;q)` contains
a unique member for every local `SCN₃(P)` image `A` in the p-group case. -/
theorem exists_unique_hInvariantStar_scn3_map_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) (hq : q ≠ p) :
    ∃ Q, Q ∈ hInvariantStar ⊤ (A.map M.subtype) {q} ∧
      ∀ Q', Q' ∈ hInvariantStar ⊤ (A.map M.subtype) {q} → Q' = Q := by
  have hBotInv : (⊥ : Subgroup G) ∈ hInvariant ⊤ (A.map M.subtype) {q} := by
    rw [mem_hInvariant]
    refine ⟨bot_le, ?_, ?_⟩
    · intro x _
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp
    · intro r hr
      rw [Subgroup.card_bot] at hr
      simp at hr
  obtain ⟨Q, hQstar, _hBotQ⟩ := exists_le_hInvariantStar hBotInv
  refine ⟨Q, hQstar, ?_⟩
  intro Q' hQ'
  exact hInvariantStar_scn3_map_eq_of_fittingInG_isPGroup
    hG hM hp P hFp hAP hA hq hQ' hQstar

/-- A local `SCN₃(P)` subgroup is normalized by the image of `P` in the ambient group. -/
theorem sylow_map_le_normalizer_scn3_map
    {M : Subgroup G} {p : ℕ} [Fact p.Prime] (P : Sylow p ↥M)
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    (P : Subgroup ↥M).map M.subtype ≤
      Subgroup.normalizer (A.map M.subtype : Set G) := by
  have hA_norm : (P : Subgroup ↥M) ≤ Subgroup.normalizer (A : Set ↥M) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mp hA.1.isNormal
  exact (Subgroup.map_mono hA_norm).trans (Subgroup.le_normalizer_map M.subtype)

/-- BG (8.12): in the p-group case, `F(M)` normalizes every local `SCN₃(P)` image. -/
theorem fittingInG_le_normalizer_scn3_map_of_fittingInG_isPGroup
    [Finite G] {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    fittingInG M ≤ Subgroup.normalizer (A.map M.subtype : Set G) :=
  (fittingInG_le_sylow_map_of_isPGroup P hFp).trans
    (sylow_map_le_normalizer_scn3_map P hAP hA)

/-- BG (8.12): the uniqueness of `H_G^*(A;q)` makes `N_G(A)` normalize its member. -/
theorem normalizer_scn3_map_le_normalizer_hInvariantStar_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) (hq : q ≠ p)
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ (A.map M.subtype) {q}) :
    Subgroup.normalizer (A.map M.subtype : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  intro x hxA
  have hxA_eq : MulAut.conj x • (A.map M.subtype) = A.map M.subtype :=
    conj_smul_eq_self_of_mem_normalizer hxA
  have hQconj : MulAut.conj x • Q ∈ hInvariantStar ⊤ (A.map M.subtype) {q} :=
    conj_smul_mem_hInvariantStar_top_of_normalizer hQ hxA_eq
  have hconj_eq : MulAut.conj x • Q = Q :=
    hInvariantStar_scn3_map_eq_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hQconj hQ
  exact mem_normalizer_of_conj_smul_eq_self hconj_eq

/-- BG (8.12): the unique member of `H_G^*(A;q)` is also maximal for `F(M)` invariance. -/
theorem hInvariantStar_scn3_map_mem_hInvariantStar_fittingInG_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) (hq : q ≠ p)
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ (A.map M.subtype) {q}) :
    Q ∈ hInvariantStar ⊤ (fittingInG M) {q} := by
  have hF_norm_A : fittingInG M ≤ Subgroup.normalizer (A.map M.subtype : Set G) :=
    fittingInG_le_normalizer_scn3_map_of_fittingInG_isPGroup P hFp hAP hA
  have hF_norm_Q : fittingInG M ≤ Subgroup.normalizer (Q : Set G) :=
    hF_norm_A.trans
      (normalizer_scn3_map_le_normalizer_hInvariantStar_of_fittingInG_isPGroup
        hG hM hp P hFp hAP hA hq hQ)
  refine ⟨⟨le_top, hF_norm_Q, hInvariantStar_isPiSubgroup hQ⟩, ?_⟩
  intro R hR hQR
  have hA_le_F : A.map M.subtype ≤ fittingInG M :=
    scn3_map_le_fittingInG_of_fittingInG_isPGroup hG hM hp P hFp hAP hA
  have hR_A : R ∈ hInvariant ⊤ (A.map M.subtype) {q} := by
    rw [mem_hInvariant] at hR ⊢
    exact ⟨le_top, hA_le_F.trans hR.2.1, hR.2.2⟩
  exact hQ.2 R hR_A hQR

/-- BG (8.12): `H_G^*(F(M);q)` has the same unique member as `H_G^*(A;q)`. -/
theorem hInvariantStar_fittingInG_eq_of_scn3_map_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) (hq : q ≠ p)
    {Q R : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ (A.map M.subtype) {q})
    (hR : R ∈ hInvariantStar ⊤ (fittingInG M) {q}) :
    R = Q := by
  have hA_le_F : A.map M.subtype ≤ fittingInG M :=
    scn3_map_le_fittingInG_of_fittingInG_isPGroup hG hM hp P hFp hAP hA
  have hR_A : R ∈ hInvariant ⊤ (A.map M.subtype) {q} := by
    rw [mem_hInvariant]
    exact ⟨le_top, hA_le_F.trans (hInvariantStar_le_normalizer hR),
      hInvariantStar_isPiSubgroup hR⟩
  obtain ⟨S, hSstar, hRS⟩ := exists_le_hInvariantStar hR_A
  have hS_eq_Q : S = Q :=
    hInvariantStar_scn3_map_eq_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hSstar hQ
  have hRQ : R ≤ Q := by
    rw [← hS_eq_Q]
    exact hRS
  have hQF : Q ∈ hInvariantStar ⊤ (fittingInG M) {q} :=
    hInvariantStar_scn3_map_mem_hInvariantStar_fittingInG_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hQ
  exact (hInvariantStar_eq_of_le hR (hInvariantStar_mem_hInvariant hQF) hRQ).symm

/-- BG (8.12): `M` normalizes the unique member of `H_G^*(A;q)`. -/
theorem maximal_le_normalizer_hInvariantStar_scn3_map_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) (hq : q ≠ p)
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ (A.map M.subtype) {q}) :
    M ≤ Subgroup.normalizer (Q : Set G) := by
  have hQF : Q ∈ hInvariantStar ⊤ (fittingInG M) {q} :=
    hInvariantStar_scn3_map_mem_hInvariantStar_fittingInG_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hQ
  intro x hxM
  have hxF : x ∈ Subgroup.normalizer (fittingInG M : Set G) :=
    mem_normalizer_fittingInG_of_mem hxM
  have hxF_eq : MulAut.conj x • (fittingInG M) = fittingInG M :=
    conj_smul_eq_self_of_mem_normalizer hxF
  have hQconjF : MulAut.conj x • Q ∈ hInvariantStar ⊤ (fittingInG M) {q} :=
    conj_smul_mem_hInvariantStar_top_of_normalizer hQF hxF_eq
  have hconj_eq : MulAut.conj x • Q = Q :=
    hInvariantStar_fittingInG_eq_of_scn3_map_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hQ hQconjF
  exact mem_normalizer_of_conj_smul_eq_self hconj_eq

/-- BG (8.12): for `q ≠ p`, every member of `H_G^*(A;q)` is trivial in the p-group case. -/
theorem hInvariantStar_scn3_map_eq_bot_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) (hq : q ≠ p)
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ (A.map M.subtype) {q}) :
    Q = ⊥ := by
  by_cases hQbot : Q = ⊥
  · exact hQbot
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    maximal_le_normalizer_hInvariantStar_scn3_map_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hQ
  have hQM : Q ≤ M :=
    le_maximal_of_le_normalizer_of_ne_bot_isPiSubgroup_singleton hG hM hMQ hQbot
      (hInvariantStar_isPiSubgroup hQ)
  have hQnorm : (Q.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hMQ
  have hQleF : Q ≤ fittingInG M :=
    le_fittingInG_of_normal_isPiSubgroup_singleton hQM hQnorm
      (hInvariantStar_isPiSubgroup hQ)
  have hFpi : Subgroup.IsPiSubgroup ({p} : Set ℕ) (fittingInG M) :=
    isPiSubgroup_singleton_of_isPGroup hFp
  have hQpi_compl : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ Q := by
    intro r hr
    have hrq : r = q := Set.mem_singleton_iff.mp ((hInvariantStar_isPiSubgroup hQ) r hr)
    rw [hrq]
    simpa [Set.mem_singleton_iff] using hq
  exact eq_bot_of_le_of_isPiSubgroup_of_isPiSubgroup_compl hQleF hFpi hQpi_compl

/-- BG (8.12), non-star form: for `q ≠ p`, every `A`-invariant q-subgroup is trivial. -/
theorem hInvariant_scn3_map_eq_bot_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) (hq : q ≠ p)
    {Q : Subgroup G} (hQ : Q ∈ hInvariant ⊤ (A.map M.subtype) {q}) :
    Q = ⊥ := by
  obtain ⟨R, hRstar, hQR⟩ := exists_le_hInvariantStar hQ
  have hRbot : R = ⊥ :=
    hInvariantStar_scn3_map_eq_bot_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hRstar
  exact le_bot_iff.mp (by simpa [hRbot] using hQR)

/-- BG (8.12), `p'` form: every `A`-invariant `p'`-subgroup is trivial in the
p-group case. -/
theorem hInvariant_scn3_map_singleton_compl_eq_bot_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M)))
    {Y : Subgroup G} (hY : Y ∈ hInvariant ⊤ (A.map M.subtype) ({p} : Set ℕ)ᶜ) :
    Y = ⊥ := by
  by_contra hYne
  have hp_dvd_G : p ∣ Nat.card G :=
    (Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.card_subgroup_dvd_card (fittingInG M))
  have hYpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ Y := hInvariant_isPiSubgroup hY
  have hYlt : Y < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hYtop
    have hpY : p ∈ (Nat.card ↥Y).primeFactors := by
      rw [hYtop, Subgroup.card_top]
      exact Nat.mem_primeFactors.mpr ⟨Fact.out, hp_dvd_G, Nat.card_pos.ne'⟩
    have hp_not : p ∈ ({p} : Set ℕ)ᶜ := hYpi p hpY
    exact hp_not (by simp)
  haveI hYsolv : IsSolvable ↥Y := hG.solvable_of_lt_top Y hYlt
  haveI hY_nontriv : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hYne
  have hFY_ne : fittingInG Y ≠ ⊥ := by
    have hF_ne : Ch01.fitting ↥Y ≠ ⊥ := Ch01.fitting_ne_bot_of_solvable_nontrivial ↥Y
    intro hbot
    rw [fittingInG] at hbot
    exact hF_ne ((Subgroup.map_eq_bot_iff_of_injective (Ch01.fitting ↥Y)
      Y.subtype_injective).mp hbot)
  have hFY_card_ne_one : Nat.card ↥(fittingInG Y) ≠ 1 := by
    intro hcard
    exact hFY_ne (Subgroup.card_eq_one.mp hcard)
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hFY_card_ne_one
  haveI hqFact : Fact q.Prime := ⟨hq_prime⟩
  have hqF : q ∈ (Nat.card ↥(fittingInG Y)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd, Nat.card_pos.ne'⟩
  have hqY : q ∈ (Nat.card ↥Y).primeFactors :=
    Nat.primeFactors_mono (Subgroup.card_dvd_of_le (fittingInG_le Y)) Nat.card_pos.ne' hqF
  have hq_compl : q ∈ ({p} : Set ℕ)ᶜ := hYpi q hqY
  have hq_ne_p : q ≠ p := by
    simpa [Set.mem_singleton_iff] using hq_compl
  let Oq : Subgroup G := opiCoreInG ({q} : Set ℕ) Y
  have hOq_ne : Oq ≠ ⊥ := by
    dsimp [Oq]
    exact opiCoreInG_singleton_ne_bot_of_mem_primeFactors_fittingInG (H := Y) hqF
  have hOq_mem : Oq ∈ hInvariant ⊤ (A.map M.subtype) {q} := by
    rw [mem_hInvariant]
    refine ⟨le_top, ?_, ?_⟩
    · dsimp [Oq]
      exact le_normalizer_opiCoreInG_of_le_normalizer ({q} : Set ℕ)
        (hInvariant_le_normalizer hY)
    · dsimp [Oq]
      exact isPiSubgroup_opiCoreInG ({q} : Set ℕ) Y
  have hOq_bot : Oq = ⊥ :=
    hInvariant_scn3_map_eq_bot_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq_ne_p hOq_mem
  exact hOq_ne hOq_bot

/-- BG (8.13), first p-group input: any subgroup containing the local `SCN₃(P)` image
has trivial `p'`-core. -/
theorem opiCoreInG_singleton_compl_eq_bot_of_scn3_map_le_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M H : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M)))
    (hAH : A.map M.subtype ≤ H) :
    opiCoreInG ({p} : Set ℕ)ᶜ H = ⊥ := by
  have hY : opiCoreInG ({p} : Set ℕ)ᶜ H ∈
      hInvariant ⊤ (A.map M.subtype) ({p} : Set ℕ)ᶜ := by
    rw [mem_hInvariant]
    refine ⟨le_top, ?_, ?_⟩
    · exact hAH.trans (le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ H)
    · exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ H
  exact hInvariant_scn3_map_singleton_compl_eq_bot_of_fittingInG_isPGroup
    hG hM hp P hFp hAP hA hY

/-- BG (8.13), second p-group input: if the `p'`-core of `H` is trivial, then
Theorem 6.2 makes `Z(L(R))` normal in `H` for every Sylow `p`-subgroup `R` of `H`. -/
theorem zCenterLOdd_sylow_map_subgroupOf_normal_of_opiCoreInG_singleton_compl_eq_bot
    [Finite G] (hG : IsMinimalSimpleOdd G) {H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp_dvd_G : p ∣ Nat.card G) (R : Sylow p ↥H) (hH_solvable : IsSolvable ↥H)
    (hOpBot : opiCoreInG ({p} : Set ℕ)ᶜ H = ⊥) :
    (((OddOrder.BG.AppB.zCenterLOdd (R : Subgroup ↥H)).map H.subtype).subgroupOf H).Normal := by
  have hp_odd_prop : Odd p := hG.odd.of_dvd_nat hp_dvd_G
  have hp_odd : p ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hp_odd_prop
    omega
  have hoddH : Odd (Nat.card ↥H) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card H)
  have hmap_bot : (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥H).map H.subtype = ⊥ := by
    simpa [opiCoreInG] using hOpBot
  have hcore_bot_compl : Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥H = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective
      (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥H) H.subtype_injective).mp hmap_bot
  -- `{q | q ≠ p}` is definitionally `({p} : Set ℕ)ᶜ`.
  have hcore_bot : Ch03.oPiCore {q | q ≠ p} ↥H = ⊥ := hcore_bot_compl
  have hZ_norm_H : (OddOrder.BG.AppB.zCenterLOdd (R : Subgroup ↥H)).Normal := by
    have h := OddOrder.BG.AppB.zCenter_lOdd_sup_oPiCore_normal hp_odd hH_solvable hoddH R
    rwa [hcore_bot, sup_bot_eq] at h
  have hH_norm_Z : H ≤ Subgroup.normalizer
      (((OddOrder.BG.AppB.zCenterLOdd (R : Subgroup ↥H)).map H.subtype) : Set G) := by
    have h1 : (Subgroup.normalizer (OddOrder.BG.AppB.zCenterLOdd (R : Subgroup ↥H) : Set ↥H)).map
        H.subtype ≤ Subgroup.normalizer
          (((OddOrder.BG.AppB.zCenterLOdd (R : Subgroup ↥H)).map H.subtype) : Set G) :=
      Subgroup.le_normalizer_map H.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr hZ_norm_H] at h1
    have htop_map : (⊤ : Subgroup ↥H).map H.subtype = H := by
      rw [← MonoidHom.range_eq_map, H.range_subtype]
    simpa [htop_map] using h1
  exact Subgroup.normal_subgroupOf_of_le_normalizer hH_norm_Z

/-- BG (8.13), Sylow setup: if the local `SCN₃(P)` subgroup image lies in `H`,
then it lies in a Sylow `p`-subgroup of the intersection `H ⊓ M`. -/
theorem exists_sylow_inf_containing_scn3_map_of_le
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) {A : Subgroup ↥M}
    (hAP : A ≤ (P : Subgroup ↥M)) (hAH : A.map M.subtype ≤ H) :
    ∃ R : Sylow p ↥(H ⊓ M),
      (A.map M.subtype).subgroupOf (H ⊓ M) ≤ (R : Subgroup ↥(H ⊓ M)) := by
  have hA_le_inf : A.map M.subtype ≤ H ⊓ M :=
    le_inf hAH (Subgroup.map_subtype_le A)
  have hAsub_p : IsPGroup p (A.subgroupOf (P : Subgroup ↥M)) :=
    P.isPGroup'.to_subgroup _
  have hA_p : IsPGroup p A :=
    hAsub_p.of_equiv (Subgroup.subgroupOfEquivOfLe hAP)
  have hAmap_p : IsPGroup p (A.map M.subtype) :=
    hA_p.map M.subtype
  have hAinf_p : IsPGroup p ((A.map M.subtype).subgroupOf (H ⊓ M)) :=
    hAmap_p.of_equiv (Subgroup.subgroupOfEquivOfLe hA_le_inf).symm
  exact hAinf_p.exists_le_sylow

/-- A `SCN₃` subgroup is nontrivial. -/
theorem isSCN3_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : IsSCN₃ p A) :
    A ≠ ⊥ := by
  intro hbot
  have hprank_le : pRank A p ≤ 0 := by
    rw [pRank_le_iff]
    intro B hB
    haveI : Subsingleton A := by
      rw [hbot]
      infer_instance
    have hBcard : Nat.card B = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    rw [hBcard, Nat.log_one_right]
  have h3 : 3 ≤ pRank A p := hA.le_pRank
  omega

/-- A local `SCN₃(P)` subgroup has nontrivial image in the ambient group. -/
theorem scn3_map_ne_bot_of_le_sylow [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) {A : Subgroup ↥M}
    (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    A.map M.subtype ≠ ⊥ := by
  have hAsub_ne : A.subgroupOf (P : Subgroup ↥M) ≠ ⊥ :=
    isSCN3_ne_bot (G := ↥(P : Subgroup ↥M)) hA
  intro hAmap_bot
  have hA_bot : A = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective A M.subtype_injective).mp hAmap_bot
  have hAsub_bot : A.subgroupOf (P : Subgroup ↥M) = ⊥ := by
    have hmap_bot : (A.subgroupOf (P : Subgroup ↥M)).map
        (P : Subgroup ↥M).subtype = ⊥ := by
      rw [Subgroup.map_subgroupOf_eq_of_le hAP, hA_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective _ (P : Subgroup ↥M).subtype_injective).mp
      hmap_bot
  exact hAsub_ne hAsub_bot

/-- BG (8.13), nontriviality setup: the Sylow subgroup of `H ⊓ M` containing the local
`SCN₃(P)` image is nontrivial. -/
theorem sylow_inf_ne_bot_of_scn3_map_le [Finite G]
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) {A : Subgroup ↥M}
    (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M)))
    (hAH : A.map M.subtype ≤ H) {R : Sylow p ↥(H ⊓ M)}
    (hA_R : (A.map M.subtype).subgroupOf (H ⊓ M) ≤
      (R : Subgroup ↥(H ⊓ M))) :
    (R : Subgroup ↥(H ⊓ M)) ≠ ⊥ := by
  have hAmap_ne : A.map M.subtype ≠ ⊥ :=
    scn3_map_ne_bot_of_le_sylow P hAP hA
  have hA_le_inf : A.map M.subtype ≤ H ⊓ M :=
    le_inf hAH (Subgroup.map_subtype_le A)
  have hAinf_ne : (A.map M.subtype).subgroupOf (H ⊓ M) ≠ ⊥ := by
    intro hAinf_bot
    apply hAmap_ne
    have hmap_bot : ((A.map M.subtype).subgroupOf (H ⊓ M)).map
        (H ⊓ M).subtype = ⊥ := by
      rw [hAinf_bot, Subgroup.map_bot]
    rwa [Subgroup.map_subgroupOf_eq_of_le hA_le_inf] at hmap_bot
  intro hR_bot
  exact hAinf_ne (le_bot_iff.mp (hA_R.trans (le_of_eq hR_bot)))

/-- BG (8.13), Sylow setup in `H`: if the local `SCN₃(P)` subgroup image lies in
`H`, then it lies in a Sylow `p`-subgroup of `H`. -/
theorem exists_sylow_containing_scn3_map_of_le
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) {A : Subgroup ↥M}
    (hAP : A ≤ (P : Subgroup ↥M)) (hAH : A.map M.subtype ≤ H) :
    ∃ R : Sylow p ↥H, (A.map M.subtype).subgroupOf H ≤ (R : Subgroup ↥H) := by
  have hAsub_p : IsPGroup p (A.subgroupOf (P : Subgroup ↥M)) :=
    P.isPGroup'.to_subgroup _
  have hA_p : IsPGroup p A :=
    hAsub_p.of_equiv (Subgroup.subgroupOfEquivOfLe hAP)
  have hAmap_p : IsPGroup p (A.map M.subtype) :=
    hA_p.map M.subtype
  have hAH_p : IsPGroup p ((A.map M.subtype).subgroupOf H) :=
    hAmap_p.of_equiv (Subgroup.subgroupOfEquivOfLe hAH).symm
  exact hAH_p.exists_le_sylow

/-- BG (8.13), nontriviality setup in `H`: a Sylow subgroup of `H` containing the
local `SCN₃(P)` image is nontrivial. -/
theorem sylow_ne_bot_of_scn3_map_le [Finite G]
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) {A : Subgroup ↥M}
    (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M)))
    (hAH : A.map M.subtype ≤ H) {R : Sylow p ↥H}
    (hA_R : (A.map M.subtype).subgroupOf H ≤ (R : Subgroup ↥H)) :
    (R : Subgroup ↥H) ≠ ⊥ := by
  have hAmap_ne : A.map M.subtype ≠ ⊥ :=
    scn3_map_ne_bot_of_le_sylow P hAP hA
  have hA_H_ne : (A.map M.subtype).subgroupOf H ≠ ⊥ := by
    intro hA_H_bot
    apply hAmap_ne
    have hmap_bot : ((A.map M.subtype).subgroupOf H).map H.subtype = ⊥ := by
      rw [hA_H_bot, Subgroup.map_bot]
    rwa [Subgroup.map_subgroupOf_eq_of_le hAH] at hmap_bot
  intro hR_bot
  exact hA_H_ne (le_bot_iff.mp (hA_R.trans (le_of_eq hR_bot)))

/-- A `p`-subgroup `K` of `H` is realized as a Sylow `p`-subgroup of `H` once its
index in `H` is prime to `p`. -/
theorem exists_sylow_subgroupOf_map_eq_of_not_dvd_index [Finite G]
    {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    (hKp : IsPGroup p K) (hKH : K ≤ H) (hidx : ¬ p ∣ (K.subgroupOf H).index) :
    ∃ R : Sylow p ↥H, (R : Subgroup ↥H).map H.subtype = K := by
  have hidx' : ¬ p ∣ (K.comap H.subtype).index := by
    rwa [Subgroup.comap_subtype]
  let R : Sylow p ↥H := (hKp.comap_subtype (K := H)).toSylow hidx'
  refine ⟨R, ?_⟩
  change ((hKp.comap_subtype (K := H)).toSylow hidx' : Subgroup ↥H).map H.subtype = K
  rw [(hKp.comap_subtype (K := H)).toSylow_coe hidx', Subgroup.comap_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKH]

/-- A `p`-subgroup `K ≤ H` has `p`-prime index in `H` if every `p`-subgroup of
`H` containing `K` has cardinal at most `K`. -/
theorem not_dvd_subgroupOf_index_of_forall_card_le [Finite G]
    {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    (hKp : IsPGroup p K) (hKH : K ≤ H)
    (hmax : ∀ L : Subgroup G, IsPGroup p L → K ≤ L → L ≤ H →
      Nat.card ↥L ≤ Nat.card ↥K) :
    ¬ p ∣ (K.subgroupOf H).index := by
  intro hidx
  have hKsub_p : IsPGroup p (K.subgroupOf H) :=
    hKp.of_equiv (Subgroup.subgroupOfEquivOfLe hKH).symm
  obtain ⟨S, hKS⟩ := hKsub_p.exists_le_sylow
  have hS_ne : (S : Subgroup ↥H) ≠ K.subgroupOf H := by
    intro hS
    have hnot : ¬ p ∣ (K.subgroupOf H).index := by
      simpa [hS] using S.not_dvd_index
    exact hnot hidx
  have hKsub_lt_S : K.subgroupOf H < (S : Subgroup ↥H) :=
    lt_of_le_of_ne hKS (fun h => hS_ne h.symm)
  have hcard_lt : Nat.card ↥(K.subgroupOf H) < Nat.card ↥(S : Subgroup ↥H) := by
    have hss : (K.subgroupOf H : Set ↥H) ⊂ ((S : Subgroup ↥H) : Set ↥H) :=
      SetLike.coe_ssubset_coe.mpr hKsub_lt_S
    exact Set.Finite.card_lt_card (Set.toFinite ((S : Subgroup ↥H) : Set ↥H)) hss
  have hK_le_Smap : K ≤ (S : Subgroup ↥H).map H.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hKH]
    exact Subgroup.map_mono hKS
  have hSmap_p : IsPGroup p ((S : Subgroup ↥H).map H.subtype) :=
    S.isPGroup'.map H.subtype
  have hSmap_le_H : (S : Subgroup ↥H).map H.subtype ≤ H :=
    Subgroup.map_subtype_le _
  have hSmap_card_le_K :
      Nat.card ↥((S : Subgroup ↥H).map H.subtype) ≤ Nat.card ↥K :=
    hmax _ hSmap_p hK_le_Smap hSmap_le_H
  have hSmap_card :
      Nat.card ↥((S : Subgroup ↥H).map H.subtype) = Nat.card ↥(S : Subgroup ↥H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hKsub_card : Nat.card ↥(K.subgroupOf H) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have hS_card_le_Ksub : Nat.card ↥(S : Subgroup ↥H) ≤ Nat.card ↥(K.subgroupOf H) := by
    rw [← hSmap_card, hKsub_card]
    exact hSmap_card_le_K
  exact (not_lt_of_ge hS_card_le_Ksub) hcard_lt

/-- A subgroup properly contained in a finite `p`-group is properly contained in its
normalizer inside that `p`-group. -/
theorem lt_inf_normalizer_of_isPGroup_lt [Finite G]
    {p : ℕ} [Fact p.Prime] {K L : Subgroup G}
    (hL : IsPGroup p L) (hKL : K < L) :
    K < L ⊓ Subgroup.normalizer (K : Set G) := by
  haveI : Group.IsNilpotent ↥L := hL.isNilpotent
  have hNC : NormalizerCondition ↥L := Group.normalizerCondition_of_isNilpotent (G := ↥L)
  have hK_le : K ≤ L := le_of_lt hKL
  have hsub_lt_top : K.subgroupOf L < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact (ne_of_lt hKL) (le_antisymm hK_le htop)
  have hlt := hNC (K.subgroupOf L) hsub_lt_top
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hK_le, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  refine lt_of_le_of_ne (le_inf hK_le Subgroup.le_normalizer) ?_
  intro heq
  apply ht_not
  have hmem : (t : G) ∈ L ⊓ Subgroup.normalizer (K : Set G) := ⟨t.2, ht_norm⟩
  rw [← heq] at hmem
  exact hmem

/-- The ambient image of a Sylow subgroup of `H ⊓ M` dominates every ambient
`p`-subgroup lying in `H ⊓ M` and containing that image. -/
theorem card_le_sylow_inf_map_of_le [Finite G]
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (R : Sylow p ↥(H ⊓ M)) {L : Subgroup G}
    (hLp : IsPGroup p L)
    (hRL : (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype ≤ L)
    (hLH : L ≤ H) (hLM : L ≤ M) :
    Nat.card ↥L ≤ Nat.card ↥((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) := by
  have hL_inf : L ≤ H ⊓ M := le_inf hLH hLM
  have hLsub_p : IsPGroup p (L.subgroupOf (H ⊓ M)) :=
    hLp.of_equiv (Subgroup.subgroupOfEquivOfLe hL_inf).symm
  have hR_le_Lsub : (R : Subgroup ↥(H ⊓ M)) ≤ L.subgroupOf (H ⊓ M) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hRL ⟨x, hx, rfl⟩
  have hLsub_eq_R : L.subgroupOf (H ⊓ M) = (R : Subgroup ↥(H ⊓ M)) :=
    R.is_maximal' hLsub_p hR_le_Lsub
  have hLsub_card : Nat.card ↥(L.subgroupOf (H ⊓ M)) = Nat.card ↥L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL_inf).toEquiv
  have hRmap_card :
      Nat.card ↥((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) =
        Nat.card ↥(R : Subgroup ↥(H ⊓ M)) :=
    Subgroup.card_map_of_injective (H ⊓ M).subtype_injective
  rw [← hLsub_card, hLsub_eq_R, hRmap_card]

/-- If the ambient normalizer of the Sylow image in `H ⊓ M` lies in `M`, then that
image is card-maximal among `p`-subgroups of `H` containing it. -/
theorem forall_card_le_of_normalizer_sylow_inf_map_le [Finite G]
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (R : Sylow p ↥(H ⊓ M))
    (hN_le_M : Subgroup.normalizer
      (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ M) :
    ∀ L : Subgroup G, IsPGroup p L →
      (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype ≤ L → L ≤ H →
      Nat.card ↥L ≤ Nat.card ↥((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) := by
  intro L hLp hRL hLH
  by_cases hL_le_R : L ≤ (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype
  · exact Subgroup.card_le_of_le hL_le_R
  · have hR_lt_L :
        (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype < L :=
      lt_of_le_of_ne hRL (fun hEq => hL_le_R (le_of_eq hEq.symm))
    have hR_lt_LN := lt_inf_normalizer_of_isPGroup_lt hLp hR_lt_L
    have hLN_p : IsPGroup p
        (L ⊓ Subgroup.normalizer
          (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) :=
      hLp.to_inf_left
    have hLN_le_H : L ⊓ Subgroup.normalizer
        (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ H :=
      inf_le_left.trans hLH
    have hLN_le_M : L ⊓ Subgroup.normalizer
        (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ M :=
      inf_le_right.trans hN_le_M
    have hLN_card_le_R :=
      card_le_sylow_inf_map_of_le R hLN_p hR_lt_LN.le hLN_le_H hLN_le_M
    have hcard_lt :
        Nat.card ↥((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) <
          Nat.card ↥(L ⊓ Subgroup.normalizer
            (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) := by
      have hss :
          (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype : Subgroup G) : Set G) ⊂
            ((L ⊓ Subgroup.normalizer
              (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) : Set G) :=
        SetLike.coe_ssubset_coe.mpr hR_lt_LN
      exact Set.Finite.card_lt_card (Set.toFinite
        ((L ⊓ Subgroup.normalizer
          (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) : Set G)) hss
    exact False.elim ((not_lt_of_ge hLN_card_le_R) hcard_lt)

/-- If `Z(L(K))`, realized in the ambient group, is nontrivial and normal in a maximal
subgroup `H`, then its ambient normalizer is exactly `H`. -/
theorem normalizer_zCenterLOdd_map_eq_of_normal_of_ne_bot [Finite G]
    (hG : IsMinimalSimpleOdd G) {H : Subgroup G} (hH : H ∈ maximalSubgroups G)
    {K : Subgroup ↥H}
    (hZnorm : (((OddOrder.BG.AppB.zCenterLOdd K).map H.subtype).subgroupOf H).Normal)
    (hZne : (OddOrder.BG.AppB.zCenterLOdd K).map H.subtype ≠ ⊥) :
    Subgroup.normalizer (((OddOrder.BG.AppB.zCenterLOdd K).map H.subtype) : Set G) = H :=
  normalizer_eq_of_normal_of_mem_maximal hG hH hZnorm hZne (Subgroup.map_subtype_le _)

/-- The BG (8.13) counterexample measure: the order of a Sylow `p`-subgroup of
`K ⊓ M`, i.e. the `p`-part of `|K ∩ M|` in the finite setting. -/
noncomputable def sylowInfCard (p : ℕ) [Fact p.Prime] (K M : Subgroup G) : ℕ :=
  Nat.card ↥((default : Sylow p ↥(K ⊓ M)) : Subgroup ↥(K ⊓ M))

/-- `sylowInfCard` is independent of the chosen Sylow subgroup. -/
theorem sylowInfCard_eq_card [Finite G]
    (p : ℕ) [Fact p.Prime] (K M : Subgroup G) (R : Sylow p ↥(K ⊓ M)) :
    sylowInfCard p K M = Nat.card ↥(R : Subgroup ↥(K ⊓ M)) := by
  unfold sylowInfCard
  rw [Sylow.card_eq_multiplicity (default : Sylow p ↥(K ⊓ M)),
    Sylow.card_eq_multiplicity R]

/-- Any ambient `p`-subgroup contained in `L ⊓ M` is bounded by `sylowInfCard p L M`. -/
theorem card_le_sylowInfCard_of_isPGroup_le [Finite G]
    {p : ℕ} [Fact p.Prime] {L M K : Subgroup G}
    (hKp : IsPGroup p K) (hKL : K ≤ L) (hKM : K ≤ M) :
    Nat.card ↥K ≤ sylowInfCard p L M := by
  have hK_inf : K ≤ L ⊓ M := le_inf hKL hKM
  have hKsub_p : IsPGroup p (K.subgroupOf (L ⊓ M)) :=
    hKp.of_equiv (Subgroup.subgroupOfEquivOfLe hK_inf).symm
  obtain ⟨S, hKS⟩ := hKsub_p.exists_le_sylow
  have hKsub_card : Nat.card ↥(K.subgroupOf (L ⊓ M)) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_inf).toEquiv
  calc
    Nat.card ↥K = Nat.card ↥(K.subgroupOf (L ⊓ M)) := hKsub_card.symm
    _ ≤ Nat.card ↥(S : Subgroup ↥(L ⊓ M)) := Subgroup.card_le_of_le hKS
    _ = sylowInfCard p L M := (sylowInfCard_eq_card p L M S).symm

/-- If the normalizer of `K` lies in `L` and the `p`-part of `L ⊓ M` is no larger
than `K`, then `K` is card-maximal among `p`-subgroups of `M` containing it. -/
theorem forall_card_le_of_normalizer_le_and_sylowInfCard_le [Finite G]
    {p : ℕ} [Fact p.Prime] {L M K : Subgroup G}
    (hN_le_L : Subgroup.normalizer (K : Set G) ≤ L)
    (hbound : sylowInfCard p L M ≤ Nat.card ↥K) :
    ∀ T : Subgroup G, IsPGroup p T → K ≤ T → T ≤ M → Nat.card ↥T ≤ Nat.card ↥K := by
  intro T hTp hKT hTM
  by_cases hT_le_K : T ≤ K
  · exact Subgroup.card_le_of_le hT_le_K
  · have hK_lt_T : K < T :=
      lt_of_le_of_ne hKT (fun hEq => hT_le_K (le_of_eq hEq.symm))
    have hK_lt_TN := lt_inf_normalizer_of_isPGroup_lt hTp hK_lt_T
    have hTN_p : IsPGroup p (T ⊓ Subgroup.normalizer (K : Set G) : Subgroup G) :=
      hTp.to_inf_left
    have hTN_le_L : T ⊓ Subgroup.normalizer (K : Set G) ≤ L :=
      inf_le_right.trans hN_le_L
    have hTN_le_M : T ⊓ Subgroup.normalizer (K : Set G) ≤ M :=
      inf_le_left.trans hTM
    have hTN_card_le_K :
        Nat.card ↥(T ⊓ Subgroup.normalizer (K : Set G) : Subgroup G) ≤ Nat.card ↥K :=
      (card_le_sylowInfCard_of_isPGroup_le hTN_p hTN_le_L hTN_le_M).trans hbound
    have hcard_lt :
        Nat.card ↥K < Nat.card ↥(T ⊓ Subgroup.normalizer (K : Set G) : Subgroup G) := by
      have hss : (K : Set G) ⊂ ((T ⊓ Subgroup.normalizer (K : Set G) : Subgroup G) : Set G) :=
        SetLike.coe_ssubset_coe.mpr hK_lt_TN
      exact Set.Finite.card_lt_card (Set.toFinite
        ((T ⊓ Subgroup.normalizer (K : Set G) : Subgroup G) : Set G)) hss
    exact False.elim ((not_lt_of_ge hTN_card_le_K) hcard_lt)

/-- If the normalizer of `K` lies in `L` and `sylowInfCard p L M` is bounded by `K`,
then `K`, viewed inside `M`, is a Sylow `p`-subgroup. -/
theorem exists_sylow_map_eq_of_normalizer_le_and_sylowInfCard_le [Finite G]
    {p : ℕ} [Fact p.Prime] {L M K : Subgroup G}
    (hKp : IsPGroup p K) (hKM : K ≤ M)
    (hN_le_L : Subgroup.normalizer (K : Set G) ≤ L)
    (hbound : sylowInfCard p L M ≤ Nat.card ↥K) :
    ∃ R : Sylow p ↥M, (R : Subgroup ↥M).map M.subtype = K :=
  exists_sylow_subgroupOf_map_eq_of_not_dvd_index hKp hKM
    (not_dvd_subgroupOf_index_of_forall_card_le hKp hKM
      (forall_card_le_of_normalizer_le_and_sylowInfCard_le hN_le_L hbound))

/-- If an ambient subgroup has the same cardinal as a Sylow subgroup, every ambient
`p`-subgroup has cardinal at most that subgroup. -/
theorem card_le_of_isPGroup_of_card_eq_sylow [Finite G]
    {p : ℕ} [Fact p.Prime] {K L : Subgroup G} (Q : Sylow p G)
    (hKcard : Nat.card ↥K = Nat.card ↥(Q : Subgroup G))
    (hLp : IsPGroup p L) :
    Nat.card ↥L ≤ Nat.card ↥K := by
  obtain ⟨S, hLS⟩ := hLp.exists_le_sylow
  calc
    Nat.card ↥L ≤ Nat.card ↥(S : Subgroup G) := Subgroup.card_le_of_le hLS
    _ = Nat.card ↥(Q : Subgroup G) := by
      rw [Sylow.card_eq_multiplicity S, Sylow.card_eq_multiplicity Q]
    _ = Nat.card ↥K := hKcard.symm

/-- If the normalizer of the Sylow image in `H ⊓ M` lies in `H`, then that image is
card-maximal among `p`-subgroups of `M` containing it. -/
theorem forall_card_le_of_normalizer_sylow_inf_map_le_left [Finite G]
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (R : Sylow p ↥(H ⊓ M))
    (hN_le_H : Subgroup.normalizer
      (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ H) :
    ∀ L : Subgroup G, IsPGroup p L →
      (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype ≤ L → L ≤ M →
      Nat.card ↥L ≤ Nat.card ↥((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) := by
  intro L hLp hRL hLM
  by_cases hL_le_R : L ≤ (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype
  · exact Subgroup.card_le_of_le hL_le_R
  · have hR_lt_L :
        (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype < L :=
      lt_of_le_of_ne hRL (fun hEq => hL_le_R (le_of_eq hEq.symm))
    have hR_lt_LN := lt_inf_normalizer_of_isPGroup_lt hLp hR_lt_L
    have hLN_p : IsPGroup p
        (L ⊓ Subgroup.normalizer
          (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) :=
      hLp.to_inf_left
    have hLN_le_H : L ⊓ Subgroup.normalizer
        (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ H :=
      inf_le_right.trans hN_le_H
    have hLN_le_M : L ⊓ Subgroup.normalizer
        (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ M :=
      inf_le_left.trans hLM
    have hLN_card_le_R :=
      card_le_sylow_inf_map_of_le R hLN_p hR_lt_LN.le hLN_le_H hLN_le_M
    have hcard_lt :
        Nat.card ↥((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) <
          Nat.card ↥(L ⊓ Subgroup.normalizer
            (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) := by
      have hss :
          (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype : Subgroup G) : Set G) ⊂
            ((L ⊓ Subgroup.normalizer
              (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) : Set G) :=
        SetLike.coe_ssubset_coe.mpr hR_lt_LN
      exact Set.Finite.card_lt_card (Set.toFinite
        ((L ⊓ Subgroup.normalizer
          (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) : Set G)) hss
    exact False.elim ((not_lt_of_ge hLN_card_le_R) hcard_lt)

/-- If the local `A` lies in the chosen Sylow subgroup of `H ⊓ M`, then its ambient image
lies in the ambient image of that Sylow subgroup. -/
theorem scn3_map_le_sylow_inf_map_of_le
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime] {A : Subgroup ↥M}
    (hAH : A.map M.subtype ≤ H) {R : Sylow p ↥(H ⊓ M)}
    (hA_R : (A.map M.subtype).subgroupOf (H ⊓ M) ≤
      (R : Subgroup ↥(H ⊓ M))) :
    A.map M.subtype ≤ (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := by
  intro x hx
  have hx_inf : x ∈ H ⊓ M := ⟨hAH hx, Subgroup.map_subtype_le A hx⟩
  let xinf : ↥(H ⊓ M) := ⟨x, hx_inf⟩
  have hx_sub : xinf ∈ (A.map M.subtype).subgroupOf (H ⊓ M) := by
    rw [Subgroup.mem_subgroupOf]
    exact hx
  exact ⟨xinf, hA_R hx_sub, rfl⟩

/-- If the local `A` lies in the chosen Sylow subgroup of `H ⊓ M`, then its ambient image
normalizes the ambient image of that Sylow subgroup. -/
theorem scn3_map_le_normalizer_sylow_inf_map_of_le
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime] {A : Subgroup ↥M}
    (hAH : A.map M.subtype ≤ H) {R : Sylow p ↥(H ⊓ M)}
    (hA_R : (A.map M.subtype).subgroupOf (H ⊓ M) ≤
      (R : Subgroup ↥(H ⊓ M))) :
    A.map M.subtype ≤
      Subgroup.normalizer (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) :=
  (scn3_map_le_sylow_inf_map_of_le hAH hA_R).trans Subgroup.le_normalizer

/-- In a minimal simple group, the normalizer of a nontrivial subgroup lying in a maximal
subgroup is contained in some maximal subgroup. -/
theorem exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal [Finite G]
    (hG : IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKne : K ≠ ⊥) (hKM : K ≤ M) :
    ∃ L : Subgroup G, L ∈ maximalSubgroups G ∧ Subgroup.normalizer (K : Set G) ≤ L := by
  haveI : IsSimpleGroup G := hG.simple
  have hMco : IsCoatom M := mem_maximalSubgroups.mp hM
  have hN_ne_top : Subgroup.normalizer (K : Set G) ≠ ⊤ := by
    intro hN_top
    have hK_normal : K.Normal := Subgroup.normalizer_eq_top_iff.mp hN_top
    rcases hK_normal.eq_bot_or_eq_top with hK_bot | hK_top
    · exact hKne hK_bot
    · have htop_le_M : ⊤ ≤ M := by
        rw [← hK_top]
        exact hKM
      exact hMco.lt_top.ne (eq_top_iff.mpr htop_le_M)
  obtain ⟨L, hLco, hN_le_L⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (K : Set G))).resolve_left hN_ne_top
  exact ⟨L, hLco, hN_le_L⟩

/-- **BG Theorem 8.1(b)** (mmd L2319-2322): 同じ仮定で `F(M)` が `p`-群なら、`M` の Sylow
`p`-部分群 `P` は `G` の Sylow `p`-部分群であり、`SCN₃(P)` の各元は `F(M)` に含まれ `𝒰` に属す。

`SCN₃(P)` 非空は §5 Lem 5.1 (Remark, mmd L2324) で保証されるが、この定理型では
非空性を仮定にせず、BG 本文どおり `SCN₃(P)` の任意の元に対する結論として保持する。 -/
theorem sylow_isSylow_and_scn3_isUniquelyMaximal_of_pGroup [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    {A₀ : Subgroup G} (_hA₀ : isMaxElemAbelianIn p A₀ (fittingInG M))
    (_hm : 3 ≤ rank ↥A₀)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M)) :
    (∃ Q : Sylow p G, (Q : Subgroup G) = (P : Subgroup ↥M).map M.subtype) ∧
    (∀ A : Subgroup ↥M, A ≤ (P : Subgroup ↥M) → IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M)) →
      A.map M.subtype ≤ fittingInG M ∧ IsUniquelyMaximal (A.map M.subtype)) := by
  obtain ⟨Q, hQ⟩ := sylow_map_mem_range_of_fittingInG_isPGroup hG hM hp P hFp
  refine ⟨⟨Q, hQ⟩, ?_⟩
  intro A hAP hA
  have hAglobal : A.map M.subtype ∈ OddOrder.BG.Ch2.S07.scn3Global p G :=
    scn3_map_mem_scn3Global_of_sylow_map P hQ hAP hA
  have hCentM : Subgroup.centralizer (A.map M.subtype : Set G) ≤ M :=
    centralizer_scn3_map_le_maximal_of_fittingInG_isPGroup hG hM hp P hFp hAP hA
  have hOpCentBot :
      opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (A.map M.subtype : Set G)) = ⊥ :=
    opiCoreInG_singleton_compl_centralizer_scn3_map_eq_bot_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA
  have hHqBot : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      ∀ {Y : Subgroup G}, Y ∈ hInvariant ⊤ (A.map M.subtype) {q} → Y = ⊥ := by
    intro q _ hq Y hY
    exact hInvariant_scn3_map_eq_bot_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hY
  have hHpPrimeBot : ∀ {Y : Subgroup G},
      Y ∈ hInvariant ⊤ (A.map M.subtype) ({p} : Set ℕ)ᶜ → Y = ⊥ := by
    intro Y hY
    exact hInvariant_scn3_map_singleton_compl_eq_bot_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hY
  have hAF : A.map M.subtype ≤ fittingInG M :=
    scn3_map_le_fittingInG_of_fittingInG_isPGroup hG hM hp P hFp hAP hA
  refine ⟨hAF, ?_⟩
  have hA_le_M : A.map M.subtype ≤ M := hAF.trans (fittingInG_le M)
  have hA_proper : A.map M.subtype < ⊤ :=
    lt_of_le_of_lt hA_le_M (mem_maximalSubgroups.mp hM).lt_top
  by_contra hnotU
  obtain ⟨H, hH, hAH, hH_ne_M, hHmax⟩ :=
    exists_maximal_counterexample_image_of_not_isUniquelyMaximal
      (H := A.map M.subtype) (M := M)
      (w := fun K : Subgroup G => sylowInfCard p K M)
      hA_proper hM hA_le_M hnotU
  have hHco : IsCoatom H := mem_maximalSubgroups.mp hH
  haveI hH_solvable : IsSolvable ↥H := hG.solvable_of_lt_top H hHco.lt_top
  have hOpComplHBot : opiCoreInG ({p} : Set ℕ)ᶜ H = ⊥ :=
    opiCoreInG_singleton_compl_eq_bot_of_scn3_map_le_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hAH
  have hp_dvd_G : p ∣ Nat.card G :=
    (Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.card_subgroup_dvd_card (fittingInG M))
  have hZNormH : ∀ R : Sylow p ↥H,
      (((OddOrder.BG.AppB.zCenterLOdd (R : Subgroup ↥H)).map H.subtype).subgroupOf H).Normal := by
    intro R
    exact zCenterLOdd_sylow_map_subgroupOf_normal_of_opiCoreInG_singleton_compl_eq_bot
      hG hp_dvd_G R hH_solvable hOpComplHBot
  obtain ⟨Rinf, hA_Rinf⟩ := exists_sylow_inf_containing_scn3_map_of_le P hAP hAH
  have hRinf_ne_bot : (Rinf : Subgroup ↥(H ⊓ M)) ≠ ⊥ :=
    sylow_inf_ne_bot_of_scn3_map_le P hAP hA hAH hA_Rinf
  have hZ_Rinf_ne_bot :
      ((OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map
        (H ⊓ M).subtype) ≠ ⊥ := by
    have hZ_ne : OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M)) ≠ ⊥ :=
      zCenterLOdd_ne_bot_of_isPGroup Rinf.isPGroup' hRinf_ne_bot
    intro hZ_map_bot
    exact hZ_ne ((Subgroup.map_eq_bot_iff_of_injective _
      (H ⊓ M).subtype_injective).mp hZ_map_bot)
  have hZ_Rinf_le_Rinf_amb :
      ((OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map
        (H ⊓ M).subtype) ≤
          (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype :=
    zCenterLOdd_map_le_map (H := H ⊓ M) (Rinf : Subgroup ↥(H ⊓ M))
  have hSylowInfCard_H :
      sylowInfCard p H M = Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) :=
    sylowInfCard_eq_card p H M Rinf
  have hHmax_Rinf : ∀ L : Subgroup G, L ∈ maximalSubgroups G →
      A.map M.subtype ≤ L → L ≠ M →
      sylowInfCard p L M ≤ Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) := by
    intro L hL hAL hLM
    calc
      sylowInfCard p L M ≤ sylowInfCard p H M := hHmax L hL hAL hLM
      _ = Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) := hSylowInfCard_H
  have hA_le_Rinf_amb :
      A.map M.subtype ≤ (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype :=
    scn3_map_le_sylow_inf_map_of_le hAH hA_Rinf
  have hA_le_NRinf : A.map M.subtype ≤
      Subgroup.normalizer (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) :=
    scn3_map_le_normalizer_sylow_inf_map_of_le hAH hA_Rinf
  have hNRinf_le_NZ_Rinf :
      Subgroup.normalizer
          (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤
        Subgroup.normalizer
          (((OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map
            (H ⊓ M).subtype) : Set G) :=
    normalizer_map_le_normalizer_zCenterLOdd_map
      (H := H ⊓ M) (Rinf : Subgroup ↥(H ⊓ M))
  have hA_le_NZ_Rinf : A.map M.subtype ≤
      Subgroup.normalizer
        (((OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map
          (H ⊓ M).subtype) : Set G) :=
    hA_le_NRinf.trans hNRinf_le_NZ_Rinf
  have hRinf_amb_ne_bot :
      (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype ≠ ⊥ := by
    intro hR_map_bot
    exact hRinf_ne_bot
      ((Subgroup.map_eq_bot_iff_of_injective _
        (H ⊓ M).subtype_injective).mp hR_map_bot)
  have hRinf_amb_le_M :
      (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype ≤ M := by
    intro x hx
    rcases hx with ⟨xinf, -, rfl⟩
    exact xinf.2.2
  have hRinf_amb_le_H :
      (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype ≤ H := by
    intro x hx
    rcases hx with ⟨xinf, -, rfl⟩
    exact xinf.2.1
  have hRinf_amb_p :
      IsPGroup p ((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) :=
    Rinf.isPGroup'.map (H ⊓ M).subtype
  have hRinfH_of_not_dvd :
      (¬ p ∣ (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype).subgroupOf H).index) →
        ∃ RinfH : Sylow p ↥H,
          (RinfH : Subgroup ↥H).map H.subtype =
            (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := by
    intro hidx
    exact exists_sylow_subgroupOf_map_eq_of_not_dvd_index
      hRinf_amb_p hRinf_amb_le_H hidx
  have hRinfH_of_forall_card_le :
      (∀ L : Subgroup G, IsPGroup p L →
          (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype ≤ L → L ≤ H →
          Nat.card ↥L ≤ Nat.card ↥((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype)) →
        ∃ RinfH : Sylow p ↥H,
          (RinfH : Subgroup ↥H).map H.subtype =
            (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := by
    intro hmax
    exact hRinfH_of_not_dvd
      (not_dvd_subgroupOf_index_of_forall_card_le
        hRinf_amb_p hRinf_amb_le_H hmax)
  have hRinfH_of_normalizer_le_M :
      Subgroup.normalizer
          (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ M →
        ∃ RinfH : Sylow p ↥H,
          (RinfH : Subgroup ↥H).map H.subtype =
            (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := by
    intro hN_le_M
    exact hRinfH_of_forall_card_le
      (forall_card_le_of_normalizer_sylow_inf_map_le Rinf hN_le_M)
  obtain ⟨LRinf, hLRinf, hNRinf_le_LRinf⟩ :=
    exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal
      hG hM hRinf_amb_ne_bot hRinf_amb_le_M
  have hA_le_LRinf : A.map M.subtype ≤ LRinf :=
    hA_le_NRinf.trans hNRinf_le_LRinf
  have hLRinf_bound : LRinf ≠ M →
      sylowInfCard p LRinf M ≤ Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) := by
    intro hLRinf_ne_M
    exact hHmax_Rinf LRinf hLRinf hA_le_LRinf hLRinf_ne_M
  have hNRinf_le_M_or_bound :
      Subgroup.normalizer
          (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ M ∨
        sylowInfCard p LRinf M ≤ Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) := by
    by_cases hLRinf_eq_M : LRinf = M
    · left
      simpa [hLRinf_eq_M] using hNRinf_le_LRinf
    · right
      exact hLRinf_bound hLRinf_eq_M
  have hRinfH_or_bound :
      (∃ RinfH : Sylow p ↥H,
          (RinfH : Subgroup ↥H).map H.subtype =
            (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) ∨
        sylowInfCard p LRinf M ≤ Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) := by
    rcases hNRinf_le_M_or_bound with hN_le_M | hbound
    · left
      exact hRinfH_of_normalizer_le_M hN_le_M
    · right
      exact hbound
  have hRinfH_of_bound :
      sylowInfCard p LRinf M ≤ Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) →
        ∃ RinfH : Sylow p ↥H,
          (RinfH : Subgroup ↥H).map H.subtype =
            (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := by
    intro hbound
    have hRinf_amb_card :
        Nat.card ↥((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) =
          Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) :=
      Subgroup.card_map_of_injective (H ⊓ M).subtype_injective
    have hbound_amb :
        sylowInfCard p LRinf M ≤
          Nat.card ↥((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) := by
      calc
        sylowInfCard p LRinf M ≤ Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) := hbound
        _ = Nat.card ↥((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) :=
          hRinf_amb_card.symm
    obtain ⟨RM, hRM_map⟩ :=
      exists_sylow_map_eq_of_normalizer_le_and_sylowInfCard_le
        hRinf_amb_p hRinf_amb_le_M hNRinf_le_LRinf hbound_amb
    have hRinf_card_Q :
        Nat.card ↥((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) =
          Nat.card ↥(Q : Subgroup G) := by
      calc
        Nat.card ↥((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype)
            = Nat.card ↥(RM : Subgroup ↥M) := by
              rw [← hRM_map, Subgroup.card_map_of_injective M.subtype_injective]
        _ = Nat.card ↥(P : Subgroup ↥M) := by
              rw [Sylow.card_eq_multiplicity RM, Sylow.card_eq_multiplicity P]
        _ = Nat.card ↥((P : Subgroup ↥M).map M.subtype) := by
              rw [Subgroup.card_map_of_injective M.subtype_injective]
        _ = Nat.card ↥(Q : Subgroup G) := by rw [hQ]
    exact hRinfH_of_forall_card_le fun L hLp _hRL _hLH =>
      card_le_of_isPGroup_of_card_eq_sylow Q hRinf_card_Q hLp
  have hRinfH_exists :
      ∃ RinfH : Sylow p ↥H,
        (RinfH : Subgroup ↥H).map H.subtype =
          (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := by
    rcases hRinfH_or_bound with hRinfH | hbound
    · exact hRinfH
    · exact hRinfH_of_bound hbound
  obtain ⟨RinfH, hRinfH_map⟩ := hRinfH_exists
  have hZ_RinfH_eq_Rinf :
      (OddOrder.BG.AppB.zCenterLOdd (RinfH : Subgroup ↥H)).map H.subtype =
        (OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map (H ⊓ M).subtype :=
    zCenterLOdd_map_eq_of_map_eq hRinfH_map
  have hZ_RinfH_ne_bot :
      (OddOrder.BG.AppB.zCenterLOdd (RinfH : Subgroup ↥H)).map H.subtype ≠ ⊥ := by
    intro hZ_map_bot
    exact hZ_Rinf_ne_bot (by rw [← hZ_RinfH_eq_Rinf, hZ_map_bot])
  have hNZ_Rinf_eq_H : Subgroup.normalizer
      (((OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map
        (H ⊓ M).subtype) : Set G) = H := by
    have hNZ_RinfH_eq_H : Subgroup.normalizer
        (((OddOrder.BG.AppB.zCenterLOdd (RinfH : Subgroup ↥H)).map H.subtype) : Set G) = H :=
      normalizer_zCenterLOdd_map_eq_of_normal_of_ne_bot
        hG hH (hZNormH RinfH) hZ_RinfH_ne_bot
    simpa [hZ_RinfH_eq_Rinf] using hNZ_RinfH_eq_H
  have hNRinf_le_H :
      Subgroup.normalizer
          (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ H :=
    hNRinf_le_NZ_Rinf.trans (le_of_eq hNZ_Rinf_eq_H)
  obtain ⟨RM, hRM_map⟩ :=
    exists_sylow_subgroupOf_map_eq_of_not_dvd_index hRinf_amb_p hRinf_amb_le_M
      (not_dvd_subgroupOf_index_of_forall_card_le hRinf_amb_p hRinf_amb_le_M
        (forall_card_le_of_normalizer_sylow_inf_map_le_left Rinf hNRinf_le_H))
  haveI hM_solvable : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hOpComplMBot : opiCoreInG ({p} : Set ℕ)ᶜ M = ⊥ :=
    opiCoreInG_singleton_compl_eq_bot_of_fittingInG_isPGroup (M := M) hp hFp
  have hZNormM :
      (((OddOrder.BG.AppB.zCenterLOdd (RM : Subgroup ↥M)).map M.subtype).subgroupOf M).Normal :=
    zCenterLOdd_sylow_map_subgroupOf_normal_of_opiCoreInG_singleton_compl_eq_bot
      hG hp_dvd_G RM hM_solvable hOpComplMBot
  have hZ_RM_eq_Rinf :
      (OddOrder.BG.AppB.zCenterLOdd (RM : Subgroup ↥M)).map M.subtype =
        (OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map (H ⊓ M).subtype :=
    zCenterLOdd_map_eq_of_map_eq hRM_map
  have hZ_RM_ne_bot :
      (OddOrder.BG.AppB.zCenterLOdd (RM : Subgroup ↥M)).map M.subtype ≠ ⊥ := by
    intro hZ_map_bot
    exact hZ_Rinf_ne_bot (by rw [← hZ_RM_eq_Rinf, hZ_map_bot])
  have hNZ_Rinf_eq_M : Subgroup.normalizer
      (((OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map
        (H ⊓ M).subtype) : Set G) = M := by
    have hNZ_RM_eq_M : Subgroup.normalizer
        (((OddOrder.BG.AppB.zCenterLOdd (RM : Subgroup ↥M)).map M.subtype) : Set G) = M :=
      normalizer_zCenterLOdd_map_eq_of_normal_of_ne_bot hG hM hZNormM hZ_RM_ne_bot
    simpa [hZ_RM_eq_Rinf] using hNZ_RM_eq_M
  exact hH_ne_M (hNZ_Rinf_eq_H.symm.trans hNZ_Rinf_eq_M)

end OddOrder.BG.Ch2.S08
