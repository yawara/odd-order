/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch2_Uniqueness.Setup
import OddOrder.BG.Ch2_Uniqueness.S07_Transitivity
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

faithful statement + `sorry`。proof は §7 (Thm 7.2/7.4/7.6) + §6 Thm 6.2 一般形 + Prop 1.10/1.3
に依存 (foundation-first)。§5 Lem 5.1 is only the nonemptiness remark for `SCN₃(P)`
(mmd L2324); the part (b) statement is universal over all `A ∈ SCN₃(P)` and should not
carry Lem 5.1 as an extra assumption. No §5 narrow classification theorem or BG Thm 4.16
assumption belongs in §8.
-/

namespace OddOrder.BG.Ch2.S08

open OddOrder.GroupTheory
open OddOrder.Isaacs

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

/-- Fitting M, realized in G, is nilpotent. -/
theorem fittingInG_isNilpotent [Finite G] (M : Subgroup G) :
    Group.IsNilpotent ↥(fittingInG M) := by
  rw [fittingInG]
  haveI : Group.IsNilpotent ↥(Ch01.fitting ↥M) := Ch01.fitting.isNilpotent
  exact nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective (Ch01.fitting ↥M)
    M.subtype M.subtype_injective)

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

private theorem normalizer_eq_of_normal_of_mem_maximal [Finite G] (hG : IsMinimalSimpleOdd G)
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
  sorry

/-- **BG Theorem 8.1(b)** (mmd L2319-2322): 同じ仮定で `F(M)` が `p`-群なら、`M` の Sylow
`p`-部分群 `P` は `G` の Sylow `p`-部分群であり、`SCN₃(P)` の各元は `F(M)` に含まれ `𝒰` に属す。

`SCN₃(P)` 非空は §5 Lem 5.1 (Remark, mmd L2324) で保証されるが、この定理型では
非空性を仮定にせず、BG 本文どおり `SCN₃(P)` の任意の元に対する結論として保持する。 -/
theorem sylow_isSylow_and_scn3_isUniquelyMaximal_of_pGroup [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    {A₀ : Subgroup G} (hA₀ : isMaxElemAbelianIn p A₀ (fittingInG M))
    (hm : 3 ≤ rank ↥A₀)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M)) :
    (∃ Q : Sylow p G, (Q : Subgroup G) = (P : Subgroup ↥M).map M.subtype) ∧
    (∀ A : Subgroup ↥M, A ≤ (P : Subgroup ↥M) → IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M)) →
      A.map M.subtype ≤ fittingInG M ∧ IsUniquelyMaximal (A.map M.subtype)) := by
  sorry

end OddOrder.BG.Ch2.S08
