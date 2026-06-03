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

/-- Fitting M, realized in G, is nilpotent. -/
theorem fittingInG_isNilpotent [Finite G] (M : Subgroup G) :
    Group.IsNilpotent ↥(fittingInG M) := by
  rw [fittingInG]
  haveI : Group.IsNilpotent ↥(Ch01.fitting ↥M) := Ch01.fitting.isNilpotent
  exact nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective (Ch01.fitting ↥M)
    M.subtype M.subtype_injective)

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

/-- **BG (8.2) normalizer localization**: if `O_q(Z(F(M)))` is nontrivial, then its
normalizer in the ambient minimal simple group is exactly the maximal subgroup `M`. -/
theorem normalizer_centerFittingOpCoreInG_eq_of_ne_bot [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hO_ne : centerFittingOpCoreInG q M ≠ ⊥) :
    Subgroup.normalizer (centerFittingOpCoreInG q M : Set G) = M :=
  normalizer_eq_of_normal_of_mem_maximal hG hM
    (centerFittingOpCoreInG_subgroupOf_normal q M) hO_ne (centerFittingOpCoreInG_le q M)

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

/-- The relative centralizer C_F(M)(A0) is proper whenever M is maximal. -/
theorem cFitting_lt_top_of_mem_maximal {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) :
    Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M < ⊤ :=
  lt_of_le_of_lt (inf_le_right.trans (fittingInG_le M))
    (mem_maximalSubgroups.mp hM).lt_top

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
  have hCenterRank : 3 ≤ rank ↥(Subgroup.center ↥A) := by
    dsimp [A]
    exact three_le_rank_center_cFitting_of_isMaxElemAbelianIn hA₀ hm
  refine IsUniquelyMaximal.of_unique_maximal hA_proper hM hA_le_M ?_
  intro H hH hAH
  have hHco : IsCoatom H := hH
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
