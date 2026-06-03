/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch2_Uniqueness.Setup
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

/-- **BG Theorem 8.1(a)** (mmd L2319-2321): `M ∈ ℳ`, `p ∈ π(F(M))`, `A₀ ∈ ℰ_p^*(F(M))`,
`m(A₀) ≥ 3`。`F(M)` が `p`-群でなければ `C_{F(M)}(A₀) ∈ 𝒰`。 -/
theorem cFitting_isUniquelyMaximal_of_not_pGroup [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    {A₀ : Subgroup G} (hA₀ : isMaxElemAbelianIn p A₀ (fittingInG M))
    (hm : 3 ≤ rank ↥A₀)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M)) :
    IsUniquelyMaximal (Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M) := by
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
