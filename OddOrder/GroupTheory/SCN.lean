/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Subgroup.Basic
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.GroupTheory.PRank

/-!
# Self-Centralizing Normal Abelian Subgroups (SCN)

`OddOrder.GroupTheory` shared module: 'SCN subgroup' (Self-Centralizing Normal abelian
subgroup) の概念.

mathlib v4.30.0-rc2 に `IsSCN` / `SCN` 不在 (0 hits). BG / Isaacs FGT における基本概念で,
**BG §4 Prop 4.4** (existence of `SCN` in p-群), **BG §4 Lem 4.7** (rank ≥ 3 ⇔ `SCN_3` 非空),
**BG §5 Lem 5.1** (SCN₃ argument), **Isaacs Ch.7** (J(P) 関連) で必要.

## Main definitions

* `OddOrder.GroupTheory.IsSCN A`: 部分群 `A : Subgroup G` is SCN.
  - `A.Normal` (`A ⊴ G`),
  - `IsMulCommutative A` (`A` is abelian),
  - `centralizer (A : Set G) = A` (`C_G(A) = A`).
* `OddOrder.GroupTheory.IsMaximalAbelianNormal A`: `A` is normal, abelian, and maximal
  with respect to being abelian among normal subgroups (BG Prop 4.4(a) の右辺).
* `OddOrder.GroupTheory.IsSCN_n p n A` / `IsSCN₃ p A`: `A ∈ SCN_n(R)`, i.e. `A` is SCN
  and `m(A) ≥ n` where `m(A) = pRank A p` (BG §4 `SCN_n(R)` の定義, p.33).

## Main results (本 module で提供)

* 構造体投影: `isNormal`, `isMulCommutative`, `selfCentralizing`.
* `IsSCN.isMaximalAbelianNormal`: SCN ⇒ maximal-abelian-normal (BG Prop 4.4(a) `⇒`,
  p-群 仮定不要).
* `IsMaximalAbelianNormal.isSCN`: p-群で maximal-abelian-normal ⇒ SCN (BG Prop 4.4(a)
  `⇐`, Gorenstein 5.3.12 = `centralizer_eq_self_of_maximal_abelian_normal` 経由).
* `isSCN_iff_isMaximalAbelianNormal`: **BG Prop 4.4(a)** — p-群で
  `IsSCN A ↔ IsMaximalAbelianNormal A`.

## Design notes

* `SCN_n(G)` (= rank ≥ `n` の `SCN`) を `pRank` と連動定義 (`PRank.lean` 完成後に追加,
  Phase 2a 第 1 波 audit 2026-05-23 で別 module として分離決定). BG の `m(A)` (abelian
  `A` の最小生成元数) は abelian `p`-群では `Ω₁(A)` の `F_p`-次元 = `pRank A p` に一致
  するので, `SCN_n` の `m(A) ≥ n` を `n ≤ pRank A p` で表す.
* `structure` 形 (Prop). dot-notation 利用可.
* 将来 mathlib upstream 視野で `OddOrder/Mathlib/SCN.lean` 候補.

## References

* BG §4 (p-Groups of Small Rank), Prop 4.4, Lem 4.7.
* BG §5 (Narrow p-Groups), Lem 5.1.
* Isaacs, _Finite Group Theory_ (AMS GSM 92, 2008), Chapter 7.
* Gorenstein, _Finite Groups_ (1968), §5.3 (Theorem 5.3.12).

## Audit context

Phase 2a 第 1 波 audit 2026-05-23 で新規 shared module 候補として確定.
詳細は `notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`.
SCN_n 定義 + Prop 4.4(a) 2026-05-30 (`notes/bg/s04_implementation_plan_2026_05_30.md` §4.2).
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **SCN subgroup** (Self-Centralizing Normal abelian subgroup):
`A ≤ G` is SCN iff `A` is normal in `G`, abelian, and equals its own centralizer
`C_G(A) = A`.

教科書 (Isaacs FGT Ch.7, BG §4) 標準定義. `A = C_G(A)` 条件は **A self-centralizing**
を意味し, abelian + normal と組み合わせて p-群構造解析の鍵となる. -/
structure IsSCN (A : Subgroup G) : Prop where
  /-- `A` is normal in `G`. -/
  isNormal : A.Normal
  /-- `A` is abelian. -/
  isMulCommutative : IsMulCommutative A
  /-- `A` is self-centralizing: `C_G(A) = A`. -/
  selfCentralizing : Subgroup.centralizer (A : Set G) = A

namespace IsSCN

variable {A : Subgroup G}

/-- An SCN subgroup is contained in its own centralizer (abelian ⇒ `A ⊆ C_G(A)`).
This is a one-direction restatement; the other direction `C_G(A) ⊆ A` is `selfCentralizing`. -/
theorem le_centralizer (h : IsSCN A) : A ≤ Subgroup.centralizer (A : Set G) := by
  rw [h.selfCentralizing]

/-- An SCN subgroup is contained in the center of its centralizer (trivially since
`C_G(A) = A` and `A` is abelian, hence in the center of itself). -/
theorem centralizer_le (h : IsSCN A) : Subgroup.centralizer (A : Set G) ≤ A :=
  h.selfCentralizing.le

end IsSCN

/-! ## 4B: BG Proposition 4.4(a) — SCN ↔ maximal abelian normal (pp. 37) -/

section MaximalAbelianNormal

/-- **Maximal abelian normal subgroup** (BG Prop 4.4(a) の右辺): `A ≤ G` is normal,
abelian, and maximal with respect to being abelian among the normal subgroups of `G`
(any abelian normal `N ⊇ A` equals `A`).

In a `p`-group this is exactly the set `SCN(R)` (BG Proposition 4.4(a)). -/
structure IsMaximalAbelianNormal (A : Subgroup G) : Prop where
  /-- `A` is normal in `G`. -/
  isNormal : A.Normal
  /-- `A` is abelian. -/
  isMulCommutative : IsMulCommutative A
  /-- `A` is maximal among abelian normal subgroups: any abelian normal `N ⊇ A` is `A`. -/
  maximal : ∀ N : Subgroup G, N.Normal → IsMulCommutative N → A ≤ N → N = A

/-- **BG Proposition 4.4(a)**, forward direction (no `p`-group hypothesis needed).
A self-centralizing normal abelian subgroup is maximal among abelian normal subgroups.

Proof: if `N` is abelian and normal with `A ≤ N`, then `N ≤ C_G(N)` (abelian) and
`C_G(N) ≤ C_G(A)` (centralizer is antitone in the set, since `A ⊆ N`); as `C_G(A) = A`
we get `N ≤ A`, hence `N = A`. -/
theorem IsSCN.isMaximalAbelianNormal {A : Subgroup G} (h : IsSCN A) :
    IsMaximalAbelianNormal A where
  isNormal := h.isNormal
  isMulCommutative := h.isMulCommutative
  maximal N hN_normal hN_comm hAN := by
    -- `N ≤ C_G(N) ≤ C_G(A) = A`, together with `A ≤ N`.
    have hN_le_cent : N ≤ Subgroup.centralizer (N : Set G) :=
      haveI := hN_comm; Subgroup.le_centralizer N
    have hcent_le : Subgroup.centralizer (N : Set G) ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAN)
    have hN_le_A : N ≤ A := by
      rw [← h.selfCentralizing]; exact le_trans hN_le_cent hcent_le
    exact le_antisymm hN_le_A hAN

/-- **BG Proposition 4.4(a)**, backward direction (`p`-group). In a `p`-group, a normal
subgroup maximal with respect to being abelian is self-centralizing, hence SCN.

Proof: normality and commutativity are immediate; self-centralization
`C_G(A) = A` is Gorenstein 5.3.12
(`centralizer_eq_self_of_maximal_abelian_normal`), whose maximality hypothesis is
supplied by `h.maximal`. -/
theorem IsMaximalAbelianNormal.isSCN {p : ℕ} [Fact p.Prime] [Finite G] (hG : IsPGroup p G)
    {A : Subgroup G} (h : IsMaximalAbelianNormal A) :
    IsSCN A := by
  haveI := h.isNormal
  haveI := h.isMulCommutative
  -- Element-level commutativity of `A`, needed by Gorenstein 5.3.12.
  have hA_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  -- Element-level maximality of `A` among abelian normal subgroups.
  have hA_max : ∀ N : Subgroup G, N.Normal →
      (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) → A ≤ N → N = A := by
    intro N hN_normal hN_comm hAN
    exact h.maximal N hN_normal (IsMulCommutative.of_comm fun x y =>
      Subtype.ext (hN_comm x x.2 y y.2)) hAN
  exact
    { isNormal := h.isNormal
      isMulCommutative := h.isMulCommutative
      selfCentralizing :=
        centralizer_eq_self_of_maximal_abelian_normal hG hA_comm hA_max }

/-- **BG Proposition 4.4(a)**. In a `p`-group `G`, `SCN(G)` is exactly the set of normal
subgroups that are maximal with respect to being abelian:
`IsSCN A ↔ IsMaximalAbelianNormal A`.

The `⇒` direction holds in any group (`IsSCN.isMaximalAbelianNormal`); the `⇐` direction
uses that `G` is a `p`-group (Gorenstein 5.3.12). -/
theorem isSCN_iff_isMaximalAbelianNormal {p : ℕ} [Fact p.Prime] [Finite G] (hG : IsPGroup p G)
    {A : Subgroup G} :
    IsSCN A ↔ IsMaximalAbelianNormal A :=
  ⟨IsSCN.isMaximalAbelianNormal, IsMaximalAbelianNormal.isSCN hG⟩

/-- **Every abelian normal subgroup lies below a maximal abelian normal one** (`[Finite G]`).
Standard finiteness argument: among the (finitely many) abelian normal subgroups containing
`B`, pick a `≤`-maximal one. Underlies "`SCN(R)` covers every normal abelian subgroup",
used in BG §4 (e.g. translating `SCN₃(R) = ∅` into a bound on `d_n(R)`). -/
theorem exists_maximalAbelianNormal_ge [Finite G] {B : Subgroup G}
    (hBnorm : B.Normal) (hBcomm : IsMulCommutative B) :
    ∃ A : Subgroup G, B ≤ A ∧ IsMaximalAbelianNormal A := by
  obtain ⟨A, hBA, hAmax⟩ :=
    exists_maximal_ge_of_wellFoundedGT
      (fun N : Subgroup G => N.Normal ∧ IsMulCommutative N) B ⟨hBnorm, hBcomm⟩
  refine ⟨A, hBA, { isNormal := hAmax.1.1, isMulCommutative := hAmax.1.2, maximal := ?_ }⟩
  intro N hN_norm hN_comm hAN
  exact le_antisymm (hAmax.2 ⟨hN_norm, hN_comm⟩ hAN) hAN

end MaximalAbelianNormal

/-! ## 4B: `SCN_n(R)` — SCN subgroups of rank `≥ n` (pp. 33) -/

section SCN_n

/-- **`SCN_n(R)` membership** (BG §4, p.33): `A ∈ SCN_n(R)` iff `A` is SCN and its
generator number `m(A)` is at least `n`.

For an abelian `p`-group `A` the BG invariant `m(A)` (minimum number of generators)
equals the `F_p`-dimension of `Ω₁(A)`, i.e. `pRank A p`; an SCN subgroup is abelian, so
we express `m(A) ≥ n` as `n ≤ pRank A p`. -/
def IsSCN_n (p n : ℕ) (A : Subgroup G) : Prop :=
  IsSCN A ∧ n ≤ pRank A p

/-- **`SCN₃(R)` membership** (BG §4, the case `n = 3`, used in BG Lem 4.7 / §5 / §7):
`A ∈ SCN₃(R)` iff `A` is SCN of rank `≥ 3`. -/
abbrev IsSCN₃ (p : ℕ) (A : Subgroup G) : Prop := IsSCN_n p 3 A

theorem IsSCN_n.isSCN {p n : ℕ} {A : Subgroup G} (h : IsSCN_n p n A) : IsSCN A := h.1

theorem IsSCN_n.le_pRank {p n : ℕ} {A : Subgroup G} (h : IsSCN_n p n A) :
    n ≤ pRank A p := h.2

/-- Membership in `SCN_n` is antitone in `n`: an `SCN_n` subgroup is also `SCN_m` for
`m ≤ n`. In particular `SCN₃(R) ⊆ SCN_2(R) ⊆ SCN_1(R)`. -/
theorem IsSCN_n.mono {p m n : ℕ} {A : Subgroup G} (hmn : m ≤ n) (h : IsSCN_n p n A) :
    IsSCN_n p m A :=
  ⟨h.1, hmn.trans h.2⟩

end SCN_n

end OddOrder.GroupTheory
