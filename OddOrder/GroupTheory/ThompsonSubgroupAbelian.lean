/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Commutator.Basic
import OddOrder.GroupTheory.ThompsonSubgroup

/-!
# Abelian Thompson Subgroup `J_a(P)` (Gorenstein 版)

`OddOrder.GroupTheory` shared module: **Gorenstein 版 Thompson subgroup**
`J_a(P) = ⟨A(P)⟩`, `A(P)` = `P` 内の **abelian** 部分群のうち**最大位数**のもの。

Gorenstein, *Finite Groups* (1968), Ch.8 §2 (pp. 270-271) の定義と基本補題
(Lem 2.1 / 2.3)。BG Thm 6.2 (literal `J(S)`) の `J` は**この版** — BG は `J` を
自前定義せず (記号表 p.170 の初出 = Thm 6.2 自身)、証明を **G** 8.2.11 (Glauberman
`Z(J)`-定理) に委ねる。Issue 9403 (claim) / 3024 / 3017。

## 既存 `Subgroup.thompsonJ` (elementary 版) との関係

`OddOrder/GroupTheory/ThompsonSubgroup.lean` の `thompsonJ` は Isaacs/Aschbacher 版
(**elementary** abelian の最大位数) で**別物**。Gorenstein §2 の機構は
**Lemma 2.1 (`A ∈ A(P) ⟹ A = C_P(A)`)** に乗っており、その証明
(「`x ∈ C_P(A)` なら `⟨A, x⟩` がより大きい abelian」) は全 abelian 部分群中の
最大性が本質 — elementary 版では `⟨A, x⟩` が elementary と限らず**不成立**。
ゆえに Glauberman ZJ の移植には本 module の abelian 版が必要。

## Main definitions

* `Subgroup.maxAbelianIn P`: `P` 内の abelian 部分群のうち最大位数のものの集合
  (Gorenstein の `A(P)`; mmd L5443)。素数 `p` に言及しない (Gorenstein 原文どおり)。
* `Subgroup.thompsonJAbelian P`: abelian Thompson subgroup `J_a(P) = ⟨A(P)⟩`
  (Gorenstein mmd L5449)。

## Main results

* `Subgroup.eq_inf_centralizer_of_mem_maxAbelianIn` — **Gorenstein Lemma 2.1**:
  `A ∈ A(P) ⟹ A = C_P(A)` (`C_P(A)` は `P ⊓ centralizer A` で符号化)。
* `Subgroup.centralizer_inf_le_of_mem_maxAbelianIn` — Lem 2.1 の系 `Z(P) ≤ A`
  (`Z(P)` は `centralizer P ⊓ P` で符号化、`S06_Thm62JS` と同じ規約)。
* `Subgroup.le_normalizer_iff_commutator_commutator_eq_bot_of_mem_maxAbelianIn` —
  **Gorenstein Lemma 2.3**: `B ≤ P` について `B ≤ N(A) ⟺ ⁅⁅B,A⁆,A⁆ = ⊥`。

## Forward references (Gorenstein Ch.8 §2 の続き; issue 9403)

Lem 2.2 (a)-(d) (`J_a` の遺伝性・共役共変性・characteristic 性)、Thm 2.4 (Thompson)、
Thm 2.5 (Thompson Replacement)、Thm 2.7 (Glauberman Replacement)、Lem 2.8-2.10、
Thm 2.11 (**Glauberman `Z(J)`-定理**) は後続 leaf。
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- The trivial subgroup `⊥` is abelian. -/
theorem bot_isMulCommutative : IsMulCommutative ((⊥ : Subgroup G)) :=
  ⟨⟨fun a b => Subtype.ext (by
    simp [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩⟩

/-- **Maximum-order abelian subgroups of `P`** (Gorenstein Ch.8 §2 の `A(P)`, p. 270).

`A(P) = {A ≤ P | A は abelian で, 任意の abelian subgroup B ≤ P について |B| ≤ |A|}`.

⚠ elementary 版 `maxElemAbelianIn` (Isaacs の `E(P)`) とは別物 — こちらは
elementary 性を課さない (Gorenstein 原文どおり素数にも言及しない). -/
def maxAbelianIn (P : Subgroup G) : Set (Subgroup G) :=
  {A | A ≤ P ∧ IsMulCommutative A ∧
       ∀ B : Subgroup G, B ≤ P → IsMulCommutative B → Nat.card B ≤ Nat.card A}

/-- **Abelian Thompson subgroup** `J_a(P) = ⟨A | A ∈ A(P)⟩` (Gorenstein Ch.8 §2, p. 271).

BG Thm 6.2 の literal `J(S)` はこの版 (BG 記号表 p.170 → **G** 8.2.11). -/
def thompsonJAbelian (P : Subgroup G) : Subgroup G :=
  ⨆ A ∈ maxAbelianIn P, A

/-- `J_a(P) ≤ P`. -/
theorem thompsonJAbelian_le (P : Subgroup G) : thompsonJAbelian P ≤ P := by
  refine iSup_le fun A => iSup_le fun hA => ?_
  exact hA.1

/-- `A ∈ A(P)` の生成元は `J_a(P)` に含まれる. -/
theorem le_thompsonJAbelian_of_mem_maxAbelianIn {P A : Subgroup G}
    (hA : A ∈ maxAbelianIn P) : A ≤ thompsonJAbelian P :=
  le_iSup_of_le A (le_iSup_of_le hA le_rfl)

/-- `[Finite G]` のもとで `A(P)` は非空 (`⊥` が常に abelian ゆえ最大元が存在). -/
theorem maxAbelianIn_nonempty [Finite G] (P : Subgroup G) :
    (maxAbelianIn P).Nonempty := by
  have hS_fin : {B : Subgroup G | B ≤ P ∧ IsMulCommutative B}.Finite :=
    Set.finite_univ.subset fun _ _ => Set.mem_univ _
  have hS_ne : {B : Subgroup G | B ≤ P ∧ IsMulCommutative B}.Nonempty :=
    ⟨⊥, bot_le, bot_isMulCommutative⟩
  obtain ⟨A, hA_S, hA_max⟩ :=
    Set.exists_max_image {B : Subgroup G | B ≤ P ∧ IsMulCommutative B}
      (fun B => Nat.card B) hS_fin hS_ne
  exact ⟨A, hA_S.1, hA_S.2, fun B hB_P hB_comm => hA_max B ⟨hB_P, hB_comm⟩⟩

/-- **Gorenstein Lemma 2.1**: `A ∈ A(P) ⟹ A = C_P(A)` (`C_P(A) = P ⊓ centralizer A`).

証明の核: `x ∈ C_P(A)` なら `A ⊔ ⟨x⟩` は `P` 内の abelian 部分群で `A` を含むので,
`A(P)` の最大位数性から `A ⊔ ⟨x⟩ = A`, ゆえに `x ∈ A`. **全 abelian 部分群中の
最大性が本質** (elementary 版では `A ⊔ ⟨x⟩` が elementary と限らず不成立). -/
theorem eq_inf_centralizer_of_mem_maxAbelianIn [Finite G] {P A : Subgroup G}
    (hA : A ∈ maxAbelianIn P) :
    A = P ⊓ centralizer (A : Set G) := by
  obtain ⟨hAP, hAcomm, hAmax⟩ := hA
  refine le_antisymm (le_inf hAP (le_centralizer_iff_isMulCommutative.mpr hAcomm)) ?_
  intro x hx
  obtain ⟨hxP, hxC⟩ := hx
  -- `B = A ⊔ ⟨x⟩` は `P` 内の abelian 部分群.
  have hBP : A ⊔ zpowers x ≤ P := sup_le hAP (zpowers_le.mpr hxP)
  have hBcomm : IsMulCommutative (A ⊔ zpowers x : Subgroup G) := by
    rw [← le_centralizer_iff_isMulCommutative]
    refine sup_le ?_ ?_
    · rw [le_centralizer_iff]
      exact sup_le (le_centralizer_iff_isMulCommutative.mpr hAcomm) (zpowers_le.mpr hxC)
    · rw [le_centralizer_iff]
      refine sup_le ?_ (le_centralizer_iff_isMulCommutative.mpr inferInstance)
      rw [le_centralizer_iff]
      exact zpowers_le.mpr hxC
  -- 最大位数性から `A = A ⊔ ⟨x⟩`, ゆえに `x ∈ A`.
  have hAB : A = A ⊔ zpowers x :=
    eq_of_le_of_card_ge le_sup_left (hAmax _ hBP hBcomm)
  rw [hAB]
  exact mem_sup_right (mem_zpowers x)

/-- **Gorenstein Lemma 2.1 の系**: `Z(P) ≤ A` for `A ∈ A(P)`
(`Z(P)` は `centralizer P ⊓ P` で符号化). -/
theorem centralizer_inf_le_of_mem_maxAbelianIn [Finite G] {P A : Subgroup G}
    (hA : A ∈ maxAbelianIn P) :
    centralizer (P : Set G) ⊓ P ≤ A := by
  intro x hx
  exact (eq_inf_centralizer_of_mem_maxAbelianIn hA).ge
    ⟨hx.2, centralizer_le (SetLike.coe_subset_coe.mpr hA.1) hx.1⟩

/-- **Gorenstein Lemma 2.3**: `A ∈ A(P)`, `B ≤ P` について
`B` が `A` を正規化する ⟺ `⁅⁅B,A⁆,A⁆ = ⊥`.

順方向は `⁅B,A⁆ ≤ A` と `A` の可換性から. 逆方向は `⁅B,A⁆ ≤ P ⊓ C(A) = A`
(**Lemma 2.1**) から `B ≤ N(A)`. -/
theorem le_normalizer_iff_commutator_commutator_eq_bot_of_mem_maxAbelianIn
    [Finite G] {P A B : Subgroup G} (hA : A ∈ maxAbelianIn P) (hB : B ≤ P) :
    B ≤ normalizer (A : Set G) ↔ ⁅⁅B, A⁆, A⁆ = ⊥ := by
  constructor
  · intro hnorm
    have h1 : ⁅B, A⁆ ≤ A := le_normalizer_iff_commutator_le_right.mp hnorm
    have h2 : ⁅⁅B, A⁆, A⁆ ≤ ⁅A, A⁆ := commutator_mono h1 le_rfl
    have h3 : ⁅A, A⁆ = (⊥ : Subgroup G) :=
      commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff_isMulCommutative.mpr hA.2.1)
    exact le_bot_iff.mp (h3 ▸ h2)
  · intro hbot
    have h1 : ⁅B, A⁆ ≤ centralizer (A : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp hbot
    have h2 : ⁅B, A⁆ ≤ P := le_trans (commutator_le_sup B A) (sup_le hB hA.1)
    have h3 : ⁅B, A⁆ ≤ A :=
      (eq_inf_centralizer_of_mem_maxAbelianIn hA).ge.trans' (le_inf h2 h1)
    exact le_normalizer_iff_commutator_le_right.mpr h3

end Subgroup
