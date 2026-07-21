/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Commutator.Basic
import OddOrder.GroupTheory.ThompsonSubgroup
import OddOrder.Isaacs.Ch01_Sylow.Basic
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh02

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

* **Gorenstein Lemma 2.2** 相当:
  `maxAbelianIn_subset_of_le` / `thompsonJAbelian_le_of_le` (= (a) 遺伝性)、
  `thompsonJAbelian_eq_of_le_of_le` (= (a) の帰結 `J_a(P) ≤ Q ≤ P ⟹ J_a(Q) = J_a(P)`;
  (b) の Sylow 形はこれの系として必要時に)、
  `thompsonJAbelian_map_of_injective` (単射準同型共変性 ⟹ (c) 共役共変性 =
  `thompsonJAbelian_map_conj_eq_of_mem_normalizer`)、
  `thompsonJAbelian_top_characteristic` / `thompsonJAbelian_subgroupOf_characteristic`
  (= (d) characteristic 性)。

## Forward references (Gorenstein Ch.8 §2 の続き; issue 9403)

Thm 2.4 (Thompson)、Thm 2.5 (Thompson Replacement)、Thm 2.7 (Glauberman Replacement)、
Lem 2.8-2.10、Thm 2.11 (**Glauberman `Z(J)`-定理**) は後続。
-/

namespace Subgroup

open scoped commutatorElement

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

/-! ### Gorenstein Thm 2.4 (Thompson) へ向けた部品

`M := ⟨⁅x,a⁆ : a ∈ A⟩` を mathlib 慣習で取る (Gorenstein の `[x,A]` は
`[a,b] = a⁻¹b⁻¹ab` 慣習; `x` は全称なので statement は等価で, 計算は `x → x⁻¹`
の鏡映で移る). -/

/-- **Gorenstein Lemma 2.5(i)** (element 形, mathlib 慣習に鏡映): `y, z` が可換で
`⁅x,y⁆` と `⁅x,z⁆` が可換なら, 二重交換子は `y, z` について対称:
`⁅⁅x,y⁆⁻¹, z⁆ = ⁅⁅x,z⁆⁻¹, y⁆`.

Gorenstein p.20 の証明の鏡映: `⁅⁅x,y⁆⁻¹,z⁆` を
`x · ((x⁻¹yxy⁻¹)(x⁻¹zxz⁻¹)) · (zyx⁻¹y⁻¹z⁻¹)` に展開 (自由恒等式) し, 中央 2 因子
(どちらも `⁅x,·⁆⁻¹` の `x⁻¹`-共役ゆえ可換) を入れ替え, `yz = zy` で尾部を
整理すると `y ↔ z` を入れ替えた同じ展開に一致する.

⚠ G 原文の仮定「`[x,G]` abelian」より弱い仮定 (使う 2 元の可換性のみ) で成立 —
原文証明の `[x⁻¹,y] = [x^m,y] ∈ [x,G]` 帰納は `x⁻¹`-共役の観察で不要になる. -/
theorem commutatorElement_inv_rotate {x y z : G} (h1 : Commute y z)
    (h2 : Commute ⁅x, y⁆ ⁅x, z⁆) :
    ⁅⁅x, y⁆⁻¹, z⁆ = ⁅⁅x, z⁆⁻¹, y⁆ := by
  have key : ∀ b c : G,
      ⁅⁅x, b⁆⁻¹, c⁆
        = x * ((x⁻¹ * b * x * b⁻¹) * (x⁻¹ * c * x * c⁻¹))
            * (c * b * x⁻¹ * b⁻¹ * c⁻¹) := by
    intro b c
    group
  have hu : Commute (x⁻¹ * y * x * y⁻¹) (x⁻¹ * z * x * z⁻¹) := by
    have e : ∀ b : G, x⁻¹ * b * x * b⁻¹ = x⁻¹ * ⁅x, b⁆⁻¹ * x := by intro b; group
    rw [e y, e z]
    have hab : Commute ⁅x, y⁆⁻¹ ⁅x, z⁆⁻¹ := h2.inv_left.inv_right
    have hswap : (x⁻¹ * ⁅x, y⁆⁻¹ * x) * (x⁻¹ * ⁅x, z⁆⁻¹ * x)
        = (x⁻¹ * ⁅x, z⁆⁻¹ * x) * (x⁻¹ * ⁅x, y⁆⁻¹ * x) :=
      calc (x⁻¹ * ⁅x, y⁆⁻¹ * x) * (x⁻¹ * ⁅x, z⁆⁻¹ * x)
          = x⁻¹ * (⁅x, y⁆⁻¹ * ⁅x, z⁆⁻¹) * x := by group
        _ = x⁻¹ * (⁅x, z⁆⁻¹ * ⁅x, y⁆⁻¹) * x := by rw [hab.eq]
        _ = (x⁻¹ * ⁅x, z⁆⁻¹ * x) * (x⁻¹ * ⁅x, y⁆⁻¹ * x) := by group
    exact hswap
  have T : z * y * x⁻¹ * y⁻¹ * z⁻¹ = y * z * x⁻¹ * z⁻¹ * y⁻¹ := by
    have e1 : z * y * x⁻¹ * y⁻¹ * z⁻¹ = (z * y) * x⁻¹ * (z * y)⁻¹ := by group
    have e2 : y * z * x⁻¹ * z⁻¹ * y⁻¹ = (y * z) * x⁻¹ * (y * z)⁻¹ := by group
    rw [e1, e2, h1.symm.eq]
  calc ⁅⁅x, y⁆⁻¹, z⁆
      = x * ((x⁻¹ * y * x * y⁻¹) * (x⁻¹ * z * x * z⁻¹))
          * (z * y * x⁻¹ * y⁻¹ * z⁻¹) := key y z
    _ = x * ((x⁻¹ * z * x * z⁻¹) * (x⁻¹ * y * x * y⁻¹))
          * (y * z * x⁻¹ * z⁻¹ * y⁻¹) := by rw [hu.eq, T]
    _ = ⁅⁅x, z⁆⁻¹, y⁆ := (key z y).symm

/-- **Thm 2.4 の coset 単射の核** (Gorenstein p.271 中段の計算):
`d := ⁅x,u⁆⁻¹ · ⁅x,v⁆` が `A` を中心化すれば, `w := u⁻¹v` は全ての `⁅x,a⁆`
(`a ∈ A`) を中心化する.

計算: `d` は `u ∈ A` と可換なので `d = u⁻¹ d u = ⁅x, u⁻¹v⁆`. すると
`⁅⁅x,w⁆⁻¹, a⁆ = 1` (∀ a ∈ A) で, **Lemma 2.5(i)** の対称性から
`⁅⁅x,a⁆⁻¹, w⁆ = 1`, すなわち `w` が `⁅x,a⁆` を中心化する. -/
theorem commute_commutatorElement_of_inv_mul_mem_centralizer
    {A : Subgroup G} (hA : IsMulCommutative A) {x u v : G}
    (hu : u ∈ A) (hv : v ∈ A)
    (hM : ∀ a ∈ A, ∀ b ∈ A, Commute ⁅x, a⁆ ⁅x, b⁆)
    (hd : ⁅x, u⁆⁻¹ * ⁅x, v⁆ ∈ centralizer (A : Set G)) :
    ∀ a ∈ A, Commute (u⁻¹ * v) ⁅x, a⁆ := by
  haveI := hA
  have hw : u⁻¹ * v ∈ A := A.mul_mem (A.inv_mem hu) hv
  have hd' : ∀ a ∈ A, a * (⁅x, u⁆⁻¹ * ⁅x, v⁆) = (⁅x, u⁆⁻¹ * ⁅x, v⁆) * a :=
    mem_centralizer_iff.mp hd
  -- `d` は `u` と可換 ⟹ `d = u⁻¹ d u = ⁅x, u⁻¹v⁆`.
  have hd_eq : ⁅x, u⁆⁻¹ * ⁅x, v⁆ = ⁅x, u⁻¹ * v⁆ := by
    have h1 : u⁻¹ * (⁅x, u⁆⁻¹ * ⁅x, v⁆) * u = ⁅x, u⁻¹ * v⁆ := by group
    have h2 : u⁻¹ * (⁅x, u⁆⁻¹ * ⁅x, v⁆) * u = ⁅x, u⁆⁻¹ * ⁅x, v⁆ := by
      rw [mul_assoc, ← hd' u hu, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [← h2, h1]
  intro a ha
  -- `⁅⁅x,w⁆⁻¹, a⁆ = 1` (`⁅x,w⁆ = d` が `A` を中心化).
  have hwa : Commute ⁅x, u⁻¹ * v⁆ a := by
    rw [← hd_eq]
    exact ((hd' a ha).symm : _ * _ = _ * _)
  have hzero : ⁅⁅x, u⁻¹ * v⁆⁻¹, a⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr hwa.inv_left
  -- Lemma 2.5(i) の対称性で回転.
  have hrot := commutatorElement_inv_rotate
    (x := x) (setLike_mul_comm hw ha) (hM _ hw _ ha)
  rw [hzero] at hrot
  have hfin : Commute ⁅x, a⁆⁻¹ (u⁻¹ * v) :=
    commutatorElement_eq_one_iff_commute.mp hrot.symm
  exact (Commute.inv_left_iff.mp hfin).symm

/-- 可換部分群同士の join は, 片方が他方を中心化すればまた可換 (一般形).

⚠ 同内容の `OddOrder.BG.Ch4.S15.isMulCommutative_sup_of_le_centralizer` が下流
(BG Ch.4) に存在する — GroupTheory からは import 不可のため一般形を本 leaf に置く.
下流側の dedup は issue 9403 に記録. -/
theorem isMulCommutative_sup_of_le_centralizer {H K : Subgroup G}
    (hH : IsMulCommutative H) (hK : IsMulCommutative K)
    (hHK : H ≤ centralizer (K : Set G)) :
    IsMulCommutative (H ⊔ K : Subgroup G) := by
  rw [← le_centralizer_iff_isMulCommutative]
  refine sup_le ?_ ?_
  · rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff_isMulCommutative.mpr hH) (le_centralizer_iff.mp hHK)
  · rw [le_centralizer_iff]
    exact sup_le hHK (le_centralizer_iff_isMulCommutative.mpr hK)

/-- 可換性は部分群に遺伝する. -/
theorem isMulCommutative_of_le {H K : Subgroup G} (hK : IsMulCommutative K)
    (hHK : H ≤ K) : IsMulCommutative H := by
  haveI := hK
  exact .of_setLike_mul_comm fun a ha b hb => setLike_mul_comm (hHK ha) (hHK hb)

/-- **Gorenstein の `[x, A]`**: 元 `x` と部分群 `A` の交換子部分群
`⟨⁅x,a⁆ : a ∈ A⟩` (mathlib 慣習 `⁅x,a⁆ = xax⁻¹a⁻¹`).

⚠ `⁅zpowers x, A⁆` とは別物 (そちらは `⁅xⁿ, a⁆` を全て含む). Gorenstein Ch.8 §2
(Thompson / Glauberman replacement) の `[x, A]` はこの形. -/
def elementCommutator (x : G) (A : Subgroup G) : Subgroup G :=
  closure {m : G | ∃ a ∈ A, m = ⁅x, a⁆}

theorem commutatorElement_mem_elementCommutator {x a : G} {A : Subgroup G}
    (ha : a ∈ A) : ⁅x, a⁆ ∈ elementCommutator x A :=
  subset_closure ⟨a, ha, rfl⟩

/-- `x ∈ P`, `A ≤ P` なら `[x,A] ≤ P`. -/
theorem elementCommutator_le {x : G} {A P : Subgroup G} (hx : x ∈ P) (hA : A ≤ P) :
    elementCommutator x A ≤ P := by
  refine (closure_le _).mpr ?_
  rintro m ⟨a, ha, rfl⟩
  rw [SetLike.mem_coe, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx (hA ha)) (inv_mem hx)) (inv_mem (hA ha))

/-- 生成元 `⁅x,a⁆` すべてと可換な元は `[x,A]` を中心化する. -/
theorem mem_centralizer_elementCommutator_of_forall_commute {x w : G} {A : Subgroup G}
    (h : ∀ a ∈ A, Commute w ⁅x, a⁆) :
    w ∈ centralizer (elementCommutator x A : Set G) := by
  have hle : elementCommutator x A ≤ centralizer ({w} : Set G) := by
    refine (closure_le _).mpr ?_
    rintro m ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact (h a ha).eq
  rw [mem_centralizer_iff]
  intro m hm
  have hmw := mem_centralizer_iff.mp (hle hm) w rfl
  exact hmw.symm

/-- **Thm 2.4 部品 (Gorenstein の `C ∩ M = A ∩ M = C_M(A)`)**:
`M ≤ P` abelian について `C_M(A) = M ⊓ C_A(M)`. `≤` 側で **Lemma 2.1**
(`C_P(A) = A`) を使う. -/
theorem inf_centralizer_eq_of_mem_maxAbelianIn [Finite G] {P A M : Subgroup G}
    (hA : A ∈ maxAbelianIn P) (hMP : M ≤ P) (hM : IsMulCommutative M) :
    M ⊓ centralizer (A : Set G) = M ⊓ (A ⊓ centralizer (M : Set G)) := by
  apply le_antisymm
  · intro m hm
    have hmA : m ∈ A := by
      have hmem : m ∈ P ⊓ centralizer (A : Set G) := ⟨hMP hm.1, hm.2⟩
      rw [← eq_inf_centralizer_of_mem_maxAbelianIn hA] at hmem
      exact hmem
    exact ⟨hm.1, hmA, le_centralizer_iff_isMulCommutative.mpr hM hm.1⟩
  · intro m hm
    exact ⟨hm.1, le_centralizer_iff_isMulCommutative.mpr hA.2.1 hm.2.1⟩

/-- **積公式** (中心化版): `H ≤ C_G(K)` なら `|H ⊔ K| = [H : H ⊓ K] · |K|`
(`[H : H⊓K]` は `(K.subgroupOf H).index` で符号化). 第二同型定理 (normalizer 版
`QuotientGroup.quotientInfEquivProdNormalizerQuotient`) と Lagrange で数える. -/
theorem card_sup_of_le_centralizer [Finite G] {H K : Subgroup G}
    (hHK : H ≤ centralizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) = (K.subgroupOf H).index * Nat.card K := by
  have hnorm : H ≤ normalizer (K : Set G) := hHK.trans (centralizer_le_normalizer _)
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hnorm
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf (H ⊔ K))]
  congr 1
  · rw [Subgroup.index_eq_card]
    exact (Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hnorm).toEquiv).symm
  · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv

/-- **Thm 2.4 の coset 単射** (Gorenstein 「distinct cosets → distinct cosets」):
`[A : C_A(M)] ≤ [M : C_M(A)]` (`M := [x,A]` abelian).

商の代表元 (`Quotient.out`) 経由の単射 `⟦u⟧ ↦ ⟦⁅x,u⁆⟧` で証明する — 誘導写像の
well-definedness は不要 (Gorenstein の主張も単射性のみ). 単射性の核 =
`commute_commutatorElement_of_inv_mul_mem_centralizer` (Lemma 2.5(i) 対称性). -/
theorem index_centralizer_subgroupOf_le_of_elementCommutator [Finite G]
    {A : Subgroup G} {x : G} (hA : IsMulCommutative A)
    (hM : IsMulCommutative (elementCommutator x A)) :
    (((A ⊓ centralizer (elementCommutator x A : Set G))).subgroupOf A).index
      ≤ ((centralizer (A : Set G)).subgroupOf (elementCommutator x A)).index := by
  classical
  set M := elementCommutator x A with hMdef
  set C := A ⊓ centralizer (M : Set G) with hCdef
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  have hMcomm : ∀ a ∈ A, ∀ b ∈ A, Commute ⁅x, a⁆ ⁅x, b⁆ := by
    intro a ha b hb
    haveI := hM
    exact setLike_mul_comm (commutatorElement_mem_elementCommutator ha)
      (commutatorElement_mem_elementCommutator hb)
  refine Nat.card_le_card_of_injective
    (fun q => QuotientGroup.mk (⟨⁅x, ((Quotient.out q : ↥A) : G)⁆,
      commutatorElement_mem_elementCommutator (Quotient.out q : ↥A).2⟩ : ↥M)) ?_
  intro q q' hqq'
  set u : ↥A := Quotient.out q with hu_def
  set v : ↥A := Quotient.out q' with hv_def
  have hd : ⁅x, (u : G)⁆⁻¹ * ⁅x, (v : G)⁆ ∈ centralizer (A : Set G) := by
    have hmem := QuotientGroup.eq.mp hqq'
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa using hmem
  have hw : (u : G)⁻¹ * (v : G) ∈ C := by
    refine ⟨A.mul_mem (A.inv_mem u.2) v.2, ?_⟩
    exact mem_centralizer_elementCommutator_of_forall_commute
      (commute_commutatorElement_of_inv_mul_mem_centralizer hA u.2 v.2 hMcomm hd)
  have hcoset : (QuotientGroup.mk u : ↥A ⧸ C.subgroupOf A) = QuotientGroup.mk v := by
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    simpa using hw
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
  exact hcoset

/-- **Gorenstein Theorem 2.4** (Thompson): `A ∈ A(P)`, `x ∈ P` で
`M := [x,A] = ⟨⁅x,a⁆ : a ∈ A⟩` が abelian なら `M·C_A(M) ∈ A(P)`
(積は `M ⊔ (A ⊓ C(M))` で符号化).

Gorenstein pp. 271-272: `M·C_A(M)` は abelian (`C_A(M)` が `M` を中心化) で,
`|M·C| = |M||C|/|C∩M| ≥ |A|` が coset 単射
(`index_centralizer_subgroupOf_le_of_elementCommutator`) と `C∩M = C_M(A)`
(`inf_centralizer_eq_of_mem_maxAbelianIn`) から従うので, `A(P)` の最大位数性で
membership が出る. -/
theorem thompson_mem_maxAbelianIn [Finite G] {P A : Subgroup G} {x : G}
    (hA : A ∈ maxAbelianIn P) (hx : x ∈ P)
    (hM : IsMulCommutative (elementCommutator x A)) :
    elementCommutator x A ⊔ (A ⊓ centralizer (elementCommutator x A : Set G))
      ∈ maxAbelianIn P := by
  set M := elementCommutator x A with hMdef
  set C := A ⊓ centralizer (M : Set G) with hCdef
  have hMP : M ≤ P := elementCommutator_le hx hA.1
  have hCA : C ≤ A := inf_le_left
  have hCcomm : IsMulCommutative C := isMulCommutative_of_le hA.2.1 hCA
  have hMcent : M ≤ centralizer (C : Set G) := le_centralizer_iff.mp inf_le_right
  have hMCcomm : IsMulCommutative (M ⊔ C : Subgroup G) :=
    isMulCommutative_sup_of_le_centralizer hM hCcomm hMcent
  -- `|A| ≤ |M ⊔ C|`
  have hcard : Nat.card A ≤ Nat.card ↥(M ⊔ C) := by
    have h1 : Nat.card A = (C.subgroupOf A).index * Nat.card C := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf A),
        ← Subgroup.index_eq_card,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv]
    have h2 := index_centralizer_subgroupOf_le_of_elementCommutator
      (x := x) hA.2.1 hM
    have h3 : ((centralizer (A : Set G)).subgroupOf M).index
        = (C.subgroupOf M).index := by
      congr 1
      rw [← Subgroup.inf_subgroupOf_left (centralizer (A : Set G)) M,
        inf_centralizer_eq_of_mem_maxAbelianIn hA hMP hM,
        Subgroup.inf_subgroupOf_left C M]
    calc Nat.card A
        = (C.subgroupOf A).index * Nat.card C := h1
      _ ≤ (C.subgroupOf M).index * Nat.card C :=
          Nat.mul_le_mul_right _ (h3 ▸ h2)
      _ = Nat.card ↥(M ⊔ C) := (card_sup_of_le_centralizer hMcent).symm
  refine ⟨sup_le hMP (hCA.trans hA.1), hMCcomm, fun B hBP hBcomm => ?_⟩
  exact (hA.2.2 B hBP hBcomm).trans hcard

/-! ### Gorenstein Thm 2.5 (Thompson Replacement) へ向けた normalizer 部品 -/

/-- 有限群で, `x` との交換子が全て `A` に入るなら `x` は `A` を正規化する
(`x a x⁻¹ = ⁅x,a⁆ · a`; conj 像が `A` に含まれ位数一致で一致). -/
theorem mem_normalizer_of_forall_commutatorElement_mem [Finite G]
    {A : Subgroup G} {x : G} (h : ∀ a ∈ A, ⁅x, a⁆ ∈ A) :
    x ∈ normalizer (A : Set G) := by
  have hconj : ∀ a ∈ A, x * a * x⁻¹ ∈ A := by
    intro a ha
    have he : x * a * x⁻¹ = ⁅x, a⁆ * a := by group
    rw [he]
    exact A.mul_mem (h a ha) ha
  have hle : A.map (MulAut.conj x).toMonoidHom ≤ A := by
    rintro - ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using hconj a ha
  have heq : A.map (MulAut.conj x).toMonoidHom = A :=
    eq_of_le_of_card_ge hle
      (le_of_eq (card_map_of_injective (MulAut.conj x).injective).symm)
  rw [mem_normalizer_iff]
  intro h'
  constructor
  · intro hh
    have : (MulAut.conj x) h' ∈ A.map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hh
    rw [heq] at this
    simpa [MulAut.conj_apply] using this
  · intro hh
    have hmem : x * h' * x⁻¹ ∈ A.map (MulAut.conj x).toMonoidHom := heq.symm ▸ hh
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hmem
    have : a = h' := by
      have := hae
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      exact mul_left_cancel (mul_right_cancel this)
    exact this ▸ ha

/-- 2 つの部分群を正規化する元は交わりを正規化する. -/
theorem mem_normalizer_inf {S T : Subgroup G} {x : G}
    (hS : x ∈ normalizer (S : Set G)) (hT : x ∈ normalizer (T : Set G)) :
    x ∈ normalizer ((S ⊓ T : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hS hT ⊢
  intro h
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(hS h).mp h1, (hT h).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(hS h).mpr h1, (hT h).mpr h2⟩

/-- `A` の正規化元同士: `x, g ∈ N(A)` なら共役 `x g x⁻¹ ∈ N(A)`. -/
theorem conj_mem_normalizer {A : Subgroup G} {x g : G}
    (hx : x ∈ normalizer (A : Set G)) (hg : g ∈ normalizer (A : Set G)) :
    x * g * x⁻¹ ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff] at hx hg ⊢
  have hx' : ∀ a, a ∈ A ↔ x⁻¹ * a * x ∈ A := by
    intro a
    have h := hx (x⁻¹ * a * x)
    rw [show x * (x⁻¹ * a * x) * x⁻¹ = a by group] at h
    exact h.symm
  intro a
  rw [show x * g * x⁻¹ * a * (x * g * x⁻¹)⁻¹
      = x * (g * (x⁻¹ * a * x) * g⁻¹) * x⁻¹ by group]
  calc a ∈ A
      ↔ x⁻¹ * a * x ∈ A := hx' a
    _ ↔ g * (x⁻¹ * a * x) * g⁻¹ ∈ A := hg _
    _ ↔ x * (g * (x⁻¹ * a * x) * g⁻¹) * x⁻¹ ∈ A := hx _

/-- `A` を正規化する元は `N(A)` も正規化する. -/
theorem mem_normalizer_normalizer {A : Subgroup G} {x : G}
    (hx : x ∈ normalizer (A : Set G)) :
    x ∈ normalizer ((normalizer (A : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact conj_mem_normalizer hx hg
  · intro hg
    have hxinv : x⁻¹ ∈ normalizer (A : Set G) :=
      (normalizer (A : Set G)).inv_mem hx
    have hconj := conj_mem_normalizer hxinv hg
    rwa [show x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g by group] at hconj

/-- **Thm 2.5 の中心元選択** (Gorenstein pp. 272: `N = N_B(A) ⊴ AB` で
`B/N ∩ Z(AB/N) ≠ 1`): 有限 p-群 `P` 内で `A` が abelian `B` を正規化し `B` が
`A` を正規化しないとき, `x ∈ B − N_B(A)` で全交換子 `⁅x,a⁆` (`a ∈ A`) が
`N_B(A) = B ⊓ N(A)` に入るものが存在する.

商 `AB/N` の中心と `B/N` の交わりの非自明元 (`IsPGroup.normal_inf_center_nontrivial`)
を持ち上げる. -/
theorem exists_commutatorElement_mem_inf_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    {P A B : Subgroup G} (hP : IsPGroup p ↥P)
    (hAP : A ≤ P) (hBP : B ≤ P) (hBcomm : IsMulCommutative B)
    (hAnB : A ≤ normalizer (B : Set G)) (hBnA : ¬ B ≤ normalizer (A : Set G)) :
    ∃ x ∈ B, x ∉ normalizer (A : Set G) ∧
      ∀ a ∈ A, ⁅x, a⁆ ∈ B ⊓ normalizer (A : Set G) := by
  classical
  set N : Subgroup G := B ⊓ normalizer (A : Set G) with hNdef
  set H : Subgroup G := A ⊔ B with hHdef
  -- `H = AB` は `N` と `B` を正規化する
  have hB_norm_N : B ≤ normalizer (N : Set G) :=
    (le_centralizer_iff.mpr (inf_le_left.trans
      (le_centralizer_iff_isMulCommutative.mpr hBcomm))).trans (centralizer_le_normalizer _)
  have hA_norm_N : A ≤ normalizer (N : Set G) := fun a ha =>
    mem_normalizer_inf (hAnB ha) (mem_normalizer_normalizer (le_normalizer ha))
  have hH_norm_N : H ≤ normalizer (N : Set G) := sup_le hA_norm_N hB_norm_N
  have hH_norm_B : H ≤ normalizer (B : Set G) := sup_le hAnB le_normalizer
  haveI hNn : (N.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hH_norm_N
  haveI hBn : (B.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hH_norm_B
  have hHP : H ≤ P := sup_le hAP hBP
  have hpH : IsPGroup p ↥H :=
    (hP.to_subgroup (H.subgroupOf P)).of_equiv (Subgroup.subgroupOfEquivOfLe hHP)
  have hpQ : IsPGroup p (↥H ⧸ N.subgroupOf H) := hpH.to_quotient _
  set π := QuotientGroup.mk' (N.subgroupOf H) with hπdef
  set Bbar : Subgroup (↥H ⧸ N.subgroupOf H) := (B.subgroupOf H).map π with hBbardef
  haveI : Bbar.Normal := hBn.map _ (QuotientGroup.mk'_surjective _)
  -- `B̄` 非自明 (さもなくば `B ≤ N ≤ N(A)`)
  have hBbar_ne : Nontrivial ↥Bbar := by
    by_contra htriv
    refine hBnA fun b hb => ?_
    have hbH : b ∈ H := le_sup_right (α := Subgroup G) (a := A) hb
    have hbin : (⟨b, hbH⟩ : ↥H) ∈ B.subgroupOf H := by
      rwa [Subgroup.mem_subgroupOf]
    have hπb : π ⟨b, hbH⟩ ∈ Bbar := Subgroup.mem_map_of_mem _ hbin
    have hone : π ⟨b, hbH⟩ = 1 := by
      by_contra hne
      exact htriv ⟨⟨π ⟨b, hbH⟩, hπb⟩, 1, by simpa using hne⟩
    have hker : (⟨b, hbH⟩ : ↥H) ∈ N.subgroupOf H := by
      have := (QuotientGroup.eq_one_iff (⟨b, hbH⟩ : ↥H)).mp hone
      exact this
    rw [Subgroup.mem_subgroupOf] at hker
    exact hker.2
  -- 中心との交わりから非自明元を取る
  have hcent := OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial
    hpQ (N := Bbar) hBbar_ne
  obtain ⟨⟨z, hz⟩, hzone⟩ := exists_ne (1 : ↥(Bbar ⊓ center (↥H ⧸ N.subgroupOf H)))
  have hzne : z ≠ 1 := by
    intro h
    exact hzone (Subtype.ext h)
  obtain ⟨bin, hbin, hbz⟩ := Subgroup.mem_map.mp hz.1
  refine ⟨(bin : G), Subgroup.mem_subgroupOf.mp hbin, ?_, ?_⟩
  · -- `x ∉ N(A)` (さもなくば `z = 1`)
    intro hmem
    have hbinN : bin ∈ N.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨Subgroup.mem_subgroupOf.mp hbin, hmem⟩
    have : π bin = 1 := (QuotientGroup.eq_one_iff bin).mpr hbinN
    rw [hbz] at this
    exact hzne this
  · -- `⁅x, a⁆ ∈ N` (`z` が商の中心に居るので交換子が `ker π` に落ちる)
    intro a ha
    have haH : a ∈ H := le_sup_left (α := Subgroup G) (b := B) ha
    have hcomm : π ⁅bin, (⟨a, haH⟩ : ↥H)⁆ = 1 := by
      rw [map_commutatorElement, hbz]
      exact commutatorElement_eq_one_iff_commute.mpr
        ((Subgroup.mem_center_iff.mp hz.2 (π ⟨a, haH⟩)).symm)
    have hmem : ⁅bin, (⟨a, haH⟩ : ↥H)⁆ ∈ N.subgroupOf H :=
      (QuotientGroup.eq_one_iff _).mp hcomm
    rw [Subgroup.mem_subgroupOf] at hmem
    have hcoe : ((⁅bin, (⟨a, haH⟩ : ↥H)⁆ : ↥H) : G) = ⁅(bin : G), a⁆ := by
      simp [commutatorElement_def]
    rwa [hcoe] at hmem

/-- **Gorenstein Theorem 2.5** (Thompson Replacement Theorem):
`P` は (ambient `G` の部分群としての) 有限 p-群, `A ∈ A(P)`, `B ≤ P` abelian で,
`A` は `B` を正規化するが `B` は `A` を正規化しないとする. このとき `A* ∈ A(P)` で
(i) `A ∩ B < A* ∩ B` (真の包含), (ii) `A*` が `A` を正規化する, を満たすものが存在する
(witness は `A* = M ⊔ C_A(M)`, `M = [x,A]`, `x` は中心元選択で取る). -/
theorem thompson_replacement [Finite G] {p : ℕ} [Fact p.Prime] {P A B : Subgroup G}
    (hP : IsPGroup p ↥P) (hA : A ∈ maxAbelianIn P) (hBP : B ≤ P)
    (hBcomm : IsMulCommutative B) (hAnB : A ≤ normalizer (B : Set G))
    (hBnA : ¬ B ≤ normalizer (A : Set G)) :
    ∃ A' ∈ maxAbelianIn P, A ⊓ B < A' ⊓ B ∧ A' ≤ normalizer (A : Set G) := by
  obtain ⟨x, hxB, hxnA, hxc⟩ := exists_commutatorElement_mem_inf_normalizer
    hP hA.1 hBP hBcomm hAnB hBnA
  -- `M := [x,A] ≤ N_B(A)`, とくに abelian.
  have hMle : elementCommutator x A ≤ B ⊓ normalizer (A : Set G) := by
    refine (closure_le _).mpr ?_
    rintro m ⟨a, ha, rfl⟩
    exact hxc a ha
  have hMcomm : IsMulCommutative (elementCommutator x A) :=
    isMulCommutative_of_le hBcomm (hMle.trans inf_le_left)
  refine ⟨elementCommutator x A ⊔ (A ⊓ centralizer (elementCommutator x A : Set G)),
    thompson_mem_maxAbelianIn hA (hBP hxB) hMcomm, ?_, ?_⟩
  · -- (i) `A ∩ B < A* ∩ B`
    rw [SetLike.lt_iff_le_and_exists]
    constructor
    · -- `A ∩ B ≤ C_A(M) ≤ A*`, かつ `≤ B`
      have hABC : A ⊓ B ≤ A ⊓ centralizer (elementCommutator x A : Set G) := by
        refine le_inf inf_le_left ?_
        intro c hc
        refine mem_centralizer_elementCommutator_of_forall_commute ?_
        intro a ha
        haveI := hBcomm
        haveI := hA.2.1
        have hcx : Commute c x := setLike_mul_comm hc.2 hxB
        have hca : Commute c a := setLike_mul_comm hc.1 ha
        have hfull : Commute c ((x * a) * (x⁻¹ * a⁻¹)) :=
          (hcx.mul_right hca).mul_right (hcx.inv_right.mul_right hca.inv_right)
        simpa [commutatorElement_def, mul_assoc] using hfull
      exact le_inf (hABC.trans le_sup_right) inf_le_right
    · -- 真性の witness: `⁅x,a⁆ ∉ A` なる生成元
      obtain ⟨a, ha, hnotA⟩ : ∃ a ∈ A, ⁅x, a⁆ ∉ A := by
        by_contra h
        push Not at h
        exact hxnA (mem_normalizer_of_forall_commutatorElement_mem h)
      refine ⟨⁅x, a⁆, ⟨mem_sup_left (commutatorElement_mem_elementCommutator ha),
        (hMle (commutatorElement_mem_elementCommutator ha)).1⟩, ?_⟩
      exact fun hmem => hnotA hmem.1
  · -- (ii) `A* ≤ N(A)`
    exact sup_le (hMle.trans inf_le_right) (inf_le_left.trans le_normalizer)

/-- **Gorenstein Theorem 2.6**: `B` が `P` の abelian 正規部分群 (`P ≤ N(B)` で符号化)
なら, `B` が正規化する `A ∈ A(P)` が存在する.

`|A ⊓ B|` 最大の `A ∈ A(P)` を取れば, replacement (Thm 2.5) は `|A* ⊓ B|` を真に
増やすので適用不能 ⟹ `B ≤ N(A)`. -/
theorem exists_mem_maxAbelianIn_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    {P B : Subgroup G} (hP : IsPGroup p ↥P) (hBP : B ≤ P)
    (hBcomm : IsMulCommutative B) (hBnormal : P ≤ normalizer (B : Set G)) :
    ∃ A ∈ maxAbelianIn P, B ≤ normalizer (A : Set G) := by
  classical
  obtain ⟨A, hAmem, hAmax⟩ := Set.exists_max_image (maxAbelianIn P)
    (fun A => Nat.card ↥(A ⊓ B))
    (Set.finite_univ.subset fun _ _ => Set.mem_univ _)
    (maxAbelianIn_nonempty P)
  refine ⟨A, hAmem, ?_⟩
  by_contra hBnA
  obtain ⟨A', hA'mem, hlt, -⟩ := thompson_replacement hP hAmem hBP hBcomm
    (hAmem.1.trans hBnormal) hBnA
  have hle : Nat.card ↥(A' ⊓ B) ≤ Nat.card ↥(A ⊓ B) := hAmax A' hA'mem
  have hstrict : Nat.card ↥(A ⊓ B) < Nat.card ↥(A' ⊓ B) := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hlt.le) ?_
    intro heq
    exact hlt.ne (eq_of_le_of_card_ge hlt.le heq.ge)
  omega

/-! ### Gorenstein Lemma 2.2: 遺伝性・共変性・characteristic 性 -/

/-- **Gorenstein Lemma 2.2(a) 前半**: `R ≤ P` が `A(P)` の元を含めば `A(R) ⊆ A(P)`.

`A ∈ A(R)` は `A₀ ≤ R` (`A₀ ∈ A(P)`) より `|A₀| ≤ |A|`, 他方任意の abelian `B ≤ P` は
`|B| ≤ |A₀|` なので `A` は `P` 内でも最大位数. -/
theorem maxAbelianIn_subset_of_le {P R A₀ : Subgroup G}
    (hRP : R ≤ P) (hA₀ : A₀ ∈ maxAbelianIn P) (hA₀R : A₀ ≤ R) :
    maxAbelianIn R ⊆ maxAbelianIn P := by
  intro A hA
  refine ⟨hA.1.trans hRP, hA.2.1, fun B hBP hBcomm => ?_⟩
  calc Nat.card B ≤ Nat.card A₀ := hA₀.2.2 B hBP hBcomm
    _ ≤ Nat.card A := hA.2.2 A₀ hA₀R hA₀.2.1

/-- **Gorenstein Lemma 2.2(a) 後半**: `R ≤ P` が `A(P)` の元を含めば `J_a(R) ≤ J_a(P)`. -/
theorem thompsonJAbelian_le_of_le {P R A₀ : Subgroup G}
    (hRP : R ≤ P) (hA₀ : A₀ ∈ maxAbelianIn P) (hA₀R : A₀ ≤ R) :
    thompsonJAbelian R ≤ thompsonJAbelian P := by
  refine iSup_le fun A => iSup_le fun hA => ?_
  exact le_thompsonJAbelian_of_mem_maxAbelianIn
    (maxAbelianIn_subset_of_le hRP hA₀ hA₀R hA)

/-- **Gorenstein Lemma 2.2(a) の帰結** (Isaacs Thm 7.2 の abelian 版):
`J_a(P) ≤ Q ≤ P` のとき `J_a(Q) = J_a(P)`.

証明: `A(Q) = A(P)` を示す (双方向とも最大位数の一致から). Gorenstein (b) の
Sylow 形 (`J_a(P) ≤ Q ∈ Syl_p ⟹ J_a(Q) = J_a(P)`) は本補題の系として必要時に導く. -/
theorem thompsonJAbelian_eq_of_le_of_le [Finite G] {P Q : Subgroup G}
    (hJQ : thompsonJAbelian P ≤ Q) (hQP : Q ≤ P) :
    thompsonJAbelian Q = thompsonJAbelian P := by
  apply le_antisymm
  · -- `J_a(Q) ≤ J_a(P)`
    refine iSup_le fun A => iSup_le fun hA_Q => ?_
    obtain ⟨A₀, hA₀_P, hA₀_comm, hA₀_max⟩ := maxAbelianIn_nonempty P
    have hA₀_le_J : A₀ ≤ thompsonJAbelian P :=
      le_thompsonJAbelian_of_mem_maxAbelianIn ⟨hA₀_P, hA₀_comm, hA₀_max⟩
    have hA₀_Q : A₀ ≤ Q := hA₀_le_J.trans hJQ
    have hcard_A₀_le_A : Nat.card A₀ ≤ Nat.card A := hA_Q.2.2 A₀ hA₀_Q hA₀_comm
    have hA_P : A ≤ P := hA_Q.1.trans hQP
    have hcard_A_le_A₀ : Nat.card A ≤ Nat.card A₀ := hA₀_max A hA_P hA_Q.2.1
    apply le_thompsonJAbelian_of_mem_maxAbelianIn
    refine ⟨hA_P, hA_Q.2.1, fun B hB_P hB_comm => ?_⟩
    calc Nat.card B
        ≤ Nat.card A₀ := hA₀_max B hB_P hB_comm
      _ ≤ Nat.card A := hcard_A₀_le_A
  · -- `J_a(P) ≤ J_a(Q)`
    refine iSup_le fun A => iSup_le fun hA_P => ?_
    have hA_le_J : A ≤ thompsonJAbelian P :=
      le_thompsonJAbelian_of_mem_maxAbelianIn hA_P
    have hA_Q : A ≤ Q := hA_le_J.trans hJQ
    apply le_thompsonJAbelian_of_mem_maxAbelianIn
    refine ⟨hA_Q, hA_P.2.1, fun B hB_Q hB_comm => ?_⟩
    exact hA_P.2.2 B (hB_Q.trans hQP) hB_comm

/-- **`J_a` は単射準同型と可換**: `f : G →* N` 単射, `P ≤ G` について
`J_a(f(P)) = f(J_a(P))` (Gorenstein Lemma 2.2(c) の一般形).

`f(P)` の abelian 部分群は `P` の abelian 部分群の `f`-像とちょうど対応する
(単射性が可換性と位数の両方を保存). -/
theorem thompsonJAbelian_map_of_injective {N : Type*} [Group N]
    {f : G →* N} (hf : Function.Injective f) (P : Subgroup G) :
    thompsonJAbelian (P.map f) = (thompsonJAbelian P).map f := by
  -- `E ≤ P.map f` は `E.comap f ≤ P` の像で, 位数・可換性が対応する.
  have key_comap : ∀ E : Subgroup N, E ∈ maxAbelianIn (P.map f) →
      E.comap f ∈ maxAbelianIn P ∧ (E.comap f).map f = E := by
    intro E hE
    obtain ⟨hE_le, hE_comm, hE_max⟩ := hE
    have hE_le_range : E ≤ f.range := hE_le.trans (Subgroup.map_le_range f P)
    have hmap_comap : (E.comap f).map f = E :=
      Subgroup.map_comap_eq_self hE_le_range
    refine ⟨⟨?_, ?_, ?_⟩, hmap_comap⟩
    · rw [← Subgroup.comap_map_eq_self_of_injective hf P]
      exact Subgroup.comap_mono hE_le
    · haveI := hE_comm
      exact E.comap_injective_isMulCommutative hf
    · intro B hB_P hB_comm
      haveI := hB_comm
      have hBmap_le : B.map f ≤ P.map f := Subgroup.map_mono hB_P
      have hcard_B : Nat.card (B.map f) = Nat.card B :=
        Subgroup.card_map_of_injective hf
      have hcard_E : Nat.card E = Nat.card (E.comap f) := by
        conv_lhs => rw [← hmap_comap]
        exact Subgroup.card_map_of_injective hf
      have hstep : Nat.card (B.map f) ≤ Nat.card E :=
        hE_max (B.map f) hBmap_le (map_isMulCommutative B f)
      rw [← hcard_E, ← hcard_B]
      exact hstep
  -- `A ∈ A(P)` の像は `A(P.map f)` の元.
  have key_map : ∀ A : Subgroup G, A ∈ maxAbelianIn P →
      A.map f ∈ maxAbelianIn (P.map f) := by
    intro A hA
    obtain ⟨hA_le, hA_comm, hA_max⟩ := hA
    haveI := hA_comm
    refine ⟨Subgroup.map_mono hA_le, map_isMulCommutative A f, ?_⟩
    intro B hB_le hB_comm
    have hB_le_range : B ≤ f.range := hB_le.trans (Subgroup.map_le_range f P)
    have hB_mapcomap : (B.comap f).map f = B := Subgroup.map_comap_eq_self hB_le_range
    have hBcomap_le : B.comap f ≤ P := by
      rw [← Subgroup.comap_map_eq_self_of_injective hf P]
      exact Subgroup.comap_mono hB_le
    have hBcomap_comm : IsMulCommutative (B.comap f) := by
      haveI := hB_comm
      exact B.comap_injective_isMulCommutative hf
    have hcard_B : Nat.card B = Nat.card (B.comap f) := by
      conv_lhs => rw [← hB_mapcomap]
      exact Subgroup.card_map_of_injective hf
    have hcard_A : Nat.card (A.map f) = Nat.card A := Subgroup.card_map_of_injective hf
    calc Nat.card B = Nat.card (B.comap f) := hcard_B
      _ ≤ Nat.card A := hA_max (B.comap f) hBcomap_le hBcomap_comm
      _ = Nat.card (A.map f) := hcard_A.symm
  apply le_antisymm
  · refine iSup_le fun E => iSup_le fun hE => ?_
    obtain ⟨hEcomap_mem, hmapcomap⟩ := key_comap E hE
    rw [← hmapcomap]
    exact Subgroup.map_mono (le_thompsonJAbelian_of_mem_maxAbelianIn hEcomap_mem)
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun A => iSup_le fun hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_thompsonJAbelian_of_mem_maxAbelianIn (key_map A hA)

/-- **Gorenstein Lemma 2.2(c)** (正規化元による共役不変): `g ∈ N(P)` なら
`g · J_a(P) · g⁻¹ = J_a(P)`. -/
theorem thompsonJAbelian_map_conj_eq_of_mem_normalizer {P : Subgroup G}
    {g : G} (hg : g ∈ normalizer (P : Set G)) :
    (thompsonJAbelian P).map (MulAut.conj g).toMonoidHom = thompsonJAbelian P := by
  have hg_iff : ∀ n, n ∈ P ↔ g * n * g⁻¹ ∈ P := mem_normalizer_iff.mp hg
  have hP_conj : P.map (MulAut.conj g).toMonoidHom = P := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hg_iff z).mp hz
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, ?_⟩
      · have hmem : g * (g⁻¹ * y * g) * g⁻¹ ∈ P := by
          have heq : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
          rw [heq]; exact hy
        exact (hg_iff (g⁻¹ * y * g)).mpr hmem
      · change g * (g⁻¹ * y * g) * g⁻¹ = y
        group
  rw [← thompsonJAbelian_map_of_injective (MulAut.conj g).injective P, hP_conj]

/-! ### Gorenstein Lemma 2.2(d): `J_a(P)` は `P` 内 characteristic -/

/-- `↥P` 内で計算した `J_a` を `P.subtype` で押し出すと ambient の `J_a(P)` に一致. -/
theorem thompsonJAbelian_top_map_subtype (P : Subgroup G) :
    (thompsonJAbelian (⊤ : Subgroup ↥P)).map P.subtype = thompsonJAbelian P := by
  rw [← thompsonJAbelian_map_of_injective P.subtype_injective (⊤ : Subgroup ↥P),
    ← MonoidHom.range_eq_map, P.range_subtype]

/-- `J_a(P)` を `↥P` 内で見ると, 全体群 `↥P` の `J_a`. -/
theorem thompsonJAbelian_subgroupOf_self (P : Subgroup G) :
    (thompsonJAbelian P).subgroupOf P = thompsonJAbelian (⊤ : Subgroup ↥P) := by
  rw [← thompsonJAbelian_top_map_subtype P, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective]

/-- **`J_a(H)` は characteristic** (top 形): 自己同型は `A(H)` を置換するので
join `J_a(H)` を固定する. -/
instance thompsonJAbelian_top_characteristic :
    (thompsonJAbelian (⊤ : Subgroup G)).Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.mpr fun ϕ => ?_
  rw [← thompsonJAbelian_map_of_injective ϕ.injective (⊤ : Subgroup G)]
  congr 1
  simp

/-- **Gorenstein Lemma 2.2(d)**: `J_a(P)` は `P` 内 characteristic
(`Subgroup ↥P` の `Subgroup.Characteristic` 形). -/
instance thompsonJAbelian_subgroupOf_characteristic (P : Subgroup G) :
    ((thompsonJAbelian P).subgroupOf P).Characteristic := by
  rw [thompsonJAbelian_subgroupOf_self]
  infer_instance

/-! ### Gorenstein Lemma 2.8 へ向けた `[B,A;i]` 部品

Gorenstein の `[B,A;i]` (帰納定義 `[B,A;0] = B`, `[B,A;i] = [[B,A;i-1],A]`) は
repo 既存の `OddOrder.Isaacs.Ch04.iterCommutator B A i` そのもの. ここでは
Lem 2.8(ii) (降下) と正規化の基本性質を与える. -/

open OddOrder.Isaacs.Ch04 in
/-- `A` は `⁅X, A⁆` を正規化する (`⁅X,A⁆ = ⁅A,X⁆` + 左因子は正規化する). -/
theorem le_normalizer_commutator_right (X A : Subgroup G) :
    A ≤ normalizer ((⁅X, A⁆ : Subgroup G) : Set G) := by
  rw [commutator_comm X A]
  exact normalizer_commutator_ge_left A X

open OddOrder.Isaacs.Ch04 in
/-- `A` は各 `[B,A;i]` を正規化する (Gorenstein Lem 2.8 の途中主張;
`i = 0` は `B ⊴ G`, `i ≥ 1` は右因子正規化で無条件). -/
theorem le_normalizer_iterCommutator {B : Subgroup G} (A : Subgroup G) [B.Normal]
    (i : ℕ) : A ≤ normalizer ((iterCommutator B A i : Subgroup G) : Set G) := by
  cases i with
  | zero =>
    rw [iterCommutator_zero]
    intro a _
    rw [mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => ‹B.Normal›.conj_mem h hh a
    · intro hh
      have hconj := ‹B.Normal›.conj_mem _ hh a⁻¹
      rwa [show a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h by group] at hconj
  | succ i =>
    rw [iterCommutator_succ]
    exact le_normalizer_commutator_right _ A

open OddOrder.Isaacs.Ch04 in
/-- **Gorenstein Lemma 2.8(ii)**: `[B,A;i+1] ≤ [B,A;i]`. -/
theorem iterCommutator_succ_le {B : Subgroup G} (A : Subgroup G) [B.Normal]
    (i : ℕ) : iterCommutator B A (i + 1) ≤ iterCommutator B A i := by
  rw [iterCommutator_succ]
  exact le_normalizer_iff_commutator_le_left.mp (le_normalizer_iterCommutator A i)

open OddOrder.Isaacs.Ch04 in
/-- `[B,A;i]` の単調降下 (一般 `i ≤ j` 形). -/
theorem iterCommutator_le_of_le {B : Subgroup G} (A : Subgroup G) [B.Normal]
    {i j : ℕ} (h : i ≤ j) : iterCommutator B A j ≤ iterCommutator B A i := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hij | hij
    · exact (iterCommutator_succ_le A j).trans (ih (Nat.lt_succ_iff.mp hij))
    · rw [Nat.le_antisymm h hij]

open OddOrder.Isaacs.Ch04 in
/-- `[B,A;i] ≤ B`. -/
theorem iterCommutator_le_base {B : Subgroup G} (A : Subgroup G) [B.Normal]
    (i : ℕ) : iterCommutator B A i ≤ B :=
  iterCommutator_le_of_le A (Nat.zero_le i)

end Subgroup
