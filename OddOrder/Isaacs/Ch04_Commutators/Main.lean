/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import Mathlib.LinearAlgebra.Dual.Lemmas
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03
import OddOrder.Mathlib.SemidirectProduct
import OddOrder.Mathlib.Subgroup

/-!
# OddOrder.Isaacs.Ch04 — Commutators

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 4
"Commutators" (pp. 113-146) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 4A | 交換子の基礎 + 下降中心列 + maximal class p-群 + Ω_r | 4.1 – 4.8 | 完成 |
| 4B | Hall-Witt + three-subgroups lemma + Mann | 4.9 – 4.19 | 4.9-4.13 完成; Mann 後回し |
| 4C | A acts on G via automorphisms | 4.20 – 4.27 | 完成 |
| 4D | Coprime action: Fitting + Thompson P×Q + Baer | 4.28 – 4.38 | 完成 |

## Mathlib direct correspondence (no wrapper)

| Isaacs | mathlib |
|---|---|
| `[g₁, g₂] = 1 ↔ g₁ g₂ = g₂ g₁` | `commutatorElement_eq_one_iff_mul_comm` |
| `⁅H, K⁆ = ⁅K, H⁆` | `Subgroup.commutator_comm` |
| **Lemma 4.2** quotient `f(⁅H,K⁆) = ⁅fH, fK⁆` | `Subgroup.map_commutator` |
| `⁅H,K⁆ = ⊥ ↔ H ⊆ Z_G(K)` | `Subgroup.commutator_eq_bot_iff_le_centralizer` |
| `⁅H₁, H₂⁆ ≤ H₂` (H₂ normal 仮定) | `Subgroup.commutator_le_right` |
| **Lemma 4.9 Three-subgroups** | `Subgroup.commutator_commutator_eq_bot_of_rotate` |
| 下降中心列 `G^k` | `lowerCentralSeries`, `lowerCentralSeries_succ` |

注: mathlib `lowerCentralSeries` の index 規約は Isaacs `G^k` と **オフセット 1 ずれ** —
mathlib `lcs 0 = ⊤ = G^1`, `lcs 1 = G' = G^2`, `lcs n = G^{n+1}`.

ノート: [`notes/isaacs/ch04_commutators.md`](../../../notes/isaacs/ch04_commutators.md)
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 4A: Commutator basics, lower central series (pp. 113-122) -/

/-- Helper: `g * ⁅a, b⁆ * g⁻¹ = ⁅g * a, b⁆ * ⁅b, g⁆`. -/
private lemma conj_commutator_split (g a b : G) :
    g * ⁅a, b⁆ * g⁻¹ = ⁅g * a, b⁆ * ⁅b, g⁆ := by
  simp only [commutatorElement_def]
  group

/-- **Isaacs Lemma 4.1**: `H, K ≤ G` のとき `H` は `⁅H, K⁆` を正規化する.
**仮定なし版** (H, K の正規性を要求しない).

証明: 一般 identity `g · ⁅a, b⁆ · g⁻¹ = ⁅g a, b⁆ · ⁅b, g⁆` を使用. h ∈ H に対して
`h · ⁅h', k⁆ · h⁻¹ = ⁅h h', k⁆ · ⁅k, h⁆`. 両因子は `⁅H, K⁆` 内. 生成元から
closure_induction で一般元へ. -/
theorem subgroup_le_normalizer_commutator_self (H K : Subgroup G) :
    H ≤ Subgroup.normalizer (⁅H, K⁆ : Subgroup G) := by
  -- For h ∈ H and x ∈ ⁅H,K⁆, both h x h⁻¹ ∈ ⁅H,K⁆ and h⁻¹ x h ∈ ⁅H,K⁆ hold by the
  -- same closure induction (since h⁻¹ ∈ H as well).
  have key : ∀ h ∈ H, ∀ x ∈ (⁅H, K⁆ : Subgroup G),
      h * x * h⁻¹ ∈ (⁅H, K⁆ : Subgroup G) := by
    intro h hh x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with ⟨h', hh', k, hk, rfl⟩
      rw [conj_commutator_split]
      refine Subgroup.mul_mem _ ?_ ?_
      · exact Subgroup.commutator_mem_commutator (H.mul_mem hh hh') hk
      · -- ⁅k, h⁆ ∈ ⁅K, H⁆ = ⁅H, K⁆.
        have hKH : ⁅k, h⁆ ∈ (⁅K, H⁆ : Subgroup G) :=
          Subgroup.commutator_mem_commutator hk hh
        rwa [Subgroup.commutator_comm] at hKH
    | one => simp
    | mul x y _ _ ihx ihy =>
      have eq : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
      rw [eq]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x _ ihx =>
      have eq : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
      rw [eq]
      exact Subgroup.inv_mem _ ihx
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key h hh x, fun hx => ?_⟩
  -- (⇐): conjugate `h * x * h⁻¹` back by `h⁻¹`.
  have hh_inv : h⁻¹ ∈ H := H.inv_mem hh
  have := key h⁻¹ hh_inv (h * x * h⁻¹) hx
  have eq : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
  rwa [eq] at this

/-- **Isaacs Lemma 4.1** (symmetric form): `K` も `⁅H, K⁆` を正規化する.
`⁅H, K⁆ = ⁅K, H⁆` 経由で上記から導出. -/
theorem subgroup_le_normalizer_commutator_self_right (H K : Subgroup G) :
    K ≤ Subgroup.normalizer (⁅H, K⁆ : Subgroup G) := by
  rw [Subgroup.commutator_comm]
  exact subgroup_le_normalizer_commutator_self K H

/-- **Isaacs Lem 4.1 系**: `H ⊔ K = ⊤` ⇒ `⁅H, K⁆` は G で normal.
`H` も `K` も `⁅H, K⁆` を正規化 (Lem 4.1) ⇒ `H ⊔ K ≤ N(⁅H, K⁆)`, `⊤ ≤ N(⁅H, K⁆)`,
よって `⁅H, K⁆.Normal`. mathlib `commutator_normal` instance は `H, K` 両方 G で normal
を要求するが, ここでは生成集合の `⊔` だけで十分. -/
theorem commutator_normal_of_sup_eq_top {H K : Subgroup G} (hsup : H ⊔ K = ⊤) :
    (⁅H, K⁆ : Subgroup G).Normal := by
  refine Subgroup.normalizer_eq_top_iff.mp ?_
  rw [← top_le_iff, ← hsup]
  exact sup_le (subgroup_le_normalizer_commutator_self H K)
    (subgroup_le_normalizer_commutator_self_right H K)

/-! **Isaacs Lemma 4.2** (quotient/map commutator):
`f : G →* G'` の像での commutator は元の像の commutator.
**mathlib `Subgroup.map_commutator` 直接利用**. wrapper 不要. -/

/-- If a commutator-to-Fitting bound holds after restricting `A` and `B` to
`A ⊔ B`, then it pushes forward to the ambient group. -/
theorem commutator_le_fitting_of_subgroupOf_sup {G : Type*} [Group G] [Finite G]
    {A B : Subgroup G}
    (h : ⁅A.subgroupOf (A ⊔ B), B.subgroupOf (A ⊔ B)⁆ ≤
      (OddOrder.Isaacs.Ch01.fitting ↥(A.subgroupOf (A ⊔ B))).map
        (A.subgroupOf (A ⊔ B)).subtype) :
    ⁅A, B⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥A).map A.subtype := by
  have hAS : A ≤ A ⊔ B := le_sup_left
  have hBS : B ≤ A ⊔ B := le_sup_right
  set e := Subgroup.subgroupOfEquivOfLe hAS with he
  have hcomp : (A ⊔ B).subtype.comp (A.subgroupOf (A ⊔ B)).subtype =
      A.subtype.comp e.toMonoidHom := by
    ext a'
    rfl
  have key : ((OddOrder.Isaacs.Ch01.fitting ↥(A.subgroupOf (A ⊔ B))).map
        (A.subgroupOf (A ⊔ B)).subtype).map (A ⊔ B).subtype =
      (OddOrder.Isaacs.Ch01.fitting ↥A).map A.subtype := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      OddOrder.Isaacs.Ch01.fitting_map_mulEquiv e]
  have hcomm :
      (⁅A.subgroupOf (A ⊔ B), B.subgroupOf (A ⊔ B)⁆).map (A ⊔ B).subtype =
        ⁅A, B⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAS, inf_eq_left.mpr hBS]
  calc ⁅A, B⁆
      = (⁅A.subgroupOf (A ⊔ B), B.subgroupOf (A ⊔ B)⁆).map (A ⊔ B).subtype :=
        hcomm.symm
    _ ≤ ((OddOrder.Isaacs.Ch01.fitting ↥(A.subgroupOf (A ⊔ B))).map
          (A.subgroupOf (A ⊔ B)).subtype).map (A ⊔ B).subtype := Subgroup.map_mono h
    _ = (OddOrder.Isaacs.Ch01.fitting ↥A).map A.subtype := key

/-- **Isaacs Lemma 4.3** (片向き): `⁅H, K⁆ ≤ H` ⇒ `K ≤ N(H)`. -/
theorem le_normalizer_of_commutator_le {H K : Subgroup G}
    (h : ⁅H, K⁆ ≤ H) : K ≤ Subgroup.normalizer H := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    -- k * x * k⁻¹ = ⁅k, x⁆ * x. ⁅k, x⁆ ∈ ⁅K, H⁆ = ⁅H, K⁆ ≤ H.
    have eq : k * x * k⁻¹ = ⁅k, x⁆ * x := by
      simp only [commutatorElement_def]; group
    rw [eq]
    refine H.mul_mem ?_ hx
    have hcomm : ⁅k, x⁆ ∈ (⁅H, K⁆ : Subgroup G) := by
      have := Subgroup.commutator_mem_commutator hk hx (H₁ := K) (H₂ := H)
      rwa [Subgroup.commutator_comm] at this
    exact h hcomm
  · intro hx
    -- (⇐) reverse direction via k⁻¹.
    have hk_inv : k⁻¹ ∈ K := K.inv_mem hk
    have eq : k⁻¹ * (k * x * k⁻¹) * k = x := by group
    have : k⁻¹ * (k * x * k⁻¹) * (k⁻¹)⁻¹ ∈ H := by
      simp only [inv_inv]
      have heq : k⁻¹ * (k * x * k⁻¹) * k = ⁅k⁻¹, k * x * k⁻¹⁆ * (k * x * k⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [heq]
      refine H.mul_mem ?_ hx
      have hcomm : ⁅k⁻¹, k * x * k⁻¹⁆ ∈ (⁅H, K⁆ : Subgroup G) := by
        have := Subgroup.commutator_mem_commutator hk_inv hx (H₁ := K) (H₂ := H)
        rwa [Subgroup.commutator_comm] at this
      exact h hcomm
    simpa [eq] using this

/-- **Isaacs Lemma 4.3** (逆向き): `K ≤ N(H)` ⇒ `⁅H, K⁆ ≤ H`. -/
theorem commutator_le_of_le_normalizer {H K : Subgroup G}
    (h : K ≤ Subgroup.normalizer H) : ⁅H, K⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro h' hh' k hk
  -- ⁅h', k⁆ = h' * (k * h'⁻¹ * k⁻¹). k normalizes H, so k * h'⁻¹ * k⁻¹ ∈ H.
  have hk_in_N : k ∈ Subgroup.normalizer H := h hk
  rw [Subgroup.mem_normalizer_iff] at hk_in_N
  have h_inv : h'⁻¹ ∈ H := H.inv_mem hh'
  have h_kh : k * h'⁻¹ * k⁻¹ ∈ H := (hk_in_N h'⁻¹).mp h_inv
  have eq : ⁅h', k⁆ = h' * (k * h'⁻¹ * k⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [eq]
  exact H.mul_mem hh' h_kh

/-- **Isaacs Lemma 4.3** (iff 版): `⁅H, K⁆ ≤ H ↔ K ≤ N(H)`. -/
theorem commutator_le_iff_le_normalizer {H K : Subgroup G} :
    ⁅H, K⁆ ≤ H ↔ K ≤ Subgroup.normalizer H :=
  ⟨le_normalizer_of_commutator_le, commutator_le_of_le_normalizer⟩

/-! **Isaacs Lemma 4.3** corollary: `H ⊴ G ↔ ⁅G, H⁆ ≤ H`.
mathlib `Subgroup.commutator_top_left_le_iff` 直接 (Lemma 4.3 iff の `K = ⊤` 系). -/

/-! **Isaacs Lemma 4.4** (class 2 p-群 exponent 一致):
`P` p-群, class ≤ 2, `P'` exponent `p^e` ⇒ `P/Z(P)` exponent も `p^e`.
形式化保留 (Subgroup `Monoid.exponent` API 拡張要). -/

/-! ### Lemma 4.4 helpers: class ≤ 2 ⇒ `⁅·, z⁆` は左で homomorphism -/

/-- General commutator identity (no hypothesis):
`⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆`. -/
private lemma commutatorElement_mul_left_eq (x y z : G) :
    ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
  simp only [commutatorElement_def]
  group

/-- Helper: `⁅x, y⁆ ∈ commutator G` for all `x, y : G`. -/
private lemma commutatorElement_mem_commutator_top (x y : G) :
    ⁅x, y⁆ ∈ _root_.commutator G := by
  rw [_root_.commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

/-- In class ≤ 2 (`commutator G ≤ Z(G)`), the map `⁅·, z⁆ : G → G'` is a
homomorphism on the left: `⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆`.

**証明**: 一般 identity `⁅x*y, z⁆ = x · ⁅y, z⁆ · x⁻¹ · ⁅x, z⁆` で `⁅y, z⁆` 中心
⇒ `x · ⁅y, z⁆ = ⁅y, z⁆ · x` ⇒ `x · ⁅y, z⁆ · x⁻¹ = ⁅y, z⁆`. 結果 `⁅y, z⁆ · ⁅x, z⁆`
を `⁅x, z⁆` 中心で swap. -/
private lemma commutatorElement_mul_left_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have h_yz : ⁅y, z⁆ ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top y z)
  have h_xz : ⁅x, z⁆ ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top x z)
  rw [commutatorElement_mul_left_eq]
  rw [show x * ⁅y, z⁆ = ⁅y, z⁆ * x from Subgroup.mem_center_iff.mp h_yz x]
  rw [mul_inv_cancel_right]
  exact Subgroup.mem_center_iff.mp h_xz ⁅y, z⁆

/-- In class ≤ 2, `⁅x^n, z⁆ = ⁅x, z⁆^n` for all `n : ℕ`. 帰納で `*` 版から従う. -/
private lemma commutatorElement_pow_left_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x z : G) (n : ℕ) :
    ⁅x^n, z⁆ = ⁅x, z⁆^n := by
  induction n with
  | zero => simp [commutatorElement_def]
  | succ k ih =>
    rw [pow_succ, commutatorElement_mul_left_of_class_le_two hC, ih, pow_succ]

/-! ### Isaacs Lemma 4.4 -/

/-- **Isaacs Lemma 4.4** (main, 一般化): `commutator G ≤ Z(G)` (class ≤ 2) で
全交換子の `n` 乗が `1` ⇒ 任意 `x : G` で `x^n ∈ Z(G)`.

Isaacs は `p`-群 + `n = p^e` で述べるが, 証明は class ≤ 2 + 任意 `n` で動く.

**証明** (Isaacs p.116): 任意 `z : G` で `⁅x^n, z⁆ = ⁅x, z⁆^n = 1`
(class ≤ 2 ⇒ `⁅·, z⁆` 左 hom + `⁅x, z⁆ ∈ G'` 仮定で `n` 乗 1). よって `x^n` は
全 `z` と可換 ⇒ `x^n ∈ Z(G)`. -/
theorem pow_mem_center_of_class_le_two_of_commutator_pow
    {n : ℕ} (hC : _root_.commutator G ≤ Subgroup.center G)
    (hExp : ∀ c ∈ _root_.commutator G, c ^ n = 1) (x : G) :
    x ^ n ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro z
  rw [eq_comm, ← commutatorElement_eq_one_iff_mul_comm,
      commutatorElement_pow_left_of_class_le_two hC]
  exact hExp ⁅x, z⁆ (commutatorElement_mem_commutator_top x z)

/-- **Isaacs Lemma 4.4** (elementary abelian corollary, "In particular" 部分):
`commutator G ≤ Z(G)` + `P'` が `p`-elementary abelian (∀ c ∈ G', c ^ p = 1)
⇒ `G/Z(G)` も `p`-elementary abelian.

(Φ(G) ⊆ Z(G) への帰結は Lem 4.5 forward を経由: 後段 `frattini_le_center_of_...` 参照.) -/
theorem isElementaryAbelian_quotient_center_of_class_le_two
    {p : ℕ} (hC : _root_.commutator G ≤ Subgroup.center G)
    (hExp : ∀ c ∈ _root_.commutator G, c ^ p = 1) :
    OddOrder.GroupTheory.IsElementaryAbelian p (G ⧸ Subgroup.center G) := by
  refine ⟨?_, ?_⟩
  · exact (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hC).is_comm.comm
  · intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    have hxp : x^p ∈ Subgroup.center G :=
      pow_mem_center_of_class_le_two_of_commutator_pow hC hExp x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hxp

/-! ### Lemma 4.5: P/N elementary abelian ⇔ Φ(P) ⊆ N -/

/-- Helper: For finite `p`-group `P` and maximal subgroup `M`, `M.index = p`.

**証明**: `M` 正規 (nilpotent + max). `|P/M| = p^k`. `k = 1` を示す:
- `k = 0` ⇒ `M = ⊤`, 矛盾.
- `k ≥ 2` ⇒ Cauchy で `P/M` に order `p` の元 `g` 存在 ⇒ `⟨g⟩` は order `p` の subgroup.
  pull back で `M < H' < ⊤` (M maximal と矛盾). -/
private lemma index_eq_prime_of_isCoatom_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P) {M : Subgroup P} (hMax : IsCoatom M) : M.index = p := by
  haveI : Group.IsNilpotent P := hP.isNilpotent
  have hMnormal : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M
      (normalizerCondition_of_isNilpotent (G := P)) hMax
  haveI := hMnormal
  have hPQuot : IsPGroup p (P ⧸ M) := hP.to_quotient M
  obtain ⟨k, hk⟩ := hPQuot.exists_card_eq
  have h_idx : M.index = Nat.card (P ⧸ M) := Subgroup.index_eq_card _
  have hM_ne_top : M ≠ ⊤ := hMax.1
  -- k ≥ 1 (else |P/M| = 1, so M = ⊤)
  have hk_pos : 1 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k
    rw [pow_zero] at hk
    have hsub : Subsingleton (P ⧸ M) := Nat.card_eq_one_iff_unique.mp hk |>.1
    apply hM_ne_top
    rw [Subgroup.eq_top_iff']
    intro x
    have h1 : (QuotientGroup.mk x : P ⧸ M) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff x).mp h1
  -- Suppose k ≥ 2 for contradiction
  by_contra h_idx_ne
  have hk_ne_1 : k ≠ 1 := fun h_eq => h_idx_ne (by rw [h_idx, hk, h_eq, pow_one])
  have hk_ge_2 : 2 ≤ k := Nat.lt_of_le_of_ne hk_pos (Ne.symm hk_ne_1)
  -- Cauchy: ∃ g : P/M, orderOf g = p
  have hp_dvd : p ∣ Nat.card (P ⧸ M) := by
    rw [hk]; exact dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hk_pos)
  obtain ⟨g, hg_ord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  -- ⟨g⟩ has order p
  let H : Subgroup (P ⧸ M) := Subgroup.zpowers g
  have hH_card : Nat.card H = p := by rw [Nat.card_zpowers, hg_ord]
  -- |P/M| = p^k > p for k ≥ 2
  have hp_lt : p < Nat.card (P ⧸ M) := by
    rw [hk]
    calc p = p^1 := (pow_one p).symm
      _ < p^k := by apply pow_lt_pow_right₀ hp.out.one_lt; omega
  have hH_ne_top : H ≠ ⊤ := by
    intro hH_top
    have hcard_eq : Nat.card H = Nat.card (P ⧸ M) := by
      rw [hH_top]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [hH_card] at hcard_eq
    omega
  have hH_ne_bot : H ≠ ⊥ := by
    intro hH_bot
    have : Nat.card H = 1 := Subgroup.card_eq_one.mpr hH_bot
    rw [hH_card] at this
    exact hp.out.one_lt.ne this.symm
  -- Pull back H to subgroup of P
  let H' : Subgroup P := H.comap (QuotientGroup.mk' M)
  -- M ≤ H'
  have h_M_le_H' : M ≤ H' := by
    intro x hx
    show (QuotientGroup.mk' M) x ∈ H
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem H
  -- H' < ⊤ (else H = ⊤ via mk' surjective)
  have h_H'_lt_top : H' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h_H'_top
    apply hH_ne_top
    rw [Subgroup.eq_top_iff']
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hxH' : x ∈ H' := h_H'_top ▸ Subgroup.mem_top x
    exact hxH'
  -- M < H' (else H = ⊥)
  have h_M_lt_H' : M < H' := by
    rw [lt_iff_le_and_ne]
    refine ⟨h_M_le_H', ?_⟩
    intro h_eq
    apply hH_ne_bot
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx_H
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hy_H' : y ∈ H' := hx_H
    rw [← h_eq] at hy_H'
    exact (QuotientGroup.eq_one_iff y).mpr hy_H'
  -- hMax.2 gives H' = ⊤, contradicting H' < ⊤
  exact h_H'_lt_top.ne (hMax.2 H' h_M_lt_H')

/-- For finite `p`-group `P` and maximal `M`, `commutator P ≤ M` (`P/M` is order `p`, abelian). -/
private lemma commutator_le_of_isCoatom_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P) {M : Subgroup P} (hMax : IsCoatom M) :
    _root_.commutator P ≤ M := by
  haveI : Group.IsNilpotent P := hP.isNilpotent
  have hMnormal : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M
      (normalizerCondition_of_isNilpotent (G := P)) hMax
  haveI := hMnormal
  have h_idx : M.index = p := index_eq_prime_of_isCoatom_of_pgroup hP hMax
  have h_card_quot : Nat.card (P ⧸ M) = p := by
    rw [← Subgroup.index_eq_card]; exact h_idx
  haveI : Fact (Nat.card (P ⧸ M)).Prime := ⟨h_card_quot ▸ hp.out⟩
  haveI : IsCyclic (P ⧸ M) := isCyclic_of_prime_card h_card_quot
  -- commutator P ≤ M iff P/M abelian
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  letI := IsCyclic.commGroup (α := P ⧸ M)
  exact ⟨⟨mul_comm⟩⟩

/-- For finite `p`-group `P` and maximal `M`, `x^p ∈ M` for all `x : P`. -/
private lemma pow_p_mem_of_isCoatom_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P) {M : Subgroup P} (hMax : IsCoatom M) (x : P) :
    x^p ∈ M := by
  haveI : Group.IsNilpotent P := hP.isNilpotent
  have hMnormal : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M
      (normalizerCondition_of_isNilpotent (G := P)) hMax
  haveI := hMnormal
  have h_idx : M.index = p := index_eq_prime_of_isCoatom_of_pgroup hP hMax
  have h_card_quot : Nat.card (P ⧸ M) = p := by
    rw [← Subgroup.index_eq_card]; exact h_idx
  -- In P/M of order p, q^p = 1 for any q. So x^p ∈ M.
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  rw [← h_card_quot]
  exact pow_card_eq_one'

/-- **For finite `p`-group `P`, `commutator P ≤ frattini P`**. -/
theorem commutator_le_frattini_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) :
    _root_.commutator P ≤ frattini P := by
  refine le_iInf fun M => ?_
  refine le_iInf fun hM => ?_
  exact commutator_le_of_isCoatom_of_pgroup hP hM

/-- **For finite `p`-group `P`, `x^p ∈ frattini P` for all `x : P`**. -/
theorem pow_p_mem_frattini_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (x : P) :
    x^p ∈ frattini P := by
  refine Subgroup.mem_iInf.mpr fun M => Subgroup.mem_iInf.mpr fun hM => ?_
  exact pow_p_mem_of_isCoatom_of_pgroup hP hM x

/-- **Isaacs Lemma 4.5 backward**: For finite `p`-group `P` and `N ⊴ P`,
`Φ(P) ⊆ N` ⇒ `P/N` is `p`-elementary abelian.

**証明**: `commutator P ≤ Φ(P) ⊆ N` ⇒ `P/N` abelian.
`∀ x, x^p ∈ Φ(P) ⊆ N` ⇒ `∀ q : P/N, q^p = 1`. -/
theorem isElementaryAbelian_quotient_of_frattini_le_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    {N : Subgroup P} [N.Normal] (hΦ : frattini P ≤ N) :
    OddOrder.GroupTheory.IsElementaryAbelian p (P ⧸ N) := by
  refine ⟨?_, ?_⟩
  · -- P/N abelian
    have h_comm_le : _root_.commutator P ≤ N :=
      le_trans (commutator_le_frattini_of_pgroup hP) hΦ
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr h_comm_le).is_comm.comm
  · -- ∀ q : P/N, q^p = 1
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hΦ (pow_p_mem_frattini_of_pgroup hP x)

/-- **Helper**: For any group `G` and subgroup `M ≤ G` with prime index, `M` is a coatom
(maximal proper subgroup) in the subgroup lattice.

**証明**: M.index = p ≥ 2 ⇒ M ≠ ⊤. For M < K, by `relIndex_mul_index`,
`M.relIndex K * K.index = M.index = p`, so K.index = 1 or p. If K.index = p, then
`M.relIndex K = 1` so K = M, contradicting M < K. Hence K.index = 1, K = ⊤. -/
private lemma isCoatom_of_index_prime {G : Type*} [Group G] {M : Subgroup G}
    {p : ℕ} (hp : p.Prime) (h_idx : M.index = p) : IsCoatom M := by
  refine ⟨?_, ?_⟩
  · -- M ≠ ⊤
    intro h_top
    rw [h_top, Subgroup.index_top] at h_idx
    exact hp.one_lt.ne' h_idx.symm
  · -- ∀ K, M < K → K = ⊤
    intro K hMK
    by_contra h_K_ne_top
    -- M ≤ K, use relIndex_mul_index
    have hMK_le : M ≤ K := hMK.le
    have h_eq : M.relIndex K * K.index = M.index :=
      Subgroup.relIndex_mul_index hMK_le
    rw [h_idx] at h_eq
    -- K.index ∣ p, so K.index = 1 or p
    have h_dvd : K.index ∣ p := by
      refine ⟨M.relIndex K, ?_⟩
      linarith [h_eq, Nat.mul_comm K.index (M.relIndex K)]
    rcases hp.eq_one_or_self_of_dvd _ h_dvd with h1 | hp_eq
    · -- K.index = 1 ⇒ K = ⊤
      have hK_top : K = ⊤ := Subgroup.index_eq_one.mp h1
      exact h_K_ne_top hK_top
    · -- K.index = p ⇒ M.relIndex K = 1 ⇒ M = K, contradicting M < K
      rw [hp_eq] at h_eq
      have h_rel_one : M.relIndex K = 1 := by
        have hp_pos : 0 < p := hp.pos
        have : M.relIndex K * p = 1 * p := by rw [h_eq, one_mul]
        exact Nat.eq_of_mul_eq_mul_right hp_pos this
      have hM_eq_K : M = K := by
        -- M.relIndex K = 1 ⇒ M.subgroupOf K = ⊤
        have := Subgroup.relIndex_eq_one.mp h_rel_one
        -- this : K ≤ M (since M.subgroupOf K = ⊤ means everything in K is in M)
        exact le_antisymm hMK_le this
      exact absurd hM_eq_K (ne_of_lt hMK)

-- rc2: scoped `IsMulCommutative → CommGroup` (consistent with the ambient `Group`,
-- unlike an explicit `{ … with mul_comm }` which makes a diamond).
open scoped IsMulCommutative in
/-- **Isaacs Lemma 4.5 forward**: For finite `p`-group `P` and `N ⊴ P`,
`P/N` is `p`-elementary abelian ⇒ `Φ(P) ⊆ N`.

**証明**: For each `x ∈ Φ(P)`, suppose `x ∉ N`. Construct a maximal `M ≤ P` with
`N ≤ M` and `x ∉ M`, contradicting `Φ(P) ⊆ M`.

`P/N` elementary abelian ⇒ `(P/N)` is a `ZMod p`-vector space (`AddCommGroup.zmodModule`
on `Additive (P/N)`). For `xa := xN ≠ 1`, `Projective.exists_dual_ne_zero` gives
a linear functional `f : (Additive (P/N)) →ₗ[ZMod p] ZMod p` with `f xa ≠ 0`.
Convert to `φ : (P/N) →* Multiplicative (ZMod p)` via `AddMonoidHom.toMultiplicativeRight`.
`φ.ker.comap (mk' N) : Subgroup P` is the desired maximal subgroup (index `p`,
`x ∉ M`, `N ≤ M`). -/
theorem frattini_le_of_isElementaryAbelian_quotient_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime] (_hP : IsPGroup p P)
    {N : Subgroup P} [N.Normal]
    (hN : OddOrder.GroupTheory.IsElementaryAbelian p (P ⧸ N)) :
    frattini P ≤ N := by
  intro x hx_frat
  by_contra hx_notN
  -- Set up: P/N as CommGroup (via IsMulCommutative instance → CommGroup.ofIsMulCommutative)
  haveI hPN_comm : IsMulCommutative (P ⧸ N) := ⟨⟨hN.comm⟩⟩
  -- Set up: Additive (P/N) as ZMod p-module (vector space over the field ZMod p)
  have hp_smul : ∀ a : Additive (P ⧸ N), (p : ℕ) • a = 0 := fun a => by
    apply Additive.toMul.injective
    show (p • a).toMul = (0 : Additive _).toMul
    rw [toMul_nsmul, toMul_zero]
    exact hN.pow_eq_one _
  haveI hMod : Module (ZMod p) (Additive (P ⧸ N)) := AddCommGroup.zmodModule hp_smul
  haveI hFree : Module.Free (ZMod p) (Additive (P ⧸ N)) :=
    @Module.Free.of_divisionRing (ZMod p) (Additive (P ⧸ N)) _ _ inferInstance
  haveI hProj : Module.Projective (ZMod p) (Additive (P ⧸ N)) := Module.Projective.of_free
  -- xa : Additive (P/N) is nonzero (corresponds to x ∉ N)
  set xa : Additive (P ⧸ N) := Additive.ofMul ((x : P ⧸ N)) with hxa_def
  have hxa_ne_zero : xa ≠ 0 := by
    intro h_eq
    apply hx_notN
    have h_mul_one : (x : P ⧸ N) = 1 := by
      have := congr_arg Additive.toMul h_eq
      rwa [toMul_ofMul, toMul_zero] at this
    exact (QuotientGroup.eq_one_iff x).mp h_mul_one
  -- Find linear functional f with f xa ≠ 0
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod p) hxa_ne_zero
  -- Convert to MonoidHom φ : (P/N) →* Multiplicative (ZMod p)
  let φ : (P ⧸ N) →* Multiplicative (ZMod p) :=
    AddMonoidHom.toMultiplicativeRight f.toAddMonoidHom
  -- Define M_quot := ker φ : Subgroup (P/N), and M := M_quot.comap (mk' N) : Subgroup P
  let M_quot : Subgroup (P ⧸ N) := φ.ker
  let M : Subgroup P := M_quot.comap (QuotientGroup.mk' N)
  -- N ≤ M: y ∈ N ⇒ mk' N y = 1 ⇒ φ 1 = 1
  have hN_le_M : N ≤ M := by
    intro y hy
    show QuotientGroup.mk' N y ∈ M_quot
    show φ (QuotientGroup.mk' N y) = 1
    have h_eq_one : QuotientGroup.mk' N y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    rw [h_eq_one, map_one]
  -- x ∉ M: φ (xN) = ofAdd (f xa), and f xa ≠ 0 ⇒ ofAdd ... ≠ 1
  have hx_notM : x ∉ M := by
    intro hx_M
    apply hf
    -- hx_M : x ∈ M = M_quot.comap (mk' N), so mk' N x ∈ M_quot = φ.ker
    -- i.e., φ (xN) = 1, i.e., ofAdd (f xa) = 1, i.e., f xa = 0
    have hx_in : φ ((x : P ⧸ N)) = 1 := hx_M
    -- φ ↑x = ofAdd (f xa) by def
    change Multiplicative.ofAdd (f xa) = 1 at hx_in
    rwa [show (1 : Multiplicative (ZMod p)) = Multiplicative.ofAdd 0 from rfl,
         Multiplicative.ofAdd.injective.eq_iff] at hx_in
  -- φ.range = ⊤ (since f ≠ 0 ⇒ range f = ⊤ in ZMod p, simple module)
  have hf_range_top : LinearMap.range f = ⊤ := by
    have h_ne_bot : LinearMap.range f ≠ ⊥ := fun h_bot => hf <| by
      have h_in : f xa ∈ LinearMap.range f := ⟨xa, rfl⟩
      rw [h_bot] at h_in
      exact (Submodule.mem_bot _).mp h_in
    rcases eq_bot_or_eq_top (LinearMap.range f) with h | h
    · exact absurd h h_ne_bot
    · exact h
  have hφ_surj : Function.Surjective φ := by
    intro y
    -- y : Multiplicative (ZMod p), need x' : P/N with φ x' = y
    -- y.toAdd ∈ ZMod p = range f (= ⊤), so ∃ a : Additive (P/N), f a = y.toAdd
    have h_in_top : y.toAdd ∈ LinearMap.range f := hf_range_top.symm ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := h_in_top
    refine ⟨a.toMul, ?_⟩
    change Multiplicative.ofAdd (f (Additive.ofMul (a.toMul))) = y
    rw [ofMul_toMul, ha, ofAdd_toAdd]
  -- M_quot.index = Nat.card (P/N) / Nat.card range = Nat.card Multiplicative (ZMod p) = p
  -- Use Subgroup.index_ker for surjective φ
  have h_M_quot_index : M_quot.index = p := by
    -- Use: φ surjective ⇒ (P/N) ⧸ φ.ker ≃* Multiplicative (ZMod p)
    -- Nat.card (Multiplicative (ZMod p)) = Nat.card (ZMod p) = p
    have h_quot_card : Nat.card ((P ⧸ N) ⧸ M_quot) = p := by
      have e : ((P ⧸ N) ⧸ φ.ker) ≃* Multiplicative (ZMod p) :=
        QuotientGroup.quotientKerEquivOfSurjective φ hφ_surj
      rw [Nat.card_congr e.toEquiv]
      exact Nat.card_zmod p
    rw [Subgroup.index, h_quot_card]
  -- M.index = p (via comap of surjective mk' N)
  have h_M_index : M.index = p := by
    rw [show M = M_quot.comap (QuotientGroup.mk' N) from rfl]
    rw [Subgroup.index_comap_of_surjective _ QuotientGroup.mk_surjective]
    exact h_M_quot_index
  -- M is a coatom (maximal proper subgroup)
  have h_M_coatom : IsCoatom M := isCoatom_of_index_prime hp.out h_M_index
  -- Φ(P) ⊆ M
  have hfrat_le_M : frattini P ≤ M := frattini_le_coatom h_M_coatom
  -- Contradiction: x ∈ Φ(P) ⊆ M but x ∉ M
  exact hx_notM (hfrat_le_M hx_frat)

/-- **Isaacs Lemma 4.5** (full equivalence): For finite `p`-group `P` and `N ⊴ P`,
`Φ(P) ⊆ N ↔ P/N is p-elementary abelian`. -/
theorem frattini_le_iff_isElementaryAbelian_quotient_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    {N : Subgroup P} [N.Normal] :
    frattini P ≤ N ↔ OddOrder.GroupTheory.IsElementaryAbelian p (P ⧸ N) :=
  ⟨isElementaryAbelian_quotient_of_frattini_le_of_pgroup hP,
   frattini_le_of_isElementaryAbelian_quotient_of_pgroup hP⟩

/-- **Isaacs Lemma 4.4 final conclusion** (`thus Φ(P) ⊆ Z(P)`):
For finite `p`-group `P` of class ≤ 2 with `commutator P` `p`-elementary abelian,
`Φ(P) ⊆ Z(P)`.

**証明**: `isElementaryAbelian_quotient_center_of_class_le_two` で `P/Z(P)` が
`p`-elementary abelian. 次に Lem 4.5 forward
(`frattini_le_of_isElementaryAbelian_quotient_of_pgroup`) で
`Φ(P) ⊆ Z(P)`. -/
theorem frattini_le_center_of_class_le_two_of_commutator_pow_eq_one
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    (hC : _root_.commutator P ≤ Subgroup.center P)
    (hExp : ∀ c ∈ _root_.commutator P, c ^ p = 1) :
    frattini P ≤ Subgroup.center P :=
  frattini_le_of_isElementaryAbelian_quotient_of_pgroup hP
    (isElementaryAbelian_quotient_center_of_class_le_two hC hExp)

/-- **Isaacs Lemma 4.6 easy direction**: `⁅A, ⊤⁆ ≤ G'` (任意 `A ≤ G` で常時成立).

`commutator_mono` で `A ≤ ⊤ ∧ ⊤ ≤ ⊤ ⇒ ⁅A, ⊤⁆ ≤ ⁅⊤, ⊤⁆ = commutator G`. -/
theorem commutator_top_subgroup_le_commutator (A : Subgroup G) :
    ⁅A, (⊤ : Subgroup G)⁆ ≤ _root_.commutator G := by
  rw [_root_.commutator_def]
  exact Subgroup.commutator_mono le_top le_rfl

/-- **Isaacs Lemma 4.6** ⭐ (章内 5 引用 + Ch.5/7/10 で多用 — 章内ハブ):
`A ⊴ G` abelian + `G/A` cyclic ⇒ `G' = ⁅A, ⊤⁆` (commutator subgroup).

(本 statement は前半. 後半 `G' ≅ A / (A ∩ Z(G))` の同型は別途 statement 化予定.)

**証明** (Isaacs p.118): `commutative_of_cyclic_center_quotient` 経由.
- (≥) 部分 = `commutator_top_subgroup_le_commutator` (上記, 仮定不要).
- (≤) 部分: `Q := G/⁅A, ⊤⁆` が abelian を示す.
  - lift `f : Q →* G/A` (mk' A の lift, 可能なのは `⁅A, ⊤⁆ ≤ A` (Lem 4.3 + A 正規)).
  - `f.ker = image(A) in Q ≤ center(Q)` (`⁅a, g⁆ ∈ ⁅A, ⊤⁆` で Q では `ag = ga`).
  - codomain `G/A` cyclic (hypothesis).
  - `commutative_of_cyclic_center_quotient` ⇒ Q commutative ⇒ commutator G ≤ ⁅A, ⊤⁆. -/
theorem commutator_eq_commutator_of_normal_abelian_cyclic_quotient
    {A : Subgroup G} [A.Normal] [Finite G]
    (_hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hCyclic : IsCyclic (G ⧸ A)) :
    _root_.commutator G = ⁅A, (⊤ : Subgroup G)⁆ := by
  refine le_antisymm ?_ (commutator_top_subgroup_le_commutator A)
  -- (≤) direction: G/⁅A,⊤⁆ が abelian であることを示し commutator G ⊆ ⁅A,⊤⁆ を導出.
  set H : Subgroup G := ⁅A, (⊤ : Subgroup G)⁆ with hHeq
  -- Step 1: H ≤ A.
  have hHleA : H ≤ A := by
    show ⁅A, (⊤ : Subgroup G)⁆ ≤ A
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_top_left_le_iff (H := A)).mpr ‹A.Normal›
  -- Step 2: lift f : G/H →* G/A.
  let f : G ⧸ H →* G ⧸ A :=
    QuotientGroup.lift H (QuotientGroup.mk' A) (fun x hx => by
      simp only [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hHleA hx)
  -- Step 3: f.ker ≤ center(G/H).
  have hker_central : f.ker ≤ Subgroup.center (G ⧸ H) := by
    intro q hq
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    -- hq : f ↑y = 1. f ↑y = (mk' A) y by lift_mk'.
    have hyA : y ∈ A := by
      have hfy : f ((y : G) : G ⧸ H) = ((y : G) : G ⧸ A) := by
        change QuotientGroup.lift H (QuotientGroup.mk' A) _ ((y : G) : G ⧸ H) = _
        exact QuotientGroup.lift_mk' _ _ y
      rw [MonoidHom.mem_ker, hfy, QuotientGroup.eq_one_iff] at hq
      exact hq
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    -- Goal: (g : G ⧸ H) * (y : G ⧸ H) = (y : G ⧸ H) * (g : G ⧸ H).
    show ((g : G) : G ⧸ H) * ((y : G) : G ⧸ H) = ((y : G) : G ⧸ H) * ((g : G) : G ⧸ H)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rw [QuotientGroup.eq_iff_div_mem]
    -- (g * y) / (y * g) ∈ H. Compute (g*y)*(y*g)⁻¹ = g*y*g⁻¹*y⁻¹ = ⁅g, y⁆ = ⁅y, g⁆⁻¹.
    have heq : g * y / (y * g) = ⁅g, y⁆ := by
      simp only [div_eq_mul_inv, commutatorElement_def]; group
    rw [heq]
    -- ⁅g, y⁆ ∈ ⁅⊤, A⁆ = ⁅A, ⊤⁆ = H.
    rw [hHeq, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hyA
  -- Step 4: G/H is abelian.
  have habelian : ∀ a b : G ⧸ H, a * b = b * a :=
    commutative_of_cyclic_center_quotient f hker_central
  -- Step 5: commutator G ⊆ H.
  rw [_root_.commutator_def, Subgroup.commutator_def, Subgroup.closure_le]
  rintro _ ⟨a, _, b, _, rfl⟩
  show ⁅a, b⁆ ∈ H
  rw [← QuotientGroup.eq_one_iff (N := H)]
  show ((⁅a, b⁆ : G) : G ⧸ H) = 1
  rw [show ((⁅a, b⁆ : G) : G ⧸ H) = ⁅(a : G ⧸ H), (b : G ⧸ H)⁆ by
    simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv]]
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact habelian _ _

/-! ### Lemma 4.6 後半: hom A → commutator G + ker = A ∩ Z(G) -/

/-- Helper: For `A ⊴ G` and `b ∈ A`, `⁅b, g⁆ ∈ A` for any `g : G`.

`⁅b, g⁆ = b · (g · b⁻¹ · g⁻¹)`. `b⁻¹ ∈ A` + A normal ⇒ `g · b⁻¹ · g⁻¹ ∈ A`. -/
private lemma commutatorElement_mem_of_normal {A : Subgroup G} [A.Normal]
    {b : G} (hb : b ∈ A) (g : G) : ⁅b, g⁆ ∈ A := by
  have heq : ⁅b, g⁆ = b * (g * b⁻¹ * g⁻¹) := by
    rw [commutatorElement_def]; group
  rw [heq]
  exact A.mul_mem hb (‹A.Normal›.conj_mem _ (A.inv_mem hb) g)

/-- **Lemma 4.6 hom** (右 commutator hom): For `A ⊴ G` abelian and any `g : G`,
the map `θ : A → G` by `θ a = ⁅a, g⁆` is a monoid homomorphism.

`map_mul`: general identity `⁅ab, g⁆ = a · ⁅b, g⁆ · a⁻¹ · ⁅a, g⁆`. `⁅b, g⁆ ∈ A`
(A normal) + A abelian ⇒ `a · ⁅b, g⁆ · a⁻¹ = ⁅b, g⁆`. Result `⁅b, g⁆ · ⁅a, g⁆`
を A 内 swap で `⁅a, g⁆ · ⁅b, g⁆`. -/
def commutatorRightHom {A : Subgroup G} [A.Normal]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (g : G) : A →* G where
  toFun a := ⁅(a : G), g⁆
  map_one' := by
    show ⁅((1 : A) : G), g⁆ = 1
    rw [Subgroup.coe_one]
    exact commutatorElement_one_left g
  map_mul' a b := by
    show ⁅((a * b : A) : G), g⁆ = ⁅((a : A) : G), g⁆ * ⁅((b : A) : G), g⁆
    rw [Subgroup.coe_mul, commutatorElement_mul_left_eq]
    have hbg : ⁅(b : G), g⁆ ∈ A := commutatorElement_mem_of_normal b.2 g
    have hag : ⁅(a : G), g⁆ ∈ A := commutatorElement_mem_of_normal a.2 g
    have h1 : (a : G) * ⁅(b : G), g⁆ * (a : G)⁻¹ = ⁅(b : G), g⁆ := by
      rw [hAb _ a.2 _ hbg, mul_assoc, mul_inv_cancel, mul_one]
    rw [h1]
    exact hAb _ hbg _ hag

/-- The range of `commutatorRightHom hAb g` is contained in `commutator G`. -/
theorem commutatorRightHom_range_le_commutator {A : Subgroup G} [A.Normal]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (g : G) :
    (commutatorRightHom hAb g).range ≤ _root_.commutator G := by
  rintro x ⟨a, rfl⟩
  show ⁅((a : A) : G), g⁆ ∈ _root_.commutator G
  exact commutatorElement_mem_commutator_top _ _

/-- For `g : G` such that `g · A` generates `G ⧸ A`, `A ⊔ ⟨g⟩ = ⊤`. -/
private lemma sup_zpowers_eq_top_of_generator_quot
    {A : Subgroup G} [A.Normal] {g : G}
    (hgen : ∀ x : G ⧸ A, x ∈ Subgroup.zpowers ((g : G ⧸ A))) :
    A ⊔ Subgroup.zpowers g = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨k, hk⟩ := hgen (x : G ⧸ A)
  -- hk : (↑g : G ⧸ A)^k = (↑x : G ⧸ A)
  -- So (↑(g^k) : G ⧸ A) = (↑x : G ⧸ A), i.e., x * (g^k)⁻¹ ∈ A.
  have hk' : ((g^k : G) : G ⧸ A) = ((x : G) : G ⧸ A) := by
    rw [← hk]
    exact (map_zpow (QuotientGroup.mk' A) g k).symm
  -- From hk': (g^k : G ⧸ A) = (x : G ⧸ A), so g^k / x ∈ A by QuotientGroup.eq_iff_div_mem
  have h_div : g^k / x ∈ A := (QuotientGroup.eq_iff_div_mem (N := A)).mp hk'
  -- Hence x * (g^k)⁻¹ = (g^k / x)⁻¹ ∈ A
  have hxgk : x * (g^k)⁻¹ ∈ A := by
    have heq : x * (g^k)⁻¹ = (g^k / x)⁻¹ := by rw [div_eq_mul_inv]; group
    rw [heq]
    exact A.inv_mem h_div
  -- x = (x * (g^k)⁻¹) * g^k ∈ A · ⟨g⟩
  have hx_eq : x = (x * (g^k)⁻¹) * g^k := by group
  rw [hx_eq]
  exact Subgroup.mul_mem_sup hxgk (Subgroup.zpow_mem_zpowers g k)

/-- For `g : G` such that `g · A` generates `G ⧸ A`, and `A` is abelian normal:
`a ∈ A` is in the kernel of `commutatorRightHom hAb g` iff `(a : G) ∈ Z(G)`. -/
theorem commutatorRightHom_mem_ker_iff {A : Subgroup G} [A.Normal]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {g : G} (hgen : ∀ x : G ⧸ A, x ∈ Subgroup.zpowers ((g : G ⧸ A))) (a : A) :
    a ∈ (commutatorRightHom hAb g).ker ↔ (a : G) ∈ Subgroup.center G := by
  constructor
  · -- Forward: a ∈ ker (commutes with g) + A abelian ⇒ a commutes with A ⊔ ⟨g⟩ = G
    intro ha
    rw [MonoidHom.mem_ker] at ha
    -- ha : ⁅(a : G), g⁆ = 1, i.e., a · g = g · a
    have ha_g : (a : G) * g = g * (a : G) :=
      commutatorElement_eq_one_iff_mul_comm.mp ha
    rw [Subgroup.mem_center_iff]
    intro x
    -- S := { x : G | (a : G) · x = x · (a : G) } = centralizer {a}
    let S : Subgroup G := Subgroup.centralizer ({(a : G)} : Set G)
    -- A ≤ S (A abelian, a ∈ A)
    have hAS : A ≤ S := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      rintro z (rfl : z = (a : G))
      exact hAb _ a.2 _ hy
    -- g ∈ S
    have hgS : g ∈ S := by
      rw [Subgroup.mem_centralizer_iff]
      rintro z (rfl : z = (a : G))
      exact ha_g
    -- ⟨g⟩ ≤ S
    have hzpgS : Subgroup.zpowers g ≤ S := by
      rw [Subgroup.zpowers_eq_closure]
      exact Subgroup.closure_le _ |>.mpr (by rintro _ (rfl : _ = g); exact hgS)
    -- A ⊔ ⟨g⟩ ≤ S
    have hsupS : A ⊔ Subgroup.zpowers g ≤ S := sup_le hAS hzpgS
    -- ⊤ ≤ S
    have hsupTop : A ⊔ Subgroup.zpowers g = ⊤ := sup_zpowers_eq_top_of_generator_quot hgen
    have hTopS : (⊤ : Subgroup G) ≤ S := hsupTop ▸ hsupS
    -- x ∈ S
    have hxS : x ∈ S := hTopS (Subgroup.mem_top x)
    rw [Subgroup.mem_centralizer_iff] at hxS
    exact (hxS _ rfl).symm
  · intro ha
    rw [MonoidHom.mem_ker]
    show ⁅(a : G), g⁆ = 1
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp ha g).symm

/-- General identity (no hypothesis): `g · ⁅a, g⁆ · g⁻¹ = ⁅g · a · g⁻¹, g⁆`.
共役 conjugation を交換子内に push. -/
private lemma conj_commutatorElement_right (a g : G) :
    g * ⁅a, g⁆ * g⁻¹ = ⁅g * a * g⁻¹, g⁆ := by
  simp only [commutatorElement_def]; group

/-- General identity (no hypothesis): `g⁻¹ · ⁅a, g⁆ · g = ⁅g⁻¹ · a · g, g⁆`. -/
private lemma inv_conj_commutatorElement_right (a g : G) :
    g⁻¹ * ⁅a, g⁆ * g = ⁅g⁻¹ * a * g, g⁆ := by
  simp only [commutatorElement_def]; group

/-- The range of `commutatorRightHom hAb g` is normal in `G` when `g · A` generates
`G ⧸ A`. A 共役: A abelian + range ⊆ A ⇒ A fixes range pointwise. g 共役:
`g · ⁅a, g⁆ · g⁻¹ = ⁅g a g⁻¹, g⁆` ∈ range (A normal ⇒ `g a g⁻¹ ∈ A`). -/
theorem commutatorRightHom_range_normal {A : Subgroup G} [A.Normal]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {g : G} (hgen : ∀ x : G ⧸ A, x ∈ Subgroup.zpowers ((g : G ⧸ A))) :
    ((commutatorRightHom hAb g).range).Normal := by
  refine ⟨?_⟩
  intro y hy x
  -- Goal: x * y * x⁻¹ ∈ range
  -- Strategy: show normalizer(range) ⊇ A ⊔ ⟨g⟩ = ⊤
  let N : Subgroup G := Subgroup.normalizer (commutatorRightHom hAb g).range
  suffices hxN : x ∈ N by
    rw [Subgroup.mem_normalizer_iff] at hxN
    exact (hxN y).mp hy
  -- Helper: range ⊆ A
  have h_range_le_A : ∀ z, z ∈ (commutatorRightHom hAb g).range → z ∈ A := by
    intro z hz
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hz
    exact commutatorElement_mem_of_normal b.2 g
  -- A ≤ N: A abelian + range ⊆ A ⇒ A fixes range pointwise under conjugation
  have hAN : A ≤ N := by
    intro a' ha'
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hz_in_A : z ∈ A := h_range_le_A z hz
      have h_eq : a' * z * a'⁻¹ = z := by
        rw [hAb _ ha' _ hz_in_A, mul_assoc, mul_inv_cancel, mul_one]
      rw [h_eq]; exact hz
    · intro hz
      have hz_conj_in_A : a' * z * a'⁻¹ ∈ A := h_range_le_A _ hz
      -- z = a'⁻¹ * (a' * z * a'⁻¹) * a' ∈ A
      have hz_in_A : z ∈ A := by
        have heq : z = a'⁻¹ * (a' * z * a'⁻¹) * a' := by group
        rw [heq]
        exact A.mul_mem (A.mul_mem (A.inv_mem ha') hz_conj_in_A) ha'
      have h_eq : a' * z * a'⁻¹ = z := by
        rw [hAb _ ha' _ hz_in_A, mul_assoc, mul_inv_cancel, mul_one]
      rw [← h_eq]; exact hz
  -- g ∈ N: uses identity g · ⁅b, g⁆ · g⁻¹ = ⁅g · b · g⁻¹, g⁆ + A normal.
  have hgN : g ∈ N := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hz
      -- hb : (commutatorRightHom hAb g) b = z
      have hgbg : g * (b : G) * g⁻¹ ∈ A := ‹A.Normal›.conj_mem _ b.2 g
      refine MonoidHom.mem_range.mpr ⟨⟨g * (b : G) * g⁻¹, hgbg⟩, ?_⟩
      change ⁅g * (b : G) * g⁻¹, g⁆ = g * z * g⁻¹
      rw [show z = ⁅((b : A) : G), g⁆ from hb.symm]
      exact (conj_commutatorElement_right (b : G) g).symm
    · intro hz
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hz
      -- hb : (commutatorRightHom hAb g) b = g * z * g⁻¹, i.e., ⁅↑b, g⁆ = g * z * g⁻¹
      have hgbg : g⁻¹ * (b : G) * g ∈ A := by
        have := ‹A.Normal›.conj_mem _ b.2 g⁻¹
        simpa using this
      refine MonoidHom.mem_range.mpr ⟨⟨g⁻¹ * (b : G) * g, hgbg⟩, ?_⟩
      change ⁅g⁻¹ * (b : G) * g, g⁆ = z
      have hb' : ⁅((b : A) : G), g⁆ = g * z * g⁻¹ := hb
      have hz_eq : z = g⁻¹ * ⁅((b : A) : G), g⁆ * g := by
        rw [hb']; group
      rw [hz_eq]
      exact (inv_conj_commutatorElement_right (b : G) g).symm
  -- ⟨g⟩ ≤ N
  have h_zpgN : Subgroup.zpowers g ≤ N := by
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_le _ |>.mpr (by rintro _ (rfl : _ = g); exact hgN)
  -- A ⊔ ⟨g⟩ ≤ N
  have hsupN : A ⊔ Subgroup.zpowers g ≤ N := sup_le hAN h_zpgN
  -- ⊤ ≤ N
  have hsupTop : A ⊔ Subgroup.zpowers g = ⊤ := sup_zpowers_eq_top_of_generator_quot hgen
  exact (hsupTop ▸ hsupN) (Subgroup.mem_top x)

/-- **Isaacs Lemma 4.6 後半**: For `A ⊴ G` abelian and `G ⧸ A` cyclic generated by `g · A`,
`(commutatorRightHom hAb g).range = commutator G`.

**証明**: `≤` direction trivial (`commutatorRightHom_range_le_commutator`).
`≥`: `commutator G = ⁅A, ⊤⁆` (Lem 4.6 main) で `⁅A, ⊤⁆ ≤ range` を示す.
`Subgroup.commutator_le` ⇒ `∀ a ∈ A, ∀ y : G, ⁅a, y⁆ ∈ range`.
`y ∈ ⊤ = A ⊔ ⟨g⟩ = closure ((A : Set G) ∪ {g})` で closure induction:
* base `y ∈ A`: `⁅a, y⁆ = 1` (A abelian).
* base `y = g`: `⁅a, g⁆ = θ(a) ∈ range` (定義).
* `y = 1`: `⁅a, 1⁆ = 1`.
* `y = y₁·y₂`: identity `⁅a, y₁y₂⁆ = ⁅a, y₁⁆·(y₁·⁅a, y₂⁆·y₁⁻¹)` + range Normal.
* `y = y₀⁻¹`: identity `⁅a, y₀⁻¹⁆ = y₀⁻¹·⁅a, y₀⁆⁻¹·y₀` + range Normal + inv_mem. -/
theorem commutatorRightHom_range_eq_commutator {A : Subgroup G} [A.Normal] [Finite G]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {g : G} (hgen : ∀ x : G ⧸ A, x ∈ Subgroup.zpowers ((g : G ⧸ A))) :
    (commutatorRightHom hAb g).range = _root_.commutator G := by
  haveI := commutatorRightHom_range_normal hAb hgen
  haveI hCyc : IsCyclic (G ⧸ A) := ⟨⟨(g : G ⧸ A), hgen⟩⟩
  refine le_antisymm (commutatorRightHom_range_le_commutator hAb g) ?_
  -- commutator G = ⁅A, ⊤⁆ (Lem 4.6 main)
  rw [commutator_eq_commutator_of_normal_abelian_cyclic_quotient hAb hCyc]
  -- Goal: ⁅A, ⊤⁆ ≤ range
  rw [Subgroup.commutator_le]
  -- Sup と closure 等式
  have hsupTop : A ⊔ Subgroup.zpowers g = ⊤ := sup_zpowers_eq_top_of_generator_quot hgen
  have hcl_eq : Subgroup.closure ((A : Set G) ∪ {g}) = (⊤ : Subgroup G) := by
    rw [← hsupTop]
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      rintro x (hxA | hxg)
      · exact (le_sup_left : A ≤ A ⊔ Subgroup.zpowers g) hxA
      · rw [Set.mem_singleton_iff] at hxg
        rw [hxg]
        exact (le_sup_right : Subgroup.zpowers g ≤ A ⊔ _) (Subgroup.mem_zpowers g)
    · refine sup_le ?_ ?_
      · intro x hx; exact Subgroup.subset_closure (Or.inl hx)
      · rw [Subgroup.zpowers_eq_closure, Subgroup.closure_le]
        intro x hx
        exact Subgroup.subset_closure (Or.inr hx)
  -- メイン induction: ∀ y ∈ closure (↑A ∪ {g}), ⁅a, y⁆ ∈ range
  suffices h_main : ∀ a ∈ A, ∀ y ∈ Subgroup.closure ((A : Set G) ∪ {g}),
      ⁅(a : G), y⁆ ∈ (commutatorRightHom hAb g).range by
    intro a ha y _hy_top
    exact h_main a ha y (hcl_eq.symm ▸ Subgroup.mem_top y)
  intro a ha y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hxA | hxg
    · -- x ∈ A: ⁅a, x⁆ = 1 (A abelian)
      have heq : ⁅(a : G), x⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact hAb _ ha _ hxA
      rw [heq]; exact Subgroup.one_mem _
    · -- x = g
      rw [Set.mem_singleton_iff] at hxg; subst hxg
      exact MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
  | one =>
    rw [commutatorElement_one_right]; exact Subgroup.one_mem _
  | mul y₁ y₂ _ _ hy₁ hy₂ =>
    -- ⁅a, y₁·y₂⁆ = ⁅a, y₁⁆ · (y₁·⁅a, y₂⁆·y₁⁻¹)
    have hid : ⁅(a : G), y₁ * y₂⁆ = ⁅(a : G), y₁⁆ * (y₁ * ⁅(a : G), y₂⁆ * y₁⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [hid]
    refine Subgroup.mul_mem _ hy₁ ?_
    exact ‹((commutatorRightHom hAb g).range).Normal›.conj_mem _ hy₂ y₁
  | inv y₀ _ hy₀ =>
    -- ⁅a, y₀⁻¹⁆ = y₀⁻¹ · ⁅a, y₀⁆⁻¹ · y₀
    have hid : ⁅(a : G), y₀⁻¹⁆ = y₀⁻¹ * ⁅(a : G), y₀⁆⁻¹ * y₀ := by
      simp only [commutatorElement_def]; group
    rw [hid]
    have h_inv : ⁅(a : G), y₀⁆⁻¹ ∈ (commutatorRightHom hAb g).range :=
      Subgroup.inv_mem _ hy₀
    have h_conj := ‹((commutatorRightHom hAb g).range).Normal›.conj_mem _ h_inv y₀⁻¹
    simpa using h_conj

/-- **Lem 4.6 後半 kernel as subgroup**: ker of `commutatorRightHom hAb g` (as a subgroup
of `A`) equals `(A ⊓ Subgroup.center G).subgroupOf A`. -/
theorem commutatorRightHom_ker_eq {A : Subgroup G} [A.Normal]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {g : G} (hgen : ∀ x : G ⧸ A, x ∈ Subgroup.zpowers ((g : G ⧸ A))) :
    (commutatorRightHom hAb g).ker = (A ⊓ Subgroup.center G).subgroupOf A := by
  ext a
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro ha
    exact ⟨a.2, (commutatorRightHom_mem_ker_iff hAb hgen a).mp ha⟩
  · intro ha
    exact (commutatorRightHom_mem_ker_iff hAb hgen a).mpr ha.2

/-- **Lem 4.6 cardinality form**: For `A ⊴ G` abelian + `G ⧸ A` cyclic + `G` finite,
`|commutator G| · |A ⊓ Z(G)| = |A|`. First iso theorem経由. -/
theorem card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient
    {A : Subgroup G} [A.Normal] [Finite G]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hCyc : IsCyclic (G ⧸ A)) :
    Nat.card (_root_.commutator G) * Nat.card (A ⊓ Subgroup.center G : Subgroup G)
      = Nat.card A := by
  obtain ⟨γ, hγ⟩ := hCyc.exists_generator
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  -- Apply Lagrange to θ := commutatorRightHom hAb g
  have h_ker := commutatorRightHom_ker_eq hAb hγ
  have h_range := commutatorRightHom_range_eq_commutator hAb hγ
  have h_lag : Nat.card (commutatorRightHom hAb g).ker *
      (commutatorRightHom hAb g).ker.index = Nat.card A :=
    Subgroup.card_mul_index _
  rw [Subgroup.index_ker, h_range, h_ker] at h_lag
  -- Convert Nat.card ((A ⊓ Z(G)).subgroupOf A) = Nat.card (A ⊓ Z(G))
  have h_card_eq : Nat.card ((A ⊓ Subgroup.center G).subgroupOf A) =
      Nat.card (A ⊓ Subgroup.center G : Subgroup G) := by
    refine Nat.card_congr ?_
    refine {
      toFun := fun x => ⟨((x : A) : G), (Subgroup.mem_subgroupOf.mp x.2)⟩
      invFun := fun y => ⟨⟨(y : G), y.2.1⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_
    }
    · -- ⟨y, y.2.1⟩ ∈ (A ⊓ Z(G)).subgroupOf A
      rw [Subgroup.mem_subgroupOf]
      exact y.2
    · intro x; rfl
    · intro y; rfl
  rw [h_card_eq] at h_lag
  rw [mul_comm]
  exact h_lag

/-! ### Thm 4.7: maximal class p-群 (helpers + base case m = 1) -/

/-- Helper: For surjective hom `f : G →* H`, `(lcs G n).map f = lcs H n`. -/
theorem lowerCentralSeries_map_eq_of_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (n : ℕ) :
    Subgroup.map f (lowerCentralSeries G n) = lowerCentralSeries H n := by
  induction n with
  | zero =>
    show Subgroup.map f (⊤ : Subgroup G) = ⊤
    exact Subgroup.map_top_of_surjective f hf
  | succ n ih =>
    show Subgroup.map f ⁅lowerCentralSeries G n, (⊤ : Subgroup G)⁆
        = ⁅lowerCentralSeries H n, (⊤ : Subgroup H)⁆
    rw [Subgroup.map_commutator, ih, Subgroup.map_top_of_surjective f hf]

/-- **Thm 4.7, m = 1 case**: `A ⊴ P` abelian, `P` p-群, `|A| = p`, `P/A` cyclic,
`|A ⊓ Z(P)| = p` ⇒ `Group.nilpotencyClass P = 1` (i.e., P abelian, nontrivial).

`|A| = |A ⊓ Z(P)| = p` ⇒ `A ⊆ Z(P)` (両者 ⊆ A で等カード ⇒ 等). P/A cyclic +
`A ⊆ Z(P)` ⇒ P abelian (`commutative_of_cyclic_center_quotient`). -/
theorem nilpotencyClass_eq_one_of_normal_abelian_cyclic_quotient_inf_center_prime_card_p
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime] (hP : IsPGroup p P)
    {A : Subgroup P} [A.Normal]
    (_hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hCyc : IsCyclic (P ⧸ A))
    (hAcard : Nat.card A = p)
    (hAZcard : Nat.card (A ⊓ Subgroup.center P : Subgroup P) = p) :
    Group.nilpotencyClass P = 1 := by
  haveI : Group.IsNilpotent P := hP.isNilpotent
  -- A ⊓ Z(P) ⊆ A, 等カード ⇒ A ⊓ Z(P) = A ⇒ A ⊆ Z(P)
  have hAZ_eq_A : A ⊓ Subgroup.center P = A :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hAcard, hAZcard])
  have hA_le_Z : A ≤ Subgroup.center P := by
    rw [← hAZ_eq_A]; exact inf_le_right
  -- P abelian: G/A cyclic + A ⊆ Z(G)
  have hP_abelian : ∀ x y : P, x * y = y * x := by
    have hker_le : (QuotientGroup.mk' A).ker ≤ Subgroup.center P := by
      rw [QuotientGroup.ker_mk']; exact hA_le_Z
    exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' A) hker_le
  -- commutator P = ⊥ via center P = ⊤
  have hcomm_bot : _root_.commutator P = ⊥ := by
    rw [commutator_eq_bot_iff_center_eq_top, Subgroup.eq_top_iff']
    intro x
    rw [Subgroup.mem_center_iff]
    intro y
    exact hP_abelian y x
  -- nilpotencyClass ≤ 1
  have h_class_le : Group.nilpotencyClass P ≤ 1 := by
    rw [← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le, lowerCentralSeries_one]
    exact hcomm_bot
  -- P nontrivial (|A| = p ≥ 2)
  have hA_ne_bot : A ≠ ⊥ := by
    intro hA_bot
    rw [hA_bot, Subgroup.card_bot] at hAcard
    have := hp.out.one_lt
    omega
  have hP_nontrivial : Nontrivial P := by
    obtain ⟨x, hx_in_A, hx_ne⟩ : ∃ x : P, x ∈ A ∧ x ≠ 1 := by
      by_contra h
      push Not at h
      apply hA_ne_bot
      rw [Subgroup.eq_bot_iff_forall]
      exact h
    exact ⟨x, 1, hx_ne⟩
  -- nilpotencyClass ≠ 0
  have h_class_ne_zero : Group.nilpotencyClass P ≠ 0 := by
    intro h
    rw [nilpotencyClass_zero_iff_subsingleton] at h
    exact not_subsingleton P h
  omega

/-- Helper: for `f : G →* G' = G/N` (`N` normal) surjective and `H ≤ G`,
`|H.map (mk' N)| · |H ⊓ N| = |H|`. First iso on `(mk' N).comp H.subtype` + Lagrange in `H`. -/
private lemma card_map_mk_mul_card_inf_eq_card {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] (H : Subgroup G) :
    Nat.card (H.map (QuotientGroup.mk' N)) * Nat.card (H ⊓ N : Subgroup G) = Nat.card H := by
  let f : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hker : f.ker = (H ⊓ N).subgroupOf H := by
    ext ⟨x, hx⟩
    simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf]
    exact ⟨fun hxN => ⟨hx, hxN⟩, fun h => h.2⟩
  have hrange : f.range = H.map (QuotientGroup.mk' N) := by
    ext y
    simp only [MonoidHom.mem_range, Subgroup.mem_map, f, MonoidHom.comp_apply,
      Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    exact ⟨fun ⟨⟨x, hx⟩, h⟩ => ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, h⟩⟩
  have hSO : Nat.card ((H ⊓ N).subgroupOf H : Subgroup H) = Nat.card (H ⊓ N : Subgroup G) :=
    Nat.card_congr
      ⟨fun x => ⟨((x : H) : G), Subgroup.mem_subgroupOf.mp x.2⟩,
        fun y => ⟨⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩, Subgroup.mem_subgroupOf.mpr y.2⟩,
        fun _ => rfl, fun _ => rfl⟩
  have hLagr : Nat.card (H ⧸ f.ker) * Nat.card f.ker = Nat.card H :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker).symm
  have hQ : Nat.card (H ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [hker, hSO] at hLagr
  rw [hker, hrange] at hQ
  rw [← hQ]; exact hLagr

/-- **Isaacs Thm 4.7** ⭐: Let `A ⊴ P` abelian, `P` a p-group, `|A| = p ^ m`, `P/A` cyclic,
`|A ⊓ Z(P)| = p`. Then `Group.nilpotencyClass P = m`.

**Proof** (Isaacs p.118-119): Induction on `m`.
- `m = 0` is impossible: `|A| = 1` but `|A ⊓ Z(P)| = p ≥ 2`, contradicting `A ⊓ Z(P) ≤ A`.
- `m = 1`: `nilpotencyClass_eq_one_of_normal_abelian_cyclic_quotient_inf_center_prime_card_p`
  (`|A| = |A ⊓ Z(P)| = p` ⇒ `A ⊆ Z(P)` ⇒ `P` abelian).
- `m ≥ 2`: Let `Z = A ⊓ Z(P)`. By Lem 4.6 cardinality, `|commutator P| = p^(m-1)`.
  Since `m-1 ≥ 1`, `commutator P` is nontrivial; by Thm 1.19,
  `commutator P ⊓ Z(P) > ⊥`. Combined with `commutator P ⊓ Z(P) ⊆ A ⊓ Z(P) = Z`
  and `|Z| = p` prime, get `commutator P ⊓ Z(P) = Z`, so `Z ⊆ commutator P`.
  Apply IH to `P̄ = P/Z` and `Ā = A.map mk'`: class `P̄ = m-1`. Lift back via
  `lowerCentralSeries_map_eq_of_surjective`. -/
theorem nilpotencyClass_eq_of_normal_abelian_cyclic_quotient_inf_center_prime_card_p_pow
    (m : ℕ) {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P) {A : Subgroup P} [A.Normal]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hCyc : IsCyclic (P ⧸ A))
    (hAcard : Nat.card A = p ^ m)
    (hAZcard : Nat.card (A ⊓ Subgroup.center P : Subgroup P) = p) :
    Group.nilpotencyClass P = m := by
  induction m generalizing P with
  | zero =>
    -- |A| = 1 but |A ⊓ Z(P)| = p ≥ 2, contradicting A ⊓ Z(P) ≤ A
    exfalso
    rw [pow_zero] at hAcard
    have hle : (A ⊓ Subgroup.center P : Subgroup P) ≤ A := inf_le_left
    have hcard_le := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
    rw [hAcard, hAZcard] at hcard_le
    have := hp.out.one_lt
    omega
  | succ k ih =>
    haveI : Group.IsNilpotent P := hP.isNilpotent
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · -- k = 0, i.e., m = 1: use existing base case
      have hAcard' : Nat.card A = p := by rw [hAcard]; ring
      exact nilpotencyClass_eq_one_of_normal_abelian_cyclic_quotient_inf_center_prime_card_p
        hP hAb hCyc hAcard' hAZcard
    -- k ≥ 1, i.e., m = k+1 ≥ 2
    have hp_prime : p.Prime := hp.out
    have hp_pos : 0 < p := hp_prime.pos
    have hp1 : 1 < p := hp_prime.one_lt
    -- Step 1: commutator P ≤ A (P/A cyclic ⇒ abelian)
    have hG'_le_A : _root_.commutator P ≤ A := by
      letI : CommGroup (P ⧸ A) := IsCyclic.commGroup
      exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp ⟨⟨mul_comm⟩⟩
    -- Step 2: |commutator P| = p^k via Lem 4.6 cardinality
    have hG'_card : Nat.card (_root_.commutator P) = p^k := by
      have h := card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient
        hAb hCyc
      rw [hAcard, hAZcard, pow_succ] at h
      exact Nat.eq_of_mul_eq_mul_right hp_pos h
    -- Step 3: commutator P is nontrivial (|commutator P| = p^k ≥ p > 1)
    have hG'_nontriv : Nontrivial (_root_.commutator P : Subgroup P) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hG'_card]
      exact one_lt_pow₀ hp1 hk_pos.ne'
    -- Step 4: Thm 1.19 ⇒ commutator P ⊓ Z(P) nontrivial
    haveI : Nontrivial ((_root_.commutator P) ⊓ Subgroup.center P : Subgroup P) :=
      OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial hP
        (N := _root_.commutator P) hG'_nontriv
    -- Step 5: commutator P ⊓ Z(P) ⊆ A ⊓ Z(P), and |A ⊓ Z(P)| = p, so equality holds
    have h_inf_le : ((_root_.commutator P) ⊓ Subgroup.center P : Subgroup P)
        ≤ (A ⊓ Subgroup.center P : Subgroup P) :=
      inf_le_inf_right _ hG'_le_A
    have h_inf_eq : ((_root_.commutator P) ⊓ Subgroup.center P : Subgroup P)
        = (A ⊓ Subgroup.center P : Subgroup P) := by
      refine Subgroup.eq_of_le_of_card_ge h_inf_le ?_
      rw [hAZcard]
      have h_nontriv_card : 1 < Nat.card ((_root_.commutator P) ⊓ Subgroup.center P : Subgroup P) :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      -- Apply Lagrange: card H divides card K = p, with card H > 1 ⇒ card H = p
      have h_dvd : Nat.card ((_root_.commutator P) ⊓ Subgroup.center P : Subgroup P)
          ∣ Nat.card (A ⊓ Subgroup.center P : Subgroup P) :=
        Subgroup.card_dvd_of_le h_inf_le
      rw [hAZcard] at h_dvd
      rcases hp_prime.eq_one_or_self_of_dvd _ h_dvd with h_one | h_self
      · omega
      · exact h_self.symm.le
    -- Set Z := A ⊓ Z(P)
    set Z : Subgroup P := A ⊓ Subgroup.center P with hZ_def
    have hZ_card : Nat.card Z = p := hAZcard
    have hZ_le_A : Z ≤ A := inf_le_left
    have hZ_le_center : Z ≤ Subgroup.center P := inf_le_right
    -- Z ≤ commutator P
    have hZ_le_G' : Z ≤ _root_.commutator P := by
      intro x hx
      have hx_in_inf : x ∈ ((_root_.commutator P) ⊓ Subgroup.center P : Subgroup P) := by
        rw [h_inf_eq]; exact hx
      exact (Subgroup.mem_inf.mp hx_in_inf).1
    -- Z is normal in P (Z ≤ Z(P))
    haveI hZ_normal : Z.Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hxZ : x ∈ Subgroup.center P := hZ_le_center hx
      rw [Subgroup.mem_center_iff] at hxZ
      have : g * x * g⁻¹ = x := by rw [hxZ g]; group
      rw [this]; exact hx
    -- Step 6: Work in P̄ = P / Z
    let φ : P →* P ⧸ Z := QuotientGroup.mk' Z
    have hφ_surj : Function.Surjective φ := QuotientGroup.mk_surjective
    haveI : Finite (P ⧸ Z) := Finite.of_surjective φ hφ_surj
    have hφ_ker : φ.ker = Z := QuotientGroup.ker_mk' Z
    -- Ā := image of A
    let Abar : Subgroup (P ⧸ Z) := A.map φ
    haveI hAbar_normal : Abar.Normal := Subgroup.Normal.map ‹A.Normal› φ hφ_surj
    -- Ā abelian
    have hAbar_Ab : ∀ a ∈ Abar, ∀ b ∈ Abar, a * b = b * a := by
      intro a ha b hb
      obtain ⟨a', ha'A, rfl⟩ := ha
      obtain ⟨b', hb'A, rfl⟩ := hb
      rw [← map_mul, ← map_mul, hAb a' ha'A b' hb'A]
    -- P̄ / Ā ≃* P / A ⇒ cyclic
    have hAbar_quot_cyclic : IsCyclic ((P ⧸ Z) ⧸ Abar) := by
      let e : ((P ⧸ Z) ⧸ Abar) ≃* P ⧸ A :=
        QuotientGroup.quotientQuotientEquivQuotient (G := P) Z A hZ_le_A
      exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    -- IsPGroup p P̄
    have hPbar : IsPGroup p (P ⧸ Z) := hP.to_quotient Z
    -- |A ⊓ Z| = |Z| = p (since Z ≤ A ⇒ A ⊓ Z = Z)
    have hAZ_inter_eq : (A ⊓ Z : Subgroup P) = Z := inf_of_le_right hZ_le_A
    -- |Ā| = p^k via card_map_mk_mul_card_inf_eq_card
    have hAbar_card : Nat.card Abar = p^k := by
      have h := card_map_mk_mul_card_inf_eq_card (N := Z) A
      rw [hAZ_inter_eq, hZ_card, hAcard, pow_succ] at h
      exact Nat.eq_of_mul_eq_mul_right hp_pos h
    -- |commutator P ⊓ Z| = |Z| = p (since Z ≤ commutator P)
    have hG'Z_inter_eq : ((_root_.commutator P) ⊓ Z : Subgroup P) = Z := inf_of_le_right hZ_le_G'
    -- commutator P̄ = (commutator P).map φ (by lcs_map at n=1)
    have h_lcs1 : Subgroup.map φ (_root_.commutator P) = _root_.commutator (P ⧸ Z) := by
      have := lowerCentralSeries_map_eq_of_surjective φ hφ_surj 1
      simpa [lowerCentralSeries_one] using this
    -- |commutator P̄| = p^(k-1)
    have hGbar'_card : Nat.card (_root_.commutator (P ⧸ Z)) = p^(k-1) := by
      have h := card_map_mk_mul_card_inf_eq_card (N := Z) (_root_.commutator P)
      rw [hG'Z_inter_eq, hZ_card, hG'_card] at h
      -- h: |(commutator P).map φ| * p = p^k
      rw [h_lcs1] at h
      have hk_succ : k = (k - 1) + 1 := (Nat.sub_add_cancel hk_pos).symm
      rw [hk_succ, pow_succ] at h
      exact Nat.eq_of_mul_eq_mul_right hp_pos h
    -- |Ā ⊓ Z(P̄)| = p (apply Lem 4.6 cardinality to P̄, Ā)
    have hAbarZbar_card : Nat.card (Abar ⊓ Subgroup.center (P ⧸ Z) : Subgroup (P ⧸ Z)) = p := by
      have h := card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient
        hAbar_Ab hAbar_quot_cyclic
      rw [hGbar'_card, hAbar_card] at h
      -- h: p^(k-1) * |Ā ⊓ Z(P̄)| = p^k
      have hk_succ : k = (k - 1) + 1 := (Nat.sub_add_cancel hk_pos).symm
      rw [hk_succ, pow_succ] at h
      have hp_pow_pos : 0 < p^(k-1) := pow_pos hp_pos _
      exact Nat.eq_of_mul_eq_mul_left hp_pow_pos h
    -- Apply IH
    have h_class_Pbar : Group.nilpotencyClass (P ⧸ Z) = k :=
      ih hPbar hAbar_Ab hAbar_quot_cyclic hAbar_card hAbarZbar_card
    -- Translate to lcs: lcs P̄ k = ⊥ and lcs P̄ (k-1) ≠ ⊥
    have h_lcs_Pbar_k : lowerCentralSeries (P ⧸ Z) k = ⊥ :=
      lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr h_class_Pbar.le
    have h_lcs_Pbar_km1_ne : lowerCentralSeries (P ⧸ Z) (k - 1) ≠ ⊥ := by
      intro h_eq
      have := lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp h_eq
      rw [h_class_Pbar] at this
      omega
    -- lcs P k ≤ Z (lift lcs P̄ k = ⊥ back)
    have h_lcs_P_k_le_Z : lowerCentralSeries P k ≤ Z := by
      have h_map : Subgroup.map φ (lowerCentralSeries P k) = lowerCentralSeries (P ⧸ Z) k :=
        lowerCentralSeries_map_eq_of_surjective φ hφ_surj k
      rw [h_lcs_Pbar_k] at h_map
      have h_le_ker : lowerCentralSeries P k ≤ φ.ker :=
        (Subgroup.map_eq_bot_iff _).mp h_map
      rw [hφ_ker] at h_le_ker
      exact h_le_ker
    -- lcs P (k+1) = ⊥ (lcs P k ≤ Z ≤ Z(P))
    have h_lcs_P_kp1 : lowerCentralSeries P (k + 1) = ⊥ :=
      lowerCentralSeries_succ_eq_bot (h_lcs_P_k_le_Z.trans hZ_le_center)
    -- lcs P k ≠ ⊥
    have h_lcs_P_k_ne : lowerCentralSeries P k ≠ ⊥ := by
      -- Case k = 1: lcs P 1 = commutator P ≠ ⊥
      -- Case k ≥ 2: lcs P (k-1) ⊆ commutator P ⊆ A, lcs P (k-1) ⊄ Z ⇒ ...
      by_cases hk1 : k = 1
      · -- k = 1
        subst hk1
        rw [lowerCentralSeries_one]
        intro h_bot
        rw [h_bot, Subgroup.card_bot] at hG'_card
        -- p^1 = 1 ⇒ p = 1, contradiction
        rw [pow_one] at hG'_card
        omega
      · -- k ≥ 2: lcs P (k-1) ⊆ commutator P ⊆ A,
        -- lcs P (k-1) ⊄ Z ⇒ lcs P (k-1) ⊄ Z(P) ⇒ lcs P k ≠ ⊥
        intro h_lcs_k_bot
        -- lcs P (k-1) maps to lcs P̄ (k-1) ≠ ⊥
        have h_map_km1 : Subgroup.map φ (lowerCentralSeries P (k - 1))
            = lowerCentralSeries (P ⧸ Z) (k - 1) :=
          lowerCentralSeries_map_eq_of_surjective φ hφ_surj (k - 1)
        -- lcs P (k-1) ⊄ Z (= φ.ker)
        have h_lcs_km1_nle_Z : ¬ lowerCentralSeries P (k - 1) ≤ Z := by
          intro h_le
          have h_le_ker : lowerCentralSeries P (k - 1) ≤ φ.ker := by
            rw [hφ_ker]; exact h_le
          have : Subgroup.map φ (lowerCentralSeries P (k - 1)) = ⊥ :=
            (Subgroup.map_eq_bot_iff _).mpr h_le_ker
          rw [h_map_km1] at this
          exact h_lcs_Pbar_km1_ne this
        -- lcs P (k-1) ⊆ commutator P ⊆ A (using k - 1 ≥ 1, lcs decreasing)
        have hk_one_le : 1 ≤ k - 1 := by omega
        have h_lcs_km1_le_G' : lowerCentralSeries P (k - 1) ≤ _root_.commutator P := by
          rw [← lowerCentralSeries_one]
          exact lowerCentralSeries_antitone hk_one_le
        have h_lcs_km1_le_A : lowerCentralSeries P (k - 1) ≤ A := h_lcs_km1_le_G'.trans hG'_le_A
        -- ∃ x ∈ lcs P (k-1), x ∉ Z
        rw [SetLike.not_le_iff_exists] at h_lcs_km1_nle_Z
        obtain ⟨x, hx_in, hx_notZ⟩ := h_lcs_km1_nle_Z
        -- x ∈ A but x ∉ Z = A ⊓ Z(P), so x ∉ Z(P) (since x ∈ A)
        have hx_in_A : x ∈ A := h_lcs_km1_le_A hx_in
        have hx_notZP : x ∉ Subgroup.center P := by
          intro hxZP
          exact hx_notZ (Subgroup.mem_inf.mpr ⟨hx_in_A, hxZP⟩)
        -- So ∃ y, [x, y] ≠ 1 (x not in center)
        rw [Subgroup.mem_center_iff] at hx_notZP
        push Not at hx_notZP
        obtain ⟨y, hxy⟩ := hx_notZP
        -- [x, y] ∈ ⁅lcs P (k-1), ⊤⁆ = lcs P k via lcs definition
        have h_xy_in_kp : ⁅x, y⁆ ∈ lowerCentralSeries P ((k - 1) + 1) := by
          show ⁅x, y⁆ ∈ ⁅lowerCentralSeries P (k - 1), (⊤ : Subgroup P)⁆
          exact Subgroup.commutator_mem_commutator hx_in (Subgroup.mem_top y)
        have hk_succ : (k - 1) + 1 = k := Nat.sub_add_cancel hk_pos
        rw [hk_succ] at h_xy_in_kp
        -- lcs P k = ⊥ ⇒ [x, y] = 1 ⇒ x*y = y*x, contradiction
        rw [h_lcs_k_bot, Subgroup.mem_bot] at h_xy_in_kp
        rw [commutatorElement_eq_one_iff_mul_comm] at h_xy_in_kp
        exact hxy h_xy_in_kp.symm
    -- Conclude: Group.nilpotencyClass P = k + 1
    refine Nat.le_antisymm ?_ ?_
    · -- ≤ : lcs P (k+1) = ⊥
      exact lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp h_lcs_P_kp1
    · -- ≥ : NOT (nilpotencyClass ≤ k)
      by_contra h
      push Not at h
      have : lowerCentralSeries P k = ⊥ :=
        lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (Nat.lt_succ_iff.mp h)
      exact h_lcs_P_k_ne this

/-! ### Commutator collection in class ≤ 2 (Thm 4.8 の前段) -/

/-- General identity: `y * x = ⁅y, x⁆ * x * y` (no hypothesis). -/
private lemma mul_eq_commutator_mul (x y : G) :
    y * x = ⁅y, x⁆ * x * y := by
  simp only [commutatorElement_def]
  group

/-- In class ≤ 2 (`commutator G ≤ Z(G)`): `y * x = x * y * ⁅y, x⁆`.
`⁅y, x⁆` 中心で `y * x = ⁅y, x⁆ * (x * y) = (x * y) * ⁅y, x⁆`. -/
private lemma mul_comm_commutator_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y : G) :
    y * x = x * y * ⁅y, x⁆ := by
  have hc : ⁅y, x⁆ ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top y x)
  rw [mul_eq_commutator_mul, mul_assoc]
  exact (Subgroup.mem_center_iff.mp hc (x * y)).symm

/-- In class ≤ 2: `⁅y, x⁆` は中心で全ての元と可換. -/
private lemma commute_commutator_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    Commute ⁅y, x⁆ z := by
  have hc : ⁅y, x⁆ ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top y x)
  exact (Subgroup.mem_center_iff.mp hc z).symm

/-- In class ≤ 2: `y^k * x = x * y^k * ⁅y, x⁆^k` (induction on `k`).
各回 `y` を `x` の右に passing で `⁅y, x⁆` が 1 個発生. -/
private lemma pow_mul_eq_mul_pow_commutator_pow_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y : G) (k : ℕ) :
    y^k * x = x * y^k * ⁅y, x⁆^k := by
  induction k with
  | zero => simp
  | succ j ih =>
    -- ⁅y, x⁆^j commutes with y (central).
    have h_pow_y : ⁅y, x⁆^j * y = y * ⁅y, x⁆^j :=
      (commute_commutator_of_class_le_two hC x y y).pow_left j
    -- 計算 chain
    have step : y^(j+1) * x = x * y^(j+1) * ⁅y, x⁆^(j+1) := by
      rw [pow_succ y j, mul_assoc (y^j) y x,
          mul_comm_commutator_of_class_le_two hC x y]
      -- Goal: y^j * (x * y * ⁅y, x⁆) = x * y^(j+1) * ⁅y, x⁆^(j+1)
      rw [show y^j * (x * y * ⁅y, x⁆) = y^j * x * y * ⁅y, x⁆ by ac_rfl]
      rw [ih]
      -- Goal: x * y^j * ⁅y, x⁆^j * y * ⁅y, x⁆ = x * y^(j+1) * ⁅y, x⁆^(j+1)
      rw [show x * y^j * ⁅y, x⁆^j * y * ⁅y, x⁆ =
            x * y^j * (⁅y, x⁆^j * y) * ⁅y, x⁆ by ac_rfl, h_pow_y]
      -- Goal: x * y^j * (y * ⁅y, x⁆^j) * ⁅y, x⁆ = x * y^(j+1) * ⁅y, x⁆^(j+1)
      rw [show x * y^j * (y * ⁅y, x⁆^j) * ⁅y, x⁆ =
            x * (y^j * y) * (⁅y, x⁆^j * ⁅y, x⁆) by ac_rfl]
      rw [← pow_succ y j, ← pow_succ ⁅y, x⁆ j]
    exact step

/-- **Commutator collection formula in class ≤ 2**:
`(x * y)^n = x^n * y^n * ⁅y, x⁆^(n*(n-1)/2)`.

**証明** (Isaacs p.120): `n` についての induction. step:
`(xy)^(k+1) = (xy)^k · xy = x^k y^k ⁅y,x⁆^(k(k-1)/2) · xy`. 中心元と移動可換で
`y^k · x = x · y^k · ⁅y,x⁆^k` (上記 helper). 整理して指数加法 `k + k(k-1)/2 = k(k+1)/2`. -/
theorem mul_pow_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y : G) (n : ℕ) :
    (x * y)^n = x^n * y^n * ⁅y, x⁆^(n * (n - 1) / 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    -- Goal: x^k * y^k * ⁅y,x⁆^(k(k-1)/2) * (x*y) = x^(k+1) * y^(k+1) * ⁅y,x⁆^((k+1)k/2)
    -- ⁅y, x⁆^(k(k-1)/2) commutes with x and y separately.
    have h_xy : ⁅y, x⁆^(k * (k - 1) / 2) * (x * y) = (x * y) * ⁅y, x⁆^(k * (k - 1) / 2) :=
      ((commute_commutator_of_class_le_two hC x y (x * y)).pow_left _)
    -- ⁅y, x⁆^k commutes with y.
    have h_ky : ⁅y, x⁆^k * y = y * ⁅y, x⁆^k :=
      ((commute_commutator_of_class_le_two hC x y y).pow_left k)
    -- Re-associate to bring (y^k * x) together
    rw [show x^k * y^k * ⁅y, x⁆^(k * (k - 1) / 2) * (x * y) =
          x^k * y^k * (⁅y, x⁆^(k * (k - 1) / 2) * (x * y)) by ac_rfl, h_xy]
    -- Goal: x^k * y^k * ((x*y) * ⁅y,x⁆^(k(k-1)/2)) = ...
    rw [show x^k * y^k * (x * y * ⁅y, x⁆^(k * (k - 1) / 2)) =
          x^k * (y^k * x) * y * ⁅y, x⁆^(k * (k - 1) / 2) by ac_rfl,
        pow_mul_eq_mul_pow_commutator_pow_of_class_le_two hC x y k]
    -- Goal: x^k * (x * y^k * ⁅y,x⁆^k) * y * ⁅y,x⁆^(k(k-1)/2) = ...
    rw [show x^k * (x * y^k * ⁅y, x⁆^k) * y * ⁅y, x⁆^(k * (k - 1) / 2) =
          x^k * x * y^k * (⁅y, x⁆^k * y) * ⁅y, x⁆^(k * (k - 1) / 2) by ac_rfl,
        h_ky]
    -- Goal: x^k * x * y^k * (y * ⁅y,x⁆^k) * ⁅y,x⁆^(k(k-1)/2) = ...
    rw [show x^k * x * y^k * (y * ⁅y, x⁆^k) * ⁅y, x⁆^(k * (k - 1) / 2) =
          (x^k * x) * (y^k * y) * (⁅y, x⁆^k * ⁅y, x⁆^(k * (k - 1) / 2)) by ac_rfl]
    rw [← pow_succ x k, ← pow_succ y k, ← pow_add]
    -- Goal: x^(k+1) * y^(k+1) * ⁅y,x⁆^(k + k(k-1)/2) = x^(k+1) * y^(k+1) * ⁅y,x⁆^((k+1)k/2)
    congr 2
    -- k + k(k-1)/2 = (k+1)k/2 over Nat. Need that k*(k-1) is even.
    rcases k with _ | j
    · simp
    · -- k = j+1: (j+1) + (j+1)*j/2 = (j+2)*(j+1)/2
      simp only [Nat.add_succ_sub_one, Nat.add_zero]
      -- (j+1)*j and (j+2)*(j+1) are both even (consecutive integers)
      have h1 : 2 ∣ (j+1) * j := by
        rw [Nat.mul_comm]; exact (Nat.even_mul_succ_self j).two_dvd
      have h2 : 2 ∣ (j+1+1) * (j+1) := by
        rw [Nat.mul_comm]; exact (Nat.even_mul_succ_self (j+1)).two_dvd
      obtain ⟨m, hm⟩ := h1
      obtain ⟨n, hn⟩ := h2
      -- Eliminate quadratics: (j+2)(j+1) = (j+1)*j + 2*(j+1)
      have key : (j+1+1) * (j+1) = (j+1) * j + 2 * (j+1) := by ring
      rw [key, hm] at hn
      omega

/-! ### Isaacs Thm 4.8(a) -/

/-- **Isaacs Theorem 4.8(a)**: `p > 2`, `G` is a group with `commutator G ≤ Z(G)`
(class ≤ 2). Then `{x ∈ G : x^p = 1}` is a subgroup.

**証明**: 唯一の閉性 (mul_mem). `x^p = y^p = 1` ⇒
`(xy)^p = x^p y^p ⁅y, x⁆^(p(p-1)/2) = ⁅y, x⁆^(p(p-1)/2)` (collection).
`⁅·, x⁆` 左 hom + `y^p = 1` ⇒ `⁅y, x⁆^p = ⁅y^p, x⁆ = ⁅1, x⁆ = 1`.
`p > 2 odd` ⇒ `(p-1)/2 ∈ ℕ` ⇒ `p(p-1)/2 = p · (p-1)/2` で `p` の倍数 ⇒
`⁅y, x⁆^(p(p-1)/2) = (⁅y, x⁆^p)^((p-1)/2) = 1`. -/
def setOfPowEqOne (hC : _root_.commutator G ≤ Subgroup.center G) {p : ℕ}
    (hp : Odd p) : Subgroup G where
  carrier := {x | x^p = 1}
  one_mem' := by show (1 : G)^p = 1; exact one_pow p
  inv_mem' := by
    intro x (hx : x^p = 1)
    show x⁻¹^p = 1
    rw [inv_pow, hx, inv_one]
  mul_mem' := by
    intro x y (hx : x^p = 1) (hy : y^p = 1)
    show (x * y)^p = 1
    rw [mul_pow_of_class_le_two hC, hx, hy, one_mul, one_mul]
    -- Goal: ⁅y, x⁆^(p*(p-1)/2) = 1
    have hcom_p : ⁅y, x⁆^p = 1 := by
      rw [← commutatorElement_pow_left_of_class_le_two hC, hy, commutatorElement_one_left]
    -- p odd ⇒ p - 1 = 2k for some k ⇒ p*(p-1)/2 = p*k.
    obtain ⟨k, hk⟩ := hp
    have hdiv : p * (p - 1) / 2 = p * k := by
      subst hk
      have h1 : 2 * k + 1 - 1 = 2 * k := by omega
      rw [h1, Nat.mul_div_assoc _ (Dvd.intro k rfl)]
      rw [show 2 * k / 2 = k from Nat.mul_div_cancel_left k (by norm_num : (0 : ℕ) < 2)]
    rw [hdiv, pow_mul, hcom_p, one_pow]

/-- **Isaacs Theorem 4.8(b)**: `p > 2` (odd), `commutator G ≤ Z(G)` (class ≤ 2),
全交換子の `p` 乗が `1` ⇒ `x ↦ x^p : G →* G` は (Monoid) 準同型.

**証明**: collection formula `(xy)^p = x^p · y^p · ⁅y, x⁆^(p(p-1)/2)`.
仮定で `⁅y, x⁆^p = 1` + `p` odd ⇒ `p ∣ p(p-1)/2` ⇒ `⁅y, x⁆^(p(p-1)/2) = 1`.
よって `(xy)^p = x^p · y^p`. `1^p = 1` は自明. -/
def powPHom (hC : _root_.commutator G ≤ Subgroup.center G) {p : ℕ} (hp : Odd p)
    (hcomp : ∀ c ∈ _root_.commutator G, c ^ p = 1) : G →* G where
  toFun x := x^p
  map_one' := one_pow p
  map_mul' x y := by
    show (x * y)^p = x^p * y^p
    rw [mul_pow_of_class_le_two hC]
    -- Goal: x^p * y^p * ⁅y, x⁆^(p*(p-1)/2) = x^p * y^p
    have hcom_p : ⁅y, x⁆^p = 1 := hcomp ⁅y, x⁆ (commutatorElement_mem_commutator_top y x)
    obtain ⟨k, hk⟩ := hp
    have hdiv : p * (p - 1) / 2 = p * k := by
      subst hk
      have h1 : 2 * k + 1 - 1 = 2 * k := by omega
      rw [h1, Nat.mul_div_assoc _ (Dvd.intro k rfl)]
      rw [show 2 * k / 2 = k from Nat.mul_div_cancel_left k (by norm_num : (0 : ℕ) < 2)]
    rw [hdiv, pow_mul, hcom_p, one_pow, mul_one]

end -- 4A

section /- 4B: Three-subgroups + lcs additivity + Mann (pp. 122-131) -/

/-! ### Isaacs §4B (Three-subgroups + lower central series)

- **Lemma 4.9 Three-subgroups**: mathlib `Subgroup.commutator_commutator_eq_bot_of_rotate`
  で完全カバー (前提 `⁅⁅H₂,H₃⁆, H₁⁆ = ⊥ ∧ ⁅⁅H₃,H₁⁆, H₂⁆ = ⊥ ⇒ ⁅⁅H₁,H₂⁆, H₃⁆ = ⊥`).
  no-wrapper. -/

/-- **Isaacs Cor 4.10** (Three-subgroups mod `N`):
`N ⊴ G` を含む形での 4.9 — `⁅⁅H₂, H₃⁆, H₁⁆ ≤ N ∧ ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N
⇒ ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N`.

商写像 `G → G/N` で push し, image 上で mathlib `commutator_commutator_eq_bot_of_rotate`
を適用. -/
theorem commutator_commutator_le_of_rotate {H₁ H₂ H₃ N : Subgroup G} [N.Normal]
    (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) :
    ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  -- Use `≤ N ↔ map (mk' N) = ⊥` (since ker (mk' N) = N).
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have to_quot : ∀ {K : Subgroup G}, K ≤ N ↔ K.map π = ⊥ := by
    intro K
    rw [eq_bot_iff, Subgroup.map_le_iff_le_comap]
    constructor
    · intro h x hx
      rw [Subgroup.mem_comap, hπ, Subgroup.mem_bot, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
      exact h hx
    · intro h x hx
      have := h hx
      rw [Subgroup.mem_comap, hπ, Subgroup.mem_bot, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at this
      exact this
  rw [to_quot]
  rw [to_quot] at h1 h2
  -- Map distributes over commutator.
  simp only [Subgroup.map_commutator] at h1 h2 ⊢
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

/-- **Isaacs Thm 4.11** (lcs 加法性) ⭐: `⁅γᵢ(G), γⱼ(G)⁆ ≤ γᵢ₊ⱼ(G)`.

mathlib indexing (`lcs 0 = ⊤ = G^1`, `lcs n = G^{n+1}`) では Isaacs `⁅G^i, G^j⁆ ≤ G^{i+j}`
は `⁅lcs (i-1), lcs (j-1)⁆ ≤ lcs (i+j-1)`, つまり `⁅lcs a, lcs b⁆ ≤ lcs (a + b + 1)`
(`a = i-1, b = j-1`).

**証明** (Isaacs p.123-124): `j` についての induction (`i` 自由).
* base `j = 0`: `⁅lcs i, ⊤⁆ = lcs (i+1)` (mathlib `lowerCentralSeries` 定義式).
* step: Cor 4.10 (Three-subgroups mod `N`) を `H₁ = lcs j, H₂ = ⊤, H₃ = lcs i,
  N = lcs (i+j+2)` で適用. `lcs n` は characteristic ⇒ normal なので `[N.Normal]` 成立.
  - h1 (`⁅⁅⊤, lcs i⁆, lcs j⁆ ≤ N`): `⁅⊤, lcs i⁆ = ⁅lcs i, ⊤⁆ = lcs (i+1)`
    (`commutator_comm` + 定義) 経由で IH at `(i+1, j)`.
  - h2 (`⁅⁅lcs i, lcs j⁆, ⊤⁆ ≤ N`): IH at `(i, j)` + `commutator_mono`
    + `lcs (i+j+1)+1 = lcs (i+j+2)` (定義).
  - 結論 `⁅⁅lcs j, ⊤⁆, lcs i⁆ ≤ N`, つまり `⁅lcs (j+1), lcs i⁆ ≤ lcs (i+j+2)`.
  - `commutator_comm` で `⁅lcs i, lcs (j+1)⁆ ≤ lcs (i+j+2)` を得る.

**下流**: Cor 4.12 (weight n commutator ⊆ G^n), Cor 4.13 (derived ⊆ lcs),
Ch.2 §2D Lucchini K = ⊥ aux の解消経路. -/
theorem commutator_lowerCentralSeries_le (i j : ℕ) :
    ⁅lowerCentralSeries G i, lowerCentralSeries G j⁆ ≤
      lowerCentralSeries G (i + j + 1) := by
  induction j generalizing i with
  | zero =>
    -- ⁅lcs i, lcs 0⁆ = ⁅lcs i, ⊤⁆ = lcs (i+1) by `lowerCentralSeries` def.
    change ⁅lowerCentralSeries G i, (⊤ : Subgroup G)⁆ ≤ lowerCentralSeries G (i + 1)
    exact le_refl _
  | succ j ih =>
    -- Goal: ⁅lcs i, lcs (j+1)⁆ ≤ lcs (i + (j+1) + 1) = lcs (i + j + 2).
    -- Step A: prove the rotated form via Cor 4.10.
    have key : ⁅⁅lowerCentralSeries G j, (⊤ : Subgroup G)⁆, lowerCentralSeries G i⁆ ≤
        lowerCentralSeries G (i + j + 2) := by
      refine commutator_commutator_le_of_rotate ?_ ?_
      · -- h1: ⁅⁅⊤, lcs i⁆, lcs j⁆ ≤ lcs (i + j + 2).
        have h_top : (⁅(⊤ : Subgroup G), lowerCentralSeries G i⁆ : Subgroup G) =
            lowerCentralSeries G (i + 1) := by
          rw [Subgroup.commutator_comm]; rfl
        rw [h_top]
        have hIH := ih (i + 1)
        have heq : (i + 1) + j + 1 = i + j + 2 := by omega
        rwa [heq] at hIH
      · -- h2: ⁅⁅lcs i, lcs j⁆, ⊤⁆ ≤ lcs (i + j + 2).
        -- By IH at i + `commutator_mono` + `lcs (i+j+1)+1 = lcs (i+j+2)` def.
        exact Subgroup.commutator_mono (ih i) le_rfl
    -- Step B: rewrite goal into rotated form via `commutator_comm` + `lowerCentralSeries` def.
    have hidx : i + (j + 1) + 1 = i + j + 2 := by omega
    rw [hidx]
    -- Goal: ⁅lcs i, lcs (j+1)⁆ ≤ lcs (i + j + 2).
    -- lcs (j+1) = ⁅lcs j, ⊤⁆ definitionally; commute and conclude.
    rw [Subgroup.commutator_comm]
    exact key

/-- **左結合 n-重交換子**: `iterLeftCommutator g [g₁, g₂, ..., gₙ] = ⁅...⁅⁅g, g₁⁆, g₂⁆..., gₙ⁆`.
`gs.length = n` のとき重み `n+1`. -/
def iterLeftCommutator (head : G) (tail : List G) : G :=
  tail.foldl (fun acc g => ⁅acc, g⁆) head

/-- **`iterLeftCommutator` 汎用補題**: accumulator が `lcs n` 内なら, 長さ `m` の
リストでの fold は `lcs (n + m)` に収まる. -/
theorem iterLeftCommutator_mem_lowerCentralSeries_add (n : ℕ) (acc : G)
    (hacc : acc ∈ lowerCentralSeries G n) (gs : List G) :
    iterLeftCommutator acc gs ∈ lowerCentralSeries G (n + gs.length) := by
  induction gs generalizing n acc with
  | nil =>
    simpa [iterLeftCommutator] using hacc
  | cons g rest ih =>
    -- iterLeftCommutator acc (g :: rest) = iterLeftCommutator ⁅acc, g⁆ rest.
    have step : ⁅acc, g⁆ ∈ lowerCentralSeries G (n + 1) := by
      change ⁅acc, g⁆ ∈ ⁅lowerCentralSeries G n, (⊤ : Subgroup G)⁆
      exact Subgroup.commutator_mem_commutator hacc (Subgroup.mem_top g)
    have hRec := ih (n + 1) ⁅acc, g⁆ step
    -- hRec : iterLeftCommutator ⁅acc, g⁆ rest ∈ lcs ((n+1) + rest.length)
    have hidx : n + (g :: rest).length = (n + 1) + rest.length := by
      simp [List.length_cons]; omega
    rw [hidx]
    -- Convert goal: iterLeftCommutator acc (g :: rest) = iterLeftCommutator ⁅acc, g⁆ rest (rfl).
    change iterLeftCommutator ⁅acc, g⁆ rest ∈ _
    exact hRec

/-- **Isaacs Cor 4.12** (weight n commutator ⊆ G^n): 重み `n+1` の左結合交換子は
`lcs G n` に含まれる. mathlib indexing で Isaacs `G^{n+1}` = mathlib `lcs G n`.

**証明**: 汎用補題 `iterLeftCommutator_mem_lowerCentralSeries_add` を `n = 0`,
`acc = g ∈ ⊤ = lcs 0` で specialize. -/
theorem iterLeftCommutator_mem_lowerCentralSeries (g : G) (gs : List G) :
    iterLeftCommutator g gs ∈ lowerCentralSeries G gs.length := by
  simpa using iterLeftCommutator_mem_lowerCentralSeries_add 0 g
    (by simp : g ∈ (⊤ : Subgroup G)) gs

/-- **Isaacs Cor 4.13** (derived ⊆ lcs with exponential index):
`derivedSeries G r ≤ lowerCentralSeries G (2^r - 1)`.

mathlib 既存の `derived_le_lower_central` (`derived r ≤ lcs r`) より strictly stronger
(`r ≥ 2` で lcs が antitone のため): Isaacs notation `G^{(r)} ⊆ G^{2^r}` (`G^k = lcs (k-1)`,
`G^{(r)} = derivedSeries r`) に対応.

**証明** (Isaacs p.124): `r`-induction.
* base `r = 0`: `derivedSeries 0 = ⊤ = lcs 0 = lcs (2^0 - 1)` (rfl).
* step: `derivedSeries (r+1) = ⁅derivedSeries r, derivedSeries r⁆`
  - IH + `commutator_mono`: ≤ `⁅lcs (2^r-1), lcs (2^r-1)⁆`.
  - **Thm 4.11** (`commutator_lowerCentralSeries_le`): ≤ `lcs ((2^r-1) + (2^r-1) + 1)`.
  - 算術: `(2^r-1) + (2^r-1) + 1 = 2·2^r - 1 = 2^(r+1) - 1` (`1 ≤ 2^r` 経由).

**系** (Isaacs Cor 4.13 文): `G` nilpotent class `m` (`lcs m = ⊥`) ⇒ derived length
`≤ 1 + ⌈log₂ m⌉`. 本リポでは boolean form のみ実装, log₂ 操作は別途. -/
theorem derivedSeries_le_lowerCentralSeries_two_pow_sub_one (r : ℕ) :
    derivedSeries G r ≤ lowerCentralSeries G (2 ^ r - 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [derivedSeries_succ]
    calc ⁅derivedSeries G r, derivedSeries G r⁆
        ≤ ⁅lowerCentralSeries G (2 ^ r - 1), lowerCentralSeries G (2 ^ r - 1)⁆ :=
          Subgroup.commutator_mono ih ih
      _ ≤ lowerCentralSeries G ((2 ^ r - 1) + (2 ^ r - 1) + 1) :=
          commutator_lowerCentralSeries_le _ _
      _ = lowerCentralSeries G (2 ^ (r + 1) - 1) := by
          congr 1
          have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
          rw [pow_succ]
          omega

/-- **Cor 4.13 系** (G nilpotent ⇒ derived series 量的境界):
`lowerCentralSeries G m = ⊥` ⇒ `derivedSeries G (Nat.log 2 m + 1) = ⊥`.

形式的には `lcs m = ⊥ ⇒ derived (⌊log₂ m⌋ + 1) = ⊥`. mathlib 既存 `IsNilpotent → IsSolvable`
は qualitative only (具体的 derived length 不明), 本補題は **Cor 4.13** から得られる
**explicit upper bound** を与える.

**証明**: `m < 2^(Nat.log 2 m + 1)` (`Nat.lt_pow_succ_log_self`) ⇒ `2^(...)-1 ≥ m`
⇒ lcs antitone で `lcs (2^(...)-1) ≤ lcs m = ⊥`. **Cor 4.13** で `derived (Nat.log 2 m + 1)
≤ lcs (2^(Nat.log 2 m + 1) - 1) = ⊥`. -/
theorem derivedSeries_eq_bot_of_lowerCentralSeries_eq_bot
    {m : ℕ} (h : lowerCentralSeries G m = ⊥) :
    derivedSeries G (Nat.log 2 m + 1) = ⊥ := by
  have h2pow : m < 2 ^ (Nat.log 2 m + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num : (1:ℕ) < 2) m
  have hidx : m ≤ 2 ^ (Nat.log 2 m + 1) - 1 := by omega
  rw [eq_bot_iff]
  calc derivedSeries G (Nat.log 2 m + 1)
      ≤ lowerCentralSeries G (2 ^ (Nat.log 2 m + 1) - 1) :=
        derivedSeries_le_lowerCentralSeries_two_pow_sub_one _
    _ ≤ lowerCentralSeries G m := lowerCentralSeries_antitone (G := G) hidx
    _ = ⊥ := h

/-! ### iterCommutator + Z(F(G)) absorbs G-minimal 補題群

`iterCommutator E F n = ⁅...⁅E, F⁆, F⁆..., F⁆` の infrastructure と
`le_centralizer_of_isMinimalNormal` (Z(F(G)) absorbs G-minimal in F(G)) 系は
**`OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh02.lean`** に移動 (2026-05-24).

理由: Lucchini K=⊥ aux 解消 (issue #0001) で同じ補助補題群を使うが,
ForwardFromCh02 → Main.lean の direct import は循環依存になる
(Main → Ch3 → ForwardFromCh02 → Main). ForwardFromCh02 に置くことで Main.lean
からは Ch3 経由で transitive にアクセス可能 (namespace `OddOrder.Isaacs.Ch04` を共有).

Main.lean 側で `iterCommutator` を使う §4C `iterCommutator_add` / §4D
`iterCommutator_inl_inr_two_eq_one` は ForwardFromCh02 の declarations を直接参照. -/

/-! **Mann 4.14-4.19**: M(G), self-centralizing normal abelian 系. Isaacs 独自集約で
**BG/Peterfalvi 直接被引用 0**. ⇒ **Phase 1 内では skip 可** (audit 確認). -/

end -- 4B

section /- 4C: A acts on G via automorphisms (pp. 131-138) -/

/-! ### Isaacs §4C (A 作用 + [G,A])

`A ⊆ Aut(G)` の作用下で `[G, A]` (= smallest A-invariant N with A trivial on G/N) の構造論.

- **Lemma 4.20**: `⁅G, A⁆` は `A` が trivial 作用する最小 A-invariant 正規部分群.
- **Cor 4.21**: TFAE: (a) 右剰余類すべて A-inv, (b) 左剰余類すべて A-inv, (c) `⁅G,A⁆ ⊆ H`.
- **Thm 4.22**: A faithful + `⁅G, A, ..., A⁆_m = 1` ⇒ A solvable, derived length ≤ m-1.
- **Cor 4.23**: m=2 版.
- **Thm 4.24**: A faithful + chain ⇒ A nilpotent.
- **Lemma 4.25**: `⁅G,A,A⁆ = 1` ⇒ `⁅G,A⁆` abelian.
- **Thm 4.26**: A p-群 + chain ⇒ `⁅G,A⁆` は p-群.
- **Thm 4.27**: A 有限 + chain ⇒ `⁅G,A⁆` nilpotent.

全 stub. `[G, A]` の Lean 形式化 (semidirect product `G ⋊ A` 経由 vs `MulAut` 経由)
の設計判断が要る. ~500-800 行 LOC 推定. -/

end -- 4C

section /- 4D: Coprime action — Fitting + Thompson PxQ + Baer (pp. 138-146) -/

/-! ### Isaacs §4D (Coprime action) ⭐ FT クリティカル

BG Prop 1.6(a)(b)(c)(d)(e) クラスタ + BG Thm 1.11 がこの section を占める.

- **Lemma 4.28** ⭐ BG Prop 1.6(a): `(|G|,|A|) = 1` + (A or G solvable)
  ⇒ `G = C_G(A) · ⁅G, A⁆`.
- **Lemma 4.29** ⭐ BG Prop 1.6(b): coprime ⇒ `⁅G, A, A⁆ = ⁅G, A⁆`.
- **Cor 4.30**: A faithful + chain ⇒ `|A|` の素因子 ⊆ `|G|` の素因子.
- **Thm 4.31 Thompson P×Q** ⭐: `A = P × Q` (P p-群, Q p'-群) acts on p-群 G,
  Q fixes every P-fixed element ⇒ Q trivial on G.
- **Lemma 4.32**: P p-群, G 非自明 p-群: `⁅G, P⁆ < G` かつ `C_G(P) > 1`.
- **Thm 4.33**: G p-solvable ⇒ 全 p-local H で `O_{p'}(H) ≤ O_{p'}(G)`. **Hall-Higman 1.2.3
  (Ch.3 Lem 3.21) 経由**.
- **Thm 4.34 Fitting** ⭐ BG Prop 1.6(d): G abelian + coprime ⇒ `G = C_G(A) × ⁅G, A⁆`.
- **Cor 4.35** ⭐ BG Prop 1.6(e): G abelian p-群 + A p'-群 fixes order-p elements
  ⇒ A trivial.
- **Thm 4.36** ⭐ BG Thm 1.11: p > 2, G p-群 + A p'-群 fixes order-p elements
  ⇒ A trivial. **Ch.5 Cor 5.30 経由で normal p-comp 5.26 へ**.
- **Lemma 4.37 Baer trick**: G odd order + class ≤ 2 ⇒ `x +' y := xy√⁅y,x⁆` で加法群.
- **Thm 4.38**: p > 2, P p-群 + Q ⊴ A p'-群, Q fixes P-fixed elements ⇒ Q trivial
  (4.31 強化, P 正規不要).

**実装スケジュール推定**: 4.28 + 4.29 + 4.30 (~200 行 / 1 週), 4.34 + 4.35 + 4.36
(~250 行 / 1-2 週), 4.31 + 4.32 + 4.38 (~150 行 / 1 週), 4.33 + 4.37 (~150 行 / 1 週).

合計 ~750 行 LOC / 4-5 週. Phase 1 残予算と要相談. -/

/-- A finite `p`-group is a `{p}`-group in the π-group sense. -/
theorem isPiGroup_singleton_of_isPGroup {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} (hH : IsPGroup p H) :
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) H := by
  intro q hq
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := H)).mp hH
  rw [hn] at hq
  by_cases hn0 : n = 0
  · simp [hn0] at hq
  · rw [Nat.primeFactors_prime_pow hn0 Fact.out] at hq
    simpa using hq

/-- A finite `{p}`-group in the π-group sense is a `p`-group. -/
theorem isPGroup_of_isPiGroup_singleton {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) H) :
    IsPGroup p H := by
  rw [IsPGroup.iff_card]
  exact ⟨(Nat.card H).primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun {q} hq_prime hq_dvd => by
      have hq_pf : q ∈ (Nat.card H).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd, Nat.card_pos.ne'⟩
      simpa using hH q hq_pf)⟩

/-- Singleton π-core agrees with the usual `p`-core. -/
theorem oPiCore_singleton_eq_opCore {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] :
    OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G =
      OddOrder.Isaacs.Ch01.opCore p G := by
  apply le_antisymm
  · exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore
      (isPGroup_of_isPiGroup_singleton (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup ({p} : Set ℕ)))
  · exact OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore
      (isPiGroup_singleton_of_isPGroup (OddOrder.Isaacs.Ch01.opCore_isPGroup p G))

private theorem opCore_eq_bot_of_mulEquiv
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (e : G ≃* H)
    (hG : OddOrder.Isaacs.Ch01.opCore p G = ⊥) :
    OddOrder.Isaacs.Ch01.opCore p H = ⊥ := by
  rw [← oPiCore_singleton_eq_opCore (G := H) p,
    ← OddOrder.Isaacs.Ch03.oPiCore.map_eq_of_mulEquiv ({p} : Set ℕ) e,
    oPiCore_singleton_eq_opCore (G := G) p, hG, Subgroup.map_bot]

/-- In a finite abelian group with trivial `O_p`, every prime divisor is different from `p`. -/
private theorem isPiGroup_compl_top_of_isMulCommutative_opCore_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [IsMulCommutative G]
    (hOp : OddOrder.Isaacs.Ch01.opCore p G = ⊥) :
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} (⊤ : Subgroup G) := by
  intro q hq hq_mem
  have hq_eq : q = p := by simpa using hq_mem
  subst q
  have hp_dvd_top : p ∣ Nat.card ↥(⊤ : Subgroup G) :=
    Nat.dvd_of_mem_primeFactors hq
  have hp_dvd : p ∣ Nat.card G := by simpa using hp_dvd_top
  let P : Sylow p G := default
  -- rc2: `CommGroup.ofIsMulCommutative` removed; build CommGroup from the IsMulCommutative.
  letI : CommGroup G :=
    { (inferInstance : Group G) with mul_comm := ‹IsMulCommutative G›.is_comm.comm }
  haveI : (P : Subgroup G).Normal := Subgroup.normal_of_comm _
  have hP_le : (P : Subgroup G) ≤ OddOrder.Isaacs.Ch01.opCore p G :=
    OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore P.isPGroup'
  have hP_bot : (P : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    simpa [hOp] using hP_le
  exact (P.ne_bot_of_dvd_card hp_dvd) hP_bot

private lemma opCore_quotient_opCore_eq_bot {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] :
    OddOrder.Isaacs.Ch01.opCore p (G ⧸ OddOrder.Isaacs.Ch01.opCore p G) = ⊥ := by
  set N : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hN_def
  set f : G →* G ⧸ N := QuotientGroup.mk' N with hf_def
  have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective N
  have hf_ker : f.ker = N := QuotientGroup.ker_mk' N
  set Kbar : Subgroup (G ⧸ N) := OddOrder.Isaacs.Ch01.opCore p (G ⧸ N) with hKbar_def
  set K : Subgroup G := Kbar.comap f with hK_def
  haveI hK_normal : K.Normal := Kbar.normal_comap f
  have hKbar_pgroup : IsPGroup p Kbar := OddOrder.Isaacs.Ch01.opCore_isPGroup p (G ⧸ N)
  have hN_pgroup : IsPGroup p N := OddOrder.Isaacs.Ch01.opCore_isPGroup p G
  have hN_le_K : N ≤ K := by
    intro x hx
    have hfx : f x = 1 := by
      have : x ∈ f.ker := by rw [hf_ker]; exact hx
      exact this
    rw [hK_def, Subgroup.mem_comap, hfx]
    exact Subgroup.one_mem _
  have hK_map : K.map f = Kbar := by
    rw [hK_def]
    exact Subgroup.map_comap_eq_self_of_surjective hf_surj Kbar
  have hK_pgroup : IsPGroup p K := by
    have h_quot_card : Nat.card (↥K ⧸ N.subgroupOf K) = Nat.card Kbar := by
      let g : ↥K →* G ⧸ N := f.comp K.subtype
      have hg_range : g.range = K.map f := by
        simp [g, MonoidHom.range_comp, Subgroup.range_subtype]
      have hg_ker : g.ker = N.subgroupOf K := by
        ext x
        constructor
        · intro hx
          have : f (x : G) = 1 := hx
          have hxN : (x : G) ∈ N := by rw [← hf_ker]; exact this
          exact hxN
        · intro hx
          have hxN : (x : G) ∈ N := hx
          have : (x : G) ∈ f.ker := by rw [hf_ker]; exact hxN
          exact this
      have h_iso : (↥K) ⧸ g.ker ≃* ↥g.range :=
        QuotientGroup.quotientKerEquivRange g
      have h_card_eq : Nat.card ((↥K) ⧸ g.ker) = Nat.card ↥g.range :=
        Nat.card_congr h_iso.toEquiv
      rw [hg_ker] at h_card_eq
      rw [h_card_eq, hg_range, hK_map]
    have h_sub_card : Nat.card (N.subgroupOf K) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_le_K).toEquiv
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hKbar_pgroup
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hN_pgroup
    have hK_card : Nat.card K = p ^ (a + b) := by
      have h_mul : Nat.card K = Nat.card (↥K ⧸ N.subgroupOf K) *
          Nat.card (N.subgroupOf K) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup]
      rw [h_mul, h_quot_card, ha, h_sub_card, hb, pow_add]
    exact IsPGroup.of_card hK_card
  have hK_le_N : K ≤ N := by
    have := OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore (N := K) hK_pgroup
    rw [hN_def]
    exact this
  have hK_eq_N : K = N := le_antisymm hK_le_N hN_le_K
  rw [← hK_map, hK_eq_N]
  apply le_bot_iff.mp
  intro y hy
  rcases hy with ⟨z, hz, hzy⟩
  rw [Subgroup.mem_bot, ← hzy]
  have : z ∈ f.ker := by rw [hf_ker]; exact hz
  exact this

private lemma subgroup_card_lt_card_of_ne_top
    {G : Type*} [Group G] [Finite G] {H : Subgroup G} (h_ne : H ≠ ⊤) :
    Nat.card ↥H < Nat.card G := by
  have h_dvd : Nat.card ↥H ∣ Nat.card G :=
    ⟨H.index, by rw [mul_comm, H.index_mul_card]⟩
  have h_le' : Nat.card ↥H ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos h_dvd
  have h_ne' : Nat.card ↥H ≠ Nat.card G := fun heq =>
    h_ne (Subgroup.eq_top_of_card_eq _ heq)
  exact Nat.lt_of_le_of_ne h_le' h_ne'

/-- A finite group is generated by all of its Sylow subgroups. -/
private lemma iSup_sylow_eq_top {M : Type*} [Group M] [Finite M] :
    (⨆ p : (Nat.card M).primeFactors, ⨆ P : Sylow p.val M, (P : Subgroup M)) = ⊤ := by
  classical
  set sup := ⨆ p : (Nat.card M).primeFactors, ⨆ P : Sylow p.val M, (P : Subgroup M) with hsup_def
  have h_sup_dvd : Nat.card sup ∣ Nat.card M := Subgroup.card_subgroup_dvd_card sup
  have h_pow_dvd : ∀ p ∈ (Nat.card M).primeFactors,
      p ^ (Nat.card M).factorization p ∣ Nat.card sup := by
    intro p hp
    haveI hp_prime : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    have hP_le : ((default : Sylow p M) : Subgroup M) ≤ sup := by
      rw [hsup_def]
      refine le_trans ?_ (le_iSup (fun q : (Nat.card M).primeFactors =>
        ⨆ Q : Sylow q.val M, (Q : Subgroup M)) ⟨p, hp⟩)
      exact le_iSup (fun Q : Sylow p M => (Q : Subgroup M)) default
    have h_dvd := Subgroup.card_dvd_of_le hP_le
    rwa [Sylow.card_eq_multiplicity] at h_dvd
  have h_factorization_le : ∀ p, (Nat.card M).factorization p ≤ (Nat.card sup).factorization p := by
    intro p
    rcases Nat.eq_zero_or_pos ((Nat.card M).factorization p) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have hp_in : p ∈ (Nat.card M).primeFactors := by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr (by omega)
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
      exact (hp_prime.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp (h_pow_dvd p hp_in)
  have h_factorization_le' : ∀ p, (Nat.card sup).factorization p ≤ (Nat.card M).factorization p :=
    fun p => (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr h_sup_dvd p
  have h_eq : Nat.card sup = Nat.card M := by
    apply Nat.eq_of_factorization_eq Nat.card_pos.ne' Nat.card_pos.ne'
    intro p
    exact le_antisymm (h_factorization_le' p) (h_factorization_le p)
  exact Subgroup.eq_top_of_card_eq sup h_eq

/-- Hall-Higman 1.2.3 specialized from `O_π` to the usual `p`-core. -/
theorem hall_higman_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hπ' : OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥) :
    Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) ≤
      OddOrder.Isaacs.Ch01.opCore p G := by
  rw [← oPiCore_singleton_eq_opCore (G := G) p]
  exact OddOrder.Isaacs.Ch03.hall_higman_1_2_3 ({p} : Set ℕ) hπ'

/-- Normal `p`-subgroups commute with normal `p'`-subgroups in a finite group. -/
theorem commute_of_normal_isPGroup_of_normal_isPiCompl
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P Q : Subgroup G} [P.Normal] [Q.Normal]
    (hP : IsPGroup p P)
    (hQ : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} Q) :
    ∀ x y : G, x ∈ P → y ∈ Q → Commute x y := by
  have hPpi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) P :=
    isPiGroup_singleton_of_isPGroup hP
  have hcop : Nat.Coprime (Nat.card P) (Nat.card Q) :=
    OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne' hPpi hQ
  have hdis : Disjoint P Q :=
    disjoint_iff.mpr (Subgroup.inf_eq_bot_of_coprime hcop)
  intro x y hx hy
  exact Subgroup.commute_of_normal_of_disjoint P Q inferInstance inferInstance hdis x y hx hy

/-- centralizer ⊆ normalizer (mathlib v4.29.1 に直接の lemma 無し). -/
private theorem centralizer_le_normalizer_subgroup {G : Type*} [Group G] (H : Subgroup G) :
    Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer H := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hcomm : ∀ z ∈ H, z * x = x * z := Subgroup.mem_centralizer_iff.mp hx
  have hx_inv_mem : x⁻¹ ∈ Subgroup.centralizer (H : Set G) :=
    Subgroup.inv_mem _ hx
  have hcomm_inv : ∀ z ∈ H, z * x⁻¹ = x⁻¹ * z :=
    Subgroup.mem_centralizer_iff.mp hx_inv_mem
  refine ⟨fun hy => ?_, fun hxyx => ?_⟩
  · have hxy : x * y = y * x := (hcomm y hy).symm
    have : x * y * x⁻¹ = y := by rw [hxy]; group
    rw [this]; exact hy
  · have hcomm_z : (x * y * x⁻¹) * x⁻¹ = x⁻¹ * (x * y * x⁻¹) :=
      hcomm_inv (x * y * x⁻¹) hxyx
    have h_eq : y * x⁻¹ = (x * y * x⁻¹) * x⁻¹ := by
      rw [hcomm_z]; group
    have hy_eq : y = x * y * x⁻¹ := mul_right_cancel h_eq
    rw [hy_eq]; exact hxyx

/-- **作用交換子部分群** `[G, A]_φ` := 集合 `{g * (φ a) g⁻¹ : g ∈ G, a ∈ A}` の生成部分群.

これは Γ = G ⋊[φ] A 内で `⁅inl(G), inr(A)⁆` を `inl : G →* Γ` 経由で pull back した
ものに対応する. 具体的計算: `[inl(g), inr(a)] = inl(g * (φ a) g⁻¹)` (`inl_aut` 経由).

下流 Isaacs §4D 4.28-4.30 の `[G, A]` 記号の自然な実装. -/
def actionCommutator {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) : Subgroup G :=
  Subgroup.closure {x : G | ∃ g : G, ∃ a : A, x = g * (φ a) g⁻¹}

/-- 自明作用 (φ = 1) の場合, `actionCommutator = ⊥` (各 generator = g * g⁻¹ = 1). -/
@[simp]
theorem actionCommutator_one_eq_bot {A G : Type*} [Group A] [Group G] :
    actionCommutator (1 : A →* MulAut G) = ⊥ := by
  rw [actionCommutator, Subgroup.closure_eq_bot_iff]
  rintro _ ⟨g, a, rfl⟩
  show g * (1 : MulAut G) g⁻¹ = 1
  simp

/-- **`actionCommutator φ` は φ 作用下で A-不変**.

`(φ b) (g * (φ a) g⁻¹) = (φ b) g * (φ (b * a * b⁻¹)) ((φ b) g)⁻¹` (generator → generator 写像)
が両方向で成り立つので生成集合自体が `(φ b)`-stable. `closure_of_invariant_set` で結論. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutator φ) := by
  apply OddOrder.Isaacs.Ch03.IsAInvariant.closure_of_invariant_set
  intro b
  -- generator g * (φ a) g⁻¹ → (φ b) g * (φ (b·a·b⁻¹)) ((φ b) g)⁻¹ (= 別の generator).
  have key : ∀ g : G, ∀ a : A,
      (φ b) (g * (φ a) g⁻¹) = (φ b) g * (φ (b * a * b⁻¹)) ((φ b) g)⁻¹ := by
    intro g a
    rw [map_mul (φ b)]
    congr 1
    -- (φ b) ((φ a) g⁻¹) = (φ (b·a·b⁻¹)) ((φ b) g)⁻¹
    rw [show ((φ b) g)⁻¹ = (φ b) g⁻¹ from (map_inv (φ b) g).symm,
        show φ (b * a * b⁻¹) = (φ b) * (φ a) * (φ b)⁻¹ from by rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  ext x
  refine ⟨?_, ?_⟩
  · -- (φ b) '' S ⊆ S
    rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    exact ⟨(φ b) g, b * a * b⁻¹, key g a⟩
  · -- S ⊆ (φ b) '' S: take preimage via (φ b)⁻¹
    rintro ⟨g, a, rfl⟩
    refine ⟨(φ b)⁻¹ g * (φ (b⁻¹ * a * b)) ((φ b)⁻¹ g)⁻¹,
      ⟨(φ b)⁻¹ g, b⁻¹ * a * b, rfl⟩, ?_⟩
    rw [map_mul (φ b)]
    congr 1
    · exact MulAut.apply_inv_self (M := G) (φ b) g
    -- (φ b) ((φ (b⁻¹·a·b)) ((φ b)⁻¹ g)⁻¹) = (φ a) g⁻¹
    rw [show ((φ b)⁻¹ g)⁻¹ = (φ b)⁻¹ g⁻¹ from (map_inv ((φ b)⁻¹) g).symm,
        show φ (b⁻¹ * a * b) = (φ b)⁻¹ * (φ a) * (φ b) from by rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, MulAut.apply_inv_self]

/-- **`(actionCommutator φ).map inl = ⁅inl.range, inr.range⁆`** (Γ = G ⋊[φ] A 内).

Γ 経由で `actionCommutator` を Γ 内 commutator subgroup と同一視. `inl` 経由 push が
Γ 内 commutator `⁅inl.range, inr.range⁆` に一致. これと Lem 4.1 (`⁅H, K⁆ ⊴ ⟨H, K⟩`)
を組合せて `(actionCommutator φ).Normal` (G 内) を導出する経路の主補題.

**証明**: 両側 `Subgroup.closure` 形に展開し集合等式. 生成元の対応は
`⁅inl g, inr a⁆ = inl (g * (φ a) g⁻¹)` (`SemidirectProduct.commutator_inl_inr`). -/
theorem actionCommutator_map_inl
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) :
    (actionCommutator φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A) =
      ⁅(SemidirectProduct.inl : G →* G ⋊[φ] A).range,
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range⁆ := by
  rw [actionCommutator, MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    refine ⟨SemidirectProduct.inl g, ⟨g, rfl⟩, SemidirectProduct.inr a, ⟨a, rfl⟩, ?_⟩
    exact SemidirectProduct.commutator_inl_inr (φ := φ) g a
  · rintro ⟨_, ⟨g, rfl⟩, _, ⟨a, rfl⟩, rfl⟩
    refine ⟨g * (φ a) g⁻¹, ⟨g, a, rfl⟩, ?_⟩
    exact (SemidirectProduct.commutator_inl_inr (φ := φ) g a).symm

/-- Restricted-action version of `actionCommutator_map_inl`.

If `B` acts on `G` through `i : B →* A` and `φ : A →* MulAut G`, then the
`B`-action commutator maps into the same semidirect product `G ⋊[φ] A` as the
commutator of `inl(G)` with the image of `B` inside `inr(A)`. -/
theorem actionCommutator_map_inl_comp
    {A B G : Type*} [Group A] [Group B] [Group G]
    (φ : A →* MulAut G) (i : B →* A) :
    (actionCommutator (φ.comp i)).map (SemidirectProduct.inl : G →* G ⋊[φ] A) =
      ⁅(SemidirectProduct.inl : G →* G ⋊[φ] A).range,
        ((SemidirectProduct.inr : A →* G ⋊[φ] A).comp i).range⁆ := by
  rw [actionCommutator, MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨g, b, rfl⟩, rfl⟩
    refine ⟨SemidirectProduct.inl g, ⟨g, rfl⟩,
      SemidirectProduct.inr (i b), ⟨b, rfl⟩, ?_⟩
    exact SemidirectProduct.commutator_inl_inr (φ := φ) g (i b)
  · rintro ⟨_, ⟨g, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    refine ⟨g * (φ (i b)) g⁻¹, ⟨g, b, rfl⟩, ?_⟩
    exact (SemidirectProduct.commutator_inl_inr (φ := φ) g (i b)).symm

/-- Restricting the acting group can only shrink the action commutator. -/
theorem actionCommutator_comp_le
    {A B G : Type*} [Group A] [Group B] [Group G]
    (φ : A →* MulAut G) (i : B →* A) :
    actionCommutator (φ.comp i) ≤ actionCommutator φ := by
  rw [actionCommutator, Subgroup.closure_le]
  rintro _ ⟨g, b, rfl⟩
  exact Subgroup.subset_closure ⟨g, i b, rfl⟩

/-- Push-forward of the conjugation-action commutator: for `K ≤ N_Γ(P)`, the
`actionCommutator` of the conjugation action of `K` on `P` realizes the ambient subgroup
commutator `⁅P, K⁆`. -/
theorem actionCommutator_conj_map_subtype {Γ : Type*} [Group Γ] {P K : Subgroup Γ}
    (hKP : K ≤ Subgroup.normalizer (P : Set Γ)) :
    (actionCommutator ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP))).map
      P.subtype = ⁅P, K⁆ := by
  rw [actionCommutator, MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    refine ⟨(g : Γ), g.2, (a : Γ), a.2, ?_⟩
    rw [commutatorElement_def]
    have hcoe : (P.subtype
          (g * ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP)) a g⁻¹) : Γ)
        = (g : Γ) * ((a : Γ) * (g : Γ)⁻¹ * (a : Γ)⁻¹) := rfl
    rw [hcoe]
    group
  · rintro ⟨g, hg, a, ha, rfl⟩
    refine ⟨(⟨g, hg⟩ : P) *
      ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP)) ⟨a, ha⟩ ⟨g, hg⟩⁻¹,
      ⟨⟨g, hg⟩, ⟨a, ha⟩, rfl⟩, ?_⟩
    rw [commutatorElement_def]
    have hcoe : (P.subtype
          ((⟨g, hg⟩ : P) *
            ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP)) ⟨a, ha⟩
              (⟨g, hg⟩ : P)⁻¹) : Γ)
        = g * (a * g⁻¹ * a⁻¹) := rfl
    rw [hcoe]
    group

/-- Push-forward of the conjugation-action fixed points: fixed points of the conjugation
action of `K` on `P` map to `C_Γ(K) ⊓ P`. -/
theorem fixedPointsOfMulAut_conj_map_subtype {Γ : Type*} [Group Γ] {P K : Subgroup Γ}
    (hKP : K ≤ Subgroup.normalizer (P : Set Γ)) :
    (Subgroup.fixedPointsOfMulAut
        ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP))).map P.subtype =
      Subgroup.centralizer (K : Set Γ) ⊓ P := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun k hk => ?_, x.2⟩
    have hfix := Subgroup.mem_fixedPointsOfMulAut.mp hx ⟨k, hk⟩
    have hcoe : k * (x : Γ) * k⁻¹ = (x : Γ) := congrArg Subtype.val hfix
    calc k * (x : Γ) = (k * x * k⁻¹) * k := by group
    _ = (x : Γ) * k := by rw [hcoe]
  · rintro ⟨hy, hyP⟩
    refine ⟨⟨y, hyP⟩, Subgroup.mem_fixedPointsOfMulAut.mpr fun a => Subtype.ext ?_, rfl⟩
    change (a : Γ) * y * (a : Γ)⁻¹ = y
    rw [hy (a : Γ) a.2]
    group

/-- **`actionCommutator φ` は G で normal subgroup**.

経路: `actionCommutator_map_inl` で `(actionCommutator φ).map inl = ⁅inl.range, inr.range⁆`,
Γ 内で `inl.range ⊔ inr.range = ⊤` (`SemidirectProduct.inl_range_sup_inr_range_eq_top`) より
Lem 4.1 系 `commutator_normal_of_sup_eq_top` で `⁅inl.range, inr.range⁆.Normal`. `inl`
injectivity で pull back (`Subgroup.Normal.of_map_injective`).

Isaacs §4C 冒頭注 (Lem 4.1 を Γ で適用) を直接実装. -/
instance actionCommutator.normal {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) :
    (actionCommutator φ).Normal := by
  refine Subgroup.Normal.of_map_injective
    (φ := (SemidirectProduct.inl : G →* G ⋊[φ] A)) SemidirectProduct.inl_injective ?_
  rw [actionCommutator_map_inl]
  exact commutator_normal_of_sup_eq_top SemidirectProduct.inl_range_sup_inr_range_eq_top

/-! ### Isaacs §4C: [G,A] の universal property (Lem 4.20, Cor 4.21) -/

/-- **Isaacs Lemma 4.20** (element form, right): `actionCommutator φ ≤ N` iff
`∀ a g, (φ a) g * g⁻¹ ∈ N`. つまり `actionCommutator φ` は
`{(φ a) g * g⁻¹ : a g}` で生成される最小の部分群.

**意味**: `N ⊴ G` が `A`-不変なら `actionCommutator ≤ N ↔ A acts trivially on G/N`
(右剰余類 `Nx` が A 不変 ↔ `(φ a) x ∈ Nx`).

**証明**: `actionCommutator` は `g * (φ a) g⁻¹ = ((φ a) g * g⁻¹)⁻¹` で生成されるので
`(φ a) g * g⁻¹` の集合と同じ subgroup を生成する. -/
theorem actionCommutator_le_iff {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) (N : Subgroup G) :
    actionCommutator φ ≤ N ↔ ∀ a : A, ∀ g : G, (φ a) g * g⁻¹ ∈ N := by
  constructor
  · intro h a g
    have h_gen : g * (φ a) g⁻¹ ∈ actionCommutator φ :=
      Subgroup.subset_closure ⟨g, a, rfl⟩
    have h_inv : (φ a) g * g⁻¹ = (g * (φ a) g⁻¹)⁻¹ := by
      rw [show (φ a) g⁻¹ = ((φ a) g)⁻¹ from map_inv (φ a) g]
      group
    rw [h_inv]
    exact Subgroup.inv_mem _ (h h_gen)
  · intro h
    rw [actionCommutator, Subgroup.closure_le]
    rintro _ ⟨g, a, rfl⟩
    have h_form : g * (φ a) g⁻¹ = ((φ a) g * g⁻¹)⁻¹ := by
      rw [show (φ a) g⁻¹ = ((φ a) g)⁻¹ from map_inv (φ a) g]
      group
    rw [h_form]
    exact Subgroup.inv_mem _ (h a g)

/-- **Isaacs Lemma 4.20** (element form, left): `actionCommutator φ ≤ N` iff
`∀ a g, g⁻¹ * (φ a) g ∈ N`. 左剰余類 `xN` 形.

**意味**: 左剰余類 `xN` が `A` 不変 ↔ `(φ a) x ∈ xN` ↔ `x⁻¹ * (φ a) x ∈ N`. -/
theorem actionCommutator_le_iff_left {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) (N : Subgroup G) :
    actionCommutator φ ≤ N ↔ ∀ a : A, ∀ g : G, g⁻¹ * (φ a) g ∈ N := by
  rw [actionCommutator_le_iff]
  -- ∀ a g, (φ a) g * g⁻¹ ∈ N ↔ ∀ a g, g⁻¹ * (φ a) g ∈ N
  constructor
  · intro h a x
    have h' := h a x⁻¹
    rw [show (φ a) x⁻¹ = ((φ a) x)⁻¹ from map_inv (φ a) x] at h'
    -- h' : ((φ a) x)⁻¹ * x⁻¹⁻¹ ∈ N
    have h_eq : ((φ a) x)⁻¹ * x⁻¹⁻¹ = (x⁻¹ * (φ a) x)⁻¹ := by group
    rw [h_eq] at h'
    simpa using Subgroup.inv_mem _ h'
  · intro h a x
    have h' := h a x⁻¹
    rw [show (φ a) x⁻¹ = ((φ a) x)⁻¹ from map_inv (φ a) x] at h'
    have h_eq : x⁻¹⁻¹ * ((φ a) x)⁻¹ = ((φ a) x * x⁻¹)⁻¹ := by group
    rw [h_eq] at h'
    simpa using Subgroup.inv_mem _ h'

/-- `actionCommutator φ = ⊥` iff `A` acts trivially on `G` (`∀ a g, (φ a) g = g`).

Lem 4.20 left form を `N = ⊥` で特殊化. BaerMul wrapper への翻訳に基本. -/
theorem actionCommutator_eq_bot_iff_acts_trivially {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) :
    actionCommutator φ = ⊥ ↔ ∀ a : A, ∀ g : G, (φ a) g = g := by
  rw [eq_bot_iff, actionCommutator_le_iff_left]
  refine ⟨fun h a g => ?_, fun h a g => ?_⟩
  · have hg := h a g
    rw [Subgroup.mem_bot, inv_mul_eq_one] at hg
    exact hg.symm
  · rw [Subgroup.mem_bot, h a g, inv_mul_cancel]

/-- **A-不変部分群への作用制限**: `φ : A →* MulAut G` + `IsAInvariant φ H` から
`A →* MulAut ↥H` を構成. 関数本体は `(φ a)` を `H` に制限したもの.

Thm 4.36 induction で IH を `[G, A] < G` 等の subgroup に適用するために必要. -/
def OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom {A G : Type*} [Group A] [Group G]
    {φ : A →* MulAut G} {H : Subgroup G}
    (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) : A →* MulAut H where
  toFun a := {
    toFun := fun h => ⟨(φ a) h.val, hH.smul_mem a h.property⟩
    invFun := fun h => ⟨(φ a)⁻¹ h.val, hH.inv_smul_mem a h.property⟩
    left_inv := fun h => Subtype.ext (by
      show (φ a)⁻¹ ((φ a) h.val) = h.val
      simp)
    right_inv := fun h => Subtype.ext (by
      show (φ a) ((φ a)⁻¹ h.val) = h.val
      simp)
    map_mul' := fun x y => Subtype.ext (map_mul (φ a) x.val y.val)
  }
  map_one' := by
    ext h
    show ((φ 1 : MulAut G) h.val) = h.val
    simp
  map_mul' a b := by
    ext h
    show ((φ (a * b) : MulAut G) h.val) = ((φ a) ((φ b) h.val))
    rw [map_mul]; rfl

@[simp] lemma OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom_apply_val
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) (a : A) (h : H) :
    ((OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH a) h).val =
      (φ a) h.val := rfl

/-- If `H` is A-invariant and `K` is characteristic in `H`, then the image of `K`
inside `G` is A-invariant. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.map_subtype_of_characteristic
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {H : Subgroup G} (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H)
    {K : Subgroup H} [K.Characteristic] :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (K.map H.subtype) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a x hx
  rcases hx with ⟨k, hk, rfl⟩
  let ψ : A →* MulAut H := OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH
  have hK_map : K.map (ψ a).toMonoidHom = K :=
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) (ψ a)
  have hk' : (ψ a) k ∈ K := by
    have : (ψ a) k ∈ K.map (ψ a).toMonoidHom := ⟨k, hk, rfl⟩
    rwa [hK_map] at this
  exact ⟨(ψ a) k, hk', rfl⟩

/-- **A-不変正規部分群で割った商群への誘導作用**.

`N` が `φ` で不変なら, 各 `φ a` は `G/N` の自己同型を誘導する. -/
noncomputable def OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) : A →* MulAut (G ⧸ N) where
  toFun a := QuotientGroup.congr N N (φ a) (by
    change N.map (φ a).toMonoidHom = N
    exact hN a)
  map_one' := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro g
    simp
  map_mul' a b := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro g
    simp [map_mul]

@[simp] lemma OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk'
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) (a : A) (g : G) :
    (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN a)
        (QuotientGroup.mk' N g) =
      QuotientGroup.mk' N ((φ a) g) := rfl

@[simp] lemma OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) (a : A) (g : G) :
    (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN a) (g : G ⧸ N) =
      ((φ a) g : G ⧸ N) := rfl

/-- **Isaacs Corollary 3.28 / BG Proposition 1.5(d), subgroup form**: for a coprime
action `φ : A → MulAut G` and an `A`-invariant normal subgroup `N`, the fixed points of
the induced action on `G/N` are exactly the image of the fixed points in `G`. -/
theorem fixedPointsOfMulAut_quotientMulAutHom_eq_map
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) (hSolv : IsSolvable A ∨ IsSolvable G)
    {N : Subgroup G} [N.Normal] (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) :
    Subgroup.fixedPointsOfMulAut (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) =
      (Subgroup.fixedPointsOfMulAut φ).map (QuotientGroup.mk' N) := by
  refine le_antisymm ?_ ?_
  · intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [Subgroup.mem_fixedPointsOfMulAut] at hq
    have hg_fix : ∀ a : A, ∃ n ∈ N, (φ a) g = g * n := by
      intro a
      have hga := hq a
      rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk',
        QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hga
      exact ⟨g⁻¹ * (φ a) g, by simpa using N.inv_mem hga, by group⟩
    obtain ⟨c, hc_fix, n, hn, hcn⟩ := coprime_fixedPoints_quotient hCop hSolv hN hg_fix
    refine Subgroup.mem_map.mpr ⟨c, Subgroup.mem_fixedPointsOfMulAut.mpr hc_fix, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hcn]
    simpa using N.inv_mem hn
  · rw [Subgroup.map_le_iff_le_comap]
    intro c hc
    rw [Subgroup.mem_fixedPointsOfMulAut] at hc
    rw [Subgroup.mem_comap, Subgroup.mem_fixedPointsOfMulAut]
    intro a
    rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk', hc a]

/-- An `A`-invariant subgroup maps to an invariant subgroup in an
`A`-invariant quotient. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.map_quotient
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N)
    {H : Subgroup G} (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) :
    OddOrder.Isaacs.Ch03.IsAInvariant
      (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN)
      (H.map (QuotientGroup.mk' N)) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a q hq
  rw [Subgroup.mem_map] at hq ⊢
  obtain ⟨g, hg, rfl⟩ := hq
  exact ⟨(φ a) g, hH.smul_mem a hg, by
    rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']⟩

/-- The preimage of an invariant subgroup of an `A`-invariant quotient is
invariant in the original group. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.comap_quotient
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N)
    {Y : Subgroup (G ⧸ N)}
    (hY : OddOrder.Isaacs.Ch03.IsAInvariant
      (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) Y) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (Y.comap (QuotientGroup.mk' N)) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a g hg
  rw [Subgroup.mem_comap] at hg ⊢
  rw [← OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
  exact hY.smul_mem a hg

/-- Pull back a quotient Hall subgroup containing the image of `K`.

The preimage is invariant, contains `K`, and has `π`-free index. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.exists_comap_quotient_hall
    {G A : Type*} [Group G] [Finite G] [Group A] {φ : A →* MulAut G}
    {π : Set ℕ} {K M : Subgroup G} [M.Normal]
    (hM : OddOrder.Isaacs.Ch03.IsAInvariant φ M)
    {Hbar : Subgroup (G ⧸ M)}
    (hHbar_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup π Hbar)
    (hHbar_inv : OddOrder.Isaacs.Ch03.IsAInvariant
      (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hM) Hbar)
    (hK_image_le : K.map (QuotientGroup.mk' M) ≤ Hbar) :
    ∃ H : Subgroup G,
      OddOrder.Isaacs.Ch03.IsAInvariant φ H ∧ K ≤ H ∧
        (∀ p ∈ H.index.primeFactors, p ∉ π) ∧
        H = Hbar.comap (QuotientGroup.mk' M) := by
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let H : Subgroup G := Hbar.comap q
  refine ⟨H, ?_, ?_, ?_, rfl⟩
  · exact OddOrder.Isaacs.Ch03.IsAInvariant.comap_quotient hM hHbar_inv
  · intro k hk
    change q k ∈ Hbar
    exact hK_image_le (by
      rw [Subgroup.mem_map]
      exact ⟨k, hk, rfl⟩)
  · have hindex : H.index = Hbar.index :=
      Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective (N := M))
    rw [hindex]
    exact hHbar_hall.2

/-- The action commutator descends to quotients as the image of the action commutator. -/
theorem actionCommutator_quotient_eq_map
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) :
    actionCommutator (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) =
      (actionCommutator φ).map (QuotientGroup.mk' N) := by
  rw [actionCommutator, actionCommutator, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨q, a, rfl⟩
    refine QuotientGroup.induction_on q ?_
    intro g
    refine ⟨g * (φ a) g⁻¹, ⟨g, a, rfl⟩, ?_⟩
    simp [map_mul]
  · rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk' N g, a, by simp [map_mul]⟩

/-- If `[G,A] ≤ N`, then the induced action on `G/N` is trivial. -/
theorem actionCommutator_quotient_eq_bot_of_le
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N)
    (h_le : actionCommutator φ ≤ N) :
    actionCommutator (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) = ⊥ := by
  rw [actionCommutator_eq_bot_iff_acts_trivially]
  intro a q
  refine QuotientGroup.induction_on q ?_
  intro g
  rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply]
  rw [QuotientGroup.eq]
  simpa [mul_inv_rev] using
    N.inv_mem ((actionCommutator_le_iff_left φ N).mp h_le a g)

/-- If `R` normalizes `K` and `⁅K, R⁆ ≤ F(K)`, then the conjugation action of `R`
on `K/F(K)` fixes every quotient element. -/
theorem fixedPoints_quotient_eq_top_of_commutator_le_fitting
    {G : Type*} [Group G] [Finite G] {K R : Subgroup G} [K.Normal]
    (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hcomm : ⁅K, R⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype) :
    Subgroup.fixedPointsOfMulAut
      (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom
        (OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic
          (H := OddOrder.Isaacs.Ch01.fitting ↥K)
          ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK)))) = ⊤ := by
  set φ : R →* MulAut K := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK)
    with hφ
  have hFinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (OddOrder.Isaacs.Ch01.fitting ↥K) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ
  have hac_le : actionCommutator φ ≤ OddOrder.Isaacs.Ch01.fitting ↥K := by
    have h := actionCommutator_conj_map_subtype hRK
    rw [← h] at hcomm
    exact Subgroup.map_le_map_iff_of_injective K.subtype_injective |>.mp hcomm
  have hbot : actionCommutator (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hFinv) =
      ⊥ := by
    rw [actionCommutator_quotient_eq_map, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hac_le
  rw [Subgroup.eq_top_iff']
  intro g
  rw [Subgroup.mem_fixedPointsOfMulAut]
  intro a
  exact (actionCommutator_eq_bot_iff_acts_trivially _).mp hbot a g

/-- **Isaacs Corollary 4.21**: For `H ≤ G`, the following are equivalent:
(a) `∀ a x, (φ a) x ∈ Hx` (right coset is A-invariant in element form);
(b) `∀ a x, (φ a) x ∈ xH` (left coset is A-invariant in element form);
(c) `actionCommutator φ ≤ H`.

Element-level: (a) = `∀ a x, (φ a) x * x⁻¹ ∈ H`, (b) = `∀ a x, x⁻¹ * (φ a) x ∈ H`. -/
theorem actionCommutator_le_iff_TFAE {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) (H : Subgroup G) :
    List.TFAE [
      actionCommutator φ ≤ H,
      ∀ a : A, ∀ x : G, (φ a) x * x⁻¹ ∈ H,
      ∀ a : A, ∀ x : G, x⁻¹ * (φ a) x ∈ H] := by
  tfae_have 1 ↔ 2 := actionCommutator_le_iff φ H
  tfae_have 1 ↔ 3 := actionCommutator_le_iff_left φ H
  tfae_finish

/-- **Isaacs Cor 4.21 corollary**: If `actionCommutator φ ≤ H`, then `H` is `A`-invariant.
(Because `(φ a) h = ((φ a) h * h⁻¹) * h` and the first factor is in `H` by Lem 4.20.) -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.of_actionCommutator_le
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {H : Subgroup G} (h_le : actionCommutator φ ≤ H) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ H := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a h hh
  -- (φ a) h ∈ H. Use: (φ a) h = ((φ a) h * h⁻¹) * h, both factors ∈ H.
  have h1 : (φ a) h * h⁻¹ ∈ H := (actionCommutator_le_iff φ H).mp h_le a h
  have h_eq : (φ a) h = ((φ a) h * h⁻¹) * h := by group
  rw [h_eq]
  exact H.mul_mem h1 hh

/-- **Isaacs Lemma 4.25** ⭐: If `A` acts trivially on `actionCommutator φ` (i.e.,
`[G, A, A] = 1`), then `actionCommutator φ` is abelian.

**証明戦略** (Isaacs p.135): Γ = G ⋊[φ] A 内で Three-subgroups lemma を適用.
- `H_Γ := ⁅inl(G).range, inr(A).range⁆` (Γ-内 commutator) `= inl(actionCommutator)`
  (`actionCommutator_map_inl`).
- 仮説 ⇒ Γ で `⁅H_Γ, inr(A).range⁆ = ⊥` (各生成元 `⁅inl k, inr a⁆ = inl(k * (φ a) k⁻¹)`
  で `(φ a) k = k` から `= inl 1 = 1`).
- `H_Γ.Normal` (Lem 4.1 系) ⇒ `⁅H_Γ, inl(G).range⁆ ≤ H_Γ` ⇒ 二重交換子も `⊥`.
- Three-subgroups で `⁅⁅inl(G).range, inr(A).range⁆, H_Γ⁆ = ⁅H_Γ, H_Γ⁆ = ⊥`.
- `inl` 単射で pull back. -/
theorem actionCommutator_commutator_eq_bot_of_acts_trivially
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G)
    (h_triv : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut φ) :
    ⁅actionCommutator φ, actionCommutator φ⁆ = ⊥ := by
  -- Setup: work in Γ = G ⋊[φ] A
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  set H_Γ : Subgroup (G ⋊[φ] A) := ⁅XG, YA⁆ with hHΓ_def
  -- H_Γ = inl(actionCommutator)
  have h_HΓ_eq : (actionCommutator φ).map SemidirectProduct.inl = H_Γ :=
    actionCommutator_map_inl φ
  -- H_Γ is Normal in Γ (Lem 4.1 系 via inl ⊔ inr = ⊤)
  haveI h_HΓ_normal : H_Γ.Normal := commutator_normal_of_sup_eq_top
    SemidirectProduct.inl_range_sup_inr_range_eq_top
  -- Step 1: ⁅H_Γ, YA⁆ = ⊥ in Γ (from hypothesis, via generator computation)
  have h_step1 : ⁅H_Γ, YA⁆ = ⊥ := by
    rw [← h_HΓ_eq, eq_bot_iff, Subgroup.commutator_le]
    rintro _ ⟨k, hk, rfl⟩ _ ⟨a, rfl⟩
    -- Goal: ⁅inl k, inr a⁆ ∈ ⊥
    rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
    -- Goal: inl (k * (φ a) k⁻¹) = 1
    have h_fix : (φ a) k = k := h_triv hk a
    rw [show (φ a) k⁻¹ = ((φ a) k)⁻¹ from map_inv (φ a) k, h_fix, mul_inv_cancel]
    exact map_one _
  -- Step 2: ⁅⁅H_Γ, XG⁆, YA⁆ = ⊥ (via H_Γ.Normal ⇒ ⁅H_Γ, XG⁆ ≤ H_Γ, then Step 1)
  have h_step2 : ⁅⁅H_Γ, XG⁆, YA⁆ = ⊥ := by
    have h_inner_le : ⁅H_Γ, XG⁆ ≤ H_Γ := Subgroup.commutator_le_left H_Γ XG
    exact le_bot_iff.mp <|
      le_trans (Subgroup.commutator_mono h_inner_le le_rfl) h_step1.le
  -- Step 3: Three-subgroups in Γ
  -- With H₁ = XG, H₂ = YA, H₃ = H_Γ:
  -- ⁅⁅H₂, H₃⁆, H₁⁆ = ⁅⁅YA, H_Γ⁆, XG⁆ = ⁅⊥, XG⁆ = ⊥ (step 1 + commutator_comm)
  -- ⁅⁅H₃, H₁⁆, H₂⁆ = ⁅⁅H_Γ, XG⁆, YA⁆ = ⊥ (step 2)
  -- Conclude: ⁅⁅H₁, H₂⁆, H₃⁆ = ⁅⁅XG, YA⁆, H_Γ⁆ = ⁅H_Γ, H_Γ⁆ = ⊥
  have h_step3 : ⁅H_Γ, H_Γ⁆ = ⊥ := by
    have h_a : ⁅⁅YA, H_Γ⁆, XG⁆ = ⊥ := by
      rw [Subgroup.commutator_comm YA H_Γ, h_step1, Subgroup.commutator_bot_left]
    have h_b : ⁅⁅H_Γ, XG⁆, YA⁆ = ⊥ := h_step2
    have h_three := Subgroup.commutator_commutator_eq_bot_of_rotate h_a h_b
    -- h_three : ⁅⁅XG, YA⁆, H_Γ⁆ = ⊥
    rwa [← hHΓ_def] at h_three
  -- Step 4: Pull back ⁅H_Γ, H_Γ⁆ = ⊥ via inl injectivity to actionCommutator
  have h_inl_comm : (⁅actionCommutator φ, actionCommutator φ⁆).map
      SemidirectProduct.inl = ⁅H_Γ, H_Γ⁆ := by
    rw [Subgroup.map_commutator, h_HΓ_eq]
  have h_map_bot : (⁅actionCommutator φ, actionCommutator φ⁆).map
      SemidirectProduct.inl = ⊥ := h_inl_comm.trans h_step3
  exact (Subgroup.map_eq_bot_iff_of_injective ⁅actionCommutator φ, actionCommutator φ⁆
        SemidirectProduct.inl_injective).mp h_map_bot

/-! ### Isaacs §4C: 連鎖仮定下の A の構造 (Thm 4.22, Cor 4.23) -/

/-- **Bridge lemma** (semidirect product): `K ≤ φ.ker` iff `⁅K.map inr, inl(G).range⁆ = ⊥`
in `Γ = G ⋊[φ] A`. つまり `K ≤ A` が trivial action ↔ `inr(K)` と `inl(G)` が可換.

**証明**: `Subgroup.commutator_eq_bot_iff_le_centralizer` で commutator = ⊥ ↔ centralizer
包含, さらに semidirect product の `inl_aut` (`inl ((φ a) g) = inr a * inl g * inr a⁻¹`)
で `inr(k)` と `inl(g)` が可換 ↔ `(φ k) g = g`. -/
theorem _root_.SemidirectProduct.commutator_inr_inl_range_eq_bot_iff_le_ker
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G} (K : Subgroup A) :
    ⁅K.map (SemidirectProduct.inr : A →* G ⋊[φ] A),
      (SemidirectProduct.inl : G →* G ⋊[φ] A).range⁆ = ⊥ ↔ K ≤ φ.ker := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  constructor
  · -- K.map inr ≤ centralizer inl.range ⇒ K ≤ ker φ
    intro h k hk
    -- k ∈ K. Want φ k = 1, i.e., (φ k) g = g for all g.
    rw [MonoidHom.mem_ker]
    -- Use MulEquiv.ext for (φ k) = 1
    refine MulEquiv.ext fun g => ?_
    -- Goal: (φ k) g = (1 : MulAut G) g = g
    rw [MulAut.one_apply]
    have h_mem : (SemidirectProduct.inr k : G ⋊[φ] A) ∈
        K.map (SemidirectProduct.inr : A →* G ⋊[φ] A) := ⟨k, hk, rfl⟩
    have h_centr := h h_mem
    rw [Subgroup.mem_centralizer_iff] at h_centr
    have h_comm := h_centr (SemidirectProduct.inl g : G ⋊[φ] A) ⟨g, rfl⟩
    -- h_comm : inl g * inr k = inr k * inl g
    have h_aut : (SemidirectProduct.inr k : G ⋊[φ] A) * SemidirectProduct.inl g =
        (SemidirectProduct.inl ((φ k) g) : G ⋊[φ] A) * SemidirectProduct.inr k := by
      have hi := SemidirectProduct.inl_aut (φ := φ) k g
      have h_inv : (SemidirectProduct.inr k⁻¹ : G ⋊[φ] A) = (SemidirectProduct.inr k)⁻¹ :=
        map_inv SemidirectProduct.inr k
      rw [hi, h_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [h_aut] at h_comm
    -- h_comm : inl g * inr k = inl ((φ k) g) * inr k
    have h_eq : (SemidirectProduct.inl g : G ⋊[φ] A) = SemidirectProduct.inl ((φ k) g) :=
      mul_right_cancel h_comm
    exact (SemidirectProduct.inl_injective h_eq).symm
  · -- K ≤ ker φ ⇒ K.map inr ≤ centralizer inl.range
    intro h y hy
    rw [Subgroup.mem_centralizer_iff]
    obtain ⟨k, hk, rfl⟩ := hy
    have h_fix : φ k = 1 := h hk
    intro x hx
    obtain ⟨g, rfl⟩ := hx
    -- Goal: inl g * inr k = inr k * inl g
    have h_aut : (SemidirectProduct.inr k : G ⋊[φ] A) * SemidirectProduct.inl g =
        (SemidirectProduct.inl ((φ k) g) : G ⋊[φ] A) * SemidirectProduct.inr k := by
      have hi := SemidirectProduct.inl_aut (φ := φ) k g
      have h_inv : (SemidirectProduct.inr k⁻¹ : G ⋊[φ] A) = (SemidirectProduct.inr k)⁻¹ :=
        map_inv SemidirectProduct.inr k
      rw [hi, h_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [h_aut, h_fix, MulAut.one_apply]

/-- **Isaacs Corollary 4.23**: A が `G` に faithful 作用 + `[G, A, A] = 1`
(`actionCommutator φ ≤ fixedPointsOfMulAut φ`) ⇒ `commutator A ≤ φ.ker`.

**Faithful case**: φ injective ⇒ φ.ker = ⊥ ⇒ commutator A = ⊥ ⇒ A abelian.

**証明戦略** (Three-subgroups in Γ = G ⋊[φ] A, m = 2 specialization of Thm 4.22):
仮定 ⇒ `⁅⁅inl(G), inr(A)⁆, inr(A)⁆ = ⊥` (= `[G, A, A] = 1` in Γ). Three-subgroups で
`⁅⁅inr(A), inr(A)⁆, inl(G)⁆ = ⊥` (= `[A, A, G] = 1`). これは `inr(A')` と
`inl(G)` の交換子 = ⊥, つまり bridge lemma で `commutator A ≤ φ.ker`. -/
theorem commutator_le_ker_of_acts_trivially_on_actionCommutator
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G)
    (h_triv : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut φ) :
    _root_.commutator A ≤ φ.ker := by
  -- Setup in Γ = G ⋊[φ] A
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range with hXG
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range with hYA
  -- Hypothesis ⇒ ⁅⁅XG, YA⁆, YA⁆ = ⊥ in Γ
  -- (Same Step 1 as in Lem 4.25 / actionCommutator_commutator_eq_bot_of_acts_trivially)
  set H_Γ : Subgroup (G ⋊[φ] A) := ⁅XG, YA⁆
  have h_HΓ_eq : (actionCommutator φ).map SemidirectProduct.inl = H_Γ :=
    actionCommutator_map_inl φ
  have h_step1 : ⁅H_Γ, YA⁆ = ⊥ := by
    rw [← h_HΓ_eq, eq_bot_iff, Subgroup.commutator_le]
    rintro _ ⟨k, hk, rfl⟩ _ ⟨a, rfl⟩
    rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
    have h_fix : (φ a) k = k := h_triv hk a
    rw [show (φ a) k⁻¹ = ((φ a) k)⁻¹ from map_inv (φ a) k, h_fix, mul_inv_cancel]
    exact map_one _
  -- Apply three-subgroups in Γ with H₁ = YA, H₂ = YA, H₃ = XG
  -- (this gives ⁅⁅YA, YA⁆, XG⁆ = ⊥)
  have h_three : ⁅⁅YA, YA⁆, XG⁆ = ⊥ := by
    -- We need: ⁅⁅YA, XG⁆, YA⁆ = ⊥ and ⁅⁅XG, YA⁆, YA⁆ = ⊥, then conclude ⁅⁅YA, YA⁆, XG⁆ = ⊥.
    have h_a : ⁅⁅YA, XG⁆, YA⁆ = ⊥ := by
      rw [Subgroup.commutator_comm YA XG]
      exact h_step1
    have h_b : ⁅⁅XG, YA⁆, YA⁆ = ⊥ := h_step1
    -- mathlib three-subgroups: ⁅⁅H₂, H₃⁆, H₁⁆ = ⊥ → ⁅⁅H₃, H₁⁆, H₂⁆ = ⊥ → ⁅⁅H₁, H₂⁆, H₃⁆ = ⊥
    -- With H₁ = YA, H₂ = YA, H₃ = XG: gives ⁅⁅YA, YA⁆, XG⁆ = ⊥ from h_a + h_b.
    exact Subgroup.commutator_commutator_eq_bot_of_rotate h_a h_b
  -- Now convert ⁅⁅YA, YA⁆, XG⁆ = ⊥ to ⁅(commutator A).map inr, inl(G).range⁆ = ⊥
  rw [← SemidirectProduct.commutator_inr_inl_range_eq_bot_iff_le_ker]
  -- Goal: ⁅(commutator A).map inr, inl(G).range⁆ = ⊥
  have h_eq : (_root_.commutator A).map (SemidirectProduct.inr : A →* G ⋊[φ] A) = ⁅YA, YA⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator]
    -- ⁅⊤, ⊤⁆.map inr = ⁅(⊤).map inr, (⊤).map inr⁆ = ⁅inr.range, inr.range⁆
    rw [show ((⊤ : Subgroup A).map (SemidirectProduct.inr : A →* G ⋊[φ] A)) = YA from
        (MonoidHom.range_eq_map SemidirectProduct.inr).symm]
  rw [h_eq]
  exact h_three

/-- **Isaacs Cor 4.23 (faithful)**: A が `G` に faithful 作用 + `[G, A, A] = 1`
⇒ A is abelian (`commutator A = ⊥`).

`commutator_le_ker_of_acts_trivially_on_actionCommutator` の faithful 特殊化. -/
theorem commutator_eq_bot_of_acts_trivially_on_actionCommutator_of_faithful
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G)
    (h_inj : Function.Injective φ)
    (h_triv : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut φ) :
    _root_.commutator A = ⊥ := by
  have h_ker : φ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ).mpr h_inj
  have h_le : _root_.commutator A ≤ φ.ker :=
    commutator_le_ker_of_acts_trivially_on_actionCommutator φ h_triv
  rw [h_ker] at h_le
  exact le_bot_iff.mp h_le

/-! ### Isaacs §4C: Thm 4.22 (chain stabilization ⇒ A solvable) -/

/-- **Helper**: `iterCommutator (iterCommutator E X j) X k = iterCommutator E X (j + k)`.
-/
private lemma iterCommutator_add (E X : Subgroup G) (j k : ℕ) :
    iterCommutator (iterCommutator E X j) X k = iterCommutator E X (j + k) := by
  induction k with
  | zero => simp [iterCommutator_zero]
  | succ k ih =>
    rw [iterCommutator_succ, ih]
    rw [show j + (k + 1) = (j + k) + 1 from by omega, iterCommutator_succ]

/-- **Abstract subgroup form of Isaacs Theorem 4.22**: For subgroups `E X` of an
ambient group `H` with `X ≤ E.normalizer` and `iterCommutator E X m = ⊥` for `m ≥ 1`,
the `(m-1)`-th derived series of `X` (viewed in `H`) commutes trivially with `E`.

**証明** (induction on `m`):
- Base `m = 1`: `iter E X 1 = ⁅E, X⁆ = ⊥`. `derivedSeries ↥X 0 = ⊤`, `.map subtype = X`.
  Goal: `⁅X, E⁆ = ⊥` = `⁅E, X⁆ = ⊥` ✓.
- Step `m = k + 1 ≥ 2`: Set `E' := ⁅E, X⁆`. `X ≤ E'.normalizer`
  (Lem 4.3: `⁅E, X⁆ ≤ E` ⇒ `⁅⁅E, X⁆, X⁆ ≤ ⁅E, X⁆`).
  `iter E' X k = iter E X (k+1) = ⊥` (helper). IH ⇒ `⁅D, E'⁆ = ⊥` where
  `D := (derivedSeries ↥X (k-1)).map subtype`.
  Three-subgroups with `H₁ = H₂ = D, H₃ = E`:
  * `⁅⁅D, E⁆, D⁆ ≤ ⁅⁅E, X⁆, D⁆ = ⁅D, ⁅E, X⁆⁆ = ⊥` (IH + comm)
  * `⁅⁅E, D⁆, D⁆ ≤ ⁅⁅E, X⁆, D⁆ = ⊥` (same)
  * ⇒ `⁅⁅D, D⁆, E⁆ = ⊥` (Three-subgroups).
  `⁅D, D⁆ = (⁅derivedSeries (k-1), derivedSeries (k-1)⁆).map subtype =
    (derivedSeries ↥X k).map subtype`. ✓ -/
theorem derivedSeries_subtype_commutator_eq_bot_of_iter_eq_bot
    {H : Type*} [Group H] {X : Subgroup H} (m : ℕ) (hm : 1 ≤ m) :
    ∀ {E : Subgroup H}, X ≤ Subgroup.normalizer E →
      iterCommutator E X m = ⊥ →
      ⁅((derivedSeries (↥X) (m - 1)).map X.subtype), E⁆ = ⊥ := by
  induction m with
  | zero => omega
  | succ k ih =>
    intro E h_norm h_iter
    rcases Nat.eq_zero_or_pos k with hk | hk
    · -- m = 1 base case (k = 0)
      subst hk
      -- derivedSeries (1-1) = derivedSeries 0 = ⊤, .map subtype = X
      have h_top : (⊤ : Subgroup ↥X).map X.subtype = X :=
        (MonoidHom.range_eq_map X.subtype).symm.trans X.range_subtype
      have h_idx : (0 + 1 : ℕ) - 1 = 0 := by omega
      rw [h_idx, derivedSeries_zero, h_top]
      -- Goal: ⁅X, E⁆ = ⊥. Hyp: iter E X 1 = ⁅E, X⁆ = ⊥.
      rw [Subgroup.commutator_comm]
      have h1 : iterCommutator E X (0 + 1) = ⁅E, X⁆ := by
        rw [iterCommutator_succ, iterCommutator_zero]
      rw [← h1]; exact h_iter
    · -- m = k + 1 ≥ 2 (k ≥ 1)
      have hk_le : 1 ≤ k := hk
      -- E' := ⁅E, X⁆
      set E' : Subgroup H := ⁅E, X⁆ with hE'_def
      -- X normalizes E'
      have h_norm_E' : X ≤ Subgroup.normalizer E' := by
        rw [← commutator_le_iff_le_normalizer]
        refine Subgroup.commutator_mono ?_ le_rfl
        exact commutator_le_iff_le_normalizer.mpr h_norm
      -- iter E' X k = iter E X (k+1) = ⊥
      have h_iter_E' : iterCommutator E' X k = ⊥ := by
        show iterCommutator (iterCommutator E X 1) X k = ⊥
        rw [iterCommutator_add]
        convert h_iter using 2
        omega
      -- IH applied
      have h_IH : ⁅(derivedSeries ↥X (k - 1)).map X.subtype, E'⁆ = ⊥ :=
        ih hk_le h_norm_E' h_iter_E'
      set D : Subgroup H := (derivedSeries ↥X (k - 1)).map X.subtype with hD_def
      -- D ≤ X
      have hD_le_X : D ≤ X := by
        rw [hD_def]
        exact (Subgroup.map_mono le_top).trans
          ((MonoidHom.range_eq_map X.subtype).symm.trans X.range_subtype).le
      -- ⁅D, ⁅E, X⁆⁆ = ⊥ from IH
      -- Three-subgroups in ambient H: H₁ = D, H₂ = D, H₃ = E
      have h_DE : ⁅⁅D, E⁆, D⁆ = ⊥ := by
        have h_le1 : ⁅D, E⁆ ≤ ⁅X, E⁆ := Subgroup.commutator_mono hD_le_X le_rfl
        have h_le2 : ⁅⁅D, E⁆, D⁆ ≤ ⁅⁅X, E⁆, D⁆ := Subgroup.commutator_mono h_le1 le_rfl
        have h_swap : ⁅⁅X, E⁆, D⁆ = ⁅D, ⁅E, X⁆⁆ := by
          rw [Subgroup.commutator_comm X E, Subgroup.commutator_comm ⁅E, X⁆ D]
        rw [h_swap] at h_le2
        exact le_bot_iff.mp (h_le2.trans h_IH.le)
      have h_ED : ⁅⁅E, D⁆, D⁆ = ⊥ := by
        rw [Subgroup.commutator_comm E D]
        exact h_DE
      -- Three-subgroups: gives ⁅⁅D, D⁆, E⁆ = ⊥
      have h_DDE : ⁅⁅D, D⁆, E⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate h_DE h_ED
      -- ⁅D, D⁆ = ((derivedSeries ↥X k)).map subtype
      have h_DD : (⁅D, D⁆ : Subgroup H) =
          (derivedSeries (↥X) k).map X.subtype := by
        rw [hD_def, ← Subgroup.map_commutator]
        congr 1
        rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel hk_le).symm,
            derivedSeries_succ]
        congr 2 <;> omega
      show ⁅(derivedSeries ↥X (k + 1 - 1)).map X.subtype, E⁆ = ⊥
      rw [show k + 1 - 1 = k from by omega]
      rw [← h_DD]
      exact h_DDE

/-- **Isaacs Theorem 4.22** ⭐: A 作用 + `[G, A, ..., A]_m = 1` ⇒
`derivedSeries A (m-1) ≤ φ.ker`. (faithful case: A is solvable with derived length ≤ m-1.)

Semidirect product `Γ = G ⋊[φ] A` 形で記述: iter (inl(G).range) (inr(A).range) m = ⊥
⇒ derivedSeries A (m-1) ≤ φ.ker. -/
theorem derivedSeries_le_ker_of_iter_inl_inr_eq_bot
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) (m : ℕ) (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
                             (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    derivedSeries A (m - 1) ≤ φ.ker := by
  -- Apply abstract form with X = inr(A).range, E = inl(G).range
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  haveI hXG_normal : XG.Normal := OddOrder.Isaacs.Ch03.inl_range_normal φ
  -- YA ≤ Subgroup.normalizer XG (XG normal ⇒ normalizer = ⊤)
  have h_norm : YA ≤ Subgroup.normalizer XG := by
    intro y _
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hXG_normal.conj_mem _ hz y, fun hz => ?_⟩
    have h1 := hXG_normal.conj_mem _ hz y⁻¹
    -- h1 : y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ ∈ XG, simplifies to z ∈ XG via group
    rwa [show y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z by group] at h1
  have h_abs := derivedSeries_subtype_commutator_eq_bot_of_iter_eq_bot
    (X := YA) m hm h_norm h_iter
  -- Bridge: ⁅(derivedSeries A (m-1)).map inr, XG⁆ = ⊥ ⇔ derivedSeries A (m-1) ≤ φ.ker
  rw [← SemidirectProduct.commutator_inr_inl_range_eq_bot_iff_le_ker]
  -- Transport: (derivedSeries A (m-1)).map inr = (derivedSeries ↥YA (m-1)).map YA.subtype
  have h_transport : ((derivedSeries A (m - 1)).map
      (SemidirectProduct.inr : A →* G ⋊[φ] A)) =
      (derivedSeries (↥YA) (m - 1)).map YA.subtype := by
    have h_factor : (SemidirectProduct.inr : A →* G ⋊[φ] A) =
        YA.subtype.comp (SemidirectProduct.inr (φ := φ)).rangeRestrict :=
      (MonoidHom.subtype_comp_rangeRestrict _).symm
    rw [h_factor, ← Subgroup.map_map]
    congr 1
    have h_surj : Function.Surjective (SemidirectProduct.inr (φ := φ)).rangeRestrict :=
      (SemidirectProduct.inr : A →* G ⋊[φ] A).rangeRestrict_surjective
    exact map_derivedSeries_eq h_surj (m - 1)
  rw [h_transport]
  exact h_abs

/-- **Isaacs Theorem 4.22 (faithful)**: A が `G` に faithful 作用 +
`iter (inl(G).range) (inr(A).range) m = ⊥` (= `[G, A, ..., A]_m = 1`)
⇒ A is solvable with derived length ≤ m - 1 (`derivedSeries A (m-1) = ⊥`). -/
theorem derivedSeries_eq_bot_of_iter_inl_inr_eq_bot_of_faithful
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G)
    (h_inj : Function.Injective φ) (m : ℕ) (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
                             (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    derivedSeries A (m - 1) = ⊥ := by
  have h_ker : φ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ).mpr h_inj
  have h_le := derivedSeries_le_ker_of_iter_inl_inr_eq_bot φ m hm h_iter
  rw [h_ker] at h_le
  exact le_bot_iff.mp h_le

private lemma iterCommutator_eq_inl_range_of_actionCommutator_eq_top
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G)
    (h_top : actionCommutator φ = ⊤) :
    ∀ {m : ℕ}, 1 ≤ m →
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m =
      (SemidirectProduct.inl : G →* G ⋊[φ] A).range := by
  intro m hm
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  have h_one : iterCommutator XG YA 1 = XG := by
    change ⁅XG, YA⁆ = XG
    rw [← actionCommutator_map_inl (φ := φ), h_top]
    simpa [XG] using
      (MonoidHom.range_eq_map (SemidirectProduct.inl : G →* G ⋊[φ] A)).symm
  induction m with
  | zero => omega
  | succ n ih =>
      rcases n with _ | n
      · exact h_one
      · have hn : 1 ≤ n + 1 := by omega
        rw [iterCommutator_succ, ih hn]
        exact h_one

private lemma actionCommutator_eq_bot_of_eq_top_iterCommutator_eq_bot
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G)
    {m : ℕ} (hm : 1 ≤ m)
    (h_top : actionCommutator φ = ⊤)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    actionCommutator φ = ⊥ := by
  have h_m :=
    iterCommutator_eq_inl_range_of_actionCommutator_eq_top φ h_top hm
  have hX_bot : (SemidirectProduct.inl : G →* G ⋊[φ] A).range = ⊥ := by
    rw [← h_m, h_iter]
  have h_map_bot : (actionCommutator φ).map
      (SemidirectProduct.inl : G →* G ⋊[φ] A) = ⊥ := by
    rw [actionCommutator_map_inl, hX_bot]
    simp
  exact (Subgroup.map_eq_bot_iff_of_injective
    (actionCommutator φ) SemidirectProduct.inl_injective).mp h_map_bot

/-! ### Isaacs §4D Lem 4.28 ⭐ (BG Prop 1.6(a)): G = C_G(A) · [G,A] for coprime + solvable -/

/-- **Isaacs Lemma 4.28** ⭐ (= BG Prop 1.6(a), **FT クリティカル**):
A acts on G via φ. Coprime (`|A|, |G|`) + one of A or G solvable ⇒
`fixedPointsOfMulAut φ ⊔ actionCommutator φ = ⊤` (= `G = C_G(A) · [G, A]`).

**証明** (Isaacs p.138, ~6 lines): Write `Ḡ = G / [G, A]`. By Cor 3.28 (coprime fixed points
come from G fixed points), `C_Ḡ(A) = image of C_G(A) under quotient`. But A acts trivially
on `Ḡ` (definition of `[G, A]` ⇒ `A` fixes every coset, so `C_Ḡ(A) = Ḡ`).
Hence `image of C_G(A) = Ḡ`, i.e., `C_G(A) ⊔ [G, A] = G`.

**Lean 化**: 各 `g ∈ G`, Cor 3.28 を `N = [G, A]` で適用 ⇒ ∃ `c ∈ C_G(A), c ∈ g · [G, A]`,
i.e., `c = g * n` for `n ∈ [G, A]`. Then `g = c * n⁻¹ ∈ C_G(A) * [G, A]`. -/
theorem fixedPoints_sup_actionCommutator_eq_top
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : IsSolvable A ∨ IsSolvable G) :
    Subgroup.fixedPointsOfMulAut φ ⊔ actionCommutator φ = ⊤ := by
  rw [eq_top_iff]
  intro g _
  -- Setup: N := actionCommutator φ, which is normal and A-invariant
  have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutator φ) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator φ
  -- For every a ∈ A, (φ a) g = g * n with n := g⁻¹ * (φ a) g ∈ actionCommutator
  -- (Lem 4.20 left form: actionCommutator ≤ actionCommutator gives this)
  have hg_fix : ∀ a : A, ∃ n ∈ actionCommutator φ, (φ a) g = g * n := by
    intro a
    refine ⟨g⁻¹ * (φ a) g, ?_, ?_⟩
    · exact (actionCommutator_le_iff_left φ (actionCommutator φ)).mp le_rfl a g
    · group
  -- Apply Cor 3.28: ∃ c ∈ C_G(A), c ∈ g · actionCommutator
  obtain ⟨c, hc_fix, ⟨n, hn_mem, hc_eq⟩⟩ :=
    coprime_fixedPoints_quotient hCop hSolv hN_inv hg_fix
  -- c ∈ fixedPointsOfMulAut, n⁻¹ ∈ actionCommutator
  have hc_mem : c ∈ Subgroup.fixedPointsOfMulAut φ := hc_fix
  -- g = c * n⁻¹: from hc_eq : c = g * n, so g = c * n⁻¹
  have hg_eq : g = c * n⁻¹ := by rw [hc_eq]; group
  -- g ∈ fixedPointsOfMulAut * actionCommutator ⊆ sup
  rw [hg_eq]
  exact Subgroup.mul_mem_sup hc_mem ((actionCommutator φ).inv_mem hn_mem)

/-! ### Isaacs §4D Lem 4.29 ⭐ (BG Prop 1.6(b)): [G, A, A] = [G, A] for coprime + solvable -/

/-- **Isaacs Lemma 4.29** (Γ form) ⭐: coprime + (A or G solvable) ⇒
`iterCommutator inl(G).range inr(A).range 2 = iterCommutator inl(G).range inr(A).range 1`
in Γ = G ⋊[φ] A. Equivalent (Isaacs notation): `[G, A, A] = [G, A]`.

**証明** (Isaacs p.139): Each generator `⁅inl g, inr a⁆` of [G, A]_Γ is in [G, A, A]_Γ.
By Lem 4.28: g = c * x with c ∈ C_G(A), x ∈ actionCommutator.
- `⁅inl c, inr a⁆ = 1` (c ∈ C_G(A) ⇒ inl c and inr a commute in Γ).
- Commutator identity: `⁅inl c · inl x, inr a⁆ = inl c · ⁅inl x, inr a⁆ · inl c⁻¹ · ⁅inl c, inr a⁆`
  `= inl c · ⁅inl x, inr a⁆ · inl c⁻¹`.
- Conjugate by inl c (= conjugate_commutatorElement): `= ⁅inl(cxc⁻¹), inr a⁆` (using
  inl c commutes with inr a).
- `cxc⁻¹ ∈ actionCommutator` (G-normal), so `inl(cxc⁻¹) ∈ inl(actionCommutator) = [G, A]_Γ`
  (`actionCommutator_map_inl`).
- Hence `⁅inl(cxc⁻¹), inr a⁆ ∈ ⁅[G, A]_Γ, inr(A).range⁆ = [G, A, A]_Γ`. -/
theorem iterCommutator_inl_inr_two_eq_one
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : IsSolvable A ∨ IsSolvable G) :
    iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
                   (SemidirectProduct.inr : A →* G ⋊[φ] A).range 2 =
    iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
                   (SemidirectProduct.inr : A →* G ⋊[φ] A).range 1 := by
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  -- I1 = ⁅XG, YA⁆ = [G, A]_Γ, I2 = ⁅I1, YA⁆ = [G, A, A]_Γ
  -- I1.Normal in Γ (Lem 4.1 系 via XG ⊔ YA = ⊤)
  haveI hI1_normal : (⁅XG, YA⁆).Normal :=
    commutator_normal_of_sup_eq_top SemidirectProduct.inl_range_sup_inr_range_eq_top
  refine le_antisymm ?_ ?_
  · -- I2 ≤ I1 (trivial: I1 normal in Γ, so ⁅I1, F⁆ ≤ I1)
    show iterCommutator XG YA 2 ≤ iterCommutator XG YA 1
    show ⁅iterCommutator XG YA 1, YA⁆ ≤ iterCommutator XG YA 1
    rw [show iterCommutator XG YA 1 = ⁅XG, YA⁆ from rfl]
    exact Subgroup.commutator_le_left _ _
  · -- I1 ≤ I2 (the substantive direction)
    show iterCommutator XG YA 1 ≤ iterCommutator XG YA 2
    show ⁅XG, YA⁆ ≤ ⁅iterCommutator XG YA 1, YA⁆
    rw [Subgroup.commutator_le]
    rintro _ ⟨g_0, rfl⟩ _ ⟨a, rfl⟩
    -- Goal: ⁅inl g_0, inr a⁆ ∈ ⁅iterCommutator XG YA 1, YA⁆
    -- By Lem 4.28: g_0 = c * x, c ∈ fixedPoints, x ∈ actionCommutator
    have h_top : g_0 ∈ Subgroup.fixedPointsOfMulAut φ ⊔ actionCommutator φ := by
      rw [fixedPoints_sup_actionCommutator_eq_top hCop hSolv]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_right] at h_top
    obtain ⟨c, hc_fix, x, hx_ac, h_eq⟩ := h_top
    -- h_eq : c * x = g_0
    have h_fix : (φ a) c = c := hc_fix a
    -- ⁅inl c, inr a⁆ = 1 (c ∈ fixedPoints ⇒ inl c commutes with inr a)
    have h_commute_ca : Commute (SemidirectProduct.inl c : G ⋊[φ] A)
        (SemidirectProduct.inr a) := by
      -- inl c · inr a = inr a · inl c iff (φ a) c = c (which holds by h_fix)
      show (SemidirectProduct.inl c : G ⋊[φ] A) * SemidirectProduct.inr a =
          SemidirectProduct.inr a * SemidirectProduct.inl c
      -- inr a * inl c * inr a⁻¹ = inl((φ a) c) = inl c (by inl_aut + h_fix)
      have h_aut := SemidirectProduct.inl_aut (φ := φ) a c
      rw [h_fix] at h_aut
      -- h_aut : inl c = inr a * inl c * inr a⁻¹
      -- Want: inl c * inr a = inr a * inl c
      -- From h_aut: inl c * inr a = (inr a * inl c * inr a⁻¹) * inr a
      --           = inr a * inl c * (inr a⁻¹ * inr a) = inr a * inl c
      have h_inv_eq : (SemidirectProduct.inr a⁻¹ : G ⋊[φ] A) =
          (SemidirectProduct.inr a)⁻¹ := map_inv SemidirectProduct.inr a
      rw [h_inv_eq] at h_aut
      rw [show (SemidirectProduct.inl c : G ⋊[φ] A) * SemidirectProduct.inr a =
            (SemidirectProduct.inr a * SemidirectProduct.inl c * (SemidirectProduct.inr a)⁻¹) *
              SemidirectProduct.inr a from by rw [← h_aut]]
      group
    have h_comm_ca_eq_one : ⁅(SemidirectProduct.inl c : G ⋊[φ] A),
        SemidirectProduct.inr a⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr h_commute_ca
    -- Goal: ⁅inl g_0, inr a⁆ ∈ ⁅⁅XG, YA⁆, YA⁆
    -- g_0 = c * x, so inl g_0 = inl c * inl x. Use commutator identity.
    rw [← h_eq, map_mul SemidirectProduct.inl]
    -- Goal: ⁅inl c * inl x, inr a⁆ ∈ ...
    -- Identity: ⁅cx, a⁆ = c · ⁅x, a⁆ · c⁻¹ · ⁅c, a⁆
    have h_id : ⁅(SemidirectProduct.inl c * SemidirectProduct.inl x : G ⋊[φ] A),
        (SemidirectProduct.inr a : G ⋊[φ] A)⁆ =
        (SemidirectProduct.inl c : G ⋊[φ] A) *
          ⁅(SemidirectProduct.inl x : G ⋊[φ] A), SemidirectProduct.inr a⁆ *
          (SemidirectProduct.inl c)⁻¹ *
          ⁅(SemidirectProduct.inl c : G ⋊[φ] A), SemidirectProduct.inr a⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h_id, h_comm_ca_eq_one, mul_one]
    -- Goal: inl c * ⁅inl x, inr a⁆ * (inl c)⁻¹ ∈ ⁅⁅XG, YA⁆, YA⁆
    -- = ⁅inl c · inl x · (inl c)⁻¹, inl c · inr a · (inl c)⁻¹⁆ (conjugate_commutatorElement)
    -- inl c · inr a · (inl c)⁻¹ = inr a (commute)
    rw [conjugate_commutatorElement]
    have h_conj_ca : (SemidirectProduct.inl c : G ⋊[φ] A) * SemidirectProduct.inr a *
        (SemidirectProduct.inl c)⁻¹ = SemidirectProduct.inr a := by
      rw [show (SemidirectProduct.inl c : G ⋊[φ] A) * SemidirectProduct.inr a =
          SemidirectProduct.inr a * SemidirectProduct.inl c from h_commute_ca]
      group
    rw [h_conj_ca]
    -- Goal: ⁅inl c * inl x * (inl c)⁻¹, inr a⁆ ∈ ⁅⁅XG, YA⁆, YA⁆
    -- inl c * inl x * (inl c)⁻¹ = inl(c * x * c⁻¹) ∈ inl(actionCommutator) = ⁅XG, YA⁆
    have h_lift : (SemidirectProduct.inl c : G ⋊[φ] A) * SemidirectProduct.inl x *
        (SemidirectProduct.inl c)⁻¹ = SemidirectProduct.inl (c * x * c⁻¹) := by
      have h_inv : ((SemidirectProduct.inl c : G ⋊[φ] A))⁻¹ = SemidirectProduct.inl c⁻¹ :=
        (map_inv SemidirectProduct.inl c).symm
      rw [h_inv, ← map_mul, ← map_mul]
    rw [h_lift]
    -- c * x * c⁻¹ ∈ actionCommutator (G-normal)
    haveI : (actionCommutator φ).Normal := actionCommutator.normal φ
    have h_cxc_ac : c * x * c⁻¹ ∈ actionCommutator φ :=
      ‹(actionCommutator φ).Normal›.conj_mem _ hx_ac c
    -- inl(c * x * c⁻¹) ∈ (actionCommutator).map inl = ⁅XG, YA⁆ (= I1)
    have h_in_I1 : (SemidirectProduct.inl (c * x * c⁻¹) : G ⋊[φ] A) ∈ ⁅XG, YA⁆ := by
      have := actionCommutator_map_inl (φ := φ)
      rw [← this]
      exact ⟨c * x * c⁻¹, h_cxc_ac, rfl⟩
    exact Subgroup.commutator_mem_commutator h_in_I1 ⟨a, rfl⟩

private lemma iterCommutator_eq_one_of_two_eq_one
    {E F : Subgroup G}
    (h : iterCommutator E F 2 = iterCommutator E F 1) :
    ∀ {m : ℕ}, 1 ≤ m → iterCommutator E F m = iterCommutator E F 1 := by
  intro m hm
  induction m with
  | zero => omega
  | succ n ih =>
      rcases n with _ | n
      · rfl
      · have hn : 1 ≤ n + 1 := by omega
        rw [iterCommutator_succ, ih hn]
        simpa [iterCommutator_succ] using h

private theorem iterCommutator_inl_inr_restrict_eq_bot
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    (P : Subgroup A) {m : ℕ}
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    let ψ : P →* MulAut G := φ.comp P.subtype
    iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
        (SemidirectProduct.inr : P →* G ⋊[ψ] P).range m = ⊥ := by
  dsimp
  let ψ : P →* MulAut G := φ.comp P.subtype
  let F : G ⋊[ψ] P →* G ⋊[φ] A :=
    SemidirectProduct.map (MonoidHom.id G) P.subtype (fun p => by
      ext g
      rfl)
  let XGP : Subgroup (G ⋊[ψ] P) := (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
  let YPP : Subgroup (G ⋊[ψ] P) := (SemidirectProduct.inr : P →* G ⋊[ψ] P).range
  let XGA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  let YAA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  have hF_inj : Function.Injective F := by
    intro x y hxy
    ext
    · simpa [F] using congrArg (fun z : G ⋊[φ] A => z.left) hxy
    · simpa [F] using congrArg (fun z : G ⋊[φ] A => z.right) hxy
  have h_map_X : XGP.map F = XGA := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, by simp [F]⟩
    · rintro ⟨g, rfl⟩
      refine ⟨(SemidirectProduct.inl : G →* G ⋊[ψ] P) g, ⟨g, rfl⟩, ?_⟩
      simp [F]
  have h_map_Y : YPP.map F ≤ YAA := by
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact ⟨p.1, by simp [F]⟩
  have h_map_iter_all :
      ∀ n : ℕ, (iterCommutator XGP YPP n).map F ≤ iterCommutator XGA YAA n := by
    intro n
    induction n with
    | zero =>
        simpa [iterCommutator_zero] using h_map_X.le
    | succ n ih =>
        rw [iterCommutator_succ, iterCommutator_succ, Subgroup.map_commutator]
        exact Subgroup.commutator_mono ih h_map_Y
  have h_map_bot : (iterCommutator XGP YPP m).map F = ⊥ := by
    refine le_antisymm ?_ bot_le
    exact (h_map_iter_all m).trans (le_of_eq h_iter)
  exact (Subgroup.map_eq_bot_iff_of_injective (iterCommutator XGP YPP m) hF_inj).mp h_map_bot

private theorem iterCommutator_inl_inr_restrict_base_eq_bot
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {H : Subgroup G} (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) {m : ℕ}
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    let ψ : A →* MulAut H := OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH
    iterCommutator (SemidirectProduct.inl : H →* H ⋊[ψ] A).range
        (SemidirectProduct.inr : A →* H ⋊[ψ] A).range m = ⊥ := by
  dsimp
  let ψ : A →* MulAut H := OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH
  let F : H ⋊[ψ] A →* G ⋊[φ] A :=
    SemidirectProduct.map H.subtype (MonoidHom.id A) (fun a => by
      ext h
      rfl)
  let XH : Subgroup (H ⋊[ψ] A) := (SemidirectProduct.inl : H →* H ⋊[ψ] A).range
  let YA_H : Subgroup (H ⋊[ψ] A) := (SemidirectProduct.inr : A →* H ⋊[ψ] A).range
  let XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  let YA_G : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  have hF_inj : Function.Injective F := by
    intro x y hxy
    ext
    · simpa [F] using congrArg (fun z : G ⋊[φ] A => z.left) hxy
    · simpa [F] using congrArg (fun z : G ⋊[φ] A => z.right) hxy
  have h_map_X : XH.map F ≤ XG := by
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    exact ⟨h.1, by simp [F]⟩
  have h_map_Y : YA_H.map F ≤ YA_G := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, by simp [F]⟩
  have h_map_iter_all :
      ∀ n : ℕ, (iterCommutator XH YA_H n).map F ≤ iterCommutator XG YA_G n := by
    intro n
    induction n with
    | zero =>
        simpa [iterCommutator_zero] using h_map_X
    | succ n ih =>
        rw [iterCommutator_succ, iterCommutator_succ, Subgroup.map_commutator]
        exact Subgroup.commutator_mono ih h_map_Y
  have h_map_bot : (iterCommutator XH YA_H m).map F = ⊥ := by
    refine le_antisymm ?_ bot_le
    exact (h_map_iter_all m).trans (le_of_eq h_iter)
  exact (Subgroup.map_eq_bot_iff_of_injective (iterCommutator XH YA_H m) hF_inj).mp h_map_bot

/-- **Isaacs Corollary 4.30**:
Let `A` act faithfully on the finite group `G`. If an iterated commutator
`[G, A, ..., A]` is trivial, then every prime divisor of `|A|` divides `|G|`.

Proof: for a prime `p ∤ |G|`, restrict the action to a Sylow `p`-subgroup `P ≤ A`.
The restricted action is coprime, and the chain hypothesis restricts from `A` to `P`.
Lemma 4.29 collapses the restricted iterated commutator to `[G, P] = 1`, so `P`
acts trivially. Faithfulness forces `P = 1`, hence `p ∤ |A|`. -/
theorem prime_dvd_card_of_faithful_iterCommutator_eq_bot
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    (φ : A →* MulAut G) (h_inj : Function.Injective φ)
    {m : ℕ} (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥)
    {p : ℕ} (hp : p.Prime) (hpA : p ∣ Nat.card A) :
    p ∣ Nat.card G := by
  by_contra hpG
  haveI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p A := default
  let ψ : P →* MulAut G := φ.comp (P : Subgroup A).subtype
  have h_iter_P :
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
          (SemidirectProduct.inr : P →* G ⋊[ψ] P).range m = ⊥ := by
    simpa [ψ] using
      iterCommutator_inl_inr_restrict_eq_bot (φ := φ) (P : Subgroup A) h_iter
  have hCop_PG : Nat.Coprime (Nat.card P) (Nat.card G) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpG)
  have hSolv : IsSolvable P ∨ IsSolvable G := by
    left
    haveI : Group.IsNilpotent P := P.isPGroup'.isNilpotent
    infer_instance
  have h_two :
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
          (SemidirectProduct.inr : P →* G ⋊[ψ] P).range 2 =
        iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
          (SemidirectProduct.inr : P →* G ⋊[ψ] P).range 1 :=
    iterCommutator_inl_inr_two_eq_one (φ := ψ) hCop_PG hSolv
  have h_iter_one :
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
          (SemidirectProduct.inr : P →* G ⋊[ψ] P).range 1 = ⊥ := by
    have h_m := iterCommutator_eq_one_of_two_eq_one h_two hm
    rw [h_m] at h_iter_P
    exact h_iter_P
  have hP_le_ker : (⊤ : Subgroup P) ≤ ψ.ker := by
    rw [← SemidirectProduct.commutator_inr_inl_range_eq_bot_iff_le_ker]
    rw [show (⊤ : Subgroup P).map (SemidirectProduct.inr : P →* G ⋊[ψ] P) =
        (SemidirectProduct.inr : P →* G ⋊[ψ] P).range from
        (MonoidHom.range_eq_map _).symm]
    rw [Subgroup.commutator_comm]
    exact h_iter_one
  have hP_bot : (P : Subgroup A) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    let x : P := ⟨a, ha⟩
    have hx_ker : x ∈ ψ.ker := hP_le_ker (Subgroup.mem_top x)
    rw [MonoidHom.mem_ker] at hx_ker
    have hφa : φ a = 1 := by
      simpa [ψ, x] using hx_ker
    exact h_inj (by simpa using hφa)
  exact (P.ne_bot_of_dvd_card hpA) hP_bot

private theorem actionCommutator_isPGroup_of_iter_eq_bot_aux
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (hA : IsPGroup p A) :
    ∀ n : ℕ, ∀ {G : Type*} [Group G] [Finite G],
      (φ : A →* MulAut G) → ∀ {m : ℕ}, 1 ≤ m →
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥ →
      Nat.card G ≤ n → IsPGroup p (actionCommutator φ) := by
  intro n
  induction n with
  | zero =>
      intro G _ _ φ m hm h_iter h_le
      exfalso
      exact Nat.not_succ_le_zero _ (Nat.card_pos.trans_le h_le)
  | succ n ih =>
      intro G _ _ φ m hm h_iter h_le
      by_cases htop : actionCommutator φ = ⊤
      · have hbot :=
          actionCommutator_eq_bot_of_eq_top_iterCommutator_eq_bot φ hm htop h_iter
        rw [hbot]
        exact IsPGroup.of_bot
      set N : Subgroup G := actionCommutator φ with hN_def
      have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ N := by
        simpa [N, hN_def] using OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator φ
      let ψN : A →* MulAut N := OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hN_inv
      have h_iter_N :
          iterCommutator (SemidirectProduct.inl : N →* N ⋊[ψN] A).range
              (SemidirectProduct.inr : A →* N ⋊[ψN] A).range m = ⊥ := by
        simpa [ψN] using
          iterCommutator_inl_inr_restrict_base_eq_bot (φ := φ) hN_inv h_iter
      have hN_card_lt : Nat.card N < Nat.card G := by
        exact subgroup_card_lt_card_of_ne_top (G := G) (H := N) (by simpa [N, hN_def] using htop)
      have hNA_pgroup : IsPGroup p (actionCommutator ψN) :=
        ih ψN hm h_iter_N (Nat.le_of_lt_succ (hN_card_lt.trans_le h_le))
      set U : Subgroup N := OddOrder.Isaacs.Ch01.opCore p N with hU_def
      set U_G : Subgroup G := U.map N.subtype with hUG_def
      haveI hUG_normal : U_G.Normal := by
        dsimp [U_G]
        infer_instance
      have hU_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ U_G := by
        simpa [U_G, hUG_def, U, hU_def] using
          (OddOrder.Isaacs.Ch03.IsAInvariant.map_subtype_of_characteristic
            (φ := φ) hN_inv (K := U))
      let q : G →* G ⧸ U_G := QuotientGroup.mk' U_G
      let φbar : A →* MulAut (G ⧸ U_G) :=
        OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hU_inv
      let Nbar : Subgroup (G ⧸ U_G) := N.map q
      have h_ac_bar : actionCommutator φbar = Nbar := by
        rw [actionCommutator_quotient_eq_map hU_inv]
      have hNA_le_U : actionCommutator ψN ≤ U := by
        haveI : (actionCommutator ψN).Normal := actionCommutator.normal ψN
        simpa [U, hU_def] using
          (OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore
            (N := actionCommutator ψN) hNA_pgroup)
      have hNbar_fixed : Nbar ≤ Subgroup.fixedPointsOfMulAut φbar := by
        rintro y ⟨g, hgN, rfl⟩ a
        change (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hU_inv a)
            (QuotientGroup.mk' U_G g) = QuotientGroup.mk' U_G g
        rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
        change (((φ a) g : G) : G ⧸ U_G) = (g : G ⧸ U_G)
        rw [QuotientGroup.eq]
        have hdeltaN :
            (⟨g, hgN⟩ : N)⁻¹ * (ψN a) ⟨g, hgN⟩ ∈ U :=
          (actionCommutator_le_iff_left ψN U).mp hNA_le_U a ⟨g, hgN⟩
        have hdeltaG : g⁻¹ * (φ a) g ∈ U_G := by
          refine ⟨(⟨g, hgN⟩ : N)⁻¹ * (ψN a) ⟨g, hgN⟩, hdeltaN, ?_⟩
          simp [ψN]
        simpa [mul_inv_rev] using U_G.inv_mem hdeltaG
      have h_comm_Nbar : ⁅Nbar, Nbar⁆ = ⊥ := by
        rw [← h_ac_bar]
        exact actionCommutator_commutator_eq_bot_of_acts_trivially φbar
          (by simpa [h_ac_bar] using hNbar_fixed)
      have hNbar_comm : IsMulCommutative Nbar :=
        Subgroup.le_centralizer_iff_isMulCommutative.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h_comm_Nbar)
      let f : N →* G ⧸ U_G := q.comp N.subtype
      have hf_ker : f.ker = U := by
        ext x
        change ((x.1 : G) : G ⧸ U_G) = 1 ↔ x ∈ U
        rw [QuotientGroup.eq_one_iff]
        constructor
        · intro hx
          rcases hx with ⟨u, huU, hu_eq⟩
          have hux : u = x := Subtype.ext hu_eq
          simpa [hux] using huU
        · intro hx
          exact ⟨x, hx, rfl⟩
      have hf_range : f.range = Nbar := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨x.1, x.2, rfl⟩
        · rintro ⟨g, hgN, rfl⟩
          exact ⟨⟨g, hgN⟩, rfl⟩
      have hOpQ0 : OddOrder.Isaacs.Ch01.opCore p (N ⧸ U) = ⊥ := by
        simpa [U, hU_def] using opCore_quotient_opCore_eq_bot (G := N) p
      let e : (N ⧸ U) ≃* Nbar :=
        (QuotientGroup.quotientMulEquivOfEq hf_ker.symm).trans
          ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hf_range))
      have hOpNbar : OddOrder.Isaacs.Ch01.opCore p Nbar = ⊥ :=
        opCore_eq_bot_of_mulEquiv e hOpQ0
      have hNbar_pi_top :
          OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)}
            (⊤ : Subgroup Nbar) := by
        letI : IsMulCommutative Nbar := hNbar_comm
        exact isPiGroup_compl_top_of_isMulCommutative_opCore_eq_bot
          (G := Nbar) (p := p) hOpNbar
      have hNbar_pi :
          OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} Nbar := by
        intro r hr
        exact hNbar_pi_top r (by simpa using hr)
      have hA_pi_top :
          OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) (⊤ : Subgroup A) :=
        isPiGroup_singleton_of_isPGroup (G := A) (H := ⊤) (hA.to_subgroup _)
      have hA_pi_card : ∀ r ∈ (Nat.card A).primeFactors, r ∈ ({p} : Set ℕ) := by
        intro r hr
        exact hA_pi_top r (by simpa using hr)
      have hCop : Nat.Coprime (Nat.card A) (Nat.card Nbar) :=
        OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
          Nat.card_pos.ne' Nat.card_pos.ne' hA_pi_card hNbar_pi
      have hSolv : IsSolvable A ∨ IsSolvable Nbar := by
        left
        haveI : Group.IsNilpotent A := hA.isNilpotent
        exact IsNilpotent.to_isSolvable
      have hNbar_inv : OddOrder.Isaacs.Ch03.IsAInvariant φbar Nbar := by
        rw [← h_ac_bar]
        exact OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator φbar
      have hphi_bar_triv : ∀ a : A, ∀ g : G ⧸ U_G, (φbar a) g = g := by
        intro a g
        have hg_fix : ∀ b : A, ∃ n ∈ Nbar, (φbar b) g = g * n := by
          intro b
          refine ⟨g⁻¹ * (φbar b) g, ?_, by group⟩
          exact (actionCommutator_le_iff_left φbar Nbar).mp (le_of_eq h_ac_bar) b g
        obtain ⟨c, hc_fix, ⟨n0, hn0, hc_eq⟩⟩ :=
          coprime_fixedPoints_quotient_of_coprime_normal
            hCop hSolv hNbar_inv hg_fix
        have hn0_fix : (φbar a) n0 = n0 := hNbar_fixed hn0 a
        have hc_fix_a := hc_fix a
        rw [hc_eq, map_mul, hn0_fix] at hc_fix_a
        exact mul_right_cancel hc_fix_a
      have hbar_bot : actionCommutator φbar = ⊥ :=
        (actionCommutator_eq_bot_iff_acts_trivially φbar).mpr hphi_bar_triv
      have hNbar_bot : Nbar = ⊥ := by
        rw [← h_ac_bar, hbar_bot]
      have hN_le_U : N ≤ U_G := by
        have hmap_bot : N.map q = ⊥ := by
          simpa [Nbar] using hNbar_bot
        have hle_ker : N ≤ q.ker := (Subgroup.map_eq_bot_iff N).mp hmap_bot
        simpa [q, QuotientGroup.ker_mk', U_G, hUG_def] using hle_ker
      have hU_pgroup : IsPGroup p U_G := by
        simpa [U_G, hUG_def, U, hU_def] using
          (OddOrder.Isaacs.Ch01.opCore_isPGroup p N).map N.subtype
      have hN_pgroup : IsPGroup p N :=
        hU_pgroup.of_injective (Subgroup.inclusion hN_le_U)
          (Subgroup.inclusion_injective hN_le_U)
      simpa [N, hN_def] using hN_pgroup

/-- **Isaacs Theorem 4.26**: if a finite `p`-group `A` acts on finite `G` and
`[G, A, ..., A] = 1`, then `[G, A]` is a `p`-group. -/
theorem isaacs_thm_4_26
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {p : ℕ} [Fact p.Prime] (φ : A →* MulAut G) (hA : IsPGroup p A)
    {m : ℕ} (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    IsPGroup p (actionCommutator φ) :=
  actionCommutator_isPGroup_of_iter_eq_bot_aux hA (Nat.card G) φ hm h_iter le_rfl

private theorem actionCommutator_isNilpotent_of_iter_eq_bot_aux :
    ∀ n : ℕ, ∀ {A G : Type*} [Group A] [Finite A] [Group G] [Finite G],
      (φ : A →* MulAut G) → ∀ {m : ℕ}, 1 ≤ m →
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥ →
      Nat.card A ≤ n → Group.IsNilpotent (actionCommutator φ) := by
  intro n
  induction n with
  | zero =>
      intro A G _ _ _ _ φ m hm h_iter h_le
      exfalso
      exact Nat.not_succ_le_zero _ (Nat.card_pos.trans_le h_le)
  | succ n ih =>
      intro A G _ _ _ _ φ m hm h_iter h_le
      by_cases hA_nontriv : Nontrivial A
      swap
      · haveI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA_nontriv
        have hbot : actionCommutator φ = ⊥ := by
          rw [actionCommutator_eq_bot_iff_acts_trivially]
          intro a g
          have ha : a = 1 := Subsingleton.elim a 1
          simp [ha]
        rw [hbot]
        infer_instance
      by_cases hSylowTop :
          ∃ p0 : (Nat.card A).primeFactors, ∃ P : Sylow p0.val A, (P : Subgroup A) = ⊤
      · rcases hSylowTop with ⟨p0, P, hPtop⟩
        haveI hp0 : Fact p0.val.Prime := ⟨Nat.prime_of_mem_primeFactors p0.property⟩
        have hA_pgroup : IsPGroup p0.val A := by
          have hP_pgroup : IsPGroup p0.val (P : Subgroup A) := P.isPGroup'
          rw [hPtop] at hP_pgroup
          exact hP_pgroup.of_equiv Subgroup.topEquiv
        exact (isaacs_thm_4_26 (p := p0.val) φ hA_pgroup hm h_iter).isNilpotent
      · let F : Subgroup G := OddOrder.Isaacs.Ch01.fitting G
        have hF_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ F := by
          simpa [F] using OddOrder.Isaacs.Ch03.IsAInvariant.fittingSubgroup φ
        let φF : A →* MulAut (G ⧸ F) :=
          OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hF_inv
        have hSylow_le_ker :
            ∀ p0 : (Nat.card A).primeFactors, ∀ P : Sylow p0.val A,
              (P : Subgroup A) ≤ φF.ker := by
          intro p0 P a haP
          haveI hp0 : Fact p0.val.Prime := ⟨Nat.prime_of_mem_primeFactors p0.property⟩
          have hP_ne_top : (P : Subgroup A) ≠ ⊤ := fun hPtop =>
            hSylowTop ⟨p0, P, hPtop⟩
          let ψP : P →* MulAut G := φ.comp (P : Subgroup A).subtype
          have h_iter_P :
              iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψP] P).range
                  (SemidirectProduct.inr : P →* G ⋊[ψP] P).range m = ⊥ := by
            simpa [ψP] using
              iterCommutator_inl_inr_restrict_eq_bot (φ := φ) (P : Subgroup A) h_iter
          have hP_card_lt : Nat.card P < Nat.card A :=
            subgroup_card_lt_card_of_ne_top (G := A) (H := (P : Subgroup A)) hP_ne_top
          have hNilpP : Group.IsNilpotent (actionCommutator ψP) :=
            ih ψP hm h_iter_P (Nat.le_of_lt_succ (hP_card_lt.trans_le h_le))
          have hP_comm_le_F : actionCommutator ψP ≤ F := by
            haveI : (actionCommutator ψP).Normal := actionCommutator.normal ψP
            haveI : Group.IsNilpotent (actionCommutator ψP) := hNilpP
            simpa [F] using
              (OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
                (G := G) (N := actionCommutator ψP))
          let x : P := ⟨a, haP⟩
          rw [MonoidHom.mem_ker]
          ext y
          refine QuotientGroup.induction_on y ?_
          intro g
          change (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hF_inv a)
              (QuotientGroup.mk' F g) = QuotientGroup.mk' F g
          rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
          change (((φ a) g : G) : G ⧸ F) = (g : G ⧸ F)
          rw [QuotientGroup.eq]
          have hdelta : g⁻¹ * (φ a) g ∈ F := by
            have := (actionCommutator_le_iff_left ψP F).mp hP_comm_le_F x g
            simpa [ψP, x] using this
          simpa [mul_inv_rev] using F.inv_mem hdelta
        have hker_top : φF.ker = ⊤ := by
          apply eq_top_iff.mpr
          rw [← iSup_sylow_eq_top (M := A)]
          exact iSup_le (fun p0 => iSup_le (fun P => hSylow_le_ker p0 P))
        have hφF_triv : ∀ a : A, ∀ y : G ⧸ F, (φF a) y = y := by
          intro a y
          have ha : a ∈ φF.ker := by
            rw [hker_top]
            exact Subgroup.mem_top a
          rw [MonoidHom.mem_ker] at ha
          rw [ha]
          rfl
        have hφF_bot : actionCommutator φF = ⊥ :=
          (actionCommutator_eq_bot_iff_acts_trivially φF).mpr hφF_triv
        have hmap_bot : (actionCommutator φ).map (QuotientGroup.mk' F) = ⊥ := by
          rw [← actionCommutator_quotient_eq_map hF_inv, hφF_bot]
        have hAC_le_F : actionCommutator φ ≤ F := by
          have hle_ker : actionCommutator φ ≤ (QuotientGroup.mk' F).ker :=
            (Subgroup.map_eq_bot_iff (actionCommutator φ)).mp hmap_bot
          simpa [QuotientGroup.ker_mk'] using hle_ker
        have hAC_sub_nilp : Group.IsNilpotent ((actionCommutator φ).subgroupOf F) :=
          inferInstance
        exact nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAC_le_F)

/-- **Isaacs Theorem 4.27**: if finite `A` acts on finite `G` and
`[G, A, ..., A] = 1`, then `[G, A]` is nilpotent. -/
theorem isaacs_thm_4_27
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    (φ : A →* MulAut G) {m : ℕ} (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    Group.IsNilpotent (actionCommutator φ) :=
  actionCommutator_isNilpotent_of_iter_eq_bot_aux (Nat.card A) φ hm h_iter le_rfl

/-! ### Isaacs §4D Thm 4.34 ⭐ (Fitting, BG Prop 1.6(d)): G abelian + coprime ⇒
G = C_G(A) × [G, A] -/

/-- **Fitting product hom** `θ : G →* G` defined by `θ(g) = ∏ a : A, (φ a) g`.

Well-defined hom for abelian G (使用 Finset.prod_mul_distrib). 教科書 (Isaacs p.140) の
Thm 4.34 証明の核. -/
noncomputable def fittingProductHom {A G : Type*} [CommGroup G] [Group A] [Fintype A]
    (φ : A →* MulAut G) : G →* G where
  toFun g := ∏ a : A, (φ a) g
  map_one' := by simp
  map_mul' x y := by
    simp_rw [map_mul]
    exact Finset.prod_mul_distrib

/-- **`fittingProductHom` of A-fixed element**: c ∈ C_G(A) ⇒ θ c = c^|A|. -/
lemma fittingProductHom_apply_of_fixed {A G : Type*} [CommGroup G] [Group A] [Fintype A]
    {φ : A →* MulAut G} {c : G} (hc : ∀ a : A, (φ a) c = c) :
    fittingProductHom φ c = c ^ Nat.card A := by
  show ∏ a : A, (φ a) c = c ^ Nat.card A
  have h_eq : ∏ a : A, (φ a) c = ∏ _a : A, c :=
    Finset.prod_congr rfl (fun a _ => hc a)
  rw [h_eq, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- **`fittingProductHom` of action-image**: For g ∈ G, a ∈ A,
`θ ((φ a) g) = θ g` (using `b ↦ b * a` is a permutation of A). -/
lemma fittingProductHom_apply_of_smul {A G : Type*} [CommGroup G] [Group A] [Fintype A]
    {φ : A →* MulAut G} (g : G) (a : A) :
    fittingProductHom φ ((φ a) g) = fittingProductHom φ g := by
  show ∏ b : A, (φ b) ((φ a) g) = ∏ b : A, (φ b) g
  -- Rewrite (φ b) ∘ (φ a) = φ (b * a) using map_mul
  have h_compose : ∀ b : A, (φ b) ((φ a) g) = (φ (b * a)) g := fun b => by
    rw [← MulAut.mul_apply, ← map_mul]
  rw [Finset.prod_congr (rfl : (Finset.univ : Finset A) = Finset.univ)
        (fun b _ => h_compose b)]
  -- ∏ b : A, (φ (b * a)) g = ∏ b' : A, (φ b') g (b' = b * a is a bijection)
  exact Finset.prod_bijective (fun b => b * a) (Group.mulRight_bijective a)
    (fun b => by simp) (fun _ _ => rfl)

/-- **`actionCommutator` is in `ker (fittingProductHom)`** (G abelian).

For each generator `g * (φ a) g⁻¹` of `actionCommutator`: `θ (g * (φ a) g⁻¹) = θ g * θ ((φ a) g)⁻¹
= θ g * (θ g)⁻¹ = 1` (using θ hom + `fittingProductHom_apply_of_smul` + map_inv on φ a). -/
lemma actionCommutator_le_ker_fittingProductHom
    {A G : Type*} [CommGroup G] [Group A] [Fintype A] (φ : A →* MulAut G) :
    actionCommutator φ ≤ (fittingProductHom φ).ker := by
  rw [actionCommutator, Subgroup.closure_le]
  rintro _ ⟨g, a, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  -- Goal: θ (g * (φ a) g⁻¹) = 1
  -- (φ a) g⁻¹ = (φ a)(g⁻¹) = ((φ a) g)⁻¹
  have h_inv_eq : (φ a) g⁻¹ = ((φ a) g)⁻¹ := map_inv (φ a) g
  rw [h_inv_eq, map_mul, map_inv, fittingProductHom_apply_of_smul]
  exact mul_inv_cancel _

/-- **Isaacs Theorem 4.34** ⭐ (Fitting, = BG Prop 1.6(d)):
G abelian + A 作用 + coprime (|A|, |G|) ⇒
`fixedPointsOfMulAut φ ⊓ actionCommutator φ = ⊥` (intersection trivial,
combined with Lem 4.28 sup = ⊤ gives internal direct product `G = C_G(A) × [G, A]`).

**証明** (Isaacs p.140): θ : G →* G, `θ g = ∏ a : A, (φ a) g`.
- For c ∈ C_G(A): `θ c = c^|A|`.
- `actionCommutator ⊆ ker θ` (各生成元 `[g, a] ↦ 1`).
- So `c ∈ C_G(A) ∩ actionCommutator ⇒ θ c = c^|A| = 1`. Combined with `c^|G| = 1`
  (Lagrange) + coprime ⇒ `c = 1` (Bezout: ∃ s t, s|A| + t|G| = 1, c = c^1 = ...). -/
theorem fixedPoints_inf_actionCommutator_eq_bot_of_abelian
    {A G : Type*} [CommGroup G] [Group A] [Finite A] [Finite G]
    (φ : A →* MulAut G) (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    Subgroup.fixedPointsOfMulAut φ ⊓ actionCommutator φ = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  obtain ⟨hc_fix, hc_ac⟩ := Subgroup.mem_inf.mp hc
  -- c is A-fixed
  have hc_fixed : ∀ a : A, (φ a) c = c := hc_fix
  -- c ∈ ker θ via actionCommutator ⊆ ker θ
  haveI : Fintype A := Fintype.ofFinite A
  have hc_ker : fittingProductHom φ c = 1 :=
    actionCommutator_le_ker_fittingProductHom φ hc_ac
  -- θ c = c^|A| from hc_fixed
  have hc_pow_A : c ^ Nat.card A = 1 := by
    rw [← fittingProductHom_apply_of_fixed hc_fixed]; exact hc_ker
  -- c^|G| = 1 (Lagrange)
  have hc_pow_G : c ^ Nat.card G = 1 := pow_card_eq_one'
  -- Bezout: ∃ s t, s|A| + t|G| = 1 (coprime), then c = c^(s|A| + t|G|) = 1
  have h_one : c = 1 := by
    have h_gcd : Nat.gcd (Nat.card A) (Nat.card G) = 1 := hCop
    -- Use orderOf c ∣ Nat.card A and orderOf c ∣ Nat.card G ⇒ orderOf c ∣ gcd = 1 ⇒ c = 1
    have h_ord_A : orderOf c ∣ Nat.card A := orderOf_dvd_of_pow_eq_one hc_pow_A
    have h_ord_G : orderOf c ∣ Nat.card G := orderOf_dvd_of_pow_eq_one hc_pow_G
    have h_ord_gcd : orderOf c ∣ Nat.gcd (Nat.card A) (Nat.card G) :=
      Nat.dvd_gcd h_ord_A h_ord_G
    rw [h_gcd] at h_ord_gcd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h_ord_gcd)
  exact h_one

/-! ### Isaacs §4D Cor 4.35 ⭐ (BG Prop 1.6(e)): abelian p-群 + p'-A fixes order-p ⇒
A trivial -/

/-- **Isaacs Corollary 4.35** ⭐ (= BG Prop 1.6(e), **FT クリティカル**):
G is abelian p-群, A is p'-group (i.e., p ∤ |A|), A acts on G via automorphisms.
If A fixes every element of order p (i.e., every g with `g^p = 1`), then
`actionCommutator φ = ⊥` (A acts trivially on G).

**証明** (Isaacs p.141):
- Coprime: p ∤ |A| + G p-group ⇒ |A| coprime |G|.
- G abelian + coprime ⇒ Thm 4.34: `fixedPoints ⊓ actionCommutator = ⊥`.
- Suppose [G, A] = actionCommutator ≠ ⊥. Then nontrivial subgroup of p-group G.
- Cauchy: ∃ g ∈ [G, A] with orderOf g = p. So `g^p = 1`, `g ≠ 1`.
- Hypothesis: A fixes g, i.e., g ∈ fixedPoints.
- So g ∈ fixedPoints ⊓ [G, A] = ⊥, contradicting g ≠ 1. -/
theorem actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p
    {A G : Type*} [Group A] [CommGroup G] [Finite A] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] (φ : A →* MulAut G) (hG : IsPGroup p G)
    (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ g : G, g ^ p = 1 → ∀ a : A, (φ a) g = g) :
    actionCommutator φ = ⊥ := by
  -- Coprime |A|, |G|: G is p-group ⇒ |G| = p^n. p ∤ |A| ⇒ gcd = 1.
  have hCop : Nat.Coprime (Nat.card A) (Nat.card G) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
    rw [hn]
    exact (Nat.Coprime.pow_right n
      (Nat.coprime_comm.mp (Nat.Prime.coprime_iff_not_dvd hp.out |>.mpr hA_p')))
  -- Apply Thm 4.34: fixedPoints ⊓ actionCommutator = ⊥
  have h_inf_bot := fixedPoints_inf_actionCommutator_eq_bot_of_abelian φ hCop
  -- Suppose actionCommutator ≠ ⊥, get contradiction via Cauchy
  by_contra h_ne_bot
  -- ∃ g ∈ actionCommutator with g ≠ 1
  obtain ⟨g_elem, hg_in, hg_ne⟩ : ∃ g ∈ actionCommutator φ, g ≠ 1 := by
    by_contra h
    push Not at h
    apply h_ne_bot
    rw [Subgroup.eq_bot_iff_forall]
    exact h
  -- actionCommutator is nontrivial subgroup of p-group ⇒ has order-p element
  haveI hG_AC : IsPGroup p (actionCommutator φ) := hG.to_subgroup _
  haveI : Nontrivial (actionCommutator φ) := ⟨⟨g_elem, hg_in⟩, 1, by
    intro h
    apply hg_ne
    exact (Subtype.ext_iff.mp h)⟩
  obtain ⟨n, hn_pos, hn_card⟩ := hG_AC.nontrivial_iff_card.mp inferInstance
  -- |actionCommutator| = p^n with n ≥ 1, so p ∣ |actionCommutator|
  have hp_dvd : p ∣ Nat.card (actionCommutator φ) := by
    rw [hn_card]; exact dvd_pow_self p hn_pos.ne'
  -- Cauchy: ∃ g ∈ actionCommutator with orderOf g = p
  obtain ⟨g, hg_ord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  -- Convert orderOf inside subgroup ⇒ orderOf in G via subtype is preserved
  have h_ord_eq : orderOf (g : G) = orderOf g := by
    exact (orderOf_injective (actionCommutator φ).subtype
      (Subgroup.subtype_injective _) g)
  have h_ord_g : orderOf (g : G) = p := h_ord_eq.trans hg_ord
  -- g^p = 1 in G
  have hg_pow : (g : G) ^ p = 1 := by
    rw [← h_ord_g]; exact pow_orderOf_eq_one _
  -- g is fixed by A (hypothesis)
  have hg_fixed : ∀ a : A, (φ a) (g : G) = g := h_fix g hg_pow
  -- So g ∈ fixedPointsOfMulAut ⊓ actionCommutator = ⊥
  have hg_in_inf : (g : G) ∈ Subgroup.fixedPointsOfMulAut φ ⊓ actionCommutator φ :=
    Subgroup.mem_inf.mpr ⟨hg_fixed, g.2⟩
  rw [h_inf_bot, Subgroup.mem_bot] at hg_in_inf
  -- hg_in_inf : (g : G) = 1, but orderOf g = p > 1, contradiction
  have : orderOf (g : G) = 1 := by rw [hg_in_inf, orderOf_one]
  rw [h_ord_g] at this
  exact hp.out.one_lt.ne' this

/-! ### Isaacs §4D: Baer trick (Lem 4.37) — odd order class ≤ 2 ⇒ additive group structure

For `G` finite of **odd order** and **nilpotence class ≤ 2**, define
`baerAdd x y := x * y * sqrtOdd ⁅y, x⁆`. Then `(G, baerAdd)` is an abelian group, and:
- (a) commuting elements satisfy `x +' y = x * y`.
- (b) Additive order = multiplicative order.
- (c) Every multiplicative automorphism is also an additive automorphism.

下流: Thm 4.36 (p > 2, p-群 + p'-A fixes order-p elements ⇒ A trivial) で利用. -/

/-- **Square root in groups with odd `Nat.card`**: `sqrtOdd x := x^((|G|+1)/2)`.
For `Odd (Nat.card G)`, `(sqrtOdd x)² = x` (`pow_card_eq_one'` で `x^(|G|+1) = x`). -/
noncomputable def sqrtOdd {G : Type*} [Group G] (x : G) : G :=
  x ^ ((Nat.card G + 1) / 2)

lemma sqrtOdd_def {G : Type*} [Group G] (x : G) :
    sqrtOdd x = x ^ ((Nat.card G + 1) / 2) := rfl

/-- **核補題**: `Odd (Nat.card G) ⇒ (sqrtOdd x)² = x`. -/
lemma sqrtOdd_sq {G : Type*} [Group G] (hOdd : Odd (Nat.card G)) (x : G) :
    (sqrtOdd x) ^ 2 = x := by
  unfold sqrtOdd
  rw [← pow_mul]
  have h_eq : (Nat.card G + 1) / 2 * 2 = Nat.card G + 1 := by
    obtain ⟨k, hk⟩ := hOdd; rw [hk]; omega
  rw [h_eq, pow_succ, pow_card_eq_one', one_mul]

@[simp] lemma sqrtOdd_one {G : Type*} [Group G] : sqrtOdd (1 : G) = 1 := by
  simp [sqrtOdd]

lemma sqrtOdd_inv {G : Type*} [Group G] (x : G) : sqrtOdd x⁻¹ = (sqrtOdd x)⁻¹ := by
  unfold sqrtOdd; rw [← inv_pow]

lemma sqrtOdd_mul_of_commute {G : Type*} [Group G] {x y : G} (h : Commute x y) :
    sqrtOdd (x * y) = sqrtOdd x * sqrtOdd y := by
  unfold sqrtOdd; rw [Commute.mul_pow h]

lemma sqrtOdd_mem_subgroup {G : Type*} [Group G] {H : Subgroup G} {x : G} (hx : x ∈ H) :
    sqrtOdd x ∈ H := H.pow_mem hx _

/-- `sqrtOdd` の center 保存性. -/
lemma sqrtOdd_mem_center {G : Type*} [Group G] {x : G} (hx : x ∈ Subgroup.center G) :
    sqrtOdd x ∈ Subgroup.center G := sqrtOdd_mem_subgroup hx

/-- `sqrtOdd` is preserved by group homomorphisms (between groups of same cardinality).
For an automorphism `f : G ≃* G`, `f (sqrtOdd x) = sqrtOdd (f x)`. -/
lemma sqrtOdd_apply_mulEquiv {G : Type*} [Group G] (f : G ≃* G) (x : G) :
    f (sqrtOdd x) = sqrtOdd (f x) := by
  unfold sqrtOdd
  rw [map_pow]

/-- `sqrtOdd ⁅x, y⁆⁻¹ = sqrtOdd ⁅y, x⁆`. -/
lemma sqrtOdd_commutator_inv {G : Type*} [Group G] (x y : G) :
    sqrtOdd (⁅x, y⁆⁻¹ : G) = sqrtOdd ⁅y, x⁆ := by
  rw [commutatorElement_inv]

/-- **Baer addition** for class ≤ 2 odd order groups: `x +' y := x * y * sqrtOdd ⁅y, x⁆`. -/
noncomputable def baerAdd {G : Type*} [Group G] (x y : G) : G := x * y * sqrtOdd ⁅y, x⁆

lemma baerAdd_def {G : Type*} [Group G] (x y : G) :
    baerAdd x y = x * y * sqrtOdd ⁅y, x⁆ := rfl

/-- **Lem 4.37 part (a) precursor**: If `x` and `y` commute, then `x +' y = x * y`
(since `⁅y, x⁆ = 1` and `sqrtOdd 1 = 1`). -/
lemma baerAdd_eq_mul_of_commute {G : Type*} [Group G] {x y : G} (h : Commute x y) :
    baerAdd x y = x * y := by
  rw [baerAdd_def, (commutatorElement_eq_one_iff_commute (g₁ := y) (g₂ := x)).mpr h.symm,
      sqrtOdd_one, mul_one]

/-- Identity: `1 +' x = x`. -/
@[simp] lemma baerAdd_one_left {G : Type*} [Group G] (x : G) : baerAdd 1 x = x := by
  rw [baerAdd_def, one_mul, commutatorElement_one_right, sqrtOdd_one, mul_one]

/-- Identity: `x +' 1 = x`. -/
@[simp] lemma baerAdd_one_right {G : Type*} [Group G] (x : G) : baerAdd x 1 = x := by
  rw [baerAdd_def, mul_one, commutatorElement_one_left, sqrtOdd_one, mul_one]

/-- Inverse: `x +' x⁻¹ = 1`. -/
@[simp] lemma baerAdd_inv_right {G : Type*} [Group G] (x : G) : baerAdd x x⁻¹ = 1 := by
  have h1 : ⁅x⁻¹, x⁆ = (1 : G) :=
    commutatorElement_eq_one_iff_commute.mpr (Commute.refl x).inv_left
  rw [baerAdd_def, mul_inv_cancel, h1, sqrtOdd_one, mul_one]

/-- Inverse: `x⁻¹ +' x = 1`. -/
@[simp] lemma baerAdd_inv_left {G : Type*} [Group G] (x : G) : baerAdd x⁻¹ x = 1 := by
  have h1 : ⁅x, x⁻¹⁆ = (1 : G) :=
    commutatorElement_eq_one_iff_commute.mpr (Commute.refl x).inv_right
  rw [baerAdd_def, inv_mul_cancel, h1, sqrtOdd_one, mul_one]

/-- **Lem 4.37 commutativity**: `x +' y = y +' x` for class ≤ 2.

Derivation: `y +' x = y * x * sqrtOdd ⁅x, y⁆ = x * y * ⁅y, x⁆ * sqrtOdd ⁅x, y⁆`
(using `mul_comm_commutator_of_class_le_two`). Now `⁅x, y⁆⁻¹ = ⁅y, x⁆`, so
`sqrtOdd ⁅x, y⁆ = (sqrtOdd ⁅y, x⁆)⁻¹`. Combined:
`y +' x = x * y * ⁅y, x⁆ * (sqrtOdd ⁅y, x⁆)⁻¹ = x * y * sqrtOdd ⁅y, x⁆ = x +' y`
(using `(sqrtOdd ⁅y, x⁆)² = ⁅y, x⁆`). -/
lemma baerAdd_comm {G : Type*} [Group G] (hC : _root_.commutator G ≤ Subgroup.center G)
    (hOdd : Odd (Nat.card G)) (x y : G) :
    baerAdd x y = baerAdd y x := by
  rw [baerAdd_def, baerAdd_def]
  -- Set S := sqrtOdd ⁅y, x⁆. Show x * y * S = y * x * sqrtOdd ⁅x, y⁆.
  set S : G := sqrtOdd ⁅y, x⁆ with hS_def
  have h_yx : y * x = x * y * ⁅y, x⁆ := mul_comm_commutator_of_class_le_two hC x y
  have h_inv : (sqrtOdd ⁅x, y⁆ : G) = S⁻¹ := by
    rw [hS_def, ← sqrtOdd_inv]
    congr 1
    exact (commutatorElement_inv y x).symm
  have h_sq : S * S = ⁅y, x⁆ := by
    have := sqrtOdd_sq hOdd (⁅y, x⁆ : G); rw [sq] at this; exact this
  -- Goal: x * y * S = y * x * sqrtOdd ⁅x, y⁆
  rw [h_inv, h_yx]
  -- Goal: x * y * S = x * y * ⁅y, x⁆ * S⁻¹
  rw [← h_sq]
  -- Goal: x * y * S = x * y * (S * S) * S⁻¹
  group

/-- **Lem 4.37 (a)**: If `x` and `y` commute, then `x +' y = x * y`. -/
lemma baerAdd_eq_mul_of_commute' {G : Type*} [Group G] {x y : G} (h : Commute x y) :
    baerAdd x y = x * y := baerAdd_eq_mul_of_commute h

/-- `sqrtOdd` of a central element is central. -/
lemma sqrtOdd_central_of_central {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) : sqrtOdd z ∈ Subgroup.center G :=
  sqrtOdd_mem_subgroup hz

/-- Right-hom version of commutator in class ≤ 2: `⁅z, a * b⁆ = ⁅z, a⁆ * ⁅z, b⁆`.
Derived from left-hom + `commutatorElement_inv`. -/
lemma commutatorElement_mul_right_of_class_le_two {G : Type*} [Group G]
    (hC : _root_.commutator G ≤ Subgroup.center G) (z a b : G) :
    ⁅z, a * b⁆ = ⁅z, a⁆ * ⁅z, b⁆ := by
  -- ⁅z, a*b⁆ = ⁅a*b, z⁆⁻¹ = (⁅a, z⁆ * ⁅b, z⁆)⁻¹ = ⁅b, z⁆⁻¹ * ⁅a, z⁆⁻¹ = ⁅z, b⁆ * ⁅z, a⁆
  -- In class 2, ⁅z, a⁆ and ⁅z, b⁆ are central, so commute.
  have h_swap : (⁅z, a⁆ : G) * ⁅z, b⁆ = ⁅z, b⁆ * ⁅z, a⁆ := by
    have h_ca : ⁅z, a⁆ ∈ Subgroup.center G := hC (commutatorElement_mem_commutator_top z a)
    exact (Subgroup.mem_center_iff.mp h_ca _).symm
  have h_inv_ab : (⁅a * b, z⁆ : G)⁻¹ = ⁅z, a * b⁆ := commutatorElement_inv (a * b) z
  have h_left : (⁅a * b, z⁆ : G) = ⁅a, z⁆ * ⁅b, z⁆ :=
    commutatorElement_mul_left_of_class_le_two hC a b z
  rw [← h_inv_ab, h_left, mul_inv_rev, commutatorElement_inv, commutatorElement_inv, h_swap]

/-- **Lem 4.37 associativity**: `x +' (y +' z) = (x +' y) +' z` for class ≤ 2 + odd order.

**証明**: 両辺は `x * y * z * sqrtOdd ⁅z, y⁆ * sqrtOdd ⁅y, x⁆ * sqrtOdd ⁅z, x⁆` に等しい
(中心 commutators の積 は順序自由).

LHS = `x * (yz·S_{zy}) * S_{(yz·S_{zy}, x)}`:
- `⁅yz·S_{zy}, x⁆ = ⁅y, x⁆ * ⁅z, x⁆` (left hom + `⁅S_{zy}, x⁆ = 1`)
- `S_{⁅y,x⁆·⁅z,x⁆} = S_{y,x} * S_{z,x}` (sqrtOdd of central commuting product)

RHS = `(xy·S_{yx}) * z * S_{(z, xy·S_{yx})}`:
- `⁅z, xy·S_{yx}⁆ = ⁅z, x⁆ * ⁅z, y⁆` (right hom + `⁅z, S_{yx}⁆ = 1`)
- `z` moves past central `S_{yx}` ⇒ `xyz·S_{yx}·S_{⁅z,x⁆·⁅z,y⁆}`
- `S_{⁅z,x⁆·⁅z,y⁆} = S_{z,x} * S_{z,y}`. -/
lemma baerAdd_assoc {G : Type*} [Group G] (hC : _root_.commutator G ≤ Subgroup.center G)
    (x y z : G) :
    baerAdd x (baerAdd y z) = baerAdd (baerAdd x y) z := by
  -- Notation: S_{ab} = sqrtOdd ⁅a, b⁆
  set Syz : G := sqrtOdd ⁅z, y⁆
  set Sxy : G := sqrtOdd ⁅y, x⁆
  set Sxz : G := sqrtOdd ⁅z, x⁆
  -- Centrality of all sqrtOdd-of-commutator elements
  have h_Sc_zy : Syz ∈ Subgroup.center G :=
    sqrtOdd_central_of_central (hC (commutatorElement_mem_commutator_top z y))
  have h_Sc_yx : Sxy ∈ Subgroup.center G :=
    sqrtOdd_central_of_central (hC (commutatorElement_mem_commutator_top y x))
  have h_Sc_zx : Sxz ∈ Subgroup.center G :=
    sqrtOdd_central_of_central (hC (commutatorElement_mem_commutator_top z x))
  -- Helper: central element commutes with anything (Commute)
  have h_comm_central : ∀ {c : G}, c ∈ Subgroup.center G → ∀ a, Commute c a := fun hc a =>
    (Subgroup.mem_center_iff.mp hc a).symm
  have h_Comm_Syz : ∀ a, Commute Syz a := fun a => h_comm_central h_Sc_zy a
  have h_Comm_Sxy : ∀ a, Commute Sxy a := fun a => h_comm_central h_Sc_yx a
  -- LHS commutator computation: ⁅y * z * Syz, x⁆ = ⁅y, x⁆ * ⁅z, x⁆
  have h_LHS_arg : ⁅y * z * Syz, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ := by
    have h_yz_x : ⁅y * z, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ :=
      commutatorElement_mul_left_of_class_le_two hC y z x
    have h_Syz_x : ⁅Syz, x⁆ = (1 : G) :=
      (commutatorElement_eq_one_iff_commute (g₁ := Syz) (g₂ := x)).mpr (h_Comm_Syz x)
    rw [commutatorElement_mul_left_of_class_le_two hC, h_yz_x, h_Syz_x, mul_one]
  -- RHS commutator computation: ⁅z, x * y * Sxy⁆ = ⁅z, x⁆ * ⁅z, y⁆
  have h_RHS_arg : ⁅z, x * y * Sxy⁆ = ⁅z, x⁆ * ⁅z, y⁆ := by
    have h_z_xy : ⁅z, x * y⁆ = ⁅z, x⁆ * ⁅z, y⁆ :=
      commutatorElement_mul_right_of_class_le_two hC z x y
    have h_z_Sxy : ⁅z, Sxy⁆ = (1 : G) :=
      (commutatorElement_eq_one_iff_commute (g₁ := z) (g₂ := Sxy)).mpr (h_Comm_Sxy z).symm
    rw [commutatorElement_mul_right_of_class_le_two hC z (x * y) Sxy, h_z_xy, h_z_Sxy, mul_one]
  -- Distribute sqrtOdd over products of central commutators
  -- sqrtOdd (⁅y, x⁆ * ⁅z, x⁆) = Sxy * Sxz (centrals commute)
  have h_C_xy : (⁅y, x⁆ : G) ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top y x)
  have h_C_zx : (⁅z, x⁆ : G) ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top z x)
  have h_split_LHS : sqrtOdd (⁅y, x⁆ * ⁅z, x⁆ : G) = Sxy * Sxz :=
    sqrtOdd_mul_of_commute ((h_comm_central h_C_xy) ⁅z, x⁆)
  -- sqrtOdd (⁅z, x⁆ * ⁅z, y⁆) = Sxz * Syz
  have h_C_zy : (⁅z, y⁆ : G) ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top z y)
  have h_split_RHS : sqrtOdd (⁅z, x⁆ * ⁅z, y⁆ : G) = Sxz * Syz :=
    sqrtOdd_mul_of_commute ((h_comm_central h_C_zx) ⁅z, y⁆)
  -- Compute LHS and RHS
  -- LHS = x * (y * z * Syz) * sqrtOdd ⁅y * z * Syz, x⁆
  --     = x * y * z * Syz * sqrtOdd (⁅y, x⁆ * ⁅z, x⁆)
  --     = x * y * z * Syz * Sxy * Sxz
  -- RHS = (x * y * Sxy) * z * sqrtOdd ⁅z, x * y * Sxy⁆
  --     = x * y * Sxy * z * sqrtOdd (⁅z, x⁆ * ⁅z, y⁆)
  --     = x * y * Sxy * z * Sxz * Syz
  --     = x * y * z * Sxy * Sxz * Syz  (Sxy commutes with z)
  -- LHS = RHS iff Syz * Sxy * Sxz = Sxy * Sxz * Syz, which holds because all centrals commute.
  rw [baerAdd_def, baerAdd_def, baerAdd_def, baerAdd_def, h_LHS_arg, h_RHS_arg,
      h_split_LHS, h_split_RHS]
  -- Goal: x * (y * z * Syz) * (Sxy * Sxz) = (x * y * Sxy) * z * (Sxz * Syz)
  -- Both sides normalize to `x * y * z * Sxy * Sxz * Syz` via commutativity
  -- of central elements (Syz, Sxy, Sxz).
  have h_Sxy_z := h_Comm_Sxy z
  have h_LHS_norm :
      x * (y * z * Syz) * (Sxy * Sxz) = x * y * z * Sxy * Sxz * Syz := by
    have hC : Commute Syz (Sxy * Sxz) := (h_Comm_Syz Sxy).mul_right (h_Comm_Syz Sxz)
    have h_rearrange :
        x * (y * z * Syz) * (Sxy * Sxz) = (x * y * z) * (Syz * (Sxy * Sxz)) := by group
    rw [h_rearrange, hC.eq]; group
  have h_RHS_norm :
      (x * y * Sxy) * z * (Sxz * Syz) = x * y * z * Sxy * Sxz * Syz := by
    have h_rearrange :
        (x * y * Sxy) * z * (Sxz * Syz) = x * y * (Sxy * z) * (Sxz * Syz) := by group
    rw [h_rearrange, h_Sxy_z.eq]; group
  rw [h_LHS_norm, h_RHS_norm]

/-- **Lem 4.37 part (c)**: Every group homomorphism (between equal-card groups) preserves
`baerAdd`: `f (baerAdd x y) = baerAdd (f x) (f y)`. -/
lemma baerAdd_map_eq {G H : Type*} [Group G] [Group H] (f : G →* H)
    (h_card : Nat.card G = Nat.card H) (x y : G) :
    f (baerAdd x y) = baerAdd (f x) (f y) := by
  rw [baerAdd_def, baerAdd_def, map_mul, map_mul]
  congr 1
  -- f (sqrtOdd ⁅y, x⁆) = sqrtOdd (f ⁅y, x⁆) = sqrtOdd ⁅f y, f x⁆
  rw [sqrtOdd, sqrtOdd, h_card, map_pow, map_commutatorElement]

/-- **Lem 4.37 part (c) for MulEquiv** (Aut preservation): For `f : G ≃* G`,
`f (baerAdd x y) = baerAdd (f x) (f y)`. つまり multiplicative automorphism は
baerAdd を保存. -/
lemma baerAdd_mulEquiv_eq {G : Type*} [Group G] (f : G ≃* G) (x y : G) :
    f (baerAdd x y) = baerAdd (f x) (f y) :=
  baerAdd_map_eq f.toMonoidHom rfl x y

/-! ### Lem 4.37(b) element form + `BaerMul G` 型ラッパー (CommGroup 構造)

Baer trick の "additive group" は実際には Lean 上では type wrapper 経由で実装する.
`BaerMul G := G` (定義的に同型) に `CommGroup` インスタンスを `baerAdd` で与える.
これにより Cor 4.35 (CommGroup 仮定) を そのまま `BaerMul G` に適用できる.

教科書 (Isaacs p.142) (b) 証明の鍵: `nx = x + (n-1)x = x · x^(n-1) = x^n`
(commute case で `baerAdd_eq_mul_of_commute`). 実装では `npow x n := x^n` (G の冪) を直接採用し,
`npow_succ : npow (n+1) x = baerAdd (npow n x) x` を `baerAdd_pow_self_eq_pow_succ` で提供. -/

/-- **Lem 4.37(b) inductive step** (仮定不要): `baerAdd (x^n) x = x^(n+1)`.

`x` と `x^n` は常に commute するので, `baerAdd x^n x = x^n * x * sqrtOdd ⁅x, x^n⁆ = x^n · x · 1 = x^{n+1}`.
これが `BaerMul G` の `npow_succ` フィールドに対応する. -/
lemma baerAdd_pow_self_eq_pow_succ {G : Type*} [Group G] (x : G) (n : ℕ) :
    baerAdd (x ^ n) x = x ^ (n + 1) := by
  have h_comm : Commute (x ^ n) x := Commute.pow_self x n
  rw [baerAdd_eq_mul_of_commute h_comm, ← pow_succ]

/-- **Baer trick type wrapper**: `BaerMul G := G` (定義的に同型).

`G` が奇数位数 + class ≤ 2 のときに `BaerMul G` 上に `baerAdd` を乗法とする `CommGroup` 構造を
与える (Lem 4.37). これにより mathlib の CommGroup 用 API (Cor 4.35 等) を `BaerMul G` に
直接適用できる.

Naming: 乗法的 wrapper として扱う ("multiplicative view of (G, +')"). -/
def BaerMul (G : Type*) : Type _ := G

namespace BaerMul

variable {G : Type*}

/-- Coercion `BaerMul G ≃ G` (identity at runtime). -/
def toG : BaerMul G ≃ G := Equiv.refl _

/-- Coercion `G ≃ BaerMul G` (identity at runtime). -/
def ofG : G ≃ BaerMul G := Equiv.refl _

@[simp] theorem toG_ofG (x : G) : toG (ofG x) = x := rfl
@[simp] theorem ofG_toG (x : BaerMul G) : ofG (toG x) = x := rfl

end BaerMul

/-- `Mul (BaerMul G) = baerAdd`. -/
noncomputable instance BaerMul.instMul {G : Type*} [Group G] : Mul (BaerMul G) where
  mul x y := BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG y))

/-- `1 : BaerMul G = ofG 1`. -/
instance BaerMul.instOne {G : Type*} [One G] : One (BaerMul G) where
  one := BaerMul.ofG 1

/-- `(·)⁻¹ : BaerMul G → BaerMul G` is the same as G's inverse (Lem 4.37 で `baerAdd x⁻¹ x = 1`). -/
instance BaerMul.instInv {G : Type*} [Inv G] : Inv (BaerMul G) where
  inv x := BaerMul.ofG (BaerMul.toG x)⁻¹

/-- **CommGroup instance for `BaerMul G`**: `G` が `Odd (Nat.card G)` + `commutator G ≤ Z(G)`
を満たすとき, `(BaerMul G, baerAdd, 1, ·⁻¹)` は可換群.

実装方針: 基本 `Mul / One / Inv` instance を別途与えて, ここでは **axiom フィールドのみ提供**.
`npow / zpow` フィールドはデフォルト (`npowRec` / `zpowRec`) を使用. `npowRec` は `*`
(我々の baerAdd) を `n` 回反復するので, BaerMul の pow = `baerAdd`-iterate.
G の `x^n` との一致は Lem 4.37(b) (`baerAdd_pow_self_eq_pow_succ`) 経由で別途証明. -/
noncomputable instance BaerMul.instCommGroup {G : Type*} [Group G]
    [hOdd : Fact (Odd (Nat.card G))]
    [hC : Fact (_root_.commutator G ≤ Subgroup.center G)] : CommGroup (BaerMul G) where
  mul_assoc x y z := by
    show BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG y))))
        (BaerMul.toG z)) =
      BaerMul.ofG (baerAdd (BaerMul.toG x)
        (BaerMul.toG (BaerMul.ofG (baerAdd (BaerMul.toG y) (BaerMul.toG z)))))
    simp only [BaerMul.toG_ofG]
    exact congr_arg BaerMul.ofG
      (baerAdd_assoc hC.out (BaerMul.toG x) (BaerMul.toG y) (BaerMul.toG z)).symm
  one_mul x := by
    show BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG 1)) (BaerMul.toG x)) = x
    simp only [BaerMul.toG_ofG, baerAdd_one_left]
    rfl
  mul_one x := by
    show BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG (BaerMul.ofG 1))) = x
    simp only [BaerMul.toG_ofG, baerAdd_one_right]
    rfl
  mul_comm x y := by
    show BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG y)) =
      BaerMul.ofG (baerAdd (BaerMul.toG y) (BaerMul.toG x))
    exact congr_arg BaerMul.ofG (baerAdd_comm hC.out hOdd.out _ _)
  inv_mul_cancel x := by
    show BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG (BaerMul.toG x)⁻¹)) (BaerMul.toG x)) =
      BaerMul.ofG 1
    simp only [BaerMul.toG_ofG]
    rw [baerAdd_inv_left]

instance BaerMul.instFinite {G : Type*} [Finite G] : Finite (BaerMul G) :=
  inferInstanceAs (Finite G)

@[simp] lemma BaerMul.nat_card_eq {G : Type*} : Nat.card (BaerMul G) = Nat.card G := rfl

/-- **Lem 4.37(c) wrapped**: G の multiplicative automorphism は `BaerMul G` 上でも
multiplicative automorphism (= baerAdd 保存). 関数本体は同じ (恒等経由). -/
noncomputable def MulAut.toBaerMul {G : Type*} [Group G] (f : G ≃* G) :
    BaerMul G ≃* BaerMul G where
  toFun x := BaerMul.ofG (f (BaerMul.toG x))
  invFun x := BaerMul.ofG (f.symm (BaerMul.toG x))
  left_inv x := by
    show BaerMul.ofG (f.symm (BaerMul.toG (BaerMul.ofG (f (BaerMul.toG x))))) = x
    simp only [BaerMul.toG_ofG, f.symm_apply_apply]
    rfl
  right_inv x := by
    show BaerMul.ofG (f (BaerMul.toG (BaerMul.ofG (f.symm (BaerMul.toG x))))) = x
    simp only [BaerMul.toG_ofG, f.apply_symm_apply]
    rfl
  map_mul' x y := by
    show BaerMul.ofG (f (BaerMul.toG (BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG y))))) =
        BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG (f (BaerMul.toG x))))
          (BaerMul.toG (BaerMul.ofG (f (BaerMul.toG y)))))
    simp only [BaerMul.toG_ofG]
    exact congr_arg BaerMul.ofG (baerAdd_mulEquiv_eq f (BaerMul.toG x) (BaerMul.toG y))

/-- `MulAut.toBaerMul` は群準同型 (composition / 1 を保存). 下の `MonoidHom.toBaerMulLift`
を構成するために使う. -/
noncomputable def MulAut.toBaerMulHom {G : Type*} [Group G] :
    MulAut G →* MulAut (BaerMul G) where
  toFun f := MulAut.toBaerMul f
  map_one' := by
    ext x
    show BaerMul.ofG ((1 : MulAut G) (BaerMul.toG x)) = x
    show BaerMul.ofG (BaerMul.toG x) = x
    exact BaerMul.ofG_toG x
  map_mul' f g := by
    ext x
    show BaerMul.ofG ((f * g) (BaerMul.toG x)) =
        BaerMul.ofG (f (BaerMul.toG (BaerMul.ofG (g (BaerMul.toG x)))))
    simp only [BaerMul.toG_ofG]
    rfl

/-- φ : A →* MulAut G を BaerMul G への作用 φ' : A →* MulAut (BaerMul G) に lift する.
関数本体は同じ (Lem 4.37(c)). -/
noncomputable def MonoidHom.toBaerMulLift {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) : A →* MulAut (BaerMul G) :=
  MulAut.toBaerMulHom.comp φ

@[simp] lemma MonoidHom.toBaerMulLift_apply {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) (a : A) (g : BaerMul G) :
    (MonoidHom.toBaerMulLift φ a) g = BaerMul.ofG ((φ a) (BaerMul.toG g)) := rfl

/-- **Lem 4.37(b) full form**: `BaerMul G` の自然冪 (baerAdd-iterate) = `G` の自然冪.
`npow_succ` の帰納で示す. -/
lemma BaerMul.npow_eq_pow {G : Type*} [Group G]
    [Fact (Odd (Nat.card G))] [Fact (_root_.commutator G ≤ Subgroup.center G)]
    (x : BaerMul G) (n : ℕ) :
    @HPow.hPow (BaerMul G) ℕ _ _ x n = BaerMul.ofG ((BaerMul.toG x) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    rfl
  | succ k ih =>
    rw [pow_succ, ih]
    show BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG ((BaerMul.toG x) ^ k))) (BaerMul.toG x)) =
        BaerMul.ofG ((BaerMul.toG x) ^ (k + 1))
    simp only [BaerMul.toG_ofG]
    rw [baerAdd_pow_self_eq_pow_succ]

/-- `BaerMul G` での `x^n = 1` ↔ `G` での `x^n = 1`. Cor 4.35 適用時の `g^p = 1` 翻訳に使用. -/
lemma BaerMul.pow_eq_one_iff {G : Type*} [Group G]
    [Fact (Odd (Nat.card G))] [Fact (_root_.commutator G ≤ Subgroup.center G)]
    (x : BaerMul G) (n : ℕ) :
    @HPow.hPow (BaerMul G) ℕ _ _ x n = 1 ↔ (BaerMul.toG x) ^ n = 1 := by
  rw [BaerMul.npow_eq_pow]
  show BaerMul.ofG ((BaerMul.toG x) ^ n) = BaerMul.ofG 1 ↔ (BaerMul.toG x) ^ n = 1
  exact BaerMul.ofG.apply_eq_iff_eq

/-- `IsPGroup p (BaerMul G) ↔ IsPGroup p G`. BaerMul の構造を経由しても p-群性は不変. -/
lemma BaerMul.isPGroup_iff {G : Type*} [Group G]
    [Fact (Odd (Nat.card G))] [Fact (_root_.commutator G ≤ Subgroup.center G)] (p : ℕ) :
    IsPGroup p (BaerMul G) ↔ IsPGroup p G := by
  unfold IsPGroup
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨n, hn⟩ := h (BaerMul.ofG x)
    refine ⟨n, ?_⟩
    rw [BaerMul.pow_eq_one_iff] at hn
    simpa [BaerMul.toG_ofG] using hn
  · obtain ⟨n, hn⟩ := h (BaerMul.toG x)
    refine ⟨n, ?_⟩
    rw [BaerMul.pow_eq_one_iff]
    exact hn

/-- **系 of Lem 4.28**: `A` が `actionCommutator φ` (= `[G, A]`) 上で trivial 作用するとき,
coprime + (A or G solvable) 仮定下では `actionCommutator φ = ⊥` (= A trivial on whole G).

**証明**: Lem 4.28 で G = C_G(A) · [G, A]. 各 g = c * x で `c ∈ C_G(A)` ⇒ `(φ a) c = c`,
`x ∈ [G, A]` + 仮定 ⇒ `(φ a) x = x`. 故に `(φ a) g = (φ a)(c·x) = c·x = g`.

Thm 4.36 induction の `[G, A] < G` ケースで使用 (IH ⇒ A trivial on [G, A] ⇒ A trivial on G). -/
theorem actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : IsSolvable A ∨ IsSolvable G)
    (h_triv : ∀ a : A, ∀ h ∈ actionCommutator φ, (φ a) h = h) :
    actionCommutator φ = ⊥ := by
  rw [actionCommutator_eq_bot_iff_acts_trivially]
  intro a g
  have h_top : g ∈ Subgroup.fixedPointsOfMulAut φ ⊔ actionCommutator φ := by
    rw [fixedPoints_sup_actionCommutator_eq_top hCop hSolv]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_sup_of_normal_right] at h_top
  obtain ⟨c, hc_fix, x, hx_ac, h_eq⟩ := h_top
  -- h_eq : c * x = g, hc_fix : c ∈ fixedPoints, hx_ac : x ∈ actionCommutator
  rw [← h_eq, map_mul, hc_fix a, h_triv a x hx_ac]

/-- **Isaacs Thm 4.36 (class ≤ 2 case)** ⭐: A acts on p-群 G of class ≤ 2 (p > 2),
A is p'-group, A fixes every order-p element of G ⇒ A trivial on G.

Baer trick で `BaerMul G` を可換群として扱い, Cor 4.35 を適用. これが Thm 4.36 の核.

`hp_odd : p ≠ 2` から `Odd p` → `Odd (p^k)` → `Odd (Nat.card G)`. `hC : class ≤ 2` を
`Fact` 化して `BaerMul.instCommGroup` を呼び出し可能に. -/
theorem actionCommutator_eq_bot_of_pgroup_class_le_two_fixes_order_p
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    (hC : _root_.commutator G ≤ Subgroup.center G)
    (φ : A →* MulAut G) (hG : IsPGroup p G) (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ g : G, g ^ p = 1 → ∀ a : A, (φ a) g = g) :
    actionCommutator φ = ⊥ := by
  -- Set up Fact (Odd (Nat.card G))
  have hOdd_p : Odd p := hp.out.odd_of_ne_two hp_odd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
  have hOdd_card : Odd (Nat.card G) := by rw [hk]; exact hOdd_p.pow
  haveI : Fact (Odd (Nat.card G)) := ⟨hOdd_card⟩
  haveI : Fact (_root_.commutator G ≤ Subgroup.center G) := ⟨hC⟩
  -- φ' : A →* MulAut (BaerMul G)
  set φ' : A →* MulAut (BaerMul G) := MonoidHom.toBaerMulLift φ with hφ'
  -- IsPGroup p (BaerMul G)
  have hG' : IsPGroup p (BaerMul G) := (BaerMul.isPGroup_iff p).mpr hG
  -- h_fix translated to BaerMul G
  have h_fix' : ∀ g : BaerMul G, g ^ p = 1 → ∀ a : A, (φ' a) g = g := by
    intro g hg a
    have hg_G : (BaerMul.toG g) ^ p = 1 := (BaerMul.pow_eq_one_iff g p).mp hg
    have h_fixed : (φ a) (BaerMul.toG g) = BaerMul.toG g := h_fix _ hg_G a
    show BaerMul.ofG ((φ a) (BaerMul.toG g)) = g
    rw [h_fixed]
    exact BaerMul.ofG_toG g
  -- Apply Cor 4.35 to BaerMul G
  have h_bot_baer : actionCommutator φ' = ⊥ :=
    actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p φ' hG' hA_p' h_fix'
  -- Translate back to G via iff
  rw [actionCommutator_eq_bot_iff_acts_trivially] at h_bot_baer
  rw [actionCommutator_eq_bot_iff_acts_trivially]
  intro a g
  have h_act := h_bot_baer a (BaerMul.ofG g)
  -- h_act : (φ' a) (ofG g) = ofG g
  -- Unfold φ': (φ' a) (ofG g) = ofG ((φ a) (toG (ofG g))) = ofG ((φ a) g)
  -- So: ofG ((φ a) g) = ofG g, hence (φ a) g = g by injectivity
  have h_eq : BaerMul.ofG ((φ a) g) = BaerMul.ofG g := by
    have hkey : (φ' a) (BaerMul.ofG g) = BaerMul.ofG ((φ a) g) := by
      show BaerMul.ofG ((φ a) (BaerMul.toG (BaerMul.ofG g))) = BaerMul.ofG ((φ a) g)
      rw [BaerMul.toG_ofG]
    rw [← hkey]
    exact h_act
  exact BaerMul.ofG.injective h_eq

/-- **強帰納法版** (`Nat.card G ≤ n` パラメータ化). Thm 4.36 本体の補助. -/
private theorem isaacs_thm_4_36_aux {A : Type*} [Group A] [Finite A]
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2) (hA_p' : ¬ p ∣ Nat.card A) :
    ∀ n : ℕ, ∀ {G : Type*} [Group G] [Finite G]
    (φ : A →* MulAut G) (_ : IsPGroup p G)
    (_ : ∀ g : G, g ^ p = 1 → ∀ a : A, (φ a) g = g),
    Nat.card G ≤ n → actionCommutator φ = ⊥ := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ _ _ h_le
    exfalso
    have h_pos : 0 < Nat.card G := Nat.card_pos
    omega
  | succ m IH =>
    intro G _ _ φ hG h_fix h_le
    -- Case: |G| ≤ m, apply IH
    rcases Nat.lt_or_ge (Nat.card G) (m + 1) with h_lt | h_ge
    · exact IH φ hG h_fix (Nat.le_of_lt_succ h_lt)
    have h_card_G : Nat.card G = m + 1 := le_antisymm h_le h_ge
    -- Subcase: G trivial
    by_cases hG_triv : Nontrivial G
    swap
    · haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG_triv
      rw [actionCommutator_eq_bot_iff_acts_trivially]
      intro a g
      exact Subsingleton.elim _ _
    -- G nontrivial setup
    have hCop : Nat.Coprime (Nat.card A) (Nat.card G) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
      rw [hk]
      exact (Nat.Coprime.pow_right k (Nat.coprime_comm.mp
        (Nat.Prime.coprime_iff_not_dvd hp.out |>.mpr hA_p')))
    haveI hG_nilp : Group.IsNilpotent G := hG.isNilpotent
    have hG_solv : IsSolvable G := IsNilpotent.to_isSolvable
    have hSolv : IsSolvable A ∨ IsSolvable G := Or.inr hG_solv
    -- 補助: H ≠ ⊤ + Finite G ⇒ Nat.card ↥H < Nat.card G
    have card_lt_of_ne_top : ∀ {H : Subgroup G}, H ≠ ⊤ → Nat.card ↥H < Nat.card G := by
      intro H h_ne
      have h_dvd : Nat.card ↥H ∣ Nat.card G :=
        ⟨H.index, by rw [mul_comm, H.index_mul_card]⟩
      have h_le' : Nat.card ↥H ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos h_dvd
      have h_ne' : Nat.card ↥H ≠ Nat.card G := fun heq =>
        h_ne (Subgroup.eq_top_of_card_eq _ heq)
      exact Nat.lt_of_le_of_ne h_le' h_ne'
    -- Case分け: [G, A] < ⊤ vs ⊤
    by_cases h_AC_top : actionCommutator φ = ⊤
    swap
    · -- [G, A] < ⊤: IH を actionCommutator に適用
      set H : Subgroup G := actionCommutator φ
      have hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H :=
        OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator φ
      let φ_H : A →* MulAut ↥H :=
        OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH_inv
      have h_H_card_lt : Nat.card ↥H < Nat.card G := card_lt_of_ne_top h_AC_top
      have hH_pgrp : IsPGroup p ↥H := hG.to_subgroup H
      have h_fix_H : ∀ h : ↥H, h ^ p = 1 → ∀ a : A, (φ_H a) h = h := by
        intro h hh_pow a
        apply Subtype.ext
        show (φ a) h.val = h.val
        apply h_fix
        have := congr_arg (Subtype.val : ↥H → G) hh_pow
        simpa using this
      have h_IH_H := IH φ_H hH_pgrp h_fix_H
        (Nat.le_of_lt_succ (h_H_card_lt.trans_le h_le))
      have h_triv : ∀ a : A, ∀ x ∈ H, (φ a) x = x := by
        intro a x hx
        rw [actionCommutator_eq_bot_iff_acts_trivially] at h_IH_H
        have := h_IH_H a ⟨x, hx⟩
        exact congr_arg Subtype.val this
      exact actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime hCop hSolv h_triv
    -- [G, A] = ⊤: G' < ⊤, IH を G' に適用, Three-subgroups で class ≤ 2
    -- G' = commutator G
    set G' : Subgroup G := commutator G with hG'_def
    have hG'_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ G' :=
      OddOrder.Isaacs.Ch03.IsAInvariant.derivedSeries φ 1
    have h_G'_lt_top : G' < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial G
    have h_G'_card_lt : Nat.card ↥G' < Nat.card G := card_lt_of_ne_top h_G'_lt_top.ne
    let φ_G' : A →* MulAut ↥G' :=
      OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hG'_inv
    have hG'_pgrp : IsPGroup p ↥G' := hG.to_subgroup G'
    have h_fix_G' : ∀ g' : ↥G', g' ^ p = 1 → ∀ a : A, (φ_G' a) g' = g' := by
      intro g' hg'_pow a
      apply Subtype.ext
      show (φ a) g'.val = g'.val
      apply h_fix
      have := congr_arg (Subtype.val : ↥G' → G) hg'_pow
      simpa using this
    have h_IH_G' := IH φ_G' hG'_pgrp h_fix_G'
      (Nat.le_of_lt_succ (h_G'_card_lt.trans_le h_le))
    have h_triv_G' : ∀ a : A, ∀ g' ∈ G', (φ a) g' = g' := by
      intro a g' hg'
      rw [actionCommutator_eq_bot_iff_acts_trivially] at h_IH_G'
      have := h_IH_G' a ⟨g', hg'⟩
      exact congr_arg Subtype.val this
    -- Three-subgroups in Γ で G' ⊆ Z(G) を導く
    have h_class_le_2 : commutator G ≤ Subgroup.center G := by
      -- Γ = G ⋊[φ] A. XG = inl(G), YA = inr(A), XG' = inl(G').
      set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
      set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
      set XG' : Subgroup (G ⋊[φ] A) := G'.map (SemidirectProduct.inl : G →* G ⋊[φ] A)
      -- Step 1: ⁅XG', YA⁆ = ⊥ (h_triv_G' + generator computation)
      have h_G'_YA : ⁅XG', YA⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        rintro _ ⟨k, hk, rfl⟩ _ ⟨a, rfl⟩
        rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
        have h_fix' : (φ a) k = k := h_triv_G' a k hk
        rw [show (φ a) k⁻¹ = ((φ a) k)⁻¹ from map_inv (φ a) k, h_fix', mul_inv_cancel]
        exact map_one _
      -- Step 2: ⁅XG, XG'⁆ ≤ XG' (G' normal in G ⇒ inl の像でも保たれる)
      have h_GG'_le : ⁅XG, XG'⁆ ≤ XG' := by
        rw [Subgroup.commutator_le]
        rintro _ ⟨g, rfl⟩ _ ⟨k, hk, rfl⟩
        -- Goal: ⁅inl g, inl k⁆ ∈ XG' (= inl(G'))
        rw [show (⁅(SemidirectProduct.inl g : G ⋊[φ] A), SemidirectProduct.inl k⁆ :
            G ⋊[φ] A) = SemidirectProduct.inl ⁅g, k⁆ from by
          simp [commutatorElement_def, ← map_mul, ← map_inv]]
        refine ⟨⁅g, k⁆, ?_, rfl⟩
        -- Since G' is normal, both `g * k * g⁻¹` and `k⁻¹` lie in G'.
        have hG'_normal : G'.Normal := inferInstance
        have h_gkg : g * k * g⁻¹ ∈ G' := hG'_normal.conj_mem k hk g
        have h_inv : k⁻¹ ∈ G' := G'.inv_mem hk
        rw [commutatorElement_def]
        exact G'.mul_mem h_gkg h_inv
      -- h12: ⁅⁅XG, XG'⁆, YA⁆ ⊆ ⁅XG', YA⁆ = ⊥
      have h12 : ⁅⁅XG, XG'⁆, YA⁆ = ⊥ := by
        rw [eq_bot_iff]
        calc ⁅⁅XG, XG'⁆, YA⁆ ≤ ⁅XG', YA⁆ := Subgroup.commutator_mono h_GG'_le le_rfl
          _ = ⊥ := h_G'_YA
      -- h23: ⁅⁅XG', YA⁆, XG⁆ = ⁅⊥, XG⁆ = ⊥
      have h23 : ⁅⁅XG', YA⁆, XG⁆ = ⊥ := by
        rw [h_G'_YA]
        exact Subgroup.commutator_bot_left XG
      -- Three-subgroups: ⁅⁅YA, XG⁆, XG'⁆ = ⊥
      have h_three : ⁅⁅YA, XG⁆, XG'⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate h12 h23
      -- ⁅YA, XG⁆ = ⁅XG, YA⁆ = XG (since actionCommutator = ⊤)
      have h_XGYA_eq_XG : ⁅XG, YA⁆ = XG := by
        rw [← actionCommutator_map_inl φ, h_AC_top]
        exact (MonoidHom.range_eq_map _).symm
      have h_YAXG_eq_XG : ⁅YA, XG⁆ = XG := by
        rw [Subgroup.commutator_comm]; exact h_XGYA_eq_XG
      -- So ⁅XG, XG'⁆ = ⊥ in Γ
      have h_XG_XG'_bot : ⁅XG, XG'⁆ = ⊥ := h_YAXG_eq_XG ▸ h_three
      -- Translate back to G: ⁅⊤, G'⁆ = ⊥ ⇒ G' ⊆ Z(G)
      -- inl(⁅⊤, G'⁆) = ⁅inl(⊤), inl(G')⁆ = ⁅XG, XG'⁆ = ⊥, so ⁅⊤, G'⁆ = ⊥ by inl injective
      have h_top_G'_bot : ⁅(⊤ : Subgroup G), G'⁆ = ⊥ := by
        apply Subgroup.map_injective (f := (SemidirectProduct.inl : G →* G ⋊[φ] A))
          SemidirectProduct.inl_injective
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.map_bot]
        exact h_XG_XG'_bot
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h_top_G'_bot
      -- h_top_G'_bot : ⊤ ≤ G'.centralizer
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have := h_top_G'_bot (Subgroup.mem_top y)
      exact (this x hx).symm
    -- Apply class ≤ 2 case
    exact actionCommutator_eq_bot_of_pgroup_class_le_two_fixes_order_p
      hp_odd h_class_le_2 φ hG hA_p' h_fix

/-- **Isaacs Theorem 4.36** ⭐ (= BG Thm 1.11, **FT クリティカル**):
`p > 2`, `G` p-群, `A` p'-群 が `G` に作用. `A` が `G` の全 order-p 要素を fix するならば,
`A` は `G` 上 trivial に作用する (`actionCommutator φ = ⊥`).

**証明** (Isaacs p.142): 強帰納法 on `|G|`.
- 自明 G: 即座.
- `[G, A] < G`: IH を `actionCommutator` に適用 ⇒ A trivial on [G, A] ⇒ Lem 4.28 系で結論.
- `[G, A] = G`: `G' < G` (G nontrivial nilpotent solvable). IH を G' に適用 ⇒ A trivial on G'.
  Three-subgroups in Γ = G ⋊ A ([G', A] = 1, [G, G'] ⊆ G' から) ⇒ `[G, G'] = 1` ⇒ G' ⊆ Z(G)
  ⇒ class ≤ 2. Baer trick + Cor 4.35 (class ≤ 2 case) で結論.

下流: BG §1 Thm 1.11 (BG Cor 1.12 等), Ch.5 Cor 5.30 経由 normal p-complement (5.26). -/
theorem isaacs_thm_4_36 {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    (φ : A →* MulAut G) (hG : IsPGroup p G) (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ g : G, g ^ p = 1 → ∀ a : A, (φ a) g = g) :
    actionCommutator φ = ⊥ :=
  isaacs_thm_4_36_aux hp_odd hA_p' (Nat.card G) φ hG h_fix le_rfl

/-- **Isaacs Lemma 4.32 (後半)** ⭐: `P` p-群 が `G` 非自明 p-群 に作用 ⇒
`C_G(P)` (= fixed point subgroup) は非自明.

**proof**: `MulAction P G` を `φ` 経由で setup. `card_modEq_card_fixedPoints` で
`|G| ≡ |fixedPoints| mod p`. G 非自明 p-群より `p ∣ |G|`. 1 は trivial fixed point.
`exists_fixed_point_of_prime_dvd_card_of_fixed_point` で `1` と異なる fixed point 存在. -/
theorem fixedPoints_ne_bot_of_pgroup_action_pgroup
    {G P : Type*} [Group G] [Group P] [Finite G] [Finite P] [Nontrivial G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (hP : IsPGroup p P)
    (φ : P →* MulAut G) :
    Subgroup.fixedPointsOfMulAut φ ≠ ⊥ := by
  letI : MulAction P G := MulAction.compHom G φ
  -- 1 ∈ fixedPoints (φ p is a group hom, so (φ p) 1 = 1)
  have h1_fix : (1 : G) ∈ MulAction.fixedPoints P G := fun p => by
    show (φ p) 1 = 1
    exact map_one (φ p)
  -- p ∣ |G| since G is a nontrivial p-group
  obtain ⟨n, hn_pos, hn_card⟩ := hG.nontrivial_iff_card.mp inferInstance
  have hp_dvd : p ∣ Nat.card G := by
    rw [hn_card]; exact dvd_pow_self p hn_pos.ne'
  -- ∃ b ∈ fixedPoints, b ≠ 1
  obtain ⟨b, hb_fix, hb_ne⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := G) hp_dvd h1_fix
  -- b ∈ Subgroup.fixedPointsOfMulAut φ via the same definition
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨b, ?_⟩, ?_⟩
  · exact fun p => hb_fix p
  · intro h
    apply hb_ne
    exact (Subtype.ext_iff.mp h).symm

/-- **Isaacs Lemma 4.32 (前半)**: `P` p-群 が `G` 非自明 p-群 に作用 ⇒
`Γ = G ⋊[φ] P` 内で `⁅inl(G), inr(P)⁆ < inl(G)` (strict).

**proof**: Γ = G ⋊ P は p-群 (`IsPGroup.semidirectProduct`) で nilpotent. `inl(G)` は
normal (`SemidirectProduct.inl_range_normal`) かつ G 非自明より ≠ ⊥.
`commutator_lt_self_of_isNilpotent_ambient` を適用.

Isaacs 流の `⁅G, P⁆ < G` (G の中で見た [G, P]) と等価 (inl を介して identify).

C_G(P) > 1 (Lem 4.32 後半) は Γ の center > 1 経由で別途. -/
theorem commutator_inl_inr_lt_inl_of_pgroup_action
    {G P : Type*} [Group G] [Group P] [Finite G] [Finite P] [Nontrivial G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (hP : IsPGroup p P)
    (φ : P →* MulAut G) :
    ⁅(SemidirectProduct.inl : G →* G ⋊[φ] P).range,
      (SemidirectProduct.inr : P →* G ⋊[φ] P).range⁆ <
        (SemidirectProduct.inl : G →* G ⋊[φ] P).range := by
  haveI : Group.IsNilpotent (G ⋊[φ] P) :=
    Group.IsNilpotent.semidirectProduct_of_pGroup hG hP
  haveI : (SemidirectProduct.inl : G →* G ⋊[φ] P).range.Normal :=
    OddOrder.Isaacs.Ch03.inl_range_normal φ
  apply commutator_lt_self_of_isNilpotent_ambient
  -- inl.range ≠ ⊥: inl injective + G nontrivial
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  refine ⟨⟨SemidirectProduct.inl g, g, rfl⟩, ?_⟩
  intro h
  apply hg
  have : SemidirectProduct.inl g = (1 : G ⋊[φ] P) := Subtype.ext_iff.mp h
  exact SemidirectProduct.inl_injective this

/-- The left factor inclusion `P →* P × Q`. -/
def prodLeftHom (P Q : Type*) [Group P] [Group Q] : P →* P × Q where
  toFun p := (p, 1)
  map_one' := rfl
  map_mul' _ _ := by
    ext <;> simp

@[simp]
theorem prodLeftHom_apply {P Q : Type*} [Group P] [Group Q] (p : P) :
    prodLeftHom P Q p = (p, 1) :=
  by simp [prodLeftHom]

/-- The right factor inclusion `Q →* P × Q`. -/
def prodRightHom (P Q : Type*) [Group P] [Group Q] : Q →* P × Q where
  toFun q := (1, q)
  map_one' := rfl
  map_mul' _ _ := by
    ext <;> simp

@[simp]
theorem prodRightHom_apply {P Q : Type*} [Group P] [Group Q] (q : Q) :
    prodRightHom P Q q = (1, q) :=
  by simp [prodRightHom]

/-- In an external direct-product action, `[G, P]` is invariant under the whole
`P × Q` action. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator_prodLeft
    {G P Q : Type*} [Group G] [Group P] [Group Q] (φ : P × Q →* MulAut G) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutator (φ.comp (prodLeftHom P Q))) := by
  apply OddOrder.Isaacs.Ch03.IsAInvariant.closure_of_invariant_set
  intro b
  have key : ∀ g : G, ∀ p : P,
      (φ b) (g * (φ (prodLeftHom P Q p)) g⁻¹) =
        (φ b) g * (φ (prodLeftHom P Q (b.1 * p * b.1⁻¹))) ((φ b) g)⁻¹ := by
    intro g p
    rw [map_mul (φ b)]
    congr 1
    rw [show ((φ b) g)⁻¹ = (φ b) g⁻¹ from (map_inv (φ b) g).symm,
        show φ (prodLeftHom P Q (b.1 * p * b.1⁻¹)) =
            (φ b) * (φ (prodLeftHom P Q p)) * (φ b)⁻¹ from by
          rw [show prodLeftHom P Q (b.1 * p * b.1⁻¹) =
              b * prodLeftHom P Q p * b⁻¹ from by
            ext <;> simp [prodLeftHom, mul_assoc]]
          rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨g, p, rfl⟩, rfl⟩
    exact ⟨(φ b) g, b.1 * p * b.1⁻¹, by simpa using key g p⟩
  · rintro ⟨g, p, hx⟩
    have hx' : x = g * (φ (prodLeftHom P Q p)) g⁻¹ := by simpa using hx
    rw [hx']
    refine ⟨(φ b)⁻¹ g * (φ (prodLeftHom P Q (b.1⁻¹ * p * b.1))) ((φ b)⁻¹ g)⁻¹,
      ⟨(φ b)⁻¹ g, b.1⁻¹ * p * b.1, by simp⟩, ?_⟩
    rw [map_mul (φ b)]
    congr 1
    · exact MulAut.apply_inv_self (M := G) (φ b) g
    rw [show ((φ b)⁻¹ g)⁻¹ = (φ b)⁻¹ g⁻¹ from (map_inv ((φ b)⁻¹) g).symm,
        show φ (prodLeftHom P Q (b.1⁻¹ * p * b.1)) =
            (φ b)⁻¹ * (φ (prodLeftHom P Q p)) * (φ b) from by
          rw [show prodLeftHom P Q (b.1⁻¹ * p * b.1) =
              b⁻¹ * prodLeftHom P Q p * b from by
            ext <;> simp [prodLeftHom, mul_assoc]]
          rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, MulAut.apply_inv_self]

/-- If `Q ⊴ A`, then `[G,Q]` is invariant under the whole `A`-action. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator_of_normal
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G)
    (Q : Subgroup A) [Q.Normal] :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutator (φ.comp Q.subtype)) := by
  apply OddOrder.Isaacs.Ch03.IsAInvariant.closure_of_invariant_set
  intro b
  have key : ∀ g : G, ∀ q : Q,
      (φ b) (g * (φ q.val) g⁻¹) =
        (φ b) g * (φ (b * q.val * b⁻¹)) ((φ b) g)⁻¹ := by
    intro g q
    rw [map_mul (φ b)]
    congr 1
    rw [show ((φ b) g)⁻¹ = (φ b) g⁻¹ from (map_inv (φ b) g).symm,
        show φ (b * q.val * b⁻¹) = (φ b) * (φ q.val) * (φ b)⁻¹ from by
          rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨g, q, rfl⟩, rfl⟩
    have hbqb : b * q.val * b⁻¹ ∈ Q :=
      (inferInstance : Q.Normal).conj_mem q.val q.property b
    exact ⟨(φ b) g, ⟨b * q.val * b⁻¹, hbqb⟩, by simp⟩
  · rintro ⟨g, q, hx⟩
    have hx' : x = g * (φ q.val) g⁻¹ := by simpa using hx
    rw [hx']
    have hbqb : b⁻¹ * q.val * b ∈ Q := by
      simpa using (inferInstance : Q.Normal).conj_mem q.val q.property b⁻¹
    refine ⟨(φ b)⁻¹ g * (φ (b⁻¹ * q.val * b)) ((φ b)⁻¹ g)⁻¹,
      ⟨(φ b)⁻¹ g, ⟨b⁻¹ * q.val * b, hbqb⟩, by simp⟩, ?_⟩
    rw [map_mul (φ b)]
    congr 1
    · exact MulAut.apply_inv_self (M := G) (φ b) g
    rw [show ((φ b)⁻¹ g)⁻¹ = (φ b)⁻¹ g⁻¹ from (map_inv ((φ b)⁻¹) g).symm,
        show φ (b⁻¹ * q.val * b) = (φ b)⁻¹ * (φ q.val) * (φ b) from by
          rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, MulAut.apply_inv_self]

/-- Abelian case of Isaacs Theorem 4.38.

Let `P,Q ≤ A`, with `P` a p-group and `Q` normal p'. If every `P`-fixed
point of the abelian p-group `G` is also `Q`-fixed, then `[G,Q]=1`. -/
theorem actionCommutator_eq_bot_of_abelian_pgroup_of_subgroup_fixedPoints
    {A G : Type*} [Group A] [CommGroup G] [Finite A] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] (φ : A →* MulAut G) (hG : IsPGroup p G)
    (P Q : Subgroup A) [Q.Normal] (hP : IsPGroup p P) (hQ_p' : ¬ p ∣ Nat.card Q)
    (h_fix : ∀ g : G, (∀ x : P, (φ x.val) g = g) → ∀ y : Q, (φ y.val) g = g) :
    actionCommutator (φ.comp Q.subtype) = ⊥ := by
  let φQ : Q →* MulAut G := φ.comp Q.subtype
  have hCop : Nat.Coprime (Nat.card Q) (Nat.card G) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
    rw [hn]
    exact (Nat.Coprime.pow_right n
      (Nat.coprime_comm.mp (Nat.Prime.coprime_iff_not_dvd hp.out |>.mpr hQ_p')))
  have h_inf_bot := fixedPoints_inf_actionCommutator_eq_bot_of_abelian φQ hCop
  by_contra h_ne_bot
  have h_ne_bot' : actionCommutator φQ ≠ ⊥ := by
    simpa [φQ] using h_ne_bot
  haveI hH_pgrp : IsPGroup p (actionCommutator φQ) := hG.to_subgroup _
  haveI : Nontrivial (actionCommutator φQ) := by
    rw [Subgroup.ne_bot_iff_exists_ne_one] at h_ne_bot'
    obtain ⟨h, hh_ne⟩ := h_ne_bot'
    exact ⟨h, 1, hh_ne⟩
  have hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutator φQ) := by
    simpa [φQ] using OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator_of_normal φ Q
  let φH : A →* MulAut (actionCommutator φQ) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH_inv
  let φP_H : P →* MulAut (actionCommutator φQ) := φH.comp P.subtype
  have hP_fixed_ne :=
    fixedPoints_ne_bot_of_pgroup_action_pgroup hH_pgrp hP φP_H
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hP_fixed_ne
  obtain ⟨h, hh_ne⟩ := hP_fixed_ne
  have hP_fix_G : ∀ x : P, (φ x.val) h.1.val = h.1.val := by
    intro x
    have hx := congr_arg (Subtype.val : actionCommutator φQ → G) (h.property x)
    simpa [φP_H, φH] using hx
  have hQ_fix_G : ∀ y : Q, (φ y.val) h.1.val = h.1.val :=
    h_fix h.1.val hP_fix_G
  have h_mem_inf : h.1.val ∈ Subgroup.fixedPointsOfMulAut φQ ⊓ actionCommutator φQ :=
    Subgroup.mem_inf.mpr ⟨hQ_fix_G, h.1.property⟩
  have h_val_one : h.1.val = 1 := by
    rw [h_inf_bot, Subgroup.mem_bot] at h_mem_inf
    exact h_mem_inf
  apply hh_ne
  apply Subtype.ext
  apply Subtype.ext
  exact h_val_one

/-- Three-subgroups step for Isaacs Theorem 4.31 in external direct-product form.

Let `P × Q` act on `G`. If the `Q`-factor acts trivially on `[G, P]`, then
the `P`-factor acts trivially on `[G, Q]`. This is the semidirect-product
calculation corresponding to `[G,P,Q]=1` and `[P,Q,G]=1`, hence `[Q,G,P]=1`. -/
theorem prodLeft_fixes_actionCommutator_prodRight_of_prodRight_fixes_actionCommutator_prodLeft
    {G P Q : Type*} [Group G] [Group P] [Group Q] (φ : P × Q →* MulAut G)
    (hQ_on_GP : ∀ q : Q, ∀ h ∈ actionCommutator (φ.comp (prodLeftHom P Q)),
      (φ (1, q)) h = h) :
    ∀ p : P, ∀ h ∈ actionCommutator (φ.comp (prodRightHom P Q)),
      (φ (p, 1)) h = h := by
  let iP : P →* P × Q := prodLeftHom P Q
  let iQ : Q →* P × Q := prodRightHom P Q
  set XG : Subgroup (G ⋊[φ] (P × Q)) :=
    (SemidirectProduct.inl : G →* G ⋊[φ] (P × Q)).range
  set YP : Subgroup (G ⋊[φ] (P × Q)) :=
    ((SemidirectProduct.inr : P × Q →* G ⋊[φ] (P × Q)).comp iP).range
  set YQ : Subgroup (G ⋊[φ] (P × Q)) :=
    ((SemidirectProduct.inr : P × Q →* G ⋊[φ] (P × Q)).comp iQ).range
  have h_GP_eq : (actionCommutator (φ.comp iP)).map
      (SemidirectProduct.inl : G →* G ⋊[φ] (P × Q)) = ⁅XG, YP⁆ := by
    simpa [XG, YP, iP] using actionCommutator_map_inl_comp φ iP
  have h_GQ_eq : (actionCommutator (φ.comp iQ)).map
      (SemidirectProduct.inl : G →* G ⋊[φ] (P × Q)) = ⁅XG, YQ⁆ := by
    simpa [XG, YQ, iQ] using actionCommutator_map_inl_comp φ iQ
  have h_GPYQ : ⁅⁅XG, YP⁆, YQ⁆ = ⊥ := by
    rw [← h_GP_eq, eq_bot_iff, Subgroup.commutator_le]
    rintro _ ⟨k, hk, rfl⟩ _ ⟨q, rfl⟩
    change ⁅(SemidirectProduct.inl k : G ⋊[φ] (P × Q)),
      SemidirectProduct.inr (iQ q)⁆ ∈ (⊥ : Subgroup (G ⋊[φ] (P × Q)))
    rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
    have h_fix : (φ (iQ q)) k = k := by
      simpa [iQ] using hQ_on_GP q k hk
    rw [show (φ (iQ q)) k⁻¹ = ((φ (iQ q)) k)⁻¹ from map_inv (φ (iQ q)) k,
      h_fix, mul_inv_cancel]
    exact map_one _
  have h_PQ : ⁅YP, YQ⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    change ⁅(SemidirectProduct.inr (iP p) : G ⋊[φ] (P × Q)),
      SemidirectProduct.inr (iQ q)⁆ ∈ (⊥ : Subgroup (G ⋊[φ] (P × Q)))
    rw [Subgroup.mem_bot]
    ext <;> simp [commutatorElement_def, iP, iQ]
  have h_PQXG : ⁅⁅YP, YQ⁆, XG⁆ = ⊥ := by
    rw [h_PQ]
    exact Subgroup.commutator_bot_left XG
  have h_three : ⁅⁅YQ, XG⁆, YP⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h_GPYQ h_PQXG
  have h_GQYP : ⁅⁅XG, YQ⁆, YP⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm YQ XG] at h_three
  intro p h hh
  have h_in_GQ : (SemidirectProduct.inl h : G ⋊[φ] (P × Q)) ∈ ⁅XG, YQ⁆ := by
    rw [← h_GQ_eq]
    exact ⟨h, hh, rfl⟩
  have h_comm_mem : ⁅(SemidirectProduct.inl h : G ⋊[φ] (P × Q)),
      SemidirectProduct.inr (iP p)⁆ ∈ ⁅⁅XG, YQ⁆, YP⁆ :=
    Subgroup.commutator_mem_commutator h_in_GQ ⟨p, rfl⟩
  have h_comm_bot : ⁅(SemidirectProduct.inl h : G ⋊[φ] (P × Q)),
      SemidirectProduct.inr (iP p)⁆ ∈ (⊥ : Subgroup (G ⋊[φ] (P × Q))) := by
    rw [← h_GQYP]
    exact h_comm_mem
  rw [Subgroup.mem_bot, SemidirectProduct.commutator_inl_inr] at h_comm_bot
  have h_mul : h * (φ (iP p)) h⁻¹ = 1 :=
    SemidirectProduct.inl_injective (by simpa using h_comm_bot)
  rw [show (φ (iP p)) h⁻¹ = ((φ (iP p)) h)⁻¹ from map_inv (φ (iP p)) h] at h_mul
  rw [mul_inv_eq_one] at h_mul
  simpa [iP] using h_mul.symm

/-- Final coprime-action step for Isaacs Theorem 4.31 in external direct-product form.

If `Q` is a `p'`-group acting on the `p`-group `G`, `Q` acts trivially on
`[G,P]`, and every `P`-fixed element of `G` is `Q`-fixed, then `[G,Q] = 1`.
Together with induction providing the first hypothesis, this is the last
paragraph of Isaacs Thm 4.31. -/
theorem actionCommutator_prodRight_eq_bot_of_prodRight_fixes_actionCommutator_prodLeft
    {G P Q : Type*} [Group G] [Group P] [Group Q] [Finite G] [Finite Q]
    {p : ℕ} [hp : Fact p.Prime] (φ : P × Q →* MulAut G)
    (hG : IsPGroup p G) (hQ_p' : ¬ p ∣ Nat.card Q)
    (hQ_on_GP : ∀ q : Q, ∀ h ∈ actionCommutator (φ.comp (prodLeftHom P Q)),
      (φ (1, q)) h = h)
    (h_fix : ∀ g : G, (∀ x : P, (φ (x, 1)) g = g) → ∀ y : Q, (φ (1, y)) g = g) :
    actionCommutator (φ.comp (prodRightHom P Q)) = ⊥ := by
  let φQ : Q →* MulAut G := φ.comp (prodRightHom P Q)
  have hP_on_GQ :
      ∀ x : P, ∀ h ∈ actionCommutator (φ.comp (prodRightHom P Q)),
        (φ (x, 1)) h = h :=
    prodLeft_fixes_actionCommutator_prodRight_of_prodRight_fixes_actionCommutator_prodLeft
      φ hQ_on_GP
  have h_triv : ∀ q : Q, ∀ h ∈ actionCommutator φQ, (φQ q) h = h := by
    intro q h hh
    have hP_fix : ∀ x : P, (φ (x, 1)) h = h := by
      intro x
      exact hP_on_GQ x h (by simpa [φQ] using hh)
    simpa [φQ] using h_fix h hP_fix q
  have hCop : Nat.Coprime (Nat.card Q) (Nat.card G) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
    rw [hk]
    exact (((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hQ_p').symm).pow_right k
  haveI : Group.IsNilpotent G := hG.isNilpotent
  have hSolv : IsSolvable Q ∨ IsSolvable G := Or.inr IsNilpotent.to_isSolvable
  exact actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime
    (A := Q) (G := G) (φ := φQ) hCop hSolv h_triv

/-- Finite subgroup card strictly drops for a proper subgroup. -/
private theorem subgroup_card_lt_of_ne_top {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hH : H ≠ ⊤) :
    Nat.card H < Nat.card G := by
  have h_dvd : Nat.card H ∣ Nat.card G :=
    ⟨H.index, by rw [mul_comm, H.index_mul_card]⟩
  have h_le : Nat.card H ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos h_dvd
  have h_ne : Nat.card H ≠ Nat.card G := fun heq =>
    hH (Subgroup.eq_top_of_card_eq _ heq)
  exact Nat.lt_of_le_of_ne h_le h_ne

/-- Strong-induction form of Isaacs Theorem 4.31 for external direct products. -/
private theorem isaacs_thm_4_31_external_aux
    {P Q : Type*} [Group P] [Group Q] [Finite P] [Finite Q]
    {p : ℕ} [hp : Fact p.Prime] (hP : IsPGroup p P) (hQ_p' : ¬ p ∣ Nat.card Q) :
    ∀ n : ℕ, ∀ {G : Type*} [Group G] [Finite G]
    (φ : P × Q →* MulAut G) (_ : IsPGroup p G)
    (_ : ∀ g : G, (∀ x : P, (φ (x, 1)) g = g) → ∀ y : Q, (φ (1, y)) g = g),
    Nat.card G ≤ n → actionCommutator (φ.comp (prodRightHom P Q)) = ⊥ := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ _ _ h_le
    exfalso
    have h_pos : 0 < Nat.card G := Nat.card_pos
    omega
  | succ m IH =>
    intro G _ _ φ hG h_fix h_le
    rcases Nat.lt_or_ge (Nat.card G) (m + 1) with h_lt | h_ge
    · exact IH φ hG h_fix (Nat.le_of_lt_succ h_lt)
    have h_card_G : Nat.card G = m + 1 := le_antisymm h_le h_ge
    by_cases hG_nontriv : Nontrivial G
    swap
    · haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG_nontriv
      rw [actionCommutator_eq_bot_iff_acts_trivially]
      intro q g
      exact Subsingleton.elim _ _
    letI : Nontrivial G := hG_nontriv
    let φP : P →* MulAut G := φ.comp (prodLeftHom P Q)
    set H : Subgroup G := actionCommutator φP with hH_def
    have h_lt_comm : ⁅(SemidirectProduct.inl : G →* G ⋊[φP] P).range,
        (SemidirectProduct.inr : P →* G ⋊[φP] P).range⁆ <
          (SemidirectProduct.inl : G →* G ⋊[φP] P).range :=
      commutator_inl_inr_lt_inl_of_pgroup_action hG hP φP
    have hH_ne_top : H ≠ ⊤ := by
      intro htop
      have hmap : H.map (SemidirectProduct.inl : G →* G ⋊[φP] P) =
          (SemidirectProduct.inl : G →* G ⋊[φP] P).range := by
        rw [htop]
        exact (MonoidHom.range_eq_map _).symm
      rw [hH_def, actionCommutator_map_inl] at hmap
      exact h_lt_comm.ne hmap
    have hH_card_lt : Nat.card H < Nat.card G := subgroup_card_lt_of_ne_top hH_ne_top
    have hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H := by
      rw [hH_def]
      simpa [φP] using OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator_prodLeft φ
    let φH : P × Q →* MulAut H :=
      OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH_inv
    have hH_pgrp : IsPGroup p H := hG.to_subgroup H
    have h_fix_H :
        ∀ h : H, (∀ x : P, (φH (x, 1)) h = h) → ∀ y : Q, (φH (1, y)) h = h := by
      intro h hP_fix y
      apply Subtype.ext
      have hP_fix_val : ∀ x : P, (φ (x, 1)) h.val = h.val := by
        intro x
        have hx := congr_arg (Subtype.val : H → G) (hP_fix x)
        simpa [φH] using hx
      have hQ_fix := h_fix h.val hP_fix_val y
      simpa [φH] using hQ_fix
    have hIH_H := IH φH hH_pgrp h_fix_H
      (Nat.le_of_lt_succ (hH_card_lt.trans_le h_le))
    have hQ_on_GP :
        ∀ q : Q, ∀ h ∈ actionCommutator (φ.comp (prodLeftHom P Q)), (φ (1, q)) h = h := by
      intro q h hh
      rw [actionCommutator_eq_bot_iff_acts_trivially] at hIH_H
      have h_in_H : h ∈ H := by
        simpa [H, φP] using hh
      have hact := congr_arg (Subtype.val : H → G) (hIH_H q ⟨h, h_in_H⟩)
      simpa [φH] using hact
    exact actionCommutator_prodRight_eq_bot_of_prodRight_fixes_actionCommutator_prodLeft
      φ hG hQ_p' hQ_on_GP h_fix

/-- **Isaacs Theorem 4.31** (external direct-product form).

Let `P × Q` act on the `p`-group `G`, with `P` a `p`-group and `Q` a
`p'`-group. If every element of `G` fixed by the `P`-factor is fixed by the
`Q`-factor, then the `Q`-factor acts trivially on `G`. -/
theorem isaacs_thm_4_31_external
    {G P Q : Type*} [Group G] [Group P] [Group Q] [Finite G] [Finite P] [Finite Q]
    {p : ℕ} [Fact p.Prime] (φ : P × Q →* MulAut G)
    (hG : IsPGroup p G) (hP : IsPGroup p P) (hQ_p' : ¬ p ∣ Nat.card Q)
    (h_fix : ∀ g : G, (∀ x : P, (φ (x, 1)) g = g) → ∀ y : Q, (φ (1, y)) g = g) :
    actionCommutator (φ.comp (prodRightHom P Q)) = ⊥ :=
  isaacs_thm_4_31_external_aux hP hQ_p' (Nat.card G) φ hG h_fix le_rfl

/-- First step toward **Isaacs Theorem 4.33**: if `Q = O_{p'}(N_G(P))`, then `Q`
centralizes the ambient `p`-core `O_p(G)`.

The proof is the 4.33 argument up to the Hall-Higman step.  Let `H = N_G(P)`,
`U = O_p(G)`, and `Q = O_{p'}(H)`.  Since `P ⊴ H` and `Q ⊴ H` have coprime
types, they commute, so `P × Q` acts on `U` by conjugation.  If `u ∈ U` is
fixed by `P`, then `u ∈ C_G(P) ≤ H`; hence `u ∈ U.subgroupOf H`, a normal
`p`-subgroup of `H`, and therefore `Q` fixes `u`.  Isaacs 4.31 then makes
the `Q`-action on `U` trivial. -/
theorem oPiCore_compl_normalizer_le_centralizer_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hP : IsPGroup p P) :
    (OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)}
        (Subgroup.normalizer (P : Set G))).map
        (Subgroup.normalizer (P : Set G)).subtype ≤
      Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) := by
  classical
  set H : Subgroup G := Subgroup.normalizer (P : Set G) with hH_def
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set PH : Subgroup H := P.subgroupOf H with hPH_def
  set Q : Subgroup H :=
    OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} H with hQ_def
  change Q.map H.subtype ≤ Subgroup.centralizer (U : Set G)
  have hP_le_H : P ≤ H := by
    rw [hH_def]
    exact Subgroup.le_normalizer
  haveI hPH_normal : PH.Normal := by
    rw [hPH_def, hH_def]
    exact Subgroup.normal_in_normalizer
  haveI hQ_normal : Q.Normal := by
    rw [hQ_def]
    infer_instance
  haveI hU_normal : U.Normal := by
    rw [hU_def]
    infer_instance
  have hPH_p : IsPGroup p PH := by
    rw [hPH_def]
    exact hP.of_equiv (Subgroup.subgroupOfEquivOfLe hP_le_H).symm
  have hQ_pi :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} Q := by
    rw [hQ_def]
    exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup {q | q ∉ ({p} : Set ℕ)}
  have hQ_p' : ¬ p ∣ Nat.card Q := by
    intro hp_dvd
    have hp_pf : p ∈ (Nat.card Q).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Fact.out, hp_dvd, Nat.card_pos.ne'⟩
    exact hQ_pi p hp_pf (by simp)
  have hPH_Q_comm : ∀ x y : H, x ∈ PH → y ∈ Q → Commute x y :=
    commute_of_normal_isPGroup_of_normal_isPiCompl hPH_p hQ_pi
  let pqMul : PH × Q →* H := {
    toFun z := z.1.val * z.2.val
    map_one' := by ext; simp
    map_mul' := by
      intro a b
      ext
      simp only [Prod.mul_def]
      change (((a.1.val * b.1.val) * (a.2.val * b.2.val) : H) : G) =
        (((a.1.val * a.2.val) * (b.1.val * b.2.val) : H) : G)
      have hc : Commute (a.2.val : H) (b.1.val : H) :=
        (hPH_Q_comm b.1.val a.2.val b.1.property a.2.property).symm
      rw [mul_assoc, ← mul_assoc b.1.val a.2.val b.2.val, ← hc.eq]
      group }
  let ψ : PH × Q →* G := H.subtype.comp pqMul
  let φ : PH × Q →* MulAut U := (MulAut.conjNormal : G →* MulAut U).comp ψ
  have hU_p : IsPGroup p U := by
    rw [hU_def]
    exact OddOrder.Isaacs.Ch01.opCore_isPGroup p G
  have hfix :
      ∀ u : U, (∀ x : PH, (φ (x, 1)) u = u) → ∀ y : Q, (φ (1, y)) u = u := by
    intro u hu y
    have hu_cent : (u : G) ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hxP
      have hfixed_x :=
        congr_arg (Subtype.val : U → G) (hu ⟨⟨x, hP_le_H hxP⟩, by simpa [PH] using hxP⟩)
      have hxconj : x * (u : G) * x⁻¹ = (u : G) := by
        simpa [φ, ψ, pqMul, MulAut.conjNormal_apply] using hfixed_x
      calc
        x * (u : G) = (x * (u : G) * x⁻¹) * x := by group
        _ = (u : G) * x := by rw [hxconj]
    have huH : (u : G) ∈ H := by
      rw [hH_def]
      exact centralizer_le_normalizer_subgroup P hu_cent
    let uH : H := ⟨u, huH⟩
    set UH : Subgroup H := U.subgroupOf H with hUH_def
    haveI hUH_normal : UH.Normal := by
      rw [hUH_def]
      exact (show U.Normal from inferInstance).subgroupOf H
    let incUH_U : UH →* U := {
      toFun x := ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have hUH_p : IsPGroup p UH :=
      hU_p.of_injective incUH_U (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congr_arg (Subtype.val : U → G) hab)
    have hu_UH : uH ∈ UH := by
      rw [hUH_def]
      change (u : G) ∈ U
      exact u.property
    have hUH_Q_comm : ∀ x y : H, x ∈ UH → y ∈ Q → Commute x y :=
      commute_of_normal_isPGroup_of_normal_isPiCompl hUH_p hQ_pi
    have hcomm_u_y : Commute uH y.val :=
      hUH_Q_comm uH y.val hu_UH y.property
    apply Subtype.ext
    have hyconj_H : (y.val : H) * uH * (y.val : H)⁻¹ = uH := by
      have hyu : (y.val : H) * uH = uH * y.val := hcomm_u_y.symm.eq
      calc
        (y.val : H) * uH * (y.val : H)⁻¹ = (uH * y.val) * (y.val : H)⁻¹ := by rw [hyu]
        _ = uH := by group
    have hyconj_G := congr_arg (Subtype.val : H → G) hyconj_H
    simpa [φ, ψ, pqMul, MulAut.conjNormal_apply] using hyconj_G
  have hAC_bot : actionCommutator (φ.comp (prodRightHom PH Q)) = ⊥ :=
    isaacs_thm_4_31_external φ hU_p hPH_p hQ_p' hfix
  rw [actionCommutator_eq_bot_iff_acts_trivially] at hAC_bot
  rintro g ⟨q, hq, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u huU
  let qQ : Q := ⟨q, hq⟩
  let uU : U := ⟨u, huU⟩
  have hqfix := congr_arg (Subtype.val : U → G) (hAC_bot qQ uU)
  have hqconj : ((q : H) : G) * u * ((q : H) : G)⁻¹ = u := by
    simpa [φ, ψ, pqMul, MulAut.conjNormal_apply] using hqfix
  have hqu : ((q : H) : G) * u = u * ((q : H) : G) := by
    calc
      ((q : H) : G) * u =
          (((q : H) : G) * u * ((q : H) : G)⁻¹) * ((q : H) : G) := by group
      _ = u * ((q : H) : G) := by rw [hqconj]
  exact hqu.symm

/-- Reduced form of **Isaacs Theorem 4.33** after the Hall-Higman reduction:
if `G` is `p`-separable and `O_{p'}(G) = 1`, then every normalizer of a
`p`-subgroup has trivial `p'`-core.

The preceding lemma puts the image of `O_{p'}(N_G(P))` inside
`C_G(O_p(G))`; Hall-Higman puts this centralizer inside `O_p(G)`.  The image is
therefore simultaneously a `p`-group and a `p'`-group, hence trivial. -/
theorem oPiCore_compl_normalizer_eq_bot_of_oPiCore_compl_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hπ' : OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥)
    (P : Subgroup G) (hP : IsPGroup p P) :
    OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)}
        (Subgroup.normalizer (P : Set G)) = ⊥ := by
  classical
  set H : Subgroup G := Subgroup.normalizer (P : Set G) with hH_def
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set Q : Subgroup H :=
    OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} H with hQ_def
  set K : Subgroup G := Q.map H.subtype with hK_def
  change Q = ⊥
  have hK_le_cent : K ≤ Subgroup.centralizer (U : Set G) := by
    rw [hK_def, hQ_def, hH_def, hU_def]
    exact oPiCore_compl_normalizer_le_centralizer_opCore P hP
  have hcent_le_U : Subgroup.centralizer (U : Set G) ≤ U := by
    rw [hU_def]
    exact hall_higman_opCore hπ'
  have hK_le_U : K ≤ U := hK_le_cent.trans hcent_le_U
  have hU_p : IsPGroup p U := by
    rw [hU_def]
    exact OddOrder.Isaacs.Ch01.opCore_isPGroup p G
  have hK_p : IsPGroup p K := hU_p.to_le hK_le_U
  have hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) K :=
    isPiGroup_singleton_of_isPGroup hK_p
  have hQ_pi :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} Q := by
    rw [hQ_def]
    exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup {q | q ∉ ({p} : Set ℕ)}
  have hK_pi' :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} K := by
    intro q hq
    have hcard : Nat.card K = Nat.card Q := by
      rw [hK_def]
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective Q H.subtype H.subtype_injective).symm.toEquiv
    rw [hcard] at hq
    exact hQ_pi q hq
  have hcop : Nat.Coprime (Nat.card K) (Nat.card K) :=
    OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne' hK_pi hK_pi'
  have hK_bot : K = ⊥ := by
    have hInf : K ⊓ K = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
    simpa using hInf
  exact (Subgroup.map_eq_bot_iff_of_injective Q H.subtype_injective).mp
    (by simpa [hK_def] using hK_bot)

/-- **Isaacs Theorem 4.33** (p-local `p'`-core containment).

If `G` is finite `p`-separable and `H` is `p`-local in `G`, then
`O_{p'}(H) ≤ O_{p'}(G)`, expressed by mapping `O_{p'}(H)` from `↥H` back into
`G`.

The general case quotients by `N = O_{p'}(G)`.  Lemma 2.17 sends `p`-local
subgroups to `p`-local subgroups modulo the `p'`-kernel, the reduced theorem
above kills the `p'`-core in the quotient, and triviality of the quotient image
is exactly containment in `N`. -/
theorem oPiCore_compl_le_oPiCore_compl_of_isPLocal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (H : Subgroup G) (hH : OddOrder.Isaacs.Ch02.IsPLocal p H) :
    (OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} H).map H.subtype ≤
      OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G := by
  classical
  set π' : Set ℕ := {q | q ∉ ({p} : Set ℕ)} with hπ'_def
  set N : Subgroup G := OddOrder.Isaacs.Ch03.oPiCore π' G with hN_def
  set f : G →* G ⧸ N := QuotientGroup.mk' N with hf_def
  set Hbar : Subgroup (G ⧸ N) := H.map f with hHbar_def
  set Q : Subgroup H := OddOrder.Isaacs.Ch03.oPiCore π' H with hQ_def
  change Q.map H.subtype ≤ N
  have hN_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π' N := by
    rw [hN_def]
    exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup π'
  have hp_coprime_N : ¬ p ∣ Nat.card N := by
    intro hp_dvd
    have hp_pf : p ∈ (Nat.card N).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Fact.out, hp_dvd, Nat.card_pos.ne'⟩
    have hp_not : p ∈ π' := hN_pi' p hp_pf
    rw [hπ'_def] at hp_not
    exact hp_not (by simp)
  have hHbar_pLocal : OddOrder.Isaacs.Ch02.IsPLocal p Hbar := by
    rw [hHbar_def, hf_def]
    exact OddOrder.Isaacs.Ch02.isPLocal_map_of_coprime_kernel hp_coprime_N hH
  have hOpi'_Gbar_bot : OddOrder.Isaacs.Ch03.oPiCore π' (G ⧸ N) = ⊥ := by
    simpa [hN_def] using OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot (G := G) π'
  have hOpi'_Hbar_bot : OddOrder.Isaacs.Ch03.oPiCore π' Hbar = ⊥ := by
    obtain ⟨Pbar, _hPbar_ne, hPbar_p, hHbar_eq⟩ := hHbar_pLocal
    rw [hHbar_eq]
    exact oPiCore_compl_normalizer_eq_bot_of_oPiCore_compl_eq_bot
      (G := G ⧸ N) (p := p) hOpi'_Gbar_bot Pbar hPbar_p
  let fH : H →* Hbar := f.subgroupMap H
  have hfH_surj : Function.Surjective fH := f.subgroupMap_surjective H
  haveI hQ_normal : Q.Normal := by
    rw [hQ_def]
    infer_instance
  haveI hQbar_normal : (Q.map fH).Normal := hQ_normal.map fH hfH_surj
  have hQ_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π' Q := by
    rw [hQ_def]
    exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup π'
  have hQbar_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π' (Q.map fH) := by
    intro r hr
    exact hQ_pi' r (Nat.primeFactors_mono (Q.card_map_dvd fH) Nat.card_pos.ne' hr)
  have hQbar_le : Q.map fH ≤ OddOrder.Isaacs.Ch03.oPiCore π' Hbar :=
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore hQbar_pi'
  have hQbar_bot : Q.map fH = ⊥ := by
    rw [hOpi'_Hbar_bot] at hQbar_le
    exact le_bot_iff.mp hQbar_le
  rintro y ⟨q, hq, rfl⟩
  have hqbar_mem : fH q ∈ Q.map fH := ⟨q, hq, rfl⟩
  rw [hQbar_bot, Subgroup.mem_bot] at hqbar_mem
  have hfq_one : f (q : G) = 1 := by
    change (f.subgroupMap H q).val = (1 : G ⧸ N)
    rw [show f.subgroupMap H q = fH q from rfl, hqbar_mem]
    rfl
  change (q : G) ∈ N
  rw [← QuotientGroup.eq_one_iff]
  simpa [hf_def] using hfq_one

/-- Strong-induction form of Isaacs Theorem 4.38. -/
private theorem isaacs_thm_4_38_aux
    {A : Type*} [Group A] [Finite A]
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    (P Q : Subgroup A) [Q.Normal] (hP : IsPGroup p P) (hQ_p' : ¬ p ∣ Nat.card Q) :
    ∀ n : ℕ, ∀ {G : Type*} [Group G] [Finite G]
    (φ : A →* MulAut G) (_ : IsPGroup p G)
    (_ : ∀ g : G, (∀ x : P, (φ x.val) g = g) → ∀ y : Q, (φ y.val) g = g),
    Nat.card G ≤ n → actionCommutator (φ.comp Q.subtype) = ⊥ := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ _ _ h_le
    exfalso
    have h_pos : 0 < Nat.card G := Nat.card_pos
    omega
  | succ m IH =>
    intro G _ _ φ hG h_fix h_le
    rcases Nat.lt_or_ge (Nat.card G) (m + 1) with h_lt | h_ge
    · exact IH φ hG h_fix (Nat.le_of_lt_succ h_lt)
    by_cases hG_nontriv : Nontrivial G
    swap
    · haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG_nontriv
      rw [actionCommutator_eq_bot_iff_acts_trivially]
      intro q g
      exact Subsingleton.elim _ _
    letI : Nontrivial G := hG_nontriv
    let φQ : Q →* MulAut G := φ.comp Q.subtype
    have hCop : Nat.Coprime (Nat.card Q) (Nat.card G) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
      rw [hk]
      exact (((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hQ_p').symm).pow_right k
    haveI hG_nilp : Group.IsNilpotent G := hG.isNilpotent
    have hG_solv : IsSolvable G := IsNilpotent.to_isSolvable
    have hSolv : IsSolvable Q ∨ IsSolvable G := Or.inr hG_solv
    by_cases h_AC_top : actionCommutator φQ = ⊤
    swap
    · set H : Subgroup G := actionCommutator φQ with hH_def
      have hH_card_lt : Nat.card H < Nat.card G := subgroup_card_lt_of_ne_top h_AC_top
      have hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H := by
        rw [hH_def]
        simpa [φQ] using OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator_of_normal φ Q
      let φH : A →* MulAut H :=
        OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH_inv
      have hH_pgrp : IsPGroup p H := hG.to_subgroup H
      have h_fix_H :
          ∀ h : H, (∀ x : P, (φH x.val) h = h) → ∀ y : Q, (φH y.val) h = h := by
        intro h hP_fix y
        apply Subtype.ext
        have hP_fix_val : ∀ x : P, (φ x.val) h.val = h.val := by
          intro x
          have hx := congr_arg (Subtype.val : H → G) (hP_fix x)
          simpa [φH] using hx
        have hQ_fix := h_fix h.val hP_fix_val y
        simpa [φH] using hQ_fix
      have hIH_H := IH φH hH_pgrp h_fix_H
        (Nat.le_of_lt_succ (hH_card_lt.trans_le h_le))
      have h_triv : ∀ q : Q, ∀ x ∈ H, (φ q.val) x = x := by
        intro q x hx
        rw [actionCommutator_eq_bot_iff_acts_trivially] at hIH_H
        have hact := congr_arg (Subtype.val : H → G) (hIH_H q ⟨x, hx⟩)
        simpa [φH] using hact
      exact actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime
        (A := Q) (G := G) (φ := φQ) hCop hSolv h_triv
    set G' : Subgroup G := commutator G with hG'_def
    have hG'_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ G' :=
      OddOrder.Isaacs.Ch03.IsAInvariant.derivedSeries φ 1
    have h_G'_lt_top : G' < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial G
    have h_G'_card_lt : Nat.card G' < Nat.card G :=
      subgroup_card_lt_of_ne_top h_G'_lt_top.ne
    let φG' : A →* MulAut G' :=
      OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hG'_inv
    have hG'_pgrp : IsPGroup p G' := hG.to_subgroup G'
    have h_fix_G' :
        ∀ g' : G', (∀ x : P, (φG' x.val) g' = g') → ∀ y : Q, (φG' y.val) g' = g' := by
      intro g' hP_fix y
      apply Subtype.ext
      have hP_fix_val : ∀ x : P, (φ x.val) g'.val = g'.val := by
        intro x
        have hx := congr_arg (Subtype.val : G' → G) (hP_fix x)
        simpa [φG'] using hx
      have hQ_fix := h_fix g'.val hP_fix_val y
      simpa [φG'] using hQ_fix
    have hIH_G' := IH φG' hG'_pgrp h_fix_G'
      (Nat.le_of_lt_succ (h_G'_card_lt.trans_le h_le))
    have h_triv_G' : ∀ q : Q, ∀ g' ∈ G', (φ q.val) g' = g' := by
      intro q g' hg'
      rw [actionCommutator_eq_bot_iff_acts_trivially] at hIH_G'
      have hact := congr_arg (Subtype.val : G' → G) (hIH_G' q ⟨g', hg'⟩)
      simpa [φG'] using hact
    have h_class_le_2 : commutator G ≤ Subgroup.center G := by
      set XG : Subgroup (G ⋊[φQ] Q) := (SemidirectProduct.inl : G →* G ⋊[φQ] Q).range
      set YQ : Subgroup (G ⋊[φQ] Q) := (SemidirectProduct.inr : Q →* G ⋊[φQ] Q).range
      set XG' : Subgroup (G ⋊[φQ] Q) := G'.map (SemidirectProduct.inl : G →* G ⋊[φQ] Q)
      have h_G'_YQ : ⁅XG', YQ⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        rintro _ ⟨k, hk, rfl⟩ _ ⟨q, rfl⟩
        rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
        have h_fix' : (φQ q) k = k := by
          simpa [φQ] using h_triv_G' q k hk
        rw [show (φQ q) k⁻¹ = ((φQ q) k)⁻¹ from map_inv (φQ q) k,
          h_fix', mul_inv_cancel]
        exact map_one _
      have h_GG'_le : ⁅XG, XG'⁆ ≤ XG' := by
        rw [Subgroup.commutator_le]
        rintro _ ⟨g, rfl⟩ _ ⟨k, hk, rfl⟩
        rw [show (⁅(SemidirectProduct.inl g : G ⋊[φQ] Q), SemidirectProduct.inl k⁆ :
            G ⋊[φQ] Q) = SemidirectProduct.inl ⁅g, k⁆ from by
          simp [commutatorElement_def, ← map_mul, ← map_inv]]
        refine ⟨⁅g, k⁆, ?_, rfl⟩
        have hG'_normal : G'.Normal := inferInstance
        have h_gkg : g * k * g⁻¹ ∈ G' := hG'_normal.conj_mem k hk g
        have h_inv : k⁻¹ ∈ G' := G'.inv_mem hk
        rw [commutatorElement_def]
        exact G'.mul_mem h_gkg h_inv
      have h12 : ⁅⁅XG, XG'⁆, YQ⁆ = ⊥ := by
        rw [eq_bot_iff]
        calc ⁅⁅XG, XG'⁆, YQ⁆ ≤ ⁅XG', YQ⁆ := Subgroup.commutator_mono h_GG'_le le_rfl
          _ = ⊥ := h_G'_YQ
      have h23 : ⁅⁅XG', YQ⁆, XG⁆ = ⊥ := by
        rw [h_G'_YQ]
        exact Subgroup.commutator_bot_left XG
      have h_three : ⁅⁅YQ, XG⁆, XG'⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate h12 h23
      have h_XGYQ_eq_XG : ⁅XG, YQ⁆ = XG := by
        rw [← actionCommutator_map_inl φQ, h_AC_top]
        exact (MonoidHom.range_eq_map _).symm
      have h_YQXG_eq_XG : ⁅YQ, XG⁆ = XG := by
        rw [Subgroup.commutator_comm]
        exact h_XGYQ_eq_XG
      have h_XG_XG'_bot : ⁅XG, XG'⁆ = ⊥ := h_YQXG_eq_XG ▸ h_three
      have h_top_G'_bot : ⁅(⊤ : Subgroup G), G'⁆ = ⊥ := by
        apply Subgroup.map_injective (f := (SemidirectProduct.inl : G →* G ⋊[φQ] Q))
          SemidirectProduct.inl_injective
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.map_bot]
        exact h_XG_XG'_bot
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h_top_G'_bot
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have := h_top_G'_bot (Subgroup.mem_top y)
      exact (this x hx).symm
    have hOdd_p : Odd p := hp.out.odd_of_ne_two hp_odd
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
    have hOdd_card : Odd (Nat.card G) := by
      rw [hk]
      exact hOdd_p.pow
    haveI : Fact (Odd (Nat.card G)) := ⟨hOdd_card⟩
    haveI : Fact (_root_.commutator G ≤ Subgroup.center G) := ⟨h_class_le_2⟩
    set φ' : A →* MulAut (BaerMul G) := MonoidHom.toBaerMulLift φ with hφ'
    have hG_baer : IsPGroup p (BaerMul G) := (BaerMul.isPGroup_iff p).mpr hG
    have h_fix_baer :
        ∀ g : BaerMul G, (∀ x : P, (φ' x.val) g = g) →
          ∀ y : Q, (φ' y.val) g = g := by
      intro g hP_fix y
      have hP_fix_G : ∀ x : P, (φ x.val) (BaerMul.toG g) = BaerMul.toG g := by
        intro x
        have hx := congr_arg BaerMul.toG (hP_fix x)
        simpa [hφ'] using hx
      have h_fixed : (φ y.val) (BaerMul.toG g) = BaerMul.toG g :=
        h_fix (BaerMul.toG g) hP_fix_G y
      change BaerMul.ofG ((φ y.val) (BaerMul.toG g)) = g
      rw [h_fixed]
      exact BaerMul.ofG_toG g
    have h_bot_baer :=
      actionCommutator_eq_bot_of_abelian_pgroup_of_subgroup_fixedPoints
        φ' hG_baer P Q hP hQ_p' h_fix_baer
    rw [actionCommutator_eq_bot_iff_acts_trivially] at h_bot_baer
    rw [actionCommutator_eq_bot_iff_acts_trivially]
    intro q g
    have h_act := h_bot_baer q (BaerMul.ofG g)
    have h_eq : BaerMul.ofG ((φ q.val) g) = BaerMul.ofG g := by
      have hkey : (φ' q.val) (BaerMul.ofG g) = BaerMul.ofG ((φ q.val) g) := by
        change BaerMul.ofG ((φ q.val) (BaerMul.toG (BaerMul.ofG g))) =
          BaerMul.ofG ((φ q.val) g)
        rw [BaerMul.toG_ofG]
      rw [← hkey]
      exact h_act
    exact BaerMul.ofG.injective h_eq

/-- **Isaacs Theorem 4.38**.

Let `A` act on the p-group `G` with `p > 2`. If `P ≤ A` is a p-group,
`Q ⊴ A` is p', and every `P`-fixed point of `G` is `Q`-fixed, then `Q`
acts trivially on `G`. -/
theorem isaacs_thm_4_38
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (φ : A →* MulAut G) (hG : IsPGroup p G)
    (P Q : Subgroup A) [Q.Normal] (hP : IsPGroup p P) (hQ_p' : ¬ p ∣ Nat.card Q)
    (h_fix : ∀ g : G, (∀ x : P, (φ x.val) g = g) → ∀ y : Q, (φ y.val) g = g) :
    actionCommutator (φ.comp Q.subtype) = ⊥ :=
  isaacs_thm_4_38_aux hp_odd P Q hP hQ_p' (Nat.card G) φ hG h_fix le_rfl

end -- 4D

/-! ### Isaacs §4C Thm 4.24 ⭐: faithful chain action ⇒ A nilpotent

**ステートメント** (Isaacs p.139): `A`, `G` finite. `A` が `G` に faithful に作用 +
`[G, A, ..., A]_m = 1` ⇒ `A` is nilpotent.

**証明戦略**: `|G|`-induction で **`A^∞` acts trivially on `G`** (non-faithful generalized
form) を示す. faithful 仮定下では `A^∞ ⊆ C_A(G) = ⊥` から `A` nilpotent.

**Phase 1 (本ファイル)**: `lowerCentralSeriesInfty A := lcs A (Nat.card A)` の infra と
stability lemma. Phase 2/3 (three-subgroups helpers + main theorem) は後続. -/

section /- §4C (続): Theorem 4.24 — faithful chain action ⇒ `A` nilpotent (infra) -/

variable {A : Type*} [Group A]

/-- 真部分群は真に小さい濃度を持つ (`Set.Finite.card_lt_card` の Subgroup 版). -/
private lemma nat_card_lt_of_subgroup_lt {G : Type*} [Group G] [Finite G]
    {H₁ H₂ : Subgroup G} (h : H₁ < H₂) :
    Nat.card H₁ < Nat.card H₂ := by
  exact Set.Finite.card_lt_card (Set.toFinite _) (SetLike.coe_ssubset_coe.mpr h)

/-- 鳩の巣論法: 有限群の lcs は `Nat.card A` step 以内に必ず stabilize する.
    具体的には `lcs A (Nat.card A) = lcs A (Nat.card A + 1)`. -/
private lemma lowerCentralSeries_card_eq_succ_card [Finite A] :
    lowerCentralSeries A (Nat.card A) = lowerCentralSeries A (Nat.card A + 1) := by
  -- antitone を使って ≤ は trivial. < は矛盾を導く.
  refine le_antisymm ?_ (lowerCentralSeries_antitone (Nat.le_succ _))
  -- by contradiction: もし lcs (N+1) < lcs N なら、それまで全 step も strict
  -- かもしれない. しかしそうとは限らないので、別ルートで.
  -- Claim: ∃ k ≤ Nat.card A, lcs k = lcs (k+1). これを取れば stability propagation.
  suffices h : ∃ k ≤ Nat.card A, lowerCentralSeries A k = lowerCentralSeries A (k + 1) by
    obtain ⟨k, hk_le, hk_eq⟩ := h
    -- propagate: lcs k = lcs (k+1) ⇒ lcs (k+j) = lcs k for all j
    have h_prop : ∀ j, lowerCentralSeries A (k + j) = lowerCentralSeries A k := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
          have h1 : lowerCentralSeries A (k + (j + 1)) =
              ⁅lowerCentralSeries A (k + j), ⊤⁆ := rfl
          rw [h1, ih]
          have h2 : lowerCentralSeries A (k + 1) = ⁅lowerCentralSeries A k, ⊤⁆ := rfl
          rw [← h2, hk_eq]
    -- want: lcs (Nat.card A) ≤ lcs (Nat.card A + 1)
    -- show both = lcs k
    have h_LHS : lowerCentralSeries A (Nat.card A) = lowerCentralSeries A k := by
      have hN : Nat.card A = k + (Nat.card A - k) := by omega
      rw [hN]; exact h_prop _
    have h_RHS : lowerCentralSeries A (Nat.card A + 1) = lowerCentralSeries A k := by
      have hN : Nat.card A + 1 = k + (Nat.card A - k + 1) := by omega
      rw [hN]; exact h_prop _
    rw [h_LHS, h_RHS]
  -- prove existence: by contradiction (pigeonhole)
  by_contra h_no_stable
  push Not at h_no_stable
  -- h_no_stable : ∀ k ≤ Nat.card A, lcs k ≠ lcs (k+1)
  -- antitone + ≠ ⇒ strict at every step ≤ Nat.card A
  have h_strict : ∀ k ≤ Nat.card A,
      lowerCentralSeries A (k + 1) < lowerCentralSeries A k := fun k hk =>
    lt_of_le_of_ne (lowerCentralSeries_antitone (Nat.le_succ k))
      (fun heq => h_no_stable k hk heq.symm)
  -- card bound: Nat.card (lcs k) ≤ Nat.card A - k for k ≤ Nat.card A + 1
  have h_card_bound : ∀ k ≤ Nat.card A + 1,
      Nat.card (lowerCentralSeries A k) + k ≤ Nat.card A + 1 := by
    intro k hk
    induction k with
    | zero =>
        simp only [Nat.add_zero]
        have h_top : lowerCentralSeries A 0 = ⊤ := lowerCentralSeries_zero
        rw [h_top]
        have h_top_card : Nat.card (⊤ : Subgroup A) = Nat.card A :=
          Nat.card_congr Subgroup.topEquiv.toEquiv
        omega
    | succ n ih =>
        have hn : n ≤ Nat.card A := by omega
        have hn_le : n ≤ Nat.card A + 1 := Nat.le_succ_of_le hn
        have ih' : Nat.card (lowerCentralSeries A n) + n ≤ Nat.card A + 1 := ih hn_le
        have h_strict_n := h_strict n hn
        have h_card_lt := nat_card_lt_of_subgroup_lt h_strict_n
        omega
  -- Apply at k = Nat.card A + 1
  have h_final := h_card_bound (Nat.card A + 1) le_rfl
  have h_ge_one : 1 ≤ Nat.card (lowerCentralSeries A (Nat.card A + 1)) :=
    Nat.card_pos
  omega

/-- The "infinity term" of the lower central series for a finite group `A`:
`A^∞ := lowerCentralSeries A (Nat.card A)`. For a finite group this is the eventual
stable value of the lower central series. -/
noncomputable def lowerCentralSeriesInfty (A : Type*) [Group A] [Finite A] : Subgroup A :=
  lowerCentralSeries A (Nat.card A)

/-- `A^∞ = ⁅A^∞, ⊤⁆` (lcs の stable 性質の右作用形). -/
lemma lowerCentralSeriesInfty_commutator_top [Finite A] :
    ⁅lowerCentralSeriesInfty A, (⊤ : Subgroup A)⁆ = lowerCentralSeriesInfty A := by
  unfold lowerCentralSeriesInfty
  exact (lowerCentralSeries_card_eq_succ_card (A := A)).symm

/-- `A^∞ = ⁅⊤, A^∞⁆` (lcs の stable 性質の左作用形, `commutator_comm` 経由). -/
lemma commutator_top_lowerCentralSeriesInfty [Finite A] :
    ⁅(⊤ : Subgroup A), lowerCentralSeriesInfty A⁆ = lowerCentralSeriesInfty A := by
  rw [Subgroup.commutator_comm]
  exact lowerCentralSeriesInfty_commutator_top

end /- §4C (続) -/

/-! ### §4C Thm 4.24 Phase 2: helpers for the main theorem -/

section /- §4C (続 II): Thm 4.24 main theorem -/

variable {A : Type*} [Group A]

/-! #### iterated commutators with `A^∞` and the chain hypothesis -/

/-- **Subgroup-valued iterated right commutator with a fixed subgroup**:
`iterRightCommutator K m = ⁅...⁅K, F⁆, F⁆...⁆`. Specialisation of `iterCommutator`
where we vary the left operand but keep the right operand fixed, used in the
"sequence terminating at 1" step of Thm 4.24.

This is definitionally `iterCommutator K F m`, but the explicit name aids
readability around `Nat.find` of "last nontrivial in chain". -/
private noncomputable def iterRightCommutator
    (K F : Subgroup G) (m : ℕ) : Subgroup G :=
  iterCommutator K F m

private lemma iterRightCommutator_zero (K F : Subgroup G) :
    iterRightCommutator K F 0 = K := rfl

private lemma iterRightCommutator_succ (K F : Subgroup G) (m : ℕ) :
    iterRightCommutator K F (m + 1) = ⁅iterRightCommutator K F m, F⁆ := rfl

/-- **Monotonicity in the left operand**: if `K ≤ K'`, then `iterRightCommutator K F m ≤ iterRightCommutator K' F m`. -/
private lemma iterRightCommutator_mono_left
    {K K' F : Subgroup G} (h : K ≤ K') (m : ℕ) :
    iterRightCommutator K F m ≤ iterRightCommutator K' F m := by
  induction m with
  | zero => simpa [iterRightCommutator_zero] using h
  | succ m ih =>
      rw [iterRightCommutator_succ, iterRightCommutator_succ]
      exact Subgroup.commutator_mono ih le_rfl

/-- **iterRightCommutator with shifted base**: `iterRightCommutator (iter K F j) F k = iter K F (j + k)`. -/
private lemma iterRightCommutator_add (K F : Subgroup G) (j k : ℕ) :
    iterRightCommutator (iterRightCommutator K F j) F k = iterRightCommutator K F (j + k) := by
  induction k with
  | zero => simp [iterRightCommutator_zero]
  | succ k ih =>
      rw [iterRightCommutator_succ, ih]
      rw [show j + (k + 1) = (j + k) + 1 from by omega, iterRightCommutator_succ]

/-! #### Restriction of the action to `A^∞ ≤ A` -/

/-- The composed hom `lowerCentralSeriesInfty A →* MulAut G` obtained by restricting `φ`. -/
private noncomputable def phiInfty {A G : Type*} [Group A] [Group G] [Finite A]
    (φ : A →* MulAut G) :
    (lowerCentralSeriesInfty A) →* MulAut G :=
  φ.comp (lowerCentralSeriesInfty A).subtype

/-- **A^∞ の作用 commutator** = `⁅G, A^∞⁆` (内部記法). Subgroup-typed. -/
private noncomputable def actionCommutatorInfty {A G : Type*} [Group A] [Group G] [Finite A]
    (φ : A →* MulAut G) : Subgroup G :=
  actionCommutator (phiInfty φ)

/-- `[G, A^∞] ≤ [G, A]` (作用 commutator は acting group の制限で縮む). -/
private lemma actionCommutatorInfty_le_actionCommutator
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G) :
    actionCommutatorInfty φ ≤ actionCommutator φ :=
  actionCommutator_comp_le φ _

/-- `[G, A^∞]` is normal in G (inherited from `actionCommutator.normal`). -/
private instance actionCommutatorInfty_normal
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G) :
    (actionCommutatorInfty φ).Normal :=
  actionCommutator.normal (phiInfty φ)

/-- `[G, A^∞]` is A-invariant (it is the image of an action commutator restricted to A^∞,
which is itself characteristic in A, but more importantly, `(φ a) g * g⁻¹` for `a ∈ A^∞`
is permuted under the broader A-action). -/
private lemma actionCommutatorInfty_isAInvariant
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutatorInfty φ) := by
  -- Strategy: actionCommutatorInfty φ = ⁅⊤, lowerCentralSeriesInfty⁆ "viewed in G" via the action.
  -- Use the fact that the generating set
  -- {g * (φ a) g⁻¹ : g ∈ G, a ∈ A^∞}
  -- is invariant under φ b for b ∈ A: (φ b) (g * (φ a) g⁻¹) = (φ b) g * (φ (b * a * b⁻¹)) ((φ b) g)⁻¹,
  -- and b * a * b⁻¹ ∈ A^∞ because A^∞ is characteristic (hence normal) in A.
  apply OddOrder.Isaacs.Ch03.IsAInvariant.closure_of_invariant_set
  intro b
  -- Generator: x = g * (phiInfty φ) ⟨a, ha⟩ g⁻¹ with ⟨a, ha⟩ : A^∞. Equivalently g * (φ a) g⁻¹.
  have h_norm : (lowerCentralSeriesInfty A).Normal := by
    unfold lowerCentralSeriesInfty
    exact (lowerCentralSeries A (Nat.card A)).normal_of_characteristic
  have key : ∀ g : G, ∀ a : lowerCentralSeriesInfty A,
      (φ b) (g * (phiInfty φ) a g⁻¹) =
        (φ b) g * (phiInfty φ) ⟨b * a.val * b⁻¹, h_norm.conj_mem _ a.property _⟩
          ((φ b) g)⁻¹ := by
    intro g a
    show (φ b) (g * (φ a.val) g⁻¹) = (φ b) g * (φ (b * a.val * b⁻¹)) ((φ b) g)⁻¹
    rw [map_mul (φ b)]
    congr 1
    rw [show ((φ b) g)⁻¹ = (φ b) g⁻¹ from (map_inv (φ b) g).symm,
        show φ (b * a.val * b⁻¹) = (φ b) * (φ a.val) * (φ b)⁻¹ from by
          rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    refine ⟨(φ b) g, ⟨b * a.val * b⁻¹, h_norm.conj_mem _ a.property _⟩, ?_⟩
    exact key g a
  · rintro ⟨g, a, rfl⟩
    refine ⟨(φ b)⁻¹ g * (phiInfty φ)
        ⟨b⁻¹ * a.val * b, by
          have := h_norm.conj_mem _ a.property b⁻¹
          simpa [mul_assoc] using this⟩
        ((φ b)⁻¹ g)⁻¹,
      ⟨(φ b)⁻¹ g, _, rfl⟩, ?_⟩
    show (φ b) ((φ b)⁻¹ g * (φ (b⁻¹ * a.val * b)) ((φ b)⁻¹ g)⁻¹) =
        g * (φ a.val) g⁻¹
    rw [map_mul (φ b)]
    congr 1
    · exact MulAut.apply_inv_self (M := G) (φ b) g
    rw [show ((φ b)⁻¹ g)⁻¹ = (φ b)⁻¹ g⁻¹ from (map_inv ((φ b)⁻¹) g).symm,
        show φ (b⁻¹ * a.val * b) = (φ b)⁻¹ * (φ a.val) * (φ b) from by
          rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self,
        MulAut.apply_inv_self]

/-- **Chain hypothesis descends to `A^∞`**: if `iterCommutator inl(G).range inr(A).range m = ⊥`
then `iterCommutator inl(G).range inr(A^∞).range m = ⊥` (acting via `phiInfty`).

Proof: `lowerCentralSeriesInfty A ≤ A` (as subgroup), and the chain hypothesis restricts. -/
private lemma iterCommutator_inl_inr_lowerCentralSeriesInfty_eq_bot
    {A G : Type*} [Group A] [Group G] [Finite A] {φ : A →* MulAut G} {m : ℕ}
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    iterCommutator
        (SemidirectProduct.inl : G →* G ⋊[phiInfty φ] (lowerCentralSeriesInfty A)).range
        (SemidirectProduct.inr : (lowerCentralSeriesInfty A) →*
            G ⋊[phiInfty φ] (lowerCentralSeriesInfty A)).range m = ⊥ :=
  iterCommutator_inl_inr_restrict_eq_bot (φ := φ) (lowerCentralSeriesInfty A) h_iter

/-! #### Fixed-point subgroup `C := [G, A^∞] ∩ C_G(A)` and its properties -/

/-- **Fixed-point subgroup**: `C := actionCommutatorInfty φ ⊓ fixedPointsOfMulAut φ`.

This is the subgroup of `[G, A^∞]` consisting of elements fixed by the entire `A`-action.
Used in the inductive step of Thm 4.24 as the kernel we factor out. -/
private noncomputable def actionCommutatorInfty_fix
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G) : Subgroup G :=
  actionCommutatorInfty φ ⊓ Subgroup.fixedPointsOfMulAut φ

/-- `C` is A-invariant. (Intersection of two A-invariant subgroups.) -/
private lemma actionCommutatorInfty_fix_isAInvariant
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutatorInfty_fix φ) := by
  refine OddOrder.Isaacs.Ch03.IsAInvariant.inf (actionCommutatorInfty_isAInvariant φ) ?_
  -- fixedPointsOfMulAut φ is A-invariant: it is a characteristic-like subgroup w.r.t. A
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro b g hg
  rw [Subgroup.mem_fixedPointsOfMulAut] at hg ⊢
  intro a
  -- Goal: (φ a) ((φ b) g) = (φ b) g.
  -- Use: (φ a) ((φ b) g) = (φ (a * b)) g = (φ b) ((φ (b⁻¹ * a * b)) g) by composing,
  -- and (φ (b⁻¹ * a * b)) g = g since g is fixed by every element of A.
  have h_eq : (φ a) ((φ b) g) = (φ b) ((φ (b⁻¹ * a * b)) g) := by
    rw [show φ (b⁻¹ * a * b) = (φ b)⁻¹ * (φ a) * (φ b) from by
        rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
  rw [h_eq, hg (b⁻¹ * a * b)]

/-! #### Lemma: `K = [G, A^∞]` centralizes `[G, A]` (three-subgroups in Γ)

Given the hypothesis that `A^∞` acts trivially on `[G, A]` (= IH applied to `[G, A]`),
we derive that `[G, A^∞]` centralizes `[G, A]`, using a three-subgroups argument in Γ. -/

/-- The hypothesis "A^∞ acts trivially on `[G, A]`" translated into a Γ-side commutator
identity: `⁅inl([G, A]), inr(A^∞)⁆ = ⊥` in Γ. -/
private lemma commutator_inl_GA_inr_Ainf_eq_bot_of_centralized
    {A G : Type*} [Group A] [Group G] [Finite A] {φ : A →* MulAut G}
    (h : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ)) :
    ⁅(actionCommutator φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A),
      (lowerCentralSeriesInfty A).map (SemidirectProduct.inr : A →* G ⋊[φ] A)⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  rintro _ ⟨k, hk, rfl⟩ _ ⟨a, ha, rfl⟩
  -- Goal: ⁅inl k, inr a⁆ ∈ ⊥
  rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
  -- Need: k * (φ a) k⁻¹ = 1 (i.e., (φ a) k = k).
  have h_fix : (φ a) k = k := by
    have hk_fix := h hk
    -- hk_fix : k ∈ fixedPointsOfMulAut (phiInfty φ), i.e., ∀ b : A^∞, (phiInfty φ b) k = k.
    -- phiInfty φ ⟨a, ha⟩ k = (φ a) k by definition. Apply to b := ⟨a, ha⟩.
    have := hk_fix ⟨a, ha⟩
    exact this
  rw [show (φ a) k⁻¹ = ((φ a) k)⁻¹ from map_inv (φ a) k, h_fix, mul_inv_cancel]
  exact map_one _

/-- **K = [G, A^∞] centralizes [G, A]**: given hypothesis (d) "A^∞ acts trivially on [G, A]",
`⁅[G, A^∞], [G, A]⁆ = ⊥` in G.

**Proof**: Three-subgroups in Γ = G ⋊[φ] A with H_1 = inr(A^∞) (lowerCentralSeriesInfty A
mapped via inr), H_2 = inl(G).range, H_3 = inl([G, A]) = ⁅XG, YA⁆ (= GA_inl):
- `⁅H_2, H_3, H_1⁆ ≤ ⁅H_3, H_1⁆ = ⁅GA_inl, H_1⁆ = ⊥` (hypothesis (d) via Γ-form).
  Wait: `⁅H_3, H_1⁆ = ⁅GA_inl, inr(A^∞)⁆` and we have hypothesis as
  `⁅GA_inl, inr(A^∞)⁆ = ⊥`, hence `⁅H_2, H_3, H_1⁆ ≤ ⁅⊤, ⊥⁆ = ⊥`... no, that's wrong.
- Actually, `⁅H_2, H_3, H_1⁆ = ⁅⁅H_2, H_3⁆, H_1⁆`. We need to bound `⁅H_2, H_3⁆`.
  Since `GA_inl ⊴ Γ` (using inl ⊔ inr = ⊤), `⁅XG, GA_inl⁆ ≤ GA_inl`.
  So `⁅H_2, H_3⁆ ≤ GA_inl`, hence `⁅⁅H_2, H_3⁆, H_1⁆ ≤ ⁅GA_inl, inr(A^∞)⁆ = ⊥` (hypothesis (d)).
- `⁅H_3, H_1, H_2⁆ = ⁅⁅GA_inl, inr(A^∞)⁆, XG⁆ = ⁅⊥, XG⁆ = ⊥` (hypothesis (d)).
- Three-subgroups (rotate): `⁅⁅H_1, H_2⁆, H_3⁆ = ⊥`.
- `⁅H_1, H_2⁆ = ⁅inr(A^∞), inl(G)⁆ = (commutator_comm) = ⁅inl(G), inr(A^∞)⁆
  = inl([G, A^∞]) = inl(K)`.
- So `⁅inl(K), GA_inl⁆ = ⁅inl(K), inl([G, A])⁆ = inl(⁅K, [G, A]⁆) = ⊥`.
- By inl_injective, `⁅K, [G, A]⁆ = ⊥` in G. -/
private theorem commutator_actionCommutatorInfty_actionCommutator_eq_bot
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G)
    (h : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ)) :
    ⁅actionCommutatorInfty φ, actionCommutator φ⁆ = ⊥ := by
  -- Set up
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  set YinfA : Subgroup (G ⋊[φ] A) :=
    (lowerCentralSeriesInfty A).map (SemidirectProduct.inr : A →* G ⋊[φ] A)
  set GA_inl : Subgroup (G ⋊[φ] A) :=
    (actionCommutator φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A) with hGA_inl
  -- GA_inl = ⁅XG, inr(A).range⁆ (from actionCommutator_map_inl)
  have hGA_inl_eq : GA_inl = ⁅XG, (SemidirectProduct.inr : A →* G ⋊[φ] A).range⁆ :=
    actionCommutator_map_inl φ
  -- Hypothesis (d): ⁅GA_inl, YinfA⁆ = ⊥
  have hd_gamma : ⁅GA_inl, YinfA⁆ = ⊥ :=
    commutator_inl_GA_inr_Ainf_eq_bot_of_centralized h
  -- GA_inl is normal in Γ (it = ⁅XG, YA⁆ with XG ⊔ inr(A) = ⊤).
  haveI hGA_norm : GA_inl.Normal := by
    rw [hGA_inl_eq]
    exact commutator_normal_of_sup_eq_top
      SemidirectProduct.inl_range_sup_inr_range_eq_top
  -- ⁅XG, GA_inl⁆ ≤ GA_inl (left commutator inclusion since GA_inl normal)
  have h_inner : ⁅XG, GA_inl⁆ ≤ GA_inl := Subgroup.commutator_le_right XG GA_inl
  -- ⁅⁅XG, GA_inl⁆, YinfA⁆ ≤ ⁅GA_inl, YinfA⁆ = ⊥
  have h_three_b : ⁅⁅XG, GA_inl⁆, YinfA⁆ = ⊥ :=
    le_bot_iff.mp <| le_trans (Subgroup.commutator_mono h_inner le_rfl) hd_gamma.le
  -- ⁅⁅GA_inl, YinfA⁆, XG⁆ = ⊥ from hd_gamma
  have h_three_a : ⁅⁅GA_inl, YinfA⁆, XG⁆ = ⊥ := by
    rw [hd_gamma, Subgroup.commutator_bot_left]
  -- Apply Subgroup.commutator_commutator_eq_bot_of_rotate
  -- with H_1 := YinfA, H_2 := XG, H_3 := GA_inl:
  -- - input1: ⁅⁅H_2, H_3⁆, H_1⁆ = ⁅⁅XG, GA_inl⁆, YinfA⁆ = h_three_b
  -- - input2: ⁅⁅H_3, H_1⁆, H_2⁆ = ⁅⁅GA_inl, YinfA⁆, XG⁆ = h_three_a
  -- - output: ⁅⁅H_1, H_2⁆, H_3⁆ = ⁅⁅YinfA, XG⁆, GA_inl⁆ = ⊥
  have h_three : ⁅⁅YinfA, XG⁆, GA_inl⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h_three_b h_three_a
  -- ⁅YinfA, XG⁆ = (actionCommutatorInfty φ).map inl
  have h_YinfA_XG_eq : ⁅YinfA, XG⁆ =
      (actionCommutatorInfty φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A) := by
    -- ⁅YinfA, XG⁆ = ⁅XG, YinfA⁆ (commutator_comm).
    -- ⁅XG, YinfA⁆ = ⁅XG, inr(A^∞ via subtype).range⁆ via image of range.
    -- And this equals (actionCommutator (φ.comp subtype)).map inl
    -- = actionCommutatorInfty.map inl (by definition).
    have h_eq_range : YinfA =
        ((SemidirectProduct.inr : A →* G ⋊[φ] A).comp
          (lowerCentralSeriesInfty A).subtype).range := by
      rw [MonoidHom.range_comp]
      change (lowerCentralSeriesInfty A).map (SemidirectProduct.inr : A →* G ⋊[φ] A) =
        ((lowerCentralSeriesInfty A).subtype.range).map _
      rw [Subgroup.range_subtype]
    rw [Subgroup.commutator_comm, h_eq_range]
    have := actionCommutator_map_inl_comp φ (lowerCentralSeriesInfty A).subtype
    -- this : (actionCommutator (φ.comp ((lowerCentralSeriesInfty A).subtype))).map inl =
    --        ⁅XG, ((SemidirectProduct.inr).comp (lowerCentralSeriesInfty A).subtype).range⁆
    -- We want LHS = (actionCommutatorInfty φ).map inl, which is the same since
    -- actionCommutatorInfty φ := actionCommutator (phiInfty φ) := actionCommutator (φ.comp subtype).
    exact this.symm
  rw [h_YinfA_XG_eq, hGA_inl, ← Subgroup.map_commutator] at h_three
  exact (Subgroup.map_eq_bot_iff_of_injective _ SemidirectProduct.inl_injective).mp h_three

/-- **`[K, [G, A]] = ⊥` ⇒ `[[G, A], C] = ⊥`** (since C ≤ K). Just commutator monotonicity. -/
private lemma commutator_actionCommutator_actionCommutatorInfty_fix_eq_bot
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G)
    (h : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ)) :
    ⁅actionCommutator φ, actionCommutatorInfty_fix φ⁆ = ⊥ := by
  have h_main := commutator_actionCommutatorInfty_actionCommutator_eq_bot φ h
  have h_C_le : actionCommutatorInfty_fix φ ≤ actionCommutatorInfty φ := inf_le_left
  -- Goal: ⁅actionCommutator φ, actionCommutatorInfty_fix φ⁆ = ⊥
  rw [Subgroup.commutator_comm]
  exact le_bot_iff.mp <|
    le_trans (Subgroup.commutator_mono h_C_le le_rfl) h_main.le

/-! #### C ⊴ G (Step 6 of Isaacs Thm 4.24)

We now show `actionCommutatorInfty_fix φ` is normal in G via:
(I) `[C, G] ≤ [G, A^∞]` (since C ≤ K and K is normal in G).
(II) `[C, G] ≤ fixedPointsOfMulAut φ` (three-subgroups in Γ with H_1 = inl(G), H_2 = inr(A),
H_3 = inl(C)). -/

/-- **A centralizes [C, G] (in Γ-form): `⁅⁅XG, inl(C)⁆, inr(A)⁆ = ⊥`**.

**Proof**: Three-subgroups in Γ with H_1 = XG, H_2 = inr(A), H_3 = inl(C):
- `⁅H_1, H_2, H_3⁆ = ⁅⁅XG, inr(A)⁆, inl(C)⁆ = ⁅GA_inl, inl(C)⁆ = inl(⁅[G, A], C⁆) = ⊥`
  (from `commutator_actionCommutator_actionCommutatorInfty_fix_eq_bot`).
- `⁅H_2, H_3, H_1⁆ = ⁅⁅inr(A), inl(C)⁆, XG⁆ = ⁅⊥, XG⁆ = ⊥` (A centralizes C ⇒ ⁅inr(A), inl(C)⁆ = ⊥).
- Three-subgroups rotate: `⁅⁅H_3, H_1⁆, H_2⁆ = ⁅⁅inl(C), XG⁆, inr(A)⁆ = ⊥`. -/
private theorem commutator_inl_C_XG_inr_A_eq_bot_of_centralized
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G)
    (h : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ)) :
    ⁅⁅(actionCommutatorInfty_fix φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A),
        (SemidirectProduct.inl : G →* G ⋊[φ] A).range⁆,
      (SemidirectProduct.inr : A →* G ⋊[φ] A).range⁆ = ⊥ := by
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  set Cinl : Subgroup (G ⋊[φ] A) :=
    (actionCommutatorInfty_fix φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A)
  -- Part A: ⁅YA, Cinl⁆ = ⊥ (A centralizes C in G)
  have h_AC_bot : ⁅YA, Cinl⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    rintro _ ⟨a, rfl⟩ _ ⟨c, hc, rfl⟩
    obtain ⟨_, hc_fix⟩ := Subgroup.mem_inf.mp hc
    have h_fix : (φ a) c = c := hc_fix a
    -- Goal: ⁅inr a, inl c⁆ ∈ ⊥
    rw [Subgroup.mem_bot]
    -- Compute ⁅inr a, inl c⁆ = (inr a) * (inl c) * (inr a)⁻¹ * (inl c)⁻¹
    -- = inl ((φ a) c) * inr a * (inr a)⁻¹ * (inl c)⁻¹  (by inl_aut)
    -- = inl c * (inl c)⁻¹ = 1
    have hi := SemidirectProduct.inl_aut (φ := φ) a c
    -- hi : inl ((φ a) c) = inr a * inl c * inr a⁻¹
    show (SemidirectProduct.inr a : G ⋊[φ] A) * SemidirectProduct.inl c *
        (SemidirectProduct.inr a)⁻¹ * (SemidirectProduct.inl c)⁻¹ = 1
    rw [show ((SemidirectProduct.inr a : G ⋊[φ] A))⁻¹ = SemidirectProduct.inr a⁻¹ from
        (map_inv _ _).symm, ← hi, h_fix]
    group
  -- Part B: ⁅⁅XG, YA⁆, Cinl⁆ = ⊥
  -- Use commutator_actionCommutator_actionCommutatorInfty_fix_eq_bot and bridge.
  have h_actY_eq : ⁅XG, YA⁆ = (actionCommutator φ).map SemidirectProduct.inl :=
    (actionCommutator_map_inl φ).symm
  have h_C_actCom : ⁅(actionCommutator φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A),
      Cinl⁆ = ⊥ := by
    -- = (⁅actionCommutator φ, actionCommutatorInfty_fix φ⁆).map inl = ⊥.map inl
    rw [← Subgroup.map_commutator,
        commutator_actionCommutator_actionCommutatorInfty_fix_eq_bot φ h]
    simp
  have h_XY_C_bot : ⁅⁅XG, YA⁆, Cinl⁆ = ⊥ := by
    rw [h_actY_eq]; exact h_C_actCom
  -- Apply three-subgroups (rotate) with H_1 = XG, H_2 = YA, H_3 = Cinl:
  -- - input1: ⁅⁅H_2, H_3⁆, H_1⁆ = ⁅⁅YA, Cinl⁆, XG⁆ = ⁅⊥, XG⁆ = ⊥
  -- - input2: ⁅⁅H_3, H_1⁆, H_2⁆ = ⁅⁅Cinl, XG⁆, YA⁆ — wait, this is what we want.
  -- We need to swap. Three-subgroups: given ⁅⁅H_2, H_3⁆, H_1⁆ + ⁅⁅H_3, H_1⁆, H_2⁆ ⇒
  -- ⁅⁅H_1, H_2⁆, H_3⁆.
  -- We have ⁅⁅XG, YA⁆, Cinl⁆ = ⊥ which is ⁅⁅H_1, H_2⁆, H_3⁆. (output of rotate)
  -- And ⁅⁅YA, Cinl⁆, XG⁆ = ⊥ which is ⁅⁅H_2, H_3⁆, H_1⁆. (input1)
  -- We want ⁅⁅Cinl, XG⁆, YA⁆ = ⁅⁅H_3, H_1⁆, H_2⁆. (input2)
  -- Three-subgroups can derive any one from the other two.
  have h_input1 : ⁅⁅YA, Cinl⁆, XG⁆ = ⊥ := by
    rw [h_AC_bot, Subgroup.commutator_bot_left]
  -- The rotate lemma gives ⁅⁅H_1, H_2⁆, H_3⁆ from ⁅⁅H_2, H_3⁆, H_1⁆ + ⁅⁅H_3, H_1⁆, H_2⁆.
  -- Apply with H_1' = YA, H_2' = Cinl, H_3' = XG:
  -- gives ⁅⁅YA, Cinl⁆, XG⁆ from ⁅⁅Cinl, XG⁆, YA⁆ + ⁅⁅XG, YA⁆, Cinl⁆.
  -- We want the inverse direction. Let's use:
  -- H_1' = Cinl, H_2' = XG, H_3' = YA:
  -- ⁅⁅H_2', H_3'⁆, H_1'⁆ = ⁅⁅XG, YA⁆, Cinl⁆ = ⊥ (h_XY_C_bot)
  -- ⁅⁅H_3', H_1'⁆, H_2'⁆ = ⁅⁅YA, Cinl⁆, XG⁆ = ⊥ (h_input1)
  -- ⇒ ⁅⁅H_1', H_2'⁆, H_3'⁆ = ⁅⁅Cinl, XG⁆, YA⁆ = ⊥.
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h_XY_C_bot h_input1

/-- **[C, G] ⊆ fixedPointsOfMulAut φ**: from the three-subgroups conclusion above. -/
private lemma commutator_actionCommutatorInfty_fix_top_le_fixedPoints
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G)
    (h : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ)) :
    ⁅actionCommutatorInfty_fix φ, (⊤ : Subgroup G)⁆ ≤ Subgroup.fixedPointsOfMulAut φ := by
  have h_three := commutator_inl_C_XG_inr_A_eq_bot_of_centralized φ h
  -- We want: ∀ x ∈ ⁅C, ⊤⁆, ∀ a, (φ a) x = x.
  intro x hx
  rw [Subgroup.mem_fixedPointsOfMulAut]
  intro a'
  -- Use h_three: ⁅⁅inl(C), XG⁆, inr(A).range⁆ = ⊥, so for x ∈ ⁅C, ⊤⁆ (mapped under inl)
  -- and any a', ⁅inl x, inr a'⁆ = 1 in Γ.
  -- inl(⁅C, ⊤⁆) = ⁅inl(C), inl(⊤)⁆ = ⁅inl(C), XG⁆.
  have h_x_inl_mem : (SemidirectProduct.inl x : G ⋊[φ] A) ∈
      ⁅(actionCommutatorInfty_fix φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A),
        (SemidirectProduct.inl : G →* G ⋊[φ] A).range⁆ := by
    have h_map : ⁅(actionCommutatorInfty_fix φ).map
          (SemidirectProduct.inl : G →* G ⋊[φ] A),
        (SemidirectProduct.inl : G →* G ⋊[φ] A).range⁆ =
        ⁅actionCommutatorInfty_fix φ, (⊤ : Subgroup G)⁆.map SemidirectProduct.inl := by
      rw [MonoidHom.range_eq_map (SemidirectProduct.inl : G →* G ⋊[φ] A),
          ← Subgroup.map_commutator]
    rw [h_map]
    exact ⟨x, hx, rfl⟩
  -- Now ⁅inl x, inr a'⁆ ∈ ⁅⁅inl(C), XG⁆, inr(A).range⁆ = ⊥
  have h_x_a_bot : ⁅(SemidirectProduct.inl x : G ⋊[φ] A),
      (SemidirectProduct.inr a' : G ⋊[φ] A)⁆ = (1 : G ⋊[φ] A) := by
    have h_mem : ⁅(SemidirectProduct.inl x : G ⋊[φ] A),
        (SemidirectProduct.inr a' : G ⋊[φ] A)⁆ ∈
        (⊥ : Subgroup (G ⋊[φ] A)) := by
      rw [← h_three]
      exact Subgroup.commutator_mem_commutator h_x_inl_mem ⟨a', rfl⟩
    exact Subgroup.mem_bot.mp h_mem
  -- ⁅inl x, inr a'⁆ = inl(x * (φ a') x⁻¹). So inl(x * (φ a') x⁻¹) = 1, hence x * (φ a') x⁻¹ = 1.
  rw [SemidirectProduct.commutator_inl_inr] at h_x_a_bot
  have h_in_G : x * (φ a') x⁻¹ = 1 :=
    SemidirectProduct.inl_injective (by rw [h_x_a_bot]; exact (map_one _).symm)
  -- x * (φ a') x⁻¹ = 1 ⇒ (φ a') x⁻¹ = x⁻¹ ⇒ ((φ a') x)⁻¹ = x⁻¹ ⇒ (φ a') x = x.
  have h_aux : (φ a') x⁻¹ = x⁻¹ := by
    have := h_in_G
    have := mul_left_cancel (a := x) (b := (φ a') x⁻¹) (c := x⁻¹)
      (by rw [this, mul_inv_cancel])
    exact this
  rw [map_inv] at h_aux
  exact (inv_injective h_aux)

/-! #### Normality and nontriviality of C in G -/

/-- **`C ⊴ G`** (Step 6 conclusion of Isaacs Thm 4.24):
combining `⁅C, ⊤⁆ ≤ [G, A^∞]` (since `C ≤ [G, A^∞]` and `[G, A^∞]` is G-normal) with
`⁅C, ⊤⁆ ≤ fixedPointsOfMulAut φ` (from
`commutator_actionCommutatorInfty_fix_top_le_fixedPoints`) yields `⁅C, ⊤⁆ ≤ C`, hence
`C` is normal in `G` by `Subgroup.commutator_top_right_le_iff`. -/
private lemma actionCommutatorInfty_fix_normal_of_centralized
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G)
    (h : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ)) :
    (actionCommutatorInfty_fix φ).Normal := by
  rw [← Subgroup.commutator_top_right_le_iff]
  refine le_inf ?_ (commutator_actionCommutatorInfty_fix_top_le_fixedPoints φ h)
  haveI : (actionCommutatorInfty φ).Normal := actionCommutatorInfty_normal φ
  calc ⁅actionCommutatorInfty_fix φ, (⊤ : Subgroup G)⁆
      ≤ ⁅actionCommutatorInfty φ, (⊤ : Subgroup G)⁆ :=
        Subgroup.commutator_mono inf_le_left le_rfl
    _ ≤ actionCommutatorInfty φ :=
        Subgroup.commutator_le_left _ _

/-! #### Phase 2D-2: nontriviality of C -/

/-- **`iterCommutator` monotonicity in the left operand**: if `K₁ ≤ K₂`, then
`iter K₁ F m ≤ iter K₂ F m`. -/
private lemma iterCommutator_mono_left {G : Type*} [Group G]
    {K₁ K₂ F : Subgroup G} (h : K₁ ≤ K₂) (m : ℕ) :
    iterCommutator K₁ F m ≤ iterCommutator K₂ F m := by
  induction m with
  | zero => simpa [iterCommutator_zero] using h
  | succ m ih =>
      rw [iterCommutator_succ, iterCommutator_succ]
      exact Subgroup.commutator_mono ih le_rfl

/-- **`C ≠ ⊥` when `[G, A^∞] ≠ ⊥`**: if `actionCommutatorInfty φ ≠ ⊥`, then there is a
nontrivial `A`-fixed subgroup of `G` contained in `[G, A^∞]`.

**Strategy** (in Γ = G ⋊[φ] A): set `K_inl := (actionCommutatorInfty φ).map inl ≠ ⊥`
(injectivity of `inl`). Consider the chain `f k := iterCommutator K_inl inr(A).range k`.
- `f 0 = K_inl ≠ ⊥`.
- `f m = ⊥` because `K_inl ≤ inl(G).range = iter inl(G).range inr(A).range 0`, hence
  `f k ≤ iter inl(G).range inr(A).range k`, and the chain hypothesis gives `f m = ⊥`.
- Let `k₀ := Nat.find` of the smallest `k` with `f k = ⊥`. Then `k₀ ≥ 1` and `f (k₀ - 1) ≠ ⊥`
  but `⁅f (k₀ - 1), inr(A).range⁆ = f k₀ = ⊥`.
- `f (k₀ - 1) ≤ inl(G).range` (induction: `K_inl ≤ inl(G).range`, and `inl(G).range` is normal
  in Γ since `actionCommutator_map_inl φ` shows `⁅inl(G).range, inr(A).range⁆ ≤ inl(G).range`
  — actually `inl(G).range` is normal in Γ by `commutator_normal_of_sup_eq_top` applied to
  `⁅inl(G).range, inl(G).range⁆` is trivially in `inl(G).range`; here we use that
  `inl(G).range ⊴ Γ` via `SemidirectProduct.inl_range_normal`).
- Pull `f (k₀ - 1)` back to `L ≤ G` via `inl` (= preimage), so `inl(L) = f (k₀ - 1)`.
- `⁅L, ⊤⁆ = ⊥` and every `l ∈ L` is `A`-fixed (from `f k₀ = ⊥` element-wise).
- `L ≤ actionCommutatorInfty φ` (induction: `f j ≤ K_inl`, but actually we need
  `f j ≤ K_inl` — `f` is decreasing because `K_inl ≤ ?`. Let me use `f (k₀ - 1) ≤ K_inl`
  directly via `iterCommutator_succ_le_self`-style.) -/
private lemma actionCommutatorInfty_fix_ne_bot_of_ne_bot
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G] {φ : A →* MulAut G}
    {m : ℕ}
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥)
    (hK : actionCommutatorInfty φ ≠ ⊥) :
    actionCommutatorInfty_fix φ ≠ ⊥ := by
  classical
  -- Setup in Γ
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range with hXG_def
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range with hYA_def
  set K_inl : Subgroup (G ⋊[φ] A) :=
    (actionCommutatorInfty φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A) with hK_inl_def
  -- f k := iter K_inl YA k
  set f : ℕ → Subgroup (G ⋊[φ] A) := fun k => iterCommutator K_inl YA k with hf_def
  -- K_inl ≠ ⊥
  have hK_inl_ne : K_inl ≠ ⊥ := by
    intro h
    apply hK
    exact (Subgroup.map_eq_bot_iff_of_injective (actionCommutatorInfty φ)
      SemidirectProduct.inl_injective).mp h
  -- K_inl ≤ XG
  have hK_inl_le_XG : K_inl ≤ XG := by
    rintro _ ⟨g, _, rfl⟩
    exact ⟨g, rfl⟩
  -- f k ≤ iter XG YA k for all k
  have hf_le_iter : ∀ k, f k ≤ iterCommutator XG YA k := fun k =>
    iterCommutator_mono_left hK_inl_le_XG k
  -- f m = ⊥
  have hfm_bot : f m = ⊥ := by
    have h := hf_le_iter m
    rw [h_iter] at h
    exact le_bot_iff.mp h
  -- ∃ k, f k = ⊥
  have h_exists : ∃ k, f k = ⊥ := ⟨m, hfm_bot⟩
  -- k₀ := Nat.find
  let k₀ := Nat.find h_exists
  have hk₀_spec : f k₀ = ⊥ := Nat.find_spec h_exists
  have hk₀_min : ∀ j < k₀, f j ≠ ⊥ := fun j hj => Nat.find_min h_exists hj
  -- f 0 = K_inl ≠ ⊥, so k₀ ≥ 1
  have hf0 : f 0 = K_inl := by simp [hf_def, iterCommutator_zero]
  have hk₀_pos : 1 ≤ k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with hzero | hpos
    · exfalso
      have := hk₀_spec
      rw [hzero, hf0] at this
      exact hK_inl_ne this
    · exact hpos
  -- Let k := k₀ - 1
  set k := k₀ - 1 with hk_def
  have hk_succ : k + 1 = k₀ := by omega
  -- f k ≠ ⊥
  have hfk_ne : f k ≠ ⊥ := hk₀_min k (by omega)
  -- f (k+1) = ⊥
  have hfk1_bot : f (k + 1) = ⊥ := by rw [hk_succ]; exact hk₀_spec
  -- ⁅f k, YA⁆ = f (k+1) = ⊥
  have h_comm_fk_YA : ⁅f k, YA⁆ = ⊥ := by
    have : f (k + 1) = ⁅f k, YA⁆ := iterCommutator_succ _ _ _
    rw [← this]
    exact hfk1_bot
  -- f k ≤ XG (induction). XG is normal in Γ, so iter preserves XG-containment.
  haveI hXG_normal : XG.Normal := by
    simp only [hXG_def]
    infer_instance
  have hXG_comm_YA_le : ⁅XG, YA⁆ ≤ XG := Subgroup.commutator_le_left XG YA
  have hfk_le_XG : ∀ j, f j ≤ XG := by
    intro j
    induction j with
    | zero =>
        simp only [hf_def, iterCommutator_zero]
        exact hK_inl_le_XG
    | succ j ih =>
        have ih' : iterCommutator K_inl YA j ≤ XG := by
          simpa [hf_def] using ih
        change iterCommutator K_inl YA (j + 1) ≤ XG
        rw [iterCommutator_succ]
        exact (Subgroup.commutator_mono ih' le_rfl).trans hXG_comm_YA_le
  have hfk_le_XG_now : f k ≤ XG := hfk_le_XG k
  -- f k ≤ K_inl (induction using iter_succ_le for normal K_inl-style)
  -- Actually K_inl may not be normal in Γ. We use a different strategy: extract L ≤ G
  -- with inl L = f k via the fact that f k ≤ XG = inl.range.
  -- Define L : Subgroup G as the preimage of f k under inl.
  let L : Subgroup G := (f k).comap (SemidirectProduct.inl : G →* G ⋊[φ] A)
  have hL_map : L.map (SemidirectProduct.inl : G →* G ⋊[φ] A) = f k := by
    -- map ∘ comap = inf with range; range = XG; f k ≤ XG
    rw [Subgroup.map_comap_eq, hXG_def.symm]
    show XG ⊓ f k = f k
    exact inf_eq_right.mpr hfk_le_XG_now
  have hL_ne_bot : L ≠ ⊥ := by
    intro hL
    apply hfk_ne
    rw [← hL_map, hL, Subgroup.map_bot]
  -- L ≤ actionCommutatorInfty φ: use that f j ≤ K_inl for all j (since K_inl is "stable
  -- enough" — iter K_inl YA j ≤ K_inl needs K_inl to be Normal in Γ. K_inl might not be normal,
  -- but iter K_inl YA j ≤ K_inl.subgroupClosure... Use the fact that
  -- iter K_inl YA j ⊆ (closure (K_inl ∪ YA)) — no, that's not what we want.
  --
  -- Alternative: K_inl is normal in XG (since XG ≅ G via inl, and actionCommutatorInfty φ
  -- is normal in G). So XG-conjugation preserves K_inl. But YA conjugation might not.
  -- However, the iter chain is built by commutators with YA. We claim:
  -- iter K_inl YA j ⊆ K_inl (within XG). Proof: induction. iter K_inl YA (j+1) =
  -- ⁅iter K_inl YA j, YA⁆. iter K_inl YA j ⊆ K_inl ⊆ XG (by IH and inl-image normality).
  -- ⁅K_inl, YA⁆ = ?. Compute generators: ⁅inl k, inr a⁆ = inl(k * (φ a) k⁻¹). k ∈ acInfty
  -- which is A-invariant via phiInfty, so (φ a) k... wait we need this for general a ∈ A,
  -- not just a ∈ A^∞. But acInfty is A-invariant (Phase 2A `actionCommutatorInfty_isAInvariant`)!
  -- So (φ a) k ∈ acInfty, so k * (φ a) k⁻¹ ∈ acInfty (closed under product/inv).
  -- Therefore ⁅K_inl, YA⁆ ⊆ K_inl.
  have hKinl_YA_le_Kinl : ⁅K_inl, YA⁆ ≤ K_inl := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨g, hg, rfl⟩ _ ⟨a, rfl⟩
    -- Goal: ⁅inl g, inr a⁆ ∈ K_inl. ⁅inl g, inr a⁆ = inl (g * (φ a) g⁻¹).
    rw [SemidirectProduct.commutator_inl_inr]
    -- Need: g * (φ a) g⁻¹ ∈ actionCommutatorInfty φ.
    have h_inv := OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem.mp
      (actionCommutatorInfty_isAInvariant φ)
    -- (φ a) g ∈ actionCommutatorInfty φ
    have h_phi_g : (φ a) g ∈ actionCommutatorInfty φ := h_inv a g hg
    -- g * (φ a) g⁻¹ ∈ actionCommutatorInfty φ
    have h_phi_g_inv : (φ a) g⁻¹ = ((φ a) g)⁻¹ := map_inv (φ a) g
    rw [h_phi_g_inv]
    exact ⟨g * ((φ a) g)⁻¹,
      (actionCommutatorInfty φ).mul_mem hg ((actionCommutatorInfty φ).inv_mem h_phi_g),
      rfl⟩
  have hfk_le_Kinl : ∀ j, f j ≤ K_inl := by
    intro j
    induction j with
    | zero => simp [hf_def, iterCommutator_zero]
    | succ j ih =>
        have ih' : iterCommutator K_inl YA j ≤ K_inl := by
          simpa [hf_def] using ih
        change iterCommutator K_inl YA (j + 1) ≤ K_inl
        rw [iterCommutator_succ]
        exact (Subgroup.commutator_mono ih' le_rfl).trans hKinl_YA_le_Kinl
  -- L ≤ actionCommutatorInfty φ: take l ∈ L, then inl l ∈ f k ≤ K_inl = inl(acInfty),
  -- so by inl_injective, l ∈ acInfty.
  have hL_le_acInfty : L ≤ actionCommutatorInfty φ := by
    intro l hl
    have hinl : (SemidirectProduct.inl l : G ⋊[φ] A) ∈ f k := hl
    have hinl_Kinl : (SemidirectProduct.inl l : G ⋊[φ] A) ∈ K_inl := hfk_le_Kinl k hinl
    obtain ⟨l', hl', heq⟩ := hinl_Kinl
    have : l = l' := SemidirectProduct.inl_injective heq.symm
    rw [this]
    exact hl'
  -- L ≤ fixedPointsOfMulAut φ: from ⁅f k, YA⁆ = ⊥, take l ∈ L, then for any a,
  -- ⁅inl l, inr a⁆ = 1. Since ⁅inl l, inr a⁆ = inl(l * (φ a) l⁻¹), inl_injective
  -- gives l * (φ a) l⁻¹ = 1, hence (φ a) l = l.
  have hL_le_fix : L ≤ Subgroup.fixedPointsOfMulAut φ := by
    intro l hl
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    -- inl l ∈ f k
    have hinl : (SemidirectProduct.inl l : G ⋊[φ] A) ∈ f k := hl
    -- ⁅inl l, inr a⁆ ∈ ⁅f k, YA⁆ = ⊥
    have h_comm_mem : ⁅(SemidirectProduct.inl l : G ⋊[φ] A),
        (SemidirectProduct.inr a : G ⋊[φ] A)⁆ ∈ (⁅f k, YA⁆ : Subgroup (G ⋊[φ] A)) :=
      Subgroup.commutator_mem_commutator hinl ⟨a, rfl⟩
    rw [h_comm_fk_YA, Subgroup.mem_bot] at h_comm_mem
    -- ⁅inl l, inr a⁆ = inl (l * (φ a) l⁻¹) = 1
    rw [SemidirectProduct.commutator_inl_inr] at h_comm_mem
    -- l * (φ a) l⁻¹ = 1 in G
    have h_one_G : l * (φ a) l⁻¹ = 1 := by
      have := h_comm_mem
      have h_inl_one : (SemidirectProduct.inl (1 : G) : G ⋊[φ] A) = 1 := map_one _
      have := this.trans h_inl_one.symm
      exact SemidirectProduct.inl_injective this
    -- (φ a) l⁻¹ = l⁻¹, so (φ a) l = l
    have h_aux : (φ a) l⁻¹ = l⁻¹ :=
      mul_left_cancel (a := l) (b := (φ a) l⁻¹) (c := l⁻¹)
        (by rw [h_one_G, mul_inv_cancel])
    rw [map_inv] at h_aux
    exact inv_injective h_aux
  -- L ≤ actionCommutatorInfty_fix φ = actionCommutatorInfty φ ⊓ fixedPointsOfMulAut φ
  have hL_le_C : L ≤ actionCommutatorInfty_fix φ := le_inf hL_le_acInfty hL_le_fix
  -- L ≠ ⊥, hence C ≠ ⊥
  intro hC_bot
  apply hL_ne_bot
  exact le_bot_iff.mp (hL_le_C.trans hC_bot.le)

/-! #### Phase 3: quotient induction and the main nilpotence theorem -/

/-- **Quotient descent for the chain hypothesis**:
if `[G,A,...,A]_m = 1`, then the same iterated commutator is trivial for the
induced action on `G/N`, provided `N` is normal and `A`-invariant. -/
private theorem iterCommutator_inl_inr_quotient_eq_bot
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) {m : ℕ}
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    let φbar : A →* MulAut (G ⧸ N) :=
      OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN
    iterCommutator (SemidirectProduct.inl : G ⧸ N →* (G ⧸ N) ⋊[φbar] A).range
        (SemidirectProduct.inr : A →* (G ⧸ N) ⋊[φbar] A).range m = ⊥ := by
  dsimp
  let φbar : A →* MulAut (G ⧸ N) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN
  let F : G ⋊[φ] A →* (G ⧸ N) ⋊[φbar] A :=
    SemidirectProduct.map (QuotientGroup.mk' N) (MonoidHom.id A) (fun a => by
      ext g
      rfl)
  let XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  let YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  let Xbar : Subgroup ((G ⧸ N) ⋊[φbar] A) :=
    (SemidirectProduct.inl : G ⧸ N →* (G ⧸ N) ⋊[φbar] A).range
  let YAbar : Subgroup ((G ⧸ N) ⋊[φbar] A) :=
    (SemidirectProduct.inr : A →* (G ⧸ N) ⋊[φbar] A).range
  have h_map_X : XG.map F = Xbar := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk' N g, by simp [F]⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      refine ⟨(SemidirectProduct.inl : G →* G ⋊[φ] A) g, ⟨g, rfl⟩, ?_⟩
      simp [F]
  have h_map_Y : YA.map F = YAbar := by
    ext x
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, by simp [F]⟩
    · rintro ⟨a, rfl⟩
      refine ⟨(SemidirectProduct.inr : A →* G ⋊[φ] A) a, ⟨a, rfl⟩, ?_⟩
      simp [F]
  have h_map_iter :
      ∀ n : ℕ, (iterCommutator XG YA n).map F = iterCommutator Xbar YAbar n := by
    intro n
    induction n with
    | zero =>
        simpa [iterCommutator_zero] using h_map_X
    | succ n ih =>
        rw [iterCommutator_succ, iterCommutator_succ, Subgroup.map_commutator, ih, h_map_Y]
  have h_map_bot : (iterCommutator XG YA m).map F = ⊥ := by
    rw [h_iter, Subgroup.map_bot]
  rwa [h_map_iter m] at h_map_bot

/-- If `N` is `A`-invariant, then it is also invariant for the restricted `A^∞`-action. -/
private lemma isAInvariant_phiInfty_of_isAInvariant
    {A G : Type*} [Group A] [Group G] [Finite A] {φ : A →* MulAut G}
    {N : Subgroup G} (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) :
    OddOrder.Isaacs.Ch03.IsAInvariant (phiInfty φ) N := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a g hg
  exact hN.smul_mem a.val hg

/-- **`[G/N, A^∞]` is the image of `[G, A^∞]`** for an `A`-invariant normal subgroup `N`. -/
private lemma actionCommutatorInfty_quotient_eq_map
    {A G : Type*} [Group A] [Group G] [Finite A] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) :
    actionCommutatorInfty
        (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) =
      (actionCommutatorInfty φ).map (QuotientGroup.mk' N) := by
  change actionCommutator
        (phiInfty (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN)) =
      (actionCommutator (phiInfty φ)).map (QuotientGroup.mk' N)
  rw [actionCommutator, actionCommutator, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨q, a, rfl⟩
    refine QuotientGroup.induction_on q ?_
    intro g
    refine ⟨g * (phiInfty φ a) g⁻¹, ⟨g, a, rfl⟩, ?_⟩
    simp [map_mul, phiInfty]
  · rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk' N g, a, by simp [map_mul, phiInfty]⟩

/-- Γ-side form of "`A` centralizes `[G,A^∞]`". -/
private lemma commutator_inl_GAinf_inr_A_eq_bot_of_fixed
    {A G : Type*} [Group A] [Group G] [Finite A] {φ : A →* MulAut G}
    (h : actionCommutatorInfty φ ≤ Subgroup.fixedPointsOfMulAut φ) :
    ⁅(actionCommutatorInfty φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A),
      (SemidirectProduct.inr : A →* G ⋊[φ] A).range⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  rintro _ ⟨k, hk, rfl⟩ _ ⟨a, rfl⟩
  rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
  have h_fix : (φ a) k = k := h hk a
  rw [show (φ a) k⁻¹ = ((φ a) k)⁻¹ from map_inv (φ a) k, h_fix, mul_inv_cancel]
  exact map_one _

/-- Γ-side bridge: `⁅inl(G), inr(A^∞)⁆ = inl([G,A^∞])`. -/
private lemma commutator_inl_range_inr_lowerCentralSeriesInfty_eq_actionCommutatorInfty_map
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G) :
    ⁅(SemidirectProduct.inl : G →* G ⋊[φ] A).range,
      (lowerCentralSeriesInfty A).map (SemidirectProduct.inr : A →* G ⋊[φ] A)⁆ =
        (actionCommutatorInfty φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A) := by
  have h_eq_range :
      (lowerCentralSeriesInfty A).map (SemidirectProduct.inr : A →* G ⋊[φ] A) =
        ((SemidirectProduct.inr : A →* G ⋊[φ] A).comp
          (lowerCentralSeriesInfty A).subtype).range := by
    rw [MonoidHom.range_comp]
    rw [Subgroup.range_subtype]
  rw [h_eq_range]
  exact (actionCommutator_map_inl_comp φ (lowerCentralSeriesInfty A).subtype).symm

/-- If `A^∞` centralizes `[G,A]` and `A` centralizes `[G,A^∞]`, then `A^∞` acts
trivially on `G`. This is the final three-subgroups step in Isaacs Thm 4.24. -/
private theorem actionCommutatorInfty_eq_bot_of_centralized_and_fixed
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G)
    (hGA : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ))
    (hKA : actionCommutatorInfty φ ≤ Subgroup.fixedPointsOfMulAut φ) :
    actionCommutatorInfty φ = ⊥ := by
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  set YinfA : Subgroup (G ⋊[φ] A) :=
    (lowerCentralSeriesInfty A).map (SemidirectProduct.inr : A →* G ⋊[φ] A)
  have h_XG_YA_Yinf : ⁅⁅XG, YA⁆, YinfA⁆ = ⊥ := by
    have h := commutator_inl_GA_inr_Ainf_eq_bot_of_centralized (φ := φ) hGA
    simpa [XG, YA, YinfA, actionCommutator_map_inl (φ := φ)] using h
  have h_YA_XG_Yinf : ⁅⁅YA, XG⁆, YinfA⁆ = ⊥ := by
    rw [Subgroup.commutator_comm YA XG]
    exact h_XG_YA_Yinf
  have h_XG_Yinf_eq :
      ⁅XG, YinfA⁆ =
        (actionCommutatorInfty φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A) := by
    simpa [XG, YinfA] using
      commutator_inl_range_inr_lowerCentralSeriesInfty_eq_actionCommutatorInfty_map φ
  have h_XG_Yinf_YA : ⁅⁅XG, YinfA⁆, YA⁆ = ⊥ := by
    have h := commutator_inl_GAinf_inr_A_eq_bot_of_fixed (φ := φ) hKA
    simpa [YA, h_XG_Yinf_eq] using h
  have h_three : ⁅⁅YinfA, YA⁆, XG⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h_YA_XG_Yinf h_XG_Yinf_YA
  have h_Yinf_YA : ⁅YinfA, YA⁆ = YinfA := by
    simp only [YinfA, YA]
    rw [MonoidHom.range_eq_map (SemidirectProduct.inr : A →* G ⋊[φ] A),
      ← Subgroup.map_commutator, lowerCentralSeriesInfty_commutator_top]
  rw [h_Yinf_YA, Subgroup.commutator_comm YinfA XG, h_XG_Yinf_eq] at h_three
  exact (Subgroup.map_eq_bot_iff_of_injective _ SemidirectProduct.inl_injective).mp h_three

/-- **General form of Isaacs Thm 4.24**: under the chain hypothesis, the stable lower
central term `A^∞` acts trivially on `G` (no faithfulness assumption). -/
private theorem actionCommutatorInfty_eq_bot_of_iter_eq_bot_aux :
    ∀ n : ℕ, ∀ {A G : Type*} [Group A] [Finite A] [Group G] [Finite G],
      (φ : A →* MulAut G) → ∀ {m : ℕ}, 1 ≤ m →
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥ →
      Nat.card G ≤ n → actionCommutatorInfty φ = ⊥ := by
  intro n
  induction n with
  | zero =>
      intro A G _ _ _ _ φ m hm h_iter h_le
      exact False.elim (Nat.not_succ_le_zero _ (Nat.card_pos.trans_le h_le))
  | succ n ih =>
      intro A G _ _ _ _ φ m hm h_iter h_le
      by_cases hG_nontriv : Nontrivial G
      swap
      · haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG_nontriv
        change actionCommutator (phiInfty φ) = ⊥
        rw [actionCommutator_eq_bot_iff_acts_trivially]
        intro a g
        exact Subsingleton.elim _ _
      haveI : Nontrivial G := hG_nontriv
      set H : Subgroup G := actionCommutator φ with hH_def
      have hH_ne_top : H ≠ ⊤ := by
        intro htop
        have hH_bot : H = ⊥ := by
          simpa [H, hH_def] using
            actionCommutator_eq_bot_of_eq_top_iterCommutator_eq_bot φ hm
              (by simpa [H, hH_def] using htop) h_iter
        have htop_bot : (⊤ : Subgroup G) = ⊥ := by
          rw [← htop, hH_bot]
        exact (top_ne_bot : (⊤ : Subgroup G) ≠ ⊥) htop_bot
      have hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H := by
        simpa [H, hH_def] using OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator φ
      let ψH : A →* MulAut H := OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH_inv
      have h_iter_H :
          iterCommutator (SemidirectProduct.inl : H →* H ⋊[ψH] A).range
              (SemidirectProduct.inr : A →* H ⋊[ψH] A).range m = ⊥ := by
        simpa [ψH] using iterCommutator_inl_inr_restrict_base_eq_bot
          (φ := φ) (H := H) hH_inv h_iter
      have hH_card_lt : Nat.card H < Nat.card G :=
        subgroup_card_lt_of_ne_top hH_ne_top
      have hH_card_le_n : Nat.card H ≤ n :=
        Nat.le_of_lt_succ (hH_card_lt.trans_le h_le)
      have hIH_H : actionCommutatorInfty ψH = ⊥ :=
        ih ψH hm h_iter_H hH_card_le_n
      have hGA_fixed_by_Ainf : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ) := by
        intro g hg
        rw [Subgroup.mem_fixedPointsOfMulAut]
        intro a
        have htriv := (actionCommutator_eq_bot_iff_acts_trivially (phiInfty ψH)).mp
          hIH_H a ⟨g, by simpa [H, hH_def] using hg⟩
        have hval := congrArg Subtype.val htriv
        simpa [ψH, phiInfty] using hval
      by_cases hK_bot : actionCommutatorInfty φ = ⊥
      · exact hK_bot
      let C : Subgroup G := actionCommutatorInfty_fix φ
      have hC_normal : C.Normal := by
        simpa [C] using actionCommutatorInfty_fix_normal_of_centralized φ hGA_fixed_by_Ainf
      haveI : C.Normal := hC_normal
      have hC_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ C := by
        simpa [C] using actionCommutatorInfty_fix_isAInvariant φ
      have hC_ne_bot : C ≠ ⊥ := by
        simpa [C] using actionCommutatorInfty_fix_ne_bot_of_ne_bot
          (φ := φ) (m := m) h_iter hK_bot
      let φbar : A →* MulAut (G ⧸ C) :=
        OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hC_inv
      have h_iter_bar :
          iterCommutator (SemidirectProduct.inl : G ⧸ C →* (G ⧸ C) ⋊[φbar] A).range
              (SemidirectProduct.inr : A →* (G ⧸ C) ⋊[φbar] A).range m = ⊥ := by
        simpa [φbar] using iterCommutator_inl_inr_quotient_eq_bot
          (φ := φ) (N := C) hC_inv h_iter
      have hC_card_gt_one : 1 < Nat.card C := by
        have hC_card_ne_one : Nat.card C ≠ 1 := fun hcard =>
          hC_ne_bot (Subgroup.card_eq_one.mp hcard)
        have hpos : 0 < Nat.card C := Nat.card_pos
        omega
      have hquot_lt : Nat.card (G ⧸ C) < Nat.card G := by
        have hcard_eq : Nat.card G = Nat.card (G ⧸ C) * Nat.card C :=
          C.card_eq_card_quotient_mul_card_subgroup
        have hq_pos : 0 < Nat.card (G ⧸ C) := Nat.card_pos
        rw [hcard_eq]
        simpa [mul_comm] using
          Nat.mul_lt_mul_of_pos_right hC_card_gt_one hq_pos
      have hquot_le_n : Nat.card (G ⧸ C) ≤ n :=
        Nat.le_of_lt_succ (hquot_lt.trans_le h_le)
      have hIH_bar : actionCommutatorInfty φbar = ⊥ :=
        ih φbar hm h_iter_bar hquot_le_n
      have hK_le_C : actionCommutatorInfty φ ≤ C := by
        have hmap_bot : (actionCommutatorInfty φ).map (QuotientGroup.mk' C) = ⊥ := by
          rw [← actionCommutatorInfty_quotient_eq_map (φ := φ) (N := C) hC_inv,
            hIH_bar]
        have hle_ker : actionCommutatorInfty φ ≤ (QuotientGroup.mk' C).ker :=
          (Subgroup.map_eq_bot_iff (actionCommutatorInfty φ)).mp hmap_bot
        simpa [QuotientGroup.ker_mk'] using hle_ker
      have hK_fixed_by_A : actionCommutatorInfty φ ≤ Subgroup.fixedPointsOfMulAut φ :=
        hK_le_C.trans (by simp [C, actionCommutatorInfty_fix])
      exact actionCommutatorInfty_eq_bot_of_centralized_and_fixed φ
        hGA_fixed_by_Ainf hK_fixed_by_A

/-- **Isaacs Thm 4.24, non-faithful form**:
under the iterated-commutator chain hypothesis, `A^∞` lies in the kernel of the action. -/
theorem lowerCentralSeriesInfty_le_ker_of_iter_inl_inr_eq_bot
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    (φ : A →* MulAut G) {m : ℕ} (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    lowerCentralSeriesInfty A ≤ φ.ker := by
  have hbot : actionCommutatorInfty φ = ⊥ :=
    actionCommutatorInfty_eq_bot_of_iter_eq_bot_aux (Nat.card G) φ hm h_iter le_rfl
  change actionCommutator (phiInfty φ) = ⊥ at hbot
  rw [actionCommutator_eq_bot_iff_acts_trivially] at hbot
  intro a ha
  rw [MonoidHom.mem_ker]
  ext g
  exact hbot ⟨a, ha⟩ g

/-- **Isaacs Theorem 4.24**: if finite `A` acts faithfully on finite `G` and
`[G,A,...,A]=1`, then `A` is nilpotent. -/
theorem isaacs_thm_4_24
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    (φ : A →* MulAut G) (hfaithful : Function.Injective φ)
    {m : ℕ} (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    Group.IsNilpotent A := by
  have hAinf_le_ker := lowerCentralSeriesInfty_le_ker_of_iter_inl_inr_eq_bot
    (φ := φ) hm h_iter
  have hAinf_bot : lowerCentralSeriesInfty A = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have hker : φ a = 1 := by
      simpa [MonoidHom.mem_ker] using hAinf_le_ker ha
    have ha_one : a = 1 := hfaithful (by rw [hker, map_one])
    simp [ha_one]
  rw [nilpotent_iff_lowerCentralSeries]
  exact ⟨Nat.card A, by simpa [lowerCentralSeriesInfty] using hAinf_bot⟩

end /- §4C (続 II) -/

end OddOrder.Isaacs.Ch04
