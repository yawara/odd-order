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
# Isaacs §4A — commutator basics, lower central series, Thm 4.7/4.8 (pp. 113-122)

Split from the former monolithic `OddOrder.Isaacs.Ch04_Commutators.Main` (directory split, issue 0103).
-/

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
| 下降中心列 `G^k` | `Subgroup.lowerCentralSeries` (`(⊤ : Subgroup G).lowerCentralSeries`), `Subgroup.lowerCentralSeries_succ` |

注: mathlib `(⊤ : Subgroup G).lowerCentralSeries` の index 規約は Isaacs `G^k` と
**オフセット 1 ずれ** — mathlib `lcs 0 = ⊤ = G^1`, `lcs 1 = G' = G^2`, `lcs n = G^{n+1}`.

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
lemma commutatorElement_mem_commutator_top (x y : G) :
    ⁅x, y⁆ ∈ _root_.commutator G := by
  rw [_root_.commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

/-- In class ≤ 2 (`commutator G ≤ Z(G)`), the map `⁅·, z⁆ : G → G'` is a
homomorphism on the left: `⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆`.

**証明**: 一般 identity `⁅x*y, z⁆ = x · ⁅y, z⁆ · x⁻¹ · ⁅x, z⁆` で `⁅y, z⁆` 中心
⇒ `x · ⁅y, z⁆ = ⁅y, z⁆ · x` ⇒ `x · ⁅y, z⁆ · x⁻¹ = ⁅y, z⁆`. 結果 `⁅y, z⁆ · ⁅x, z⁆`
を `⁅x, z⁆` 中心で swap. -/
lemma commutatorElement_mul_left_of_class_le_two
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
      (Group.normalizerCondition_of_isNilpotent (G := P)) hMax
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
      (Group.normalizerCondition_of_isNilpotent (G := P)) hMax
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
      (Group.normalizerCondition_of_isNilpotent (G := P)) hMax
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

**証明** (Isaacs p.118): `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` 経由.
- (≥) 部分 = `commutator_top_subgroup_le_commutator` (上記, 仮定不要).
- (≤) 部分: `Q := G/⁅A, ⊤⁆` が abelian を示す.
  - lift `f : Q →* G/A` (mk' A の lift, 可能なのは `⁅A, ⊤⁆ ≤ A` (Lem 4.3 + A 正規)).
  - `f.ker = image(A) in Q ≤ center(Q)` (`⁅a, g⁆ ∈ ⁅A, ⊤⁆` で Q では `ag = ga`).
  - codomain `G/A` cyclic (hypothesis).
  - `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`
    ⇒ Q commutative ⇒ commutator G ≤ ⁅A, ⊤⁆. -/
theorem commutator_eq_commutator_of_normal_abelian_cyclic_quotient
    {A : Subgroup G} [A.Normal]
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
    (f.isMulCommutative_of_isCyclic_of_ker_le_center hker_central).is_comm.comm
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
theorem commutatorRightHom_range_eq_commutator {A : Subgroup G} [A.Normal]
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

/-! ### Thm 4.7: maximal class p-群 (helpers + base case m = 1)

surjective `f` での `(lcs G n).map f = lcs H n` (旧自前 helper
`lowerCentralSeries_map_eq_of_surjective`) は mathlib `Subgroup.map_lowerCentralSeries`
(一般 `f` で等号) + `Subgroup.map_top_of_surjective` の合成で直接得る (wrapper 方針). -/

/-- **Thm 4.7, m = 1 case**: `A ⊴ P` abelian, `P` p-群, `|A| = p`, `P/A` cyclic,
`|A ⊓ Z(P)| = p` ⇒ `Group.nilpotencyClass P = 1` (i.e., P abelian, nontrivial).

`|A| = |A ⊓ Z(P)| = p` ⇒ `A ⊆ Z(P)` (両者 ⊆ A で等カード ⇒ 等). P/A cyclic +
`A ⊆ Z(P)` ⇒ P abelian (`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`). -/
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
    exact ((QuotientGroup.mk' A).isMulCommutative_of_isCyclic_of_ker_le_center
      hker_le).is_comm.comm
  -- commutator P = ⊥ via center P = ⊤
  have hcomm_bot : _root_.commutator P = ⊥ := by
    rw [commutator_eq_bot_iff_center_eq_top, Subgroup.eq_top_iff']
    intro x
    rw [Subgroup.mem_center_iff]
    intro y
    exact hP_abelian y x
  -- nilpotencyClass ≤ 1
  have h_class_le : Group.nilpotencyClass P ≤ 1 := by
    rw [← Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
      Subgroup.top_lowerCentralSeries_one]
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
    rw [Group.nilpotencyClass_zero_iff_subsingleton] at h
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
  `Subgroup.map_lowerCentralSeries` (+ `Subgroup.map_top_of_surjective`). -/
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
      have := Subgroup.map_lowerCentralSeries (S := (⊤ : Subgroup P)) φ 1
      rwa [Subgroup.map_top_of_surjective φ hφ_surj, Subgroup.top_lowerCentralSeries_one,
        Subgroup.top_lowerCentralSeries_one] at this
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
    have h_lcs_Pbar_k : (⊤ : Subgroup (P ⧸ Z)).lowerCentralSeries k = ⊥ :=
      Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr h_class_Pbar.le
    have h_lcs_Pbar_km1_ne : (⊤ : Subgroup (P ⧸ Z)).lowerCentralSeries (k - 1) ≠ ⊥ := by
      intro h_eq
      have := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp h_eq
      rw [h_class_Pbar] at this
      omega
    -- lcs P k ≤ Z (lift lcs P̄ k = ⊥ back)
    have h_lcs_P_k_le_Z : (⊤ : Subgroup P).lowerCentralSeries k ≤ Z := by
      have h_map : Subgroup.map φ ((⊤ : Subgroup P).lowerCentralSeries k)
          = (⊤ : Subgroup (P ⧸ Z)).lowerCentralSeries k := by
        rw [Subgroup.map_lowerCentralSeries, Subgroup.map_top_of_surjective φ hφ_surj]
      rw [h_lcs_Pbar_k] at h_map
      have h_le_ker : (⊤ : Subgroup P).lowerCentralSeries k ≤ φ.ker :=
        (Subgroup.map_eq_bot_iff _).mp h_map
      rw [hφ_ker] at h_le_ker
      exact h_le_ker
    -- lcs P (k+1) = ⊥ (lcs P k ≤ Z ≤ Z(P))
    have h_lcs_P_kp1 : (⊤ : Subgroup P).lowerCentralSeries (k + 1) = ⊥ :=
      Subgroup.lowerCentralSeries_succ_eq_bot ⊤ (h_lcs_P_k_le_Z.trans hZ_le_center)
    -- lcs P k ≠ ⊥
    have h_lcs_P_k_ne : (⊤ : Subgroup P).lowerCentralSeries k ≠ ⊥ := by
      -- Case k = 1: lcs P 1 = commutator P ≠ ⊥
      -- Case k ≥ 2: lcs P (k-1) ⊆ commutator P ⊆ A, lcs P (k-1) ⊄ Z ⇒ ...
      by_cases hk1 : k = 1
      · -- k = 1
        subst hk1
        rw [Subgroup.top_lowerCentralSeries_one]
        intro h_bot
        rw [h_bot, Subgroup.card_bot] at hG'_card
        -- p^1 = 1 ⇒ p = 1, contradiction
        rw [pow_one] at hG'_card
        omega
      · -- k ≥ 2: lcs P (k-1) ⊆ commutator P ⊆ A,
        -- lcs P (k-1) ⊄ Z ⇒ lcs P (k-1) ⊄ Z(P) ⇒ lcs P k ≠ ⊥
        intro h_lcs_k_bot
        -- lcs P (k-1) maps to lcs P̄ (k-1) ≠ ⊥
        have h_map_km1 : Subgroup.map φ ((⊤ : Subgroup P).lowerCentralSeries (k - 1))
            = (⊤ : Subgroup (P ⧸ Z)).lowerCentralSeries (k - 1) := by
          rw [Subgroup.map_lowerCentralSeries, Subgroup.map_top_of_surjective φ hφ_surj]
        -- lcs P (k-1) ⊄ Z (= φ.ker)
        have h_lcs_km1_nle_Z : ¬ (⊤ : Subgroup P).lowerCentralSeries (k - 1) ≤ Z := by
          intro h_le
          have h_le_ker : (⊤ : Subgroup P).lowerCentralSeries (k - 1) ≤ φ.ker := by
            rw [hφ_ker]; exact h_le
          have : Subgroup.map φ ((⊤ : Subgroup P).lowerCentralSeries (k - 1)) = ⊥ :=
            (Subgroup.map_eq_bot_iff _).mpr h_le_ker
          rw [h_map_km1] at this
          exact h_lcs_Pbar_km1_ne this
        -- lcs P (k-1) ⊆ commutator P ⊆ A (using k - 1 ≥ 1, lcs decreasing)
        have hk_one_le : 1 ≤ k - 1 := by omega
        have h_lcs_km1_le_G' :
            (⊤ : Subgroup P).lowerCentralSeries (k - 1) ≤ _root_.commutator P := by
          rw [← Subgroup.top_lowerCentralSeries_one]
          exact (⊤ : Subgroup P).lowerCentralSeries_antitone hk_one_le
        have h_lcs_km1_le_A : (⊤ : Subgroup P).lowerCentralSeries (k - 1) ≤ A :=
          h_lcs_km1_le_G'.trans hG'_le_A
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
        have h_xy_in_kp : ⁅x, y⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries ((k - 1) + 1) := by
          show ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup P).lowerCentralSeries (k - 1), (⊤ : Subgroup P)⁆
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
      exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp h_lcs_P_kp1
    · -- ≥ : NOT (nilpotencyClass ≤ k)
      by_contra h
      push Not at h
      have : (⊤ : Subgroup P).lowerCentralSeries k = ⊥ :=
        Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (Nat.lt_succ_iff.mp h)
      exact h_lcs_P_k_ne this

/-! ### Commutator collection in class ≤ 2 (Thm 4.8 の前段) -/

/-- General identity: `y * x = ⁅y, x⁆ * x * y` (no hypothesis). -/
private lemma mul_eq_commutator_mul (x y : G) :
    y * x = ⁅y, x⁆ * x * y := by
  simp only [commutatorElement_def]
  group

/-- In class ≤ 2 (`commutator G ≤ Z(G)`): `y * x = x * y * ⁅y, x⁆`.
`⁅y, x⁆` 中心で `y * x = ⁅y, x⁆ * (x * y) = (x * y) * ⁅y, x⁆`. -/
lemma mul_comm_commutator_of_class_le_two
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

end OddOrder.Isaacs.Ch04
