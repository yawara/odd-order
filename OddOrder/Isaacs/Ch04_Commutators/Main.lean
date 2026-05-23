/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import OddOrder.Isaacs.Ch03_SplitExtensions
import OddOrder.Mathlib.SemidirectProduct
import OddOrder.Mathlib.Subgroup

/-!
# OddOrder.Isaacs.Ch04 — Commutators

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 4
"Commutators" (pp. 113-146) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 4A | 交換子の基礎 + 下降中心列 + maximal class p-群 + Ω_r | 4.1 – 4.8 | 部分 (Lem 4.1, 4.3, 4.6 完成) |
| 4B | Hall-Witt + three-subgroups lemma + Mann | 4.9 – 4.19 | 部分 (Cor 4.10, Thm 4.11, Cor 4.12, Cor 4.13 完成) |
| 4C | A acts on G via automorphisms | 4.20 – 4.27 | TODO (coprime action machinery 要) |
| 4D | Coprime action: Fitting + Thompson P×Q + Baer | 4.28 – 4.38 | 部分 (Lem 4.32 完成; 残 coprime action 要) |

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
    | one => simpa using one_mem _
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

/-! **Isaacs Lemma 4.5** (`P/N` elementary abelian ⇔ `Φ(P) ⊆ N`):
mathlib `Subgroup.frattini` を経由. 形式化保留 (本書 §1B 正式証明の Ch.4 再述). -/

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

/-! **Isaacs Thm 4.7**: maximal class p-群構造 — `A ⊴ P` abelian, `P/A` cyclic,
`|A ∩ Z(P)| = p` ⇒ nilpotence class = `m` where `|A| = p^m`.

Lem 4.6 を経由. 形式化保留. -/

/-! **Isaacs Thm 4.8** (p > 2 + class ≤ 2):
(a) `{x ∈ P : x^p = 1}` is a subgroup;
(b) commutators p乗 = 1 ⇒ `x ↦ x^p` is a homomorphism.

Ch.10 で 2 回引用. Baer trick (Lem 4.37) の前身. 形式化保留. -/

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

/-! ### iterated right commutator infrastructure

Lucchini K = ⊥ case の「Z(F(G)) absorbs G-minimal normal」補題等で使用する.
`E, F ≤ G` に対し `iter E F n = ⁅...⁅E, F⁆, F⁆..., F⁆` (`n` 回右から `F`). -/

/-- **Iterated right commutator**: `iterCommutator E F n = ⁅...⁅E, F⁆, F⁆..., F⁆`. -/
def iterCommutator (E F : Subgroup G) : ℕ → Subgroup G
  | 0 => E
  | n + 1 => ⁅iterCommutator E F n, F⁆

@[simp]
theorem iterCommutator_zero (E F : Subgroup G) :
    iterCommutator E F 0 = E := rfl

@[simp]
theorem iterCommutator_succ (E F : Subgroup G) (n : ℕ) :
    iterCommutator E F (n + 1) = ⁅iterCommutator E F n, F⁆ := rfl

/-- **iterCommutator は F の lcs 経由で押し込められる**: `E ≤ F` ⇒
`iterCommutator E F n ≤ (lowerCentralSeries (↥F) n).map F.subtype`.

特に `F` が冪零 (Group.IsNilpotent ↥F) なら, 十分大きな `n` で `lcs ↥F n = ⊥`,
よって `iterCommutator E F n = ⊥`. これが Lucchini K = ⊥ case の核心 (Z(F(G))
absorbs G-minimal). -/
theorem iterCommutator_le_lowerCentralSeries_map
    {E F : Subgroup G} (hE : E ≤ F) (n : ℕ) :
    iterCommutator E F n ≤ (lowerCentralSeries (↥F) n).map F.subtype := by
  induction n with
  | zero =>
    simp only [iterCommutator_zero, lowerCentralSeries_zero]
    rw [← MonoidHom.range_eq_map, F.range_subtype]
    exact hE
  | succ n ih =>
    rw [iterCommutator_succ]
    have hRange : (⊤ : Subgroup ↥F).map F.subtype = F := by
      rw [← MonoidHom.range_eq_map]; exact F.range_subtype
    have hMapLcs : (lowerCentralSeries (↥F) (n + 1)).map F.subtype =
        ⁅((lowerCentralSeries (↥F) n).map F.subtype), F⁆ := by
      change ⁅lowerCentralSeries (↥F) n, (⊤ : Subgroup ↥F)⁆.map F.subtype = _
      rw [Subgroup.map_commutator, hRange]
    rw [hMapLcs]
    exact Subgroup.commutator_mono ih le_rfl

/-- **iterCommutator は ambient G の lcs に押し込められる**: 任意 `E, F ⊆ G` で
`iterCommutator E F n ≤ lowerCentralSeries G n`. `E ≤ F` 不要 (E, F は ⊤ ≤ G で挟まれる).

`E ≤ ⊤` と `F ≤ ⊤` 経由で `iterCommutator E F n ≤ iterCommutator ⊤ ⊤ n = lcs G n`. -/
theorem iterCommutator_le_lowerCentralSeries (E F : Subgroup G) (n : ℕ) :
    iterCommutator E F n ≤ lowerCentralSeries G n := by
  induction n with
  | zero =>
    simp only [iterCommutator_zero, lowerCentralSeries_zero]
    exact le_top
  | succ n ih =>
    rw [iterCommutator_succ, lowerCentralSeries_succ]
    exact Subgroup.commutator_mono ih le_top

/-- **ambient G 冪零 ⇒ iterCommutator は最終的に ⊥** (任意 E, F).
`E ≤ F` 制約のない一般版 (上の `iterCommutator_eq_bot_of_isNilpotent` は `E ≤ F` 必要). -/
theorem iterCommutator_eq_bot_of_isNilpotent_ambient
    [Group.IsNilpotent G] (E F : Subgroup G) :
    ∃ n, iterCommutator E F n = ⊥ := by
  obtain ⟨n, hn⟩ := nilpotent_iff_lowerCentralSeries.mp ‹_›
  refine ⟨n, le_antisymm ?_ bot_le⟩
  exact (iterCommutator_le_lowerCentralSeries E F n).trans (le_of_eq hn)

/-- **冪零 ambient G + nontrivial normal E ⇒ ⁅E, F⁆ < E**: 厳密降下.

`⁅E, F⁆ = E` なら iterCommutator E F は定常 (induction で各 n で = E). しかし
`iterCommutator_eq_bot_of_isNilpotent_ambient` で ∃ n, iter = ⊥. ⇒ E = ⊥ 矛盾. -/
theorem commutator_lt_self_of_isNilpotent_ambient
    [Group.IsNilpotent G] {E F : Subgroup G} [E.Normal] (hE : E ≠ ⊥) :
    ⁅E, F⁆ < E := by
  refine lt_of_le_of_ne (Subgroup.commutator_le_left E F) ?_
  intro heq
  have hconst : ∀ n, iterCommutator E F n = E := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iterCommutator_succ, ih]
      exact heq
  obtain ⟨n, hn⟩ := iterCommutator_eq_bot_of_isNilpotent_ambient E F
  rw [hconst n] at hn
  exact hE hn

/-- **iterCommutator は normal を保つ**. `E, F ⊴ G` ⇒ `iter E F n ⊴ G`. -/
theorem iterCommutator_normal {E F : Subgroup G} [E.Normal] [F.Normal] (n : ℕ) :
    (iterCommutator E F n).Normal := by
  induction n with
  | zero => exact ‹E.Normal›
  | succ n ih =>
    haveI := ih
    rw [iterCommutator_succ]
    infer_instance

/-- **iterCommutator は antitone (decreasing)**. `E, F ⊴ G` ⇒
`iter E F (n+1) ≤ iter E F n`.

(直観: `iter E F n ⊴ G ⊇ F` で `F` は `iter E F n` を normalize するので
`⁅iter, F⁆ ≤ iter`.) -/
theorem iterCommutator_succ_le_self {E F : Subgroup G} [E.Normal] [F.Normal] (n : ℕ) :
    iterCommutator E F (n + 1) ≤ iterCommutator E F n := by
  haveI : (iterCommutator E F n).Normal := iterCommutator_normal n
  rw [iterCommutator_succ]
  exact Subgroup.commutator_le_left (iterCommutator E F n) F

/-- **F 冪零 ⇒ iterCommutator は最終的に ⊥**: `E ≤ F` + `F` (as group `↥F`) が冪零
⇒ ∃ n, `iter E F n = ⊥`. -/
theorem iterCommutator_eq_bot_of_isNilpotent
    {E F : Subgroup G} (hE : E ≤ F) [hF : Group.IsNilpotent ↥F] :
    ∃ n, iterCommutator E F n = ⊥ := by
  obtain ⟨n, hn⟩ := nilpotent_iff_lowerCentralSeries.mp hF
  refine ⟨n, le_antisymm ?_ bot_le⟩
  calc iterCommutator E F n
      ≤ (lowerCentralSeries (↥F) n).map F.subtype :=
        iterCommutator_le_lowerCentralSeries_map hE n
    _ ≤ ⊥ := by rw [hn]; exact (Subgroup.map_bot F.subtype).le

/-- **iterCommutator は E 内に留まる**: `E, F ⊴ G ⇒ iter E F n ≤ E`. -/
theorem iterCommutator_le_self {E F : Subgroup G} [E.Normal] [F.Normal] (n : ℕ) :
    iterCommutator E F n ≤ E := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact (iterCommutator_succ_le_self n).trans ih

/-- **Z(F(G)) absorbs G-minimal normal in F(G)** ⭐ (Lucchini K=⊥ aux 解消の核補題):
`E ⊴ G` minimal normal, `E ≤ F`, `F ⊴ G` 冪零 ⇒ `E ≤ centralizer F`.

**証明** (Isaacs §4A lcs 経路):
1. `iterCommutator E F` の降下列を考える. 各項は G-normal (`iterCommutator_normal`),
   decreasing (`iterCommutator_succ_le_self`), `E` 内 (`iterCommutator_le_self`).
2. `F` 冪零 で `iter n = ⊥` for some `n` (`iterCommutator_eq_bot_of_isNilpotent`).
3. 最小 `k` で `iter k = ⊥` を取る. `k = 0` だと `E = ⊥` で `E` minimal 仮定と矛盾.
4. `k = j + 1` で, `iter j ≠ ⊥`, `iter j ⊴ G`, `iter j ≤ E`. **E の minimality**
   より `iter j = E`.
5. `⁅E, F⁆ = ⁅iter j, F⁆ = iter (j+1) = iter k = ⊥`. 故に `E ≤ centralizer F`.

**下流**: Ch.2 §2D Lucchini K=⊥ aux. -/
theorem le_centralizer_of_isMinimalNormal {E F : Subgroup G}
    (hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal E) (hEF : E ≤ F)
    [F.Normal] [Group.IsNilpotent ↥F] :
    E ≤ Subgroup.centralizer (F : Set G) := by
  classical
  haveI hE_norm : E.Normal := hMin.1
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  -- Find smallest k with iter E F k = ⊥.
  have hExists : ∃ k, iterCommutator E F k = ⊥ :=
    iterCommutator_eq_bot_of_isNilpotent hEF
  set k := Nat.find hExists with hk_def
  have hk_iter : iterCommutator E F k = ⊥ := Nat.find_spec hExists
  -- k = 0 ⇒ E = ⊥, 矛盾.
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · exfalso
    rw [hk0, iterCommutator_zero] at hk_iter
    exact hMin.2.1 hk_iter
  -- k = j + 1, j minimality に達しない.
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk_pos.ne'
  have hIter_j_ne : iterCommutator E F j ≠ ⊥ := fun h => by
    have hjk : j < k := hj ▸ Nat.lt_succ_self j
    exact absurd (Nat.find_min' hExists h) (not_le.mpr hjk)
  haveI : (iterCommutator E F j).Normal := iterCommutator_normal j
  have hIter_j_le : iterCommutator E F j ≤ E := iterCommutator_le_self j
  rcases hMin.2.2 _ inferInstance hIter_j_le with h_bot | h_eq_E
  · exact absurd h_bot hIter_j_ne
  · -- iter j = E, hence ⁅E, F⁆ = iter (j+1) = iter k = ⊥.
    rw [← h_eq_E, ← iterCommutator_succ,
        show j + 1 = k from hj.symm]
    exact hk_iter

/-- **Helper**: 部分群 `E` で `↥E` 冪零 + 非自明 ⇒ `⁅E, E⁆ < E`.

mathlib `IsSolvable.commutator_lt_of_ne_bot` の冪零部分群版 (ambient `G` の可解性は不要).
証明は mathlib 版を mirror: `IsSolvable ↥E ← IsNilpotent ↥E` + `map_subtype_lt_map_subtype`. -/
theorem commutator_lt_self_of_isNilpotent_subtype
    {G : Type*} [Group G]
    (E : Subgroup G) [Group.IsNilpotent ↥E] [Nontrivial ↥E] :
    ⁅E, E⁆ < E := by
  haveI : IsSolvable ↥E := IsNilpotent.to_isSolvable
  rw [← E.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
      Subgroup.map_subtype_lt_map_subtype]
  exact IsSolvable.commutator_lt_top_of_nontrivial ↥E

/-- **Variant of Thm 3.11 part 1** (minimal normal nilpotent ⇒ abelian):
`E ⊴ G` minimal normal + `↥E` 冪零 ⇒ `E` abelian.

`solvable_minimal_normal_isAbelian` の `[IsSolvable G]` 仮定を `[Group.IsNilpotent ↥E]`
に弱めた版. Lucchini K=⊥ で E ≤ F(G) (G は solvable と限らない) の場合に有用. -/
theorem isCommutative_of_isMinimalNormal_of_isNilpotent_subtype
    {G : Type*} [Group G] [Finite G]
    {E : Subgroup G} (hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal E)
    [Group.IsNilpotent ↥E] :
    ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
  haveI hEnormal : E.Normal := hMin.1
  haveI hE_NT : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hMin.2.1
  have hcomm_lt : ⁅E, E⁆ < E := commutator_lt_self_of_isNilpotent_subtype E
  have hCommNormal : (⁅E, E⁆ : Subgroup G).Normal := inferInstance
  have hcomm_eq_bot : ⁅E, E⁆ = ⊥ := by
    rcases hMin.2.2 ⁅E, E⁆ hCommNormal hcomm_lt.le with h | h
    · exact h
    · exact absurd h hcomm_lt.ne
  intro x hx y hy
  have hcomm_xy : ⁅x, y⁆ ∈ ⁅E, E⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [hcomm_eq_bot, Subgroup.mem_bot] at hcomm_xy
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm_xy

/-- **Variant of Thm 3.11**: minimal normal subgroup of finite group with `↥E` nilpotent
⇒ E is elementary abelian p-group for some prime p.

`solvable_minimal_normal_isElementaryAbelian` の `[IsSolvable G]` 仮定を
`[Group.IsNilpotent ↥E]` に弱めた版. 証明は Ch.3 既存版とほぼ同じだが abelianness 取得を
`isCommutative_of_isMinimalNormal_of_isNilpotent_subtype` に置換.

**Lucchini K=⊥ 用途**: E ≤ F(G) で `↥E` 冪零 (F(G) 冪零の部分群経由) かつ minimal normal の
場合に, E が elementary abelian p-group であることを示す. -/
theorem isElementaryAbelian_of_isMinimalNormal_of_isNilpotent_subtype
    {G : Type*} [Group G] [Finite G]
    {E : Subgroup G} (hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal E)
    [Group.IsNilpotent ↥E] :
    ∃ p : ℕ, p.Prime ∧ E.IsElementaryAbelian p := by
  haveI hEnormal : E.Normal := hMin.1
  have hE_ne_bot : E ≠ ⊥ := hMin.2.1
  have habel := isCommutative_of_isMinimalNormal_of_isNilpotent_subtype hMin
  haveI hEcomm : IsMulCommutative ↥E :=
    ⟨⟨fun a b => Subtype.ext (habel a a.2 b b.2)⟩⟩
  haveI hEnt : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hE_ne_bot
  have hE_card_pos : 1 < Nat.card ↥E := Finite.one_lt_card
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hE_card_pos.ne'
  refine ⟨p, hp_prime, ?_⟩
  haveI hpFact : Fact p.Prime := ⟨hp_prime⟩
  -- T = {x : ↥E | x^p = 1} as Subgroup ↥E.
  let T : Subgroup ↥E :=
    { carrier := {x | x ^ p = 1}
      one_mem' := one_pow p
      mul_mem' := by
        intro a b ha hb
        change (a * b) ^ p = 1
        change a ^ p = 1 at ha
        change b ^ p = 1 at hb
        rw [mul_pow, ha, hb, one_mul]
      inv_mem' := by
        intro a ha
        change a⁻¹ ^ p = 1
        change a ^ p = 1 at ha
        rw [inv_pow, ha, inv_one] }
  haveI hT_char : T.Characteristic := by
    rw [Subgroup.characteristic_iff_le_comap]
    intro φ x hx
    rw [Subgroup.mem_comap]
    change (φ x) ^ p = 1
    change x ^ p = 1 at hx
    rw [← map_pow, hx, map_one]
  obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) p hp_dvd
  have hx_pow : x ^ p = 1 := by
    rw [← hx_ord]; exact pow_orderOf_eq_one x
  have hx_ne_one : x ≠ 1 := by
    intro heq
    rw [heq, orderOf_one] at hx_ord
    exact hp_prime.ne_one hx_ord.symm
  have hT_ne_bot : T ≠ ⊥ := by
    intro hbot
    have hx_T : x ∈ T := hx_pow
    rw [hbot, Subgroup.mem_bot] at hx_T
    exact hx_ne_one hx_T
  haveI hTE_normal : (T.map E.subtype).Normal := inferInstance
  have hTE_le_E : T.map E.subtype ≤ E := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  rcases hMin.2.2 (T.map E.subtype) hTE_normal hTE_le_E with hTE_bot | hTE_eq
  · exfalso
    have hT_eq_bot : T = ⊥ := by
      have : T.map E.subtype = (⊥ : Subgroup ↥E).map E.subtype := by
        rw [hTE_bot, Subgroup.map_bot]
      exact Subgroup.map_injective E.subtype_injective this
    exact hT_ne_bot hT_eq_bot
  · refine ⟨fun a b => Subtype.ext (habel a a.2 b b.2), fun y => ?_⟩
    have hy_TE : (y : G) ∈ T.map E.subtype := by
      rw [hTE_eq]; exact y.2
    obtain ⟨z, hz_T, hz_eq⟩ := hy_TE
    have hzy : z = y := Subtype.ext hz_eq
    exact hzy ▸ hz_T

/-- **Lucchini K=⊥ 1st step (with elem abelian conclusion)**: G 非自明有限, A abelian,
`|A| ≥ |G:A|` ⇒ ∃ `E ⊴ G` minimal normal で:
- `E ≤ F(G)`
- `E ≤ centralizer F(G)` (Z(F(G)) absorbs)
- `E` elementary abelian `p`-group (for some prime `p`)

書籍 p.62 の Lucchini K=⊥ proof の最初の **4 ステップ** を 1 補題に集約:
1. **Cor 2.19** で `F(G) ≠ ⊥`.
2. **`exists_isMinimalNormal_le_of_normal`** で minimal normal `E ≤ F(G)` を取得.
3. **`le_centralizer_of_isMinimalNormal`** (Z(F(G)) absorbs lemma) で
   `E ≤ centralizer F(G)`.
4. **`isElementaryAbelian_of_isMinimalNormal_of_isNilpotent_subtype`** で `E` elem
   abelian p-group. `↥E` 冪零性は `E ≤ F(G)` + `fitting.isNilpotent` +
   `subgroupOfEquivOfLe` 経由.

下流: Lucchini K=⊥ 残 2 case (M abelian/non-abelian) でこの E を使う. -/
theorem exists_isMinimalNormal_le_fitting_le_centralizer_fitting
    {G : Type*} [Group G] [Finite G] [Nontrivial G]
    {A : Subgroup G}
    (hA_ab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hCard : A.index ≤ Nat.card A) :
    ∃ (E : Subgroup G) (p : ℕ), p.Prime ∧
      OddOrder.Isaacs.Ch02.IsMinimalNormal E ∧
      E ≤ OddOrder.Isaacs.Ch01.fitting G ∧
      E ≤ Subgroup.centralizer ((OddOrder.Isaacs.Ch01.fitting G : Subgroup G) : Set G) ∧
      E.IsElementaryAbelian p := by
  -- F(G) ≠ ⊥ via Cor 2.19.
  have hFne : OddOrder.Isaacs.Ch01.fitting G ≠ ⊥ := by
    intro hF
    have h := OddOrder.Isaacs.Ch02.inf_fitting_ne_bot_of_abelian_card_ge_index hA_ab hCard
    apply h
    rw [hF, inf_bot_eq]
  obtain ⟨E, hMin, hEle⟩ :=
    OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal _ hFne
  -- ↥E nilpotent via E ≤ F(G) + subgroupOfEquivOfLe.
  haveI hFNilp : Group.IsNilpotent ↥(OddOrder.Isaacs.Ch01.fitting G) :=
    OddOrder.Isaacs.Ch01.fitting.isNilpotent
  haveI hENilp : Group.IsNilpotent ↥E :=
    nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEle)
  -- E elem abelian p-group.
  obtain ⟨p, hp_prime, hElem⟩ :=
    isElementaryAbelian_of_isMinimalNormal_of_isNilpotent_subtype hMin
  refine ⟨E, p, hp_prime, hMin, hEle, ?_, hElem⟩
  exact le_centralizer_of_isMinimalNormal hMin hEle

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
- **Cor 4.30**: A faithful + chain + coprime ⇒ `|A|` の素因子 ⊆ `|G|` の素因子.
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

end -- 4D

end OddOrder.Isaacs.Ch04
