/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import OddOrder.Isaacs.Ch03_SplitExtensions

/-!
# OddOrder.Isaacs.Ch04 — Commutators

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 4
"Commutators" (pp. 113-146) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 4A | 交換子の基礎 + 下降中心列 + maximal class p-群 + Ω_r | 4.1 – 4.8 | 着手中 |
| 4B | Hall-Witt + three-subgroups lemma + Mann | 4.9 – 4.19 | TODO |
| 4C | A acts on G via automorphisms | 4.20 – 4.27 | TODO |
| 4D | Coprime action: Fitting + Thompson P×Q + Baer | 4.28 – 4.38 | TODO (FT クリティカル) |

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

**証明骨子** (Isaacs p.118):
- (≥) 部分 = `commutator_top_subgroup_le_commutator` (上記, 仮定不要).
- (≤) 部分 `G' ≤ ⁅A, ⊤⁆`: `G/⁅A, ⊤⁆` が abelian であることを示す.
  - `commutative_of_cyclic_center_quotient` (mathlib `Cyclic.lean:180`) を Q = G/⁅A,⊤⁆ に
    適用: Q → G/A が cyclic codomain (hypothesis) で ker = (image of A in Q) ⊆ Z(Q).
  - Z(Q) 包含: `a ∈ A, x ∈ G ⇒ ⁅a, x⁆ ∈ ⁅A, ⊤⁆` ⇒ Q で `ax ≡ xa`.
  - ⁅A, ⊤⁆ ≤ A (A 正規 + Lem 4.3) で `Q/ker ≅ G/A` cyclic.
形式化保留 (~80 LOC: mathlib `commutative_of_cyclic_center_quotient` の wrapper として
構築). -/
theorem commutator_eq_commutator_of_normal_abelian_cyclic_quotient
    {A : Subgroup G} [A.Normal] [Finite G]
    (_hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (_hCyclic : IsCyclic (G ⧸ A)) :
    _root_.commutator G = ⁅A, (⊤ : Subgroup G)⁆ := by
  refine le_antisymm ?_ (commutator_top_subgroup_le_commutator A)
  -- 残り方向: commutator G ≤ ⁅A, ⊤⁆. `commutative_of_cyclic_center_quotient` 経由.
  sorry

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

/-! **Isaacs Thm 4.11** (`⁅G^i, G^j⁆ ≤ G^{i+j}`): mathlib `lowerCentralSeries` の加法性.
新規補題 ~30 行. **Lucchini K=⊥ aux 前提** (Ch.2 §2D ノートで指摘). 形式化保留. -/

/-! **Isaacs Cor 4.12** (weight n commutator ⊆ G^n), **Cor 4.13** (derived ⊆ lcs,
derived length ≤ 1 + log₂ m): 4.11 系. 形式化保留. -/

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

end -- 4D

end OddOrder.Isaacs.Ch04
