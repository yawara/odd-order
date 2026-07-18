/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Trivial Intersection (TI) Subsets

`OddOrder.GroupTheory` shared module: TI-subset (trivial intersection subset) の
正式定義. Peterfalvi *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000) §4-§8 全節 + §11-§16 で多用される概念.

## 数学的定義

有限群 `G` の部分集合 `A ⊂ G` が **TI** ⟺ `A` の異なる共役が非自明な交差を持たない:

  `∀ g ∈ G, (A^g ∩ A ≠ ∅) ⟹ g ∈ N_G(A)`

(ここで `A^g = g·A·g⁻¹`, `N_G(A)` は `A` の集合-正規化群)

Peterfalvi の典型 setup は `A = H \ {1}` で, ホスト `L = N_G(H)` に対し
"`A` is TI-subset with normalizer `L`" の形で現れる. 本 module は
**`L` を parameter として取る `IsTISubset A L` 形式** を採用:
- Peterfalvi 流に直結する自然な表現
- `N_G(A)` の毎回計算を回避できる
- §6 (4.6), §8 (6.7) 等で `L = N_G(A)` と限らない一般化された使用にも対応

## mathlib カバレッジ

mathlib v4.29.1 で TI-subset 概念は **完全不在**:
- `Mathlib.GroupTheory.GroupAction.Blocks.IsTrivialBlock` は **別概念**
  (block の singleton/univ 性であって TI とは無関係)
- `Subgroup.normalizer` は subgroup 用 (set 上の集合-正規化群ではない)

そのため本 module で新規定義. (audit 訂正前の per-section ノートで
`MulAction.IsTrivialIntersection` 既存と誤記されていたが該当 API 不在を確認済.)

## Peterfalvi での主要使用箇所

- §4 (2.3): `H(a) = 1 ⟺ A is TI-subset` — Dade Hypothesis の TI 特殊化
- §5 (3.1): `V = W - (W₁∪W₂)` is TI-subset for `N_G(V) = W` (cyclic normalizer)
- §6 (4.3.a): `W - W₂` is TI-subset of `L` (Hypothesis (4.2) 下)
- §8 (6.7), (6.8): `P^# = P \ {1}` is TI-subset (Sylow case, |L| odd)

詳細 audit: `notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md` §3.1 row
`IsTISubset A`. Wave 1a 共有 infra (~80 LOC) として最初に着手.

## 関連 mathlib upstream

将来的に `Mathlib.GroupTheory.Subgroup.TI` へ upstream 視野. 現状は
`OddOrder.GroupTheory` namespace で保持し, naming/API を mathlib 互換に
保ちながら開発する (CLAUDE.md no-mathlib-wrapper policy).
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- A subset `A ⊆ G` is a **TI-subset** with normalizer-bound `L ≤ G` iff every
element `g : G` that produces an overlap between `A` and the conjugate
`g · A · g⁻¹` must already lie in `L`.

Formally: `∀ g : G, (∃ a ∈ A, g * a * g⁻¹ ∈ A) → g ∈ L`.

The intended use is `L = N_G(A)`, in which case the TI condition states that
distinct conjugates of `A` (by elements outside `L`) are mutually disjoint.

Peterfalvi §4-§8 全節共有の predicate. -/
def IsTISubset (A : Set G) (L : Subgroup G) : Prop :=
  ∀ g : G, (∃ a ∈ A, g * a * g⁻¹ ∈ A) → g ∈ L

namespace IsTISubset

variable {A : Set G} {L : Subgroup G}

/-- TI 条件の対偶: `L` 外の `g` では `A` と `g · A · g⁻¹` が disjoint. -/
theorem disjoint_conj_of_not_mem (hA : IsTISubset A L) {g : G} (hg : g ∉ L) :
    ∀ a ∈ A, g * a * g⁻¹ ∉ A := by
  intro a ha hga
  exact hg (hA g ⟨a, ha, hga⟩)

/-- **TI overlap ⇒ conjugator ratio in `L`**: if two `G`-conjugates `g·A·g⁻¹` and `h·A·h⁻¹` of a
TI-subset `A` overlap (share a common element `g·a·g⁻¹ = h·b·h⁻¹` with `a, b ∈ A`), then the
conjugators differ by an element of the normalizer-bound: `h⁻¹·g ∈ L`.  This is the orbit-stabilizer
heart of the conjugate-union counting `|A^G| = [G : L]·|A|` (Peterfalvi (13.10.3) disjoint-union
counting `G = {1} ⊔ G₀ ⊔ (H^#)^G ⊔ (Q^#)^G`): distinct cosets `gL` give *disjoint* conjugates.
Proof: `(h⁻¹g)·a·(h⁻¹g)⁻¹ = h⁻¹·(g·a·g⁻¹)·h = h⁻¹·(h·b·h⁻¹)·h = b ∈ A`, so the TI condition
places `h⁻¹g ∈ L`. -/
theorem mem_of_conj_mem_conj (hA : IsTISubset A L) {g h a b : G}
    (ha : a ∈ A) (hb : b ∈ A) (hab : g * a * g⁻¹ = h * b * h⁻¹) : h⁻¹ * g ∈ L := by
  refine hA (h⁻¹ * g) ⟨a, ha, ?_⟩
  have key : (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹ = b := by
    have e : (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * a * g⁻¹) * h := by group
    rw [e, hab]; group
  rw [key]; exact hb

/-- **Distinct conjugates of a TI-subset are disjoint**: if the conjugator ratio `h⁻¹·g ∉ L`, then
no
element is simultaneously a `g`-conjugate and an `h`-conjugate of elements of `A` — i.e. `g·A·g⁻¹`
and `h·A·h⁻¹` are disjoint.  This is the disjoint-union step of the conjugate-union counting
`|A^G| = [G : L]·|A|`: the conjugates are indexed by cosets `gL` (via `mem_of_conj_mem_conj`) and
distinct cosets give disjoint conjugates.  Contrapositive of `mem_of_conj_mem_conj`. -/
theorem conj_disjoint_of_ratio_not_mem (hA : IsTISubset A L) {g h x : G} (hgh : h⁻¹ * g ∉ L)
    (hxg : ∃ a ∈ A, x = g * a * g⁻¹) (hxh : ∃ b ∈ A, x = h * b * h⁻¹) : False := by
  obtain ⟨a, ha, hxa⟩ := hxg
  obtain ⟨b, hb, hxb⟩ := hxh
  exact hgh (hA.mem_of_conj_mem_conj ha hb (hxa.symm.trans hxb))

/-- 対偶の逆: 「`L` 外で全ての `a ∈ A` の共役が `A` 外」⇒ TI. `IsTISubset` の
構築によく使う introduction form. -/
theorem of_disjoint_conj
    (h : ∀ g : G, g ∉ L → ∀ a ∈ A, g * a * g⁻¹ ∉ A) :
    IsTISubset A L := by
  intro g ⟨a, ha, hga⟩
  by_contra hg
  exact h g hg a ha hga

/-- ホスト部分群を緩めても TI: `L ≤ L'` なら `A` は `L'` 相対でも TI. -/
theorem mono {L' : Subgroup G} (hA : IsTISubset A L) (hLL' : L ≤ L') :
    IsTISubset A L' :=
  fun g hg => hLL' (hA g hg)

/-- 部分集合に絞っても TI: `A' ⊆ A` なら `A'` も同じ `L` で TI. -/
theorem subset {A' : Set G} (hA : IsTISubset A L) (hA' : A' ⊆ A) :
    IsTISubset A' L :=
  fun g ⟨a, ha', hga'⟩ => hA g ⟨a, hA' ha', hA' hga'⟩

/-- もし `A` が `L`-bound の TI-subset で `x ∈ A` なら, `x` の `G`-中心化群全体が `L`
に収まる: `c ∈ C_G(x)` は `x = c x c⁻¹ ∈ A` を固定するので, TI 条件が `c ∈ L` を強制
する. BG Thm II の "`C_G(x) ⊄ M` ⇒ `x ∈ M_σ`" 論法で使う汎用 infra. -/
theorem centralizer_le (hA : IsTISubset A L) {x : G} (hx : x ∈ A) :
    Subgroup.centralizer ({x} : Set G) ≤ L := by
  intro c hc
  have hcomm : x * c = c * x :=
    Subgroup.mem_centralizer_iff.mp hc x (Set.mem_singleton x)
  have hfix : c * x * c⁻¹ ∈ A := by
    have hxx : c * x * c⁻¹ = x := by rw [← hcomm, mul_inv_cancel_right]
    rwa [hxx]
  exact hA c ⟨x, hx, hfix⟩

/-- **TI transport along an `M`-conjugacy saturation.**  If `T` is a TI-subset with
normalizer-bound `Z ≤ M`, and every element of `A` is `M`-conjugate to an element of `T`
(i.e. `A` lies inside the `M`-conjugacy saturation `⋃_{m ∈ M} m·T·m⁻¹`), then `A` is itself a
TI-subset with normalizer-bound `M`.

This is the abstract content behind BG Theorem B(5) and C(9): the sets `A(M) − M_σ` and
`A_0(M) − A(M)` are contained in `M`-conjugacy saturations of TI-sets (the `σ`-singular pieces,
resp. `Ẑ = Z − (K ∪ K*)`), so they inherit TI-ness with normalizer `M`.

Proof: for `a, g·a·g⁻¹ ∈ A`, write `a = m₁·t₁·m₁⁻¹` and `g·a·g⁻¹ = m₂·t₂·m₂⁻¹` with `mᵢ ∈ M`,
`tᵢ ∈ T`.  Then `h := m₂⁻¹·g·m₁` conjugates `t₁` to `t₂ ∈ T`, so `h ∈ Z ≤ M` by the TI property
of `T`, whence `g = m₂·h·m₁⁻¹ ∈ M`. -/
theorem of_subset_conj_of_isTISubset {T : Set G} {Z M : Subgroup G}
    (hT : IsTISubset T Z) (hZM : Z ≤ M)
    (hsub : ∀ a ∈ A, ∃ m ∈ M, ∃ t ∈ T, a = m * t * m⁻¹) :
    IsTISubset A M := by
  intro g ⟨a, ha, hga⟩
  obtain ⟨m₁, hm₁, t₁, ht₁, ha₁⟩ := hsub a ha
  obtain ⟨m₂, hm₂, t₂, ht₂, ha₂⟩ := hsub _ hga
  -- `h := m₂⁻¹ * g * m₁` conjugates `t₁` to `t₂ ∈ T`.
  have hconj : (m₂⁻¹ * g * m₁) * t₁ * (m₂⁻¹ * g * m₁)⁻¹ = t₂ := by
    have e : (m₂⁻¹ * g * m₁) * t₁ * (m₂⁻¹ * g * m₁)⁻¹
        = m₂⁻¹ * (g * (m₁ * t₁ * m₁⁻¹) * g⁻¹) * m₂ := by group
    rw [e, ← ha₁, ha₂]; group
  -- The TI property of `T` then places `h` in `Z ≤ M`, and `g = m₂ · h · m₁⁻¹ ∈ M`.
  have hhZ : m₂⁻¹ * g * m₁ ∈ Z := hT _ ⟨t₁, ht₁, by rw [hconj]; exact ht₂⟩
  have hgM : m₂ * (m₂⁻¹ * g * m₁) * m₁⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem hm₂ (hZM hhZ)) (M.inv_mem hm₁)
  have hg_eq : m₂ * (m₂⁻¹ * g * m₁) * m₁⁻¹ = g := by group
  rwa [hg_eq] at hgM

end IsTISubset

end OddOrder.GroupTheory

namespace Subgroup

variable {G : Type*} [Group G]

/-- A subgroup `H ≤ G` is **TI** iff its non-identity part `H \ {1}` is a
TI-subset (in the `OddOrder.GroupTheory.IsTISubset` sense) relative to the
normalizer `N_G(H)`.

これは古典的な「Trivial Intersection 部分群」の概念: 異なる共役
`g H g⁻¹` (g ∉ N_G(H)) は `H` と `{1}` のみで交わる.

Peterfalvi §8 (6.7), (6.8) で `P` Sylow `p`-部分群 + `L = N_G(P)`, `P^#` TI
の形で多用. -/
def IsTI (H : Subgroup G) : Prop :=
  OddOrder.GroupTheory.IsTISubset ((H : Set G) \ {1}) (Subgroup.normalizer (H : Set G))

end Subgroup
