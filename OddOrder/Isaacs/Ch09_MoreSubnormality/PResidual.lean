/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Order.Minimal

/-!
# The `p`-residual `O^p(G)` (Isaacs Ch. 9 §9C 準備)

`O^p(G)` = **`p`-residual** = 商が `p`-群になる最小の正規部分群 (書籍 p. 283 の
Lemma 9.26 で使う). 「`G/N` が `p`-群となる正規部分群 `N` の交わり」として定義し API を与える:

- `pResidual p G` (= `O^p(G)`): `sInf {N | N ◁ G ∧ IsPGroup p (G/N)}`.
- `pResidual.characteristic`: `O^p(G)` は characteristic (∴ normal).
- `isPGroup_quotient_pResidual` (**核心**): `G/O^p(G)` は `p`-群
  (集合 `{N | G/N が p-群}` が `⊓` で閉じ有限ゆえ最小元 = `sInf` を持つ).
- `pResidual_le_iff_isPGroup_quotient`: `O^p(G) ≤ N ⟺ G/N が p-群` (`N ◁ G`).

## 実装ノート

`nilpotentResidual` (lower central series の交わり) の `O^p` 版だが, `O^p` には自然な
降列が無いので「`p`-群商を与える正規部分群の sInf」で定義する. 集合の元 `N` に対し
`G ⧸ N` の群構造は `N.Normal` を要するので, 述語は `∃ _ : N.Normal, IsPGroup p (G⧸N)`
の形で書く (匿名仮説がインスタンス解決に載る).
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup QuotientGroup

variable {G : Type*} [Group G]

/-- `G/N` が `p`-群となる正規部分群 `N` の集合. -/
def pQuotientNormals (p : ℕ) (G : Type*) [Group G] : Set (Subgroup G) :=
  {N : Subgroup G | ∃ _ : N.Normal, IsPGroup p (G ⧸ N)}

/-- **`p`-residual** `O^p(G)`: 商が `p`-群となる最小の正規部分群. -/
def pResidual (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  sInf (pQuotientNormals p G)

variable {p : ℕ}

theorem normal_of_mem_pQuotientNormals {N : Subgroup G} (hN : N ∈ pQuotientNormals p G) :
    N.Normal := hN.choose

theorem isPGroup_quotient_of_mem_pQuotientNormals {N : Subgroup G} [N.Normal]
    (hN : N ∈ pQuotientNormals p G) : IsPGroup p (G ⧸ N) := hN.choose_spec

theorem top_mem_pQuotientNormals : (⊤ : Subgroup G) ∈ pQuotientNormals p G := by
  refine ⟨inferInstance, ?_⟩
  haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  exact fun g => ⟨0, by rw [pow_zero, pow_one]; exact Subsingleton.elim g 1⟩

/-- automorphism `ψ` による `comap` は `p`-群商を保つ: `G/N` が `p`-群なら
`G/(comap ψ N)` も `p`-群 (`ψ` が誘導する同型 `G/(comap ψ N) ≃ G/N`). -/
theorem isPGroup_quotient_comap (ψ : G ≃* G) {N : Subgroup G} [N.Normal]
    (hN : IsPGroup p (G ⧸ N)) :
    IsPGroup p (G ⧸ Subgroup.comap ψ.toMonoidHom N) := by
  haveI : (Subgroup.comap ψ.toMonoidHom N).Normal := ‹N.Normal›.comap _
  set f := (QuotientGroup.mk' N).comp ψ.toMonoidHom with hf
  have hsurj : Function.Surjective f :=
    (QuotientGroup.mk'_surjective N).comp ψ.surjective
  have hker : f.ker = Subgroup.comap ψ.toMonoidHom N := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have e : (G ⧸ Subgroup.comap ψ.toMonoidHom N) ≃* (G ⧸ N) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  exact hN.of_equiv e.symm

theorem comap_mem_pQuotientNormals (ψ : G ≃* G) {N : Subgroup G}
    (hN : N ∈ pQuotientNormals p G) :
    Subgroup.comap ψ.toMonoidHom N ∈ pQuotientNormals p G := by
  haveI := normal_of_mem_pQuotientNormals hN
  exact ⟨‹N.Normal›.comap _,
    isPGroup_quotient_comap ψ (isPGroup_quotient_of_mem_pQuotientNormals hN)⟩

/-- `comap ψ (comap ψ.symm K) = K` (`ψ` は自己同型). -/
private theorem comap_comap_symm (ψ : G ≃* G) (K : Subgroup G) :
    Subgroup.comap ψ.toMonoidHom (Subgroup.comap ψ.symm.toMonoidHom K) = K := by
  rw [Subgroup.comap_comap]
  have : ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [this, Subgroup.comap_id]

instance pResidual.characteristic : (pResidual p G).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_eq]
  have key : ∀ ψ : G ≃* G,
      Subgroup.comap ψ.toMonoidHom (pResidual p G) ≤ pResidual p G := fun ψ =>
    le_sInf fun M hM =>
      (Subgroup.comap_mono (sInf_le (comap_mem_pQuotientNormals ψ.symm hM))).trans_eq
        (comap_comap_symm ψ M)
  intro ψ
  refine le_antisymm (key ψ) ?_
  calc pResidual p G
      = Subgroup.comap ψ.toMonoidHom (Subgroup.comap ψ.symm.toMonoidHom (pResidual p G)) :=
        (comap_comap_symm ψ _).symm
    _ ≤ Subgroup.comap ψ.toMonoidHom (pResidual p G) := Subgroup.comap_mono (key ψ.symm)

instance pResidual.normal : (pResidual p G).Normal := inferInstance

/-- `p`-群商を与える正規部分群の集合は `⊓` で閉じている: `G/N₁`, `G/N₂` が `p`-群なら
`G/(N₁⊓N₂)` も `p`-群 (`G/(N₁⊓N₂) ↪ (G/N₁)×(G/N₂)`). -/
theorem inf_mem_pQuotientNormals [Finite G] [Fact p.Prime] {N₁ N₂ : Subgroup G}
    (h₁ : N₁ ∈ pQuotientNormals p G) (h₂ : N₂ ∈ pQuotientNormals p G) :
    N₁ ⊓ N₂ ∈ pQuotientNormals p G := by
  haveI := normal_of_mem_pQuotientNormals h₁
  haveI := normal_of_mem_pQuotientNormals h₂
  have hpg₁ := isPGroup_quotient_of_mem_pQuotientNormals h₁
  have hpg₂ := isPGroup_quotient_of_mem_pQuotientNormals h₂
  refine ⟨inferInstance, ?_⟩
  have hprod : IsPGroup p ((G ⧸ N₁) × (G ⧸ N₂)) := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hpg₁
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hpg₂
    exact IsPGroup.of_card (by rw [Nat.card_prod, ha, hb, ← pow_add])
  set φ := (QuotientGroup.mk' N₁).prod (QuotientGroup.mk' N₂) with hφ
  have hker : φ.ker = N₁ ⊓ N₂ := by
    rw [hφ, MonoidHom.ker_prod, QuotientGroup.ker_mk', QuotientGroup.ker_mk']
  have e : (G ⧸ (N₁ ⊓ N₂)) ≃* φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)
  exact (hprod.to_subgroup φ.range).of_equiv e.symm

/-- **核心**: `G/O^p(G)` は `p`-群. `p`-群商を与える正規部分群の集合は `⊓` で閉じ有限ゆえ
最小元 `N₀` をもち, `sInf = N₀ ∈` 集合ゆえ `G/O^p(G) = G/N₀` は `p`-群. -/
theorem isPGroup_quotient_pResidual [Finite G] [Fact p.Prime] :
    IsPGroup p (G ⧸ pResidual p G) := by
  haveI : Finite (Subgroup G) := Finite.of_injective _ (SetLike.coe_injective (A := Subgroup G))
  haveI : WellFoundedLT (Subgroup G) := Finite.to_wellFoundedLT
  obtain ⟨N₀, hN₀⟩ :=
    exists_minimal_of_wellFoundedLT (· ∈ pQuotientNormals p G) ⟨⊤, top_mem_pQuotientNormals⟩
  have hmin : ∀ M ∈ pQuotientNormals p G, N₀ ≤ M := fun M hM =>
    (hN₀.2 (inf_mem_pQuotientNormals hN₀.1 hM) inf_le_left).trans inf_le_right
  have hpr : pResidual p G = N₀ := le_antisymm (sInf_le hN₀.1) (le_sInf hmin)
  haveI := normal_of_mem_pQuotientNormals hN₀.1
  exact (isPGroup_quotient_of_mem_pQuotientNormals hN₀.1).of_equiv
    (QuotientGroup.quotientMulEquivOfEq hpr).symm

/-- 普遍性 (易しい向き): `N ◁ G`, `G/N` が `p`-群 ⇒ `O^p(G) ≤ N`. -/
theorem pResidual_le_of_isPGroup_quotient {N : Subgroup G} [N.Normal]
    (hN : IsPGroup p (G ⧸ N)) : pResidual p G ≤ N :=
  sInf_le ⟨inferInstance, hN⟩

end OddOrder.Isaacs.Ch09
