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

/-- `O^p(G) = ⊥ ⟺ G は p-群`. (`G/O^p(G)` が p-群なので `O^p(G)=⊥` なら `G` も; 逆は
`G/⊥ ≅ G` が p-群ゆえ `O^p(G) ≤ ⊥`.) -/
theorem pResidual_eq_bot_iff_isPGroup [Finite G] [Fact p.Prime] :
    pResidual p G = ⊥ ↔ IsPGroup p G := by
  constructor
  · intro h
    exact (((isPGroup_quotient_pResidual (p := p) (G := G)).of_equiv
      (QuotientGroup.quotientMulEquivOfEq h)).of_equiv QuotientGroup.quotientBot)
  · intro hG
    exact le_bot_iff.mp
      (pResidual_le_of_isPGroup_quotient (hG.of_equiv QuotientGroup.quotientBot.symm))

/-- 正規部分群 `S ◁ G` の characteristic 部分群 `C` は `G` に normal (`C.map S.subtype ◁ G`).
`g` 共役は `S` 上の自己同型 `conjNormal g` を誘導し, characteristic ゆえ `C` を保つ. -/
theorem map_subtype_normal_of_characteristic {S : Subgroup G} [S.Normal]
    (C : Subgroup ↥S) [C.Characteristic] : (C.map S.subtype).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_map] at hn
  obtain ⟨c, hc, rfl⟩ := hn
  have hcC : MulAut.conjNormal g c ∈ C :=
    Subgroup.mem_comap.mp
      ((Subgroup.characteristic_iff_comap_eq.mp ‹C.Characteristic› (MulAut.conjNormal g)).symm ▸ hc)
  have heq : g * S.subtype c * g⁻¹ = S.subtype (MulAut.conjNormal g c) :=
    (MulAut.conjNormal_apply g c).symm
  rw [heq]
  exact Subgroup.mem_map_of_mem _ hcC

/-- **Isaacs Corollary 9.27** (p. 283): `S ◁ G` ならば `O^p(S) ◁ G` (ambient で
`(O^p ↥S).map S.subtype`), 特に任意の `P ≤ G` (書籍では `P ◁ G` p-群) が `O^p(S)` を正規化する.

書籍は 9.26 (`O^p(SP) = O^p(S)`) を経由するが, `O^p(S)` は `S` に characteristic なので
`S ◁ G` から直接 `G`-normal (より一般に `P` の p-群性は不要). -/
theorem pResidual_map_subtype_normal {S : Subgroup G} [S.Normal] :
    ((pResidual p ↥S).map S.subtype).Normal :=
  map_subtype_normal_of_characteristic _

/-- **Isaacs Lemma 9.26** (p. 283): `G = SP`, `S ◁ G`, `P ◁ G` p-群 ⇒ `O^p(G) = O^p(S)`
(ambient: `pResidual p G = (pResidual p ↥S).map S.subtype`). `O^p` 版の Lemma 9.15.

証明: `R_S := O^p(S)` は `S` に characteristic ゆえ `◁ G`, `R_S ≤ S`, `R_S.subgroupOf S =
O^p(↥S)`. `G/S` は p-群 (`G=SP`). `⊆`: `[G:R_S] = [S:R_S][G:S] = p^a·p^b` で `G/R_S` p-群
→ 普遍性。`⊇`: `↥S/(R_G⊓S).subgroupOf S ↪ G/R_G` (p-群) ゆえ `O^p(↥S) ≤ (R_G⊓S).subgroupOf S`,
map して `R_S ≤ R_G`. -/
theorem pResidual_eq_map_subtype_of_sup_isPGroup [Finite G] [Fact p.Prime]
    {S P : Subgroup G} [S.Normal] [P.Normal] (hP : IsPGroup p ↥P) (hSP : S ⊔ P = ⊤) :
    pResidual p G = (pResidual p ↥S).map S.subtype := by
  set R_S := (pResidual p ↥S).map S.subtype with hRS
  set R_G := pResidual p G with hRG
  haveI : R_S.Normal := pResidual_map_subtype_normal
  have hRS_le_S : R_S ≤ S := Subgroup.map_subtype_le _
  have hRSsub : R_S.subgroupOf S = pResidual p ↥S :=
    Subgroup.comap_map_eq_self_of_injective S.subtype_injective _
  -- `G/S` は p-群 (`G = SP`)
  have hGS : IsPGroup p (G ⧸ S) := by
    have hPmap : P.map (QuotientGroup.mk' S) = ⊤ := by
      apply Subgroup.comap_injective (QuotientGroup.mk'_surjective S)
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top, sup_comm, hSP]
    have h := hP.map (QuotientGroup.mk' S)
    rw [hPmap] at h
    exact h.of_equiv Subgroup.topEquiv
  apply le_antisymm
  · -- `O^p(G) ≤ R_S`: `G/R_S` は p-群
    apply pResidual_le_of_isPGroup_quotient
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := p)).mp (isPGroup_quotient_pResidual (G := ↥S))
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := p)).mp hGS
    refine IsPGroup.of_card (n := a + b) ?_
    have h1 : R_S.relIndex S = p ^ a :=
      calc R_S.relIndex S = (R_S.subgroupOf S).index := rfl
        _ = Nat.card (↥S ⧸ R_S.subgroupOf S) := (R_S.subgroupOf S).index_eq_card
        _ = Nat.card (↥S ⧸ pResidual p ↥S) := by rw [hRSsub]
        _ = p ^ a := ha
    have h2 : S.index = p ^ b := by rw [S.index_eq_card]; exact hb
    have hab : Nat.card (G ⧸ R_S) = p ^ a * p ^ b := by
      rw [← Subgroup.index_eq_card, ← Subgroup.relIndex_mul_index hRS_le_S, h1, h2]
    rw [hab, ← pow_add]
  · -- `R_S ≤ O^p(G)`
    haveI : (R_G ⊓ S).Normal := inferInstance
    have hkey : pResidual p ↥S ≤ (R_G ⊓ S).subgroupOf S := by
      apply pResidual_le_of_isPGroup_quotient
      have hkerf : ((QuotientGroup.mk' R_G).comp S.subtype).ker = (R_G ⊓ S).subgroupOf S := by
        rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
        exact (Subgroup.inf_subgroupOf_right R_G S).symm
      have e : (↥S ⧸ (R_G ⊓ S).subgroupOf S)
          ≃* ((QuotientGroup.mk' R_G).comp S.subtype).range :=
        (QuotientGroup.quotientMulEquivOfEq hkerf.symm).trans
          (QuotientGroup.quotientKerEquivRange _)
      exact ((isPGroup_quotient_pResidual (G := G)).to_subgroup _).of_equiv e.symm
    calc R_S = (pResidual p ↥S).map S.subtype := hRS
      _ ≤ ((R_G ⊓ S).subgroupOf S).map S.subtype := Subgroup.map_mono hkey
      _ = (R_G ⊓ S) ⊓ S := Subgroup.subgroupOf_map_subtype _ _
      _ ≤ R_G := inf_le_left.trans inf_le_left

end OddOrder.Isaacs.Ch09
