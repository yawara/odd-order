/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.IsSubnormal
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Order.Minimal

/-!
# The `p`-residual `O^p(G)` (Isaacs Ch. 9 §9C 準備)

`O^p(G)` = **`p`-residual** = 商が `p`-群になる最小の正規部分群 (書籍 p. 287 の
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

/-- 同型 `e : G ≃* K` による `comap` は `p`-群商を保つ: `K/N` が `p`-群なら
`G/(comap e N)` も `p`-群 (`e` が誘導する同型 `G/(comap e N) ≃ K/N`). -/
theorem isPGroup_quotient_comap {K : Type*} [Group K] (e : G ≃* K) {N : Subgroup K} [N.Normal]
    (hN : IsPGroup p (K ⧸ N)) :
    IsPGroup p (G ⧸ Subgroup.comap (e : G →* K) N) := by
  haveI : (Subgroup.comap (e : G →* K) N).Normal := ‹N.Normal›.comap _
  set f := (QuotientGroup.mk' N).comp (e : G →* K) with hf
  have hsurj : Function.Surjective f :=
    (QuotientGroup.mk'_surjective N).comp e.surjective
  have hker : f.ker = Subgroup.comap (e : G →* K) N := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have equiv : (G ⧸ Subgroup.comap (e : G →* K) N) ≃* (K ⧸ N) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  exact hN.of_equiv equiv.symm

theorem comap_mem_pQuotientNormals {K : Type*} [Group K] (e : G ≃* K) {N : Subgroup K}
    (hN : N ∈ pQuotientNormals p K) :
    Subgroup.comap (e : G →* K) N ∈ pQuotientNormals p G := by
  haveI := normal_of_mem_pQuotientNormals hN
  exact ⟨‹N.Normal›.comap _,
    isPGroup_quotient_comap e (isPGroup_quotient_of_mem_pQuotientNormals hN)⟩

/-- `comap e (comap e.symm A) = A` (`e` は同型). -/
private theorem comap_comap_symm {K : Type*} [Group K] (e : G ≃* K) (A : Subgroup G) :
    Subgroup.comap (e : G →* K) (Subgroup.comap (e.symm : K →* G) A) = A := by
  rw [Subgroup.comap_comap]
  have : (e.symm : K →* G).comp (e : G →* K) = MonoidHom.id G := by ext x; simp
  rw [this, Subgroup.comap_id]

/-- 片側包含 (両向きに適用して `comap_pResidual_mulEquiv` を得る). -/
private theorem comap_pResidual_le {K : Type*} [Group K] (e : G ≃* K) :
    Subgroup.comap (e : G →* K) (pResidual p K) ≤ pResidual p G :=
  le_sInf fun M hM =>
    (Subgroup.comap_mono (sInf_le (comap_mem_pQuotientNormals e.symm hM))).trans_eq
      (comap_comap_symm e M)

/-- `O^p` は群同型と可換 (comap 版): `comap e (O^p(K)) = O^p(G)`. -/
theorem comap_pResidual_mulEquiv {K : Type*} [Group K] (e : G ≃* K) :
    Subgroup.comap (e : G →* K) (pResidual p K) = pResidual p G := by
  refine le_antisymm (comap_pResidual_le e) ?_
  calc pResidual p G
      = Subgroup.comap (e : G →* K) (Subgroup.comap (e.symm : K →* G) (pResidual p G)) :=
        (comap_comap_symm e _).symm
    _ ≤ Subgroup.comap (e : G →* K) (pResidual p K) :=
        Subgroup.comap_mono (comap_pResidual_le e.symm)

/-- `O^p` は群同型と可換 (map 版): `(O^p(G)).map e = O^p(K)`. -/
theorem map_pResidual_mulEquiv {K : Type*} [Group K] (e : G ≃* K) :
    (pResidual p G).map (e : G →* K) = pResidual p K := by
  rw [← comap_pResidual_mulEquiv e, Subgroup.map_comap_eq_self_of_surjective e.surjective]

instance pResidual.characteristic : (pResidual p G).Characteristic :=
  Subgroup.characteristic_iff_comap_eq.mpr fun ψ => comap_pResidual_mulEquiv ψ

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

/-- **Isaacs Corollary 9.27 の normal 特殊形** (p. 287): `S ◁ G` ならば `O^p(S) ◁ G`
(ambient で `(O^p ↥S).map S.subtype`), 特に任意の `P ≤ G` が `O^p(S)` を正規化する.

書籍の 9.27 は `S ◁◁ G` (subnormal) 仮説で, 9.26 (`O^p(SP) = O^p(S)`) を経由する.
`S ◁ G` の場合は `O^p(S)` が `S` に characteristic ゆえ直接 `G`-normal が出る (この形では
`P` の p-群性も不要). 書籍どおりの一般 subnormal 版は
`le_normalizer_pResidualOf_of_isSubnormal`. -/
theorem pResidual_map_subtype_normal {S : Subgroup G} [S.Normal] :
    ((pResidual p ↥S).map S.subtype).Normal :=
  map_subtype_normal_of_characteristic _

/-- **Isaacs Lemma 9.26 の normal 特殊形** (p. 287): `G = SP`, `S ◁ G`, `P ◁ G` p-群 ⇒
`O^p(G) = O^p(S)` (ambient: `pResidual p G = (pResidual p ↥S).map S.subtype`).
`O^p` 版の Lemma 9.15. 書籍どおりの一般 subnormal 版 (`S ◁◁ G`) は
`pResidual_eq_pResidualOf_of_isSubnormal` — その証明が本補題を base case として使う.

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

section /- 9C: ambient 値の `O^p(S)` -/

/-- **ambient 値の `p`-residual** `O^p(S)`: 部分群 `S ≤ G` に対し `Subgroup G` の元として
`O^p(S)` を与える (`nilpotentResidual` と同じ ambient 設計). 共役同変性
(`map_pResidualOf`) が使えるので `O^p(S^g) = O^p(S)^g` 等が扱える. -/
def pResidualOf (p : ℕ) (S : Subgroup G) : Subgroup G :=
  (pResidual p ↥S).map S.subtype

theorem pResidualOf_le (p : ℕ) (S : Subgroup G) : pResidualOf p S ≤ S :=
  Subgroup.map_subtype_le _

theorem subgroupOf_pResidualOf (p : ℕ) (S : Subgroup G) :
    (pResidualOf p S).subgroupOf S = pResidual p ↥S :=
  Subgroup.comap_map_eq_self_of_injective S.subtype_injective _

/-- `O^p(⊤) = O^p(G)` (ambient と型レベルの整合). -/
theorem pResidualOf_top : pResidualOf p (⊤ : Subgroup G) = pResidual p G := by
  rw [pResidualOf, ← map_pResidual_mulEquiv (Subgroup.topEquiv (G := G))]
  rfl

/-- **同変性**: `(O^p(S)).map e = O^p(S.map e)` (`e : G ≃* K` 同型). -/
theorem map_pResidualOf {K : Type*} [Group K] (e : G ≃* K) (S : Subgroup G) :
    (pResidualOf p S).map (e : G →* K) = pResidualOf p (S.map (e : G →* K)) := by
  rw [pResidualOf, pResidualOf, Subgroup.map_map,
    ← map_pResidual_mulEquiv (e.subgroupMap S), Subgroup.map_map]
  -- 残るのは `(S.map e).subtype ∘ (e.subgroupMap S) = e ∘ S.subtype`.
  congr 1

/-- `N_G(S) ≤ N_G(O^p(S))`: `S` を固定する共役は `O^p(S)` も固定する. -/
theorem normalizer_le_normalizer_pResidualOf (p : ℕ) (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (pResidualOf p S : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  rw [map_pResidualOf, hg]

/-- `S ◁ G` ⇒ `O^p(S) ◁ G` (`O^p(S)` は `S` に characteristic). -/
instance pResidualOf.normal {S : Subgroup G} [S.Normal] : (pResidualOf p S).Normal :=
  pResidual_map_subtype_normal

theorem pResidualOf_eq_bot_iff_isPGroup [Finite G] [Fact p.Prime] (S : Subgroup G) :
    pResidualOf p S = ⊥ ↔ IsPGroup p ↥S := by
  rw [pResidualOf, Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective,
    pResidual_eq_bot_iff_isPGroup]

/-- `↥H` で正規な `A` を ambient に落とした `A.map H.subtype` は `H` に正規化される. -/
theorem le_normalizer_map_subtype_of_normal {H : Subgroup G} {A : Subgroup ↥H} (hA : A.Normal) :
    H ≤ Subgroup.normalizer ((A.map H.subtype : Subgroup G) : Set G) := by
  have heq : (A.map H.subtype).subgroupOf H = A :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective A
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le A), heq]
  exact hA

/-- **正規化群は同型と可換**: `N_G(A).map e = N_K(A.map e)`.
特に `e = MulAut.conj g` で `N_G(A^g) = N_G(A)^g` (Thm 9.24 Case 2 の
`N_G(X^k) = H^k` に使う). mathlib に無いので与える. -/
theorem map_normalizer_mulEquiv {K : Type*} [Group K] (e : G ≃* K) (A : Subgroup G) :
    (Subgroup.normalizer (A : Set G)).map (e : G →* K)
      = Subgroup.normalizer ((A.map (e : G →* K) : Subgroup K) : Set K) := by
  have hmem : ∀ x : G, (e x ∈ Subgroup.normalizer ((A.map (e : G →* K) : Subgroup K) : Set K))
      ↔ x ∈ Subgroup.normalizer (A : Set G) := by
    intro x
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    have hconj : ∀ n : G, e x * e n * (e x)⁻¹ = e (x * n * x⁻¹) := by
      intro n; simp [map_mul, map_inv]
    have hmap : ∀ n : G, (e n ∈ (A.map (e : G →* K) : Subgroup K)) ↔ n ∈ A := by
      intro n
      constructor
      · rintro ⟨a, ha, hea⟩
        have han : a = n := e.injective (by simpa using hea)
        rwa [han] at ha
      · intro hn
        exact ⟨n, hn, rfl⟩
    constructor
    · intro h n
      have h2 := h (e n)
      rw [hconj n, hmap n, hmap (x * n * x⁻¹)] at h2
      exact h2
    · intro h m
      obtain ⟨n, rfl⟩ := e.surjective m
      rw [hconj n, hmap n, hmap (x * n * x⁻¹)]
      exact h n
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mpr hx
  · intro hy
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨x, (hmem x).mp hy, rfl⟩

/-- `↥R` 内で計算した `O^p(S.subgroupOf R)` を落とすと ambient の `O^p(S)` (`S ≤ R`).
`map_subtype_nilpotentResidual_subgroupOf` の `O^p` 版. -/
theorem map_subtype_pResidualOf_subgroupOf {S R : Subgroup G} (h : S ≤ R) :
    (pResidualOf p (S.subgroupOf R)).map R.subtype = pResidualOf p S := by
  have hhom : R.subtype.comp (S.subgroupOf R).subtype
      = S.subtype.comp ((Subgroup.subgroupOfEquivOfLe h : _ ≃* ↥S) : _ →* ↥S) := by
    ext x; rfl
  rw [pResidualOf, Subgroup.map_map, hhom, ← Subgroup.map_map,
    map_pResidual_mulEquiv (Subgroup.subgroupOfEquivOfLe h)]
  rfl

end

section /- 9C: Lemma 9.26 / Corollary 9.27 (pp. 287-288) — normal 特殊形と書籍どおりの subnormal 版 -/

open scoped Pointwise

/-- 正規化条件を `↥H` へ落とす: `A ≤ N_G(B)` ⇒ `A.subgroupOf H ≤ N_{↥H}(B.subgroupOf H)`. -/
theorem subgroupOf_le_normalizer_subgroupOf {A B H : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) :
    A.subgroupOf H ≤ Subgroup.normalizer ((B.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hxN := Subgroup.mem_normalizer_iff.mp (h (Subgroup.mem_subgroupOf.mp hx)) (y : G)
  simpa [Subgroup.mem_subgroupOf] using hxN

/-- 正規化条件を ambient へ持ち上げる: `A' ≤ N_{↥H}(B')` ⇒
`A'.map H.subtype ≤ N_G(B'.map H.subtype)`. -/
theorem map_subtype_le_normalizer_map_subtype {H : Subgroup G} {A' B' : Subgroup ↥H}
    (h : A' ≤ Subgroup.normalizer (B' : Set ↥H)) :
    A'.map H.subtype ≤ Subgroup.normalizer ((B'.map H.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hconj := Subgroup.mem_normalizer_iff.mp (h ha)
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨a * b * a⁻¹, (hconj b).mp hb, by simp⟩
  · rintro ⟨c, hc, hceq⟩
    refine ⟨a⁻¹ * c * a, (hconj (a⁻¹ * c * a)).mpr (by simpa [mul_assoc] using hc), ?_⟩
    have hc' : (a : G) * y * (a : G)⁻¹ = (c : G) := hceq.symm
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hc']
    group

/-- **Isaacs Lemma 9.26 (ambient 版)**: `R = S ⊔ P` で `S`, `P` がともに `R` に normal,
`P` が `p`-群ならば `O^p(R) = O^p(S)`.

型レベル版 `pResidual_eq_map_subtype_of_sup_isPGroup` を `↥R` に適用し
`map_subtype_pResidualOf_subgroupOf` で ambient に戻しただけ. -/
theorem pResidualOf_sup_eq [Finite G] [Fact p.Prime] {S P R : Subgroup G}
    (hSR : S ≤ R) (hPR : P ≤ R)
    (hSn : R ≤ Subgroup.normalizer (S : Set G))
    (hPn : R ≤ Subgroup.normalizer (P : Set G))
    (hP : IsPGroup p ↥P) (hsup : S ⊔ P = R) :
    pResidualOf p R = pResidualOf p S := by
  haveI : (S.subgroupOf R).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSR).mpr hSn
  haveI : (P.subgroupOf R).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPR).mpr hPn
  have hP' : IsPGroup p ↥(P.subgroupOf R) :=
    hP.of_injective (Subgroup.subgroupOfEquivOfLe hPR).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPR).injective
  have hsup' : S.subgroupOf R ⊔ P.subgroupOf R = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hSR hPR, hsup, Subgroup.subgroupOf_self]
  have key := pResidual_eq_map_subtype_of_sup_isPGroup (G := ↥R) hP' hsup'
  calc pResidualOf p R = (pResidual p ↥R).map R.subtype := rfl
    _ = (pResidualOf p (S.subgroupOf R)).map R.subtype := by rw [key]; rfl
    _ = pResidualOf p S := map_subtype_pResidualOf_subgroupOf hSR

/-- **Isaacs Lemma 9.26** (p. 287, 書籍どおりの subnormal 版): `G = SP` で `S ◁◁ G` かつ
`P ◁ G` が `p`-群ならば `O^p(G) = O^p(S)`.

書籍は `|G|` の帰納で `S ≤ M ◁ G`, `M < G` を選ぶが, `Subgroup.IsSubnormal` が inductive
predicate なのでその構造帰納で置き換える (書籍の `M` = 帰納の `K`):
* `top` 段 (`S = ⊤`): 自明 (`pResidualOf_top`).
* `step` 段 (`S ◁ K`, `K ◁◁ G`): `S ≤ K` から `K ⊔ P = ⊤` なので帰納法の仮定が
  `O^p(G) = O^p(K)` を与える. 一方 `P ◁ G` ゆえ `S ⊔ P = S·P` (集合の積) で Dedekind 則が
  `K = S(K ⊓ P)` を与え, `K ⊓ P ◁ K` は `p`-群だから normal 版 `pResidualOf_sup_eq` が
  `O^p(K) = O^p(S)` を与える.

`P` を全称量化した形で述べるのは, 構造帰納の motive が `S` のみに依存する必要があるため
(`step` 段では同じ `P` を `K` に対して使う). -/
theorem pResidual_eq_pResidualOf_of_isSubnormal [Finite G] [Fact p.Prime]
    {S : Subgroup G} (hS : S.IsSubnormal) :
    ∀ P : Subgroup G, P.Normal → IsPGroup p ↥P → S ⊔ P = ⊤ →
      pResidual p G = pResidualOf p S := by
  induction hS with
  | top => intro _ _ _ _; exact pResidualOf_top.symm
  | step S K hle _ hSnorm ih =>
    intro P hPnorm hP hsup
    haveI := hPnorm
    have hKP : K ⊔ P = ⊤ := by
      rw [eq_top_iff, ← hsup]; exact sup_le_sup_right hle P
    have hSn : K ≤ Subgroup.normalizer (S : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hSnorm
    have hKPn : K ≤ Subgroup.normalizer ((K ⊓ P : Subgroup G) : Set G) := by
      rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : K ⊓ P ≤ K),
        Subgroup.inf_subgroupOf_left]
      exact hPnorm.subgroupOf K
    -- Dedekind (modular) 則: `P ◁ G` ゆえ `S ⊔ P = S·P` (集合の積) なので要素計算でよい
    -- (`Subgroup G` の束は一般には modular でない — mathlib の instance は CommGroup 限定).
    have hded : S ⊔ (K ⊓ P) = K := by
      refine le_antisymm (sup_le hle inf_le_left) fun k hk => ?_
      have hkmem : k ∈ ((S : Set G) * (P : Set G)) := by
        have h : k ∈ ((S ⊔ P : Subgroup G) : Set G) := by
          rw [SetLike.mem_coe, hsup]; exact Subgroup.mem_top k
        rwa [Subgroup.mul_normal S P] at h
      obtain ⟨s, hs, x, hx, rfl⟩ := hkmem
      have hxK : x ∈ K := by
        have h := K.mul_mem (K.inv_mem (hle hs)) hk
        simpa using h
      exact Subgroup.mul_mem_sup hs ⟨hxK, hx⟩
    have hKPp : IsPGroup p ↥(K ⊓ P) :=
      hP.of_injective (Subgroup.inclusion (inf_le_right : K ⊓ P ≤ P))
        (Subgroup.inclusion_injective _)
    rw [ih P hPnorm hP hKP]
    exact pResidualOf_sup_eq hle inf_le_left hSn hKPn hKPp hded

/-- **Isaacs Lemma 9.26 (ambient 版, subnormal)**: `R = S ⊔ P` で `S` が `↥R` の中で
subnormal, `P` が `R` に正規な `p`-群ならば `O^p(R) = O^p(S)`.

型レベル版を `↥R` に適用し `map_subtype_pResidualOf_subgroupOf` で ambient に戻しただけ
(normal 版 `pResidualOf_sup_eq` と同じ持ち上げ方). -/
theorem pResidualOf_sup_eq_of_isSubnormal [Finite G] [Fact p.Prime] {S P R : Subgroup G}
    (hSR : S ≤ R) (hPR : P ≤ R) (hS : (S.subgroupOf R).IsSubnormal)
    (hPn : R ≤ Subgroup.normalizer (P : Set G))
    (hP : IsPGroup p ↥P) (hsup : S ⊔ P = R) :
    pResidualOf p R = pResidualOf p S := by
  haveI : (P.subgroupOf R).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPR).mpr hPn
  have hP' : IsPGroup p ↥(P.subgroupOf R) :=
    hP.of_injective (Subgroup.subgroupOfEquivOfLe hPR).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPR).injective
  have hsup' : S.subgroupOf R ⊔ P.subgroupOf R = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hSR hPR, hsup, Subgroup.subgroupOf_self]
  have key := pResidual_eq_pResidualOf_of_isSubnormal (G := ↥R) hS (P.subgroupOf R)
    inferInstance hP' hsup'
  calc pResidualOf p R = (pResidual p ↥R).map R.subtype := rfl
    _ = (pResidualOf p (S.subgroupOf R)).map R.subtype := by rw [key]
    _ = pResidualOf p S := map_subtype_pResidualOf_subgroupOf hSR

/-- **Isaacs Corollary 9.27** (p. 287, 書籍どおりの subnormal 版): `S ◁◁ G` かつ `P ◁ G` が
`p`-群ならば `P` は `O^p(S)` を正規化する.

書籍の証明そのまま: Lemma 9.26 を `SP` の中で使うと `O^p(SP) = O^p(S)` で, 左辺は `SP` に
characteristic ゆえ `P ≤ SP` に正規化される. -/
theorem le_normalizer_pResidualOf_of_isSubnormal [Finite G] [Fact p.Prime]
    {S P : Subgroup G} (hS : S.IsSubnormal) [P.Normal] (hP : IsPGroup p ↥P) :
    P ≤ Subgroup.normalizer (pResidualOf p S : Set G) := by
  have hPn : S ⊔ P ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have key : pResidualOf p (S ⊔ P) = pResidualOf p S :=
    pResidualOf_sup_eq_of_isSubnormal le_sup_left le_sup_right hS.subgroupOf hPn hP rfl
  calc P ≤ S ⊔ P := le_sup_right
    _ ≤ Subgroup.normalizer ((S ⊔ P : Subgroup G) : Set G) := Subgroup.le_normalizer
    _ ≤ Subgroup.normalizer (pResidualOf p (S ⊔ P) : Set G) :=
        normalizer_le_normalizer_pResidualOf p _
    _ = Subgroup.normalizer (pResidualOf p S : Set G) := by rw [key]

end

/-- **Isaacs Corollary 9.27 の相対形**: ambient 群を部分群 `H` に取り替えた形.
`S ≤ H` が `↥H` の中で subnormal, `P ≤ H` が `H` に正規な `p`-群ならば
`P ≤ N_G(O^p(S))`.

Thm 9.24 の Case 2 はこの形で使う (`H` が ambient; `S = V`, `P = O_p(H)` はいずれも `G` に
は normal でない). 絶対版を `↥H` に適用し `map_subtype_le_normalizer_map_subtype` で
ambient に戻す. -/
theorem le_normalizer_pResidualOf_of_isSubnormal_rel [Finite G] [Fact p.Prime]
    {H S P : Subgroup G} (hSH : S ≤ H) (hPH : P ≤ H)
    (hS : (S.subgroupOf H).IsSubnormal)
    (hPn : H ≤ Subgroup.normalizer (P : Set G)) (hP : IsPGroup p ↥P) :
    P ≤ Subgroup.normalizer (pResidualOf p S : Set G) := by
  haveI : (P.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr hPn
  have hPpg : IsPGroup p ↥(P.subgroupOf H) :=
    hP.of_injective (Subgroup.subgroupOfEquivOfLe hPH).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPH).injective
  have key := le_normalizer_pResidualOf_of_isSubnormal (G := ↥H) hS hPpg
  have hlift := map_subtype_le_normalizer_map_subtype key
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPH,
    map_subtype_pResidualOf_subgroupOf hSH] at hlift

/-- **Corollary 9.27 の defect 2 相対形** (呼び出し側の便宜): `S ◁ T ◁ H` (いずれも `H` の
中での話) と `P ◁ H` が `p`-群という形から `P ≤ N_G(O^p(S))` を得る.

`(S.subgroupOf H).IsSubnormal` を長さ 2 の鎖から組み立てて
`le_normalizer_pResidualOf_of_isSubnormal_rel` に渡すだけ. Thm 9.24 の Case 2 は
Step A (`V ◁ M ◁ H`) と Step D (`U^k ◁ N ◁ D`) の 2 箇所でこの形を使う. -/
theorem le_normalizer_pResidualOf_of_subnormal_two_rel [Finite G] [Fact p.Prime]
    {H S T P : Subgroup G} (hST : S ≤ T) (hTH : T ≤ H) (hPH : P ≤ H)
    (hTn : H ≤ Subgroup.normalizer (T : Set G))
    (hPn : H ≤ Subgroup.normalizer (P : Set G))
    (hSn : T ≤ Subgroup.normalizer (S : Set G)) (hP : IsPGroup p ↥P) :
    P ≤ Subgroup.normalizer (pResidualOf p S : Set G) := by
  haveI : (T.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hTH).mpr hTn
  have hSTH : S.subgroupOf H ≤ T.subgroupOf H := Subgroup.comap_mono hST
  refine le_normalizer_pResidualOf_of_isSubnormal_rel (hST.trans hTH) hPH ?_ hPn hP
  exact Subgroup.IsSubnormal.step _ _ hSTH ‹(T.subgroupOf H).Normal›.isSubnormal
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hSTH).mpr
      (subgroupOf_le_normalizer_subgroupOf hSn))

end OddOrder.Isaacs.Ch09
