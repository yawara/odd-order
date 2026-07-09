/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable
import OddOrder.GroupTheory.ElementaryAbelian
import OddOrder.Mathlib.Subgroup
import OddOrder.Mathlib.SchurZassenhausConj
import OddOrder.Isaacs.Ch02_Subnormality.Main
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh02

/-!
# OddOrder.Isaacs.Ch03 — Split Extensions

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 3
"Split Extensions" (pp. 65-112) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 3A | 半直積構成 + Aut(G) 位数評価 | 3.1 – 3.4 | ✅ 3.1-3.4 |
| 3B | Schur-Zassenhaus + 可解群基本 | 3.5 – 3.12 | ✅ 3.11 まで |
| 3C | Hall 部分群 + 可解性判定 | 3.13 – 3.17 | ✅ Hall-E/C + 3.16 |
| 3D | π-separable + Hall-Higman 1.2.3 | 3.18 – 3.22 | ✅ 3.18-3.22 |
| 3E | Coprime action | 3.23 – 3.34 | ✅ Tier 1; Tier 2 は Ch.4 待ち |
| 3F | 巡回商 lift | 3.35 – 3.36 | ✅ 3.35-3.36 |

## 方針

mathlib `SemidirectProduct` (Chris Hughes), `SchurZassenhaus`, `Complement`,
`IsSolvable` を全面利用. Thm 3.1 (uniqueness), 3.2 (existence) は mathlib の
construction を Isaacs 流に再述するラッパー.

Thm 3.3 Horosevskii は Ch.2 Thm 2.20 Lucchini に依存 (PDF p.71 で証明確認済).
Thm 3.4 は Ch.1 Thm 1.37 Brodkey に依存 (Ch.1 §1F 未着手).

ノート: [notes/isaacs/ch03_split.md](../../notes/isaacs/ch03_split.md)
-/

namespace OddOrder.Isaacs.Ch03

open SemidirectProduct
open scoped Pointwise

section /- 3A: Semidirect product + Aut bounds (pp. 65-74) -/

variable {N H : Type*} [Group N] [Group H] (φ : H →* MulAut N)

/-- **Isaacs Thm 3.2 part 1** (半直積の正規部分群).
作用 `φ : H →* MulAut N` に対し、半直積 `N ⋊[φ] H` 内で `inl(N)` は正規部分群.

mathlib `SemidirectProduct.range_inl_eq_ker_rightHom` で `inl.range = rightHom.ker` と
書け, 核は正規. -/
instance inl_range_normal : ((inl : N →* N ⋊[φ] H)).range.Normal := by
  rw [range_inl_eq_ker_rightHom]
  infer_instance

/-- **Isaacs Thm 3.2 part 2** (半直積の補集合).
`inl(N)` と `inr(H)` は `N ⋊[φ] H` 内で互いに補集合 (`IsComplement'`).

各元 `g : N ⋊[φ] H` は `g = inl g.left * inr g.right` と一意に書ける
(`SemidirectProduct.inl_left_mul_inr_right`)。 -/
theorem inl_range_isComplement_inr_range :
    ((inl : N →* N ⋊[φ] H).range).IsComplement' ((inr : H →* N ⋊[φ] H).range) := by
  rw [Subgroup.isComplement'_def, Subgroup.isComplement_iff_bijective]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨_, n₁, rfl⟩, ⟨_, h₁, rfl⟩⟩ ⟨⟨_, n₂, rfl⟩, ⟨_, h₂, rfl⟩⟩ heq
    -- heq : inl n₁ * inr h₁ = inl n₂ * inr h₂ (in N ⋊[φ] H)
    have hL : (inl n₁ * inr h₁ : N ⋊[φ] H).left  = (inl n₂ * inr h₂ : N ⋊[φ] H).left  :=
      congrArg left heq
    have hR : (inl n₁ * inr h₁ : N ⋊[φ] H).right = (inl n₂ * inr h₂ : N ⋊[φ] H).right :=
      congrArg right heq
    simp only [mul_left, mul_right, left_inl, right_inl, left_inr, right_inr,
               map_one, mul_one, one_mul] at hL hR
    subst hL; subst hR; rfl
  · intro g
    exact ⟨(⟨inl g.left, g.left, rfl⟩, ⟨inr g.right, g.right, rfl⟩), inl_left_mul_inr_right g⟩

/-- **Isaacs Thm 3.2 part 3** (共役 = 作用).
半直積 `N ⋊[φ] H` 内では `inr h` による `inl n` の共役が元の作用 `φ h n` を実現する.

mathlib `inl_aut` のラッパー (Isaacs 流の方向に向きを揃える). -/
theorem inr_conj_inl_eq (h : H) (n : N) :
    (inr h * inl n * inr h⁻¹ : N ⋊[φ] H) = inl (φ h n) :=
  (inl_aut h n).symm

/-- **Isaacs Thm 3.1** (uniqueness of split extension up to unique iso).
`G` の正規部分群 `N` が `K` で補集合化されているとき, `N` への `K` 共役作用を介した
半直積 `N ⋊ K` は `G` と同型.

mathlib `SemidirectProduct.mulEquivSubgroup` の Isaacs 流再述 (Lemma 3.1 を
`G₀` の具体的構成 = semidirect product に固定した形). -/
noncomputable def mulEquivSubgroupOfComplement {G : Type*} [Group G]
    {N K : Subgroup G} [N.Normal] (hCompl : N.IsComplement' K) :
    N ⋊[(N.normalizerMonoidHom).comp
      (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top))] K ≃* G :=
  SemidirectProduct.mulEquivSubgroup hCompl

/-- **Isaacs Thm 3.3 Horosevskii**: 有限非自明群 `G` で `σ ∈ Aut(G)` ならば `o(σ) < |G|`.

Isaacs p.71 の証明: `A = ⟨σ⟩ ≤ Aut(G)` cyclic, `Γ = G ⋊ A` semidirect product. `inr A ≤ Γ` は
`A` の同型像で proper (Nontrivial G). Lucchini (Thm 2.20) を `inr A` に適用:
`|inr A : K| < |Γ : inr A| = |G|`, where `K = core_Γ(inr A)`.
`K ⊆ inr A`, `inr A ⊓ inl(G) = ⊥` (補集合) ⇒ `K ⊓ inl(G) = ⊥`. `K, inl(G) ⊴ Γ` で Lemma 2.7
適用 ⇒ K と inl(G) 可換. K ⊆ C_Γ(inl(G)) ⊓ inr A = ⊥ (非自明自己同型は非自明作用). 故に
K = ⊥, `|inr A : K| = |inr A| = o(σ)`. 結論 `o(σ) < |G|`.

実装 TODO: Lucchini axiom + 半直積セットアップが揃った後に別 commit で本証明を fill in.
鍵となる補題:
- `SemidirectProduct.card`, `SemidirectProduct.equivProd` (Finite + 濃度)
- `inl_range_isComplement_inr_range` (本ファイル §3A): inl(G), inr(A) 補集合
- `inr_conj_inl_eq` (本ファイル §3A): 半直積内の共役 = 作用
- `Subgroup.commute_of_normal_of_disjoint` (mathlib, Lemma 2.7): K ⊴, inl(G) ⊴, K∩inl(G)=⊥ ⇒ 可換
- `OddOrder.Isaacs.Ch04.lucchini_index_normalCore_lt_index` (Ch.4 dir owner; K = ⊥ axiom 残)
- `MonoidHom.map_zpowers`, `Nat.card_zpowers`, `Subgroup.index_mul_card`. -/
theorem horosevskii_aut_order_lt {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (σ : MulAut G) :
    orderOf σ < Nat.card G := by
  -- Setup the semidirect product Γ = G ⋊ ⟨σ⟩.
  let A : Subgroup (MulAut G) := Subgroup.zpowers σ
  let φ : ↥A →* MulAut G := A.subtype
  haveI : Finite ↥A := inferInstance
  haveI : Finite (G ⋊[φ] ↥A) :=
    Finite.of_equiv _ (SemidirectProduct.equivProd (φ := φ)).symm
  -- |↥A| = orderOf σ; |G ⋊[φ] ↥A| = |G| * orderOf σ.
  have hA_card : Nat.card ↥A = orderOf σ := Nat.card_zpowers σ
  have hΓ_card : Nat.card (G ⋊[φ] ↥A) = Nat.card G * orderOf σ := by
    rw [SemidirectProduct.card]; rw [hA_card]
  -- Aₛ := inr.range (the copy of A inside Γ); Gₛ := inl.range.
  set Aₛ : Subgroup (G ⋊[φ] ↥A) := (SemidirectProduct.inr : ↥A →* G ⋊[φ] ↥A).range with hAₛ
  set Gₛ : Subgroup (G ⋊[φ] ↥A) := (SemidirectProduct.inl : G →* G ⋊[φ] ↥A).range with hGₛ
  -- |Aₛ| = orderOf σ.
  have hAₛ_card : Nat.card Aₛ = orderOf σ := by
    have h := Nat.card_congr (Equiv.ofInjective _ SemidirectProduct.inr_injective
      (β := G ⋊[φ] ↥A))
    -- Nat.card ↥A = Nat.card ↥inr.range
    rw [hA_card] at h
    exact h.symm
  -- Aₛ.index = Nat.card G.
  have hAₛ_index : Aₛ.index = Nat.card G := by
    have h := Subgroup.index_mul_card Aₛ
    rw [hAₛ_card, hΓ_card] at h
    have : Aₛ.index * orderOf σ = Nat.card G * orderOf σ := h
    exact Nat.eq_of_mul_eq_mul_right (orderOf_pos σ) this
  -- Aₛ is generated by g₀ := inr ⟨σ, mem_zpowers σ⟩.
  let g₀ : G ⋊[φ] ↥A := SemidirectProduct.inr ⟨σ, Subgroup.mem_zpowers σ⟩
  have hAₛ_eq_zpowers : Aₛ = Subgroup.zpowers g₀ := by
    -- inr.range = inr (⊤ : Subgroup ↥A) = inr (zpowers ⟨σ, _⟩).
    -- This is `Subgroup.zpowers (inr ⟨σ, _⟩)`.
    have h_top_eq : (⊤ : Subgroup ↥A) =
        Subgroup.zpowers (⟨σ, Subgroup.mem_zpowers σ⟩ : ↥A) := by
      ext ⟨a, ha⟩
      simp only [Subgroup.mem_top, true_iff]
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      refine ⟨n, ?_⟩
      ext; simp
    change ((SemidirectProduct.inr : ↥A →* G ⋊[φ] ↥A).range) = Subgroup.zpowers g₀
    rw [MonoidHom.range_eq_map, h_top_eq, MonoidHom.map_zpowers]
  -- Aₛ is proper in Γ.
  have hAₛ_proper : Aₛ < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hT
    have hC : Nat.card Aₛ = Nat.card (G ⋊[φ] ↥A) := by
      conv_lhs => rw [hT]
      exact Subgroup.card_top
    rw [hAₛ_card, hΓ_card] at hC
    have hG2 : 2 ≤ Nat.card G := Finite.one_lt_card
    have hAo : 1 ≤ orderOf σ := orderOf_pos σ
    nlinarith
  -- Aₛ abelian.
  have hAₛ_ab : ∀ a ∈ Aₛ, ∀ b ∈ Aₛ, a * b = b * a := by
    intro a ha b hb
    rw [hAₛ_eq_zpowers] at ha hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← zpow_add, add_comm, zpow_add]
  -- Apply Lucchini.
  have hLucchini :=
    OddOrder.Isaacs.Ch04.lucchini_index_normalCore_lt_index hAₛ_proper hAₛ_ab
      ⟨g₀, hAₛ_eq_zpowers⟩
  -- Show Aₛ.normalCore = ⊥.
  -- Setup normality and disjointness.
  haveI : Aₛ.normalCore.Normal := Subgroup.normalCore_normal _
  haveI : Gₛ.Normal := by
    change ((SemidirectProduct.inl : G →* G ⋊[φ] ↥A).range).Normal
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hCompl :
      Gₛ.IsComplement' Aₛ := inl_range_isComplement_inr_range (φ := φ)
  have hDisj_AG : Disjoint Aₛ Gₛ := hCompl.disjoint.symm
  have hK_le : Aₛ.normalCore ≤ Aₛ := Subgroup.normalCore_le _
  have hDisj_KG : Disjoint Aₛ.normalCore Gₛ := Disjoint.mono_left hK_le hDisj_AG
  have hNC_bot : Aₛ.normalCore = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    -- k ∈ Aₛ.normalCore ⊆ Aₛ ⇒ k = inr a for some a.
    have hk_Aₛ : k ∈ Aₛ := hK_le hk
    obtain ⟨a, rfl⟩ := hk_Aₛ
    -- k centralizes Gₛ by Lemma 2.7.
    have hcent : ∀ g : G, Commute (SemidirectProduct.inr a : G ⋊[φ] ↥A)
        (SemidirectProduct.inl g) := by
      intro g
      have hg_in : (SemidirectProduct.inl g : G ⋊[φ] ↥A) ∈ Gₛ := ⟨g, rfl⟩
      exact Subgroup.commute_of_normal_of_disjoint
        Aₛ.normalCore Gₛ inferInstance inferInstance hDisj_KG
        (SemidirectProduct.inr a) (SemidirectProduct.inl g) hk hg_in
    -- inr a centralizes inl g for all g ⇒ φ a = identity automorphism ⇒ a = 1.
    have ha_act_trivial : ∀ g : G, (φ a) g = g := by
      intro g
      have h1 : (SemidirectProduct.inr a : G ⋊[φ] ↥A) *
                  (SemidirectProduct.inl g) * (SemidirectProduct.inr a⁻¹) =
                SemidirectProduct.inl ((φ a) g) := (SemidirectProduct.inl_aut a g).symm
      have h2 : (SemidirectProduct.inr a : G ⋊[φ] ↥A) *
                  (SemidirectProduct.inl g) * (SemidirectProduct.inr a⁻¹) =
                SemidirectProduct.inl g := by
        rw [(hcent g).eq, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
      have heq := h1.symm.trans h2
      exact SemidirectProduct.inl_injective heq
    have ha_eq_one : a = 1 := by
      have h_subtype_eq : (a : MulAut G) = (1 : MulAut G) := by
        ext g
        exact ha_act_trivial g
      exact Subtype.ext h_subtype_eq
    rw [ha_eq_one, map_one]
    exact Subgroup.mem_bot.mpr rfl
  -- Compute the index of bot in Aₛ and conclude.
  rw [hNC_bot] at hLucchini
  have h_bot_sub : (⊥ : Subgroup (G ⋊[φ] ↥A)).subgroupOf Aₛ = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot]
    exact disjoint_bot_left
  rw [h_bot_sub, Subgroup.index_bot] at hLucchini
  rw [hAₛ_card, hAₛ_index] at hLucchini
  exact hLucchini

/-- **Isaacs Cor 3.4**: `P` が `Aut(G)` の abelian `p`-部分群で `p ∤ |G|` ならば,
`P` は `G` に regular orbit を持つ. 形式化では「∃ g : G, P の stabilizer が trivial」
として書く (orbit が regular = stabilizer trivial, 標準的な同値).

Isaacs p.71-72 の証明:
1. `Γ := G ⋊ P` を natural action で構成, `inl(G), inr(P) ≤ Γ` と同一視.
2. `|Γ : inr P| = |G|` で `p ∤ |G|` ⇒ `inr P ∈ Syl_p(Γ)`.
3. `inr P` 内の元の `inl(G)` への conjugation = 元の作用. P 自己同型から成り恒等のみ自明
   作用 ⇒ `inr P ∩ C_Γ(inl G) = 1`.
4. `O_p(Γ) ⊆ inr P` (Sylow との交わり), `O_p(Γ) ∩ inl G = 1` (補集合性).
5. `inl G, O_p(Γ) ⊴ Γ` で disjoint ⇒ お互いに中心化 (Lemma 2.7). よって
   `O_p(Γ) ⊆ inr P ∩ C_Γ(inl G) = 1`.
6. `inr P` abelian + Brodkey (Thm 1.37) ⇒ `O_p(Γ) = S ⊓ T` for some Sylows S, T.
   Sylow 共役性で S = inr P, T = (inr P)^x の形に取れる. ∴ `inr P ⊓ (inr P)^x = 1`.
7. `x = inl n * inr u` (補集合分解), P abelian で `(inr P)^{inr u} = inr P`, よって
   `(inr P)^x = (inr P)^{inl n}`. `inr P ⊓ (inr P)^{inl n} = 1`.
8. `n` の P-stabilizer は `inr P ⊓ (inr P)^{inl n}` と同型 (作用 = conjugation), 故 trivial.
-/
theorem abelian_p_aut_regular_orbit {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : ¬ p ∣ Nat.card G) {P : Subgroup (MulAut G)}
    (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hPpgroup : IsPGroup p P) :
    ∃ g : G, ∀ φ : P, (φ : MulAut G) g = g → φ = 1 := by
  -- Setup the semidirect product Γ = G ⋊ ↥P (action via subtype P.subtype).
  let φP : ↥P →* MulAut G := P.subtype
  haveI : Finite ↥P := inferInstance
  haveI : Finite (G ⋊[φP] ↥P) :=
    Finite.of_equiv _ (SemidirectProduct.equivProd (φ := φP)).symm
  -- |G ⋊ ↥P| = |G| * |P|.
  have hΓ_card : Nat.card (G ⋊[φP] ↥P) = Nat.card G * Nat.card ↥P := SemidirectProduct.card
  set Pₛ : Subgroup (G ⋊[φP] ↥P) :=
    (SemidirectProduct.inr : ↥P →* G ⋊[φP] ↥P).range with hPₛ_def
  set Gₛ : Subgroup (G ⋊[φP] ↥P) :=
    (SemidirectProduct.inl : G →* G ⋊[φP] ↥P).range with hGₛ_def
  -- Cardinalities.
  have hPₛ_card : Nat.card Pₛ = Nat.card ↥P :=
    (Nat.card_congr (Equiv.ofInjective _ SemidirectProduct.inr_injective
      (β := G ⋊[φP] ↥P))).symm
  have hGₛ_card : Nat.card Gₛ = Nat.card G :=
    (Nat.card_congr (Equiv.ofInjective _ SemidirectProduct.inl_injective
      (β := G ⋊[φP] ↥P))).symm
  have hPₛ_index : Pₛ.index = Nat.card G := by
    have h := Subgroup.index_mul_card Pₛ
    rw [hPₛ_card, hΓ_card] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  -- Pₛ is a p-group via the iso ↥P ≃* Pₛ.
  have hPₛ_pgroup : IsPGroup p Pₛ :=
    hPpgroup.of_equiv
      (MonoidHom.ofInjective (f := (SemidirectProduct.inr : ↥P →* G ⋊[φP] ↥P))
        SemidirectProduct.inr_injective)
  -- ¬ p ∣ Pₛ.index from hp.
  have hp_Pₛ_idx : ¬ p ∣ Pₛ.index := by rw [hPₛ_index]; exact hp
  -- Promote Pₛ to a Sylow p-subgroup.
  let Pₛ_sylow : Sylow p (G ⋊[φP] ↥P) := hPₛ_pgroup.toSylow hp_Pₛ_idx
  have hPₛ_sylow_coe : (Pₛ_sylow : Subgroup (G ⋊[φP] ↥P)) = Pₛ :=
    IsPGroup.toSylow_coe _ _
  -- Gₛ is normal.
  haveI hGₛ_normal : Gₛ.Normal := by
    change ((SemidirectProduct.inl : G →* G ⋊[φP] ↥P).range).Normal
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  -- Complement: Gₛ and Pₛ are complements.
  have hCompl : Gₛ.IsComplement' Pₛ := inl_range_isComplement_inr_range (φ := φP)
  have hDisj_GP : Disjoint Gₛ Pₛ := hCompl.disjoint
  -- O_p(Γ) ≤ Pₛ.
  have hOp_le_Pₛ : OddOrder.Isaacs.Ch01.opCore p (G ⋊[φP] ↥P) ≤ Pₛ := by
    have h := OddOrder.Isaacs.Ch01.opCore_le Pₛ_sylow
    rwa [hPₛ_sylow_coe] at h
  -- O_p(Γ) ∩ Gₛ = ⊥.
  have hDisj_OpG : Disjoint (OddOrder.Isaacs.Ch01.opCore p (G ⋊[φP] ↥P)) Gₛ :=
    Disjoint.mono_left hOp_le_Pₛ hDisj_GP.symm
  -- O_p(Γ) is normal.
  haveI hOpNormal : (OddOrder.Isaacs.Ch01.opCore p (G ⋊[φP] ↥P)).Normal :=
    OddOrder.Isaacs.Ch01.opCore.normal p _
  -- O_p(Γ) = ⊥: elements centralize Gₛ (Lemma 2.7), but Pₛ acts faithfully.
  have hOp_bot : OddOrder.Isaacs.Ch01.opCore p (G ⋊[φP] ↥P) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := hOp_le_Pₛ hx
    -- inr a commutes with all inl g (Lemma 2.7 on O_p × Gₛ).
    have hcent : ∀ g : G, Commute (SemidirectProduct.inr a : G ⋊[φP] ↥P)
        (SemidirectProduct.inl g) := fun g =>
      Subgroup.commute_of_normal_of_disjoint
        (OddOrder.Isaacs.Ch01.opCore p (G ⋊[φP] ↥P)) Gₛ
        hOpNormal hGₛ_normal hDisj_OpG
        (SemidirectProduct.inr a) (SemidirectProduct.inl g)
        hx ⟨g, rfl⟩
    -- ⇒ φP a = identity ⇒ a = 1.
    have ha_act : ∀ g : G, (φP a) g = g := fun g => by
      have h1 : (SemidirectProduct.inr a : G ⋊[φP] ↥P) * SemidirectProduct.inl g *
                (SemidirectProduct.inr a⁻¹) = SemidirectProduct.inl ((φP a) g) :=
        (SemidirectProduct.inl_aut a g).symm
      have h2 : (SemidirectProduct.inr a : G ⋊[φP] ↥P) * SemidirectProduct.inl g *
                (SemidirectProduct.inr a⁻¹) = SemidirectProduct.inl g := by
        rw [(hcent g).eq, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
      exact SemidirectProduct.inl_injective (h1.symm.trans h2)
    have ha_one : a = 1 := Subtype.ext (MulEquiv.ext ha_act)
    simp [ha_one]
  -- Pₛ elements commute (since P is abelian and inr is a monoid hom).
  have hPₛ_ab : ∀ a ∈ Pₛ, ∀ b ∈ Pₛ, a * b = b * a := by
    rintro _ ⟨α, rfl⟩ _ ⟨β, rfl⟩
    have hcomm : α * β = β * α := Subtype.ext (hPab α α.2 β β.2)
    calc SemidirectProduct.inr α * SemidirectProduct.inr β
        = SemidirectProduct.inr (α * β) := (map_mul (SemidirectProduct.inr (φ := φP)) α β).symm
      _ = SemidirectProduct.inr (β * α) := by rw [hcomm]
      _ = SemidirectProduct.inr β * SemidirectProduct.inr α :=
            map_mul (SemidirectProduct.inr (φ := φP)) β α
  -- All Sylow p-subgroups of Γ are abelian (conjugate to Pₛ which is abelian).
  have hAllSyl_ab : ∀ Q : Sylow p (G ⋊[φP] ↥P),
      ∀ a ∈ (Q : Subgroup (G ⋊[φP] ↥P)),
      ∀ b ∈ (Q : Subgroup (G ⋊[φP] ↥P)), a * b = b * a := by
    intro Q a ha b hb
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G ⋊[φP] ↥P) Pₛ_sylow Q
    -- (Q : Subgroup) = MulAut.conj g • Pₛ.
    have hQ : (Q : Subgroup (G ⋊[φP] ↥P)) = MulAut.conj g • Pₛ := by
      rw [← hg, Sylow.coe_subgroup_smul, hPₛ_sylow_coe]
    rw [hQ, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at ha hb
    simp only [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv] at ha hb
    -- ha : g⁻¹ * a * g ∈ Pₛ; similarly for hb.
    have comm := hPₛ_ab _ ha _ hb
    -- Conjugate by g to recover a * b = b * a.
    have key : g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ =
               g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [comm]
    have h_lhs : g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ = a * b := by group
    have h_rhs : g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ = b * a := by group
    rw [h_lhs, h_rhs] at key
    exact key
  -- Apply Brodkey: ∃ S T : Sylow p Γ, ↑S ⊓ ↑T = O_p(Γ) = ⊥.
  obtain ⟨Syl1, Syl2, hST⟩ :=
    OddOrder.Isaacs.Ch01.exists_pair_inf_eq_opCore_of_abelian (G := G ⋊[φP] ↥P) (p := p)
      (fun Q x y hx hy => hAllSyl_ab Q x hx y hy)
  rw [hOp_bot] at hST
  -- Conjugate so one Sylow is Pₛ_sylow and the other is x • Pₛ_sylow (Sylow II twice).
  obtain ⟨g₁, hg₁⟩ := MulAction.exists_smul_eq (G ⋊[φP] ↥P) Syl1 Pₛ_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (G ⋊[φP] ↥P) Pₛ_sylow (g₁ • Syl2)
  -- Pₛ ⊓ (MulAut.conj x • Pₛ) = (MulAut.conj g₁ • ↑Syl1) ⊓ (MulAut.conj g₁ • ↑Syl2)
  --                          = MulAut.conj g₁ • (↑Syl1 ⊓ ↑Syl2) = MulAut.conj g₁ • ⊥ = ⊥.
  have h_Pₛ_as_conj_Syl1 : Pₛ = MulAut.conj g₁ • (Syl1 : Subgroup (G ⋊[φP] ↥P)) := by
    rw [← hPₛ_sylow_coe, ← hg₁, Sylow.coe_subgroup_smul]
  have h_conj_x_eq_conj_Syl2 : MulAut.conj x • Pₛ
      = MulAut.conj g₁ • (Syl2 : Subgroup (G ⋊[φP] ↥P)) := by
    rw [← hPₛ_sylow_coe, ← Sylow.coe_subgroup_smul, hx, Sylow.coe_subgroup_smul]
  have hDisj_x : Disjoint Pₛ (MulAut.conj x • Pₛ) := by
    rw [disjoint_iff, h_conj_x_eq_conj_Syl2, h_Pₛ_as_conj_Syl1, ← Subgroup.smul_inf, hST,
        Subgroup.smul_bot]
  -- Decompose x = inl n * inr u; inr u ∈ Pₛ ⇒ MulAut.conj (inr u) • Pₛ = Pₛ.
  -- So MulAut.conj x • Pₛ = MulAut.conj (inl n) • Pₛ.
  set n : G := x.left with hn_def
  set u : ↥P := x.right with hu_def
  have hx_decomp : x = SemidirectProduct.inl n * SemidirectProduct.inr u :=
    (SemidirectProduct.inl_left_mul_inr_right x).symm
  have hPₛ_conj_inr_u : MulAut.conj (SemidirectProduct.inr u : G ⋊[φP] ↥P) • Pₛ = Pₛ :=
    Subgroup.conj_smul_eq_self_of_mem ⟨u, rfl⟩
  have hDisj_n : Disjoint Pₛ
      (MulAut.conj (SemidirectProduct.inl n : G ⋊[φP] ↥P) • Pₛ) := by
    have h : MulAut.conj x • Pₛ =
        MulAut.conj (SemidirectProduct.inl n : G ⋊[φP] ↥P) • Pₛ := by
      rw [hx_decomp, map_mul, mul_smul, hPₛ_conj_inr_u]
    rw [← h]; exact hDisj_x
  -- Witness for regular orbit: n. For φ ∈ ↥P fixing n, show φ = 1.
  refine ⟨n, fun φ hφg => ?_⟩
  -- φ fixes n ⇒ inr φ commutes with inl n (via inl_aut) ⇒ inr φ ∈ MulAut.conj (inl n) • Pₛ.
  -- Combined with inr φ ∈ Pₛ and hDisj_n: inr φ ∈ ⊥, hence φ = 1.
  have hfix : (φP φ) n = n := hφg
  have hφ_in_Pₛ : (SemidirectProduct.inr φ : G ⋊[φP] ↥P) ∈ Pₛ := ⟨φ, rfl⟩
  have hcomm : (SemidirectProduct.inl n : G ⋊[φP] ↥P) * SemidirectProduct.inr φ
             = SemidirectProduct.inr φ * SemidirectProduct.inl n := by
    -- inl_aut φ n : inl ((φP φ) n) = inr φ * inl n * inr φ⁻¹.
    -- With hfix: inl n = inr φ * inl n * inr φ⁻¹.
    -- Right-multiplying by inr φ: inl n * inr φ = inr φ * inl n.
    have h1 : (SemidirectProduct.inl n : G ⋊[φP] ↥P) =
        SemidirectProduct.inr φ * SemidirectProduct.inl n * SemidirectProduct.inr φ⁻¹ := by
      have h : (SemidirectProduct.inl ((φP φ) n) : G ⋊[φP] ↥P) =
          SemidirectProduct.inr φ * SemidirectProduct.inl n * SemidirectProduct.inr φ⁻¹ :=
        SemidirectProduct.inl_aut φ n
      rw [hfix] at h; exact h
    conv_lhs => rw [h1]
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have hφ_in_conj : (SemidirectProduct.inr φ : G ⋊[φP] ↥P) ∈
      MulAut.conj (SemidirectProduct.inl n : G ⋊[φP] ↥P) • Pₛ := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
        MulAut.conj_inv_apply]
    -- Goal: (inl n)⁻¹ * inr φ * inl n ∈ Pₛ. Equals inr φ via hcomm.
    rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hφ_in_Pₛ
  have hφ_eq_one : (SemidirectProduct.inr φ : G ⋊[φP] ↥P) = 1 :=
    Subgroup.mem_bot.mp (hDisj_n.le_bot ⟨hφ_in_Pₛ, hφ_in_conj⟩)
  exact SemidirectProduct.inr_injective (hφ_eq_one.trans (map_one _).symm)

end -- 3A

section /- 3B: Schur-Zassenhaus + 可解群基本 (pp. 75-82) -/

variable {G : Type*} [Group G]

/-! ### Isaacs §3B 結果 ↔ mathlib 対応表

CLAUDE.md mathlib ラッパー方針に従い, 純粋なリネームは書かない. 呼び出し側で
直接 mathlib 名を使う:

| Isaacs | mathlib |
|---|---|
| Thm 3.5 (Schur-Zassenhaus, abelian normal) | `Subgroup.exists_right_complement'_of_coprime` |
| Thm 3.6 (crossed homom) | `OneCocycle` / `OneCocycles` (`GroupCohomology.LowDegree`) |
| Thm 3.7 (transversal differ) | mathlib `MonoidHom.crossed*` 周辺 |
| Thm 3.8 (Schur-Zassenhaus 一般) | `Subgroup.exists_right_complement'_of_coprime` |
| Thm 3.9 (G solvable ⇔ G^(m) = 1) | `isSolvable_iff_derivedSeries_eq_bot` |
| Thm 3.10 (solvable 基本) | `IsSolvable` instance による subgroup/quotient/extension 各種 |
| Thm 3.11 (solvable min normal は elem abelian p-group) | **新規**? — mathlib にあるか要確認 (TODO) |
| Thm 3.12 (complement conjugacy in solvable) | `IsConj` 系 + `SchurZassenhaus` |

新規実装候補:
- **Thm 3.11**: solvable group の minimal normal subgroup は elementary abelian p-group.
  Isaacs 自身の証明は短い. mathlib に直接の対応があるか調査が必要.
-/

/-- A normal subgroup meeting a prime-order complement trivially lies in the normal Hall kernel.

If `K ◁ G` has complement `R` of prime order and `|K|` is coprime to `|R|`, then any
normal subgroup `N ◁ G` with `N ⊓ R = ⊥` satisfies `N ≤ K`. -/
theorem normal_le_of_complement_prime_of_inf_eq_bot
    {G : Type*} [Group G] [Finite G] {K N R : Subgroup G} [K.Normal] [N.Normal]
    (hcompl : Subgroup.IsComplement' K R) (hp : (Nat.card R).Prime)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R)) (hNR : N ⊓ R = ⊥) :
    N ≤ K := by
  haveI : Fact (Nat.card R).Prime := ⟨hp⟩
  have hpK : ¬ (Nat.card R) ∣ Nat.card K := (hp.coprime_iff_not_dvd).mp hcop.symm
  have hcard_mul : Nat.card K * Nat.card R = Nat.card G := hcompl.card_mul
  have hquot : Nat.card (G ⧸ K) = Nat.card R := by
    have h1 : Nat.card G = Nat.card (G ⧸ K) * Nat.card K :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup K
    have h2 : Nat.card (G ⧸ K) * Nat.card K = Nat.card R * Nat.card K := by
      rw [← h1, ← hcard_mul, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hfact : (Nat.card G).factorization (Nat.card R) = 1 := by
    rw [← hcard_mul, Nat.factorization_mul (Nat.ne_of_gt Nat.card_pos)
      (Nat.ne_of_gt Nat.card_pos), Finsupp.coe_add, Pi.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpK, hp.factorization_self, zero_add]
  let Rsyl : Sylow (Nat.card R) G := Sylow.ofCard R (by rw [hfact, pow_one])
  have hpN : ¬ (Nat.card R) ∣ Nat.card N := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) (Nat.card R) hdvd
    have hxG : orderOf ((x : G)) = Nat.card R := by
      rw [← hx]; exact orderOf_injective N.subtype N.subtype_injective x
    have hPgroup : IsPGroup (Nat.card R) (Subgroup.zpowers ((x : G))) :=
      IsPGroup.of_card (((Nat.card_zpowers _).trans hxG).trans (pow_one _).symm)
    obtain ⟨Q, hQ⟩ := hPgroup.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q Rsyl
    have hxQ : (x : G) ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers _)
    have hcompute : (MulAut.conj g)⁻¹ • (g * (x : G) * g⁻¹) = (x : G) := by
      rw [← map_inv]
      change (MulAut.conj g⁻¹) (g * (x : G) * g⁻¹) = (x : G)
      rw [MulAut.conj_apply]; group
    have hconjR : g * (x : G) * g⁻¹ ∈ R := by
      have hRsyl : (Rsyl : Subgroup G) = R := rfl
      rw [← hRsyl, ← hg, Sylow.coe_subgroup_smul,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [hcompute] using hxQ
    have hconjN : g * (x : G) * g⁻¹ ∈ N :=
      (inferInstance : N.Normal).conj_mem (x : G) x.2 g
    have hmem : g * (x : G) * g⁻¹ ∈ N ⊓ R := ⟨hconjN, hconjR⟩
    rw [hNR, Subgroup.mem_bot] at hmem
    have hx1 : (x : G) = 1 := by
      have hc : (MulAut.conj g) (x : G) = 1 := by rw [MulAut.conj_apply]; exact hmem
      exact (MulEquiv.map_eq_one_iff _).mp hc
    rw [hx1, orderOf_one] at hxG
    exact hp.one_lt.ne hxG
  have hdvd1 : Nat.card (N.map (QuotientGroup.mk' K)) ∣ Nat.card N :=
    Subgroup.card_map_dvd _ _
  have hdvd2 : Nat.card (N.map (QuotientGroup.mk' K)) ∣ Nat.card R := by
    rw [← hquot]; exact Subgroup.card_subgroup_dvd_card _
  have hcop2 : Nat.Coprime (Nat.card N) (Nat.card R) := ((hp.coprime_iff_not_dvd).mpr hpN).symm
  have hone : Nat.card (N.map (QuotientGroup.mk' K)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop2 hdvd1 hdvd2
  have hbot : N.map (QuotientGroup.mk' K) = ⊥ := Subgroup.card_eq_one.mp hone
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

/-! **Elementary Abelian p-Group** の def は `OddOrder/GroupTheory/ElementaryAbelian.lean`
に移動 (2026-05-23). Ch.3, Ch.6, Ch.7 共通の shared concept として独立 module 化.
本ファイルでは `OddOrder.GroupTheory.IsElementaryAbelian` (whole-group form) と
`Subgroup.IsElementaryAbelian` (subgroup form) の双方を利用可能. -/

open scoped commutatorElement in
/-- Thm 3.11 の前半: 可解群の minimal normal subgroup は abelian.

証明: M 可解 (G 可解の部分群), M ≠ ⊥ (minimal normal) ⇒
`IsSolvable.commutator_lt_of_ne_bot` で `⁅M, M⁆ < M`. `⁅M, M⁆ ⊴ G` (commutator of normals).
M の minimality で `⁅M, M⁆ = ⊥`, よって M abelian. -/
theorem solvable_minimal_normal_isAbelian {G : Type*} [Group G] [Finite G] [IsSolvable G]
    {M : Subgroup G} (hM : OddOrder.Isaacs.Ch02.IsMinimalNormal M) :
    ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
  haveI hMnormal : M.Normal := hM.1
  have hM_ne_bot : M ≠ ⊥ := hM.2.1
  -- ⁅M, M⁆ < M (M solvable, M ≠ ⊥).
  have hcomm_lt : ⁅M, M⁆ < M := IsSolvable.commutator_lt_of_ne_bot hM_ne_bot
  -- ⁅M, M⁆ ⊴ G (commutator of normals: mathlib auto-instance).
  have hCommNormal : (⁅M, M⁆ : Subgroup G).Normal := inferInstance
  -- By minimality of M, ⁅M, M⁆ = ⊥ or = M. Strict < rules out =.
  have hcomm_eq_bot : ⁅M, M⁆ = ⊥ := by
    rcases hM.2.2 ⁅M, M⁆ hCommNormal hcomm_lt.le with h | h
    · exact h
    · exact absurd h hcomm_lt.ne
  -- M abelian: ⁅x, y⁆ ∈ ⁅M, M⁆ = ⊥ ⇒ x * y = y * x.
  intro x hx y hy
  have hcomm_xy : ⁅x, y⁆ ∈ ⁅M, M⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [hcomm_eq_bot, Subgroup.mem_bot] at hcomm_xy
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm_xy

/-- **Isaacs Thm 3.11**: 可解群 `G` の minimal normal subgroup は ある素数 `p` について
elementary abelian p-group.

証明: M abelian (前補題). `p ∣ |M|` を取り, `T = {x ∈ M | x^p = 1}` を M の部分群とする
(M abelian で閉性 OK). T は M で characteristic (自己同型は p-冪を保つ).
Cauchy で T ≠ ⊥. T.map M.subtype は characteristic-in-normal で G 正規 + ≤ M.
M minimality で T.map M.subtype ∈ {⊥, M}. T ≠ ⊥ より T.map M.subtype = M, よって T = ⊤,
即ち全 x ∈ M で x^p = 1. -/
theorem solvable_minimal_normal_isElementaryAbelian [Finite G] [IsSolvable G]
    {M : Subgroup G} (hM : OddOrder.Isaacs.Ch02.IsMinimalNormal M) :
    ∃ p : ℕ, p.Prime ∧ M.IsElementaryAbelian p := by
  haveI hMnormal : M.Normal := hM.1
  have hM_ne_bot : M ≠ ⊥ := hM.2.1
  have habel := solvable_minimal_normal_isAbelian hM
  haveI hMcomm : IsMulCommutative ↥M :=
    ⟨⟨fun a b => Subtype.ext (habel a a.2 b b.2)⟩⟩
  haveI hMnt : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
  have hM_card_pos : 1 < Nat.card ↥M := Finite.one_lt_card
  obtain ⟨p, hp_prime, hp_dvd⟩ :=
    Nat.exists_prime_and_dvd hM_card_pos.ne'
  refine ⟨p, hp_prime, ?_⟩
  haveI hpFact : Fact p.Prime := ⟨hp_prime⟩
  -- T = {x : ↥M | x^p = 1} as a Subgroup of ↥M.
  let T : Subgroup ↥M :=
    { carrier := {x | x ^ p = 1}
      one_mem' := one_pow p
      mul_mem' := by
        intro a b ha hb
        change (a * b) ^ p = 1
        change a ^ p = 1 at ha
        change b ^ p = 1 at hb
        -- rc2: `mul_pow` needs `CommMonoid ↥M`; derive `Commute a b` from `habel`.
        have hcomm : Commute a b := Subtype.ext (habel a a.2 b b.2)
        rw [hcomm.mul_pow, ha, hb, one_mul]
      inv_mem' := by
        intro a ha
        change a⁻¹ ^ p = 1
        change a ^ p = 1 at ha
        rw [inv_pow, ha, inv_one] }
  -- T characteristic in ↥M.
  haveI hT_char : T.Characteristic := by
    rw [Subgroup.characteristic_iff_le_comap]
    intro φ x hx
    rw [Subgroup.mem_comap]
    change (φ x) ^ p = 1
    change x ^ p = 1 at hx
    rw [← map_pow, hx, map_one]
  -- T ≠ ⊥ via Cauchy.
  obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) p hp_dvd
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
  -- T.map M.subtype ⊴ G (characteristic-in-normal).
  haveI hTM_normal : (T.map M.subtype).Normal := inferInstance
  have hTM_le_M : T.map M.subtype ≤ M := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  -- Minimality.
  rcases hM.2.2 (T.map M.subtype) hTM_normal hTM_le_M with hTM_bot | hTM_eq
  · exfalso
    have hT_eq_bot : T = ⊥ := by
      have : T.map M.subtype = (⊥ : Subgroup ↥M).map M.subtype := by
        rw [hTM_bot, Subgroup.map_bot]
      exact Subgroup.map_injective M.subtype_injective this
    exact hT_ne_bot hT_eq_bot
  · refine ⟨fun a b => Subtype.ext (habel a a.2 b b.2), fun y => ?_⟩
    have hy_TM : (y : G) ∈ T.map M.subtype := by
      rw [hTM_eq]; exact y.2
    obtain ⟨z, hz_T, hz_eq⟩ := hy_TM
    have hzy : z = y := Subtype.ext hz_eq
    exact hzy ▸ hz_T

end -- 3B

section /- 3C: Hall theory (pp. 83-88) -/

variable {G : Type*} [Group G]

/-- **`π`-Hall 部分群** (Isaacs Def): 有限群 `G` の部分群 `H` で,
`|H|` の素因子が全て `π` に含まれ, `|G:H|` の素因子が `π` を避ける.

同値な条件: `Nat.Coprime (Nat.card H) H.index` (Hall property = 位数と指数 coprime).
mathlib 未収載の新規定義. -/
def IsHallSubgroup (π : Set ℕ) (H : Subgroup G) : Prop :=
  (∀ p ∈ (Nat.card H).primeFactors, p ∈ π) ∧
  (∀ p ∈ H.index.primeFactors, p ∉ π)

/-- π-Hall H ⇒ H's order has only π-prime factors (definition の片半分 = π-group 性質). -/
theorem IsHallSubgroup.primeFactors_card_subset {π : Set ℕ} {H : Subgroup G}
    (h : IsHallSubgroup π H) : ∀ p ∈ (Nat.card H).primeFactors, p ∈ π := h.1

/-- π-Hall H ⇒ H.index is a π'-number (no π-prime divides it). -/
theorem IsHallSubgroup.index_no_pi {π : Set ℕ} {H : Subgroup G}
    (h : IsHallSubgroup π H) : ∀ p ∈ H.index.primeFactors, p ∉ π := h.2

/-- `IsHallSubgroup` is order-determined: equal cardinality transfers the Hall property
(`H.index` is `|ambient| / |H|`, so equal `|H|` gives equal index, and both Hall conditions are
prime-factor conditions on `|H|` and `H.index`). -/
theorem isHallSubgroup_of_card_eq [Finite G] {π : Set ℕ} {A B : Subgroup G}
    (hB : IsHallSubgroup π B) (hc : Nat.card A = Nat.card B) :
    IsHallSubgroup π A := by
  have hidx : A.index = B.index := by
    have key : Nat.card A * A.index = Nat.card B * B.index := by
      rw [Subgroup.card_mul_index, Subgroup.card_mul_index]
    rw [hc] at key
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos key
  exact ⟨fun p hp => hB.1 p (hc ▸ hp), fun p hp => hB.2 p (hidx ▸ hp)⟩

/-- π-Hall ⇒ Coprime `|H|` `|G:H|`. 標準的: 共通素因子は π と π' 両方に属し矛盾. -/
theorem IsHallSubgroup.coprime_index [Finite G] {π : Set ℕ} {H : Subgroup G}
    (h : IsHallSubgroup π H) : Nat.Coprime (Nat.card H) H.index := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hne
  rw [Nat.dvd_gcd_iff] at hp_dvd
  have hH_pos : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hI_pos : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hp_H_pf : p ∈ (Nat.card H).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd.1, hH_pos⟩
  have hp_idx_pf : p ∈ H.index.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd.2, hI_pos⟩
  exact h.2 p hp_idx_pf (h.1 p hp_H_pf)

/-- The image of a π-Hall subgroup in a quotient is again π-Hall. -/
theorem IsHallSubgroup.map_quotient [Finite G] {π : Set ℕ} {N : Subgroup G}
    [N.Normal] {H : Subgroup G} (hH : IsHallSubgroup π H) :
    IsHallSubgroup π (H.map (QuotientGroup.mk' N)) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    apply hH.1
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hp.1, hp.2.1.trans (Subgroup.card_map_dvd _ _), Nat.card_pos.ne'⟩
  · intro p hp
    apply hH.2
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hp.1,
      hp.2.1.trans (H.index_map_dvd (QuotientGroup.mk'_surjective N)),
      Subgroup.index_ne_zero_of_finite⟩

/-- A `π`-Hall subgroup stays `π`-Hall under any automorphism of the ambient group. -/
theorem IsHallSubgroup.mulAut_smul [Finite G] {π : Set ℕ} {H : Subgroup G}
    (hH : IsHallSubgroup π H) (φ : MulAut G) : IsHallSubgroup π (φ • H) := by
  rw [show (φ • H : Subgroup G) = H.map (φ : G →* G) by
    rw [Subgroup.pointwise_smul_def]
    rfl]
  refine ⟨?_, ?_⟩
  · have hcard : Nat.card ↥(H.map (φ : G →* G)) = Nat.card ↥H :=
      (Nat.card_congr (Subgroup.equivMapOfInjective H _ φ.injective).toEquiv).symm
    rw [hcard]
    exact hH.1
  · have hidx : (H.map (φ : G →* G)).index = H.index :=
      Subgroup.index_map_equiv H φ
    rw [hidx]
    exact hH.2

/-- The type of `π`-Hall subgroups of `G`. -/
abbrev HallSubgroups (π : Set ℕ) (G : Type*) [Group G] :=
  {H : Subgroup G // IsHallSubgroup π H}

/-- Ambient automorphisms act on the type of `π`-Hall subgroups. -/
instance HallSubgroups.mulAutAction [Finite G] (π : Set ℕ) :
    MulAction (MulAut G) (HallSubgroups π G) where
  smul φ H := ⟨φ • H.1, H.2.mulAut_smul φ⟩
  one_smul H := by
    apply Subtype.ext
    change (1 : MulAut G) • H.1 = H.1
    simp
  mul_smul φ ψ H := by
    apply Subtype.ext
    change (φ * ψ) • H.1 = φ • (ψ • H.1)
    simp [mul_smul]

/-- The conjugation action of `G` on its `π`-Hall subgroups. -/
instance HallSubgroups.conjAction [Finite G] (π : Set ℕ) :
    MulAction G (HallSubgroups π G) :=
  MulAction.compHom (HallSubgroups π G) (MulAut.conj : G →* MulAut G)

/-- A Hall subgroup of a subgroup whose ambient index is a `π'`-number stays Hall after
pushing it back to the whole ambient group. -/
theorem IsHallSubgroup.map_subtype_of_index_no_pi [Finite G] {π : Set ℕ}
    {H : Subgroup G} {L : Subgroup H} (hL : IsHallSubgroup π L)
    (hH_index : ∀ p ∈ H.index.primeFactors, p ∉ π) :
    IsHallSubgroup π (L.map H.subtype) := by
  have hcard : Nat.card ↥(L.map H.subtype) = Nat.card ↥L :=
    (Nat.card_congr
      (Subgroup.equivMapOfInjective L H.subtype H.subtype_injective).toEquiv).symm
  have hindex : (L.map H.subtype).index = L.index * H.index := by
    have hpos : 0 < Nat.card ↥L := Nat.card_pos
    have hmul : Nat.card ↥L * (L.map H.subtype).index =
        Nat.card ↥L * (L.index * H.index) := by
      calc
        Nat.card ↥L * (L.map H.subtype).index
            = Nat.card ↥(L.map H.subtype) * (L.map H.subtype).index := by rw [hcard]
        _ = Nat.card G := Subgroup.card_mul_index (L.map H.subtype)
        _ = Nat.card H * H.index := (Subgroup.card_mul_index H).symm
        _ = (Nat.card ↥L * L.index) * H.index := by rw [Subgroup.card_mul_index L]
        _ = Nat.card ↥L * (L.index * H.index) := by ring
    exact Nat.mul_left_cancel hpos hmul
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [hcard] at hp
    exact hL.1 p hp
  · intro p hp hp_pi
    rw [hindex] at hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hp_prime, hp_dvd, _⟩ := hp
    rcases hp_prime.dvd_mul.mp hp_dvd with hp_L | hp_H
    · exact hL.2 p
        (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_L, Subgroup.index_ne_zero_of_finite⟩) hp_pi
    · exact hH_index p
        (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_H, Subgroup.index_ne_zero_of_finite⟩) hp_pi

/-- `⊤` は π-Hall ⇔ `G` が π-group (`|G|` の全素因子が π に属す). -/
theorem IsHallSubgroup.top_iff (π : Set ℕ) :
    IsHallSubgroup π (⊤ : Subgroup G) ↔ ∀ p ∈ (Nat.card G).primeFactors, p ∈ π := by
  unfold IsHallSubgroup
  rw [Subgroup.index_top, Subgroup.card_top, Nat.primeFactors_one]
  simp

/-- `⊥` は π-Hall ⇔ `G` が π'-group (`|G|` の素因子が π を避ける). -/
theorem IsHallSubgroup.bot_iff (π : Set ℕ) :
    IsHallSubgroup π (⊥ : Subgroup G) ↔ ∀ p ∈ (Nat.card G).primeFactors, p ∉ π := by
  unfold IsHallSubgroup
  rw [Subgroup.index_bot, Subgroup.card_bot, Nat.primeFactors_one]
  simp

/-- `|G| = 1` ⇒ `⊥` は任意の π について π-Hall. -/
theorem IsHallSubgroup.bot_of_card_eq_one (π : Set ℕ) (h : Nat.card G = 1) :
    IsHallSubgroup π (⊥ : Subgroup G) := by
  rw [IsHallSubgroup.bot_iff]
  intro p hp
  rw [h, Nat.primeFactors_one] at hp
  exact absurd hp (Finset.notMem_empty p)

/-- **Isaacs Thm 3.13 Hall-E** の `|G|`-強誘導補助補題.

`n` パラメータは `Nat.card G ≤ n` を表し, induction by `n` で strong induction の
形を取れる. base case (`Nat.card G = 1`) は完全に閉じる. step case (~200 LOC):
1. M minimal normal 取り (G nontrivial で existence).
2. Thm 3.11 で M elementary abelian p-group.
3. `IH (G ⧸ M) (|G/M| ≤ n から |G/M| = |G|/|M| < |G|)` で `H̄` π-Hall in G/M を得る.
4. pullback `H = comap (mk' M) H̄`.
5. p ∈ π case: H は π-Hall (|H| = |H̄|·|M|, |M| は p-power, |G:H| = |G/M : H̄|).
6. p ∉ π case: H の subgroup M ⊴ H で `Coprime (Nat.card M) M.index` (in H).
   Schur-Zassenhaus で `H = M ⋊ K`. K が π-Hall in G.

**実装状態** ⭐ sorry-free (2026-05-23 完成). AxiomsCheck flagship 入り
(`OddOrder.Isaacs.Ch03.hall_E_exists`). -/
private theorem hall_E_strong_aux : ∀ n : ℕ,
    ∀ (G : Type*) [Group G] [Finite G] [IsSolvable G],
      Nat.card G ≤ n → ∀ (π : Set ℕ),
      ∃ H : Subgroup G, IsHallSubgroup π H := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ hcard _
    exact absurd hcard (Nat.not_le_of_lt Nat.card_pos)
  | succ n ih =>
    intro G _ _ _ hcard π
    by_cases hsmall : Nat.card G ≤ n
    · exact ih G hsmall π
    · by_cases hG_one : Nat.card G = 1
      · exact ⟨⊥, IsHallSubgroup.bot_of_card_eq_one π hG_one⟩
      · -- |G| > 1. G nontrivial.
        haveI hG_nontrivial : Nontrivial G :=
          Finite.one_lt_card_iff_nontrivial.mp
            (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.card_pos.ne', hG_one⟩)
        -- Get minimal normal M ≤ ⊤.
        obtain ⟨M, hM, _⟩ :=
          OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
        haveI hMnormal : M.Normal := hM.1
        have hM_ne_bot : M ≠ ⊥ := hM.2.1
        -- M elementary abelian p-group via Thm 3.11.
        obtain ⟨_p, _hp_prime, _hp_elem⟩ := solvable_minimal_normal_isElementaryAbelian hM
        -- |M| ≥ 2 since M is nontrivial.
        haveI hM_nontrivial : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
        have hM_card_ge_two : 2 ≤ Nat.card ↥M := Finite.one_lt_card
        -- |G/M| · |M| = |G|. So |G/M| ≤ |G|/2 ≤ n (since |G| ≤ n+1).
        have hquot_card : Nat.card (G ⧸ M) ≤ n := by
          have key : Nat.card G = Nat.card (G ⧸ M) * Nat.card M :=
            Subgroup.card_eq_card_quotient_mul_card_subgroup M
          have hQ_pos : 0 < Nat.card (G ⧸ M) := Nat.card_pos
          -- |G/M| * 2 ≤ |G/M| * |M| = |G| ≤ n+1.
          have h1 : Nat.card (G ⧸ M) * 2 ≤ Nat.card G := by
            rw [key]
            exact Nat.mul_le_mul_left _ hM_card_ge_two
          omega
        haveI hQuot_sol : IsSolvable (G ⧸ M) := inferInstance
        -- IH on G/M.
        obtain ⟨Hbar, hHbar⟩ := ih (G ⧸ M) hquot_card π
        -- Pull back: H = comap (mk' M) Hbar.
        set H : Subgroup G := Subgroup.comap (QuotientGroup.mk' M) Hbar with hH_def
        -- Key cardinality facts.
        have hH_index : H.index = Hbar.index :=
          Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective (N := M))
        have hHbar_idx_pos : 0 < Hbar.index := Nat.pos_of_ne_zero
          (Subgroup.index_ne_zero_of_finite)
        -- |H| = |Hbar| * |M|.
        have hH_card_eq : Nat.card H = Nat.card Hbar * Nat.card ↥M := by
          have eq1 : Nat.card H * H.index = Nat.card G := Subgroup.card_mul_index H
          have eq2 : Nat.card Hbar * Hbar.index = Nat.card (G ⧸ M) :=
            Subgroup.card_mul_index Hbar
          have eq3 : Nat.card (G ⧸ M) * Nat.card ↥M = Nat.card G :=
            (Subgroup.card_eq_card_quotient_mul_card_subgroup M).symm
          have h_eq : Nat.card H * Hbar.index = (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by
            calc Nat.card H * Hbar.index
                = Nat.card H * H.index := by rw [hH_index]
              _ = Nat.card G := eq1
              _ = Nat.card (G ⧸ M) * Nat.card ↥M := eq3.symm
              _ = (Nat.card Hbar * Hbar.index) * Nat.card ↥M := by rw [eq2]
              _ = (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by ring
          exact Nat.mul_right_cancel hHbar_idx_pos h_eq
        -- |M| is a p-power (M is elementary abelian p-group ⇒ IsPGroup).
        have hM_pPower : ∃ k, Nat.card ↥M = _p ^ k := by
          haveI : Fact _p.Prime := ⟨_hp_prime⟩
          have hPG : IsPGroup _p ↥M := fun x => ⟨1, by
            rw [pow_one]
            exact _hp_elem.2 x⟩
          exact IsPGroup.iff_card.mp hPG
        -- Primes of |M| ⊆ {p}.
        have hM_primes : ∀ q ∈ (Nat.card ↥M).primeFactors, q = _p := by
          obtain ⟨k, hk⟩ := hM_pPower
          intro q hq
          rw [hk] at hq
          rw [Nat.mem_primeFactors] at hq
          obtain ⟨hq_prime, hq_dvd, _⟩ := hq
          exact (Nat.prime_dvd_prime_iff_eq hq_prime _hp_prime).mp
            (hq_prime.dvd_of_dvd_pow hq_dvd)
        by_cases hp_pi : _p ∈ π
        · -- Case 1: p ∈ π. H is π-Hall.
          refine ⟨H, ?_, ?_⟩
          · -- Primes of |H| ⊆ π.
            intro q hq_pf
            rw [hH_card_eq] at hq_pf
            rw [Nat.mem_primeFactors] at hq_pf
            obtain ⟨hq_prime, hq_dvd, hq_ne0⟩ := hq_pf
            -- q divides |Hbar| * |M|, so q divides |Hbar| or q divides |M|.
            rcases hq_prime.dvd_mul.mp hq_dvd with h_in_Hbar | h_in_M
            · -- q ∈ primeFactors(|Hbar|) ⊆ π.
              refine hHbar.1 q ?_
              exact Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_Hbar, Nat.card_pos.ne'⟩
            · -- q ∈ primeFactors(|M|) ⊆ {p} ⊆ π.
              have hq_in_M_pf : q ∈ (Nat.card ↥M).primeFactors :=
                Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_M, Nat.card_pos.ne'⟩
              rw [hM_primes q hq_in_M_pf]
              exact hp_pi
          · -- Primes of H.index ⊆ π'.
            rw [hH_index]
            exact hHbar.2
        · -- Case 2: p ∉ π. Apply Schur-Zassenhaus to M.subgroupOf H ≤ H.
          have hM_le_H : M ≤ H := QuotientGroup.le_comap_mk' M Hbar
          have h_card_MH : Nat.card ↥(M.subgroupOf H) = Nat.card ↥M :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM_le_H).toEquiv
          -- Coprime |M| |Hbar|.
          have h_disjoint : Disjoint (Nat.card ↥M).primeFactors (Nat.card Hbar).primeFactors := by
            rw [Finset.disjoint_left]
            intro q hq_M hq_Hbar
            exact hp_pi (hM_primes q hq_M ▸ hHbar.1 q hq_Hbar)
          have h_coprime_M_Hbar : Nat.Coprime (Nat.card ↥M) (Nat.card Hbar) :=
            (Nat.disjoint_primeFactors Nat.card_pos.ne' Nat.card_pos.ne').mp h_disjoint
          -- (M.subgroupOf H).index = |Hbar|.
          have h_idx_MH : (M.subgroupOf H).index = Nat.card Hbar := by
            have hMH_lag : Nat.card ↥(M.subgroupOf H) * (M.subgroupOf H).index = Nat.card ↥H :=
              Subgroup.card_mul_index (M.subgroupOf H)
            rw [h_card_MH, hH_card_eq] at hMH_lag
            -- Nat.card ↥M * (M.subgroupOf H).index = Nat.card Hbar * Nat.card ↥M
            have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
            have : Nat.card ↥M * (M.subgroupOf H).index = Nat.card ↥M * Nat.card Hbar := by
              rw [hMH_lag, mul_comm (Nat.card Hbar)]
            exact Nat.mul_left_cancel hM_pos this
          -- Schur-Zassenhaus.
          have h_coprime_MH : Nat.Coprime (Nat.card ↥(M.subgroupOf H)) (M.subgroupOf H).index := by
            rw [h_card_MH, h_idx_MH]; exact h_coprime_M_Hbar
          haveI : (M.subgroupOf H).Normal := hMnormal.subgroupOf H
          obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime h_coprime_MH
          -- K.index in H = |M.subgroupOf H|, |K| = |Hbar|.
          have hK_index : K.index = Nat.card ↥(M.subgroupOf H) := hK.index_eq_card
          have hK_card : Nat.card ↥K = Nat.card Hbar := by
            have := hK.card_mul
            -- this : Nat.card (M.subgroupOf H) * Nat.card K = Nat.card H
            rw [h_card_MH, hH_card_eq] at this
            -- |M| * |K| = |Hbar| * |M|
            have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
            have h_eq : Nat.card ↥M * Nat.card ↥K = Nat.card ↥M * Nat.card Hbar := by
              rw [this, mul_comm]
            exact Nat.mul_left_cancel hM_pos h_eq
          -- |K.map H.subtype| = |K| = |Hbar|.
          have hKlift_card : Nat.card ↥(K.map H.subtype) = Nat.card Hbar := by
            rw [Subgroup.card_subtype, hK_card]
          -- (K.map H.subtype).index = K.index * H.index = |M| * Hbar.index.
          have hKlift_index : (K.map H.subtype).index = Nat.card ↥M * Hbar.index := by
            rw [Subgroup.index_map, Subgroup.ker_subtype, sup_bot_eq, hK_index, h_card_MH,
                Subgroup.range_subtype, hH_index]
          refine ⟨K.map H.subtype, ?_, ?_⟩
          · -- Primes of |K.map H.subtype| ⊆ π.
            intro q hq_pf
            rw [hKlift_card] at hq_pf
            exact hHbar.1 q hq_pf
          · -- Primes of (K.map H.subtype).index ⊆ π'.
            intro q hq_pf hq_pi
            rw [hKlift_index] at hq_pf
            rw [Nat.mem_primeFactors] at hq_pf
            obtain ⟨hq_prime, hq_dvd, _⟩ := hq_pf
            rcases hq_prime.dvd_mul.mp hq_dvd with h_in_M | h_in_HbarIdx
            · -- q divides |M| ⇒ q = p (M is p-power).
              have hq_in_M_pf : q ∈ (Nat.card ↥M).primeFactors :=
                Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_M, Nat.card_pos.ne'⟩
              have hq_eq_p : q = _p := hM_primes q hq_in_M_pf
              rw [hq_eq_p] at hq_pi
              exact hp_pi hq_pi
            · -- q divides Hbar.index ⇒ q ∉ π (from IH).
              have hq_in_HbarIdx_pf : q ∈ Hbar.index.primeFactors :=
                Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_HbarIdx, Subgroup.index_ne_zero_of_finite⟩
              exact hHbar.2 q hq_in_HbarIdx_pf hq_pi

/-- **Isaacs Thm 3.13 Hall-E** ⭐ **FT クリティカル**: `G` 可解 ⇒ 任意の `π ⊆ Primes`
について `π`-Hall 部分群が存在.

証明骨子 (Isaacs p.84): `|G|`-induction.
* Base: `|G| = 1` ⇒ `⊥ = ⊤` が π-Hall.
* Step: minimal normal `M` を取る (G ≠ ⊥). Thm 3.11 で `M` は elem abelian p-group.
  - **Case 1** `p ∈ π`: IH を `G/M` に適用 (`G/M` solvable, `|G/M| < |G|`),
    π-Hall `H/M` を得る. 引き戻した `H` が `G` の π-Hall.
  - **Case 2** `p ∉ π`: IH を `G/M` に. π-Hall `L/M`. `M` 位数と `L/M` 位数 coprime
    (`p ∉ π` で `L/M` 内に `p` 因子なし). Schur-Zassenhaus で `L = M ⋊ H`, `H` が
    `G` の π-Hall. -/
theorem hall_E_exists [Finite G] [IsSolvable G] (π : Set ℕ) :
    ∃ H : Subgroup G, IsHallSubgroup π H :=
  hall_E_strong_aux (Nat.card G) G le_rfl π

/-- **Isaacs Thm 3.14 Hall-C** の `|G|`-強誘導補助補題.

`Phase 2` (2026-05-23): Phase 1 `IsComplement'.exists_conj_of_coprime` 完成で実装可能化.

証明骨格 (Isaacs FGT p.85-86):
1. base case (`Nat.card G = 1`): trivial (H = K = ⊥).
2. step case:
   - `M` minimal normal ⊆ `G`, Thm 3.11 で elementary abelian `p`-group.
   - `H̄, K̄ : Subgroup (G/M)` ともに π-Hall (cardinality 議論).
   - IH on `G/M` で `∃ ḡ, H̄.map (conj ḡ) = K̄`. Lift to `g ∈ G`.
   - `H^g ⊔ M = K ⊔ M` (= `HM`) via `mk'_comp_conj_eq` + `map_eq_map_iff`.
   - **Case `p ∈ π`**: `M ⊆ H, M ⊆ K` (cardinality + π-Hall maximality). 故に
     `HM = H^g = K`.
   - **Case `p ∉ π`**: `H^g ∩ M = ⊥, K ∩ M = ⊥` (coprime orders). 両方 `M` の
     complement in `HM`. Phase 1 `IsComplement'.exists_conj_of_coprime`
     (M solvable since abelian p-group) で `∃ m ∈ M, H^g.map (conj m) = K`. -/
private theorem hall_C_strong_aux : ∀ n : ℕ,
    ∀ (G : Type*) [Group G] [Finite G] [IsSolvable G],
      Nat.card G ≤ n → ∀ {π : Set ℕ} {H K : Subgroup G},
      IsHallSubgroup π H → IsHallSubgroup π K →
      ∃ g : G, H.map (MulAut.conj g).toMonoidHom = K := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ hcard _ _ _ _ _
    exact absurd hcard (Nat.not_le_of_lt Nat.card_pos)
  | succ n ih =>
    intro G _ _ _ hcard π H K hH hK
    by_cases hsmall : Nat.card G ≤ n
    · exact ih G hsmall hH hK
    by_cases hG_one : Nat.card G = 1
    · -- |G| = 1 ⇒ G subsingleton ⇒ H = K = ⊥. Take g = 1.
      haveI : Subsingleton G := Nat.card_eq_one_iff_unique.mp hG_one |>.1
      refine ⟨1, ?_⟩
      apply Subgroup.ext
      intro x
      have hx : x = 1 := Subsingleton.elim x 1
      subst hx
      simp
    -- |G| > 1: G nontrivial.
    haveI hG_nontrivial : Nontrivial G :=
      Finite.one_lt_card_iff_nontrivial.mp
        (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.card_pos.ne', hG_one⟩)
    -- Minimal normal M ⊆ G.
    obtain ⟨M, hM, _⟩ :=
      OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
    haveI hMnormal : M.Normal := hM.1
    have hM_ne_bot : M ≠ ⊥ := hM.2.1
    -- M elementary abelian p-group via Thm 3.11.
    obtain ⟨p, hp_prime, hp_elem⟩ := solvable_minimal_normal_isElementaryAbelian hM
    haveI hp_fact : Fact p.Prime := ⟨hp_prime⟩
    haveI hM_nontrivial : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
    have hM_card_ge_two : 2 ≤ Nat.card ↥M := Finite.one_lt_card
    -- |G/M| ≤ n.
    have hquot_card : Nat.card (G ⧸ M) ≤ n := by
      have key : Nat.card G = Nat.card (G ⧸ M) * Nat.card ↥M :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup M
      have h1 : Nat.card (G ⧸ M) * 2 ≤ Nat.card G := by
        rw [key]
        exact Nat.mul_le_mul_left _ hM_card_ge_two
      omega
    -- M is a p-group (from elementary abelian structure).
    have hM_pPower : ∃ k, Nat.card ↥M = p ^ k := by
      have hPG : IsPGroup p ↥M := fun x => ⟨1, by rw [pow_one]; exact hp_elem.2 x⟩
      exact IsPGroup.iff_card.mp hPG
    -- |M| primes ⊆ {p}.
    have hM_primes : ∀ q ∈ (Nat.card ↥M).primeFactors, q = p := by
      obtain ⟨k, hk⟩ := hM_pPower
      intro q hq
      rw [hk, Nat.mem_primeFactors] at hq
      exact (Nat.prime_dvd_prime_iff_eq hq.1 hp_prime).mp (hq.1.dvd_of_dvd_pow hq.2.1)
    -- Step 1: H̄ := H.map (mk' M), K̄ := K.map (mk' M) are π-Hall in G/M.
    have hbar_hall : ∀ {S : Subgroup G}, IsHallSubgroup π S →
        IsHallSubgroup π (S.map (QuotientGroup.mk' M)) := by
      intro S hS
      refine ⟨?_, ?_⟩
      · -- |S̄| divides |S|, so primeFactors ⊆ π.
        intro q hq
        apply hS.1
        rw [Nat.mem_primeFactors] at hq ⊢
        exact ⟨hq.1, hq.2.1.trans (Subgroup.card_map_dvd _ _), Nat.card_pos.ne'⟩
      · -- S̄.index divides S.index, so primeFactors ⊆ π'.
        intro q hq
        apply hS.2
        rw [Nat.mem_primeFactors] at hq ⊢
        exact ⟨hq.1,
          hq.2.1.trans (S.index_map_dvd (QuotientGroup.mk'_surjective M)),
          Subgroup.index_ne_zero_of_finite⟩
    have h_Hbar_hall := hbar_hall hH
    have h_Kbar_hall := hbar_hall hK
    -- Step 2: IH on G/M.
    haveI : IsSolvable (G ⧸ M) := inferInstance
    obtain ⟨gbar, h_gbar⟩ := ih (G ⧸ M) hquot_card h_Hbar_hall h_Kbar_hall
    -- Step 3: Lift gbar to g.
    obtain ⟨g, hg_mk⟩ : ∃ g : G, (QuotientGroup.mk g : G ⧸ M) = gbar :=
      QuotientGroup.mk_surjective gbar
    -- Step 4: H^g ⊔ M = K ⊔ M via mk'-conj intertwining.
    have h_supeq : (H.map (MulAut.conj g).toMonoidHom) ⊔ M = K ⊔ M := by
      -- (mk' M).comp (conj g) = (conj (mk g)).comp (mk' M), so:
      -- (H.map (conj g)).map (mk' M) = H.map ((conj (mk g)).comp (mk' M))
      --   = (H.map (mk' M)).map (conj (mk g)) = H̄.map (conj gbar) = K̄
      have h_intertwine : (QuotientGroup.mk' M).comp (MulAut.conj g).toMonoidHom =
          ((MulAut.conj (QuotientGroup.mk g : G ⧸ M)).toMonoidHom).comp (QuotientGroup.mk' M) := by
        ext x
        change (QuotientGroup.mk (g * x * g⁻¹) : G ⧸ M) =
             (QuotientGroup.mk g) * (QuotientGroup.mk x) * (QuotientGroup.mk g)⁻¹
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h_quot_eq : (H.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' M) =
          K.map (QuotientGroup.mk' M) := by
        rw [Subgroup.map_map, h_intertwine, ← Subgroup.map_map, hg_mk]
        exact h_gbar
      have h_iff := (Subgroup.map_eq_map_iff (f := QuotientGroup.mk' M)).mp h_quot_eq
      rwa [QuotientGroup.ker_mk'] at h_iff
    -- Step 5: Case split on p ∈ π.
    by_cases hp_pi : p ∈ π
    · -- Case p ∈ π. M ⊆ H, M ⊆ K. So H^g · M = H^g, K · M = K. H^g = K.
      -- π-Hall maximality: |S| ∣ |T| for any π-subgroup S and π-Hall T.
      have π_hall_max : ∀ {T : Subgroup G}, IsHallSubgroup π T →
          ∀ {S : Subgroup G}, (∀ q ∈ (Nat.card ↥S).primeFactors, q ∈ π) →
          Nat.card ↥S ∣ Nat.card ↥T := by
        intro T hT S hS_pi
        have h_S_dvd_G : Nat.card ↥S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card S
        have h_cop : Nat.Coprime (Nat.card ↥S) T.index := by
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne
          obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
          rw [Nat.dvd_gcd_iff] at hq_dvd
          have hq_S_pf : q ∈ (Nat.card ↥S).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.1, Nat.card_pos.ne'⟩
          have hq_idx_pf : q ∈ T.index.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.2, Subgroup.index_ne_zero_of_finite⟩
          exact hT.2 q hq_idx_pf (hS_pi q hq_S_pf)
        have h_G_eq : Nat.card G = Nat.card ↥T * T.index := (Subgroup.card_mul_index T).symm
        rw [h_G_eq] at h_S_dvd_G
        exact h_cop.dvd_of_dvd_mul_right h_S_dvd_G
      have hM_pi : ∀ q ∈ (Nat.card ↥M).primeFactors, q ∈ π := fun q hq =>
        hM_primes q hq ▸ hp_pi
      -- |S ⊔ M| primes ⊆ π when S is π-Hall.
      have hSup_pi : ∀ {S : Subgroup G}, IsHallSubgroup π S →
          ∀ q ∈ (Nat.card ↥(S ⊔ M : Subgroup G)).primeFactors, q ∈ π := by
        intro S hS q hq
        rw [Nat.mem_primeFactors] at hq
        obtain ⟨hq_prime, hq_dvd, _⟩ := hq
        have h_card_eq : Nat.card ↥(S ⊔ M : Subgroup G) * Nat.card ↥(S ⊓ M : Subgroup G)
            = Nat.card ↥S * Nat.card ↥M := by
          have h_hk := Subgroup.card_HK_mul_card_inf_eq_card_mul_card S M
          rwa [show (↑S * ↑M : Set G) = ↑(S ⊔ M : Subgroup G) from
            (Subgroup.mul_normal S M).symm] at h_hk
        have h_dvd_prod : q ∣ Nat.card ↥S * Nat.card ↥M := by
          rw [← h_card_eq]; exact hq_dvd.mul_right _
        rcases (Nat.Prime.dvd_mul hq_prime).mp h_dvd_prod with hS_dvd | hM_dvd
        · exact hS.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, hS_dvd, Nat.card_pos.ne'⟩)
        · exact hM_pi q (Nat.mem_primeFactors.mpr ⟨hq_prime, hM_dvd, Nat.card_pos.ne'⟩)
      -- M ⊆ S for any π-Hall S (since p ∈ π).
      have hM_le_hall : ∀ {S : Subgroup G}, IsHallSubgroup π S → M ≤ S := by
        intro S hS
        have h_HM_card_dvd : Nat.card ↥(S ⊔ M : Subgroup G) ∣ Nat.card ↥S :=
          π_hall_max hS (hSup_pi hS)
        have h_S_le_SM : S ≤ S ⊔ M := le_sup_left
        have h_S_le_card : Nat.card ↥S ≤ Nat.card ↥(S ⊔ M : Subgroup G) :=
          Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective h_S_le_SM)
        have h_card_eq : Nat.card ↥(S ⊔ M : Subgroup G) = Nat.card ↥S :=
          Nat.le_antisymm (Nat.le_of_dvd Nat.card_pos h_HM_card_dvd) h_S_le_card
        have h_SM_eq : (S ⊔ M : Subgroup G) = S :=
          (Subgroup.eq_of_le_of_card_ge h_S_le_SM h_card_eq.le).symm
        intro x hxM
        have : x ∈ (S ⊔ M : Subgroup G) := Subgroup.mem_sup_right hxM
        rwa [h_SM_eq] at this
      have hM_le_H : M ≤ H := hM_le_hall hH
      have hM_le_K : M ≤ K := hM_le_hall hK
      -- M ⊴ G + M ≤ H ⇒ M ≤ H^g.
      have hM_le_Hg : M ≤ H.map (MulAut.conj g).toMonoidHom := by
        intro x hxM
        rw [Subgroup.mem_map]
        refine ⟨g⁻¹ * x * g, ?_, by
          change g * (g⁻¹ * x * g) * g⁻¹ = x
          group⟩
        apply hM_le_H
        have := hMnormal.conj_mem x hxM g⁻¹
        simpa using this
      -- H^g · M = H^g, K · M = K. Conclude H^g = K.
      have h_HMg_eq : (H.map (MulAut.conj g).toMonoidHom) ⊔ M =
          H.map (MulAut.conj g).toMonoidHom := sup_eq_left.mpr hM_le_Hg
      have h_KM_eq : K ⊔ M = K := sup_eq_left.mpr hM_le_K
      refine ⟨g, ?_⟩
      rw [← h_HMg_eq, h_supeq, h_KM_eq]
    · -- Case p ∉ π. H ∩ M = ⊥, K ∩ M = ⊥. Apply SZ conjugacy in HM.
      -- Helper: any π-Hall S has S ⊓ M = ⊥ (coprime orders).
      have h_inter_bot : ∀ {S : Subgroup G}, IsHallSubgroup π S →
          (S ⊓ M : Subgroup G) = ⊥ := by
        intro S hS
        apply Subgroup.eq_bot_of_card_eq
        have h_dvd_S : Nat.card ↥(S ⊓ M : Subgroup G) ∣ Nat.card ↥S :=
          Subgroup.card_dvd_of_le inf_le_left
        have h_dvd_M : Nat.card ↥(S ⊓ M : Subgroup G) ∣ Nat.card ↥M :=
          Subgroup.card_dvd_of_le inf_le_right
        have h_cop : Nat.Coprime (Nat.card ↥S) (Nat.card ↥M) := by
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne
          obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
          rw [Nat.dvd_gcd_iff] at hq_dvd
          have hq_S_pf : q ∈ (Nat.card ↥S).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.1, Nat.card_pos.ne'⟩
          have hq_M_pf : q ∈ (Nat.card ↥M).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.2, Nat.card_pos.ne'⟩
          exact hp_pi (hM_primes q hq_M_pf ▸ hS.1 q hq_S_pf)
        have h := Nat.dvd_gcd h_dvd_S h_dvd_M
        rw [h_cop] at h
        exact Nat.dvd_one.mp h
      -- Hg := H^g is also π-Hall (conjugation preserves cardinality and index).
      set Hg : Subgroup G := H.map (MulAut.conj g).toMonoidHom with hHg_def
      have h_Hg_card : Nat.card ↥Hg = Nat.card ↥H :=
        Nat.card_congr (Subgroup.equivMapOfInjective H _
          (MulEquiv.injective _)).toEquiv.symm
      have h_Hg_index : Hg.index = H.index := Subgroup.index_map_equiv H (MulAut.conj g)
      have hHg_hall : IsHallSubgroup π Hg := by
        refine ⟨?_, ?_⟩
        · intro q hq
          apply hH.1
          rwa [h_Hg_card] at hq
        · intro q hq
          apply hH.2
          rwa [h_Hg_index] at hq
      have h_Hg_inter_M : (Hg ⊓ M : Subgroup G) = ⊥ := h_inter_bot hHg_hall
      have h_K_inter_M : (K ⊓ M : Subgroup G) = ⊥ := h_inter_bot hK
      -- HM := Hg ⊔ M = K ⊔ M (from h_supeq).
      set HM : Subgroup G := Hg ⊔ M with hHM_def
      have hM_le_HM : M ≤ HM := le_sup_right
      have hHg_le_HM : Hg ≤ HM := le_sup_left
      have hK_le_HM : K ≤ HM := h_supeq.symm ▸ (le_sup_left : K ≤ K ⊔ M)
      -- Setup in ↥HM: N' := M.subgroupOf HM.
      haveI hHM_finite : Finite ↥HM := inferInstance
      haveI hM_subgroupOf_normal : (M.subgroupOf HM).Normal :=
        Subgroup.normal_subgroupOf
      -- N' ≃ M (since M ≤ HM).
      have h_M_card_eq : Nat.card ↥(M.subgroupOf HM) = Nat.card ↥M :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM_le_HM).toEquiv
      -- Construct IsComplement' (M.subgroupOf HM) (Hg.subgroupOf HM) in ↥HM.
      have h_compl_Hg : Subgroup.IsComplement' (M.subgroupOf HM) (Hg.subgroupOf HM) := by
        apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
        · -- Disjoint via M ⊓ Hg = ⊥.
          rw [disjoint_iff]
          ext ⟨x, hx⟩
          simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot,
                     Subtype.ext_iff, OneMemClass.coe_one]
          refine ⟨fun ⟨hxM, hxHg⟩ => ?_, fun h => by simp [h]⟩
          have : x ∈ (M ⊓ Hg : Subgroup G) := ⟨hxM, hxHg⟩
          rw [show (M ⊓ Hg : Subgroup G) = ⊥ by rw [inf_comm]; exact h_Hg_inter_M,
            Subgroup.mem_bot] at this
          exact this
        · -- Product covers ↥HM: ∀ x : HM, ∃ m ∈ M, h ∈ Hg, m * h = x.
          rw [Set.eq_univ_iff_forall]
          rintro ⟨x, hx_HM⟩
          -- x ∈ HM = Hg ⊔ M. Decompose: ∃ h ∈ Hg, m ∈ M, x = h * m (Hg.normalizes M or M ⊴ G).
          have hx_sup : x ∈ (Hg ⊔ M : Subgroup G) := hx_HM
          rw [Subgroup.mem_sup_of_normal_right] at hx_sup
          obtain ⟨h, hhHg, m, hmM, h_eq⟩ := hx_sup
          -- x = h * m. Use normality to rewrite it as m' * h,
          -- with m' := h * m * h⁻¹ ∈ M.
          refine ⟨⟨h * m * h⁻¹, ?_⟩,
            Subgroup.mem_subgroupOf.mpr (hMnormal.conj_mem m hmM h), ⟨h, ?_⟩,
            Subgroup.mem_subgroupOf.mpr hhHg, ?_⟩
          · exact hM_le_HM (hMnormal.conj_mem m hmM h)
          · exact hHg_le_HM hhHg
          · ext
            change h * m * h⁻¹ * h = x
            rw [← h_eq]
            group
      -- Similarly for K.
      have h_compl_K : Subgroup.IsComplement' (M.subgroupOf HM) (K.subgroupOf HM) := by
        apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
        · rw [disjoint_iff]
          ext ⟨x, hx⟩
          simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot,
                     Subtype.ext_iff, OneMemClass.coe_one]
          refine ⟨fun ⟨hxM, hxK⟩ => ?_, fun h => by simp [h]⟩
          have : x ∈ (M ⊓ K : Subgroup G) := ⟨hxM, hxK⟩
          rw [show (M ⊓ K : Subgroup G) = ⊥ by rw [inf_comm]; exact h_K_inter_M,
            Subgroup.mem_bot] at this
          exact this
        · rw [Set.eq_univ_iff_forall]
          rintro ⟨x, hx_HM⟩
          have hx_sup : x ∈ (K ⊔ M : Subgroup G) := by rw [← h_supeq]; exact hx_HM
          rw [Subgroup.mem_sup_of_normal_right] at hx_sup
          obtain ⟨h, hhK, m, hmM, h_eq⟩ := hx_sup
          refine ⟨⟨h * m * h⁻¹, ?_⟩,
            Subgroup.mem_subgroupOf.mpr (hMnormal.conj_mem m hmM h), ⟨h, ?_⟩,
            Subgroup.mem_subgroupOf.mpr hhK, ?_⟩
          · exact hM_le_HM (hMnormal.conj_mem m hmM h)
          · exact hK_le_HM hhK
          · ext
            change h * m * h⁻¹ * h = x
            rw [← h_eq]
            group
      -- M.subgroupOf HM has solvable structure (M abelian / p-group).
      haveI hM_solv : IsSolvable ↥(M.subgroupOf HM) := by
        have h_iso := Subgroup.subgroupOfEquivOfLe hM_le_HM
        exact solvable_of_solvable_injective (f := h_iso.toMonoidHom) h_iso.injective
      -- Coprime: |M.subgroupOf HM| coprime its index.
      have h_HM_card : Nat.card ↥HM = Nat.card ↥Hg * Nat.card ↥M := by
        have h_hk := Subgroup.card_HK_mul_card_inf_eq_card_mul_card Hg M
        rw [show Hg ⊓ M = (⊥ : Subgroup G) from h_Hg_inter_M, Subgroup.card_bot,
            mul_one] at h_hk
        have h_set : (↑Hg * ↑M : Set G) = (↑HM : Set G) := by
          rw [← Subgroup.mul_normal, ← hHM_def]
        rw [h_set] at h_hk
        omega
      have h_M_idx_HM : (M.subgroupOf HM).index = Nat.card ↥Hg := by
        have h1 : Nat.card ↥(M.subgroupOf HM) * (M.subgroupOf HM).index = Nat.card ↥HM :=
          (M.subgroupOf HM).card_mul_index
        rw [h_M_card_eq, h_HM_card] at h1
        -- h1 : |M| · idx = |Hg| · |M|.
        have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
        have h2 : Nat.card ↥M * (M.subgroupOf HM).index = Nat.card ↥M * Nat.card ↥Hg := by
          rw [h1]; ring
        exact Nat.eq_of_mul_eq_mul_left hM_pos h2
      have h_cop : Nat.Coprime (Nat.card ↥(M.subgroupOf HM)) (M.subgroupOf HM).index := by
        rw [h_M_card_eq, h_M_idx_HM]
        -- gcd(|M|, |Hg|) = gcd(p-power, π-Hall) = 1.
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
        rw [Nat.dvd_gcd_iff] at hq_dvd
        have hq_M_pf : q ∈ (Nat.card ↥M).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.1, Nat.card_pos.ne'⟩
        have hq_Hg_pf : q ∈ (Nat.card ↥Hg).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.2, Nat.card_pos.ne'⟩
        exact hp_pi (hM_primes q hq_M_pf ▸ hHg_hall.1 q hq_Hg_pf)
      -- Apply SZ conjugacy (Phase 1).
      obtain ⟨n_HM, hn_HM_mem, hn_eq⟩ :=
        Subgroup.IsComplement'.exists_conj_of_coprime h_cop (Or.inl hM_solv)
          h_compl_Hg h_compl_K
      -- Lift n_HM ∈ M.subgroupOf HM to m ∈ M (via HM.subtype + subgroupOf membership).
      let m : G := n_HM.val
      have hm_M : m ∈ M := Subgroup.mem_subgroupOf.mp hn_HM_mem
      -- Push hn_eq via HM.subtype: Hg.map (conj m) = K.
      have h_Hg_conj_m : Hg.map (MulAut.conj m).toMonoidHom = K := by
        have h_intertwine : HM.subtype.comp ((MulAut.conj n_HM).toMonoidHom) =
            ((MulAut.conj (n_HM.val : G)).toMonoidHom).comp HM.subtype := by
          ext ⟨x, hx⟩; rfl
        have h_lhs : (((Hg.subgroupOf HM).map (MulAut.conj n_HM).toMonoidHom).map
            HM.subtype) = Hg.map (MulAut.conj m).toMonoidHom := by
          rw [Subgroup.map_map, h_intertwine, ← Subgroup.map_map]
          congr 1
          rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype,
              inf_of_le_right hHg_le_HM]
        have h_rhs : ((K.subgroupOf HM).map HM.subtype) = K := by
          rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype,
              inf_of_le_right hK_le_HM]
        have := congrArg (·.map HM.subtype) hn_eq
        rw [h_lhs, h_rhs] at this
        exact this
      -- K = H^(m * g) via composition.
      refine ⟨m * g, ?_⟩
      have hcomp : (MulAut.conj (m * g)).toMonoidHom =
            (MulAut.conj m).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
        ext x
        change m * g * x * (m * g)⁻¹ = m * (g * x * g⁻¹) * m⁻¹
        group
      rw [hcomp, ← Subgroup.map_map]
      exact h_Hg_conj_m

/-- **Isaacs Thm 3.14 Hall-C**: `G` 可解 ⇒ 任意の `π`-Hall 部分群対は共役.

Phase 2 (2026-05-23) で完成. Phase 1 (Isaacs Thm 3.12 SZ 共役性) を前提に
`hall_C_strong_aux` 経由で `|G|`-強誘導.

主結果: `∃ g : G, H.map (MulAut.conj g).toMonoidHom = K` (即ち `H^g = K`).
共役元 `g` は一般に `G` 全体 (`N` の部分集合とは限らない). -/
theorem hall_C [Finite G] [IsSolvable G] {π : Set ℕ} {H K : Subgroup G}
    (hH : IsHallSubgroup π H) (hK : IsHallSubgroup π K) :
    ∃ g : G, H.map (MulAut.conj g).toMonoidHom = K :=
  hall_C_strong_aux (Nat.card G) G le_rfl hH hK

/-- The conjugation action on Hall `π`-subgroups of a finite solvable group is transitive. -/
theorem HallSubgroups.conjAction_pretransitive [Finite G] [IsSolvable G] (π : Set ℕ) :
    MulAction.IsPretransitive G (HallSubgroups π G) := by
  constructor
  intro H K
  obtain ⟨g, hg⟩ := hall_C (π := π) H.2 K.2
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change MulAut.conj g • H.1 = K.1
  rw [show (MulAut.conj g • H.1 : Subgroup G) =
      H.1.map (MulAut.conj g : G →* G) by
    rw [Subgroup.pointwise_smul_def]
    rfl]
  exact hg

/-- A normal `π`-Hall subgroup of a finite solvable group is the unique `π`-Hall subgroup.
This is the standard immediate consequence of Hall conjugacy: every other `π`-Hall subgroup is a
conjugate of the normal one, hence is equal to it. -/
theorem IsHallSubgroup.eq_of_normal [Finite G] [IsSolvable G] {π : Set ℕ} {H K : Subgroup G}
    (hH : IsHallSubgroup π H) (hK : IsHallSubgroup π K) (hN : H.Normal) : H = K := by
  haveI := hN
  obtain ⟨g, hg⟩ := hall_C hH hK
  rw [← hg]
  exact (Subgroup.Normal.conj_smul_eq_self g H).symm

/-- **Schur-Zassenhaus D-part (抽象版)**: `M ⊴ G` が可解で補群 `K` を持つとき, `|M|` と
位数が互いに素な部分群 `U` は `K` の共役 `Kˣ` に含まれる.

Hall D-定理 (`hall_D`) のエンジン. 証明: `P := U ⊔ M` の中で `U` も `P ⊓ K` も
正規部分群 `M.subgroupOf P` (index は `|U|`, よって `|M|` と互いに素) の補群になる.
Schur-Zassenhaus 共役性 (`IsComplement'.exists_conj_of_coprime`) を `P` 内で適用すると,
`P ⊓ K` の (`M` の元による) 共役が `U` に一致するので, `U = (P ⊓ K)ᵐ ≤ Kᵐ`. -/
theorem exists_conj_le_of_isComplement'_of_coprime [Finite G] {M K : Subgroup G} [M.Normal]
    (hMsolv : IsSolvable ↥M) (hK : M.IsComplement' K) {U : Subgroup G}
    (hcop : Nat.Coprime (Nat.card ↥U) (Nat.card ↥M)) :
    ∃ x : G, U ≤ K.map (MulAut.conj x).toMonoidHom := by
  set P : Subgroup G := U ⊔ M with hP_def
  have hM_le_P : M ≤ P := le_sup_right
  have hU_le_P : U ≤ P := le_sup_left
  have hMnorm : M.Normal := inferInstance
  haveI hMP_normal : (M.subgroupOf P).Normal := Subgroup.normal_subgroupOf
  have hU_inf_M : (U ⊓ M : Subgroup G) = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hM_inf_K : (M ⊓ K : Subgroup G) = ⊥ := hK.disjoint.eq_bot
  have h_card_MP : Nat.card ↥(M.subgroupOf P) = Nat.card ↥M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM_le_P).toEquiv
  have h_card_UP : Nat.card ↥(U.subgroupOf P) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU_le_P).toEquiv
  -- Complement 1: `U.subgroupOf P` complements `M.subgroupOf P` in `P`.
  have h_compl_U : Subgroup.IsComplement' (M.subgroupOf P) (U.subgroupOf P) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot,
                 Subtype.ext_iff, OneMemClass.coe_one]
      refine ⟨fun ⟨hxM, hxU⟩ => ?_, fun h => by simp [h]⟩
      have : x ∈ (U ⊓ M : Subgroup G) := ⟨hxU, hxM⟩
      rwa [hU_inf_M, Subgroup.mem_bot] at this
    · rw [Set.eq_univ_iff_forall]
      rintro ⟨x, hx_P⟩
      have hx_sup : x ∈ (U ⊔ M : Subgroup G) := hx_P
      rw [Subgroup.mem_sup_of_normal_right] at hx_sup
      obtain ⟨u, huU, m, hmM, h_eq⟩ := hx_sup
      refine ⟨⟨u * m * u⁻¹, hM_le_P (hMnorm.conj_mem m hmM u)⟩,
        Subgroup.mem_subgroupOf.mpr (hMnorm.conj_mem m hmM u), ⟨u, hU_le_P huU⟩,
        Subgroup.mem_subgroupOf.mpr huU, ?_⟩
      ext; change u * m * u⁻¹ * u = x; rw [← h_eq]; group
  -- Complement 2: `K.subgroupOf P` (= `(P ⊓ K).subgroupOf P`) complements `M.subgroupOf P`.
  have h_compl_K : Subgroup.IsComplement' (M.subgroupOf P) (K.subgroupOf P) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot,
                 Subtype.ext_iff, OneMemClass.coe_one]
      refine ⟨fun ⟨hxM, hxK⟩ => ?_, fun h => by simp [h]⟩
      have : x ∈ (M ⊓ K : Subgroup G) := ⟨hxM, hxK⟩
      rwa [hM_inf_K, Subgroup.mem_bot] at this
    · rw [Set.eq_univ_iff_forall]
      rintro ⟨x, hx_P⟩
      have hx_top : x ∈ (M ⊔ K : Subgroup G) := by rw [hK.sup_eq_top]; trivial
      rw [Subgroup.mem_sup_of_normal_left] at hx_top
      obtain ⟨m, hmM, k, hkK, h_eq⟩ := hx_top
      have hk_P : k ∈ P := by
        have hkeq : k = m⁻¹ * x := by rw [← h_eq]; group
        rw [hkeq]; exact P.mul_mem (P.inv_mem (hM_le_P hmM)) hx_P
      refine ⟨⟨m, hM_le_P hmM⟩, Subgroup.mem_subgroupOf.mpr hmM, ⟨k, hk_P⟩,
        Subgroup.mem_subgroupOf.mpr hkK, ?_⟩
      ext; exact h_eq
  -- index of `M.subgroupOf P` in `P` is `|U|`, hence coprime to `|M|`.
  have h_idx_MP : (M.subgroupOf P).index = Nat.card ↥U := by
    rw [h_compl_U.symm.index_eq_card, h_card_UP]
  have h_cop_MP : Nat.Coprime (Nat.card ↥(M.subgroupOf P)) (M.subgroupOf P).index := by
    rw [h_card_MP, h_idx_MP]; exact hcop.symm
  haveI hMP_solv : IsSolvable ↥(M.subgroupOf P) := by
    have h_iso := Subgroup.subgroupOfEquivOfLe hM_le_P
    exact solvable_of_solvable_injective (f := h_iso.toMonoidHom) h_iso.injective
  -- SZ conjugacy in `P`: conjugate `K.subgroupOf P` to `U.subgroupOf P` by `n ∈ M.subgroupOf P`.
  obtain ⟨n, hn_mem, hn_eq⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime h_cop_MP (Or.inl hMP_solv) h_compl_K h_compl_U
  let m : G := n.val
  refine ⟨m, ?_⟩
  -- Push `hn_eq` through `P.subtype`: `(P ⊓ K)ᵐ = U`, hence `U ≤ Kᵐ`.
  have h_intertwine : P.subtype.comp (MulAut.conj n).toMonoidHom =
      ((MulAut.conj (n.val : G)).toMonoidHom).comp P.subtype := by
    ext ⟨x, hx⟩; rfl
  have h_lhs : (((K.subgroupOf P).map (MulAut.conj n).toMonoidHom).map P.subtype) =
      (P ⊓ K).map (MulAut.conj m).toMonoidHom := by
    rw [Subgroup.map_map, h_intertwine, ← Subgroup.map_map]
    congr 1
    rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype]
  have h_rhs : ((U.subgroupOf P).map P.subtype) = U := by
    rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype,
        inf_of_le_right hU_le_P]
  have h_eq_lifted := congrArg (·.map P.subtype) hn_eq
  rw [h_lhs, h_rhs] at h_eq_lifted
  rw [← h_eq_lifted]
  exact Subgroup.map_mono inf_le_right

/-- Hall D-定理の `|G|`-強誘導本体. `hall_E_strong_aux` と同じ骨格 (極小正規 `M`,
`G/M` への IH, `p ∈ π` / `p ∉ π` 場合分け) に, 「IH は `U` の像を含む π-Hall を返す」
+「`p ∉ π` では補群を `U` を含むものに取り替える (`exists_conj_le_of_isComplement'_of_coprime`)」
の 2 点を加えたもの. -/
private theorem hall_D_strong_aux : ∀ n : ℕ,
    ∀ (G : Type*) [Group G] [Finite G] [IsSolvable G],
      Nat.card G ≤ n → ∀ {π : Set ℕ} {U : Subgroup G},
      (∀ q ∈ (Nat.card ↥U).primeFactors, q ∈ π) →
      ∃ H : Subgroup G, IsHallSubgroup π H ∧ U ≤ H := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ hcard _ _ _
    exact absurd hcard (Nat.not_le_of_lt Nat.card_pos)
  | succ n ih =>
    intro G _ _ _ hcard π U hU
    by_cases hsmall : Nat.card G ≤ n
    · exact ih G hsmall hU
    by_cases hG_one : Nat.card G = 1
    · -- |G| = 1: G subsingleton, so U ≤ ⊥; take H = ⊥.
      haveI : Subsingleton G := Nat.card_eq_one_iff_unique.mp hG_one |>.1
      refine ⟨⊥, IsHallSubgroup.bot_of_card_eq_one π hG_one, ?_⟩
      intro x _
      rw [Subgroup.mem_bot]; exact Subsingleton.elim x 1
    haveI hG_nontrivial : Nontrivial G :=
      Finite.one_lt_card_iff_nontrivial.mp
        (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.card_pos.ne', hG_one⟩)
    obtain ⟨M, hM, _⟩ :=
      OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
    haveI hMnormal : M.Normal := hM.1
    have hM_ne_bot : M ≠ ⊥ := hM.2.1
    obtain ⟨p, hp_prime, hp_elem⟩ := solvable_minimal_normal_isElementaryAbelian hM
    haveI hM_nontrivial : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
    have hM_card_ge_two : 2 ≤ Nat.card ↥M := Finite.one_lt_card
    have hquot_card : Nat.card (G ⧸ M) ≤ n := by
      have key : Nat.card G = Nat.card (G ⧸ M) * Nat.card ↥M :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup M
      have h1 : Nat.card (G ⧸ M) * 2 ≤ Nat.card G := by
        rw [key]; exact Nat.mul_le_mul_left _ hM_card_ge_two
      omega
    -- |M| is a p-power; its prime factors are {p}.
    have hM_pPower : ∃ k, Nat.card ↥M = p ^ k := by
      haveI : Fact p.Prime := ⟨hp_prime⟩
      have hPG : IsPGroup p ↥M := fun x => ⟨1, by rw [pow_one]; exact hp_elem.2 x⟩
      exact IsPGroup.iff_card.mp hPG
    have hM_primes : ∀ q ∈ (Nat.card ↥M).primeFactors, q = p := by
      obtain ⟨k, hk⟩ := hM_pPower
      intro q hq
      rw [hk, Nat.mem_primeFactors] at hq
      exact (Nat.prime_dvd_prime_iff_eq hq.1 hp_prime).mp (hq.1.dvd_of_dvd_pow hq.2.1)
    -- IH on G/M with the π-subgroup `U.map (mk' M)`: get a π-Hall ⊇ image of U.
    set Ubar : Subgroup (G ⧸ M) := U.map (QuotientGroup.mk' M) with hUbar_def
    have hUbar_pi : ∀ q ∈ (Nat.card ↥Ubar).primeFactors, q ∈ π := by
      intro q hq
      apply hU
      rw [Nat.mem_primeFactors] at hq ⊢
      exact ⟨hq.1, hq.2.1.trans (Subgroup.card_map_dvd _ _), Nat.card_pos.ne'⟩
    obtain ⟨Hbar, hHbar, hUbar_le⟩ := ih (G ⧸ M) hquot_card hUbar_pi
    -- Pull back: H = comap (mk' M) Hbar contains both M and U.
    set H : Subgroup G := Subgroup.comap (QuotientGroup.mk' M) Hbar with hH_def
    have hM_le_H : M ≤ H := QuotientGroup.le_comap_mk' M Hbar
    have hU_le_H : U ≤ H := by
      intro u hu
      rw [hH_def, Subgroup.mem_comap]
      exact hUbar_le (Subgroup.mem_map_of_mem _ hu)
    have hH_index : H.index = Hbar.index :=
      Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective (N := M))
    have hHbar_idx_pos : 0 < Hbar.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hH_card_eq : Nat.card ↥H = Nat.card ↥Hbar * Nat.card ↥M := by
      have eq1 : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
      have eq2 : Nat.card ↥Hbar * Hbar.index = Nat.card (G ⧸ M) := Subgroup.card_mul_index Hbar
      have eq3 : Nat.card (G ⧸ M) * Nat.card ↥M = Nat.card G :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup M).symm
      have h_eq : Nat.card ↥H * Hbar.index = (Nat.card ↥Hbar * Nat.card ↥M) * Hbar.index := by
        calc Nat.card ↥H * Hbar.index
            = Nat.card ↥H * H.index := by rw [hH_index]
          _ = Nat.card G := eq1
          _ = Nat.card (G ⧸ M) * Nat.card ↥M := eq3.symm
          _ = (Nat.card ↥Hbar * Hbar.index) * Nat.card ↥M := by rw [eq2]
          _ = (Nat.card ↥Hbar * Nat.card ↥M) * Hbar.index := by ring
      exact Nat.mul_right_cancel hHbar_idx_pos h_eq
    by_cases hp_pi : p ∈ π
    · -- Case p ∈ π: H is a Hall π-subgroup of G and U ≤ H.
      refine ⟨H, ⟨?_, ?_⟩, hU_le_H⟩
      · intro q hq_pf
        rw [hH_card_eq, Nat.mem_primeFactors] at hq_pf
        obtain ⟨hq_prime, hq_dvd, _⟩ := hq_pf
        rcases hq_prime.dvd_mul.mp hq_dvd with h_in_Hbar | h_in_M
        · exact hHbar.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_Hbar, Nat.card_pos.ne'⟩)
        · have hqM : q ∈ (Nat.card ↥M).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_M, Nat.card_pos.ne'⟩
          rw [hM_primes q hqM]; exact hp_pi
      · rw [hH_index]; exact hHbar.2
    · -- Case p ∉ π: replace a complement of `M.subgroupOf H` by one containing `U`.
      have hMH_card : Nat.card ↥(M.subgroupOf H) = Nat.card ↥M :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM_le_H).toEquiv
      have h_coprime_M_Hbar : Nat.Coprime (Nat.card ↥M) (Nat.card ↥Hbar) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
        rw [Nat.dvd_gcd_iff] at hq_dvd
        have hqM : q ∈ (Nat.card ↥M).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.1, Nat.card_pos.ne'⟩
        have hqHbar : q ∈ (Nat.card ↥Hbar).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.2, Nat.card_pos.ne'⟩
        exact hp_pi (hM_primes q hqM ▸ hHbar.1 q hqHbar)
      have h_idx_MH : (M.subgroupOf H).index = Nat.card ↥Hbar := by
        have hlag : Nat.card ↥(M.subgroupOf H) * (M.subgroupOf H).index = Nat.card ↥H :=
          Subgroup.card_mul_index (M.subgroupOf H)
        rw [hMH_card, hH_card_eq] at hlag
        have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
        have : Nat.card ↥M * (M.subgroupOf H).index = Nat.card ↥M * Nat.card ↥Hbar := by
          rw [hlag, mul_comm (Nat.card ↥Hbar)]
        exact Nat.mul_left_cancel hM_pos this
      have h_cop_MH : Nat.Coprime (Nat.card ↥(M.subgroupOf H)) (M.subgroupOf H).index := by
        rw [hMH_card, h_idx_MH]; exact h_coprime_M_Hbar
      haveI hMH_normal : (M.subgroupOf H).Normal := hMnormal.subgroupOf H
      haveI hMH_solv : IsSolvable ↥(M.subgroupOf H) := by
        have h_iso := Subgroup.subgroupOfEquivOfLe hM_le_H
        exact solvable_of_solvable_injective (f := h_iso.toMonoidHom) h_iso.injective
      obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime h_cop_MH
      -- `U.subgroupOf H` is a π-subgroup with order coprime to `|M.subgroupOf H|`.
      have hUH_card : Nat.card ↥(U.subgroupOf H) = Nat.card ↥U :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU_le_H).toEquiv
      have h_cop_UH_MH :
          Nat.Coprime (Nat.card ↥(U.subgroupOf H)) (Nat.card ↥(M.subgroupOf H)) := by
        rw [hUH_card, hMH_card, Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
        rw [Nat.dvd_gcd_iff] at hq_dvd
        have hqU : q ∈ (Nat.card ↥U).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.1, Nat.card_pos.ne'⟩
        have hqM : q ∈ (Nat.card ↥M).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.2, Nat.card_pos.ne'⟩
        exact hp_pi (hM_primes q hqM ▸ hU q hqU)
      -- SZ-D: `U.subgroupOf H` lies in a conjugate `K' = K.map (conj x)` of `K`.
      obtain ⟨x, hx⟩ := exists_conj_le_of_isComplement'_of_coprime hMH_solv hK h_cop_UH_MH
      set K' : Subgroup ↥H := K.map (MulAut.conj x).toMonoidHom with hK'_def
      have hK'_card : Nat.card ↥K' = Nat.card ↥K :=
        Nat.card_congr (Subgroup.equivMapOfInjective K _ (MulEquiv.injective _)).toEquiv.symm
      have hK'_index : K'.index = K.index := Subgroup.index_map_equiv K (MulAut.conj x)
      have hK_index : K.index = Nat.card ↥(M.subgroupOf H) := hK.index_eq_card
      have hK_card : Nat.card ↥K = Nat.card ↥Hbar := by
        have hcm := hK.card_mul
        rw [hMH_card, hH_card_eq] at hcm
        have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
        have h_eq : Nat.card ↥M * Nat.card ↥K = Nat.card ↥M * Nat.card ↥Hbar := by
          rw [hcm, mul_comm]
        exact Nat.mul_left_cancel hM_pos h_eq
      -- `K'.map H.subtype` is the desired Hall π-subgroup of G, and contains U.
      refine ⟨K'.map H.subtype, ⟨?_, ?_⟩, ?_⟩
      · intro q hq_pf
        rw [Subgroup.card_subtype, hK'_card, hK_card] at hq_pf
        exact hHbar.1 q hq_pf
      · intro q hq_pf hq_pi
        rw [show (K'.map H.subtype).index = Nat.card ↥M * Hbar.index from ?_] at hq_pf
        · rw [Nat.mem_primeFactors] at hq_pf
          obtain ⟨hq_prime, hq_dvd, _⟩ := hq_pf
          rcases hq_prime.dvd_mul.mp hq_dvd with h_in_M | h_in_HbarIdx
          · have hqM : q ∈ (Nat.card ↥M).primeFactors :=
              Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_M, Nat.card_pos.ne'⟩
            rw [hM_primes q hqM] at hq_pi; exact hp_pi hq_pi
          · exact hHbar.2 q (Nat.mem_primeFactors.mpr
              ⟨hq_prime, h_in_HbarIdx, Subgroup.index_ne_zero_of_finite⟩) hq_pi
        · rw [Subgroup.index_map, Subgroup.ker_subtype, sup_bot_eq, hK'_index, hK_index,
              hMH_card, Subgroup.range_subtype, hH_index]
      · calc U = (U.subgroupOf H).map H.subtype := by
                rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype,
                    inf_of_le_right hU_le_H]
          _ ≤ K'.map H.subtype := Subgroup.map_mono hx

/-- **Isaacs 3C.1 (Hall D-定理, Wielandt)** ⭐: 有限可解群では, 任意の `π`-部分群は
ある Hall `π`-部分群に含まれる.

`U` を `π`-部分群 (`|U|` の全素因子が `π` に属す) とすると, `U ≤ H` なる `π`-Hall `H` が存在.
Hall E (`hall_E_exists`) / Hall C (`hall_C`) と合わせて Hall E-C-D を完備化する.
証明は `hall_E_strong_aux` と同型の `|G|`-強誘導 (`hall_D_strong_aux`). -/
theorem hall_D [Finite G] [IsSolvable G] {π : Set ℕ} {U : Subgroup G}
    (hU : ∀ q ∈ (Nat.card ↥U).primeFactors, q ∈ π) :
    ∃ H : Subgroup G, IsHallSubgroup π H ∧ U ≤ H :=
  hall_D_strong_aux (Nat.card G) G le_rfl hU

/-- `N ⊴ G` のとき, 任意の `H` について `[N : H ∩ N] = H.relIndex N` は `[G : H] = H.index`
を割る. (mathlib `relIndex_dvd_index_of_normal` は正規部分群側の relindex を扱うので, その
「右版」を指数の塔等式 + 第二同型から導く.)

`[G:H]·[H:H∩N] = [G:N]·[N:H∩N]` (どちらも `[G:H∩N]`), かつ `[H:H∩N] ∣ [G:N]` (正規) より
`[N:H∩N] ∣ [G:H]`. -/
theorem relIndex_dvd_index_of_normal_right [Finite G] (H : Subgroup G) {N : Subgroup G}
    [N.Normal] : H.relIndex N ∣ H.index := by
  -- (H⊓N).relIndex H * H.index = [G:H∩N] と (H⊓N).relIndex N * N.index = [G:H∩N].
  have hA : N.relIndex H * H.index = (H ⊓ N : Subgroup G).index := by
    rw [← Subgroup.inf_relIndex_left]; exact Subgroup.relIndex_mul_index inf_le_left
  have hB : H.relIndex N * N.index = (H ⊓ N : Subgroup G).index := by
    rw [← Subgroup.inf_relIndex_right]; exact Subgroup.relIndex_mul_index inf_le_right
  -- [H:H∩N] = N.relIndex H ∣ [G:N] = N.index (正規).
  obtain ⟨t, ht⟩ : N.relIndex H ∣ N.index := Subgroup.relIndex_dvd_index_of_normal N H
  have hb_ne : N.relIndex H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hA
    exact Subgroup.index_ne_zero_of_finite hA.symm
  -- N.relIndex H * H.index = N.relIndex H * (H.relIndex N * t).
  have key : N.relIndex H * H.index = N.relIndex H * (H.relIndex N * t) := by
    rw [hA, ← hB, ht]; ring
  exact ⟨t, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hb_ne) key⟩

/-- **Hall ∩ normal**: `H` が `G` の `π`-Hall 部分群, `N ⊴ G` なら `H ∩ N` (= `N` 内で
`H.subgroupOf N`) は `N` の `π`-Hall 部分群.

`|H ∩ N| ∣ |H|` なので素因子は `π` に含まれ, `[N : H∩N] ∣ [G:H] = index H` (π'-number,
`relIndex_dvd_index_of_normal_right`) なので余指数の素因子は `π` の外. BG Cor 10.9 で
`W ∩ M'` / `W ∩ M_σ` が `M'` / `M_σ` の Hall になることに使う. -/
theorem isHallSubgroup_subgroupOf_of_normal [Finite G] {π : Set ℕ} {H N : Subgroup G}
    (hH : IsHallSubgroup π H) [N.Normal] :
    IsHallSubgroup π (H.subgroupOf N) := by
  have hcard : Nat.card ↥(H.subgroupOf N) = Nat.card ↥(H ⊓ N : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  refine ⟨?_, ?_⟩
  · -- |H.subgroupOf N| = |H ⊓ N| ∣ |H|, so prime factors ⊆ π.
    intro q hq
    rw [hcard] at hq
    apply hH.1
    rw [Nat.mem_primeFactors] at hq ⊢
    exact ⟨hq.1, hq.2.1.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩
  · -- index = H.relIndex N ∣ H.index, so prime factors ⊆ π'.
    intro q hq hqπ
    have hdvd : (H.subgroupOf N).index ∣ H.index := relIndex_dvd_index_of_normal_right H
    rw [Nat.mem_primeFactors] at hq
    exact hH.2 q (Nat.mem_primeFactors.mpr
      ⟨hq.1, hq.2.1.trans hdvd, Subgroup.index_ne_zero_of_finite⟩) hqπ

/-! **Isaacs Thm 3.15**: 全ての素数 `p` について `p`-complement (i.e., `{p}'`-Hall) が
存在 ⇒ `G` 可解.

**Forward dep**: Burnside `p^a q^b` 経由. Ch.7 完成後に back-fill.
所在: `OddOrder/Isaacs/Ch07_ThompsonSubgroup/ForwardFromCh03.lean` (placeholder).
詳細は [`notes/isaacs/ch07_burnside.md`](../../notes/isaacs/ch07_burnside.md). -/

/-- **Isaacs Lemma 3.16**: `|G:H|`, `|G:K|` が coprime ⇒ `G = HK` (i.e., `H ⊔ K = ⊤`).

証明: `(H ⊔ K).index` は `H.index` と `K.index` の両方を割り切るので gcd を割り切る.
gcd は 1 なので `(H ⊔ K).index = 1`, 故に `H ⊔ K = ⊤`. -/
theorem sup_eq_top_of_coprime_index {H K : Subgroup G}
    (h : Nat.Coprime H.index K.index) : H ⊔ K = ⊤ := by
  have h1 : (H ⊔ K).index ∣ H.index := Subgroup.index_dvd_of_le le_sup_left
  have h2 : (H ⊔ K).index ∣ K.index := Subgroup.index_dvd_of_le le_sup_right
  have h_dvd : (H ⊔ K).index ∣ 1 := h ▸ Nat.dvd_gcd h1 h2
  exact Subgroup.index_eq_one.mp (Nat.dvd_one.mp h_dvd)

/-! **Isaacs Thm 3.17 Wielandt**: 3 部分群 pairwise coprime index + solvable ⇒ G solvable.

**Forward dep**: 単純群の場合分けで Burnside `p^a q^b` 必要. Ch.7 完成後に back-fill.
所在: `OddOrder/Isaacs/Ch07_ThompsonSubgroup/ForwardFromCh03.lean` (placeholder). -/

end -- 3C

section /- 3D: π-separable + Hall-Higman (pp. 89-95) -/

variable {G : Type*} [Group G]

/-- **`π`-group**: `G` の全ての素因子が `π` に属す.

mathlib 未収載 (`IsPGroup` の π 版). `IsHallSubgroup π ⊤` と同値だが,
意図 (G 自体が π-group) を明示するため別名を導入. -/
def IsPiGroup (π : Set ℕ) (G : Type*) [Group G] : Prop :=
  ∀ p ∈ (Nat.card G).primeFactors, p ∈ π

/-- 部分群版: `H ≤ G` が π-group (= `|H|` の全素因子が π). -/
def Subgroup.IsPiGroup (π : Set ℕ) (H : Subgroup G) : Prop :=
  ∀ p ∈ (Nat.card H).primeFactors, p ∈ π

/-- If `H` is a π-Hall subgroup, every π-subgroup has cardinality dividing `|H|`. -/
theorem IsHallSubgroup.card_dvd_of_isPiGroup [Finite G] {π : Set ℕ} {H S : Subgroup G}
    (hH : IsHallSubgroup π H) (hS : Subgroup.IsPiGroup π S) :
    Nat.card S ∣ Nat.card H := by
  have hS_dvd_G : Nat.card S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card S
  have hcop : Nat.Coprime (Nat.card S) H.index := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
    rw [Nat.dvd_gcd_iff] at hq_dvd
    have hq_S_pf : q ∈ (Nat.card S).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.1, Nat.card_pos.ne'⟩
    have hq_idx_pf : q ∈ H.index.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.2, Subgroup.index_ne_zero_of_finite⟩
    exact hH.2 q hq_idx_pf (hS q hq_S_pf)
  have hG_eq : Nat.card G = Nat.card H * H.index := (Subgroup.card_mul_index H).symm
  rw [hG_eq] at hS_dvd_G
  exact hcop.dvd_of_dvd_mul_right hS_dvd_G

/-- **π-radical** `O_π(G)`: `G` の正規 π-subgroup の sup (= 最大の正規 π-subgroup).

mathlib 未収載 (各 `opCore p G` の π 版 sup). Hall-Higman 1.2.3 で必須.
形式化都合で subtype 上の単層 iSup を採用. -/
def oPiCore (π : Set ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨆ H : {H : Subgroup G // H.Normal ∧ Subgroup.IsPiGroup π H}, (H.val : Subgroup G)

/-- `O_π(G)` は `G` の正規部分群 (正規部分群の sup). -/
instance oPiCore.normal (π : Set ℕ) (G : Type*) [Group G] : (oPiCore π G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  refine Subgroup.iSup_induction _ (C := fun x => g * x * g⁻¹ ∈ oPiCore π G) hn
    ?mem ?one ?mul
  case mem =>
    rintro ⟨H, hN, _⟩ x hx
    -- x ∈ H 正規 ⇒ g x g⁻¹ ∈ H ≤ oPiCore π G.
    have hHle : H ≤ oPiCore π G :=
      le_iSup (fun K : {K : Subgroup G // K.Normal ∧ Subgroup.IsPiGroup π K} =>
        (K.val : Subgroup G)) ⟨H, hN, ‹_›⟩
    exact hHle (hN.conj_mem x hx g)
  case one => simp
  case mul =>
    intro x y hx hy
    have heq : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [heq]
    exact (oPiCore π G).mul_mem hx hy

/-- `O_π(G)` は `G` で characteristic. mathlib `characteristic_iff_le_comap` 経由で
任意の自己同型 `φ : G ≃* G` で `oPiCore` の generator 各 `H` (normal π-group) の像
`H.map φ` も normal π-group ⇒ `≤ oPiCore` を使う.

Hall-Higman 3.21 の K char in C/B + C ⊴ G ⇒ K ⊴ G の経路で必須. -/
instance oPiCore.characteristic (π : Set ℕ) (G : Type*) [Group G] :
    (oPiCore π G).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ
  refine iSup_le ?_
  rintro ⟨H, hHN, hHpi⟩ h hh
  rw [Subgroup.mem_comap]
  -- φ h ∈ H.map φ.toMonoidHom (which is normal + π-group) ≤ oPiCore π G.
  haveI hMapN : (H.map φ.toMonoidHom).Normal := hHN.map φ.toMonoidHom φ.surjective
  have hMapPi : Subgroup.IsPiGroup π (H.map φ.toMonoidHom) := by
    intro p hp
    have hcardEq : Nat.card ↥(H.map φ.toMonoidHom) = Nat.card ↥H :=
      Nat.card_congr (Subgroup.equivMapOfInjective H φ.toMonoidHom φ.injective).symm.toEquiv
    rw [hcardEq] at hp
    exact hHpi p hp
  have hMapMem : φ h ∈ H.map φ.toMonoidHom := ⟨h, hh, rfl⟩
  exact le_iSup (fun K : {K : Subgroup G // K.Normal ∧ Subgroup.IsPiGroup π K} =>
    (K.val : Subgroup G)) ⟨H.map φ.toMonoidHom, hMapN, hMapPi⟩ hMapMem

/-! ### π-separable 群の正式定義 (Isaacs Def 3.18)

`G` は π-separable とは, 正規列 `⊥ = F₀ ⊴ F₁ ⊴ ... ⊴ Fₙ = ⊤` で各因子 `Fᵢ₊₁/Fᵢ` が
π-group または π'-group となるものが存在する場合をいう (Isaacs FGT p.89).

**実装**: mathlib の `IsSolvable` パターンに準拠して `piFittingSeries` (`⊥` から始まり
各ステップで `G/Fₙ` の π-radical と π'-radical の sup を pull back する) の停留条件として
定式化. `derivedSeries G n = ⊥` パターン参照.

各 `Fₙ` は subtype `{S // S.Normal}` 経由で再帰中に normal instance を確保. -/

private def piFittingSeriesAux (π : Set ℕ) (G : Type*) [Group G] :
    ℕ → {S : Subgroup G // S.Normal}
  | 0 => ⟨⊥, inferInstance⟩
  | n + 1 =>
    let prev := piFittingSeriesAux π G n
    haveI : prev.val.Normal := prev.property
    ⟨Subgroup.comap (QuotientGroup.mk' prev.val)
        (oPiCore π (G ⧸ prev.val) ⊔ oPiCore {p | p ∉ π} (G ⧸ prev.val)),
     inferInstance⟩

/-- **π-Fitting series** of `G`: `F₀ = ⊥` から始まり, `Fₙ₊₁` は `G/Fₙ` 上の
`O_π(G/Fₙ) ⊔ O_{π'}(G/Fₙ)` の pullback. mathlib `derivedSeries`/`lowerCentralSeries`
パターンに準拠. `G` は π-separable iff この series が有限ステップで `⊤` に到達する. -/
def piFittingSeries (π : Set ℕ) (G : Type*) [Group G] (n : ℕ) : Subgroup G :=
  (piFittingSeriesAux π G n).val

instance piFittingSeries.normal (π : Set ℕ) (G : Type*) [Group G] (n : ℕ) :
    (piFittingSeries π G n).Normal :=
  (piFittingSeriesAux π G n).property

@[simp] theorem piFittingSeries_zero (π : Set ℕ) (G : Type*) [Group G] :
    piFittingSeries π G 0 = ⊥ := rfl

theorem piFittingSeries_succ (π : Set ℕ) (G : Type*) [Group G] (n : ℕ) :
    piFittingSeries π G (n + 1) =
      Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
        (oPiCore π (G ⧸ piFittingSeries π G n) ⊔
         oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n)) := rfl

theorem piFittingSeries_le_succ (π : Set ℕ) (G : Type*) [Group G] (n : ℕ) :
    piFittingSeries π G n ≤ piFittingSeries π G (n + 1) := by
  intro g hg
  rw [piFittingSeries_succ, Subgroup.mem_comap]
  rw [show (QuotientGroup.mk' (piFittingSeries π G n) g : G ⧸ piFittingSeries π G n) = 1
        from (QuotientGroup.eq_one_iff g).mpr hg]
  exact (oPiCore π (G ⧸ piFittingSeries π G n) ⊔
         oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n)).one_mem

theorem piFittingSeries_monotone (π : Set ℕ) (G : Type*) [Group G] :
    Monotone (piFittingSeries π G) :=
  monotone_nat_of_le_succ (piFittingSeries_le_succ π G)

/-- **π-separable 群** (Isaacs Def 3.18): `G` の π-Fitting series が有限ステップで
`⊤` に到達する. これは `G` が π-group と π'-group の交互の正規列に分解できることと同値.

定式化は mathlib `IsSolvable` パターン (`exists_top : ∃ n, piFittingSeries π G n = ⊤`)
に準拠. -/
class IsPiSeparable (π : Set ℕ) (G : Type*) [Group G] : Prop where
  exists_top : ∃ n : ℕ, piFittingSeries π G n = ⊤

/-- **`IsPiGroup.le_oPiCore`**: 任意の normal π-subgroup は `oPiCore π G` に含まれる.
`le_iSup` の素直な実体化. Hall-Higman 等での頻用 helper. -/
theorem Subgroup.IsPiGroup.le_oPiCore {G : Type*} [Group G] {π : Set ℕ} {H : Subgroup G}
    [H.Normal] (hH : Subgroup.IsPiGroup π H) : H ≤ oPiCore π G :=
  le_iSup (fun K : {K : Subgroup G // K.Normal ∧ Subgroup.IsPiGroup π K} =>
    (K.val : Subgroup G)) ⟨H, ‹_›, hH⟩

/-- **`⊥` は任意 π について π-group**: |⊥| = 1, primeFactors 1 = ∅. -/
theorem Subgroup.IsPiGroup.bot {G : Type*} [Group G] (π : Set ℕ) :
    Subgroup.IsPiGroup π (⊥ : Subgroup G) := by
  intro p hp
  simp at hp

/-- **IsPiGroup は subgroup inclusion で保持**: 有限 G で `H ≤ K` and `K` is π-group
⇒ `H` is π-group. `Nat.card ↥H ∣ Nat.card ↥K` で primeFactors 包含. -/
theorem Subgroup.IsPiGroup.le {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {H K : Subgroup G} (hHK : H ≤ K) (hK : Subgroup.IsPiGroup π K) :
    Subgroup.IsPiGroup π H := by
  intro p hp
  have hdvd : Nat.card ↥H ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hHK
  exact hK p (Nat.primeFactors_mono hdvd Nat.card_pos.ne' hp)

/-- A finite `p`-group is a `π`-group once `p ∈ π`. -/
theorem Subgroup.IsPiGroup.of_isPGroup_of_mem {G : Type*} [Group G] [Finite G]
    {π : Set ℕ} {H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hH : IsPGroup p H) (hpπ : p ∈ π) :
    Subgroup.IsPiGroup π H := by
  intro q hq
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := H)).mp hH
  rw [hn] at hq
  by_cases hn0 : n = 0
  · simp [hn0] at hq
  · rw [Nat.primeFactors_prime_pow hn0 Fact.out] at hq
    rw [Finset.mem_singleton] at hq
    rw [hq]
    exact hpπ

/-- **`oPiCore π G = ⊥` ⇒ G で normal π-subgroup は ⊥ のみ**.
`Subgroup.IsPiGroup.le_oPiCore` + `oPiCore = ⊥` の chain.

用途: Hall-Higman 3.21 case π' で `H ≤ O_π'(K) ⊴ G` + `O_π'(G) = ⊥` ⇒ `O_π'(K) = ⊥`,
よって H = ⊥ で Schur-Zassenhaus complement の存在と矛盾. -/
theorem eq_bot_of_isPiGroup_of_oPiCore_eq_bot {G : Type*} [Group G] (π : Set ℕ)
    {H : Subgroup G} [H.Normal] (hHpi : Subgroup.IsPiGroup π H)
    (hCore : oPiCore π G = ⊥) :
    H = ⊥ := by
  rw [eq_bot_iff, ← hCore]
  exact hHpi.le_oPiCore

/-- **`π` と `π'` の cardinality は互いに素**: `n` の素因子が全 `π` 内 + `m` の素因子
が全 `π` 外 ⇒ `Coprime n m`.

Hall-Higman 3.21 case π' で B π-group + K/B π'-group のとき Schur-Zassenhaus 適用
の前提 `Nat.Coprime |B| (K.index in K)` を得るための補題. -/
theorem Nat.coprime_of_isPiGroup_of_isPiGroup_compl
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) {π : Set ℕ}
    (hnPi : ∀ p ∈ n.primeFactors, p ∈ π)
    (hmPi' : ∀ p ∈ m.primeFactors, p ∉ π) :
    Nat.Coprime n m := by
  rw [← Nat.disjoint_primeFactors hn hm, Finset.disjoint_left]
  intro p hp_n hp_m
  exact absurd (hnPi p hp_n) (hmPi' p hp_m)

/-- A `π`-subgroup has trivial intersection with a `p`-group for `p ∉ π`. -/
theorem Subgroup.IsPiGroup.inf_eq_bot_of_isPGroup_not_mem {G : Type*} [Group G]
    [Finite G] {π : Set ℕ} {K M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hK : Subgroup.IsPiGroup π K) (hM : IsPGroup p M) (hp_notπ : p ∉ π) :
    K ⊓ M = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  have hM_pi' : Subgroup.IsPiGroup {q | q ∉ π} M :=
    Subgroup.IsPiGroup.of_isPGroup_of_mem hM hp_notπ
  have hdvdK : Nat.card ↥(K ⊓ M : Subgroup G) ∣ Nat.card K :=
    Subgroup.card_dvd_of_le inf_le_left
  have hdvdM : Nat.card ↥(K ⊓ M : Subgroup G) ∣ Nat.card M :=
    Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime (Nat.card K) (Nat.card M) :=
    Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne' hK hM_pi'
  have hdvd_gcd : Nat.card ↥(K ⊓ M : Subgroup G) ∣ Nat.gcd (Nat.card K) (Nat.card M) :=
    Nat.dvd_gcd hdvdK hdvdM
  rw [hcop] at hdvd_gcd
  exact Nat.dvd_one.mp hdvd_gcd

/-- Complementary Hall subgroups have coprime orders. -/
theorem IsHallSubgroup.card_coprime_of_compl [Finite G] {π : Set ℕ} {K H : Subgroup G}
    (hK : IsHallSubgroup {p | p ∉ π} K) (hH : IsHallSubgroup π H) :
    Nat.Coprime (Nat.card K) (Nat.card H) := by
  have hHK : Nat.Coprime (Nat.card H) (Nat.card K) :=
    Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne'
      hH.1
      (fun p hp => by simpa using hK.1 p hp)
  exact hHK.symm

/-- The index of a `π'`-Hall subgroup and the index of a `π`-Hall subgroup are coprime. -/
theorem IsHallSubgroup.index_coprime_of_compl [Finite G] {π : Set ℕ} {K H : Subgroup G}
    (hK : IsHallSubgroup {p | p ∉ π} K) (hH : IsHallSubgroup π H) :
    Nat.Coprime K.index H.index := by
  refine Nat.coprime_of_isPiGroup_of_isPiGroup_compl
    Subgroup.index_ne_zero_of_finite Subgroup.index_ne_zero_of_finite ?_ hH.2
  intro p hp
  by_contra hp_not
  exact hK.2 p hp hp_not

/-- If `K` is Hall `π'` and `H` is Hall `π`, then `|K| * |H| = |G|`. -/
theorem IsHallSubgroup.card_mul_of_compl [Finite G] {π : Set ℕ} {K H : Subgroup G}
    (hK : IsHallSubgroup {p | p ∉ π} K) (hH : IsHallSubgroup π H) :
    Nat.card K * Nat.card H = Nat.card G := by
  have h_card_cop : Nat.Coprime (Nat.card K) (Nat.card H) :=
    hK.card_coprime_of_compl hH
  have h_index_cop : Nat.Coprime H.index K.index :=
    (hK.index_coprime_of_compl hH).symm
  have hK_dvd_Hindex : Nat.card K ∣ H.index := by
    have hdiv : Nat.card K ∣ Nat.card H * H.index := by
      rw [Subgroup.card_mul_index H]
      exact Subgroup.card_subgroup_dvd_card K
    rw [mul_comm] at hdiv
    exact h_card_cop.dvd_of_dvd_mul_right hdiv
  have hHindex_dvd_K : H.index ∣ Nat.card K := by
    have hdivG : H.index ∣ Nat.card G :=
      ⟨Nat.card H, by rw [mul_comm, Subgroup.card_mul_index H]⟩
    have hdiv : H.index ∣ Nat.card K * K.index := by
      rwa [← Subgroup.card_mul_index K] at hdivG
    exact h_index_cop.dvd_of_dvd_mul_right hdiv
  have hK_card_eq : Nat.card K = H.index :=
    Nat.dvd_antisymm hK_dvd_Hindex hHindex_dvd_K
  calc
    Nat.card K * Nat.card H = H.index * Nat.card H := by rw [hK_card_eq]
    _ = Nat.card H * H.index := by rw [mul_comm]
    _ = Nat.card G := Subgroup.card_mul_index H

/-- Complementary Hall subgroups form an internal complement pair. -/
theorem IsHallSubgroup.isComplement_of_compl [Finite G] {π : Set ℕ} {K H : Subgroup G}
    (hK : IsHallSubgroup {p | p ∉ π} K) (hH : IsHallSubgroup π H) :
    Subgroup.IsComplement' K H :=
  Subgroup.isComplement'_of_coprime (hK.card_mul_of_compl hH)
    (hK.card_coprime_of_compl hH)

/-- **Hall-Higman 3.21 case π core**: `K ⊴ G` π-group + `K ≤ C_G(O_π(G))` ⇒
`K ≤ C_G(O_π(G)) ⊓ O_π(G)`.

`oPiCore π G` の極大性 (`IsPiGroup.le_oPiCore`) で `K ≤ oPiCore π G`,
これと仮定 `K ≤ centralizer` から inf に入る. 1-liner.

**用途**: Hall-Higman 3.21 case π で `K/B ⊆ C/B π-group ⇒ K ⊆ C ⊓ O = B`,
これと `B < K` で矛盾 (K = preimage of nontrivial K' で `B < K` を担保). -/
theorem hall_higman_case_pi_K_le_B {G : Type*} [Group G] [Finite G] (π : Set ℕ)
    {K : Subgroup G} [K.Normal] (hKpi : Subgroup.IsPiGroup π K)
    (hKC : K ≤ Subgroup.centralizer (oPiCore π G : Set G)) :
    K ≤ Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G :=
  le_inf hKC hKpi.le_oPiCore

/-- **IsPiGroup は MulEquiv (group iso) で保持**: `K ≃* K.map φ.toMonoidHom`
(`equivMapOfInjective`) で cardinality 同じ. -/
theorem Subgroup.IsPiGroup.map_equiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    {π : Set ℕ} {K : Subgroup G} (hK : Subgroup.IsPiGroup π K) :
    Subgroup.IsPiGroup π (K.map φ.toMonoidHom) := by
  intro p hp
  have hcard : Nat.card ↥(K.map φ.toMonoidHom) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.equivMapOfInjective K φ.toMonoidHom φ.injective).symm.toEquiv
  rw [hcard] at hp
  exact hK p hp

/-- A `π`-subgroup remains a `π`-subgroup after mapping to a quotient. -/
theorem Subgroup.IsPiGroup.map_quotient {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {N K : Subgroup G} [N.Normal] (hK : Subgroup.IsPiGroup π K) :
    Subgroup.IsPiGroup π (K.map (QuotientGroup.mk' N)) := by
  intro p hp
  apply hK
  rw [Nat.mem_primeFactors] at hp ⊢
  exact ⟨hp.1, hp.2.1.trans (Subgroup.card_map_dvd _ _), Nat.card_pos.ne'⟩

/-- **IsPiGroup は subgroupOf で保持**: `B ≤ K ≤ G` で `B` が π-group (as `Subgroup G`)
⇒ `B.subgroupOf K` も π-group (as `Subgroup ↥K`).

mathlib `subgroupOfEquivOfLe` で `↥(B.subgroupOf K) ≃* ↥B`, よって cardinality 同じ
⇒ primeFactors 同じ. -/
theorem Subgroup.IsPiGroup.subgroupOf {G : Type*} [Group G] {π : Set ℕ}
    {B K : Subgroup G} (hBK : B ≤ K) (hB : Subgroup.IsPiGroup π B) :
    Subgroup.IsPiGroup π (B.subgroupOf K) := by
  intro p hp
  have hcard : Nat.card ↥(B.subgroupOf K) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv
  rw [hcard] at hp
  exact hB p hp

/-- A complement to a `π'`-subgroup is a Hall `π`-subgroup of the ambient subgroup. -/
theorem isHallSubgroup_subgroupOf_of_complement_pi_pi' [Finite G] {π : Set ℕ}
    {U H M : Subgroup G} (hH_le_U : H ≤ U) (hM_le_U : M ≤ U)
    (hH_pi : Subgroup.IsPiGroup π H)
    (hM_pi' : Subgroup.IsPiGroup {p | p ∉ π} M)
    (hComp : Subgroup.IsComplement' (M.subgroupOf U) (H.subgroupOf U)) :
    IsHallSubgroup π (H.subgroupOf U) := by
  refine ⟨?_, ?_⟩
  · exact Subgroup.IsPiGroup.subgroupOf hH_le_U hH_pi
  · have hMsub_pi' : Subgroup.IsPiGroup {p | p ∉ π} (M.subgroupOf U) :=
      Subgroup.IsPiGroup.subgroupOf hM_le_U hM_pi'
    intro q hq hq_pi
    rw [hComp.index_eq_card] at hq
    exact hMsub_pi' q hq hq_pi

/-- **π-group extension**: `N ⊴ H` で `N` も `H/N` も π-group ⇒ `H` は π-group.
mathlib `card_eq_card_quotient_mul_card_subgroup` (`|H| = |H/N| * |N|`) +
`primeFactors_mul` で primes |H| ⊆ primes |H/N| ∪ primes |N| ⊆ π. -/
theorem IsPiGroup.of_normal_quotient {H : Type*} [Group H] [Finite H]
    {π : Set ℕ} (N : Subgroup H) [N.Normal]
    (hN : ∀ p ∈ (Nat.card ↥N).primeFactors, p ∈ π)
    (hQ : ∀ p ∈ (Nat.card (H ⧸ N)).primeFactors, p ∈ π) :
    IsPiGroup π H := by
  intro p hp
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N] at hp
  rw [Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hp
  rcases Finset.mem_union.mp hp with h | h
  · exact hQ p h
  · exact hN p h

/-- **2 つの normal π-subgroup の sup も π-subgroup**: 有限群 `G` で `H₁, H₂ ⊴ G`
が共に π-group ⇒ `H₁ ⊔ H₂` も π-group.

**証明**: `|H₁ ⊔ H₂| · |H₁ ⊓ H₂| = |H₁| · |H₂|` (`card_HK_mul_card_inf_eq_card_mul_card`
in `OddOrder/Mathlib/Subgroup`) + `(H₁ ⊔ H₂ : Set G) = ↑H₁ * ↑H₂` (normal で
`mem_sup_of_normal_left`) で `|H₁ ⊔ H₂| ∣ |H₁| · |H₂|`. primeFactors monotone +
primeFactors_mul で結論.

**用途**: `oPiCore.isPiGroup` (Hall-Higman 3.21 critical bottleneck) の closure step. -/
theorem Subgroup.IsPiGroup.sup_of_normal {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {H K : Subgroup G} [H.Normal] [K.Normal]
    (hH : Subgroup.IsPiGroup π H) (hK : Subgroup.IsPiGroup π K) :
    Subgroup.IsPiGroup π (H ⊔ K) := by
  intro p hp
  -- Step 1: Nat.card ↥(H ⊔ K) = Nat.card (↑H * ↑K : Set G) via mem_sup_of_normal_left.
  have hcard_eq : Nat.card ↥(H ⊔ K) = Nat.card (↑H * ↑K : Set G) := by
    refine Nat.card_congr ⟨fun x => ⟨x.val, ?_⟩, fun y => ⟨y.val, ?_⟩,
        fun _ => rfl, fun _ => rfl⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp x.2
      exact ⟨a, ha, b, hb, hab⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := y.2
      rw [← hab]
      exact Subgroup.mul_mem_sup ha hb
  -- Step 3: Nat.card (↑H * ↑K : Set G) ∣ Nat.card ↥H * Nat.card ↥K.
  have hHKformula : Nat.card (↑H * ↑K : Set G) * Nat.card ↥(H ⊓ K)
      = Nat.card H * Nat.card K :=
    Subgroup.card_HK_mul_card_inf_eq_card_mul_card H K
  have hdvd : Nat.card ↥(H ⊔ K) ∣ Nat.card ↥H * Nat.card ↥K := by
    rw [hcard_eq]
    exact ⟨_, hHKformula.symm⟩
  -- Step 4: primeFactors of |H ⊔ K| ⊆ primeFactors of (|H| * |K|).
  have hne : Nat.card ↥H * Nat.card ↥K ≠ 0 :=
    mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  have hsubset : (Nat.card ↥(H ⊔ K)).primeFactors
      ⊆ (Nat.card ↥H * Nat.card ↥K).primeFactors :=
    Nat.primeFactors_mono hdvd hne
  rw [Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hsubset
  rcases Finset.mem_union.mp (hsubset hp) with hpH | hpK
  · exact hH p hpH
  · exact hK p hpK

/-- A normal π-subgroup is contained in every π-Hall subgroup. -/
theorem Subgroup.IsPiGroup.normal_le_hall {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {N H : Subgroup G} [N.Normal] (hN : Subgroup.IsPiGroup π N)
    (hH : IsHallSubgroup π H) :
    N ≤ H := by
  have hSup_pi : Subgroup.IsPiGroup π (H ⊔ N : Subgroup G) := by
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hq_prime, hq_dvd, _⟩ := hq
    have h_card_eq : Nat.card ↥(H ⊔ N : Subgroup G) * Nat.card ↥(H ⊓ N : Subgroup G)
        = Nat.card ↥H * Nat.card ↥N := by
      have h_hk := Subgroup.card_HK_mul_card_inf_eq_card_mul_card H N
      rwa [show (↑H * ↑N : Set G) = ↑(H ⊔ N : Subgroup G) from
        (Subgroup.mul_normal H N).symm] at h_hk
    have h_dvd_prod : q ∣ Nat.card ↥H * Nat.card ↥N := by
      rw [← h_card_eq]
      exact hq_dvd.mul_right _
    rcases hq_prime.dvd_mul.mp h_dvd_prod with hH_dvd | hN_dvd
    · exact hH.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, hH_dvd, Nat.card_pos.ne'⟩)
    · exact hN q (Nat.mem_primeFactors.mpr ⟨hq_prime, hN_dvd, Nat.card_pos.ne'⟩)
  have h_card_dvd : Nat.card ↥(H ⊔ N : Subgroup G) ∣ Nat.card ↥H :=
    hH.card_dvd_of_isPiGroup hSup_pi
  have hH_le_sup : H ≤ H ⊔ N := le_sup_left
  have h_card_ge : Nat.card ↥H ≤ Nat.card ↥(H ⊔ N : Subgroup G) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hH_le_sup)
  have h_card_eq : Nat.card ↥(H ⊔ N : Subgroup G) = Nat.card ↥H :=
    Nat.le_antisymm (Nat.le_of_dvd Nat.card_pos h_card_dvd) h_card_ge
  have h_sup_eq : (H ⊔ N : Subgroup G) = H :=
    (Subgroup.eq_of_le_of_card_ge hH_le_sup h_card_eq.le).symm
  intro x hx
  have hx_sup : x ∈ (H ⊔ N : Subgroup G) := Subgroup.mem_sup_right hx
  rwa [h_sup_eq] at hx_sup

/-- **`oPiCore.isPiGroup`** ⭐ (Hall-Higman 3.21 critical bottleneck):
有限 `G` で `oPiCore π G` は π-group.

**証明** (~30 LOC): `Finset.sup_induction` を predicate `H ↦ H.Normal ∧ IsPiGroup π H`
で適用.
- iSup = Finset.sup over finite indexing (`Subgroup G` is Fintype for finite G).
- bot: trivially normal + π-group (primeFactors 1 = ∅).
- closure: `H₁, H₂ ⊴ G + π-group ⇒ H₁ ⊔ H₂ ⊴ G + π-group` (mathlib + `IsPiGroup.sup_of_normal`).
- generators: each subtype element has the predicate by construction. -/
theorem oPiCore.isPiGroup [Finite G] (π : Set ℕ) :
    Subgroup.IsPiGroup π (oPiCore π G) := by
  classical
  haveI hSubF : Fintype {H : Subgroup G // H.Normal ∧ Subgroup.IsPiGroup π H} :=
    Fintype.ofFinite _
  -- The iSup over the subtype equals Finset.univ.sup.
  set p : Subgroup G → Prop := fun H => H.Normal ∧ Subgroup.IsPiGroup π H with hp_def
  -- Step: show p holds for oPiCore.
  have hgoal : p (oPiCore π G) := by
    change p (⨆ H : {H : Subgroup G // H.Normal ∧ Subgroup.IsPiGroup π H},
        (H.val : Subgroup G))
    have hsup : (⨆ H : {H : Subgroup G // H.Normal ∧ Subgroup.IsPiGroup π H},
        (H.val : Subgroup G)) =
        (Finset.univ : Finset {H : Subgroup G // H.Normal ∧ Subgroup.IsPiGroup π H}).sup
          (fun H => (H.val : Subgroup G)) := by
      rw [Finset.sup_eq_iSup]
      simp [iSup_pos]
    rw [hsup]
    refine Finset.sup_induction (p := p) ?_ ?_ ?_
    · refine ⟨inferInstance, ?_⟩
      intro q hq
      simp at hq
    · rintro a₁ ⟨ha₁N, ha₁Pi⟩ a₂ ⟨ha₂N, ha₂Pi⟩
      haveI := ha₁N
      haveI := ha₂N
      exact ⟨inferInstance, Subgroup.IsPiGroup.sup_of_normal ha₁Pi ha₂Pi⟩
    · intro b _
      exact ⟨b.2.1, b.2.2⟩
  exact hgoal.2

/-- **K.map qmk が π-group ⇒ ↥K ⧸ N.subgroupOf K の primes も π 内**.
`Subgroup.nat_card_quotient_subgroupOf_eq_card_map` 経由で cardinality 経由の primeFactors
転送.

用途: Hall-Higman 3.21 body で `K/B` の π-group 性を `K_GB = K.map qmk` から導出. -/
theorem Subgroup.IsPiGroup.primeFactors_quotient_subgroupOf
    {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {N : Subgroup G} [N.Normal] {K : Subgroup G}
    (hMap : Subgroup.IsPiGroup π (K.map (QuotientGroup.mk' N))) :
    ∀ p ∈ (Nat.card ((↥K) ⧸ (N.subgroupOf K))).primeFactors, p ∈ π := by
  intro p hp
  rw [Subgroup.nat_card_quotient_subgroupOf_eq_card_map N K] at hp
  exact hMap p hp

/-- **`oPiCore` は `π` について monotone**: `π₁ ⊆ π₂ ⇒ oPiCore π₁ G ≤ oPiCore π₂ G`.
π を広げると normal π-subgroup の集合は大きくなり, iSup も増える. -/
theorem oPiCore_mono {π₁ π₂ : Set ℕ} (h : π₁ ⊆ π₂) (G : Type*) [Group G] :
    oPiCore π₁ G ≤ oPiCore π₂ G := by
  refine iSup_le ?_
  rintro ⟨H, hHN, hHpi⟩
  exact le_iSup (fun K : {K : Subgroup G // K.Normal ∧ Subgroup.IsPiGroup π₂ K} =>
    (K.val : Subgroup G)) ⟨H, hHN, fun p hp => h (hHpi p hp)⟩

/-- **`O_π` 交差補題**: 有限群 `G` と素数集合 `S` について、各 `p ∈ S` の補集合 π-radical
`O_{p'}(G) = oPiCore {p}ᶜ G` の交差は `O_{S'}(G) = oPiCore Sᶜ G` に一致する:
`⨅ p ∈ S, O_{p'}(G) = O_{S'}(G)`.

- `⊇` (`oPiCore Sᶜ G ≤ ⨅ ...`): 各 `p ∈ S` で `Sᶜ ⊆ {p}ᶜ` ゆえ `oPiCore_mono`。
- `⊆` (`⨅ ... ≤ oPiCore Sᶜ G`): 交差 `D` は normal な `Sᶜ`-group。実際 `q ∈ S` を仮に
  `q ∣ |D|` とすると `D ≤ oPiCore {q}ᶜ G` (`q` 番目の項) は `{q}ᶜ`-group (`oPiCore.isPiGroup`)
  なので `q ∤ |D|`、矛盾。よって `IsPiGroup.le_oPiCore`。

用途: BG Lemma 10.8 conjunct 1 (`M_β` が Hall) — `M_β = ⋂_{p∈π(M)−β(M)} (M' の normal
p-complement)` を `O_{(π(M)−β(M))ᶜ}(M')` にまとめる第一ピース (unconditional)。 -/
theorem iInf_oPiCore_compl_singleton {G : Type*} [Group G] [Finite G] (S : Set ℕ) :
    ⨅ p ∈ S, oPiCore ({p}ᶜ : Set ℕ) G = oPiCore Sᶜ G := by
  apply le_antisymm
  · -- `D := ⨅ p ∈ S, O_{p'}(G)` is a normal `Sᶜ`-group.
    haveI hDnormal : (⨅ p ∈ S, oPiCore ({p}ᶜ : Set ℕ) G).Normal :=
      Subgroup.normal_iInf_normal fun _ =>
        Subgroup.normal_iInf_normal fun _ => inferInstance
    refine Subgroup.IsPiGroup.le_oPiCore ?_
    intro q hq
    rw [Set.mem_compl_iff]
    intro hqS
    have hDle : (⨅ p ∈ S, oPiCore ({p}ᶜ : Set ℕ) G) ≤ oPiCore ({q}ᶜ : Set ℕ) G :=
      iInf₂_le q hqS
    have hmem : q ∈ ({q}ᶜ : Set ℕ) :=
      Subgroup.IsPiGroup.le hDle (oPiCore.isPiGroup ({q}ᶜ : Set ℕ)) q hq
    simp at hmem
  · refine le_iInf₂ fun p hp => ?_
    refine oPiCore_mono ?_ G
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    rintro rfl
    exact hx hp

/-- **Hall-Higman prereq**: 有限非自明可解群は π-radical または π'-radical が非自明.

`oPiCore π G ≠ ⊥ ∨ oPiCore {p | p ∉ π} G ≠ ⊥`.

**証明**: minimal normal `M ⊴ G` を取り (Ch.2 `exists_isMinimalNormal_le_of_normal`),
Thm 3.11 で `M` elem abelian `p`-group (for some prime `p`). `IsPGroup p ↥M` から
`|M| = p^n` (`IsPGroup.iff_card`). `n ≥ 1` (`M ≠ ⊥`) で primeFactors `(p^n) = {p}`.
`p ∈ π` or `p ∉ π` で場合分け: 各々 `M ≤ oPiCore (π or π') G`, `M ≠ ⊥` で結論. -/
theorem exists_oPiCore_ne_bot_or_oPi'Core_ne_bot
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSolvable G] (π : Set ℕ) :
    oPiCore π G ≠ ⊥ ∨ oPiCore {p | p ∉ π} G ≠ ⊥ := by
  have hTopNeBot : (⊤ : Subgroup G) ≠ ⊥ := top_ne_bot
  obtain ⟨M, hMin, _⟩ :=
    OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal _ hTopNeBot
  haveI hMNormal : M.Normal := hMin.1
  have hM_ne_bot : M ≠ ⊥ := hMin.2.1
  obtain ⟨p, hp_prime, hElem⟩ := solvable_minimal_normal_isElementaryAbelian hMin
  haveI hpFact : Fact p.Prime := ⟨hp_prime⟩
  have hIsPGroup : IsPGroup p ↥M := fun x => ⟨1, by
    rw [pow_one]; exact hElem.pow_eq_one x⟩
  obtain ⟨n, hn_card⟩ := (IsPGroup.iff_card (G := ↥M)).mp hIsPGroup
  haveI hMnt : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
  have hM_card_gt : 1 < Nat.card ↥M := Finite.one_lt_card
  have hn_ne : n ≠ 0 := by
    intro h
    rw [h, pow_zero] at hn_card
    rw [hn_card] at hM_card_gt
    exact absurd hM_card_gt (lt_irrefl _)
  have hPF : (Nat.card ↥M).primeFactors = {p} := by
    rw [hn_card]
    exact Nat.primeFactors_prime_pow hn_ne hp_prime
  by_cases hp_pi : p ∈ π
  · left
    intro hbot
    have hM_isPi : Subgroup.IsPiGroup π M := by
      intro q hq
      rw [hPF, Finset.mem_singleton] at hq
      exact hq ▸ hp_pi
    have hMle : M ≤ oPiCore π G :=
      le_iSup (fun K : {K : Subgroup G // K.Normal ∧ Subgroup.IsPiGroup π K} =>
        (K.val : Subgroup G)) ⟨M, hMNormal, hM_isPi⟩
    have : M = ⊥ := le_antisymm (hbot ▸ hMle) bot_le
    exact hM_ne_bot this
  · right
    intro hbot
    have hM_isPi' : Subgroup.IsPiGroup {q | q ∉ π} M := by
      intro q hq
      rw [hPF, Finset.mem_singleton] at hq
      exact hq ▸ hp_pi
    have hMle : M ≤ oPiCore {q | q ∉ π} G :=
      le_iSup (fun K : {K : Subgroup G // K.Normal ∧ Subgroup.IsPiGroup {q | q ∉ π} K} =>
        (K.val : Subgroup G)) ⟨M, hMNormal, hM_isPi'⟩
    have : M = ⊥ := le_antisymm (hbot ▸ hMle) bot_le
    exact hM_ne_bot this

/-! ### `oPiCore` の写像下振る舞い: surjective map / injective comap

`oPiCore` は normal π-subgroup の sup なので, surjective hom で image-押し出しは
`oPiCore` を超えず, injective hom で comap-引き戻しも `oPiCore` を超えない. これらは
`IsPiSeparable` の quotient / normal subgroup 閉包 instance の主要ステップ. -/

/-- **`oPiCore.map_le_of_surjective`**: surjective hom `f : G →* H` 下で
`oPiCore π G` の像は `oPiCore π H` に含まれる.

理由: 各 normal π-subgroup `K ⊴ G` の image `K.map f ⊴ H` は `Nat.card (K.map f) ∣ Nat.card K`
(`Subgroup.card_map_dvd`) なので π-group. -/
theorem oPiCore.map_le_of_surjective {G H : Type*} [Group G] [Finite G] [Group H] (π : Set ℕ)
    (f : G →* H) (hf : Function.Surjective f) :
    (oPiCore π G).map f ≤ oPiCore π H := by
  rw [oPiCore, Subgroup.map_iSup]
  refine iSup_le ?_
  rintro ⟨K, hKN, hKpi⟩
  haveI hKmapN : (K.map f).Normal := hKN.map f hf
  have hKmapPi : Subgroup.IsPiGroup π (K.map f) :=
    fun p hp => hKpi p (Nat.primeFactors_mono (K.card_map_dvd f) Nat.card_pos.ne' hp)
  exact Subgroup.IsPiGroup.le_oPiCore hKmapPi

/-- The π-Fitting series is contained in the complementary π-Fitting series.

The successor step maps the quotient by `F_n(π)` onto the quotient by `F_n(π')`;
`O_π` and `O_{π'}` are then carried into the two summands on the complementary side. -/
theorem piFittingSeries_le_compl (π : Set ℕ) (G : Type*) [Group G] [Finite G] :
    ∀ n, piFittingSeries π G n ≤ piFittingSeries {p | p ∉ π} G n := by
  intro n
  induction n with
  | zero =>
      rw [piFittingSeries_zero, piFittingSeries_zero]
  | succ n ih =>
      intro x hx
      set π' : Set ℕ := {p | p ∉ π} with hπ'_def
      set F : Subgroup G := piFittingSeries π G n with hF_def
      set F' : Subgroup G := piFittingSeries π' G n with hF'_def
      have hF_le_F' : F ≤ F' := by
        intro y hy
        exact ih hy
      set Q : G ⧸ F →* G ⧸ F' :=
        QuotientGroup.map F F' (MonoidHom.id G) hF_le_F' with hQ_def
      have hQsurj : Function.Surjective Q := by
        intro y
        rcases QuotientGroup.mk'_surjective F' y with ⟨g, rfl⟩
        exact ⟨QuotientGroup.mk' F g, by simp [Q]⟩
      have hQ_eq : (QuotientGroup.mk' F') x = Q ((QuotientGroup.mk' F) x) := by
        simp [Q]
      rw [piFittingSeries_succ, Subgroup.mem_comap] at hx
      rw [piFittingSeries_succ, Subgroup.mem_comap]
      rw [show ({q | q ∉ π'} : Set ℕ) = π by
        ext q
        simp [π']]
      change (QuotientGroup.mk' F') x ∈
        oPiCore π' (G ⧸ F') ⊔ oPiCore π (G ⧸ F')
      rw [hQ_eq]
      have hxF : (QuotientGroup.mk' F) x ∈
          oPiCore π (G ⧸ F) ⊔ oPiCore π' (G ⧸ F) := by
        simpa [F, π', hπ'_def] using hx
      have hMapSup :
          (oPiCore π (G ⧸ F) ⊔ oPiCore π' (G ⧸ F)).map Q ≤
            oPiCore π' (G ⧸ F') ⊔ oPiCore π (G ⧸ F') := by
        calc
          (oPiCore π (G ⧸ F) ⊔ oPiCore π' (G ⧸ F)).map Q =
              (oPiCore π (G ⧸ F)).map Q ⊔ (oPiCore π' (G ⧸ F)).map Q := by
            rw [Subgroup.map_sup]
          _ ≤ oPiCore π (G ⧸ F') ⊔ oPiCore π' (G ⧸ F') :=
            sup_le_sup (oPiCore.map_le_of_surjective π Q hQsurj)
              (oPiCore.map_le_of_surjective π' Q hQsurj)
          _ = oPiCore π' (G ⧸ F') ⊔ oPiCore π (G ⧸ F') := by
            rw [sup_comm]
      exact hMapSup ⟨_, hxF, rfl⟩

/-- π-separability is symmetric under replacing `π` by its complement. -/
theorem isPiSeparable_compl (π : Set ℕ) (G : Type*) [Group G] [Finite G]
    (hG : IsPiSeparable π G) : IsPiSeparable {p | p ∉ π} G := by
  rcases hG.exists_top with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hle := piFittingSeries_le_compl π G n
  rw [hn] at hle
  exact top_le_iff.mp hle

/-- `O_π` is invariant under group isomorphism. -/
theorem oPiCore.map_eq_of_mulEquiv {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (π : Set ℕ) (e : G ≃* H) :
    (oPiCore π G).map e = oPiCore π H := by
  refine le_antisymm (oPiCore.map_le_of_surjective π (e : G →* H) e.surjective) ?_
  intro y hy
  refine ⟨e.symm y, ?_, by simp⟩
  exact oPiCore.map_le_of_surjective π (e.symm : H →* G) e.symm.surjective ⟨y, hy, rfl⟩

/-- **`oPiCore.comap_le_of_injective`**: injective hom `f : G →* H`, `[Finite H]` 下で
`oPiCore π H` の preimage は `oPiCore π G` に含まれる.

理由: `(oPiCore π H).comap f ⊴ G` (Normal.comap instance) で π-group
(injective f で `Subgroup.equivMapOfInjective` により `comap f S ≃* (comap f S).map f`,
さらに `(comap f S).map f ≤ S = oPiCore π H` で cardinality dvd). -/
theorem oPiCore.comap_le_of_injective {G H : Type*} [Group G] [Group H] [Finite H] (π : Set ℕ)
    (f : G →* H) (hf : Function.Injective f) :
    (oPiCore π H).comap f ≤ oPiCore π G := by
  have hN : ((oPiCore π H).comap f).Normal := inferInstance
  have hPi : Subgroup.IsPiGroup π ((oPiCore π H).comap f) := by
    intro p hp
    have hcard_eq : Nat.card ↥((oPiCore π H).comap f) =
        Nat.card ↥(((oPiCore π H).comap f).map f) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ f hf).toEquiv
    have hle : ((oPiCore π H).comap f).map f ≤ oPiCore π H :=
      Subgroup.map_comap_le _ _
    have hdvd : Nat.card ↥((oPiCore π H).comap f) ∣ Nat.card ↥(oPiCore π H) := by
      rw [hcard_eq]; exact Subgroup.card_dvd_of_le hle
    exact (oPiCore.isPiGroup π) p (Nat.primeFactors_mono hdvd Nat.card_pos.ne' hp)
  exact Subgroup.IsPiGroup.le_oPiCore hPi

/-- Quotienting by `O_π(G)` kills the π-radical. -/
theorem oPiCore_quotient_self_eq_bot {G : Type*} [Group G] [Finite G] (π : Set ℕ) :
    oPiCore π (G ⧸ oPiCore π G) = ⊥ := by
  let N : Subgroup G := oPiCore π G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Kbar : Subgroup (G ⧸ N) := oPiCore π (G ⧸ N)
  let K : Subgroup G := Kbar.comap q
  haveI hN_normal : N.Normal := inferInstance
  haveI hK_normal : K.Normal := inferInstance
  have hN_le_K : N ≤ K := by
    intro x hx
    change q x ∈ Kbar
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact Kbar.one_mem
  have hK_map : K.map q = Kbar := by
    dsimp [K, q]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Kbar
  have hKmap_pi : Subgroup.IsPiGroup π (K.map q) := by
    rw [hK_map]
    exact oPiCore.isPiGroup π
  have hNsub_pi : Subgroup.IsPiGroup π (N.subgroupOf K) :=
    Subgroup.IsPiGroup.subgroupOf hN_le_K (oPiCore.isPiGroup π)
  have hKquot_pi :
      ∀ p ∈ (Nat.card (↥K ⧸ N.subgroupOf K)).primeFactors, p ∈ π :=
    Subgroup.IsPiGroup.primeFactors_quotient_subgroupOf hKmap_pi
  have hK_pi : Subgroup.IsPiGroup π K :=
    IsPiGroup.of_normal_quotient (N.subgroupOf K) hNsub_pi hKquot_pi
  have hK_le_N : K ≤ N := hK_pi.le_oPiCore
  have hK_eq_N : K = N := le_antisymm hK_le_N hN_le_K
  have hN_map_bot : N.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff N]
    dsimp [q]
    rw [QuotientGroup.ker_mk']
  calc
    Kbar = K.map q := hK_map.symm
    _ = N.map q := by rw [hK_eq_N]
    _ = ⊥ := hN_map_bot

/-- **`oPiCore π G ⊓ oPiCore π' G = ⊥`** for finite `G`.

`oPiCore π G` は π-group, `oPiCore π' G` は π'-group なので primeFactors が排他的
⇒ cardinality が coprime ⇒ inf が ⊥ (`Subgroup.disjoint_of_coprime_natCard` 経由).

Hall-Higman π-separable 一般版の Bezout decomposition 前提として必須. -/
theorem oPiCore.coprime_inf {G : Type*} [Group G] [Finite G] (π : Set ℕ) :
    oPiCore π G ⊓ oPiCore {p | p ∉ π} G = ⊥ := by
  apply Disjoint.eq_bot
  apply Subgroup.disjoint_of_coprime_natCard
  exact Nat.coprime_of_isPiGroup_of_isPiGroup_compl
    Nat.card_pos.ne' Nat.card_pos.ne'
    (oPiCore.isPiGroup π) (oPiCore.isPiGroup _)

/-- **Bezout 分解**: 有限群 `Q` で `A` 正規 π-group, `B` 正規 π'-group, `A ⊓ B = ⊥` のとき,
`x ∈ A ⊔ B` ならば 整数指数 `k₁ + k₂ = 1` で `x^k₁ ∈ A`, `x^k₂ ∈ B`.

数学的内容: `A ⊓ B = ⊥` + normality より `commute_of_normal_of_disjoint` で `A` と `B` の
元は可換, したがって `A ⊔ B ≃ A × B` の内部直積分解が成立. `x = ã * b̃` から各成分を
`x` の整数べきで実現 (`x^(n*β) = ã^(n*β)` (∵ `b̃^n = 1`) で π-部分, 同様に π'-部分). -/
private theorem decompose_pi_pi'_exists_zpow {Q : Type*} [Group Q] [Finite Q] (π : Set ℕ)
    {A B : Subgroup Q} [hAN : A.Normal] [hBN : B.Normal]
    (hA : Subgroup.IsPiGroup π A) (hB : Subgroup.IsPiGroup {p | p ∉ π} B)
    (hAB : A ⊓ B = ⊥) {x : Q} (hx : x ∈ A ⊔ B) :
    ∃ k₁ k₂ : ℤ, k₁ + k₂ = 1 ∧ x^k₁ ∈ A ∧ x^k₂ ∈ B := by
  obtain ⟨aA, haA, bB, hbB, hxeq⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  have hdis : Disjoint A B := disjoint_iff.mpr hAB
  have hcomm : Commute aA bB :=
    Subgroup.commute_of_normal_of_disjoint A B hAN hBN hdis aA bB haA hbB
  have hm_dvd : orderOf aA ∣ Nat.card ↥A := A.orderOf_dvd_natCard haA
  have hn_dvd : orderOf bB ∣ Nat.card ↥B := B.orderOf_dvd_natCard hbB
  have hm_pi : ∀ p ∈ (orderOf aA).primeFactors, p ∈ π := fun p hp =>
    hA p (Nat.primeFactors_mono hm_dvd Nat.card_pos.ne' hp)
  have hn_pi' : ∀ p ∈ (orderOf bB).primeFactors, p ∉ π := fun p hp =>
    hB p (Nat.primeFactors_mono hn_dvd Nat.card_pos.ne' hp)
  have hcop : (orderOf aA).Coprime (orderOf bB) :=
    Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (orderOf_pos aA).ne' (orderOf_pos bB).ne' hm_pi hn_pi'
  have hbezout : (orderOf aA : ℤ) * (orderOf aA).gcdA (orderOf bB) +
      (orderOf bB : ℤ) * (orderOf aA).gcdB (orderOf bB) = 1 := by
    have h := Nat.gcd_eq_gcd_ab (orderOf aA) (orderOf bB)
    have hg : Nat.gcd (orderOf aA) (orderOf bB) = 1 := hcop
    rw [hg, Nat.cast_one] at h
    linarith
  refine ⟨(orderOf bB : ℤ) * (orderOf aA).gcdB (orderOf bB),
          (orderOf aA : ℤ) * (orderOf aA).gcdA (orderOf bB), ?_, ?_, ?_⟩
  · linarith
  · rw [show x = aA * bB from hxeq.symm, hcomm.mul_zpow]
    have hb_pow : bB ^ ((orderOf bB : ℤ) * (orderOf aA).gcdB (orderOf bB)) = 1 := by
      rw [zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    rw [hb_pow, mul_one]
    exact A.zpow_mem haA _
  · rw [show x = aA * bB from hxeq.symm, hcomm.mul_zpow]
    have ha_pow : aA ^ ((orderOf aA : ℤ) * (orderOf aA).gcdA (orderOf bB)) = 1 := by
      rw [zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    rw [ha_pow, one_mul]
    exact B.zpow_mem hbB _

/-- **Image of `H.subgroupOf N` in `↥N/F'` is contained in `oPiCore π (↥N/F')`**.

仮定: `F ⊴ G` で `F ≤ H ⊴ G`, `H.map (mk' F)` が π-group, `N ⊴ G`, `F' ⊴ ↥N` で
`F.subgroupOf N ≤ F'`.

数学的内容: cardinality chain
- `|image| = |↥(H.subgroupOf N) / F'.subgroupOf|` (`nat_card_quotient_subgroupOf_eq_card_map`)
- `∣ |↥(H.subgroupOf N) / (F.subgroupOf N).subgroupOf|` (`F.subgroupOf N ≤ F'` で分母拡大)
- `= |φ.range|` for `φ := (mk' F).comp (N.subtype.comp S.subtype)` (1st iso)
- `∣ |H.map (mk' F)|` (`φ.range ≤ H.map (mk' F)`).

これで image の primeFactors ⊆ π, normality は image of normal under surjective ⇒
`Subgroup.IsPiGroup.le_oPiCore` で結論. -/
private lemma image_subgroupOf_le_oPiCore (π : Set ℕ) {G : Type*} [Group G] [Finite G]
    {F : Subgroup G} [F.Normal] {H : Subgroup G} [H.Normal] (_hFH : F ≤ H)
    (hH_pi : Subgroup.IsPiGroup π (H.map (QuotientGroup.mk' F)))
    {N : Subgroup G} {F' : Subgroup ↥N} [F'.Normal]
    (hF'_le : F.subgroupOf N ≤ F') :
    (H.subgroupOf N).map (QuotientGroup.mk' F') ≤ oPiCore π (↥N ⧸ F') := by
  apply Subgroup.IsPiGroup.le_oPiCore
  intro p hp
  set S : Subgroup ↥N := H.subgroupOf N with hS_def
  let φ : ↥S →* G ⧸ F := (QuotientGroup.mk' F).comp (N.subtype.comp S.subtype)
  have hφ_range : φ.range ≤ H.map (QuotientGroup.mk' F) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x.val.val, x.property, rfl⟩
  have hφ_ker : φ.ker = (F.subgroupOf N).subgroupOf S := by
    ext x
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
               QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have h_T_eq : Nat.card ↥(S.map (QuotientGroup.mk' F')) = Nat.card (↥S ⧸ F'.subgroupOf S) :=
    (Subgroup.nat_card_quotient_subgroupOf_eq_card_map F' S).symm
  have hKK' : (F.subgroupOf N).subgroupOf S ≤ F'.subgroupOf S := fun x hx => hF'_le hx
  have h_quot_dvd : Nat.card (↥S ⧸ F'.subgroupOf S) ∣
      Nat.card (↥S ⧸ (F.subgroupOf N).subgroupOf S) := by
    apply Subgroup.card_dvd_of_surjective
      (QuotientGroup.map ((F.subgroupOf N).subgroupOf S) (F'.subgroupOf S) (MonoidHom.id ↥S)
        (fun x hx => by simpa using hKK' hx))
    apply QuotientGroup.map_surjective_of_surjective
    exact QuotientGroup.mk_surjective
  have h_ker_eq : Nat.card (↥S ⧸ (F.subgroupOf N).subgroupOf S) = Nat.card (↥S ⧸ φ.ker) := by
    rw [hφ_ker]
  have h_first_iso : Nat.card (↥S ⧸ φ.ker) = Nat.card ↥φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have h_range_dvd : Nat.card ↥φ.range ∣ Nat.card ↥(H.map (QuotientGroup.mk' F)) :=
    Subgroup.card_dvd_of_le hφ_range
  have hT_dvd : Nat.card ↥(S.map (QuotientGroup.mk' F')) ∣
      Nat.card ↥(H.map (QuotientGroup.mk' F)) := by
    calc Nat.card ↥(S.map (QuotientGroup.mk' F'))
        = Nat.card (↥S ⧸ F'.subgroupOf S) := h_T_eq
      _ ∣ Nat.card (↥S ⧸ (F.subgroupOf N).subgroupOf S) := h_quot_dvd
      _ = Nat.card (↥S ⧸ φ.ker) := h_ker_eq
      _ = Nat.card ↥φ.range := h_first_iso
      _ ∣ Nat.card ↥(H.map (QuotientGroup.mk' F)) := h_range_dvd
  exact hH_pi p (Nat.primeFactors_mono hT_dvd Nat.card_pos.ne' hp)

/-! ### `IsPiSeparable` の閉包 instance (quotient / normal subgroup)

`piFittingSeries` を quotient map で押し出し / subgroup へ引き戻して長さ保存. -/

/-- **`piFittingSeries` の quotient 押し出し**: `(piFittingSeries π G n).map (mk' N) ≤
piFittingSeries π (G/N) n`. quotient closure instance の主要 step. -/
private theorem piFittingSeries_map_quot_le (π : Set ℕ) (G : Type*) [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] : ∀ n,
    (piFittingSeries π G n).map (QuotientGroup.mk' N) ≤ piFittingSeries π (G ⧸ N) n := by
  intro n
  induction n with
  | zero => simp [piFittingSeries_zero, Subgroup.map_bot]
  | succ n ih =>
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hx
    have hg' : (QuotientGroup.mk' (piFittingSeries π G n)) g ∈
        oPiCore π (G ⧸ piFittingSeries π G n) ⊔
        oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n) := by
      rw [piFittingSeries_succ] at hg
      exact Subgroup.mem_comap.mp hg
    -- IH gives F^G_n ≤ (F^{G/N}_n).comap (mk' N)
    have hH_le : piFittingSeries π G n ≤
        (piFittingSeries π (G ⧸ N) n).comap (QuotientGroup.mk' N) := by
      intro y hy
      rw [Subgroup.mem_comap]
      exact ih ⟨y, hy, rfl⟩
    -- QuotientGroup.map : G/F^G_n → (G/N)/F^{G/N}_n is surjective.
    set Q : G ⧸ piFittingSeries π G n →* (G ⧸ N) ⧸ piFittingSeries π (G ⧸ N) n :=
      QuotientGroup.map _ _ (QuotientGroup.mk' N) hH_le with hQ_def
    have hQsurj : Function.Surjective Q := by
      apply QuotientGroup.map_surjective_of_surjective
      exact (QuotientGroup.mk_surjective).comp (QuotientGroup.mk'_surjective N)
    -- (mk' F^{G/N}_n) (mk' N g) = Q (mk' F^G_n g)
    have hQ_eq : (QuotientGroup.mk' (piFittingSeries π (G ⧸ N) n)) ((QuotientGroup.mk' N) g) =
        Q ((QuotientGroup.mk' (piFittingSeries π G n)) g) := by
      simp [hQ_def]
    rw [piFittingSeries_succ, Subgroup.mem_comap, hQ_eq]
    -- Q maps sup_G into sup_{G/N} by oPiCore.map_le_of_surjective.
    have hMapSup : (oPiCore π (G ⧸ piFittingSeries π G n) ⊔
        oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n)).map Q ≤
        oPiCore π ((G ⧸ N) ⧸ piFittingSeries π (G ⧸ N) n) ⊔
        oPiCore {p | p ∉ π} ((G ⧸ N) ⧸ piFittingSeries π (G ⧸ N) n) := by
      rw [Subgroup.map_sup]
      exact sup_le_sup (oPiCore.map_le_of_surjective π Q hQsurj)
                       (oPiCore.map_le_of_surjective {p | p ∉ π} Q hQsurj)
    exact hMapSup ⟨_, hg', rfl⟩

/-- **`IsPiSeparable` の quotient 閉包**: `[IsPiSeparable π G] [N ⊴ G] ⇒ [IsPiSeparable π (G/N)]`. -/
instance quotient_isPiSeparable (π : Set ℕ) (G : Type*) [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [IsPiSeparable π G] : IsPiSeparable π (G ⧸ N) where
  exists_top := by
    obtain ⟨n, hn⟩ := IsPiSeparable.exists_top (π := π) (G := G)
    refine ⟨n, ?_⟩
    have hmap := piFittingSeries_map_quot_le π G N n
    rw [hn, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at hmap
    exact top_le_iff.mp hmap

/-! ### Subgroup 閉包

`[IsPiSeparable π G] {N ≤ G} ⇒ [IsPiSeparable π ↥N]`.

数学的内容 (Isaacs Lem 3.18 piFittingSeries 版): `(piFittingSeries π G n).subgroupOf N`
は `↥N` の正規列で各因子が "A_π ⊔ A_π'" 構造. 各層で Bezout 分解
(`decompose_pi_pi'_exists_zpow`) により `x = x^k₁ * x^k₂` と π-part × π'-part に分け,
`image_subgroupOf_le_oPiCore` で各 part が `oPiCore π` / `oPiCore π'` に入ることを示す. -/

/-- **`piFittingSeries` の subgroup 制限**:
`N ≤ G` で `(piFittingSeries π G n).subgroupOf N ≤ piFittingSeries π N n`.

帰納法: succ ステップで Bezout 分解で `x · F_n = π-part · π'-part` を整数指数で実現,
各 part の image を `image_subgroupOf_le_oPiCore` で `O_π` / `O_π'` に押し込む. -/
private theorem piFittingSeries_subgroupOf_le (π : Set ℕ)
    (G : Type*) [Group G] [Finite G] (N : Subgroup G) : ∀ n,
    (piFittingSeries π G n).subgroupOf N ≤ piFittingSeries π N n := by
  intro n
  induction n with
  | zero =>
    rw [piFittingSeries_zero, Subgroup.bot_subgroupOf, piFittingSeries_zero]
  | succ n ih =>
    intro x hx
    haveI hFn_normal : (piFittingSeries π G n).Normal := piFittingSeries.normal π G n
    haveI hF'n_normal : (piFittingSeries π N n).Normal := piFittingSeries.normal π N n
    rw [Subgroup.mem_subgroupOf, piFittingSeries_succ, Subgroup.mem_comap] at hx
    -- hx : (mk' Fn) (x.val) ∈ oPiCore π (G/Fn) ⊔ oPiCore π' (G/Fn).
    -- Apply Bezout in G/Fn.
    obtain ⟨k₁, k₂, hsum, hk₁mem, hk₂mem⟩ :=
      decompose_pi_pi'_exists_zpow π (oPiCore.isPiGroup π) (oPiCore.isPiGroup _)
        (oPiCore.coprime_inf π) hx
    -- Goal: x ∈ piFittingSeries π N (n+1).
    rw [piFittingSeries_succ, Subgroup.mem_comap]
    -- Express x = x^k₁ * x^k₂ in ↥N (since k₁ + k₂ = 1).
    have hx_zpow : x = x^k₁ * x^k₂ := by
      rw [← zpow_add, hsum, zpow_one]
    rw [hx_zpow, map_mul]
    -- Goal: (mk' F'n) (x^k₁) * (mk' F'n) (x^k₂) ∈ oPiCore π ⊔ oPiCore π'.
    -- Show (mk' F'n) (x^k₁) ∈ oPiCore π via image_subgroupOf_le_oPiCore.
    have hF_le_Hπ : piFittingSeries π G n ≤
        Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
          (oPiCore π (G ⧸ piFittingSeries π G n)) := by
      calc
        piFittingSeries π G n = (QuotientGroup.mk' (piFittingSeries π G n)).ker :=
          (QuotientGroup.ker_mk' _).symm
        _ ≤ Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
            (oPiCore π (G ⧸ piFittingSeries π G n)) :=
          Subgroup.ker_le_comap _ _
    have hF_le_Hπ' : piFittingSeries π G n ≤
        Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
          (oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n)) := by
      calc
        piFittingSeries π G n = (QuotientGroup.mk' (piFittingSeries π G n)).ker :=
          (QuotientGroup.ker_mk' _).symm
        _ ≤ Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
            (oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n)) :=
          Subgroup.ker_le_comap _ _
    have hHπ_image_eq : (Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
          (oPiCore π (G ⧸ piFittingSeries π G n))).map
          (QuotientGroup.mk' (piFittingSeries π G n)) =
        oPiCore π (G ⧸ piFittingSeries π G n) := by
      rw [Subgroup.map_comap_eq,
          MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
      exact top_inf_eq _
    have hHπ'_image_eq : (Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
          (oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n))).map
          (QuotientGroup.mk' (piFittingSeries π G n)) =
        oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n) := by
      rw [Subgroup.map_comap_eq,
          MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
      exact top_inf_eq _
    have hHπ_pi : Subgroup.IsPiGroup π
        ((Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
          (oPiCore π (G ⧸ piFittingSeries π G n))).map
          (QuotientGroup.mk' (piFittingSeries π G n))) := by
      rw [hHπ_image_eq]; exact oPiCore.isPiGroup π
    have hHπ'_pi : Subgroup.IsPiGroup {p | p ∉ π}
        ((Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
          (oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n))).map
          (QuotientGroup.mk' (piFittingSeries π G n))) := by
      rw [hHπ'_image_eq]; exact oPiCore.isPiGroup _
    have hT1 : ((Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
        (oPiCore π (G ⧸ piFittingSeries π G n))).subgroupOf N).map
        (QuotientGroup.mk' (piFittingSeries π N n)) ≤
        oPiCore π (↥N ⧸ piFittingSeries π N n) :=
      image_subgroupOf_le_oPiCore π hF_le_Hπ hHπ_pi ih
    have hT2 : ((Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
        (oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n))).subgroupOf N).map
        (QuotientGroup.mk' (piFittingSeries π N n)) ≤
        oPiCore {p | p ∉ π} (↥N ⧸ piFittingSeries π N n) :=
      image_subgroupOf_le_oPiCore {p | p ∉ π} hF_le_Hπ' hHπ'_pi ih
    -- y1 := x^k₁, y2 := x^k₂ in ↥N.
    have hy1_in : x^k₁ ∈ (Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
        (oPiCore π (G ⧸ piFittingSeries π G n))).subgroupOf N := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_zpow, map_zpow]
      exact hk₁mem
    have hy2_in : x^k₂ ∈ (Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n))
        (oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n))).subgroupOf N := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_zpow, map_zpow]
      exact hk₂mem
    exact Subgroup.mul_mem_sup
      (hT1 ⟨x^k₁, hy1_in, rfl⟩)
      (hT2 ⟨x^k₂, hy2_in, rfl⟩)

/-- **`IsPiSeparable` の subgroup 閉包**:
`[IsPiSeparable π G] {N ≤ G} ⇒ [IsPiSeparable π ↥N]`. -/
theorem Subgroup.isPiSeparable_of_isPiSeparable (π : Set ℕ)
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [IsPiSeparable π G] :
    IsPiSeparable π ↥N where
  exists_top := by
    obtain ⟨n, hn⟩ := IsPiSeparable.exists_top (π := π) (G := G)
    refine ⟨n, ?_⟩
    have hle := piFittingSeries_subgroupOf_le π G N n
    rw [hn, Subgroup.top_subgroupOf] at hle
    exact top_le_iff.mp hle

/-- **`IsPiSeparable` の normal subgroup 閉包**:
`[IsPiSeparable π G] {N ⊴ G} ⇒ [IsPiSeparable π ↥N]`. -/
instance normalSubgroup_isPiSeparable (π : Set ℕ) (G : Type*) [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [IsPiSeparable π G] : IsPiSeparable π ↥N :=
  Subgroup.isPiSeparable_of_isPiSeparable π N

/-- 補助: `piFittingSeries π G (n+1)` が `piFittingSeries π G n` を真に拡張する条件は,
`G/Fₙ` 上の `O_π ⊔ O_{π'}` が非自明であることと同値. -/
private theorem piFittingSeries_lt_succ_iff (π : Set ℕ) {G : Type*} [Group G] (n : ℕ) :
    piFittingSeries π G n < piFittingSeries π G (n + 1) ↔
      (oPiCore π (G ⧸ piFittingSeries π G n) ⊔
        oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n)) ≠ ⊥ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · intro h_sup_bot
    apply ne_of_lt h
    rw [piFittingSeries_succ, h_sup_bot]
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
  · refine lt_of_le_of_ne (piFittingSeries_le_succ π G n) ?_
    intro h_eq
    apply h
    have hSurj : Function.Surjective (QuotientGroup.mk' (piFittingSeries π G n)) :=
      QuotientGroup.mk'_surjective _
    apply Subgroup.comap_injective hSurj
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk', ← piFittingSeries_succ, h_eq]

/-! **Isaacs Lemma 3.18** の役割は本実装では subgroup / quotient 閉包 instance が果たす
(別 issue で追加予定). 現状は `isPiSeparable_of_solvable` で十分. -/

/-- **Isaacs Cor 3.19**: `G` 有限 solvable ⇒ 全 π について π-separable. instance 形.

戦略: `Nat.card G ≤ Nat.card (Fₙ) + k` の `k` についての強誘導. 各ステップで
`Fₙ < ⊤` なら `G/Fₙ` 非自明可解で `exists_oPiCore_ne_bot_or_oPi'Core_ne_bot` 適用,
`Fₙ < F_{n+1}` ⇒ `|Fₙ| < |F_{n+1}|` で measure 単調減少. -/
instance isPiSeparable_of_solvable (π : Set ℕ) (G : Type*) [Group G] [Finite G] [IsSolvable G] :
    IsPiSeparable π G where
  exists_top := by
    classical
    suffices h : ∀ (k : ℕ) (n : ℕ),
        Nat.card G ≤ Nat.card (piFittingSeries π G n) + k →
        ∃ m, piFittingSeries π G m = ⊤ from
      h (Nat.card G) 0 (by simp)
    intro k
    induction k with
    | zero =>
      intro n hk
      refine ⟨n, ?_⟩
      have hle : piFittingSeries π G n ≤ (⊤ : Subgroup G) := le_top
      apply Subgroup.eq_of_le_of_card_ge hle
      have hcardTop : Nat.card ↥(⊤ : Subgroup G) = Nat.card G :=
        Nat.card_congr Subgroup.topEquiv.toEquiv
      omega
    | succ k ih =>
      intro n hk
      by_cases h_top : piFittingSeries π G n = ⊤
      · exact ⟨n, h_top⟩
      · have hFn_lt_top : piFittingSeries π G n < ⊤ := lt_of_le_of_ne le_top h_top
        haveI : Nontrivial (G ⧸ piFittingSeries π G n) := by
          rw [QuotientGroup.nontrivial_iff]
          exact ne_of_lt hFn_lt_top
        haveI : IsSolvable (G ⧸ piFittingSeries π G n) := inferInstance
        have hOplus : oPiCore π (G ⧸ piFittingSeries π G n) ⊔
            oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n) ≠ ⊥ := by
          rcases exists_oPiCore_ne_bot_or_oPi'Core_ne_bot (G := G ⧸ piFittingSeries π G n) π with
            hπ | hπ'
          · intro h; exact hπ (le_bot_iff.mp (h ▸ le_sup_left))
          · intro h; exact hπ' (le_bot_iff.mp (h ▸ le_sup_right))
        have hFn_lt : piFittingSeries π G n < piFittingSeries π G (n + 1) :=
          (piFittingSeries_lt_succ_iff π n).mpr hOplus
        have hcard_lt : Nat.card (piFittingSeries π G n) <
            Nat.card (piFittingSeries π G (n + 1)) := by
          rcases lt_iff_le_and_ne.mp hFn_lt with ⟨hle, hne⟩
          refine lt_of_le_of_ne (Subgroup.card_le_of_le hle) ?_
          intro hcard_eq
          exact hne (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard_eq.symm))
        apply ih (n + 1)
        omega

/-! ### disjunction lemma の `[IsPiSeparable]` 版 -/

/-- If `O_π(G) = ⊥`, then also `O_π(G/⊥) = ⊥`.

This is the quotient-by-`⊥` bridge used to transfer the first nontrivial
`piFittingSeries` step back from `G ⧸ ⊥` to `G`. -/
private theorem oPiCore_quotient_bot_eq_bot_of_oPiCore_eq_bot
    {G : Type*} [Group G] [Finite G] (π : Set ℕ)
    (hbot : oPiCore π G = ⊥) :
    oPiCore π (G ⧸ (⊥ : Subgroup G)) = ⊥ := by
  let q : G →* G ⧸ (⊥ : Subgroup G) := QuotientGroup.mk' (⊥ : Subgroup G)
  have hq_surj : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hq_inj : Function.Injective q := by
    have hker : q.ker = ⊥ := by
      dsimp [q]
      exact QuotientGroup.ker_mk' (⊥ : Subgroup G)
    exact (MonoidHom.ker_eq_bot_iff q).mp hker
  apply Subgroup.comap_injective hq_surj
  apply le_antisymm
  · rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    exact (oPiCore.comap_le_of_injective π q hq_inj).trans (le_of_eq hbot)
  · rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    exact bot_le

/-- **π-separable disjunction**: a finite nontrivial π-separable group has a nontrivial
first π-Fitting layer, i.e. `O_π(G) ⊔ O_{π'}(G) ≠ ⊥`. -/
theorem oPiCore_sup_ne_bot_of_isPiSeparable
    {G : Type*} [Group G] [Finite G] (π : Set ℕ) [Nontrivial G] [IsPiSeparable π G] :
    (oPiCore π G ⊔ oPiCore {p | p ∉ π} G) ≠ ⊥ := by
  have hF1_ne_bot : piFittingSeries π G 1 ≠ ⊥ := by
    intro hF1
    obtain ⟨n, hn⟩ := IsPiSeparable.exists_top (π := π) (G := G)
    have hQsup_bot : (oPiCore π (G ⧸ (⊥ : Subgroup G)) ⊔
        oPiCore {p | p ∉ π} (G ⧸ (⊥ : Subgroup G))) = ⊥ := by
      apply Subgroup.comap_injective (QuotientGroup.mk'_surjective (⊥ : Subgroup G))
      rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
      -- `piFittingSeries π G 1` は定義 (`piFittingSeries_succ`/`_zero` とも `rfl`) より
      -- ちょうどこの comap (bump 後は simp 経由だと instance 経路がずれるので defeq で渡す).
      exact hF1
    have h_all_bot : ∀ n, piFittingSeries π G n = ⊥ := by
      intro n
      induction n with
      | zero =>
        exact piFittingSeries_zero π G
      | succ n ih =>
        let e : G ⧸ piFittingSeries π G n ≃* G ⧸ (⊥ : Subgroup G) :=
          QuotientGroup.quotientMulEquivOfEq ih
        let Sₙ : Subgroup (G ⧸ piFittingSeries π G n) :=
          oPiCore π (G ⧸ piFittingSeries π G n) ⊔
            oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n)
        have hSₙ_map : Sₙ.map e.toMonoidHom =
            oPiCore π (G ⧸ (⊥ : Subgroup G)) ⊔
              oPiCore {p | p ∉ π} (G ⧸ (⊥ : Subgroup G)) := by
          dsimp [Sₙ, e]
          rw [Subgroup.map_sup, oPiCore.map_eq_of_mulEquiv π,
            oPiCore.map_eq_of_mulEquiv {p | p ∉ π}]
        have hSₙ_bot : Sₙ = ⊥ := by
          refine (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom)
            (H := Sₙ) e.injective).mp ?_
          rw [hSₙ_map, hQsup_bot]
        rw [piFittingSeries_succ]
        change Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n)) Sₙ = ⊥
        rw [hSₙ_bot, MonoidHom.comap_bot, QuotientGroup.ker_mk', ih]
    have htop_bot : (⊤ : Subgroup G) = ⊥ := by
      rw [← hn, h_all_bot n]
    exact top_ne_bot htop_bot
  have hF0_lt : piFittingSeries π G 0 < piFittingSeries π G 1 := by
    refine lt_of_le_of_ne (piFittingSeries_le_succ π G 0) ?_
    intro hEq
    exact hF1_ne_bot (by rw [← hEq, piFittingSeries_zero])
  have hQsup0 :=
    (piFittingSeries_lt_succ_iff π (G := G) 0).mp hF0_lt
  have hQsup : (oPiCore π (G ⧸ (⊥ : Subgroup G)) ⊔
      oPiCore {p | p ∉ π} (G ⧸ (⊥ : Subgroup G))) ≠ ⊥ := by
    -- `piFittingSeries π G 0 = ⊥` は `rfl` (bump 後は simp 経由だと instance 経路が
    -- ずれるので defeq で渡す).
    exact hQsup0
  intro hsup_bot
  have hπ_bot : oPiCore π G = ⊥ := by
    apply le_antisymm ?_ bot_le
    rw [← hsup_bot]
    exact le_sup_left
  have hπ'_bot : oPiCore {p | p ∉ π} G = ⊥ := by
    apply le_antisymm ?_ bot_le
    rw [← hsup_bot]
    exact le_sup_right
  have hQπ_bot : oPiCore π (G ⧸ (⊥ : Subgroup G)) = ⊥ :=
    oPiCore_quotient_bot_eq_bot_of_oPiCore_eq_bot π hπ_bot
  have hQπ'_bot : oPiCore {p | p ∉ π} (G ⧸ (⊥ : Subgroup G)) = ⊥ :=
    oPiCore_quotient_bot_eq_bot_of_oPiCore_eq_bot {p | p ∉ π} hπ'_bot
  exact hQsup (by rw [hQπ_bot, hQπ'_bot, bot_sup_eq])

/-- **π-separable disjunction**, split form:
`O_π(G) ≠ ⊥ ∨ O_{π'}(G) ≠ ⊥`. -/
theorem exists_oPiCore_ne_bot_or_oPi'Core_ne_bot_of_isPiSeparable
    {G : Type*} [Group G] [Finite G] (π : Set ℕ) [Nontrivial G] [IsPiSeparable π G] :
    oPiCore π G ≠ ⊥ ∨ oPiCore {p | p ∉ π} G ≠ ⊥ := by
  have hsup := oPiCore_sup_ne_bot_of_isPiSeparable (G := G) π
  by_cases hπ : oPiCore π G = ⊥
  · right
    intro hπ'
    exact hsup (by rw [hπ, hπ', bot_sup_eq])
  · exact Or.inl hπ

/-- A minimal normal subgroup of a finite π-separable group is either a π-group
or a π'-group. -/
private theorem minimal_normal_isPiGroup_or_isPiGroup_compl_of_isPiSeparable
    {G : Type*} [Group G] [Finite G] (π : Set ℕ) [IsPiSeparable π G]
    {M : Subgroup G} (hM : OddOrder.Isaacs.Ch02.IsMinimalNormal M) :
    Subgroup.IsPiGroup π M ∨ Subgroup.IsPiGroup {p | p ∉ π} M := by
  haveI hM_normal : M.Normal := hM.1
  haveI hM_nontrivial : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM.2.1
  haveI hM_piSep : IsPiSeparable π ↥M := normalSubgroup_isPiSeparable π G M
  let liftCore (ρ : Set ℕ) (hcore : oPiCore ρ ↥M ≠ ⊥) :
      Subgroup.IsPiGroup ρ M := by
    have hmap_ne_bot : (oPiCore ρ ↥M).map M.subtype ≠ ⊥ := by
      intro hmap
      exact hcore ((Subgroup.map_eq_bot_iff_of_injective
        (H := oPiCore ρ ↥M) M.subtype_injective).mp hmap)
    haveI hmap_normal : ((oPiCore ρ ↥M).map M.subtype).Normal := inferInstance
    have hmap_le_M : (oPiCore ρ ↥M).map M.subtype ≤ M := by
      simpa [M.range_subtype] using (oPiCore ρ ↥M).map_le_range M.subtype
    have hmap_eq_M : (oPiCore ρ ↥M).map M.subtype = M := by
      rcases hM.2.2 _ hmap_normal hmap_le_M with hbot | htop
      · exact absurd hbot hmap_ne_bot
      · exact htop
    have hcore_top : oPiCore ρ ↥M = ⊤ := by
      apply (Subgroup.map_subtype_inj (H := M)).mp
      rw [hmap_eq_M]
      rw [← MonoidHom.range_eq_map, M.range_subtype]
    intro p hp
    have hpiTop : Subgroup.IsPiGroup ρ (⊤ : Subgroup ↥M) := by
      rw [← hcore_top]
      exact oPiCore.isPiGroup ρ
    rw [← Subgroup.card_top (G := ↥M)] at hp
    exact hpiTop p hp
  rcases exists_oPiCore_ne_bot_or_oPi'Core_ne_bot_of_isPiSeparable
      (G := ↥M) π with hπ | hπ'
  · exact Or.inl (liftCore π hπ)
  · exact Or.inr (liftCore {p | p ∉ π} hπ')

/-- Strong-induction core for Hall existence in finite π-separable groups. -/
private theorem hall_exists_of_piSeparable_aux (π : Set ℕ) : ∀ n : ℕ,
    ∀ (G : Type*) [Group G] [Finite G], IsPiSeparable π G → Nat.card G ≤ n →
      ∃ H : Subgroup G, IsHallSubgroup π H := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ hcard
    exact absurd hcard (Nat.not_le_of_lt Nat.card_pos)
  | succ n ih =>
    intro G _ _ hPiSep hcard
    by_cases hsmall : Nat.card G ≤ n
    · exact ih G hPiSep hsmall
    by_cases hG_one : Nat.card G = 1
    · exact ⟨⊥, IsHallSubgroup.bot_of_card_eq_one π hG_one⟩
    haveI hG_nontrivial : Nontrivial G :=
      Finite.one_lt_card_iff_nontrivial.mp
        (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.card_pos.ne', hG_one⟩)
    obtain ⟨M, hM, _⟩ :=
      OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
    haveI hMnormal : M.Normal := hM.1
    have hM_ne_bot : M ≠ ⊥ := hM.2.1
    haveI hM_nontrivial : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
    have hM_card_ge_two : 2 ≤ Nat.card ↥M := Finite.one_lt_card
    have hquot_card : Nat.card (G ⧸ M) ≤ n := by
      have key : Nat.card G = Nat.card (G ⧸ M) * Nat.card ↥M :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup M
      have h1 : Nat.card (G ⧸ M) * 2 ≤ Nat.card G := by
        rw [key]
        exact Nat.mul_le_mul_left _ hM_card_ge_two
      omega
    haveI hQuot_piSep : IsPiSeparable π (G ⧸ M) :=
      quotient_isPiSeparable π G M
    obtain ⟨Hbar, hHbar⟩ := ih (G ⧸ M) hQuot_piSep hquot_card
    rcases minimal_normal_isPiGroup_or_isPiGroup_compl_of_isPiSeparable π hM with
      hM_pi | hM_pi'
    · -- If M is a π-group, the pullback of a π-Hall of G/M is π-Hall in G.
      set H : Subgroup G := Subgroup.comap (QuotientGroup.mk' M) Hbar with hH_def
      have hH_index : H.index = Hbar.index :=
        Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective (N := M))
      have hHbar_idx_pos : 0 < Hbar.index :=
        Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have hH_card_eq : Nat.card H = Nat.card Hbar * Nat.card ↥M := by
        have eq1 : Nat.card H * H.index = Nat.card G := Subgroup.card_mul_index H
        have eq2 : Nat.card Hbar * Hbar.index = Nat.card (G ⧸ M) :=
          Subgroup.card_mul_index Hbar
        have eq3 : Nat.card (G ⧸ M) * Nat.card ↥M = Nat.card G :=
          (Subgroup.card_eq_card_quotient_mul_card_subgroup M).symm
        have h_eq : Nat.card H * Hbar.index = (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by
          calc Nat.card H * Hbar.index
              = Nat.card H * H.index := by rw [hH_index]
            _ = Nat.card G := eq1
            _ = Nat.card (G ⧸ M) * Nat.card ↥M := eq3.symm
            _ = (Nat.card Hbar * Hbar.index) * Nat.card ↥M := by rw [eq2]
            _ = (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by ring
        exact Nat.mul_right_cancel hHbar_idx_pos h_eq
      refine ⟨H, ?_, ?_⟩
      · intro q hq_pf
        rw [hH_card_eq] at hq_pf
        rw [Nat.mem_primeFactors] at hq_pf
        obtain ⟨hq_prime, hq_dvd, _⟩ := hq_pf
        rcases hq_prime.dvd_mul.mp hq_dvd with h_in_Hbar | h_in_M
        · exact hHbar.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_Hbar, Nat.card_pos.ne'⟩)
        · exact hM_pi q (Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_M, Nat.card_pos.ne'⟩)
      · rw [hH_index]
        exact hHbar.2
    · -- If M is a π'-group, split the pullback by Schur-Zassenhaus.
      set H : Subgroup G := Subgroup.comap (QuotientGroup.mk' M) Hbar with hH_def
      have hH_index : H.index = Hbar.index :=
        Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective (N := M))
      have hM_le_H : M ≤ H := QuotientGroup.le_comap_mk' M Hbar
      have h_card_MH : Nat.card ↥(M.subgroupOf H) = Nat.card ↥M :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM_le_H).toEquiv
      have h_coprime_M_Hbar : Nat.Coprime (Nat.card ↥M) (Nat.card Hbar) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
        rw [Nat.dvd_gcd_iff] at hq_dvd
        have hq_M_pf : q ∈ (Nat.card ↥M).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.1, Nat.card_pos.ne'⟩
        have hq_Hbar_pf : q ∈ (Nat.card Hbar).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.2, Nat.card_pos.ne'⟩
        exact hM_pi' q hq_M_pf (hHbar.1 q hq_Hbar_pf)
      have h_idx_MH : (M.subgroupOf H).index = Nat.card Hbar := by
        have hMH_lag : Nat.card ↥(M.subgroupOf H) * (M.subgroupOf H).index = Nat.card ↥H :=
          Subgroup.card_mul_index (M.subgroupOf H)
        have hH_card_eq : Nat.card H = Nat.card Hbar * Nat.card ↥M := by
          have eq1 : Nat.card H * H.index = Nat.card G := Subgroup.card_mul_index H
          have eq2 : Nat.card Hbar * Hbar.index = Nat.card (G ⧸ M) :=
            Subgroup.card_mul_index Hbar
          have eq3 : Nat.card (G ⧸ M) * Nat.card ↥M = Nat.card G :=
            (Subgroup.card_eq_card_quotient_mul_card_subgroup M).symm
          have hHbar_idx_pos : 0 < Hbar.index :=
            Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
          have h_eq : Nat.card H * Hbar.index =
              (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by
            calc Nat.card H * Hbar.index
                = Nat.card H * H.index := by rw [hH_index]
              _ = Nat.card G := eq1
              _ = Nat.card (G ⧸ M) * Nat.card ↥M := eq3.symm
              _ = (Nat.card Hbar * Hbar.index) * Nat.card ↥M := by rw [eq2]
              _ = (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by ring
          exact Nat.mul_right_cancel hHbar_idx_pos h_eq
        rw [h_card_MH, hH_card_eq] at hMH_lag
        have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
        have : Nat.card ↥M * (M.subgroupOf H).index = Nat.card ↥M * Nat.card Hbar := by
          rw [hMH_lag, mul_comm (Nat.card Hbar)]
        exact Nat.mul_left_cancel hM_pos this
      have h_coprime_MH : Nat.Coprime (Nat.card ↥(M.subgroupOf H)) (M.subgroupOf H).index := by
        rw [h_card_MH, h_idx_MH]
        exact h_coprime_M_Hbar
      haveI : (M.subgroupOf H).Normal := hMnormal.subgroupOf H
      obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime h_coprime_MH
      have hK_index : K.index = Nat.card ↥(M.subgroupOf H) := hK.index_eq_card
      have hK_card : Nat.card ↥K = Nat.card Hbar := by
        have := hK.card_mul
        have hH_card_eq : Nat.card H = Nat.card Hbar * Nat.card ↥M := by
          have eq1 : Nat.card H * H.index = Nat.card G := Subgroup.card_mul_index H
          have eq2 : Nat.card Hbar * Hbar.index = Nat.card (G ⧸ M) :=
            Subgroup.card_mul_index Hbar
          have eq3 : Nat.card (G ⧸ M) * Nat.card ↥M = Nat.card G :=
            (Subgroup.card_eq_card_quotient_mul_card_subgroup M).symm
          have hHbar_idx_pos : 0 < Hbar.index :=
            Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
          have h_eq : Nat.card H * Hbar.index =
              (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by
            calc Nat.card H * Hbar.index
                = Nat.card H * H.index := by rw [hH_index]
              _ = Nat.card G := eq1
              _ = Nat.card (G ⧸ M) * Nat.card ↥M := eq3.symm
              _ = (Nat.card Hbar * Hbar.index) * Nat.card ↥M := by rw [eq2]
              _ = (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by ring
          exact Nat.mul_right_cancel hHbar_idx_pos h_eq
        rw [h_card_MH, hH_card_eq] at this
        have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
        have h_eq : Nat.card ↥M * Nat.card ↥K = Nat.card ↥M * Nat.card Hbar := by
          rw [this, mul_comm (Nat.card Hbar)]
        exact Nat.mul_left_cancel hM_pos h_eq
      have hKlift_card : Nat.card ↥(K.map H.subtype) = Nat.card Hbar := by
        rw [Subgroup.card_subtype, hK_card]
      have hKlift_index : (K.map H.subtype).index = Nat.card ↥M * Hbar.index := by
        rw [Subgroup.index_map, Subgroup.ker_subtype, sup_bot_eq, hK_index, h_card_MH,
            Subgroup.range_subtype, hH_index]
      refine ⟨K.map H.subtype, ?_, ?_⟩
      · intro q hq_pf
        rw [hKlift_card] at hq_pf
        exact hHbar.1 q hq_pf
      · intro q hq_pf hq_pi
        rw [hKlift_index] at hq_pf
        rw [Nat.mem_primeFactors] at hq_pf
        obtain ⟨hq_prime, hq_dvd, _⟩ := hq_pf
        rcases hq_prime.dvd_mul.mp hq_dvd with h_in_M | h_in_HbarIdx
        · have hq_in_M_pf : q ∈ (Nat.card ↥M).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_M, Nat.card_pos.ne'⟩
          exact hM_pi' q hq_in_M_pf hq_pi
        · have hq_in_HbarIdx_pf : q ∈ Hbar.index.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_HbarIdx, Subgroup.index_ne_zero_of_finite⟩
          exact hHbar.2 q hq_in_HbarIdx_pf hq_pi

/-- **Isaacs Thm 3.20**: finite π-separable groups have π-Hall subgroups. -/
theorem hall_exists_of_piSeparable [Finite G] (π : Set ℕ) [IsPiSeparable π G] :
    ∃ H : Subgroup G, IsHallSubgroup π H :=
  hall_exists_of_piSeparable_aux π (Nat.card G) G ‹IsPiSeparable π G› le_rfl

/-- **`C/B` nontrivial when `B < C`**:
`B < C` strict + `B ⊴ G` ⇒ `C.map (QuotientGroup.mk' B) ≠ ⊥`. -/
theorem Subgroup.map_quotientGroup_mk_ne_bot_of_lt {G : Type*} [Group G]
    {B C : Subgroup G} [B.Normal] (hBC : B < C) :
    C.map (QuotientGroup.mk' B) ≠ ⊥ := by
  intro h
  have hCleB : C ≤ B := by
    intro c hc
    have hmem : (QuotientGroup.mk' B) c ∈ C.map (QuotientGroup.mk' B) := ⟨c, hc, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact absurd hCleB (fun hCB => (lt_irrefl _) (hBC.trans_le hCB))

/-- **Hall-Higman 3.21 setup**:
`¬ centralizer(O) ≤ O ⇒ B := centralizer(O) ⊓ O < centralizer(O)`. -/
theorem hall_higman_B_lt_C_of_not_le {G : Type*} [Group G] (π : Set ℕ)
    (h_not_le : ¬ Subgroup.centralizer (oPiCore π G : Set G) ≤ oPiCore π G) :
    Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G <
      Subgroup.centralizer (oPiCore π G : Set G) := by
  refine lt_of_le_of_ne inf_le_left ?_
  intro h
  apply h_not_le
  rw [show Subgroup.centralizer (oPiCore π G : Set G) =
       Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G from h.symm]
  exact inf_le_right

/-- **Hall-Higman 3.21 case π closure**: K, B, C 関係 + K/B π-group + B < K ⇒ False. -/
theorem hall_higman_case_pi_contradiction
    {G : Type*} [Group G] [Finite G] (π : Set ℕ)
    {K : Subgroup G} [K.Normal]
    (hKle : K ≤ Subgroup.centralizer (oPiCore π G : Set G))
    (hBle : Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G ≤ K)
    (hQpi : ∀ p ∈ (Nat.card ((↥K) ⧸
        (Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G).subgroupOf K)).primeFactors,
      p ∈ π)
    (hStrict : Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G < K) :
    False := by
  have hBpi : Subgroup.IsPiGroup π
      (Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G) :=
    Subgroup.IsPiGroup.le inf_le_right (oPiCore.isPiGroup π)
  have hBsubpi : Subgroup.IsPiGroup π
      ((Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G).subgroupOf K) :=
    Subgroup.IsPiGroup.subgroupOf hBle hBpi
  have hKpi : Subgroup.IsPiGroup π K := fun p hp =>
    IsPiGroup.of_normal_quotient _ hBsubpi hQpi p hp
  have hKle_B := hall_higman_case_pi_K_le_B π hKpi hKle
  exact absurd hKle_B (lt_irrefl _ ∘ hStrict.trans_le)

/-- **Hall-Higman 3.21 case π body**: case π での K construction + 矛盾.
case π 仮定 (`oPiCore π (↥CB) ≠ ⊥`) から K = preimage of K_quot を構築し
`hall_higman_case_pi_contradiction` で False を導出. -/
private theorem hall_higman_case_pi_body
    {G : Type*} [Group G] [Finite G] (π : Set ℕ)
    (h_not_le : ¬ Subgroup.centralizer (oPiCore π G : Set G) ≤ oPiCore π G)
    (hCπ : oPiCore π ↥((Subgroup.centralizer (oPiCore π G : Set G)).map
        (QuotientGroup.mk' (Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G))) ≠ ⊥) :
    False := by
  set O : Subgroup G := oPiCore π G with hO_def
  set C : Subgroup G := Subgroup.centralizer (O : Set G) with hC_def
  set B : Subgroup G := C ⊓ O with hB_def
  haveI hO_normal : O.Normal := inferInstance
  haveI hC_normal : C.Normal := Subgroup.normal_centralizer
  haveI hB_normal : B.Normal := by rw [hB_def]; infer_instance
  have hBC_lt : B < C := hall_higman_B_lt_C_of_not_le π h_not_le
  set CB : Subgroup (G ⧸ B) := C.map (QuotientGroup.mk' B) with hCB_def
  haveI hCB_normal : CB.Normal := hC_normal.map _ QuotientGroup.mk_surjective
  set K_quot : Subgroup ↥CB := oPiCore π ↥CB
  haveI hKq_norm : K_quot.Normal := inferInstance
  haveI hKq_char : K_quot.Characteristic := inferInstance
  set K_GB : Subgroup (G ⧸ B) := K_quot.map CB.subtype with hKGB_def
  haveI hKGB_norm : K_GB.Normal := inferInstance
  set K : Subgroup G := K_GB.comap (QuotientGroup.mk' B) with hK_def
  haveI hK_norm : K.Normal := inferInstance
  have hKGB_le_CB : K_GB ≤ CB := by
    have hRangEq : CB = (⊤ : Subgroup ↥CB).map CB.subtype := by
      rw [← MonoidHom.range_eq_map]; exact CB.range_subtype.symm
    rw [hRangEq]; exact Subgroup.map_mono le_top
  have hKle_C : K ≤ C := Subgroup.comap_le_of_le_map_quotient inf_le_left hKGB_le_CB
  have hBle_K : B ≤ K := by
    intro x hx
    simp only [hK_def, Subgroup.mem_comap]
    rw [show (QuotientGroup.mk' B) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact K_GB.one_mem
  have hBK_lt : B < K := by
    refine lt_of_le_of_ne hBle_K ?_
    intro hBKeq
    apply hCπ
    have hKGB_bot : K_GB = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hxy⟩ := QuotientGroup.mk_surjective y
      rw [← hxy] at hy ⊢
      have hx_K : x ∈ K := Subgroup.mem_comap.mpr hy
      rw [← hBKeq] at hx_K
      exact (QuotientGroup.eq_one_iff x).mpr hx_K
    apply Subgroup.map_injective CB.subtype_injective
    rw [Subgroup.map_bot]
    exact hKGB_bot
  have hQpi : ∀ p ∈ (Nat.card ((↥K) ⧸ (B.subgroupOf K))).primeFactors, p ∈ π := by
    intro p hp
    rw [Subgroup.nat_card_quotient_subgroupOf_eq_card_map B K] at hp
    have hKmap_eq : K.map (QuotientGroup.mk' B) = K_GB :=
      Subgroup.map_comap_eq_self_of_surjective QuotientGroup.mk_surjective K_GB
    rw [hKmap_eq] at hp
    have hcard : Nat.card ↥K_GB = Nat.card ↥K_quot :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective K_quot CB.subtype CB.subtype_injective).symm.toEquiv
    rw [hcard] at hp
    exact (oPiCore.isPiGroup (G := ↥CB) π) p hp
  exact hall_higman_case_pi_contradiction π hKle_C hBle_K hQpi hBK_lt

/-- **Hall-Higman 3.21 case π' body**: case π' での K + Schur-Zassenhaus + H' ⊴ K + 矛盾. -/
private theorem hall_higman_case_pi'_body
    {G : Type*} [Group G] [Finite G] (π : Set ℕ)
    (hπ' : oPiCore {p | p ∉ π} G = ⊥)
    (h_not_le : ¬ Subgroup.centralizer (oPiCore π G : Set G) ≤ oPiCore π G)
    (hCπ' : oPiCore {p | p ∉ π} ↥((Subgroup.centralizer (oPiCore π G : Set G)).map
        (QuotientGroup.mk' (Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G))) ≠ ⊥) :
    False := by
  set O : Subgroup G := oPiCore π G with hO_def
  set C : Subgroup G := Subgroup.centralizer (O : Set G) with hC_def
  set B : Subgroup G := C ⊓ O with hB_def
  haveI hO_normal : O.Normal := inferInstance
  haveI hC_normal : C.Normal := Subgroup.normal_centralizer
  haveI hB_normal : B.Normal := by rw [hB_def]; infer_instance
  have hBC_lt : B < C := hall_higman_B_lt_C_of_not_le π h_not_le
  set CB : Subgroup (G ⧸ B) := C.map (QuotientGroup.mk' B) with hCB_def
  haveI hCB_normal : CB.Normal := hC_normal.map _ QuotientGroup.mk_surjective
  set K_quot : Subgroup ↥CB := oPiCore {p | p ∉ π} ↥CB
  haveI hKq_norm : K_quot.Normal := inferInstance
  haveI hKq_char : K_quot.Characteristic := inferInstance
  set K_GB : Subgroup (G ⧸ B) := K_quot.map CB.subtype with hKGB_def
  haveI hKGB_norm : K_GB.Normal := inferInstance
  set K : Subgroup G := K_GB.comap (QuotientGroup.mk' B) with hK_def
  haveI hK_norm : K.Normal := inferInstance
  have hKGB_le_CB : K_GB ≤ CB := by
    have hRangEq : CB = (⊤ : Subgroup ↥CB).map CB.subtype := by
      rw [← MonoidHom.range_eq_map]; exact CB.range_subtype.symm
    rw [hRangEq]; exact Subgroup.map_mono le_top
  have hKle_C : K ≤ C := Subgroup.comap_le_of_le_map_quotient inf_le_left hKGB_le_CB
  have hBle_K : B ≤ K := by
    intro x hx
    simp only [hK_def, Subgroup.mem_comap]
    rw [show (QuotientGroup.mk' B) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact K_GB.one_mem
  have hBK_lt : B < K := by
    refine lt_of_le_of_ne hBle_K ?_
    intro hBKeq
    apply hCπ'
    have hKGB_bot : K_GB = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hxy⟩ := QuotientGroup.mk_surjective y
      rw [← hxy] at hy ⊢
      have hx_K : x ∈ K := Subgroup.mem_comap.mpr hy
      rw [← hBKeq] at hx_K
      exact (QuotientGroup.eq_one_iff x).mpr hx_K
    apply Subgroup.map_injective CB.subtype_injective
    rw [Subgroup.map_bot]
    exact hKGB_bot
  have hBpi : Subgroup.IsPiGroup π B :=
    Subgroup.IsPiGroup.le inf_le_right (oPiCore.isPiGroup π)
  have hBsub_pi : Subgroup.IsPiGroup π (B.subgroupOf K) :=
    Subgroup.IsPiGroup.subgroupOf hBle_K hBpi
  have hKBindex_pi' : ∀ p ∈ (B.subgroupOf K).index.primeFactors, p ∉ π := by
    intro p hp
    have hindex_eq : (B.subgroupOf K).index = Nat.card ↥K_GB := by
      change Nat.card (↥K ⧸ (B.subgroupOf K)) = _
      rw [Subgroup.nat_card_quotient_subgroupOf_eq_card_map B K]
      have hKmap_eq : K.map (QuotientGroup.mk' B) = K_GB :=
        Subgroup.map_comap_eq_self_of_surjective QuotientGroup.mk_surjective K_GB
      rw [hKmap_eq]
    rw [hindex_eq] at hp
    have hcard : Nat.card ↥K_GB = Nat.card ↥K_quot :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective K_quot CB.subtype CB.subtype_injective).symm.toEquiv
    rw [hcard] at hp
    exact (oPiCore.isPiGroup (G := ↥CB) {p | p ∉ π}) p hp
  haveI hBsub_K_normal : (B.subgroupOf K).Normal := inferInstance
  have hCoprime : Nat.Coprime (Nat.card ↥(B.subgroupOf K)) (B.subgroupOf K).index :=
    Nat.coprime_of_isPiGroup_of_isPiGroup_compl Nat.card_pos.ne'
      Subgroup.index_ne_zero_of_finite hBsub_pi hKBindex_pi'
  obtain ⟨H', hH'_compl⟩ :=
    Subgroup.exists_right_complement'_of_coprime (N := B.subgroupOf K) hCoprime
  have hCommute : ∀ n ∈ B.subgroupOf K, ∀ h ∈ H', n * h = h * n := by
    intro n hn h _
    apply Subtype.ext
    change n.val * h.val = h.val * n.val
    have hnB : n.val ∈ B := hn
    have hnO : n.val ∈ O := by
      rw [hB_def, Subgroup.mem_inf] at hnB
      exact hnB.2
    have hh_in_K : h.val ∈ K := h.property
    have hh_in_C : h.val ∈ C := hKle_C hh_in_K
    exact (Subgroup.mem_centralizer_iff.mp hh_in_C) n.val hnO
  haveI hH'_normal : H'.Normal := Subgroup.normal_complement_of_commute hH'_compl hCommute
  have hH'_card : Nat.card ↥H' = (B.subgroupOf K).index := by
    have hCompl_card : Nat.card ↥(B.subgroupOf K) * Nat.card ↥H' = Nat.card ↥K := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (Subgroup.IsComplement.equiv hH'_compl).symm
    have hKcard : Nat.card ↥K =
        Nat.card (↥K ⧸ B.subgroupOf K) * Nat.card ↥(B.subgroupOf K) :=
      (B.subgroupOf K).card_eq_card_quotient_mul_card_subgroup
    have hpos : 0 < Nat.card ↥(B.subgroupOf K) := Nat.card_pos
    have heq : Nat.card ↥H' * Nat.card ↥(B.subgroupOf K) =
        (B.subgroupOf K).index * Nat.card ↥(B.subgroupOf K) := by
      rw [Nat.mul_comm (Nat.card ↥H') _, hCompl_card, hKcard]
      change (B.subgroupOf K).index * Nat.card ↥(B.subgroupOf K) =
           (B.subgroupOf K).index * Nat.card ↥(B.subgroupOf K)
      rfl
    exact Nat.eq_of_mul_eq_mul_right hpos heq
  have hH'_pi' : Subgroup.IsPiGroup {p | p ∉ π} H' := by
    intro p hp
    rw [hH'_card] at hp
    exact hKBindex_pi' p hp
  have hH'_le : H' ≤ oPiCore {p | p ∉ π} ↥K := hH'_pi'.le_oPiCore
  haveI hOpi'_KG_normal : ((oPiCore {p | p ∉ π} ↥K).map K.subtype).Normal := inferInstance
  have hOpi'_KG_pi' : Subgroup.IsPiGroup {p | p ∉ π}
      ((oPiCore {p | p ∉ π} ↥K).map K.subtype) := by
    intro p hp
    have hcard : Nat.card ↥((oPiCore {p | p ∉ π} ↥K).map K.subtype) =
        Nat.card ↥(oPiCore {p | p ∉ π} ↥K) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).symm.toEquiv
    rw [hcard] at hp
    exact oPiCore.isPiGroup (G := ↥K) {p | p ∉ π} p hp
  have hKG_le_bot : (oPiCore {p | p ∉ π} ↥K).map K.subtype = ⊥ :=
    eq_bot_of_isPiGroup_of_oPiCore_eq_bot {p | p ∉ π} hOpi'_KG_pi' hπ'
  have hOpi'_K_bot : oPiCore {p | p ∉ π} ↥K = ⊥ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_bot]
    exact hKG_le_bot
  have hH'_bot : H' = ⊥ := le_bot_iff.mp (hH'_le.trans (le_of_eq hOpi'_K_bot))
  have hBsub_ne_top : B.subgroupOf K ≠ ⊤ := by
    intro hEq
    rw [Subgroup.subgroupOf_eq_top] at hEq
    exact absurd hEq (fun hKleB => (lt_irrefl _) (hBK_lt.trans_le hKleB))
  have hH'_card_gt : 1 < Nat.card ↥H' := by
    rw [hH'_card]
    exact Subgroup.one_lt_index_of_ne_top hBsub_ne_top
  have hH'_card_one : Nat.card ↥H' = 1 := by
    rw [hH'_bot, Subgroup.card_bot]
  omega

/-- **Isaacs Thm 3.21 Hall-Higman 1.2.3** ⭐ **FT クリティカル**.
`G` π-separable + `O_{π'}(G) = ⊥` ⇒ `C_G(O_π(G)) ≤ O_π(G)`.

**所在**: Isaacs PDF p.94 の証明は **Ch.3 内部資産で完結** — π-separable normal series +
`Subgroup.centralizer` + Schur-Zassenhaus + Sylow のみを使う.

**証明戦略** (Isaacs p.94, 5 段階):
1. `C := C_G(O_π(G))`, `B := C ⊓ O_π(G)`. 目標 `B = C`. 背理法で `B < C`.
2. `B` は π-group, `B, C` は G で正規 (characteristic も).
3. `C/B` 非自明 π-separable ⇒ 非自明 characteristic 部分群 `K/B` で π-group か π'-group.
   - `K/B ⊴ G/B` ⇒ `K ⊴ G`.
4. Case `K/B` π-group: `K` 正規 π-subgroup (B π-group + K/B π-group). `K ⊆ O_π(G)` で
   `B < K ⊆ C` だが `B = C ⊓ O_π(G)` で矛盾.
5. Case `K/B` π'-group: Schur-Zassenhaus で複合 `K = B ⋊ H`, `H > 1` π'-group.
   `H ⊆ C ⊆ C_G(B)` で `H ⊴ K`. `H ⊆ O_{π'}(K) ⊴ G` で `O_{π'}(G) = ⊥` 矛盾.

**下流被引用**: Ch.4 Thm 4.33 (mmd L2659), Ch.7 Thm 7.5 (L3853), Thm 7.6 (L3802) の 3 箇所.

**実装状態** ⭐ sorry-free. case π body + case π' body を
`exists_oPiCore_ne_bot_or_oPi'Core_ne_bot_of_isPiSeparable` (↥CB に対して) で場合分けして組み立て.
-/
theorem hall_higman_1_2_3 [Finite G] (π : Set ℕ) [IsPiSeparable π G]
    (hπ' : oPiCore {p | p ∉ π} G = ⊥) :
    Subgroup.centralizer (oPiCore π G : Set G) ≤ oPiCore π G := by
  by_contra h_not_le
  set O : Subgroup G := oPiCore π G with hO_def
  set C : Subgroup G := Subgroup.centralizer (O : Set G) with hC_def
  set B : Subgroup G := C ⊓ O with hB_def
  haveI hO_normal : O.Normal := inferInstance
  haveI hC_normal : C.Normal := Subgroup.normal_centralizer
  haveI hB_normal : B.Normal := by rw [hB_def]; infer_instance
  have hBC_lt : B < C := hall_higman_B_lt_C_of_not_le π h_not_le
  set CB : Subgroup (G ⧸ B) := C.map (QuotientGroup.mk' B) with hCB_def
  have hCB_ne_bot : CB ≠ ⊥ := Subgroup.map_quotientGroup_mk_ne_bot_of_lt hBC_lt
  haveI hCB_nontrivial : Nontrivial ↥CB := (Subgroup.nontrivial_iff_ne_bot CB).mpr hCB_ne_bot
  haveI hCB_normal : CB.Normal := hC_normal.map _ QuotientGroup.mk_surjective
  haveI hQuot_piSeparable : IsPiSeparable π (G ⧸ B) :=
    quotient_isPiSeparable π G B
  haveI hCB_piSeparable : IsPiSeparable π ↥CB :=
    normalSubgroup_isPiSeparable π (G ⧸ B) CB
  rcases exists_oPiCore_ne_bot_or_oPi'Core_ne_bot_of_isPiSeparable (G := ↥CB) π with
    hπCase | hπ'Case
  · exact hall_higman_case_pi_body π h_not_le hπCase
  · exact hall_higman_case_pi'_body π hπ' h_not_le hπ'Case

/-- **Hall-Higman 1.2.3 系**: `G` π-separable + `O_{π'}(G) = ⊥` ⇒
`C_G(O_π(G)) = Z(O_π(G))` (i.e., centralizer of O_π is the center of O_π).

`C_G(O_π(G)) ≤ O_π(G)` (Hall-Higman 3.21) + 一般 `Z(H) = H ⊓ C_G(H)` から従う. -/
theorem centralizer_oPiCore_eq_center [Finite G] (π : Set ℕ) [IsPiSeparable π G]
    (hπ' : oPiCore {p | p ∉ π} G = ⊥) :
    Subgroup.centralizer (oPiCore π G : Set G) =
      (Subgroup.center ↥(oPiCore π G)).map (oPiCore π G).subtype := by
  apply le_antisymm
  · -- C_G(O) ⊆ O (Hall-Higman) so g ∈ C_G(O) ⇒ ⟨g, _⟩ ∈ Z(↥O)
    intro g hg
    have hg_O : g ∈ oPiCore π G := hall_higman_1_2_3 π hπ' hg
    refine ⟨⟨g, hg_O⟩, ?_, rfl⟩
    change (⟨g, hg_O⟩ : ↥(oPiCore π G)) ∈ Subgroup.center ↥(oPiCore π G)
    rw [Subgroup.mem_center_iff]
    rintro ⟨h, hh⟩
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hg h hh
  · -- Z(↥O) image ⊆ C_G(O) trivially
    rintro _ ⟨⟨g, hg_O⟩, hg_center, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hc : (⟨h, hh⟩ : ↥(oPiCore π G)) * ⟨g, hg_O⟩ = ⟨g, hg_O⟩ * ⟨h, hh⟩ :=
      Subgroup.mem_center_iff.mp hg_center ⟨h, hh⟩
    exact congr_arg Subtype.val hc

/-- `O_{π',π}(G)`: the preimage of `O_π(G/O_{π'}(G))`.

This is the subgroup appearing in Isaacs Thm 3.22.  The theorem is usually stated as
`[O_{π',π}(G), O_{π',π}(G)] ≤ O_{π'}(G)`, equivalent to π-length at most one. -/
def oPiPrimePiCore (π : Set ℕ) (G : Type*) [Group G] : Subgroup G :=
  Subgroup.comap (QuotientGroup.mk' (oPiCore {p | p ∉ π} G))
    (oPiCore π (G ⧸ oPiCore {p | p ∉ π} G))

instance oPiPrimePiCore.normal (π : Set ℕ) (G : Type*) [Group G] :
    (oPiPrimePiCore π G).Normal := by
  rw [oPiPrimePiCore]
  infer_instance

/-- The lower `O_{π'}` layer is contained in `O_{π',π}`. -/
theorem oPiCore_compl_le_oPiPrimePiCore (π : Set ℕ) (G : Type*) [Group G] :
    oPiCore {p | p ∉ π} G ≤ oPiPrimePiCore π G := by
  intro g hg
  rw [oPiPrimePiCore, Subgroup.mem_comap]
  rw [show (QuotientGroup.mk' (oPiCore {p | p ∉ π} G)) g = 1
      from (QuotientGroup.eq_one_iff g).mpr hg]
  exact (oPiCore π (G ⧸ oPiCore {p | p ∉ π} G)).one_mem

open scoped commutatorElement in
/-- **Isaacs Thm 3.22 (片向き; π-length ≤ 1 の Hall-Higman 系)**:
`G` π-separable + abelian な π-Hall ⇒ `[O_{π',π}(G), O_{π',π}(G)] ≤ O_{π'}(G)`.

`O_{π',π}(G)` (= `π` を `O_{π'}(G)` 上に乗せた π-層) の交換子部分群が `O_{π'}(G)` に
含まれる, つまり π-length ≤ 1 と同値. -/
theorem piLength_le_one_of_abelian_pi_hall [Finite G] (π : Set ℕ) [IsPiSeparable π G]
    (hAb : ∀ (H : Subgroup G) (_ : IsHallSubgroup π H), ∀ a ∈ H, ∀ b ∈ H,
      a * b = b * a) :
    ⁅oPiPrimePiCore π G, oPiPrimePiCore π G⁆ ≤ oPiCore {p | p ∉ π} G := by
  let N : Subgroup G := oPiCore {p | p ∉ π} G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let O : Subgroup (G ⧸ N) := oPiCore π (G ⧸ N)
  let K : Subgroup G := oPiPrimePiCore π G
  have hK_def : K = O.comap q := by
    dsimp [K, O, q, N, oPiPrimePiCore]
  obtain ⟨H, hH⟩ := hall_exists_of_piSeparable π (G := G)
  let Hbar : Subgroup (G ⧸ N) := H.map q
  have hHbar : IsHallSubgroup π Hbar := hH.map_quotient
  have hO_le_Hbar : O ≤ Hbar :=
    Subgroup.IsPiGroup.normal_le_hall (oPiCore.isPiGroup π) hHbar
  have hHbar_ab : ∀ a ∈ Hbar, ∀ b ∈ Hbar, a * b = b * a := by
    intro a ha b hb
    rcases ha with ⟨a₀, ha₀, rfl⟩
    rcases hb with ⟨b₀, hb₀, rfl⟩
    simpa using congrArg q (hAb H hH a₀ ha₀ b₀ hb₀)
  have hO_comm : ⁅O, O⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have hc : ⁅a, b⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (hHbar_ab a (hO_le_Hbar ha) b (hO_le_Hbar hb))
    simpa [Subgroup.mem_bot] using hc
  have hK_map : K.map q = O := by
    rw [hK_def]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) O
  have hmap_comm : (⁅K, K⁆).map q = ⊥ := by
    rw [Subgroup.map_commutator, hK_map, hO_comm]
  have hle_ker : ⁅K, K⁆ ≤ q.ker := (Subgroup.map_eq_bot_iff ⁅K, K⁆).mp hmap_comm
  simpa [K, q, N, QuotientGroup.ker_mk'] using hle_ker

end -- 3D

section /- 3E: Coprime action (pp. 96-104) -/

variable {G : Type*} [Group G]

/-! ### Isaacs §3E (Coprime action)

`A` が `G` に作用し `gcd(|A|, |G|) = 1` の場合の構造論. BG/Peterfalvi 全体で頻用.

**含まれる結果**:
- Thm 3.23: coprime action ⇒ A-invariant Sylow 存在・共役・unique up to A-action.
- Lemma 3.24 (Glauberman lemma): A 作用 + transitive G 作用 のコンパチで A-fixed 元存在.
- Thm 3.25-3.27: A-不変部分群と商の対応 (`C_G(A)` 経由).
- Thm 3.28: A-不変 Sylow と `C_G(A)` の Sylow の対応.
- Thm 3.29-3.31: 軌道構造 (Hartley-Turull, orbit-size 主張).
- Thm 3.32-3.34: テクニカル系 (`[G,A,A] = [G,A]` Three-Subgroup Lemma 経由 等).

**形式化状態**: 全 stub.  完全実装は ~8-12 週の大規模作業 (mathlib coprime action machinery
の活用 + Isaacs 流の細部). 別 phase で進める. -/

/-- **A-不変部分群**: `φ : A →* MulAut G` の作用下で `H ≤ G` が `A`-不変.
i.e., `∀ a ∈ A, φ(a) • H = H`. -/
def IsAInvariant {A : Type*} [Group A] (φ : A →* MulAut G) (H : Subgroup G) : Prop :=
  ∀ a : A, (φ a : MulAut G) • H = H

/-- A-不変な H に対し, 要素レベルで `(φ a) g ∈ H` が成立. -/
theorem IsAInvariant.smul_mem {A : Type*} [Group A] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : IsAInvariant φ H) (a : A) {g : G} (hg : g ∈ H) : (φ a) g ∈ H := by
  have : (φ a) g ∈ (φ a) • H := ⟨g, hg, rfl⟩
  rwa [hH a] at this

/-- **A-不変の特徴付け**: `IsAInvariant φ H ↔ ∀ a g, g ∈ H ⇒ (φ a) g ∈ H`. -/
theorem isAInvariant_iff_smul_mem {A : Type*} [Group A] {φ : A →* MulAut G} {H : Subgroup G} :
    IsAInvariant φ H ↔ ∀ a : A, ∀ g, g ∈ H → (φ a) g ∈ H := by
  refine ⟨fun hH a g hg => hH.smul_mem a hg, fun h a => ?_⟩
  -- (φ a) • H = H. Show le_antisymm.
  apply le_antisymm
  · -- (φ a) • H ≤ H: image is in H by assumption
    rintro _ ⟨g, hg, rfl⟩
    exact h a g hg
  · -- H ≤ (φ a) • H: take h, find preimage via (φ a)⁻¹
    intro g hg
    refine ⟨(φ a)⁻¹ g, ?_, MulAut.apply_inv_self G (φ a) g⟩
    -- (φ a)⁻¹ g ∈ H: use h with a := a⁻¹, since φ is a hom, (φ a⁻¹) = (φ a)⁻¹
    have hg' : (φ a⁻¹) g ∈ H := h a⁻¹ g hg
    rw [φ.map_inv] at hg'
    exact hg'

/-- A-不変な H に対し, 要素レベルで `(φ a)⁻¹ g ∈ H` が成立 (= 逆作用 a⁻¹ で smul_mem). -/
theorem IsAInvariant.inv_smul_mem {A : Type*} [Group A] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : IsAInvariant φ H) (a : A) {g : G} (hg : g ∈ H) : (φ a)⁻¹ g ∈ H := by
  have hHinv : (φ a⁻¹) • H = H := hH a⁻¹
  rw [φ.map_inv] at hHinv
  have : (φ a)⁻¹ g ∈ (φ a)⁻¹ • H := ⟨g, hg, rfl⟩
  rwa [hHinv] at this

/-- If an invariant subgroup of `W` is acted on by an automorphism whose underlying value is
conjugation by `g` in the ambient group, then `g` normalizes its image under `W.subtype`. -/
theorem IsAInvariant.mem_normalizer_map_subtype_of_smul_val {W : Subgroup G}
    {A : Type*} [Group A] {φ : A →* MulAut W} {L : Subgroup W}
    (hL : IsAInvariant φ L) {a : A} {g : G}
    (hval : ∀ k : W, ((φ a k : W) : G) = g * (k : G) * g⁻¹) :
    g ∈ Subgroup.normalizer ((L.map W.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨φ a k, hL.smul_mem _ hk, hval k⟩
  · rintro ⟨k, hk, hkeq⟩
    refine ⟨(φ a)⁻¹ k, hL.inv_smul_mem _ hk, ?_⟩
    have hv2 := hval ((φ a)⁻¹ k)
    rw [MulAut.apply_inv_self] at hv2
    have h3 := hv2.symm.trans hkeq
    exact mul_left_cancel (mul_right_cancel h3)

/-- ⊤ は常に A-不変. -/
theorem IsAInvariant.top {A : Type*} [Group A] (φ : A →* MulAut G) :
    IsAInvariant φ (⊤ : Subgroup G) := fun a => by
  ext x
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_top]

/-- ⊥ は常に A-不変. -/
theorem IsAInvariant.bot {A : Type*} [Group A] (φ : A →* MulAut G) :
    IsAInvariant φ (⊥ : Subgroup G) := fun _ => Subgroup.smul_bot _

/-- A-不変部分群の交わりは A-不変. -/
theorem IsAInvariant.inf {A : Type*} [Group A] {φ : A →* MulAut G} {H K : Subgroup G}
    (hH : IsAInvariant φ H) (hK : IsAInvariant φ K) : IsAInvariant φ (H ⊓ K) := fun a => by
  rw [Subgroup.smul_inf, hH a, hK a]

/-- A-不変部分群の sup は A-不変. -/
theorem IsAInvariant.sup {A : Type*} [Group A] {φ : A →* MulAut G} {H K : Subgroup G}
    (hH : IsAInvariant φ H) (hK : IsAInvariant φ K) : IsAInvariant φ (H ⊔ K) := fun a => by
  rw [Subgroup.smul_sup, hH a, hK a]

/-- Conjugating an `A`-invariant subgroup by an `A`-fixed element preserves invariance. -/
theorem IsAInvariant.mulAut_conj_smul_of_fixed {A : Type*} [Group A] {φ : A →* MulAut G}
    {H : Subgroup G} (hH : IsAInvariant φ H) {c : G} (hc : ∀ a : A, (φ a) c = c) :
    IsAInvariant φ (MulAut.conj c • H) := by
  rw [isAInvariant_iff_smul_mem]
  intro a x hx
  rw [Subgroup.pointwise_smul_def, Subgroup.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(φ a) y, hH.smul_mem a hy, ?_⟩
  simp [MulAut.conj_apply, map_mul, map_inv, hc a]

/-- **Characteristic 部分群は常に A-不変**: H.Characteristic ⇒ IsAInvariant φ H for any φ.
mathlib `characteristic_iff_map_eq` 経由. -/
theorem IsAInvariant.of_characteristic {A : Type*} [Group A] (φ : A →* MulAut G)
    {H : Subgroup G} [hH : H.Characteristic] : IsAInvariant φ H := fun a => by
  change H.map (φ a).toMonoidHom = H
  exact (Subgroup.characteristic_iff_map_eq.mp hH) (φ a)

/-- `derivedSeries G n` は A-不変 (characteristic instance 経由). -/
theorem IsAInvariant.derivedSeries {A : Type*} [Group A] (φ : A →* MulAut G) (n : ℕ) :
    IsAInvariant φ (derivedSeries G n) :=
  IsAInvariant.of_characteristic φ

/-- `(⊤ : Subgroup G).lowerCentralSeries n` (旧 `lowerCentralSeries G n`) は A-不変
(characteristic instance 経由). -/
theorem IsAInvariant.lowerCentralSeries {A : Type*} [Group A] (φ : A →* MulAut G) (n : ℕ) :
    IsAInvariant φ ((⊤ : Subgroup G).lowerCentralSeries n) :=
  IsAInvariant.of_characteristic φ

/-- `Subgroup.center G` は A-不変 (characteristic instance 経由). -/
theorem IsAInvariant.center {A : Type*} [Group A] (φ : A →* MulAut G) :
    IsAInvariant φ (Subgroup.center G) :=
  IsAInvariant.of_characteristic φ

/-- `fitting G` (Fitting subgroup) は A-不変 (characteristic instance 経由). -/
theorem IsAInvariant.fittingSubgroup {A : Type*} [Group A] [Finite G] (φ : A →* MulAut G) :
    IsAInvariant φ (OddOrder.Isaacs.Ch01.fitting G) :=
  IsAInvariant.of_characteristic φ

/-- `commutator G = G'` は A-不変 (derivedSeries 1 経由). -/
theorem IsAInvariant.commutator_self {A : Type*} [Group A] (φ : A →* MulAut G) :
    IsAInvariant φ (commutator G) := by
  rw [← derivedSeries_one]
  exact IsAInvariant.derivedSeries φ 1

/-- `frattini G` (Frattini subgroup, mathlib def) は A-不変 (characteristic instance 経由). -/
theorem IsAInvariant.frattini {A : Type*} [Group A] (φ : A →* MulAut G) :
    IsAInvariant φ (_root_.frattini G) :=
  IsAInvariant.of_characteristic φ

/-- A-不変な集合 S の生成部分群 `Subgroup.closure S` は A-不変. -/
theorem IsAInvariant.closure_of_invariant_set {A : Type*} [Group A] {φ : A →* MulAut G}
    {S : Set G} (hS : ∀ a : A, (φ a) '' S = S) :
    IsAInvariant φ (Subgroup.closure S) := fun a => by
  change (Subgroup.closure S).map (φ a).toMonoidHom = Subgroup.closure S
  rw [MonoidHom.map_closure]
  congr 1
  exact hS a

/-- A-不変 + A-不変 の commutator は A-不変 (`Subgroup.map_commutator`). -/
theorem IsAInvariant.commutator {A : Type*} [Group A] {φ : A →* MulAut G} {H K : Subgroup G}
    (hH : IsAInvariant φ H) (hK : IsAInvariant φ K) :
    IsAInvariant φ ⁅H, K⁆ := fun a => by
  change ⁅H, K⁆.map (φ a).toMonoidHom = ⁅H, K⁆
  rw [Subgroup.map_commutator]
  rw [show H.map (φ a).toMonoidHom = H from hH a,
      show K.map (φ a).toMonoidHom = K from hK a]

/-- A-不変部分群の normalizer は A-不変 (`Subgroup.map_normalizer_eq_of_bijective`). -/
theorem IsAInvariant.normalizer {A : Type*} [Group A] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : IsAInvariant φ H) : IsAInvariant φ (Subgroup.normalizer H) := fun a => by
  change (Subgroup.normalizer H).map (φ a).toMonoidHom = Subgroup.normalizer H
  rw [Subgroup.map_normalizer_eq_of_bijective H (φ a).bijective,
      show H.map (φ a).toMonoidHom = H from hH a]

/-- A-不変部分群の centralizer は A-不変. `Subgroup.map_centralizer_eq_of_bijective` +
`hH a` で (φ a) '' H = H が言えるので clean. -/
theorem IsAInvariant.centralizer {A : Type*} [Group A] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : IsAInvariant φ H) :
    IsAInvariant φ (Subgroup.centralizer (H : Set G)) := fun a => by
  change (Subgroup.centralizer (H : Set G)).map (φ a).toMonoidHom
      = Subgroup.centralizer (H : Set G)
  rw [Subgroup.map_centralizer_eq_of_bijective _ _ (φ a).bijective]
  congr 1
  -- want: (φ a).toMonoidHom '' (H : Set G) = (H : Set G)
  have hH_set : ((H.map (φ a).toMonoidHom : Subgroup G) : Set G) = (H : Set G) := by
    rw [show H.map (φ a).toMonoidHom = H from hH a]
  exact hH_set

/-- A-不変部分群族の iSup は A-不変. -/
theorem IsAInvariant.iSup {A : Type*} [Group A] {φ : A →* MulAut G} {ι : Sort*}
    {f : ι → Subgroup G} (hf : ∀ i, IsAInvariant φ (f i)) :
    IsAInvariant φ (⨆ i, f i) := fun a => by
  change (⨆ i, f i).map (φ a).toMonoidHom = ⨆ i, f i
  rw [Subgroup.map_iSup]
  exact iSup_congr fun i => hf i a

/-- A-不変部分群族の iInf は A-不変 (非空 ι が必要; `(φ a)` 単射性を利用). -/
theorem IsAInvariant.iInf {A : Type*} [Group A] {φ : A →* MulAut G} {ι : Sort*} [Nonempty ι]
    {f : ι → Subgroup G} (hf : ∀ i, IsAInvariant φ (f i)) :
    IsAInvariant φ (⨅ i, f i) := fun a => by
  change (⨅ i, f i).map (φ a).toMonoidHom = ⨅ i, f i
  rw [Subgroup.map_iInf _ (φ a).injective]
  exact iInf_congr fun i => hf i a

/-- **A-不変部分群への制限作用**: `φ : A →* MulAut G` + A-inv `H` から
`A →* MulAut ↥H` を構成する. 各 `a : A` で `(φ a)` は `H` を保つので
restricted MulEquiv ↥H ↥H を作る. -/
def IsAInvariant.restrict {A : Type*} [Group A] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : IsAInvariant φ H) : A →* MulAut ↥H where
  toFun a := {
    toFun := fun h => ⟨(φ a) h.val, hH.smul_mem a h.property⟩
    invFun := fun h => ⟨(φ a)⁻¹ h.val, hH.inv_smul_mem a h.property⟩
    left_inv := fun h => Subtype.ext (MulAut.inv_apply_self G (φ a) h.val)
    right_inv := fun h => Subtype.ext (MulAut.apply_inv_self G (φ a) h.val)
    map_mul' := fun x y => Subtype.ext (map_mul (φ a) x.val y.val)
  }
  map_one' := by
    apply MulEquiv.ext
    intro ⟨g, hg⟩
    apply Subtype.ext
    change (φ 1) g = g
    rw [φ.map_one]
    rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro ⟨g, hg⟩
    apply Subtype.ext
    change (φ (a * b)) g = (φ a) ((φ b) g)
    rw [φ.map_mul]
    rfl

/-- restrict の値域への射影: A-inv H に対し, `(IsAInvariant.restrict hH a) h` の underlying
要素は `(φ a) h.val`. -/
@[simp]
theorem IsAInvariant.restrict_apply_val {A : Type*} [Group A] {φ : A →* MulAut G}
    {H : Subgroup G} (hH : IsAInvariant φ H) (a : A) (h : ↥H) :
    ((hH.restrict a) h).val = (φ a) h.val := rfl

/-- A-不変 H の normalCore は A-不変. proof: `normalCore_eq_iInf_conjAct` で
`normalCore H = ⨅ g : ConjAct G, g • H`. (φ a) は inner action と可換でないが,
element-level の `b * x * b⁻¹ ∈ H` を通して直接示せる. -/
theorem IsAInvariant.normalCore {A : Type*} [Group A] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : IsAInvariant φ H) : IsAInvariant φ H.normalCore := fun a => by
  change H.normalCore.map (φ a).toMonoidHom = H.normalCore
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    -- hy : y ∈ normalCore H = {a : ∀ b, b * a * b⁻¹ ∈ H}
    change ∀ b, b * (φ a) y * b⁻¹ ∈ H
    intro b
    have hcyc : ((φ a)⁻¹ b) * y * ((φ a)⁻¹ b)⁻¹ ∈ H := hy ((φ a)⁻¹ b)
    have h_apply : (φ a) (((φ a)⁻¹ b) * y * ((φ a)⁻¹ b)⁻¹) ∈ H := hH.smul_mem a hcyc
    simp only [map_mul, MulAut.apply_inv_self, map_inv] at h_apply
    exact h_apply
  · intro hx
    -- hx : x ∈ normalCore H = {a : ∀ b, b * a * b⁻¹ ∈ H}
    refine ⟨(φ a)⁻¹ x, ?_, MulAut.apply_inv_self G (φ a) x⟩
    change ∀ b, b * ((φ a)⁻¹ x) * b⁻¹ ∈ H
    intro b
    have hcxc : ((φ a) b) * x * ((φ a) b)⁻¹ ∈ H := hx ((φ a) b)
    have h_apply : (φ a)⁻¹ (((φ a) b) * x * ((φ a) b)⁻¹) ∈ H := hH.inv_smul_mem a hcxc
    simp only [map_mul, map_inv,
      show ∀ y : G, ((φ a)⁻¹ : MulAut G) ((φ a) y) = y from
        fun y => MulAut.inv_apply_self G (φ a) y] at h_apply
    exact h_apply

/-- A-不変 H と K (`K ≤ G`) に対し, `K.subgroupOf H` は restricted action `hH.restrict`
下で A-不変. -/
theorem IsAInvariant.subgroupOf {A : Type*} [Group A] {φ : A →* MulAut G}
    {H K : Subgroup G} (hH : IsAInvariant φ H) (hK : IsAInvariant φ K) :
    IsAInvariant hH.restrict (K.subgroupOf H) := fun a => by
  ext ⟨g, hg⟩
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_subgroupOf]
  constructor
  · intro hmem
    -- hmem : ((hH.restrict a)⁻¹ • ⟨g, hg⟩).val ∈ K
    -- We have ((hH.restrict a)⁻¹ ⟨g, hg⟩).val = (φ a)⁻¹ g
    -- So (φ a)⁻¹ g ∈ K (via hmem). Apply (φ a) to get g ∈ K.
    change g ∈ K
    have h1 : ((hH.restrict a)⁻¹ • (⟨g, hg⟩ : ↥H)).val = (φ a)⁻¹ g := rfl
    have h2 : (φ a)⁻¹ g ∈ K := h1 ▸ hmem
    have : (φ a) ((φ a)⁻¹ g) ∈ K := hK.smul_mem a h2
    rwa [MulAut.apply_inv_self] at this
  · intro hg_K
    -- g ∈ K
    -- Want ((hH.restrict a)⁻¹ ⟨g, hg⟩).val ∈ K, i.e., (φ a)⁻¹ g ∈ K.
    change ((hH.restrict a)⁻¹ • (⟨g, hg⟩ : ↥H)).val ∈ K
    change (φ a)⁻¹ g ∈ K
    exact hK.inv_smul_mem a hg_K

/-- Lift a Hall subgroup found inside an invariant overgroup back to the ambient group. -/
theorem lift_hall_from_invariant_overgroup [Finite G] {A : Type*} [Group A]
    {φ : A →* MulAut G} {π : Set ℕ} {K H : Subgroup G}
    (hH_inv : IsAInvariant φ H)
    (hH_index : ∀ p ∈ H.index.primeFactors, p ∉ π)
    (hK_le_H : K ≤ H) {L : Subgroup H}
    (hL_hall : IsHallSubgroup π L)
    (hL_inv : IsAInvariant hH_inv.restrict L)
    (hK_sub_le_L : K.subgroupOf H ≤ L) :
    ∃ Lg : Subgroup G, IsHallSubgroup π Lg ∧ IsAInvariant φ Lg ∧ K ≤ Lg := by
  refine ⟨L.map H.subtype, hL_hall.map_subtype_of_index_no_pi hH_index, ?_, ?_⟩
  · rw [isAInvariant_iff_smul_mem]
    rintro a _ ⟨l, hl, rfl⟩
    exact ⟨(hH_inv.restrict a) l, hL_inv.smul_mem a hl,
      IsAInvariant.restrict_apply_val hH_inv a l⟩
  · intro k hk
    rw [Subgroup.mem_map]
    exact ⟨⟨k, hK_le_H hk⟩, hK_sub_le_L (by simpa [Subgroup.mem_subgroupOf] using hk), rfl⟩

/-- Assemble a proper invariant-overgroup induction step for invariant Hall overgroups. -/
theorem proper_overgroup_branch_frame [Finite G] {A : Type*} [Group A]
    {φ : A →* MulAut G} {π : Set ℕ} {K H : Subgroup G}
    (hH_inv : IsAInvariant φ H)
    (hH_index : ∀ p ∈ H.index.primeFactors, p ∉ π)
    (hK_pi : Subgroup.IsPiGroup π K)
    (hK_inv : IsAInvariant φ K)
    (hK_le_H : K ≤ H)
    (hIH_H : ∀ {Ksub : Subgroup H},
      Subgroup.IsPiGroup π Ksub →
        IsAInvariant hH_inv.restrict Ksub →
        ∃ L : Subgroup H, IsHallSubgroup π L ∧
          IsAInvariant hH_inv.restrict L ∧ Ksub ≤ L) :
    ∃ Lg : Subgroup G, IsHallSubgroup π Lg ∧ IsAInvariant φ Lg ∧ K ≤ Lg := by
  let Ksub : Subgroup H := K.subgroupOf H
  have hKsub_pi : Subgroup.IsPiGroup π Ksub :=
    Subgroup.IsPiGroup.subgroupOf hK_le_H hK_pi
  have hKsub_inv : IsAInvariant hH_inv.restrict Ksub :=
    hH_inv.subgroupOf hK_inv
  obtain ⟨L, hL_hall, hL_inv, hKsub_le_L⟩ := hIH_H hKsub_pi hKsub_inv
  exact lift_hall_from_invariant_overgroup hH_inv hH_index hK_le_H
    hL_hall hL_inv hKsub_le_L

/-- `fixedPointsOfMulAut φ` は (同じ) `φ` 作用下で A-不変 (定義より trivially). -/
theorem IsAInvariant.fixedPointsOfMulAut {A : Type*} [Group A] (φ : A →* MulAut G) :
    IsAInvariant φ (Subgroup.fixedPointsOfMulAut φ) := fun a => by
  change (Subgroup.fixedPointsOfMulAut φ).map (φ a).toMonoidHom = Subgroup.fixedPointsOfMulAut φ
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_fixedPointsOfMulAut]
  refine ⟨?_, fun hy => ⟨y, hy, hy a⟩⟩
  rintro ⟨x, hx, rfl⟩
  -- (MulEquiv.toMonoidHom (φ a)) x = (φ a) x; need to show ∀ b, (φ b) ((φ a) x) = (φ a) x
  change ∀ b, (φ b) ((φ a) x) = (φ a) x
  intro b
  rw [show (φ a) x = x from hx a]
  exact hx b

/-! **Isaacs Thm 3.23, 3.24 (Coprime action)** ⭐ **FT クリティカル**.
A coprime action ⇒ A-不変 Sylow 存在 (3.23a), 共役 (3.23b), Glauberman fixed point (3.24).

**Forward dep**: Ch.4 §4C-§4D (coprime action machinery) を要する. ~8-12 週の大規模.
所在: `OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean` (placeholder). -/

end -- 3E

section /- 3F: 巡回商 lift (pp. 105-112) -/

variable {G : Type*} [Group G]

/-! ### Isaacs §3F (Cyclic quotient lift)

3.35-3.36: `H ⊴ G` で `G/H` 巡回 (位数 n) のとき, `H ≤ K ≤ G` で `G = HK` かつ
`|K/H| = n` となる `K` が存在 (3.35 lift, 3.36 specialization).

FT 経路では優先度低 (Peterfalvi で散発使用).

**形式化状態**: stub. 全 lifted 結果は SemidirectProduct (mathlib) との接続で得られる
可能性が高い. -/

/-- **Isaacs Thm 3.35 (cyclic lift; generator)**: `H ⊴ G`, `G/H` cyclic ⇒ ある `g ∈ G` が
`G/H` の生成元の lift で, `⟨g⟩ ⊔ H = G`. (Thm 3.35 強版の uniqueness の前提.) -/
theorem cyclic_quotient_lift [Finite G] {H : Subgroup G} [H.Normal]
    (hCyclic : IsCyclic (G ⧸ H)) :
    ∃ g : G, Subgroup.zpowers g ⊔ H = ⊤ := by
  obtain ⟨gbar, hgbar⟩ := hCyclic.exists_generator
  -- gbar : G ⧸ H, hgbar : ∀ x, x ∈ Subgroup.zpowers gbar.
  -- Lift to g ∈ G.
  obtain ⟨g, hg_proj⟩ := QuotientGroup.mk_surjective gbar
  refine ⟨g, ?_⟩
  rw [eq_top_iff]
  intro x _
  -- ⟦x⟧ ∈ ⟨gbar⟩, so ⟦x⟧ = gbar^n for some n. So x = g^n · h for some h ∈ H.
  have hx : (x : G ⧸ H) ∈ Subgroup.zpowers gbar := hgbar _
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨n, hn⟩ := hx
  -- hn : gbar ^ n = (x : G ⧸ H). Substituting gbar = ⟦g⟧: ⟦g⟧^n = ⟦g^n⟧ = ⟦x⟧.
  have h_in_H : x * (g ^ n)⁻¹ ∈ H := by
    rw [← QuotientGroup.eq_one_iff]
    rw [← hg_proj] at hn
    -- hn : (↑g : G ⧸ H) ^ n = ↑x
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow, ← hn]
    group
  -- x = (x · (g^n)⁻¹) · g^n with first factor in H and second in ⟨g⟩.
  rw [show x = (x * (g ^ n)⁻¹) * g ^ n by group, sup_comm]
  exact Subgroup.mul_mem_sup h_in_H (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n)

/-- **Isaacs Thm 3.35 (uniqueness)** ⭐: `N ⊴ G` で `gN` が `G/N` の生成元のとき,
`G →* G₀` の準同型は `N` 上での値と `g ↦ g₀` から **一意に決定**.

Isaacs §3F の主結果 (extension uniqueness). 任意 `u ∈ G` は `u = (u·(g^i)⁻¹) · g^i` の
形に一意分解 (`u·(g^i)⁻¹ ∈ N`, `i` は `gN` の zpowers での representation).
両 θ, θ' が同じ extension を与えるなら値が一致.

**注**: existence (Thm 3.36 cyclic extension) は別途 (Sym(Ω) realization), Phase 4 予定. -/
theorem cyclic_quotient_extension_unique
    {G G₀ : Type*} [Group G] [Group G₀]
    {N : Subgroup G} [N.Normal]
    (g : G) (g₀ : G₀)
    (hg_gen : Subgroup.zpowers ((g : G ⧸ N)) = ⊤)
    {θ θ' : G →* G₀}
    (hθ_ext : ∀ x ∈ N, θ x = θ' x) (hθ_g : θ g = g₀) (hθ'_g : θ' g = g₀) :
    θ = θ' := by
  ext u
  -- ⟦u⟧ ∈ ⟨⟦g⟧⟩, so ⟦u⟧ = ⟦g⟧^i for some i ∈ ℤ.
  have hu_mem : (u : G ⧸ N) ∈ Subgroup.zpowers ((g : G ⧸ N)) := hg_gen ▸ Subgroup.mem_top _
  rw [Subgroup.mem_zpowers_iff] at hu_mem
  obtain ⟨i, hi⟩ := hu_mem
  -- hi : (↑g)^i = ↑u in G ⧸ N, i.e., x := u * (g^i)⁻¹ ∈ N.
  set x : G := u * (g^i)⁻¹ with hxdef
  have hx_mem : x ∈ N := by
    rw [hxdef, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_zpow, ← hi]
    group
  -- u = x * g^i.
  have hu_decomp : u = x * g^i := by rw [hxdef]; group
  rw [hu_decomp, map_mul θ, map_mul θ', map_zpow θ, map_zpow θ', hθ_g, hθ'_g, hθ_ext _ hx_mem]

/-! ### Isaacs Thm 3.36 (cyclic extension existence)

`N` 群, `m > 0`, `a ∈ N`, `σ ∈ Aut(N)` で `σ a = a` かつ `σ^m = MulAut.conj a` を満たすとき,
`N ⊴ G` で `G/N` cyclic of order `m`, generator `g` で `g^m = a` かつ `x^g = σ x`
となる群 `G` が存在.

構成: `preG := N ⋊_σ (Multiplicative ℤ)` を quotient by `K := ⟨(a⁻¹, m)⟩`.
`hσa, hσm` から `(a⁻¹, m)` が `preG` の中心元 ⇒ `K ⊴ preG`. 各性質は商計算. -/
/-- Twist hom: `Multiplicative ℤ →* MulAut N` sending `ofAdd k ↦ σ^k`. -/
private noncomputable def cyclicExtPhi {N : Type*} [Group N] (σ : MulAut N) :
    Multiplicative ℤ →* MulAut N :=
  zpowersHom (MulAut N) σ

@[simp] private lemma cyclicExtPhi_apply {N : Type*} [Group N] (σ : MulAut N)
    (k : Multiplicative ℤ) : cyclicExtPhi σ k = σ ^ k.toAdd := rfl

/-- The pre-quotient group `N ⋊_σ ℤ`. -/
private abbrev CyclicExtPreG (N : Type*) [Group N] (σ : MulAut N) : Type _ :=
  SemidirectProduct N (Multiplicative ℤ) (cyclicExtPhi σ)

/-- The "central" element `(a⁻¹, m)` in `preG`. -/
private noncomputable def cyclicExtK {N : Type*} [Group N]
    (m : ℕ) (a : N) (σ : MulAut N) : CyclicExtPreG N σ :=
  SemidirectProduct.inl a⁻¹ * SemidirectProduct.inr (Multiplicative.ofAdd (m : ℤ))

/-- Under `hσa` and `hσm`, the element `(a⁻¹, m)` is fixed by conjugation. -/
private lemma cyclicExtK_centralized {N : Type*} [Group N]
    (m : ℕ) (a : N) (σ : MulAut N)
    (hσa : σ a = a) (hσm : σ ^ m = MulAut.conj a) :
    ∀ y : CyclicExtPreG N σ, y * cyclicExtK m a σ * y⁻¹ = cyclicExtK m a σ := by
  intro y
  -- σ^k fixes a (and a⁻¹) for any k : ℤ (since σ ∈ stabilizer a).
  have hσka : ∀ k : ℤ, (σ ^ k) a = a := fun k =>
    (Subgroup.zpow_mem (MulAction.stabilizer (MulAut N) a)
      (MulAction.mem_stabilizer_iff.mpr hσa) k : _)
  have hσka_inv : ∀ k : ℤ, (σ ^ k) a⁻¹ = a⁻¹ := fun k => by rw [map_inv, hσka k]
  -- σ^m sends x to a * x * a⁻¹ (from hσm).
  have hσm_apply : ∀ x : N, ((σ ^ m : MulAut N)) x = a * x * a⁻¹ := fun x => by
    rw [hσm]; rfl
  -- (cyclicExtK).left = a⁻¹, .right = ofAdd m.
  have h_K_left : (cyclicExtK m a σ).left = a⁻¹ := by
    change (SemidirectProduct.inl a⁻¹ * SemidirectProduct.inr _).left = _
    simp [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
          SemidirectProduct.left_inr]
  have h_K_right : (cyclicExtK m a σ).right = Multiplicative.ofAdd (m : ℤ) := by
    change (SemidirectProduct.inl a⁻¹ * SemidirectProduct.inr _).right = _
    simp [SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.right_inr]
  ext
  · -- Left component.
    change ((y * cyclicExtK m a σ) * y⁻¹).left = (cyclicExtK m a σ).left
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
               SemidirectProduct.inv_left,
               h_K_left, h_K_right, cyclicExtPhi_apply]
    -- Goal (approx): y.left * (σ^l.toAdd) a⁻¹ * (σ^(l.toAdd+m)) ((σ^(-l.toAdd)) y.left⁻¹) = a⁻¹.
    rw [hσka_inv]
    -- Compose σ chain.
    have hcompose : (σ ^ ((y.right * Multiplicative.ofAdd (m : ℤ)).toAdd))
        ((σ ^ ((y.right⁻¹ : Multiplicative ℤ).toAdd)) y.left⁻¹) =
          ((σ : MulAut N) ^ m) y.left⁻¹ := by
      change (σ ^ ((y.right.toAdd + (m : ℤ)) : ℤ))
            ((σ ^ ((-y.right.toAdd) : ℤ)) y.left⁻¹) = _
      rw [← MulAut.mul_apply, ← zpow_add,
          show (y.right.toAdd + (m : ℤ)) + (-y.right.toAdd) = (m : ℤ) by ring,
          zpow_natCast]
    rw [hcompose, hσm_apply]
    group
  · -- Right component (Multiplicative ℤ abelian).
    change ((y * cyclicExtK m a σ) * y⁻¹).right = (cyclicExtK m a σ).right
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right]
    rw [mul_comm y.right _, mul_assoc, mul_inv_cancel, mul_one]

/-- The kernel subgroup `K = ⟨(a⁻¹, m)⟩`. -/
private noncomputable abbrev cyclicExtKSubgroup {N : Type*} [Group N]
    (m : ℕ) (a : N) (σ : MulAut N) : Subgroup (CyclicExtPreG N σ) :=
  Subgroup.zpowers (cyclicExtK m a σ)

private lemma cyclicExtKSubgroup_normal {N : Type*} [Group N]
    (m : ℕ) (a : N) (σ : MulAut N)
    (hσa : σ a = a) (hσm : σ ^ m = MulAut.conj a) :
    (cyclicExtKSubgroup m a σ).Normal := by
  refine ⟨fun n hn y => ?_⟩
  rw [Subgroup.mem_zpowers_iff] at hn
  obtain ⟨j, hj⟩ := hn
  refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
  rw [← hj]
  have h_conj_zpow : y * (cyclicExtK m a σ)^j * y⁻¹ = (y * cyclicExtK m a σ * y⁻¹)^j := by
    have h : (MulAut.conj y) ((cyclicExtK m a σ)^j) = ((MulAut.conj y) (cyclicExtK m a σ))^j :=
      map_zpow (MulAut.conj y) _ _
    simpa only [MulAut.conj_apply] using h
  rw [h_conj_zpow, cyclicExtK_centralized m a σ hσa hσm]

/-- **Isaacs Thm 3.36 (cyclic extension existence)** ⭐:
given `N`, `m > 0`, `a ∈ N`, `σ ∈ Aut(N)` with `σ a = a` and `σ^m = MulAut.conj a`,
there exists a group `G` with `N ⊴ G` (via iso `ι`), `G/N` cyclic of order `m` generator `g`,
`g^m = ι a` and `g · ι x · g⁻¹ = ι (σ x)`.

Construction: `G := (N ⋊_σ ℤ) / ⟨(a⁻¹, m)⟩`. The element `(a⁻¹, m)` is central (proven in
`cyclicExtK_centralized` using `σ a = a` and `σ^m = MulAut.conj a`), so its zpowers form
a normal subgroup. Quotienting gives `G` with the desired cyclic-extension structure. -/
theorem cyclic_extension_exists.{u} {N : Type u} [Group N] {m : ℕ} (_hm : 0 < m)
    (a : N) (σ : MulAut N) (hσa : σ a = a) (hσm : σ ^ m = MulAut.conj a) :
    ∃ (G : Type u) (_ : Group G) (N₀ : Subgroup G) (_ : N₀.Normal)
      (ι : N ≃* ↥N₀) (g : G),
      Subgroup.zpowers ((g : G ⧸ N₀)) = ⊤ ∧
      g ^ m = (ι a : G) ∧
      ∀ x : N, g * (ι x : G) * g⁻¹ = (ι (σ x) : G) := by
  haveI hK_norm : (cyclicExtKSubgroup m a σ).Normal :=
    cyclicExtKSubgroup_normal m a σ hσa hσm
  -- G := preG ⧸ K with the natural Group instance.
  let G := CyclicExtPreG N σ ⧸ cyclicExtKSubgroup m a σ
  -- inl_to_G : N →* G via inl then quotient.
  let inl_to_G : N →* G :=
    (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)).comp SemidirectProduct.inl
  -- inl_to_G is injective: ker = inl⁻¹(K) = ⊥.
  have h_inj : Function.Injective inl_to_G := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h_in_K : (SemidirectProduct.inl x : CyclicExtPreG N σ) ∈ cyclicExtKSubgroup m a σ := by
      have heq : inl_to_G x = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
          (SemidirectProduct.inl x) := rfl
      rw [heq] at hx
      exact (QuotientGroup.eq_one_iff _).mp hx
    rw [Subgroup.mem_zpowers_iff] at h_in_K
    obtain ⟨j, hj⟩ := h_in_K
    have h_K_right : (cyclicExtK m a σ).right = Multiplicative.ofAdd (m : ℤ) := by
      change (SemidirectProduct.inl a⁻¹ * SemidirectProduct.inr _).right = _
      simp
    have h_jm_eq_zero : (j • (m : ℤ)) = 0 := by
      have h_right_of_inl : (SemidirectProduct.inl x : CyclicExtPreG N σ).right = 1 :=
        SemidirectProduct.right_inl x
      have h_zpow_right : ((cyclicExtK m a σ) ^ j : CyclicExtPreG N σ).right =
          (Multiplicative.ofAdd (m : ℤ)) ^ j := by
        have hmap : SemidirectProduct.rightHom ((cyclicExtK m a σ) ^ j) =
            SemidirectProduct.rightHom (cyclicExtK m a σ) ^ j := map_zpow _ _ _
        change SemidirectProduct.rightHom ((cyclicExtK m a σ) ^ j) = _
        rw [hmap]; congr 1
      have h_one : ((cyclicExtK m a σ) ^ j : CyclicExtPreG N σ).right = 1 := by
        rw [hj]; exact h_right_of_inl
      rw [h_zpow_right] at h_one
      rw [← ofAdd_zsmul, ofAdd_eq_one] at h_one
      exact h_one
    have hj_zero : j = 0 := by
      rw [smul_eq_mul] at h_jm_eq_zero
      rcases mul_eq_zero.mp h_jm_eq_zero with h | h
      · exact h
      · exfalso
        have hm_pos : (m : ℤ) > 0 := Int.natCast_pos.mpr _hm
        exact (ne_of_gt hm_pos) h
    subst hj_zero
    rw [zpow_zero] at hj
    have h_inl_one : (SemidirectProduct.inl x : CyclicExtPreG N σ) = 1 := hj.symm
    have : SemidirectProduct.inl x = (SemidirectProduct.inl (1 : N) : CyclicExtPreG N σ) := by
      rw [(SemidirectProduct.inl : N →* CyclicExtPreG N σ).map_one]; exact h_inl_one
    exact SemidirectProduct.inl_injective this
  -- N₀ := range of inl_to_G.
  let N₀ : Subgroup G := inl_to_G.range
  haveI hN₀_norm : N₀.Normal := by
    have h_range_eq : (inl_to_G.range : Subgroup G) =
        (SemidirectProduct.inl : N →* CyclicExtPreG N σ).range.map
          (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)) :=
      MonoidHom.range_comp _ _
    change N₀.Normal
    rw [show N₀ = inl_to_G.range from rfl, h_range_eq]
    have h_inl_range_normal :
        (SemidirectProduct.inl : N →* CyclicExtPreG N σ).range.Normal := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      exact (SemidirectProduct.rightHom : CyclicExtPreG N σ →* Multiplicative ℤ).normal_ker
    exact h_inl_range_normal.map _ (QuotientGroup.mk'_surjective _)
  -- ι := N ≃* N₀.
  let ι : N ≃* ↥N₀ := MonoidHom.ofInjective h_inj
  -- g := ⟦inr (ofAdd 1)⟧.
  let g : G := QuotientGroup.mk' _ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)))
  refine ⟨G, inferInstance, N₀, hN₀_norm, ι, g, ?_, ?_, ?_⟩
  · -- zpowers ⟦g⟧ = ⊤ in G/N₀: every G/N₀ element lifts to preG, decompose y = inl·inr;
    -- inl part vanishes in G/N₀, inr part is ⟦g⟧^(y.right.toAdd).
    rw [Subgroup.eq_top_iff']
    intro z
    obtain ⟨zG, rfl⟩ : ∃ zG : G, QuotientGroup.mk' N₀ zG = z :=
      QuotientGroup.mk'_surjective _ z
    obtain ⟨y, rfl⟩ : ∃ y : CyclicExtPreG N σ,
        QuotientGroup.mk' (cyclicExtKSubgroup m a σ) y = zG :=
      QuotientGroup.mk'_surjective _ zG
    rw [show y = SemidirectProduct.inl y.left * SemidirectProduct.inr y.right from
      (SemidirectProduct.inl_left_mul_inr_right y).symm,
      map_mul (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)),
      map_mul (QuotientGroup.mk' N₀)]
    have h_in_N₀ : (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
        (SemidirectProduct.inl y.left)) ∈ N₀ := ⟨y.left, rfl⟩
    have h_first_one : (QuotientGroup.mk' N₀ : G →* G ⧸ N₀)
        ((QuotientGroup.mk' (cyclicExtKSubgroup m a σ)) (SemidirectProduct.inl y.left)) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact h_in_N₀
    rw [h_first_one, one_mul]
    have h_right_eq : y.right = (Multiplicative.ofAdd (1 : ℤ)) ^ y.right.toAdd := by
      conv_lhs => rw [← ofAdd_toAdd y.right]
      rw [← ofAdd_zsmul]; congr 1; simp
    rw [h_right_eq, map_zpow (SemidirectProduct.inr : Multiplicative ℤ →* CyclicExtPreG N σ),
      map_zpow (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)),
      map_zpow (QuotientGroup.mk' N₀)]
    exact Subgroup.zpow_mem_zpowers _ _
  · -- g^m = ι a.
    -- g^m = mk' K (inr (ofAdd m)). (ι a : G) = mk' K (inl a).
    -- (inr (ofAdd m))⁻¹ * inl a = (a, ofAdd(-m)) = cExt⁻¹ ∈ K (using σ^k a = a ∀ k).
    have h_iota_a : (ι a : G) = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
        (SemidirectProduct.inl a) := rfl
    rw [h_iota_a]
    have h_g_pow : (g ^ m : G) = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
        (SemidirectProduct.inr (Multiplicative.ofAdd (m : ℤ))) := by
      change (QuotientGroup.mk' _ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)))) ^ m = _
      rw [← map_pow]; congr 1
      rw [← map_pow]; congr 1
      rw [← ofAdd_nsmul]; congr 1; simp
    rw [h_g_pow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hσa_zpow : ∀ k : ℤ, (σ ^ k) a = a := fun k =>
      Subgroup.zpow_mem (MulAction.stabilizer (MulAut N) a)
        (MulAction.mem_stabilizer_iff.mpr hσa) k
    have h_eq_inv : (SemidirectProduct.inr (Multiplicative.ofAdd (m : ℤ))
        : CyclicExtPreG N σ)⁻¹ * SemidirectProduct.inl a = (cyclicExtK m a σ)⁻¹ := by
      apply SemidirectProduct.ext
      · change ((SemidirectProduct.inr (Multiplicative.ofAdd (m : ℤ)))⁻¹ *
            SemidirectProduct.inl a : CyclicExtPreG N σ).left = (cyclicExtK m a σ)⁻¹.left
        unfold cyclicExtK
        simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left,
          SemidirectProduct.inv_right, cyclicExtPhi_apply]
      · change ((SemidirectProduct.inr (Multiplicative.ofAdd (m : ℤ)))⁻¹ *
            SemidirectProduct.inl a : CyclicExtPreG N σ).right = (cyclicExtK m a σ)⁻¹.right
        unfold cyclicExtK
        simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
          SemidirectProduct.right_inl, SemidirectProduct.right_inr, one_mul, mul_one]
    rw [h_eq_inv]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  · -- Conjugation: g · ι x · g⁻¹ = ι (σ x) via SemidirectProduct.inl_aut.
    intro x
    have h_iota_x : (ι x : G) = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
        (SemidirectProduct.inl x) := rfl
    have h_iota_σx : (ι (σ x) : G) = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
        (SemidirectProduct.inl (σ x)) := rfl
    rw [h_iota_x, h_iota_σx]
    change (QuotientGroup.mk' _ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)))) *
        (QuotientGroup.mk' _ (SemidirectProduct.inl x)) *
        (QuotientGroup.mk' _ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))))⁻¹ =
      QuotientGroup.mk' _ (SemidirectProduct.inl (σ x))
    rw [← map_inv (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)),
        ← map_mul (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)),
        ← map_mul (QuotientGroup.mk' (cyclicExtKSubgroup m a σ))]
    congr 1
    -- Goal: inr (ofAdd 1) * inl x * (inr (ofAdd 1))⁻¹ = inl (σ x)
    have h_phi : (cyclicExtPhi σ) (Multiplicative.ofAdd (1 : ℤ)) = σ := by
      change σ ^ (Multiplicative.ofAdd (1 : ℤ)).toAdd = σ
      exact zpow_one σ
    have h_inl_aut : (SemidirectProduct.inl ((cyclicExtPhi σ) (Multiplicative.ofAdd (1 : ℤ)) x)
        : CyclicExtPreG N σ) =
        SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)) * SemidirectProduct.inl x *
          SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))⁻¹ :=
      SemidirectProduct.inl_aut (φ := cyclicExtPhi σ) (Multiplicative.ofAdd (1 : ℤ)) x
    rw [h_phi] at h_inl_aut
    rw [← (SemidirectProduct.inr : Multiplicative ℤ →* CyclicExtPreG N σ).map_inv] at *
    exact h_inl_aut.symm

end -- 3F

end OddOrder.Isaacs.Ch03
