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
import OddOrder.Isaacs.Ch03_SplitExtensions.SplitExtensionUniqueness
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh02


/-!
# Isaacs §3A — Semidirect products and automorphism bounds

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 3, §3A (pp. 65-74):
the semidirect-product construction (Thm 3.1/3.2 as mathlib re-statements) and the
automorphism-order bounds Thm 3.3 (Horosevskii, via Ch.2 Thm 2.20 Lucchini) and Thm 3.4
(via Ch.1 Thm 1.37 Brodkey).

Split from `OddOrder.Isaacs.Ch03_SplitExtensions.Basic` (issue 0149, the longFile-1500
campaign); `Basic` imports this leaf, so downstream imports are unchanged.
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

/-! **Isaacs Lemma 3.1** (split extension の同型を除く一意性) は上流 leaf
[`SplitExtensionUniqueness`](SplitExtensionUniqueness.lean) の
`existsUnique_mulEquiv_of_isComplement'` (書籍 p.70 の two-abstract-groups 形).
`G₀` を `N ⋊ K` に固定した特殊形は mathlib `SemidirectProduct.mulEquivSubgroup`
そのものなので, ラッパー方針によりここでは再述しない. -/

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

end OddOrder.Isaacs.Ch03
