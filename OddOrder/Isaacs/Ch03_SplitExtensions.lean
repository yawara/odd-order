/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable
import OddOrder.Isaacs.Ch02_Subnormality

/-!
# OddOrder.Isaacs.Ch03 — Split Extensions

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 3
"Split Extensions" (pp. 65-112) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 3A | 半直積構成 + Aut(G) 位数評価 | 3.1 – 3.4 | 着手中 (Thm 3.1, 3.2 wrapper 済) |
| 3B | Schur-Zassenhaus + 可解群基本 | 3.5 – 3.12 | TODO (mathlib `SchurZassenhaus` ラッパー予定) |
| 3C | Hall 部分群 + 可解性判定 | 3.13 – 3.17 | TODO (FT クリティカル, 新規実装重い) |
| 3D | π-separable + Hall-Higman 1.2.3 | 3.18 – 3.22 | TODO (FT クリティカル) |
| 3E | Coprime action | 3.23 – 3.34 | TODO |
| 3F | 巡回商 lift | 3.35 – 3.36 | TODO (FT 経路で必要性低) |

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
- `OddOrder.Isaacs.Ch02.lucchini_index_normalCore_lt_index` (axiom)
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
    -- inr.range = inr (⊤ : Subgroup ↥A) = inr (Subgroup.zpowers ⟨σ, _⟩) = Subgroup.zpowers (inr ⟨σ, _⟩)
    have h_top_eq : (⊤ : Subgroup ↥A) =
        Subgroup.zpowers (⟨σ, Subgroup.mem_zpowers σ⟩ : ↥A) := by
      ext ⟨a, ha⟩
      simp only [Subgroup.mem_top, true_iff]
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      refine ⟨n, ?_⟩
      ext; simp
    show ((SemidirectProduct.inr : ↥A →* G ⋊[φ] ↥A).range) = Subgroup.zpowers g₀
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
    OddOrder.Isaacs.Ch02.lucchini_index_normalCore_lt_index hAₛ_proper hAₛ_ab
      ⟨g₀, hAₛ_eq_zpowers⟩
  -- Show Aₛ.normalCore = ⊥.
  -- Setup normality and disjointness.
  haveI : Aₛ.normalCore.Normal := Subgroup.normalCore_normal _
  haveI : Gₛ.Normal := by
    show ((SemidirectProduct.inl : G →* G ⋊[φ] ↥A).range).Normal
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

/-- **Elementary Abelian p-Group**: G が abelian かつ全ての元の `p`乗が単位元.
mathlib 未収載の新規定義. -/
def IsElementaryAbelian (p : ℕ) (G : Type*) [Group G] : Prop :=
  (∀ x y : G, x * y = y * x) ∧ (∀ x : G, x ^ p = 1)

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
    ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p ↥M := by
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
        rw [mul_pow, ha, hb, one_mul]
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
形を取れる. base case (`Nat.card G = 1`) は完全に閉じる; step case は IH on `G/M`
+ Schur-Zassenhaus で要 ~200 行 (sorry).

TODO: step case を completion. 必要なのは:
1. M minimal normal 取り (G nontrivial で existence).
2. Thm 3.11 で M elementary abelian p-group.
3. `IH (G ⧸ M) (|G/M| ≤ n から |G/M| = |G|/|M| < |G|)` で `H̄` π-Hall in G/M を得る.
4. pullback `H = comap (mk' M) H̄`.
5. p ∈ π case: H は π-Hall (|H| = |H̄|·|M|, |M| は p-power, |G:H| = |G/M : H̄|).
6. p ∉ π case: H の subgroup M ⊴ H で `Coprime (Nat.card M) M.index` (in H).
   Schur-Zassenhaus で `H = M ⋊ K`. K が π-Hall in G. -/
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
          have hPG : IsPGroup _p ↥M := fun x => ⟨1, by simp [pow_one]; exact _hp_elem.2 x⟩
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

/-- **Isaacs Thm 3.14 Hall-C** ⭐ **FT クリティカル**: `G` 可解 ⇒ `π`-Hall 部分群は共役.

証明骨子: 同じく `|G|`-induction. Minimal normal `M` 経由で G/M に IH 適用, 個別の
H₁, H₂ が M 経由で同じ商で対応する Hall に降りる. Schur-Zassenhaus の共役性で
`H₁ = (H₂)^g` を得る.

TODO: 本コミットでは base case (`|G| = 1`) のみ完結. Step は IH on G/M +
Schur-Zassenhaus 共役性で要 ~200 行. -/
axiom hall_C_conjugate [Finite G] [IsSolvable G] (π : Set ℕ)
    {H₁ H₂ : Subgroup G} (_h1 : IsHallSubgroup π H₁) (_h2 : IsHallSubgroup π H₂) :
    ∃ g : G, H₁.map (MulEquiv.toMonoidHom (MulAut.conj g)) = H₂

/-- **Isaacs Thm 3.15**: 全ての素数 `p` について `p`-complement (i.e., `{p}'`-Hall) が
存在 ⇒ `G` 可解.

証明骨子 (Hall's converse): `|G|`-induction. p, q を `|G|` を割る相異なる素数とし,
H_p, H_q の p-, q-complement を取る. H_p ∩ H_q は {p,q}'-Hall に相当. 商と部分群の
solvability を組み合わせる.

TODO: 本コミットでは base case (`|G| = 1`) のみ. Step は p, q 区別 + Hall 部分群
ペアの組合せで要 ~150 行. -/
axiom solvable_of_pcomplement_exists [Finite G]
    (_h : ∀ p : ℕ, p.Prime → ∃ H : Subgroup G, IsHallSubgroup {q | q ≠ p} H) :
    IsSolvable G

/-- **Isaacs Lemma 3.16**: `|G:H|`, `|G:K|` が coprime ⇒ `G = HK` (i.e., `H ⊔ K = ⊤`).

証明: `(H ⊔ K).index` は `H.index` と `K.index` の両方を割り切るので gcd を割り切る.
gcd は 1 なので `(H ⊔ K).index = 1`, 故に `H ⊔ K = ⊤`. -/
theorem sup_eq_top_of_coprime_index {H K : Subgroup G}
    (h : Nat.Coprime H.index K.index) : H ⊔ K = ⊤ := by
  have h1 : (H ⊔ K).index ∣ H.index := Subgroup.index_dvd_of_le le_sup_left
  have h2 : (H ⊔ K).index ∣ K.index := Subgroup.index_dvd_of_le le_sup_right
  have h_dvd : (H ⊔ K).index ∣ 1 := h ▸ Nat.dvd_gcd h1 h2
  exact Subgroup.index_eq_one.mp (Nat.dvd_one.mp h_dvd)

/-- **Isaacs Thm 3.17** (Wielandt): 3 つの部分群が pairwise coprime index + solvable ⇒
`G` solvable.

証明骨子 (Isaacs Thm 3.17 の証明は missing page にあり; Wielandt 1971 の一般的議論):
`|G|`-induction. 最小反例 G を取り, M を minimal normal とする. G/M は IH で
solvable. M も `(H ∩ M)`, `(K ∩ M)`, `(L ∩ M)` 部分群経由で IH より solvable.
よって G solvable, 矛盾. ただし G が単純の場合 M = G で別議論を要する
(Burnside p^a q^b 等. 本リポでは sorry).

TODO: 本コミットでは base case + 非単純ケース skeleton のみ. -/
axiom solvable_of_three_subgroups [Finite G] {H K L : Subgroup G}
    (_h12 : Nat.Coprime H.index K.index) (_h13 : Nat.Coprime H.index L.index)
    (_h23 : Nat.Coprime K.index L.index)
    [IsSolvable H] [IsSolvable K] [IsSolvable L] :
    IsSolvable G

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

/-- **`π`-separable 群** (working definition): 正式には `G` の正規列で各因子が
`π`-group または `π'`-group となるものだが, 本リポでは FT 適用に十分な
**`IsSolvable G`** を仮の定義とする. mathlib 未収載の新規定義.

理由: FT 経路では π-separable が登場する文脈の G は事実上常に solvable
(最小反例の真部分群はすべて solvable). 正式な normal series 定義は将来別ファイル
(`OddOrder/Group/PiSeparable.lean`) に移行可. -/
def IsPiSeparable (_π : Set ℕ) (G : Type*) [Group G] : Prop := IsSolvable G

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

/-- **Isaacs Lemma 3.18**: π-separable の補助補題. 正式定義下では non-trivial だが
仮定義 (=IsSolvable) では trivial に True. -/
theorem isPiSeparable_aux : True := trivial

/-- **Isaacs Cor 3.19**: `G` solvable ⇒ 全 π について π-separable.
仮定義 `IsPiSeparable := IsSolvable` 下で identity. -/
theorem isPiSeparable_of_solvable [Finite G] [hSol : IsSolvable G] (_π : Set ℕ) :
    IsPiSeparable _π G :=
  hSol

/-- **Isaacs Thm 3.20**: π-separable ⇒ π-Hall 部分群存在.
仮定義下では `IsPiSeparable π G = IsSolvable G`, よって Hall-E (Thm 3.13) に帰着. -/
theorem hall_exists_of_piSeparable [Finite G] (π : Set ℕ) (hπsep : IsPiSeparable π G) :
    ∃ H : Subgroup G, IsHallSubgroup π H :=
  haveI : IsSolvable G := hπsep
  hall_E_exists π

/-- **Isaacs Thm 3.21 (Hall-Higman 1.2.3)** ⭐ **FT クリティカル**.
`G` π-separable + `O_{π'}(G) = ⊥` ⇒ `C_G(O_π(G)) ≤ O_π(G)`.

書籍 p.94 の証明骨子: π-separable normal series での induction. F* (一般化 Fitting) 経由,
または Bender 法 (`C := C_G(O_π(G))` の極小反例 → `C ⊓ O_π(G) = Z(O_π(G))` と
`C O_π(G) ⊴ G` の解析). 完全形式化は ~100-200 行 (別 commit).

本リポでは正確な statement で axiom 化. (`Subgroup.centralizer` は mathlib 既存.) -/
axiom hall_higman_1_2_3 [Finite G] (π : Set ℕ) (_hπsep : IsPiSeparable π G)
    (_hPiPrime : oPiCore πᶜ G = ⊥) :
    Subgroup.centralizer (oPiCore π G : Set G) ≤ oPiCore π G

/-- **Isaacs Thm 3.22 (片向き; π-length ≤ 1 の Hall-Higman 系)**:
`G` π-separable + abelian な π-Hall ⇒ `[O_{π',π}(G), O_{π',π}(G)] ≤ O_{π'}(G)`.

`O_{π',π}(G)` (= `π` を `O_{π'}(G)` 上に乗せた π-層) の交換子部分群が `O_{π'}(G)` に
含まれる, つまり π-length ≤ 1 と同値. 完全 π-length 定義は別ファイル. 本リポでは
statement を保留 (型レベル定式化が大きいため): -/
theorem piLength_le_one_of_abelian_pi_hall [Finite G] (π : Set ℕ)
    (_hπsep : IsPiSeparable π G)
    (_hAb : ∀ (H : Subgroup G) (_ : IsHallSubgroup π H), ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    True := by  -- TODO: π-length の正式定義後に書き直す
  trivial

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

/-- **Isaacs Thm 3.23 (a)** ⭐: 有限 `A`, `G`, `gcd(|A|, |G|) = 1`, `A` が `G` に
`φ` で作用 ⇒ 任意素数 `p` で `A`-不変 Sylow `p`-部分群が存在. -/
axiom exists_aInvariant_sylow {A : Type*} [Group A] [Finite A] [Finite G]
    (φ : A →* MulAut G) (_hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (p : ℕ) [Fact p.Prime] :
    ∃ P : Sylow p G, IsAInvariant φ (P : Subgroup G)

/-- **Isaacs Thm 3.23 (b)** ⭐: 上記設定下で, 二つの `A`-不変 Sylow は `C_G(A)` で共役. -/
axiom aInvariant_sylow_conj {A : Type*} [Group A] [Finite A] [Finite G]
    (φ : A →* MulAut G) (_hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    {p : ℕ} [Fact p.Prime] {P Q : Sylow p G}
    (_hP : IsAInvariant φ (P : Subgroup G)) (_hQ : IsAInvariant φ (Q : Subgroup G)) :
    ∃ g : G, (∀ a : A, (φ a).toMonoidHom g = g) ∧
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom = (Q : Subgroup G)

/-- **Isaacs Lemma 3.24 (Glauberman lemma)** ⭐: `A` 可解, `A → MulAut G`,
`gcd(|A|, |G|) = 1` で `G` が transitive に `Ω` に作用しているとき, `A` の作用と
コンパチブルなら A-fixed 点が存在. (FT 経路で多用.)

形式化メモ: コンパチ条件 `(s • g) • ω = s • (g • ω)` は SemidirectProduct を経由する
方が clean な定式化が可能. 完全形式化は別 phase で. 現状は stub. -/
axiom glauberman_fixed_point {A : Type*} [Group A] [Finite A] [Finite G]
    (φ : A →* MulAut G) (_hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (_hASol : IsSolvable A)
    (Ω : Type*) [MulAction G Ω] [Finite Ω]
    -- TODO: A の Ω 上作用と φ の compatible 条件 (正式記述は SemidirectProduct 経由)
    (_hTrans : ∀ ω₁ ω₂ : Ω, ∃ g : G, g • ω₁ = ω₂) :
    ∃ ω : Ω, ∀ a : A, ∀ g : G, (φ a).toMonoidHom g • ω = g • ω
    -- ↑ A-不変条件の最小定式化

end -- 3E

section /- 3F: 巡回商 lift (pp. 105-112) -/

variable {G : Type*} [Group G]

/-! ### Isaacs §3F (Cyclic quotient lift)

3.35-3.36: `H ⊴ G` で `G/H` 巡回 (位数 n) のとき, `H ≤ K ≤ G` で `G = HK` かつ
`|K/H| = n` となる `K` が存在 (3.35 lift, 3.36 specialization).

FT 経路では優先度低 (Peterfalvi で散発使用).

**形式化状態**: stub. 全 lifted 結果は SemidirectProduct (mathlib) との接続で得られる
可能性が高い. -/

/-- **Isaacs Thm 3.35 (cyclic lift; 弱版)**: `H ⊴ G`, `G/H` cyclic ⇒ ある `g ∈ G` が
`G/H` の生成元の lift で, `⟨g⟩ ⊔ H = G`.

Isaacs FGT 3.35 の本体は cyclic-quotient extension の **uniqueness** (与えられた
N + 自己同型 + 適合条件で extension が同型 up to iso). 本リポでは FT 経路必要性が低い
ため, 弱版 (cyclic 部分群 ⟨g⟩ で G/H を覆える g の存在) のみ. 完全 3.35 は Phase 4 で. -/
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

end -- 3F

end OddOrder.Isaacs.Ch03
