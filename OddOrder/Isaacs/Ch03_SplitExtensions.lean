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
import OddOrder.GroupTheory.ElementaryAbelian
import OddOrder.Isaacs.Ch02_Subnormality
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh02

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
    OddOrder.Isaacs.Ch04.lucchini_index_normalCore_lt_index hAₛ_proper hAₛ_ab
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

/-! **Isaacs Thm 3.14 Hall-C**: `G` 可解 ⇒ `π`-Hall 部分群は共役.

**Forward dep**: mathlib への Schur-Zassenhaus 共役性追加が前提.
詳細は [Ch03_SplitExtensions に直接書く理由]:
- mathlib への汎用補題なので owner chapter 不在.
- 将来 SZ 共役性を `OddOrder/Mathlib/SchurZassenhausConj.lean` に実装した時点で
  本箇所で theorem 化.
- それまでは **leaf axiom 削除** (使用箇所 0 件).
- 詳細は [`notes/isaacs/ch03_split.md`](../../notes/isaacs/ch03_split.md). -/

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
  simp [Subgroup.card_bot] at hp

/-- **IsPiGroup は subgroup inclusion で保持**: 有限 G で `H ≤ K` and `K` is π-group
⇒ `H` is π-group. `Nat.card ↥H ∣ Nat.card ↥K` で primeFactors 包含. -/
theorem Subgroup.IsPiGroup.le {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {H K : Subgroup G} (hHK : H ≤ K) (hK : Subgroup.IsPiGroup π K) :
    Subgroup.IsPiGroup π H := by
  intro p hp
  have hdvd : Nat.card ↥H ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hHK
  exact hK p (Nat.primeFactors_mono hdvd Nat.card_pos.ne' hp)

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

/-- **`oPiCore.isPiGroup`** ⭐ (Hall-Higman 3.21 critical bottleneck):
有限 `G` で `oPiCore π G` は π-group.

**証明** (~30 LOC): `Finset.sup_induction` を predicate `H ↦ H.Normal ∧ IsPiGroup π H`
で適用.
- iSup = Finset.sup over finite indexing (`Subgroup G` is Fintype for finite G).
- bot: trivially normal + π-group (primeFactors 1 = ∅).
- closure: `H₁, H₂ ⊴ G + π-group ⇒ H₁ ⊔ H₂ ⊴ G + π-group` (mathlib + `IsPiGroup.sup_of_normal`).
- generators: each subtype element has the predicate by construction. -/
instance oPiCore.isPiGroup [Finite G] (π : Set ℕ) :
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
      simp [Subgroup.card_bot] at hq
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

/-- **`C/B` nontrivial when `B < C`**: `B < C` strict + `B ⊴ G` ⇒ `C.map (QuotientGroup.mk' B) ≠ ⊥`. -/
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

/-- **Hall-Higman 3.21 setup**: `¬ centralizer(O) ≤ O ⇒ B := centralizer(O) ⊓ O < centralizer(O)`. -/
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
    {G : Type*} [Group G] [Finite G] [IsSolvable G] (π : Set ℕ)
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
    {G : Type*} [Group G] [Finite G] [IsSolvable G] (π : Set ℕ)
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
      show Nat.card (↥K ⧸ (B.subgroupOf K)) = _
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
    show n.val * h.val = h.val * n.val
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
      show (B.subgroupOf K).index * Nat.card ↥(B.subgroupOf K) =
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

**実装状態** ⭐ sorry-free. case π body + case π' body を `exists_oPiCore_ne_bot_or_oPi'Core_ne_bot`
(↥CB に対して) で場合分けして組み立て.
-/
theorem hall_higman_1_2_3 [Finite G] (π : Set ℕ)
    (hπsep : IsPiSeparable π G)
    (hπ' : oPiCore {p | p ∉ π} G = ⊥) :
    Subgroup.centralizer (oPiCore π G : Set G) ≤ oPiCore π G := by
  haveI : IsSolvable G := hπsep
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
  haveI hCB_solvable : IsSolvable ↥CB := inferInstance
  rcases exists_oPiCore_ne_bot_or_oPi'Core_ne_bot (G := ↥CB) π with hπCase | hπ'Case
  · exact hall_higman_case_pi_body π h_not_le hπCase
  · exact hall_higman_case_pi'_body π hπ' h_not_le hπ'Case

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

/-- **Characteristic 部分群は常に A-不変**: H.Characteristic ⇒ IsAInvariant φ H for any φ.
mathlib `characteristic_iff_map_eq` 経由. -/
theorem IsAInvariant.of_characteristic {A : Type*} [Group A] (φ : A →* MulAut G)
    {H : Subgroup G} [hH : H.Characteristic] : IsAInvariant φ H := fun a => by
  show H.map (φ a).toMonoidHom = H
  exact (Subgroup.characteristic_iff_map_eq.mp hH) (φ a)

/-- `derivedSeries G n` は A-不変 (characteristic instance 経由). -/
theorem IsAInvariant.derivedSeries {A : Type*} [Group A] (φ : A →* MulAut G) (n : ℕ) :
    IsAInvariant φ (derivedSeries G n) :=
  IsAInvariant.of_characteristic φ

/-- `lowerCentralSeries G n` は A-不変 (characteristic instance 経由). -/
theorem IsAInvariant.lowerCentralSeries {A : Type*} [Group A] (φ : A →* MulAut G) (n : ℕ) :
    IsAInvariant φ (lowerCentralSeries G n) :=
  IsAInvariant.of_characteristic φ

/-- `Subgroup.center G` は A-不変 (characteristic instance 経由). -/
theorem IsAInvariant.center {A : Type*} [Group A] (φ : A →* MulAut G) :
    IsAInvariant φ (Subgroup.center G) :=
  IsAInvariant.of_characteristic φ

/-- A-不変 + A-不変 の commutator は A-不変 (`Subgroup.map_commutator`). -/
theorem IsAInvariant.commutator {A : Type*} [Group A] {φ : A →* MulAut G} {H K : Subgroup G}
    (hH : IsAInvariant φ H) (hK : IsAInvariant φ K) :
    IsAInvariant φ ⁅H, K⁆ := fun a => by
  show ⁅H, K⁆.map (φ a).toMonoidHom = ⁅H, K⁆
  rw [Subgroup.map_commutator]
  show ⁅H.map (φ a).toMonoidHom, K.map (φ a).toMonoidHom⁆ = ⁅H, K⁆
  rw [show H.map (φ a).toMonoidHom = H from hH a,
      show K.map (φ a).toMonoidHom = K from hK a]

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
