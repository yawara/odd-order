/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch02_Subnormality.Basic
import OddOrder.Isaacs.Ch09_MoreSubnormality.ThompsonWielandt
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Isaacs §9C の演習 (書籍 pp. 288-289)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 9C
(Thompson–Wielandt 周辺)。statement はページ画像
`references/isaacs/pages/isaacs-p288-301.png` / `isaacs-p289-302.png` で確定。

* **9C.1** `relCore_thompsonWielandtCore_eq_bot_or_of_isSubnormal` — Thm 9.24 の設定で
  `H`, `K` がともに `G` で **subnormal** なら `U = 1` または `V = 1`。
* **9C.2** `pResidualOf_top_eq_sup_of_isSubnormal` — `G = AB` で `A, B ⊲⊲ G` なら
  `O^p(G) = O^p(A) O^p(B)`。9B.5 (`G^∞ = A^∞B^∞`) と同型の帰納法。
  ⚠ 仮説は join でなく**積** `(A : Set G) * B = Set.univ`。書籍の結論は**集合の積**なので
  join 形に加えて積形 `pResidualOf_top_eq_mul_of_isSubnormal` も証明する
  (吸収 `O^p(X ⊓ Y) ≤ O^p(X)` で middle 項が消える 2 段の帰納法)。
* **9C.3** `mul_eq_univ_of_isSubnormal_of_coprime_abelianization` — `G = ⟨A, B⟩`,
  `A, B ⊲⊲ G`, `|A:A'|` と `|B:B'|` が互いに素なら `G = AB`。鍵は Thm 2.6 (Wielandt,
  極小正規は subnormal を正規化) と積形 9C.2 + Lemma 9.26。

⚠ `pdftotext` は上付きを落とすので 9C.2 は一見 `O_p` に見えるが、ページ画像で
**`O^p` (p-residual)** であることを確認済 ([[pdftotext-drops-superscripts]])。

## 9C.1 の証明 (書籍 hint に沿う)

`U ≠ 1` かつ `V ≠ 1` と仮定する。Thm 9.24 (`thompsonWielandt`) からある素数 `p` で
`U` または `V` が `p`-群。`U ◁ H ◁◁ G` なので `U ◁◁ G`、同様に `V ◁◁ G`。
非自明な subnormal `p`-部分群は `O_p(G)` に入る (`le_oPiCore_of_isSubnormal`, issue 9216)
ので **`O_p(G) > 1`**。

`Z := Z(O_p(G))` (ambient で `centerPCore p G`) は `O_p(G)` に characteristic ゆえ `G` に
normal で、非自明 (非自明な `p`-群の中心)。書籍 hint の核心は **`Z ≤ H`**:

* `U` が `p`-群のとき: `U ≤ O_p(G)` なので `Z` は `U` を中心化する。よって
  `Z ≤ C_G(U) ≤ N_G(U) = H`。
* `U` が `p`-群でないとき: `X := O^p(U) ≠ 1` で `X ≤ U ≤ D`, `N_G(U) ≤ N_G(X)` ゆえ
  `N_G(X) = H`。Corollary 9.27 (`le_normalizer_pResidualOf_of_isSubnormal`) が
  `O_p(G) ≤ N_G(O^p(U)) = H` を与えるので `Z ≤ O_p(G) ≤ H`。

`V` について同じ議論で `Z ≤ K`、すなわち `1 ≠ Z ≤ D` が `G` に normal。`H ≠ K` なので
`H` か `K` の一方は `⊤` より真に小さく、`NoNormalInSupergroup` に矛盾する。
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

section /- 9C.1: H, K がともに subnormal なら U = 1 または V = 1 (p. 288) -/

/-- **`Z(O_p(G))`** を ambient 群 `G` の部分群として実現したもの。 -/
def centerPCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  (Subgroup.center ↥(Ch03.oPiCore ({p} : Set ℕ) G)).map
    (Ch03.oPiCore ({p} : Set ℕ) G).subtype

theorem centerPCore_le {p : ℕ} : centerPCore p G ≤ Ch03.oPiCore ({p} : Set ℕ) G :=
  Subgroup.map_subtype_le _

/-- `O_p(G)` は `p`-群 (`oPiCore` が `π`-群であることの singleton 版)。 -/
theorem isPGroup_oPiCore [Finite G] {p : ℕ} [Fact p.Prime] :
    IsPGroup p ↥(Ch03.oPiCore ({p} : Set ℕ) G) :=
  isPGroup_of_isPiSubgroup_singleton (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))

/-- `Z(O_p(G))` は `G` に normal (`O_p(G) ◁ G` の characteristic 部分群)。 -/
instance centerPCore_normal {p : ℕ} : (centerPCore p G).Normal :=
  map_subtype_normal_of_characteristic _

/-- `Z(O_p(G))` の元は `O_p(G)` の元と可換。 -/
theorem centerPCore_commute {p : ℕ} {z u : G} (hz : z ∈ centerPCore p G)
    (hu : u ∈ Ch03.oPiCore ({p} : Set ℕ) G) : u * z = z * u := by
  obtain ⟨x, hx, rfl⟩ := hz
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨u, hu⟩)

/-- `O_p(G) ≠ 1` なら `Z(O_p(G)) ≠ 1` (非自明な `p`-群の中心は非自明)。 -/
theorem centerPCore_ne_bot [Finite G] {p : ℕ} [Fact p.Prime]
    (hP : Ch03.oPiCore ({p} : Set ℕ) G ≠ ⊥) : centerPCore p G ≠ ⊥ := by
  haveI : Nontrivial ↥(Ch03.oPiCore ({p} : Set ℕ) G) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hP
  have hcenter : Subgroup.center ↥(Ch03.oPiCore ({p} : Set ℕ) G) ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp isPGroup_oPiCore.center_nontrivial
  intro hbot
  exact hcenter ((Subgroup.map_eq_bot_iff_of_injective _
    (Subgroup.subtype_injective _)).mp hbot)

/-- **9C.1 の核** ⭐: `D` に含まれ `H` に normal な非自明部分群 `U` があり `H ◁◁ G` なら
`Z(O_p(G)) ≤ H`。

書籍 hint の「`U` が `p`-群であるかどうかで場合分け」がここ。`hnorm` は
`NoNormalInSupergroup` から取れる形 (`normalizer_eq_left_of_noNormal` /
`normalizer_eq_right_of_noNormal`) で渡す。 -/
theorem centerPCore_le_of_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {H U D : Subgroup G}
    (hUbot : U ≠ ⊥) (hUH : U ≤ H) (hUD : U ≤ D)
    (hUn : H ≤ Subgroup.normalizer (U : Set G)) (hHsn : H.IsSubnormal)
    (hnorm : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ D →
      H ≤ Subgroup.normalizer (W : Set G) → Subgroup.normalizer (W : Set G) = H) :
    centerPCore p G ≤ H := by
  have hUsn : U.IsSubnormal :=
    Subgroup.IsSubnormal.step U H hUH hHsn
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mpr hUn)
  by_cases hUp : IsPGroup p ↥U
  · -- `U ≤ O_p(G)`; `Z(O_p(G))` は `U` を中心化するので `N_G(U) = H` に入る
    have hUP : U ≤ Ch03.oPiCore ({p} : Set ℕ) G :=
      le_oPiCore_of_isSubnormal hUsn (Subgroup.isPiSubgroup_of_isPGroup_of_mem hUp rfl)
    rw [← hnorm U hUbot hUD hUn]
    refine le_trans (fun z hz => ?_) (Subgroup.centralizer_le_normalizer (U : Set G))
    exact Subgroup.mem_centralizer_iff.mpr fun u hu => centerPCore_commute hz (hUP hu)
  · -- `X = O^p(U) ≠ 1`; Corollary 9.27 で `O_p(G) ≤ N_G(X) = H`
    have hX : pResidualOf p U ≠ ⊥ := fun h => hUp ((pResidualOf_eq_bot_iff_isPGroup U).mp h)
    have hXn : H ≤ Subgroup.normalizer (pResidualOf p U : Set G) :=
      hUn.trans (normalizer_le_normalizer_pResidualOf p U)
    have hNX := hnorm _ hX ((pResidualOf_le p U).trans hUD) hXn
    have hPX := le_normalizer_pResidualOf_of_isSubnormal (p := p)
      (P := Ch03.oPiCore ({p} : Set ℕ) G) hUsn isPGroup_oPiCore
    rw [hNX] at hPX
    exact centerPCore_le.trans hPX

/-- **Isaacs Problem 9C.1** (書籍 p. 288) ⭐: Theorem 9.24 の設定に加えて `H`, `K` が
ともに `G` で **subnormal** なら, `U = 1` または `V = 1`
(`U = core_H(E)`, `V = core_K(E)`, `E = thompsonWielandtCore H K`)。

すなわち Thm 9.24 の結論「`U` か `V` が `p`-群」は subnormal な場合には
「`U` か `V` が自明」まで強まる。 -/
theorem relCore_thompsonWielandtCore_eq_bot_or_of_isSubnormal [Finite G] {H K : Subgroup G}
    (hHK : H ≠ K) (hyp : NoNormalInSupergroup H K (H ⊓ K))
    (hHsn : H.IsSubnormal) (hKsn : K.IsSubnormal) :
    relCore H (thompsonWielandtCore H K) = ⊥ ∨ relCore K (thompsonWielandtCore H K) = ⊥ := by
  by_contra hcon
  obtain ⟨hU, hV⟩ := not_or.mp hcon
  set E := thompsonWielandtCore H K with hE
  -- `U`, `V` の基本性質
  have hUH : relCore H E ≤ H := relCore_le_left H E
  have hKV : relCore K E ≤ K := relCore_le_left K E
  have hUD : relCore H E ≤ H ⊓ K := (relCore_le H E).trans (thompsonWielandtCore_le H K)
  have hVD : relCore K E ≤ H ⊓ K := (relCore_le K E).trans (thompsonWielandtCore_le H K)
  have hUn : H ≤ Subgroup.normalizer (relCore H E : Set G) := le_normalizer_relCore H E
  have hVn : K ≤ Subgroup.normalizer (relCore K E : Set G) := le_normalizer_relCore K E
  have hUsn : (relCore H E).IsSubnormal :=
    Subgroup.IsSubnormal.step _ H hUH hHsn
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mpr hUn)
  have hVsn : (relCore K E).IsSubnormal :=
    Subgroup.IsSubnormal.step _ K hKV hKsn
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKV).mpr hVn)
  -- Thm 9.24: ある `p` で `U` か `V` が `p`-群 ⟹ `O_p(G) > 1`
  obtain ⟨p, hp, hpg⟩ := thompsonWielandt H K hHK hyp
  haveI : Fact p.Prime := ⟨hp⟩
  have hPbot : Ch03.oPiCore ({p} : Set ℕ) G ≠ ⊥ := by
    rcases hpg with hg | hg
    · exact fun h => hU (le_bot_iff.mp (h ▸ le_oPiCore_of_isSubnormal hUsn
        (Subgroup.isPiSubgroup_of_isPGroup_of_mem hg rfl)))
    · exact fun h => hV (le_bot_iff.mp (h ▸ le_oPiCore_of_isSubnormal hVsn
        (Subgroup.isPiSubgroup_of_isPGroup_of_mem hg rfl)))
  -- `Z = Z(O_p(G))` は非自明・`G`-normal で `H` にも `K` にも入る
  have hZH : centerPCore p G ≤ H :=
    centerPCore_le_of_ne_bot hU hUH hUD hUn hHsn
      fun W hW hWD hWn => normalizer_eq_left_of_noNormal hyp hW hWD hWn
  have hZK : centerPCore p G ≤ K :=
    centerPCore_le_of_ne_bot hV hKV hVD hVn hKsn
      fun W hW hWD hWn => normalizer_eq_right_of_noNormal hyp hW hWD hWn
  -- `H ≠ K` なので一方は `⊤` より真に小さい: `NoNormalInSupergroup` に矛盾
  have hlt : H < ⊤ ∨ K < ⊤ := by
    rcases eq_or_ne H ⊤ with rfl | h
    · exact Or.inr (lt_top_iff_ne_top.mpr fun hKtop => hHK hKtop.symm)
    · exact Or.inl (lt_top_iff_ne_top.mpr h)
  refine hyp ⊤ hlt (centerPCore p G) (centerPCore_ne_bot hPbot) (le_inf hZH hZK) ?_
  rw [Subgroup.normalizer_eq_top]

end -- 9C.1

section /- 9C.2: G = AB (A, B subnormal) なら O^p(G) = O^p(A) O^p(B) (p. 288) -/

open scoped Pointwise

/-- `O^p(G) ≤ N ◁ G` なら `G/N` は `p`-群 (`G/O^p(G)` の商だから)。

`pResidual_le_of_isPGroup_quotient` の逆向き (`O^p` の普遍性の非自明な側)。 -/
theorem isPGroup_quotient_of_pResidual_le [Finite G] {p : ℕ} [Fact p.Prime] {N : Subgroup G}
    [N.Normal] (h : pResidual p G ≤ N) : IsPGroup p (G ⧸ N) := by
  refine (isPGroup_quotient_pResidual (p := p) (G := G)).of_surjective
    (QuotientGroup.map _ _ (MonoidHom.id G) h) fun x => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨QuotientGroup.mk g, rfl⟩

/-- `O^p(A) ≤ N ◁ G` なら `A` の `G/N` での像は `p`-群。

`A.map (mk' N) ≅ ↥A / N.subgroupOf A` で, 後者は `↥A / O^p(↥A)` の商。 -/
theorem isPGroup_map_of_pResidualOf_le [Finite G] {p : ℕ} [Fact p.Prime] {A N : Subgroup G}
    [N.Normal] (h : pResidualOf p A ≤ N) : IsPGroup p ↥(A.map (QuotientGroup.mk' N)) := by
  have hker : ((QuotientGroup.mk' N).comp A.subtype).ker = N.subgroupOf A := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hrange : ((QuotientGroup.mk' N).comp A.subtype).range = A.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hle : pResidual p ↥A ≤ N.subgroupOf A :=
    Subgroup.map_le_iff_le_comap.mp h
  have hq : IsPGroup p (↥A ⧸ N.subgroupOf A) := isPGroup_quotient_of_pResidual_le hle
  refine hq.of_equiv ?_
  exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange _)).trans (MulEquiv.subgroupCongr hrange)

/-- **9C.2 の base case** (書籍 hint の第 1 段): `A, B ⊴ G` で `G = AB` なら
`O^p(G) = O^p(A) O^p(B)`。

`N := O^p(A) ⊔ O^p(B)` は正規で, `G/N` は正規 `p`-部分群 2 つ (`A`, `B` の像) の積なので
どちらも `O_p(G/N)` に入り `O_p(G/N) = ⊤`, すなわち `G/N` は `p`-群。ゆえに `O^p(G) ≤ N`。
逆の包含は `pResidualOf_mono`。9B.5 の base case (`F(G/N) = ⊤` 論法) の `O_p` 版。 -/
theorem pResidualOf_top_eq_sup_of_normal [Finite G] {p : ℕ} [Fact p.Prime] {A B : Subgroup G}
    [A.Normal] [B.Normal] (hAB : A ⊔ B = ⊤) :
    pResidualOf p (⊤ : Subgroup G) = pResidualOf p A ⊔ pResidualOf p B := by
  refine le_antisymm ?_ (sup_le (pResidualOf_mono le_top) (pResidualOf_mono le_top))
  set N := pResidualOf p A ⊔ pResidualOf p B with hNdef
  haveI : N.Normal := Subgroup.sup_normal _ _
  rw [pResidualOf_top]
  refine pResidual_le_of_isPGroup_quotient ?_
  -- `A`, `B` の像は正規 `p`-群
  have hA : IsPGroup p ↥(A.map (QuotientGroup.mk' N)) :=
    isPGroup_map_of_pResidualOf_le le_sup_left
  have hB : IsPGroup p ↥(B.map (QuotientGroup.mk' N)) :=
    isPGroup_map_of_pResidualOf_le le_sup_right
  haveI : (A.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  haveI : (B.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  -- 両方 `O_p(G/N)` に入り, 生成するので `O_p(G/N) = ⊤`
  have htop : (⊤ : Subgroup (G ⧸ N)) ≤ Ch03.oPiCore ({p} : Set ℕ) (G ⧸ N) := by
    rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N), ← hAB, Subgroup.map_sup]
    exact sup_le
      (Ch03.Subgroup.IsPiGroup.le_oPiCore (Subgroup.isPiSubgroup_of_isPGroup_of_mem hA rfl))
      (Ch03.Subgroup.IsPiGroup.le_oPiCore (Subgroup.isPiSubgroup_of_isPGroup_of_mem hB rfl))
  exact (isPGroup_oPiCore (p := p) (G := G ⧸ N)).of_equiv
    ((MulEquiv.subgroupCongr (top_le_iff.mp htop)).trans Subgroup.topEquiv)

/-- 9C.2 の帰納核: `Nat.card G ≤ n` の有限群で `A, B ◁◁ G`, `G = AB` ⟹
`O^p(G) ≤ O^p(A) ⊔ O^p(B)`。`∀ G` を内側に量化して `n` で帰納 (9B.5 の核と同型)。 -/
private theorem pResidualOf_sup_aux.{u} (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G ≤ n →
      ∀ {A B : Subgroup G}, A.IsSubnormal → B.IsSubnormal →
        (A : Set G) * (B : Set G) = Set.univ →
        pResidualOf p (⊤ : Subgroup G) ≤ pResidualOf p A ⊔ pResidualOf p B := by
  induction n with
  | zero =>
    intro G _ _ hcard
    exact absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ n IH =>
    intro G _ _ hcard A B hA hB hprod
    have hjoin : A ⊔ B = ⊤ := GroupTheory.sup_eq_top_of_mul_eq_univ hprod
    rcases hA.lt_normal with rfl | ⟨A₁, hA₁norm, hAA₁, hA₁lt⟩
    · exact le_sup_of_le_left (pResidualOf_mono le_top)
    rcases hB.lt_normal with rfl | ⟨B₁, hB₁norm, hBB₁, hB₁lt⟩
    · exact le_sup_of_le_right (pResidualOf_mono le_top)
    haveI := hA₁norm
    haveI := hB₁norm
    have hA₁B₁ : A₁ ⊔ B₁ = ⊤ := by
      refine top_le_iff.mp ?_
      rw [← hjoin]
      exact sup_le_sup hAA₁ hBB₁
    rw [pResidualOf_top_eq_sup_of_normal hA₁B₁]
    refine sup_le ?_ ?_
    · -- `O^p(A₁) ≤ O^p(A) ⊔ O^p(B ⊓ A₁) ≤ O^p(A) ⊔ O^p(B)`
      have hIHA := IH ↥A₁ (GroupTheory.card_le_of_lt_top hcard hA₁lt) hA.subgroupOf
        (hB.inf hA₁norm.isSubnormal).subgroupOf
        (GroupTheory.subgroupOf_mul_inf_subgroupOf_eq_univ hAA₁ hprod)
      have hm := Subgroup.map_mono (f := A₁.subtype) hIHA
      rw [map_subtype_pResidualOf_top, Subgroup.map_sup,
        map_subtype_pResidualOf_subgroupOf hAA₁,
        map_subtype_pResidualOf_subgroupOf (inf_le_right : B ⊓ A₁ ≤ A₁)] at hm
      exact hm.trans (sup_le le_sup_left ((pResidualOf_mono inf_le_left).trans le_sup_right))
    · -- 対称
      have hIHB := IH ↥B₁ (GroupTheory.card_le_of_lt_top hcard hB₁lt) hB.subgroupOf
        (hA.inf hB₁norm.isSubnormal).subgroupOf
        (GroupTheory.subgroupOf_mul_inf_subgroupOf_eq_univ hBB₁
          (GroupTheory.mul_eq_univ_comm hprod))
      have hm := Subgroup.map_mono (f := B₁.subtype) hIHB
      rw [map_subtype_pResidualOf_top, Subgroup.map_sup,
        map_subtype_pResidualOf_subgroupOf hBB₁,
        map_subtype_pResidualOf_subgroupOf (inf_le_right : A ⊓ B₁ ≤ B₁)] at hm
      exact hm.trans (sup_le le_sup_right ((pResidualOf_mono inf_le_left).trans le_sup_left))

/-- **Isaacs Problem 9C.2** (書籍 p. 288) ⭐: `G = AB` で `A, B ⊲⊲ G` (**subnormal**)
なら `O^p(G) = O^p(A) O^p(B)`。

書籍 hint どおり「9B.5 と同様に、まず両方 normal の場合
(`pResidualOf_top_eq_sup_of_normal`)、次に `|G|` の帰納法」。帰納段は
`A ≤ A₁ ◁ G`, `A₁ < ⊤` を取って base case で `O^p(G) = O^p(A₁) ⊔ O^p(B₁)` とし、
Dedekind (`A₁ = A (B ⊓ A₁)`) で `↥A₁` に帰納法を当てる。⚠ 仮説は join でなく**積**
`(A : Set G) * B = Set.univ` (9B.5 と同じ理由 — 部分群束は modular でない)。 -/
theorem pResidualOf_top_eq_sup_of_isSubnormal [Finite G] {p : ℕ} [Fact p.Prime]
    {A B : Subgroup G} (hA : A.IsSubnormal) (hB : B.IsSubnormal)
    (hprod : (A : Set G) * (B : Set G) = Set.univ) :
    pResidualOf p (⊤ : Subgroup G) = pResidualOf p A ⊔ pResidualOf p B :=
  le_antisymm (pResidualOf_sup_aux p (Nat.card G) G le_rfl hA hB hprod)
    (sup_le (pResidualOf_mono le_top) (pResidualOf_mono le_top))

/-- 9C.2 **積形**の第 1 段 (`A ⊴ G` の場合) の帰納核: `A ⊴ G`, `B ◁◁ G`, `G = AB` なら
`O^p(G) = O^p(A)·O^p(B)` (**集合の積**)。

`B ◁ G` なら両者の `O^p` がともに正規なので join = 積 (`Subgroup.mul_normal`)。さもなくば
`B ≤ B₁ ◁ G`, `B₁ < ⊤` を取り、pair `(A, B₁)` (両方正規) で `O^p(G) = O^p(A)·O^p(B₁)`、
`↥B₁` 内の pair `(A ⊓ B₁, B)` に帰納法で `O^p(B₁) = O^p(A ⊓ B₁)·O^p(B)`。middle 項は
`O^p(A ⊓ B₁) ≤ O^p(A)` の左吸収 (`coe_mul_coe_eq_left`) で消える。 -/
private theorem pResidualOf_top_eq_mul_normal_aux.{u} (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G ≤ n →
      ∀ {A B : Subgroup G}, A.Normal → B.IsSubnormal →
        (A : Set G) * (B : Set G) = Set.univ →
        (pResidualOf p (⊤ : Subgroup G) : Set G) =
          (pResidualOf p A : Set G) * (pResidualOf p B : Set G) := by
  induction n with
  | zero =>
    intro G _ _ hcard
    exact absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ n IH =>
    intro G _ _ hcard A B hAnorm hB hprod
    haveI := hAnorm
    rcases hB.lt_normal with rfl | ⟨B₁, hB₁norm, hBB₁, hB₁lt⟩
    · -- `B = ⊤`: 右吸収
      exact (GroupTheory.coe_mul_coe_eq_right (pResidualOf_mono le_top)).symm
    haveI := hB₁norm
    -- pair `(A, B₁)` は両方正規: join = 積
    have hAB₁ : A ⊔ B₁ = ⊤ := by
      rw [eq_top_iff, ← GroupTheory.sup_eq_top_of_mul_eq_univ hprod]
      exact sup_le_sup_left hBB₁ A
    have hbase : (pResidualOf p (⊤ : Subgroup G) : Set G) =
        (pResidualOf p A : Set G) * (pResidualOf p B₁ : Set G) := by
      rw [pResidualOf_top_eq_sup_of_normal hAB₁]
      exact Subgroup.mul_normal _ _
    -- `↥B₁` 内の pair `(A ⊓ B₁, B)` に帰納法
    have hprod' : (((A ⊓ B₁).subgroupOf B₁ : Subgroup ↥B₁) : Set ↥B₁) *
        ((B.subgroupOf B₁ : Subgroup ↥B₁) : Set ↥B₁) = Set.univ :=
      GroupTheory.mul_eq_univ_comm
        (GroupTheory.subgroupOf_mul_inf_subgroupOf_eq_univ hBB₁
          (GroupTheory.mul_eq_univ_comm hprod))
    have hnorm' : ((A ⊓ B₁).subgroupOf B₁).Normal := by
      rw [Subgroup.inf_subgroupOf_right]
      exact hAnorm.subgroupOf B₁
    have hIH := IH ↥B₁ (GroupTheory.card_le_of_lt_top hcard hB₁lt) hnorm'
      hB.subgroupOf hprod'
    have hpush := congrArg (Set.image B₁.subtype) hIH
    rw [Set.image_mul, ← Subgroup.coe_map, ← Subgroup.coe_map, ← Subgroup.coe_map,
      map_subtype_pResidualOf_top,
      map_subtype_pResidualOf_subgroupOf (inf_le_right : A ⊓ B₁ ≤ B₁),
      map_subtype_pResidualOf_subgroupOf hBB₁] at hpush
    rw [hbase, hpush, ← mul_assoc,
      GroupTheory.coe_mul_coe_eq_left (pResidualOf_mono inf_le_left)]

/-- **9C.2 の積形 (normal × subnormal)**: `A ⊴ G`, `B ◁◁ G`, `G = AB` なら
`O^p(G) = O^p(A) O^p(B)` (集合の積)。 -/
theorem pResidualOf_top_eq_mul_of_normal_of_isSubnormal [Finite G] {p : ℕ} [Fact p.Prime]
    {A B : Subgroup G} [A.Normal] (hB : B.IsSubnormal)
    (hprod : (A : Set G) * (B : Set G) = Set.univ) :
    (pResidualOf p (⊤ : Subgroup G) : Set G) =
      (pResidualOf p A : Set G) * (pResidualOf p B : Set G) :=
  pResidualOf_top_eq_mul_normal_aux p (Nat.card G) G le_rfl inferInstance hB hprod

/-- 9C.2 積形の第 2 段の帰納核: `A, B ◁◁ G`, `G = AB` の一般形。`A ≤ A₁ ◁ G` を取り
第 1 段の pair `(A₁, B)` で `O^p(G) = O^p(A₁)·O^p(B)`、`↥A₁` 内の pair `(A, B ⊓ A₁)` に
帰納法で `O^p(A₁) = O^p(A)·O^p(B ⊓ A₁)`。middle 項は `O^p(B ⊓ A₁) ≤ O^p(B)` の
右吸収で消える。 -/
private theorem pResidualOf_top_eq_mul_aux.{u} (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G ≤ n →
      ∀ {A B : Subgroup G}, A.IsSubnormal → B.IsSubnormal →
        (A : Set G) * (B : Set G) = Set.univ →
        (pResidualOf p (⊤ : Subgroup G) : Set G) =
          (pResidualOf p A : Set G) * (pResidualOf p B : Set G) := by
  induction n with
  | zero =>
    intro G _ _ hcard
    exact absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ n IH =>
    intro G _ _ hcard A B hA hB hprod
    rcases hA.lt_normal with rfl | ⟨A₁, hA₁norm, hAA₁, hA₁lt⟩
    · -- `A = ⊤`: 左吸収
      exact (GroupTheory.coe_mul_coe_eq_left (pResidualOf_mono le_top)).symm
    haveI := hA₁norm
    -- 第 1 段を pair `(A₁, B)` に適用
    have hprodA₁ : (A₁ : Set G) * (B : Set G) = Set.univ := by
      refine Set.eq_univ_of_forall fun g => ?_
      have hg : g ∈ (A : Set G) * (B : Set G) := by rw [hprod]; trivial
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      exact ⟨a, hAA₁ ha, b, hb, rfl⟩
    have hstep1 := pResidualOf_top_eq_mul_of_normal_of_isSubnormal (p := p) hB hprodA₁
    -- `↥A₁` 内の pair `(A, B ⊓ A₁)` に帰納法
    have hIH := IH ↥A₁ (GroupTheory.card_le_of_lt_top hcard hA₁lt) hA.subgroupOf
      (hB.inf hA₁norm.isSubnormal).subgroupOf
      (GroupTheory.subgroupOf_mul_inf_subgroupOf_eq_univ hAA₁ hprod)
    have hpush := congrArg (Set.image A₁.subtype) hIH
    rw [Set.image_mul, ← Subgroup.coe_map, ← Subgroup.coe_map, ← Subgroup.coe_map,
      map_subtype_pResidualOf_top, map_subtype_pResidualOf_subgroupOf hAA₁,
      map_subtype_pResidualOf_subgroupOf (inf_le_right : B ⊓ A₁ ≤ A₁)] at hpush
    rw [hstep1, hpush, mul_assoc,
      GroupTheory.coe_mul_coe_eq_right (pResidualOf_mono inf_le_left)]

/-- **Isaacs Problem 9C.2 (積形, 書籍どおり)** ⭐: `G = AB` で `A, B ⊲⊲ G` なら
`O^p(G) = O^p(A) O^p(B)` — join 形 (`pResidualOf_top_eq_sup_of_isSubnormal`) だけでなく
**集合の積**として成り立つ (書籍の記法 `O^p(A)O^p(B)` は集合の積)。

証明は 2 段の `|G|` 帰納: (i) `A ⊴ G` の場合を先に確立 (`B ≤ B₁ ◁ G` に降りると middle 項
`O^p(A ⊓ B₁) ≤ O^p(A)` が吸収で消える)、(ii) 一般は `A ≤ A₁ ◁ G` を取り (i) の
pair `(A₁, B)` と `↥A₁` 内の帰納で middle 項 `O^p(B ⊓ A₁) ≤ O^p(B)` を吸収。
9C.3 の step (d) はこの積形を使う。 -/
theorem pResidualOf_top_eq_mul_of_isSubnormal [Finite G] {p : ℕ} [Fact p.Prime]
    {A B : Subgroup G} (hA : A.IsSubnormal) (hB : B.IsSubnormal)
    (hprod : (A : Set G) * (B : Set G) = Set.univ) :
    (pResidualOf p (⊤ : Subgroup G) : Set G) =
      (pResidualOf p A : Set G) * (pResidualOf p B : Set G) :=
  pResidualOf_top_eq_mul_aux p (Nat.card G) G le_rfl hA hB hprod

end -- 9C.2

section /- 9C.3: G = ⟨A,B⟩, A,B ⊲⊲, |A:A'| ⊥ |B:B'| なら G = AB (p. 289) -/

open scoped Pointwise

/-- **非自明冪零群の交換子部分群は真**: `[Q,Q] ≠ Q`。`[Q,Q] = Q` だと降中心列が `⊤` で
止まり `⊥` に到達できない。(9C.3 では `p`-群の場合に使う。) -/
theorem commutator_ne_top_of_isNilpotent (Q : Type*) [Group Q] [Nontrivial Q]
    [Group.IsNilpotent Q] : commutator Q ≠ ⊤ := by
  intro htop
  have hall : ∀ n : ℕ, (⊤ : Subgroup Q).lowerCentralSeries n = ⊤ := by
    intro n
    induction n with
    | zero => exact Subgroup.lowerCentralSeries_zero ⊤
    | succ m ihm =>
      rw [Subgroup.lowerCentralSeries_succ, ihm]
      exact htop
  obtain ⟨k, hk⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp ‹Group.IsNilpotent Q›
  rw [hall k] at hk
  obtain ⟨x, hx⟩ := exists_ne (1 : Q)
  exact hx (Subgroup.mem_bot.mp (by rw [← hk]; exact Subgroup.mem_top x))

/-- **`p ∤ |Q : Q'|` なら `O^p(Q) = Q`** (type-level): `O^p(Q) < Q` だと非自明な `p`-群
`R := Q/O^p(Q)` が現れ、その (非自明な) abelianization が `p ∣ |Q^{ab}|` を強制する。 -/
theorem pResidual_eq_top_of_not_dvd_card_abelianization {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime] (h : ¬ p ∣ Nat.card (Abelianization Q)) :
    pResidual p Q = ⊤ := by
  by_contra hne
  have hRp : IsPGroup p (Q ⧸ pResidual p Q) := isPGroup_quotient_pResidual
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : Q, q₀ ∉ pResidual p Q := by
    by_contra hall
    push Not at hall
    exact hne ((Subgroup.eq_top_iff' _).mpr hall)
  haveI hRnt : Nontrivial (Q ⧸ pResidual p Q) :=
    ⟨⟨QuotientGroup.mk q₀, 1, fun heq => hq₀ ((QuotientGroup.eq_one_iff q₀).mp heq)⟩⟩
  haveI : Group.IsNilpotent (Q ⧸ pResidual p Q) := IsPGroup.isNilpotent hRp
  have hcomm_ne : commutator (Q ⧸ pResidual p Q) ≠ ⊤ :=
    commutator_ne_top_of_isNilpotent _
  -- `R` の abelianization は非自明な `p`-群なので位数は `p` で割れる
  have hAbR_p : IsPGroup p (Abelianization (Q ⧸ pResidual p Q)) :=
    hRp.to_quotient (commutator (Q ⧸ pResidual p Q))
  have hpAbR : p ∣ Nat.card (Abelianization (Q ⧸ pResidual p Q)) := by
    obtain ⟨r, hr⟩ : ∃ r, r ∉ commutator (Q ⧸ pResidual p Q) := by
      by_contra hall
      push Not at hall
      exact hcomm_ne ((Subgroup.eq_top_iff' _).mpr hall)
    have hone : Abelianization.of r ≠ 1 :=
      fun heq => hr ((QuotientGroup.eq_one_iff r).mp heq)
    obtain ⟨k, hk⟩ := hAbR_p (Abelianization.of r)
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
      (orderOf_dvd_of_pow_eq_one hk)
    rcases j with _ | j'
    · rw [pow_zero] at hj
      exact absurd (orderOf_eq_one_iff.mp hj) hone
    · exact dvd_trans (by rw [hj]; exact dvd_pow_self p j'.succ_ne_zero)
        (orderOf_dvd_natCard (Abelianization.of r))
  -- `Abelianization Q ↠ Abelianization R` で位数が割り切れる
  have hsurj : Function.Surjective
      (Abelianization.map (QuotientGroup.mk' (pResidual p Q))) := by
    intro y
    obtain ⟨r, hy⟩ := QuotientGroup.mk'_surjective (commutator (Q ⧸ pResidual p Q)) y
    obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective (pResidual p Q) r
    exact ⟨Abelianization.of q, by rw [Abelianization.map_of, hq]; exact hy⟩
  exact h (hpAbR.trans (Subgroup.card_dvd_of_surjective _ hsurj))

/-- **`p ∤ |B : B'|` なら `O^p(B) = B`** (ambient 版)。9C.3 step (d) の入口。 -/
theorem pResidualOf_eq_self_of_not_dvd_card_abelianization [Finite G] {p : ℕ}
    [Fact p.Prime] {B : Subgroup G} (h : ¬ p ∣ Nat.card (Abelianization ↥B)) :
    pResidualOf p B = B := by
  have htop : pResidual p ↥B = ⊤ := pResidual_eq_top_of_not_dvd_card_abelianization h
  calc pResidualOf p B = (pResidual p ↥B).map B.subtype := rfl
    _ = (⊤ : Subgroup ↥B).map B.subtype := by rw [htop]
    _ = B := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- Abelianization の位数は全射像の側が割り切る: `|(A.map f)^{ab}| ∣ |A^{ab}|`。
9C.3 step (a) で互いに素性を商 `G/N` に遺伝させる。 -/
private theorem card_abelianization_map_dvd {G K : Type*} [Group G] [Group K]
    (f : G →* K) (A : Subgroup G) :
    Nat.card (Abelianization ↥(A.map f)) ∣ Nat.card (Abelianization ↥A) := by
  refine Subgroup.card_dvd_of_surjective (Abelianization.map (f.subgroupMap A)) ?_
  intro y
  obtain ⟨x, hy⟩ := QuotientGroup.mk'_surjective (commutator ↥(A.map f)) y
  obtain ⟨a, ha⟩ := f.subgroupMap_surjective A x
  exact ⟨Abelianization.of a, by rw [Abelianization.map_of, ha]; exact hy⟩

/-- 9C.3 step (b) の片翼: `N ⊴ G` が `A` を正規化する (Thm 2.6 が供給) とき、`A` の元に
よる共役は `D := (N ⊓ A) ⊔ (N ⊓ B)` を保つ。生成元で見ると、`x ∈ N ⊓ A` は
`a x a⁻¹ ∈ N ⊓ A`、`x ∈ N ⊓ B` は `a x a⁻¹ = [a,x] · x` で `[a,x] ∈ N ⊓ A`。 -/
private theorem conj_mem_inf_sup_inf {A B N : Subgroup G} [hNn : N.Normal]
    (hNA : N ≤ Subgroup.normalizer (A : Set G)) :
    ∀ a ∈ A, ∀ x ∈ (N ⊓ A) ⊔ (N ⊓ B), a * x * a⁻¹ ∈ (N ⊓ A) ⊔ (N ⊓ B) := by
  intro a ha x hx
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with h1 | h2
    · rw [SetLike.mem_coe, Subgroup.mem_inf] at h1
      exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr
        ⟨hNn.conj_mem s h1.1 a, A.mul_mem (A.mul_mem ha h1.2) (A.inv_mem ha)⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_inf] at h2
      have hcomm : a * s * a⁻¹ * s⁻¹ ∈ N ⊓ A := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact N.mul_mem (hNn.conj_mem s h2.1 a) (N.inv_mem h2.1)
        · have hsa : s * a⁻¹ * s⁻¹ ∈ A :=
            (Subgroup.mem_normalizer_iff.mp (hNA h2.1) a⁻¹).mp (A.inv_mem ha)
          rw [show a * s * a⁻¹ * s⁻¹ = a * (s * a⁻¹ * s⁻¹) by group]
          exact A.mul_mem ha hsa
      rw [show a * s * a⁻¹ = a * s * a⁻¹ * s⁻¹ * s by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcomm)
        (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr h2))
  | one => simp
  | mul x y _ _ ihx ihy =>
    rw [show a * (x * y) * a⁻¹ = a * x * a⁻¹ * (a * y * a⁻¹) by group]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ihx =>
    rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ihx

/-- **9C.3 の詰め (step (d)(e))**: `N ⊴ G` が `p`-群、`G = (A ⊔ N)·B`, `A ⊔ B = ⊤`,
`p ∤ |B:B'|` なら `G = AB`。

* Lemma 9.26 (`pResidualOf_sup_eq_of_isSubnormal`) で `O^p(A ⊔ N) = O^p(A)`。
* **積形 9C.2** を pair `(A ⊔ N, B)` に当てて `O^p(G) = O^p(A ⊔ N)·O^p(B) = O^p(A)·B`
  (`O^p(B) = B` は `p ∤ |B:B'|`)。
* `B ≤ O^p(G)` ゆえ `A ⊔ O^p(G) = ⊤`、正規部分群との積で `G = A·O^p(G)`。代入して
  `G = A·O^p(A)·B = A·B` (左吸収)。 -/
private theorem mul_eq_univ_endgame [Finite G] {p : ℕ} [Fact p.Prime] {A B N : Subgroup G}
    (hA : A.IsSubnormal) (hB : B.IsSubnormal) [hNn : N.Normal] (hNpg : IsPGroup p ↥N)
    (hgen : A ⊔ B = ⊤)
    (hprod : ((A ⊔ N : Subgroup G) : Set G) * (B : Set G) = Set.univ)
    (hpB : ¬ p ∣ Nat.card (Abelianization ↥B)) :
    (A : Set G) * (B : Set G) = Set.univ := by
  have hOB : pResidualOf p B = B := pResidualOf_eq_self_of_not_dvd_card_abelianization hpB
  have hNnormalizer : A ⊔ N ≤ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hOAN : pResidualOf p (A ⊔ N) = pResidualOf p A :=
    pResidualOf_sup_eq_of_isSubnormal le_sup_left le_sup_right hA.subgroupOf
      hNnormalizer hNpg rfl
  have h92 : (pResidualOf p (⊤ : Subgroup G) : Set G) =
      (pResidualOf p (A ⊔ N) : Set G) * (pResidualOf p B : Set G) :=
    pResidualOf_top_eq_mul_of_isSubnormal
      (Ch02.isSubnormal_sup_of_isSubnormal hA hNn.isSubnormal) hB hprod
  rw [hOAN, hOB] at h92
  have hBV : B ≤ pResidualOf p (⊤ : Subgroup G) := by
    conv_lhs => rw [← hOB]
    exact pResidualOf_mono le_top
  have hAV : A ⊔ pResidualOf p (⊤ : Subgroup G) = ⊤ :=
    top_le_iff.mp (hgen.symm.trans_le (sup_le_sup_left hBV A))
  have hmain : Set.univ = (A : Set G) * (pResidualOf p (⊤ : Subgroup G) : Set G) :=
    calc Set.univ = ((⊤ : Subgroup G) : Set G) := Subgroup.coe_top.symm
      _ = ((A ⊔ pResidualOf p (⊤ : Subgroup G) : Subgroup G) : Set G) := by rw [hAV]
      _ = _ := Subgroup.mul_normal A _
  rw [h92, ← mul_assoc, GroupTheory.coe_mul_coe_eq_left (pResidualOf_le p A)] at hmain
  exact hmain.symm

/-- 9C.3 の帰納核: `Nat.card G ≤ n` の有限群で `A, B ◁◁ G`, `A ⊔ B = ⊤`,
`|A:A'| ⊥ |B:B'|` ⟹ `G = AB` (集合の積)。`∀ G` を内側に量化して `n` で帰納。 -/
private theorem mul_eq_univ_coprime_aux.{u} (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G ≤ n →
      ∀ {A B : Subgroup G}, A.IsSubnormal → B.IsSubnormal → A ⊔ B = ⊤ →
        Nat.Coprime (Nat.card (Abelianization ↥A)) (Nat.card (Abelianization ↥B)) →
        (A : Set G) * (B : Set G) = Set.univ := by
  induction n with
  | zero =>
    intro G _ _ hcard
    exact absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ n IH =>
    intro G _ _ hcard A B hA hB hgen hcop
    by_cases hnt : Nontrivial G
    swap
    · -- `Subsingleton G`: 全元が `1 = 1 * 1`
      rw [not_nontrivial_iff_subsingleton] at hnt
      haveI := hnt
      refine Set.eq_univ_of_forall fun g => ?_
      exact ⟨1, A.one_mem, 1, B.one_mem, Subsingleton.elim _ _⟩
    haveI := hnt
    have htop_ne_bot : (⊤ : Subgroup G) ≠ ⊥ := by
      intro h
      obtain ⟨x, y, hxy⟩ := hnt
      apply hxy
      have hx : x ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_top x
      have hy : y ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_top y
      rw [Subgroup.mem_bot] at hx hy
      rw [hx, hy]
    obtain ⟨N, hN, _⟩ :=
      Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) htop_ne_bot
    haveI hNnorm : N.Normal := hN.1
    -- (a): `G/N` で帰納法 ⟹ 分解 `G = A·N·B`
    have hAbar : (A.map (QuotientGroup.mk' N)).IsSubnormal :=
      hA.map (QuotientGroup.mk'_surjective N)
    have hBbar : (B.map (QuotientGroup.mk' N)).IsSubnormal :=
      hB.map (QuotientGroup.mk'_surjective N)
    have hgenbar : A.map (QuotientGroup.mk' N) ⊔ B.map (QuotientGroup.mk' N) = ⊤ := by
      rw [← Subgroup.map_sup, hgen,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    have hcopbar : Nat.Coprime
        (Nat.card (Abelianization ↥(A.map (QuotientGroup.mk' N))))
        (Nat.card (Abelianization ↥(B.map (QuotientGroup.mk' N)))) :=
      Nat.Coprime.coprime_dvd_right (card_abelianization_map_dvd _ B)
        (Nat.Coprime.coprime_dvd_left (card_abelianization_map_dvd _ A) hcop)
    have h1lt_N : 1 < Nat.card ↥N := by
      have h_ne_one : Nat.card ↥N ≠ 1 := by
        intro h1
        apply hN.2.1
        haveI : Subsingleton ↥N := (Nat.card_eq_one_iff_unique.mp h1).1
        refine (Subgroup.eq_bot_iff_forall N).mpr fun x hx => ?_
        exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥N) 1)
      have h_pos : 0 < Nat.card ↥N := Nat.card_pos
      omega
    have hquot_le : Nat.card (G ⧸ N) ≤ n := by
      have heq : N.index * Nat.card ↥N = Nat.card G := N.index_mul_card
      have hidx : Nat.card (G ⧸ N) = N.index := rfl
      have hidxpos : 0 < N.index := by
        rcases Nat.eq_zero_or_pos N.index with h0 | h
        · rw [h0, zero_mul] at heq
          exact absurd heq.symm Nat.card_pos.ne'
        · exact h
      have hlt : Nat.card (G ⧸ N) < Nat.card G := by
        rw [hidx, ← heq]
        exact (Nat.lt_mul_iff_one_lt_right hidxpos).mpr h1lt_N
      omega
    have hIHquot := IH (G ⧸ N) hquot_le hAbar hBbar hgenbar hcopbar
    have hdecomp : ∀ g : G, ∃ a ∈ A, ∃ m ∈ N, ∃ b ∈ B, g = a * m * b := by
      intro g
      have hg : QuotientGroup.mk' N g ∈
          ((A.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) *
            ((B.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
        rw [hIHquot]; trivial
      obtain ⟨abar, habar, bbar, hbbar, heq⟩ := hg
      rw [SetLike.mem_coe] at habar hbbar
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp habar
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hbbar
      have hmk : QuotientGroup.mk' N (a * b) = QuotientGroup.mk' N g := by
        rw [map_mul]; exact heq
      obtain ⟨m, hm, hgm⟩ := (QuotientGroup.mk'_eq_mk' N).mp hmk
      exact ⟨a, ha, b * m * b⁻¹, hNnorm.conj_mem m hm b, b, hb, by rw [← hgm]; group⟩
    have hprodAN : ((A ⊔ N : Subgroup G) : Set G) * (B : Set G) = Set.univ := by
      refine Set.eq_univ_of_forall fun g => ?_
      obtain ⟨a, ha, m, hm, b, hb, hgeq⟩ := hdecomp g
      exact ⟨a * m,
        Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hm),
        b, hb, hgeq.symm⟩
    have hprodBN : ((B ⊔ N : Subgroup G) : Set G) * (A : Set G) = Set.univ := by
      refine Set.eq_univ_of_forall fun g => ?_
      obtain ⟨a, ha, m, hm, b, hb, hgeq⟩ := hdecomp g⁻¹
      refine ⟨b⁻¹ * m⁻¹,
        Subgroup.mul_mem _ (Subgroup.mem_sup_left (B.inv_mem hb))
          (Subgroup.mem_sup_right (N.inv_mem hm)),
        a⁻¹, A.inv_mem ha, ?_⟩
      have hg : g = (a * m * b)⁻¹ := by rw [← hgeq, inv_inv]
      rw [hg]; group
    -- (b): Thm 2.6 (Wielandt) — `N` は `A`, `B` を正規化 ⟹ `D` は `G`-正規
    have hNA : N ≤ Subgroup.normalizer (A : Set G) :=
      Ch02.isMinimalNormal_le_normalizer_of_isSubnormal hA hN
    have hNB : N ≤ Subgroup.normalizer (B : Set G) :=
      Ch02.isMinimalNormal_le_normalizer_of_isSubnormal hB hN
    have hDnorm : ((N ⊓ A) ⊔ (N ⊓ B)).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen, sup_le_iff]
      constructor
      · intro a ha
        rw [Subgroup.mem_normalizer_iff]
        intro x
        refine ⟨fun hx => conj_mem_inf_sup_inf hNA a ha x hx, fun hx => ?_⟩
        have hback := conj_mem_inf_sup_inf hNA a⁻¹ (A.inv_mem ha) _ hx
        rwa [show a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x by group] at hback
      · intro b hb
        have hswap : ∀ y ∈ B, ∀ x ∈ (N ⊓ A) ⊔ (N ⊓ B),
            y * x * y⁻¹ ∈ (N ⊓ A) ⊔ (N ⊓ B) := by
          intro y hy x hx
          rw [sup_comm] at hx ⊢
          exact conj_mem_inf_sup_inf (B := A) hNB y hy x hx
        rw [Subgroup.mem_normalizer_iff]
        intro x
        refine ⟨fun hx => hswap b hb x hx, fun hx => ?_⟩
        have hback := hswap b⁻¹ (B.inv_mem hb) _ hx
        rwa [show b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x by group] at hback
    -- (c): 極小性で `D = ⊥` か `D = N`
    rcases hN.2.2 _ hDnorm (sup_le inf_le_left inf_le_left) with hDbot | hDN
    · -- `D = ⊥`: `N ≤ Z(G)` かつ `|N| = p` 素数 ⟹ endgame (d)(e)
      have hNAbot : N ⊓ A = ⊥ := by
        rw [← le_bot_iff, ← hDbot]
        exact le_sup_left
      have hNBbot : N ⊓ B = ⊥ := by
        rw [← le_bot_iff, ← hDbot]
        exact le_sup_right
      have hNcent : N ≤ Subgroup.center G := by
        intro m hm
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ A ⊔ B := by rw [hgen]; exact Subgroup.mem_top g
        rw [Subgroup.sup_eq_closure] at hg
        induction hg using Subgroup.closure_induction with
        | mem s hs =>
          rcases hs with h1 | h2
          · rw [SetLike.mem_coe] at h1
            have hc : m * s * m⁻¹ * s⁻¹ ∈ N ⊓ A := by
              refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
              · rw [show m * s * m⁻¹ * s⁻¹ = m * (s * m⁻¹ * s⁻¹) by group]
                exact N.mul_mem hm (hNnorm.conj_mem m⁻¹ (N.inv_mem hm) s)
              · exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNA hm) s).mp h1)
                  (A.inv_mem h1)
            rw [hNAbot, Subgroup.mem_bot] at hc
            have hc' : (m * s) * (s * m)⁻¹ = 1 := by
              rw [show (m * s) * (s * m)⁻¹ = m * s * m⁻¹ * s⁻¹ by group]
              exact hc
            exact (mul_inv_eq_one.mp hc').symm
          · rw [SetLike.mem_coe] at h2
            have hc : m * s * m⁻¹ * s⁻¹ ∈ N ⊓ B := by
              refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
              · rw [show m * s * m⁻¹ * s⁻¹ = m * (s * m⁻¹ * s⁻¹) by group]
                exact N.mul_mem hm (hNnorm.conj_mem m⁻¹ (N.inv_mem hm) s)
              · exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNB hm) s).mp h2)
                  (B.inv_mem h2)
            rw [hNBbot, Subgroup.mem_bot] at hc
            have hc' : (m * s) * (s * m)⁻¹ = 1 := by
              rw [show (m * s) * (s * m)⁻¹ = m * s * m⁻¹ * s⁻¹ by group]
              exact hc
            exact (mul_inv_eq_one.mp hc').symm
        | one => rw [one_mul, mul_one]
        | mul x y _ _ ihx ihy =>
          calc x * y * m = x * (y * m) := by group
            _ = x * (m * y) := by rw [ihy]
            _ = x * m * y := by group
            _ = m * x * y := by rw [ihx]
            _ = m * (x * y) := by group
        | inv x _ ihx =>
          calc x⁻¹ * m = x⁻¹ * (m * x) * x⁻¹ := by group
            _ = x⁻¹ * (x * m) * x⁻¹ := by rw [← ihx]
            _ = m * x⁻¹ := by group
      obtain ⟨p, hp, hcardN⟩ :=
        Ch02.exists_prime_card_of_isMinimalNormal_of_le_center hN hNcent
      haveI : Fact p.Prime := ⟨hp⟩
      have hNpg : IsPGroup p ↥N := IsPGroup.of_card (by rw [hcardN, pow_one])
      by_cases hpB : p ∣ Nat.card (Abelianization ↥B)
      · -- 互いに素性から `p ∤ |A:A'|`: 役割交換で endgame
        have hpA : ¬ p ∣ Nat.card (Abelianization ↥A) := by
          intro hpA
          have hgcd : Nat.gcd (Nat.card (Abelianization ↥A))
              (Nat.card (Abelianization ↥B)) = 1 := hcop
          have hdvd1 : p ∣ 1 := by rw [← hgcd]; exact Nat.dvd_gcd hpA hpB
          exact absurd (Nat.dvd_one.mp hdvd1) hp.one_lt.ne'
        have hBA : (B : Set G) * (A : Set G) = Set.univ :=
          mul_eq_univ_endgame hB hA hNpg (by rw [sup_comm]; exact hgen) hprodBN hpA
        exact GroupTheory.mul_eq_univ_comm hBA
      · exact mul_eq_univ_endgame hA hB hNpg hgen hprodAN hpB
    · -- `D = N`: `N = (N⊓A)·(N⊓B)` を分解に代入して直接 `G = AB`
      have hNnormNA : N ≤ Subgroup.normalizer ((N ⊓ A : Subgroup G) : Set G) := by
        have hstep : ∀ m ∈ N, ∀ x, x ∈ N ⊓ A → m * x * m⁻¹ ∈ N ⊓ A := by
          intro m hm x hx
          obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
          exact Subgroup.mem_inf.mpr ⟨hNnorm.conj_mem x hx1 m,
            (Subgroup.mem_normalizer_iff.mp (hNA hm) x).mp hx2⟩
        intro m hm
        rw [Subgroup.mem_normalizer_iff]
        intro x
        refine ⟨fun hx => hstep m hm x hx, fun hx => ?_⟩
        have hback := hstep m⁻¹ (N.inv_mem hm) _ hx
        rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x by group] at hback
      have hNprod : (N : Set G) =
          ((N ⊓ A : Subgroup G) : Set G) * ((N ⊓ B : Subgroup G) : Set G) := by
        rw [← GroupTheory.coe_sup_eq_mul_of_le_normalizer
          (le_trans inf_le_left hNnormNA), hDN]
      refine Set.eq_univ_of_forall fun g => ?_
      obtain ⟨a, ha, m, hm, b, hb, hgeq⟩ := hdecomp g
      have hmset : m ∈ (N : Set G) := hm
      rw [hNprod] at hmset
      obtain ⟨u, hu, v, hv, huv⟩ := hmset
      have huA : u ∈ A := (Subgroup.mem_inf.mp hu).2
      have hvB : v ∈ B := (Subgroup.mem_inf.mp hv).2
      exact ⟨a * u, A.mul_mem ha huA, v * b, B.mul_mem hvB hb,
        by rw [hgeq, ← huv]; group⟩

/-- **Isaacs Problem 9C.3** (書籍 p. 289) ⭐: `G = ⟨A, B⟩` で `A, B ⊲⊲ G`、
`|A:A'| = |Abelianization A|` と `|B:B'|` が互いに素なら `G = AB` (集合の積)。

書籍 hint の 5 段を `|G|` の直接帰納で形式化:
* **(a)** 極小正規 `N` を取り `G/N` で帰納 ⟹ 分解 `G = A·N·B`。互いに素性は
  abelianization の全射性 (`card_abelianization_map_dvd`) で商に遺伝。
* **(b)** `D := (N⊓A)(N⊓B)` は `A` と `B` に正規化される。鍵は **Thm 2.6 (Wielandt)**
  (`isMinimalNormal_le_normalizer_of_isSubnormal`): 極小正規 `N` は subnormal な `A`, `B`
  を正規化するので `[A, N] ≤ N ⊓ A` となり、`x ∈ N⊓B` に対し `a x a⁻¹ = [a,x]·x ∈ D`。
  書籍はこの段の論法を明示しないが、Thm 2.6 で一様に処理できる
  (abelian / 非 abelian の場合分けも不要)。
* **(c)** `D ⊴ G` と `N` の極小性で `D = ⊥` か `D = N`。`D = N` なら分解に代入して
  ただちに `G = AB`。`D = ⊥` なら `[A,N] = [B,N] = 1` ⟹ `N ≤ Z(G)`、極小性から
  `|N| = p` 素数 (`exists_prime_card_of_isMinimalNormal_of_le_center`)。
* **(d)** 互いに素性から WLOG `p ∤ |B:B'|`、つまり `O^p(B) = B`
  (`pResidualOf_eq_self_of_not_dvd_card_abelianization`)。**積形 9C.2** を
  pair `(A ⊔ N, B)` (積 `= G` は (a) から) に当て、Lemma 9.26 で
  `O^p(A ⊔ N) = O^p(A)` に簡約して `O^p(G) = O^p(A)·B`。
* **(e)** `B ≤ O^p(G)` ゆえ `A ⊔ O^p(G) = ⊤` で `G = A·O^p(G)` (正規部分群との積)。
  (d) を代入し `A·O^p(A) = A` の吸収で `G = A·B`。 -/
theorem mul_eq_univ_of_isSubnormal_of_coprime_abelianization [Finite G]
    {A B : Subgroup G} (hA : A.IsSubnormal) (hB : B.IsSubnormal) (hgen : A ⊔ B = ⊤)
    (hcop : Nat.Coprime (Nat.card (Abelianization ↥A))
      (Nat.card (Abelianization ↥B))) :
    (A : Set G) * (B : Set G) = Set.univ :=
  mul_eq_univ_coprime_aux (Nat.card G) G le_rfl hA hB hgen hcop

end -- 9C.3

end OddOrder.Isaacs.Ch09
