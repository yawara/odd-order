/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.ThompsonWielandt

/-!
# Isaacs §9C の演習 (書籍 pp. 288-289)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 9C
(Thompson–Wielandt 周辺)。statement はページ画像
`references/isaacs/pages/isaacs-p288-301.png` / `isaacs-p289-302.png` で確定。

* **9C.1** `relCore_thompsonWielandtCore_eq_bot_or_of_isSubnormal` — Thm 9.24 の設定で
  `H`, `K` がともに `G` で **subnormal** なら `U = 1` または `V = 1`。
* **9C.2** `pResidualOf_top_eq_sup_of_isSubnormal` — `G = AB` で `A, B ⊲⊲ G` なら
  `O^p(G) = O^p(A) O^p(B)`。9B.5 (`G^∞ = A^∞B^∞`) と同型の帰納法。
  ⚠ 仮説は join でなく**積** `(A : Set G) * B = Set.univ`。

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

end -- 9C.2

end OddOrder.Isaacs.Ch09
