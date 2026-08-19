/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Carter.NilpotentQuotient

/-!
# Isaacs Problem 3C.7(a) — Carter 部分群の存在

有限可解群は Carter 部分群 (冪零かつ自己正規化) を持つ。書籍は証明を与えない
(challenge problem) ので証明は自前。

`|G|` の強帰納。`G` が冪零なら `⊤` が Carter。そうでなければ極小正規部分群 `N` を取り、
帰納法の仮説で `G ⧸ N` の Carter 部分群 `K̄` を得て、その引き戻し `K` を考える。

* **`K < ⊤`**: 帰納法の仮説で `↥K` の Carter 部分群 `C` を取る。`↥K ⧸ (N ∩ K) ≅ K̄` は
  冪零なので 3C.7(c) が `N ⊔ C = K` を与え、`N_G(C) ≤ N_G(N ⊔ C) = N_G(K) = K`。
  `C` は `↥K` で自己正規化なので `N_G(C) = C`, すなわち `C` は `G` の Carter 部分群。
* **`K = ⊤`** (= `G ⧸ N` が冪零): `G` は冪零でないので正規でない極大部分群 `M` がある
  (`Group.isNilpotent_of_finite_tfae`)。`N ≤ M` だと `M ⊴ G` になってしまう
  (`normal_of_isCoatom_of_le_of_isNilpotent_quotient`) ので `N ⊄ M`, ゆえに
  `M ⊔ N = ⊤` かつ (極小性から) `M ⊓ N = ⊥`。すると `↥M ≅ G ⧸ N` は冪零で、
  極大性と非正規性から `N_G(M) = M`。よって `M` が Carter 部分群
  (`isCarterSubgroup_of_isCoatom_not_normal`)。

## Main results

- `normal_of_isCoatom_of_le_of_isNilpotent_quotient` — `G ⧸ N` 冪零 + `N ≤ M` 極大 ⟹ `M ⊴ G`。
- `isCarterSubgroup_of_isCoatom_not_normal` — 上記 `K = ⊤` の場合の Carter 部分群。
- `exists_isCarterSubgroup` — **Problem 3C.7(a)**。
-/

namespace OddOrder.Isaacs.Ch03

open _root_.OddOrder.Isaacs.Ch03.Subgroup Pointwise

section /- 3C.7(a): 存在 -/

universe u

variable {G : Type*} [Group G]

/-- `G ⧸ N` が冪零で `N ≤ M`, `M` が極大 (coatom) なら `M ⊴ G`。

`N_G(M) = M` だとすると対応定理 (`normalizer_eq_iff_map_mk'`) で `M/N` が `G/N` の
自己正規化部分群になり、冪零性から `M/N = ⊤`, ゆえに `M = ⊤` で極大性に矛盾。
よって `M < N_G(M)`, 極大性から `N_G(M) = ⊤` すなわち `M ⊴ G`。 -/
theorem normal_of_isCoatom_of_le_of_isNilpotent_quotient {N M : Subgroup G} [N.Normal]
    (hnil : Group.IsNilpotent (G ⧸ N)) (hM : IsCoatom M) (hNM : N ≤ M) : M.Normal := by
  have := hnil
  have hne : Subgroup.normalizer (M : Set G) ≠ M := by
    intro h
    have hbar := (normalizer_eq_iff_map_mk' M hNM).mpr h
    have htop : M.map (QuotientGroup.mk' N) = ⊤ :=
      normalizerCondition_iff_only_full_group_self_normalizing.mp
        Group.normalizerCondition_of_isNilpotent _ hbar
    have hcomap := congrArg (Subgroup.comap (QuotientGroup.mk' N)) htop
    rw [Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hNM),
      Subgroup.comap_top] at hcomap
    exact hM.1 hcomap
  rw [← Subgroup.normalizer_eq_top_iff]
  exact hM.2 _ (lt_of_le_of_ne Subgroup.le_normalizer (Ne.symm hne))

/-- `N` が極小正規で `G ⧸ N` が冪零のとき, **正規でない極大部分群 `M` は Carter 部分群**。

`N ≤ M` だと `M ⊴ G` になる (`normal_of_isCoatom_of_le_of_isNilpotent_quotient`) ので
`N ⊄ M`, ゆえに極大性から `M ⊔ N = ⊤`, `N` の極小性から `M ⊓ N = ⊥`。
すると `↥M ↪ G ⧸ N` は全単射なので `↥M ≅ G ⧸ N` は冪零。
`M ≤ N_G(M)` で `M < N_G(M)` なら極大性より `N_G(M) = ⊤`, これは `M ⊴ G` を意味して
仮定に反するので `N_G(M) = M`。 -/
theorem isCarterSubgroup_of_isCoatom_not_normal {N M : Subgroup G} [N.Normal]
    (hN : Ch02.IsMinimalNormal N) (hnil : Group.IsNilpotent (G ⧸ N))
    (habel : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hM : IsCoatom M) (hMnn : ¬ M.Normal) : IsCarterSubgroup M := by
  have := hnil
  have hNM : ¬ N ≤ M := fun h =>
    hMnn (normal_of_isCoatom_of_le_of_isNilpotent_quotient hnil hM h)
  have hMN : M ⊔ N = ⊤ :=
    hM.2 _ (lt_of_le_of_ne le_sup_left fun h => hNM (le_sup_right.trans h.ge))
  have hMiN : M ⊓ N = ⊥ := by
    have := normal_inf_of_comm_of_sup_eq_top (C := M) habel hMN
    rcases hN.2.2 (M ⊓ N) inferInstance inf_le_right with h | h
    · exact h
    · exact absurd (h ▸ (inf_le_left : M ⊓ N ≤ M)) hNM
  refine ⟨?_, ?_⟩
  · -- `↥M ≅ G ⧸ N` は冪零。
    have hinj : Function.Injective ((QuotientGroup.mk' N).comp M.subtype) := by
      rw [injective_iff_map_eq_one]
      rintro ⟨x, hxM⟩ hx
      have hxN : x ∈ N := by
        simpa [QuotientGroup.eq_one_iff] using hx
      have hmem : x ∈ (M ⊓ N : Subgroup G) := ⟨hxM, hxN⟩
      rw [hMiN, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp M.subtype) := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      have hg : g ∈ ((M : Set G) * (N : Set G)) := by
        rw [← Subgroup.mul_normal M N, hMN]
        trivial
      obtain ⟨m, hm, x, hx, rfl⟩ := hg
      refine ⟨⟨m, hm⟩, ?_⟩
      have hx1 : (QuotientGroup.mk' N) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      change (QuotientGroup.mk' N) m = (QuotientGroup.mk' N) (m * x)
      rw [map_mul, hx1, mul_one]
    exact Group.nilpotent_of_mulEquiv
      (MulEquiv.ofBijective _ ⟨hinj, hsurj⟩ : ↥M ≃* G ⧸ N).symm
  · rcases eq_or_lt_of_le (Subgroup.le_normalizer (H := M)) with h | h
    · exact h.symm
    · exact absurd (Subgroup.normalizer_eq_top_iff.mp (hM.2 _ h)) hMnn

set_option backward.isDefEq.respectTransparency false in
/-- 3C.7(a) の `|G|` 強帰納本体。 -/
private theorem exists_isCarterSubgroup_aux : ∀ (n : ℕ) {G : Type u} [Group G] [Finite G]
    [Group.IsSolvable G], Nat.card G ≤ n → ∃ C : Subgroup G, IsCarterSubgroup C := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ hcard
    exact absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ _ hcard
    by_cases hnil : Group.IsNilpotent G
    · have := hnil
      exact ⟨⊤, isCarterSubgroup_top_of_isNilpotent⟩
    -- 冪零でないので `G` は非自明。
    have hGtriv : (⊤ : Subgroup G) ≠ ⊥ := by
      intro h
      have hone : ∀ x : G, x = 1 := fun x =>
        Subgroup.mem_bot.mp (h ▸ (Subgroup.mem_top x))
      have : Subsingleton G := ⟨fun a b => by rw [hone a, hone b]⟩
      exact hnil inferInstance
    obtain ⟨N, hN, -⟩ := Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) hGtriv
    have := hN.1
    obtain ⟨Kbar, hKbar⟩ := ih (G := G ⧸ N)
      (Nat.lt_succ_iff.mp (lt_of_lt_of_le (card_quotient_lt hN.2.1) hcard))
    have hNK : N ≤ Kbar.comap (QuotientGroup.mk' N) := by
      have hker := Subgroup.ker_le_comap (QuotientGroup.mk' N) Kbar
      rwa [QuotientGroup.ker_mk'] at hker
    have hKmap : (Kbar.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = Kbar :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Kbar
    by_cases hKtop : Kbar.comap (QuotientGroup.mk' N) = ⊤
    · -- `G ⧸ N` が冪零なので正規でない極大部分群が Carter。
      have hKbartop : Kbar = ⊤ := by
        rw [← hKmap, hKtop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
      have hquotnil : Group.IsNilpotent (G ⧸ N) := by
        have : Group.IsNilpotent ↥(⊤ : Subgroup (G ⧸ N)) := hKbartop ▸ hKbar.1
        exact Group.nilpotent_of_mulEquiv Subgroup.topEquiv
      obtain ⟨M, hMcoatom, hMnn⟩ : ∃ M : Subgroup G, IsCoatom M ∧ ¬ M.Normal := by
        by_contra hcon
        refine hnil (((Group.isNilpotent_of_finite_tfae (G := G)).out 2 0).mp ?_)
        intro H hH
        by_contra hHn
        exact hcon ⟨H, hH, hHn⟩
      exact ⟨M, isCarterSubgroup_of_isCoatom_not_normal hN hquotnil
        (minimal_normal_isAbelian_of_isSolvable hN) hMcoatom hMnn⟩
    · -- `K < ⊤`: `↥K` の Carter 部分群がそのまま `G` の Carter 部分群。
      set K : Subgroup G := Kbar.comap (QuotientGroup.mk' N) with hKdef
      have hKlt : Nat.card ↥K < Nat.card G := by
        classical
        obtain ⟨x, hx⟩ : ∃ x : G, x ∉ K := by
          simpa [Subgroup.eq_top_iff'] using hKtop
        exact Finite.card_subtype_lt (x := x) hx
      obtain ⟨C', hC'⟩ := ih (G := ↥K) (Nat.lt_succ_iff.mp (lt_of_lt_of_le hKlt hcard))
      have : (N.subgroupOf K).Normal := Subgroup.normal_subgroupOf
      -- `↥K ⧸ (N ∩ K) ≅ K̄` は冪零。
      have hquotK : Group.IsNilpotent (↥K ⧸ (N.subgroupOf K)) := by
        have := hKbar.1
        have hsurj : Function.Surjective
            (((QuotientGroup.mk' N).comp K.subtype).codRestrict Kbar fun x => x.2) := by
          rintro ⟨y, hy⟩
          obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
          exact ⟨⟨g, hy⟩, rfl⟩
        have hker : (((QuotientGroup.mk' N).comp K.subtype).codRestrict Kbar
            fun x => x.2).ker = N.subgroupOf K := by
          ext x
          simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
        have hequiv := (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
          (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)
        exact Group.nilpotent_of_mulEquiv hequiv.symm
      -- 3C.7(c) で `N ⊔ C = K`。
      have hsupK : (N.subgroupOf K) ⊔ C' = ⊤ := sup_eq_top_of_isNilpotent_quotient hC' hquotK
      refine ⟨C'.map K.subtype, isNilpotent_map_of_isNilpotent hC'.1 K.subtype, ?_⟩
      have hCK : C'.map K.subtype ≤ K := Subgroup.map_subtype_le C'
      have hCsub : (C'.map K.subtype).subgroupOf K = C' :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective C'
      have hNCK : N ⊔ C'.map K.subtype = K := by
        have hmap := congrArg (Subgroup.map K.subtype) hsupK
        rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNK,
          ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
      have hKself : Subgroup.normalizer (K : Set G) = K :=
        (normalizer_eq_iff_map_mk' K hNK).mp (by rw [hKmap]; exact hKbar.2)
      refine le_antisymm (fun g hg => ?_) Subgroup.le_normalizer
      have hgK : g ∈ K := by
        have hstep : Subgroup.normalizer ((C'.map K.subtype : Subgroup G) : Set G)
            ≤ Subgroup.normalizer ((N ⊔ C'.map K.subtype : Subgroup G) : Set G) := fun a ha =>
          Subgroup.normalizer_inf_normalizer_le_normalizer_sup N (C'.map K.subtype)
            ⟨by rw [Subgroup.normalizer_eq_top (H := N)]; trivial, ha⟩
        rw [hNCK, hKself] at hstep
        exact hstep hg
      have hmemC' : (⟨g, hgK⟩ : ↥K) ∈ C' := by
        have hnormK : (⟨g, hgK⟩ : ↥K) ∈
            Subgroup.normalizer (((C'.map K.subtype).subgroupOf K : Subgroup ↥K) : Set ↥K) := by
          rw [← Subgroup.subgroupOf_normalizer_eq hCK]
          exact Subgroup.mem_subgroupOf.mpr hg
        rwa [hCsub, hC'.normalizer_eq] at hnormK
      exact ⟨⟨g, hgK⟩, hmemC', rfl⟩

/-- **Isaacs Problem 3C.7(a)** (書籍 p. 91): 有限可解群は Carter 部分群
(冪零かつ自己正規化な部分群) を持つ。

書籍は証明を与えない (challenge problem)。証明は `|G|` の強帰納 (ファイル冒頭の骨格)。 -/
theorem exists_isCarterSubgroup {G : Type u} [Group G] [Finite G] [Group.IsSolvable G] :
    ∃ C : Subgroup G, IsCarterSubgroup C :=
  exists_isCarterSubgroup_aux (Nat.card G) le_rfl

end -- 3C.7(a)

end OddOrder.Isaacs.Ch03
