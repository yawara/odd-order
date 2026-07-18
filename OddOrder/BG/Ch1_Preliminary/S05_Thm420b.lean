/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S05_NarrowPGroups
import Mathlib.GroupTheory.Sylow

/-!
# BG §4: Theorem 4.20(b) — characteristic subgroups of a Sylow inside `S'` are `G`-normal

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §4 Theorem 4.20(b) (mmd `references/bg/local-analysis.mmd`
L1783). Issue `3014`.

**Theorem 4.20(b)** (`characteristic_le_derived_normal_of_rank_fitting_le_two`): let `G` be a
finite solvable group of odd order with `r(F(G)) ≤ 2`.  If `S` is a Sylow subgroup of `G`, `T`
is a *characteristic* subgroup of `S`, and `T ⊆ S'` (`= ⁅S, S⁆`), then `T ⊴ G`.

## Proof (mmd L1793)

Write `F := F(G)`, `p` the prime with `S` a Sylow `p`-subgroup, `TG := T`-inside-`G`.

1. By Theorem 4.20(a) (`derived_le_fitting_of_rank_fitting_le_two`), `G' ≤ F`, so `G/F` is
   abelian; in particular every subgroup `⊇ G'` is normal.
2. `TG ≤ S' = ⁅S, S⁆ ≤ ⁅⊤, ⊤⁆ = G' ≤ F` and `TG ≤ S`, so `TG ≤ F ⊓ S`.
3. **Frattini**: `F ⊔ S ⊴ G` (it contains `G'`), so with `S` a Sylow `p` of `F ⊔ S`
   (`Sylow.normalizer_sup_eq_top'`) `N_G(S) ⊔ (F ⊔ S) = ⊤`; simplifying (`S ≤ N_G(S)`) gives
   `N_G(S) ⊔ F = ⊤`.
4. `T char S ⟹ N_G(S) ≤ N_G(TG)` (`normalizer_le_normalizer_map_of_char`), so also
   `S ≤ N_G(S) ≤ N_G(TG)`.
5. `F ≤ N_G(TG)`: writing `F = ⨆_q O_q(G)`, the summand `O_p(G) ≤ S ≤ N_G(TG)`, while for
   `q ≠ p` the summand `O_q(G)` centralizes `O_p(G) ⊇ TG` (`commute_of_normal_of_disjoint`),
   hence `O_q(G) ≤ C_G(TG) ≤ N_G(TG)`.  Here `TG ≤ O_p(G)` because `TG` is a `p`-group inside
   the nilpotent `F` (`le_opCore_of_isPGroup_of_le_fitting`).
6. `⊤ = N_G(S) ⊔ F ≤ N_G(TG)`, so `N_G(TG) = ⊤`, i.e. `TG ⊴ G`.
-/

namespace OddOrder.BG.Ch1.S05

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- **Characteristic transport under normalizers.** If `W` is a characteristic subgroup of
`K ≤ G` (as a subgroup of `↥K`), then `N_G(K) ≤ N_G(W.map K.subtype)`: for `g ∈ N_G(K)`,
conjugation by `g` restricts to an automorphism of `↥K`, which preserves the characteristic
`W`.  (Self-contained reproduction of the §7D Thompson helper of the same name, kept here so
that this file depends only on §5 and mathlib.) -/
private theorem normalizer_le_normalizer_map_of_char
    {K : Subgroup G} {W : Subgroup ↥K} [W.Characteristic] :
    Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((W.map K.subtype) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  -- The automorphism of `↥K` induced by conjugation by `g ∈ N_G(K)`.
  set cg : ↥K ≃* ↥K := K.normalizerMonoidHom (⟨g, hg⟩ : ↥(Subgroup.normalizer (K : Set G)))
    with hcg_def
  have hWfix : W.map (cg : ↥K →* ↥K) = W :=
    (Subgroup.characteristic_iff_map_eq.mp ‹W.Characteristic›) cg
  have hcg_apply : ∀ w : ↥K, ((cg w : ↥K) : G) = g * (w : G) * g⁻¹ := fun _ => rfl
  have hcg_symm_apply : ∀ w : ↥K, ((cg.symm w : ↥K) : G) = g⁻¹ * (w : G) * g := by
    intro w
    have h := hcg_apply (cg.symm w)
    rw [cg.apply_symm_apply] at h
    rw [h]; group
  intro y
  simp only [Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨w, hwW, rfl⟩
    refine ⟨cg w, ?_, ?_⟩
    · rw [← hWfix]; exact ⟨w, hwW, rfl⟩
    · rw [hcg_apply]
  · rintro ⟨w, hwW, hyeq⟩
    refine ⟨cg.symm w, ?_, ?_⟩
    · rw [← hWfix] at hwW
      obtain ⟨w', hw'W, hw'eq⟩ := hwW
      have : cg.symm w = w' := by rw [← hw'eq]; exact cg.symm_apply_apply w'
      rw [this]; exact hw'W
    · rw [hcg_symm_apply, hyeq]; group

/-- **A `p`-subgroup of the (nilpotent) Fitting subgroup lands in `O_p(G)`.** If `W ≤ F(G)` is a
`p`-group, then `W ≤ O_p(G)`: the Sylow `p` of the nilpotent `F(G)` containing `W.subgroupOf F`
is normal (`Sylow.normal_of_isNilpotent`), hence characteristic, and its `G`-image is a normal
`p`-subgroup, so `≤ O_p(G)` by Problem 1B.2.  (Reproduction of the private §5 helper.) -/
private theorem le_opCore_of_isPGroup_of_le_fitting {p : ℕ} [Fact p.Prime]
    {W : Subgroup G} (hW : IsPGroup p ↥W) (hWF : W ≤ Ch01.fitting G) :
    W ≤ Ch01.opCore p G := by
  classical
  have hW'_pg : IsPGroup p ↥(W.subgroupOf (Ch01.fitting G)) :=
    hW.of_injective (Subgroup.subgroupOfEquivOfLe hWF).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hWF).injective
  obtain ⟨P, hWP⟩ := hW'_pg.exists_le_sylow
  have hPnorm : P.Normal := Ch01.Sylow.normal_of_isNilpotent P
  haveI : (P : Subgroup ↥(Ch01.fitting G)).Characteristic :=
    Sylow.characteristic_of_normal P hPnorm
  haveI : ((P : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype).Normal :=
    inferInstance
  have hPmap_pg :
      IsPGroup p ↥((P : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype) :=
    P.2.map _
  calc W = (W.subgroupOf (Ch01.fitting G)).map (Ch01.fitting G).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hWF).symm
    _ ≤ (P : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype :=
        Subgroup.map_mono hWP
    _ ≤ Ch01.opCore p G := Ch01.normal_pgroup_le_opCore hPmap_pg

/-- **BG Theorem 4.20(b)** (mmd L1783): let `G` be a finite solvable group of odd order with
`r(F(G)) ≤ 2`.  If `T` is a characteristic subgroup of a Sylow `p`-subgroup `S` of `G` with
`T ⊆ S' = ⁅S, S⁆`, then the image of `T` in `G` is normal in `G`. -/
theorem characteristic_le_derived_normal_of_rank_fitting_le_two
    [IsSolvable G] (hodd : Odd (Nat.card G))
    (hrank : rank ↥(Ch01.fitting G) ≤ 2)
    {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    {T : Subgroup ↥(S : Subgroup G)} (hTchar : T.Characteristic)
    (hTderiv : T.map (S : Subgroup G).subtype ≤ ⁅(S : Subgroup G), (S : Subgroup G)⁆) :
    (T.map (S : Subgroup G).subtype).Normal := by
  classical
  haveI := hTchar
  -- Trivial group: every subgroup is normal.
  rcases subsingleton_or_nontrivial G with hsub | hnt
  · exact ⟨fun n hn g => by rwa [Subsingleton.elim (g * n * g⁻¹) n]⟩
  set TG : Subgroup G := T.map (S : Subgroup G).subtype with hTG_def
  -- Step 1: `G' ≤ F` (Theorem 4.20(a)).
  have hG' : commutator G ≤ Ch01.fitting G :=
    derived_le_fitting_of_rank_fitting_le_two hodd hrank
  -- Step 2: `TG ≤ S` and `TG ≤ F`.
  have hTG_le_S : TG ≤ (S : Subgroup G) := Subgroup.map_subtype_le T
  have hTG_le_F : TG ≤ Ch01.fitting G :=
    le_trans hTderiv (le_trans (Subgroup.commutator_mono le_top le_top) hG')
  -- Step 4: `T char S ⟹ N_G(S) ≤ N_G(TG)`, hence `S ≤ N_G(TG)`.
  have hStep4 : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
      Subgroup.normalizer (TG : Set G) := by
    rw [hTG_def]; exact normalizer_le_normalizer_map_of_char
  have hS_le_NT : (S : Subgroup G) ≤ Subgroup.normalizer (TG : Set G) :=
    le_trans Subgroup.le_normalizer hStep4
  -- Step 3: Frattini. `F ⊔ S ⊴ G` (contains `G'`), so `N_G(S) ⊔ F = ⊤`.
  haveI hHnorm : (Ch01.fitting G ⊔ (S : Subgroup G)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hc : ⁅g, n⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n)
    have hgn : g * n * g⁻¹ = ⁅g, n⁆ * n := by rw [commutatorElement_def]; group
    rw [hgn]
    exact (Ch01.fitting G ⊔ (S : Subgroup G)).mul_mem (Subgroup.mem_sup_left (hG' hc)) hn
  have hfratt : Subgroup.normalizer ((S : Subgroup G) : Set G) ⊔
      (Ch01.fitting G ⊔ (S : Subgroup G)) = ⊤ :=
    Sylow.normalizer_sup_eq_top' S le_sup_right
  have hfratt2 : Subgroup.normalizer ((S : Subgroup G) : Set G) ⊔ Ch01.fitting G = ⊤ := by
    rw [sup_comm (Ch01.fitting G) (S : Subgroup G), ← sup_assoc,
      sup_eq_left.mpr Subgroup.le_normalizer] at hfratt
    exact hfratt
  -- Step 5: `F ≤ N_G(TG)`.
  have hTG_pg : IsPGroup p ↥TG := S.isPGroup'.to_le hTG_le_S
  have hTG_le_Op : TG ≤ Ch01.opCore p G :=
    le_opCore_of_isPGroup_of_le_fitting hTG_pg hTG_le_F
  have hStep5 : Ch01.fitting G ≤ Subgroup.normalizer (TG : Set G) := by
    have hbound : ∀ q : Nat.Primes, Ch01.opCore (q : ℕ) G ≤ Subgroup.normalizer (TG : Set G) := by
      intro q
      haveI hqfact : Fact (q : ℕ).Prime := ⟨q.2⟩
      by_cases hq : (q : ℕ) = p
      · -- `O_p(G) ≤ S ≤ N_G(TG)`.
        rw [hq]; exact le_trans (Ch01.opCore_le S) hS_le_NT
      · -- `O_q(G)` centralizes `O_p(G) ⊇ TG`, hence `≤ C_G(TG) ≤ N_G(TG)`.
        have hdis : Disjoint (Ch01.opCore (q : ℕ) G) (Ch01.opCore p G) :=
          IsPGroup.disjoint_of_ne (q : ℕ) p hq _ _
            (Ch01.opCore_isPGroup (q : ℕ) G) (Ch01.opCore_isPGroup p G)
      -- `O_q ≤ C_G(TG)`
        have hqc : Ch01.opCore (q : ℕ) G ≤ Subgroup.centralizer (TG : Set G) := by
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (Subgroup.commute_of_normal_of_disjoint _ _ (Ch01.opCore.normal (q : ℕ) G)
            (Ch01.opCore.normal p G) hdis x y hx (hTG_le_Op hy)).symm
        exact le_trans hqc (Subgroup.centralizer_le_normalizer _)
    calc Ch01.fitting G = ⨆ q : Nat.Primes, Ch01.opCore (q : ℕ) G := rfl
      _ ≤ Subgroup.normalizer (TG : Set G) := iSup_le hbound
  -- Step 6: assemble.
  have htop : Subgroup.normalizer (TG : Set G) = ⊤ := by
    have hle : Subgroup.normalizer ((S : Subgroup G) : Set G) ⊔ Ch01.fitting G ≤
        Subgroup.normalizer (TG : Set G) :=
      sup_le hStep4 hStep5
    rw [hfratt2] at hle
    exact top_le_iff.mp hle
  exact Subgroup.normalizer_eq_top_iff.mp htop

end OddOrder.BG.Ch1.S05
