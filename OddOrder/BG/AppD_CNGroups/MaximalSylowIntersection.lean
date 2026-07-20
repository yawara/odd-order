/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppD_CNGroups.Basic
import OddOrder.BG.Ch2_Uniqueness.S08_FittingOfMaximal
import OddOrder.GroupTheory.CNGroupStructure

/-!
# BG Appendix D: maximal Sylow intersections in a minimal simple CN-group

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix D, pp. 153--154.

This file carries the local analysis at the heart of Lemma D.1.  Fix a Sylow `p`-subgroup `P` of
a minimal simple CN-group `G` of odd order and put

  `N = N_G(Z(L(P)))`

(BG writes `N_G(Z(J(P)))` and explicitly sanctions substituting `L(P)` for `J(P)` throughout,
so as to use Theorem B.4 in place of Theorem 6.2; that is what the repository has).  The main
result says that for **every** Sylow `p`-subgroup `Q ≠ P` with `P ∩ Q` maximal, `N` is a 3-step
group with respect to `p` and

  `P ∩ Q = O_p(N)`.

Since `N` depends only on `P`, this is BG's display (D.2), and it pins every maximal intersection
with `P` to one and the same subgroup.

## A step BG leaves out

BG applies Theorem 6.2 to `M` to obtain `Z(J(P)) ⊴ M` *with `P` the full Sylow `p`-subgroup of
`G`*, which presupposes `P ≤ M` — but at that point in the text only `P ∩ M ∈ Syl_p(M)` has been
established, and `P ≤ M` is what the display is used to prove.  The gap is repaired here, and
the repair is short: Theorem 6.2 applied to `M` and its Sylow subgroup `S = P ∩ M` gives
`Z(L(S)) ⊴ M`, hence `M ≤ N_G(Z(L(S)))`, and the maximal choice of `M` upgrades this to
`M = N_G(Z(L(S)))`.  Now `Z(L(S))` is characteristic in `S`, so `N_G(S) ≤ N_G(Z(L(S))) = M` and
therefore `N_P(S) ≤ P ∩ M = S`; a `p`-subgroup that is self-normalizing in `P` is `P`, so
`S = P` after all.  Everything BG writes is then correct as written.
-/

namespace OddOrder.BG.AppD

open OddOrder.GroupTheory OddOrder.Isaacs

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-! ## Choosing the two maximal objects

BG makes two maximal choices: a Sylow `p`-subgroup `Q ≠ P` for which `P ∩ Q` is as large as
possible, and a subgroup `M ⊇ N_G(P ∩ Q)` with `O_p(M) ≠ 1` as large as possible. -/

omit [Fact (Nat.Prime p)] in
/-- Among the Sylow `p`-subgroups `R ≠ P` whose intersection with `P` contains a prescribed one,
there is a `Q` for which `P ⊓ Q` is maximal — and then `P ⊓ Q` is maximal among *all* of
`{P ⊓ R : R ≠ P}`, since any `R` beating it also satisfies the constraint. -/
theorem exists_maximal_sylow_inter (P R₀ : Sylow p G)
    (hR₀ : (R₀ : Subgroup G) ≠ (P : Subgroup G)) :
    ∃ Q : Sylow p G, (Q : Subgroup G) ≠ (P : Subgroup G) ∧
      (P : Subgroup G) ⊓ (R₀ : Subgroup G) ≤ (P : Subgroup G) ⊓ (Q : Subgroup G) ∧
      ∀ R : Sylow p G, (R : Subgroup G) ≠ (P : Subgroup G) →
        (P : Subgroup G) ⊓ (Q : Subgroup G) ≤ (P : Subgroup G) ⊓ (R : Subgroup G) →
        (P : Subgroup G) ⊓ (R : Subgroup G) = (P : Subgroup G) ⊓ (Q : Subgroup G) := by
  classical
  set s : Set (Sylow p G) := {R | (R : Subgroup G) ≠ (P : Subgroup G) ∧
    (P : Subgroup G) ⊓ (R₀ : Subgroup G) ≤ (P : Subgroup G) ⊓ (R : Subgroup G)} with hs_def
  obtain ⟨Q, hQs, hQmax⟩ := Set.Finite.exists_maximalFor
    (fun R : Sylow p G => (P : Subgroup G) ⊓ (R : Subgroup G)) s (Set.toFinite s)
    ⟨R₀, hR₀, le_rfl⟩
  exact ⟨Q, hQs.1, hQs.2, fun R hR hle =>
    le_antisymm (hQmax ⟨hR, hQs.2.trans hle⟩ hle) hle⟩

/-- BG's maximal choice of `M`: a largest subgroup that contains `N_G(D)` and still has a
nontrivial `p`-core.  The family is nonempty because `N_G(D)` itself belongs to it: `D` is a
nontrivial normal `p`-subgroup of its own normalizer. -/
theorem exists_maximal_oPiCore_ne_bot {D : Subgroup G} (hDp : IsPGroup p ↥D) (hD : D ≠ ⊥) :
    ∃ M : Subgroup G, Subgroup.normalizer (D : Set G) ≤ M ∧
      opiCoreInG ({p} : Set ℕ) M ≠ ⊥ ∧
      ∀ H : Subgroup G, Subgroup.normalizer (D : Set G) ≤ H →
        opiCoreInG ({p} : Set ℕ) H ≠ ⊥ → M ≤ H → H = M := by
  classical
  set s : Set (Subgroup G) := {H | Subgroup.normalizer (D : Set G) ≤ H ∧
    opiCoreInG ({p} : Set ℕ) H ≠ ⊥} with hs_def
  have hmem : Subgroup.normalizer (D : Set G) ∈ s := by
    refine ⟨le_rfl, ?_⟩
    have hle : D ≤ opiCoreInG ({p} : Set ℕ) (Subgroup.normalizer (D : Set G)) :=
      le_opiCoreInG_of_normal_of_isPiSubgroup (Subgroup.le_normalizer)
        Subgroup.normal_in_normalizer (isPiSubgroup_singleton_of_isPGroup hDp)
    exact fun hbot => hD (le_bot_iff.mp (hbot ▸ hle))
  haveI : Finite (Subgroup G) := Finite.of_injective (fun H : Subgroup G => (H : Set G))
    (fun _ _ h => SetLike.coe_injective h)
  obtain ⟨M, hMs, hMmax⟩ :=
    Set.Finite.exists_maximalFor (id : Subgroup G → Subgroup G) s (Set.toFinite s) ⟨_, hmem⟩
  exact ⟨M, hMs.1, hMs.2, fun H h1 h2 hle => le_antisymm (hMmax ⟨h1, h2⟩ hle) hle⟩

/-! ## Elementary consequences of the maximal choice of `Q` -/

/-- If `P ⊓ Q ≠ ⊥` for two Sylow `p`-subgroups then `p` divides `|G|`, hence `p ≠ 2` when `|G|`
is odd. -/
theorem prime_ne_two_of_inf_ne_bot (hodd : Odd (Nat.card G)) {P Q : Sylow p G}
    (hne : (P : Subgroup G) ⊓ (Q : Subgroup G) ≠ ⊥) : p ≠ 2 := by
  rintro rfl
  have hp2 : IsPGroup 2 ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) := P.2.to_inf_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp2
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ (by simpa using hk)) hne
    · exact h
  have hdvd : (2 : ℕ) ∣ Nat.card G :=
    dvd_trans (hk ▸ dvd_pow_self 2 hkpos.ne') (Subgroup.card_subgroup_dvd_card _)
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨c, hc⟩ := hdvd
  omega

omit [Finite G] [Fact (Nat.Prime p)] in
/-- Two distinct Sylow `p`-subgroups meet in a proper subgroup of each: `P ⊓ Q < P`. -/
theorem inf_lt_of_ne {P Q : Sylow p G} (hPQ : (P : Subgroup G) ≠ (Q : Subgroup G)) :
    (P : Subgroup G) ⊓ (Q : Subgroup G) < (P : Subgroup G) := by
  refine lt_of_le_of_ne inf_le_left fun heq => hPQ ?_
  have hle : (P : Subgroup G) ≤ (Q : Subgroup G) := heq ▸ inf_le_right
  exact (P.3 Q.2 hle).symm

omit [Finite G] in
/-- The ambient `π`-core of `⊤` is the `π`-core of the whole group. -/
theorem opiCoreInG_top (π : Set ℕ) :
    opiCoreInG π (⊤ : Subgroup G) = Ch03.oPiCore π G := by
  have h := Ch03.oPiCore.map_eq_of_mulEquiv (G := ↥(⊤ : Subgroup G)) (H := G) π Subgroup.topEquiv
  rw [opiCoreInG, ← h]
  rfl

/-! ## BG's configuration

Fix a Sylow `p`-subgroup `P` of `G`, a Sylow `p`-subgroup `Q ≠ P` for which `D = P ∩ Q ≠ 1` is
maximal, and a maximal `M ⊇ N_G(D)` with `O_p(M) ≠ 1`.  The lemmas of this section walk through
BG's proof of Lemma D.1 with those data fixed. -/

section MaximalConfig

variable (hyp : MinimalSimpleCNHypothesis G) {P Q : Sylow p G}
  (hQP : (Q : Subgroup G) ≠ (P : Subgroup G))
  (hne : (P : Subgroup G) ⊓ (Q : Subgroup G) ≠ ⊥)
  (hmax : ∀ R : Sylow p G, (R : Subgroup G) ≠ (P : Subgroup G) →
    (P : Subgroup G) ⊓ (Q : Subgroup G) ≤ (P : Subgroup G) ⊓ (R : Subgroup G) →
    (P : Subgroup G) ⊓ (R : Subgroup G) = (P : Subgroup G) ⊓ (Q : Subgroup G))
  {M : Subgroup G}
  (hM_ge : Subgroup.normalizer (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G) ≤ M)
  (hM_core : opiCoreInG ({p} : Set ℕ) M ≠ ⊥)
  (hM_max : ∀ H : Subgroup G,
    Subgroup.normalizer (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G) ≤ H →
    opiCoreInG ({p} : Set ℕ) H ≠ ⊥ → M ≤ H → H = M)

include hyp hM_core in
/-- `M` is a proper subgroup: `G` is simple and nonsolvable, so `O_p(G) = 1`. -/
theorem lt_top_of_oPiCore_ne_bot : M < ⊤ := by
  refine lt_of_le_of_ne le_top fun hM => ?_
  refine hM_core ?_
  rw [hM, opiCoreInG_top, hyp.oPiCore_eq_bot p]

include hQP hmax hM_ge in
/-- **BG (D.1), first half**: `P ∩ M` is a Sylow `p`-subgroup of `M`.

`N_P(D) ≤ P ∩ M` lies in a Sylow `p`-subgroup `P₁` of `M`, which in turn lies in a Sylow
`p`-subgroup `P₂` of `G`.  Then `P ∩ P₂ ⊇ N_P(D) ⊋ D`, so the maximal choice of `Q` forces
`P₂ = P`; hence `P₁ ≤ P ∩ M`, and `P ∩ M` is Sylow in `M`. -/
theorem exists_sylow_eq_inf_subgroupOf :
    ∃ P₁ : Sylow p ↥M, (P₁ : Subgroup ↥M) = ((P : Subgroup G) ⊓ M).subgroupOf M := by
  classical
  -- `N_P(D)` is strictly bigger than `D` and lies in `P ∩ M`.
  have hNPD_lt : (P : Subgroup G) ⊓ (Q : Subgroup G) <
      (P : Subgroup G) ⊓ Subgroup.normalizer
        (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G) :=
    OddOrder.BG.Ch2.S08.lt_inf_normalizer_of_isPGroup_lt P.2 (inf_lt_of_ne (Ne.symm hQP))
  have hNPD_le : (P : Subgroup G) ⊓ Subgroup.normalizer
      (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G) ≤ (P : Subgroup G) ⊓ M :=
    le_inf inf_le_left (inf_le_right.trans hM_ge)
  -- A Sylow `p`-subgroup `P₁` of `M` above `P ∩ M`.
  have hp1 : IsPGroup p ↥(((P : Subgroup G) ⊓ M).subgroupOf M) :=
    (P.2.to_inf_left (K := M)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : (P : Subgroup G) ⊓ M ≤ M)).symm
  obtain ⟨P₁, hP₁⟩ := hp1.exists_le_sylow
  refine ⟨P₁, le_antisymm ?_ hP₁⟩
  -- Push `P₁` up to a Sylow `p`-subgroup `P₂` of `G`.
  have hP₁G_p : IsPGroup p ↥((P₁ : Subgroup ↥M).map M.subtype) :=
    P₁.2.of_equiv (Subgroup.equivMapOfInjective _ _ M.subtype_injective)
  obtain ⟨P₂, hP₂⟩ := hP₁G_p.exists_le_sylow
  have hPM_le : (P : Subgroup G) ⊓ M ≤ (P₁ : Subgroup ↥M).map M.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : (P : Subgroup G) ⊓ M ≤ M)]
    exact Subgroup.map_mono hP₁
  have hlt : (P : Subgroup G) ⊓ (Q : Subgroup G) < (P : Subgroup G) ⊓ (P₂ : Subgroup G) :=
    hNPD_lt.trans_le (hNPD_le.trans (le_inf inf_le_left (hPM_le.trans hP₂)))
  have hP₂P : (P₂ : Subgroup G) = (P : Subgroup G) := by
    by_contra hcon
    exact hlt.ne' (hmax P₂ hcon hlt.le)
  -- Hence `P₁` lands inside `P ∩ M`.
  have hP₁G_le : (P₁ : Subgroup ↥M).map M.subtype ≤ (P : Subgroup G) ⊓ M :=
    le_inf (hP₂.trans (le_of_eq hP₂P)) (Subgroup.map_subtype_le _)
  intro x hx
  exact hP₁G_le (Subgroup.mem_map_of_mem _ hx)

include hQP hM_ge in
/-- `Q ∩ M` is not contained in `P`: it contains `N_Q(D)`, which is strictly bigger than `D`. -/
theorem inf_right_not_le : ¬ ((Q : Subgroup G) ⊓ M ≤ (P : Subgroup G)) := by
  intro hle
  have hDltQ : (P : Subgroup G) ⊓ (Q : Subgroup G) < (Q : Subgroup G) := by
    have h := inf_lt_of_ne hQP
    rwa [inf_comm] at h
  have hNQD_lt : (P : Subgroup G) ⊓ (Q : Subgroup G) <
      (Q : Subgroup G) ⊓ Subgroup.normalizer
        (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G) :=
    OddOrder.BG.Ch2.S08.lt_inf_normalizer_of_isPGroup_lt Q.2 hDltQ
  have hNQD_le : (Q : Subgroup G) ⊓ Subgroup.normalizer
      (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G) ≤ (Q : Subgroup G) ⊓ M :=
    le_inf inf_le_left (inf_le_right.trans hM_ge)
  exact absurd (hNQD_lt.trans_le (hNQD_le.trans (le_inf hle inf_le_left))) (lt_irrefl _)

include hyp hQP hmax hM_ge hM_core in
/-- **BG**: `M` is a 3-step group with respect to `p` (Gorenstein Ch. 12 §1, Corollary 1.6).

`M` is proper, hence solvable, and it inherits the CN condition.  Its `p`-core is nontrivial by
the choice of `M`, and it is *not* Sylow in `M`: were it Sylow, every Sylow `p`-subgroup of `M`
would coincide with it, forcing `Q ∩ M ≤ P ∩ M ≤ P` and hence `N_Q(D) ≤ D`. -/
theorem isThreeStepGroup_of_maximal : IsThreeStepGroup ↥M p := by
  classical
  haveI : IsSolvable ↥M :=
    hyp.minimalSimpleOdd.solvable_of_lt_top M (lt_top_of_oPiCore_ne_bot hyp hM_core)
  have hcore : Ch03.oPiCore ({p} : Set ℕ) ↥M ≠ ⊥ := fun h =>
    hM_core (by rw [opiCoreInG, h, Subgroup.map_bot])
  rcases oPiCore_isSylow_or_isThreeStepGroup (G := ↥M) (hyp.cn.to_subgroup M) hcore with
    ⟨S, hS⟩ | h3
  · exfalso
    -- If `O_p(M)` is Sylow then every Sylow `p`-subgroup of `M` equals it.
    have hall : ∀ T : Sylow p ↥M, (T : Subgroup ↥M) = Ch03.oPiCore ({p} : Set ℕ) ↥M := by
      intro T
      have hle : (S : Subgroup ↥M) ≤ (T : Subgroup ↥M) := by
        rw [hS]; exact oPiCore_le_sylow T
      rw [← hS]; exact S.3 T.2 hle
    obtain ⟨P₁, hP₁⟩ := exists_sylow_eq_inf_subgroupOf hQP hmax hM_ge
    have hQMp : IsPGroup p ↥(((Q : Subgroup G) ⊓ M).subgroupOf M) :=
      (Q.2.to_inf_left (K := M)).of_equiv
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : (Q : Subgroup G) ⊓ M ≤ M)).symm
    obtain ⟨T₁, hT₁⟩ := hQMp.exists_le_sylow
    have hsub : ((Q : Subgroup G) ⊓ M).subgroupOf M ≤ ((P : Subgroup G) ⊓ M).subgroupOf M := by
      rw [← hP₁, hall P₁, ← hall T₁]; exact hT₁
    refine inf_right_not_le hQP hM_ge (fun x hx => ?_)
    have hx' : (⟨x, hx.2⟩ : ↥M) ∈ ((Q : Subgroup G) ⊓ M).subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr hx
    exact (Subgroup.mem_subgroupOf.mp (hsub hx')).1
  · exact h3

include hyp hQP hne hmax hM_ge hM_core hM_max in
/-- **The step BG omits**: `P ≤ M`, and therefore `M = N_G(Z(L(P)))`.

Theorem 6.2 — in the repository's Theorem B.4 form — applied to the solvable odd-order group `M`
and its Sylow `p`-subgroup `S = P ∩ M` gives `Z(L(S))·O_{p'}(M) ⊴ M`, and `O_{p'}(M) = 1`
because `M` is a 3-step group; so `M ≤ N_G(Z(L(S)))`.  That normalizer contains `N_G(D)` too and
has nontrivial `p`-core, so the maximal choice of `M` upgrades this to `M = N_G(Z(L(S)))`.  Now
`Z(L(S))` is characteristic in `S`, so `N_G(S) ≤ N_G(Z(L(S))) = M`, whence `N_P(S) ≤ P ∩ M = S`;
a self-normalizing subgroup of the `p`-group `P` is `P` itself, so `S = P`.

BG writes the conclusion (`Z(J(P)) ⊴ M` for the full Sylow `p`-subgroup `P`) directly. -/
theorem sylow_le_and_eq_normalizer :
    (P : Subgroup G) ≤ M ∧
      M = Subgroup.normalizer (AppB.zCenterLOdd (P : Subgroup G) : Set G) := by
  classical
  obtain ⟨P₁, hP₁⟩ := exists_sylow_eq_inf_subgroupOf hQP hmax hM_ge
  have h3 := isThreeStepGroup_of_maximal hyp hQP hmax hM_ge hM_core
  haveI hsolv : IsSolvable ↥M :=
    hyp.minimalSimpleOdd.solvable_of_lt_top M (lt_top_of_oPiCore_ne_bot hyp hM_core)
  have hoddM : Odd (Nat.card ↥M) :=
    hyp.minimalSimpleOdd.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hp_odd : p ≠ 2 := prime_ne_two_of_inf_ne_bot hyp.minimalSimpleOdd.odd hne
  have hD_le_PM : (P : Subgroup G) ⊓ (Q : Subgroup G) ≤ (P : Subgroup G) ⊓ M :=
    le_inf inf_le_left (Subgroup.le_normalizer.trans hM_ge)
  have hPM_ne : (P : Subgroup G) ⊓ M ≠ ⊥ := fun hbot => hne (le_bot_iff.mp (hbot ▸ hD_le_PM))
  -- Theorem 6.2 inside `M`, using `O_{p'}(M) = 1`.
  have hZnormal : (AppB.zCenterLOdd (P₁ : Subgroup ↥M)).Normal := by
    have h62 := AppB.zCenter_lOdd_sup_oPiCore_normal (G := ↥M) hp_odd hsolv hoddM P₁
    rwa [h3.oPiCore_pPrime_eq_bot, sup_bot_eq] at h62
  -- Transport to the ambient group.
  have hinj : Function.Injective (M.subtype.comp (P₁ : Subgroup ↥M).subtype) := fun _ _ h =>
    Subtype.ext (M.subtype_injective h)
  have hmapP₁ : (P₁ : Subgroup ↥M).map M.subtype = (P : Subgroup G) ⊓ M := by
    rw [hP₁]; exact Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have hZmap : (AppB.zCenterLOdd (P₁ : Subgroup ↥M)).map M.subtype =
      AppB.zCenterLOdd ((P : Subgroup G) ⊓ M) := by
    rw [AppB.map_zCenterLOdd_of_injOn (G := ↥M) (G' := G) M.subtype
      (H := (P₁ : Subgroup ↥M)) hinj, hmapP₁]
  have hZ_le : AppB.zCenterLOdd ((P : Subgroup G) ⊓ M) ≤ M :=
    ((AppB.zCenterLOdd_le_lOddIn _).trans (AppB.lOddIn_le_self _)).trans inf_le_right
  have hZ_subgroupOf : (AppB.zCenterLOdd ((P : Subgroup G) ⊓ M)).subgroupOf M =
      AppB.zCenterLOdd (P₁ : Subgroup ↥M) := by
    rw [← hZmap, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hM_le_NZ : M ≤
      Subgroup.normalizer ((AppB.zCenterLOdd ((P : Subgroup G) ⊓ M) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZ_le).mp (hZ_subgroupOf ▸ hZnormal)
  have hZ_ne : AppB.zCenterLOdd ((P : Subgroup G) ⊓ M) ≠ ⊥ :=
    Ch2.S08.zCenterLOdd_ne_bot_of_isPGroup (P.2.to_inf_left (K := M)) hPM_ne
  have hcoreNZ : opiCoreInG ({p} : Set ℕ)
      (Subgroup.normalizer ((AppB.zCenterLOdd ((P : Subgroup G) ⊓ M) : Subgroup G) : Set G))
      ≠ ⊥ := by
    have hle : AppB.zCenterLOdd ((P : Subgroup G) ⊓ M) ≤ opiCoreInG ({p} : Set ℕ)
        (Subgroup.normalizer ((AppB.zCenterLOdd ((P : Subgroup G) ⊓ M) : Subgroup G) : Set G)) :=
      le_opiCoreInG_of_normal_of_isPiSubgroup Subgroup.le_normalizer
        Subgroup.normal_in_normalizer
        (isPiSubgroup_singleton_of_isPGroup
          ((P.2.to_inf_left (K := M)).to_le
            ((AppB.zCenterLOdd_le_lOddIn _).trans (AppB.lOddIn_le_self _))))
    exact fun hbot => hZ_ne (le_bot_iff.mp (hbot ▸ hle))
  -- Maximality of `M` pins `M = N_G(Z(L(P ∩ M)))`.
  have hMeq : Subgroup.normalizer
      ((AppB.zCenterLOdd ((P : Subgroup G) ⊓ M) : Subgroup G) : Set G) = M :=
    hM_max _ (hM_ge.trans hM_le_NZ) hcoreNZ hM_le_NZ
  -- `Z(L(P ∩ M))` is characteristic in `P ∩ M`, so `P ∩ M` is self-normalizing in `P`.
  have hPM_eq : (P : Subgroup G) = (P : Subgroup G) ⊓ M := by
    refine sylow_coe_eq_of_normalizer_inf_le (Q := P) inf_le_left (fun g hg => ?_)
    have hgM : g ∈ M := hMeq ▸ Ch2.S08.normalizer_le_normalizer_zCenterLOdd _ hg.1
    exact ⟨hg.2, hgM⟩
  refine ⟨le_of_eq_of_le hPM_eq inf_le_right, ?_⟩
  rw [← hMeq, ← hPM_eq]

include hyp hQP hne hmax hM_ge hM_core in
/-- **BG display (D.2)**: `P ∩ Q = O_p(M)`.

`≤` comes from the 3-step Sylow-intersection identity `inf_sylow_eq_oPiCore`, applied to the
Sylow `p`-subgroups `P ∩ M` and a `T ⊇ Q ∩ M` of `M`, which are distinct because `Q ∩ M ⊄ P`.

For `≥`, note that `N_Q(P ∩ Q)` lies in `M` and hence normalizes `O_p(M)`, so
`O_p(M)·N_Q(P ∩ Q)` is a `p`-subgroup of `G`.  A Sylow `p`-subgroup `R` containing it is not `P`
(otherwise `N_Q(P ∩ Q) ≤ P ∩ Q`), so the maximal choice of `Q` gives `P ∩ R = P ∩ Q`; and
`O_p(M)` lies in both `P` and `R`. -/
theorem inf_eq_oPiCore_of_maximal :
    (P : Subgroup G) ⊓ (Q : Subgroup G) = opiCoreInG ({p} : Set ℕ) M := by
  classical
  obtain ⟨P₁, hP₁⟩ := exists_sylow_eq_inf_subgroupOf hQP hmax hM_ge
  have h3 := isThreeStepGroup_of_maximal hyp hQP hmax hM_ge hM_core
  -- A Sylow `p`-subgroup of `M` above `Q ∩ M`, necessarily different from `P₁`.
  have hQMp : IsPGroup p ↥(((Q : Subgroup G) ⊓ M).subgroupOf M) :=
    (Q.2.to_inf_left (K := M)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : (Q : Subgroup G) ⊓ M ≤ M)).symm
  obtain ⟨T₁, hT₁⟩ := hQMp.exists_le_sylow
  have hQM_le : (Q : Subgroup G) ⊓ M ≤ (T₁ : Subgroup ↥M).map M.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : (Q : Subgroup G) ⊓ M ≤ M)]
    exact Subgroup.map_mono hT₁
  have hP₁ne : (P₁ : Subgroup ↥M) ≠ (T₁ : Subgroup ↥M) := by
    intro heq
    refine inf_right_not_le hQP hM_ge (fun x hx => ?_)
    have hx' : (⟨x, hx.2⟩ : ↥M) ∈ ((Q : Subgroup G) ⊓ M).subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr hx
    have hmem := hT₁ hx'
    rw [← heq, hP₁] at hmem
    exact (Subgroup.mem_subgroupOf.mp hmem).1
  -- The 3-step identity, transported to the ambient group.
  have hmapinf : ((P : Subgroup G) ⊓ M) ⊓ ((T₁ : Subgroup ↥M).map M.subtype)
      = opiCoreInG ({p} : Set ℕ) M := by
    rw [opiCoreInG, ← h3.inf_sylow_eq_oPiCore hP₁ne,
      Subgroup.map_inf _ _ _ M.subtype_injective, hP₁,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : (P : Subgroup G) ⊓ M ≤ M)]
  have hD_le_M : (P : Subgroup G) ⊓ (Q : Subgroup G) ≤ M := Subgroup.le_normalizer.trans hM_ge
  have hDle : (P : Subgroup G) ⊓ (Q : Subgroup G) ≤ opiCoreInG ({p} : Set ℕ) M := by
    rw [← hmapinf]
    exact le_inf (le_inf inf_le_left hD_le_M)
      ((le_inf inf_le_right hD_le_M).trans hQM_le)
  refine le_antisymm hDle ?_
  -- `O_p(M) ≤ P`, and `N_Q(P ∩ Q)` normalizes `O_p(M)`.
  have hOle_P : opiCoreInG ({p} : Set ℕ) M ≤ (P : Subgroup G) := by
    rw [← hmapinf]; exact inf_le_left.trans inf_le_left
  have hDltQ : (P : Subgroup G) ⊓ (Q : Subgroup G) < (Q : Subgroup G) := by
    have h := inf_lt_of_ne hQP
    rwa [inf_comm] at h
  have hNQD_lt : (P : Subgroup G) ⊓ (Q : Subgroup G) <
      (Q : Subgroup G) ⊓ Subgroup.normalizer
        (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G) :=
    OddOrder.BG.Ch2.S08.lt_inf_normalizer_of_isPGroup_lt Q.2 hDltQ
  have hNQD_norm : (Q : Subgroup G) ⊓ Subgroup.normalizer
      (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((opiCoreInG ({p} : Set ℕ) M : Subgroup G) : Set G) :=
    (inf_le_right.trans hM_ge).trans (le_normalizer_opiCoreInG _ M)
  have hWp : IsPGroup p ↥(opiCoreInG ({p} : Set ℕ) M ⊔ ((Q : Subgroup G) ⊓
      Subgroup.normalizer (((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G))) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_opiCoreInG_singleton M) Q.2.to_inf_left hNQD_norm
  obtain ⟨R, hR⟩ := hWp.exists_le_sylow
  have hRneP : (R : Subgroup G) ≠ (P : Subgroup G) := by
    intro hRP
    refine absurd (hNQD_lt.trans_le (le_inf ?_ inf_le_left)) (lt_irrefl _)
    exact (le_sup_right.trans hR).trans (le_of_eq hRP)
  have hDleR : (P : Subgroup G) ⊓ (Q : Subgroup G) ≤ (P : Subgroup G) ⊓ (R : Subgroup G) :=
    le_inf inf_le_left (hDle.trans (le_sup_left.trans hR))
  rw [← hmax R hRneP hDleR]
  exact le_inf hOle_P (le_sup_left.trans hR)

end MaximalConfig

/-! ## Packaging: everything in terms of `N_G(Z(L(P)))`

The subgroup `M` produced by the maximal choice turns out to be `N_G(Z(L(P)))`, which depends
only on `P`.  Restating the configuration lemmas in those terms removes `M` and `Q` from the
interface, and that is what makes BG's endgame work: *every* maximal intersection with `P` is
`O_p(N_G(Z(L(P))))`, one and the same subgroup. -/

omit [Finite G] [Fact (Nat.Prime p)] in
/-- `P` normalizes `Z(L(P))`, a characteristic subgroup of `P`. -/
theorem sylow_le_normalizer_zCenterLOdd (P : Sylow p G) :
    (P : Subgroup G) ≤ Subgroup.normalizer (AppB.zCenterLOdd (P : Subgroup G) : Set G) :=
  Subgroup.le_normalizer.trans (Ch2.S08.normalizer_le_normalizer_zCenterLOdd _)

/-- The configuration lemmas with `M` eliminated: for a maximal nontrivial intersection
`P ∩ Q`, the subgroup `N = N_G(Z(L(P)))` is a 3-step group and `P ∩ Q = O_p(N)`. -/
theorem isThreeStepGroup_and_inf_eq_oPiCore (hyp : MinimalSimpleCNHypothesis G) {P Q : Sylow p G}
    (hQP : (Q : Subgroup G) ≠ (P : Subgroup G))
    (hne : (P : Subgroup G) ⊓ (Q : Subgroup G) ≠ ⊥)
    (hmax : ∀ R : Sylow p G, (R : Subgroup G) ≠ (P : Subgroup G) →
      (P : Subgroup G) ⊓ (Q : Subgroup G) ≤ (P : Subgroup G) ⊓ (R : Subgroup G) →
      (P : Subgroup G) ⊓ (R : Subgroup G) = (P : Subgroup G) ⊓ (Q : Subgroup G)) :
    IsThreeStepGroup ↥(Subgroup.normalizer (AppB.zCenterLOdd (P : Subgroup G) : Set G)) p ∧
      (P : Subgroup G) ⊓ (Q : Subgroup G) = opiCoreInG ({p} : Set ℕ)
        (Subgroup.normalizer (AppB.zCenterLOdd (P : Subgroup G) : Set G)) := by
  obtain ⟨M, hM_ge, hM_core, hM_max⟩ :=
    exists_maximal_oPiCore_ne_bot (P.2.to_inf_left (K := (Q : Subgroup G))) hne
  obtain ⟨-, hMeq⟩ := sylow_le_and_eq_normalizer hyp hQP hne hmax hM_ge hM_core hM_max
  refine ⟨hMeq ▸ isThreeStepGroup_of_maximal hyp hQP hmax hM_ge hM_core, ?_⟩
  rw [← hMeq]
  exact inf_eq_oPiCore_of_maximal hyp hQP hne hmax hM_ge hM_core

/-- **The form Lemma D.1 uses**: *every* Sylow `p`-subgroup `R ≠ P` meets `P` inside
`O_p(N_G(Z(L(P))))`.

Extend `P ∩ R` to a maximal intersection `P ∩ Q`; the previous theorem identifies `P ∩ Q` with
`O_p(N_G(Z(L(P))))`, and `N_G(Z(L(P)))` does not depend on the choice of `Q`. -/
theorem inf_le_oPiCore_normalizer_zCenterLOdd (hyp : MinimalSimpleCNHypothesis G)
    {P R : Sylow p G} (hR : (R : Subgroup G) ≠ (P : Subgroup G)) :
    (P : Subgroup G) ⊓ (R : Subgroup G) ≤ opiCoreInG ({p} : Set ℕ)
      (Subgroup.normalizer (AppB.zCenterLOdd (P : Subgroup G) : Set G)) := by
  by_cases hRbot : (P : Subgroup G) ⊓ (R : Subgroup G) = ⊥
  · rw [hRbot]; exact bot_le
  obtain ⟨Q, hQP, hle, hmax⟩ := exists_maximal_sylow_inter P R hR
  have hne : (P : Subgroup G) ⊓ (Q : Subgroup G) ≠ ⊥ := fun h =>
    hRbot (le_bot_iff.mp (h ▸ hle))
  exact hle.trans (isThreeStepGroup_and_inf_eq_oPiCore hyp hQP hne hmax).2.le

/-- If `P` meets some other Sylow `p`-subgroup nontrivially, `N_G(Z(L(P)))` is a 3-step group. -/
theorem isThreeStepGroup_normalizer_zCenterLOdd (hyp : MinimalSimpleCNHypothesis G)
    {P R : Sylow p G} (hR : (R : Subgroup G) ≠ (P : Subgroup G))
    (hRne : (P : Subgroup G) ⊓ (R : Subgroup G) ≠ ⊥) :
    IsThreeStepGroup ↥(Subgroup.normalizer (AppB.zCenterLOdd (P : Subgroup G) : Set G)) p := by
  obtain ⟨Q, hQP, hle, hmax⟩ := exists_maximal_sylow_inter P R hR
  have hne : (P : Subgroup G) ⊓ (Q : Subgroup G) ≠ ⊥ := fun h =>
    hRne (le_bot_iff.mp (h ▸ hle))
  exact (isThreeStepGroup_and_inf_eq_oPiCore hyp hQP hne hmax).1

end OddOrder.BG.AppD
