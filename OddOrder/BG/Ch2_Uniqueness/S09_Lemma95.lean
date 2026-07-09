/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/


import OddOrder.BG.Ch2_Uniqueness.Setup
import OddOrder.BG.Ch1_Preliminary.S05_NarrowPGroups
import OddOrder.BG.Ch2_Uniqueness.S07_Transitivity
import OddOrder.BG.Ch2_Uniqueness.S08_FittingOfMaximal
import OddOrder.GroupTheory.MaximalSubgroup
import OddOrder.GroupTheory.AInvariantPiSubgroups
import OddOrder.GroupTheory.PRank
import OddOrder.GroupTheory.OmegaSubgroup
import OddOrder.GroupTheory.ElementaryAbelianFamily
import OddOrder.BG.Ch2_Uniqueness.S09_Theorem91
import OddOrder.BG.Ch2_Uniqueness.S09_Corollaries

/-!
# BG §9: Lemma 9.5 (SCN₃ subgroups are uniquely maximal)

**スコープ**: Bender–Glauberman §9, Lemma 9.5 (mmd L2559-2625)。`A ∈ SCN₃(p) ⇒ A ∈ 𝒰`
(`r(F(M))` への矛盾)。§9 チェーンの pivotal step。`S09_Theorem91` / `S09_Corollaries` を import。
-/

namespace OddOrder.BG.Ch2.S09

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-- The Theorem 7.6 → Theorem 7.4 propagation step used in BG Lemma 9.5.

If `A ∈ SCN₃(p)`, `A ≤ R`, and `R` is a proper `p`-subgroup, then for every `q ≠ p`
`O_{p'}(C_G(R))` acts transitively on `ℋ_G^*(R;q)`. This is the formal version of the
line "By Theorems 7.6 and 7.4" in the normalizer part of Lemma 9.5. -/
private theorem conjTransitiveOn_hInvariantStar_of_scn3Global_intermediate [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A R : Subgroup G}
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R) (hRlt : R < ⊤)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) :
    S07.ConjTransitiveOn (opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G)))
      (hInvariantStar ⊤ R {q}) := by
  classical
  have hA0 := hA
  obtain ⟨P, hAP, hAscn3⟩ := hA0
  have hAab : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hAp : IsPGroup p A := isPGroup_of_mem_scn3Global hA
  have hAscn2 : IsSCN_n p 2 (A.subgroupOf (P : Subgroup G)) :=
    IsSCN_n.mono (by norm_num) hAscn3
  have hHyp : S07.Hypothesis71 A := S07.hypothesis71_of_scn2 hG hAab hAp P hAP hAscn2
  have hπ : S07.primesOf A = ({p} : Set ℕ) := primesOf_eq_singleton_of_mem_scn3Global hA
  have hqA : q ∈ (S07.primesOf A)ᶜ := by
    rw [hπ]
    simpa [Set.mem_singleton_iff] using hqp
  have hRpi : Subgroup.IsPiSubgroup (S07.primesOf A) R := by
    rw [hπ]
    exact isPiSubgroup_singleton_of_isPGroup hRp
  have hAsub : Subgroup.IsSubnormal (A.subgroupOf R) :=
    subgroupOf_isSubnormal_of_isPGroup hRp
  have htransA : S07.ConjTransitiveOn (S07.kSubgroup A) (hInvariantStar ⊤ A {q}) := by
    have hT := S07.thompsonTransitivity hG (prime_dvd_card_of_mem_scn3Global hA) hA hqp
    simpa [S07.kSubgroup, hπ] using hT
  have hprop := S07.transitivity_propagates hG hHyp hqA R hRlt hRpi hAR hAsub htransA
  simpa [hπ] using hprop.2.1

/-- A conjugation-transitivity bookkeeping step for BG Lemma 9.5.

If `x` normalizes `R`, transitivity gives `k ∈ K` with `Q^k = Q^x`. Once both `K` and
`N_G(Q)` lie in `M`, this forces `x ∈ M`. -/
private theorem mem_of_mem_normalizer_of_conjTransitiveOn
    {K M R Q : Subgroup G} {q : ℕ} [Fact q.Prime] {x : G}
    (hxR : x ∈ Subgroup.normalizer (R : Set G))
    (hQ : Q ∈ hInvariantStar ⊤ R {q})
    (htrans : S07.ConjTransitiveOn K (hInvariantStar ⊤ R {q}))
    (hKleM : K ≤ M) (hNQleM : Subgroup.normalizer (Q : Set G) ≤ M) :
    x ∈ M := by
  classical
  have hxR_eq : MulAut.conj x • R = R :=
    conj_smul_eq_self_of_mem_normalizer hxR
  have hxQ : MulAut.conj x • Q ∈ hInvariantStar ⊤ R {q} :=
    conj_smul_mem_hInvariantStar_top_of_normalizer hQ hxR_eq
  obtain ⟨k, hkK, hkQ⟩ := htrans Q hQ (MulAut.conj x • Q) hxQ
  have hknorm : k⁻¹ * x ∈ Subgroup.normalizer (Q : Set G) := by
    apply mem_normalizer_of_conj_smul_eq_self
    calc MulAut.conj (k⁻¹ * x) • Q
        = MulAut.conj k⁻¹ • MulAut.conj x • Q := by
            rw [smul_smul, ← map_mul]
      _ = MulAut.conj k⁻¹ • MulAut.conj k • Q := by rw [← hkQ]
      _ = Q := by
            rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hkM : k ∈ M := hKleM hkK
  have hknormM : k⁻¹ * x ∈ M := hNQleM hknorm
  have hprod : k * (k⁻¹ * x) ∈ M := M.mul_mem hkM hknormM
  simpa [mul_assoc] using hprod

/-- BG Lemma 9.5's normalizer step after the `Q` and `(9.8)` witnesses have been supplied.

This packages the final use of Theorems 7.6 and 7.4: the transitivity bridge puts a
normalizer element of `R` in the fixed maximal subgroup `M`, provided `Q ∈ ℋ_G^*(R;q)` and
`N_G(Q) ≤ M` are already known. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate [Finite G]
    (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R Q : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p)
    (hQ : Q ∈ hInvariantStar ⊤ R {q})
    (hNQleM : Subgroup.normalizer (Q : Set G) ≤ M) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  have htrans :
      S07.ConjTransitiveOn
        (opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G)))
        (hInvariantStar ⊤ R {q}) :=
    conjTransitiveOn_hInvariantStar_of_scn3Global_intermediate hG hA hRp hAR hRlt hqp
  have hKleM :
      opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G)) ≤ M := by
    exact (opiCoreInG_le ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G))).trans
      ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAR)).trans hM.2)
  intro x hxR
  exact mem_of_mem_normalizer_of_conjTransitiveOn hxR hQ htrans hKleM hNQleM

/-- BG Lemma 9.5's L2573-L2589 normalizer step, with the `Q` package as input.

The low-rank and high-rank cases both produce a `Q ∈ ℋ_G^*(R;q)` with `N_G(Q) ≤ M`;
this helper consumes that uniform package and applies the Theorems 7.6/7.4 transitivity
bridge. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_exists_hInvariantStar
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p)
    (hQpack :
      ∃ Q : Subgroup G,
        Q ∈ hInvariantStar ⊤ R {q} ∧
          opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  obtain ⟨Q, hQ, _hcoreQ, hNQleM⟩ := hQpack
  exact normalizer_le_maximal_of_scn3Global_intermediate
    hG hM hA hRp hAR hRlt hqp hQ hNQleM

/-- The `Q`-choice in BG Lemma 9.5.

If `R ≤ M`, then `R` normalizes `O_q(M)`, so `O_q(M)` lies in `ℋ_G(R;q)` and can be
extended to a maximal member of `ℋ_G^*(R;q)`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_of_le [Finite G]
    {q : ℕ} [Fact q.Prime] {M R : Subgroup G} (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧ opiCoreInG ({q} : Set ℕ) M ≤ Q := by
  classical
  have hcore : opiCoreInG ({q} : Set ℕ) M ∈ hInvariant ⊤ R {q} := by
    refine ⟨le_top, ?_, isPiSubgroup_opiCoreInG ({q} : Set ℕ) M⟩
    exact hRM.trans (le_normalizer_opiCoreInG ({q} : Set ℕ) M)
  exact exists_le_hInvariantStar hcore

/-- A member of `ℋ_G^*(R;q)` containing a Sylow `q`-subgroup is that Sylow subgroup. -/
private theorem hInvariantStar_eq_sylow_of_sylow_le [Finite G]
    {q : ℕ} [Fact q.Prime] (P : Sylow q G) {R Q : Subgroup G}
    (hQ : Q ∈ hInvariantStar ⊤ R {q}) (hPQ : (P : Subgroup G) ≤ Q) :
    Q = (P : Subgroup G) := by
  have hQp : IsPGroup q Q :=
    isPGroup_of_isPiSubgroup_singleton (hInvariantStar_isPiSubgroup hQ)
  exact P.is_maximal' hQp hPQ

/-- If a subgroup is the ambient image of a Sylow `q`-subgroup of `M` and its ambient
normalizer is contained in `M`, then it is a Sylow `q`-subgroup of `G`.

This is the Sylow-normalizer bookkeeping in BG (9.7). -/
private theorem exists_sylow_eq_of_sylow_subgroupOf_and_normalizer_le [Finite G]
    {q : ℕ} [Fact q.Prime] {M O : Subgroup G} (PM : Sylow q ↥M)
    (hPMO : (PM : Subgroup ↥M).map M.subtype = O)
    (hNOM : Subgroup.normalizer (O : Set G) ≤ M) :
    ∃ P : Sylow q G, (P : Subgroup G) = O := by
  classical
  have hOp : IsPGroup q O := by
    rw [← hPMO]
    exact PM.isPGroup'.map M.subtype
  obtain ⟨S, hOS⟩ := hOp.exists_le_sylow
  have hSO : (S : Subgroup G) = O := by
    by_contra hS_ne_O
    have hOltS : O < (S : Subgroup G) :=
      lt_of_le_of_ne hOS (fun h => hS_ne_O h.symm)
    have hOltSN : O < (S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G) :=
      S08.lt_inf_normalizer_of_isPGroup_lt S.isPGroup' hOltS
    have hSN_le_M : (S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G) ≤ M :=
      inf_le_right.trans hNOM
    let K : Subgroup ↥M :=
      ((S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G)).subgroupOf M
    have hKp : IsPGroup q K := (S.isPGroup'.to_inf_left).comap_subtype
    have hPM_le_K : (PM : Subgroup ↥M) ≤ K := by
      intro x hx
      have hxO : (x : G) ∈ O := by
        rw [← hPMO]
        exact ⟨x, hx, rfl⟩
      change (x : G) ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G)
      exact (le_inf hOS Subgroup.le_normalizer) hxO
    have hK_eq_PM : K = (PM : Subgroup ↥M) := PM.is_maximal' hKp hPM_le_K
    have hSN_eq_O : (S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G) = O := by
      calc
        (S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G)
            = K.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hSN_le_M).symm
        _ = (PM : Subgroup ↥M).map M.subtype := by rw [hK_eq_PM]
        _ = O := hPMO
    exact (ne_of_lt hOltSN) hSN_eq_O.symm
  exact ⟨S, hSO⟩

/-- The `(9.7)` side of BG Lemma 9.5's `(9.8)` step, abstracted from the source of the
Sylow fact.

If the core `O_q(M)` is a Sylow `q`-subgroup of `G` and its normalizer lies in `M`, then
the `Q` chosen above has `N_G(Q) ≤ M`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_sylow
    [Finite G] {q : ℕ} [Fact q.Prime] {M R : Subgroup G} (P : Sylow q G)
    (hPcore : (P : Subgroup G) = opiCoreInG ({q} : Set ℕ) M) (hRM : R ≤ M)
    (hNPM : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  obtain ⟨Q, hQ, hcoreQ⟩ := exists_hInvariantStar_containing_opiCoreInG_of_le (q := q) hRM
  have hPQ : (P : Subgroup G) ≤ Q := (le_of_eq hPcore).trans hcoreQ
  have hQeq : Q = (P : Subgroup G) := hInvariantStar_eq_sylow_of_sylow_le P hQ hPQ
  refine ⟨Q, hQ, hcoreQ, ?_⟩
  rw [hQeq]
  exact hNPM

/-- Low-rank `(9.7)` package once Theorem 4.20(c) has identified `O_q(M)` as the
ambient image of a Sylow `q`-subgroup of `M`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M)
    (hOqne : opiCoreInG ({q} : Set ℕ) M ≠ ⊥) (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  have hNcoreM : Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) M : Set G) ≤ M :=
    normalizer_opiCoreInG_singleton_le_maximal_of_ne_bot hG hM hOqne
  obtain ⟨P, hPcore⟩ :=
    exists_sylow_eq_of_sylow_subgroupOf_and_normalizer_le PM hPMcore hNcoreM
  have hNPM : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M := by
    rw [hPcore]
    exact hNcoreM
  exact exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_sylow
    P hPcore hRM hNPM

/-- If a local Sylow `q`-subgroup maps onto `O_q(M)` and `q ∈ π(M)`, then
`O_q(M)` is nontrivial. -/
private theorem opiCoreInG_singleton_ne_bot_of_local_sylow_eq_of_mem_primeFactors
    [Finite G] {q : ℕ} [Fact q.Prime] {M : Subgroup G} (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) :
    opiCoreInG ({q} : Set ℕ) M ≠ ⊥ := by
  classical
  have hq_dvd_M : q ∣ Nat.card ↥M := (Nat.mem_primeFactors.mp hqM).2.1
  have hPMne : (PM : Subgroup ↥M) ≠ ⊥ :=
    OddOrder.Isaacs.Ch07.Sylow.ne_bot_of_dvd_card hq_dvd_M PM
  intro hOqbot
  have hPMmap_bot : (PM : Subgroup ↥M).map M.subtype = ⊥ := by
    rw [hPMcore, hOqbot]
  have hPMbot : (PM : Subgroup ↥M) = ⊥ := by
    apply (Subgroup.map_subtype_inj (H := M)).mp
    simpa [Subgroup.map_bot] using hPMmap_bot
  exact hPMne hPMbot

/-- Low-rank `(9.7)` package when Theorem 4.20(c) has supplied only the local Sylow
equality; nontriviality follows from `q ∈ π(M)`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow_eq
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  exact exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow
    hG hM PM hPMcore
    (opiCoreInG_singleton_ne_bot_of_local_sylow_eq_of_mem_primeFactors PM hPMcore hqM)
    hRM

/-- Convert the local `O_q(M)` notation used by the §4 endpoint into the ambient
`opiCoreInG` notation used in §9. -/
private theorem local_sylow_map_eq_opiCoreInG_of_eq_opCore
    [Finite G] {q : ℕ} [Fact q.Prime] {M : Subgroup G} (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M) = Ch01.opCore q ↥M) :
    (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M := by
  rw [hPMcore, opiCoreInG, OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := ↥M) q]

/-- Low-rank `(9.7)` package with the natural §4-shaped input
`(P_M : Subgroup M) = O_q(M)`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_opCore
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M) = Ch01.opCore q ↥M)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  exact exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow_eq
    hG hM PM (local_sylow_map_eq_opiCoreInG_of_eq_opCore PM hPMcore) hqM hRM

/-- Low-rank `(9.7)` package when §4 has supplied a normal local Sylow subgroup. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_normal_local_sylow
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (PM : Sylow q ↥M)
    (hPMnorm : (PM : Subgroup ↥M).Normal)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  exact exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_opCore
    hG hM PM (Ch01.Sylow.eq_opCore_of_normal PM hPMnorm) hqM hRM

/-- A rank-three `q`-subgroup is nontrivial. -/
private theorem ne_bot_of_isPGroup_of_three_le_rank [Finite G]
    {q : ℕ} [Fact q.Prime] {B : Subgroup G} (hBq : IsPGroup q B)
    (hBrank : 3 ≤ rank ↥B) :
    B ≠ ⊥ := by
  have h3pRankB : 3 ≤ pRank ↥B q :=
    three_le_pRank_of_isPGroup_of_three_le_rank hBq hBrank
  have hq_dvd_B : q ∣ Nat.card B :=
    (Nat.mem_primeFactors.mp
      (mem_primeFactors_card_of_pos_pRank (H := ↥B) (p := q) (by omega))).2.1
  intro hBbot
  rw [hBbot, Subgroup.card_bot] at hq_dvd_B
  exact (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp hq_dvd_B)

/-- If a uniquely maximal subgroup `B` lies in both a fixed maximal subgroup `M` and a
nontrivial `q`-subgroup `Q`, then the normalizer of `Q` lies in `M`.

This is the uniqueness bookkeeping behind BG Lemma 9.5's high-rank `(9.8)` step. -/
private theorem normalizer_le_maximal_of_isUniquelyMaximal_le [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M B Q : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hBU : IsUniquelyMaximal B)
    (hBM : B ≤ M) (hBQ : B ≤ Q) (hQne : Q ≠ ⊥)
    (hQpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) Q) :
    Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  have hQlt : Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hQtop
    have hQp : IsPGroup q Q := isPGroup_of_isPiSubgroup_singleton hQpi
    have hGp : IsPGroup q G :=
      (hQtop ▸ hQp : IsPGroup q ↥(⊤ : Subgroup G)).of_surjective
        (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom
        Subgroup.topEquiv.surjective
    haveI : Group.IsNilpotent G := hGp.isNilpotent
    exact hG.notSolvable inferInstance
  obtain ⟨N, hNco, hQN⟩ := (eq_top_or_exists_le_coatom Q).resolve_left hQlt.ne
  have hN_eq_M : N = M :=
    hBU.eq_of_isCoatom_of_le hNco (hBQ.trans hQN) (mem_maximalSubgroups.mp hM) hBM
  have hQM : Q ≤ M := hQN.trans (le_of_eq hN_eq_M)
  obtain ⟨L, hL, hNQleL⟩ :=
    S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal hG hM hQne hQM
  have hB_le_L : B ≤ L := hBQ.trans (Subgroup.le_normalizer.trans hNQleL)
  have hL_eq_M : L = M :=
    hBU.eq_of_isCoatom_of_le (mem_maximalSubgroups.mp hL) hB_le_L
      (mem_maximalSubgroups.mp hM) hBM
  exact hNQleL.trans (le_of_eq hL_eq_M)

/-- High-rank `(9.8)` bookkeeping once a rank-three subgroup inside `O_q(M)` has been
chosen.

Lemma 9.4 makes the rank-three subgroup uniquely maximal; uniqueness then forces the
normalizer of the chosen `Q ∈ ℋ_G^*(R;q)` into the fixed maximal subgroup `M`. -/
private theorem normalizer_hInvariantStar_le_maximal_of_rank_three_opiCoreInG_witness
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R Q : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q)
    (hQ : Q ∈ hInvariantStar ⊤ R {q}) (hOqQ : opiCoreInG ({q} : Set ℕ) M ≤ Q)
    (hwit :
      ∃ B : Subgroup G,
        IsMulCommutative B ∧ IsPGroup q B ∧ 3 ≤ rank ↥B ∧
          B ≤ opiCoreInG ({q} : Set ℕ) M) :
    Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  obtain ⟨B, hBab, hBq, hBrank, hBcore⟩ := hwit
  have hBU : IsUniquelyMaximal B :=
    (abelian_rank_three_isUniquelyMaximal_of_fitting hG hM h3Fq) B hBab hBq hBrank
  have hBM : B ≤ M := hBcore.trans (opiCoreInG_le ({q} : Set ℕ) M)
  have hBQ : B ≤ Q := hBcore.trans hOqQ
  have hBne : B ≠ ⊥ := ne_bot_of_isPGroup_of_three_le_rank hBq hBrank
  have hQne : Q ≠ ⊥ := by
    intro hQbot
    exact hBne (le_bot_iff.mp (hBQ.trans (le_of_eq hQbot)))
  exact normalizer_le_maximal_of_isUniquelyMaximal_le hG hM hBU hBM hBQ hQne
    (hInvariantStar_isPiSubgroup hQ)

/-- A high `q`-rank Fitting subgroup supplies a rank-three abelian `q`-subgroup inside
`O_q(M)`.

The point is that the elementary abelian witness in `F(M)` lies in `O_q(F(M))` by
nilpotence, and `O_q(F(M)) ≤ O_q(M)`. -/
private theorem exists_rank_three_abelian_le_opiCoreInG_of_three_le_pRank_fittingInG
    [Finite G] {q : ℕ} [Fact q.Prime] {M : Subgroup G}
    (h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q) :
    ∃ B : Subgroup G,
      IsMulCommutative B ∧ IsPGroup q B ∧ 3 ≤ rank ↥B ∧
        B ≤ opiCoreInG ({q} : Set ℕ) M := by
  classical
  obtain ⟨B, hBmax, hBrank⟩ :=
    exists_isMaxElemAbelianIn_rank_three_of_three_le_pRank
      (H := S08.fittingInG M) h3Fq
  have hBea : B.IsElementaryAbelian q :=
    S08.isMaxElemAbelianIn_isElementaryAbelian hBmax
  have hBab : IsMulCommutative B := IsMulCommutative.of_comm hBea.comm
  have hBq : IsPGroup q B := hBea.isPGroup
  have hBF : B ≤ S08.fittingInG M := S08.isMaxElemAbelianIn_le hBmax
  have hBOF : B ≤ opiCoreInG ({q} : Set ℕ) (S08.fittingInG M) :=
    S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
      (S08.fittingInG_isNilpotent M) hBF hBq
  have hBOM : B ≤ opiCoreInG ({q} : Set ℕ) M :=
    hBOF.trans (S08.opiCoreInG_fittingInG_le_opiCoreInG ({q} : Set ℕ) M)
  exact ⟨B, hBab, hBq, hBrank, hBOM⟩

/-- The high-rank side of BG Lemma 9.5's `(9.8)` package.

If `r_q(F(M)) ≥ 3`, the `Q ∈ ℋ_G^*(R;q)` chosen to contain `O_q(M)` has
`N_G(Q) ≤ M`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_high_pRank
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q)
    (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  obtain ⟨Q, hQ, hcoreQ⟩ := exists_hInvariantStar_containing_opiCoreInG_of_le (q := q) hRM
  refine ⟨Q, hQ, hcoreQ, ?_⟩
  exact normalizer_hInvariantStar_le_maximal_of_rank_three_opiCoreInG_witness
    hG hM h3Fq hQ hcoreQ
    (exists_rank_three_abelian_le_opiCoreInG_of_three_le_pRank_fittingInG h3Fq)

/-- Low-rank version of the BG Lemma 9.5 normalizer step, after Thm 4.20(c) has supplied
`O_q(M)` as the ambient image of a Sylow `q`-subgroup of `M`. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_local_sylow
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p) (hRM : R ≤ M) (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M)
    (hOqne : opiCoreInG ({q} : Set ℕ) M ≠ ⊥) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  exact normalizer_le_maximal_of_scn3Global_intermediate_of_exists_hInvariantStar
    hG hM hA hRp hAR hRlt hqp
    (exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow
      hG hM.1 PM hPMcore hOqne hRM)

/-- Low-rank normalizer step when Theorem 4.20(c) has supplied the local Sylow equality;
nontriviality follows from `q ∈ π(M)`. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_local_sylow_eq
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p) (hRM : R ≤ M) (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  exact normalizer_le_maximal_of_scn3Global_intermediate_of_exists_hInvariantStar
    hG hM hA hRp hAR hRlt hqp
    (exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow_eq
      hG hM.1 PM hPMcore hqM hRM)

/-- Low-rank normalizer step with the natural §4-shaped input
`(P_M : Subgroup M) = O_q(M)`. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_local_opCore
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p) (hRM : R ≤ M) (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M) = Ch01.opCore q ↥M)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  exact normalizer_le_maximal_of_scn3Global_intermediate_of_exists_hInvariantStar
    hG hM hA hRp hAR hRlt hqp
    (exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_opCore
      hG hM.1 PM hPMcore hqM hRM)

/-- Low-rank normalizer step when §4 has supplied a normal local Sylow subgroup. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_normal_local_sylow
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p) (hRM : R ≤ M) (PM : Sylow q ↥M)
    (hPMnorm : (PM : Subgroup ↥M).Normal)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  exact normalizer_le_maximal_of_scn3Global_intermediate_of_exists_hInvariantStar
    hG hM hA hRp hAR hRlt hqp
    (exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_normal_local_sylow
      hG hM.1 PM hPMnorm hqM hRM)

/-- Low-rank normalizer step when §4 supplies a positive-length characteristic
Sylow series for the local maximal subgroup. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_characteristicSylowSeries
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hRM : R ≤ M)
    (S : OddOrder.BG.Ch1.S04.CharacteristicSylowSeries ↥M) (hpos : 0 < S.length)
    (hterminal_mem :
      ∀ i : Fin S.length,
        i.succ = Fin.last S.length → (S.step i).q ∈ (Nat.card ↥M).primeFactors)
    (hterminal_ne :
      ∀ i : Fin S.length, i.succ = Fin.last S.length → (S.step i).q ≠ p) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  obtain ⟨i, hi, PM, hPMnorm⟩ :=
    OddOrder.BG.Ch1.S04.CharacteristicSylowSeries.exists_normal_sylow_of_length_pos S hpos
  haveI : Fact (S.step i).q.Prime := (S.step i).q_prime
  exact normalizer_le_maximal_of_scn3Global_intermediate_of_normal_local_sylow
    hG hM hA hRp hAR hRlt (hterminal_ne i hi) hRM PM hPMnorm (hterminal_mem i hi)

/-- In the low-rank Lemma 9.5 branch, the terminal normal local Sylow label
cannot be the ambient `SCN₃` prime. -/
private theorem normal_sylow_label_ne_of_scn3Global_of_pRank_fittingInG_le_two
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {A M : Subgroup G}
    (hA : A ∈ S07.scn3Global p G) (hAM : A ≤ M)
    (hFp : pRank ↥(S08.fittingInG M) p ≤ 2)
    (PM : Sylow q ↥M) (hPMnorm : (PM : Subgroup ↥M).Normal) :
    q ≠ p := by
  classical
  intro hqp
  subst q
  have hAp : IsPGroup p A := isPGroup_of_mem_scn3Global hA
  have hArank : 3 ≤ rank ↥A := three_le_rank_of_mem_scn3Global hA
  have h3A : 3 ≤ pRank ↥A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank hAp hArank
  let AM : Subgroup ↥M := A.subgroupOf M
  have hAMp : IsPGroup p AM :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAM).symm
  obtain ⟨P, hAMP⟩ := hAMp.exists_le_sylow
  haveI : Unique (Sylow p ↥M) := Sylow.unique_of_normal PM hPMnorm
  have hAM_PM : AM ≤ (PM : Subgroup ↥M) := by
    have hP_eq : P = PM := Subsingleton.elim P PM
    rwa [← hP_eq]
  have hA_PM_map : A ≤ (PM : Subgroup ↥M).map M.subtype := by
    calc
      A = AM.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hAM).symm
      _ ≤ (PM : Subgroup ↥M).map M.subtype := Subgroup.map_mono hAM_PM
  have hPMcore : (PM : Subgroup ↥M) = Ch01.opCore p ↥M :=
    Ch01.Sylow.eq_opCore_of_normal PM hPMnorm
  have hPMfit : (PM : Subgroup ↥M).map M.subtype ≤ S08.fittingInG M := by
    rw [hPMcore, ← OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := ↥M) p]
    change opiCoreInG ({p} : Set ℕ) M ≤ S08.fittingInG M
    exact S08.opiCoreInG_singleton_le_fittingInG M
  have hAF : A ≤ S08.fittingInG M := hA_PM_map.trans hPMfit
  have h3F : 3 ≤ pRank ↥(S08.fittingInG M) p :=
    h3A.trans
      (pRank_le_of_injective (f := Subgroup.inclusion hAF)
        (Subgroup.inclusion_injective hAF))
  omega

/-- **BG Theorem 4.20(c) package bridge for §9.** A maximal subgroup `M` of the minimal simple
odd group `G` with `r(F(M)) ≤ 2` carries a characteristic Sylow series package: `M` is solvable
(`hG.solvable_of_mem_maximalSubgroups`), of odd order (`|M| ∣ |G|`), nontrivial, and
`rank F(↥M) = rank (fittingInG M) ≤ 2` (the two Fitting subgroups are isomorphic via
`M.subtype`).  This is how the low-rank branch of the Lemma 9.5 normalizer step obtains its
`(9.7)` Sylow data internally — replacing the (unfulfillable, since `r(F(M))` may be `≥ 3`)
external package hypothesis. -/
private theorem exists_characteristicSylowSeriesPackage_of_maximal_of_rank_fittingInG_le_two
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) [Nontrivial ↥M]
    (hrank : rank ↥(S08.fittingInG M) ≤ 2) :
    Nonempty (OddOrder.BG.Ch1.S04.CharacteristicSylowSeriesPackage ↥M) := by
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hodd : Odd (Nat.card ↥M) := by
    rcases Nat.even_or_odd (Nat.card ↥M) with he | ho
    · exfalso
      have h2 : (2 : ℕ) ∣ Nat.card G := he.two_dvd.trans (Subgroup.card_subgroup_dvd_card M)
      have := hG.odd; rw [Nat.odd_iff] at this; omega
    · exact ho
  have hrankF : rank ↥(Ch01.fitting ↥M) ≤ 2 := by
    refine le_trans (OddOrder.GroupTheory.rank_le_of_injective
      (f := (Subgroup.equivMapOfInjective (Ch01.fitting ↥M) M.subtype
        M.subtype_injective).toMonoidHom) ?_) hrank
    exact (Subgroup.equivMapOfInjective (Ch01.fitting ↥M) M.subtype M.subtype_injective).injective
  exact ⟨(OddOrder.BG.Ch1.S05.exists_characteristicSylowSeriesPackage_of_rank_fitting_le_two
    hodd hrankF).some⟩

/-- Low-rank normalizer step when §4 supplies a positive-length characteristic
Sylow series and Lemma 9.5 has already established `r_p(F(M)) ≤ 2`. -/
private theorem normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_lowRank
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hRM : R ≤ M)
    (hFp : pRank ↥(S08.fittingInG M) p ≤ 2)
    (S : OddOrder.BG.Ch1.S04.CharacteristicSylowSeries ↥M) (hpos : 0 < S.length)
    (hterminal_mem :
      ∀ i : Fin S.length,
        i.succ = Fin.last S.length → (S.step i).q ∈ (Nat.card ↥M).primeFactors) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  have hAab : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hA_le_C : A ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (isMulCommutative_iff.mp hAab ⟨y, hy⟩ ⟨x, hx⟩)
  have hAM : A ≤ M := hA_le_C.trans hM.2
  refine normalizer_le_maximal_of_scn3Global_intermediate_of_characteristicSylowSeries
    hG hM hA hRp hAR hRlt hRM S hpos hterminal_mem ?_
  intro i hi
  obtain ⟨PM, hPMnorm⟩ :=
    OddOrder.BG.Ch1.S04.CharacteristicSylowSeries.exists_normal_sylow_of_terminal_step S i hi
  haveI : Fact (S.step i).q.Prime := (S.step i).q_prime
  exact normal_sylow_label_ne_of_scn3Global_of_pRank_fittingInG_le_two
    hA hAM hFp PM hPMnorm

/-- High-rank version of the BG Lemma 9.5 normalizer step, using Lemma 9.4 through the
rank-three witness inside `O_q(M)`. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_high_pRank
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p) (hRM : R ≤ M)
    (h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  exact normalizer_le_maximal_of_scn3Global_intermediate_of_exists_hInvariantStar
    hG hM hA hRp hAR hRlt hqp
    (exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_high_pRank
      hG hM.1 h3Fq hRM)

/-- If the overall rank is at least three but the fixed `p`-rank is at most two,
then some other prime has rank at least three. -/
private theorem exists_pRank_ge_three_ne_of_rank_ge_three_of_pRank_le_two
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hrank : 3 ≤ rank H) (hp : pRank H p ≤ 2) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ 3 ≤ pRank H q := by
  obtain ⟨q, hq, h3q⟩ :=
    exists_pRank_ge_of_pos_le_rank (G := H) (n := 3) (by norm_num) hrank
  refine ⟨q, hq, ?_, h3q⟩
  intro hqp
  subst q
  omega

/-- BG Lemma 9.5 rank-case normalizer adapter.

The low-rank branch consumes the §4 characteristic Sylow series package, while the
high-rank branch chooses a prime `q ≠ p` with `r_q(F(M)) ≥ 3` and applies Lemma 9.4. -/
private theorem normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_rankCases
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hRM : R ≤ M)
    (hFp : pRank ↥(S08.fittingInG M) p ≤ 2) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  by_cases hrank : rank ↥(S08.fittingInG M) ≤ 2
  · -- low rank: build the §4.20(c) characteristic Sylow series of `M` internally via L2
    have hAM : A ≤ M := hAR.trans hRM
    haveI : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr fun hM0 =>
      ne_bot_of_mem_scn3Global hA (le_bot_iff.mp (hM0 ▸ hAM))
    obtain ⟨pkg⟩ :=
      exists_characteristicSylowSeriesPackage_of_maximal_of_rank_fittingInG_le_two hG hM.1 hrank
    exact normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_lowRank
      hG hM hA hRp hAR hRlt hRM hFp pkg.series pkg.length_pos pkg.terminal_mem
  · have h3rank : 3 ≤ rank ↥(S08.fittingInG M) := by omega
    obtain ⟨q, hq, hqp, h3Fq⟩ :=
      exists_pRank_ge_three_ne_of_rank_ge_three_of_pRank_le_two
        (H := ↥(S08.fittingInG M)) (p := p) h3rank hFp
    haveI : Fact q.Prime := ⟨hq⟩
    exact normalizer_le_maximal_of_scn3Global_intermediate_of_high_pRank
      hG hM hA hRp hAR hRlt hqp hRM h3Fq

/-- BG Lemma 9.5 normalizer step specialized to `R = A`.

After the rank-case normalizer adapter has been supplied with the §4 characteristic
Sylow series package, the first application gives `N_G(A) ≤ M`. -/
private theorem normalizer_scn3_self_le_maximal_of_rankCases
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G)
    (hFp : pRank ↥(S08.fittingInG M) p ≤ 2) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  classical
  have hAab : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hA_le_C : A ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (isMulCommutative_iff.mp hAab ⟨y, hy⟩ ⟨x, hx⟩)
  have hAM : A ≤ M := hA_le_C.trans hM.2
  have hAlt : A < ⊤ :=
    lt_of_le_of_lt hA_le_C (centralizer_lt_top_of_mem_scn3Global hG hA)
  exact normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_rankCases
    hG hM hA (isPGroup_of_mem_scn3Global hA) le_rfl hAlt hAM hFp

/-- BG Lemma 9.5 normalizer step specialized to a `p`-subgroup of `N_G(A)`.

The `R = A` instance first puts every chosen `P ≤ N_G(A)` inside `M`; the rank-case
adapter can then be applied with `R = P` to obtain `N_G(P) ≤ M`. -/
private theorem normalizer_scn3_sylowNormalizer_le_maximal_of_rankCases
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M P : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hPp : IsPGroup p P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hFp : pRank ↥(S08.fittingInG M) p ≤ 2) :
    P ≤ M ∧ Subgroup.normalizer (P : Set G) ≤ M := by
  classical
  have hNAleM : Subgroup.normalizer (A : Set G) ≤ M :=
    normalizer_scn3_self_le_maximal_of_rankCases hG hM hA hFp
  have hPM : P ≤ M := hPnormA.trans hNAleM
  have hMlt : M < ⊤ := (mem_maximalSubgroups.mp hM.1).lt_top
  have hPlt : P < ⊤ := lt_of_le_of_lt hPM hMlt
  exact ⟨hPM,
    normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_rankCases
      hG hM hA hPp hAP hPlt hPM hFp⟩

/-- If an `SCN₃(p)` subgroup is a counterexample to uniqueness, then every maximal
subgroup has `pRank F(M) ≤ 2`.

This is the first reduction in BG Lemma 9.5: otherwise Lemma 9.4 would put the
rank-three abelian `p`-subgroup `A` itself in `𝒰`. -/
private theorem pRank_fittingInG_le_two_of_not_scn3_isUniquelyMaximal [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hA : A ∈ S07.scn3Global p G)
    (hAnot : ¬ IsUniquelyMaximal A) :
    pRank ↥(S08.fittingInG M) p ≤ 2 := by
  classical
  by_contra hnot
  have h3F : 3 ≤ pRank ↥(S08.fittingInG M) p := by omega
  have hAab : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hAp : IsPGroup p A := isPGroup_of_mem_scn3Global hA
  have hArank : 3 ≤ rank ↥A := three_le_rank_of_mem_scn3Global hA
  exact hAnot
    ((abelian_rank_three_isUniquelyMaximal_of_fitting hG hM h3F) A hAab hAp hArank)

/-- The opening choice in BG Lemma 9.5, bundled with the rank cut (9.6).

For a counterexample `A ∈ SCN₃(p)` with `A ∉ 𝒰`, choose `M ∈ 𝓜(C_G(A))`; then Lemma 9.4
implies `r_p(F(M)) ≤ 2`. -/
private theorem exists_maximal_centralizer_and_pRank_fittingInG_le_two_of_not_scn3
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A) :
    ∃ M : Subgroup G,
      M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) ∧
        pRank ↥(S08.fittingInG M) p ≤ 2 := by
  classical
  obtain ⟨M, hMcont⟩ := exists_maximalSubgroupsContaining_centralizer_of_mem_scn3Global hG hA
  have hM : M ∈ maximalSubgroups G := hMcont.1
  exact ⟨M, hMcont, pRank_fittingInG_le_two_of_not_scn3_isUniquelyMaximal hG hM hA hAnot⟩

/-- Counterexample version of the `R = A` normalizer step in BG Lemma 9.5.

The rank cut `(9.6)` is derived internally from `A ∉ 𝒰`. -/
private theorem normalizer_scn3_self_le_maximal_of_not_scn3
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  have hFp : pRank ↥(S08.fittingInG M) p ≤ 2 :=
    pRank_fittingInG_le_two_of_not_scn3_isUniquelyMaximal hG hM.1 hA hAnot
  exact normalizer_scn3_self_le_maximal_of_rankCases hG hM hA hFp

/-- Counterexample version of the `R = P` normalizer step in BG Lemma 9.5.

Once `P` is a `p`-subgroup between `A` and `N_G(A)`, the rank cut `(9.6)` and the
`R = A` instance put `P` inside `M`, and the rank-case adapter gives `N_G(P) ≤ M`. -/
private theorem normalizer_scn3_pSubgroup_le_maximal_of_not_scn3
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M P : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (hPp : IsPGroup p P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G)) :
    P ≤ M ∧ Subgroup.normalizer (P : Set G) ≤ M := by
  have hFp : pRank ↥(S08.fittingInG M) p ≤ 2 :=
    pRank_fittingInG_le_two_of_not_scn3_isUniquelyMaximal hG hM.1 hA hAnot
  exact normalizer_scn3_sylowNormalizer_le_maximal_of_rankCases
    hG hM hA hPp hAP hPnormA hFp

/-- Choose an ambient `p`-subgroup between a global `SCN₃(p)` subgroup and its normalizer.

This is the subgroup-level form of the BG choice of a Sylow `p`-subgroup of `N_G(A)`. -/
private theorem exists_pSubgroup_between_scn3_and_normalizer [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    ∃ P : Subgroup G,
      IsPGroup p P ∧ A ≤ P ∧ P ≤ Subgroup.normalizer (A : Set G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  let AN : Subgroup ↥N := A.subgroupOf N
  have hANp : IsPGroup p AN :=
    (isPGroup_of_mem_scn3Global hA).of_equiv (Subgroup.subgroupOfEquivOfLe hAN).symm
  obtain ⟨PN, hANPN⟩ := hANp.exists_le_sylow
  let P : Subgroup G := (PN : Subgroup ↥N).map N.subtype
  have hPp : IsPGroup p P := PN.isPGroup'.map N.subtype
  have hAP : A ≤ P := by
    calc
      A = AN.map N.subtype := (Subgroup.map_subgroupOf_eq_of_le hAN).symm
      _ ≤ (PN : Subgroup ↥N).map N.subtype := Subgroup.map_mono hANPN
  have hPN : P ≤ N := by
    dsimp [P]
    exact Subgroup.map_subtype_le (PN : Subgroup ↥N)
  exact ⟨P, hPp, hAP, hPN⟩

/-- BG Lemma 9.5 opening normalizer package for a chosen maximal subgroup over `C_G(A)`.

Given the §4 characteristic Sylow series package for `M`, a counterexample `A ∉ 𝒰`
supplies a `p`-subgroup `P` with `A ≤ P ≤ N_G(A)`, `P ≤ M`, and `N_G(P) ≤ M`. -/
private theorem exists_pSubgroup_normalizer_package_of_not_scn3
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A) :
    ∃ P : Subgroup G,
      IsPGroup p P ∧ A ≤ P ∧ P ≤ Subgroup.normalizer (A : Set G) ∧
        P ≤ M ∧ Subgroup.normalizer (P : Set G) ≤ M := by
  obtain ⟨P, hPp, hAP, hPnormA⟩ := exists_pSubgroup_between_scn3_and_normalizer hA
  have hpack : P ≤ M ∧ Subgroup.normalizer (P : Set G) ≤ M :=
    normalizer_scn3_pSubgroup_le_maximal_of_not_scn3
      hG hM hA hAnot hPp hAP hPnormA
  exact ⟨P, hPp, hAP, hPnormA, hpack.1, hpack.2⟩

/-- BG Lemma 9.5's Proposition 1.16 extraction step.

If `P0` does not centralize `D`, and a noncyclic abelian subgroup `A` normalizes `D`
coprimely, then among the cocyclic centralizers generating `D` there is one not centralized
by `P0`. This is the formal version of the line "Take `B ⊆ Ω₁(A)` such that
`Ω₁(A)/B` is cyclic and `P₀` does not centralize `C_D(B)`." -/
private theorem exists_cocyclic_not_le_centralizer_inf_centralizer_of_not_le_centralizer
    [Finite G] {A D P0 : Subgroup G} [IsMulCommutative ↥A]
    (hAD : A ≤ Subgroup.normalizer D)
    (hCop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥D))
    (hAnc : ¬ IsCyclic ↥A)
    (hP0D : ¬ P0 ≤ Subgroup.centralizer (D : Set G)) :
    ∃ B : Subgroup G,
      B ≤ A ∧ (∃ a ∈ A, B ⊔ Subgroup.zpowers a = A) ∧
        ¬ P0 ≤ Subgroup.centralizer
          ((D ⊓ Subgroup.centralizer (B : Set G)) : Set G) := by
  classical
  by_contra hnone
  have hAll :
      ∀ B : Subgroup G,
        B ≤ A → (∃ a ∈ A, B ⊔ Subgroup.zpowers a = A) →
          P0 ≤ Subgroup.centralizer
            ((D ⊓ Subgroup.centralizer (B : Set G)) : Set G) := by
    intro B hBA hcyc
    by_contra hnot
    exact hnone ⟨B, hBA, hcyc, hnot⟩
  have hDinv : Ch03.IsAInvariant (S07.conjAction A) D :=
    S07.isAInvariant_conjAction_iff.mpr hAD
  have htop :=
    OddOrder.BG.Ch1.S01.cocyclicFixedByClosure_eq_top_of_not_isCyclic
      hDinv.restrict hCop hAnc
  exact hP0D (by
    intro x hxP0
    rw [Subgroup.mem_centralizer_iff]
    intro d hdD
    let CxD : Subgroup ↥D :=
      (D ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf D
    have hclosure_le :
        OddOrder.BG.Ch1.S01.cocyclicFixedByClosure hDinv.restrict ≤ CxD := by
      rw [OddOrder.BG.Ch1.S01.cocyclicFixedByClosure, Subgroup.closure_le]
      rintro z ⟨Yb, ⟨a, hcycYb⟩, hfix⟩
      change (z : G) ∈ D ⊓ Subgroup.centralizer ({x} : Set G)
      set Y : Subgroup G := Yb.map A.subtype with hYdef
      have hYleA : Y ≤ A := by
        rw [hYdef]
        exact Subgroup.map_subtype_le Yb
      have hYcyc : ∃ a' ∈ A, Y ⊔ Subgroup.zpowers a' = A := by
        refine ⟨(a : G), a.2, ?_⟩
        have hzp : Subgroup.zpowers (a : G) = (Subgroup.zpowers a).map A.subtype :=
          (MonoidHom.map_zpowers A.subtype a).symm
        rw [hYdef, hzp, ← Subgroup.map_sup, hcycYb, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      have hzY : (z : G) ∈ D ⊓ Subgroup.centralizer (Y : Set G) := by
        refine ⟨z.2, ?_⟩
        change (z : G) ∈ Subgroup.centralizer (Y : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hyY
        rw [hYdef, Subgroup.coe_map, Set.mem_image] at hyY
        obtain ⟨yb, hyb, rfl⟩ := hyY
        have hval := congrArg (fun w : ↥D => (w : G)) (hfix yb hyb)
        change ((hDinv.restrict yb) z : G) = (z : G) at hval
        rw [Ch03.IsAInvariant.restrict_apply_val] at hval
        simp only [S07.conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype,
          MulAut.conj_apply] at hval
        exact mul_inv_eq_iff_eq_mul.mp hval
      refine ⟨z.2, ?_⟩
      change (z : G) ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      have hx_cent := (hAll Y hYleA hYcyc) hxP0
      exact (Subgroup.mem_centralizer_iff.mp hx_cent (z : G) hzY).symm
    have hdCx : (⟨d, hdD⟩ : ↥D) ∈ CxD := by
      apply hclosure_le
      rw [htop]
      exact Subgroup.mem_top _
    have hdc : d ∈ Subgroup.centralizer ({x} : Set G) := by
      simpa [CxD, Subgroup.mem_subgroupOf] using hdCx
    exact (Subgroup.mem_centralizer_iff.mp hdc x (Set.mem_singleton x)).symm)

/-- A cocyclic subgroup `Y` (`Y ⊔ ⟨b⟩ = B`) of an elementary abelian `p`-group `B`
of rank at least three is noncyclic. -/
private theorem not_isCyclic_of_cocyclic_elementary_rank_three [Finite G] {p : ℕ}
    (hp2 : 2 ≤ p) {B Y : Subgroup G}
    (hB_ea : B.IsElementaryAbelian p) (hlog : 3 ≤ Nat.log p (Nat.card ↥B))
    (hYB : Y ≤ B) {b : G} (hb : b ∈ B) (hsup : Y ⊔ Subgroup.zpowers b = B) :
    ¬ IsCyclic ↥Y := by
  classical
  haveI : IsMulCommutative ↥B := IsMulCommutative.of_comm hB_ea.1
  set Y' : Subgroup ↥B := Y.subgroupOf B with hY'
  set K : Subgroup ↥B := (Subgroup.zpowers b).subgroupOf B with hK
  haveI : Y'.Normal := Subgroup.normal_of_isMulCommutative _
  have hzple : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hb
  have hsup' : Y' ⊔ K = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_sup, hY', hK, Subgroup.map_subgroupOf_eq_of_le hYB,
      Subgroup.map_subgroupOf_eq_of_le hzple, hsup, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hKle : Nat.card ↥K ≤ p := by
    rw [hK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzple).toEquiv, Nat.card_zpowers]
    refine Nat.le_of_dvd (by omega : 0 < p) (orderOf_dvd_of_pow_eq_one ?_)
    have hbp := congrArg Subtype.val (hB_ea.2 (⟨b, hb⟩ : ↥B))
    simpa using hbp
  have hKmap : K.map (QuotientGroup.mk' Y') = ⊤ := by
    have h1 : (Y' ⊔ K).map (QuotientGroup.mk' Y') = ⊤ := by
      rw [hsup', Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Y')]
    rwa [Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff Y').mpr (le_of_eq (QuotientGroup.ker_mk' Y').symm),
      bot_sup_eq] at h1
  have hquot_le : Nat.card (↥B ⧸ Y') ≤ Nat.card ↥K :=
    Nat.card_le_card_of_surjective ((QuotientGroup.mk' Y').comp K.subtype) (by
      intro x
      obtain ⟨k, hk, hkx⟩ := hKmap ▸ Subgroup.mem_top x
      exact ⟨⟨k, hk⟩, hkx⟩)
  have hcardB : Nat.card ↥B ≤ Nat.card ↥K * Nat.card ↥Y := by
    have hY'card : Nat.card ↥Y' = Nat.card ↥Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYB).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Y', hY'card]
    exact Nat.mul_le_mul_right _ hquot_le
  intro hcyc
  have hY_ea : Y.IsElementaryAbelian p := by
    refine ⟨fun x y => Subtype.ext ?_, fun x => Subtype.ext ?_⟩
    · change (x : G) * (y : G) = (y : G) * (x : G)
      exact congrArg (Subtype.val : ↥B → G)
        (hB_ea.1 ⟨(x : G), hYB x.2⟩ ⟨(y : G), hYB y.2⟩)
    · change (x : G) ^ p = 1
      exact congrArg (Subtype.val : ↥B → G)
        (hB_ea.2 (⟨(x : G), hYB x.2⟩ : ↥B))
  have hYle : Nat.card ↥Y ≤ p := by
    have hdvd : Monoid.exponent ↥Y ∣ p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      exact hY_ea.2
    rw [← hcyc.exponent_eq_card]
    exact Nat.le_of_dvd (by omega : 0 < p) hdvd
  have hp3 : p ^ 3 ≤ Nat.card ↥B :=
    (Nat.le_log_iff_pow_le (by omega : 1 < p) Nat.card_pos.ne').mp hlog
  have h1 : Nat.card ↥B ≤ p ^ 2 := by
    rw [pow_two]
    exact le_trans hcardB (Nat.mul_le_mul hKle hYle)
  have h2 : p ^ 2 < p ^ 3 :=
    Nat.pow_lt_pow_right (by omega : 1 < p) (by norm_num)
  omega

/-- If `A` has `pRank ≥ 3`, then its abelian `Ω₁(A)` has logarithmic size at least three. -/
private theorem three_le_log_card_omega1OfAbelian_of_three_le_pRank [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3A : 3 ≤ pRank A p) :
    3 ≤ Nat.log p
      (Nat.card ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set)) := by
  have hp3_dvd : p ^ 3 ∣
      Nat.card ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) :=
    OddOrder.GroupTheory.pow_dvd_card_omega1OfAbelian_of_pos_le_pRank
      (G := G) (H := A) (p := p) (hH := hAcomm_set) (n := 3) (by norm_num) h3A
  have hp3_le : p ^ 3 ≤
      Nat.card ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) :=
    Nat.le_of_dvd Nat.card_pos hp3_dvd
  exact (Nat.le_log_iff_pow_le (Fact.out : p.Prime).one_lt Nat.card_pos.ne').mpr hp3_le

/-- `Ω₁(A)` is noncyclic when `A` has `pRank ≥ 3`. -/
private theorem not_isCyclic_omega1OfAbelian_of_three_le_pRank [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3A : 3 ≤ pRank A p) :
    ¬ IsCyclic ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) := by
  exact not_isCyclic_of_isElementaryAbelian_of_two_le_log_card
    (OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
      (G := G) (H := A) (p := p) (hH := hAcomm_set))
    (by
      have hlog := three_le_log_card_omega1OfAbelian_of_three_le_pRank
        (G := G) (p := p) hAcomm_set h3A
      omega)

/-- A cocyclic subgroup of `Ω₁(A)` is noncyclic when `pRank A ≥ 3`. -/
private theorem not_isCyclic_of_cocyclic_omega1OfAbelian_of_three_le_pRank [Finite G]
    {p : ℕ} [Fact p.Prime] {A B : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3A : 3 ≤ pRank A p)
    (hBΩ : B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set)
    {a : G} (ha : a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set)
    (hsup : B ⊔ Subgroup.zpowers a =
      OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) :
    ¬ IsCyclic ↥B := by
  exact not_isCyclic_of_cocyclic_elementary_rank_three
    (G := G) (p := p) (hp2 := (Fact.out : p.Prime).two_le)
    (B := OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) (Y := B)
    (OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
      (G := G) (H := A) (p := p) (hH := hAcomm_set))
    (three_le_log_card_omega1OfAbelian_of_three_le_pRank
      (G := G) (p := p) hAcomm_set h3A)
    hBΩ ha hsup

/-- BG Lemma 9.5's Prop 1.16 extraction specialized to `Ω₁(A)` under `pRank A ≥ 3`.

The output packages the cocyclic subgroup `B ≤ Ω₁(A)` with the extra facts needed for the
next step of the Lemma 9.5 contradiction: `B ≤ A`, `B` is noncyclic, and `P0` still does
not centralize `D ∩ C_G(B)`. -/
private theorem exists_noncyclic_cocyclic_omega1OfAbelian_not_le_centralizer_inf
    [Finite G] {p : ℕ} [Fact p.Prime] {A D P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3A : 3 ≤ pRank A p)
    (hΩD : OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ≤ Subgroup.normalizer D)
    (hCop : Nat.Coprime
      (Nat.card ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set)) (Nat.card ↥D))
    (hP0D : ¬ P0 ≤ Subgroup.centralizer (D : Set G)) :
    ∃ B : Subgroup G,
      B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ∧
      B ≤ A ∧ ¬ IsCyclic ↥B ∧
      (∃ a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set,
        B ⊔ Subgroup.zpowers a = OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) ∧
      ¬ P0 ≤ Subgroup.centralizer
        ((D ⊓ Subgroup.centralizer (B : Set G)) : Set G) := by
  classical
  let ΩA : Subgroup G := OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set
  have hΩea : ΩA.IsElementaryAbelian p := by
    simpa [ΩA] using
      (OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
        (G := G) (H := A) (p := p) (hH := hAcomm_set))
  haveI : IsMulCommutative ↥ΩA := IsMulCommutative.of_comm hΩea.1
  have hΩAnc : ¬ IsCyclic ↥ΩA := by
    simpa [ΩA] using
      (not_isCyclic_omega1OfAbelian_of_three_le_pRank
        (G := G) (p := p) (A := A) hAcomm_set h3A)
  obtain ⟨B, hBΩ, hcycpack, hnot⟩ :=
    exists_cocyclic_not_le_centralizer_inf_centralizer_of_not_le_centralizer
      (A := ΩA) (D := D) (P0 := P0) (by simpa [ΩA] using hΩD)
      (by simpa [ΩA] using hCop) hΩAnc hP0D
  rcases hcycpack with ⟨a, haΩ, hsup⟩
  have hBΩ_raw : B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set := by
    simpa [ΩA] using hBΩ
  have haΩ_raw : a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set := by
    simpa [ΩA] using haΩ
  have hsup_raw : B ⊔ Subgroup.zpowers a =
      OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set := by
    simpa [ΩA] using hsup
  refine ⟨B, hBΩ_raw, ?_, ?_, ⟨a, haΩ_raw, hsup_raw⟩, hnot⟩
  · exact hBΩ_raw.trans (OddOrder.GroupTheory.omega1OfAbelian_le (G := G) (H := A)
      (p := p) (hH := hAcomm_set))
  · exact not_isCyclic_of_cocyclic_omega1OfAbelian_of_three_le_pRank
      (G := G) (p := p) (A := A) (B := B) hAcomm_set h3A hBΩ_raw haΩ_raw hsup_raw


/-- Lemma 9.5's Prop. 1.16 extraction with `D = O_{p'}(F(M))`.

For `M ∈ ℳ(C_G(A))` and `A ∈ SCN₃(p)`, the subgroup `Ω₁(A)` normalizes
`O_{p'}(F(M))`: `A ≤ C_G(A) ≤ M`, `M` normalizes `F(M)`, and the ambient
`p'`-core is characteristic in `F(M)`. Since `Ω₁(A)` is a `p`-group and
`O_{p'}(F(M))` is a `p'`-subgroup, the action is coprime. This packages the
exact input needed for the BG L2590--L2613 contradiction block. -/
private theorem exists_cocyclic_omega1_not_le_cent_inf_opiCoreFitting
    [Finite G] {p : ℕ} [Fact p.Prime] {A M P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G)
    (hP0D : ¬ P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G)) :
    ∃ B : Subgroup G,
      B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ∧
      B ≤ A ∧ ¬ IsCyclic ↥B ∧
      (∃ a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set,
        B ⊔ Subgroup.zpowers a =
          OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) ∧
      ¬ P0 ≤ Subgroup.centralizer
        (((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) ⊓
            Subgroup.centralizer (B : Set G)) : Set G) := by
  classical
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  have h3A : 3 ≤ pRank A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank
      (isPGroup_of_mem_scn3Global hA) (three_le_rank_of_mem_scn3Global hA)
  haveI hAcomm_inst : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hA_le_M : A ≤ M := by
    exact (Subgroup.le_centralizer A).trans hM.2
  have hM_norm_F : M ≤ Subgroup.normalizer (S08.fittingInG M : Set G) := by
    intro x hxM
    exact S08.mem_normalizer_fittingInG_of_mem hxM
  have hA_norm_F : A ≤ Subgroup.normalizer (S08.fittingInG M : Set G) :=
    hA_le_M.trans hM_norm_F
  have hOmegaD : OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ≤
      Subgroup.normalizer D := by
    exact (OddOrder.GroupTheory.omega1OfAbelian_le (G := G) (H := A)
      (p := p) (hH := hAcomm_set)).trans
        (le_normalizer_opiCoreInG_of_le_normalizer ({p} : Set ℕ)ᶜ hA_norm_F)
  have hOmegapi : Subgroup.IsPiSubgroup ({p} : Set ℕ)
      (OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) :=
    isPiSubgroup_singleton_of_isPGroup
      (OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
        (G := G) (H := A) (p := p) (hH := hAcomm_set)).isPGroup
  have hDpic : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ D := by
    simpa [D] using
      (isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M))
  have hCop : Nat.Coprime
      (Nat.card ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set)) (Nat.card ↥D) :=
    coprime_card_of_isPiSubgroup_of_isPiSubgroup_compl hOmegapi hDpic
  simpa [D] using
    (exists_noncyclic_cocyclic_omega1OfAbelian_not_le_centralizer_inf
      (G := G) (p := p) (A := A) (D := D) (P0 := P0)
      hAcomm_set h3A hOmegaD hCop (by simpa [D] using hP0D))

/-- Any subgroup of the abelian `Ω₁(A)` is elementary abelian at the same prime. -/
private theorem isElementaryAbelian_of_le_omega1OfAbelian {p : ℕ} {A B : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hBΩ : B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) :
    B.IsElementaryAbelian p := by
  let Ω : Subgroup G := OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set
  have hΩea : Ω.IsElementaryAbelian p := by
    simpa [Ω] using
      (OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
        (G := G) (H := A) (p := p) (hH := hAcomm_set))
  have hB_sub_ea : (B.subgroupOf Ω).IsElementaryAbelian p :=
    hΩea.to_subgroup (B.subgroupOf Ω)
  exact IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBΩ) hB_sub_ea

/-- BG Lemma 9.5 bridge: the `B` found by the cocyclic `Ω₁(A)` argument is
also outside the uniqueness class whenever the ambient `SCN₃` subgroup `A` is
the chosen counterexample. -/
private theorem exists_nonU_cocyclic_omega1_not_le_cent_inf_opiCoreFitting [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A M P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (hP0D : ¬ P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G)) :
    ∃ B : Subgroup G,
      B.IsElementaryAbelian p ∧
      ¬ IsUniquelyMaximal B ∧
      B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ∧
      B ≤ A ∧
      ¬ IsCyclic ↥B ∧
      (∃ a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set,
        B ⊔ Subgroup.zpowers a =
          OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) ∧
      ¬ P0 ≤ Subgroup.centralizer
        (((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) ⊓
            Subgroup.centralizer (B : Set G)) : Set G) := by
  obtain ⟨B, hBΩ, hBA, hBnc, hcyc, hnot_cent⟩ :=
    exists_cocyclic_omega1_not_le_cent_inf_opiCoreFitting hAcomm_set hM hA hP0D
  have hBea : B.IsElementaryAbelian p :=
    isElementaryAbelian_of_le_omega1OfAbelian hAcomm_set hBΩ
  exact ⟨B, hBea,
    not_isUniquelyMaximal_of_le_scn3_counterexample hG hAcomm_set hA hBA hAnot,
    hBΩ, hBA, hBnc, hcyc, hnot_cent⟩

/-- Lemma 9.5 witness package after Theorem 9.1: from the cocyclic `Ω₁(A)`
witness one also obtains `y ∈ B#` and a maximal subgroup `L` containing
`C_G(y)` with `L ≠ M`. -/
private theorem exists_nonU_cocyclic_omega1_witness_maximal_ne [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A M P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (hP0D : ¬ P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G)) :
    ∃ B : Subgroup G, ∃ y : G, ∃ L : Subgroup G,
      B.IsElementaryAbelian p ∧
      ¬ IsUniquelyMaximal B ∧
      B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ∧
      B ≤ A ∧
      ¬ IsCyclic ↥B ∧
      (∃ a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set,
        B ⊔ Subgroup.zpowers a =
          OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) ∧
      ¬ P0 ≤ Subgroup.centralizer
        (((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) ⊓
            Subgroup.centralizer (B : Set G)) : Set G) ∧
      y ∈ B ∧ y ≠ 1 ∧
      ¬ Subgroup.centralizer ({y} : Set G) ≤ M ∧
      L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)) ∧
      L ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) ∧
      L ≠ M := by
  obtain ⟨B, hBea, hBnot, hBΩ, hBA, hBnc, hcyc, hnot_cent⟩ :=
    exists_nonU_cocyclic_omega1_not_le_cent_inf_opiCoreFitting hG hAcomm_set hM hA hAnot hP0D
  haveI hAcomm_inst : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hA_le_M : A ≤ M := (Subgroup.le_centralizer A).trans hM.2
  have hBM : B ≤ M := hBA.trans hA_le_M
  obtain ⟨y, L, hyB, hy1, hCGnotM, hL, hLneM⟩ :=
    exists_nontrivial_centralizer_maximal_ne_of_not_isUniquelyMaximal hG hM.1 hBea hBM
      hBnc hBnot
  have hLA : L ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) :=
    maximalSubgroupsContaining_centralizer_of_mem_centralizer_singleton (hBA hyB) hL
  exact ⟨B, y, L, hBea, hBnot, hBΩ, hBA, hBnc, hcyc, hnot_cent,
    hyB, hy1, hCGnotM, hL, hLA, hLneM⟩

/-- BG Lemma 9.5: reapply the `(9.9)` normalizer package with a maximal subgroup
`L ∈ 𝓜(C_G(y))`, where `y ∈ A`.  The conclusion is for the same `p`-subgroup
`P ≤ N_G(A)`, matching the line `N_G(P) ≤ L` before (9.10). -/
private theorem normalizer_scn3_pSubgroup_le_witness_maximal_of_not_scn3
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A L P : Subgroup G} {y : G}
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A) (hyA : y ∈ A)
    (hL : L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)))
    (hPp : IsPGroup p P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G)) :
    P ≤ L ∧ Subgroup.normalizer (P : Set G) ≤ L := by
  exact normalizer_scn3_pSubgroup_le_maximal_of_not_scn3 hG
    (maximalSubgroupsContaining_centralizer_of_mem_centralizer_singleton hyA hL)
    hA hAnot hPp hAP hPnormA

/-- Ambient form of the identity `H' = [H,H]`. -/
private theorem derivedInG_eq_commutator (H : Subgroup G) :
    derivedInG H = ⁅(H : Subgroup G), H⁆ := by
  exact Subgroup.map_subtype_commutator H

/-- Monotonicity of the ambient derived subgroup. -/
private theorem derivedInG_mono {H K : Subgroup G} (hHK : H ≤ K) :
    derivedInG H ≤ derivedInG K := by
  rw [derivedInG_eq_commutator H, derivedInG_eq_commutator K]
  exact Subgroup.commutator_mono hHK hHK

/-- The ambient derived subgroup is contained in the subgroup it is derived from. -/
private theorem derivedInG_le_self (H : Subgroup G) : derivedInG H ≤ H := by
  unfold derivedInG
  exact Subgroup.map_subtype_le _

/-- Mapping the derived subgroup of the top subgroup of `H` back to `G` recovers
the ambient derived subgroup `H'`. -/
private theorem derivedInG_top_map_subtype (H : Subgroup G) :
    (derivedInG (⊤ : Subgroup ↥H)).map H.subtype = derivedInG H := by
  have htop : (⊤ : Subgroup ↥H).map H.subtype = H := by
    ext x
    constructor
    · rintro ⟨y, _hy, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  rw [derivedInG_eq_commutator (⊤ : Subgroup ↥H), derivedInG_eq_commutator H,
    Subgroup.map_commutator, htop]

/-- If an ambient subgroup `P₀` lies in `H'`, then its restriction to `H` lies
in the derived subgroup of the top subgroup of `↥H`. -/
private theorem subgroupOf_le_derivedInG_top_of_le_derivedInG {H P0 : Subgroup G}
    (hP0D : P0 ≤ derivedInG H) :
    P0.subgroupOf H ≤ derivedInG (⊤ : Subgroup ↥H) := by
  have hP0H : P0 ≤ H := hP0D.trans (derivedInG_le_self H)
  rw [← H.map_subtype_le_map_subtype, Subgroup.map_subgroupOf_eq_of_le hP0H,
    derivedInG_top_map_subtype H]
  exact hP0D

/-- The subgroup-theoretic core of BG (9.10): if `P₀ ≤ N_G(P)'` and
`N_G(P) ≤ L ∩ M`, then `P₀ ≤ (L ∩ M)'`. -/
private theorem le_derivedInG_inf_of_le_derivedInG_normalizer {P M L P0 : Subgroup G}
    (hP0N : P0 ≤ derivedInG (Subgroup.normalizer (P : Set G)))
    (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (hNPL : Subgroup.normalizer (P : Set G) ≤ L) :
    P0 ≤ derivedInG (L ⊓ M) :=
  hP0N.trans (derivedInG_mono (le_inf hNPL hNPM))

/-- BG Lemma 9.5 bridge toward (9.10): after reapplying (9.9) with the witness
maximal subgroup `L`, any `P₀ ≤ N_G(P)'` lies in `(L ∩ M)'`. -/
private theorem p0_le_derivedInG_inf_of_scn3_witness_maximal
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M L P P0 : Subgroup G} {y : G}
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A) (hyA : y ∈ A)
    (hL : L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)))
    (hPp : IsPGroup p P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (hP0N : P0 ≤ derivedInG (Subgroup.normalizer (P : Set G))) :
    P0 ≤ derivedInG (L ⊓ M) := by
  have hNPL : Subgroup.normalizer (P : Set G) ≤ L :=
    (normalizer_scn3_pSubgroup_le_witness_maximal_of_not_scn3
      hG hA hAnot hyA hL hPp hAP hPnormA).2
  exact le_derivedInG_inf_of_le_derivedInG_normalizer hP0N hNPM hNPL

/-- If `y ∈ B` and `L` contains `C_G(y)`, then `D ∩ C_G(B)` is contained in
`D ∩ L`. This is the subgroup inclusion used to pass from a centralizer of
`D ∩ L` to a centralizer of `D ∩ C_G(B)`. -/
private theorem inf_centralizer_le_inf_of_mem_of_maximalContaining_centralizer_singleton
    {B D L : Subgroup G} {y : G} (hyB : y ∈ B)
    (hL : L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G))) :
    D ⊓ Subgroup.centralizer (B : Set G) ≤ D ⊓ L := by
  refine le_inf inf_le_left ?_
  exact inf_le_right.trans
    ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyB)).trans hL.2)

/-- Antitonicity bridge for the final contradiction in BG Lemma 9.5. If `P₀`
centralizes `D ∩ L`, then it centralizes the smaller subgroup `D ∩ C_G(B)`. -/
private theorem le_centralizer_inf_centralizer_of_le_centralizer_inf_maximal
    {B D L P0 : Subgroup G} {y : G} (hyB : y ∈ B)
    (hL : L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)))
    (hcentDL : P0 ≤ Subgroup.centralizer ((D ⊓ L : Subgroup G) : Set G)) :
    P0 ≤ Subgroup.centralizer
      (((D ⊓ Subgroup.centralizer (B : Set G) : Subgroup G)) : Set G) :=
  hcentDL.trans
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
      (inf_centralizer_le_inf_of_mem_of_maximalContaining_centralizer_singleton
        (D := D) hyB hL)))


/-- Lemma 9.4 rank squeeze in the form used inside BG Lemma 9.5: if `K ≤ F(M)`
and every subgroup of `K` is excluded from `𝒰`, then `K` has rank at most two. -/
private theorem rank_le_two_of_no_uniqueMaximal_subgroups_le_fitting
    [Finite G] (hG : IsMinimalSimpleOdd G) {M K : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKF : K ≤ S08.fittingInG M)
    (hno : ∀ B : Subgroup G, B ≤ K → ¬ IsUniquelyMaximal B) :
    rank ↥K ≤ 2 := by
  classical
  by_contra hnot
  have h3K : 3 ≤ rank ↥K := by omega
  obtain ⟨q, hq, h3Kq⟩ :=
    exists_pRank_ge_of_pos_le_rank (G := ↥K) (n := 3) (by norm_num) h3K
  haveI : Fact q.Prime := ⟨hq⟩
  have h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q :=
    h3Kq.trans
      (pRank_le_of_injective (f := Subgroup.inclusion hKF)
        (Subgroup.inclusion_injective hKF))
  obtain ⟨B, hBmax, hBrank⟩ :=
    exists_isMaxElemAbelianIn_rank_three_of_three_le_pRank (H := K) h3Kq
  have hBea : B.IsElementaryAbelian q :=
    S08.isMaxElemAbelianIn_isElementaryAbelian hBmax
  have hBK : B ≤ K := S08.isMaxElemAbelianIn_le hBmax
  have hBU : IsUniquelyMaximal B :=
    (abelian_rank_three_isUniquelyMaximal_of_fitting hG hM h3Fq)
      B (IsMulCommutative.of_comm hBea.comm) hBea.isPGroup hBrank
  exact (hno B hBK) hBU

/-- In the BG Lemma 9.5 contradiction setup, `D ∩ L` has rank at most two.
Here `D` is any subgroup of `F(M)` and `L ≠ M` is another maximal subgroup; the
specialization `D = O_{p'}(F(M))` is used below. -/
private theorem rank_inf_le_two_of_le_fitting_of_distinct_maximals
    [Finite G] (hG : IsMinimalSimpleOdd G) {D M L : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hL : L ∈ maximalSubgroups G) (hLM : L ≠ M)
    (hDF : D ≤ S08.fittingInG M) :
    rank ↥(D ⊓ L : Subgroup G) ≤ 2 := by
  refine rank_le_two_of_no_uniqueMaximal_subgroups_le_fitting hG hM
    (K := D ⊓ L) (inf_le_left.trans hDF) ?_
  intro B hB
  exact not_isUniquelyMaximal_of_le_inf_distinct_maximals hM hL
    (hB.trans (le_inf (inf_le_left.trans (hDF.trans (S08.fittingInG_le M))) inf_le_right))
    hLM

/-- Specialization of the Lemma 9.5 rank squeeze to `D = O_{p'}(F(M))`. -/
private theorem rank_inf_opiCoreFitting_le_two_of_distinct_maximals
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} {M L : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hL : L ∈ maximalSubgroups G) (hLM : L ≠ M) :
    rank ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M) ⊓ L : Subgroup G) ≤ 2 :=
  rank_inf_le_two_of_le_fitting_of_distinct_maximals hG hM hL hLM
    (opiCoreInG_le ({p} : Set ℕ)ᶜ (S08.fittingInG M))

/-- A `subgroupOf` copy has rank no larger than the ambient subgroup it copies. -/
private theorem rank_subgroupOf_le_of_le [Finite G] {H K : Subgroup G} (hKH : K ≤ H) :
    rank ↥(K.subgroupOf H) ≤ rank ↥K :=
  rank_le_of_injective (G := ↥K) (H := ↥(K.subgroupOf H))
    (f := (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hKH).injective

/-- Local `L ∩ M` version of the `O_{p'}(F(M)) ∩ L` rank squeeze. -/
private theorem pRank_subgroupOf_inf_opiCoreFitting_le_two_of_distinct_maximals
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact q.Prime]
    {M L : Subgroup G} (hM : M ∈ maximalSubgroups G) (hL : L ∈ maximalSubgroups G)
    (hLM : L ≠ M) :
    pRank ↥((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M) ⊓ L : Subgroup G).subgroupOf
      (L ⊓ M)) q ≤ 2 := by
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  let K : Subgroup G := D ⊓ L
  have hKleH : K ≤ L ⊓ M := by
    refine le_inf inf_le_right ?_
    exact inf_le_left.trans ((opiCoreInG_le ({p} : Set ℕ)ᶜ (S08.fittingInG M)).trans
      (S08.fittingInG_le M))
  have hrankK : rank ↥K ≤ 2 := by
    simpa [D, K] using
      (rank_inf_opiCoreFitting_le_two_of_distinct_maximals
        (G := G) (p := p) hG hM hL hLM)
  exact (pRank_le_rank
      (G := ↥(K.subgroupOf (L ⊓ M))) q).trans
    ((rank_subgroupOf_le_of_le hKleH).trans hrankK)

open OddOrder.Isaacs.Ch03 in
open scoped commutatorElement in
/-- BG Lemma 1.9 applied to a chief series: a coprime subgroup that stabilizes
every chief factor of `K` centralizes `K`. This isolates the Lemma 1.9 part of
BG Lemma 9.5 after Corollary 4.19 supplies the per-factor stabilizer input. -/
private theorem coprime_chiefSeries_stabilizer_le_centralizer
    {M : Type*} [Group M] [Finite M] {K : Subgroup M} [K.Normal] {D : Subgroup M}
    (hcop : (Nat.card ↥D).Coprime (Nat.card ↥K))
    (hsolv : IsSolvable ↥D ∨ IsSolvable ↥K)
    (hstab : ∀ i, ⁅chiefSeriesInside K i, D⁆ ≤ chiefSeriesInside K (i + 1)) :
    D ≤ Subgroup.centralizer (K : Set M) := by
  classical
  obtain ⟨N, hN⟩ := chiefSeriesInside_exists_eq_bot K
  set ψ : ↥D →* MulAut ↥K := (MulAut.conjNormal (H := K)).comp D.subtype with hψ
  set s : ℕ → Subgroup ↥K := fun i => (chiefSeriesInside K i).subgroupOf K with hs
  have hψcoe : ∀ (a : ↥D) (g : ↥K),
      ((ψ a) g : M) = (a : M) * (g : M) * (a : M)⁻¹ := by
    intro a g
    rw [hψ]
    simp [MulAut.conjNormal_apply]
  have htrivψ : ∀ a : ↥D, ψ a = 1 := by
    refine OddOrder.BG.Ch1.S01.coprime_stabilizes_chain_trivial
      ψ hcop hsolv s ?_ ?_ (n := N) ?_ ?_ ?_ ?_
    · intro i j hij
      exact Subgroup.comap_mono (chiefSeriesInside_antitone K hij)
    · simp [hs, chiefSeriesInside_zero, Subgroup.subgroupOf_self]
    · simp [hs, hN, Subgroup.bot_subgroupOf]
    · intro i
      exact (inferInstance : (chiefSeriesInside K i).Normal).subgroupOf K
    · intro i
      rw [isAInvariant_iff_smul_mem]
      intro a g hg
      rw [hs, Subgroup.mem_subgroupOf] at hg ⊢
      rw [hψcoe]
      exact (chiefSeriesInside_instNormal K i).conj_mem _ hg _
    · intro i a x hx
      rw [hs, Subgroup.mem_subgroupOf] at hx
      refine ⟨x⁻¹ * ψ a x, ?_, by group⟩
      rw [hs, Subgroup.mem_subgroupOf]
      have hcoe : ((x⁻¹ * ψ a x : ↥K) : M) = ⁅(x : M)⁻¹, (a : M)⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hψcoe, commutatorElement_def]
        group
      rw [hcoe]
      exact hstab i (Subgroup.commutator_mem_commutator
        (Subgroup.inv_mem _ hx) (SetLike.coe_mem a))
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 := DFunLike.congr_fun (htrivψ ⟨x, hx⟩) ⟨k, hk⟩
  have h2 : (x : M) * k * x⁻¹ = k := by
    have := congrArg Subtype.val h1
    rwa [hψcoe] at this
  have h3 : x * k = k * x := by
    have := congrArg (· * x) h2
    simpa [mul_assoc] using this
  exact h3.symm

/-- If a subgroup centralizes every chief factor in `chiefSeriesInside K`, it
stabilizes that chief series. This is the exact shape needed to feed the Lemma
1.9 bridge after Corollary 4.19 gives chief-factor centralization. -/
private theorem chiefSeries_stabilizer_of_le_chiefFactorCentralizer
    {M : Type*} [Group M] [Finite M] {K D E : Subgroup M} [K.Normal]
    (hDE : D ≤ E)
    (hcent : ∀ i, E ≤ chiefFactorCentralizer
      (chiefSeriesInside K i) (chiefSeriesInside K (i + 1))) :
    ∀ i, ⁅chiefSeriesInside K i, D⁆ ≤ chiefSeriesInside K (i + 1) := by
  intro i
  exact chiefFactorCentralizer.commutator_le_of_le ((hDE).trans (hcent i))

/-- Corollary 4.19 output plus Lemma 1.9 input, already composed: if `D` is
coprime to `K`, lies in a subgroup `E`, and `E` centralizes every chief factor
of `K`, then `D` centralizes `K`. -/
private theorem le_centralizer_of_le_chiefFactorCentralizer_chain
    {M : Type*} [Group M] [Finite M] {K D E : Subgroup M} [K.Normal]
    (hcop : (Nat.card ↥D).Coprime (Nat.card ↥K))
    (hsolv : IsSolvable ↥D ∨ IsSolvable ↥K)
    (hDE : D ≤ E)
    (hcent : ∀ i, E ≤ chiefFactorCentralizer
      (chiefSeriesInside K i) (chiefSeriesInside K (i + 1))) :
    D ≤ Subgroup.centralizer (K : Set M) :=
  coprime_chiefSeries_stabilizer_le_centralizer hcop hsolv
    (chiefSeries_stabilizer_of_le_chiefFactorCentralizer hDE hcent)

/-- A centralizer conclusion proved in the local group `↥H` lifts back to the
ambient group. This is the final direction needed after applying Corollary 4.19
inside `L ∩ M`. -/
private theorem le_centralizer_of_subgroupOf_le_centralizer
    {H K P0 : Subgroup G} (hP0H : P0 ≤ H) (hKH : K ≤ H)
    (hlocal : P0.subgroupOf H ≤
      Subgroup.centralizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H)) :
    P0 ≤ Subgroup.centralizer (K : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hxH : x ∈ H := hP0H hx
  have hkH : k ∈ H := hKH hk
  have hxlocal : (⟨x, hxH⟩ : ↥H) ∈ P0.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact hx
  have hklocal : (⟨k, hkH⟩ : ↥H) ∈ K.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact hk
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.mp (hlocal hxlocal)
      (⟨k, hkH⟩ : ↥H) hklocal)

/-- Data needed to apply BG Corollary 4.19 to one local chief factor `U/V`.
The prime and the rank-two normal `p`-subgroup are factor-specific; this is the
shape produced later from the `D ∩ L` rank bound in Lemma 9.5. -/
private structure Cor419ChiefFactorData (M : Type*) [Group M] [Finite M]
    (U V : Subgroup M) [V.Normal] where
  q : ℕ
  q_prime : q.Prime
  q_odd : Odd q
  R : Subgroup M
  R_normal : R.Normal
  R_pgroup : IsPGroup q ↥R
  R_rank : pRank ↥R q ≤ 2
  Ubar_pgroup : IsPGroup q ↥(U.map (QuotientGroup.mk' V))
  U_le_sup : U ≤ R ⊔ V

/-- A chief factor of a finite solvable group is a `q`-group for some prime `q`.
This isolates the prime-selection part needed when Lemma 9.5 feeds a local chief
factor into BG Corollary 4.19. -/
private theorem exists_prime_isPGroup_chiefFactor_quotient
    {M : Type*} [Group M] [Finite M] [IsSolvable M]
    {U V : Subgroup M} (hChief : IsChiefFactor U V) :
    haveI : V.Normal := hChief.normal_bot
    ∃ q : ℕ, q.Prime ∧ IsPGroup q ↥(U.map (QuotientGroup.mk' V)) := by
  haveI : V.Normal := hChief.normal_bot
  have hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal (U.map (QuotientGroup.mk' V)) :=
    hChief.isMinimalNormal_map_quotient
  obtain ⟨q, hq, hElem⟩ :=
    OddOrder.Isaacs.Ch03.solvable_minimal_normal_isElementaryAbelian hMin
  exact ⟨q, hq, hElem.isPGroup⟩

/-- In an odd-order ambient group, the prime attached to a nontrivial chief-factor
`q`-group quotient is odd. -/
private theorem odd_prime_of_chiefFactor_quotient_isPGroup
    {M : Type*} [Group M] [Finite M] (hoddM : Odd (Nat.card M))
    {q : ℕ} (hq : q.Prime) {U V : Subgroup M} (hChief : IsChiefFactor U V)
    (hUbar_pgroup :
      haveI : V.Normal := hChief.normal_bot
      IsPGroup q ↥(U.map (QuotientGroup.mk' V))) :
    Odd q := by
  haveI : V.Normal := hChief.normal_bot
  haveI : Fact q.Prime := ⟨hq⟩
  have hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal (U.map (QuotientGroup.mk' V)) :=
    hChief.isMinimalNormal_map_quotient
  have hUbar_ne : U.map (QuotientGroup.mk' V) ≠ ⊥ := hMin.2.1
  have hcard_ne_one : Nat.card ↥(U.map (QuotientGroup.mk' V)) ≠ 1 := by
    intro hcard
    exact hUbar_ne (Subgroup.eq_bot_of_card_eq _ hcard)
  have hq_dvd_Ubar : q ∣ Nat.card ↥(U.map (QuotientGroup.mk' V)) := by
    rcases hUbar_pgroup.card_eq_or_dvd with hcard | hdvd
    · exact False.elim (hcard_ne_one hcard)
    · exact hdvd
  have hq_dvd_quot : q ∣ Nat.card (M ⧸ V) :=
    hq_dvd_Ubar.trans (Subgroup.card_subgroup_dvd_card (U.map (QuotientGroup.mk' V)))
  exact hoddM.of_dvd_nat (hq_dvd_quot.trans (Subgroup.card_quotient_dvd_card V))

/-- The ambient `q`-core of a rank-two normal subgroup has `q`-rank at most two.
This is the rank input needed when Lemma 9.5 uses `O_q(D ∩ L)` as the Corollary
4.19 subgroup for a `q`-primary chief factor. -/
private theorem pRank_opiCoreInG_singleton_le_two_of_rank_le_two
    {M : Type*} [Group M] [Finite M] {q : ℕ} [Fact q.Prime] {K : Subgroup M}
    (hK_rank : rank ↥K ≤ 2) :
    pRank ↥(opiCoreInG ({q} : Set ℕ) K) q ≤ 2 := by
  exact (pRank_le_rank
      (G := ↥(opiCoreInG ({q} : Set ℕ) K)) q).trans
    ((rank_le_of_injective
      (f := Subgroup.inclusion (opiCoreInG_le ({q} : Set ℕ) K))
      (Subgroup.inclusion_injective (opiCoreInG_le ({q} : Set ℕ) K))).trans hK_rank)

/-- A finite subgroup that is both a `p`-group and a `q`-group for distinct
prime numbers is trivial. -/
private theorem eq_bot_of_isPGroup_of_isPGroup_ne
    {M : Type*} [Group M] [Finite M] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) {H : Subgroup M} (hp : IsPGroup p ↥H) (hq : IsPGroup q ↥H) :
    H = ⊥ := by
  have hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥H) :=
    IsPGroup.coprime_card_of_ne p q hpq H H hp hq
  exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl)

/-- If the image of `P` in `M/V` is trivial, then `P ≤ V`. -/
private theorem le_of_map_quotient_eq_bot
    {M : Type*} [Group M] {V P : Subgroup M} [V.Normal]
    (h : P.map (QuotientGroup.mk' V) = ⊥) : P ≤ V := by
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  exact h

/-- In a finite nilpotent normal subgroup, a `q`-primary chief-series layer is
absorbed by `O_q(K)` modulo the next layer. -/
private theorem chiefSeriesInside_le_opiCoreInG_sup_of_nilpotent
    {M : Type*} [Group M] [Finite M] {q : ℕ} [Fact q.Prime]
    {K : Subgroup M} [K.Normal] (hKnilp : Group.IsNilpotent ↥K) (i : ℕ)
    (hUbar_pgroup :
      IsPGroup q ↥((chiefSeriesInside K i).map
        (QuotientGroup.mk' (chiefSeriesInside K (i + 1))))) :
    chiefSeriesInside K i ≤
      opiCoreInG ({q} : Set ℕ) K ⊔ chiefSeriesInside K (i + 1) := by
  classical
  let U : Subgroup M := chiefSeriesInside K i
  let V : Subgroup M := chiefSeriesInside K (i + 1)
  let X : Subgroup M := opiCoreInG ({q} : Set ℕ) K ⊔ V
  have hU_le_K : U ≤ K := by
    simpa [U] using chiefSeriesInside_le K i
  have hU_nilp : Group.IsNilpotent ↥U := by
    haveI : Group.IsNilpotent ↥K := hKnilp
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hU_le_K)
  change U ≤ X
  refine S08.le_of_sylow_le_of_nilpotent hU_nilp ?_
  intro r
  haveI hrFact : Fact (Nat.Prime (r : ℕ)) :=
    ⟨Nat.prime_of_mem_primeFactors r.2⟩
  let S : Sylow (r : ℕ) ↥U := default
  let Sm : Subgroup M := (S : Subgroup ↥U).map U.subtype
  have hSm_le_U : Sm ≤ U := by
    simpa [Sm] using Subgroup.map_subtype_le (S : Subgroup ↥U)
  have hSm_le_K : Sm ≤ K := hSm_le_U.trans hU_le_K
  by_cases hrq : (r : ℕ) = q
  · have hSm_q : IsPGroup q ↥Sm := by
      simpa [S, Sm, hrq] using ((S : Sylow (r : ℕ) ↥U).isPGroup'.map U.subtype)
    have hSm_le_O : Sm ≤ opiCoreInG ({q} : Set ℕ) K :=
      S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hKnilp hSm_le_K hSm_q
    have hSm_le_X : Sm ≤ X := hSm_le_O.trans le_sup_left
    simpa [S, Sm, X] using hSm_le_X
  · have hSm_r : IsPGroup (r : ℕ) ↥Sm := by
      simpa [S, Sm] using ((S : Sylow (r : ℕ) ↥U).isPGroup'.map U.subtype)
    have hSmq_r : IsPGroup (r : ℕ) ↥(Sm.map (QuotientGroup.mk' V)) :=
      hSm_r.map (QuotientGroup.mk' V)
    have hSmq_le_Ubar :
        Sm.map (QuotientGroup.mk' V) ≤ U.map (QuotientGroup.mk' V) :=
      Subgroup.map_mono hSm_le_U
    have hSmq_q : IsPGroup q ↥(Sm.map (QuotientGroup.mk' V)) := by
      simpa [U, V] using hUbar_pgroup.to_le hSmq_le_Ubar
    have hSmq_bot : Sm.map (QuotientGroup.mk' V) = ⊥ :=
      eq_bot_of_isPGroup_of_isPGroup_ne hrq hSmq_r hSmq_q
    have hSm_le_V : Sm ≤ V := le_of_map_quotient_eq_bot hSmq_bot
    have hSm_le_X : Sm ≤ X := hSm_le_V.trans le_sup_right
    simpa [S, Sm, X] using hSm_le_X

/-- Package one chief-series layer using the ambient `q`-core of `K` as the
rank-two normal `q`-subgroup required by BG Corollary 4.19.  The only remaining
mathematical input is the nilpotent/Hall-style absorption `U ≤ O_q(K) V`, which
is kept explicit here. -/
private def cor419ChiefFactorData_chiefSeriesInside_of_opiCoreInG
    {M : Type*} [Group M] [Finite M] {q : ℕ} (hq_prime : q.Prime) (hq_odd : Odd q)
    {K : Subgroup M} [K.Normal] (hK_rank : rank ↥K ≤ 2) (i : ℕ)
    (hUbar_pgroup :
      IsPGroup q ↥((chiefSeriesInside K i).map
        (QuotientGroup.mk' (chiefSeriesInside K (i + 1)))))
    (hU_le_sup :
      chiefSeriesInside K i ≤ opiCoreInG ({q} : Set ℕ) K ⊔ chiefSeriesInside K (i + 1)) :
    Cor419ChiefFactorData M (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) := by
  haveI : Fact q.Prime := ⟨hq_prime⟩
  refine
    { q := q
      q_prime := hq_prime
      q_odd := hq_odd
      R := opiCoreInG ({q} : Set ℕ) K
      R_normal := opiCoreInG_normal ({q} : Set ℕ)
      R_pgroup := isPGroup_opiCoreInG_singleton K
      R_rank := pRank_opiCoreInG_singleton_le_two_of_rank_le_two hK_rank
      Ubar_pgroup := hUbar_pgroup
      U_le_sup := hU_le_sup }

/-- Choose the chief-factor prime and package Corollary 4.19 data from the
ambient `q`-core of `K`.  After the rank and oddness bridges, the only remaining
input is the nilpotent absorption statement `U ≤ O_q(K) V`. -/
private noncomputable def cor419ChiefFactorData_chiefSeriesInside_of_opiCoreInG_absorption
    {M : Type*} [Group M] [Finite M] [IsSolvable M] (hoddM : Odd (Nat.card M))
    {K : Subgroup M} [K.Normal] (hK_rank : rank ↥K ≤ 2) (i : ℕ)
    (hU_ne : chiefSeriesInside K i ≠ ⊥)
    (habsorb : ∀ q : ℕ, q.Prime →
      IsPGroup q ↥((chiefSeriesInside K i).map
        (QuotientGroup.mk' (chiefSeriesInside K (i + 1)))) →
      chiefSeriesInside K i ≤ opiCoreInG ({q} : Set ℕ) K ⊔ chiefSeriesInside K (i + 1)) :
    Cor419ChiefFactorData M (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) := by
  classical
  have hChief : IsChiefFactor (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) :=
    isChiefFactor_chiefSeriesInside hU_ne
  let ex := exists_prime_isPGroup_chiefFactor_quotient hChief
  let q : ℕ := Classical.choose ex
  have hq : q.Prime := (Classical.choose_spec ex).1
  have hUbar_pgroup :
      IsPGroup q ↥((chiefSeriesInside K i).map
        (QuotientGroup.mk' (chiefSeriesInside K (i + 1)))) :=
    (Classical.choose_spec ex).2
  exact cor419ChiefFactorData_chiefSeriesInside_of_opiCoreInG
    hq (odd_prime_of_chiefFactor_quotient_isPGroup hoddM hq hChief hUbar_pgroup)
    hK_rank i hUbar_pgroup (habsorb q hq hUbar_pgroup)

/-- Nilpotent version of the chief-series Corollary 4.19 data package. -/
private noncomputable def cor419ChiefFactorData_chiefSeriesInside_of_nilpotent
    {M : Type*} [Group M] [Finite M] [IsSolvable M] (hoddM : Odd (Nat.card M))
    {K : Subgroup M} [K.Normal] (hKnilp : Group.IsNilpotent ↥K)
    (hK_rank : rank ↥K ≤ 2) :
    ∀ i, chiefSeriesInside K i ≠ ⊥ →
      Cor419ChiefFactorData M (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) := by
  intro i hU_ne
  exact cor419ChiefFactorData_chiefSeriesInside_of_opiCoreInG_absorption
    hoddM hK_rank i hU_ne
    (fun q hq hUbar => by
      haveI : Fact q.Prime := ⟨hq⟩
      exact chiefSeriesInside_le_opiCoreInG_sup_of_nilpotent (q := q) hKnilp i hUbar)

/-- Chief-series layers contained in a normal rank-two `q`-subgroup already have
the shape required by BG Corollary 4.19.  The later Lemma 9.5 proof uses this
with the `q`-part extracted from `D ∩ L`. -/
private def cor419ChiefFactorData_chiefSeriesInside_of_le_normal_pSubgroup
    {M : Type*} [Group M] [Finite M] {q : ℕ} (hq_prime : q.Prime) (hq_odd : Odd q)
    {K R : Subgroup M} [K.Normal] [R.Normal]
    (hK_le_R : K ≤ R) (hR_pgroup : IsPGroup q ↥R) (hR_rank : pRank ↥R q ≤ 2) :
    ∀ i, chiefSeriesInside K i ≠ ⊥ →
      Cor419ChiefFactorData M (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) := by
  intro i _hU_ne
  have hU_le_R : chiefSeriesInside K i ≤ R :=
    (chiefSeriesInside_le K i).trans hK_le_R
  have hU_pgroup : IsPGroup q ↥(chiefSeriesInside K i) := hR_pgroup.to_le hU_le_R
  refine
    { q := q
      q_prime := hq_prime
      q_odd := hq_odd
      R := R
      R_normal := inferInstance
      R_pgroup := hR_pgroup
      R_rank := hR_rank
      Ubar_pgroup := ?_
      U_le_sup := ?_ }
  · exact hU_pgroup.map (QuotientGroup.mk' (chiefSeriesInside K (i + 1)))
  · exact hU_le_R.trans le_sup_left

/-- Turn per-factor BG Corollary 4.19 data into the exact chief-factor
centralizer chain input consumed by the Lemma 1.9 bridge.  Trivial zero layers
of `chiefSeriesInside` are handled without Corollary 4.19 data. -/
private theorem local_derived_le_chiefFactorCentralizer_chain_of_cor419Data
    {M : Type*} [Group M] [Finite M] (hoddM : Odd (Nat.card M))
    {K : Subgroup M} [K.Normal]
    (hdata : ∀ i, chiefSeriesInside K i ≠ ⊥ →
      Cor419ChiefFactorData M (chiefSeriesInside K i) (chiefSeriesInside K (i + 1))) :
    ∀ i, derivedInG (⊤ : Subgroup M) ≤
      chiefFactorCentralizer (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) := by
  intro i
  by_cases hU0 : chiefSeriesInside K i = ⊥
  · rw [chiefFactorCentralizer.le_iff_commutator_le, hU0, Subgroup.commutator_bot_left]
    exact bot_le
  · let d := hdata i hU0
    have hChief : IsChiefFactor (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) :=
      isChiefFactor_chiefSeriesInside hU0
    haveI : Fact d.q.Prime := ⟨d.q_prime⟩
    haveI : d.R.Normal := d.R_normal
    have hcomm : _root_.commutator M ≤
        chiefFactorCentralizer (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) :=
      OddOrder.BG.Ch1.S04.commutator_le_chiefFactorCentralizer_of_pRank_le_two_of_le_sup
        (G := M) hoddM d.q_odd hChief d.Ubar_pgroup d.R_pgroup d.R_rank d.U_le_sup
    rw [derivedInG_eq_commutator (G := M) (⊤ : Subgroup M)]
    simpa [_root_.commutator] using hcomm

/-- Local Corollary 4.19 output plus the S09 bridge package: if `P₀ ≤ H'`
and the local derived subgroup of `H` centralizes every chief factor of `K`,
then `P₀` centralizes `K` back in the ambient group. -/
private theorem le_centralizer_of_local_derived_chiefFactorCentralizer_chain
    [Finite G] {H K P0 : Subgroup G} [((K.subgroupOf H : Subgroup ↥H)).Normal]
    (hP0D : P0 ≤ derivedInG H) (hKH : K ≤ H)
    (hcop : (Nat.card ↥(P0.subgroupOf H)).Coprime
      (Nat.card ↥(K.subgroupOf H)))
    (hsolv : IsSolvable ↥(P0.subgroupOf H) ∨ IsSolvable ↥(K.subgroupOf H))
    (hcent : ∀ i, derivedInG (⊤ : Subgroup ↥H) ≤
      chiefFactorCentralizer
        (chiefSeriesInside (K.subgroupOf H) i)
        (chiefSeriesInside (K.subgroupOf H) (i + 1))) :
    P0 ≤ Subgroup.centralizer (K : Set G) := by
  have hP0_local :
      P0.subgroupOf H ≤ derivedInG (⊤ : Subgroup ↥H) :=
    subgroupOf_le_derivedInG_top_of_le_derivedInG hP0D
  have hlocal :
      P0.subgroupOf H ≤
        Subgroup.centralizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
    le_centralizer_of_le_chiefFactorCentralizer_chain
      (K := K.subgroupOf H) (D := P0.subgroupOf H)
      (E := derivedInG (⊤ : Subgroup ↥H)) hcop hsolv hP0_local hcent
  exact le_centralizer_of_subgroupOf_le_centralizer
    (hP0D.trans (derivedInG_le_self H)) hKH hlocal

/-- Local BG Corollary 4.19 data plus the S09 bridge package, already composed:
if `P₀ ≤ H'` and every nonzero chief layer of `K` carries Corollary 4.19 data,
then `P₀` centralizes `K` in the ambient group. -/
private theorem le_centralizer_of_local_cor419Data_chain
    [Finite G] {H K P0 : Subgroup G} [((K.subgroupOf H : Subgroup ↥H)).Normal]
    (hoddH : Odd (Nat.card ↥H)) (hP0D : P0 ≤ derivedInG H) (hKH : K ≤ H)
    (hcop : (Nat.card ↥(P0.subgroupOf H)).Coprime
      (Nat.card ↥(K.subgroupOf H)))
    (hsolv : IsSolvable ↥(P0.subgroupOf H) ∨ IsSolvable ↥(K.subgroupOf H))
    (hdata : ∀ i, chiefSeriesInside (K.subgroupOf H) i ≠ ⊥ →
      Cor419ChiefFactorData (↥H)
        (chiefSeriesInside (K.subgroupOf H) i)
        (chiefSeriesInside (K.subgroupOf H) (i + 1))) :
    P0 ≤ Subgroup.centralizer (K : Set G) :=
  le_centralizer_of_local_derived_chiefFactorCentralizer_chain
    hP0D hKH hcop hsolv
    (local_derived_le_chiefFactorCentralizer_chain_of_cor419Data hoddH hdata)

/-- Odd order passes from the ambient group to a subgroup. -/
private theorem odd_card_subgroup_of_odd [Finite G] (hoddG : Odd (Nat.card G))
    (H : Subgroup G) : Odd (Nat.card ↥H) :=
  hoddG.of_dvd_nat (Subgroup.card_subgroup_dvd_card H)

/-- If `D` is normalized by `M` and contained in `M`, then `D ∩ L` is normal
inside `L ∩ M`.  This is the local normality needed before applying chief-series
arguments to `D ∩ L` in BG Lemma 9.5. -/
private theorem inf_subgroupOf_inf_normal_of_le_normalizer
    {D L M : Subgroup G} (hDM : D ≤ M)
    (hMnormD : M ≤ Subgroup.normalizer (D : Set G)) :
    (((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) : Subgroup ↥(L ⊓ M))).Normal := by
  have hK_le_H : (D ⊓ L : Subgroup G) ≤ L ⊓ M :=
    le_inf inf_le_right (inf_le_left.trans hDM)
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hK_le_H).mpr ?_
  intro x hxH
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    rw [Subgroup.mem_inf] at hk ⊢
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hMnormD hxH.2) k).mp hk.1
    · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hxH.1) k).mp hk.2
  · intro hk
    rw [Subgroup.mem_inf] at hk ⊢
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hMnormD hxH.2) k).mpr hk.1
    · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hxH.1) k).mpr hk.2

/-- Lemma 9.5's `D ∩ L` Corollary 4.19 consumption step, specialized to the
local group `L ∩ M`.  Once `(9.10)` gives `P₀ ≤ (L ∩ M).derived` and Corollary
4.19 data is available for every nonzero chief layer of `D ∩ L`, this proves
that `P₀` centralizes `D ∩ L`. -/
private theorem le_centralizer_inf_of_local_cor419Data_chain
    [Finite G] (hG : IsMinimalSimpleOdd G) {D L M P0 : Subgroup G}
    (hDM : D ≤ M) (hMnormD : M ≤ Subgroup.normalizer (D : Set G))
    (hP0_der : P0 ≤ derivedInG (L ⊓ M))
    (hcop : (Nat.card ↥(P0.subgroupOf (L ⊓ M))).Coprime
      (Nat.card ↥((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M))))
    (hsolv :
      IsSolvable ↥(P0.subgroupOf (L ⊓ M)) ∨
        IsSolvable ↥((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M)))
    (hdata :
      letI : (((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) :
          Subgroup ↥(L ⊓ M))).Normal :=
        inf_subgroupOf_inf_normal_of_le_normalizer hDM hMnormD
      ∀ i,
      chiefSeriesInside ((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M)) i ≠ ⊥ →
        Cor419ChiefFactorData (↥(L ⊓ M))
          (chiefSeriesInside ((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M)) i)
          (chiefSeriesInside ((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M)) (i + 1))) :
    P0 ≤ Subgroup.centralizer ((D ⊓ L : Subgroup G) : Set G) := by
  have hDL_le_LM : (D ⊓ L : Subgroup G) ≤ L ⊓ M :=
    le_inf inf_le_right (inf_le_left.trans hDM)
  haveI : (((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) :
      Subgroup ↥(L ⊓ M))).Normal :=
    inf_subgroupOf_inf_normal_of_le_normalizer hDM hMnormD
  exact le_centralizer_of_local_cor419Data_chain
    (H := L ⊓ M) (K := D ⊓ L) (P0 := P0)
    (odd_card_subgroup_of_odd hG.odd (L ⊓ M)) hP0_der hDL_le_LM hcop hsolv hdata

/-- A `π`-subgroup remains a `π`-subgroup when viewed as a subgroup of an
ambient overgroup. -/
private theorem isPiSubgroup_subgroupOf_of_le [Finite G]
    {π : Set ℕ} {K H : Subgroup G} (hKH : K ≤ H)
    (hKpi : Subgroup.IsPiSubgroup π K) :
    Subgroup.IsPiSubgroup π (K.subgroupOf H) := by
  intro r hr
  exact hKpi r (by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv] at hr)

/-- Nilpotent/rank version of the local `D ∩ L` Corollary 4.19 consumption
step.  The solvability of the local group supplies the chief-factor prime, and
nilpotence supplies the `O_q(K)` absorption for every chief layer. -/
private theorem le_centralizer_inf_of_local_nilpotent_rank_chain
    [Finite G] (hG : IsMinimalSimpleOdd G) {D L M P0 : Subgroup G}
    [IsSolvable ↥(L ⊓ M)]
    (hDM : D ≤ M) (hMnormD : M ≤ Subgroup.normalizer (D : Set G))
    (hP0_der : P0 ≤ derivedInG (L ⊓ M))
    (hcop : (Nat.card ↥(P0.subgroupOf (L ⊓ M))).Coprime
      (Nat.card ↥((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M))))
    (hKnilp : Group.IsNilpotent
      ↥(((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) : Subgroup ↥(L ⊓ M))))
    (hK_rank :
      rank ↥(((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) : Subgroup ↥(L ⊓ M))) ≤ 2) :
    P0 ≤ Subgroup.centralizer ((D ⊓ L : Subgroup G) : Set G) := by
  have hK_solv :
      IsSolvable
        ↥(((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) : Subgroup ↥(L ⊓ M))) := by
    haveI : Group.IsNilpotent
        ↥(((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) : Subgroup ↥(L ⊓ M))) :=
      hKnilp
    infer_instance
  haveI : (((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) :
      Subgroup ↥(L ⊓ M))).Normal :=
    inf_subgroupOf_inf_normal_of_le_normalizer hDM hMnormD
  exact le_centralizer_inf_of_local_cor419Data_chain
    (D := D) (L := L) (M := M) (P0 := P0)
    hG hDM hMnormD hP0_der hcop (Or.inr hK_solv)
    (cor419ChiefFactorData_chiefSeriesInside_of_nilpotent
      (M := ↥(L ⊓ M))
      (K := ((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) : Subgroup ↥(L ⊓ M)))
      (odd_card_subgroup_of_odd hG.odd (L ⊓ M)) hKnilp hK_rank)

/-- Lemma 9.5's concrete local centralizer step for
`D = O_{p'}(F(M))`.  If the local `(9.10)` inclusion puts a `p`-subgroup `P₀`
inside `(L ∩ M)'`, then Corollary 4.19 and Lemma 1.9 force `P₀` to centralize
`O_{p'}(F(M)) ∩ L`. -/
private theorem le_centralizer_inf_opiCoreFitting_of_pSubgroup_local_derived
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M L P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hL : L ∈ maximalSubgroups G) (hLM : L ≠ M)
    (hP0p : IsPGroup p ↥P0) (hP0_der : P0 ≤ derivedInG (L ⊓ M)) :
    P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M) ⊓ L : Subgroup G) : Set G) := by
  classical
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  let H : Subgroup G := L ⊓ M
  let K : Subgroup G := D ⊓ L
  have hD_le_F : D ≤ S08.fittingInG M := by
    simpa [D] using opiCoreInG_le ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  have hDM : D ≤ M := hD_le_F.trans (S08.fittingInG_le M)
  have hM_norm_F : M ≤ Subgroup.normalizer (S08.fittingInG M : Set G) := by
    intro x hxM
    exact S08.mem_normalizer_fittingInG_of_mem hxM
  have hMnormD : M ≤ Subgroup.normalizer (D : Set G) := by
    simpa [D] using le_normalizer_opiCoreInG_of_le_normalizer ({p} : Set ℕ)ᶜ hM_norm_F
  have hK_le_H : K ≤ H := by
    refine le_inf inf_le_right ?_
    exact inf_le_left.trans hDM
  have hP0H : P0 ≤ H := by
    simpa [H] using hP0_der.trans (derivedInG_le_self (L ⊓ M))
  have hD_nilp : Group.IsNilpotent ↥D := by
    haveI : Group.IsNilpotent ↥(S08.fittingInG M) := S08.fittingInG_isNilpotent M
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hD_le_F)
  have hK_nilp_ambient : Group.IsNilpotent ↥K := by
    haveI : Group.IsNilpotent ↥D := hD_nilp
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe inf_le_left)
  have hK_nilp :
      Group.IsNilpotent ↥((K.subgroupOf H : Subgroup ↥H)) := by
    haveI : Group.IsNilpotent ↥K := hK_nilp_ambient
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK_le_H).symm
  have hK_rank_ambient : rank ↥K ≤ 2 := by
    simpa [D, K] using
      (rank_inf_opiCoreFitting_le_two_of_distinct_maximals
        (G := G) (p := p) hG hM hL hLM)
  have hK_rank : rank ↥(K.subgroupOf H) ≤ 2 :=
    (rank_subgroupOf_le_of_le hK_le_H).trans hK_rank_ambient
  have hP0p_local : IsPGroup p ↥(P0.subgroupOf H) :=
    hP0p.of_equiv (Subgroup.subgroupOfEquivOfLe hP0H).symm
  have hP0pi : Subgroup.IsPiSubgroup ({p} : Set ℕ) (P0.subgroupOf H) :=
    isPiSubgroup_singleton_of_isPGroup hP0p_local
  have hDpic : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ D := by
    simpa [D] using isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  have hKpic_ambient : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ K := by
    intro r hr
    exact hDpic r
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_left) Nat.card_pos.ne' hr)
  have hKpic : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ (K.subgroupOf H) :=
    isPiSubgroup_subgroupOf_of_le hK_le_H hKpic_ambient
  have hcop : (Nat.card ↥(P0.subgroupOf H)).Coprime (Nat.card ↥(K.subgroupOf H)) :=
    coprime_card_of_isPiSubgroup_of_isPiSubgroup_compl hP0pi hKpic
  haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  haveI hHsolv : IsSolvable ↥H :=
    solvable_of_solvable_injective (f := Subgroup.inclusion (inf_le_right : H ≤ M))
      (Subgroup.inclusion_injective (inf_le_right : H ≤ M))
  simpa [D, H, K] using
    (le_centralizer_inf_of_local_nilpotent_rank_chain
      (D := D) (L := L) (M := M) (P0 := P0)
      hG hDM hMnormD (by simpa [H] using hP0_der) hcop hK_nilp hK_rank)

/-- Lemma 9.5's final contradiction for a fixed cocyclic witness `B` and
maximal subgroup `L`: the local `(9.10)` inclusion and Corollary 4.19 force
`P₀` to centralize the subgroup whose noncentralization selected `B`. -/
private theorem false_of_not_le_centralizer_inf_centralizer_opiCoreFitting_witness
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A B M L P P0 : Subgroup G} {y : G}
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (hBA : B ≤ A) (hyB : y ∈ B)
    (hL : L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)))
    (hM : M ∈ maximalSubgroups G) (hLM : L ≠ M)
    (hPp : IsPGroup p ↥P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (hP0p : IsPGroup p ↥P0)
    (hP0N : P0 ≤ derivedInG (Subgroup.normalizer (P : Set G)))
    (hnot_cent : ¬ P0 ≤ Subgroup.centralizer
      (((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) ⊓
          Subgroup.centralizer (B : Set G)) : Set G)) :
    False := by
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  have hP0_der : P0 ≤ derivedInG (L ⊓ M) :=
    p0_le_derivedInG_inf_of_scn3_witness_maximal
      hG hA hAnot (hBA hyB) hL hPp hAP hPnormA hNPM hP0N
  have hcentDL : P0 ≤ Subgroup.centralizer ((D ⊓ L : Subgroup G) : Set G) := by
    simpa [D] using
      (le_centralizer_inf_opiCoreFitting_of_pSubgroup_local_derived
        (G := G) (p := p) hG hM hL.1 hLM hP0p hP0_der)
  have hcentDB : P0 ≤ Subgroup.centralizer
      (((D ⊓ Subgroup.centralizer (B : Set G) : Subgroup G)) : Set G) :=
    le_centralizer_inf_centralizer_of_le_centralizer_inf_maximal
      (D := D) hyB hL hcentDL
  exact hnot_cent (by simpa [D] using hcentDB)

/-- Lemma 9.5's `P₀` centralizes `O_{p'}(F(M))` bridge.  Assuming the existing
normalizer package for `P`, and characteristic Sylow-series packages for the
witness maximal subgroups produced by Theorem 9.1, the Prop. 1.16 witness
argument cannot find a noncentralized cocyclic centralizer. -/
private theorem p0_le_centralizer_opiCoreFitting_of_pSubgroup_normalizer_package
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M P P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (hPp : IsPGroup p ↥P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (hP0p : IsPGroup p ↥P0)
    (hP0N : P0 ≤ derivedInG (Subgroup.normalizer (P : Set G))) :
    P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G) := by
  classical
  by_contra hP0D
  obtain ⟨B, y, L, _hBea, _hBnot, _hBΩ, hBA, _hBnc, _hcyc,
      hnot_cent, hyB, _hy1, _hCGnotM, hL, _hLA, hLM⟩ :=
    exists_nonU_cocyclic_omega1_witness_maximal_ne
      hG hAcomm_set hM hA hAnot hP0D
  exact false_of_not_le_centralizer_inf_centralizer_opiCoreFitting_witness
    hG hA hAnot hBA hyB hL hM.1 hLM hPp hAP hPnormA hNPM hP0p hP0N hnot_cent

/-- If a rank-three abelian subgroup of `F(M)` centralizes a nontrivial `P₀ ≤ M`,
then `N_G(P₀)` is uniquely maximal, with unique maximal subgroup `M`.

This is the high-rank bookkeeping used in BG Lemma 9.5 after `(9.11)`: Lemma 9.4
puts the rank-three witness in `𝒰`, and every maximal subgroup over `N_G(P₀)`
also contains that witness. -/
private theorem normalizer_isUniquelyMaximal_and_le_maximal_of_rank_three_fitting_witness
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime]
    {M U P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hUab : IsMulCommutative U) (hUq : IsPGroup q U) (hUrank : 3 ≤ rank ↥U)
    (hUF : U ≤ S08.fittingInG M)
    (hUcentP0 : U ≤ Subgroup.centralizer (P0 : Set G))
    (hP0M : P0 ≤ M) (hP0ne : P0 ≠ ⊥) :
    IsUniquelyMaximal (Subgroup.normalizer (P0 : Set G)) ∧
      Subgroup.normalizer (P0 : Set G) ≤ M := by
  classical
  let N0 : Subgroup G := Subgroup.normalizer (P0 : Set G)
  have h3Uq : 3 ≤ pRank ↥U q :=
    three_le_pRank_of_isPGroup_of_three_le_rank hUq hUrank
  have h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q :=
    h3Uq.trans
      (pRank_le_of_injective (f := Subgroup.inclusion hUF)
        (Subgroup.inclusion_injective hUF))
  have hUU : IsUniquelyMaximal U :=
    (abelian_rank_three_isUniquelyMaximal_of_fitting hG hM h3Fq)
      U hUab hUq hUrank
  have hUM : U ≤ M := hUF.trans (S08.fittingInG_le M)
  have hU_le_N0 : U ≤ N0 :=
    hUcentP0.trans (Subgroup.centralizer_le_normalizer (P0 : Set G))
  have hN0lt : N0 < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hN0top
    haveI : P0.Normal := Subgroup.normalizer_eq_top_iff.mp hN0top
    rcases hG.simple.eq_bot_or_eq_top_of_normal P0 inferInstance with hP0bot | hP0top
    · exact hP0ne hP0bot
    · have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        rw [← hP0top]
        exact hP0M
      exact (mem_maximalSubgroups.mp hM).lt_top.ne (eq_top_iff.mpr htop_le_M)
  obtain ⟨N, hNco, hN0N⟩ :=
    (eq_top_or_exists_le_coatom N0).resolve_left hN0lt.ne
  have hUN : U ≤ N := hU_le_N0.trans hN0N
  have hN_eq_M : N = M :=
    hUU.eq_of_isCoatom_of_le hNco hUN (mem_maximalSubgroups.mp hM) hUM
  have hN0M : N0 ≤ M := hN0N.trans (le_of_eq hN_eq_M)
  have hN0U : IsUniquelyMaximal N0 :=
    IsUniquelyMaximal.of_unique_maximal hN0lt hM hN0M
      (fun N hNco hN0N => by
        have hUN : U ≤ N := hU_le_N0.trans hN0N
        exact hUU.eq_of_isCoatom_of_le hNco hUN (mem_maximalSubgroups.mp hM) hUM)
  exact ⟨hN0U, hN0M⟩

/-- If a rank-three abelian subgroup of `F(M)` centralizes a nontrivial `P₀ ≤ M`,
then uniqueness forces `N_G(P₀) ≤ M`. -/
private theorem normalizer_le_maximal_of_rank_three_fitting_centralizer_witness
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime]
    {M U P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hUab : IsMulCommutative U) (hUq : IsPGroup q U) (hUrank : 3 ≤ rank ↥U)
    (hUF : U ≤ S08.fittingInG M)
    (hUcentP0 : U ≤ Subgroup.centralizer (P0 : Set G))
    (hP0M : P0 ≤ M) (hP0ne : P0 ≠ ⊥) :
    Subgroup.normalizer (P0 : Set G) ≤ M :=
  (normalizer_isUniquelyMaximal_and_le_maximal_of_rank_three_fitting_witness
    hG hM hUab hUq hUrank hUF hUcentP0 hP0M hP0ne).2

/-- The same normalizer-control bridge specialized to
`D = O_{p'}(F(M))`. -/
private theorem normalizer_le_maximal_of_rank_three_opiCoreFitting_centralizer_witness
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact q.Prime]
    {M U P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hUab : IsMulCommutative U) (hUq : IsPGroup q U) (hUrank : 3 ≤ rank ↥U)
    (hUD : U ≤ opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M))
    (hP0centD : P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G))
    (hP0M : P0 ≤ M) (hP0ne : P0 ≠ ⊥) :
    Subgroup.normalizer (P0 : Set G) ≤ M := by
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  have hDcentP0 : D ≤ Subgroup.centralizer (P0 : Set G) := by
    simpa [D] using (Subgroup.le_centralizer_iff.mp hP0centD)
  exact normalizer_le_maximal_of_rank_three_fitting_centralizer_witness
    hG hM hUab hUq hUrank
    (hUD.trans (by simpa [D] using opiCoreInG_le ({p} : Set ℕ)ᶜ (S08.fittingInG M)))
    (hUD.trans hDcentP0) hP0M hP0ne

/-- The same uniquely-maximal normalizer bridge specialized to
`D = O_{p'}(F(M))`. -/
private theorem normalizer_isUniquelyMaximal_and_le_maximal_of_rank_three_opiCoreFitting_witness
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact q.Prime]
    {M U P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hUab : IsMulCommutative U) (hUq : IsPGroup q U) (hUrank : 3 ≤ rank ↥U)
    (hUD : U ≤ opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M))
    (hP0centD : P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G))
    (hP0M : P0 ≤ M) (hP0ne : P0 ≠ ⊥) :
    IsUniquelyMaximal (Subgroup.normalizer (P0 : Set G)) ∧
      Subgroup.normalizer (P0 : Set G) ≤ M := by
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  have hDcentP0 : D ≤ Subgroup.centralizer (P0 : Set G) := by
    simpa [D] using (Subgroup.le_centralizer_iff.mp hP0centD)
  exact normalizer_isUniquelyMaximal_and_le_maximal_of_rank_three_fitting_witness
    hG hM hUab hUq hUrank
    (hUD.trans (by simpa [D] using opiCoreInG_le ({p} : Set ℕ)ᶜ (S08.fittingInG M)))
    (hUD.trans hDcentP0) hP0M hP0ne

/-- A high `q`-rank inside `D = O_{p'}(F(M))` supplies the rank-three witness
needed to force `N_G(P₀) ≤ M`.

This packages the high-rank half of BG Lemma 9.5's `(9.12)` after `P₀` has
been shown to centralize `D`. -/
private theorem normalizer_le_maximal_of_three_le_pRank_opiCoreFitting_centralizer
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact q.Prime]
    {M P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (h3Dq : 3 ≤ pRank
      ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) q)
    (hP0centD : P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G))
    (hP0M : P0 ≤ M) (hP0ne : P0 ≠ ⊥) :
    Subgroup.normalizer (P0 : Set G) ≤ M := by
  classical
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  obtain ⟨U, hUmax, hUrank⟩ :=
    exists_isMaxElemAbelianIn_rank_three_of_three_le_pRank
      (H := D) (by simpa [D] using h3Dq)
  have hUea : U.IsElementaryAbelian q :=
    S08.isMaxElemAbelianIn_isElementaryAbelian hUmax
  exact normalizer_le_maximal_of_rank_three_opiCoreFitting_centralizer_witness
    hG hM (IsMulCommutative.of_comm hUea.comm) hUea.isPGroup hUrank
    (by simpa [D] using S08.isMaxElemAbelianIn_le hUmax)
    hP0centD hP0M hP0ne

/-- High `q`-rank version of the `(9.12)` singleton package. -/
private theorem normalizer_isUniquelyMaximal_and_le_maximal_of_three_le_pRank_opiCoreFitting
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact q.Prime]
    {M P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (h3Dq : 3 ≤ pRank
      ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) q)
    (hP0centD : P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G))
    (hP0M : P0 ≤ M) (hP0ne : P0 ≠ ⊥) :
    IsUniquelyMaximal (Subgroup.normalizer (P0 : Set G)) ∧
      Subgroup.normalizer (P0 : Set G) ≤ M := by
  classical
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  obtain ⟨U, hUmax, hUrank⟩ :=
    exists_isMaxElemAbelianIn_rank_three_of_three_le_pRank
      (H := D) (by simpa [D] using h3Dq)
  have hUea : U.IsElementaryAbelian q :=
    S08.isMaxElemAbelianIn_isElementaryAbelian hUmax
  exact normalizer_isUniquelyMaximal_and_le_maximal_of_rank_three_opiCoreFitting_witness
    hG hM (IsMulCommutative.of_comm hUea.comm) hUea.isPGroup hUrank
    (by simpa [D] using S08.isMaxElemAbelianIn_le hUmax)
    hP0centD hP0M hP0ne

/-- Rank-three `D = O_{p'}(F(M))` form of the normalizer-control bridge. -/
private theorem normalizer_le_maximal_of_three_le_rank_opiCoreFitting_centralizer
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (h3D : 3 ≤ rank
      ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)))
    (hP0centD : P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G))
    (hP0M : P0 ≤ M) (hP0ne : P0 ≠ ⊥) :
    Subgroup.normalizer (P0 : Set G) ≤ M := by
  classical
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  obtain ⟨q, hq, h3Dq⟩ :=
    exists_pRank_ge_of_pos_le_rank (G := ↥D) (n := 3) (by norm_num)
      (by simpa [D] using h3D)
  haveI : Fact q.Prime := ⟨hq⟩
  exact normalizer_le_maximal_of_three_le_pRank_opiCoreFitting_centralizer
    (G := G) (p := p) (q := q) hG hM (by simpa [D] using h3Dq)
    hP0centD hP0M hP0ne

/-- Rank-three `D = O_{p'}(F(M))` singleton form of the normalizer-control bridge. -/
private theorem normalizer_isUniquelyMaximal_and_le_maximal_of_three_le_rank_opiCoreFitting
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (h3D : 3 ≤ rank
      ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)))
    (hP0centD : P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G))
    (hP0M : P0 ≤ M) (hP0ne : P0 ≠ ⊥) :
    IsUniquelyMaximal (Subgroup.normalizer (P0 : Set G)) ∧
      Subgroup.normalizer (P0 : Set G) ≤ M := by
  classical
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  obtain ⟨q, hq, h3Dq⟩ :=
    exists_pRank_ge_of_pos_le_rank (G := ↥D) (n := 3) (by norm_num)
      (by simpa [D] using h3D)
  haveI : Fact q.Prime := ⟨hq⟩
  exact normalizer_isUniquelyMaximal_and_le_maximal_of_three_le_pRank_opiCoreFitting
    (G := G) (p := p) (q := q) hG hM (by simpa [D] using h3Dq)
    hP0centD hP0M hP0ne

/-- Contrapositive rank squeeze for BG Lemma 9.5's `(9.12)`: once `P₀`
centralizes `D = O_{p'}(F(M))`, failure of `N_G(P₀) ≤ M` forces `rank D ≤ 2`. -/
private theorem rank_opiCoreFitting_le_two_of_centralizer_of_not_normalizer_le
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hP0centD : P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G))
    (hP0M : P0 ≤ M) (hP0ne : P0 ≠ ⊥)
    (hnot : ¬ Subgroup.normalizer (P0 : Set G) ≤ M) :
    rank ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) ≤ 2 := by
  by_contra hrank
  have h3D : 3 ≤ rank
      ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) := by
    omega
  exact hnot
    (normalizer_le_maximal_of_three_le_rank_opiCoreFitting_centralizer
      hG hM h3D hP0centD hP0M hP0ne)

/-- Lemma 9.5 `(9.12)` high-rank package: the previously established
normalizer package for `P` first makes `P₀` centralize `D = O_{p'}(F(M))`;
if `rank D ≥ 3`, uniqueness of a rank-three witness in `D` forces `N_G(P₀) ≤ M`. -/
private theorem normalizer_p0_le_maximal_of_high_rank_opiCoreFitting_package
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M P P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (hPp : IsPGroup p ↥P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (hP0p : IsPGroup p ↥P0)
    (hP0N : P0 ≤ derivedInG (Subgroup.normalizer (P : Set G)))
    (hP0ne : P0 ≠ ⊥)
    (h3D : 3 ≤ rank
      ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)))
    :
    Subgroup.normalizer (P0 : Set G) ≤ M := by
  have hP0M : P0 ≤ M :=
    (hP0N.trans (derivedInG_le_self (Subgroup.normalizer (P : Set G)))).trans hNPM
  have hP0centD : P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G) :=
    p0_le_centralizer_opiCoreFitting_of_pSubgroup_normalizer_package
      hG hAcomm_set hM hA hAnot hPp hAP hPnormA hNPM hP0p hP0N
  exact normalizer_le_maximal_of_three_le_rank_opiCoreFitting_centralizer
    hG hM.1 h3D hP0centD hP0M hP0ne

/-- Lemma 9.5 `(9.12)` high-rank singleton package.  Under the normalizer data for
`P` and `P₀`, if `rank O_{p'}(F(M)) ≥ 3`, then `N_G(P₀)` itself lies in `𝒰` and
its unique maximal subgroup is `M`. -/
private theorem normalizer_p0_isUniquelyMaximal_and_le_maximal_of_high_rank_package
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M P P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (hPp : IsPGroup p ↥P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (hP0p : IsPGroup p ↥P0)
    (hP0N : P0 ≤ derivedInG (Subgroup.normalizer (P : Set G)))
    (hP0ne : P0 ≠ ⊥)
    (h3D : 3 ≤ rank
      ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)))
    :
    IsUniquelyMaximal (Subgroup.normalizer (P0 : Set G)) ∧
      Subgroup.normalizer (P0 : Set G) ≤ M := by
  have hP0M : P0 ≤ M :=
    (hP0N.trans (derivedInG_le_self (Subgroup.normalizer (P : Set G)))).trans hNPM
  have hP0centD : P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G) :=
    p0_le_centralizer_opiCoreFitting_of_pSubgroup_normalizer_package
      hG hAcomm_set hM hA hAnot hPp hAP hPnormA hNPM hP0p hP0N
  exact normalizer_isUniquelyMaximal_and_le_maximal_of_three_le_rank_opiCoreFitting
    hG hM.1 h3D hP0centD hP0M hP0ne

/-- Low-rank `(9.12)` maximality core: once the low-rank argument has shown
`M ≤ N_G(P₀)`, the nontriviality of `P₀ ≤ M` makes `N_G(P₀)` proper, so maximality
of `M` forces `N_G(P₀) = M` and hence `N_G(P₀) ∈ 𝒰`. -/
private theorem normalizer_isUniquelyMaximal_and_eq_maximal_of_maximal_le_normalizer
    [Finite G] (hG : IsMinimalSimpleOdd G) {M P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP0M : P0 ≤ M) (hP0ne : P0 ≠ ⊥)
    (hMnormP0 : M ≤ Subgroup.normalizer (P0 : Set G)) :
    IsUniquelyMaximal (Subgroup.normalizer (P0 : Set G)) ∧
      Subgroup.normalizer (P0 : Set G) = M := by
  classical
  let N0 : Subgroup G := Subgroup.normalizer (P0 : Set G)
  have hMco : IsCoatom M := mem_maximalSubgroups.mp hM
  have hN0lt : N0 < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hN0top
    haveI : P0.Normal := Subgroup.normalizer_eq_top_iff.mp hN0top
    rcases hG.simple.eq_bot_or_eq_top_of_normal P0 inferInstance with hP0bot | hP0top
    · exact hP0ne hP0bot
    · have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        rw [← hP0top]
        exact hP0M
      exact hMco.lt_top.ne (eq_top_iff.mpr htop_le_M)
  have hN0leM : N0 ≤ M :=
    (isCoatom_iff_ge_of_le.mp hMco).2 N0 hN0lt.ne hMnormP0
  have hN0eqM : N0 = M := le_antisymm hN0leM hMnormP0
  have hN0U : IsUniquelyMaximal N0 := by
    refine IsUniquelyMaximal.of_unique_maximal hN0lt hM (le_of_eq hN0eqM) ?_
    intro N hNco hN0N
    have hMN : M ≤ N := (le_of_eq hN0eqM.symm).trans hN0N
    have hNleM : N ≤ M :=
      (isCoatom_iff_ge_of_le.mp hMco).2 N hNco.lt_top.ne hMN
    exact le_antisymm hNleM hMN
  exact ⟨by simpa [N0] using hN0U, by simpa [N0] using hN0eqM⟩

/-- Contrapositive form of the `(9.12)` high-rank package.  Once the Lemma 9.5
normalizer data for `P` and `P₀` is available, failure of `N_G(P₀) ≤ M` forces
`rank O_{p'}(F(M)) ≤ 2`. -/
private theorem rank_opiCoreFitting_le_two_of_pSubgroup_normalizer_package
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M P P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (hPp : IsPGroup p ↥P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (hP0p : IsPGroup p ↥P0)
    (hP0N : P0 ≤ derivedInG (Subgroup.normalizer (P : Set G)))
    (hP0ne : P0 ≠ ⊥)
    (hnot : ¬ Subgroup.normalizer (P0 : Set G) ≤ M)
    :
    rank ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) ≤ 2 := by
  by_contra hrank
  have h3D : 3 ≤ rank
      ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) := by
    omega
  exact hnot
    (normalizer_p0_le_maximal_of_high_rank_opiCoreFitting_package
      hG hAcomm_set hM hA hAnot hPp hAP hPnormA hNPM hP0p hP0N
      hP0ne h3D)

/-- BG Lemma 9.5 (9.9)→`P₀ ≠ 1`: for a Sylow `p`-subgroup `P` of the minimal simple odd group `G`
(with `p ∣ |G|`), `P₀ = ⁅P, N_G(P)⁆ ≠ 1`.  If `P₀ = 1` then `N_G(P) ≤ C_G(P)`, so Burnside
(Theorem 1.18) gives a normal `p`-complement `N`; simplicity forces `N = ⊥` (⇒ `G` a `p`-group,
hence solvable — impossible) or `N = ⊤` (⇒ `P = ⊥`, so `p ∤ |G|`). -/
private theorem commutator_normalizer_ne_bot_of_isSylow [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp_dvd : p ∣ Nat.card G) :
    ⁅(P : Subgroup G), Subgroup.normalizer ((P : Subgroup G) : Set G)⁆ ≠ ⊥ := by
  classical
  intro h
  have hNC : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((P : Subgroup G) : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h
  obtain ⟨N, hNnorm, hNcompl⟩ :=
    OddOrder.Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer P hNC
  rcases hG.simple.eq_bot_or_eq_top_of_normal N hNnorm with hNbot | hNtop
  · -- `N = ⊥` ⇒ `P = ⊤` ⇒ `G` is a `p`-group ⇒ solvable, contradicting `hG`.
    have hPtop : (P : Subgroup G) = ⊤ :=
      Subgroup.isComplement'_bot_left.mp (hNbot ▸ hNcompl P)
    have hGp : IsPGroup p G :=
      (hPtop ▸ P.isPGroup' : IsPGroup p ↥(⊤ : Subgroup G)).of_equiv Subgroup.topEquiv
    haveI := hGp.isNilpotent
    exact hG.notSolvable inferInstance
  · -- `N = ⊤` ⇒ `P = ⊥` ⇒ `p ∤ |G|`, contradicting `hp_dvd`.
    have hPbot : (P : Subgroup G) = ⊥ :=
      Subgroup.isComplement'_top_left.mp (hNtop ▸ hNcompl P)
    have hcard : Nat.card ↥(P : Subgroup G) = p ^ (Nat.card G).factorization p :=
      P.card_eq_multiplicity
    rw [hPbot, Subgroup.card_bot] at hcard
    have hfact0 : (Nat.card G).factorization p = 0 :=
      (Nat.pow_eq_one.mp hcard.symm).resolve_left (Fact.out : p.Prime).ne_one
    exact ((Fact.out : p.Prime).factorization_pos_of_dvd Nat.card_pos.ne' hp_dvd).ne' hfact0

/-- In a finite nilpotent group `N`, the `q`-rank for `q ≠ p` is realized inside the `p'`-core
`O_{p'}(N)` (the `q`-Sylow is normal, a `{r ≠ p}`-group, hence lies in `O_{p'}(N)`). -/
private theorem pRank_le_pRank_oPiCore_compl_of_nilpotent
    {N : Type*} [Group N] [Finite N] [Group.IsNilpotent N] {p q : ℕ} [Fact q.Prime] (hqp : q ≠ p) :
    pRank N q ≤ pRank ↥(Ch03.oPiCore {r : ℕ | r ≠ p} N) q := by
  classical
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow q N))
  have hiff : Group.IsNilpotent N ↔
      ∀ (p' : ℕ) (_hp : Fact p'.Prime) (P : Sylow p' N), (↑P : Subgroup N).Normal :=
    (Group.isNilpotent_of_finite_tfae (G := N)).out 0 3
  haveI hSnorm : (S : Subgroup N).Normal := hiff.mp inferInstance q inferInstance S
  have hSpi : Ch03.Subgroup.IsPiGroup {r : ℕ | r ≠ p} (S : Subgroup N) := by
    intro r hr
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    rw [hk, Nat.mem_primeFactors] at hr
    have hrq : r = q :=
      (Nat.prime_dvd_prime_iff_eq hr.1 (Fact.out : q.Prime)).mp (hr.1.dvd_of_dvd_pow hr.2.1)
    show r ≠ p
    rw [hrq]; exact hqp
  have hScore : (S : Subgroup N) ≤ Ch03.oPiCore {r : ℕ | r ≠ p} N := hSpi.le_oPiCore
  calc pRank N q = pRank ↥(S : Subgroup N) q := (pRank_sylow_eq S).symm
    _ ≤ pRank ↥(Ch03.oPiCore {r : ℕ | r ≠ p} N) q :=
        pRank_le_of_injective (Subgroup.inclusion_injective hScore)

/-- If `r_p(F(M)) ≤ 2` and the `p'`-core `O_{p'}(F(M))` has rank ≤ 2, then `F(M)` itself has
rank ≤ 2 (for `q ≠ p`, `F(M)`'s `q`-rank lives in `O_{p'}(F(M))` since `F(M)` is nilpotent). -/
private theorem rank_fitting_subtype_le_two_of_low_rank
    [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hp : pRank ↥(S08.fittingInG M) p ≤ 2)
    (hp' : rank ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) ≤ 2) :
    rank ↥(Ch01.fitting ↥M) ≤ 2 := by
  classical
  haveI : Group.IsNilpotent ↥(S08.fittingInG M) := S08.fittingInG_isNilpotent M
  have hcompl : (({p} : Set ℕ)ᶜ) = {r : ℕ | r ≠ p} := by
    ext r; simp [Set.mem_compl_iff, Set.mem_singleton_iff]
  refine (rank_le_of_injective
    (f := (Subgroup.equivMapOfInjective (Ch01.fitting ↥M) M.subtype
      M.subtype_injective).toMonoidHom)
    (Subgroup.equivMapOfInjective _ _ M.subtype_injective).injective).trans ?_
  rw [rank_le_iff]
  intro q hq
  haveI : Fact q.Prime := ⟨hq⟩
  by_cases hqp : q = p
  · subst hqp; exact hp
  · have h1 : pRank ↥(S08.fittingInG M) q ≤
        pRank ↥(Ch03.oPiCore {r : ℕ | r ≠ p} ↥(S08.fittingInG M)) q :=
      pRank_le_pRank_oPiCore_compl_of_nilpotent hqp
    have h2 : pRank ↥(Ch03.oPiCore {r : ℕ | r ≠ p} ↥(S08.fittingInG M)) q ≤
        pRank ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) q := by
      rw [← hcompl]
      exact pRank_le_of_injective
        (f := (Subgroup.equivMapOfInjective (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥(S08.fittingInG M))
          (S08.fittingInG M).subtype (S08.fittingInG M).subtype_injective).toMonoidHom)
        (Subgroup.equivMapOfInjective _ _ (S08.fittingInG M).subtype_injective).injective
    exact (h1.trans h2).trans ((pRank_le_rank q).trans hp')

/-- BG Lemma 9.5 low-rank, the `M'' ≤ F(M')` step (BG L2615 "By Theorem 4.20, M''⊆F"): a maximal
`M` of the minimal simple odd `G` with `r_p(F(M)) ≤ 2` and `rank O_{p'}(F(M)) ≤ 2` (so
`rank F(M) ≤ 2`) satisfies `M' ≤ F(M)` in `G`-coordinates. -/
private theorem derivedInG_le_fittingInG_of_low_rank
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hAM : A ≤ M) (hAne : A ≠ ⊥)
    (hp : pRank ↥(S08.fittingInG M) p ≤ 2)
    (hp' : rank ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) ≤ 2) :
    derivedInG M ≤ S08.fittingInG M := by
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  haveI : Nontrivial ↥M :=
    (Subgroup.nontrivial_iff_ne_bot M).mpr fun hM0 => hAne (le_bot_iff.mp (hM0 ▸ hAM))
  have hoddM : Odd (Nat.card ↥M) := by
    rcases Nat.even_or_odd (Nat.card ↥M) with he | ho
    · exact absurd (he.two_dvd.trans (Subgroup.card_subgroup_dvd_card M))
        (by have := hG.odd; rw [Nat.odd_iff] at this; omega)
    · exact ho
  have hderiv : commutator ↥M ≤ Ch01.fitting ↥M :=
    OddOrder.BG.Ch1.S05.derived_le_fitting_of_rank_fitting_le_two hoddM
      (rank_fitting_subtype_le_two_of_low_rank hp hp')
  exact Subgroup.map_mono hderiv

/-- If `g` normalizes `K`, then conjugation by `g` fixes `K` setwise. -/
private theorem map_conj_eq_self_of_mem_normalizer {g : G} {K : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    K.map (MulAut.conj g).toMonoidHom = K := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg z).mp hz
  · intro hy
    exact ⟨g⁻¹ * y * g, (Subgroup.mem_normalizer_iff''.mp hg y).mp hy, by group⟩

/-- `N_G(H)` normalizes the commutator `⁅H, N_G(H)⁆`: conjugation by an element of
`N_G(H)` fixes both `H` and `N_G(H)`, hence fixes their commutator. -/
private theorem normalizer_le_normalizer_commutator_normalizer (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer
        ((⁅H, Subgroup.normalizer (H : Set G)⁆ : Subgroup G) : Set G) := by
  intro g hg
  have key : (⁅H, Subgroup.normalizer (H : Set G)⁆).map (MulAut.conj g).toMonoidHom
      = ⁅H, Subgroup.normalizer (H : Set G)⁆ := by
    rw [Subgroup.map_commutator, map_conj_eq_self_of_mem_normalizer hg,
      map_conj_eq_self_of_mem_normalizer (Subgroup.le_normalizer hg)]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hmem : (MulAut.conj g) h ∈
        (⁅H, Subgroup.normalizer (H : Set G)⁆).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
    rw [key] at hmem
    simpa [MulAut.conj_apply] using hmem
  · intro hh
    have hmem : (MulAut.conj g) h ∈ ⁅H, Subgroup.normalizer (H : Set G)⁆ := by
      simpa [MulAut.conj_apply] using hh
    rw [← key, Subgroup.mem_map] at hmem
    obtain ⟨z, hz, hzeq⟩ := hmem
    have hzh : z = h := (MulAut.conj g).injective (by
      simpa [MulEquiv.coe_toMonoidHom] using hzeq)
    rwa [hzh] at hz

/-- A finite nilpotent group is generated by its `p`-core and its `p'`-core. -/
private theorem top_le_oPiCore_singleton_sup_compl_of_isNilpotent
    {K : Type*} [Group K] [Finite K] [Group.IsNilpotent K] (p : ℕ) :
    (⊤ : Subgroup K) ≤
      Ch03.oPiCore ({p} : Set ℕ) K ⊔ Ch03.oPiCore (({p} : Set ℕ)ᶜ) K := by
  classical
  have hfit : Ch01.fitting K = ⊤ := by
    refine top_le_iff.mp ?_
    haveI : Group.IsNilpotent ↥(⊤ : Subgroup K) := Group.isNilpotent_top.mpr inferInstance
    exact Ch01.nilpotent_normal_le_fitting
  rw [← hfit, Ch01.fitting_eq_iSup_primeFactors]
  refine iSup_le fun q => ?_
  obtain ⟨qval, hq_mem⟩ := q
  haveI : Fact qval.Prime := ⟨(Nat.mem_primeFactors.mp hq_mem).1⟩
  rw [show (Ch01.opCore qval K) = Ch03.oPiCore ({qval} : Set ℕ) K from
      (Ch04.oPiCore_singleton_eq_opCore qval).symm]
  by_cases hqeq : qval = p
  · exact le_sup_of_le_left
      (Ch03.oPiCore_mono (Set.singleton_subset_iff.mpr (Set.mem_singleton_iff.mpr hqeq)) K)
  · exact le_sup_of_le_right
      (Ch03.oPiCore_mono
        (Set.singleton_subset_iff.mpr (Set.mem_compl_singleton_iff.mpr hqeq)) K)

/-- `F(M) ≤ O_p(F(M)) ⊔ O_{p'}(F(M))` in the ambient group: `F(M)` is nilpotent, so it
is generated by its `p`-core and `p'`-core. -/
private theorem fittingInG_le_opiCoreInG_sup_compl [Finite G] (p : ℕ) (M : Subgroup G) :
    S08.fittingInG M ≤ opiCoreInG ({p} : Set ℕ) (S08.fittingInG M)
      ⊔ opiCoreInG (({p} : Set ℕ)ᶜ) (S08.fittingInG M) := by
  classical
  haveI : Group.IsNilpotent ↥(S08.fittingInG M) := S08.fittingInG_isNilpotent M
  have hmap := Subgroup.map_mono (f := (S08.fittingInG M).subtype)
    (top_le_oPiCore_singleton_sup_compl_of_isNilpotent (K := ↥(S08.fittingInG M)) p)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  exact hmap

/-- **BG Lemma 9.5** (mmd L2559): `p` prime, `A ∈ SCN₃(p)` ⇒ `A ∈ 𝒰`。

Proof gate: mmd L2579 uses Thm 7.6 and Thm 7.4; L2605 uses Cor 4.19; L2615 uses
Thm 4.20. The `SCN₃(p)` input is the right interface, so no §5 narrow or Thm 4.16
assumption should be introduced here. -/
theorem scn3_isUniquelyMaximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    IsUniquelyMaximal A := by
  classical
  by_contra hAnot
  -- abelian + `p`-group data for `A`
  have hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val
      (isMulCommutative_iff.mp (isMulCommutative_of_mem_scn3Global hA) ⟨x, hx⟩ ⟨y, hy⟩)
  have hAp : IsPGroup p ↥A := isPGroup_of_mem_scn3Global hA
  have hAne : A ≠ ⊥ := ne_bot_of_mem_scn3Global hA
  have h3pRankA : 3 ≤ pRank ↥A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank hAp (three_le_rank_of_mem_scn3Global hA)
  have hA_le_C : A ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx; rw [Subgroup.mem_centralizer_iff]; intro y hy; exact (hAcomm_set y hy x hx)
  -- `p ∣ |G|`
  have hp_dvd : p ∣ Nat.card G := by
    haveI : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hAne
    obtain ⟨k, hk⟩ := hAp.exists_card_eq
    have hk1 : k ≠ 0 := by
      rintro rfl; rw [pow_zero] at hk; exact (Finite.one_lt_card (α := ↥A)).ne' hk
    exact (hk ▸ dvd_pow_self p hk1 : p ∣ Nat.card ↥A).trans (Subgroup.card_subgroup_dvd_card A)
  -- the Sylow `p`-subgroup `P` of `G` containing `A` (from `A ∈ SCN₃`), and `P₀ = ⁅P, N_G(P)⁆`
  obtain ⟨PG, hAPG, hSCN⟩ := S07.exists_sylow_of_mem_scn3Global hA
  set P : Subgroup G := (PG : Subgroup G) with hPdef
  have hPp : IsPGroup p ↥P := PG.isPGroup'
  have hAP : A ≤ P := hAPG
  have hPnormA : P ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAPG).mp hSCN.1.isNormal
  set P0 : Subgroup G := ⁅P, Subgroup.normalizer (P : Set G)⁆ with hP0def
  have hP0_le_P : P0 ≤ P := by
    rw [hP0def, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    have hbab : b * a⁻¹ * b⁻¹ ∈ P := ((Subgroup.mem_normalizer_iff.mp hb) a⁻¹).mp (P.inv_mem ha)
    have heq : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [heq]
    exact P.mul_mem ha hbab
  have hP0p : IsPGroup p ↥P0 := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    obtain ⟨j, _, hj⟩ :=
      (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (hk ▸ Subgroup.card_dvd_of_le hP0_le_P)
    exact IsPGroup.of_card hj
  have hP0N : P0 ≤ derivedInG (Subgroup.normalizer (P : Set G)) := by
    rw [hP0def, derivedInG_eq_commutator]
    exact Subgroup.commutator_mono Subgroup.le_normalizer le_rfl
  have hP0ne : P0 ≠ ⊥ := commutator_normalizer_ne_bot_of_isSylow hG PG hp_dvd
  -- key `(9.6)→(9.12)`: every maximal `M'` over `C_G(A)` is the unique maximal over `N_G(P₀)`
  have key : ∀ M' : Subgroup G,
      M' ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) →
        IsUniquelyMaximal (Subgroup.normalizer (P0 : Set G)) ∧
          Subgroup.normalizer (P0 : Set G) ≤ M' := by
    intro M' hM'
    have hNPM' : Subgroup.normalizer (P : Set G) ≤ M' :=
      (normalizer_scn3_pSubgroup_le_maximal_of_not_scn3 hG hM' hA hAnot hPp hAP hPnormA).2
    have hP0M' : P0 ≤ M' := hP0_le_P.trans (Subgroup.le_normalizer.trans hNPM')
    by_cases h3D : 3 ≤ rank ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M'))
    · exact normalizer_p0_isUniquelyMaximal_and_le_maximal_of_high_rank_package
        hG hAcomm_set hM' hA hAnot hPp hAP hPnormA hNPM' hP0p hP0N hP0ne h3D
    · -- low rank `(9.12)` (BG L2615-2619): `r(F(M')) ≤ 2` ⟹ by Thm 4.20 `M'' ≤ F(M')`, so
      -- `M' = O_{p'}(F(M'))·N_{M'}(P)`; `(9.11)` puts `O_{p'}(F(M'))` in `C_G(P₀)` and
      -- `N_{M'}(P) ≤ N_G(P) ≤ N_G(P₀)`, whence `P₀ ⊴ M'`, i.e. `M' ≤ N_G(P₀)`.
      -- TODO(§9 Phase B sub-assembly 2): the Frattini decomposition. `derived_le_fitting_of_rank_fitting_le_two`
      -- (Thm 4.20a) applies since `r_p(F)≤2` (here) + `r(O_{p'}(F))≤2` (¬h3D) ⟹ `rank F(M')≤2` (full).
      have hMN0 : M' ≤ Subgroup.normalizer (P0 : Set G) := by
        -- `(9.6)`: `r_p(F(M')) ≤ 2`, and `¬ h3D` gives `rank O_{p'}(F(M')) ≤ 2`.
        have hpr : pRank ↥(S08.fittingInG M') p ≤ 2 :=
          pRank_fittingInG_le_two_of_not_scn3_isUniquelyMaximal hG hM'.1 hA hAnot
        have hpr' : rank ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M')) ≤ 2 := by omega
        have hAM' : A ≤ M' := hA_le_C.trans hM'.2
        have hPM' : (P : Subgroup G) ≤ M' := Subgroup.le_normalizer.trans hNPM'
        -- Theorem 4.20(a) inside `↥M'`: `M'' ≤ F(M')`, i.e. `commutator ↥M' ≤ fitting ↥M'`.
        have hderiv : derivedInG M' ≤ S08.fittingInG M' :=
          derivedInG_le_fittingInG_of_low_rank hG hM'.1 hAM' hAne hpr hpr'
        have hcomm_le : commutator ↥M' ≤ Ch01.fitting ↥M' :=
          (Subgroup.map_le_map_iff_of_injective M'.subtype_injective).mp hderiv
        -- `P` as a Sylow `p`-subgroup of `↥M'`, and `FP = F(M') ⊔ P ⊴ M'`.
        let PM' : Sylow p ↥M' := PG.subtype hPM'
        have hPM'coe : (PM' : Subgroup ↥M') = (P : Subgroup G).subgroupOf M' :=
          PG.coe_subtype hPM'
        set FP : Subgroup ↥M' := Ch01.fitting ↥M' ⊔ (P : Subgroup G).subgroupOf M' with hFPdef
        have hcomm_FP : commutator ↥M' ≤ FP := by
          rw [hFPdef]; exact hcomm_le.trans le_sup_left
        haveI hFPnorm : FP.Normal :=
          Subgroup.Normal.of_commutator_le (G := ↥M') (H := FP) hcomm_FP
        have hPM'_le_FP : (PM' : Subgroup ↥M') ≤ FP := by rw [hPM'coe]; exact le_sup_right
        -- Frattini argument in `↥M'`: `N_{M'}(P) ⊔ FP = ⊤`.
        have hFrat : Subgroup.normalizer ((PM' : Subgroup ↥M') : Set ↥M') ⊔ FP = ⊤ :=
          Sylow.normalizer_sup_eq_top' PM' hPM'_le_FP
        -- `N_G(P) ≤ N_G(P₀)` (conjugation preserves `P₀ = ⁅P, N_G(P)⁆`), hence `P ≤ N_G(P₀)`.
        have hNP_NP0 : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤
            Subgroup.normalizer (P0 : Set G) :=
          normalizer_le_normalizer_commutator_normalizer (P : Subgroup G)
        have hP_NP0 : (P : Subgroup G) ≤ Subgroup.normalizer (P0 : Set G) :=
          Subgroup.le_normalizer.trans hNP_NP0
        -- `O_p(F(M')) ≤ P`: a normal `p`-subgroup of `↥M'` lies in the Sylow `P`.
        have hOp_le_P : opiCoreInG ({p} : Set ℕ) (S08.fittingInG M') ≤ (P : Subgroup G) := by
          set Op : Subgroup G := opiCoreInG ({p} : Set ℕ) (S08.fittingInG M') with hOpdef
          have hOp_le_M' : Op ≤ M' := (opiCoreInG_le _ _).trans (S08.fittingInG_le M')
          have hM'_norm_F : M' ≤ Subgroup.normalizer ((S08.fittingInG M') : Set G) :=
            fun x hx => S08.mem_normalizer_fittingInG_of_mem hx
          have hM'_norm_Op : M' ≤ Subgroup.normalizer (Op : Set G) :=
            le_normalizer_opiCoreInG_of_le_normalizer ({p} : Set ℕ) hM'_norm_F
          haveI hOpnorm : (Op.subgroupOf M').Normal :=
            (Subgroup.normal_subgroupOf_iff_le_normalizer hOp_le_M').mpr hM'_norm_Op
          have hOpp : IsPGroup p ↥(Op.subgroupOf M') :=
            (isPGroup_opiCoreInG_singleton (S08.fittingInG M')).comap_of_injective
              M'.subtype M'.subtype_injective
          have hsub : Op.subgroupOf M' ≤ (P : Subgroup G).subgroupOf M' := by
            rw [← hPM'coe]
            exact (Ch01.normal_pgroup_le_opCore hOpp).trans (Ch01.opCore_le PM')
          intro x hx
          have hxM' : x ∈ M' := hOp_le_M' hx
          have hmem : (⟨x, hxM'⟩ : ↥M') ∈ (P : Subgroup G).subgroupOf M' :=
            hsub (Subgroup.mem_subgroupOf.mpr hx)
          exact Subgroup.mem_subgroupOf.mp hmem
        -- `F(M') ≤ N_G(P₀)`: `O_p(F) ≤ P ≤ N_G(P₀)` and `O_{p'}(F) ≤ C_G(P₀) ≤ N_G(P₀)`.
        have hFle : S08.fittingInG M' ≤ Subgroup.normalizer (P0 : Set G) := by
          refine (fittingInG_le_opiCoreInG_sup_compl p M').trans (sup_le ?_ ?_)
          · exact hOp_le_P.trans hP_NP0
          · have h911 := p0_le_centralizer_opiCoreFitting_of_pSubgroup_normalizer_package
              hG hAcomm_set hM' hA hAnot hPp hAP hPnormA hNPM' hP0p hP0N
            exact (Subgroup.le_centralizer_iff.mp h911).trans
              (Subgroup.centralizer_le_normalizer _)
        -- transport the Frattini decomposition back to `G` and bound by `N_G(P₀)`.
        calc M' = (⊤ : Subgroup ↥M').map M'.subtype := by
                rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
          _ ≤ (Subgroup.normalizer ((PM' : Subgroup ↥M') : Set ↥M') ⊔ FP).map M'.subtype :=
                Subgroup.map_mono hFrat.ge
          _ = (Subgroup.normalizer ((PM' : Subgroup ↥M') : Set ↥M')).map M'.subtype
                ⊔ FP.map M'.subtype := Subgroup.map_sup _ _ _
          _ ≤ Subgroup.normalizer (P0 : Set G) := by
                refine sup_le ?_ ?_
                · rw [hPM'coe]
                  refine (Subgroup.le_normalizer_map M'.subtype).trans ?_
                  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPM']
                  exact hNP_NP0
                · rw [hFPdef, Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
                    inf_eq_left.mpr hPM']
                  exact sup_le hFle hP_NP0
      obtain ⟨hU, hEq⟩ :=
        normalizer_isUniquelyMaximal_and_eq_maximal_of_maximal_le_normalizer
          hG hM'.1 hP0M' hP0ne hMN0
      exact ⟨hU, le_of_eq hEq⟩
  obtain ⟨M, hM⟩ := exists_maximalSubgroupsContaining_centralizer_of_mem_scn3Global hG hA
  obtain ⟨hUniq, hN0M⟩ := key M hM
  -- final contradiction: `Ω₁(A) ∉ 𝒰` ⟹ Theorem 9.1 gives `x` with `C_G(x) ⊄ M`, so a maximal
  -- `M* ⊇ C_G(x)` lies in `𝓜(C_G(A))` and `M* ≠ M`; but `(9.12)` forces `M = M*`.
  set W : Subgroup G := OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set with hWdef
  have hWA : W ≤ A := fun x hx => OddOrder.GroupTheory.omega1OfAbelian_le hx
  have hWnot : ¬ IsUniquelyMaximal W :=
    not_isUniquelyMaximal_of_le_scn3_counterexample hG hAcomm_set hA hWA hAnot
  have hWea : W.IsElementaryAbelian p :=
    OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian (hH := hAcomm_set)
  have hWnc : ¬ IsCyclic ↥W :=
    not_isCyclic_omega1OfAbelian_of_three_le_pRank hAcomm_set h3pRankA
  have hWleM : W ≤ M := hWA.trans (hA_le_C.trans hM.2)
  have hncase := mt (noncyclic_isUniquelyMaximal_of_centralizer_le hG hM.1 hWea hWleM hWnc) hWnot
  rw [not_or] at hncase
  have hfirst := hncase.1
  push Not at hfirst
  obtain ⟨x, hxW, hx1, hxnotM⟩ := hfirst
  -- `Z(G) = ⊥`, hence `C_G(x) < ⊤`
  have hZbot : Subgroup.center G = ⊥ := by
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exact absurd (isSolvable_of_comm fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm) hG.notSolvable
  have hCxlt : Subgroup.centralizer ({x} : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hCtop
    have hxZ : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({x} : Set G) := by
        rw [hCtop]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg x (Set.mem_singleton x)).symm
    rw [hZbot, Subgroup.mem_bot] at hxZ
    exact hx1 hxZ
  obtain ⟨Mstar, hMstarCo, hCMstar⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.centralizer ({x} : Set G))).resolve_left hCxlt.ne
  have hMstarA : Mstar ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) :=
    maximalSubgroupsContaining_centralizer_of_mem_centralizer_singleton (hWA hxW)
      ⟨hMstarCo, hCMstar⟩
  obtain ⟨_, hN0Mstar⟩ := key Mstar hMstarA
  have hMM : M = Mstar :=
    hUniq.eq_of_isCoatom_of_le (mem_maximalSubgroups.mp hM.1) hN0M hMstarCo hN0Mstar
  exact hxnotM (hMM ▸ hCMstar)

/-- A local `SCN₃(P)` subgroup of a Sylow subgroup, viewed in `G`, is a global
`SCN₃(p)` subgroup. -/
private theorem scn3Global_of_scn3_sylow [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {A : Subgroup ↥(P : Subgroup G)}
    (hA : IsSCN₃ p A) :
    A.map (P : Subgroup G).subtype ∈ S07.scn3Global p G := by
  classical
  have hAP : A.map (P : Subgroup G).subtype ≤ (P : Subgroup G) :=
    Subgroup.map_subtype_le A
  refine ⟨P, hAP, ?_⟩
  have htarget :
      (A.map (P : Subgroup G).subtype).subgroupOf (P : Subgroup G) = A := by
    apply (Subgroup.map_subtype_inj (H := (P : Subgroup G))).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hAP]
  rwa [htarget]

/-- If `K` has rank at least two, then `C_G(K)` is proper. -/
theorem centralizer_lt_top_of_two_le_rank [Finite G] (hG : IsMinimalSimpleOdd G)
    {K : Subgroup G} (hr : 2 ≤ rank ↥K) :
    Subgroup.centralizer (K : Set G) < ⊤ := by
  classical
  have hZbot : Subgroup.center G = ⊥ := by
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exact absurd (isSolvable_of_comm fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm) hG.notSolvable
  have hKne : K ≠ ⊥ := by
    obtain ⟨p, hp, A, _hAea, hAK, hAnc⟩ :=
      exists_isElementaryAbelian_not_isCyclic_le_of_two_le_rank K hr
    intro hKbot
    have hA_bot : A = ⊥ := le_bot_iff.mp (hAK.trans (le_of_eq hKbot))
    haveI : Nontrivial ↥A := Nontrivial.of_not_isCyclic hAnc
    exact ((Subgroup.nontrivial_iff_ne_bot A).mp inferInstance) hA_bot
  rw [lt_top_iff_ne_top]
  intro hCtop
  have hKleZ : K ≤ Subgroup.center G :=
    Subgroup.centralizer_eq_top_iff_subset.mp hCtop
  have hKbot : K = ⊥ := by
    exact le_bot_iff.mp (hKleZ.trans (le_of_eq hZbot))
  exact hKne hKbot

/-- Proper form of BG Theorem 9.6 for the branch `r(K) ≥ 3`. -/
theorem isUniquelyMaximal_of_three_le_rank_of_lt_top [Finite G]
    (hG : IsMinimalSimpleOdd G) {K : Subgroup G} (hKlt : K < ⊤)
    (hr3 : 3 ≤ rank ↥K) :
    IsUniquelyMaximal K := by
  classical
  obtain ⟨p, hp, hpRankK⟩ :=
    exists_pRank_ge_of_pos_le_rank (G := ↥K) (n := 3) (by norm_num) hr3
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B₀, hB₀ea, hB₀log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥K) (p := p) (n := 3) (by norm_num) hpRankK
  let B : Subgroup G := B₀.map K.subtype
  have hBea : B.IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.map K.subtype_injective hB₀ea
  have hBK : B ≤ K := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  have hBlog : 3 ≤ Nat.log p (Nat.card B) := by
    rw [show B = B₀.map K.subtype from rfl,
      Subgroup.card_map_of_injective K.subtype_injective]
    exact hB₀log
  have hBnc : ¬ IsCyclic ↥B :=
    not_isCyclic_of_isElementaryAbelian_of_two_le_log_card hBea (by omega)
  have hBp : IsPGroup p B := hBea.isPGroup
  have hp_dvd_B : p ∣ Nat.card B := by
    obtain ⟨n, hn⟩ := hBp.exists_card_eq
    have hnpos : 0 < n := by
      by_contra hn0
      have hn_zero : n = 0 := by omega
      rw [hn_zero, pow_zero] at hn
      rw [hn] at hBlog
      norm_num at hBlog
    rw [hn]
    exact dvd_pow_self p hnpos.ne'
  have hp_odd : Odd p :=
    hG.odd.of_dvd_nat (hp_dvd_B.trans (Subgroup.card_subgroup_dvd_card B))
  obtain ⟨P, hBP⟩ := hBp.exists_le_sylow
  have h3P : 3 ≤ pRank ↥(P : Subgroup G) p := by
    let Bsub : Subgroup ↥(P : Subgroup G) := B.subgroupOf (P : Subgroup G)
    have hBsub_ea : Bsub.IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBP).symm hBea
    have hBsub_log : 3 ≤ Nat.log p (Nat.card Bsub) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv]
      exact hBlog
    exact hBsub_log.trans (le_pRank Bsub hBsub_ea)
  obtain ⟨A₀, hA₀scn⟩ :=
    OddOrder.BG.Ch1.S05.scn3_nonempty_of_three_le_pRank
      (R := ↥(P : Subgroup G)) hp_odd P.isPGroup' h3P
  let A : Subgroup G := A₀.map (P : Subgroup G).subtype
  have hAglobal : A ∈ S07.scn3Global p G := by
    change A₀.map (P : Subgroup G).subtype ∈ S07.scn3Global p G
    exact scn3Global_of_scn3_sylow P hA₀scn
  have hAU : IsUniquelyMaximal A :=
    scn3_isUniquelyMaximal hG hAglobal
  have hAab : IsMulCommutative A := by
    haveI : IsMulCommutative A₀ := hA₀scn.isSCN.isMulCommutative
    change IsMulCommutative (A₀.map (P : Subgroup G).subtype)
    infer_instance
  have hAp : IsPGroup p A := by
    change IsPGroup p (A₀.map (P : Subgroup G).subtype)
    exact (P.isPGroup'.to_subgroup A₀).map (P : Subgroup G).subtype
  have hmA : 3 ≤ rank ↥A := by
    have h3pRankA : 3 ≤ pRank ↥A p := by
      have hmono :
          pRank A₀ p ≤ pRank ↥(A₀.map (P : Subgroup G).subtype) p :=
        pRank_le_of_injective
          (f := (Subgroup.equivMapOfInjective A₀ (P : Subgroup G).subtype
            (P : Subgroup G).subtype_injective).toMonoidHom)
          (Subgroup.equivMapOfInjective A₀ (P : Subgroup G).subtype
            (P : Subgroup G).subtype_injective).injective
      exact hA₀scn.le_pRank.trans hmono
    exact h3pRankA.trans (pRank_le_rank (G := ↥A) p)
  have hB_le_CB : B ≤ Subgroup.centralizer (B : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (congrArg Subtype.val (hBea.comm ⟨b, hb⟩ ⟨c, hc⟩)).symm
  have hrB : 3 ≤ pRank ↥(Subgroup.centralizer (B : Set G)) p := by
    let Bsub : Subgroup ↥(Subgroup.centralizer (B : Set G)) :=
      B.subgroupOf (Subgroup.centralizer (B : Set G))
    have hBsub_ea : Bsub.IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hB_le_CB).symm hBea
    have hBsub_log : 3 ≤ Nat.log p (Nat.card Bsub) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_CB).toEquiv]
      exact hBlog
    exact hBsub_log.trans (le_pRank Bsub hBsub_ea)
  have hBU : IsUniquelyMaximal B :=
    isUniquelyMaximal_of_abelian_rank_three hG hAab hAp hBp hBnc hAU hmA hrB
  exact hBU.of_le_of_lt_top hBK hKlt


end OddOrder.BG.Ch2.S09
