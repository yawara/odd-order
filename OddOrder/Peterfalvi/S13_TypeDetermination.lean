/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_Noncoherence

/-!
# S13_TypeDetermination — Peterfalvi (13.2.a) and the κ-ordered maximal pair

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Section 13, statement (13.2.a) (with its §11 input (11.9.b), pp. 66–68, 79–80).

The (13.2.a) type determination — the member of the maximal pair with the *smaller* κ-Hall
factor is of type `P₂` (= Type II) — together with its two consumers: the canonical
`Section16MaximalPair` producer (the `S_typeP2` fill) and the κ-ordered form of the
`M`-seeded pair.

Relocated from `FeitThompsonSetup` / `S12_TypeIIGridTranspose` (issue 1020 Phase 3): the
type-V exclusion inside `card_kappaHall_lt_of_isTypeP1` cites the **unconditional**
Theorem (10.10) (`S12.no_typeV_maximal_unconditional`, `S12_Noncoherence`), which lives
*below* the pair machinery.  This restores the book dependency order
`(10.7) → (10.8) → (10.10) → (11.9.b) → (13.2.a)`: the κ-*ordering* results here are
strictly downstream of the order-free `Core` pair the (10.7)/(10.8) chain runs on
(issue 1020 Phase 1a), so no (13.2.a) → (10.8) cycle can form.

The `OddOrder`-root declarations keep their names and namespace (they are the
Feit–Thompson assembly layer, continuing `FeitThompsonSetup`); only their home moved
below `S12_Noncoherence` to consume the honest (10.10).
-/

namespace OddOrder

open OddOrder.BG
open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

namespace Peterfalvi.S13

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

/-- **Peterfalvi (11.3), unconditional**: `𝒮(H₀C)` is not coherent — `S_H0C_not_coherent`
re-founded on the unconditional Theorem (10.8) (`S12.S_not_coherent_unconditional`, whose
partner supply is assembled internally; issue 1020 Phase 3).  If `𝒮(H₀C)` were coherent,
Theorem (6.3) (`coherent_S_of_coherent_SH0C`) would make the full family `𝒮` coherent. -/
theorem S_H0C_not_coherent_unconditional {G : Type*} [Group G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (s13hyp : Hypothesis M) :
    ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      s13hyp.base.tau (s13hyp.SOf s13hyp.H0C) s13hyp.base.A0) :=
  fun hcoh => OddOrder.Peterfalvi.S12.S_not_coherent_unconditional hG s13hyp.base
    (coherent_S_of_coherent_SH0C hG s13hyp
      (OddOrder.Peterfalvi.S12.isTypeIIIorIV_unconditional hG s13hyp.base) hcoh)

/-- **Peterfalvi (11.9.b), unconditional** — `w₂ < w₁` for the §10 hypothesis on a type-III/IV
maximal subgroup: the refuter core `exists_zeta_residual_not_orthogonal_H0C_of_refuter`
instantiated at the unconditional (11.3) (`S_H0C_not_coherent_unconditional`), composed with
the coherence-free reduction `w2_lt_w1_of_residual_not_orthogonal`.  This is the honest heir
of the retired legacy `w2_lt_w1_of_hypothesis_H0C` (whose (11.3) routed through the
partner-sorried `S12.S_not_coherent`), and the `feitThompson`-spine consumer via
`card_kappaHall_lt_of_isTypeIIIorIV` below (issue 1020 Phase 3). -/
theorem w2_lt_w1_of_hypothesis_H0C_unconditional {G : Type*} [Group G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (hM2 : secondDerivedInAmbient M
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1) :
    hyp.w2 < hyp.w1 := by
  obtain ⟨ζ, hζS, hζirr, hζ1, h118⟩ :=
    exists_zeta_residual_not_orthogonal_H0C_of_refuter hG hyp htype hM2 hHcard
      (fun s13hyp => S_H0C_not_coherent_unconditional hG s13hyp)
  exact OddOrder.Peterfalvi.S12.w2_lt_w1_of_residual_not_orthogonal hG hyp hζS hζirr hζ1 h118

end Peterfalvi.S13

/-- **Peterfalvi (11.9.b), character core** (Peterfalvi §11
coherence / Dade norm).  For a Type III/IV maximal subgroup `S` (the Hypothesis (11.2) case), with
κ-Hall factor `K` and dual factor `K* = M_σ(S) ⊓ C_G(K)`, the coherence / norm-inequality bound on
the character set `S(HC)` forces `q > p`, i.e. the dual factor is the smaller: `|K*| < |K|`
(`q = |W₁| = |K|`, `p = |W₂| = |K*|`).

The proof is now **fully assembled** from three pieces: (i) the carrier translation `|K| = w₁` (both
`K` and `W₁` complement `M'`, so both equal the derived index — `card_kappaHall_eq_derived_index`,
`TypePData.card_W1_eq_derived_index`); (ii) the carrier translation `|K*| = w₂`
(`card_Msigma_inf_centralizer_eq_card_W2`, axiom-clean BG §14 group theory); and (iii) the §11
character reduction `w₂ < w₁` (`S13.w2_lt_w1_of_hypothesis_H0C_unconditional` — the honest
narrow-`𝒮(H₀C)` route on the unconditional (11.3), issues 1019/1020; the deprecated wide
`S12.w2_lt_w1_of_hypothesis` and its false uniform-degree lemma have been retired).  All of
(i)/(ii) and the reduction spine of (iii) are proven; the residual is the genuine Peterfalvi
(11.8) non-orthogonality (`S13.exists_zeta_residual_not_orthogonal_H0C_of_refuter`), whose
remaining `sorry`s are the §14 Sibley glue `(6.7)`/`(5.8)` and the `(9.11)` caseA refuter
(the former `(10.8)` residual is discharged by `S_not_coherent_unconditional`). -/
theorem card_kappaHall_lt_of_isTypeIIIorIV {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {S K Kstar : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hIIIorIV : IsTypeIII S ∨ IsTypeIV S) :
    Nat.card ↥Kstar < Nat.card ↥K := by
  -- `K` is cyclic, as a subgroup of the cyclic `Z = K ⊔ K*` (BG 14.7(d), via `typeP_duality`).
  obtain ⟨_, _, _, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
    BG.Ch4.S14.typeP_duality hG hS hSP hKS hK hKstar
  haveI : IsCyclic ↥(K ⊔ Kstar) := hcyc
  haveI : IsCyclic ↥K :=
    isCyclic_of_injective (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Kstar))
      (Subgroup.inclusion_injective _)
  -- Build the §10 hypothesis on `S` (type III/IV ⊆ III/IV/V).
  obtain ⟨hyp⟩ := OddOrder.Peterfalvi.S12.exists_hypothesis_of_typeIIIorIVorV hG hS
    (hIIIorIV.imp id Or.inl)
  -- `|K| = w₁`: both `K` and `W₁` complement `M'`, so both equal the derived index.
  have hKw1 : Nat.card ↥K = hyp.w1 := by
    rw [BG.Ch4.S16.card_kappaHall_eq_derived_index hG hS hSP hKS hK]
    exact hyp.typeP.card_W1_eq_derived_index.symm
  -- `|K*| = w₂`: the carrier bridge (lane-b W3, BG §14 group theory, now in `S10`).
  have hKstarw2 : Nat.card ↥Kstar = hyp.w2 := by
    rw [hKstar]
    exact OddOrder.Peterfalvi.S10.card_Msigma_inf_centralizer_eq_card_W2 hG hS hSP hKS hK hyp.typeP
  -- The two (11.5)/(11.7) structural facts, discharged via §13 (`secondDerived_eq_HC`,
  -- `H_elementaryAbelian`): `M'' = H ⊔ C_U(H)` and `|H| = |W₂|^{|W₁|}`.
  have hM2 : secondDerivedInAmbient S
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)) :=
    OddOrder.Peterfalvi.S13.secondDerived_eq_fitting_of_base hG hyp hIIIorIV
      (fun s13 => OddOrder.Peterfalvi.S13.S_H0C_not_coherent_unconditional hG s13)
  have hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1 :=
    OddOrder.Peterfalvi.S13.card_H_eq_of_base hG hyp hIIIorIV
      (fun s13 => OddOrder.Peterfalvi.S13.S_H0C_not_coherent_unconditional hG s13)
  -- `w₂ < w₁` (Peterfalvi (11.9.b), from the genuine (11.8) via the honest narrow `𝒮(H₀C)` route
  -- on the unconditional (11.3) — `w2_lt_w1_of_hypothesis_H0C_unconditional`, issues 1019/1020).
  rw [hKstarw2, hKw1]
  exact OddOrder.Peterfalvi.S13.w2_lt_w1_of_hypothesis_H0C_unconditional hG hyp hIIIorIV hM2
    hHcard

/-- **Peterfalvi (13.2.a), character core** (mmd §13, `references/peterfalvi/04.15_*`).

For the type-`P` member `S` of a dual maximal pair (BG Theorem 14.7), with κ-Hall factor `K` and
dual factor `K* = M_σ(S) ⊓ C_G(K)`, the type-`P₁` alternative (`S` of Type III/IV/V) carries the
*larger* κ-Hall factor: `|K*| < |K|`.  In Peterfalvi's notation `q = |W₁| = |K|`, `p = |W₂| = |K*|`,
this is "`S` of Type III ⟹ `q > p`".

**Type-V exclusion via the unconditional Theorem (10.10)** (issue 1020 Phase 3 relayering): by
the type dictionary `proposition_type_classification`, a type-`P₁` `S` is Type III/IV (if
`M_F ≠ M_σ`) or Type V (if `M_F = M_σ`); the latter is impossible by
`no_typeV_maximal_unconditional` (`S12_Noncoherence` — the honest (10.8) → (10.10) chain, whose
only remaining `sorry`s are the (6.5) gate lemmas, issue 2022), so `S` is Type III/IV and the
genuinely §11 character core `card_kappaHall_lt_of_isTypeIIIorIV` ((11.9.b)) applies.  Consumed
by `isTypeP2_of_typeP_kappaHall_lt`. -/
theorem card_kappaHall_lt_of_isTypeP1 {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {S K Kstar : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hP1 : BG.Ch4.S14.IsTypeP1 S) :
    Nat.card ↥Kstar < Nat.card ↥K := by
  -- Type dictionary: `S` type-`P₁` ⟹ Type III/IV (`M_F ≠ M_σ`) or Type V (`M_F = M_σ`).
  obtain ⟨_, _, hcIII_IV, hdV, _, _⟩ := BG.Ch4.S16.proposition_type_classification hG hS
  -- Type V is excluded by Theorem (10.10) `no_typeV_maximal`, so `M_F ≠ M_σ` and `S` is III/IV.
  have hMF : BG.Ch4.S15.MF S ≠ BG.Ch3.S10.Msigma S := fun hMF =>
    OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG ⟨S, hS, hdV.mpr ⟨hP1, hMF⟩⟩
  -- The genuinely §11 character core (11.9.b) gives `|K*| < |K|`.
  exact card_kappaHall_lt_of_isTypeIIIorIV hG hS hSP hKS hK hKstar (hcIII_IV.mpr ⟨hP1, hMF⟩)

/-- **Peterfalvi (13.2.a)** (mmd §13, `references/peterfalvi/04.15_*`): the type-`P` member `S` of a
dual maximal pair whose κ-Hall factor `K` is the *smaller* of the two coprime factors of
`W = K × K*` is of type `P₂` (BG) / Type II (Peterfalvi).

This selects, out of the type-duality disjunction `IsTypeP2 S ∨ IsTypeP2 T` (BG Theorem 14.7,
`typeP_duality`, which carries no order information), the determinate side `IsTypeP2 S` fixed by the
ordering `|K| < |K*|`.  Skeleton proof: `S` is type-`P`, hence type `P₁` or `P₂`
(`isTypeP_iff_isTypeP1_or_isTypeP2`); the `P₁` branch is excluded by `card_kappaHall_lt_of_isTypeP1`
(the Pf §10–§11 character core), leaving `P₂`.

Consumed by `section16MaximalPair_of_isMinimalSimpleOdd` to carry `Section16MaximalPair.S_typeP2`
(relane #4, issues 4009/2019), which unblocks the §15 `basic_structure` `TypePData` carrier wiring
(`exists_typePData_W1_eq_of_isTypeP2`). -/
theorem isTypeP2_of_typeP_kappaHall_lt {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {S K Kstar : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hlt : Nat.card ↥K < Nat.card ↥Kstar) :
    BG.Ch4.S14.IsTypeP2 S := by
  rcases BG.Ch4.S14.isTypeP_iff_isTypeP1_or_isTypeP2.mp hSP with hP1 | hP2
  · exact absurd (card_kappaHall_lt_of_isTypeP1 hG hS hSP hKS hK hKstar hP1) (lt_asymm hlt)
  · exact hP2

/-- **BG §16 maximal-pair producer** — *lane-g* (BG §16 main results).
Constructs the maximal pair `S, T`, their type classification, and the case-(b)
trichotomy of (8.8) from a minimal simple group of odd order.

This is the first real consumer of the §16 main results.  Peterfalvi (8.8)
(`maximalSubgroup_type_dichotomy`, repackaging BG Theorem I) gives the dichotomy
"every maximal subgroup is Type I, or the type-P pair `S, T` covers everything".
The second branch supplies every field directly.  The first branch is impossible:
Peterfalvi (12.17) (`theorem88_caseB_holds`, the all-Type-I non-existence argument
of §7.11/§12) produces a *non-Type-I* maximal subgroup, which contradicts "every
maximal subgroup is Type I" via the type-exclusivity corollary of Proposition 16.1
(`not_isTypeI_of_isTypeNonI`). -/
noncomputable def section16MaximalPair_of_isMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) : Section16MaximalPair G := by
  classical
  -- `exists_section16MaximalPair_data` supplies the canonical pair `S, T = Mstar` with the full
  -- κ-Hall witness data.  The four subgroup witnesses are extracted by choice (the `Exists` cannot
  -- be `rcases`'d into the `Type`-valued structure goal); the structural conjunction is an `And`
  -- (large-eliminating), so it `obtain`s into named hypotheses directly.
  have e := exists_section16MaximalPair_data hG
    (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG)
  obtain ⟨hSmax, hTmax, hSneT, hSnonI, hTnonI, hone, hcaseB, hKleS, hKhall, hKstareq,
    hStypeP, hTtypeP, hSTnconj, hKstarleT, hKstarhall, hKeq, hZcyc, hKlt⟩ :=
    e.choose_spec.choose_spec.choose_spec.choose_spec
  exact
    { S := e.choose
      T := e.choose_spec.choose
      K := e.choose_spec.choose_spec.choose
      Kstar := e.choose_spec.choose_spec.choose_spec.choose
      S_maximal := hSmax
      T_maximal := hTmax
      S_ne_T := hSneT
      S_nonI := hSnonI
      T_nonI := hTnonI
      one_typeII := hone
      theorem88_caseB := hcaseB
      K_le_S := hKleS
      K_hall := hKhall
      Kstar_eq := hKstareq
      S_typeP := hStypeP
      T_typeP := hTtypeP
      S_T_not_conj := hSTnconj
      Kstar_le_T := hKstarleT
      Kstar_hall := hKstarhall
      K_eq := hKeq
      Z_cyclic := hZcyc
      K_lt_Kstar := hKlt
      S_typeP2 := isTypeP2_of_typeP_kappaHall_lt hG hSmax hStypeP hKleS hKhall hKstareq hKlt }

namespace Peterfalvi.S12

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **The `M`-seeded canonical-pair data, κ-ordered form**: `exists_section16MaximalPairCore_data_around`
together with the (13.2.a)-deep ordering `|K| < |W₁|` (`isTypeP2_of_typeP_kappaHall_lt`
contrapositive).  ⚠ This ordering routes through (10.10) ← (10.8); order-free consumers — the
(10.7)/(10.8) chain — must use the `Core` form (issue 1020 Phase 1a). -/
theorem exists_section16MaximalPair_data_around [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M W1 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : OddOrder.BG.Ch4.S14.IsTypeP M)
    (hnotP2 : ¬ OddOrder.BG.Ch4.S14.IsTypeP2 M)
    (hW1M : W1 ≤ M)
    (hW1hall : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M)
      (W1.subgroupOf M)) :
    ∃ S K : Subgroup G,
      S ∈ maximalSubgroups G ∧ S ≠ M ∧
      IsTypeNonI S ∧ IsTypeNonI M ∧ IsTypeII S ∧
      (∀ N : Subgroup G, N ∈ maximalSubgroups G →
        IsTypeI N ∨ (∃ g : G, MulAut.conj g • N = S) ∨ (∃ g : G, MulAut.conj g • N = M)) ∧
      K ≤ S ∧
      OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa S) (K.subgroupOf S) ∧
      W1 = OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G) ∧
      OddOrder.BG.Ch4.S14.IsTypeP S ∧
      ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup S M ∧
      K = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (W1 : Set G) ∧
      IsCyclic ↥(K ⊔ W1) ∧ Nat.card ↥K < Nat.card ↥W1 := by
  obtain ⟨S, K, hSmax, hSne, hSnonI, hMnonI, hSII, hcov, hKleS, hKhall, hW1eq, hSP,
    hSnconj, hKdef, hcyc⟩ :=
    exists_section16MaximalPairCore_data_around hG hM hP hnotP2 hW1M hW1hall
  have hne := OddOrder.BG.Ch4.S14.card_kappaHall_ne_card_Kstar hP hW1M hW1hall hKdef
  have hlt : Nat.card ↥K < Nat.card ↥W1 := by
    rcases lt_or_gt_of_ne hne with hlt' | hgt
    · exact absurd (isTypeP2_of_typeP_kappaHall_lt hG hM hP hW1M hW1hall hKdef hlt') hnotP2
    · exact hgt
  exact ⟨S, K, hSmax, hSne, hSnonI, hMnonI, hSII, hcov, hKleS, hKhall, hW1eq, hSP,
    hSnconj, hKdef, hcyc, hlt⟩

/-- **The `M`-seeded canonical pair** (packaging of
`exists_section16MaximalPair_data_around`): a `Section16MaximalPair` whose `T`-member is
the given `M` and whose dual κ-Hall factor is the given `W₁`.  This is the pair the (10.7)
pair-witness route runs on: the §10 machinery of `M` plugs into the pair lemmas with
`dataT := hyp.typeP` and `hTW1 : hyp.typeP.W1 = mp.Kstar` along the returned equations
(`typePData_W1_isHallSubgroup_kappa` supplies the Hall seed). -/
theorem exists_section16MaximalPair_around [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M W1 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : OddOrder.BG.Ch4.S14.IsTypeP M)
    (hnotP2 : ¬ OddOrder.BG.Ch4.S14.IsTypeP2 M)
    (hW1M : W1 ≤ M)
    (hW1hall : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M)
      (W1.subgroupOf M)) :
    ∃ mp : Section16MaximalPair G, mp.T = M ∧ mp.Kstar = W1 := by
  classical
  obtain ⟨S, K, hSmax, hSneM, hSnonI, hMnonI, hSII, hcov, hKleS, hKhall, hW1eq, hSP,
    hSnconj, hKdef, hcyc, hlt⟩ :=
    exists_section16MaximalPair_data_around hG hM hP hnotP2 hW1M hW1hall
  exact ⟨{ S := S
           T := M
           K := K
           Kstar := W1
           S_maximal := hSmax
           T_maximal := hM
           S_ne_T := hSneM
           S_nonI := hSnonI
           T_nonI := hMnonI
           one_typeII := Or.inl hSII
           theorem88_caseB := hcov
           K_le_S := hKleS
           K_hall := hKhall
           Kstar_eq := hW1eq
           S_typeP := hSP
           T_typeP := hP
           S_T_not_conj := hSnconj
           Kstar_le_T := hW1M
           Kstar_hall := hW1hall
           K_eq := hKdef
           Z_cyclic := hcyc
           K_lt_Kstar := hlt
           S_typeP2 :=
             (OddOrder.BG.Ch4.S16.proposition_type_classification hG hSmax).2.1.mp hSII },
    rfl, rfl⟩

end Peterfalvi.S12

end OddOrder
