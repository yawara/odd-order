/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S04_DadeIsometry
import OddOrder.Peterfalvi.S09_NonexistenceCertain
import OddOrder.GroupTheory.MaximalSubgroupType
import OddOrder.GroupTheory.MaximalSubgroup
import OddOrder.Isaacs.Ch06_FrobeniusActions.OddComplement
import OddOrder.BG.Ch2_Uniqueness.Setup
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_Lemma1413
import OddOrder.Peterfalvi.S10_BGInterface

/-!
# S10_StructureSetup

Prefix-split from `OddOrder.Peterfalvi.S10_MinimalSimpleBasic` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# S10_MinimalSimpleBasic

Prefix-split from `OddOrder.Peterfalvi.S10_MinimalSimpleStructure` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# Peterfalvi Section 10: Structure of a Minimal Simple Group of Odd Order

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 10, pp. 44--49.

This section is the interface between BG local analysis and Peterfalvi's final
character-theoretic analysis.  It fixes the maximal-subgroup taxonomy
(type `F`, type I, type `P`, and types II--V) and records the BG Section 16
structural consequences consumed by Peterfalvi Sections 11--16.

The actual type definitions live in `OddOrder.GroupTheory.MaximalSubgroupType`
because BG Chapter IV uses the same taxonomy.  This file provides the
Peterfalvi-numbered entry points and the main scaffold statements.  Those of
(8.11), (8.12), (8.13) quote BG Theorems A--E / Theorems I--II, which are now
stated (still `sorry`) in `OddOrder.BG.Ch4.S16` and are cited here as the
Peterfalvi-facing wiring is built; (8.8) is already wired to BG Theorem I
(`theoremI_nilpotentHall_conjugacy_and_type_dichotomy`).  The remaining `sorry`s
reduce to those BG endpoints plus a notation dictionary, not to new axioms;
see `notes/peterfalvi/s10_13_maximal_structure.md`.

The Nougat extract drops the statements around (8.14)--(8.17).  The PDF page
has now been recovered; this file records the `R(x)`/thickened-support notation,
the Type-II TI endpoint, the Dade (2.2) interface behind (8.15), and the BG
Theorem E covering interface.  The higher §4.6/§5.2 Dade specializations remain
as a precise TODO until their section-level carriers are stable enough to avoid
opaque placeholders.
-/

namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## (8.1)--(8.7): type taxonomy -/

/-- **Peterfalvi (8.1)**: data for a group of type `F`.

The definition is shared as `OddOrder.GroupTheory.TypeFData`; the proposition
form is `OddOrder.GroupTheory.IsTypeF`. -/
abbrev TypeFData (M : Subgroup G) := OddOrder.GroupTheory.TypeFData M

/-- **Peterfalvi (8.3)**: data for a maximal subgroup of type I. -/
abbrev TypeIData (M : Subgroup G) := OddOrder.GroupTheory.TypeIData M

/-- **Peterfalvi (8.4)**: data for a maximal subgroup of type `P`. -/
abbrev TypePData (M : Subgroup G) := OddOrder.GroupTheory.TypePData M

/-- **Peterfalvi (8.6)**: data for a maximal subgroup of type II. -/
abbrev TypeIIData (M : Subgroup G) := OddOrder.GroupTheory.TypeIIData M

/-- **Peterfalvi (8.6)**: data for a maximal subgroup of type III. -/
abbrev TypeIIIData (M : Subgroup G) := OddOrder.GroupTheory.TypeIIIData M

/-- **Peterfalvi (8.6)**: data for a maximal subgroup of type IV. -/
abbrev TypeIVData (M : Subgroup G) := OddOrder.GroupTheory.TypeIVData M

/-- **Peterfalvi (8.7)**: data for a maximal subgroup of type V. -/
abbrev TypeVData (M : Subgroup G) := OddOrder.GroupTheory.TypeVData M

/-- **Group form of `isZGroup_of_isFrobeniusAction_of_odd`** ([BG] Proposition 3.9 / Huppert
V.8.18): the complement `A` of a finite Frobenius group `G' = N ⋊ A` whose complement has **odd
order** is a Z-group (every Sylow subgroup is cyclic).  This bridges the pair form
`IsFrobeniusGroup` to the action-based `isZGroup_of_isFrobeniusAction_of_odd`, mirroring
`normal_of_card_prime_of_isFrobeniusGroup_of_odd`. -/
theorem isZGroup_of_isFrobeniusGroup_of_odd {G' : Type*} [Group G'] [Finite G']
    {N A : Subgroup G'} (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G' N A)
    (hodd : Odd (Nat.card ↥A)) : _root_.IsZGroup ↥A := by
  letI : N.Normal := hFrob.isNormal
  letI : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom ↥N ((MulAut.conjNormal (H := N)).comp A.subtype)
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hFrob.ne_bot_kernel
  exact OddOrder.Isaacs.Ch06.isZGroup_of_isFrobeniusAction_of_odd hFrob.toFrobeniusAction hodd

/-- **Peterfalvi (8.2.a)**: in type `F`, the chosen `U_0` has order equal to the exponent of the
complement `U`.

**Proof** ([Pf] (8.2.a), quoting [BG] Proposition 3.9).  `U_0` is a Frobenius complement of odd
order (`data.frobenius_HU0` says `H U_0` is Frobenius with kernel `H`), so its Sylow subgroups are
cyclic — i.e. `U_0` is a Z-group (`isZGroup_of_isFrobeniusGroup_of_odd`).  For a finite Z-group,
`|U_0| = exp(U_0)` (`IsZGroup.exponent_eq_card`: each cyclic Sylow `p`-subgroup contributes an
element of order `|U_0|_p`, so `|U_0| = ∏_p |U_0|_p ∣ exp(U_0)`, and `exp(U_0) ∣ |U_0|` always).
Finally `exp(U_0) = exp(U)` is `data.exponent_eq` (part of the type-`F` datum (8.1.c)).

The odd-order hypothesis is essential: without it `U_0` could be (generalized) quaternion, where
`exp < |U_0|`.  It is supplied here as `Odd (Nat.card G)`, from which `Odd |U_0|` follows since
`|U_0| ∣ |G|`. -/
theorem typeF_card_U0_eq_exponent [Finite G] (hodd : Odd (Nat.card G)) {M : Subgroup G}
    (data : TypeFData M) :
    Nat.card ↥data.U0 = Monoid.exponent data.U := by
  classical
  have hU0le : data.U0 ≤ data.H ⊔ data.U0 := le_sup_right
  let e : ↥(data.U0.subgroupOf (data.H ⊔ data.U0)) ≃* ↥data.U0 :=
    Subgroup.subgroupOfEquivOfLe hU0le
  have hcardA : Nat.card ↥(data.U0.subgroupOf (data.H ⊔ data.U0)) = Nat.card ↥data.U0 :=
    Nat.card_congr e.toEquiv
  have hdvd : Nat.card ↥data.U0 ∣ Nat.card G := Subgroup.card_subgroup_dvd_card data.U0
  have hoddA : Odd (Nat.card ↥(data.U0.subgroupOf (data.H ⊔ data.U0))) := by
    rw [hcardA]; exact Odd.of_dvd_nat hodd hdvd
  haveI hZA : _root_.IsZGroup ↥(data.U0.subgroupOf (data.H ⊔ data.U0)) :=
    isZGroup_of_isFrobeniusGroup_of_odd data.frobenius_HU0 hoddA
  haveI hZU0 : _root_.IsZGroup ↥data.U0 := by
    have hinj : Function.Injective ⇑(e.symm.toMonoidHom) := by simpa using e.symm.injective
    exact _root_.IsZGroup.of_injective hinj
  rw [← _root_.IsZGroup.exponent_eq_card (G := ↥data.U0), data.exponent_eq]

/-- **Peterfalvi (8.2.b), one direction**: when the complement has cyclic Sylow
subgroups, type `F` collapses to a Frobenius group with kernel `M_F`.

The cyclic-Sylow hypothesis is represented by the cardinal/exponent equality
`|U| = exp(U)`, the finite cyclic-complement criterion used in the text. -/
theorem typeF_frobenius_of_card_eq_exponent [Finite G] {M : Subgroup G}
    (data : TypeFData M) (hU : Nat.card ↥data.U = Monoid.exponent data.U) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.H.subgroupOf M) (data.U.subgroupOf M) := by
  -- The cyclic-Sylow hypothesis `|U| = exp(U) = exp(U₀)` forces `U₀ = U`, so the
  -- Frobenius structure of `H ⊔ U₀` (a field of `TypeFData`) collapses to `M`.
  have hexp : Monoid.exponent ↥data.U0 = Nat.card ↥data.U :=
    data.exponent_eq.trans hU.symm
  have hdvd1 : Nat.card ↥data.U ∣ Nat.card ↥data.U0 := by
    rw [← hexp]; exact Group.exponent_dvd_nat_card
  have hdvd2 : Nat.card ↥data.U0 ∣ Nat.card ↥data.U :=
    Subgroup.card_dvd_of_le data.U0_le
  have hcard : Nat.card ↥data.U0 = Nat.card ↥data.U := Nat.dvd_antisymm hdvd2 hdvd1
  have hU0eq : data.U0 = data.U := Subgroup.eq_of_le_of_card_ge data.U0_le hcard.ge
  -- `H ⊔ U = M`, from the complement `H ⋊ U = M`.
  have hHU : data.H ⊔ data.U = M := by
    have htop : data.H.subgroupOf M ⊔ data.U.subgroupOf M = ⊤ := data.complement.sup_eq_top
    have hmap := congrArg (Subgroup.map M.subtype) htop
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left data.H_le, inf_of_le_left data.U_le, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap
  -- Transport `frobenius_HU0 : IsFrobeniusGroup (H ⊔ U₀) H U₀` along `U₀ = U` and `H ⊔ U = M`.
  have hfrob := data.frobenius_HU0
  rw [hU0eq, hHU] at hfrob
  exact hfrob

/-! ## (8.8): BG maximal-subgroup dichotomy -/

/-- **Peterfalvi (8.8)**: BG Theorem I / Proposition 16.1 / Theorems B and C(3),
repackaged as Peterfalvi's maximal-subgroup dichotomy.

Either every maximal subgroup is type I, or there are two distinguished maximal
subgroups `S,T` of non-type-I kind such that at least one is type II and every
maximal subgroup is conjugate to `S`, conjugate to `T`, or type I. -/
theorem maximalSubgroup_type_dichotomy [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) ∨
      ∃ S T : Subgroup G,
        S ∈ maximalSubgroups G ∧ T ∈ maximalSubgroups G ∧ S ≠ T ∧
        IsTypeNonI S ∧ IsTypeNonI T ∧ (IsTypeII S ∨ IsTypeII T) ∧
        (∀ M : Subgroup G, M ∈ maximalSubgroups G →
          IsTypeI M ∨ (∃ g : G, MulAut.conj g • M = S) ∨
            (∃ g : G, MulAut.conj g • M = T)) := by
  -- BG Theorem I (`OddOrder.BG.Ch4.S16`) supplies exactly this dichotomy, in the
  -- shared `IsTypeI`/`IsTypeNonI`/`IsTypeII` language, with extra `W₁,W₂,W` data
  -- that Peterfalvi (8.8) drops.  `S14.IsConjugateSubgroup M S` is *defeq* to
  -- `∃ g, MulAut.conj g • M = S`, so the covering clause transfers directly.
  rcases (OddOrder.BG.Ch4.S16.theoremI_nilpotentHall_conjugacy_and_type_dichotomy hG).2 with
    hI | ⟨S, T, _W1, _W2, _W, hS, hT, hST, _hW, _hWcyc, _hWinter, hSnonI, hTnonI, hII, hcov⟩
  · exact Or.inl hI
  · exact Or.inr ⟨S, T, hS, hT, hST, hSnonI, hTnonI, hII, hcov⟩

/-- Centralizer of a cyclic subgroup equals the centralizer of a generator. -/
private theorem centralizer_eq_of_generator {W : Subgroup G} (g : G)
    (hg : g ∈ W) (hgen : ∀ w ∈ W, w ∈ Subgroup.zpowers g) :
    Subgroup.centralizer (W : Set G) = Subgroup.centralizer ({g} : Set G) := by
  apply le_antisymm
  · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hg)
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hc : Commute g y := (Subgroup.mem_centralizer_iff.mp hy) g rfl
    obtain ⟨n, hn⟩ := hgen w hw
    rw [← hn]
    simpa using (hc.zpow_left n).eq

/-- Lift conjugation transport from `↥M` to `G`: `(K^c).map ι = (K.map ι)^(c : G)`. -/
private theorem map_subtype_conj_smul {M : Subgroup G} (c : ↥M)
    (K : Subgroup ↥M) :
    (MulAut.conj c • K).map M.subtype = MulAut.conj (c : G) • (K.map M.subtype) := by
  rw [Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def, Subgroup.map_map,
    Subgroup.map_map]
  refine congrArg (fun f => K.map f) ?_
  ext x
  simp [MulAut.conj_apply]

/-- **`|K*| = w₂` carrier bridge** (lane-b W3, BG §14 group theory; axiom-clean).  For a type-`P`
maximal `S` of a minimal simple group of odd order, with κ-Hall factor `K` (cyclic) and any
`TypePData d` on `S`, the dual factor `K* = M_σ(S) ⊓ C_G(K)` has order `|W₂| = w₂`.

This is the group-theoretic translation that pairs with the §11 character reduction (`q > p`,
`w₂ < w₁`) to close `card_kappaHall_lt_of_isTypeIIIorIV`, and with `typeP_duality` to supply the
(8.8) Type-II partner (`exists_typeII_maximal_with_w2_of_typeP`).  Proof: `W₂ = M' ⊓ C(W₁)`
(`centralizer_W1`, `W₁` cyclic) and `W₂ ≤ M_F ≤ M_σ ≤ M'` (`W2_le`, `H_eq`,
`maxNilpotentNormalHall_le_Msigma`, `Msigma_le_derived`) sandwich `M_σ ⊓ C(W₁) = W₂`; `K` and `W₁`
both complement the normal Hall `M'`, hence are `S`-conjugate (Schur–Zassenhaus,
`IsComplement'.exists_conj_of_coprime`); conjugating `M_σ ⊓ C(K)` (with `M_σ` `S`-invariant) onto
`M_σ ⊓ C(W₁) = W₂` gives the equal cardinality.  No character theory. -/
theorem card_Msigma_inf_centralizer_eq_card_W2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S K : Subgroup G} (hS : S ∈ maximalSubgroups G)
    (hSP : OddOrder.BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa S) (K.subgroupOf S)) [IsCyclic ↥K]
    (d : TypePData S) :
    Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G)) =
      Nat.card ↥d.W2 := by
  classical
  haveI : IsCyclic ↥d.W1 := d.W1_cyclic
  obtain ⟨g0, hg0gen⟩ := IsCyclic.exists_generator (α := ↥d.W1)
  set g : G := (g0 : G) with hgdef
  have hgW1 : g ∈ d.W1 := g0.2
  have hgne : g ≠ 1 := by
    intro h
    apply d.W1_nontrivial
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨n, hn⟩ := hg0gen ⟨w, hw⟩
    have hg0one : g0 = 1 := Subtype.ext h
    rw [hg0one] at hn
    rw [Subgroup.mem_bot]
    have : (⟨w, hw⟩ : ↥d.W1) = 1 := by rw [← hn]; simp
    exact Subtype.ext_iff.mp this
  have hgenW1 : ∀ w ∈ d.W1, w ∈ Subgroup.zpowers g := by
    intro w hw
    obtain ⟨n, hn⟩ := hg0gen ⟨w, hw⟩
    refine ⟨n, ?_⟩
    have := congrArg (Subgroup.subtype d.W1) hn
    simpa [hgdef] using this
  have hCW1 : Subgroup.centralizer (d.W1 : Set G) = Subgroup.centralizer ({g} : Set G) :=
    centralizer_eq_of_generator g hgW1 hgenW1
  have hW2Msigma : d.W2 ≤ OddOrder.BG.Ch3.S10.Msigma S := by
    refine d.W2_le.trans (le_trans inf_le_left ?_)
    rw [d.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hS
  have hMsigmaM' : OddOrder.BG.Ch3.S10.Msigma S ≤ derivedInG S :=
    OddOrder.BG.Ch3.S10.Msigma_le_derived hG hS
  have hcent : derivedInG S ⊓ Subgroup.centralizer ({g} : Set G) = d.W2 :=
    d.centralizer_W1 g hgW1 hgne
  have hkey : OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (d.W1 : Set G) = d.W2 := by
    rw [hCW1]
    apply le_antisymm
    · calc OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer ({g} : Set G)
          ≤ derivedInG S ⊓ Subgroup.centralizer ({g} : Set G) := inf_le_inf_right _ hMsigmaM'
        _ = d.W2 := hcent
    · rw [le_inf_iff]
      exact ⟨hW2Msigma, by rw [← hcent]; exact inf_le_right⟩
  have hKcompl : Subgroup.IsComplement' ((derivedInG S).subgroupOf S) (K.subgroupOf S) :=
    OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hS hSP hKS hK
  have hW1compl : Subgroup.IsComplement' ((derivedInG S).subgroupOf S) (d.W1.subgroupOf S) :=
    d.M_complement
  have hNeq : (derivedInG S).subgroupOf S = commutator ↥S :=
    Subgroup.comap_map_eq_self_of_injective S.subtype_injective _
  haveI hNnormal : ((derivedInG S).subgroupOf S).Normal := by rw [hNeq]; infer_instance
  haveI : IsSolvable ↥S := hG.solvable_of_mem_maximalSubgroups hS
  haveI : IsSolvable ↥((derivedInG S).subgroupOf S) := inferInstance
  have hcop : Nat.Coprime (Nat.card ↥((derivedInG S).subgroupOf S))
      ((derivedInG S).subgroupOf S).index := by
    rw [hKcompl.symm.index_eq_card]
    exact OddOrder.BG.Ch4.S14.coprime_card_derived_kappaHall_of_isComplement' hK hKcompl
  obtain ⟨n, hnN, hnconj⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop (Or.inl inferInstance) hW1compl hKcompl
  have hconjG : MulAut.conj (n : G) • d.W1 = K := by
    have h2 : MulAut.conj (n : G) • ((d.W1.subgroupOf S).map S.subtype)
            = (K.subgroupOf S).map S.subtype := by
      rw [← map_subtype_conj_smul]
      exact congrArg (Subgroup.map S.subtype) hnconj
    rwa [Subgroup.map_subgroupOf_eq_of_le d.W1_le,
      Subgroup.map_subgroupOf_eq_of_le hKS] at h2
  set g0G : G := (n : G) with hg0G
  have hg0M : g0G ∈ S := n.2
  have hMsigmaInv : MulAut.conj g0G • OddOrder.BG.Ch3.S10.Msigma S = OddOrder.BG.Ch3.S10.Msigma S := by
    apply conj_smul_eq_self_of_mem_normalizer
    have hsub : S ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma S) := by
      rw [OddOrder.BG.Ch3.S10.Msigma]
      exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma S) S
    exact hsub hg0M
  have hCKconj : Subgroup.centralizer (K : Set G)
      = MulAut.conj g0G • Subgroup.centralizer (d.W1 : Set G) := by
    rw [OddOrder.BG.Ch3.S13.smul_centralizer_subgroup, hconjG]
  have htransport : OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G)
      = MulAut.conj g0G • (OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (d.W1 : Set G)) := by
    rw [Subgroup.smul_inf, hMsigmaInv, ← hCKconj]
  rw [htransport, hkey]
  exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g0G) d.W2).toEquiv).symm

/-- **Peterfalvi (8.8)/(8.13) for the given `M`**: a non-type-I (type-`P`) maximal subgroup `M`
admits a Type-II maximal subgroup `S` whose cyclic-factor order `|S : [S,S]|` equals `|W₂|`.

This is the `M`-specific case-(b) datum of Theorem (8.8): the type-`P` maximal `M` participates in
the case-(b) configuration of (8.8), one of whose two distinguished maximal subgroups is of Type II
and shares the cyclic-factor order `w₂ = |W₂|`.  It is the §8 obligation behind both the (9.3) order
relations (`S11.typeIIIorIV_W2_prime`) and the (10.3) prime computation (`S12.Hypothesis.w2_prime`).

**Proof (BG §14 duality + the `|K*| = w₂` bridge)**: `M` is type `P₁` (from
`proposition_type_classification` on the III/IV/V hypothesis), hence κ-nonempty.  Pick a κ-Hall
`K ≤ M` (Hall's theorem in solvable `M`) and set `K* = M_σ(M) ⊓ C(K)`.  `typeP_duality` produces the
nonconjugate partner `M*` with `K*` its κ-Hall and `Z = K ⊔ K*` cyclic, and the disjunction
`IsTypeP2 M ∨ IsTypeP2 M*`; `M` type `P₁` excludes the left disjunct, so `M*` is `P₂` = Type II.
Then `[M* : (M*)'] = |K*|` (`card_kappaHall_eq_derived_index` for `M*`, `K*` cyclic) and
`|K*| = |W₂|` (`card_Msigma_inf_centralizer_eq_card_W2`).  Cites the (sorried, lane-f W1)
`proposition_type_classification`; the group-theoretic core is axiom-clean. -/
theorem exists_typeII_maximal_with_w2_of_typeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (data : TypePData M)
    (hM : M ∈ maximalSubgroups G) (hType : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) :
    ∃ S : Subgroup G, S ∈ maximalSubgroups G ∧ IsTypeII S ∧
      ((derivedInG S).subgroupOf S).index = Nat.card ↥data.W2 := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- `M` is type `P₁`, hence κ-nonempty (`BG.Ch4.S14.IsTypeP`).
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M := by
    rcases hType with h | h | h
    · exact ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hM).2.2.1.mp (Or.inl h)).1
    · exact ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hM).2.2.1.mp (Or.inr h)).1
    · exact ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hM).2.2.2.1.mp h).1
  have hP : OddOrder.BG.Ch4.S14.IsTypeP M := OddOrder.BG.Ch4.S14.isTypeP_of_isTypeP1 hP1
  -- A κ-Hall `K` of `M`.
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (OddOrder.BG.Ch4.S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' := Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K.subgroupOf M) := by
    rw [hKeq]; exact hK'
  set Kstar : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
    with hKstardef
  -- `typeP_duality`: partner `Mstar`, type-`P₂` disjunction, cyclic `Z = K ⊔ K*`.
  obtain ⟨_, _, Mstar, ⟨hMstarMem, hMstarP, _,
      ⟨hKstarMstar, hKstar_hall, _⟩, hcyc, _, hP2disj, _⟩, _⟩ :=
    OddOrder.BG.Ch4.S14.typeP_duality hG hM hP hKM hK hKstardef
  -- `M` not `P₂` ⟹ partner `Mstar` is `P₂` = Type II.
  have hnotP2M : ¬ OddOrder.BG.Ch4.S14.IsTypeP2 M := fun h2 =>
    OddOrder.BG.Ch4.S14.not_isTypeP1_and_isTypeP2 ⟨hP1, h2⟩
  have hP2Mstar : OddOrder.BG.Ch4.S14.IsTypeP2 Mstar := hP2disj.resolve_left hnotP2M
  have hMstarII : IsTypeII Mstar :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG hMstarMem).2.1.mpr hP2Mstar
  -- `K` and `K*` cyclic (subgroups of cyclic `Z = K ⊔ K*`).
  haveI : IsCyclic ↥(K ⊔ Kstar) := hcyc
  haveI : IsCyclic ↥K :=
    isCyclic_of_injective (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Kstar))
      (Subgroup.inclusion_injective _)
  haveI : IsCyclic ↥Kstar :=
    isCyclic_of_injective (Subgroup.inclusion (le_sup_right : Kstar ≤ K ⊔ Kstar))
      (Subgroup.inclusion_injective _)
  -- `[Mstar:Mstar'] = |K*| = |W₂|`.
  refine ⟨Mstar, hMstarMem, hMstarII, ?_⟩
  rw [← OddOrder.BG.Ch4.S16.card_kappaHall_eq_derived_index (K := Kstar) hG hMstarMem hMstarP
    hKstarMstar hKstar_hall, hKstardef]
  exact card_Msigma_inf_centralizer_eq_card_W2 hG hM hP hKM hK data

/-! ## (8.10)--(8.13): `M_s`, support sets, and centralizer control -/

/-- **Peterfalvi (8.10)**: the notation `M_s`, shared as `mainSubgroup`. -/
noncomputable abbrev mainSubgroup (M : Subgroup G) (tau : PeterfalviType) :=
  OddOrder.GroupTheory.mainSubgroup M tau

/-- **Peterfalvi (8.10)**: the notation `A_1(M) = M_s#`, shared as `A1`. -/
noncomputable abbrev A1 (M : Subgroup G) (tau : PeterfalviType) := OddOrder.GroupTheory.A1 M tau

/-- **Peterfalvi (8.11)**: if `M` has one of the five Peterfalvi types, then
`M_F` and `M_s` are Hall subgroups of `G`.

The proof is a BG Section 16 consequence, not a local Peterfalvi argument: `M_s = M_σ`
(`mainSubgroup_eq_Msigma`, BG Prop 16.1) is an ambient Hall subgroup by BG Theorem A(1)
(`Msigma_isHall`, re-indexed to `π(M_σ)` by `primeFactors_Msigma_eq_sigma`), and `M_F` combines
its Hall-in-`M` property (`maxNilpotentNormalHall_isHall`) with `M_F ≤ M_σ` for the
`[G : M]`-part of its index. -/
theorem hall_maxNilpotentNormalHall_and_mainSubgroup [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {tau : PeterfalviType} (hType : HasPeterfalviType tau M) :
    Ch03.IsHallSubgroup (Nat.card ↥(maxNilpotentNormalHall M)).primeFactors
        (maxNilpotentNormalHall M) ∧
      Ch03.IsHallSubgroup (Nat.card ↥(mainSubgroup M tau)).primeFactors
        (mainSubgroup M tau) := by
  have hMsHall := OddOrder.BG.Ch3.S10.Msigma_isHall hG hM
  constructor
  · refine ⟨fun p hp => hp, fun p hpidx hpH => ?_⟩
    have hp_prime : p.Prime := (Nat.mem_primeFactors.mp hpidx).1
    -- `p ∈ σ(M)`, via `M_F ≤ M_σ` and `π(M_σ) = σ(M)`.
    have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
      (OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hM p).mp
        (Nat.mem_primeFactors.mpr ⟨hp_prime,
          (Nat.dvd_of_mem_primeFactors hpH).trans (Subgroup.card_dvd_of_le
            (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hM)),
          Nat.card_pos.ne'⟩)
    -- Split `[G : M_F] = [M : M_F] · [G : M]`.
    have hrel : ((maxNilpotentNormalHall M).subgroupOf M).index * M.index
        = (maxNilpotentNormalHall M).index :=
      Subgroup.relIndex_mul_index (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le M)
    have hp_dvd : p ∣ ((maxNilpotentNormalHall M).subgroupOf M).index * M.index := by
      rw [hrel]; exact Nat.dvd_of_mem_primeFactors hpidx
    rcases hp_prime.dvd_mul.mp hp_dvd with hin | hout
    · -- the `[M : M_F]`-part is coprime to `|M_F|`: `M_F` is Hall in `M`.
      exact (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall M).2 p
        (Nat.mem_primeFactors.mpr ⟨hp_prime, hin, Subgroup.index_ne_zero_of_finite⟩) hpH
    · -- the `[G : M]`-part divides `[G : M_σ]`, which avoids `σ(M)`-primes.
      have hpMσidx : p ∣ (OddOrder.BG.Ch3.S10.Msigma M).index :=
        hout.trans ⟨((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index,
          ((Nat.mul_comm _ _).trans
            (Subgroup.relIndex_mul_index (OddOrder.BG.Ch3.S10.Msigma_le M))).symm⟩
      exact hMsHall.2 p
        (Nat.mem_primeFactors.mpr ⟨hp_prime, hpMσidx, Subgroup.index_ne_zero_of_finite⟩) hpσ
  · -- `M_s = M_σ` (BG Prop 16.1); the Hall property is `Msigma_isHall` re-indexed to `π(M_σ)`.
    change Ch03.IsHallSubgroup
      (Nat.card ↥(OddOrder.GroupTheory.mainSubgroup M tau)).primeFactors
      (OddOrder.GroupTheory.mainSubgroup M tau)
    rw [OddOrder.BG.Ch4.S16.mainSubgroup_eq_Msigma hG hM hType]
    exact ⟨fun p hp => hp, fun p hpidx hp => hMsHall.2 p hpidx
      ((OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hM p).mp hp)⟩

/-- **Peterfalvi (8.12.b)**, faithful form: type I/II Sylow-complement centralizer control.

For `M` of type I or II, its genuine `(κ ∪ σ)ᶜ`-Hall complement `U` (`M = H ⋊ U` for type I,
`[M,M] = H ⋊ U` for type II), and every non-empty `X ⊆ U#` with `C_H(X) ≠ 1`, `M` is the unique
maximal subgroup of `G` over `C_G(X)`.  Proof: `⟨X⟩ ≤ U` is a nontrivial `(κ ∪ σ)ᶜ`-subgroup with
`C_{M_σ}(⟨X⟩) = C_{M_σ}(X) ≠ 1` (`M_F = M_σ` for type I/II), so BG **Theorem B(4)**
(`typeP_hall_small_subgroup_cyclic_tau2`) pins `ℳ(C_G(⟨X⟩)) = {M}`, and `C_G(X) = C_G(⟨X⟩)`
(`centralizer_closure`).  Reference: [BG], §16, Theorem B and Proposition 16.1. -/
theorem typeI_or_typeII_centralizer_unique_hall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M ∨ IsTypeII M) (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∀ X : Set G, X.Nonempty → X ⊆ sharpSubgroup U →
      maxNilpotentNormalHall M ⊓ Subgroup.centralizer X ≠ ⊥ →
        Subgroup.centralizer X ≤ M ∧ IsUniquelyMaximal (Subgroup.centralizer X) := by
  intro X hXne hXU hCX
  classical
  -- `Y = ⟨X⟩ ≤ U` is a nontrivial `(κ ∪ σ)ᶜ`-subgroup.
  set Y : Subgroup G := Subgroup.closure X with hYdef
  have hXsubU : X ⊆ (U : Set G) := hXU.trans (by rw [sharpSubgroup]; exact Set.sdiff_subset)
  have hYU : Y ≤ U := (Subgroup.closure_le U).mpr hXsubU
  obtain ⟨x0, hx0X⟩ := hXne
  have hx0mem : x0 ∈ (U : Set G) ∧ x0 ∉ ({1} : Set G) := hXU hx0X
  have hYne : Y ≠ ⊥ := fun hbot => hx0mem.2
    (by rw [Set.mem_singleton_iff]; exact Subgroup.mem_bot.mp (hbot ▸ Subgroup.subset_closure hx0X))
  -- `C_G(X) = C_G(Y)` and `M_F = M_σ` for type I/II.
  have hCeq : Subgroup.centralizer X = Subgroup.centralizer (Y : Set G) :=
    (Subgroup.centralizer_closure X).symm
  have hMFσ : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG hM hType
  have hCY : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (Y : Set G) ≠ ⊥ := by
    rw [← hCeq, ← hMFσ]; exact hCX
  -- BG Theorem B(4): `ℳ(C_G(Y)) = {M}`.
  have hM4 := (OddOrder.BG.Ch4.S14.typeP_hall_small_subgroup_cyclic_tau2 hG hM hUM hU hYU hYne hCY).1
  rw [hCeq]
  have hCleM : Subgroup.centralizer (Y : Set G) ≤ M :=
    (mem_maximalSubgroupsContaining.mp (hM4 ▸ Set.mem_singleton M)).2
  refine ⟨hCleM, IsUniquelyMaximal.of_unique_maximal
    (hCleM.trans_lt (lt_top_iff_ne_top.mpr hM.1)) hM hCleM (fun K hK hHK => ?_)⟩
  have hKmem : K ∈ maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) := ⟨hK, hHK⟩
  rw [hM4, Set.mem_singleton_iff] at hKmem
  exact hKmem

/-- **Peterfalvi (8.6.b II)**, canonical form: for a maximal subgroup `M` of Type II and **any**
type-`P` data on `M`, the complement `U` has `N_G(U) ⊄ M`.

Definition (8.6.b II) records `N_G(U) ⊄ M` for *the* `U` of the chosen `(8.4)` data; since any two
type-`P` complements of `H = M_F` in `M' = [M,M]` are `M'`-conjugate (Schur–Zassenhaus in the
solvable proper subgroup `M'`) and `N_G(U^g) = N_G(U)^g` with `g ∈ M' ≤ M`, the property is
independent of the witness.  Stated here so the (9.3) order relations can apply it to the type-`P`
data carried by `TypesIIIIIIVSetup` (which need not be the `IsTypeII` witness).  The
complement-conjugacy step is the residual obligation. -/
theorem typeII_normalizer_not_le_of_typePData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (data : TypePData M)
    (hM : M ∈ maximalSubgroups G) (hII : IsTypeII M) :
    ¬ Subgroup.normalizer (data.U : Set G) ≤ M := by
  classical
  obtain ⟨td⟩ := hII
  -- The Type-II witness carries `¬ N_G(U₀) ≤ M` for its own complement `U₀ = td.typeP.U`.
  -- `M_F = maxNilpotentNormalHall M` also equals `maxNilpotentNormalHall M'` (type II Fitting).
  have hMFeq : maxNilpotentNormalHall (derivedInG M) = maxNilpotentNormalHall M :=
    td.derived_fitting_eq.trans td.typeP.H_eq
  -- Kernel `N = M_F` inside `M' = derivedInG M`: normal and Hall (hence coprime index).
  haveI hNnormal : ((maxNilpotentNormalHall (derivedInG M)).subgroupOf (derivedInG M)).Normal :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal (derivedInG M)
  have hcop : Nat.Coprime
      (Nat.card ↥((maxNilpotentNormalHall (derivedInG M)).subgroupOf (derivedInG M)))
      ((maxNilpotentNormalHall (derivedInG M)).subgroupOf (derivedInG M)).index :=
    (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall (derivedInG M)).coprime_index
  -- Both `td.typeP.U` and `data.U` complement `M_F` in `M'` (Definition (8.4) `derived_complement`).
  have hTd_compl : Subgroup.IsComplement'
      ((maxNilpotentNormalHall (derivedInG M)).subgroupOf (derivedInG M))
      (td.typeP.U.subgroupOf (derivedInG M)) := by
    have h := td.typeP.derived_complement; rwa [td.typeP.H_eq, ← hMFeq] at h
  have hData_compl : Subgroup.IsComplement'
      ((maxNilpotentNormalHall (derivedInG M)).subgroupOf (derivedInG M))
      (data.U.subgroupOf (derivedInG M)) := by
    have h := data.derived_complement; rwa [data.H_eq, ← hMFeq] at h
  -- `M'` (and hence `M_F ≤ M'`) is solvable, giving Schur–Zassenhaus conjugacy of complements.
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hM'leM : derivedInG M ≤ M := Subgroup.map_subtype_le _
  haveI : IsSolvable ↥(derivedInG M) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hM'leM)
  obtain ⟨n, -, hnconj⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop (Or.inl inferInstance) hTd_compl hData_compl
  -- Lift the `M'`-conjugation to `G`: `conj (↑n) • td.typeP.U = data.U`, with `↑n ∈ M' ≤ M`.
  have hnM : (n : G) ∈ M := hM'leM (SetLike.coe_mem n)
  have hconjG : MulAut.conj (n : G) • td.typeP.U = data.U := by
    have h2 : MulAut.conj (n : G) •
          ((td.typeP.U.subgroupOf (derivedInG M)).map (derivedInG M).subtype)
          = (data.U.subgroupOf (derivedInG M)).map (derivedInG M).subtype := by
      rw [← map_subtype_conj_smul]
      exact congrArg (Subgroup.map (derivedInG M).subtype) hnconj
    rwa [Subgroup.map_subgroupOf_eq_of_le td.typeP.U_le,
      Subgroup.map_subgroupOf_eq_of_le data.U_le] at h2
  -- If `N_G(data.U) ≤ M`, transport back to `N_G(U₀) ≤ M`, contradicting the Type-II witness.
  intro hle
  refine td.normalizer_not_le ?_
  have htrans : Subgroup.normalizer (data.U : Set G)
      = MulAut.conj (n : G) • Subgroup.normalizer (td.typeP.U : Set G) := by
    rw [normalizer_pointwise_smul, hconjG]
  have hMconj : MulAut.conj (n : G) • M = M :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hnM)
  rw [htrans] at hle
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mp (hle.trans_eq hMconj.symm)

/-! ## (8.14)--(8.17): support notation and TI-covering facts

(Peterfalvi (8.13), `escapingCentralizers_control`, lives downstream in
`S10_MinimalSimpleBasic`, next to its `(8.13.a)`/`(8.13.b)` ingredients
`conjClassSetIn_typePV_isConj_conj_in_M` / `escaping_typePA0_mem_sigmaSharp_of_isTypeP1`.) -/

/- **Peterfalvi (8.16) — RETIRED** (false-as-stated + unconsumed; loop¹⁰⁶ finding, executed lane-a
/loop 2026-07-07).  The former `typeII_A_sets_TI` / `typeII_A_sets_normalizer` claimed the *full*
type-II sets `A(M) = (M')#`, `A_1(M) = M_σ#` are TI-subsets of `G` with normalizer `M`.  This is
**false**: `M_σ` is only *tamely* imbedded (BG Theorem II), `M_σ ∩ M_σ^g` cyclic (Theorem D(2))
rather than trivial, with escaping `σ`-elements (`C_G(x) ⊄ M`).  The *faithful* content — `A(M) − M_σ`
is a TI-subset — is Pf (8.10)/(8.12.c) = BG Theorem B(5), **proved** as
`OddOrder.BG.Ch4.S16.theoremB_A_minus_Msigma_isTISubset`; cite that directly.  The false sorries are
removed to prevent a bogus-witness false pin (cf. the `sibleyTarget`/`frobI` precedents). -/

/-- **Peterfalvi (8.14)**: the subgroup `R(x)`, shared as
`OddOrder.GroupTheory.supportKernel`. -/
noncomputable abbrev supportKernel (L M : Subgroup G) (X : Set G) (x : G) :=
  OddOrder.GroupTheory.supportKernel L M X x

/-- **Peterfalvi (8.14), the faithful per-`x` signalizer kernel `R(x)`** (Coq `FTsignalizer`,
PFsection8): on the escaping set (`x ∈ A` with `C_G(x) ⊄ M`) it is the BG Theorem-D signalizer
`FT_signalizer x = (N[x])_σ ⊓ C_G(x)` attached to the *supporting* maximal `N[x] ⊇ C_G(x)`; off
the escaping set `R(x) = 1`.  For the supporting `N[x]` (type `F` or `P₂`,
`signalizer_structure_of_mem_sigmaSharp`) one has `(N[x])_F = (N[x])_σ`
(`maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2`), so on the escaping set this is
Peterfalvi's `R(x) = C_{(N[x])_F}(x)`.

This is **not** `supportKernel M M A` (`= C_{M_F}(x)` on the escaping set): the self-based kernel
is unsatisfiable as an (2.2) kernel, since for escaping `x` both `C_{M_F}(x)` and `C_M(x)`
contain `x`, contradicting the `(2.2.b)` complement-disjointness and `(2.2.c)` coprimality (the
issue-8021 unfaithfulness, at the Dade-hypothesis carrier). -/
noncomputable def ftSupportKernel (M : Subgroup G) (A : Set G) (x : G) : Subgroup G := by
  classical
  exact
    if x ∈ OddOrder.GroupTheory.escapingCentralizerSet M A then
      OddOrder.BG.Ch4.S16.FT_signalizer x
    else ⊥

/-- Off the escaping set the faithful kernel is trivial. -/
theorem ftSupportKernel_eq_bot_of_not_escaping {M : Subgroup G} {A : Set G} {x : G}
    (hx : x ∉ OddOrder.GroupTheory.escapingCentralizerSet M A) :
    ftSupportKernel M A x = ⊥ := by
  unfold ftSupportKernel
  rw [if_neg hx]

/-- On the escaping set the faithful kernel is the BG signalizer. -/
theorem ftSupportKernel_eq_of_escaping {M : Subgroup G} {A : Set G} {x : G}
    (hx : x ∈ OddOrder.GroupTheory.escapingCentralizerSet M A) :
    ftSupportKernel M A x = OddOrder.BG.Ch4.S16.FT_signalizer x := by
  unfold ftSupportKernel
  rw [if_pos hx]

/-- The escaping-set membership (hence the faithful kernel) only depends on the point, not on
which support set `A ∋ x` it is tested against: for `x ∈ A₁ ⊆ A`,
`ftSupportKernel M A₁ x = ftSupportKernel M A x`.  This is what makes the (2.11) restriction of a
faithful Dade datum to a smaller support again faithful. -/
theorem ftSupportKernel_restrict {M : Subgroup G} {A A₁ : Set G} (hA₁A : A₁ ⊆ A) {x : G}
    (hx : x ∈ A₁) :
    ftSupportKernel M A₁ x = ftSupportKernel M A x := by
  by_cases hC : Subgroup.centralizer ({x} : Set G) ≤ M
  · rw [ftSupportKernel_eq_bot_of_not_escaping (fun h => h.2 hC),
      ftSupportKernel_eq_bot_of_not_escaping (fun h => h.2 hC)]
  · rw [ftSupportKernel_eq_of_escaping ⟨hx, hC⟩, ftSupportKernel_eq_of_escaping ⟨hA₁A hx, hC⟩]

/-- **Peterfalvi (8.14), the faithful thickened support** `Ã(M,A) = ⋃_{x∈A} (x·R(x))^G`, with the
per-`x` signalizer `R = ftSupportKernel M A`. -/
noncomputable def ftThickenedSupport (M : Subgroup G) (A : Set G) : Set G :=
  {y | ∃ x ∈ A, y ∈ conjClassSet (OddOrder.GroupTheory.leftCosetSet x (ftSupportKernel M A x))}

/-- **Peterfalvi (8.14)**: the thickened support set
`⋃_{x ∈ X} (x R(x))^G`, shared as `OddOrder.GroupTheory.thickenedSupport`. -/
noncomputable abbrev thickenedSupport (L M : Subgroup G) (X : Set G) :=
  OddOrder.GroupTheory.thickenedSupport L M X

/-- **Peterfalvi (8.14)**: the thickened `A_1(M)`. -/
noncomputable abbrev thickenedA1 (L M : Subgroup G) (tau : PeterfalviType) :=
  OddOrder.GroupTheory.thickenedA1 L M tau

/-- **Peterfalvi (8.14)**: the thickened `A(M)` for type-I data. -/
noncomputable abbrev typeIThickenedA (L M : Subgroup G) (data : TypeIData M) :=
  OddOrder.GroupTheory.typeIThickenedA L M data

/-- **Peterfalvi (8.14)**: the thickened `A(M)` for type-`P` data. -/
noncomputable abbrev typePThickenedA (L M : Subgroup G) (data : TypePData M) :=
  OddOrder.GroupTheory.typePThickenedA L M data

/-- **Peterfalvi (8.14)**: the thickened `A_0(M)` for type-`P` data. -/
noncomputable abbrev typePThickenedA0 (L M : Subgroup G) (data : TypePData M) :=
  OddOrder.GroupTheory.typePThickenedA0 L M data

/-- Carrier for the Dade-hypothesis part of **Peterfalvi (8.15)** for a single
support set `A`.

It records the part already expressible with the existing §4 API: `L = M`,
`N_G(A) = M`, the Dade Hypothesis (2.2), the recovered formula `H(a)=R(a)` with
the *faithful per-`x`* kernel `ftSupportKernel` of (8.14), and the
`M`-conjugation invariance of the kernels (Peterfalvi's `R(x^m) = R(x)^m`, from
the uniqueness of the supporting maximal `N[x]`, BG Theorem D).  The §4 Dade
support then *is* the faithful thickened support of (8.14)
(`dadeSupport_eq_ftThickenedSupport`, a lemma rather than a field).  The later
Hypothesis (4.6)/(5.2) specializations add character-family data and are kept as
a separate TODO below.

⚠ The earlier revision pinned `H(a) = supportKernel M M A a = C_{M_F}(a)`, which is
**unsatisfiable** whenever `A` has an escaping element (see `ftSupportKernel`); consumers
(`S12.Hypothesis`, `S14.Hypothesis`) were therefore vacuously parameterized.  Fixed 2026-07-02
(lane b, carve-out issue 0096). -/
structure DadeSupportHypothesisData [Fintype G] (M : Subgroup G) (A : Set G) where
  /-- Peterfalvi (8.15): `M = N_G(A)`. -/
  normalizer_eq : Subgroup.normalizer A = M
  /-- Peterfalvi (8.15): Hypothesis (2.2) holds with `L = M`. -/
  dade : OddOrder.Peterfalvi.S04.Hypothesis G A M
  /-- Peterfalvi (8.15): the subgroups in Hypothesis (2.2) are the recovered
  faithful `R(a)` from (8.14). -/
  H_eq_ftSupportKernel :
    ∀ a : {a : G // a ∈ A}, dade.H a = ftSupportKernel M A a.1
  /-- Peterfalvi (8.14)/(8.15): the kernels are `M`-conjugation invariant (`R(x^m) = R(x)^m`,
  by the uniqueness of the supporting maximal `N[x^m] = N[x]^m`, BG Theorem D). -/
  hconj : dade.HConjInvariant

namespace DadeSupportHypothesisData

/-- The §4 Dade support of a faithful (8.15) datum is the faithful thickened support
`Ã(M,A) = ⋃_{x∈A}(x·R(x))^G` of (8.14). -/
theorem dadeSupport_eq_ftThickenedSupport [Fintype G] {M : Subgroup G} {A : Set G}
    (d : DadeSupportHypothesisData M A) :
    d.dade.dadeSupport = ftThickenedSupport M A := by
  ext g
  rw [OddOrder.Peterfalvi.S04.Hypothesis.mem_dadeSupport_iff]
  constructor
  · rintro ⟨a, h, hh, hconj⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    refine ⟨a.1, a.2, ?_⟩
    rw [mem_conjClassSet]
    refine ⟨a.1 * h, ⟨h, ?_, rfl⟩, c, hc⟩
    rw [SetLike.mem_coe, ← d.H_eq_ftSupportKernel a]
    exact hh
  · rintro ⟨x, hx, hg⟩
    rw [mem_conjClassSet] at hg
    obtain ⟨t, ⟨h, hh, rfl⟩, c, hc⟩ := hg
    refine ⟨⟨x, hx⟩, h, ?_, isConj_iff.mpr ⟨c, hc⟩⟩
    rw [d.H_eq_ftSupportKernel ⟨x, hx⟩]
    exact SetLike.mem_coe.mp hh

end DadeSupportHypothesisData

end OddOrder.Peterfalvi.S10
