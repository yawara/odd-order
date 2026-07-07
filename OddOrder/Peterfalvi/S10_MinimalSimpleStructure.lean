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

The proof is a BG Section 16 consequence, not a local Peterfalvi argument. -/
theorem hall_maxNilpotentNormalHall_and_mainSubgroup [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {tau : PeterfalviType} (hType : HasPeterfalviType tau M) :
    Ch03.IsHallSubgroup (Nat.card ↥(maxNilpotentNormalHall M)).primeFactors
        (maxNilpotentNormalHall M) ∧
      Ch03.IsHallSubgroup (Nat.card ↥(mainSubgroup M tau)).primeFactors
        (mainSubgroup M tau) := by
  sorry

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
  have hXsubU : X ⊆ (U : Set G) := hXU.trans (by rw [sharpSubgroup]; exact Set.diff_subset)
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

/-- **Peterfalvi (8.13)**: centralizers escaping a maximal subgroup are controlled
by `A_1(M)` and a unique maximal subgroup of type I or II.

Here `X` is either `A_1(M)` or the type-`P` set `A_0(M)` from (8.10). -/
theorem escapingCentralizers_control [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {tau : PeterfalviType} (hType : HasPeterfalviType tau M) {X : Set G}
    (hX : X = A1 M tau ∨ ∃ data : TypePData M, X = typePA0 M data) :
    let D := escapingCentralizerSet M X
    D ⊆ A1 M tau ∧
      ∀ x : G, x ∈ D →
        ∃! L : Subgroup G,
          L ∈ maximalSubgroups G ∧ Subgroup.centralizer ({x} : Set G) ≤ L ∧
            (IsTypeI L ∨ IsTypeII L) := by
  sorry

/-! ## (8.14)--(8.17): support notation and TI-covering facts -/

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

/-! ### (8.15) assembly for type I

Shallow facts about the support `A(M) = typeIA M data` (membership, sharpness, `M`-invariance,
nonemptiness), the two genuinely-deep (8.13) obligations as precise `sorry` pins, and the faithful
(8.15) construction assembled from them.  The pins are exactly the pieces Peterfalvi's (8.15) proof
cites: "Statements (2.2.a, b, c) hold by (8.13.a, c1, c2)" — (8.13) = BG §16 Theorem II +
Theorem B(5) + Theorem D(4) (Coq `FTsupport_facts`, PFsection8). -/

/-- Elements of `A(M)` are nonidentity: `A(M) ⊆ G^#`. -/
theorem typeIA_subset_sharp (M : Subgroup G) (data : TypeIData M) :
    typeIA M data ⊆ OddOrder.Peterfalvi.S04.sharp (Set.univ : Set G) := by
  rintro y ⟨-, hy1, -⟩
  exact OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ y, hy1⟩

/-- `A(M) ⊆ M`. -/
theorem typeIA_subset (M : Subgroup G) (data : TypeIData M) :
    typeIA M data ⊆ (M : Set G) :=
  fun _ hy => hy.1

/-- Conjugation preserves nonidentity: `m·a·m⁻¹ ≠ 1` for `a ≠ 1`. -/
private theorem conj_ne_one {m a : G} (ha : a ≠ 1) : m * a * m⁻¹ ≠ 1 := fun h =>
  ha (by
    have h2 : a = m⁻¹ * (m * a * m⁻¹) * m := by group
    rw [h] at h2
    simpa using h2)

/-- `A(M)` is `M`-conjugation invariant: `m·A(M)·m⁻¹ = A(M)` pointwise.  The centralizer witness
`x ∈ H^#` transports along the `M`-normality of `H = M_F` (`maxNilpotentNormalHall_le_normalizer`). -/
theorem typeIA_conj_mem (M : Subgroup G) (data : TypeIData M) {m : G} (hm : m ∈ M) {a : G}
    (ha : a ∈ typeIA M data) : m * a * m⁻¹ ∈ typeIA M data := by
  obtain ⟨haM, ha1, x, hx, hax⟩ := ha
  obtain ⟨hxH, hx1⟩ := (Set.mem_diff x).mp hx
  have hmxH : m * x * m⁻¹ ∈ maxNilpotentNormalHall M := by
    have hnorm := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M hm
    rw [Subgroup.mem_normalizer_iff] at hnorm
    exact (hnorm x).mp (data.typeF.H_eq ▸ (SetLike.mem_coe.mp hxH))
  refine ⟨mul_mem (mul_mem hm haM) (inv_mem hm), conj_ne_one ha1, m * x * m⁻¹, ?_, ?_⟩
  · exact (Set.mem_diff _).mpr ⟨data.typeF.H_eq ▸ (SetLike.mem_coe.mpr hmxH),
      conj_ne_one (fun h => hx1 (Set.mem_singleton_iff.mpr h))⟩
  · rw [Subgroup.mem_centralizer_singleton_iff] at hax ⊢
    calc m * a * m⁻¹ * (m * x * m⁻¹) = m * (a * x) * m⁻¹ := by group
      _ = m * (x * a) * m⁻¹ := by rw [hax]
      _ = m * x * m⁻¹ * (m * a * m⁻¹) := by group

/-- `A(M)` is nonempty (any `x ∈ H^#` lies in `C_M(x)^#`). -/
theorem typeIA_nonempty (M : Subgroup G) (data : TypeIData M) :
    (typeIA M data).Nonempty := by
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp data.typeF.H_nontrivial
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  exact ⟨a.1, data.typeF.H_le a.2, ha1',
    a.1, (Set.mem_diff _).mpr ⟨SetLike.mem_coe.mpr a.2, fun h => ha1' (Set.mem_singleton_iff.mp h)⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

/-- **The type-`F` complement `U` is a `(κ ∪ σ)′`-Hall subgroup of `M`.**  For type I,
`κ(M) = ∅` (Proposition 16.1) and `H = M_F = M_σ` is the `σ`-Hall of `G`, so the complement
`U` of `H` in `M` has `σ′`-order (`|U| = |M : H|` divides `|G : M_σ|`) and `σ`-index
(`|M : U| = |H|`).  Supplies the `hU` input of BG Theorem II
(`theoremII_tame_embedding`) from the shared type-I data. -/
theorem typeF_complement_isHall_kappa_sigma_compl [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIData M) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (data.typeF.U.subgroupOf M) := by
  have hκ : OddOrder.BG.Ch4.S14.kappa M = ∅ :=
    (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hM).mp ⟨data⟩
  have hHMσ : data.typeF.H = OddOrder.BG.Ch3.S10.Msigma M := by
    rw [data.typeF.H_eq]
    exact OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hM (Or.inl ⟨data⟩)
  have hcompl := data.typeF.complement
  have hHall := OddOrder.BG.Ch3.S10.Msigma_isHall hG hM
  constructor
  · -- primes of `|U|` avoid `κ ∪ σ = σ`: `|U| = |M : H|` divides `|G : M_σ|`, a `σ′`-number.
    intro p hp
    simp only [Set.mem_compl_iff, Set.mem_union, hκ, Set.mem_empty_iff_false, false_or]
    intro hpσ
    have hidx : (data.typeF.H.subgroupOf M).index
        = Nat.card (data.typeF.U.subgroupOf M) := hcompl.symm.index_eq_card
    have hrel : (data.typeF.H.subgroupOf M).index * M.index = data.typeF.H.index :=
      Subgroup.relIndex_mul_index data.typeF.H_le
    have hdvd : p ∣ (OddOrder.BG.Ch3.S10.Msigma M).index := by
      rw [← hHMσ, ← hrel]
      exact Dvd.dvd.mul_right (hidx ▸ (Nat.mem_primeFactors.mp hp).2.1) _
    have hidx_ne : (OddOrder.BG.Ch3.S10.Msigma M).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    exact hHall.2 p (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hp).1, hdvd, hidx_ne⟩) hpσ
  · -- primes of `|M : U| = |H| = |M_σ|` lie in `σ ⊆ κ ∪ σ`.
    intro p hp
    simp only [Set.mem_compl_iff, Set.mem_union, not_not, hκ, Set.mem_empty_iff_false, false_or]
    have hidxU : (data.typeF.U.subgroupOf M).index
        = Nat.card (data.typeF.H.subgroupOf M) := hcompl.index_eq_card
    have hcardH : Nat.card (data.typeF.H.subgroupOf M) = Nat.card data.typeF.H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeF.H_le).toEquiv
    have hpH : p ∣ Nat.card (OddOrder.BG.Ch3.S10.Msigma M) := by
      rw [← hHMσ, ← hcardH, ← hidxU]
      exact (Nat.mem_primeFactors.mp hp).2.1
    exact hHall.1 p (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hp).1, hpH, Nat.card_pos.ne'⟩)

/-- **The type-I support `A(M)` lies in BG's Theorem E set `A(M) = ASet M U`.**  A point
`y ∈ A(M)` is a nonidentity element of `M` centralizing some `x ∈ H^# = M_σ^#`, so
`M_σ ⊓ C_G(y) ≠ ⊥` (`y ∈ \widehat{M_σ}`), and `y ∈ M = U ⊔ M_σ` by the type-`F` complement
decomposition.  The support-set bridge feeding BG Theorem II into the (8.13) pins. -/
theorem typeIA_subset_ASet [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypeIData M) :
    typeIA M data ⊆ OddOrder.BG.Ch4.S16.ASet M data.typeF.U := by
  have hHMσ : data.typeF.H = OddOrder.BG.Ch3.S10.Msigma M := by
    rw [data.typeF.H_eq]
    exact OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hM (Or.inl ⟨data⟩)
  rintro y ⟨hyM, _hy1, x, hxH, hyC⟩
  obtain ⟨hxHmem, hx1⟩ := (Set.mem_diff _).mp hxH
  refine ⟨⟨hyM, ?_⟩, ?_⟩
  · -- `x ∈ M_σ ⊓ C_G(y)` is a nonidentity witness.
    intro hbot
    have hxC : x ∈ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (Subgroup.mem_centralizer_iff.mp hyC x (Set.mem_singleton x)).symm
    have hxmem : x ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hHMσ ▸ SetLike.mem_coe.mp hxHmem, hxC⟩
    rw [hbot] at hxmem
    exact hx1 (Set.mem_singleton_iff.mpr (Subgroup.mem_bot.mp hxmem))
  · -- `y ∈ U ⊔ M_σ`: decompose `y = h · u` along the type-`F` complement.
    obtain ⟨⟨h, u⟩, hhu, -⟩ := Subgroup.IsComplement.existsUnique
      data.typeF.complement (⟨y, hyM⟩ : ↥M)
    have hyval : ((h : ↥M) : G) * ((u : ↥M) : G) = y := by
      simpa using congrArg (fun z : ↥M => (z : G)) hhu
    have hh : ((h : ↥M) : G) ∈ OddOrder.BG.Ch3.S10.Msigma M :=
      hHMσ ▸ Subgroup.mem_subgroupOf.mp h.2
    have hu : ((u : ↥M) : G) ∈ data.typeF.U := Subgroup.mem_subgroupOf.mp u.2
    rw [SetLike.mem_coe, ← hyval]
    exact mul_mem (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left hu)

/-- **Peterfalvi (8.13.a) for the type-I support**: two `G`-conjugate elements of `A(M)` are
already `M`-conjugate.  BG §16 Theorem II conjunct 1 (`theoremII_tame_embedding`, whose
`X = ASet M U` branch receives `A(M)` via `typeIA_subset_ASet`); the `κ`-Hall input is `K = ⊥`
(`κ(M) = ∅` for type I) and the `(κ ∪ σ)′`-Hall input is the type-`F` complement
(`typeF_complement_isHall_kappa_sigma_compl`). -/
theorem typeIA_isConj_conj_in_M [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypeIData M)
    {a b : G} (ha : a ∈ typeIA M data) (hb : b ∈ typeIA M data) (hab : IsConj a b) :
    ∃ m : G, m ∈ M ∧ m * a * m⁻¹ = b := by
  have hκ : OddOrder.BG.Ch4.S14.kappa M = ∅ :=
    (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hM).mp ⟨data⟩
  have hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M)
      ((⊥ : Subgroup G).subgroupOf M) := by
    rw [Subgroup.bot_subgroupOf, OddOrder.Isaacs.Ch03.IsHallSubgroup.bot_iff]
    intro p _
    rw [hκ]
    exact Set.notMem_empty p
  have hII := OddOrder.BG.Ch4.S16.theoremII_tame_embedding hG hM bot_le data.typeF.U_le hK
    (typeF_complement_isHall_kappa_sigma_compl hG hM data) (Or.inl rfl)
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  obtain ⟨m, hmM, hmb⟩ := hII.1 a (typeIA_subset_ASet hG hM data ha)
    b (typeIA_subset_ASet hG hM data hb) ⟨g, hg.symm⟩
  exact ⟨m, hmM, hmb.symm⟩

/-- `MulAut` smul is `map` along the automorphism (local copy of the S09/S11 helper). -/
private theorem mulAut_smul_eq_map' (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := by
  rw [Subgroup.pointwise_smul_def]
  rfl

/-- `τ₂` is conjugation-equivariant (from `σ`-equivariance and the `pRank` invariance under
the conjugation isomorphism). -/
private theorem tau2_conj_smul' [Finite G] (g : G) (M : Subgroup G) :
    OddOrder.BG.Ch3.S12.tau2 (MulAut.conj g • M) = OddOrder.BG.Ch3.S12.tau2 M := by
  have e : ↥M ≃* ↥(MulAut.conj g • M) :=
    (Subgroup.equivMapOfInjective M (MulAut.conj g : G →* G)
      (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr (mulAut_smul_eq_map' (MulAut.conj g) M).symm)
  ext p
  simp only [OddOrder.BG.Ch3.S12.tau2, Set.mem_setOf_eq,
    OddOrder.BG.Ch4.S14.sigma_conj_smul_eq]
  rw [OddOrder.BG.Ch3.S13.pRank_eq_of_mulEquiv (p := p) e.symm]

/-- **Peterfalvi (8.13.c2) coprimality core at a `σ`-sharp point** — the `σ`-decomposition-generic
form (`non_disjoint_signalizer_frobenius`, BG Lemma 14.13(a), takes any maximal `S`; the type-I
`escaping_sigma_disjoint_centralizer` only specialises it by deriving `z ∈ M_σ^#` from `κ(S) = ∅`
and `w ∈ M_σ` from the type-`F` Frobenius absorption — both are hypotheses here).

For an escaping `z ∈ M_σ^#` and any `w ∈ M_σ^#`, no prime `p ∈ σ(N[z])` divides `|C_S(w)|`:
a common `p ∈ σ(N[z]) ∩ π(S)` makes `S` Frobenius with kernel `S_σ` and `τ₂(S) = ∅`; `w ∈ S_σ`
absorbs a Cauchy `p`-element of `C_S(w)` into `S_σ`, so `p ∈ σ(S)`, forcing `N[z]` conjugate to `S`
(`sigma_disjoint_of_nonconjugate`) and transporting `τ₂(N[z]) ∋ π(⟨z⟩) ≠ ∅` onto `τ₂(S) = ∅`. -/
theorem escaping_sigmaSharp_disjoint_centralizer [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hS : S ∈ maximalSubgroups G)
    {z : G} (hσz : z ∈ OddOrder.BG.Ch4.S14.sigmaSharp S)
    (hzesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ S)
    {w : G} (hwMσ : w ∈ OddOrder.BG.Ch3.S10.Msigma S) (hw1 : w ≠ 1)
    {p : ℕ} (hpp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase z))
    (hpC : p ∣ Nat.card (OddOrder.Peterfalvi.S04.centralizerIn S w)) : False := by
  classical
  have hz1 : z ≠ 1 := hσz.2
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement z).ncard := by
    by_contra h
    exact hzesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hS hσz.1 hz1
      (not_lt.mp h))
  -- `p ∈ π(S)` (it divides `|C_S(w)| ∣ |S|`), so Lemma 14.13(a) fires.
  have hpS : p ∈ OddOrder.BG.Ch4.S14.piSet S := by
    refine Nat.mem_primeFactors.mpr ⟨hpp, hpC.trans ?_, Nat.card_pos.ne'⟩
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨-, htau2S, U, -, hfrobU⟩ :=
    OddOrder.BG.Ch4.S16.non_disjoint_signalizer_frobenius hG hS hσz hgt ⟨p, hpσ, hpS⟩
  -- Frobenius kernel absorption: commuting with a nontrivial `S_σ`-element lands in `S_σ`.
  have hker : ∀ {u v : G}, u ∈ S → v ∈ OddOrder.BG.Ch3.S10.Msigma S → v ≠ 1 →
      Commute u v → u ∈ OddOrder.BG.Ch3.S10.Msigma S := by
    intro u v huS hvMσ hv1 hcomm
    have hvS : v ∈ S := OddOrder.BG.Ch3.S10.Msigma_le S hvMσ
    have hcent := OddOrder.Isaacs.Ch06.IsFrobeniusGroup.centralizer_kernel_le hfrobU
      (⟨v, hvS⟩ : ↥S) (Subgroup.mem_subgroupOf.mpr hvMσ)
      (fun h1 => hv1 (congrArg Subtype.val h1))
    have humem : (⟨u, huS⟩ : ↥S) ∈
        Subgroup.centralizer ({(⟨v, hvS⟩ : ↥S)} : Set ↥S) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hcomm.eq
    exact Subgroup.mem_subgroupOf.mp (hcent humem)
  have hwS : w ∈ S := OddOrder.BG.Ch3.S10.Msigma_le S hwMσ
  -- a Cauchy `p`-element of `C_S(w)` lies in `S_σ` (absorption), so `p ∈ σ(S)`.
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card' p hpC
  have hcS : (c : G) ∈ S := (Subgroup.mem_inf.mp c.2).1
  have hcC : Commute (c : G) w := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).2
    exact this
  have hcMσ : (c : G) ∈ OddOrder.BG.Ch3.S10.Msigma S :=
    hker hcS hwMσ hw1 hcC
  have hpσS : p ∈ OddOrder.BG.Ch3.S10.sigma S := by
    refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup S p (Nat.mem_primeFactors.mpr
      ⟨hpp, ?_, Nat.card_pos.ne'⟩)
    have hcord : orderOf ((⟨(c : G), hcMσ⟩ :
        ↥(OddOrder.BG.Ch3.S10.Msigma S))) = p := by
      rw [← hc_ord]
      exact (orderOf_injective (OddOrder.BG.Ch3.S10.Msigma S).subtype
        (OddOrder.BG.Ch3.S10.Msigma S).subtype_injective
        (⟨(c : G), hcMσ⟩ : ↥(OddOrder.BG.Ch3.S10.Msigma S))).symm.trans
        (orderOf_injective (OddOrder.Peterfalvi.S04.centralizerIn S w).subtype
          (OddOrder.Peterfalvi.S04.centralizerIn S w).subtype_injective c)
    rw [← hcord]
    exact orderOf_dvd_natCard _
  -- `σ(N[z]) ∩ σ(S) ≠ ∅` forces `N[z] ~ S`, transporting `τ₂`.
  have hN₀max : OddOrder.BG.Ch4.S16.FT_signalizerBase z ∈ maximalSubgroups G := by
    obtain ⟨N₀, hN₀⟩ :=
      OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
        hG hS hσz hzesc
    have hbr : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement z).ncard ∧
        (maximalSubgroupsContaining (Subgroup.centralizer ({z} : Set G))).Nonempty :=
      ⟨hgt, ⟨N₀, by rw [hN₀]; rfl⟩⟩
    have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase z = hbr.2.choose :=
      dif_pos hbr
    rw [hb]
    exact (mem_maximalSubgroupsContaining.mp hbr.2.choose_spec).1
  have hconj : ∃ g : G, MulAut.conj g • OddOrder.BG.Ch4.S16.FT_signalizerBase z = S := by
    by_contra hnc2
    exact Set.disjoint_left.mp
      (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hN₀max hS hnc2) hpσ hpσS
  obtain ⟨g, hg⟩ := hconj
  obtain ⟨Nstr, ⟨hNstr_max, hNstr_C, -, -, hNstr_tau2, -, -⟩, -⟩ :=
    OddOrder.BG.Ch4.S16.signalizer_structure_of_mem_sigmaSharp hG hS hσz hgt
  have hNstr_eq : Nstr = OddOrder.BG.Ch4.S16.FT_signalizerBase z := by
    obtain ⟨N₀, hN₀⟩ :=
      OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
        hG hS hσz hzesc
    have huniq : ∀ L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({z} : Set G)),
        L = N₀ := by
      intro L hL
      rw [hN₀, Set.mem_singleton_iff] at hL
      exact hL
    have hbr : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement z).ncard ∧
        (maximalSubgroupsContaining (Subgroup.centralizer ({z} : Set G))).Nonempty :=
      ⟨hgt, ⟨N₀, by rw [hN₀]; rfl⟩⟩
    have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase z = hbr.2.choose := dif_pos hbr
    rw [hb, huniq _ hbr.2.choose_spec,
      huniq Nstr (mem_maximalSubgroupsContaining.mpr ⟨hNstr_max, hNstr_C⟩)]
  -- a prime of `orderOf z` lies in `τ₂(N[z]) = τ₂(S) = ∅`, but `z ≠ 1` — contradiction.
  set p₀ : ℕ := (orderOf z).minFac with hp₀
  have hp₀p : p₀.Prime := Nat.minFac_prime (fun h => hz1 (orderOf_eq_one_iff.mp h))
  have hp₀tau2 : p₀ ∈ OddOrder.BG.Ch3.S12.tau2 Nstr := by
    refine hNstr_tau2 p₀ ?_
    refine Nat.mem_primeFactors.mpr ⟨hp₀p, ?_, Nat.card_pos.ne'⟩
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
    exact Nat.minFac_dvd _
  rw [hNstr_eq, show OddOrder.BG.Ch4.S16.FT_signalizerBase z = MulAut.conj g⁻¹ • S from by
      rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul],
    tau2_conj_smul'] at hp₀tau2
  exact htau2S p₀ hp₀p hp₀tau2

/-- **The (8.13.c2) coprimality core**: for an escaping point `z` of the type-I support `A(S)`,
no prime of `σ(N[z])` (`N[z] = FT_signalizerBase z` the supporting maximal) divides `|C_S(w)|`
for any `w ∈ A(S)`.

BG Theorem II conjunct (c): a common prime `p ∈ σ(N[z]) ∩ π(C_S(w)) ⊆ σ(N[z]) ∩ π(S)` fires
Lemma 14.13(a) (`non_disjoint_signalizer_frobenius`), making `S` a Frobenius group with kernel
`S_σ` and `τ₂(S) = ∅`.  The Frobenius kernel absorbs centralizers
(`IsFrobeniusGroup.centralizer_kernel_le`): the `A(S)`-point `w` centralizes a nontrivial
element of `S_F = S_σ`, so `w ∈ S_σ`, and a Cauchy `p`-element of `C_S(w)` then also lies in
`S_σ`, giving `p ∈ σ(S)`.  Now `σ(N[z]) ∩ σ(S) ≠ ∅` forces `N[z]` conjugate to `S` (Theorem
13.9, `sigma_disjoint_of_nonconjugate`), transporting `τ₂(N[z]) ∋ π(⟨z⟩) ≠ ∅`
(`signalizer_structure_of_mem_sigmaSharp`) onto `τ₂(S) = ∅` — contradiction. -/
theorem escaping_sigma_disjoint_centralizer [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (dS : TypeIData S)
    {z : G} (hz : z ∈ OddOrder.GroupTheory.escapingCentralizerSet S (typeIA S dS))
    {w : G} (hw : w ∈ typeIA S dS) {p : ℕ} (hpp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase z))
    (hpC : p ∣ Nat.card (OddOrder.Peterfalvi.S04.centralizerIn S w)) : False := by
  classical
  obtain ⟨hzA, hzesc⟩ := hz
  have hz1 : z ≠ 1 := hzA.2.1
  -- `z` is σ-sharp with more than one σ-maximal.
  have hκ : OddOrder.BG.Ch4.S14.kappa S = ∅ :=
    (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hS).mp ⟨dS⟩
  have hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa S)
      ((⊥ : Subgroup G).subgroupOf S) := by
    rw [Subgroup.bot_subgroupOf, OddOrder.Isaacs.Ch03.IsHallSubgroup.bot_iff]
    intro q _
    rw [hκ]
    exact Set.notMem_empty q
  have hσz : z ∈ OddOrder.BG.Ch4.S14.sigmaSharp S :=
    OddOrder.BG.Ch4.S16.mem_sigmaSharp_of_mem_aSet_of_escape hG hS bot_le dS.typeF.U_le hK
      (typeF_complement_isHall_kappa_sigma_compl hG hS dS) (Or.inl rfl)
      (typeIA_subset_ASet hG hS dS hzA) hz1 hzesc
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement z).ncard := by
    by_contra h
    exact hzesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hS hσz.1 hz1
      (not_lt.mp h))
  -- `p ∈ π(S)` (it divides `|C_S(w)| ∣ |S|`), so Lemma 14.13(a) fires.
  have hpS : p ∈ OddOrder.BG.Ch4.S14.piSet S := by
    refine Nat.mem_primeFactors.mpr ⟨hpp, hpC.trans ?_, Nat.card_pos.ne'⟩
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨-, -, U, -, hfrobU⟩ :=
    OddOrder.BG.Ch4.S16.non_disjoint_signalizer_frobenius hG hS hσz hgt ⟨p, hpσ, hpS⟩
  -- Frobenius kernel absorption: commuting with a nontrivial `S_σ`-element lands in `S_σ`.
  have hker : ∀ {u v : G}, u ∈ S → v ∈ OddOrder.BG.Ch3.S10.Msigma S → v ≠ 1 →
      Commute u v → u ∈ OddOrder.BG.Ch3.S10.Msigma S := by
    intro u v huS hvMσ hv1 hcomm
    have hvS : v ∈ S := OddOrder.BG.Ch3.S10.Msigma_le S hvMσ
    have hcent := OddOrder.Isaacs.Ch06.IsFrobeniusGroup.centralizer_kernel_le hfrobU
      (⟨v, hvS⟩ : ↥S) (Subgroup.mem_subgroupOf.mpr hvMσ)
      (fun h1 => hv1 (congrArg Subtype.val h1))
    have humem : (⟨u, huS⟩ : ↥S) ∈
        Subgroup.centralizer ({(⟨v, hvS⟩ : ↥S)} : Set ↥S) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hcomm.eq
    exact Subgroup.mem_subgroupOf.mp (hcent humem)
  -- `w ∈ S_σ`: it centralizes a nontrivial element of `S_F = S_σ` (type-`F` absorption).
  have hMFMσ : maxNilpotentNormalHall S = OddOrder.BG.Ch3.S10.Msigma S :=
    OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hS (Or.inl ⟨dS⟩)
  obtain ⟨hwS, hw1, h, hh, hwC⟩ := hw
  obtain ⟨hhH, hh1⟩ := (Set.mem_diff _).mp hh
  have hh1' : h ≠ 1 := fun he => hh1 (Set.mem_singleton_iff.mpr he)
  have hhMσ : h ∈ OddOrder.BG.Ch3.S10.Msigma S := by
    rw [← hMFMσ, ← dS.typeF.H_eq]
    exact SetLike.mem_coe.mp hhH
  have hwMσ : w ∈ OddOrder.BG.Ch3.S10.Msigma S := by
    refine hker hwS hhMσ hh1' ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp hwC
  -- the remaining `σ`-generic contradiction is the shared coprimality core.
  exact escaping_sigmaSharp_disjoint_centralizer hG hS hσz hzesc hwMσ hw1 hpp hpσ hpC

/-- **Peterfalvi (8.13.c1) at a `σ`-sharp escaping point** — the `σ`-decomposition-generic core of
`escaping_typeIA_signalizer_structure`, shared by every Peterfalvi type.  For `a ∈ M_σ^#` with
`C_G(a) ⊄ M`, the signalizer `R(a) = FT_signalizer a` gives `C_G(a) = R(a) ⋊ C_M(a)`:
- join `C_G(a) = R(a) ⊔ C_M(a)`, disjointness `R(a) ⊓ C_M(a) = ⊥`, and normality of `R(a)` in `C_G(a)`.

The escaping hypothesis forces `1 < |𝓜_σ(a)|` (`centralizer_le_of_maximalSigma_le_one`), so the
supporting maximal is pinned (`N[a] = FT_signalizerBase a`, singleton uniqueness) and Theorem D(3)'s
complement structure at `M ∈ 𝓜_σ(a)` (`signalizer_structure_of_mem_sigmaSharp` →
`signalizer_centralizer_isComplement`) supplies the split, with normality from
`FT_signalizer_normal_in_centralizer`.  The type-specific (8.13.c2) coprimality conjunct is *not*
included here — it is proved per type (`escaping_sigma_disjoint_centralizer` for type I). -/
theorem escaping_sigmaSharp_signalizer_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {a : G}
    (hσa : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (haesc : ¬ Subgroup.centralizer ({a} : Set G) ≤ M) :
    Subgroup.centralizer ({a} : Set G)
        = OddOrder.BG.Ch4.S16.FT_signalizer a ⊔ OddOrder.Peterfalvi.S04.centralizerIn M a ∧
      Disjoint (OddOrder.BG.Ch4.S16.FT_signalizer a)
        (OddOrder.Peterfalvi.S04.centralizerIn M a) ∧
      (∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ OddOrder.BG.Ch4.S16.FT_signalizer a,
        c * y * c⁻¹ ∈ OddOrder.BG.Ch4.S16.FT_signalizer a) := by
  classical
  have ha1 : a ≠ 1 := hσa.2
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a).ncard := by
    by_contra h
    exact haesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hM hσa.1 ha1
      (not_lt.mp h))
  obtain ⟨N₀, hN₀⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG hM hσa haesc
  have huniq : ∀ L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G)),
      L = N₀ := by
    intro L hL
    rw [hN₀, Set.mem_singleton_iff] at hL
    exact hL
  have hbr : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G))).Nonempty :=
    ⟨hgt, ⟨N₀, by rw [hN₀]; rfl⟩⟩
  have hbase : OddOrder.BG.Ch4.S16.FT_signalizerBase a = N₀ := by
    have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase a = hbr.2.choose := dif_pos hbr
    rw [hb]
    exact huniq _ hbr.2.choose_spec
  obtain ⟨Nstr, ⟨hNstr_max, hNstr_C, -, -, -, -, hNstr_all⟩, -⟩ :=
    OddOrder.BG.Ch4.S16.signalizer_structure_of_mem_sigmaSharp hG hM hσa hgt
  have hNstr_eq : Nstr = N₀ :=
    huniq Nstr (mem_maximalSubgroupsContaining.mpr ⟨hNstr_max, hNstr_C⟩)
  have hM𝓜 : M ∈ OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a := ⟨hM, hσa.1⟩
  obtain ⟨-, -, hMcompl, -⟩ := hNstr_all M hM𝓜
  have hCN₀ : Subgroup.centralizer ({a} : Set G) ≤ N₀ := hNstr_eq ▸ hNstr_C
  have haM : a ∈ M := OddOrder.BG.Ch3.S10.Msigma_le M hσa.1
  have hcompl := OddOrder.BG.Ch4.S16.signalizer_centralizer_isComplement
    (hNstr_eq ▸ hMcompl) hCN₀ haM
  have hRdef : OddOrder.BG.Ch4.S16.FT_signalizer a
      = OddOrder.BG.Ch3.S10.Msigma N₀ ⊓ Subgroup.centralizer ({a} : Set G) := by
    rw [OddOrder.BG.Ch4.S16.FT_signalizer, hbase]
  have hRle : OddOrder.BG.Ch4.S16.FT_signalizer a ≤ Subgroup.centralizer ({a} : Set G) :=
    OddOrder.BG.Ch4.S16.FT_signalizer_le_centralizer a
  have hCMle : OddOrder.Peterfalvi.S04.centralizerIn M a ≤
      Subgroup.centralizer ({a} : Set G) := inf_le_right
  refine ⟨?_, ?_, ?_⟩
  · refine le_antisymm ?_ (sup_le hRle hCMle)
    intro c hc
    obtain ⟨⟨u, v⟩, huv, -⟩ := Subgroup.IsComplement.existsUnique hcompl
      (⟨c, hc⟩ : ↥(Subgroup.centralizer ({a} : Set G)))
    have hcval : ((u : ↥(Subgroup.centralizer ({a} : Set G))) : G) *
        ((v : ↥(Subgroup.centralizer ({a} : Set G))) : G) = c := by
      simpa using congrArg (fun z : ↥(Subgroup.centralizer ({a} : Set G)) => (z : G)) huv
    have hu : ((u : ↥(Subgroup.centralizer ({a} : Set G))) : G) ∈
        OddOrder.Peterfalvi.S04.centralizerIn M a := by
      have hu' := Subgroup.mem_subgroupOf.mp u.2
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hu').1,
        SetLike.coe_mem (u : ↥(Subgroup.centralizer ({a} : Set G)))⟩
    have hv : ((v : ↥(Subgroup.centralizer ({a} : Set G))) : G) ∈
        OddOrder.BG.Ch4.S16.FT_signalizer a := by
      have hv' := Subgroup.mem_subgroupOf.mp v.2
      rw [hRdef]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hv').1,
        SetLike.coe_mem (v : ↥(Subgroup.centralizer ({a} : Set G)))⟩
    rw [← hcval]
    exact mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left hv)
  · rw [disjoint_iff, eq_bot_iff]
    intro y hy
    obtain ⟨hyR, hyC⟩ := Subgroup.mem_inf.mp hy
    have hyc : y ∈ Subgroup.centralizer ({a} : Set G) := hRle hyR
    have hymem : (⟨y, hyc⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈
        ((M ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf
          (Subgroup.centralizer ({a} : Set G))) ⊓
        ((OddOrder.BG.Ch3.S10.Msigma N₀ ⊓
          Subgroup.centralizer ({a} : Set G)).subgroupOf
          (Subgroup.centralizer ({a} : Set G))) := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hyC,
        Subgroup.mem_subgroupOf.mpr ?_⟩
      exact hRdef ▸ hyR
    have hybot := hcompl.disjoint.le_bot hymem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hybot))
  · intro c hc y hy
    have hnorm := OddOrder.BG.Ch4.S16.FT_signalizer_normal_in_centralizer hbr hc
    exact (Subgroup.mem_normalizer_iff.mp hnorm y).mp hy

/-- **Peterfalvi (8.13.c1/c2) at an escaping point of the type-I support** (BG §16 Theorem II +
Theorem D(3)/(4); Coq `FTsupport_facts` part c).  For escaping `a ∈ A(M)` (`C_G(a) ⊄ M`), with
`R(a) = FT_signalizer a` the supporting-maximal signalizer:
- (8.13.c1) `C_G(a) = R(a) ⋊ C_M(a)` — join, disjointness, and normality of `R(a)`;
- (8.13.c2) `|R(a)|` is coprime to `|C_M(b)|` for every `b ∈ A(M)`.

Assembly: the escaping point is `σ`-sharp with more than one `σ`-maximal (the (8.13.b)
machinery), so the supporting maximal is the pinned `N[a] = FT_signalizerBase a` and Theorem
D(3) supplies the complement structure — `signalizer_centralizer_isComplement` fed by the
`N`-complement of `signalizer_structure_of_mem_sigmaSharp` at `M ∈ 𝓜_σ(a)` — while the
normality is `FT_signalizer_normal_in_centralizer`.  (c2): a prime of `|R(a)|` divides
`|(N[a])_σ|`, so it lies in `σ(N[a])` and the coprimality core
`escaping_sigma_disjoint_centralizer` (BG Lemma 14.13(a) route) applies. -/
theorem escaping_typeIA_signalizer_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIData M)
    {a : G} (ha : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M (typeIA M data)) :
    Subgroup.centralizer ({a} : Set G)
        = OddOrder.BG.Ch4.S16.FT_signalizer a ⊔ OddOrder.Peterfalvi.S04.centralizerIn M a ∧
      Disjoint (OddOrder.BG.Ch4.S16.FT_signalizer a)
        (OddOrder.Peterfalvi.S04.centralizerIn M a) ∧
      (∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ OddOrder.BG.Ch4.S16.FT_signalizer a,
        c * y * c⁻¹ ∈ OddOrder.BG.Ch4.S16.FT_signalizer a) ∧
      (∀ b ∈ typeIA M data,
        Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
          (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b))) := by
  classical
  obtain ⟨haA, haesc⟩ := ha
  have ha1 : a ≠ 1 := haA.2.1
  -- `a` is σ-sharp with more than one σ-maximal (the (8.13.b) machinery).
  have hκ : OddOrder.BG.Ch4.S14.kappa M = ∅ :=
    (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hM).mp ⟨data⟩
  have hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M)
      ((⊥ : Subgroup G).subgroupOf M) := by
    rw [Subgroup.bot_subgroupOf, OddOrder.Isaacs.Ch03.IsHallSubgroup.bot_iff]
    intro q _
    rw [hκ]
    exact Set.notMem_empty q
  have hσa : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M :=
    OddOrder.BG.Ch4.S16.mem_sigmaSharp_of_mem_aSet_of_escape hG hM bot_le data.typeF.U_le hK
      (typeF_complement_isHall_kappa_sigma_compl hG hM data) (Or.inl rfl)
      (typeIA_subset_ASet hG hM data haA) ha1 haesc
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a).ncard := by
    by_contra h
    exact haesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hM hσa.1 ha1
      (not_lt.mp h))
  -- singleton uniqueness pins the supporting maximal, identifying the base of `R(a)`.
  obtain ⟨N₀, hN₀⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG hM hσa haesc
  have huniq : ∀ L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G)),
      L = N₀ := by
    intro L hL
    rw [hN₀, Set.mem_singleton_iff] at hL
    exact hL
  have hbr : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G))).Nonempty :=
    ⟨hgt, ⟨N₀, by rw [hN₀]; rfl⟩⟩
  have hbase : OddOrder.BG.Ch4.S16.FT_signalizerBase a = N₀ := by
    have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase a = hbr.2.choose := dif_pos hbr
    rw [hb]
    exact huniq _ hbr.2.choose_spec
  -- unfold `R(a) = (N₀)_σ ⊓ C_G(a)` for the coprimality step.
  have hRdef : OddOrder.BG.Ch4.S16.FT_signalizer a
      = OddOrder.BG.Ch3.S10.Msigma N₀ ⊓ Subgroup.centralizer ({a} : Set G) := by
    rw [OddOrder.BG.Ch4.S16.FT_signalizer, hbase]
  -- (8.13.c1) join/disjoint/normal is the `σ`-decomposition-generic complement structure.
  obtain ⟨hjoin, hdisj, hnormc⟩ :=
    escaping_sigmaSharp_signalizer_structure hG hM hσa haesc
  refine ⟨hjoin, hdisj, hnormc, ?_⟩
  · -- (c2): primes of `|R(a)|` lie in `σ(N[a])`; apply the coprimality core.
    intro b hb
    by_contra hnc
    obtain ⟨p, hpp, hpR, hpC⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase a) := by
      rw [hbase]
      refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup N₀ p (Nat.mem_primeFactors.mpr
        ⟨hpp, ?_, Nat.card_pos.ne'⟩)
      refine hpR.trans (Subgroup.card_dvd_of_le ?_)
      rw [hRdef]
      exact inf_le_left
    exact escaping_sigma_disjoint_centralizer hG hM data ⟨haA, haesc⟩ hb hpp hpσ hpC

/-- The escaping set of an `M`-invariant support is `M`-conjugation invariant: conjugation by
`m ∈ M` transports centralizers and preserves the non-containment `C_G(x) ⊄ M`. -/
theorem escapingCentralizerSet_conj_mem {M : Subgroup G} {X : Set G} {m x : G}
    (hm : m ∈ M) (hX : m * x * m⁻¹ ∈ X ↔ x ∈ X) :
    m * x * m⁻¹ ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
      ↔ x ∈ OddOrder.GroupTheory.escapingCentralizerSet M X := by
  have key : ∀ {u v : G}, u ∈ M → Subgroup.centralizer ({v} : Set G) ≤ M →
      Subgroup.centralizer ({u * v * u⁻¹} : Set G) ≤ M := by
    intro u v hu hv c hc
    have hc' : u⁻¹ * c * u ∈ Subgroup.centralizer ({v} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      calc u⁻¹ * c * u * v = u⁻¹ * (c * (u * v * u⁻¹)) * u := by group
        _ = u⁻¹ * ((u * v * u⁻¹) * c) * u := by rw [hc]
        _ = v * (u⁻¹ * c * u) := by group
    have hmem := hv hc'
    have h2 : c = u * (u⁻¹ * c * u) * u⁻¹ := by group
    rw [h2]
    exact mul_mem (mul_mem hu hmem) (inv_mem hu)
  constructor
  · rintro ⟨hmx, hesc⟩
    refine ⟨hX.mp hmx, fun hle => hesc ?_⟩
    exact key hm hle
  · rintro ⟨hx, hesc⟩
    refine ⟨hX.mpr hx, fun hle => hesc ?_⟩
    have h2 : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
    exact h2 ▸ key (inv_mem hm) hle

/-- Conjugation by a `MulAut` distributes over the subgroup infimum (the pointwise action is
an order isomorphism). -/
private theorem conj_smul_inf' (φ : MulAut G) (H K : Subgroup G) :
    φ • (H ⊓ K) = φ • H ⊓ φ • K := by
  ext z
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_inf]

/-- Conjugation transports the centralizer of a singleton:
`g · C_G(a) · g⁻¹ = C_G(g a g⁻¹)` (local copy of the S12/S14 helper; pure group theory). -/
private theorem conj_smul_centralizer_singleton' (g a : G) :
    MulAut.conj g • Subgroup.centralizer ({a} : Set G)
      = Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
  have hinv : (MulAut.conj g)⁻¹ • y = g⁻¹ * y * g := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  simp only [Set.mem_singleton_iff, forall_eq, hinv]
  constructor
  · intro h
    calc g * a * g⁻¹ * y
        = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * a) * g⁻¹ := by rw [h]
      _ = y * (g * a * g⁻¹) := by group
  · intro h
    calc a * (g⁻¹ * y * g)
        = g⁻¹ * (g * a * g⁻¹ * y) * g := by group
      _ = g⁻¹ * (y * (g * a * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * y * g * a := by group


/-- `MulAut`-conjugation transports `opiCoreInG` (local copy of the S14 helper). -/
private theorem conj_smul_opiCoreInG'' [Finite G] (π : Set ℕ) (φ : MulAut G) (H : Subgroup G) :
    φ • opiCoreInG π H = opiCoreInG π (φ • H) := by
  have hHmap : H.map (φ : G →* G) = φ • H :=
    (mulAut_smul_eq_map' φ H).symm
  let e : ↥H ≃* ↥(φ • H) :=
    (Subgroup.equivMapOfInjective H (φ : G →* G) φ.injective).trans
      (MulEquiv.subgroupCongr hHmap)
  have hcomp : (φ • H).subtype.comp (e : ↥H →* ↥(φ • H)) = (φ : G →* G).comp H.subtype := by
    ext x; rfl
  calc φ • opiCoreInG π H
      = (opiCoreInG π H).map (φ : G →* G) := mulAut_smul_eq_map' φ _
    _ = ((OddOrder.Isaacs.Ch03.oPiCore π ↥H).map H.subtype).map (φ : G →* G) := rfl
    _ = (OddOrder.Isaacs.Ch03.oPiCore π ↥H).map ((φ : G →* G).comp H.subtype) := by
        rw [Subgroup.map_map]
    _ = (OddOrder.Isaacs.Ch03.oPiCore π ↥H).map
          ((φ • H).subtype.comp (e : ↥H →* ↥(φ • H))) := by rw [hcomp]
    _ = ((OddOrder.Isaacs.Ch03.oPiCore π ↥H).map (e : ↥H →* ↥(φ • H))).map
          (φ • H).subtype := by rw [← Subgroup.map_map]
    _ = (OddOrder.Isaacs.Ch03.oPiCore π ↥(φ • H)).map (φ • H).subtype := by
        rw [OddOrder.Isaacs.Ch03.oPiCore.map_eq_of_mulEquiv]

/-- `M_σ` is conjugation-equivariant (local copy of the S14 private helper). -/
private theorem Msigma_conj_smul' [Finite G] (g : G) (M : Subgroup G) :
    OddOrder.BG.Ch3.S10.Msigma (MulAut.conj g • M)
      = MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M := by
  simp only [OddOrder.BG.Ch3.S10.Msigma]
  rw [conj_smul_opiCoreInG'', OddOrder.BG.Ch4.S14.sigma_conj_smul_eq]

/-- **(8.14) kernel equivariance at an escaping point**: `R(m·a·m⁻¹) = m·R(a)·m⁻¹` for `m ∈ M`.

The escaping point and its conjugate are both `σ`-sharp with escaping centralizer
(`mem_sigmaSharp_of_mem_aSet_of_escape` via the `typeIA_subset_ASet` bridge), so both supporting
maximals are pinned by the singleton uniqueness
(`maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape`, BG Theorem D);
`MulAut.conj m • N[a]` is maximal over `C_G(m·a·m⁻¹) = m·C_G(a)·m⁻¹`, so
`N[m·a·m⁻¹] = m·N[a]·m⁻¹`, and `R = N_σ ⊓ C_G(·)` transports by `M_σ`-equivariance. -/
theorem FT_signalizer_conj_smul_of_escaping [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIData M)
    {a m : G} (hm : m ∈ M)
    (ha : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M (typeIA M data)) :
    OddOrder.BG.Ch4.S16.FT_signalizer (m * a * m⁻¹)
      = MulAut.conj m • OddOrder.BG.Ch4.S16.FT_signalizer a := by
  classical
  obtain ⟨haA, hesc⟩ := ha
  -- the conjugate is again an escaping support point
  have hiff : ∀ {x : G}, m * x * m⁻¹ ∈ typeIA M data ↔ x ∈ typeIA M data := by
    intro x
    constructor
    · intro h
      have := typeIA_conj_mem M data (inv_mem hm) h
      have hx : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
      rwa [hx] at this
    · exact typeIA_conj_mem M data hm
  obtain ⟨ha'A, hesc'⟩ :=
    (escapingCentralizerSet_conj_mem hm hiff).mpr ⟨haA, hesc⟩
  -- both points are σ-sharp, so both supporting maximals are unique
  have hκ : OddOrder.BG.Ch4.S14.kappa M = ∅ :=
    (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hM).mp ⟨data⟩
  have hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M)
      ((⊥ : Subgroup G).subgroupOf M) := by
    rw [Subgroup.bot_subgroupOf, OddOrder.Isaacs.Ch03.IsHallSubgroup.bot_iff]
    intro p _
    rw [hκ]
    exact Set.notMem_empty p
  have hU := typeF_complement_isHall_kappa_sigma_compl hG hM data
  have hσ : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M :=
    OddOrder.BG.Ch4.S16.mem_sigmaSharp_of_mem_aSet_of_escape hG hM bot_le data.typeF.U_le hK hU
      (Or.inl rfl) (typeIA_subset_ASet hG hM data haA) haA.2.1 hesc
  have hσ' : m * a * m⁻¹ ∈ OddOrder.BG.Ch4.S14.sigmaSharp M :=
    OddOrder.BG.Ch4.S16.mem_sigmaSharp_of_mem_aSet_of_escape hG hM bot_le data.typeF.U_le hK hU
      (Or.inl rfl) (typeIA_subset_ASet hG hM data ha'A) ha'A.2.1 hesc'
  obtain ⟨N, hN⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG hM hσ hesc
  obtain ⟨N', hN'⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG hM hσ' hesc'
  have hNmem : N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G)) := by
    rw [hN]; rfl
  obtain ⟨hNmax, hCN⟩ := mem_maximalSubgroupsContaining.mp hNmem
  -- branch conditions for the concrete `FT_signalizerBase`
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a).ncard := by
    by_contra h
    push_neg at h
    exact hesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hM hσ.1 haA.2.1 h)
  have hgt' : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement (m * a * m⁻¹)).ncard := by
    by_contra h
    push_neg at h
    exact hesc'
      (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hM hσ'.1 ha'A.2.1 h)
  have hbr : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G))).Nonempty :=
    ⟨hgt, ⟨N, hNmem⟩⟩
  have hbr' : 1 <
      (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement (m * a * m⁻¹)).ncard ∧
      (maximalSubgroupsContaining
        (Subgroup.centralizer ({m * a * m⁻¹} : Set G))).Nonempty :=
    ⟨hgt', ⟨N', by rw [hN']; rfl⟩⟩
  -- identify the two bases (avoiding a motive dependence on the `Nonempty` proof)
  have huniq : ∀ L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G)),
      L = N := by
    intro L hL
    rw [hN, Set.mem_singleton_iff] at hL
    exact hL
  have huniq' : ∀ L ∈ maximalSubgroupsContaining
      (Subgroup.centralizer ({m * a * m⁻¹} : Set G)), L = N' := by
    intro L hL
    rw [hN', Set.mem_singleton_iff] at hL
    exact hL
  have hbase : OddOrder.BG.Ch4.S16.FT_signalizerBase a = N := by
    have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase a = hbr.2.choose := dif_pos hbr
    rw [hb]
    exact huniq _ hbr.2.choose_spec
  have hCconj : Subgroup.centralizer ({m * a * m⁻¹} : Set G)
      = MulAut.conj m • Subgroup.centralizer ({a} : Set G) :=
    (conj_smul_centralizer_singleton' m a).symm
  have hbase' : OddOrder.BG.Ch4.S16.FT_signalizerBase (m * a * m⁻¹) = MulAut.conj m • N := by
    have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase (m * a * m⁻¹) = hbr'.2.choose :=
      dif_pos hbr'
    have hmemN' : MulAut.conj m • N ∈
        maximalSubgroupsContaining (Subgroup.centralizer ({m * a * m⁻¹} : Set G)) := by
      rw [mem_maximalSubgroupsContaining]
      refine ⟨OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hNmax), ?_⟩
      rw [hCconj]
      exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hCN
    rw [hb, huniq' _ hbr'.2.choose_spec]
    exact (huniq' _ hmemN').symm
  -- assemble: `R = N_σ ⊓ C_G(·)` transports
  rw [OddOrder.BG.Ch4.S16.FT_signalizer, OddOrder.BG.Ch4.S16.FT_signalizer, hbase, hbase',
    Msigma_conj_smul', hCconj, conj_smul_inf']

/-- The faithful kernel is `M`-conjugation equivariant on an `M`-invariant sub-support of `A(M)`
(escaping side by the Theorem-D pin, non-escaping side trivially `⊥`). -/
theorem ftSupportKernel_conj_smul [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypeIData M)
    {X : Set G} (hXA : X ⊆ typeIA M data)
    (hXiff : ∀ {m x : G}, m ∈ M → (m * x * m⁻¹ ∈ X ↔ x ∈ X))
    {a m : G} (hm : m ∈ M) :
    ftSupportKernel M X (m * a * m⁻¹) = MulAut.conj m • ftSupportKernel M X a := by
  by_cases hesc : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
  · rw [ftSupportKernel_eq_of_escaping
        ((escapingCentralizerSet_conj_mem hm (hXiff hm)).mpr hesc),
      ftSupportKernel_eq_of_escaping hesc]
    exact FT_signalizer_conj_smul_of_escaping hG hM data hm ⟨hXA hesc.1, hesc.2⟩
  · rw [ftSupportKernel_eq_bot_of_not_escaping
        (fun h => hesc ((escapingCentralizerSet_conj_mem hm (hXiff hm)).mp h)),
      ftSupportKernel_eq_bot_of_not_escaping hesc, Subgroup.smul_bot]

/-- **(8.15) normalizer identification**: for a nonempty `M`-invariant `X ⊆ M ∖ {1}`,
`N_G(X) = M`.  Peterfalvi: `X ⊆ M ⊆ N_G(X)`; if `N_G(X) = G` then `⟨X⟩` would be a nontrivial
normal subgroup inside the proper `M`, contradicting simplicity; maximality forces equality. -/
theorem normalizer_support_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {X : Set G}
    (hXM : X ⊆ (M : Set G)) (hX1 : ∀ x ∈ X, x ≠ (1 : G)) (hXne : X.Nonempty)
    (hXiff : ∀ {m x : G}, m ∈ M → (m * x * m⁻¹ ∈ X ↔ x ∈ X)) :
    Subgroup.normalizer X = M := by
  have hMle : M ≤ Subgroup.normalizer X := by
    intro m hm
    rw [Subgroup.mem_set_normalizer_iff]
    exact fun n => (hXiff hm).symm
  rcases eq_or_lt_of_le hMle with h | h
  · exact h.symm
  · exfalso
    have hcoatom : IsCoatom M := mem_maximalSubgroups.mp hM
    have htop : Subgroup.normalizer X = ⊤ := hcoatom.2 _ h
    have hGinv : ∀ g x : G, x ∈ X → g * x * g⁻¹ ∈ X := by
      intro g x hx
      have hg : g ∈ Subgroup.normalizer X := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_set_normalizer_iff.mp hg x).mp hx
    have hnormal : (Subgroup.closure X).Normal := by
      constructor
      intro n hn g
      induction hn using Subgroup.closure_induction with
      | mem x hx => exact Subgroup.subset_closure (hGinv g x hx)
      | one => simpa using Subgroup.one_mem (Subgroup.closure X)
      | mul x y _ _ hx hy =>
          have hxy : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
          rw [hxy]; exact mul_mem hx hy
      | inv x _ hx =>
          have hxi : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
          rw [hxi]; exact inv_mem hx
    obtain ⟨x0, hx0⟩ := hXne
    have hle : Subgroup.closure X ≤ M := (Subgroup.closure_le M).mpr hXM
    rcases hG.simple.eq_bot_or_eq_top_of_normal _ hnormal with hb | ht
    · exact hX1 x0 hx0 (Subgroup.mem_bot.mp (hb ▸ Subgroup.subset_closure hx0))
    · exact hcoatom.1 (top_le_iff.mp (ht ▸ hle))

/-- **Faithful (8.15) datum for an `M`-invariant sub-support of `A(M)`** (assembly): the (2.2)
kernel at `a` is `ftSupportKernel M X a`; escaping points get the (8.13.c1/c2) semidirect
structure from `escaping_typeIA_signalizer_structure`, non-escaping points are the trivial
`C_G(a) = C_M(a)` case.  Instantiated at `X = A(M)` and `X = A₁(M)` below. -/
theorem dadeSupportHypothesisData_of_subset [Fintype G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIData M)
    {X : Set G} (hXA : X ⊆ typeIA M data) (hXne : X.Nonempty)
    (hXiff : ∀ {m x : G}, m ∈ M → (m * x * m⁻¹ ∈ X ↔ x ∈ X)) :
    Nonempty (DadeSupportHypothesisData M X) := by
  classical
  have hXsharp : ∀ x ∈ X, x ≠ (1 : G) := fun x hx =>
    (OddOrder.Peterfalvi.S04.mem_sharp.mp (typeIA_subset_sharp M data (hXA hx))).2
  have hXM : X ⊆ (M : Set G) := fun x hx => typeIA_subset M data (hXA hx)
  -- the escaping-point structure, converted from the `A(M)`-level pin to `X`-level points
  have hstruct : ∀ {a : G}, a ∈ OddOrder.GroupTheory.escapingCentralizerSet M X →
      Subgroup.centralizer ({a} : Set G)
          = OddOrder.BG.Ch4.S16.FT_signalizer a ⊔ OddOrder.Peterfalvi.S04.centralizerIn M a ∧
        Disjoint (OddOrder.BG.Ch4.S16.FT_signalizer a)
          (OddOrder.Peterfalvi.S04.centralizerIn M a) ∧
        (∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ OddOrder.BG.Ch4.S16.FT_signalizer a,
          c * y * c⁻¹ ∈ OddOrder.BG.Ch4.S16.FT_signalizer a) ∧
        (∀ b ∈ typeIA M data,
          Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
            (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b))) :=
    fun {a} ha => escaping_typeIA_signalizer_structure hG hM data ⟨hXA ha.1, ha.2⟩
  refine ⟨{ normalizer_eq := normalizer_support_eq hG hM hXM hXsharp hXne @hXiff
            dade :=
              { subset_sharp := fun x hx =>
                  OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ x, hXsharp x hx⟩
                subset_L := fun x hx => hXM hx
                L_normalizes_A := fun l a ha => (hXiff l.2).mpr ha
                H := fun a => ftSupportKernel M X a.1
                conj_in_L := by
                  intro a b ha hb hab
                  obtain ⟨m, hmM, hmab⟩ :=
                    typeIA_isConj_conj_in_M hG hM data (hXA ha) (hXA hb) hab
                  exact ⟨⟨m, hmM⟩, hmab⟩
                centralizer_eq_sup := by
                  intro a
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).1
                  · have hle : Subgroup.centralizer ({a.1} : Set G) ≤ M := by
                      by_contra hnle
                      exact hesc ⟨a.2, hnle⟩
                    rw [ftSupportKernel_eq_bot_of_not_escaping hesc, bot_sup_eq]
                    exact (inf_eq_right.mpr hle).symm
                centralizer_disjoint := by
                  intro a
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).2.1
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc]
                    exact disjoint_bot_left
                H_normalized := by
                  intro a c hc x hx
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc] at hx ⊢
                    exact (hstruct hesc).2.2.1 c hc x hx
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc] at hx ⊢
                    rw [Subgroup.mem_bot] at hx ⊢
                    rw [hx]
                    group
                centralizer_coprime := by
                  intro a b
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).2.2.2 b.1 (hXA b.2)
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc]
                    simpa using Nat.coprime_one_left _ }
            H_eq_ftSupportKernel := fun _ => rfl
            hconj := fun a l => ftSupportKernel_conj_smul hG hM data hXA @hXiff l.2 }⟩

/-- `A₁(M) = (M_F)^# ⊆ A(M)` for type I (`M_s = M_F = H`, and `x ∈ H^#` centralizes itself). -/
theorem A1_subset_typeIA (M : Subgroup G) (data : TypeIData M) :
    A1 M PeterfalviType.I ⊆ typeIA M data := by
  intro x hx
  obtain ⟨hxH, hx1⟩ := (Set.mem_diff x).mp hx
  have hx1' : x ≠ 1 := fun h => hx1 (Set.mem_singleton_iff.mpr h)
  have hxH' : x ∈ data.typeF.H := data.typeF.H_eq ▸ SetLike.mem_coe.mp hxH
  exact ⟨data.typeF.H_le hxH', hx1',
    x, (Set.mem_diff _).mpr ⟨SetLike.mem_coe.mpr hxH', hx1⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩


/-- **`M`-conjugation invariance of `sharpSubgroup H`** when `M` normalizes `H` (general helper for
the type-`τ` Dade-support sets `A₁(M) = M_s#`, `A(M) = (M')#`, all of the form `sharpSubgroup H`
with `H ⊴ M`). -/
theorem sharpSubgroup_conj_mem {H : Subgroup G} {m : G}
    (hn : m ∈ Subgroup.normalizer (H : Set G)) {a : G}
    (ha : a ∈ OddOrder.GroupTheory.sharpSubgroup H) :
    m * a * m⁻¹ ∈ OddOrder.GroupTheory.sharpSubgroup H := by
  obtain ⟨haH, ha1⟩ := (Set.mem_diff a).mp ha
  rw [Subgroup.mem_normalizer_iff] at hn
  refine (Set.mem_diff _).mpr ⟨SetLike.mem_coe.mpr ((hn a).mp (SetLike.mem_coe.mp haH)), ?_⟩
  exact fun h => (conj_ne_one (fun h1 => ha1 (Set.mem_singleton_iff.mpr h1)))
    (Set.mem_singleton_iff.mp h)

/-- **`M`-conjugation invariance of `A₁(M) = M_s#`** for every Peterfalvi type: `M_s` is `M_F`
(types I, II, V) or `M'` (types III, IV), both `⊴ M`. -/
theorem A1_conj_mem (M : Subgroup G) (tau : OddOrder.GroupTheory.PeterfalviType) {m : G}
    (hm : m ∈ M) {a : G} (ha : a ∈ A1 M tau) : m * a * m⁻¹ ∈ A1 M tau := by
  refine sharpSubgroup_conj_mem (H := OddOrder.GroupTheory.mainSubgroup M tau) ?_ ha
  cases tau with
  | I => exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M hm
  | II => exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M hm
  | V => exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M hm
  | III => exact OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M hm
  | IV => exact OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M hm

/-- **`M`-conjugation invariance of the type-`P` support `A(M) = (M')#`** (`M' ⊴ M`). -/
theorem typePA_conj_mem (M : Subgroup G) (data : TypePData M) {m : G} (hm : m ∈ M) {a : G}
    (ha : a ∈ typePA M data) : m * a * m⁻¹ ∈ typePA M data := by
  rw [typePA_eq_sharpSubgroup_derivedInG] at ha ⊢
  exact sharpSubgroup_conj_mem (OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M hm) ha

/-- **Type-`P₁` support is `M_σ#`** (`A(M) = (M')# = M_σ#`).  For a type-`P₁` maximal subgroup
`M' = M_σ` (`isTypeP1_derivedInG_eq_Msigma`, from `mainSubgroup_eq_Msigma`/BG Prop 16.1), so the
Peterfalvi Dade support `typePA = (M')#` coincides with the BG σ-sharp set `sigmaSharp = M_σ#`.

This is the structural bridge that makes the type-`P` Dade-support escaping structure a **direct**
application of the σ-sharp signalizer machinery (`signalizer_structure_of_mem_sigmaSharp`), with no
`ASet` detour: every escaping point of `A(M)` is already `σ`-sharp.  (For type `P₂`, `M_σ ⊊ M'`, so
`typePA ⊋ M_σ#`; the escaping points still land in `A_1 = M_σ#` by Peterfalvi (8.13.b) +
`A1_eq_sigmaSharp`, but that reduction is the deeper type-`P₂` obligation.) -/
theorem typePA_eq_sigmaSharp_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) :
    typePA M data = OddOrder.BG.Ch4.S14.sigmaSharp M := by
  rw [typePA_eq_sharpSubgroup_derivedInG,
    OddOrder.BG.Ch4.S16.isTypeP1_derivedInG_eq_Msigma hG hM hP1]
  rfl

/-- **Escaping type-`P₁` support points are `σ`-sharp** (the soundness lemma for the type-`P₁` Dade
engine): for a type-`P₁` maximal, an escaping point of `A(M) = (M')#` lies in `M_σ#`.  Immediate from
`typePA = M_σ#` (`typePA_eq_sigmaSharp_of_isTypeP1`).  This is the type-`P₁` analogue of the type-`I`
`escaping_typeIA_mem_A1`, but with no `ASet`/`mem_sigmaSharp_of_mem_aSet_of_escape` detour. -/
theorem escaping_typePA_mem_sigmaSharp_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) {a : G}
    (ha : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M (typePA M data)) :
    a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M := by
  rw [← typePA_eq_sigmaSharp_of_isTypeP1 hG hM data hP1]
  exact ha.1

/-- **Peterfalvi (4.6.b) / (4.3.a), ambient version**: for a type-`P` maximal subgroup, the
exceptional set `V = W − (W₁ ∪ W₂)` is a TI-subset of `G` with normalizer-bound `W`.

Given `g` conjugating some `a ∈ V` into `V`, the singleton normalizer fact `N_G({a}) = W`
(`TypePData.normalizer_V`) forces `g` to normalize `W` — both `h ∈ W` and `g h g⁻¹ ∈ W` reduce to
`h a h⁻¹ = a`.  Since `W = W₁ × W₂` is cyclic with coprime factors, `W₁` and `W₂` are the *unique*
subgroups of their orders (`cyclic_subgroup_eq_of_card_eq`), hence characteristic, so `g` also
normalizes `W₁` and `W₂` and therefore `V`; finally `N_G(V) = W` (`normalizer_V` with `X = V`) gives
`g ∈ W`.  This is the `V`-conjugacy control behind the type-`P` `A_0(M)` support (`(8.13.a)` for the
exceptional part) and the §10 → §5 ω-grid bridge (S12). -/
theorem typePData_V_ti [Finite G] {M : Subgroup G} (data : TypePData M) :
    IsTISubset (typePV M data) data.W := by
  classical
  haveI : IsCyclic ↥data.W := data.W_cyclic
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  have mem_norm_sing : ∀ c z : G,
      z ∈ Subgroup.normalizer ({c} : Set G) ↔ z * c * z⁻¹ = c := by
    intro c z
    rw [Subgroup.mem_set_normalizer_iff]
    constructor
    · intro hz
      have := (hz c).mp rfl
      simpa using this
    · intro hz h
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro rfl; exact hz
      · intro hh
        have hcc : z * h * z⁻¹ = z * c * z⁻¹ := by rw [hh, hz]
        exact mul_left_cancel (mul_right_cancel hcc)
  intro g hg
  obtain ⟨a, haV, hbV⟩ := hg
  have hNa : Subgroup.normalizer ({a} : Set G) = data.W :=
    data.normalizer_V {a} (Set.singleton_nonempty a) (Set.singleton_subset_iff.mpr haV)
  have hNb : Subgroup.normalizer ({g * a * g⁻¹} : Set G) = data.W :=
    data.normalizer_V {g * a * g⁻¹} (Set.singleton_nonempty _) (Set.singleton_subset_iff.mpr hbV)
  have hgW : ∀ h, h ∈ data.W ↔ g * h * g⁻¹ ∈ data.W := by
    intro h
    have e1 : (h ∈ data.W) ↔ h * a * h⁻¹ = a := by rw [← hNa, mem_norm_sing]
    have e2 : (g * h * g⁻¹ ∈ data.W) ↔ h * a * h⁻¹ = a := by
      rw [← hNb, mem_norm_sing]
      have hexp : g * h * g⁻¹ * (g * a * g⁻¹) * (g * h * g⁻¹)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ := by
        group
      rw [hexp]
      constructor
      · intro hh; exact mul_left_cancel (mul_right_cancel hh)
      · intro hh; rw [hh]
    rw [e1, e2]
  have hstab : ∀ (A : Subgroup G), A ≤ data.W → ∀ x : G, g * x * g⁻¹ ∈ A ↔ x ∈ A := by
    intro A hAW
    have hmap_le : A.map (MulAut.conj g).toMonoidHom ≤ data.W := by
      rintro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hzA, rfl⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (hgW z).mp (hAW hzA)
    have hcard : Nat.card ↥(A.map (MulAut.conj g).toMonoidHom) = Nat.card ↥A :=
      (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv).symm
    have hsubeq : (A.map (MulAut.conj g).toMonoidHom).subgroupOf data.W
        = A.subgroupOf data.W := by
      apply OddOrder.BG.Ch3.S10.cyclic_subgroup_eq_of_card_eq (C := ↥data.W)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmap_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv, hcard]
    have hmapeq : A.map (MulAut.conj g).toMonoidHom = A := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hmap_le, hsubeq,
        Subgroup.map_subgroupOf_eq_of_le hAW]
    intro x
    constructor
    · intro hx
      have hmem : g * x * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := by rw [hmapeq]; exact hx
      rw [Subgroup.mem_map] at hmem
      obtain ⟨z, hzA, hz⟩ := hmem
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hz
      have hzx : z = x := mul_left_cancel (mul_right_cancel hz)
      rwa [hzx] at hzA
    · intro hx
      have hmem : (MulAut.conj g).toMonoidHom x ∈ A.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hmapeq] at hmem
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
  rw [← data.normalizer_V (typePV M data) ⟨a, haV⟩ Set.Subset.rfl,
    Subgroup.mem_set_normalizer_iff]
  intro h
  simp only [typePV, Set.mem_diff, Set.mem_union, SetLike.mem_coe]
  rw [hgW h, hstab data.W1 hW1le h, hstab data.W2 hW2le h]

/-- An element of the exceptional set `V = W − (W₁ ∪ W₂)` of a type-`P` maximal subgroup lies
outside the derived subgroup `M' = [M,M]`.  Decompose `v ∈ W = W₁ ⊔ W₂` (cyclic, abelian) as
`v = x·y` (`x ∈ W₁`, `y ∈ W₂`); `W₂ ≤ M'`, so `v ∈ M'` forces `x = v·y⁻¹ ∈ W₁ ⊓ M' = ⊥`
(`M_complement`), i.e. `x = 1` and `v = y ∈ W₂`, contradicting `v ∉ W₂`.  (Upstreamed here for the
type-`P` `A_0(M)` support geometry; also used in S12's §10 Dade-image analysis.) -/
theorem typePData_typePV_not_mem_derived {M : Subgroup G} (data : TypePData M)
    {v : G} (hv : v ∈ typePV M data) : v ∉ derivedInG M := by
  simp only [typePV, Set.mem_diff, Set.mem_union, SetLike.mem_coe, not_or] at hv
  obtain ⟨hvW, _hvnW1, hvnW2⟩ := hv
  intro hvM'
  haveI hcyc : IsCyclic ↥data.W := data.W_cyclic
  letI : CommGroup ↥data.W := hcyc.commGroup
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  have hsup : data.W1.subgroupOf data.W ⊔ data.W2.subgroupOf data.W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← data.W_eq, Subgroup.subgroupOf_self]
  have hvmem : (⟨v, hvW⟩ : ↥data.W) ∈
      data.W1.subgroupOf data.W ⊔ data.W2.subgroupOf data.W := by
    rw [hsup]; exact Subgroup.mem_top _
  rw [Subgroup.mem_sup] at hvmem
  obtain ⟨a, ha, b, hb, hab⟩ := hvmem
  have haW1 : ((a : ↥data.W) : G) ∈ data.W1 := Subgroup.mem_subgroupOf.mp ha
  have hbW2 : ((b : ↥data.W) : G) ∈ data.W2 := Subgroup.mem_subgroupOf.mp hb
  have habG : ((a : ↥data.W) : G) * ((b : ↥data.W) : G) = v := by
    have := congrArg (Subtype.val) hab
    simpa using this
  have hW2D : data.W2 ≤ derivedInG M := data.W2_le.trans (inf_le_left.trans data.H_le)
  have haM' : ((a : ↥data.W) : G) ∈ derivedInG M := by
    have heq : ((a : ↥data.W) : G) = v * ((b : ↥data.W) : G)⁻¹ := by rw [← habG]; group
    rw [heq]; exact mul_mem hvM' (inv_mem (hW2D hbW2))
  have haM : ((a : ↥data.W) : G) ∈ M := data.W1_le haW1
  have hdisj := data.M_complement.disjoint
  rw [Subgroup.disjoint_def] at hdisj
  have hm1 : (⟨(a : ↥data.W), haM⟩ : ↥M) ∈ (derivedInG M).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr haM'
  have hm2 : (⟨(a : ↥data.W), haM⟩ : ↥M) ∈ data.W1.subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr haW1
  have ha1 : ((a : ↥data.W) : G) = 1 := Subtype.ext_iff.mp (hdisj hm1 hm2)
  exact hvnW2 (by rw [← habG, ha1, one_mul]; exact hbW2)

/-- **Type-`P` exceptional points are non-escaping**: for `v ∈ V = W ∖ (W₁ ∪ W₂)`, the singleton
normalizer `N_G(⟨v⟩) = W` (`TypePData.normalizer_V`) equals `C_G(v)` (singleton: centralizing ⟺
normalizing), and `W = W₁ ⊔ W₂ ≤ M`.  So `C_G(v) ≤ M`: the exceptional `V^M`-support of `A_0(M)`
carries the *trivial* (non-escaping) Dade structure `H(v) = ⊥`, `C_G(v) = C_M(v)` — the only part of
`A_0(M)` outside `M_σ^#`, and it needs no signalizer. -/
theorem centralizer_typePV_le_M {M : Subgroup G} (data : TypePData M) {v : G}
    (hv : v ∈ typePV M data) : Subgroup.centralizer ({v} : Set G) ≤ M := by
  have hNV : Subgroup.normalizer ({v} : Set G) = data.W :=
    data.normalizer_V {v} (Set.singleton_nonempty v) (Set.singleton_subset_iff.mpr hv)
  have hWM : (data.W : Subgroup G) ≤ M := by
    rw [data.W_eq]
    refine sup_le data.W1_le ?_
    exact data.W2_le.trans (inf_le_left.trans
      (data.H_le.trans (Subgroup.map_subtype_le _)))
  refine le_trans ?_ (hNV.le.trans hWM)
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff]
  have hgv : g * v * g⁻¹ = v := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [mul_inv_eq_iff_eq_mul]
    exact h
  intro n
  rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
  constructor
  · intro h; rw [h]; exact hgv
  · intro h
    calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
      _ = g⁻¹ * v * g := by rw [h]
      _ = g⁻¹ * (g * v * g⁻¹) * g := by rw [hgv]
      _ = v := by group

/-- **Peterfalvi (8.13.b) for the type-`P₁` `A_0`-support**: an escaping point of
`A_0(M) = A(M) ∪ V^M` is `σ`-sharp.  The exceptional `V^M`-points are non-escaping
(`centralizer_typePV_le_M`: `C_G(m·v·m⁻¹) = m·C_G(v)·m⁻¹ ≤ M`), so an escaping point of `A_0` lies in
`A(M) = M_σ^#` (`typePA_eq_sigmaSharp_of_isTypeP1`).  This is the `(8.13.b)` reduction the `σ`-sharp
Dade engine needs to cover the full `A_0(M)` support (not just `A_1 = M_σ^#`) for type `P₁`. -/
theorem escaping_typePA0_mem_sigmaSharp_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) {a : G}
    (ha : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M (typePA0 M data)) :
    a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M := by
  obtain ⟨haA0, hesc⟩ := ha
  rcases haA0 with hpa | hpv
  · rw [← typePA_eq_sigmaSharp_of_isTypeP1 hG hM data hP1]
    exact hpa
  · exfalso
    obtain ⟨v, hv, m, hmM, hmva⟩ := hpv
    apply hesc
    rw [← hmva, ← conj_smul_centralizer_singleton']
    calc MulAut.conj m • Subgroup.centralizer ({v} : Set G)
        ≤ MulAut.conj m • M :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (centralizer_typePV_le_M data hv)
      _ = M := conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hmM)

/-- **Peterfalvi (8.13.a) for the exceptional `V^M`-support**: two `G`-conjugate elements of
`V^M = conjClassSetIn M V` are already `M`-conjugate.  Since `V` is a TI-subset with normalizer `W`
(`typePData_V_ti`), writing `a = m₁v₁m₁⁻¹`, `b = m₂v₂m₂⁻¹` and `b = gag⁻¹`, the element
`h = m₂⁻¹gm₁` conjugates `v₁ ∈ V` to `v₂ ∈ V`, so `h ∈ W ≤ M`; then `g = m₂·h·m₁⁻¹ ∈ M` is itself
the `M`-conjugator.  This is the `V^M`-half of the type-`P` `A_0(M)` `isConj` obligation (the
`M_σ^#`-half is `sigmaSharp_isConj_conj_in_M`). -/
theorem conjClassSetIn_typePV_isConj_conj_in_M {M : Subgroup G} (data : TypePData M)
    [Finite G] {a b : G} (ha : a ∈ conjClassSetIn M (typePV M data))
    (hb : b ∈ conjClassSetIn M (typePV M data)) (hab : IsConj a b) :
    ∃ m : G, m ∈ M ∧ m * a * m⁻¹ = b := by
  obtain ⟨v1, hv1, m1, hm1, hm1a⟩ := ha
  obtain ⟨v2, hv2, m2, hm2, hm2b⟩ := hb
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  have hWM : (data.W : Subgroup G) ≤ M := by
    rw [data.W_eq]
    refine sup_le data.W1_le ?_
    exact data.W2_le.trans (inf_le_left.trans
      (data.H_le.trans (Subgroup.map_subtype_le _)))
  have hv2eq : (m2⁻¹ * g * m1) * v1 * (m2⁻¹ * g * m1)⁻¹ = v2 := by
    calc (m2⁻¹ * g * m1) * v1 * (m2⁻¹ * g * m1)⁻¹
        = m2⁻¹ * g * (m1 * v1 * m1⁻¹) * g⁻¹ * m2 := by group
      _ = m2⁻¹ * (g * a * g⁻¹) * m2 := by rw [hm1a]; group
      _ = m2⁻¹ * b * m2 := by rw [hg]
      _ = m2⁻¹ * (m2 * v2 * m2⁻¹) * m2 := by rw [hm2b]
      _ = v2 := by group
  have hhW : (m2⁻¹ * g * m1) ∈ data.W :=
    typePData_V_ti data (m2⁻¹ * g * m1) ⟨v1, hv1, by rw [hv2eq]; exact hv2⟩
  have hgM : g ∈ M := by
    have hgeq : g = m2 * (m2⁻¹ * g * m1) * m1⁻¹ := by group
    rw [hgeq]
    exact mul_mem (mul_mem hm2 (hWM hhW)) (inv_mem hm1)
  exact ⟨g, hgM, hg⟩

/-- **Peterfalvi (8.13.a) for the `σ`-sharp support**: two `G`-conjugate elements of `M_σ^#`
are already `M`-conjugate.  This is the `σ`-sharp analogue of `typeIA_isConj_conj_in_M`, but proved
*natively* from the `σ`-decomposition (BG Theorem 14.4, `exists_conj_centralizer_of_mem_maximalSigma`)
rather than through the BG §16 tame embedding.  Since `A₁(M) = M_σ^#` for every Peterfalvi type
(`A1_eq_sigmaSharp`) and `A(M) = (M')^# = M_σ^#` for type `P₁` (`typePA_eq_sigmaSharp_of_isTypeP1`),
this one lemma discharges the Dade-engine `conj_in_L` obligation on `A₁` uniformly and on the
type-`P₁` `A(M)`.

Both `M` and `g^{-1}Mg` are `σ`-maximals of `a` — the latter is a conjugate of `M` containing
`a = g^{-1}bg` (`b ∈ M`), so `maximalConjugatesContaining_eq_maximalSigma` places it in `𝓜_σ(a)`.
Theorem 14.4 gives `c ∈ C_G(a)` with `cMc^{-1} = g^{-1}Mg`, whence `gc ∈ N_G(M) = M`
(`normalizer_eq_self_of_mem_maximalSubgroups`) is the `M`-conjugator: `(gc)a(gc)^{-1} = gag^{-1} = b`. -/
theorem sigmaSharp_isConj_conj_in_M [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {a b : G} (ha : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (hb : b ∈ OddOrder.BG.Ch4.S14.sigmaSharp M) (hab : IsConj a b) :
    ∃ m : G, m ∈ M ∧ m * a * m⁻¹ = b := by
  classical
  have haMσ : a ∈ OddOrder.BG.Ch3.S10.Msigma M := ha.1
  have ha1 : a ≠ 1 := ha.2
  have hbMσ : b ∈ OddOrder.BG.Ch3.S10.Msigma M := hb.1
  have hbM : b ∈ M := OddOrder.BG.Ch3.S10.Msigma_le M hbMσ
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  -- `g⁻¹Mg` is a conjugate of `M` containing `a = g⁻¹bg`, hence a `σ`-maximal of `a`.
  have hNconj : (MulAut.conj g⁻¹ • M) ∈
      OddOrder.BG.Ch4.S16.maximalConjugatesContaining M a := by
    refine ⟨g⁻¹, rfl, ?_⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : (MulAut.conj g⁻¹)⁻¹ • a = g * a * g⁻¹ := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]; group
    rw [hinv, hg]; exact hbM
  rw [OddOrder.BG.Ch4.S16.maximalConjugatesContaining_eq_maximalSigma hG hM haMσ ha1] at hNconj
  -- Theorem 14.4: `M` and `g⁻¹Mg` are `C_G(a)`-conjugate.
  obtain ⟨c, hcC, hc⟩ := OddOrder.BG.Ch4.S14.exists_conj_centralizer_of_mem_maximalSigma hG
    (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG)
    (OddOrder.BG.Ch4.S14.Msigma_ell1 hG hM haMσ ha1) ⟨hM, haMσ⟩ hNconj
  -- `conj c • M = conj g⁻¹ • M` ⟹ `conj (g*c) • M = M` ⟹ `g*c ∈ N_G(M) = M`.
  have hgc_norm : g * c ∈ Subgroup.normalizer M := by
    apply mem_normalizer_of_conj_smul_eq_self
    rw [map_mul, mul_smul, hc, ← mul_smul, ← map_mul]
    simp
  have hgc_M : g * c ∈ M := by
    rwa [OddOrder.BG.Ch4.S14.normalizer_eq_self_of_mem_maximalSubgroups hG hM] at hgc_norm
  refine ⟨g * c, hgc_M, ?_⟩
  have hca : c * a * c⁻¹ = a := by
    have h := Subgroup.mem_centralizer_iff.mp hcC a (Set.mem_singleton a)
    rw [← h]; group
  calc g * c * a * (g * c)⁻¹ = g * (c * a * c⁻¹) * g⁻¹ := by group
    _ = g * a * g⁻¹ := by rw [hca]
    _ = b := hg

/-- **Mixed-case vacuity for the type-`P₁` `A_0`-support**: an `M_σ^#`-point (`= A(M)` for `P₁`) and
a `V^M`-point are never `G`-conjugate.  An `M_σ^#`-point is a `σ(M)`-element, conjugation preserves
this, and a `σ(M)`-element `v ∈ M` lies in the normal `σ`-Hall `M_σ = M'` (type `P₁`), contradicting
`v ∉ M'` (`typePData_typePV_not_mem_derived`). -/
theorem not_isConj_typePA_typePV_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) {x y : G}
    (hx : x ∈ typePA M data) (hy : y ∈ conjClassSetIn M (typePV M data))
    (hxy : IsConj x y) : False := by
  classical
  rw [typePA_eq_sigmaSharp_of_isTypeP1 hG hM data hP1] at hx
  have hxpi : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x :=
    OddOrder.BG.Ch4.S14.isPiElement_sigma_of_mem_Msigma hx.1
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  have hypi : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) y :=
    hg ▸ OddOrder.BG.Ch4.S14.isPiElement_conj g hxpi
  obtain ⟨v, hv, m, hmM, hmv⟩ := hy
  have hvpi : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) v := by
    have h1 : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) (m⁻¹ * y * m⁻¹⁻¹) :=
      OddOrder.BG.Ch4.S14.isPiElement_conj m⁻¹ hypi
    rwa [show m⁻¹ * y * m⁻¹⁻¹ = v from by rw [← hmv]; group] at h1
  have hvW : v ∈ data.W := by
    have hv' := hv
    simp only [typePV, Set.mem_diff] at hv'
    exact hv'.1
  have hvM : v ∈ M := by
    have hWM : (data.W : Subgroup G) ≤ M := by
      rw [data.W_eq]
      exact sup_le data.W1_le (data.W2_le.trans (inf_le_left.trans
        (data.H_le.trans (Subgroup.map_subtype_le _))))
    exact hWM hvW
  have hvpiG : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma M)
      (Subgroup.zpowers v) := by
    intro p hp
    rw [Nat.card_zpowers] at hp
    exact hvpi p hp
  have hvMσ : v ∈ OddOrder.BG.Ch3.S10.Msigma M :=
    OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM) (Subgroup.zpowers_le.mpr hvM)
      hvpiG (Subgroup.mem_zpowers v)
  rw [← OddOrder.BG.Ch4.S16.isTypeP1_derivedInG_eq_Msigma hG hM hP1] at hvMσ
  exact typePData_typePV_not_mem_derived data hv hvMσ

/-- **Peterfalvi (8.13.a) for the type-`P₁` `A_0`-support**: two `G`-conjugate elements of
`A_0(M) = A(M) ∪ V^M` are `M`-conjugate.  Three cases: both in `A(M) = M_σ^#`
(`sigmaSharp_isConj_conj_in_M`), both in `V^M` (`conjClassSetIn_typePV_isConj_conj_in_M`), or one of
each — the *mixed* case is vacuous (`not_isConj_typePA_typePV_of_isTypeP1`).  This is the `conj_in_L`
obligation for the type-`P₁` `A_0(M)` Dade support. -/
theorem typePA0_isConj_conj_in_M_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) {a b : G}
    (ha : a ∈ typePA0 M data) (hb : b ∈ typePA0 M data) (hab : IsConj a b) :
    ∃ m : G, m ∈ M ∧ m * a * m⁻¹ = b := by
  simp only [typePA0, Set.mem_union] at ha hb
  rcases ha with hpa | hva
  · rcases hb with hpb | hvb
    · rw [typePA_eq_sigmaSharp_of_isTypeP1 hG hM data hP1] at hpa hpb
      exact sigmaSharp_isConj_conj_in_M hG hM hpa hpb hab
    · exact (not_isConj_typePA_typePV_of_isTypeP1 hG hM data hP1 hpa hvb hab).elim
  · rcases hb with hpb | hvb
    · exact (not_isConj_typePA_typePV_of_isTypeP1 hG hM data hP1 hpb hva hab.symm).elim
    · exact conjClassSetIn_typePV_isConj_conj_in_M data hva hvb hab

/-- **(8.13.c2) coprimality for the exceptional `V^M`-support** (type `P₁`): for escaping
`a ∈ M_σ^#` and a `V^M`-point `b`, `|R(a)|` is coprime to `|C_M(b)|`.  `C_M(b)` is `M`-conjugate to
`C_M(v) = W` (`v ∈ V`: `C_G(v) = N_G(⟨v⟩) = W` by `normalizer_V`, using `W` abelian for `⊇`); picking
a nonidentity `w ∈ W₂ ⊆ M_σ^#`, `W ≤ C_M(w)` (abelian), so the `σ`-sharp coprimality
(`escaping_sigmaSharp_disjoint_centralizer`) at `w` kills every common prime.  This reduces the
exceptional-support coprimality to the σ-sharp one — the `V^M` half of the engine's
`centralizer_coprime`. -/
theorem coprime_FT_signalizer_centralizerIn_typePV [Fintype G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    {a : G} (haσ : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (haesc : ¬ Subgroup.centralizer ({a} : Set G) ≤ M)
    {b : G} (hb : b ∈ conjClassSetIn M (typePV M data)) :
    Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
      (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b)) := by
  classical
  obtain ⟨v, hv, m, hmM, hmv⟩ := hb
  have hvW : v ∈ data.W := by
    have hv' := hv; simp only [typePV, Set.mem_diff] at hv'; exact hv'.1
  have hWM : (data.W : Subgroup G) ≤ M := by
    rw [data.W_eq]
    exact sup_le data.W1_le (data.W2_le.trans (inf_le_left.trans
      (data.H_le.trans (Subgroup.map_subtype_le _))))
  haveI hcyc : IsCyclic ↥data.W := data.W_cyclic
  letI : CommGroup ↥data.W := hcyc.commGroup
  -- `C_G(v) = W` (`≤`: `normalizer_V`; `⊇`: `W` abelian).
  have hCGv : Subgroup.centralizer ({v} : Set G) = data.W := by
    refine le_antisymm ?_ ?_
    · rw [← data.normalizer_V {v} (Set.singleton_nonempty v) (Set.singleton_subset_iff.mpr hv)]
      intro g hg
      have hgv : g * v * g⁻¹ = v := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hg
        rw [mul_inv_eq_iff_eq_mul]; exact h
      rw [Subgroup.mem_set_normalizer_iff]
      intro n
      rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
      constructor
      · intro h; rw [h]; exact hgv
      · intro h
        calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
          _ = g⁻¹ * v * g := by rw [h]
          _ = g⁻¹ * (g * v * g⁻¹) * g := by rw [hgv]
          _ = v := by group
    · intro x hxW
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc : (⟨x, hxW⟩ : ↥data.W) * ⟨v, hvW⟩ = ⟨v, hvW⟩ * ⟨x, hxW⟩ := mul_comm _ _
      have := congrArg Subtype.val hc
      simpa using this
  have hcard_b : Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b) = Nat.card data.W := by
    rw [← hmv, OddOrder.Peterfalvi.S04.card_centralizerIn_conj hmM v,
      OddOrder.Peterfalvi.S04.centralizerIn, hCGv, inf_eq_right.mpr hWM]
  rw [hcard_b]
  -- coprime `|R(a)| |W|`: pick `w ∈ W₂^#`, `W ≤ C_M(w)`, and the σ-sharp coprimality.
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp data.W2_nontrivial
  have hwW : (w : G) ∈ data.W := (data.W_eq ▸ le_sup_right : data.W2 ≤ data.W) w.2
  have hw1' : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwMσ : (w : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := by
    have hHMσ : data.H ≤ OddOrder.BG.Ch3.S10.Msigma M := by
      rw [data.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hM
    exact hHMσ (Subgroup.mem_inf.mp (data.W2_le w.2)).1
  have hW_le_CMw : data.W ≤ OddOrder.Peterfalvi.S04.centralizerIn M (w : G) := by
    intro x hxW
    rw [OddOrder.Peterfalvi.S04.mem_centralizerIn]
    refine ⟨hWM hxW, ?_⟩
    have hc : (⟨x, hxW⟩ : ↥data.W) * ⟨(w : G), hwW⟩ = ⟨(w : G), hwW⟩ * ⟨x, hxW⟩ := mul_comm _ _
    have := congrArg Subtype.val hc
    simpa using this
  by_contra hnc
  obtain ⟨p, hpp, hpR, hpW⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase a) := by
    refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup (OddOrder.BG.Ch4.S16.FT_signalizerBase a) p
      (Nat.mem_primeFactors.mpr ⟨hpp, ?_, Nat.card_pos.ne'⟩)
    refine hpR.trans (Subgroup.card_dvd_of_le ?_)
    rw [OddOrder.BG.Ch4.S16.FT_signalizer]
    exact inf_le_left
  have hpCw : p ∣ Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M (w : G)) :=
    hpW.trans (Subgroup.card_dvd_of_le hW_le_CMw)
  exact escaping_sigmaSharp_disjoint_centralizer hG hM haσ haesc hwMσ hw1' hpp hpσ hpCw

/-- **Peterfalvi (8.15)** for type I: the Dade (2.2) support hypotheses hold for `A(M) = A_0(M)`
and `A₁(M)`, with `L = M` and the faithful `H(a) = R(a)` of (8.14).  Assembly is genuine
(`dadeSupportHypothesisData_of_subset`); the deep (8.13.a/c1/c2) obligations are the pins above. -/
theorem dadeSupportHypotheses_typeI [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIData M) :
    Nonempty (DadeSupportHypothesisData M (typeIA M data)) ∧
      Nonempty (DadeSupportHypothesisData M (A1 M PeterfalviType.I)) := by
  have hiffA : ∀ {m x : G}, m ∈ M → (m * x * m⁻¹ ∈ typeIA M data ↔ x ∈ typeIA M data) := by
    intro m x hm
    refine ⟨fun h => ?_, typeIA_conj_mem M data hm⟩
    have h2 := typeIA_conj_mem M data (inv_mem hm) h
    have h3 : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
    rwa [h3] at h2
  have hiffA1 : ∀ {m x : G}, m ∈ M →
      (m * x * m⁻¹ ∈ A1 M PeterfalviType.I ↔ x ∈ A1 M PeterfalviType.I) := by
    intro m x hm
    refine ⟨fun h => ?_, A1_conj_mem M OddOrder.GroupTheory.PeterfalviType.I hm⟩
    have h2 := A1_conj_mem M OddOrder.GroupTheory.PeterfalviType.I (inv_mem hm) h
    have h3 : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
    rwa [h3] at h2
  constructor
  · exact dadeSupportHypothesisData_of_subset hG hM data (fun _ h => h)
      (typeIA_nonempty M data) @hiffA
  · refine dadeSupportHypothesisData_of_subset hG hM data (A1_subset_typeIA M data) ?_ @hiffA1
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp data.typeF.H_nontrivial
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have haH : a.1 ∈ mainSubgroup M PeterfalviType.I := by
      show a.1 ∈ maxNilpotentNormalHall M
      rw [← data.typeF.H_eq]
      exact a.2
    exact ⟨a.1, (Set.mem_diff _).mpr
      ⟨SetLike.mem_coe.mpr haH, fun h => ha1' (Set.mem_singleton_iff.mp h)⟩⟩

/-- **(8.14) kernel equivariance at a `σ`-sharp escaping point** (`σ`-generic form of
`FT_signalizer_conj_smul_of_escaping`): `R(m·a·m⁻¹) = m·R(a)·m⁻¹` for `m ∈ M`.  The type-I proof
only used `κ = ∅` to pin `σ`-sharpness of `a` and its conjugate — here both are hypotheses.  Both
supporting maximals are pinned by singleton uniqueness, `MulAut.conj m • N[a]` is maximal over
`m·C_G(a)·m⁻¹`, and `R = N_σ ⊓ C_G(·)` transports by `M_σ`-equivariance. -/
theorem FT_signalizer_conj_smul_of_escaping_sigmaSharp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {a m : G} (hm : m ∈ M)
    (hσ : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (hesc : ¬ Subgroup.centralizer ({a} : Set G) ≤ M)
    (hσ' : m * a * m⁻¹ ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (hesc' : ¬ Subgroup.centralizer ({m * a * m⁻¹} : Set G) ≤ M) :
    OddOrder.BG.Ch4.S16.FT_signalizer (m * a * m⁻¹)
      = MulAut.conj m • OddOrder.BG.Ch4.S16.FT_signalizer a := by
  classical
  obtain ⟨N, hN⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG hM hσ hesc
  obtain ⟨N', hN'⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG hM hσ' hesc'
  have hNmem : N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G)) := by
    rw [hN]; rfl
  obtain ⟨hNmax, hCN⟩ := mem_maximalSubgroupsContaining.mp hNmem
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a).ncard := by
    by_contra h
    push_neg at h
    exact hesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hM hσ.1 hσ.2 h)
  have hgt' : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement (m * a * m⁻¹)).ncard := by
    by_contra h
    push_neg at h
    exact hesc'
      (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hM hσ'.1 hσ'.2 h)
  have hbr : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G))).Nonempty :=
    ⟨hgt, ⟨N, hNmem⟩⟩
  have hbr' : 1 <
      (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement (m * a * m⁻¹)).ncard ∧
      (maximalSubgroupsContaining
        (Subgroup.centralizer ({m * a * m⁻¹} : Set G))).Nonempty :=
    ⟨hgt', ⟨N', by rw [hN']; rfl⟩⟩
  have huniq : ∀ L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G)),
      L = N := by
    intro L hL
    rw [hN, Set.mem_singleton_iff] at hL
    exact hL
  have huniq' : ∀ L ∈ maximalSubgroupsContaining
      (Subgroup.centralizer ({m * a * m⁻¹} : Set G)), L = N' := by
    intro L hL
    rw [hN', Set.mem_singleton_iff] at hL
    exact hL
  have hbase : OddOrder.BG.Ch4.S16.FT_signalizerBase a = N := by
    have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase a = hbr.2.choose := dif_pos hbr
    rw [hb]
    exact huniq _ hbr.2.choose_spec
  have hCconj : Subgroup.centralizer ({m * a * m⁻¹} : Set G)
      = MulAut.conj m • Subgroup.centralizer ({a} : Set G) :=
    (conj_smul_centralizer_singleton' m a).symm
  have hbase' : OddOrder.BG.Ch4.S16.FT_signalizerBase (m * a * m⁻¹) = MulAut.conj m • N := by
    have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase (m * a * m⁻¹) = hbr'.2.choose :=
      dif_pos hbr'
    have hmemN' : MulAut.conj m • N ∈
        maximalSubgroupsContaining (Subgroup.centralizer ({m * a * m⁻¹} : Set G)) := by
      rw [mem_maximalSubgroupsContaining]
      refine ⟨OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hNmax), ?_⟩
      rw [hCconj]
      exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hCN
    rw [hb, huniq' _ hbr'.2.choose_spec]
    exact (huniq' _ hmemN').symm
  rw [OddOrder.BG.Ch4.S16.FT_signalizer, OddOrder.BG.Ch4.S16.FT_signalizer, hbase, hbase',
    Msigma_conj_smul', hCconj, conj_smul_inf']

/-- The faithful kernel is `M`-conjugation equivariant on an `M`-invariant sub-support of `M_σ^#`
(`σ`-generic form of `ftSupportKernel_conj_smul`). -/
theorem ftSupportKernel_conj_smul_sigmaSharp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {X : Set G} (hXσ : X ⊆ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (hXiff : ∀ {m x : G}, m ∈ M → (m * x * m⁻¹ ∈ X ↔ x ∈ X))
    {a m : G} (hm : m ∈ M) :
    ftSupportKernel M X (m * a * m⁻¹) = MulAut.conj m • ftSupportKernel M X a := by
  by_cases hesc : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
  · have hconj_esc := (escapingCentralizerSet_conj_mem hm (hXiff hm)).mpr hesc
    rw [ftSupportKernel_eq_of_escaping hconj_esc, ftSupportKernel_eq_of_escaping hesc]
    exact FT_signalizer_conj_smul_of_escaping_sigmaSharp hG hM hm (hXσ hesc.1) hesc.2
      (hXσ hconj_esc.1) hconj_esc.2
  · rw [ftSupportKernel_eq_bot_of_not_escaping
        (fun h => hesc ((escapingCentralizerSet_conj_mem hm (hXiff hm)).mp h)),
      ftSupportKernel_eq_bot_of_not_escaping hesc, Subgroup.smul_bot]

/-- **Faithful (8.15) datum for an `M`-invariant sub-support of `M_σ^#`** (`σ`-generic engine): the
same assembly as `dadeSupportHypothesisData_of_subset`, but driven by the three `σ`-decomposition-
generic pins (`sigmaSharp_isConj_conj_in_M`, `escaping_sigmaSharp_signalizer_structure`,
`escaping_sigmaSharp_disjoint_centralizer`) instead of the type-I lemmas.  Any `X ⊆ M_σ^#` that is
`M`-conjugation-invariant and nonempty carries the Dade (2.2) support data.  Instantiated at
`X = A₁(M) = M_σ^#` (all types) and the type-`P₁` `A(M) = M_σ^#`. -/
theorem dadeSupportHypothesisData_of_subset_sigmaSharp [Fintype G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    {X : Set G} (hXσ : X ⊆ OddOrder.BG.Ch4.S14.sigmaSharp M) (hXne : X.Nonempty)
    (hXiff : ∀ {m x : G}, m ∈ M → (m * x * m⁻¹ ∈ X ↔ x ∈ X)) :
    Nonempty (DadeSupportHypothesisData M X) := by
  classical
  have hXsharp : ∀ x ∈ X, x ≠ (1 : G) := fun x hx => (hXσ hx).2
  have hXM : X ⊆ (M : Set G) := fun x hx => OddOrder.BG.Ch3.S10.Msigma_le M (hXσ hx).1
  have hstruct : ∀ {a : G}, a ∈ OddOrder.GroupTheory.escapingCentralizerSet M X →
      Subgroup.centralizer ({a} : Set G)
          = OddOrder.BG.Ch4.S16.FT_signalizer a ⊔ OddOrder.Peterfalvi.S04.centralizerIn M a ∧
        Disjoint (OddOrder.BG.Ch4.S16.FT_signalizer a)
          (OddOrder.Peterfalvi.S04.centralizerIn M a) ∧
        (∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ OddOrder.BG.Ch4.S16.FT_signalizer a,
          c * y * c⁻¹ ∈ OddOrder.BG.Ch4.S16.FT_signalizer a) ∧
        (∀ b ∈ OddOrder.BG.Ch4.S14.sigmaSharp M,
          Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
            (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b))) := by
    intro a ha
    have hσa : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M := hXσ ha.1
    obtain ⟨hjoin, hdisj, hnormc⟩ :=
      escaping_sigmaSharp_signalizer_structure hG hM hσa ha.2
    refine ⟨hjoin, hdisj, hnormc, ?_⟩
    intro b hb
    by_contra hnc
    obtain ⟨p, hpp, hpR, hpC⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase a) := by
      refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup (OddOrder.BG.Ch4.S16.FT_signalizerBase a) p
        (Nat.mem_primeFactors.mpr ⟨hpp, ?_, Nat.card_pos.ne'⟩)
      refine hpR.trans (Subgroup.card_dvd_of_le ?_)
      rw [OddOrder.BG.Ch4.S16.FT_signalizer]
      exact inf_le_left
    exact escaping_sigmaSharp_disjoint_centralizer hG hM hσa ha.2 hb.1 hb.2 hpp hpσ hpC
  refine ⟨{ normalizer_eq := normalizer_support_eq hG hM hXM hXsharp hXne @hXiff
            dade :=
              { subset_sharp := fun x hx =>
                  OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ x, hXsharp x hx⟩
                subset_L := fun x hx => hXM hx
                L_normalizes_A := fun l a ha => (hXiff l.2).mpr ha
                H := fun a => ftSupportKernel M X a.1
                conj_in_L := by
                  intro a b ha hb hab
                  obtain ⟨m, hmM, hmab⟩ :=
                    sigmaSharp_isConj_conj_in_M hG hM (hXσ ha) (hXσ hb) hab
                  exact ⟨⟨m, hmM⟩, hmab⟩
                centralizer_eq_sup := by
                  intro a
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).1
                  · have hle : Subgroup.centralizer ({a.1} : Set G) ≤ M := by
                      by_contra hnle
                      exact hesc ⟨a.2, hnle⟩
                    rw [ftSupportKernel_eq_bot_of_not_escaping hesc, bot_sup_eq]
                    exact (inf_eq_right.mpr hle).symm
                centralizer_disjoint := by
                  intro a
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).2.1
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc]
                    exact disjoint_bot_left
                H_normalized := by
                  intro a c hc x hx
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc] at hx ⊢
                    exact (hstruct hesc).2.2.1 c hc x hx
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc] at hx ⊢
                    rw [Subgroup.mem_bot] at hx ⊢
                    rw [hx]
                    group
                centralizer_coprime := by
                  intro a b
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).2.2.2 b.1 (hXσ b.2)
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc]
                    simpa using Nat.coprime_one_left _ }
            H_eq_ftSupportKernel := fun _ => rfl
            hconj := fun a l => ftSupportKernel_conj_smul_sigmaSharp hG hM hXσ @hXiff l.2 }⟩

/-- The faithful kernel is `M`-conjugation equivariant when `X ⊆ M` has all *escaping* points
`σ`-sharp (the general form, driven by `escaping ⊆ M_σ^#` instead of `X ⊆ M_σ^#`). -/
theorem ftSupportKernel_conj_smul_escaping_sigmaSharp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {X : Set G} (hXesc : ∀ a ∈ OddOrder.GroupTheory.escapingCentralizerSet M X,
      a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (hXiff : ∀ {m x : G}, m ∈ M → (m * x * m⁻¹ ∈ X ↔ x ∈ X))
    {a m : G} (hm : m ∈ M) :
    ftSupportKernel M X (m * a * m⁻¹) = MulAut.conj m • ftSupportKernel M X a := by
  by_cases hesc : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
  · have hconj_esc := (escapingCentralizerSet_conj_mem hm (hXiff hm)).mpr hesc
    rw [ftSupportKernel_eq_of_escaping hconj_esc, ftSupportKernel_eq_of_escaping hesc]
    exact FT_signalizer_conj_smul_of_escaping_sigmaSharp hG hM hm (hXesc a hesc) hesc.2
      (hXesc _ hconj_esc) hconj_esc.2
  · rw [ftSupportKernel_eq_bot_of_not_escaping
        (fun h => hesc ((escapingCentralizerSet_conj_mem hm (hXiff hm)).mp h)),
      ftSupportKernel_eq_bot_of_not_escaping hesc, Subgroup.smul_bot]

/-- **Faithful (8.15) datum for an `M`-invariant `X ⊆ M` whose escaping points are `σ`-sharp**
(the general `σ`-decomposition engine).  Generalises `dadeSupportHypothesisData_of_subset_sigmaSharp`
from `X ⊆ M_σ^#` to `X ⊆ M` with escaping points in `M_σ^#`, taking the `(8.13.a)` `conj_in_L` and the
`(8.13.c2)` coprimality as inputs (the escaping structure `(8.13.c1)` is still the `σ`-generic
`escaping_sigmaSharp_signalizer_structure`).  Instantiated at `X = A_0(M)` for type `P₁`. -/
theorem dadeSupportHypothesisData_of_subset_escaping_sigmaSharp [Fintype G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {X : Set G} (hXM : X ⊆ (M : Set G)) (hXsharp : ∀ x ∈ X, x ≠ (1 : G))
    (hXesc : ∀ a ∈ OddOrder.GroupTheory.escapingCentralizerSet M X,
      a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (hXconj : ∀ a ∈ X, ∀ b ∈ X, IsConj a b → ∃ m : G, m ∈ M ∧ m * a * m⁻¹ = b)
    (hXcop : ∀ a ∈ OddOrder.GroupTheory.escapingCentralizerSet M X, ∀ b ∈ X,
      Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
        (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b)))
    (hXne : X.Nonempty)
    (hXiff : ∀ {m x : G}, m ∈ M → (m * x * m⁻¹ ∈ X ↔ x ∈ X)) :
    Nonempty (DadeSupportHypothesisData M X) := by
  classical
  have hstruct : ∀ {a : G}, a ∈ OddOrder.GroupTheory.escapingCentralizerSet M X →
      Subgroup.centralizer ({a} : Set G)
          = OddOrder.BG.Ch4.S16.FT_signalizer a ⊔ OddOrder.Peterfalvi.S04.centralizerIn M a ∧
        Disjoint (OddOrder.BG.Ch4.S16.FT_signalizer a)
          (OddOrder.Peterfalvi.S04.centralizerIn M a) ∧
        (∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ OddOrder.BG.Ch4.S16.FT_signalizer a,
          c * y * c⁻¹ ∈ OddOrder.BG.Ch4.S16.FT_signalizer a) ∧
        (∀ b ∈ X, Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
            (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b))) := by
    intro a ha
    obtain ⟨hjoin, hdisj, hnormc⟩ :=
      escaping_sigmaSharp_signalizer_structure hG hM (hXesc a ha) ha.2
    exact ⟨hjoin, hdisj, hnormc, fun b hb => hXcop a ha b hb⟩
  refine ⟨{ normalizer_eq := normalizer_support_eq hG hM hXM hXsharp hXne @hXiff
            dade :=
              { subset_sharp := fun x hx =>
                  OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ x, hXsharp x hx⟩
                subset_L := fun x hx => hXM hx
                L_normalizes_A := fun l a ha => (hXiff l.2).mpr ha
                H := fun a => ftSupportKernel M X a.1
                conj_in_L := by
                  intro a b ha hb hab
                  obtain ⟨m, hmM, hmab⟩ := hXconj a ha b hb hab
                  exact ⟨⟨m, hmM⟩, hmab⟩
                centralizer_eq_sup := by
                  intro a
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).1
                  · have hle : Subgroup.centralizer ({a.1} : Set G) ≤ M := by
                      by_contra hnle
                      exact hesc ⟨a.2, hnle⟩
                    rw [ftSupportKernel_eq_bot_of_not_escaping hesc, bot_sup_eq]
                    exact (inf_eq_right.mpr hle).symm
                centralizer_disjoint := by
                  intro a
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).2.1
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc]
                    exact disjoint_bot_left
                H_normalized := by
                  intro a c hc x hx
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc] at hx ⊢
                    exact (hstruct hesc).2.2.1 c hc x hx
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc] at hx ⊢
                    rw [Subgroup.mem_bot] at hx ⊢
                    rw [hx]
                    group
                centralizer_coprime := by
                  intro a b
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).2.2.2 b.1 b.2
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc]
                    simpa using Nat.coprime_one_left _ }
            H_eq_ftSupportKernel := fun _ => rfl
            hconj := fun a l =>
              ftSupportKernel_conj_smul_escaping_sigmaSharp hG hM hXesc @hXiff l.2 }⟩

/-- **(8.13.c2) coprimality for the full type-`P₁` `A_0`-support**: for escaping `a ∈ M_σ^#` and any
`b ∈ A_0(M)`, `|R(a)|` is coprime to `|C_M(b)|`.  Splits `A_0 = A(M) ∪ V^M`: for `b ∈ A(M) = M_σ^#`
it is the σ-sharp coprimality (`escaping_sigmaSharp_disjoint_centralizer`); for `b ∈ V^M` it is
`coprime_FT_signalizer_centralizerIn_typePV`. -/
theorem coprime_FT_signalizer_centralizerIn_typePA0_of_isTypeP1 [Fintype G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M)
    {a : G} (haσ : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (haesc : ¬ Subgroup.centralizer ({a} : Set G) ≤ M)
    {b : G} (hb : b ∈ typePA0 M data) :
    Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
      (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b)) := by
  simp only [typePA0, Set.mem_union] at hb
  rcases hb with hpb | hvb
  · rw [typePA_eq_sigmaSharp_of_isTypeP1 hG hM data hP1] at hpb
    by_contra hnc
    obtain ⟨p, hpp, hpR, hpC⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase a) := by
      refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup (OddOrder.BG.Ch4.S16.FT_signalizerBase a) p
        (Nat.mem_primeFactors.mpr ⟨hpp, ?_, Nat.card_pos.ne'⟩)
      refine hpR.trans (Subgroup.card_dvd_of_le ?_)
      rw [OddOrder.BG.Ch4.S16.FT_signalizer]
      exact inf_le_left
    exact escaping_sigmaSharp_disjoint_centralizer hG hM haσ haesc hpb.1 hpb.2 hpp hpσ hpC
  · exact coprime_FT_signalizer_centralizerIn_typePV hG hM data haσ haesc hvb

/-- **Peterfalvi (8.15) type-`P₁` `A_0(M)` datum**: the Dade (2.2) support hypotheses hold for the
full type-`P₁` support `A_0(M) = A(M) ∪ V^M`.  Assembles the `σ`-decomposition-generic engine
(`dadeSupportHypothesisData_of_subset_escaping_sigmaSharp`) with the type-`P₁` pins: escaping points
are `σ`-sharp (`escaping_typePA0_mem_sigmaSharp_of_isTypeP1`, `(8.13.b)`), the `conj_in_L`
(`typePA0_isConj_conj_in_M_of_isTypeP1`, `(8.13.a)`), and the coprimality
(`coprime_FT_signalizer_centralizerIn_typePA0_of_isTypeP1`, `(8.13.c2)`), plus the union set-facts
(`A_0 ⊆ M`, non-identity, nonempty, `M`-conjugation-invariant). -/
theorem dadeSupportHypothesisData_typePA0_of_isTypeP1 [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) :
    Nonempty (DadeSupportHypothesisData M (typePA0 M data)) := by
  classical
  have hVM : typePV M data ⊆ (M : Set G) := by
    intro v hv
    have hvW : v ∈ data.W := by simp only [typePV, Set.mem_diff] at hv; exact hv.1
    exact (show (data.W : Subgroup G) ≤ M by
      rw [data.W_eq]; exact sup_le data.W1_le (data.W2_le.trans (inf_le_left.trans
        (data.H_le.trans (Subgroup.map_subtype_le _))))) hvW
  refine dadeSupportHypothesisData_of_subset_escaping_sigmaSharp hG hM ?_ ?_
    (fun a ha => escaping_typePA0_mem_sigmaSharp_of_isTypeP1 hG hM data hP1 ha)
    (fun a ha b hb hab => typePA0_isConj_conj_in_M_of_isTypeP1 hG hM data hP1 ha hb hab)
    (fun a ha b hb => coprime_FT_signalizer_centralizerIn_typePA0_of_isTypeP1 hG hM data hP1
      (escaping_typePA0_mem_sigmaSharp_of_isTypeP1 hG hM data hP1 ha) ha.2 hb)
    ?_ ?_
  · -- `A_0(M) ⊆ M`
    intro x hx
    rcases hx with hpa | hva
    · rw [typePA_eq_sharpSubgroup_derivedInG] at hpa
      exact (Subgroup.map_subtype_le _) ((Set.mem_diff _).mp hpa).1
    · exact conjClassSetIn_subset hVM hva
  · -- `x ≠ 1`
    intro x hx
    rcases hx with hpa | hva
    · rw [typePA_eq_sharpSubgroup_derivedInG] at hpa
      exact fun h => ((Set.mem_diff _).mp hpa).2 (Set.mem_singleton_iff.mpr h)
    · obtain ⟨v, hv, m, hmM, hmv⟩ := hva
      have hv1 : v ≠ 1 := by
        rintro rfl
        have h1 := hv
        simp only [typePV, Set.mem_diff, Set.mem_union] at h1
        exact h1.2 (Or.inl (Subgroup.one_mem data.W1))
      intro hx1
      apply hv1
      calc v = m⁻¹ * (m * v * m⁻¹) * m := by group
        _ = m⁻¹ * x * m := by rw [hmv]
        _ = m⁻¹ * 1 * m := by rw [hx1]
        _ = 1 := by group
  · -- `A_0(M)` nonempty
    obtain ⟨a, ha1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM)
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    refine ⟨a.1, Or.inl ?_⟩
    rw [typePA_eq_sigmaSharp_of_isTypeP1 hG hM data hP1]
    exact (Set.mem_diff _).mpr
      ⟨SetLike.mem_coe.mpr a.2, fun h => ha1' (Set.mem_singleton_iff.mp h)⟩
  · -- `M`-conjugation invariance
    intro m x hm
    simp only [typePA0, Set.mem_union]
    constructor
    · rintro (hpa | hva)
      · exact Or.inl (by
          have := typePA_conj_mem M data (inv_mem hm) hpa
          rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x from by group] at this)
      · exact Or.inr ((mem_conjClassSetIn_conj_iff hm x).mp hva)
    · rintro (hpa | hva)
      · exact Or.inl (typePA_conj_mem M data hm hpa)
      · exact Or.inr ((mem_conjClassSetIn_conj_iff hm x).mpr hva)

/-- **Peterfalvi (8.15)** for type `P₁` (BG types III/IV/V): the Dade (2.2) support hypotheses hold
for `A_0(M)`, `A(M)`, and `A_1(M)`, with `L=M` and `H(a)=R(a)`.

**Restricted to `P₁`** (issue 9008).  Peterfalvi (8.10) defines the type-`P` support as
`A(M) = ⋃_{x∈M_s^#} C_{M'}(x)^#` indexed over the **core** `M_s^# = M_σ^#`.  For `P₁` (`M_σ = M'`)
this equals `(M')^#`, which is exactly `typePA` (`typePA_eq_sigmaSharp_of_isTypeP1`).  For `P₂`
(type II, `M_σ = M_F ⊊ M'`) the correct `A(M)` is *strictly smaller* than `(M')^#`: it excludes the
Frobenius-complement points `U^#` (which have `C_{M_σ} = 1`).  Since `typePA` models the full `(M')^#`
(the `.mmd` extraction of (8.10) dropped the `M_s → M` subscript — see 9008), the `P₂` Dade support
over `typePA` is **false-as-stated**: those `U^#` points can escape `M` yet are not `σ`-sharp,
violating (8.13.b).  It also has **no on-path consumer** — the sole intended consumer
(`S12.Hypothesis.dadeData`) is `IsTypeIII ∨ IsTypeIV ∨ IsTypeV = P₁`, and type-II Dade support flows
through `Section16CharacterData.A0S` (an abstract `Set ↥S`, off-path/vestigial), not `typePA0`.  The
"deep `P₂` geometry" chased by earlier loops was that OCR error; the `hP1` hypothesis is the honest
scope.  (If a type-II consumer ever needs the *correct* `A(S)`, redefine `typePA` to index over
`M_σ^#`; the `P₂` escape then reduces to the type-I `ASet` bridge — see 9008 Option A.) -/
theorem dadeSupportHypotheses_typeP [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M)
    {tau : PeterfalviType} (hType : HasPeterfalviType tau M) :
    Nonempty (DadeSupportHypothesisData M (typePA0 M data)) ∧
      Nonempty (DadeSupportHypothesisData M (typePA M data)) ∧
        Nonempty (DadeSupportHypothesisData M (A1 M tau)) := by
  -- The `A_1(M) = M_σ^#` datum (all types, `A1_eq_sigmaSharp`) via the `σ`-sharp Dade engine.
  -- Reused for `A_1(M)` and — since `A(M) = M_σ^#` for `P₁` — the type-`P₁` case of `A(M)`.
  have hA1 : Nonempty (DadeSupportHypothesisData M (A1 M tau)) := by
    refine dadeSupportHypothesisData_of_subset_sigmaSharp hG hM
      (OddOrder.BG.Ch4.S16.A1_eq_sigmaSharp hG hM hType).subset ?_ ?_
    · obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
        (show OddOrder.GroupTheory.mainSubgroup M tau ≠ ⊥ by
          rw [OddOrder.BG.Ch4.S16.mainSubgroup_eq_Msigma hG hM hType]
          exact OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM)
      have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
      exact ⟨a.1, (Set.mem_diff _).mpr
        ⟨SetLike.mem_coe.mpr a.2, fun h => ha1' (Set.mem_singleton_iff.mp h)⟩⟩
    · intro m x hm
      refine ⟨fun h => ?_, A1_conj_mem M tau hm⟩
      have h2 := A1_conj_mem M tau (inv_mem hm) h
      have h3 : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
      rwa [h3] at h2
  refine ⟨?_, ?_, hA1⟩
  · -- `A_0(M) = A(M) ∪ V^M`, type-`P₁`: the σ-decomposition engine assembles the full datum.
    exact dadeSupportHypothesisData_typePA0_of_isTypeP1 hG hM data hP1
  · -- `A(M) = (M')^# = M_σ^# = A_1(M)` for `P₁` (`typePA_eq_sigmaSharp_of_isTypeP1` +
    -- `A1_eq_sigmaSharp`), so the `A_1` datum transports directly.
    rw [typePA_eq_sigmaSharp_of_isTypeP1 hG hM data hP1,
      ← OddOrder.BG.Ch4.S16.A1_eq_sigmaSharp hG hM hType]
    exact hA1

/-! ### (8.17.c) bridge: the faithful thickened `A₁`-support is the BG `M̃`-cover

`Ã₁(M) = ⋃_{x∈A₁}(x·R(x))^G` with the faithful kernel is exactly `𝒞_G(M̃)` for BG's
`M̃ = ⋃_{x∈M_σ^#} x·R(x)` — for type I/II, `A₁(M) = M_σ^#` (`A1_eq_sigmaSharp_of_typeI_or_II`)
and both kernels are the Theorem-14.4 signalizer of the **unique** maximal over `C_G(x)`.  The
(8.17.c) `Ã₁`-disjointness for non-conjugate maximals then *is* BG 14.5(b)
(`conjClassSet_Mtilde_disjoint`), sorry-free. -/

/-- **The faithful kernel agrees with the BG signalizer on escaping `σ`-sharp points**:
`FT_signalizer x = Rsub x`.  Escape forces `1 < |𝓜_σ(x)|`
(`centralizer_le_of_maximalSigma_le_one`), so both branches are live, and both choices are *the*
unique maximal over `C_G(x)`
(`maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape`). -/
theorem FT_signalizer_eq_Rsub_of_escape [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G}
    (hx : x ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    OddOrder.BG.Ch4.S16.FT_signalizer x
      = OddOrder.BG.Ch4.S14.Rsub hG (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG) x := by
  classical
  have hx1 : x ≠ 1 := hx.2
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := hx.1
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement x).ncard := by
    by_contra h
    exact hesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hM hxMσ hx1
      (not_lt.mp h))
  have hlen : (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG).length x = 1 :=
    OddOrder.BG.Ch4.S14.Msigma_ell1 hG hM hxMσ hx1
  obtain ⟨N, hsingle⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG hM hx hesc
  have hbranch : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement x).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G))).Nonempty :=
    ⟨hgt, hsingle ▸ ⟨N, rfl⟩⟩
  -- both `choose`s land in the singleton `{N}`
  have hbase_eq : OddOrder.BG.Ch4.S16.FT_signalizerBase x = N := by
    have hmem : OddOrder.BG.Ch4.S16.FT_signalizerBase x
        ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) := by
      rw [show OddOrder.BG.Ch4.S16.FT_signalizerBase x = hbranch.2.choose from dif_pos hbranch]
      exact hbranch.2.choose_spec
    rw [hsingle, Set.mem_singleton_iff] at hmem
    exact hmem
  have hstruct := (OddOrder.BG.Ch4.S14.sigmaLength_one_centralizer_structure hG
    (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG) hx1 hlen).2 hgt
  have hN'_eq : hstruct.exists.choose = N := by
    have hmem : hstruct.exists.choose
        ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
      ⟨mem_maximalSubgroups.mp hstruct.exists.choose_spec.1, hstruct.exists.choose_spec.2.1⟩
    have hmem2 : hstruct.exists.choose ∈ ({N} : Set (Subgroup G)) := by
      rw [← hsingle]; exact hmem
    exact Set.mem_singleton_iff.mp hmem2
  rw [OddOrder.BG.Ch4.S14.Rsub_eq_inf hG (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG)
    hx1 hlen hgt]
  show OddOrder.BG.Ch3.S10.Msigma (OddOrder.BG.Ch4.S16.FT_signalizerBase x)
      ⊓ Subgroup.centralizer ({x} : Set G) = _
  rw [hbase_eq, hN'_eq]

/-- **The faithful thickened `A₁`-support lands in the `M̃`-cover**:
`Ã₁(M) ⊆ 𝒞_G(M̃)` for type-I/II `M`.  Escaping points contribute `x·R(x)` with
`R(x) = FT_signalizer x = Rsub x` (the defining generators of `M̃`); non-escaping points
contribute the bare `x = x·1 ∈ M̃`. -/
theorem ftThickenedSupport_A1_subset_conjClassSet_Mtilde [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M ∨ IsTypeII M)
    {tau : PeterfalviType} (htau : tau = PeterfalviType.I ∨ tau = PeterfalviType.II) :
    ftThickenedSupport M (A1 M tau) ⊆
      conjClassSet (OddOrder.BG.Ch4.S14.Mtilde hG
        (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG) M) := by
  have hA1σ : A1 M tau = OddOrder.BG.Ch4.S14.sigmaSharp M :=
    OddOrder.Peterfalvi.S10Interface.A1_eq_sigmaSharp_of_typeI_or_II hG hM hType htau
  rintro y ⟨x, hxA1, hy⟩
  have hxσ : x ∈ OddOrder.BG.Ch4.S14.sigmaSharp M := hA1σ ▸ hxA1
  refine conjClassSet_mono ?_ hy
  rintro z ⟨r, hr, rfl⟩
  by_cases hesc : x ∈ OddOrder.GroupTheory.escapingCentralizerSet M (A1 M tau)
  · rw [SetLike.mem_coe, ftSupportKernel_eq_of_escaping hesc,
      FT_signalizer_eq_Rsub_of_escape hG hM hxσ hesc.2] at hr
    exact ⟨x, hxσ, r, hr, rfl⟩
  · rw [SetLike.mem_coe, ftSupportKernel_eq_bot_of_not_escaping hesc, Subgroup.mem_bot] at hr
    exact ⟨x, hxσ, r, by rw [hr]; exact one_mem _, rfl⟩

/-- **Peterfalvi (8.17.c), `Ã₁`-disjointness** (the disjointness core of BG Theorem E /
Coq `FT_Dade1_support_disjoint`): the faithful thickened `A₁`-supports of non-conjugate
type-I/II maximal subgroups are disjoint.  Sorry-free: both supports embed in the disjoint
`𝒞_G(M̃)`-covers (`conjClassSet_Mtilde_disjoint`, BG 14.5(b)). -/
theorem ftThickenedSupport_A1_disjoint_of_nonconjugate [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L1 L2 : Subgroup G}
    (hL1 : L1 ∈ maximalSubgroups G) (hL2 : L2 ∈ maximalSubgroups G)
    (hT1 : IsTypeI L1 ∨ IsTypeII L1) (hT2 : IsTypeI L2 ∨ IsTypeII L2)
    {tau1 tau2 : PeterfalviType}
    (ht1 : tau1 = PeterfalviType.I ∨ tau1 = PeterfalviType.II)
    (ht2 : tau2 = PeterfalviType.I ∨ tau2 = PeterfalviType.II)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L1 L2) :
    Disjoint (ftThickenedSupport L1 (A1 L1 tau1)) (ftThickenedSupport L2 (A1 L2 tau2)) :=
  Disjoint.mono (ftThickenedSupport_A1_subset_conjClassSet_Mtilde hG hL1 hT1 ht1)
    (ftThickenedSupport_A1_subset_conjClassSet_Mtilde hG hL2 hT2 ht2)
    (OddOrder.BG.Ch4.S14.conjClassSet_Mtilde_disjoint hG
      (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG) hL1 hL2 hnc)

/-! ### (8.18): the support graph and the mixed `Ã₁ ∩ Ã` disjointness

Peterfalvi (8.18) for a type-I pair, in conjugation-free form.  The deep §16 inputs are pinned:
(8.13.b) escaping points lie in `A₁` (`escaping_typeIA_mem_A1`), (8.12.b) the unique maximal over
the centralizer of an `A(T)`-point of `σ(T)′`-order (`typeI_centralizer_le_and_unique`), and the
(8.13.c2/c4) cross-coprimality under support (`supported_sigma_coprime`).  The (8.18.a/b/c)
assembly — the `σ`-order bookkeeping, the escape to the proven `Ã₁`-disjointness, the `π`-part
power argument, and the final two-sided contradiction — is genuine. -/

/-- **Peterfalvi (8.13.b), `D ⊆ A₁` conjunct**: an escaping point of the type-I support `A(M)`
lies in the sharp core `A₁(M)`.  The BG `D ⊆ M_σ^#` reduction of Theorem II conjunct 2
(`mem_sigmaSharp_of_mem_aSet_of_escape`, fed through the `typeIA_subset_ASet` bridge), with
`A₁(M) = M_σ^#` the type-I support-set bridge (`A1_eq_sigmaSharp_of_typeI_or_II`). -/
theorem escaping_typeIA_mem_A1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypeIData M)
    {a : G} (ha : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M (typeIA M data)) :
    a ∈ A1 M PeterfalviType.I := by
  obtain ⟨haA, hesc⟩ := ha
  have hκ : OddOrder.BG.Ch4.S14.kappa M = ∅ :=
    (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hM).mp ⟨data⟩
  have hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M)
      ((⊥ : Subgroup G).subgroupOf M) := by
    rw [Subgroup.bot_subgroupOf, OddOrder.Isaacs.Ch03.IsHallSubgroup.bot_iff]
    intro p _
    rw [hκ]
    exact Set.notMem_empty p
  have hσ : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M :=
    OddOrder.BG.Ch4.S16.mem_sigmaSharp_of_mem_aSet_of_escape hG hM bot_le data.typeF.U_le hK
      (typeF_complement_isHall_kappa_sigma_compl hG hM data) (Or.inl rfl)
      (typeIA_subset_ASet hG hM data haA) haA.2.1 hesc
  have hA1 : A1 M PeterfalviType.I = OddOrder.BG.Ch4.S14.sigmaSharp M :=
    OddOrder.Peterfalvi.S10Interface.A1_eq_sigmaSharp_of_typeI_or_II hG hM
      (Or.inl ⟨data⟩) (Or.inl rfl)
  rw [hA1]
  exact hσ

/-- The centralizer of the cyclic subgroup `⟨z⟩` is the centralizer of `z` (powers commute). -/
private theorem centralizer_zpowers_eq_singleton' (z : G) :
    Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)
      = Subgroup.centralizer ({z} : Set G) := by
  ext c
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hc z (SetLike.mem_coe.mpr (Subgroup.mem_zpowers z))
  · intro hc y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hy)
    have hzc : Commute z c := hc z (Set.mem_singleton z)
    exact (hzc.zpow_left n).eq

/-- **Peterfalvi (8.12.b), single-point form**: for type-I `T` and `x ∈ T` of order coprime to
`|T_F|` centralizing a nontrivial element of `T_F`, `T` is the unique maximal subgroup
containing `C_G(x)`.

BG §16 Theorem B, centralizer clause (`theoremB_U_and_A_tame`, conjunct 4), reached through the
Hall-conjugacy move: `x` is a `(κ ∪ σ)′`-element of the solvable `T` (its order is coprime to
`|T_F| = |M_σ|`), so Hall D/C (`hall_D`/`hall_C`) conjugate `⟨x⟩` into the type-`F` complement
`U` by some `t ∈ T`; the conjugated witness keeps `M_σ ⊓ C_G(⟨t x t⁻¹⟩) ≠ ⊥`, so Theorem B pins
`ℳ(C_G(t x t⁻¹)) = {T}`, and conjugating back by `t ∈ T` (which fixes `T`) gives both
conjuncts for `x`. -/
theorem typeI_centralizer_le_and_unique [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {T : Subgroup G} (hT : T ∈ maximalSubgroups G) (dT : TypeIData T)
    {x : G} (hxT : x ∈ T) (hx1 : x ≠ 1)
    (hord : Nat.Coprime (orderOf x) (Nat.card (maxNilpotentNormalHall T)))
    (hwit : ∃ h ∈ maxNilpotentNormalHall T, h ≠ 1 ∧ Commute x h) :
    Subgroup.centralizer ({x} : Set G) ≤ T ∧
      ∀ L ∈ maximalSubgroups G, Subgroup.centralizer ({x} : Set G) ≤ L → L = T := by
  classical
  haveI : IsSolvable ↥T := hG.solvable_of_mem_maximalSubgroups hT
  have hκ : OddOrder.BG.Ch4.S14.kappa T = ∅ :=
    (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hT).mp ⟨dT⟩
  have hMFMσ : maxNilpotentNormalHall T = OddOrder.BG.Ch3.S10.Msigma T :=
    OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hT (Or.inl ⟨dT⟩)
  -- (i) `x` is a `(κ ∪ σ)′`-element of `T`.
  set xT : ↥T := ⟨x, hxT⟩ with hxTdef
  have hordeq : orderOf x = orderOf xT :=
    orderOf_injective T.subtype T.subtype_injective xT
  have hZπ : ∀ q ∈ (Nat.card ↥(Subgroup.zpowers xT)).primeFactors,
      q ∈ (OddOrder.BG.Ch4.S14.kappa T ∪ OddOrder.BG.Ch3.S10.sigma T)ᶜ := by
    intro q hq
    rw [Nat.card_zpowers, ← hordeq] at hq
    obtain ⟨hqp, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
    simp only [Set.mem_compl_iff, Set.mem_union, hκ, Set.mem_empty_iff_false, false_or]
    intro hqσ
    -- `q ∈ σ(T)` divides `|M_σ| = |T_F|`, contradicting the coprimality with `orderOf x`.
    have hHall := OddOrder.BG.Ch3.S10.Msigma_isHall hG hT
    have hqnidx : ¬ q ∣ (OddOrder.BG.Ch3.S10.Msigma T).index := fun hdvd =>
      hHall.2 q (Nat.mem_primeFactors.mpr ⟨hqp, hdvd, Subgroup.index_ne_zero_of_finite⟩) hqσ
    have hqG : q ∣ Nat.card G := hqdvd.trans ((orderOf_dvd_natCard x).trans dvd_rfl)
    have hqMσ : q ∣ Nat.card (OddOrder.BG.Ch3.S10.Msigma T) := by
      rcases (Nat.Prime.dvd_mul hqp).mp
        ((Subgroup.card_mul_index (OddOrder.BG.Ch3.S10.Msigma T)) ▸ hqG) with h | h
      · exact h
      · exact absurd h hqnidx
    have hgcd : q ∣ Nat.gcd (orderOf x) (Nat.card (maxNilpotentNormalHall T)) :=
      Nat.dvd_gcd hqdvd (hMFMσ ▸ hqMσ)
    rw [Nat.Coprime.gcd_eq_one hord] at hgcd
    exact hqp.one_lt.ne' (Nat.dvd_one.mp hgcd)
  -- (ii) Hall D + C inside `T`: conjugate `x` into the type-`F` complement `U`.
  obtain ⟨W, hWhall, hZW⟩ := OddOrder.Isaacs.Ch03.hall_D (G := ↥T) hZπ
  obtain ⟨t, htmap⟩ := OddOrder.Isaacs.Ch03.hall_C (G := ↥T) hWhall
    (typeF_complement_isHall_kappa_sigma_compl hG hT dT)
  set τ : G := (t : G) with hτdef
  have hτT : τ ∈ T := t.2
  set x' : G := τ * x * τ⁻¹ with hx'def
  have hx'U : x' ∈ dT.typeF.U := by
    have hxW : xT ∈ W := hZW (Subgroup.mem_zpowers xT)
    have hmem : (MulAut.conj t) xT ∈ W.map (MulAut.conj t).toMonoidHom :=
      ⟨xT, hxW, rfl⟩
    rw [htmap] at hmem
    have := Subgroup.mem_subgroupOf.mp hmem
    simpa [hx'def, hτdef, MulAut.conj_apply] using this
  have hx'1 : x' ≠ 1 := by
    simp only [hx'def, ne_eq, conj_eq_one_iff]
    exact hx1
  -- (iii) the conjugated witness keeps `M_σ ⊓ C_G(⟨x'⟩) ≠ ⊥`.
  obtain ⟨h, hhMF, hh1, hcomm⟩ := hwit
  have hMFle := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le T
  have hh'MF : τ * h * τ⁻¹ ∈ maxNilpotentNormalHall T := by
    haveI hnorm := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal T
    have hmem : (⟨h, hMFle hhMF⟩ : ↥T) ∈ (maxNilpotentNormalHall T).subgroupOf T :=
      Subgroup.mem_subgroupOf.mpr hhMF
    have := Subgroup.mem_subgroupOf.mp (hnorm.conj_mem _ hmem t)
    simpa [hτdef] using this
  have hh'1 : τ * h * τ⁻¹ ≠ 1 := by
    simp only [ne_eq, conj_eq_one_iff]
    exact hh1
  have hcomm' : Commute x' (τ * h * τ⁻¹) := by
    have := hcomm.map (MulAut.conj τ : G →* G)
    simpa [hx'def, MulAut.conj_apply] using this
  have hCne : OddOrder.BG.Ch3.S10.Msigma T ⊓
      Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G) ≠ ⊥ := by
    intro hbot
    have hmem : τ * h * τ⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma T ⊓
        Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hMFMσ ▸ hh'MF, ?_⟩
      rw [centralizer_zpowers_eq_singleton']
      exact Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hcomm'.eq
    rw [hbot] at hmem
    exact hh'1 (Subgroup.mem_bot.mp hmem)
  -- (iv) BG Lemma 15.1(c) / Theorem B(4) pins `ℳ(C_G(x')) = {T}` (sorry-free, no Theorem B gate).
  have hB := (OddOrder.BG.Ch4.S14.typeP_hall_small_subgroup_cyclic_tau2 hG hT dT.typeF.U_le
    (typeF_complement_isHall_kappa_sigma_compl hG hT dT)
    (Subgroup.zpowers_le.mpr hx'U)
    (by simpa [Subgroup.zpowers_eq_bot] using hx'1) hCne).1
  rw [centralizer_zpowers_eq_singleton'] at hB
  -- (v) conjugate back by `τ ∈ T`.
  have hCconj : Subgroup.centralizer ({x'} : Set G)
      = MulAut.conj τ • Subgroup.centralizer ({x} : Set G) :=
    (conj_smul_centralizer_singleton' τ x).symm
  have hconj_self : ∀ g ∈ T, MulAut.conj g • T = T := by
    intro g hg
    ext z
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : (MulAut.conj g)⁻¹ • z = g⁻¹ * z * g := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
    rw [hinv]
    constructor
    · intro hz
      have := mul_mem (mul_mem hg hz) (inv_mem hg)
      simpa [mul_assoc] using this
    · intro hz
      exact mul_mem (mul_mem (inv_mem hg) hz) hg
  have hTmem : T ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) := by
    rw [hB]
    rfl
  have hCT' : Subgroup.centralizer ({x'} : Set G) ≤ T :=
    (mem_maximalSubgroupsContaining.mp hTmem).2
  constructor
  · -- `C_G(x) ≤ T`
    intro c hc
    have hc' : τ * c * τ⁻¹ ∈ Subgroup.centralizer ({x'} : Set G) := by
      rw [hCconj]
      exact ⟨c, hc, rfl⟩
    have hcT : τ * c * τ⁻¹ ∈ T := hCT' hc'
    have := mul_mem (mul_mem (inv_mem hτT) hcT) hτT
    simpa [mul_assoc] using this
  · -- uniqueness
    intro L hL hCL
    have hLconj : MulAut.conj τ • L ∈
        maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) := by
      rw [mem_maximalSubgroupsContaining]
      refine ⟨OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hL), ?_⟩
      rw [hCconj]
      exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hCL
    rw [hB, Set.mem_singleton_iff] at hLconj
    calc L = MulAut.conj τ⁻¹ • (MulAut.conj τ • L) := by
            rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      _ = MulAut.conj τ⁻¹ • T := by rw [hLconj]
      _ = T := hconj_self τ⁻¹ (inv_mem hτT)



theorem supported_sigma_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {S T : Subgroup G} (hS : S ∈ maximalSubgroups G) (_hT : T ∈ maximalSubgroups G)
    (dS : TypeIData S) (_dT : TypeIData T)
    (hsupp : ∃ z ∈ OddOrder.GroupTheory.escapingCentralizerSet S (typeIA S dS),
      ∃ N ∈ maximalSubgroups G, Subgroup.centralizer ({z} : Set G) ≤ N ∧
        OddOrder.BG.Ch4.S14.IsConjugateSubgroup T N) :
    ∀ w ∈ typeIA S dS,
      Nat.Coprime (Nat.card (OddOrder.BG.Ch3.S10.Msigma T))
        (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn S w)) := by
  classical
  intro w hw
  by_contra hnc
  obtain ⟨p, hpp, hpT, hpC⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  obtain ⟨z, hz, N, hNmax, hCN, hTN⟩ := hsupp
  obtain ⟨hzA, hzesc⟩ := hz
  have hz1 : z ≠ 1 := hzA.2.1
  -- identify `N` with `N[z] = FT_signalizerBase z` via the singleton uniqueness.
  have hκ : OddOrder.BG.Ch4.S14.kappa S = ∅ :=
    (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hS).mp ⟨dS⟩
  have hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa S)
      ((⊥ : Subgroup G).subgroupOf S) := by
    rw [Subgroup.bot_subgroupOf, OddOrder.Isaacs.Ch03.IsHallSubgroup.bot_iff]
    intro q _
    rw [hκ]
    exact Set.notMem_empty q
  have hσz : z ∈ OddOrder.BG.Ch4.S14.sigmaSharp S :=
    OddOrder.BG.Ch4.S16.mem_sigmaSharp_of_mem_aSet_of_escape hG hS bot_le dS.typeF.U_le hK
      (typeF_complement_isHall_kappa_sigma_compl hG hS dS) (Or.inl rfl)
      (typeIA_subset_ASet hG hS dS hzA) hz1 hzesc
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement z).ncard := by
    by_contra h
    exact hzesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hS hσz.1 hz1
      (not_lt.mp h))
  obtain ⟨N₀, hN₀⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG hS hσz hzesc
  have huniq : ∀ L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({z} : Set G)),
      L = N₀ := by
    intro L hL
    rw [hN₀, Set.mem_singleton_iff] at hL
    exact hL
  have hbr : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement z).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({z} : Set G))).Nonempty :=
    ⟨hgt, ⟨N₀, by rw [hN₀]; rfl⟩⟩
  have hbase : OddOrder.BG.Ch4.S16.FT_signalizerBase z = N₀ := by
    have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase z = hbr.2.choose := dif_pos hbr
    rw [hb]
    exact huniq _ hbr.2.choose_spec
  have hNN₀ : N = N₀ :=
    huniq N (mem_maximalSubgroupsContaining.mpr ⟨hNmax, hCN⟩)
  -- `p ∈ σ(T) = σ(N) = σ(N[z])`.
  have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase z) := by
    obtain ⟨g, hg⟩ := hTN
    rw [hbase, ← hNN₀, ← hg, OddOrder.BG.Ch4.S14.sigma_conj_smul_eq]
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup T p
      (Nat.mem_primeFactors.mpr ⟨hpp, hpT, Nat.card_pos.ne'⟩)
  exact escaping_sigma_disjoint_centralizer hG hS dS ⟨hzA, hzesc⟩ hw hpp hpσ hpC

/-- **`π`-part extraction from a commuting coprime product**: if `b, k` commute with coprime
orders then `b ∈ ⟨b·k⟩` (`b` is the `primeFactors (orderOf b)`-part of `b·k`). -/
theorem mem_zpowers_mul_right_of_coprime [Finite G] {b k : G} (hcomm : Commute b k)
    (hcop : Nat.Coprime (orderOf b) (orderOf k)) :
    b ∈ Subgroup.zpowers (b * k) := by
  classical
  set π : Set ℕ := {p | p ∈ (orderOf b).primeFactors} with hπ
  have hbπ : OddOrder.GroupTheory.IsPiElement π b := fun p hp => hp
  have hkπ' : OddOrder.GroupTheory.IsPiElement πᶜ k := by
    intro p hp hpb
    have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpk : p ∣ orderOf k := (Nat.mem_primeFactors.mp hp).2.1
    have hpb' : p ∣ orderOf b := (Nat.mem_primeFactors.mp hpb).2.1
    have : p ∣ 1 := hcop ▸ Nat.dvd_gcd hpb' hpk
    exact hpprime.one_lt.ne' (Nat.dvd_one.mp this)
  have hmul : OddOrder.BG.Ch4.S14.piPart π (b * k) = b := by
    rw [OddOrder.BG.Ch4.S14.piPart_mul_of_commute hcomm,
      OddOrder.BG.Ch4.S14.piPart_self_of_isPiElement hbπ,
      OddOrder.BG.Ch4.S14.piPart_eq_one_of_isPiElement_compl hkπ', mul_one]
  have hz := OddOrder.BG.Ch4.S14.piPart_mem_zpowers π (b * k)
  rwa [hmul] at hz

/-- **(8.18.a), conjugation-free core**: if `x ∈ A₁(S)` and some conjugate `g·x·g⁻¹ ∈ A(T)` for
non-conjugate type-I `S, T`, then `x` is an escaping point of `A(S)` and its centralizer lies in
the `T`-conjugate `g⁻¹·T·g`.  Genuine except the (8.12.b) pin: the `σ`-order bookkeeping is
`sigma_disjoint_of_nonconjugate` + `primeFactors_Msigma_eq_sigma`. -/
theorem escaping_supported_of_A1_conj_mem_typeIA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S T : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hT : T ∈ maximalSubgroups G)
    (dS : TypeIData S) (dT : TypeIData T)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup S T)
    {x g : G} (hxA1 : x ∈ A1 S PeterfalviType.I) (hgx : g * x * g⁻¹ ∈ typeIA T dT) :
    x ∈ OddOrder.GroupTheory.escapingCentralizerSet S (typeIA S dS) ∧
      Subgroup.centralizer ({x} : Set G) ≤ MulAut.conj g⁻¹ • T := by
  obtain ⟨hxMF, hx1s⟩ := (Set.mem_diff x).mp hxA1
  have hx1 : x ≠ 1 := fun h => hx1s (Set.mem_singleton_iff.mpr h)
  set y := g * x * g⁻¹ with hydef
  have hy1 : y ≠ 1 := conj_ne_one hx1
  -- `orderOf y = orderOf x` is a `σ(S)`-number; `|T_F| = |T_σ|` is a `σ(T)`-number; disjoint.
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma S := by
    have : x ∈ maxNilpotentNormalHall S := SetLike.mem_coe.mp hxMF
    rwa [OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG hS
      (Or.inl ⟨dS⟩)] at this
  have hxpi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma S) x :=
    OddOrder.BG.Ch4.S14.isPiElement_sigma_of_mem_Msigma hxMσ
  have horder_eq : orderOf y = orderOf x := by
    have : Function.Injective (MulAut.conj g) := (MulAut.conj g).injective
    simpa [hydef] using orderOf_injective (MulAut.conj g).toMonoidHom this x
  have hσdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma S) (OddOrder.BG.Ch3.S10.sigma T) :=
    OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hS hT hnc
  have hord : Nat.Coprime (orderOf y) (Nat.card (maxNilpotentNormalHall T)) := by
    rw [OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG hT
      (Or.inl ⟨dT⟩)]
    rw [← Nat.disjoint_primeFactors (orderOf_pos y).ne'
      Nat.card_pos.ne']
    rw [Finset.disjoint_left]
    intro p hpy hpT
    have hpσS : p ∈ OddOrder.BG.Ch3.S10.sigma S := hxpi p (horder_eq ▸ hpy)
    have hpσT : p ∈ OddOrder.BG.Ch3.S10.sigma T := by
      have := OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hT
      rw [← this]
      exact hpT
    exact Set.disjoint_left.mp hσdisj hpσS hpσT
  -- the (8.12.b) pin at `y`
  obtain ⟨hyT, -, h, hh, hyh⟩ := hgx
  have hwit : ∃ h' ∈ maxNilpotentNormalHall T, h' ≠ 1 ∧ Commute y h' := by
    obtain ⟨hhH, hh1⟩ := (Set.mem_diff h).mp hh
    refine ⟨h, ?_, fun he => hh1 (Set.mem_singleton_iff.mpr he), ?_⟩
    · rw [← dT.typeF.H_eq]; exact SetLike.mem_coe.mp hhH
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hyh)
  obtain ⟨hCyT, huniq⟩ := typeI_centralizer_le_and_unique hG hT dT hyT hy1 hord hwit
  constructor
  · refine ⟨A1_subset_typeIA S dS hxA1, fun hle => ?_⟩
    -- if `C(x) ≤ S` then `C(y) ≤ g·S·g⁻¹`, a maximal over `C(y)`, so `g·S·g⁻¹ = T` — conjugate.
    have hCyS : Subgroup.centralizer ({y} : Set G) ≤ MulAut.conj g • S := by
      intro c hc
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer ({x} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
        calc g⁻¹ * c * g * x = g⁻¹ * (c * y) * g := by rw [hydef]; group
          _ = g⁻¹ * (y * c) * g := by rw [hc]
          _ = x * (g⁻¹ * c * g) := by rw [hydef]; group
      simpa [MulAut.smul_def] using hle hc'
    have hmax : MulAut.conj g • S ∈ maximalSubgroups G :=
      mem_maximalSubgroups.mpr
        (OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hS))
    exact hnc ⟨g, huniq _ hmax hCyS⟩
  · intro c hc
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hc' : g * c * g⁻¹ ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      calc g * c * g⁻¹ * y = g * (c * x) * g⁻¹ := by rw [hydef]; group
        _ = g * (x * c) * g⁻¹ := by rw [hc]
        _ = y * (g * c * g⁻¹) := by rw [hydef]; group
    have := hCyT hc'
    simpa [MulAut.smul_def] using this

/-- **(8.18.b) for a type-I pair**: a nonempty intersection of the thickened supports
`Ã₁(S) ∩ Ã(T) ≠ ∅` descends to a *bare* intersection: some `x ∈ A₁(S)` has a conjugate in
`A(T)`.  Genuine: an escaping `A(T)`-point would put the intersection inside
`Ã₁(S) ∩ Ã₁(T) = ∅` (the proven (8.17.c)); for a non-escaping point the thickening on the
`T`-side is trivial and the `S`-side coset collapses through the `π`-part power argument
(`mem_zpowers_mul_right_of_coprime`, orders coprime by the (8.13.c2) pin). -/
theorem exists_A1_conj_mem_typeIA_of_not_disjoint [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S T : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hT : T ∈ maximalSubgroups G)
    (dS : TypeIData S) (dT : TypeIData T)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup S T)
    (hint : ¬ Disjoint (ftThickenedSupport S (A1 S PeterfalviType.I))
      (ftThickenedSupport T (typeIA T dT))) :
    ∃ x u : G, x ∈ A1 S PeterfalviType.I ∧ u * x * u⁻¹ ∈ typeIA T dT := by
  rw [Set.not_disjoint_iff] at hint
  obtain ⟨y, ⟨b, hbA1, hyb⟩, ⟨a, haA, hya⟩⟩ := hint
  by_cases haesc : a ∈ OddOrder.GroupTheory.escapingCentralizerSet T (typeIA T dT)
  · -- escaping `a`: `y ∈ Ã₁(S) ∩ Ã₁(T)`, contradicting the proven (8.17.c).
    exfalso
    have haA1 : a ∈ A1 T PeterfalviType.I := escaping_typeIA_mem_A1 hG hT dT haesc
    have hyT1 : y ∈ ftThickenedSupport T (A1 T PeterfalviType.I) := by
      refine ⟨a, haA1, ?_⟩
      rwa [ftSupportKernel_eq_of_escaping haesc,
        ← ftSupportKernel_eq_of_escaping (⟨haA1, haesc.2⟩ :
          a ∈ OddOrder.GroupTheory.escapingCentralizerSet T (A1 T PeterfalviType.I))] at hya
    exact Set.disjoint_left.mp
      (ftThickenedSupport_A1_disjoint_of_nonconjugate hG hS hT (Or.inl ⟨dS⟩) (Or.inl ⟨dT⟩)
        (Or.inl rfl) (Or.inl rfl) hnc)
      ⟨b, hbA1, hyb⟩ hyT1
  · -- non-escaping `a`: the `T`-side thickening is trivial, `y ~ a`.
    rw [ftSupportKernel_eq_bot_of_not_escaping haesc] at hya
    obtain ⟨t, ⟨r0, hr0, rfl⟩, w, hw⟩ := hya
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hr0
    subst hr0
    simp only [mul_one] at hw
    -- `S`-side: `y = v·(b·k)·v⁻¹`.
    obtain ⟨t', ⟨k, hk, rfl⟩, v, hv⟩ := hyb
    have hb1 : b ≠ 1 := fun h =>
      ((Set.mem_diff b).mp hbA1).2 (Set.mem_singleton_iff.mpr h)
    obtain ⟨haT, ha1, hwitA⟩ := haA
    by_cases hbesc : b ∈ OddOrder.GroupTheory.escapingCentralizerSet S (A1 S PeterfalviType.I)
    · -- thick `S`-side: extract `b` as a power of `b·k`.
      rw [SetLike.mem_coe, ftSupportKernel_eq_of_escaping hbesc] at hk
      have hbescA : b ∈ OddOrder.GroupTheory.escapingCentralizerSet S (typeIA S dS) :=
        ⟨A1_subset_typeIA S dS hbesc.1, hbesc.2⟩
      have hcards := (escaping_typeIA_signalizer_structure hG hS dS hbescA).2.2.2 b
        (A1_subset_typeIA S dS hbesc.1)
      have hob : orderOf b ∣ Nat.card (OddOrder.Peterfalvi.S04.centralizerIn S b) :=
        Subgroup.orderOf_dvd_natCard _
          (OddOrder.Peterfalvi.S04.mem_centralizerIn.mpr
            ⟨(A1_subset_typeIA S dS hbA1).1, rfl⟩)
      have hok : orderOf k ∣ Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer b) :=
        Subgroup.orderOf_dvd_natCard _ hk
      have hcop : Nat.Coprime (orderOf b) (orderOf k) :=
        ((Nat.Coprime.coprime_dvd_left hok hcards).coprime_dvd_right hob).symm
      have hcomm : Commute b k := by
        have := OddOrder.BG.Ch4.S16.FT_signalizer_le_centralizer b hk
        exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
        (mem_zpowers_mul_right_of_coprime hcomm hcop)
      -- `a = u·(b·k)·u⁻¹` with `u := w⁻¹·v`; then `a^n = u·b·u⁻¹ ∈ A(T)`.
      set u := w⁻¹ * v with hudef
      have hau : a = u * (b * k) * u⁻¹ := by
        have : w * a * w⁻¹ = v * (b * k) * v⁻¹ := by rw [hw, hv]
        calc a = w⁻¹ * (w * a * w⁻¹) * w := by group
          _ = w⁻¹ * (v * (b * k) * v⁻¹) * w := by rw [this]
          _ = u * (b * k) * u⁻¹ := by rw [hudef]; group
      have hazn : a ^ n = u * b * u⁻¹ := by
        rw [hau]
        calc (u * (b * k) * u⁻¹) ^ n = u * (b * k) ^ n * u⁻¹ := by
              rw [← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply]
          _ = u * b * u⁻¹ := by rw [hn]
      refine ⟨b, u, hbA1, ?_⟩
      rw [← hazn]
      obtain ⟨h, hh, hah⟩ := hwitA
      refine ⟨Subgroup.zpow_mem T haT n, ?_, h, hh, ?_⟩
      · rw [hazn]
        exact conj_ne_one hb1
      · exact Subgroup.zpow_mem _ hah n
    · -- trivial `S`-side: `k = 1`, `a = u·b·u⁻¹` directly.
      rw [SetLike.mem_coe, ftSupportKernel_eq_bot_of_not_escaping hbesc,
        Subgroup.mem_bot] at hk
      subst hk
      simp only [mul_one] at hv
      refine ⟨b, w⁻¹ * v, hbA1, ?_⟩
      have : w⁻¹ * v * b * (w⁻¹ * v)⁻¹ = a := by
        have h1 : w * a * w⁻¹ = v * b * v⁻¹ := by rw [hw, hv]
        calc w⁻¹ * v * b * (w⁻¹ * v)⁻¹ = w⁻¹ * (v * b * v⁻¹) * w := by group
          _ = w⁻¹ * (w * a * w⁻¹) * w := by rw [h1]
          _ = a := by group
      rw [show w⁻¹ * v * b * (w⁻¹ * v)⁻¹ = a from this]
      exact ⟨haT, ha1, hwitA⟩

/-- **Peterfalvi (8.18.c) for a type-I pair** (mixed `Ã₁ ∩ Ã` disjointness): for non-conjugate
type-I maximal subgroups `S, T`, `Ã₁(S) ∩ Ã(T) = ∅` or `Ã₁(T) ∩ Ã(S) = ∅`.

Proof (genuine, modulo the three §16 pins): if both intersections were nonempty, (8.18.b) at
`(S,T)` produces a bare supporting configuration whose (8.18.a) escape feeds the (8.13.c2)
cross-coprimality `|T_σ| ⊥ |C_S(w)|`; (8.18.b) at `(T,S)` produces `x' ∈ A₁(T)` with a conjugate
`w ∈ A(S)`, and `orderOf x'` divides both coprime cardinalities — forcing `x' = 1`, absurd. -/
theorem ftThickenedSupport_mixed_disjoint_of_nonconjugate [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S T : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hT : T ∈ maximalSubgroups G)
    (dS : TypeIData S) (dT : TypeIData T)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup S T) :
    Disjoint (ftThickenedSupport S (A1 S PeterfalviType.I))
        (ftThickenedSupport T (typeIA T dT)) ∨
      Disjoint (ftThickenedSupport T (A1 T PeterfalviType.I))
        (ftThickenedSupport S (typeIA S dS)) := by
  by_contra hcon
  obtain ⟨hST, hTS⟩ := not_or.mp hcon
  -- (8.18.b) + (8.18.a) at `(S,T)`: a supporting configuration for the coprimality pin.
  obtain ⟨x, g, hxA1S, hgx⟩ :=
    exists_A1_conj_mem_typeIA_of_not_disjoint hG hS hT dS dT hnc hST
  obtain ⟨hxesc, hxle⟩ :=
    escaping_supported_of_A1_conj_mem_typeIA hG hS hT dS dT hnc hxA1S hgx
  have hcop := supported_sigma_coprime hG hS hT dS dT
    ⟨x, hxesc, MulAut.conj g⁻¹ • T,
      mem_maximalSubgroups.mpr
        (OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hT)),
      hxle, ⟨g⁻¹, rfl⟩⟩
  -- (8.18.b) at `(T,S)`: an `A₁(T)`-point with a conjugate in `A(S)`.
  have hncTS : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup T S := fun h => hnc h.symm
  obtain ⟨x', u, hx'A1T, hux'⟩ :=
    exists_A1_conj_mem_typeIA_of_not_disjoint hG hT hS dT dS hncTS hTS
  -- `orderOf x'` divides the coprime pair `|T_σ|`, `|C_S(u·x'·u⁻¹)|`.
  set w := u * x' * u⁻¹ with hwdef
  have hx'1 : x' ≠ 1 := fun h =>
    ((Set.mem_diff x').mp hx'A1T).2 (Set.mem_singleton_iff.mpr h)
  have h1 : orderOf x' ∣ Nat.card (OddOrder.BG.Ch3.S10.Msigma T) := by
    have hx'Mσ : x' ∈ OddOrder.BG.Ch3.S10.Msigma T := by
      have : x' ∈ maxNilpotentNormalHall T :=
        SetLike.mem_coe.mp ((Set.mem_diff x').mp hx'A1T).1
      rwa [OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG hT
        (Or.inl ⟨dT⟩)] at this
    exact Subgroup.orderOf_dvd_natCard _ hx'Mσ
  have h2 : orderOf x' ∣ Nat.card (OddOrder.Peterfalvi.S04.centralizerIn S w) := by
    have hworder : orderOf w = orderOf x' := by
      have : Function.Injective (MulAut.conj u) := (MulAut.conj u).injective
      simpa [hwdef] using orderOf_injective (MulAut.conj u).toMonoidHom this x'
    have := Subgroup.orderOf_dvd_natCard (OddOrder.Peterfalvi.S04.centralizerIn S w)
      (OddOrder.Peterfalvi.S04.mem_centralizerIn.mpr ⟨hux'.1, rfl⟩)
    rwa [hworder] at this
  have : orderOf x' ∣ 1 := (hcop w hux') ▸ Nat.dvd_gcd h1 h2
  exact hx'1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp this))

/-- **Peterfalvi (8.17)**: BG Theorem E data for a set of conjugacy-class
representatives of maximal subgroups.

The field `ι` indexes the representatives `M_i`.  The prime-factor fields record
the statement that `π(G)` is the disjoint union of the `π((M_i)_s)`, while
`cover_card` records the faithful BG cover cardinality
`|𝒞_G(M̃_i)| = (|(M_i)_s| - 1) |G : M_i|`. -/
structure BGTheoremECoverData (G : Type*) [Group G] where
  /-- Indexing type for the representative maximal subgroups. -/
  ι : Type*
  /-- The representative maximal subgroup `M_i`. -/
  reps : ι → Subgroup G
  /-- The Peterfalvi type attached to `M_i`. -/
  tau : ι → PeterfalviType
  /-- The faithful BG cover set `𝒞_G(M̃_i)` attached to `M_i`: the conjugacy-saturation of the
  `σ`-decomposition support `M̃_i = ⋃_{x ∈ (M_i)_σ#} x R(x)` of BG Lemma 14.5.  Abstracted as a
  bare `Set G` so the structure need not carry the `SigmaDecompositionData`/`Finite` data of `M̃`.
  (This replaces the unfaithful `thickenedA1 (M_i) (M_i)`, whose `(M_i)_F`-based kernel disagrees
  with the per-`x` signalizer `(N[x])_F` of Peterfalvi (8.14); see issue 8021.) -/
  cover : ι → Set G
  /-- The representatives form a finite family. -/
  finite_index : Fintype ι
  /-- Every representative is maximal. -/
  maximal : ∀ i : ι, reps i ∈ maximalSubgroups G
  /-- Every representative has its indicated Peterfalvi type. -/
  typed : ∀ i : ι, HasPeterfalviType (tau i) (reps i)
  /-- Every maximal subgroup is conjugate to one of the representatives. -/
  representatives :
    ∀ M : Subgroup G, M ∈ maximalSubgroups G →
      ∃ i : ι, ∃ g : G, MulAut.conj g • M = reps i
  /-- The representatives have no repeated conjugacy classes. -/
  nonconjugate :
    ∀ i j : ι, (∃ g : G, MulAut.conj g • reps i = reps j) → i = j
  /-- `π(G)` is covered by the `π((M_i)_s)`. -/
  primeFactors_cover :
    ∀ p : ℕ, p.Prime →
      (p ∈ (Nat.card G).primeFactors ↔
        ∃ i : ι, p ∈ (Nat.card ↥(mainSubgroup (reps i) (tau i))).primeFactors)
  /-- The `π((M_i)_s)` are pairwise disjoint. -/
  primeFactors_disjoint :
    ∀ i j : ι, i ≠ j →
      Disjoint
        ((Nat.card ↥(mainSubgroup (reps i) (tau i))).primeFactors : Finset ℕ)
        ((Nat.card ↥(mainSubgroup (reps j) (tau j))).primeFactors : Finset ℕ)
  /-- **BG Lemma 14.5(c)**: the cardinality formula for the faithful cover `𝒞_G(M̃_i)`:
  `|𝒞_G(M̃_i)| = (|(M_i)_s| - 1) |G : M_i|`. -/
  cover_card :
    ∀ i : ι,
      Nat.card ↥(cover i) =
        (Nat.card ↥(mainSubgroup (reps i) (tau i)) - 1) * (reps i).index

/-- **Peterfalvi (8.17), case (8.8.a)**: when all maximal subgroups are type I,
`G#` is the disjoint union of the thickened `A_1(M_i)` sets. -/
structure BGTheoremETypeICovering (data : BGTheoremECoverData G) : Prop where
  /-- The cover sets `𝒞_G(M̃_i)` cover all nonidentity elements of `G`. -/
  cover_nonidentity :
    sharpSubgroup (⊤ : Subgroup G) =
      ⋃ i : data.ι, data.cover i
  /-- The cover by the `𝒞_G(M̃_i)` is disjoint. -/
  pairwise_disjoint_thickened :
    (Set.univ : Set data.ι).PairwiseDisjoint fun i => data.cover i
  /-- **All-type-I refinement**: each cover set lands in the conjugates of the kernel sharp-set
  `((M_i)_F)#`.  In the all-type-I case the signalizer `R(x)` is trivial, so
  `M̃_i = (M_i)_σ# = (M_i)_F#` and the cover collapses onto the Frobenius kernels (BG Cor 14.9 /
  the (8.8.a) dichotomy). -/
  cover_subset_kernels :
    ∀ i : data.ι,
      data.cover i ⊆ conjClassSet ((maxNilpotentNormalHall (data.reps i) : Set G) \ {1})

/-- **Peterfalvi (8.17), case (8.8.b)**: in the two-exceptional-subgroup case,
`G#` is covered by the thickened `A_1(M_i)` sets together with the conjugates of
the exceptional `W#`. -/
structure BGTheoremENonTypeICovering (data : BGTheoremECoverData G) where
  /-- The exceptional TI-set `Ẑ` (BG `zTilde K K* = (K ⊔ K*) \ (K ∪ K*)`) whose nonidentity
  conjugates supplement the cover.  Modelled as a bare `Set G`, **not** `W#` for a subgroup `W`:
  `Ẑ` removes all of `K ∪ K*` (not just `1`), so no `sharpSubgroup W = W \ {1}` equals it.  The
  earlier `W : Subgroup` form is unsatisfiable — the minimal subgroup containing `Ẑ` is `K ⊔ K*`,
  whose `K*# ⊆ M_σ# ⊆ M̃` would overlap the cover, breaking `exceptional_disjoint_thickened`
  (issue 8020).  Satisfied by `exceptionalSet = zTilde K K*` via the fixed-`W` cover
  (`BG.Ch4.S14.exists_mem_conjClassSet_Mtilde_or_fixed_zTilde`). -/
  exceptionalSet : Set G
  /-- The cover sets `𝒞_G(M̃_i)` and the conjugates of `Ẑ` cover `G#`. -/
  cover_nonidentity :
    sharpSubgroup (⊤ : Subgroup G) =
      (⋃ i : data.ι, data.cover i) ∪
        conjClassSet exceptionalSet
  /-- The `𝒞_G(M̃_i)` part of the cover is disjoint. -/
  pairwise_disjoint_thickened :
    (Set.univ : Set data.ι).PairwiseDisjoint fun i => data.cover i
  /-- The exceptional part is disjoint from every `𝒞_G(M̃_i)`. -/
  exceptional_disjoint_thickened :
    ∀ i : data.ι,
      Disjoint (conjClassSet exceptionalSet) (data.cover i)

/-- **NonTypeICovering producer** (the `𝓜_P ≠ ∅` side of the (8.8) dichotomy): when `data`'s cover
is the faithful `𝒞_G(M̃_i)` family and a reference type-`P` maximal `Mref` exists (Theorem 14.7 data
`Kref, K*ref, Uref`), `data` admits a `BGTheoremENonTypeICovering` with exceptional set
`Ẑ = zTilde Kref K*ref`.

- `cover_nonidentity`: the fixed-`W` cover (`exists_mem_conjClassSet_Mtilde_or_fixed_zTilde`) puts
  every `x ≠ 1` in some `𝒞_G(M̃_M)` — moved to a representative via `data.representatives` +
  `Mtilde_conj_smul` + `conjClassSet_conj_smul` — or in the fixed `𝒞_G(Ẑ)`; the reverse uses that
  conjugacy-saturations of `1`-free sets avoid `1`.
- `pairwise_disjoint_thickened`: `conjClassSet_Mtilde_disjoint` on nonconjugate reps.
- `exceptional_disjoint_thickened`: `conjClassSet_T_Mtilde_disjoint`, with `Ẑ` rewritten to the
  family `T`-set form via `family_inf_msigma_union_eq`. -/
noncomputable def nonTypeICovering_of_isTypeP [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (data : BGTheoremECoverData G)
    (hcover : ∀ j : data.ι, data.cover j = conjClassSet
      (OddOrder.BG.Ch4.S14.Mtilde hG (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG)
        (data.reps j)))
    {Mref Kref Kstarref Uref : Subgroup G} (hMref : Mref ∈ maximalSubgroups G)
    (hMPref : OddOrder.BG.Ch4.S14.IsTypeP Mref) (hKMref : Kref ≤ Mref)
    (hKref : Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa Mref)
      (Kref.subgroupOf Mref))
    (hKstarref : Kstarref =
      OddOrder.BG.Ch3.S10.Msigma Mref ⊓ Subgroup.centralizer (Kref : Set G))
    (hUref : Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa Mref ∪ OddOrder.BG.Ch3.S10.sigma Mref)ᶜ)
      (Uref.subgroupOf Mref)) :
    BGTheoremENonTypeICovering data := by
  classical
  set D := OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG with hD
  -- conjugacy-saturation of a `1`-free set avoids `1`, hence lands in `(⊤)#`.
  have hsub : ∀ S : Set G, (1 : G) ∉ S → conjClassSet S ⊆ sharpSubgroup (⊤ : Subgroup G) := by
    rintro S hS y ⟨t, ht, g, rfl⟩
    rw [sharpSubgroup, Set.mem_diff, Set.mem_singleton_iff]
    refine ⟨Subgroup.mem_top _, fun h1 => hS ?_⟩
    have ht1 : t = 1 := mul_left_cancel ((mul_inv_eq_one.mp h1).trans (mul_one g).symm)
    exact ht1 ▸ ht
  refine ⟨OddOrder.BG.Ch4.S14.zTilde Kref Kstarref, ?_, ?_, ?_⟩
  · -- cover_nonidentity
    apply Set.Subset.antisymm
    · intro x hx
      have hx1 : x ≠ 1 := by
        rw [sharpSubgroup, Set.mem_diff, Set.mem_singleton_iff] at hx; exact hx.2
      rcases OddOrder.BG.Ch4.S14.exists_mem_conjClassSet_Mtilde_or_fixed_zTilde hG hMref hMPref
        hKMref hKref hKstarref hUref hx1 with ⟨M, hMmax, hxM⟩ | hxZ
      · obtain ⟨j, g, hgconj⟩ := data.representatives M hMmax
        refine Or.inl (Set.mem_iUnion.mpr ⟨j, ?_⟩)
        rw [hcover j, ← hgconj, ← OddOrder.BG.Ch4.S14.Mtilde_conj_smul hG D g M,
          OddOrder.BG.Ch4.S14.conjClassSet_conj_smul]
        exact hxM
      · exact Or.inr hxZ
    · rintro y (hy | hy)
      · obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
        rw [hcover j] at hyj
        exact hsub _ (OddOrder.BG.Ch4.S14.one_not_mem_Mtilde hG D (data.maximal j)) hyj
      · exact hsub _ (OddOrder.BG.Ch4.S14.one_not_mem_zTilde Kref Kstarref) hy
  · -- pairwise_disjoint_thickened
    intro j _ k _ hjk
    show Disjoint (data.cover j) (data.cover k)
    rw [hcover j, hcover k]
    exact OddOrder.BG.Ch4.S14.conjClassSet_Mtilde_disjoint hG D (data.maximal j) (data.maximal k)
      (fun hconj => hjk (data.nonconjugate j k hconj))
  · -- exceptional_disjoint_thickened
    intro j
    rw [hcover j]
    obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ :=
      OddOrder.BG.Ch4.S14.exists_partner hG D hMref hMPref hKMref hKref hKstarref hUref
    have hunion := OddOrder.BG.Ch4.S14.family_inf_msigma_union_eq hG hMref hMPref hKMref hKref
      hKstarref hUref hMstarmem hMstarne hpart
    have hzeq : OddOrder.BG.Ch4.S14.zTilde Kref Kstarref =
        ((Kref ⊔ Kstarref : Subgroup G) : Set G) \
        ⋃ N ∈ OddOrder.BG.Ch4.S14.ZFamilyFinset Mref Kref,
          (((Kref ⊔ Kstarref) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
      simp only [OddOrder.BG.Ch4.S14.zTilde]; rw [hunion]
    rw [hzeq]
    exact OddOrder.BG.Ch4.S14.conjClassSet_T_Mtilde_disjoint hG D hMref hMPref hKMref hKref
      hKstarref hUref (data.maximal j)

/-- **Peterfalvi (8.17)**: BG Theorem E, repackaged as the Section 10 covering
interface.

This statement deliberately does not prove BG Theorem E.  It records the exact
data Peterfalvi uses after (8.14): the `π(G)` partition by the `M_i_s`, the
cardinality of each thickened `A_1(M_i)`, and the appropriate `G#` cover in the
two cases from (8.8). -/
theorem bgTheoremE_cover_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ∃ data : BGTheoremECoverData G,
      BGTheoremETypeICovering data ∨ Nonempty (BGTheoremENonTypeICovering data) := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨reps, hrepsMax, hreps⟩ := OddOrder.BG.Ch4.S16.exists_maximal_conjugacy_reps (G := G)
  haveI : Fintype ↥reps := Fintype.ofFinite _
  -- Index the representatives by `Fin n`, then `ULift` to the (universe-polymorphic) struct index.
  let e := Fintype.equivFin (↥reps)
  -- Peterfalvi type label + classification proof for each representative (exhaustiveness).
  let tau : ↥reps → PeterfalviType := fun i =>
    (OddOrder.BG.Ch4.S16.exists_peterfalviType hG (hrepsMax i.1 i.2)).choose
  have htyped : ∀ i : ↥reps, HasPeterfalviType (tau i) i.1 := fun i =>
    (OddOrder.BG.Ch4.S16.exists_peterfalviType hG (hrepsMax i.1 i.2)).choose_spec
  -- Prime-factor bridge: `π(M_s) = σ(M)`, via `M_s = M_σ` (Pf 8.10, `mainSubgroup_eq_Msigma`)
  -- and `π(M_σ) = σ(M)` (`primeFactors_Msigma_eq_sigma`).
  have hbridge : ∀ (i : ↥reps) (t : PeterfalviType), HasPeterfalviType t i.1 → ∀ p : ℕ,
      p ∈ (Nat.card ↥(mainSubgroup i.1 t)).primeFactors ↔
        p ∈ OddOrder.BG.Ch3.S10.sigma i.1 := fun i t ht p => by
    have h : mainSubgroup i.1 t = OddOrder.BG.Ch3.S10.Msigma i.1 :=
      OddOrder.BG.Ch4.S16.mainSubgroup_eq_Msigma hG (hrepsMax i.1 i.2) ht
    rw [h]
    exact OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG (hrepsMax i.1 i.2) p
  -- Canonical `σ`-decomposition data (the faithful cover `𝒞_G(M̃)` is independent of the choice).
  let D := OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG
  refine ⟨{
    ι := ULift (Fin (Fintype.card (↥reps)))
    reps := fun j => (e.symm j.down).1
    tau := fun j => tau (e.symm j.down)
    cover := fun j => conjClassSet (OddOrder.BG.Ch4.S14.Mtilde hG D (e.symm j.down).1)
    finite_index := inferInstance
    maximal := fun j => hrepsMax _ (e.symm j.down).2
    typed := fun j => htyped (e.symm j.down)
    representatives := fun M hM => by
      obtain ⟨Mi, ⟨hMirep, hconj⟩, _⟩ := hreps M hM
      refine ⟨⟨e ⟨Mi, hMirep⟩⟩, ?_⟩
      simp only [ULift.down_up, Equiv.symm_apply_apply]
      exact hconj
    nonconjugate := fun j k hconj => by
      have hsub : e.symm j.down = e.symm k.down := by
        obtain ⟨_, _, huniq⟩ := hreps (e.symm j.down).1 (hrepsMax _ (e.symm j.down).2)
        exact Subtype.ext
          ((huniq _ ⟨(e.symm j.down).2, OddOrder.BG.Ch4.S14.IsConjugateSubgroup.refl _⟩).trans
            (huniq _ ⟨(e.symm k.down).2, hconj⟩).symm)
      exact ULift.ext _ _ (e.symm.injective hsub)
    primeFactors_cover := fun p _ => by
      rw [OddOrder.BG.Ch4.S16.sigma_reps_prime_cover hG hrepsMax hreps p]
      constructor
      · rintro ⟨Mi, hMirep, hpMi⟩
        refine ⟨⟨e ⟨Mi, hMirep⟩⟩, ?_⟩
        simp only [ULift.down_up, Equiv.symm_apply_apply]
        exact (hbridge ⟨Mi, hMirep⟩ _ (htyped ⟨Mi, hMirep⟩) p).mpr hpMi
      · rintro ⟨j, hpj⟩
        exact ⟨(e.symm j.down).1, (e.symm j.down).2,
          (hbridge (e.symm j.down) _ (htyped (e.symm j.down)) p).mp hpj⟩
    primeFactors_disjoint := fun j k hjk => by
      rw [Finset.disjoint_left]
      intro p hpj hpk
      have hne : (e.symm j.down).1 ≠ (e.symm k.down).1 := fun h =>
        hjk (ULift.ext _ _ (e.symm.injective (Subtype.ext h)))
      have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (e.symm j.down).1 ∩
          OddOrder.BG.Ch3.S10.sigma (e.symm k.down).1 :=
        ⟨(hbridge (e.symm j.down) _ (htyped (e.symm j.down)) p).mp hpj,
          (hbridge (e.symm k.down) _ (htyped (e.symm k.down)) p).mp hpk⟩
      rw [OddOrder.BG.Ch4.S16.sigma_reps_pairwise_disjoint hG hrepsMax hreps
        (e.symm j.down).2 (e.symm k.down).2 hne] at hpσ
      exact Set.notMem_empty p hpσ
    cover_card := fun j => by
      -- **BG Lemma 14.5(c)** for the faithful cover (issue 8021 resolution): the cover is
      -- `𝒞_G(M̃)` with `M̃ = ⋃_{x ∈ M_σ#} x R(x)` the per-`x` signalizer support, whose cardinality
      -- `sigmaConjugacySaturation_Mtilde_ncard` proves to be `(|M_σ| − 1)·[G:M]`.  The
      -- `mainSubgroup`-stated RHS is rewritten to `M_σ` by `mainSubgroup_eq_Msigma` (Pf 8.10).
      have hms : mainSubgroup (e.symm j.down).1 (tau (e.symm j.down))
          = OddOrder.BG.Ch3.S10.Msigma (e.symm j.down).1 :=
        OddOrder.BG.Ch4.S16.mainSubgroup_eq_Msigma hG (hrepsMax _ (e.symm j.down).2)
          (htyped (e.symm j.down))
      show Nat.card ↥(conjClassSet (OddOrder.BG.Ch4.S14.Mtilde hG D (e.symm j.down).1)) = _
      rw [Nat.card_coe_set_eq,
        OddOrder.BG.Ch4.S14.sigmaConjugacySaturation_Mtilde_ncard hG D
          (hrepsMax _ (e.symm j.down).2), hms]
  }, ?_⟩
  -- The (8.8) covering dichotomy (BG Cor 14.9) splits on whether a type-`P` maximal exists.
  by_cases hP : (OddOrder.BG.Ch4.S14.maximalTypePFamily G).Nonempty
  · -- `𝓜_P ≠ ∅`: the non-Type-I covering, exceptional `Ẑ` of a reference type-`P` maximal (fix-`W`).
    obtain ⟨Mref, hMrefmax, hMrefP⟩ := hP
    obtain ⟨Kref, Kstarref, Uref, hKMref, hKref, hKstarref, hUref⟩ :=
      OddOrder.BG.Ch4.S14.exists_typeP_data hG hMrefmax
    exact Or.inr ⟨nonTypeICovering_of_isTypeP hG _ (fun _ => rfl) hMrefmax hMrefP hKMref hKref
      hKstarref hUref⟩
  · -- `𝓜_P = ∅` (every maximal is type-F/I): the Type-I covering.  Its `cover_subset_kernels`
    -- (`M̃_i ⊆ ((M_i)_F)#` conjugates) is the §8 / route-B endpoint (`bgTheoremE_cover_data`'s
    -- TypeICovering side, owned by the §8 Dade work in lane-a/c), so this branch remains gated.
    sorry

/-- **Peterfalvi (8.18.c)**: the final support-exclusion relation in Section 10.  For **non-conjugate
type-I** maximal subgroups `S, T`, the sharp sets `A₁(S) = (S_F)^#` and `A₁(T) = (T_F)^#` cannot
mutually support each other.

Proof.  Both are type I, so `A₁(S) = M_σ(S)^#` and `A₁(T) = M_σ(T)^#`
(`A1_eq_sigmaSharp_of_typeI_or_II`).  Pick `y ∈ A₁(S)` (nonempty: `S_F ≠ ⊥` for type I).  Then
`y ∈ M_σ(S)^# ⊆ M̃(S) ⊆ 𝒞_G(M̃(S))` (`sigmaSharp_subset_Mtilde`, `subset_conjClassSet`); and the
support hypothesis `A₁(S) ⊆ 𝒞_G(A₁(T)) = 𝒞_G(M_σ(T)^#) ⊆ 𝒞_G(M̃(T))` (`conjClassSet_mono`).  But
`𝒞_G(M̃(S)) ∩ 𝒞_G(M̃(T)) = ∅` for non-conjugate `S, T` (`conjClassSet_Mtilde_disjoint`, BG Lemma
14.5(b)) — contradiction.  Only one support direction is needed. -/
theorem support_mutual_exclusion [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S T : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hT : T ∈ maximalSubgroups G)
    (hSI : IsTypeI S) (hTI : IsTypeI T)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup S T) :
    ¬ (Supports (A1 S PeterfalviType.I) (A1 T PeterfalviType.I) ∧
        Supports (A1 T PeterfalviType.I) (A1 S PeterfalviType.I)) := by
  rintro ⟨hsup, -⟩
  set D := OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG with hD
  have hA1S : A1 S PeterfalviType.I = OddOrder.BG.Ch4.S14.sigmaSharp S :=
    OddOrder.Peterfalvi.S10Interface.A1_eq_sigmaSharp_of_typeI_or_II hG hS (Or.inl hSI) (Or.inl rfl)
  have hA1T : A1 T PeterfalviType.I = OddOrder.BG.Ch4.S14.sigmaSharp T :=
    OddOrder.Peterfalvi.S10Interface.A1_eq_sigmaSharp_of_typeI_or_II hG hT (Or.inl hTI) (Or.inl rfl)
  -- `A₁(S)` is nonempty: `S_F ≠ ⊥` for type I.
  obtain ⟨data⟩ := hSI
  have hHne : maxNilpotentNormalHall S ≠ ⊥ := by
    rw [← data.typeF.H_eq]; exact data.typeF.H_nontrivial
  haveI : Nontrivial ↥(maxNilpotentNormalHall S) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hHne
  obtain ⟨y, hyne⟩ := exists_ne (1 : ↥(maxNilpotentNormalHall S))
  have hxA1 : (y : G) ∈ A1 S PeterfalviType.I := by
    show (y : G) ∈ (maxNilpotentNormalHall S : Set G) \ {1}
    exact ⟨y.2, fun h => hyne (Subtype.ext h)⟩
  have h1 : (y : G) ∈ conjClassSet (OddOrder.BG.Ch4.S14.Mtilde hG D S) :=
    subset_conjClassSet (OddOrder.BG.Ch4.S14.sigmaSharp_subset_Mtilde hG D (hA1S ▸ hxA1))
  have h2 : (y : G) ∈ conjClassSet (OddOrder.BG.Ch4.S14.Mtilde hG D T) := by
    refine conjClassSet_mono (OddOrder.BG.Ch4.S14.sigmaSharp_subset_Mtilde hG D) ?_
    rw [← hA1T]; exact hsup hxA1
  exact Set.disjoint_left.mp
    (OddOrder.BG.Ch4.S14.conjClassSet_Mtilde_disjoint hG D hS hT hnc) h1 h2

-- TODO (Peterfalvi (8.15), higher Dade specializations): add the recovered
-- Hypothesis (4.6)/(5.2) statements with `K=M_prime` and `H=M_F` or `M_s`
-- once those section-level carriers expose the needed `L=M` specialization
-- without opaque placeholder propositions.
--

/-! ### Route-B (M̃-cover) `G₀ = {1}` reduction for the (7.4) Dade-support family

The all-type-I non-existence proof (Peterfalvi (12.17), `S14.not_all_maximal_typeI`) needs
`G₀ = {1}`: once the family's supports cover `G#`, no nonidentity element survives in `G₀`.  For
the kernel-cover `FrobeniusFamily` this is inline in `not_all_maximal_typeI`; the *faithful*
M̃-cover route (issue 8022) rebuilds the family as a `FamilyHypothesis71` whose Dade supports
`A_i^{τ_i} = 𝒞_G(M̃_i)` are the lane-d-proven cover
(`S14.sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF`).  These two helpers supply the
matching `G₀ = {1}` step for that family; the (7.5) `S09.family_inequality` then yields the
contradiction (the §7/§8 character inputs to
`S09.not_trivial_G0_of_family71_coherent_zeta_source_data` remain the gated lane-a/c residual). -/

/-- `1 ∈ G₀` for a `(7.4)` Dade-support family: the identity lies in no Dade support `A_i^{τ_i}`
(`one_notMem_dadeSupport`). -/
theorem familyHyp71_one_mem_G0 {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {k : ℕ}
    (F : OddOrder.Peterfalvi.S09.FamilyHypothesis71 G k) : (1 : G) ∈ F.G0 :=
  F.mem_G0_iff.mpr fun i => (F.hyp71 i).hyp.one_notMem_dadeSupport

/-- **Peterfalvi (7.4)(d), the covered case** for a `FamilyHypothesis71`: if every nonidentity
element of `G` lies in some Dade support `A_i^{τ_i}` (the family covers `G#`), then `G₀ = {1}`.
Pure set theory given the cover — the route-B / M̃-cover analogue of the `FrobeniusFamily`
kernel-cover `G₀ = {1}` step in `S14.not_all_maximal_typeI`. -/
theorem familyHyp71_G0_eq_singleton_one_of_cover {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {k : ℕ}
    (F : OddOrder.Peterfalvi.S09.FamilyHypothesis71 G k)
    (hcov : ∀ x : G, x ≠ 1 → ∃ i, x ∈ (F.hyp71 i).hyp.dadeSupport) :
    F.G0 = {1} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨familyHyp71_one_mem_G0 F, fun x hx => by
    by_contra hx1
    obtain ⟨i, hi⟩ := hcov x hx1
    exact F.mem_G0_iff.mp hx i hi⟩

end OddOrder.Peterfalvi.S10
