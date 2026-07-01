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

/-- **Peterfalvi (8.12.b)**: type I/II Sylow-complement centralizer control.

If `M` is of type I or II and `U` is the relevant complement (`M = H ⋊ U` for type I,
`[M,M] = H ⋊ U` for type II), then for every non-empty subset `X` of `U#` such that
`C_H(X) ≠ 1` (i.e. `M_F ⊓ C_G(X) ≠ ⊥`), **`M` is the unique maximal subgroup of `G` which
contains `C_G(X)`** — recorded as `C_G(X) ≤ M` together with `IsUniquelyMaximal (C_G(X))`
(the unique coatom above `C_G(X)` being `M`).

The earlier formulation recorded only `IsUniquelyMaximal (C_G(X))`, which is strictly weaker:
for type II `C_G(X)` need not lie in `M`, so without the `C_G(X) ≤ M` clause the result cannot
identify the unique maximal as `M` (as (9.3) requires).  Reference: [BG], §16, Theorem B and
Proposition 16.1. -/
theorem typeI_or_typeII_centralizer_unique [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M ∨ IsTypeII M) (hUle : U ≤ M) :
    ∀ X : Set G, X.Nonempty → X ⊆ sharpSubgroup U →
      maxNilpotentNormalHall M ⊓ Subgroup.centralizer X ≠ ⊥ →
        Subgroup.centralizer X ≤ M ∧ IsUniquelyMaximal (Subgroup.centralizer X) := by
  sorry

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

/-- **Peterfalvi (8.16)**: for a maximal subgroup of Type II, the three sets
`A_0(M)`, `A(M)`, and `A_1(M)` are TI-subsets of `G` with normalizer `M`.

This is the directly usable part of the PDF-recovered missing page.  The proof is
BG Section 16 / Peterfalvi (2.3), not a local character-theoretic argument. -/
theorem typeII_A_sets_TI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIIData M) :
    IsTISubset (typePA0 M data.typeP) M ∧
      IsTISubset (typePA M data.typeP) M ∧
        IsTISubset (A1 M PeterfalviType.II) M := by
  sorry

/-- **Peterfalvi (8.16)**, normalizer form: for Type II, the normalizers of
`A_0(M)`, `A(M)`, and `A_1(M)` are all `M`. -/
theorem typeII_A_sets_normalizer [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIIData M) :
    Subgroup.normalizer (typePA0 M data.typeP) = M ∧
      Subgroup.normalizer (typePA M data.typeP) = M ∧
        Subgroup.normalizer (A1 M PeterfalviType.II) = M := by
  sorry

/-- **Peterfalvi (8.14)**: the subgroup `R(x)`, shared as
`OddOrder.GroupTheory.supportKernel`. -/
noncomputable abbrev supportKernel (L M : Subgroup G) (X : Set G) (x : G) :=
  OddOrder.GroupTheory.supportKernel L M X x

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
`N_G(A) = M`, the Dade Hypothesis (2.2), the recovered formula `H(a)=R(a)`, and
that the §4 Dade support is the thickened support from (8.14).  The later
Hypothesis (4.6)/(5.2) specializations add character-family data and are kept as
a separate TODO below. -/
structure DadeSupportHypothesisData [Fintype G] (M : Subgroup G) (A : Set G) where
  /-- Peterfalvi (8.15): `M = N_G(A)`. -/
  normalizer_eq : Subgroup.normalizer A = M
  /-- Peterfalvi (8.15): Hypothesis (2.2) holds with `L = M`. -/
  dade : OddOrder.Peterfalvi.S04.Hypothesis G A M
  /-- Peterfalvi (8.15): the subgroups in Hypothesis (2.2) are the recovered
  `R(a)` from (8.14). -/
  H_eq_supportKernel :
    ∀ a : {a : G // a ∈ A}, dade.H a = supportKernel M M A a.1
  /-- The Dade support from §4 is the thickened support notation of (8.14). -/
  dadeSupport_eq_thickenedSupport : dade.dadeSupport = thickenedSupport M M A

/-- **Peterfalvi (8.15)** for type I: the Dade (2.2) support hypotheses hold
for `A(M)=A_0(M)` and `A_1(M)`, with `L=M` and `H(a)=R(a)`. -/
theorem dadeSupportHypotheses_typeI [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIData M) :
    Nonempty (DadeSupportHypothesisData M (typeIA M data)) ∧
      Nonempty (DadeSupportHypothesisData M (A1 M PeterfalviType.I)) := by
  sorry

/-- **Peterfalvi (8.15)** for type `P`: the Dade (2.2) support hypotheses hold
for `A_0(M)`, `A(M)`, and `A_1(M)`, with `L=M` and `H(a)=R(a)`. -/
theorem dadeSupportHypotheses_typeP [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    {tau : PeterfalviType} (hType : HasPeterfalviType tau M) :
    Nonempty (DadeSupportHypothesisData M (typePA0 M data)) ∧
      Nonempty (DadeSupportHypothesisData M (typePA M data)) ∧
        Nonempty (DadeSupportHypothesisData M (A1 M tau)) := by
  sorry


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
