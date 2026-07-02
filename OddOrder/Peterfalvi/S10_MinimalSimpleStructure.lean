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

/-- **Peterfalvi (8.13.a) for the type-I support** (pin): two `G`-conjugate elements of `A(M)` are
already `M`-conjugate.  Deep §16 fusion obligation (BG §16 Theorem II; Coq `FTsupport_facts`
part a), `sorry`-pinned for the (8.15) assembly (issue 0096). -/
theorem typeIA_isConj_conj_in_M [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypeIData M)
    {a b : G} (ha : a ∈ typeIA M data) (hb : b ∈ typeIA M data) (hab : IsConj a b) :
    ∃ m : G, m ∈ M ∧ m * a * m⁻¹ = b := by
  sorry

/-- **Peterfalvi (8.13.c1/c2) at an escaping point of the type-I support** (pin; BG §16
Theorem II + Theorem D(4); Coq `FTsupport_facts` part c).  For escaping `a ∈ A(M)`
(`C_G(a) ⊄ M`), with `R(a) = FT_signalizer a` the supporting-maximal signalizer:
- (8.13.c1) `C_G(a) = R(a) ⋊ C_M(a)` — join, disjointness, and normality of `R(a)`;
- (8.13.c2) `|R(a)|` is coprime to `|C_M(b)|` for every `b ∈ A(M)`.

The BG-side ingredients are `signalizer_structure_of_mem_sigmaSharp` /
`signalizer_centralizer_isComplement` / `FT_signalizer_normal_in_centralizer` (S16); the remaining
gap is identifying escaping `A(M)`-points as `σ`-sharp with more than one `σ`-maximal
((8.13.b), `escapingCentralizers_control`) and the cross-point coprimality (8.13.c2). -/
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
  sorry

/-- **(8.14) kernel equivariance at an escaping point** (pin): `R(m·a·m⁻¹) = m·R(a)·m⁻¹` for
`m ∈ M`, from the uniqueness of the supporting maximal (`N[m·a·m⁻¹] = m·N[a]·m⁻¹`, BG Theorem D). -/
theorem FT_signalizer_conj_smul_of_escaping [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIData M)
    {a m : G} (hm : m ∈ M)
    (ha : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M (typeIA M data)) :
    OddOrder.BG.Ch4.S16.FT_signalizer (m * a * m⁻¹)
      = MulAut.conj m • OddOrder.BG.Ch4.S16.FT_signalizer a := by
  sorry

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
    have h2 : m * x * m⁻¹ = m * x * m⁻¹ := rfl
    exact key hm hle
  · rintro ⟨hx, hesc⟩
    refine ⟨hX.mpr hx, fun hle => hesc ?_⟩
    have h2 : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
    exact h2 ▸ key (inv_mem hm) hle

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

/-- `A₁(M)` is `M`-conjugation invariant (via the `M`-normality of `M_F`). -/
theorem A1_typeI_conj_mem (M : Subgroup G) {m : G} (hm : m ∈ M) {a : G}
    (ha : a ∈ A1 M PeterfalviType.I) : m * a * m⁻¹ ∈ A1 M PeterfalviType.I := by
  obtain ⟨haH, ha1⟩ := (Set.mem_diff a).mp ha
  have hnorm := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M hm
  rw [Subgroup.mem_normalizer_iff] at hnorm
  refine (Set.mem_diff _).mpr ⟨SetLike.mem_coe.mpr ((hnorm a).mp (SetLike.mem_coe.mp haH)), ?_⟩
  exact fun h => (conj_ne_one (fun h1 => ha1 (Set.mem_singleton_iff.mpr h1)))
    (Set.mem_singleton_iff.mp h)

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
    refine ⟨fun h => ?_, A1_typeI_conj_mem M hm⟩
    have h2 := A1_typeI_conj_mem M (inv_mem hm) h
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

/-- **Peterfalvi (8.13.b), `D ⊆ A₁` conjunct** (pin; BG §16 Theorem II): an escaping point of the
type-I support `A(M)` lies in the sharp core `A₁(M)`. -/
theorem escaping_typeIA_mem_A1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypeIData M)
    {a : G} (ha : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M (typeIA M data)) :
    a ∈ A1 M PeterfalviType.I := by
  sorry

/-- **Peterfalvi (8.12.b), single-point form** (pin; BG §16 Theorem B): for type-I `T` and
`x ∈ T` of order coprime to `|T_F|` centralizing a nontrivial element of `T_F`, `T` is the unique
maximal subgroup containing `C_G(x)`.  (The Hall-conjugacy move of `x` into a complement is
absorbed into the pin.) -/
theorem typeI_centralizer_le_and_unique [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {T : Subgroup G} (hT : T ∈ maximalSubgroups G) (dT : TypeIData T)
    {x : G} (hxT : x ∈ T) (hx1 : x ≠ 1)
    (hord : Nat.Coprime (orderOf x) (Nat.card (maxNilpotentNormalHall T)))
    (hwit : ∃ h ∈ maxNilpotentNormalHall T, h ≠ 1 ∧ Commute x h) :
    Subgroup.centralizer ({x} : Set G) ≤ T ∧
      ∀ L ∈ maximalSubgroups G, Subgroup.centralizer ({x} : Set G) ≤ L → L = T := by
  sorry

/-- **Peterfalvi (8.13.c2/c4) cross-coprimality under support** (pin): if some escaping point of
`A(S)` has its centralizer inside a conjugate of `T`, then `T` "supports" `S` and `|T_σ|` is
coprime to `|C_S(w)|` for every `w ∈ A(S)`  ((8.13.c2) applied to the supporting maximal
`N ~ T`, whose Fitting core has the `σ(T)`-order, plus (8.13.c4)). -/
theorem supported_sigma_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {S T : Subgroup G} (hS : S ∈ maximalSubgroups G) (hT : T ∈ maximalSubgroups G)
    (dS : TypeIData S) (dT : TypeIData T)
    (hsupp : ∃ z ∈ OddOrder.GroupTheory.escapingCentralizerSet S (typeIA S dS),
      ∃ N ∈ maximalSubgroups G, Subgroup.centralizer ({z} : Set G) ≤ N ∧
        OddOrder.BG.Ch4.S14.IsConjugateSubgroup T N) :
    ∀ w ∈ typeIA S dS,
      Nat.Coprime (Nat.card (OddOrder.BG.Ch3.S10.Msigma T))
        (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn S w)) := by
  sorry

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
