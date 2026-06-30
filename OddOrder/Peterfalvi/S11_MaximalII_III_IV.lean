/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S10_MinimalSimpleStructure
import OddOrder.Peterfalvi.S10_CoherenceWiring
import OddOrder.GroupTheory.CoprimeAction
import OddOrder.GroupTheory.WielandtFixedPoint
import OddOrder.GroupTheory.CoprimeFixedPoints
import OddOrder.GroupTheory.MaximalSubgroupTypeConj
import OddOrder.GroupTheory.AInvariantPiSubgroups
import OddOrder.BG.Ch1_Preliminary.OperatorMaschke
import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF
import OddOrder.GroupTheory.RepresentationTheory.SingerField
import OddOrder.GroupTheory.RepresentationTheory.WielandtElabBridge
import OddOrder.GroupTheory.RepresentationTheory.CliffordSingleOrbit
import OddOrder.Peterfalvi.S08_CoherenceCorePart1

/-!
# Peterfalvi Section 11: Maximal Subgroups of Types II, III, and IV

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 11, pp. 50--57.

This section analyzes a maximal subgroup `M` of type II, III, or IV.  It starts
with Wielandt's fixed-point formula for a coprime Frobenius action, extracts the
chief factor `H/H_0` inside the Fitting part of `M`, and then applies Clifford
theory to split the character-theoretic argument into the two cases of
Peterfalvi (9.7).  The endpoint is the coherence statement (9.11) used by the
later maximal-subgroup comparisons.

The present file is a scaffold.  It keeps the group-theoretic carriers explicit
and uses the existing §7 coherence API directly; the quotient action, Clifford
case data, and counting assertions are bundled as named structures so downstream
sections can import stable theorem names without committing to a premature model
of the quotient module `H/H_0`.
-/

namespace OddOrder.Peterfalvi.S11
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## (9.1): Wielandt's fixed-point formula

The shared carrier `OddOrder.GroupTheory.CoprimeFrobeniusAction` lives in
`OddOrder.GroupTheory.CoprimeAction`; the Wielandt theorems, proved from the chief-series
assembly, live in `OddOrder.GroupTheory.WielandtFixedPoint`:

* `OddOrder.GroupTheory.CoprimeFrobeniusAction` (carrier, `CoprimeAction`)
* `OddOrder.GroupTheory.wielandt_fixedPoint_frobenius`
* `OddOrder.GroupTheory.wielandt_fixedPoint_trivial_E_fixed`
* `OddOrder.GroupTheory.wielandt_fixedPoint_trivial_U_fixed`

They are kept outside this Peterfalvi section because the same coprime-action
interface is expected to be reused by the BG and Isaacs layers. -/

/-! ## (9.2)--(9.6): type II--IV setup and the chief factor `H/H_0` -/

/-- The common setup of Peterfalvi (9.2): a maximal subgroup of type II, III, or
IV, together with its type-`P` data from (8.4).

The `nontrivial` field records the `TypePNontrivialCore` of (8.6) — `U ≠ 1`, `|W₁|` prime, and the
TI condition — that all of types II, III, IV carry (it is the `common` field of `TypeIIData` /
`TypeIIIData` / `TypeIVData`); it makes the setup a faithful model of "`M` is of type II/III/IV with
*these* data" (so e.g. `U ≠ 1` is available for the present `typeP`, not only for some witness). -/
structure TypesIIIIIIVSetup (M : Subgroup G) where
  maximal : M ∈ maximalSubgroups G
  typeP : TypePData M
  nontrivial : TypePNontrivialCore M typeP
  type_alt : IsTypeII M ∨ IsTypeIII M ∨ IsTypeIV M

namespace TypesIIIIIIVSetup

/-- Peterfalvi's `H` in (9.2).  Reducible so that the chief-factor carrier `↥data.H ⧸ N` is
defeq-transparently `↥data.typeP.H ⧸ N`, letting instance search find the kernel's normality and the
descended action across the `TypesIIIIIIVSetup`/`TypePData` boundary. -/
@[reducible] def H {M : Subgroup G} (data : TypesIIIIIIVSetup M) : Subgroup G :=
  data.typeP.H

/-- Peterfalvi's `U` in (9.2). -/
def U {M : Subgroup G} (data : TypesIIIIIIVSetup M) : Subgroup G :=
  data.typeP.U

/-- Peterfalvi's `W_1` in (9.2). -/
def W1 {M : Subgroup G} (data : TypesIIIIIIVSetup M) : Subgroup G :=
  data.typeP.W1

/-- Peterfalvi's `W_2` in (9.2). -/
def W2 {M : Subgroup G} (data : TypesIIIIIIVSetup M) : Subgroup G :=
  data.typeP.W2

/-- Peterfalvi's `q = |W_1|` in (9.2). -/
noncomputable def q {M : Subgroup G} (data : TypesIIIIIIVSetup M) : ℕ :=
  Nat.card ↥data.W1

end TypesIIIIIIVSetup

/-! ## (9.1) ⇒ (9.3): the Frobenius action of `U W₁` on `H` and Wielandt's order relation

Definition (8.4) makes `U W₁` a Frobenius group with kernel `U`, acting coprimely on the nilpotent
Hall subgroup `H = M_F`.  Wielandt's fixed-point formula `wielandt_fixedPoint_frobenius` (9.1) then
gives the order relation `|C_H(U W₁)|^q · |H| = |W₂|^q · |C_H(U)|` (here `C_H(W₁) = W₂`), which is the
quantitative core of (9.3).  We build the `CoprimeFrobeniusAction` from the type-`P` data and read
off the three fixed-point subgroups as the concrete centralizers. -/

section Wielandt93

open OddOrder.Isaacs.Ch06

variable {M : Subgroup G}

private theorem derivedInG_le_self (H : Subgroup G) : derivedInG H ≤ H := by
  unfold derivedInG; exact Subgroup.map_subtype_le _

/-- `A ⊓ B = ⊥` from a relative complement: if `A, B ≤ K` and `A.subgroupOf K`, `B.subgroupOf K`
are complements in `↥K`, then `A` and `B` meet trivially in `G`. -/
private theorem inf_eq_bot_of_isComplement_subgroupOf {A B K : Subgroup G}
    (hA : A ≤ K) (hc : Subgroup.IsComplement' (A.subgroupOf K) (B.subgroupOf K)) :
    A ⊓ B = ⊥ := by
  have hcomap : (A.subgroupOf K) ⊓ (B.subgroupOf K) = (A ⊓ B).subgroupOf K :=
    (Subgroup.comap_inf A B K.subtype).symm
  have hd : (A ⊓ B).subgroupOf K = ⊥ := by rw [← hcomap]; exact hc.disjoint.eq_bot
  rw [Subgroup.subgroupOf_eq_bot] at hd
  exact hd.eq_bot_of_le (inf_le_left.trans hA)

/-- `H ⊓ U = ⊥`: `H` and `U` are complementary in `M' = derivedInG M` (`derived_complement`). -/
private theorem typeP_H_inf_U (data : TypePData M) : data.H ⊓ data.U = ⊥ :=
  inf_eq_bot_of_isComplement_subgroupOf data.H_le data.derived_complement

/-- `U ⊓ W₁ = ⊥`: `W₁` complements `M' = derivedInG M` in `M` (`M_complement`) and `U ≤ M'`. -/
private theorem typeP_U_inf_W1 (data : TypePData M) : data.U ⊓ data.W1 = ⊥ := by
  have hM' : derivedInG M ⊓ data.W1 = ⊥ :=
    inf_eq_bot_of_isComplement_subgroupOf (derivedInG_le_self M) data.M_complement
  refine le_bot_iff.mp (le_trans ?_ hM'.le)
  exact inf_le_inf_right _ data.U_le

/-- The fixed-point-free condition of Definition (8.4): for `w ∈ W₁#`, no nontrivial `u ∈ U` is
fixed by conjugation by `w`.  `C_U(w) ⊆ M' ⊓ C_G(w) = W₂` (`centralizer_W1`) and `U ⊓ W₂ ⊆ U ⊓ H = ⊥`
(`W₂ ≤ H`, `H ⊓ U = ⊥`). -/
private theorem typeP_W1_fpf_U (data : TypePData M) {w : G} (hw : w ∈ data.W1) (hwne : w ≠ 1)
    {u : G} (hu : u ∈ data.U) (heq : w * u * w⁻¹ = u) : u = 1 := by
  have hcomm : w * u = u * w := mul_inv_eq_iff_eq_mul.mp heq
  have hmemC : u ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hin : u ∈ derivedInG M ⊓ Subgroup.centralizer ({w} : Set G) := ⟨data.U_le hu, hmemC⟩
  rw [data.centralizer_W1 w hw hwne] at hin
  have huH : u ∈ data.H := (data.W2_le hin).1
  have : u ∈ data.H ⊓ data.U := ⟨huH, hu⟩
  rw [typeP_H_inf_U data] at this
  exact this

/-- **Definition (8.4)**: `U W₁` is a Frobenius group with kernel `U` and complement `W₁`
(for types II–IV, where `U ≠ 1`; at type V the kernel `U = 1` degenerates). -/
theorem typeP_uW1_frobenius (data : TypePData M) (hU : data.U ≠ ⊥) :
    IsFrobeniusGroup ↥(data.U ⊔ data.W1)
      (data.U.subgroupOf (data.U ⊔ data.W1)) (data.W1.subgroupOf (data.U ⊔ data.W1)) := by
  set L := data.U ⊔ data.W1 with hL
  have hUnorm : (data.U.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer data.W1_normalizes_U)
  have hdisj : Disjoint (data.U.subgroupOf L) (data.W1.subgroupOf L) := by
    have hc : (data.U.subgroupOf L) ⊓ (data.W1.subgroupOf L) = (data.U ⊓ data.W1).subgroupOf L :=
      (Subgroup.comap_inf data.U data.W1 L.subtype).symm
    rw [disjoint_iff, hc, typeP_U_inf_W1 data, Subgroup.bot_subgroupOf]
  have hsup : (data.U.subgroupOf L) ⊔ (data.W1.subgroupOf L) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  refine ⟨hUnorm, ?_, ?_, ?_, ?_⟩
  · refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
    haveI := hUnorm
    rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]
  · rw [Ne, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hU (hd.eq_bot_of_le le_sup_left)
  · rw [Ne, Subgroup.subgroupOf_eq_bot]
    exact fun hd => data.W1_nontrivial (hd.eq_bot_of_le le_sup_right)
  · intro a haA hane n hnN hnne hconj
    have hwW1 : (a : G) ∈ data.W1 := Subgroup.mem_subgroupOf.mp haA
    have huU : (n : G) ∈ data.U := Subgroup.mem_subgroupOf.mp hnN
    have haG : (a : G) ≠ 1 := fun h => hane (Subtype.ext h)
    have hnG : (n : G) ≠ 1 := fun h => hnne (Subtype.ext h)
    have hconjG : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := Subtype.ext_iff.mp hconj
    exact hnG (typeP_W1_fpf_U data hwW1 haG huU hconjG)

/-- `U W₁ ≤ M ≤ N_G(H)`: the conjugation action of `U W₁` on `H = M_F`. -/
theorem typeP_uW1_le_normalizer_H (data : TypePData M) :
    data.U ⊔ data.W1 ≤ Subgroup.normalizer (data.H : Set G) := by
  have hMnorm : M ≤ Subgroup.normalizer (data.H : Set G) := by
    rw [data.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M
  refine sup_le ?_ (data.W1_le.trans hMnorm)
  exact (data.U_le.trans (derivedInG_le_self M)).trans hMnorm

/-- The conjugation action of `U W₁ ≤ N_G(H)` on `H = M_F`. -/
noncomputable def typeP_conjAction (data : TypePData M) :
    ↥(data.U ⊔ data.W1) →* MulAut ↥data.H :=
  letI : MulDistribMulAction ↥(data.U ⊔ data.W1) ↥data.H :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (data.H : Set G))) ↥data.H
      (Subgroup.inclusion (typeP_uW1_le_normalizer_H data))
  MulDistribMulAction.toMulAut ↥(data.U ⊔ data.W1) ↥data.H

theorem typeP_conjAction_apply (data : TypePData M) (a : ↥(data.U ⊔ data.W1)) (x : ↥data.H) :
    ((typeP_conjAction data a x : ↥data.H) : G) = (a : G) * (x : G) * (a : G)⁻¹ := rfl

/-- The action of `U W₁` on `H = M_F` is coprime: `|H| ⟂ |U W₁| = |U| · |W₁|`.  `H` is a Hall
subgroup of `M` (`maxNilpotentNormalHall_isHall`), and the index `[M : H] = [M : M'] · [M' : H]
= |W₁| · |U| = |U W₁|` (the relative-index tower with the `M_complement`/`derived_complement`
splittings and the Frobenius product `|U W₁| = |U| · |W₁|`). -/
theorem typeP_coprime_H_uW1 [Finite G] (data : TypePData M) (hU : data.U ≠ ⊥) :
    Nat.Coprime (Nat.card ↥data.H) (Nat.card ↥(data.U ⊔ data.W1)) := by
  have hHleM : data.H ≤ M := data.H_le.trans (derivedInG_le_self M)
  -- `[M' : H] = |U|` and `[M : M'] = |W₁|` from the two complement splittings.
  have hUidx : (data.H.subgroupOf (derivedInG M)).index = Nat.card ↥data.U := by
    rw [data.derived_complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.U_le).toEquiv]
  have hW1idx : ((derivedInG M).subgroupOf M).index = Nat.card ↥data.W1 := by
    rw [data.M_complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.W1_le).toEquiv]
  -- `[M' : H] · [M : M'] = [M : H]` (relative-index tower), so `[M : H] = |U| · |W₁|`.
  have htower : (data.H.subgroupOf (derivedInG M)).index * ((derivedInG M).subgroupOf M).index
      = (data.H.subgroupOf M).index :=
    Subgroup.relIndex_mul_relIndex data.H (derivedInG M) M data.H_le (derivedInG_le_self M)
  rw [hUidx, hW1idx] at htower
  -- `|U W₁| = |U| · |W₁|` from the Frobenius complement.
  have hcard : Nat.card ↥(data.U ⊔ data.W1) = Nat.card ↥data.U * Nat.card ↥data.W1 := by
    rw [← (typeP_uW1_frobenius data hU).isComplement.card_mul,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
  -- `H` is Hall in `M`: `|H| ⟂ [M : H] = |U| · |W₁| = |U W₁|`.
  have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall M
  rw [← data.H_eq] at hHall
  have hcop_idx := hHall.coprime_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleM).toEquiv] at hcop_idx
  rw [hcard, htower]
  exact hcop_idx

/-- The coprime Frobenius action of `U W₁` (kernel `U`, complement `W₁`) on `H = M_F`, by
conjugation — the carrier for Wielandt's formula (9.1). -/
noncomputable def typeP_coprimeAction [Finite G] (data : TypePData M) (hU : data.U ≠ ⊥) :
    CoprimeFrobeniusAction ↥(data.U ⊔ data.W1) ↥data.H where
  U := data.U.subgroupOf (data.U ⊔ data.W1)
  E := data.W1.subgroupOf (data.U ⊔ data.W1)
  frobenius := typeP_uW1_frobenius data hU
  H_solvable := by
    rw [data.H_eq]
    haveI := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent M
    exact IsNilpotent.to_isSolvable
  φ := typeP_conjAction data
  coprime_order := typeP_coprime_H_uW1 data hU

/-! ### Identifying the fixed-point subgroups with the concrete centralizers -/

/-- The image in `G` of the fixed subgroup of `K ≤ U W₁` under the conjugation action is the
concrete centralizer `C_H(K) = H ⊓ C_G(K)`. -/
theorem typeP_fixedSubgroup_map (data : TypePData M) {K : Subgroup G}
    (hK : K ≤ data.U ⊔ data.W1) :
    (fixedSubgroup (typeP_conjAction data) (K.subgroupOf (data.U ⊔ data.W1))).map data.H.subtype
      = data.H ⊓ Subgroup.centralizer (K : Set G) := by
  ext x
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h.2, Subgroup.mem_centralizer_iff.mpr (fun g hg => ?_)⟩
    have hfix := hh ⟨g, hK hg⟩ (Subgroup.mem_subgroupOf.mpr hg)
    have hconj : (g : G) * (h : G) * (g : G)⁻¹ = (h : G) := by
      have := Subtype.ext_iff.mp hfix; rwa [typeP_conjAction_apply] at this
    exact mul_inv_eq_iff_eq_mul.mp hconj
  · rintro ⟨hxH, hxC⟩
    refine ⟨⟨x, hxH⟩, fun l hl => ?_, rfl⟩
    have hlx : (l : G) * x = x * (l : G) :=
      Subgroup.mem_centralizer_iff.mp hxC (l : G) (Subgroup.mem_subgroupOf.mp hl)
    have hval : ((typeP_conjAction data l) ⟨x, hxH⟩ : G) = x := by
      rw [typeP_conjAction_apply]; show (l : G) * x * (l : G)⁻¹ = x
      rw [hlx, mul_inv_cancel_right]
    exact Subtype.ext hval

/-- The order of the fixed subgroup of `K ≤ U W₁` equals `|C_H(K)| = |H ⊓ C_G(K)|`. -/
theorem typeP_card_fixedSubgroup (data : TypePData M) {K : Subgroup G}
    (hK : K ≤ data.U ⊔ data.W1) :
    Nat.card ↥(fixedSubgroup (typeP_conjAction data) (K.subgroupOf (data.U ⊔ data.W1)))
      = Nat.card ↥(data.H ⊓ Subgroup.centralizer (K : Set G)) := by
  rw [← typeP_fixedSubgroup_map data hK]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective _ data.H.subtype data.H.subtype_injective).toEquiv

/-- **`C_H(W₁) = W₂`** (Peterfalvi (9.2)): `W₂ = C_{M'}(w)` for any `w ∈ W₁#` (`centralizer_W1`),
and since `W = W₁ W₂` is cyclic, `W₂` centralizes all of `W₁`. -/
theorem typeP_H_inf_centralizer_W1 (data : TypePData M) :
    data.H ⊓ Subgroup.centralizer (data.W1 : Set G) = data.W2 := by
  obtain ⟨w, hwW1, hwne⟩ := (data.W1.bot_or_exists_ne_one).resolve_left data.W1_nontrivial
  apply le_antisymm
  · intro h hh
    obtain ⟨hhH, hhC⟩ := hh
    have : h ∈ derivedInG M ⊓ Subgroup.centralizer ({w} : Set G) := by
      refine ⟨data.H_le hhH, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact (Subgroup.mem_centralizer_iff.mp hhC w hwW1).symm
    rwa [data.centralizer_W1 w hwW1 hwne] at this
  · refine le_inf ?_ ?_
    · intro x hx; exact (data.W2_le hx).1
    · intro x hxW2
      rw [Subgroup.mem_centralizer_iff]
      intro g hgW1
      have hxW : x ∈ data.W := by rw [data.W_eq]; exact Subgroup.mem_sup_right hxW2
      have hgW : g ∈ data.W := by rw [data.W_eq]; exact Subgroup.mem_sup_left hgW1
      exact (S06.commute_of_mem_of_isCyclic data.W_cyclic hgW hxW).eq

/-- **Peterfalvi (9.3), the quantitative core** via Wielandt's fixed-point formula (9.1):
`|C_H(U W₁)|^q · |H| = |W₂|^q · |C_H(U)|` with `q = |W₁|` and `C_H(W₁) = W₂`.  The Frobenius
group `U W₁` (kernel `U`) acts coprimely on `H = M_F`, and the three fixed-point subgroups of
Wielandt's formula are the concrete centralizers. -/
theorem typeP_wielandt_order_relation [Finite G] (data : TypePData M) (hU : data.U ≠ ⊥) :
    Nat.card ↥(data.H ⊓ Subgroup.centralizer ((data.U ⊔ data.W1 : Subgroup G) : Set G))
          ^ Nat.card ↥data.W1 * Nat.card ↥data.H
      = Nat.card ↥data.W2 ^ Nat.card ↥data.W1
          * Nat.card ↥(data.H ⊓ Subgroup.centralizer (data.U : Set G)) := by
  have key := wielandt_fixedPoint_frobenius (typeP_coprimeAction data hU)
  have hEcard : Nat.card ↥(typeP_coprimeAction data hU).E = Nat.card ↥data.W1 := by
    show Nat.card ↥(data.W1.subgroupOf (data.U ⊔ data.W1)) = Nat.card ↥data.W1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hUfix : Nat.card ↥(typeP_coprimeAction data hU).fixedByU
      = Nat.card ↥(data.H ⊓ Subgroup.centralizer (data.U : Set G)) := by
    show Nat.card ↥(fixedSubgroup (typeP_conjAction data) (data.U.subgroupOf (data.U ⊔ data.W1)))
      = _
    exact typeP_card_fixedSubgroup data le_sup_left
  have hEfix : Nat.card ↥(typeP_coprimeAction data hU).fixedByE = Nat.card ↥data.W2 := by
    show Nat.card ↥(fixedSubgroup (typeP_conjAction data) (data.W1.subgroupOf (data.U ⊔ data.W1)))
      = _
    rw [typeP_card_fixedSubgroup data le_sup_right, typeP_H_inf_centralizer_W1 data]
  have hUEfix : Nat.card ↥(typeP_coprimeAction data hU).fixedByUE
      = Nat.card ↥(data.H ⊓ Subgroup.centralizer ((data.U ⊔ data.W1 : Subgroup G) : Set G)) := by
    show Nat.card ↥(fixedSubgroup (typeP_conjAction data) ⊤) = _
    rw [← Subgroup.subgroupOf_self (data.U ⊔ data.W1)]
    exact typeP_card_fixedSubgroup data le_rfl
  rw [hUEfix, hEcard, hEfix, hUfix] at key
  exact key

/-! ### Peterfalvi (8.5.b): `U` does not centralize `H` (derived from the type-`P` data) -/

/-- `C_H(U W₁) ≤ W₂`: the fixed points of the whole Frobenius group lie in `C_H(W₁) = W₂`. -/
theorem typeP_centralizer_uW1_le_W2 (data : TypePData M) :
    data.H ⊓ Subgroup.centralizer ((data.U ⊔ data.W1 : Subgroup G) : Set G) ≤ data.W2 := by
  rw [← typeP_H_inf_centralizer_W1 data]
  exact inf_le_inf_left data.H (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))

/-- `|H| ⟂ |W₁|`: `H` is Hall in `M` and `|W₁| = [M : M']` divides `[M : H]`. -/
private theorem typeP_coprime_H_W1 [Finite G] (data : TypePData M) :
    Nat.Coprime (Nat.card ↥data.H) (Nat.card ↥data.W1) := by
  have hHleM : data.H ≤ M := data.H_le.trans (derivedInG_le_self M)
  have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall M
  rw [← data.H_eq] at hHall
  have hcop_idx := hHall.coprime_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleM).toEquiv] at hcop_idx
  have hW1idx : ((derivedInG M).subgroupOf M).index = Nat.card ↥data.W1 := by
    rw [data.M_complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.W1_le).toEquiv]
  have hdvd : Nat.card ↥data.W1 ∣ (data.H.subgroupOf M).index := by
    rw [← hW1idx]; exact Subgroup.index_dvd_of_le (Subgroup.comap_mono data.H_le)
  exact hcop_idx.coprime_dvd_right hdvd

/-- `|U| ⟂ |W₁|`: from the Frobenius group `U W₁`. -/
private theorem typeP_coprime_U_W1 [Finite G] (data : TypePData M) (hU : data.U ≠ ⊥) :
    Nat.Coprime (Nat.card ↥data.U) (Nat.card ↥data.W1) := by
  have h := (typeP_uW1_frobenius data hU).coprime_card_kernel_complement
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at h

/-- **Peterfalvi (8.5.b)**: if `U ≠ 1`, then `U` does not centralize `H`.

If `U ≤ C(H)`, then `F(M) = H ⊔ (U ⊓ C(H)) = H ⊔ U = M'` (`fitting_eq`,
`derivedInG_eq_fitting_sup_U`), so `M' = derivedInG M` is nilpotent (the image of the Fitting
subgroup).  But `M'` is also a normal Hall subgroup of `M` (`|M'| = |H|·|U|` is coprime to
`[M : M'] = |W₁|`, since `H` is Hall and `U W₁` is Frobenius), so `M' ≤ M_F = H`
(`le_maxNilpotentNormalHall`); then `U ≤ M' ≤ H` with `H ⊓ U = ⊥` forces `U = ⊥`. -/
theorem typeP_U_not_centralizes_H [Finite G] (data : TypePData M) (hU : data.U ≠ ⊥) :
    ¬ data.U ≤ Subgroup.centralizer (data.H : Set G) := by
  intro hUC
  apply hU
  have hM'M : derivedInG M ≤ M := derivedInG_le_self M
  -- `M' = H ⊔ U` and `F(M) = M'`.
  have hM'eq : derivedInG M = data.H ⊔ data.U := by
    rw [data.derivedInG_eq_fitting_sup_U, data.H_eq]
  have hFit : (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype = derivedInG M := by
    rw [data.fitting_eq, inf_eq_left.mpr hUC, hM'eq]
  -- `M'` is nilpotent (image of `F(↥M)`).
  haveI : Group.IsNilpotent ↥(OddOrder.Isaacs.Ch01.fitting (↥M : Type _)) :=
    OddOrder.Isaacs.Ch01.fitting.isNilpotent
  haveI hM'nil : Group.IsNilpotent ↥(derivedInG M) := by
    rw [← hFit]
    exact nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective (OddOrder.Isaacs.Ch01.fitting ↥M)
      M.subtype M.subtype_injective)
  -- `M'.subgroupOf M` is the commutator subgroup of `↥M`: normal and nilpotent.
  have hM'sub : (derivedInG M).subgroupOf M = commutator ↥M :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective (commutator ↥M)
  have hM'norm : ((derivedInG M).subgroupOf M).Normal := by rw [hM'sub]; infer_instance
  haveI : Group.IsNilpotent ↥((derivedInG M).subgroupOf M) :=
    nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hM'M).symm
  -- `M'` is a normal Hall subgroup of `M`, so `M' ≤ M_F = H`.
  have hidxM' : ((derivedInG M).subgroupOf M).index = Nat.card ↥data.W1 := by
    rw [data.M_complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.W1_le).toEquiv]
  have hcop : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1) := by
    rw [show Nat.card ↥(derivedInG M) = Nat.card ↥data.H * Nat.card ↥data.U by
      rw [← data.derived_complement.card_mul,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.H_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.U_le).toEquiv]]
    exact (Nat.Coprime.mul_right (typeP_coprime_H_W1 data).symm
      (typeP_coprime_U_W1 data hU).symm).symm
  have hcardSub : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'M).toEquiv
  have hM'hall : OddOrder.Isaacs.Ch03.IsHallSubgroup
      (Nat.card ↥(derivedInG M)).primeFactors ((derivedInG M).subgroupOf M) := by
    refine ⟨fun p hp => hcardSub ▸ hp, fun p hp hpM' => ?_⟩
    rw [hidxM'] at hp
    have hp1 : p ∣ 1 :=
      hcop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hpM') (Nat.dvd_of_mem_primeFactors hp)
    exact (Nat.prime_of_mem_primeFactors hp).ne_one (Nat.dvd_one.mp hp1)
  have hM'leH : derivedInG M ≤ data.H := by
    rw [data.H_eq]
    exact OddOrder.BG.Ch4.S15.le_maxNilpotentNormalHall hM'M hM'norm inferInstance hM'hall
  have hUleH : data.U ≤ data.H := (le_sup_right.trans hM'eq.ge).trans hM'leH
  rw [← inf_of_le_left hUleH, inf_comm, typeP_H_inf_U data]

/-- **Peterfalvi (8.5.b), first part**: `[U, U]` centralizes `H`, so `Ū = U/C_U(H)` is abelian — the
structural input to Peterfalvi (9.7) case (b).

`[U,U] ⊆ M'' = ⁅M', M'⁆` (`commutator_mono`, `U ≤ M' = derivedInG M`), and `M'' ⊆ F(M) =
H ⊔ (U ⊓ C_M(H))` (`secondDerived_le_fitting`).  Since `[U,U] ⊆ U`, `U ⊓ H = ⊥`, and `K = U ⊓ C_M(H)`
centralizes (hence normalizes) `H` — so `↑(H ⊔ K) = ↑H · ↑K` — any `x ∈ [U,U]` writes `x = h·c` with
`h ∈ H`, `c ∈ K ⊆ U`; then `h = x·c⁻¹ ∈ U ⊓ H = ⊥`, so `x = c ∈ K ⊆ C_M(H)`. -/
theorem typeP_commutator_U_centralizes_H (data : TypePData M) :
    ⁅data.U, data.U⁆ ≤ Subgroup.centralizer (data.H : Set G) := by
  set K := data.U ⊓ Subgroup.centralizer (data.H : Set G) with hK
  -- `derivedInG J = ⁅J, J⁆`, so `M'' = secondDerivedInAmbient M = ⁅M', M'⁆`.
  have hderiv : ∀ J : Subgroup G, derivedInG J = ⁅J, J⁆ := fun J => by
    show (commutator ↥J).map J.subtype = ⁅J, J⁆
    rw [commutator_def, Subgroup.map_commutator]
    simp only [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hUU_M'' : ⁅data.U, data.U⁆ ≤ secondDerivedInAmbient M := by
    show ⁅data.U, data.U⁆ ≤ derivedInG (derivedInG M)
    rw [hderiv (derivedInG M)]
    exact Subgroup.commutator_mono data.U_le data.U_le
  have hUU_HK : ⁅data.U, data.U⁆ ≤ data.H ⊔ K := hUU_M''.trans data.secondDerived_le_fitting
  have hUU_U : ⁅data.U, data.U⁆ ≤ data.U :=
    Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  -- `K ≤ C_M(H) ≤ N(H)`, so `↑(H ⊔ K) = ↑H · ↑K`.
  have hKnorm : K ≤ Subgroup.normalizer data.H :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer (data.H : Set G))
  intro x hx
  have hxU : x ∈ data.U := hUU_U hx
  have hxHK : x ∈ (↑(data.H ⊔ K) : Set G) := hUU_HK hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left data.H K hKnorm] at hxHK
  obtain ⟨h, hh, c, hc, heq⟩ := Set.mem_mul.mp hxHK
  have hcU : c ∈ data.U := (inf_le_left : K ≤ data.U) hc
  have hhU : h ∈ data.U := by
    have hheq : h = x * c⁻¹ := by rw [← heq]; group
    rw [hheq]; exact Subgroup.mul_mem _ hxU (Subgroup.inv_mem _ hcU)
  have hh1 : h = 1 := by
    have hmem : h ∈ data.U ⊓ data.H := ⟨hhU, hh⟩
    rw [inf_comm, typeP_H_inf_U data] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hxc : x = c := by rw [← heq, hh1, one_mul]
  rw [hxc]
  exact (inf_le_right : K ≤ Subgroup.centralizer (data.H : Set G)) hc

end Wielandt93

/-! ### §8 inputs to (9.3)

The two fixed-point-free §8 facts that (9.3) consumes are stated here as named obligations about
the *explicit* type-`P` data of the maximal subgroup, so that (9.3) cites them directly (its proof
body carries no `sorry` of its own).  Each is to be discharged by the §8/§10 local-analysis
development by wiring it to the cited canonical result; doing so makes (9.3) unconditional. -/

/-- Conjugation preserves coatoms (local copy; avoids a cross-area dependency on BG Ch3). -/
private theorem isCoatom_conj_smul {g : G} {M : Subgroup G} (h : IsCoatom M) :
    IsCoatom (MulAut.conj g • M) := by
  have hMeq : M = MulAut.conj g⁻¹ • (MulAut.conj g • M) := by
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  constructor
  · intro htop
    apply h.1
    rw [eq_top_iff]
    intro x _
    have hx : g * x * g⁻¹ ∈ MulAut.conj g • M := by
      rw [htop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    simpa [MulAut.smul_def, mul_assoc] using hx
  · intro b hb
    have hle : M ≤ MulAut.conj g⁻¹ • b := by
      rw [hMeq]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hb.le
    have h1 : M < MulAut.conj g⁻¹ • b := by
      refine lt_of_le_of_ne hle (fun heq => hb.ne ?_)
      rw [heq, ← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    have h2 := h.2 _ h1
    have h3 := congrArg (fun K => MulAut.conj g • K) h2
    simpa [← mul_smul, ← map_mul, mul_inv_cancel] using h3

/-- A maximal subgroup of a minimal simple group is self-normalizing (`N_G(M) = M`): `N_G(M) ⊇ M`
is a coatom, so it is `M` or `⊤`; the latter makes `M` normal, hence `⊥` or `⊤` by simplicity —
impossible for a nontrivial proper maximal subgroup. -/
private theorem maximal_normalizer_eq_self [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Subgroup.normalizer (M : Set G) = M := by
  have hco : IsCoatom M := hM
  refine le_antisymm ?_ Subgroup.le_normalizer
  by_contra hle
  have hlt : M < Subgroup.normalizer (M : Set G) :=
    lt_of_le_of_ne Subgroup.le_normalizer (fun heq => hle heq.ge)
  have hnormal : M.Normal := Subgroup.normalizer_eq_top_iff.mp (hco.2 _ hlt)
  rcases hG.simple.eq_bot_or_eq_top_of_normal M hnormal with hb | ht
  · exact hG.ne_bot_of_isCoatom hco hb
  · exact hco.1 ht

/-- **§8 input to (9.3)** — Peterfalvi (8.6.b II) + (8.12.b): for a maximal subgroup `M` of type II,
the Frobenius kernel `U` acts fixed-point-freely on `H = M_F`, i.e. `C_H(U) = 1`.

*Proof.* If `C_H(U) ≠ 1` then, taking `X = U#` (`C_G(X) = C_G(U)`), Peterfalvi (8.12.b)
(`S10.typeI_or_typeII_centralizer_unique`) makes `M` the unique maximal subgroup containing
`C_G(U)`.  Since `g ∈ N_G(U)` fixes `C_G(U)` (it normalizes `U`), conjugation by `g` carries that
unique maximal to itself, so `g` normalizes `M`; as `M` is self-normalizing,
`N_G(U) ⊆ M`.  This contradicts (8.6.b II) (`S10.typeII_normalizer_not_le_of_typePData`), so
`C_H(U) = 1`. -/
theorem typeII_centralizer_U_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (data : TypePData M) (hM : M ∈ maximalSubgroups G) (hII : IsTypeII M) :
    data.H ⊓ Subgroup.centralizer (data.U : Set G) = ⊥ := by
  by_contra hne
  obtain ⟨dataII⟩ := hII
  -- `data.U ≠ ⊥`: `|U| = [M' : M_F]` is independent of the type-`P` witness, and the `IsTypeII`
  -- witness has `U ≠ 1`.
  have hU_ne : data.U ≠ ⊥ := by
    have hcard : Nat.card ↥data.U = Nat.card ↥dataII.typeP.U := by
      rw [data.card_U_eq_index, dataII.typeP.card_U_eq_index]
    refine fun hbot => dataII.common.1 (Subgroup.card_eq_one.mp ?_)
    rw [← hcard, hbot, Subgroup.card_bot]
  -- `C_G(U#) = C_G(U)` (the identity is centralized by everyone).
  have hCeq : Subgroup.centralizer (sharpSubgroup data.U)
      = Subgroup.centralizer (data.U : Set G) := by
    refine le_antisymm ?_ (Subgroup.centralizer_le Set.diff_subset)
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro h hh
    rcases eq_or_ne h 1 with rfl | h1
    · simp
    · exact hg h ⟨hh, h1⟩
  -- `X = U#` is nonempty and `C_H(X) ≠ 1`, so (8.12.b) makes `M` the unique maximal `∋ C_G(X)`.
  obtain ⟨x, hxU, hx1⟩ := (Subgroup.bot_or_exists_ne_one data.U).resolve_left hU_ne
  have hUleM : data.U ≤ M := data.U_le.trans (Subgroup.map_subtype_le _)
  have hCHne : maxNilpotentNormalHall M ⊓ Subgroup.centralizer (sharpSubgroup data.U) ≠ ⊥ := by
    rw [← data.H_eq, hCeq]; exact hne
  obtain ⟨hCleM, hUniq⟩ :=
    OddOrder.Peterfalvi.S10.typeI_or_typeII_centralizer_unique hG hM (Or.inr ⟨dataII⟩) hUleM
      (sharpSubgroup data.U) ⟨x, hxU, hx1⟩ le_rfl hCHne
  -- `N_G(U) ⊆ M`.
  have hNleM : Subgroup.normalizer (data.U : Set G) ≤ M := by
    intro g hg
    have hgU : MulAut.conj g • data.U = data.U := conj_smul_eq_self_of_mem_normalizer hg
    have hgC : MulAut.conj g • Subgroup.centralizer (sharpSubgroup data.U)
        = Subgroup.centralizer (sharpSubgroup data.U) := by
      rw [centralizer_pointwise_smul, image_sharpSubgroup, hgU]
    have hgM : MulAut.conj g • M = M := by
      have hCle' : Subgroup.centralizer (sharpSubgroup data.U) ≤ MulAut.conj g • M := by
        rw [← hgC]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hCleM
      exact hUniq.eq_of_isCoatom_of_le (isCoatom_conj_smul hM) hCle' hM hCleM
    have hmem : g ∈ Subgroup.normalizer (M : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have key : MulAut.conj g • h ∈ MulAut.conj g • M ↔ h ∈ M :=
        Subgroup.smul_mem_pointwise_smul_iff
      rw [hgM] at key
      simpa [MulAut.smul_def, MulAut.conj_apply] using key.symm
    rwa [maximal_normalizer_eq_self hG hM] at hmem
  exact OddOrder.Peterfalvi.S10.typeII_normalizer_not_le_of_typePData hG data hM ⟨dataII⟩ hNleM

/-- **§8 input to (9.3)** — Peterfalvi Theorem (8.8): for a maximal subgroup `M` of type III or IV,
the order `|W₂|` is prime.

*Discharge route:* (8.8) supplies a type-II maximal `S` with `|S : S'| = |W₂|`
(`OddOrder.Peterfalvi.S12.Hypothesis.exists_typeII_maximal_with_w2`, resting on
`theorem88_caseB_holds`), and a type-II cyclic factor has prime order
(`theorem88_caseB_prime_orders`).  The §8/§12 obligation. -/
theorem typeIIIorIV_W2_prime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (data : TypePData M) (hM : M ∈ maximalSubgroups G)
    (hIIIIV : IsTypeIII M ∨ IsTypeIV M) :
    (Nat.card ↥data.W2).Prime := by
  -- (8.8)/(8.13) for `M` (`S10.exists_typeII_maximal_with_w2_of_typeP`): there is a Type-II maximal
  -- subgroup `S` with `|S : [S,S]| = |W₂|`.  A Type-II maximal's cyclic factor `W₁(S)` has prime
  -- order (8.6.a, carried by `TypePNontrivialCore`) and equals that index
  -- (`card_W1_eq_derived_index`), so `|W₂|` is prime.  (Mirrors `S12.Hypothesis.w2_prime`.)
  obtain ⟨S, -, hSII, hindex⟩ :=
    OddOrder.Peterfalvi.S10.exists_typeII_maximal_with_w2_of_typeP hG data hM
      (hIIIIV.elim Or.inl (fun h => Or.inr (Or.inl h)))
  obtain ⟨dataII⟩ := hSII
  have hcard : Nat.card ↥dataII.typeP.W1 = Nat.card ↥data.W2 := by
    rw [dataII.typeP.card_W1_eq_derived_index]; exact hindex
  rw [← hcard]
  exact dataII.common.2.1

/-- **Peterfalvi (9.3)**: the order and centralizer alternatives for type II
versus types III/IV.

*Proof.* The order relations are the Wielandt fixed-point identity (9.1)
`typeP_wielandt_order_relation` (`|C_H(U W₁)|^q · |H| = |W₂|^q · |C_H(U)|`) specialised by the
fixed-point-free §8 inputs.  For type II, `C_H(U) = 1` (Peterfalvi (8.6.b II)+(8.12.b): a nontrivial
`C_H(U)` would put `N_G(U)` both inside and outside `M`); then `C_H(U W₁) ⊆ C_H(U) = 1` and the
identity gives `|H| = |W₂|^q`.  For types III/IV, `|W₂| = p` is prime (Theorem (8.8): there is a
type-II maximal `S` with `|S : S'| = |W₂|`), and then `C_H(U W₁) = 1` is *derived* from Peterfalvi
(8.5.b) (`typeP_U_not_centralizes_H`): `C_H(U W₁) ⊆ C_H(W₁) = W₂` has order dividing the prime `p`, so
if nontrivial it equals `W₂` and the identity forces `|H| = |C_H(U)|`, i.e. `U` centralizes `H`,
contradicting (8.5.b); the identity then gives `|H| = p^q · |C_H(U)|`.  The remaining §8 obligations
are exactly: type II `C_H(U) = 1`, and types III/IV `|W₂|` prime and `U ≠ 1` — the order arithmetic
and the type III/IV `C_H(U W₁) = 1` reduction are the content discharged here. -/
theorem typeII_III_IV_order_relations [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (data : TypesIIIIIIVSetup M) :
    (IsTypeII M →
      data.H ⊓ Subgroup.centralizer (data.U : Set G) = ⊥ ∧
        Nat.card ↥data.H = Nat.card ↥data.W2 ^ data.q) ∧
      ((IsTypeIII M ∨ IsTypeIV M) →
        ∃ p : ℕ, p.Prime ∧ Nat.card ↥data.W2 = p ∧
          data.H ⊓ Subgroup.centralizer ((data.U ⊔ data.W1 : Subgroup G) : Set G) = ⊥ ∧
          Nat.card ↥data.H =
            p ^ data.q * Nat.card ↥(data.H ⊓ Subgroup.centralizer (data.U : Set G))) := by
  have hH_ne : data.typeP.H ≠ ⊥ := fun heq => data.typeP.H_noncyclic (heq ▸ inferInstance)
  refine ⟨fun _hII => ?_, fun _hIII_IV => ?_⟩
  · -- **Type II.** §8 input: `C_H(U) = 1` (Peterfalvi (8.6.b II) + (8.12.b)), cited as the
    -- `typeII_centralizer_U_eq_bot` obligation.
    have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
    have hCU : data.typeP.H ⊓ Subgroup.centralizer (data.typeP.U : Set G) = ⊥ :=
      typeII_centralizer_U_eq_bot hG data.typeP data.maximal _hII
    -- `C_H(U W₁) ⊆ C_H(U) = 1`.
    have hmono : Subgroup.centralizer ((data.typeP.U ⊔ data.typeP.W1 : Subgroup G) : Set G)
        ≤ Subgroup.centralizer (data.typeP.U : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)
    have hCUW : data.typeP.H
        ⊓ Subgroup.centralizer ((data.typeP.U ⊔ data.typeP.W1 : Subgroup G) : Set G) = ⊥ :=
      le_bot_iff.mp (hCU ▸ inf_le_inf_left data.typeP.H hmono)
    refine ⟨hCU, ?_⟩
    have key := typeP_wielandt_order_relation data.typeP hU
    rwa [hCUW, hCU, Subgroup.card_bot, one_pow, one_mul, mul_one] at key
  · -- **Types III/IV.** Sole §8 input: `|W₂| = p` prime (Theorem (8.8)).  `U ≠ 1` is the setup's
    -- `nontrivial` core, and `C_H(U W₁) = 1` is then *derived* from (8.5.b).
    obtain ⟨p, hp_prime, hpW2⟩ : ∃ p : ℕ, p.Prime ∧ Nat.card ↥data.typeP.W2 = p :=
      ⟨_, typeIIIorIV_W2_prime hG data.typeP data.maximal _hIII_IV, rfl⟩
    have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
    -- `C_H(U W₁) = 1`: it lies in `C_H(W₁) = W₂` of prime order `p`; were it nontrivial it would
    -- equal `W₂`, and Wielandt's identity would force `|H| = |C_H(U)|`, i.e. `U` centralizes `H`,
    -- against (8.5.b) (`typeP_U_not_centralizes_H`).
    have hCUW : data.typeP.H
        ⊓ Subgroup.centralizer ((data.typeP.U ⊔ data.typeP.W1 : Subgroup G) : Set G) = ⊥ := by
      by_contra hne
      have hdvd : Nat.card ↥(data.typeP.H
          ⊓ Subgroup.centralizer ((data.typeP.U ⊔ data.typeP.W1 : Subgroup G) : Set G))
          ∣ Nat.card ↥data.typeP.W2 :=
        Subgroup.card_dvd_of_le (typeP_centralizer_uW1_le_W2 data.typeP)
      have hcardCUW : Nat.card ↥(data.typeP.H
          ⊓ Subgroup.centralizer ((data.typeP.U ⊔ data.typeP.W1 : Subgroup G) : Set G)) = p := by
        rw [hpW2] at hdvd
        refine (hp_prime.eq_one_or_self_of_dvd _ hdvd).resolve_left (fun h1 => hne ?_)
        exact Subgroup.card_eq_one.mp h1
      have key := typeP_wielandt_order_relation data.typeP hU
      rw [hcardCUW, hpW2] at key
      have hHC : Nat.card ↥data.typeP.H
          = Nat.card ↥(data.typeP.H ⊓ Subgroup.centralizer (data.typeP.U : Set G)) :=
        Nat.eq_of_mul_eq_mul_left (pow_pos hp_prime.pos _) key
      have hHleCU : data.typeP.H ≤ Subgroup.centralizer (data.typeP.U : Set G) := by
        have : data.typeP.H ⊓ Subgroup.centralizer (data.typeP.U : Set G) = data.typeP.H :=
          Subgroup.eq_of_le_of_card_ge inf_le_left hHC.le
        rw [← this]; exact inf_le_right
      exact typeP_U_not_centralizes_H data.typeP hU (Subgroup.le_centralizer_iff.mp hHleCU)
    refine ⟨p, hp_prime, hpW2, hCUW, ?_⟩
    have key := typeP_wielandt_order_relation data.typeP hU
    rwa [hCUW, hpW2, Subgroup.card_bot, one_pow, one_mul] at key

/-! ### (9.6): the chief factor `H̄ = H/H₀` has order `p^q`

Given the (9.4) chief factor — an `M`-invariant (equivalently `U W₁`-invariant, as the nilpotent
normal `H = M_F` centralizes every `M`-chief factor of `H`) elementary abelian `p`-section
`H̄ = H/H₀` of `H` on which `U` acts non-trivially and which is `U W₁`-irreducible — Peterfalvi (9.6)
computes `|H̄| = p^q`.  The conjugation action of `U W₁` descends to `H̄` (a coprime Frobenius action),
`C_{H̄}(U) = 1` (the `U W₁`-invariant `C_{H̄}(U) ≠ H̄` must vanish by irreducibility), and Wielandt's
formula gives `|H̄| = |C_{H̄}(W₁)|^q`; as `C_{H̄}(W₁)` is the image of the cyclic `W₂ = C_H(W₁)`
(Isaacs Cor 3.28, `map_fixedSubgroup_eq_fixedSubgroup_quotient`), it is cyclic of order dividing the
exponent `p`, so `|H̄| = p^q`. -/

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)
open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

/-- The fixed subgroup `C_H(K)` of a *normal* subgroup `K ◁ L` under an action `φ : L →* MulAut H`
is `φ`-invariant: `φ` permutes the fixed subgroups `C_H(K)` according to its action on the `K`'s,
and a normal `K` is sent to itself. -/
theorem isAInvariant_fixedSubgroup_of_normal {L H : Type*} [Group L] [Group H]
    (φ : L →* MulAut H) {K : Subgroup L} (hK : K.Normal) :
    IsAInvariant φ (fixedSubgroup φ K) := by
  rw [isAInvariant_iff_smul_mem]
  intro a x hx k hk
  show (φ k) ((φ a) x) = (φ a) x
  have hmem : a⁻¹ * k * a ∈ K := by
    have := hK.conj_mem k hk a⁻¹
    simpa using this
  have hfix : (φ (a⁻¹ * k * a)) x = x := hx _ hmem
  calc (φ k) ((φ a) x)
      = (φ a) ((φ (a⁻¹ * k * a)) x) := by
        simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.apply_inv_self]
    _ = (φ a) x := by rw [hfix]

variable {M : Subgroup G}

/-- The conjugation action of `U W₁` on `H = M_F`, descended to a `U W₁`-invariant quotient
`H̄ = ↥H ⧸ N` (a coprime Frobenius action — the carrier for Wielandt's formula on the chief
factor of (9.4)). -/
noncomputable def typeP_quotientCoprimeAction [Finite G] (data : TypePData M) (hU : data.U ≠ ⊥)
    {N : Subgroup ↥data.H} [N.Normal]
    (hN : IsAInvariant (typeP_conjAction data) N) :
    CoprimeFrobeniusAction ↥(data.U ⊔ data.W1) (↥data.H ⧸ N) where
  U := data.U.subgroupOf (data.U ⊔ data.W1)
  E := data.W1.subgroupOf (data.U ⊔ data.W1)
  frobenius := typeP_uW1_frobenius data hU
  H_solvable := by
    haveI := (typeP_coprimeAction data hU).H_solvable
    exact solvable_of_surjective (QuotientGroup.mk'_surjective N)
  φ := OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN
  coprime_order := Nat.Coprime.coprime_dvd_left (Subgroup.card_quotient_dvd_card N)
    (typeP_coprime_H_uW1 data hU)

/-- A cyclic subgroup `C` of a group of exponent dividing a prime `p` has order dividing `p`:
the generator `g` satisfies `g^p = 1`, so `|C| = orderOf g ∣ p`. -/
theorem card_dvd_prime_of_isCyclic_of_pow {H : Type*} [Group H] {p : ℕ}
    (hexp : ∀ x : H, x ^ p = 1) {C : Subgroup H} (hcyc : IsCyclic ↥C) :
    Nat.card ↥C ∣ p := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgp : g ^ p = 1 := by
    have h := hexp (g : H)
    rw [← Subgroup.coe_pow] at h
    exact Subtype.ext (h.trans (Subgroup.coe_one C).symm)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact orderOf_dvd_of_pow_eq_one hgp

/-- **Chief-factor order via Wielandt's formula** (the arithmetic core of Peterfalvi (9.6),
abstracted from the carrier).  For a coprime Frobenius action `act` (kernel `act.U` normal in `L`,
complement `act.E`) on an elementary abelian `p`-group `K`: if `act` is `L`-irreducible (every
invariant subgroup is `⊥` or `⊤`), `act.U` does not centralize `K` (`fixedByU ≠ ⊤`), the `E`-fixed
points `C_K(E) = fixedByE` are cyclic, and `K ≠ 1`, then `|K| = p^{|E|}` *and* `|C_K(E)| = p`.

`C_K(U) = fixedByU` is `L`-invariant (as `act.U ◁ L`) and `≠ K`, so `= ⊥` by irreducibility;
`|C_K(E)| ∣ p` since `C_K(E)` is cyclic of exponent `p`, and `≠ 1` (else `|K| = |C_K(E)|^{|E|} = 1`
by Wielandt), so `= p`; Wielandt's fixed-point formula then gives `|K| = p^{|E|}`.  The `|C_K(E)| = p`
clause feeds the type III/IV identity `p = |W₂|` (the chief factor's `E`-fixed points are the image
of `W₂`).  This serves both the quotient chief factor `H̄ = ↥H ⧸ N` (`typeP_chiefFactor_card`) and
the irreducible *summand* of the elementary abelian seed in the (9.4) existence proof. -/
theorem coprimeFrobeniusChiefFactor_card {L K : Type*} [Group L] [Group K] [Finite K] [Finite L]
    (act : CoprimeFrobeniusAction L K) (hUnorm : act.U.Normal)
    {p : ℕ} (hp : p.Prime) (hK : IsElementaryAbelian p K)
    (hirr : ∀ J : Subgroup K, IsAInvariant act.φ J → J = ⊥ ∨ J = ⊤)
    (hUntriv : act.fixedByU ≠ ⊤) (hEcyc : IsCyclic ↥act.fixedByE)
    (hK1 : Nat.card K ≠ 1) :
    Nat.card K = p ^ Nat.card ↥act.E ∧ Nat.card ↥act.fixedByE = p := by
  have hUinv : IsAInvariant act.φ act.fixedByU :=
    isAInvariant_fixedSubgroup_of_normal act.φ hUnorm
  have hfixU : act.fixedByU = ⊥ := (hirr _ hUinv).resolve_right hUntriv
  have hdvd : Nat.card ↥act.fixedByE ∣ p := card_dvd_prime_of_isCyclic_of_pow hK.2 hEcyc
  have hcard := coprimeFrobeniusAction_card_eq_prime_pow act hfixU hp hdvd hK1
  refine ⟨hcard, ?_⟩
  have hne : Nat.card ↥act.fixedByE ≠ 1 := fun h => hK1 (by
    have key := wielandt_fixedPoint_trivial_U_fixed act hfixU
    rwa [h, one_pow] at key)
  exact (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hne

/-- **Chief-factor order on an irreducible summand** (the form (9.4)/(9.6) use).  For a coprime
Frobenius action `act` on an elementary abelian `p`-group `V` (kernel `act.U ◁ L`, `C_V(E)` cyclic),
and an `act.φ`-invariant subgroup `S ≠ ⊥` that is `L`-irreducible *inside `V`* (`hirr`) and met
trivially by `C_V(U)` (`hUnc`, so `U` is fixed-point-free on `S`), the order of `S` is `p^{|E|}`,
and `|C_V(E) ⊓ S| = |C_S(E)| = p`.

This is `coprimeFrobeniusChiefFactor_card` transported to the *summand* `S` via the restricted
action `hSinv.restrict` on `↥S`: `S` is elementary abelian (subgroup of `V`); `L`-irreducible
(invariant subgroups of `↥S` correspond, via `S.subtype`, to invariant subgroups of `V` inside `S`);
`U`-noncentral (`C_S(U) = C_V(U) ⊓ S = ⊥ ≠ S`); and `C_S(E) = C_V(E) ⊓ S` is cyclic (subgroup of the
cyclic `C_V(E)`).  Together with the Maschke summand `exists_aInvariant_irreducible_summand_disjoint`
this furnishes the chief factor `|H̄| = p^q` of Peterfalvi (9.4) once the elementary-abelian seed is
in place. -/
theorem coprimeFrobeniusChiefFactor_card_of_summand
    {L V : Type*} [Group L] [Group V] [Finite V] [Finite L]
    (act : CoprimeFrobeniusAction L V) (hUnorm : act.U.Normal)
    {p : ℕ} (hp : p.Prime) (hV : IsElementaryAbelian p V)
    {S : Subgroup V} (hSinv : IsAInvariant act.φ S) (hSne : S ≠ ⊥)
    (hirr : ∀ K : Subgroup V, IsAInvariant act.φ K → K ≤ S → K = ⊥ ∨ K = S)
    (hUnc : act.fixedByU ⊓ S = ⊥) (hEcyc : IsCyclic ↥act.fixedByE) :
    Nat.card ↥S = p ^ Nat.card ↥act.E ∧
      Nat.card ↥(act.fixedByE ⊓ S : Subgroup V) = p := by
  have hSel : IsElementaryAbelian p ↥S := hV.to_subgroup S
  have hSsolv : IsSolvable ↥S := by
    letI : CommGroup ↥S := { (inferInstance : Group ↥S) with mul_comm := hSel.comm }
    infer_instance
  -- the restricted Frobenius action on the summand `↥S`
  let act_S : CoprimeFrobeniusAction L ↥S :=
    { U := act.U
      E := act.E
      frobenius := act.frobenius
      H_solvable := hSsolv
      φ := hSinv.restrict
      coprime_order :=
        Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card S) act.coprime_order }
  -- `L`-irreducibility of `↥S`: invariant subgroups correspond to invariant subgroups of `V ≤ S`.
  have hirr_S : ∀ J : Subgroup ↥S, IsAInvariant act_S.φ J → J = ⊥ ∨ J = ⊤ := by
    intro J hJinv
    rcases hirr (J.map S.subtype) (aInvariant_map_subtype_of_restrict hSinv hJinv)
        (Subgroup.map_subtype_le J) with h | h
    · exact Or.inl (Subgroup.map_injective S.subtype_injective (by rw [h, Subgroup.map_bot]))
    · exact Or.inr (Subgroup.map_injective S.subtype_injective
        (by rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]))
  -- `U` is non-central on `↥S`: `|C_S(U)| = |C_V(U) ⊓ S| = 1 ≠ |S|`.
  have hUntriv_S : act_S.fixedByU ≠ ⊤ := by
    intro htop
    have hc : Nat.card ↥act_S.fixedByU = 1 := by
      have hr := card_fixedSubgroup_restrict (φ := act.φ) (N := S) (X := act.U) hSinv
      rwa [show fixedSubgroup act.φ act.U ⊓ S = ⊥ from hUnc, Subgroup.card_bot] at hr
    rw [htop, Nat.card_congr Subgroup.topEquiv.toEquiv] at hc
    exact hSne (Subgroup.card_eq_one.mp hc)
  -- `C_S(E) = C_V(E) ⊓ S` is a subgroup of the cyclic `C_V(E)`, hence cyclic.
  have hEcyc_S : IsCyclic ↥act_S.fixedByE := by
    haveI : IsCyclic ↥(fixedSubgroup act.φ act.E) := hEcyc
    haveI : IsCyclic ↥(fixedSubgroup act.φ act.E ⊓ S : Subgroup V) :=
      Subgroup.isCyclic_of_le inf_le_left
    have e := Subgroup.equivMapOfInjective
      ((fixedSubgroup act.φ act.E).subgroupOf S) S.subtype S.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype] at e
    have hcyc : IsCyclic ↥((fixedSubgroup act.φ act.E).subgroupOf S) :=
      isCyclic_of_surjective e.symm e.symm.surjective
    show IsCyclic ↥(fixedSubgroup hSinv.restrict act.E)
    rwa [fixedSubgroup_restrict_eq hSinv]
  have hK1 : Nat.card ↥S ≠ 1 := fun h => hSne (Subgroup.card_eq_one.mp h)
  obtain ⟨hScard, hEcard⟩ :=
    coprimeFrobeniusChiefFactor_card act_S hUnorm hp hSel hirr_S hUntriv_S hEcyc_S hK1
  refine ⟨hScard, ?_⟩
  -- `|C_V(E) ⊓ S| = |C_S(E)| = p` via `card_fixedSubgroup_restrict`.
  have hr := card_fixedSubgroup_restrict (φ := act.φ) (N := S) (X := act.E) hSinv
  rw [show fixedSubgroup hSinv.restrict act.E = act_S.fixedByE from rfl, hEcard] at hr
  exact hr.symm

/-- The `E`-fixed points `C_{H̄}(W₁)` of the quotient chief-factor action are cyclic: they are the
image (under `mk' N`, Isaacs Cor 3.28 `map_fixedSubgroup_eq_fixedSubgroup_quotient`) of the cyclic
`W₂ = C_H(W₁)`.  This is the cyclic-`C_K(E)` hypothesis of `coprimeFrobeniusChiefFactor_card` for
both the chief factor (`typeP_chiefFactor_card`) and the (9.4) existence proof. -/
theorem typeP_quotient_fixedByE_cyclic [Finite G] (data : TypePData M) (hU : data.U ≠ ⊥)
    {N : Subgroup ↥data.H} [N.Normal] (hN : IsAInvariant (typeP_conjAction data) N) :
    IsCyclic ↥(typeP_quotientCoprimeAction data hU hN).fixedByE := by
  set act' := typeP_quotientCoprimeAction data hU hN with hact'
  have hcopHW1 : Nat.Coprime
      (Nat.card ↥(data.W1.subgroupOf (data.U ⊔ data.W1))) (Nat.card ↥data.H) :=
    (typeP_coprime_H_uW1 data hU).symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
  haveI : IsSolvable ↥data.H := (typeP_coprimeAction data hU).H_solvable
  have hmap : (fixedSubgroup (typeP_conjAction data)
      (data.W1.subgroupOf (data.U ⊔ data.W1))).map (QuotientGroup.mk' N) = act'.fixedByE :=
    map_fixedSubgroup_eq_fixedSubgroup_quotient hN hcopHW1 (Or.inr inferInstance)
  have hCHW1 : (fixedSubgroup (typeP_conjAction data)
      (data.W1.subgroupOf (data.U ⊔ data.W1))).map data.H.subtype = data.W2 := by
    rw [typeP_fixedSubgroup_map data le_sup_right, typeP_H_inf_centralizer_W1]
  haveI : IsCyclic ↥data.W2 := data.W2_cyclic
  haveI hcycCHW1 : IsCyclic ↥(fixedSubgroup (typeP_conjAction data)
      (data.W1.subgroupOf (data.U ⊔ data.W1))) := by
    have e := Subgroup.equivMapOfInjective
      (fixedSubgroup (typeP_conjAction data) (data.W1.subgroupOf (data.U ⊔ data.W1)))
      data.H.subtype data.H.subtype_injective
    rw [hCHW1] at e
    exact isCyclic_of_surjective e.symm e.symm.surjective
  let f := (QuotientGroup.mk' N).comp (fixedSubgroup (typeP_conjAction data)
      (data.W1.subgroupOf (data.U ⊔ data.W1))).subtype
  have hrange : f.range = act'.fixedByE := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]; exact hmap
  rw [← hrange]
  exact isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective

/-- **Peterfalvi (9.6)** (conditional on the (9.4) chief factor): the order computation
`|H̄| = p^q` for the chief factor `H̄ = ↥H ⧸ N`.

Hypotheses: `N` is a `U W₁`-invariant normal subgroup of `H = M_F` (the (9.4) `H₀`), the quotient
`H̄` is an elementary abelian `p`-group, `H̄` is `U W₁`-irreducible (`hirr`: every invariant subgroup
is `⊥` or `⊤`), `U` does not centralize `H̄` (`hUntriv`), and `H̄ ≠ 1` (`hHbar`).  Then `|H̄| = p^q`.

Proof: `C_{H̄}(U)` is `U W₁`-invariant (`U ◁ U W₁`) and `≠ H̄`, so `= 1` by irreducibility; Wielandt's
formula gives `|H̄| = |C_{H̄}(W₁)|^q`; and `C_{H̄}(W₁)` is the image of the cyclic `W₂ = C_H(W₁)`, hence
cyclic of order dividing the exponent `p`, so `|H̄| = p^q`. -/
theorem typeP_chiefFactor_card [Finite G] (data : TypePData M) (hU : data.U ≠ ⊥)
    {N : Subgroup ↥data.H} [N.Normal] (hN : IsAInvariant (typeP_conjAction data) N)
    {p : ℕ} (hp : p.Prime) (hpe : IsElementaryAbelian p (↥data.H ⧸ N))
    (hirr : ∀ K : Subgroup (↥data.H ⧸ N),
        IsAInvariant (typeP_quotientCoprimeAction data hU hN).φ K → K = ⊥ ∨ K = ⊤)
    (hUntriv : (typeP_quotientCoprimeAction data hU hN).fixedByU ≠ ⊤)
    (hHbar : Nat.card (↥data.H ⧸ N) ≠ 1) :
    Nat.card (↥data.H ⧸ N) = p ^ Nat.card ↥data.W1 := by
  set act' := typeP_quotientCoprimeAction data hU hN with hact'
  have hUnorm : (act'.U).Normal := (typeP_uW1_frobenius data hU).isNormal
  have hEcyc : IsCyclic ↥act'.fixedByE := typeP_quotient_fixedByE_cyclic data hU hN
  -- Wielandt's formula + the prime computation give `|H̄| = p^{|act'.E|} = p^q`.
  have hcard := (coprimeFrobeniusChiefFactor_card act' hUnorm hp hpe hirr hUntriv hEcyc hHbar).1
  rw [hcard]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv

/-- **Peterfalvi (9.4) input**: `U` does not centralize `H = M_F` (in action form): the fixed
subgroup `C_H(U)` of the Frobenius kernel is a *proper* subgroup, `C_H(U) ≠ H`.  This is the
non-centrality that the (9.4) chief factor selection requires; it is the action-level reading of
Peterfalvi (8.5.b) (`typeP_U_not_centralizes_H`): a nontrivial `U` cannot centralize `H`. -/
theorem typeP_U_noncentral_on_H [Finite G] (data : TypePData M) (hU : data.U ≠ ⊥) :
    (typeP_coprimeAction data hU).fixedByU ≠ ⊤ := by
  intro htop
  refine typeP_U_not_centralizes_H data hU (Subgroup.le_centralizer_iff.mp ?_)
  have key := typeP_card_fixedSubgroup data (le_sup_left : data.U ≤ data.U ⊔ data.W1)
  rw [show fixedSubgroup (typeP_conjAction data) (data.U.subgroupOf (data.U ⊔ data.W1))
      = (typeP_coprimeAction data hU).fixedByU from rfl, htop,
    Nat.card_congr Subgroup.topEquiv.toEquiv] at key
  have heq : data.H ⊓ Subgroup.centralizer (data.U : Set G) = data.H :=
    Subgroup.eq_of_le_of_card_ge inf_le_left key.le
  exact heq ▸ inf_le_right

/-- A surjective homomorphic image of an elementary abelian `p`-group is elementary abelian. -/
private theorem isElementaryAbelian_of_surjective {A B : Type*} [Group A] [Group B] {p : ℕ}
    {f : A →* B} (hf : Function.Surjective f) (hA : IsElementaryAbelian p A) :
    IsElementaryAbelian p B := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← map_mul, ← map_mul, hA.comm]
  · obtain ⟨a, rfl⟩ := hf x
    rw [← map_pow, hA.pow_eq_one, map_one]

/-- **Peterfalvi (9.4), the chief-factor kernel** (given the elementary-abelian seed `N₀`).  From a
`U W₁`-invariant normal `N₀ ◁ H = M_F` with `H/N₀` elementary abelian `p` on which `U` is non-central
(`hUnc`), the operator Maschke summand and the summand Wielandt order produce a chief-factor kernel
`N ⊇ N₀` with `|H/N| = p^q` (the chief factor `|H̄|`) and `p ∣ |W₂|`.

`V = H/N₀ = S ⊕ W` (Maschke), `S` irreducible with `U` fixed-point-free (`C_V(U) ⊓ S = ⊥`), so
`|S| = p^q` and `|C_V(W₁) ⊓ S| = p` (`coprimeFrobeniusChiefFactor_card_of_summand`).  Take
`N = W.comap (mk' N₀)`: then `H/N ≅ V/W ≅ S`, so `|H/N| = W.index = |S| = p^q`; and
`p = |C_V(W₁) ⊓ S| ∣ |C_V(W₁)| ∣ |W₂|` since `C_V(W₁)` is the image of `W₂`. -/
theorem exists_chiefFactor_kernel [Finite G] {M : Subgroup G} (data : TypePData M)
    (hU : data.U ≠ ⊥) {p : ℕ} (hp : p.Prime) {N₀ : Subgroup ↥data.H} [N₀.Normal]
    (hN₀ : IsAInvariant (typeP_conjAction data) N₀)
    (hpe : IsElementaryAbelian p (↥data.H ⧸ N₀))
    (hUnc : (typeP_quotientCoprimeAction data hU hN₀).fixedByU ≠ ⊤) :
    ∃ N : Subgroup ↥data.H, N₀ ≤ N ∧ ∃ (hNnorm : N.Normal)
      (hNinv : IsAInvariant (typeP_conjAction data) N),
      Nat.card (↥data.H ⧸ N) = p ^ Nat.card ↥data.W1 ∧ p ∣ Nat.card ↥data.W2 ∧
        (letI := hNnorm
         IsElementaryAbelian p (↥data.H ⧸ N) ∧
           (∀ J : Subgroup (↥data.H ⧸ N),
               IsAInvariant (quotientMulAutHom hNinv) J → J = ⊥ ∨ J = ⊤) ∧
           fixedSubgroup (quotientMulAutHom hNinv)
             (data.U.subgroupOf (data.U ⊔ data.W1)) ≠ ⊤) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set act_V := typeP_quotientCoprimeAction data hU hN₀ with hact_V
  have hUnorm : act_V.U.Normal := (typeP_uW1_frobenius data hU).isNormal
  have hCinv : IsAInvariant act_V.φ act_V.fixedByU :=
    isAInvariant_fixedSubgroup_of_normal act_V.φ hUnorm
  -- Operator Maschke: an irreducible summand `S` with `U`-noncentral complement structure.
  obtain ⟨S, W, hSinv, hWinv, hSW_inf, hSW_sup, hSne, hirr, hCS⟩ :=
    OddOrder.BG.Ch1_Preliminary.exists_aInvariant_irreducible_summand_disjoint hpe
      act_V.coprime_order.symm hCinv hUnc
  have hEcyc : IsCyclic ↥act_V.fixedByE := typeP_quotient_fixedByE_cyclic data hU hN₀
  obtain ⟨hScard, hCSEcard⟩ :=
    coprimeFrobeniusChiefFactor_card_of_summand act_V hUnorm hp hpe hSinv hSne hirr hCS hEcyc
  have hEcard : Nat.card ↥act_V.E = Nat.card ↥data.W1 := by
    show Nat.card ↥(data.W1.subgroupOf (data.U ⊔ data.W1)) = Nat.card ↥data.W1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hScard' : Nat.card ↥S = p ^ Nat.card ↥data.W1 := by rw [hScard, hEcard]
  -- `V` is abelian, so all its subgroups are normal.
  haveI hSnorm : S.Normal := ⟨fun n hn g => by
    rwa [show g * n * g⁻¹ = n by rw [hpe.comm g n]; group]⟩
  haveI hWnorm : W.Normal := ⟨fun n hn g => by
    rwa [show g * n * g⁻¹ = n by rw [hpe.comm g n]; group]⟩
  -- `S` complements `W` in `V`, so `W.index = |S|`.
  have hcompl : Subgroup.IsComplement' S W :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hSW_inf)
      (by rw [← Subgroup.normal_mul, hSW_sup, Subgroup.coe_top])
  set N := W.comap (QuotientGroup.mk' N₀) with hNdef
  -- `N₀ ≤ N`: `N₀ = ker (mk' N₀) ≤ comap _ W`.
  have hN₀leN : N₀ ≤ N := by
    intro x hx
    rw [hNdef, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact W.one_mem
  -- `N` is `U W₁`-invariant (preimage of the invariant `W`); hence normal.
  have hNinv : IsAInvariant (typeP_conjAction data) N :=
    OddOrder.BG.Ch1_Preliminary.isAInvariant_comap_mk' hN₀ hWinv
  haveI hNnorm : N.Normal := inferInstance
  have hNmapW : N.map (QuotientGroup.mk' N₀) = W :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N₀) W
  -- `|H/N| = W.index = |S| = p^q`.
  have hcardN : Nat.card (↥data.H ⧸ N) = p ^ Nat.card ↥data.W1 := by
    show N.index = p ^ Nat.card ↥data.W1
    rw [hNdef, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N₀),
      hcompl.index_eq_card, hScard']
  -- `p ∣ |W₂|`: `p = |C_V(W₁) ⊓ S| ∣ |C_V(W₁)| = |act_V.fixedByE| ∣ |W₂|`.
  have hpW2 : p ∣ Nat.card ↥data.W2 := by
    have h1 : p ∣ Nat.card ↥act_V.fixedByE :=
      hCSEcard ▸ Subgroup.card_dvd_of_le inf_le_left
    refine h1.trans ?_
    set CHW1 := fixedSubgroup (typeP_conjAction data) (data.W1.subgroupOf (data.U ⊔ data.W1))
      with hCHW1def
    have hcopHW1 : Nat.Coprime
        (Nat.card ↥(data.W1.subgroupOf (data.U ⊔ data.W1))) (Nat.card ↥data.H) :=
      (typeP_coprime_H_uW1 data hU).symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
    haveI : IsSolvable ↥data.H := (typeP_coprimeAction data hU).H_solvable
    have hmap : CHW1.map (QuotientGroup.mk' N₀) = act_V.fixedByE :=
      map_fixedSubgroup_eq_fixedSubgroup_quotient hN₀ hcopHW1 (Or.inr inferInstance)
    have hCHW1card : Nat.card ↥CHW1 = Nat.card ↥data.W2 := by
      have hCHW1eq : CHW1.map data.H.subtype = data.W2 := by
        rw [hCHW1def, typeP_fixedSubgroup_map data le_sup_right, typeP_H_inf_centralizer_W1]
      rw [← hCHW1eq]
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective CHW1 data.H.subtype data.H.subtype_injective).toEquiv
    rw [← hmap, ← hCHW1card]
    exact Subgroup.card_map_dvd CHW1 (QuotientGroup.mk' N₀)
  -- shared coprimality / solvability for the fixed-point and quotient-action lemmas.
  have hcopU : Nat.Coprime (Nat.card ↥(data.U.subgroupOf (data.U ⊔ data.W1)))
      (Nat.card ↥data.H) :=
    (typeP_coprime_H_uW1 data hU).symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
  haveI hHsolv : IsSolvable ↥data.H := (typeP_coprimeAction data hU).H_solvable
  -- **Elementary abelian**: `H/N ≅ (H/N₀)/W` is a quotient of the elementary abelian `V = H/N₀`.
  have hEA : IsElementaryAbelian p (↥data.H ⧸ N) := by
    haveI : (N.map (QuotientGroup.mk' N₀)).Normal := hNmapW ▸ hWnorm
    exact IsElementaryAbelian.of_mulEquiv
      (QuotientGroup.quotientQuotientEquivQuotient N₀ N hN₀leN)
      (isElementaryAbelian_of_surjective
        (QuotientGroup.mk'_surjective (N.map (QuotientGroup.mk' N₀))) hpe)
  -- **`C_V(U) ≤ W`**: a `U`-fixed `x = a·b` (`a ∈ S`, `b ∈ W`) has both components `U`-fixed, and
  -- `C_S(U) = C_V(U) ⊓ S = ⊥` kills `a`.
  have hCsubW : act_V.fixedByU ≤ W := by
    letI : CommGroup (↥data.H ⧸ N₀) :=
      { (inferInstance : Group (↥data.H ⧸ N₀)) with mul_comm := hpe.comm }
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (hSW_sup ▸ Subgroup.mem_top x)
    have hxfix : a * b ∈ fixedSubgroup act_V.φ act_V.U := hx
    have hafix : a ∈ act_V.fixedByU := by
      show a ∈ fixedSubgroup act_V.φ act_V.U
      rw [mem_fixedSubgroup]
      intro l hl
      have hxl : act_V.φ l a * act_V.φ l b = a * b := by
        have hf := (mem_fixedSubgroup.mp hxfix) l hl
        rwa [map_mul] at hf
      have hla : act_V.φ l a ∈ S := hSinv.smul_mem l ha
      have hlb : act_V.φ l b ∈ W := hWinv.smul_mem l hb
      have hdiv : act_V.φ l a / a = b / act_V.φ l b := by
        rw [div_eq_div_iff_mul_eq_mul, hxl]; exact mul_comm a b
      have hmem : act_V.φ l a / a ∈ S ⊓ W := ⟨S.div_mem hla ha, hdiv ▸ W.div_mem hb hlb⟩
      rw [hSW_inf, Subgroup.mem_bot, div_eq_one] at hmem
      exact hmem
    have ha1 : a = 1 := by
      have hmem : a ∈ act_V.fixedByU ⊓ S := ⟨hafix, ha⟩
      rw [hCS, Subgroup.mem_bot] at hmem
      exact hmem
    subst ha1
    simpa using hb
  -- `C_H(U) ≤ N` (preimage of `C_V(U) ≤ W`), so `U` is fixed-point-free on `H/N`.
  set CHU := fixedSubgroup (typeP_conjAction data) (data.U.subgroupOf (data.U ⊔ data.W1))
    with hCHUdef
  have hCHU_V : CHU.map (QuotientGroup.mk' N₀) = act_V.fixedByU :=
    map_fixedSubgroup_eq_fixedSubgroup_quotient hN₀ hcopU (Or.inr inferInstance)
  have hCHUleN : CHU ≤ N := by
    rw [hNdef, ← Subgroup.map_le_iff_le_comap, hCHU_V]; exact hCsubW
  have hNonc : fixedSubgroup (quotientMulAutHom hNinv)
      (data.U.subgroupOf (data.U ⊔ data.W1)) ≠ ⊤ := by
    have hfixN : CHU.map (QuotientGroup.mk' N) =
        fixedSubgroup (quotientMulAutHom hNinv) (data.U.subgroupOf (data.U ⊔ data.W1)) :=
      map_fixedSubgroup_eq_fixedSubgroup_quotient hNinv hcopU (Or.inr inferInstance)
    have hbot : fixedSubgroup (quotientMulAutHom hNinv)
        (data.U.subgroupOf (data.U ⊔ data.W1)) = ⊥ := by
      rw [← hfixN, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']; exact hCHUleN
    rw [hbot]
    haveI : Nontrivial (↥data.H ⧸ N) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcardN]
      exact Nat.one_lt_pow Nat.card_pos.ne' hp.one_lt
    exact bot_ne_top
  -- **`U W₁`-irreducibility of `H̄ = H/N`** (the chief factor): pull `J` back to `J̃ ◁ H`
  -- (`N ≤ J̃`), push to `J̄ ≤ V` (`W ≤ J̄`), and split on `J̄ ⊓ S ∈ {⊥, S}`.
  have hIrr : ∀ J : Subgroup (↥data.H ⧸ N),
      IsAInvariant (quotientMulAutHom hNinv) J → J = ⊥ ∨ J = ⊤ := by
    intro J hJinv
    set Jt := J.comap (QuotientGroup.mk' N) with hJtdef
    have hJtinv : IsAInvariant (typeP_conjAction data) Jt :=
      OddOrder.BG.Ch1_Preliminary.isAInvariant_comap_mk' hNinv hJinv
    have hNleJt : N ≤ Jt := by
      intro x hx
      rw [hJtdef, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact J.one_mem
    set Jb := Jt.map (QuotientGroup.mk' N₀) with hJbdef
    have hJbinv : IsAInvariant act_V.φ Jb :=
      OddOrder.BG.Ch1_Preliminary.isAInvariant_map_mk' hN₀ hJtinv
    have hWleJb : W ≤ Jb := by rw [hJbdef, ← hNmapW]; exact Subgroup.map_mono hNleJt
    have hScapinv : IsAInvariant act_V.φ (Jb ⊓ S) := by
      rw [isAInvariant_iff_smul_mem]
      intro l x hx
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨hJbinv.smul_mem l hx.1, hSinv.smul_mem l hx.2⟩
    have hcap : Jb ⊓ S = ⊥ ∨ Jb ⊓ S = S := hirr (Jb ⊓ S) hScapinv inf_le_right
    have hJtcomap : Jt = Jb.comap (QuotientGroup.mk' N₀) := by
      rw [hJbdef, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
        sup_eq_left.mpr (hN₀leN.trans hNleJt)]
    have hJmap : J = Jt.map (QuotientGroup.mk' N) := by
      rw [hJtdef]
      exact (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) J).symm
    rcases hcap with hbotS | htopS
    · -- `J̄ ⊓ S = ⊥`: the component argument gives `J̄ = W`, so `J̃ = N` and `J = ⊥`.
      refine Or.inl ?_
      have hJbleW : Jb ≤ W := by
        letI : CommGroup (↥data.H ⧸ N₀) :=
          { (inferInstance : Group (↥data.H ⧸ N₀)) with mul_comm := hpe.comm }
        intro x hx
        obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (hSW_sup ▸ Subgroup.mem_top x)
        have haJb : a ∈ Jb := by
          have ha_eq : a = a * b / b := by rw [mul_div_assoc, div_self', mul_one]
          rw [ha_eq]; exact Jb.div_mem hx (hWleJb hb)
        have ha1 : a = 1 := by
          have hmem : a ∈ Jb ⊓ S := ⟨haJb, ha⟩
          rw [hbotS, Subgroup.mem_bot] at hmem
          exact hmem
        subst ha1
        simpa using hb
      have hJbW : Jb = W := le_antisymm hJbleW hWleJb
      have hJtN : Jt = N := by rw [hJtcomap, hJbW]
      rw [hJmap, hJtN]
      exact N.map_eq_bot_iff.mpr (le_of_eq (QuotientGroup.ker_mk' N).symm)
    · -- `J̄ ⊓ S = S`: then `S ⊔ W ≤ J̄`, so `J̄ = ⊤`, `J̃ = ⊤`, `J = ⊤`.
      refine Or.inr ?_
      have hSleJb : S ≤ Jb := htopS ▸ inf_le_left
      have hJbtop : Jb = ⊤ := top_le_iff.mp (hSW_sup ▸ sup_le hSleJb hWleJb)
      have hJttop : Jt = ⊤ := by rw [hJtcomap, hJbtop, Subgroup.comap_top]
      rw [hJmap, hJttop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  exact ⟨N, hN₀leN, hNnorm, hNinv, hcardN, hpW2, hEA, hIrr, hNonc⟩

/-- **`M`-normality of the chief-factor kernel image.**  For a `U W₁`-invariant normal subgroup
`N ◁ H = M_F`, its image `H₀ = N.map H.subtype` in `G` is normalized by all of `M`.  Indeed
`M = H ⊔ U ⊔ W₁` (the `M' = H ⋊ U`, `M = M' ⋊ W₁` complement splittings), `H` normalizes `H₀`
(`N ◁ H`, via `Subgroup.le_normalizer_map`), and `U W₁` normalizes `H₀` (`N` is `U W₁`-invariant:
conjugation by `g ∈ U W₁` is `typeP_conjAction` and preserves `N`). -/
theorem typeP_aInvariantNormal_le_normalizer [Finite G] {M : Subgroup G} (data : TypePData M)
    {N : Subgroup ↥data.H} [hNn : N.Normal] (hN : IsAInvariant (typeP_conjAction data) N) :
    M ≤ Subgroup.normalizer ((N.map data.H.subtype : Subgroup G) : Set G) := by
  -- `M ≤ (H ⊔ U) ⊔ W₁`.
  have hM1 : M ≤ derivedInG M ⊔ data.W1 := by
    have hsup := data.M_complement.sup_eq_top
    rw [← Subgroup.subgroupOf_sup (derivedInG_le_self M) data.W1_le] at hsup
    exact Subgroup.subgroupOf_eq_top.mp hsup
  have hderiv : derivedInG M = data.H ⊔ data.U := by
    rw [data.derivedInG_eq_fitting_sup_U, ← data.H_eq]
  have hM2 : M ≤ (data.H ⊔ data.U) ⊔ data.W1 := hderiv ▸ hM1
  -- `H` normalizes `H₀` (`N ◁ H`): `H = subtype '' (normalizer N = ⊤) ≤ normalizer (image)`.
  have hH_norm : data.H ≤ Subgroup.normalizer ((N.map data.H.subtype : Subgroup G) : Set G) := by
    have h := Subgroup.le_normalizer_map (H := N) data.H.subtype
    rwa [Subgroup.normalizer_eq_top_iff.mpr hNn, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
  -- `U W₁` normalizes `H₀`: conjugation by `g ∈ U W₁` is `typeP_conjAction`, which preserves `N`.
  have hconj : ∀ (l : ↥(data.U ⊔ data.W1)) {m : ↥data.H}, m ∈ N →
      (l : G) * data.H.subtype m * (l : G)⁻¹ ∈ N.map data.H.subtype := fun l m hm =>
    ⟨typeP_conjAction data l m, hN.smul_mem l hm, typeP_conjAction_apply data l m⟩
  have hUW1_norm :
      data.U ⊔ data.W1 ≤ Subgroup.normalizer ((N.map data.H.subtype : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    rintro h
    refine ⟨fun ⟨m, hm, hval⟩ => hval ▸ hconj ⟨g, hg⟩ hm, fun hh => ?_⟩
    obtain ⟨m, hm, hval⟩ := hh
    have key := hconj ⟨g, hg⟩⁻¹ hm
    have hE : ((⟨g, hg⟩ : ↥(data.U ⊔ data.W1))⁻¹ : G) * data.H.subtype m
        * (((⟨g, hg⟩ : ↥(data.U ⊔ data.W1))⁻¹ : G))⁻¹ = h := by
      rw [hval]; show g⁻¹ * (g * h * g⁻¹) * (g⁻¹ : G)⁻¹ = h; group
    exact hE ▸ key
  exact hM2.trans (sup_le (sup_le hH_norm (le_sup_left.trans hUW1_norm))
    (le_sup_right.trans hUW1_norm))

/-- A subgroup containing a Sylow `p`-subgroup for every prime `p` is the whole group: its order is
divisible by every maximal prime power `p^{v_p(|G|)} = |Sylow_p|`, hence by `|G|`. -/
theorem eq_top_of_forall_sylow_le {Γ : Type*} [Group Γ] [Finite Γ] {K : Subgroup Γ}
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p Γ), (↑P : Subgroup Γ) ≤ K) : K = ⊤ := by
  refine Subgroup.eq_top_of_card_eq K
    (Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card K) ?_)
  rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    have hdvd : p ^ (Nat.card Γ).factorization p ∣ Nat.card ↥K := by
      have := Subgroup.card_dvd_of_le (h p (default : Sylow p Γ))
      rwa [Sylow.card_eq_multiplicity] at this
    exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
  · simp [Nat.factorization_eq_zero_of_non_prime _ hp]

/-- In a finite **nilpotent** group `H`, a Sylow `p`-subgroup `P` (for a prime `p ∣ |H|`) has a
**characteristic complement** `Q` — the `p`-complement `⨆_{q ≠ p} O_q(H)`.  Each `O_q = opCore q H`
is characteristic; their join is characteristic; the `O_q` have pairwise coprime order hence are
independent (so `O_p` is disjoint from the join of the others); and they jointly generate `H`
(nilpotent), so `Q` complements the normal Sylow `O_p = ↑P`.  Characteristic ⟹ both `Q.Normal`
and (for any operator action) `IsAInvariant`, which is what the (9.4) seed needs. -/
theorem exists_characteristic_complement_to_sylow_of_nilpotent
    {H : Type*} [Group H] [Finite H] [Group.IsNilpotent H]
    {p : ℕ} [Fact p.Prime] (P : Sylow p H) (hp_mem : p ∈ (Nat.card H).primeFactors) :
    ∃ Q : Subgroup H, Q.Characteristic ∧ Subgroup.IsComplement' (↑P : Subgroup H) Q := by
  classical
  set O : (Nat.card H).primeFactors → Subgroup H :=
    fun q => OddOrder.Isaacs.Ch01.opCore (q : ℕ) H with hOdef
  -- The `opCore`'s have pairwise coprime order, hence are independent.
  have hindep : iSupIndep O := by
    apply OddOrder.Isaacs.Ch01.iSupIndep_of_coprime_card_of_normal O
    intro i j hij
    haveI : Fact (i : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors i.2⟩
    haveI : Fact (j : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors j.2⟩
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
    exact IsPGroup.coprime_card_of_ne (i : ℕ) (j : ℕ) hne _ _
      (OddOrder.Isaacs.Ch01.opCore_isPGroup (i : ℕ) H)
      (OddOrder.Isaacs.Ch01.opCore_isPGroup (j : ℕ) H)
  -- `↑P = O ⟨p, hp_mem⟩` (a normal Sylow is the `p`-core).
  have hPnorm : (↑P : Subgroup H).Normal := OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent P
  set i₀ : (Nat.card H).primeFactors := ⟨p, hp_mem⟩ with hi₀
  have hPeq : (↑P : Subgroup H) = O i₀ := OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal P hPnorm
  -- The join of all `opCore`'s is `⊤` (nilpotent: Sylows generate, and each = its `p`-core).
  have htop : (⨆ q, O q) = ⊤ := by
    have hrw : (⨆ q, O q)
        = ⨆ q : (Nat.card H).primeFactors, ((default : Sylow (q : ℕ) H) : Subgroup H) :=
      iSup_congr fun q => by
        haveI : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
        exact (OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal default
          (OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent default)).symm
    rw [hrw]; exact OddOrder.Isaacs.Ch01.iSup_default_sylow_eq_top_of_nilpotent H
  refine ⟨⨆ (j) (_ : j ≠ i₀), O j, ?_, ?_⟩
  · -- characteristic: join of characteristic `opCore`'s.
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    simp_rw [Subgroup.map_iSup]
    exact iSup_congr fun j => iSup_congr fun _ =>
      Subgroup.characteristic_iff_map_eq.mp (OddOrder.Isaacs.Ch01.opCore.characteristic (j : ℕ) H) φ
  · -- complement: disjoint (independence) + join `⊤`.
    rw [hPeq]
    have hdisj : Disjoint (O i₀) (⨆ (j) (_ : j ≠ i₀), O j) := (iSupIndep_def.mp hindep) i₀
    have hsup : O i₀ ⊔ (⨆ (j) (_ : j ≠ i₀), O j) = ⊤ := by
      refine le_antisymm le_top ?_
      rw [← htop]
      refine iSup_le fun j => ?_
      by_cases hj : j = i₀
      · exact hj ▸ le_sup_left
      · exact le_sup_of_le_right (le_iSup₂ (f := fun j (_ : j ≠ i₀) => O j) j hj)
    exact Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Peterfalvi (9.4), the elementary-abelian seed** (the remaining group-theoretic input).
There is a `U W₁`-invariant normal subgroup `N₀ ◁ H = M_F` with `H/N₀` elementary abelian `p`
on which `U` is non-central (`C_H(U) ⊔ N₀ ≠ H`, action-free form).

*Proof.* `H = M_F` is nilpotent and `U` does not centralise it (`typeP_U_noncentral_on_H`).  Since
`C_H(U) ≠ ⊤`, `eq_top_of_forall_sylow_le` produces a Sylow `p`-subgroup `P` with `↑P ⊄ C_H(U)`.  As
`H` is nilpotent, `P = O_p(H)` is characteristic and has a characteristic `p`-complement `Q`
(`exists_characteristic_complement_to_sylow_of_nilpotent`), so `B := H/Q ≅ P` is a `p`-group.  Take
`N₀ = (mk' Q)⁻¹ (Φ(B))`: it is normal, `A`-invariant (`isAInvariant_comap_mk'` + `Φ(B)`
characteristic), and `H/N₀ ≅ B/Φ(B)` is elementary abelian `p`
(`IsPGroup.quotient_frattini_isElementaryAbelian`).  If `C_H(U) ⊔ N₀ = ⊤`, projecting to `B` gives
`C_B(U) ⊔ Φ(B) = ⊤`, so `C_B(U) = ⊤` by the Frattini non-generating property
(`frattini_nongenerating`); then for `x ∈ P`, `(φ l x) x⁻¹ ∈ P ⊓ Q = ⊥`, i.e. `↑P ≤ C_H(U)`,
contradicting the choice of `P`. -/
theorem exists_chiefFactor_seed [Finite G] {M : Subgroup G} (data : TypePData M) (hU : data.U ≠ ⊥) :
    ∃ (p : ℕ) (N₀ : Subgroup ↥data.H) (_ : N₀.Normal), p.Prime ∧
      IsAInvariant (typeP_conjAction data) N₀ ∧
      IsElementaryAbelian p (↥data.H ⧸ N₀) ∧
      fixedSubgroup (typeP_conjAction data) (data.U.subgroupOf (data.U ⊔ data.W1)) ⊔ N₀ ≠ ⊤ := by
  classical
  -- `H = M_F` is nilpotent.
  haveI hHnil : Group.IsNilpotent ↥data.H := by
    rw [data.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent M
  set CU := fixedSubgroup (typeP_conjAction data) (data.U.subgroupOf (data.U ⊔ data.W1)) with hCU
  -- `U` does not centralise `H`: `C_H(U) = CU ≠ ⊤`.
  have hCUtop : CU ≠ ⊤ := typeP_U_noncentral_on_H data hU
  -- A Sylow `p`-subgroup `P` of `H` with `U` non-central on it (`↑P ⊄ CU`).
  obtain ⟨p, hpfact, P, hP_not⟩ :
      ∃ (p : ℕ) (_ : Fact p.Prime) (P : Sylow p ↥data.H),
        ¬ ((↑P : Subgroup ↥data.H) ≤ CU) := by
    by_contra hcon
    push_neg at hcon
    exact hCUtop (eq_top_of_forall_sylow_le hcon)
  haveI := hpfact
  have hp : p.Prime := hpfact.out
  -- `↑P ≠ ⊥` (else `↑P ≤ CU`), so `p ∣ |H|`, i.e. `p ∈ primeFactors |H|`.
  have hPbot : (↑P : Subgroup ↥data.H) ≠ ⊥ := fun h => hP_not (h ▸ bot_le)
  have hp_mem : p ∈ (Nat.card ↥data.H).primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨hp, ?_, Nat.card_pos.ne'⟩
    by_contra hpdvd
    refine hPbot (Subgroup.eq_bot_of_card_eq _ ?_)
    rw [Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hpdvd, pow_zero]
  -- The characteristic `p`-complement `Q` (so `H = P × Q` internally).
  obtain ⟨Q, hQchar, hQcompl⟩ :=
    exists_characteristic_complement_to_sylow_of_nilpotent P hp_mem
  haveI : Q.Characteristic := hQchar
  haveI : Q.Normal := inferInstance
  have hQinv : IsAInvariant (typeP_conjAction data) Q :=
    OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic (typeP_conjAction data)
  -- `↑P` is characteristic (`= O_p(H)`), hence `A`-invariant.
  have hPnorm : (↑P : Subgroup ↥data.H).Normal :=
    OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent P
  haveI hPchar : (↑P : Subgroup ↥data.H).Characteristic := by
    rw [OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal P hPnorm]; infer_instance
  have hPinv : IsAInvariant (typeP_conjAction data) (↑P : Subgroup ↥data.H) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic (typeP_conjAction data)
  -- `B = H/Q` is a `p`-group (`|B| = [H:Q] = |P| = p^k`).
  haveI hBpgroup : IsPGroup p (↥data.H ⧸ Q) :=
    IsPGroup.of_card (by
      calc Nat.card (↥data.H ⧸ Q) = Nat.card (↑P : Subgroup ↥data.H) := hQcompl.index_eq_card
        _ = p ^ (Nat.card ↥data.H).factorization p := Sylow.card_eq_multiplicity P)
  -- `N₀ = (mk' Q)⁻¹ Φ(B)`: normal, `A`-invariant, and `H/N₀ ≅ B/Φ(B)` el. abelian `p`.
  set N₀ := Subgroup.comap (QuotientGroup.mk' Q) (frattini (↥data.H ⧸ Q)) with hN₀
  haveI : N₀.Normal := inferInstance
  have hN₀inv : IsAInvariant (typeP_conjAction data) N₀ :=
    OddOrder.BG.Ch1_Preliminary.isAInvariant_comap_mk' hQinv
      (OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic (quotientMulAutHom hQinv))
  have hQleN₀ : Q ≤ N₀ := by
    intro x hx
    rw [hN₀, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hN₀map : N₀.map (QuotientGroup.mk' Q) = frattini (↥data.H ⧸ Q) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q) _
  have hEA : IsElementaryAbelian p (↥data.H ⧸ N₀) := by
    haveI : (N₀.map (QuotientGroup.mk' Q)).Normal :=
      (inferInstance : N₀.Normal).map _ (QuotientGroup.mk'_surjective Q)
    exact IsElementaryAbelian.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hN₀map).symm.trans
        (QuotientGroup.quotientQuotientEquivQuotient Q N₀ hQleN₀))
      (OddOrder.GroupTheory.IsPGroup.quotient_frattini_isElementaryAbelian hBpgroup)
  refine ⟨p, N₀, inferInstance, hp, hN₀inv, hEA, ?_⟩
  -- Non-centrality `CU ⊔ N₀ ≠ ⊤`.
  intro htop
  have hcopU : Nat.Coprime (Nat.card ↥(data.U.subgroupOf (data.U ⊔ data.W1)))
      (Nat.card ↥data.H) :=
    (typeP_coprime_H_uW1 data hU).symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
  haveI : IsSolvable ↥data.H := (typeP_coprimeAction data hU).H_solvable
  -- Project to `B`: `C_B(U) ⊔ Φ(B) = ⊤`, so by the Frattini argument `C_B(U) = ⊤`.
  have hCUmap := map_fixedSubgroup_eq_fixedSubgroup_quotient
    (φ := typeP_conjAction data) (N := Q) hQinv hcopU (Or.inr inferInstance)
  have hproj : fixedSubgroup (quotientMulAutHom hQinv)
      (data.U.subgroupOf (data.U ⊔ data.W1)) ⊔ frattini (↥data.H ⧸ Q) = ⊤ := by
    rw [← hCUmap, ← hN₀map, ← Subgroup.map_sup, ← hCU, htop,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)]
  have hfix := frattini_nongenerating hproj
  -- Hence `↑P ≤ CU`, contradicting `hP_not`.
  apply hP_not
  intro x hxP
  rw [hCU, mem_fixedSubgroup]
  intro l hl
  -- `mk' Q x` is `U`-fixed in `B`, so `mk' Q (φ l x) = mk' Q x`.
  have hxfix : quotientMulAutHom hQinv l (QuotientGroup.mk' Q x) = QuotientGroup.mk' Q x := by
    have hmem : QuotientGroup.mk' Q x ∈ fixedSubgroup (quotientMulAutHom hQinv)
        (data.U.subgroupOf (data.U ⊔ data.W1)) := by rw [hfix]; exact Subgroup.mem_top _
    exact mem_fixedSubgroup.mp hmem l hl
  rw [quotientMulAutHom_apply_mk'] at hxfix
  -- `(φ l x)⁻¹ * x ∈ Q ∩ ↑P = ⊥`, so `φ l x = x`.
  have hQmem : (typeP_conjAction data l x)⁻¹ * x ∈ Q := by
    rwa [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxfix
  have hPmem : (typeP_conjAction data l x)⁻¹ * x ∈ (↑P : Subgroup ↥data.H) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hPinv.smul_mem l hxP)) hxP
  have hinf : (typeP_conjAction data l x)⁻¹ * x ∈ ((↑P : Subgroup ↥data.H) ⊓ Q) := ⟨hPmem, hQmem⟩
  rw [disjoint_iff.mp hQcompl.disjoint, Subgroup.mem_bot, inv_mul_eq_one] at hinf
  exact hinf

/-- Data for the chief factor `H/H_0` selected in Peterfalvi (9.4).

The chief factor is recorded through the kernel `N ◁ H` (with `H₀ = N.map H.subtype`): `H̄ ≅ ↥H ⧸ N`
is elementary abelian, `U W₁`-irreducible, and not centralized by `U` (the genuine chief-factor
structure produced by `exists_chiefFactorData`). -/
structure ChiefFactorData {M : Subgroup G} (data : TypesIIIIIIVSetup M) where
  H0 : Subgroup G
  H0_lt_H : H0 < data.H
  H0_normalized_by_M : M ≤ Subgroup.normalizer (H0 : Set G)
  p : ℕ
  p_prime : p.Prime
  /-- The chief-factor kernel realized inside `H`: a normal subgroup `N ◁ H` with
  `H₀ = N.map H.subtype`.  The module structure of the chief factor `H̄ = H/H₀` is recorded
  through the isomorphic quotient `↥H ⧸ N`. -/
  N : Subgroup ↥data.H
  [N_normal : N.Normal]
  H0_eq : H0 = N.map data.H.subtype
  /-- `N` is `U W₁`-invariant. -/
  N_aInvariant : IsAInvariant (typeP_conjAction data.typeP) N
  /-- **`H̄ = H/H₀ ≅ ↥H ⧸ N` is elementary abelian `p`.** -/
  quotient_elementaryAbelian : IsElementaryAbelian p (↥data.H ⧸ N)
  /-- **`H̄` is `U W₁`-irreducible** (a chief factor of `M`): every `U W₁`-invariant subgroup of
  `H̄` is `⊥` or `⊤`. -/
  quotient_chiefFactor :
    ∀ J : Subgroup (↥data.H ⧸ N),
      IsAInvariant (quotientMulAutHom (N := N) N_aInvariant) J → J = ⊥ ∨ J = ⊤
  quotient_order : Nat.card ↥data.H = p ^ data.q * Nat.card ↥H0
  typeIII_IV_p_eq_W2 : IsTypeIII M ∨ IsTypeIV M → Nat.card ↥data.W2 = p
  /-- **`U` does not centralize `H̄`** (it acts fixed-point-freely). -/
  U_noncentral_on_quotient :
    fixedSubgroup (quotientMulAutHom (N := N) N_aInvariant)
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) ≠ ⊤

-- Expose the chief-factor kernel's normality as an instance, so that the quotient `↥H ⧸ N` carries
-- its group structure (hence `Subgroup (↥H ⧸ N)` makes sense) wherever a `ChiefFactorData` is in scope.
attribute [instance] ChiefFactorData.N_normal

/-- **Peterfalvi (9.4)**: existence of a nontrivial elementary abelian chief
factor `H/H_0` not centralized by `U`.  Assembles the elementary-abelian seed
(`exists_chiefFactor_seed`), the chief-factor kernel (`exists_chiefFactor_kernel`,
`|H/H₀| = p^q`, `p ∣ |W₂|`), and the `M`-normality of the kernel image
(`typeP_aInvariantNormal_le_normalizer`) into the `ChiefFactorData`. -/
theorem exists_chiefFactorData [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (data : TypesIIIIIIVSetup M) :
    ∃ chief : ChiefFactorData data, chief.H0 < data.H := by
  classical
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  obtain ⟨p, N₀, hN₀norm, hp, hN₀inv, hpe, hUnc_seed⟩ := exists_chiefFactor_seed data.typeP hU
  haveI := hN₀norm
  -- Convert the action-free non-centrality `C_H(U) ⊔ N₀ ≠ H` to the quotient form `fixedByU ≠ ⊤`.
  have hUnc : (typeP_quotientCoprimeAction data.typeP hU hN₀inv).fixedByU ≠ ⊤ := by
    have hcopU : Nat.Coprime
        (Nat.card ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
        (Nat.card ↥data.typeP.H) :=
      (typeP_coprime_H_uW1 data.typeP hU).symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
    haveI : IsSolvable ↥data.typeP.H := (typeP_coprimeAction data.typeP hU).H_solvable
    have hmap := map_fixedSubgroup_eq_fixedSubgroup_quotient (φ := typeP_conjAction data.typeP)
      (N := N₀) (X := data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) hN₀inv hcopU
      (Or.inr inferInstance)
    rw [show (typeP_quotientCoprimeAction data.typeP hU hN₀inv).fixedByU
        = (fixedSubgroup (typeP_conjAction data.typeP)
            (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))).map
            (QuotientGroup.mk' N₀) from hmap.symm]
    intro htop
    refine hUnc_seed ?_
    have hc := congrArg (Subgroup.comap (QuotientGroup.mk' N₀)) htop
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hc
  -- The chief-factor kernel and its image `H₀ = N.map subtype`.
  obtain ⟨N, hN₀leN, hNnorm, hNinv, hcardN, hpW2, hEA, hIrr, hNonc⟩ :=
    exists_chiefFactor_kernel data.typeP hU hp hN₀inv hpe hUnc
  haveI := hNnorm
  have hqpos : Nat.card ↥data.typeP.W1 ≠ 0 := Nat.card_pos.ne'
  have hNtop : N ≠ ⊤ := by
    intro h
    rw [h, show Nat.card (↥data.typeP.H ⧸ (⊤ : Subgroup ↥data.typeP.H)) = 1
      from Subgroup.index_top] at hcardN
    exact (Nat.one_lt_pow hqpos hp.one_lt).ne' hcardN.symm
  have hlt : N.map data.typeP.H.subtype < data.typeP.H :=
    lt_of_le_of_ne (Subgroup.map_subtype_le N) fun heq => hNtop <| by
      apply Subgroup.map_injective data.typeP.H.subtype_injective
      rw [heq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨{ H0 := N.map data.typeP.H.subtype
            H0_lt_H := hlt
            H0_normalized_by_M := typeP_aInvariantNormal_le_normalizer data.typeP hNinv
            p := p
            p_prime := hp
            N := N
            N_normal := hNnorm
            H0_eq := rfl
            N_aInvariant := hNinv
            quotient_elementaryAbelian := hEA
            quotient_chiefFactor := hIrr
            quotient_order := ?_
            typeIII_IV_p_eq_W2 := ?_
            U_noncentral_on_quotient := hNonc }, hlt⟩
  · -- `|H| = |H/N| · |N| = p^q · |H₀|`.
    show Nat.card ↥data.typeP.H
        = p ^ Nat.card ↥data.typeP.W1 * Nat.card ↥(N.map data.typeP.H.subtype)
    rw [← Subgroup.index_mul_card N,
      show N.index = p ^ Nat.card ↥data.typeP.W1 from hcardN,
      Nat.card_congr (Subgroup.equivMapOfInjective N data.typeP.H.subtype
        data.typeP.H.subtype_injective).toEquiv]
  · -- `p = |W₂|` for type III/IV: `p ∣ |W₂|` and `|W₂|` is prime.
    intro hIIIIV
    exact ((Nat.prime_dvd_prime_iff_eq hp
      (typeIIIorIV_W2_prime hG data.typeP data.maximal hIIIIV)).mp hpW2).symm

/-! ## (9.5)--(9.7): Clifford-theory data over the selected chief factor -/

/-! ### The genuine character families `𝒳`, `𝒮` of Peterfalvi (9.5)

We realise Peterfalvi's families honestly (following the `S12.inducedFamily` pattern), so the
formerly free `Section11CharacterData` fields are pinned to genuine constructions.  `HU = H ⊔ U`
is realised inside `↥M` as `(H ⊔ U).subgroupOf M`; then

* `𝒳 = {χ ∈ Irr(HU) | H ⊄ Ker χ}` (`xiSet`),
* `𝒮 = {Ind_{HU}^M χ | χ ∈ 𝒳}` (`sSet`),

with the restricted families `𝒳(Y) = {χ ∈ 𝒳 | Y ⊆ Ker χ}` (`xiOf`) and `𝒮(Y) = Ind 𝒳(Y)` (`sOf`)
for a subgroup `Y` (the cases `Y = H₀, H₀C, H₀C', H₀U'` of (9.8)/(9.9)). -/

/-- `HU = H ⊔ U`, realised as a subgroup of `↥M`. -/
def huSub (data : TypesIIIIIIVSetup M) : Subgroup ↥M :=
  (data.H ⊔ data.U).subgroupOf M

/-- `HU = H ⊔ U` is exactly the derived subgroup `M' = derivedInG M` realised inside `↥M`
(Peterfalvi (9.2): `M' = HU`).  This identifies the §9 induction carrier `huSub data` with the
`(derivedInG M).subgroupOf M` whose `mk'`-image is the `K` of the `M/H₀`-`Hypothesis`
(`chiefFactorQuotientHypothesis`), the bridge from the §9 family to the §6 reducible count
(issue 1012, B2 bijection). -/
theorem huSub_eq_derivedInG_subgroupOf (data : TypesIIIIIIVSetup M) :
    huSub data = (derivedInG M).subgroupOf M := by
  have h : data.H ⊔ data.U = derivedInG M := by
    rw [data.typeP.derivedInG_eq_fitting_sup_U, ← data.typeP.H_eq]; rfl
  rw [huSub, h]

/-- **`HU ◁ M`**: `HU = H ⊔ U = M' = [M,M]` is the derived subgroup realised inside `↥M`, hence
normal.  This is the `H ⊴ G` hypothesis letting the §9 induction `induceHU = Ind_{HU}^M` use the
Clifford fibre/orbit machinery (`induce_eq_induce_iff_conj`: distinct `M`-conjugacy orbits ↔ distinct
inductions) for the `𝒳 ↔ 𝒮` count of Peterfalvi (9.5)/(9.9). -/
instance huSub_normal (data : TypesIIIIIIVSetup M) : (huSub data).Normal := by
  rw [huSub_eq_derivedInG_subgroupOf, show (derivedInG M).subgroupOf M = commutator ↥M by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]]
  infer_instance

/-- `H`, realised as a subgroup of `HU = H ⊔ U` inside `↥M`.  Used to state the kernel condition
`H ⊄ Ker χ` defining `𝒳`. -/
def hInHu (data : TypesIIIIIIVSetup M) : Subgroup ↥(huSub data) :=
  (data.H.subgroupOf M).subgroupOf (huSub data)

/-- **Peterfalvi (9.5)'s family `𝒳`**: the irreducible characters of `HU = H ⊔ U` (realised inside
`↥M`) that do not contain `H` in their kernel. -/
def xiSet (data : TypesIIIIIIVSetup M) : Set (IrreducibleCharacter ↥(huSub data)) :=
  { χ | ¬ ((hInHu data : Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ)) }

/-- **Peterfalvi (9.5)'s family `𝒳(Y)`**: the members of `𝒳` containing `Y` in their kernel.  For
`Y ≤ HU`, `Y` is realised inside `HU` as `(Y.subgroupOf M).subgroupOf (huSub data)`. -/
def xiOf (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    Set (IrreducibleCharacter ↥(huSub data)) :=
  { χ ∈ xiSet data | ((Y.subgroupOf M).subgroupOf (huSub data) : Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ) }

theorem xiOf_subset_xiSet (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    xiOf data Y ⊆ xiSet data :=
  fun _ h => h.1

theorem mem_xiOf {data : TypesIIIIIIVSetup M} {Y : Subgroup G}
    {χ : IrreducibleCharacter ↥(huSub data)} :
    χ ∈ xiOf data Y ↔ χ ∈ xiSet data ∧
      ((Y.subgroupOf M).subgroupOf (huSub data) : Set ↥(huSub data)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ) :=
  Iff.rfl

/-- `𝒳(Y)` is antitone in `Y`: a larger kernel demand `Y ⊆ Ker χ` selects fewer characters. -/
theorem xiOf_antitone (data : TypesIIIIIIVSetup M) {Y Y' : Subgroup G} (hY : Y ≤ Y') :
    xiOf data Y' ⊆ xiOf data Y := fun _ hχ =>
  ⟨hχ.1, subset_trans (SetLike.coe_subset_coe.mpr
    (Subgroup.subgroupOf_mono (huSub data) (Subgroup.subgroupOf_mono M hY))) hχ.2⟩

/-- `Ind_{HU}^M χ`, the induction of a class function of `HU = H ⊔ U` to `↥M`.  The required
`Invertible (Nat.card ↥HU : ℂ)` is constructed from `[Finite G]` and baked in here so that `sSet`
and `sOf` share one canonical instance (avoiding the induce-instance desync). -/
noncomputable def induceHU [Finite G] (data : TypesIIIIIIVSetup M)
    (χ : ClassFunction ↥(huSub data) ℂ) : ClassFunction ↥M ℂ :=
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  ClassFunction.induce (huSub data) χ

/-- The induced degree: `(Ind_{HU}^M χ)(1) = [M : HU] · χ(1)` (Peterfalvi's `Ind` raises degrees by
the index `[M : HU]`). -/
theorem induceHU_apply_one [Finite G] (data : TypesIIIIIIVSetup M)
    (χ : ClassFunction ↥(huSub data) ℂ) :
    induceHU data χ (1 : ↥M) = ((huSub data).index : ℂ) * χ (1 : ↥(huSub data)) := by
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact ClassFunction.induce_apply_one (huSub data) χ

/-- **`[M : HU] = q = |W₁|`.**  `HU = H ⊔ U = M' = derivedInG M` (the type-`P` complementarity
`derived_complement`, `derivedInG_eq_fitting_sup_U`), and `W₁` complements `M'` in `M`
(`M_complement`), so `[M : HU] = [M : M'] = |W₁| = q`.  This pins the index that
`induceHU_apply_one` leaves abstract: every `𝒮`-member `Ind_{HU}^M χ` has degree `q · χ(1)`. -/
theorem huSub_index_eq_q [Finite G] (data : TypesIIIIIIVSetup M) :
    (huSub data).index = data.q := by
  have hsup : data.H ⊔ data.U = derivedInG M := by
    simp only [TypesIIIIIIVSetup.H, TypesIIIIIIVSetup.U]
    rw [data.typeP.derivedInG_eq_fitting_sup_U, data.typeP.H_eq]
  have hidx : ((derivedInG M).subgroupOf M).index = data.q := by
    simp only [TypesIIIIIIVSetup.q, TypesIIIIIIVSetup.W1]
    rw [data.typeP.M_complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeP.W1_le).toEquiv]
  show ((data.H ⊔ data.U).subgroupOf M).index = data.q
  rw [hsup]; exact hidx

/-- The induced degree, with the index resolved: `(Ind_{HU}^M χ)(1) = q · χ(1)` (`q = |W₁|`).  This
is the degree formula the §9 counts (9.8)/(9.9) use directly (`𝒮`-members of source degree `s` have
degree `q·s`, e.g. `qu`, `qa`). -/
theorem induceHU_apply_one_eq_q_mul [Finite G] (data : TypesIIIIIIVSetup M)
    (χ : ClassFunction ↥(huSub data) ℂ) :
    induceHU data χ (1 : ↥M) = (data.q : ℂ) * χ (1 : ↥(huSub data)) := by
  rw [induceHU_apply_one, huSub_index_eq_q]

/-- **Peterfalvi (9.5)'s family `𝒮`**: `{Ind_{HU}^M χ | χ ∈ 𝒳}`. -/
noncomputable def sSet [Finite G] (data : TypesIIIIIIVSetup M) : Set (ClassFunction ↥M ℂ) :=
  { φ | ∃ χ ∈ xiSet data, φ = induceHU data (χ : ClassFunction ↥(huSub data) ℂ) }

/-- **Peterfalvi (9.5)'s family `𝒮(Y)`**: `{Ind_{HU}^M χ | χ ∈ 𝒳(Y)}`. -/
noncomputable def sOf [Finite G] (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    Set (ClassFunction ↥M ℂ) :=
  { φ | ∃ χ ∈ xiOf data Y, φ = induceHU data (χ : ClassFunction ↥(huSub data) ℂ) }

theorem mem_sSet [Finite G] {data : TypesIIIIIIVSetup M} {φ : ClassFunction ↥M ℂ} :
    φ ∈ sSet data ↔ ∃ χ ∈ xiSet data, φ = induceHU data (χ : ClassFunction ↥(huSub data) ℂ) :=
  Iff.rfl

theorem mem_sOf [Finite G] {data : TypesIIIIIIVSetup M} {Y : Subgroup G}
    {φ : ClassFunction ↥M ℂ} :
    φ ∈ sOf data Y ↔ ∃ χ ∈ xiOf data Y, φ = induceHU data (χ : ClassFunction ↥(huSub data) ℂ) :=
  Iff.rfl

/-- `𝒮(Y) ⊆ 𝒮`: every character induced from `𝒳(Y)` is induced from `𝒳` (since `𝒳(Y) ⊆ 𝒳`). -/
theorem sOf_subset_sSet [Finite G] (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    sOf data Y ⊆ sSet data := fun _ ⟨χ, hχ, hφ⟩ =>
  ⟨χ, xiOf_subset_xiSet data Y hχ, hφ⟩

/-- `𝒮(Y)` is antitone in `Y` (inherited from `xiOf_antitone`). -/
theorem sOf_antitone [Finite G] (data : TypesIIIIIIVSetup M) {Y Y' : Subgroup G} (hY : Y ≤ Y') :
    sOf data Y' ⊆ sOf data Y := fun _ ⟨χ, hχ, hφ⟩ =>
  ⟨χ, xiOf_antitone data hY hχ, hφ⟩

/-- Every `𝒮`-member is a genuine virtual character of `M`: `Ind_{HU}^M χ ∈ ℤ[Irr M]` for
`χ ∈ Irr(HU)` (`ClassFunction.induce_mem_ZIrr`).  This is the foundation on which the (9.8)/(9.9)
degree and inner-product counts treat `𝒮`-members as characters. -/
theorem induceHU_mem_ZIrr [Finite G] (data : TypesIIIIIIVSetup M)
    (χ : IrreducibleCharacter ↥(huSub data)) :
    induceHU data (χ : ClassFunction ↥(huSub data) ℂ) ∈ ZIrr ↥M := by
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact ClassFunction.induce_mem_ZIrr (huSub data) χ.mem_ZIrr

/-- `𝒮 ⊆ ℤ[Irr M]`: the whole induced family consists of virtual characters of `M`. -/
theorem sSet_subset_ZIrr [Finite G] (data : TypesIIIIIIVSetup M) :
    sSet data ⊆ (ZIrr ↥M : Set (ClassFunction ↥M ℂ)) := by
  rintro _ ⟨χ, -, rfl⟩
  exact induceHU_mem_ZIrr data χ

/-! ### The genuine subgroups `C = C_U(H̄)`, `U' = [U,U]`, `C' = [C,C]` of Peterfalvi (9.5) -/

/-- The `U`-action on the chief factor `H̄ = ↥H ⧸ N` (Peterfalvi (9.5)), as the hom from `U` (realised
inside `U ⊔ W₁`) to `Aut(H̄)`.  Its range has order `u` (`u_eq_card_quotient`); its kernel is
`C = C_U(H̄)`. -/
noncomputable def uActionHom (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :=
  (quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
    (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype

/-- **Peterfalvi's `C = C_U(H̄)`** (9.5): the kernel of the `U`-action on the chief factor `H̄`,
realised as a subgroup of `G` with `C ≤ U`.  By the first isomorphism theorem `|U : C| = u`
(`u_eq_card_quotient`'s range). -/
noncomputable def cSub (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) : Subgroup G :=
  ((uActionHom data chief).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
    (data.typeP.U ⊔ data.typeP.W1).subtype

theorem cSub_le_U (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    cSub data chief ≤ data.U :=
  (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans <| by
    rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left

/-- **Peterfalvi's `U' = [U, U]`** (9.5), realised in `G` as `derivedInG U`. -/
def uprimeSub (data : TypesIIIIIIVSetup M) : Subgroup G := derivedInG data.U

theorem uprimeSub_le_U (data : TypesIIIIIIVSetup M) : uprimeSub data ≤ data.U :=
  Subgroup.map_subtype_le _

/-- **Peterfalvi's `C' = [C, C]`** (9.5), realised in `G` as `derivedInG C`. -/
noncomputable def cprimeSub (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) : Subgroup G :=
  derivedInG (cSub data chief)

theorem cprimeSub_le_C (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    cprimeSub data chief ≤ cSub data chief :=
  Subgroup.map_subtype_le _

open Subgroup in
/-- **`C = C_U(H̄) ◁ U`** (Peterfalvi (9.5)): the kernel of the `U`-action on the chief factor is
normal in `U`.  `cSub` is the `G`-image of `(uActionHom).ker`, which corresponds (via the
realization iso `subgroupOfEquivOfLe : ↥(U.subgroupOf (U ⊔ W₁)) ≃* ↥U`) to a kernel of a
homomorphism out of `↥U`; kernels are normal.  This is the `C ◁ U` input of the (9.9.a) carrier
normality `HC ◁ HU` (`sup_normal_of_normal_left_of_normal_subgroupOf`). -/
theorem cSub_subgroupOf_U_normal (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    ((cSub data chief).subgroupOf data.U).Normal := by
  set e := subgroupOfEquivOfLe (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1) with he
  have heq : (cSub data chief).subgroupOf data.U
      = (uActionHom data chief).ker.map e.toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      simp only [cSub, Subgroup.mem_map] at hx
      obtain ⟨z, ⟨y, hy, hyz⟩, hzx⟩ := hx
      refine ⟨y, hy, ?_⟩
      apply Subtype.ext
      rw [MulEquiv.coe_toMonoidHom, he, subgroupOfEquivOfLe_apply_coe, ← hzx, ← hyz]
      rfl
    · rintro ⟨y, hy, rfl⟩
      simp only [cSub, Subgroup.mem_map]
      refine ⟨_, ⟨y, hy, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, he, subgroupOfEquivOfLe_apply_coe]
      rfl
  rw [heq]
  exact (MonoidHom.normal_ker _).map e.toMonoidHom e.surjective

/-- **`U W₁ ≤ N_G(C)`** (the `W₁`-half of the `H₀C ◁ M` normality, issue 1012): the `U W₁`-action on
the chief factor `H̄ = ↥H ⧸ N` is defined on *all* of `U ⊔ W₁` (`quotientMulAutHom`, built from
`typeP_conjAction : U ⊔ W₁ → MulAut ↥H`), so `C = C_U(H̄)` realises inside `L = ↥(U ⊔ W₁)` as the
intersection `U' ⊓ ker(quotientMulAutHom)` of two `L`-normal subgroups (`U' = U.subgroupOf L` normal
by the Frobenius structure `typeP_uW1_frobenius`, the action kernel normal as a kernel).  A normal
subgroup of `L` is normalized by all of `L = ↑(U ⊔ W₁)` once pushed forward along `L.subtype`
(`le_normalizer_map`, `normalizer_eq_top`).  Unlike the `H`-conjugation (which only gives
`[C, H] ≤ H₀`, i.e. `H ≤ N(H₀C)` not `H ≤ N(C)`), `W₁` normalizes `C` *exactly*. -/
theorem cSub_normalized_by_uW1 [Finite G] (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    data.typeP.U ⊔ data.typeP.W1 ≤ Subgroup.normalizer (cSub data chief : Set G) := by
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  haveI hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal :=
    (typeP_uW1_frobenius data.typeP hU).isNormal
  haveI hKnorm : (quotientMulAutHom chief.N_aInvariant).ker.Normal := MonoidHom.normal_ker _
  haveI hInfNorm : ((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
      ⊓ (quotientMulAutHom chief.N_aInvariant).ker).Normal :=
    Subgroup.normal_inf_normal _ _
  -- `C` realised in `L = ↥(U ⊔ W₁)` is `U' ⊓ ker(quotientMulAutHom)`.
  have hinner : (uActionHom data chief).ker.map
        (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype
      = (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
          ⊓ (quotientMulAutHom chief.N_aInvariant).ker := by
    rw [show (uActionHom data chief).ker
          = (quotientMulAutHom chief.N_aInvariant).ker.comap
              (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype from
        (MonoidHom.comap_ker _ _).symm,
      Subgroup.map_comap_eq, Subgroup.range_subtype]
  have hcSub : cSub data chief
      = ((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
            ⊓ (quotientMulAutHom chief.N_aInvariant).ker).map
          (data.typeP.U ⊔ data.typeP.W1).subtype := by
    unfold cSub
    rw [hinner]
  rw [hcSub]
  have h1 := Subgroup.le_normalizer_map
    (H := (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
      ⊓ (quotientMulAutHom chief.N_aInvariant).ker)
    (data.typeP.U ⊔ data.typeP.W1).subtype
  rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1

/-! ### (9.9.a) realization: `HC ◁ HU` (the inertia subgroup is normal)

For the (9.9.a) Clifford degree `χ(1) = u` we induce from the inertia subgroup `HC` of a chief-factor
character; `isIrreducibleCharacter_induce_of_inertia_eq` requires `HC ◁ HU`.  We realize `U` and
`C = C_U(H̄)` inside `HU = huSub` and apply the abstract
`sup_normal_of_normal_left_of_normal_subgroupOf` (`H ◁ HU` from `hInHu_normal`, `C ◁ U` from
`cSub_subgroupOf_U_normal`, `H ⊔ U = ⊤`). -/

/-- `H ⊴ HU`: the realization `hInHu data = (H.subgroupOf M).subgroupOf HU` of `H = M_F` inside
`HU` is normal (`M_F ◁ M`, descended along the inclusions). -/
instance hInHu_normal {M : Subgroup G} (data : TypesIIIIIIVSetup M) :
    (hInHu data).Normal := by
  have h1 : (data.H.subgroupOf M).Normal := by
    rw [show data.H = maxNilpotentNormalHall M from data.typeP.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal M
  exact h1.subgroupOf (huSub data)

theorem U_le_M (data : TypesIIIIIIVSetup M) : data.U ≤ M :=
  data.typeP.U_le.trans (Subgroup.map_subtype_le _)

theorem H_le_M (data : TypesIIIIIIVSetup M) : data.H ≤ M :=
  data.typeP.H_le.trans (Subgroup.map_subtype_le _)

/-- `U`, realized as a subgroup of `HU = H ⊔ U` inside `↥M`. -/
noncomputable def uInHu (data : TypesIIIIIIVSetup M) : Subgroup ↥(huSub data) :=
  (data.U.subgroupOf M).subgroupOf (huSub data)

/-- `C = C_U(H̄)`, realized as a subgroup of `HU` inside `↥M`. -/
noncomputable def cInHu (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    Subgroup ↥(huSub data) :=
  ((cSub data chief).subgroupOf M).subgroupOf (huSub data)

theorem cInHu_le_uInHu (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    cInHu data chief ≤ uInHu data :=
  Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ (cSub_le_U data chief))

open Subgroup in
/-- **`C ◁ U` inside `HU`** (realized form): `cInHu ◁ uInHu`, transported from `cSub ◁ U`
(`cSub_subgroupOf_U_normal`) along the realization iso `↥uInHu ≃* ↥U`.  Comap of a normal subgroup
is normal. -/
theorem cInHu_normal (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    ((cInHu data chief).subgroupOf (uInHu data)).Normal := by
  have hUsubM : data.U.subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_sup_right : data.U ≤ data.H ⊔ data.U)
  set f : ↥(uInHu data) ≃* ↥data.U :=
    (subgroupOfEquivOfLe hUsubM).trans (subgroupOfEquivOfLe (U_le_M data)) with hf
  have hgval : ∀ x : ↥(uInHu data), ((f x : ↥data.U) : G) = (((x : ↥(huSub data)) : ↥M) : G) := by
    intro x
    have h1 : (f x : ↥data.U)
        = subgroupOfEquivOfLe (U_le_M data) (subgroupOfEquivOfLe hUsubM x) := by rw [hf]; rfl
    rw [h1, subgroupOfEquivOfLe_apply_coe, subgroupOfEquivOfLe_apply_coe]
  have hcomap : (cInHu data chief).subgroupOf (uInHu data)
      = ((cSub data chief).subgroupOf data.U).comap f.toMonoidHom := by
    ext x
    simp only [cInHu, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, hgval x]
  rw [hcomap]
  exact (cSub_subgroupOf_U_normal data chief).comap f.toMonoidHom

open Subgroup in
/-- **`H ⊔ U = ⊤` inside `HU`** (realized form): `hInHu ⊔ uInHu = ⊤`, since `HU = H ⊔ U`.  Both
`H.subgroupOf M` and `U.subgroupOf M` lie below `huSub = (H ⊔ U).subgroupOf M`, and `subgroupOf`
distributes over `⊔` for subgroups below the ambient (`subgroupOf_sup`), so the realized join is
`((H ⊔ U).subgroupOf M).subgroupOf (huSub) = huSub.subgroupOf huSub = ⊤`. -/
theorem hInHu_sup_uInHu_eq_top (data : TypesIIIIIIVSetup M) :
    hInHu data ⊔ uInHu data = ⊤ := by
  have hHsub : data.H.subgroupOf M ≤ huSub data := Subgroup.subgroupOf_mono M le_sup_left
  have hUsub : data.U.subgroupOf M ≤ huSub data := Subgroup.subgroupOf_mono M le_sup_right
  unfold hInHu uInHu
  rw [← subgroupOf_sup hHsub hUsub, ← subgroupOf_sup (H_le_M data) (U_le_M data)]
  exact Subgroup.subgroupOf_self _

/-- **Peterfalvi (9.9.a), the inertia subgroup is normal: `HC ◁ HU`.**  Realized as
`hInHu ⊔ cInHu ◁ huSub`, by the abstract `sup_normal_of_normal_left_of_normal_subgroupOf`:
`H ◁ HU` (`hInHu_normal`), `C ◁ U` (`cInHu_normal`), `H ⊔ U = ⊤` (`hInHu_sup_uInHu_eq_top`).  This is
the normality `isIrreducibleCharacter_induce_of_inertia_eq` needs to make `Ind_{HC}^{HU} ψ`
irreducible in the (9.9.a) Clifford-degree argument. -/
theorem hcInHu_normal (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    (hInHu data ⊔ cInHu data chief).Normal :=
  haveI := hInHu_normal data
  haveI := cInHu_normal data chief
  sup_normal_of_normal_left_of_normal_subgroupOf (cInHu_le_uInHu data chief)
    (hInHu_sup_uInHu_eq_top data)

section
open scoped IsMulCommutative

/-- **`H ⊓ U ≤ C = C_U(H̄)`** (realized form `hInHu ⊓ uInHu ≤ cInHu`).  An element lying in both
`H` and `U` centralizes the chief factor `H̄ = H/H₀`: conjugation by an `H`-element descends to an
inner automorphism of the *abelian* `H̄`, hence is trivial, so the element lies in
`C = ker(U → Aut H̄)`.  This is the index input of (9.9.a)'s `[HU : HC] = u`. -/
theorem hInHu_inf_uInHu_le_cInHu [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    hInHu data ⊓ uInHu data ≤ cInHu data chief := by
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  intro x hx
  obtain ⟨hxH, hxU⟩ := hx
  have hgH : (((x : ↥(huSub data)) : ↥M) : G) ∈ data.H := by
    simp only [hInHu, Subgroup.mem_subgroupOf] at hxH; exact hxH
  have hgU : (((x : ↥(huSub data)) : ↥M) : G) ∈ data.typeP.U := by
    simp only [uInHu, Subgroup.mem_subgroupOf] at hxU; exact hxU
  have hgUW1 : (((x : ↥(huSub data)) : ↥M) : G) ∈ data.typeP.U ⊔ data.typeP.W1 :=
    Subgroup.mem_sup_left hgU
  -- the `U`-action element with the same `G`-coordinate
  set a : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
    ⟨⟨(((x : ↥(huSub data)) : ↥M) : G), hgUW1⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha_def
  -- `a ∈ ker(uActionHom)`: conjugation by an `H`-element is trivial on the abelian `H̄`.
  have hker : a ∈ (uActionHom data chief).ker := by
    rw [MonoidHom.mem_ker]
    ext q
    induction q using QuotientGroup.induction_on with
    | _ h =>
      rw [uActionHom, MonoidHom.comp_apply,
        OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply,
        MulAut.one_apply]
      have hconj : (typeP_conjAction data.typeP
          ((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype a) h)
          = (⟨_, hgH⟩ : ↥data.H) * h * (⟨_, hgH⟩ : ↥data.H)⁻¹ := by
        apply Subtype.ext
        rw [typeP_conjAction_apply]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rfl
      rw [hconj]
      simp only [← QuotientGroup.mk'_apply, map_mul, map_inv]
      rw [mul_comm (QuotientGroup.mk' chief.N ⟨_, hgH⟩) (QuotientGroup.mk' chief.N h),
        mul_assoc, mul_inv_cancel, mul_one]
  simp only [cInHu, Subgroup.mem_subgroupOf, cSub, Subgroup.mem_map]
  exact ⟨_, ⟨a, hker, rfl⟩, rfl⟩

end

/-- **`U ⊓ HC = C`** (realized: `uInHu ⊓ (hInHu ⊔ cInHu) = cInHu`).  The `U`-part of the inertia
subgroup `HC` is exactly `C`.  `⊇` is `C ≤ U` and `C ≤ HC`; `⊆` decomposes `x = h·c`
(`H ◁ HU`, `mem_sup_of_normal_left`) with `c ∈ C ≤ U`, so `h = x·c⁻¹ ∈ U`, whence
`h ∈ H ⊓ U ≤ C` (`hInHu_inf_uInHu_le_cInHu`) and `x = h·c ∈ C`.  This is the `[HU:HC] = [U:C]`
input of (9.9.a). -/
theorem uInHu_inf_hcInHu_eq_cInHu [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    uInHu data ⊓ (hInHu data ⊔ cInHu data chief) = cInHu data chief := by
  haveI := hInHu_normal data
  apply le_antisymm
  · rintro x ⟨hxU, hxHC⟩
    obtain ⟨hh, hhmem, cc, ccmem, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxHC
    have hcc_u : cc ∈ uInHu data := cInHu_le_uInHu data chief ccmem
    have hh_u : hh ∈ uInHu data := by
      have h1 : hh * cc * cc⁻¹ ∈ uInHu data :=
        (uInHu data).mul_mem hxU ((uInHu data).inv_mem hcc_u)
      rwa [mul_inv_cancel_right] at h1
    have hh_c : hh ∈ cInHu data chief :=
      hInHu_inf_uInHu_le_cInHu data chief (Subgroup.mem_inf.mpr ⟨hhmem, hh_u⟩)
    exact (cInHu data chief).mul_mem hh_c ccmem
  · exact le_inf (cInHu_le_uInHu data chief) le_sup_right

/-- **(9.9.a) index step (A): `[HU:HC] = [U:C]` realized form `HC.index = (cInHu.subgroupOf uInHu).index`.**
The second isomorphism theorem for `HC ◁ HU` with `uInHu ⊔ HC = ⊤`: `HU ⧸ HC ≃ uInHu ⧸ (uInHu ⊓ HC)`,
and `uInHu ⊓ HC = cInHu` (`uInHu_inf_hcInHu_eq_cInHu`). -/
theorem index_hcInHu_eq_relindex_cInHu [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    (hInHu data ⊔ cInHu data chief).index
      = ((cInHu data chief).subgroupOf (uInHu data)).index := by
  haveI : (hInHu data ⊔ cInHu data chief).Normal := hcInHu_normal data chief
  have htop : uInHu data ⊔ (hInHu data ⊔ cInHu data chief) = ⊤ := by
    rw [← sup_assoc, sup_comm (uInHu data) (hInHu data), hInHu_sup_uInHu_eq_top, top_sup_eq]
  have he := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient
    (uInHu data) (hInHu data ⊔ cInHu data chief)).toEquiv
  -- The iso's source denominator `HC.subgroupOf uInHu = cInHu.subgroupOf uInHu` (by `U ⊓ HC = C`).
  have hsub : (hInHu data ⊔ cInHu data chief).subgroupOf (uInHu data)
      = (cInHu data chief).subgroupOf (uInHu data) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxin : (x : ↥(huSub data)) ∈ uInHu data ⊓ (hInHu data ⊔ cInHu data chief) :=
        Subgroup.mem_inf.mpr ⟨x.2, hx⟩
      rw [uInHu_inf_hcInHu_eq_cInHu data chief] at hxin
      exact hxin
    · intro hx; exact Subgroup.mem_sup_right hx
  rw [hsub] at he
  -- `he : Nat.card (↥uInHu ⧸ cInHu.subgroupOf uInHu)
  --       = Nat.card (↥(uInHu ⊔ HC) ⧸ HC.subgroupOf (uInHu ⊔ HC))`
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((hInHu data ⊔ cInHu data chief).subgroupOf (uInHu data ⊔ (hInHu data ⊔ cInHu data chief)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
        (hInHu data ⊔ cInHu data chief) ≤ uInHu data ⊔ (hInHu data ⊔ cInHu data chief))).toEquiv,
    ← he, ← Subgroup.index_eq_card] at hsplit
  -- `hsplit : Nat.card ↥(uInHu ⊔ HC) = (cInHu.subgroupOf uInHu).index * Nat.card ↥HC`
  have htopcard : Nat.card ↥(uInHu data ⊔ (hInHu data ⊔ cInHu data chief))
      = Nat.card ↥(huSub data) := by
    rw [htop]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [htopcard] at hsplit
  -- `hsplit : Nat.card ↥(huSub) = (cInHu.subgroupOf uInHu).index * Nat.card ↥HC`
  have hmul := Subgroup.card_mul_index (hInHu data ⊔ cInHu data chief)
  rw [hsplit, mul_comm (((cInHu data chief).subgroupOf (uInHu data)).index)] at hmul
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul

/-- `|uInHu| = |U|` (the realization `uInHu = (U.subgroupOf M).subgroupOf HU`). -/
theorem card_uInHu_eq (data : TypesIIIIIIVSetup M) :
    Nat.card ↥(uInHu data) = Nat.card ↥data.U := by
  have hUsubM : data.U.subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_sup_right : data.U ≤ data.H ⊔ data.U)
  calc Nat.card ↥(uInHu data)
      = Nat.card ↥(data.U.subgroupOf M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUsubM).toEquiv
    _ = Nat.card ↥data.U := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (U_le_M data)).toEquiv

/-- `|cInHu| = |C|` (the realization `cInHu = (cSub.subgroupOf M).subgroupOf HU`). -/
theorem card_cInHu_eq (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    Nat.card ↥(cInHu data chief) = Nat.card ↥(cSub data chief) := by
  have hCsubM : (cSub data chief).subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M
      ((cSub_le_U data chief).trans (le_sup_right : data.U ≤ data.H ⊔ data.U))
  have hCleM : cSub data chief ≤ M := (cSub_le_U data chief).trans (U_le_M data)
  calc Nat.card ↥(cInHu data chief)
      = Nat.card ↥((cSub data chief).subgroupOf M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCsubM).toEquiv
    _ = Nat.card ↥(cSub data chief) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleM).toEquiv

/-- `|C| = |ker(uActionHom)|`: `cSub` is the injective double-image of the kernel. -/
theorem card_cSub_eq_card_ker (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    Nat.card ↥(cSub data chief) = Nat.card ↥(uActionHom data chief).ker := by
  show Nat.card ↥(((uActionHom data chief).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
        (data.typeP.U ⊔ data.typeP.W1).subtype) = Nat.card ↥(uActionHom data chief).ker
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv,
    ← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv]

/-- The character-theoretic setup of Peterfalvi (9.5).

`C`, `U'`, and `C'` denote the centralizer, commutator subgroup, and its
intersection with `C` used in the text.  The families of irreducible characters
`X`, `S`, `XOf`, and `SOf` are no longer free carrier fields: they are *genuine*
definitions (`Section11CharacterData.X = xiSet data` etc.), so the (9.8)/(9.9)
counts and (9.11) coherence are stated against Peterfalvi's honest families
`𝒳 = {χ ∈ Irr(HU) | H ⊄ Ker χ}`, `𝒮 = Ind_{HU}^M 𝒳`, `𝒳(Y)`, `𝒮(Y)`. -/
structure Section11CharacterData {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) where
  u : ℕ
  /-- **`u = |Ū|`**, the order of the image `Ū = U/C_U(H̄)` of the `U`-action on the chief factor
  `H̄ = ↥H ⧸ N` (Peterfalvi (9.5)).  This pins the formerly free `u` to the genuine quantity used by
  the Clifford dichotomy (9.7): in case (b) the Singer field model gives `|Ū| ∣ (p^q-1)/(p-1)` and
  `Coprime |Ū| (p-1)`.  Stated `Finite`-freely via `quotientMulAutHom` so the carrier needs no
  `[Finite G]`; it is definitionally the image used by `chiefFactor_caseB_image_*`. -/
  u_eq_card_quotient : u = Nat.card ↥(((quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
    (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).range)
  H0CprimeSupport : Set ↥M
  tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  quotientSemidirectFrobenius : Prop

namespace Section11CharacterData

variable {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}

/-- **Peterfalvi's `C = C_U(H̄)`** (9.5), genuine: the kernel of the `U`-action on the chief
factor (`cSub`), no longer a free field. -/
noncomputable def C (_chars : Section11CharacterData data chief) : Subgroup G := cSub data chief

theorem C_le_U (chars : Section11CharacterData data chief) : chars.C ≤ data.U := cSub_le_U data chief

/-- **Peterfalvi's `U' = [U, U]`** (9.5), genuine (`uprimeSub`). -/
def Uprime (_chars : Section11CharacterData data chief) : Subgroup G := uprimeSub data

theorem Uprime_le_U (chars : Section11CharacterData data chief) : chars.Uprime ≤ data.U :=
  uprimeSub_le_U data

/-- **Peterfalvi's `C' = [C, C]`** (9.5), genuine (`cprimeSub`). -/
noncomputable def Cprime (_chars : Section11CharacterData data chief) : Subgroup G :=
  cprimeSub data chief

theorem Cprime_le_C (chars : Section11CharacterData data chief) : chars.Cprime ≤ chars.C :=
  cprimeSub_le_C data chief

/-- The genuine family `𝒳 = {χ ∈ Irr(HU) | H ⊄ Ker χ}` (Peterfalvi (9.5)), pinned to `xiSet`. -/
def X (_chars : Section11CharacterData data chief) : Set (IrreducibleCharacter ↥(huSub data)) :=
  xiSet data

/-- The genuine family `𝒳(Y) = {χ ∈ 𝒳 | Y ⊆ Ker χ}` (Peterfalvi (9.5)), pinned to `xiOf`. -/
def XOf (_chars : Section11CharacterData data chief) (Y : Subgroup G) :
    Set (IrreducibleCharacter ↥(huSub data)) :=
  xiOf data Y

/-- The genuine family `𝒮 = Ind_{HU}^M 𝒳` (Peterfalvi (9.5)), pinned to `sSet`. -/
noncomputable def S [Finite G] (_chars : Section11CharacterData data chief) :
    Set (ClassFunction ↥M ℂ) :=
  sSet data

/-- The genuine family `𝒮(Y) = Ind_{HU}^M 𝒳(Y)` (Peterfalvi (9.5)), pinned to `sOf`. -/
noncomputable def SOf [Finite G] (_chars : Section11CharacterData data chief) (Y : Subgroup G) :
    Set (ClassFunction ↥M ℂ) :=
  sOf data Y

@[simp] theorem X_eq (chars : Section11CharacterData data chief) : chars.X = xiSet data := rfl
@[simp] theorem XOf_eq (chars : Section11CharacterData data chief) (Y : Subgroup G) :
    chars.XOf Y = xiOf data Y := rfl
@[simp] theorem S_eq [Finite G] (chars : Section11CharacterData data chief) :
    chars.S = sSet data := rfl
@[simp] theorem SOf_eq [Finite G] (chars : Section11CharacterData data chief) (Y : Subgroup G) :
    chars.SOf Y = sOf data Y := rfl

end Section11CharacterData

/-- **A nontrivial character of a prime-order group is faithful.**  `ker χ ≤ K` has order
dividing the prime `|K|`, and `χ ≠ 1` rules out `ker χ = K`, so `ker χ = ⊥`.  The per-factor input
of Peterfalvi (9.8)'s `def_Itheta`: on each order-`p` chief-factor summand a nontrivial linear
character is faithful, so any automorphism fixing it is the identity. -/
theorem injective_of_prime_card_of_ne_one {K : Type*} [Group K] [Finite K]
    (hp : (Nat.card K).Prime) (χ : K →* ℂˣ) (hχ : χ ≠ 1) : Function.Injective χ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hdvd : Nat.card ↥(MonoidHom.ker χ) ∣ Nat.card K := Subgroup.card_subgroup_dvd_card _
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hpeq
  · exact Subgroup.card_eq_one.mp h1
  · exact absurd (MonoidHom.ker_eq_top_iff.mp ((MonoidHom.ker χ).eq_top_of_card_eq hpeq)) hχ

/-- **An automorphism fixing a nontrivial character of a prime-order group is the identity.**
`χ (α x) = χ x` with `χ` faithful (`injective_of_prime_card_of_ne_one`) forces `α x = x`. -/
theorem mulAut_eq_one_of_fixes_ne_one_hom {K : Type*} [Group K] [Finite K]
    (hp : (Nat.card K).Prime) (α : MulAut K) (χ : K →* ℂˣ) (hχ : χ ≠ 1)
    (hfix : ∀ x, χ (α x) = χ x) : α = 1 := by
  ext x
  exact injective_of_prime_card_of_ne_one hp χ hχ (hfix x)

open OddOrder.RepresentationTheory in
/-- **Per-factor stabilizer = centralizer** (Peterfalvi (9.8) `def_Itheta`, character form): for an
abelian prime-order group `K`, an automorphism `α` fixing a nontrivial irreducible character `θ` is
the identity.  `θ` is linear (`exists_linearIrreducibleCharacter_eq_of_isMulCommutative`), so it is a
faithful homomorphism `χ : K →* ℂˣ` (`injective_of_prime_card_of_ne_one`), and `α` fixing `χ` forces
`α = 1`.  Applied per order-`p` chief-factor summand of the non-Galois (9.7) decomposition. -/
theorem mulAut_eq_one_of_fixes_irr_ne_trivial_of_prime_card {K : Type*} [Group K] [Finite K]
    [IsMulCommutative K] (hp : (Nat.card K).Prime) (α : MulAut K)
    (θ : IrreducibleCharacter K)
    (hθnt : (θ : ClassFunction K ℂ) ≠ trivialClassFunction K)
    (hfix : ∀ x, (θ : ClassFunction K ℂ) (α x) = (θ : ClassFunction K ℂ) x) : α = 1 := by
  obtain ⟨χ, hχ⟩ := θ.isIrreducible.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  have hχne : χ ≠ 1 := by
    intro h0
    apply hθnt
    rw [← hχ, h0, show (linearIrreducibleCharacter (1 : K →* ℂˣ)) = trivialIrreducibleCharacter K from
      linearIrreducibleCharacter_eq_trivial_iff.mpr rfl]
    rfl
  refine mulAut_eq_one_of_fixes_ne_one_hom hp α χ hχne (fun x => ?_)
  apply Units.val_injective
  have h1 := hfix x
  rw [← hχ] at h1
  simpa only [linearIrreducibleCharacter_apply] using h1

/-- **An automorphism trivial on a spanning family of subgroups is the identity.**  The fixed
points `{x | α x = x}` form a subgroup containing each `K i`, hence `⨆ i, K i = ⊤`; so `α` fixes
everything.  Piece (D) of the non-Galois (9.8) inertia: `φ(g)` trivial on each order-`p` chief-factor
summand `Hpart i` (which span `H̄`) is trivial on `H̄`. -/
theorem mulAut_eq_one_of_eq_id_on_iSup {H : Type*} [Group H] (α : MulAut H)
    {ι : Type*} (K : ι → Subgroup H) (hspan : ⨆ i, K i = ⊤)
    (htriv : ∀ i, ∀ x ∈ K i, α x = x) : α = 1 := by
  set S : Subgroup H :=
    { carrier := {x | α x = x}
      one_mem' := map_one α
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢; rw [map_inv, ha] } with hS
  have htop : S = ⊤ := top_le_iff.mp (hspan ▸ iSup_le (fun i x hx => htriv i x hx))
  ext x
  show α x = x
  exact htop.ge (Subgroup.mem_top x)

/-- Case (a) of Peterfalvi (9.7): `H/H_0` splits as a direct product of `q`
order-`p` factors permuted by `W_1`.

The parts `Hpart` live in the chief factor `H̄ = ↥H ⧸ N` itself (not in `G`): an order-`p` piece of
`H̄` pulls back to a subgroup of `G` of order `p·|H₀|`, so the genuine order-`p` factors are
subgroups of `H̄`. -/
structure CliffordCaseAData {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief) where
  Hpart : Fin data.q → Subgroup (↥data.H ⧸ chief.N)
  Hpart_order : ∀ i, Nat.card ↥(Hpart i) = chief.p
  W1_transitive_on_parts : Prop
  W1_transitive_on_parts_holds : W1_transitive_on_parts
  a : ℕ
  a_pos : 0 < a
  a_dvd_p_sub_one : a ∣ chief.p - 1
  quotient_factors_cyclic_order_a : Prop
  quotient_factors_cyclic_order_a_holds : quotient_factors_cyclic_order_a
  Ubar_embeds_product : Prop
  Ubar_embeds_product_holds : Ubar_embeds_product

/-- Case (b) of Peterfalvi (9.7): `U` acts irreducibly on `H/H_0`, modeled by
the multiplicative group of a field of order `p^q`.

The genuine consequences of this case are supplied by standalone lemmas (which carry the required
`[Finite G]`/`chief.N.Normal` instances that a `structure` field type cannot): the fixed-point-free
Frobenius action `H̄ ⋊ Ū` by `chiefFactor_caseB_action_fpf` (the structural input of Peterfalvi
(9.9)), the Singer cyclicity of `Ū` by `chiefFactor_caseB_image_cyclic`, and the divisibilities
`u_coprime_p_sub_one`/`u_dvd_norm_quotient` carried here. -/
structure CliffordCaseBData {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief) where
  field_model : Prop
  field_model_holds : field_model
  Ubar_cyclic : Prop
  Ubar_cyclic_holds : Ubar_cyclic
  u_coprime_p_sub_one : Nat.Coprime chars.u (chief.p - 1)
  u_dvd_norm_quotient : chars.u ∣ (chief.p ^ data.q - 1) / (chief.p - 1)
  /-- The defining property of case (b): `U` acts **irreducibly** on the chief factor `H̄ = H/H_0`,
  i.e. the only `U`-invariant subgroups of `H̄` are `⊥` and `⊤`.  Stated `Finite`-freely via the
  `U`-action hom `uActionHom` (definitionally `(typeP_quotientCoprimeAction …).φ.comp (…).U.subtype`,
  which needs `[Finite G]`).  This is the hypothesis the Clifford degree analysis (9.8.c)/(9.9.a)
  consumes through `inertia_eq_hcInHu` (it computes the inertia group `I_{HU}(θ₀) = HC` of a
  nontrivial chief-factor character). -/
  actsIrreducibly : ∀ J : Subgroup (↥data.H ⧸ chief.N),
      IsAInvariant (uActionHom data chief) J → J = ⊥ ∨ J = ⊤

/-- **Peterfalvi (9.6)**: after choosing `H_0`, the induced `U`-action is non-trivial (`U` does not
centralize `H`), `H̄ = H/H_0` is a chief factor of `M`, `|H̄| = p^q`, and (types III/IV) `|W_2| = p`.

*Faithfulness note.* The printed (9.6) asserts `|W̄_2| = p` for the **image** `W̄_2 = C_{H̄}(W_1)`,
which for type II is strictly smaller than the full `W_2 = C_H(W_1)` (the carrier never pins `|W_2|`,
only `|W_1|` is prime).  The earlier formalization stated the **unconditional** `|W_2| = p`, which is
*false* for type II: `|W_2|^q = |H| = p^q·|H_0|` (by (9.3) + `quotient_order`) gives `|W_2| = p`
only when `H_0 = 1`.  We therefore state the faithful, carrier-provable form: `|W_2| = p` only in
the types III/IV branch (where `|W_2| = p` directly, `typeIII_IV_p_eq_W2`), together with the genuine
order conclusion `|H̄| = p^q` (`quotient_order`).  The image fact `|W̄_2| = p` needs the (non-opaque)
chief-factor structure and is delivered by `typeP_chiefFactor_card`. -/
theorem chiefFactor_basic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    data.U ⊓ Subgroup.centralizer (data.H : Set G) ≠ data.U ∧
      (IsTypeIII M ∨ IsTypeIV M → Nat.card ↥data.W2 = chief.p) ∧
      Nat.card ↥data.H = chief.p ^ data.q * Nat.card ↥chief.H0 := by
  obtain ⟨hII_case, hIIIIV_case⟩ := typeII_III_IV_order_relations hG data
  have hH_ne : data.typeP.H ≠ ⊥ := fun heq => data.typeP.H_noncyclic (heq ▸ inferInstance)
  refine ⟨?_, chief.typeIII_IV_p_eq_W2, chief.quotient_order⟩
  -- `U` does not centralize `H`: else `C_H(U) = H`, contradicting (9.3).
  intro hcentr
  have hUle : data.U ≤ Subgroup.centralizer (data.H : Set G) := inf_eq_left.mp hcentr
  have hHle : data.H ≤ Subgroup.centralizer (data.U : Set G) := Subgroup.le_centralizer_iff.mp hUle
  have hHinf : data.H ⊓ Subgroup.centralizer (data.U : Set G) = data.H := inf_eq_left.mpr hHle
  rcases data.type_alt with hII | hIIIIV
  · -- Type II: (9.3) gives `C_H(U) = ⊥`, but `C_H(U) = H ≠ ⊥`.
    exact hH_ne (hHinf.symm.trans (hII_case hII).1)
  · -- Types III/IV: (9.3) gives `|H| = p^q·|C_H(U)| = p^q·|H|`, forcing `p^q = 1`.
    obtain ⟨p, hp, _hpW2, _hCUW, hHcard⟩ := hIIIIV_case hIIIIV
    rw [hHinf] at hHcard
    have hpq1 : p ^ data.q = 1 := by
      rcases Nat.eq_zero_or_pos (Nat.card ↥data.H) with h0 | hpos
      · exact absurd h0 Nat.card_pos.ne'
      · exact Nat.eq_of_mul_eq_mul_right hpos (by rw [one_mul]; exact hHcard.symm)
    have hq_ne : data.q ≠ 0 := Nat.card_pos.ne'
    have h2 : 2 ≤ p ^ data.q := le_trans hp.two_le (Nat.le_self_pow hq_ne p)
    omega

/-- **Centralizer commutes with a coprime cyclic quotient** (general group theory): for `x : Γ` and
`N ◁ Γ` with `gcd(|⟨x⟩|, |N|) = 1`, the centralizer of `x̄ = x N` in `Γ/N` is the image of the
centralizer of `x` in `Γ`: `C_{Γ/N}(x̄) = (C_Γ(x)).map (mk' N)`.

`⊇` is functoriality of `mk'`.  `⊆` lifts an `x̄`-centralizing element `g N` through the coprime
action of `⟨x⟩` on `Γ` (conjugation): `g N ∈ C(x̄)` means every power of `x` fixes `g` modulo `N`,
so Isaacs Cor 3.28 (`coprime_fixedPoints_quotient_of_coprime_normal`) produces a genuine
`x`-centralizing representative `c ≡ g (mod N)`.  This is the engine of the Peterfalvi (8.4.d)
`centralizer_W̄₂` computation (`Γ = ↥M`, `N = H₀`). -/
theorem centralizer_map_mk'_eq_of_coprime_zpowers {Γ : Type*} [Group Γ] [Finite Γ]
    {N : Subgroup Γ} [N.Normal] (x : Γ)
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥N)) :
    Subgroup.centralizer ({(QuotientGroup.mk' N x : Γ ⧸ N)} : Set (Γ ⧸ N))
      = (Subgroup.centralizer ({x} : Set Γ)).map (QuotientGroup.mk' N) := by
  classical
  apply le_antisymm
  · -- `⊆`: coprime lift of an `x̄`-centralizing element to an `x`-centralizing one
    intro gbar hgbar
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gbar
    set φ : ↥(Subgroup.zpowers x) →* MulAut Γ :=
      (MulAut.conj (G := Γ)).comp (Subgroup.zpowers x).subtype with hφ
    have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ N := by
      rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
      intro c n hn
      show (MulAut.conj (c : Γ)) n ∈ N
      rw [MulAut.conj_apply]
      exact (inferInstance : N.Normal).conj_mem n hn (c : Γ)
    haveI : IsCyclic ↥(Subgroup.zpowers x) := Subgroup.isCyclic_zpowers x
    have hcomm : Commute (QuotientGroup.mk' N x) (QuotientGroup.mk' N g) :=
      Subgroup.mem_centralizer_iff.mp hgbar _ (Set.mem_singleton _)
    have hg_fix : ∀ c : ↥(Subgroup.zpowers x), ∃ n ∈ N, φ c g = g * n := by
      intro c
      refine ⟨g⁻¹ * φ c g, ?_, by group⟩
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv]
      have hφc : φ c g = (c : Γ) * g * (c : Γ)⁻¹ := by simp [hφ, MulAut.conj_apply]
      have hcc : Commute (QuotientGroup.mk' N (c : Γ)) (QuotientGroup.mk' N g) := by
        obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp c.2
        rw [← hk, map_zpow]
        exact hcomm.zpow_left k
      rw [hφc, map_mul, map_mul, map_inv, hcc.eq]
      group
    obtain ⟨c, hc_fixed, n, hn, hc_eq⟩ :=
      OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal
        hcop (Or.inl inferInstance) hN_inv hg_fix
    rw [Subgroup.mem_map]
    refine ⟨c, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      have hfix := hc_fixed ⟨x, Subgroup.mem_zpowers x⟩
      rw [hφ] at hfix
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply] at hfix
      -- `hfix : x * c * x⁻¹ = c`  ⟹  `x * c = c * x`
      rw [hy]
      exact mul_inv_eq_iff_eq_mul.mp hfix
    · have hn1 : (QuotientGroup.mk' N) n = 1 := by
        rw [QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff n).mpr hn
      rw [hc_eq, map_mul, hn1, mul_one]
  · -- `⊇`: image of the centralizer centralizes `x̄`
    rw [Subgroup.map_le_iff_le_comap]
    intro c hc
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro ybar hybar
    rw [Set.mem_singleton_iff] at hybar; subst hybar
    show QuotientGroup.mk' N x * QuotientGroup.mk' N c = QuotientGroup.mk' N c * QuotientGroup.mk' N x
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc x (Set.mem_singleton _)]

/-- **`H₀ ◁ M`** (the chief-factor kernel is `M`-normal): `H₀.subgroupOf M` is normal in `↥M`, so
the quotient `↥M ⧸ H₀` — the ambient of Peterfalvi (8.4.d)'s certain-type group `L = M/H₀` — is a
group.  Immediate from the `M`-normalization `H0_normalized_by_M` of (9.4) via
`normal_subgroupOf_iff_le_normalizer` (using `H₀ < H ≤ M`).  This is the foundation of the §9
reducible-count `quotient`-Dade framework (issue 1012). -/
theorem chiefFactor_H0_subgroupOf_normal {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    (chief : ChiefFactorData data) : (chief.H0.subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (chief.H0_lt_H.le.trans (H_le_M data))).mpr chief.H0_normalized_by_M

/-- **`W₁ ⊓ H₀ = ⊥` inside `↥M`**: `W₁` complements `M' = [M,M]` (`data.M_complement`) and
`H₀ < H ≤ M'`, so `W₁ ⊓ H₀ ≤ W₁ ⊓ M' = ⊥`.  In `↥M ⧸ H₀` this makes `W̄₁ = W₁ H₀ / H₀ ≅ W₁`
(needed for `W̄₁ ≠ ⊥` and the Hall coprimality of the (8.4.d) certain-type group). -/
theorem chiefFactor_W1_inf_H0_subgroupOf_eq_bot {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (data.W1.subgroupOf M) ⊓ (chief.H0.subgroupOf M) = ⊥ := by
  have hH0M' : (chief.H0.subgroupOf M) ≤ (derivedInG M).subgroupOf M :=
    Subgroup.comap_mono (chief.H0_lt_H.le.trans data.typeP.H_le)
  rw [eq_bot_iff]
  exact le_trans (inf_le_inf_left _ hH0M')
    (disjoint_iff.mp data.typeP.M_complement.disjoint.symm).le

/-- **`gcd(|H₀|, |W₁|) = 1`**: `H₀ < H` and `gcd(|H|, |W₁|) = 1` (`typeP_coprime_H_W1`, the coprime
action of the Hall complement `W₁` on the nilpotent `H = M_F`).  This is the coprimality the
(8.4.d) centralizer computation `C_{M'/H₀}(x̄) = W̄₂` needs (the `x`-fixed points of `M'` lift
across `H₀` by Isaacs Cor 3.28). -/
theorem chiefFactor_coprime_H0_W1 [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    Nat.Coprime (Nat.card ↥chief.H0) (Nat.card ↥data.W1) :=
  (typeP_coprime_H_W1 data.typeP).coprime_dvd_left
    (Subgroup.card_dvd_of_le chief.H0_lt_H.le)

/-- **`(H₀ ⊔ C) ⊓ H = H₀`** (Peterfalvi (9.8.b)/(9.9.b) shared, the Dedekind step) — the unifying
condition `K ∩ H = H₀` that lets the §9↔§6 reducible count `reducible_count_sOf_H0` apply to
`K = H₀C` exactly as to `K = H₀` (Coq `PFsection9` `nb_redM`, instantiated at both `K = H0` and
`K = H0C`).  `C ≤ U` and `H ⊓ U = ⊥` (`typeP_H_inf_U`) kill the `C`-part: writing
`x ∈ H₀ ⊔ C = H₀·C` (`coe_mul_of_right_le_normalizer_left`, since `C ≤ U ≤ M ≤ N(H₀)`) as
`x = h₀·c`, membership `x ∈ H` together with `h₀ ∈ H₀ ≤ H` forces `c ∈ H ⊓ C ≤ H ⊓ U = ⊥`.
Consequently `W₂ ∩ H₀C = W₂ ∩ H ∩ H₀C = W₂ ∩ H₀` (as `W₂ ≤ H`), so the chief-factor image `W̄₂`
keeps order `p` in `M/H₀C` just as in `M/H₀` — this is what makes the `H₀C` reducible count
`reducible_count_sOf_H0C` a parallel of the `H₀` one (issue 1012). -/
theorem chiefFactor_H0supC_inf_H_eq_H0 {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (chief.H0 ⊔ cSub data chief) ⊓ data.H = chief.H0 := by
  refine le_antisymm ?_ (le_inf le_sup_left chief.H0_lt_H.le)
  intro x hx
  obtain ⟨hxHC, hxH⟩ := Subgroup.mem_inf.mp hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left chief.H0 (cSub data chief)
      (((cSub_le_U data chief).trans (U_le_M data)).trans chief.H0_normalized_by_M)] at hxHC
  obtain ⟨h₀, hh₀, c, hc, rfl⟩ := hxHC
  have hcH : c ∈ data.typeP.H := by
    have hcalc : h₀⁻¹ * (h₀ * c) ∈ data.H := mul_mem (inv_mem (chief.H0_lt_H.le hh₀)) hxH
    simpa [inv_mul_cancel_left] using hcalc
  have hc1 : c = 1 := by
    have hmem : c ∈ data.typeP.H ⊓ data.typeP.U :=
      Subgroup.mem_inf.mpr ⟨hcH, cSub_le_U data chief hc⟩
    rwa [typeP_H_inf_U data.typeP, Subgroup.mem_bot] at hmem
  simpa [hc1] using hh₀

/-- **`H₀C ≤ M' = HU`**: `H₀ ≤ H ≤ M'` (`typeP.H_le`) and `C ≤ U ≤ M'` (`typeP.U_le`).  The second
input (`K ≤ HU`) of the generic reducible-count hypothesis (Coq `PFsection9` `nb_redM`) for the
quotient `M/H₀C`; combined with `chiefFactor_H0supC_inf_H_eq_H0` and `H₀C ◁ M` it makes the §9↔§6
count apply to `K = H₀C` (issue 1012). -/
theorem chiefFactor_H0supC_le_derived {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    chief.H0 ⊔ cSub data chief ≤ derivedInG M :=
  sup_le (chief.H0_lt_H.le.trans data.typeP.H_le)
    ((cSub_le_U data chief).trans data.typeP.U_le)

/-- **`A.map f ⊓ B.map f = (A ⊓ B).map f` when `ker f ≤ B`** (general group theory).  `⊇` is
monotonicity; for `⊆`, `f a = f b` with `b ∈ B` and `ker f ≤ B` forces `a ∈ B`, so `a ∈ A ⊓ B`.
The step (8.4.d) needs to pull `C(x̄) ⊓ K̄` out of the image (`f = mk' H₀`, `ker = H₀ ≤ K = M'`). -/
theorem map_inf_map_of_ker_le {H : Type*} [Group H] {f : G →* H} {A B : Subgroup G}
    (hB : f.ker ≤ B) : A.map f ⊓ B.map f = (A ⊓ B).map f := by
  refine le_antisymm ?_ (le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right))
  intro y hy
  rw [Subgroup.mem_inf] at hy
  obtain ⟨a, ha, rfl⟩ := hy.1
  obtain ⟨b, hb, hab⟩ := hy.2
  have hker : a * b⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
  have haB : a ∈ B := by
    have hmem : a * b⁻¹ * b ∈ B := mul_mem (hB hker) hb
    simpa using hmem
  exact ⟨a, ⟨ha, haB⟩, rfl⟩

/-- **Peterfalvi (8.4.d), step 3 — `centralizer_W₁` transported to `↥M`**: for a lift `x` of a
nontrivial `W̄₁`-element, `C_{↥M}(x) ⊓ M' = W₂` (inside `↥M`).  The (8.4) datum
`derivedInG M ⊓ C_G(x) = W₂` (`data.centralizer_W1`) transported across `↥M ↪ G`
(`S03h.centralizer_subgroupOf`). -/
theorem chiefFactor_centralizer_inf_derived {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (x : ↥M) (hx : (x : G) ∈ data.W1) (hx1 : (x : G) ≠ 1) :
    Subgroup.centralizer ({x} : Set ↥M) ⊓ ((derivedInG M).subgroupOf M)
      = data.W2.subgroupOf M := by
  have hamb : Subgroup.centralizer ({(x : G)} : Set G) ⊓ derivedInG M = data.W2 := by
    rw [inf_comm]; exact data.typeP.centralizer_W1 (x : G) hx hx1
  rw [OddOrder.BG.Ch1.S03h.centralizer_subgroupOf, Set.image_singleton]
  simp only [Subgroup.subgroupOf, ← Subgroup.comap_inf, Subgroup.coe_subtype, hamb]

/-- **Peterfalvi (8.4.d) `centralizer_W̄₂`, generic in the quotient kernel `N'`** (reused for both
`N' = H₀` and `N' = H₀C`): for `N' ◁ ↥M` with `N' ≤ M' = derivedInG M` and `gcd(|W₁|, |N'|) = 1`,
and a nontrivial `x̄ ∈ W̄₁ = W₁ N'/N'`, `C_{↥M/N'}(x̄) ⊓ (M'/N') = W₂ N'/N'`.  Three steps with the
`N'`-dependence isolated to the coprimality and the containment `ker (mk' N') = N' ≤ M'`:
`centralizer_map_mk'_eq_of_coprime_zpowers` (`gcd(|⟨x⟩|,|N'|)=1`), `map_inf_map_of_ker_le`, and the
`N'`-independent `C_{↥M}(x) ⊓ M' = W₂` (`chiefFactor_centralizer_inf_derived`). -/
theorem centralizer_W2bar_quotient [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (N' : Subgroup ↥M) [N'.Normal]
    (hN'le : N' ≤ (derivedInG M).subgroupOf M)
    (hcopW1 : Nat.Coprime (Nat.card ↥data.W1) (Nat.card ↥N'))
    (xbar : ↥M ⧸ N')
    (hxbar : xbar ∈ (data.W1.subgroupOf M).map (QuotientGroup.mk' N'))
    (hxbar1 : xbar ≠ 1) :
    Subgroup.centralizer ({xbar} : Set (↥M ⧸ N'))
        ⊓ ((derivedInG M).subgroupOf M).map (QuotientGroup.mk' N')
      = (data.W2.subgroupOf M).map (QuotientGroup.mk' N') := by
  obtain ⟨x, hx_mem, rfl⟩ := Subgroup.mem_map.mp hxbar
  have hx1 : x ≠ 1 := fun h => hxbar1 (by rw [h]; exact map_one _)
  have hxW1 : ((x : ↥M) : G) ∈ data.W1 := Subgroup.mem_subgroupOf.mp hx_mem
  have hxG1 : ((x : ↥M) : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hcardW1 : Nat.card ↥(data.W1.subgroupOf M) = Nat.card ↥data.W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeP.W1_le).toEquiv
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥N') := by
    refine hcopW1.coprime_dvd_left ?_
    rw [← hcardW1]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx_mem)
  rw [centralizer_map_mk'_eq_of_coprime_zpowers x hcop,
    map_inf_map_of_ker_le (B := (derivedInG M).subgroupOf M) (by
      rw [QuotientGroup.ker_mk']; exact hN'le),
    chiefFactor_centralizer_inf_derived x hxW1 hxG1]

/-- **Peterfalvi (8.4.d), `centralizer_W̄₂`** (the `N' = H₀` instance of `centralizer_W2bar_quotient`):
in `L = ↥M ⧸ H₀`, for a nontrivial `x̄ ∈ W̄₁`, `C_L(x̄) ⊓ K̄ = W̄₂` where `K̄ = M'/H₀` and
`W̄₂ = W₂ H₀/H₀`.  This is the (8.4.d) certain-type `centralizer_W₂` field of `S06.Hypothesis (M/H₀)`. -/
theorem chiefFactor_centralizer_W2bar [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [(chief.H0.subgroupOf M).Normal]
    (xbar : ↥M ⧸ (chief.H0.subgroupOf M))
    (hxbar : xbar ∈ (data.W1.subgroupOf M).map (QuotientGroup.mk' (chief.H0.subgroupOf M)))
    (hxbar1 : xbar ≠ 1) :
    Subgroup.centralizer ({xbar} : Set (↥M ⧸ (chief.H0.subgroupOf M)))
        ⊓ ((derivedInG M).subgroupOf M).map (QuotientGroup.mk' (chief.H0.subgroupOf M))
      = (data.W2.subgroupOf M).map (QuotientGroup.mk' (chief.H0.subgroupOf M)) := by
  have hcardH0 : Nat.card ↥(chief.H0.subgroupOf M) = Nat.card ↥chief.H0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (chief.H0_lt_H.le.trans (H_le_M data))).toEquiv
  refine centralizer_W2bar_quotient (chief.H0.subgroupOf M) ?_ ?_ xbar hxbar hxbar1
  · exact Subgroup.comap_mono (chief.H0_lt_H.le.trans data.typeP.H_le)
  · rw [hcardH0]; exact (chiefFactor_coprime_H0_W1 chief).symm

/-! ### (9.7) The chief factor `H̄ = H/H₀` as an `𝔽ₚ[U W₁]`-module

The Clifford dichotomy of (9.7) is read off the `𝔽ₚ`-dimension of `H̄`: it equals `q`, and `q` is
prime, so under the restricted `U`-action `H̄` decomposes into `k` irreducible summands of a common
dimension `d` with `q = k·d`, forcing `(k, d) ∈ {(1, q), (q, 1)}`.  The starting point is the order
`|H̄| = p^q` (hence `dim_{𝔽ₚ} H̄ = q`). -/

/-- The chief factor `H̄ = H/H₀ ≅ ↥H ⧸ N` has order `p^q`: `|H| = p^q·|H₀|` (`quotient_order`) and
`|H₀| = |N|` (`H₀ = N.map H.subtype`), so `[H : N] = p^q`. -/
theorem chiefFactor_quotient_card [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    (chief : ChiefFactorData data) :
    Nat.card (↥data.H ⧸ chief.N) = chief.p ^ data.q := by
  haveI := chief.N_normal
  have hH0card : Nat.card ↥chief.H0 = Nat.card ↥chief.N := by
    rw [chief.H0_eq]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective chief.N data.H.subtype
      data.H.subtype_injective).toEquiv).symm
  have key : chief.N.index * Nat.card ↥chief.N = chief.p ^ data.q * Nat.card ↥chief.N := by
    rw [Subgroup.index_mul_card, chief.quotient_order, hH0card]
  rw [(Subgroup.index_eq_card chief.N).symm]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos key

/-- **Peterfalvi (8.4.d) `W2_nontrivial` input: `W₂ ⊄ H₀`.**  The `W₁`-fixed points of the chief
factor `H̄ = ↥H ⧸ N` have order `p ≠ 1` (`coprimeFrobeniusChiefFactor_card`, Wielandt), and they are
the image of `C_H(W₁) = W₂` (`map_fixedSubgroup_eq_fixedSubgroup_quotient`).  So `C_H(W₁) ⊄ N`, i.e.
some element of `W₂` lies outside `H₀ = N.map H.subtype`; hence `W₂ ⊄ H₀`, equivalently the
certain-type `W̄₂ = W₂ H₀ / H₀` of `S06.Hypothesis (M/H₀)` is nontrivial. -/
theorem chiefFactor_W2_not_le_H0 [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ¬ data.W2 ≤ chief.H0 := by
  show ¬ data.typeP.W2 ≤ chief.H0
  haveI := chief.N_normal
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  have hHbar : Nat.card (↥data.H ⧸ chief.N) ≠ 1 := by
    rw [chiefFactor_quotient_card chief]
    exact (Nat.one_lt_pow (Nat.card_pos (α := ↥data.W1)).ne' chief.p_prime.one_lt).ne'
  have hUnorm : ((typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).U).Normal :=
    (typeP_uW1_frobenius data.typeP hU).isNormal
  have hEcyc := typeP_quotient_fixedByE_cyclic data.typeP hU chief.N_aInvariant
  have hcard := coprimeFrobeniusChiefFactor_card
    (typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant) hUnorm chief.p_prime
    chief.quotient_elementaryAbelian chief.quotient_chiefFactor chief.U_noncentral_on_quotient
    hEcyc hHbar
  have hfixne : (typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).fixedByE ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥(typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).fixedByE = 1 :=
      by rw [h]; simp
    exact chief.p_prime.ne_one (hcard.2.symm.trans h1)
  have hcopHW1 : Nat.Coprime
      (Nat.card ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) (Nat.card ↥data.H) :=
    (typeP_coprime_H_uW1 data.typeP hU).symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
  haveI : IsSolvable ↥data.H := (typeP_coprimeAction data.typeP hU).H_solvable
  have hmap : (fixedSubgroup (typeP_conjAction data.typeP)
      (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))).map (QuotientGroup.mk' chief.N)
      = (typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).fixedByE :=
    map_fixedSubgroup_eq_fixedSubgroup_quotient chief.N_aInvariant hcopHW1 (Or.inr inferInstance)
  have hCHW1 : (fixedSubgroup (typeP_conjAction data.typeP)
        (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))).map data.typeP.H.subtype
      = data.typeP.W2 := by
    rw [typeP_fixedSubgroup_map data.typeP le_sup_right, typeP_H_inf_centralizer_W1]
  have hCfixN : ¬ (fixedSubgroup (typeP_conjAction data.typeP)
      (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) ≤ chief.N := by
    intro hle
    apply hfixne
    rw [← hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hle
  obtain ⟨c, hcCfix, hcN⟩ := SetLike.not_le_iff_exists.mp hCfixN
  intro hW2H0
  have hcG_W2 : (data.typeP.H.subtype c) ∈ data.typeP.W2 := by
    rw [← hCHW1]; exact Subgroup.mem_map_of_mem _ hcCfix
  have hcG_H0 : (data.typeP.H.subtype c) ∈ chief.H0 := hW2H0 hcG_W2
  rw [chief.H0_eq, Subgroup.mem_map] at hcG_H0
  obtain ⟨n, hn, hnc⟩ := hcG_H0
  exact hcN (data.typeP.H.subtype_injective hnc ▸ hn)

/-- **`W₁ ⊓ H₀C = ⊥` inside `↥M`** (the `N' = H₀C` non-degeneracy input for
`chiefFactorQuotientHypothesisGen`): `H₀C ≤ M'` (`chiefFactor_H0supC_le_derived`) and `W₁` is a
complement to `M'` (`M_complement`), so `W₁ ⊓ H₀C ≤ W₁ ⊓ M' = ⊥`. -/
theorem chiefFactor_W1_inf_H0supC_subgroupOf_eq_bot [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (data.W1.subgroupOf M) ⊓ ((chief.H0 ⊔ cSub data chief).subgroupOf M) = ⊥ := by
  have hH0CM' : ((chief.H0 ⊔ cSub data chief).subgroupOf M) ≤ (derivedInG M).subgroupOf M :=
    Subgroup.comap_mono (chiefFactor_H0supC_le_derived chief)
  rw [eq_bot_iff]
  exact le_trans (inf_le_inf_left _ hH0CM')
    (disjoint_iff.mp data.typeP.M_complement.disjoint.symm).le

/-- **`W₂ ⊄ H₀C` inside `↥M`** (the `N' = H₀C` `W2_nontrivial` input): if `W₂ ≤ H₀C` then, as
`W₂ ≤ H`, `W₂ ≤ H₀C ⊓ H = H₀` (`chiefFactor_H0supC_inf_H_eq_H0`), contradicting
`chiefFactor_W2_not_le_H0`. -/
theorem chiefFactor_W2_not_le_H0supC [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ¬ data.W2.subgroupOf M ≤ (chief.H0 ⊔ cSub data chief).subgroupOf M := by
  intro hle
  have hW2leM : data.W2 ≤ M := (data.typeP.W2_le.trans inf_le_left).trans (H_le_M data)
  have hW2H0C : data.W2 ≤ chief.H0 ⊔ cSub data chief := by
    intro y hy
    have hyM : (⟨y, hW2leM hy⟩ : ↥M) ∈ data.W2.subgroupOf M := Subgroup.mem_subgroupOf.mpr hy
    exact Subgroup.mem_subgroupOf.mp (hle hyM)
  refine chiefFactor_W2_not_le_H0 chief ?_
  have hW2H : data.W2 ≤ data.H := data.typeP.W2_le.trans inf_le_left
  have hkey : data.W2 ≤ (chief.H0 ⊔ cSub data chief) ⊓ data.H := le_inf hW2H0C hW2H
  rwa [chiefFactor_H0supC_inf_H_eq_H0 chief] at hkey

/-- **Peterfalvi (9.9.b), `|W̄₂| = p`**: the image `W̄₂ = (W₂.subgroupOf M).map(mk' H₀')` of the
cyclic factor `W₂` in the chief-factor quotient `↥M ⧸ H₀` has order `p` — the quotient chief-factor
centralizer order `|C_{H̄}(W₁)| = p` (`coprimeFrobeniusChiefFactor_card`), *not* `|W₂|` (which can
exceed `p` in type II).

The bridge is a card identity avoiding the explicit cross-quotient iso: both `W̄₂` and the quotient
`fixedByE = F.map(mk' N)` (`F = C_H(W₁)` the `W₁`-fixed points in `↥H`) are quotients
`|F|/|F ⊓ kernel|`.  Via the injective `H.subtype` (`F ↦ W₂`, `N ↦ H₀`), the kernels match
(`|F ⊓ N| = |W₂ ⊓ H₀| = |J₁|`), and `|F| = |W₂|`, so `|W̄₂| = |F|/|F⊓N| = |fixedByE| = p`.  This
gives the `p-1` reducible count once `card_reducible_Hnontrivial_induce_eq_W2_sub_one` is
instantiated on `chiefFactorQuotientHypothesis` (issue 1012, B3). -/
theorem chiefFactor_card_W2bar [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [(chief.H0.subgroupOf M).Normal] :
    Nat.card ↥((data.W2.subgroupOf M).map (QuotientGroup.mk' (chief.H0.subgroupOf M)))
      = chief.p := by
  haveI := chief.N_normal
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  -- The quotient chief-factor action and `|fixedByE| = p`.
  have hHbar : Nat.card (↥data.typeP.H ⧸ chief.N) ≠ 1 := by
    rw [chiefFactor_quotient_card chief]
    exact (Nat.one_lt_pow (Nat.card_pos (α := ↥data.typeP.W1)).ne' chief.p_prime.one_lt).ne'
  have hUnorm : ((typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).U).Normal :=
    (typeP_uW1_frobenius data.typeP hU).isNormal
  have hEcyc := typeP_quotient_fixedByE_cyclic data.typeP hU chief.N_aInvariant
  have hcard := coprimeFrobeniusChiefFactor_card
    (typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant) hUnorm chief.p_prime
    chief.quotient_elementaryAbelian chief.quotient_chiefFactor chief.U_noncentral_on_quotient
    hEcyc hHbar
  have hcopHW1 : Nat.Coprime
      (Nat.card ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) (Nat.card ↥data.typeP.H) :=
    (typeP_coprime_H_uW1 data.typeP hU).symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
  haveI : IsSolvable ↥data.typeP.H := (typeP_coprimeAction data.typeP hU).H_solvable
  -- `F = C_H(W₁)`, with `F.map(mk' N) = fixedByE` and `F.map H.subtype = W₂`.
  set F := fixedSubgroup (typeP_conjAction data.typeP)
    (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) with hF
  have hmap : F.map (QuotientGroup.mk' chief.N)
      = (typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).fixedByE :=
    map_fixedSubgroup_eq_fixedSubgroup_quotient chief.N_aInvariant hcopHW1 (Or.inr inferInstance)
  have hCHW1 : F.map data.typeP.H.subtype = data.typeP.W2 := by
    rw [hF, typeP_fixedSubgroup_map data.typeP le_sup_right, typeP_H_inf_centralizer_W1]
  -- `W₂ ≤ M` (via `W₂ ≤ H ≤ M' ≤ M`).
  have hW2M : data.typeP.W2 ≤ M := ((data.typeP.W2_le.trans inf_le_left).trans
    data.typeP.H_le).trans (Subgroup.map_subtype_le _)
  -- `|A.subgroupOf B| = |A ⊓ B|` (image under the injective `B.subtype`).
  have hcardSubOf : ∀ {K : Type u_1} [inst : Group K] (A B : Subgroup K),
      Nat.card ↥(A.subgroupOf B) = Nat.card ↥(A ⊓ B) := by
    intro K _ A B
    rw [← Subgroup.subgroupOf_map_subtype A B]
    exact Nat.card_congr (Subgroup.equivMapOfInjective (A.subgroupOf B) B.subtype
      (Subgroup.subtype_injective B)).toEquiv
  -- `|F| = |W₂|` (`H.subtype` injective) and `|fixedByE| = p`.
  have hcardF_W2 : Nat.card ↥F = Nat.card ↥data.typeP.W2 := by
    rw [← hCHW1]
    exact Nat.card_congr (Subgroup.equivMapOfInjective F data.typeP.H.subtype
      data.typeP.H.subtype_injective).toEquiv
  have hfixp : Nat.card ↥(typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).fixedByE
      = chief.p := hcard.2
  -- `|F| = |fixedByE| · |N ⊓ F|` (first iso for `mk' N` restricted to `F`).
  have hFsplit : Nat.card ↥F
      = Nat.card ↥(typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).fixedByE
        * Nat.card ↥(chief.N.subgroupOf F) := by
    rw [← hmap, ← Subgroup.nat_card_quotient_subgroupOf_eq_card_map]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  -- `|W₂.subgroupOf M| = |W̄₂| · |J₁|` (first iso for `mk' H₀'` restricted to `W₂.subgroupOf M`).
  set J₁ := (chief.H0.subgroupOf M).subgroupOf (data.typeP.W2.subgroupOf M) with hJ₁
  have hW2split : Nat.card ↥(data.typeP.W2.subgroupOf M)
      = Nat.card ↥((data.typeP.W2.subgroupOf M).map (QuotientGroup.mk' (chief.H0.subgroupOf M)))
        * Nat.card ↥J₁ := by
    rw [← Subgroup.nat_card_quotient_subgroupOf_eq_card_map]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hcardW2M : Nat.card ↥(data.typeP.W2.subgroupOf M) = Nat.card ↥data.typeP.W2 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2M).toEquiv
  -- The two kernels have equal order: `|J₁| = |N ⊓ F| = |W₂ ⊓ H₀|`.
  have hker : Nat.card ↥J₁ = Nat.card ↥(chief.N.subgroupOf F) := by
    -- `|J₁| = |(H₀.subgroupOf M) ⊓ (W₂.subgroupOf M)| = |(H₀ ⊓ W₂).subgroupOf M| = |H₀ ⊓ W₂|`.
    have hinf : (chief.H0.subgroupOf M) ⊓ (data.typeP.W2.subgroupOf M)
        = (chief.H0 ⊓ data.typeP.W2).subgroupOf M :=
      (Subgroup.comap_inf chief.H0 data.typeP.W2 M.subtype).symm
    have h1 : Nat.card ↥J₁ = Nat.card ↥(chief.H0 ⊓ data.typeP.W2 : Subgroup G) := by
      rw [hJ₁, hcardSubOf, hinf, hcardSubOf, inf_of_le_left (inf_le_right.trans hW2M)]
    -- `|N.subgroupOf F| = |N ⊓ F| = |(N ⊓ F).map H.subtype| = |H₀ ⊓ W₂|`.
    have h2 : Nat.card ↥(chief.N.subgroupOf F)
        = Nat.card ↥(chief.H0 ⊓ data.typeP.W2 : Subgroup G) := by
      rw [hcardSubOf]
      have hmapinf : (chief.N ⊓ F).map data.typeP.H.subtype
          = (chief.H0 ⊓ data.typeP.W2 : Subgroup G) := by
        rw [Subgroup.map_inf_eq chief.N F data.typeP.H.subtype data.typeP.H.subtype_injective,
          hCHW1, ← chief.H0_eq]
      rw [← hmapinf]
      exact Nat.card_congr (Subgroup.equivMapOfInjective _ data.typeP.H.subtype
        data.typeP.H.subtype_injective).toEquiv
    rw [h1, h2]
  -- Combine: `|W̄₂| · |J₁| = |W₂| = |F| = |fixedByE| · |J₁|`, cancel.
  have hposJ : 0 < Nat.card ↥J₁ := Nat.card_pos
  have hchain : Nat.card ↥((data.typeP.W2.subgroupOf M).map
        (QuotientGroup.mk' (chief.H0.subgroupOf M))) * Nat.card ↥J₁
      = chief.p * Nat.card ↥J₁ := by
    rw [← hW2split, hcardW2M, ← hcardF_W2, hFsplit, hfixp, hker]
  show Nat.card ↥((data.typeP.W2.subgroupOf M).map (QuotientGroup.mk' (chief.H0.subgroupOf M)))
    = chief.p
  exact Nat.eq_of_mul_eq_mul_right hposJ hchain

/-- **Image order under `mk'` depends only on `S ∩ N`** (general): for normal `N₁, N₂` with
`S ⊓ N₁ = S ⊓ N₂`, the images `S/(S∩Nᵢ)` have equal order, since `|S.map(mk' N)| · |S ⊓ N| = |S|`
(first isomorphism `nat_card_quotient_subgroupOf_eq_card_map`). -/
theorem nat_card_map_mk'_eq_of_inf_eq {Γ : Type*} [Group Γ] [Finite Γ]
    (S N₁ N₂ : Subgroup Γ) [N₁.Normal] [N₂.Normal] (h : S ⊓ N₁ = S ⊓ N₂) :
    Nat.card ↥(S.map (QuotientGroup.mk' N₁)) = Nat.card ↥(S.map (QuotientGroup.mk' N₂)) := by
  have hsplit : ∀ (N : Subgroup Γ) [N.Normal],
      Nat.card ↥(S.map (QuotientGroup.mk' N)) * Nat.card ↥(S ⊓ N) = Nat.card ↥S := by
    intro N _
    have hc : Nat.card ↥(N.subgroupOf S) = Nat.card ↥(S ⊓ N) := by
      rw [inf_comm, ← Subgroup.subgroupOf_map_subtype N S]
      exact Nat.card_congr (Subgroup.equivMapOfInjective (N.subgroupOf S) S.subtype
        (Subgroup.subtype_injective S)).toEquiv
    rw [← hc, ← Subgroup.nat_card_quotient_subgroupOf_eq_card_map]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf S)).symm
  have h1 := hsplit N₁
  rw [h] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans (hsplit N₂).symm)

/-- **`|W̄₂'| = p` for the `M/H₀C` quotient** (issue 1012, step A): the chief-factor image `W̄₂'` in
`↥M ⧸ H₀C` keeps order `p`.  Reduces to the `H₀` case (`chiefFactor_card_W2bar`): the kernels
coincide, `W₂ ⊓ H₀C = W₂ ⊓ H₀` (as `W₂ ≤ H` and `(H₀C) ⊓ H = H₀` by
`chiefFactor_H0supC_inf_H_eq_H0`), so by `nat_card_map_mk'_eq_of_inf_eq` the images have equal
order. -/
theorem chiefFactor_card_W2bar_H0supC [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [(chief.H0.subgroupOf M).Normal] [((chief.H0 ⊔ cSub data chief).subgroupOf M).Normal] :
    Nat.card ↥((data.W2.subgroupOf M).map
        (QuotientGroup.mk' ((chief.H0 ⊔ cSub data chief).subgroupOf M))) = chief.p := by
  have hW2H : data.W2 ≤ data.H := data.typeP.W2_le.trans inf_le_left
  have hG_eq : data.W2 ⊓ (chief.H0 ⊔ cSub data chief) = data.W2 ⊓ chief.H0 := by
    apply le_antisymm
    · refine le_inf inf_le_left ?_
      calc data.W2 ⊓ (chief.H0 ⊔ cSub data chief)
          ≤ data.H ⊓ (chief.H0 ⊔ cSub data chief) := inf_le_inf_right _ hW2H
        _ = (chief.H0 ⊔ cSub data chief) ⊓ data.H := inf_comm _ _
        _ = chief.H0 := chiefFactor_H0supC_inf_H_eq_H0 chief
    · exact inf_le_inf_left _ le_sup_left
  have hinf : (data.W2.subgroupOf M) ⊓ ((chief.H0 ⊔ cSub data chief).subgroupOf M)
      = (data.W2.subgroupOf M) ⊓ (chief.H0.subgroupOf M) := by
    simp only [Subgroup.subgroupOf, ← Subgroup.comap_inf, hG_eq]
  rw [nat_card_map_mk'_eq_of_inf_eq (data.W2.subgroupOf M)
    ((chief.H0 ⊔ cSub data chief).subgroupOf M) (chief.H0.subgroupOf M) hinf]
  exact chiefFactor_card_W2bar chief

/-- **Induction-inflation commute, term level** (general): for `f : Γ →* Q` with `ker f ≤ H`, the
induced-character term of the inflated `compHom (f.subgroupMap H) χ̄` at `(x, g)` equals the
induced-character term of `χ̄` on `H.map f` at `(f x, f g)`.  The conjugate `x⁻¹gx ∈ H` iff
`f(x⁻¹gx) = (fx)⁻¹(fg)(fx) ∈ H.map f` (`comap_map_eq_self`, `ker f ≤ H`), and the values agree
(`χ̄⟨f(x⁻¹gx)⟩`).  Term level of the (8.4.d) induction-inflation commute (issue 1012, B2). -/
theorem induceTerm_compHom_subgroupMap {Γ Q : Type*} [Group Γ] [Group Q]
    (f : Γ →* Q) {H : Subgroup Γ} (hker : f.ker ≤ H)
    (χbar : ClassFunction ↥(H.map f) ℂ) (x g : Γ) :
    ClassFunction.induceTerm H (ClassFunction.compHom (f.subgroupMap H) χbar) x g
      = ClassFunction.induceTerm (H.map f) χbar (f x) (f g) := by
  have hmem : (f x)⁻¹ * (f g) * (f x) ∈ H.map f ↔ x⁻¹ * g * x ∈ H := by
    rw [← map_inv, ← map_mul, ← map_mul, ← Subgroup.mem_comap, Subgroup.comap_map_eq_self hker]
  by_cases hx : x⁻¹ * g * x ∈ H
  · rw [ClassFunction.induceTerm_of_mem _ hx, ClassFunction.induceTerm_of_mem _ (hmem.mpr hx),
      ClassFunction.compHom_apply]
    have heq : (f.subgroupMap H) ⟨x⁻¹ * g * x, hx⟩
        = (⟨(f x)⁻¹ * (f g) * (f x), hmem.mpr hx⟩ : ↥(H.map f)) := by
      apply Subtype.ext
      change f (x⁻¹ * g * x) = (f x)⁻¹ * (f g) * (f x)
      rw [map_mul, map_mul, map_inv]
    rw [heq]
  · rw [ClassFunction.induceTerm_of_not_mem _ hx,
      ClassFunction.induceTerm_of_not_mem _ (fun h => hx (hmem.mp h))]

/-- **The fiber of `mk' N` over `q` is equinumerous to `N`** (`x ↦ x₀⁻¹ x` for a representative
`x₀`).  Used for the `|N|`-fold fiberwise sum in the (8.4.d) induction-inflation commute. -/
theorem card_fiber_mk'_eq {Γ : Type*} [Group Γ] {N : Subgroup Γ} [N.Normal] (q : Γ ⧸ N) :
    Nat.card {x : Γ // QuotientGroup.mk' N x = q} = Nat.card ↥N := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective N q
  refine Nat.card_congr ⟨fun p => ⟨x₀⁻¹ * (p : Γ), QuotientGroup.eq.mp p.2.symm⟩,
    fun n => ⟨x₀ * (n : Γ), ?_⟩, ?_, ?_⟩
  · refine QuotientGroup.eq.mpr ?_
    have he : (x₀ * (n : Γ))⁻¹ * x₀ = ((n : Γ))⁻¹ := by group
    rw [he]; exact inv_mem n.2
  · intro p; ext; show x₀ * (x₀⁻¹ * (p : Γ)) = (p : Γ); group
  · intro n; ext; show x₀⁻¹ * (x₀ * (n : Γ)) = (n : Γ); group

/-- **`|N|`-fold fiberwise sum over a quotient** (general): `∑_{x:Γ} g(x N) = |N| • ∑_{q:Γ/N} g q`.
Each fiber of `mk' N` has `|N|` elements (`card_fiber_mk'_eq`), and the summand is constant on
fibers.  This is step 2 of the (8.4.d) induction-inflation commute (issue 1012, B2). -/
theorem sum_comp_mk'_eq {Γ : Type*} [Group Γ] [Fintype Γ] (N : Subgroup Γ) [N.Normal]
    [DecidablePred (· ∈ N)] {M : Type*} [AddCommMonoid M] (g : Γ ⧸ N → M) :
    (∑ x : Γ, g (QuotientGroup.mk' N x)) = Nat.card ↥N • ∑ q : Γ ⧸ N, g q := by
  classical
  rw [Finset.smul_sum,
    ← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (Γ ⧸ N)))
      (fun (x : Γ) (_ : x ∈ Finset.univ) => Finset.mem_univ (QuotientGroup.mk' N x))]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.sum_congr rfl (g := fun _ => g q)
      (fun x hx => by rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const]
  congr 1
  rw [← card_fiber_mk'_eq q, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **`|H| = |N| · |H/N|`** (`N ◁ Γ`, `N ≤ H`): the image `H.map (mk' N)` of `H` in `Γ/N` has order
`|H|/|N|`, since the restriction `mk' N |_H : ↥H → ↥(H.map (mk' N))` has kernel `N` and is onto
(Noether's first isomorphism, `quotientKerEquivRange`).  The `|H|⁻¹·|N| = |H/N|⁻¹` normalization
(step 3) of the (8.4.d) induction-inflation commute (issue 1012, B2). -/
theorem card_eq_card_subgroup_mul_card_map_mk' {Γ : Type*} [Group Γ] [Fintype Γ]
    {N H : Subgroup Γ} [N.Normal] (hNH : N ≤ H) :
    Nat.card ↥H = Nat.card ↥N * Nat.card ↥(H.map (QuotientGroup.mk' N)) := by
  set φ := (QuotientGroup.mk' N).comp H.subtype with hφ
  have hrange : φ.range = H.map (QuotientGroup.mk' N) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker = N.subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (h : Γ)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv, mul_comm]

/-- **Induction-inflation commute** (B2 crux, for `f = mk' N`): for `N ◁ Γ`, `N ≤ H`, the induced
character of the inflated `compHom ((mk' N).subgroupMap H) χ̄` on `Γ` equals the inflation
`compHom (mk' N)` of the induced character of `χ̄` on the image `H.map (mk' N) ⊆ Γ/N`.

Term-by-term equality (`induceTerm_compHom_subgroupMap`), the `|N|`-fold fiberwise sum
(`sum_comp_mk'_eq`), and the `|H| = |N|·|H/N|` normalization
(`card_eq_card_subgroup_mul_card_map_mk'`) combine to cancel the `|N|` factor.  This is the
character-level engine of Peterfalvi's (8.4.d) identification of `𝒮(H₀)` with the `M/H₀`-induction
family (issue 1012, B2). -/
theorem induce_compHom_subgroupMap_mk' {Γ : Type*} [Group Γ] [Fintype Γ] (N : Subgroup Γ) [N.Normal]
    [DecidablePred (· ∈ N)] {H : Subgroup Γ} (hNH : N ≤ H)
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥(H.map (QuotientGroup.mk' N)) : ℂ)]
    (χbar : ClassFunction ↥(H.map (QuotientGroup.mk' N)) ℂ) :
    ClassFunction.induce H (ClassFunction.compHom ((QuotientGroup.mk' N).subgroupMap H) χbar)
      = ClassFunction.compHom (QuotientGroup.mk' N)
          (ClassFunction.induce (H.map (QuotientGroup.mk' N)) χbar) := by
  have hker : (QuotientGroup.mk' N).ker ≤ H := by rw [QuotientGroup.ker_mk']; exact hNH
  haveI : Invertible (Nat.card ↥N : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hnorm : (Nat.card ↥H : ℂ)
      = (Nat.card ↥N : ℂ) * (Nat.card ↥(H.map (QuotientGroup.mk' N)) : ℂ) := by
    rw [← Nat.cast_mul, card_eq_card_subgroup_mul_card_map_mk' hNH]
  have hkey : ⅟(Nat.card ↥H : ℂ) * (Nat.card ↥N : ℂ)
      = ⅟(Nat.card ↥(H.map (QuotientGroup.mk' N)) : ℂ) := by
    rw [invOf_eq_inv, invOf_eq_inv, hnorm, mul_inv, mul_comm ((Nat.card ↥N : ℂ)⁻¹), mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), mul_one]
  apply ClassFunction.ext
  intro g
  rw [ClassFunction.compHom_apply, ClassFunction.induce_apply, ClassFunction.induce_apply,
    Finset.sum_congr rfl (fun x _ =>
      induceTerm_compHom_subgroupMap (QuotientGroup.mk' N) hker χbar x g),
    sum_comp_mk'_eq N (fun x' => ClassFunction.induceTerm (H.map (QuotientGroup.mk' N)) χbar x'
      (QuotientGroup.mk' N g)), nsmul_eq_mul, ← mul_assoc, hkey]

open OddOrder.Peterfalvi.S06 in
/-- **Generic chief-factor quotient `Hypothesis`** over a normal `N' ◁ ↥M` with `N' ≤ M'` and the
non-degeneracy `W₁ ⊓ N' = ⊥`, `W₂ ⊄ N'`: the certain-type structural hypothesis
`S06.Hypothesis (↥M ⧸ N')` with `K̄ = M'/N'`, `W̄₁ = W₁ N'/N'`, `W̄₂ = W₂ N'/N'`.  Both the chief
factor kernel `N' = H₀` and the join `N' = H₀ ⊔ C` instantiate this (Coq `PFsection9` `nb_redM`),
the unifying conditions being exactly `N' ◁ M`, `N' ≤ HU`, and (through the non-degeneracy)
`N' ∩ H = H₀`.  `isComplement` from `IsComplement'.map_mk'`, `centralizer_W2` from
`centralizer_W2bar_quotient`, `W2_nontrivial` from `W₂ ⊄ N'` directly. -/
noncomputable def chiefFactorQuotientHypothesisGen [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (N' : Subgroup ↥M) [N'.Normal]
    (hN'le : N' ≤ (derivedInG M).subgroupOf M)
    (hW1inf : data.W1.subgroupOf M ⊓ N' = ⊥)
    (hW2notle : ¬ data.W2.subgroupOf M ≤ N')
    (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1)) :
    Hypothesis (↥M ⧸ N') := by
  haveI := data.typeP.W1_cyclic
  haveI := data.typeP.W2_cyclic
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hW2leM' : data.W2 ≤ derivedInG M :=
    data.typeP.W2_le.trans (le_trans inf_le_right (Subgroup.map_subtype_le _))
  have hW2leM : data.W2 ≤ M := hW2leM'.trans hM'le
  have hKnorm : ((derivedInG M).subgroupOf M).Normal := by
    rw [show (derivedInG M).subgroupOf M = commutator ↥M by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]]
    infer_instance
  have hcardK : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv
  have hcardW1 : Nat.card ↥(data.W1.subgroupOf M) = Nat.card ↥data.W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeP.W1_le).toEquiv
  have hcopW1 : Nat.Coprime (Nat.card ↥data.W1) (Nat.card ↥N') :=
    hHall.symm.coprime_dvd_right (hcardK ▸ Subgroup.card_dvd_of_le hN'le)
  refine
    { K := ((derivedInG M).subgroupOf M).map (QuotientGroup.mk' N')
      W1 := (data.W1.subgroupOf M).map (QuotientGroup.mk' N')
      W2 := (data.W2.subgroupOf M).map (QuotientGroup.mk' N')
      K_normal := hKnorm.map _ (QuotientGroup.mk'_surjective _)
      isComplement := by
        have hcop : Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M))
            (Nat.card ↥(data.W1.subgroupOf M)) := by rw [hcardK, hcardW1]; exact hHall
        exact data.typeP.M_complement.map_mk' hcop N'
      W1_nontrivial := ?_
      W1_cyclic := ?_
      card_coprime :=
        (hHall.coprime_dvd_left (hcardK ▸ Subgroup.card_map_dvd _ _)).coprime_dvd_right
          (hcardW1 ▸ Subgroup.card_map_dvd _ _)
      W2_nontrivial := ?_
      W2_cyclic := ?_
      W2_le_K := Subgroup.map_mono (Subgroup.comap_mono hW2leM')
      centralizer_W2 := fun x hx hx1 => centralizer_W2bar_quotient N' hN'le hcopW1 x hx hx1
      W_odd := ?_ }
  · rw [ne_eq, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    intro hle
    have hbot : data.W1.subgroupOf M = ⊥ :=
      le_bot_iff.mp (le_trans (le_inf le_rfl hle) hW1inf.le)
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    exact data.typeP.W1_nontrivial (disjoint_self.mp (hbot.mono_right data.typeP.W1_le))
  · haveI : IsCyclic ↥(data.W1.subgroupOf M) :=
      isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe data.typeP.W1_le).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe data.typeP.W1_le).injective
    rw [show (data.W1.subgroupOf M).map (QuotientGroup.mk' N')
        = ((QuotientGroup.mk' N').comp (data.W1.subgroupOf M).subtype).range by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]]
    exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  · rw [ne_eq, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hW2notle
  · haveI : IsCyclic ↥data.W2 := data.typeP.W2_cyclic
    haveI : IsCyclic ↥(data.W2.subgroupOf M) :=
      isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hW2leM).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hW2leM).injective
    rw [show (data.W2.subgroupOf M).map (QuotientGroup.mk' N')
        = ((QuotientGroup.mk' N').comp (data.W2.subgroupOf M).subtype).range by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]]
    exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  · have hdvd : Nat.card ↥(((data.W1.subgroupOf M).map (QuotientGroup.mk' N'))
        ⊔ ((data.W2.subgroupOf M).map (QuotientGroup.mk' N')))
        ∣ Nat.card G :=
      dvd_trans (Subgroup.card_subgroup_dvd_card _)
        (dvd_trans (Subgroup.index_dvd_card _) (Subgroup.card_subgroup_dvd_card M))
    rcases Nat.even_or_odd (Nat.card ↥(((data.W1.subgroupOf M).map (QuotientGroup.mk' N'))
        ⊔ ((data.W2.subgroupOf M).map (QuotientGroup.mk' N')))) with he | ho
    · have h2G : 2 ∣ Nat.card G := dvd_trans he.two_dvd hdvd
      rw [Nat.odd_iff] at hodd
      omega
    · exact ho

open OddOrder.Peterfalvi.S06 in
/-- **Peterfalvi (8.4.d): Hypothesis (4.2) holds for `L = M/H₀`.**  The certain-type structural
hypothesis `S06.Hypothesis (↥M ⧸ H₀)` with `K = M'/H₀`, `W̄₁ = W₁ H₀/H₀`, `W̄₂ = W₂ H₀/H₀`.  Built
from the type-`P` data of `M` by pushing the (8.4) datum through the quotient `mk' H₀`:
`isComplement` from `M = M' ⋊ W₁` (`IsComplement'.map_mk'`), `centralizer_W2` from the coprime
centralizer-quotient (`chiefFactor_centralizer_W2bar`), `W2_nontrivial` from `W₂ ⊄ H₀`
(`chiefFactor_W2_not_le_H0`).  The Hall coprimality `gcd(|M'|, |W₁|) = 1` is the input `hHall`
(as in `typePData_toS06Hypothesis`).  This is the quotient `L = M/H₀` of issue 1012's reducible
counts; the §9 family `𝒮(H₀)` is its induction family. -/
noncomputable def chiefFactorQuotientHypothesis [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [(chief.H0.subgroupOf M).Normal] (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1)) :
    Hypothesis (↥M ⧸ (chief.H0.subgroupOf M)) := by
  have hW2leM : data.W2 ≤ M :=
    (data.typeP.W2_le.trans (le_trans inf_le_right (Subgroup.map_subtype_le _))).trans
      (Subgroup.map_subtype_le _)
  refine chiefFactorQuotientHypothesisGen chief (chief.H0.subgroupOf M)
    (Subgroup.comap_mono (chief.H0_lt_H.le.trans data.typeP.H_le))
    (chiefFactor_W1_inf_H0_subgroupOf_eq_bot chief) ?_ hodd hHall
  intro hle
  refine chiefFactor_W2_not_le_H0 chief (fun y hy => ?_)
  have hmem : (⟨y, hW2leM hy⟩ : ↥M) ∈ data.W2.subgroupOf M := Subgroup.mem_subgroupOf.mpr hy
  exact Subgroup.mem_subgroupOf.mp (hle hmem)


/-- **`|W̄₂| = p` for the `M/H₀` quotient hypothesis** (issue 1012, B3b bridge): the `W₂` field of
`chiefFactorQuotientHypothesis` is `W̄₂ = (W₂.subgroupOf M).map(mk' H₀')`, whose order is `p` by
`chiefFactor_card_W2bar`. -/
theorem chiefFactorQuotient_card_W2_eq_p [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [(chief.H0.subgroupOf M).Normal] (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1)) :
    Nat.card ↥(chiefFactorQuotientHypothesis chief hodd hHall).W2 = chief.p :=
  chiefFactor_card_W2bar chief

/-- The `K` of the `M/H₀`-`Hypothesis` is the `mk'`-image of the §9 induction carrier `HU = huSub`
(`huSub_eq_derivedInG_subgroupOf`).  This bridges the §6 reducible count (over `Irr(K̄)`,
`card_reducible_Hnontrivial_induce_eq_W2_sub_one`) to the §9 family `𝒮(H₀)` whose members are
`induceHU`-inductions of inflations from `K̄ = HU/H₀` (issue 1012, B2 bijection). -/
theorem chiefFactorQuotientHypothesis_K_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [(chief.H0.subgroupOf M).Normal] (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1)) :
    (chiefFactorQuotientHypothesis chief hodd hHall).K
      = (huSub data).map (QuotientGroup.mk' (chief.H0.subgroupOf M)) := by
  show ((derivedInG M).subgroupOf M).map (QuotientGroup.mk' (chief.H0.subgroupOf M))
      = (huSub data).map (QuotientGroup.mk' (chief.H0.subgroupOf M))
  rw [huSub_eq_derivedInG_subgroupOf]

/-- The `K` of the generic `chiefFactorQuotientHypothesisGen` is the `mk' N'`-image of the §9
induction carrier `HU = huSub` (`huSub_eq_derivedInG_subgroupOf`); same bridge as the `H₀` case,
generic in `N'`. -/
theorem chiefFactorQuotientHypothesisGen_K_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (N' : Subgroup ↥M) [N'.Normal]
    (hN'le : N' ≤ (derivedInG M).subgroupOf M)
    (hW1inf : data.W1.subgroupOf M ⊓ N' = ⊥)
    (hW2notle : ¬ data.W2.subgroupOf M ≤ N')
    (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1)) :
    (chiefFactorQuotientHypothesisGen chief N' hN'le hW1inf hW2notle hodd hHall).K
      = (huSub data).map (QuotientGroup.mk' N') := by
  show ((derivedInG M).subgroupOf M).map (QuotientGroup.mk' N')
      = (huSub data).map (QuotientGroup.mk' N')
  rw [huSub_eq_derivedInG_subgroupOf]

/-- **`H₀ ≤ HU` inside `↥M`** (`H₀ < H ≤ M' = HU`): the inclusion needed to specialize the
induction-inflation commute `induce_compHom_subgroupMap_mk'` to `N = H₀`, `H = huSub` for the §9↔§6
reducibility bridge (issue 1012, B2 bijection).  The commute itself is applied inline in the
bijection assembly (under a single `letI : Fintype ↥M`) — stating it standalone fights the
statement-level `Fintype (↥M ⧸ H₀)` that `ClassFunction.induce`'s sum needs. -/
theorem chiefFactor_H0_le_huSub {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    (chief.H0.subgroupOf M) ≤ huSub data := by
  rw [huSub_eq_derivedInG_subgroupOf]
  exact Subgroup.comap_mono (chief.H0_lt_H.le.trans data.typeP.H_le)

/-- **(9.7) span step** (general form): in an irreducible `A`-action on a group `H` (every
`A`-invariant subgroup is `⊥` or `⊤`), any nonzero subgroup `S₀` generates `H` under its
`A`-orbit — `⨆_{a} φ(a) • S₀ = ⊤`.  The orbit join is `A`-invariant (reindex `a ↦ h·a`) and
contains `S₀ ≠ ⊥`, hence is `⊤`.  Applied to the `U W₁`-irreducible chief factor `H̄` with `S₀` a
minimal `U`-invariant piece, this shows `H̄` is spanned by the `W₁`-conjugates of `S₀` — the entry
point to the Clifford decomposition. -/
theorem iSup_smul_eq_top_of_irreducible {A H : Type*} [Group A] [Group H] {φ : A →* MulAut H}
    (hirr : ∀ J : Subgroup H, IsAInvariant φ J → J = ⊥ ∨ J = ⊤)
    {S₀ : Subgroup H} (hS₀ : S₀ ≠ ⊥) :
    ⨆ (a : A), φ a • S₀ = ⊤ := by
  set T := ⨆ (a : A), φ a • S₀ with hT
  -- `T` is `φ`-invariant: `φ h • T = ⨆ a, φ (h·a) • S₀ = T` by reindexing `a ↦ h·a`.
  have hTinv : IsAInvariant φ T := by
    intro h
    have h1 : φ h • T = ⨆ (a : A), φ (h * a) • S₀ := by
      rw [hT, pointwise_mulAut_smul_eq_map, Subgroup.map_iSup]
      exact iSup_congr fun a => by
        rw [← pointwise_mulAut_smul_eq_map, smul_smul, ← map_mul]
    rw [h1]
    exact le_antisymm (iSup_le fun a => le_iSup_of_le (h * a) le_rfl)
      (iSup_le fun a => le_iSup_of_le (h⁻¹ * a)
        (le_of_eq (by rw [← mul_assoc, mul_inv_cancel, one_mul])))
  -- `T ≠ ⊥` (contains the `a = 1` term `S₀`), so irreducibility forces `T = ⊤`.
  have hTne : T ≠ ⊥ := by
    intro hbot
    refine hS₀ (le_bot_iff.mp (hbot ▸ ?_))
    have := le_iSup (fun a : A => φ a • S₀) 1
    rwa [map_one, one_smul] at this
  exact (hirr T hTinv).resolve_left hTne

/-- **(9.7) order step** (general form): a finite group `K` whose elements pairwise commute (e.g. an
elementary abelian `p`-group) that is the join `⨆ i, S i` of a family of `φ`-invariant subgroups,
each either trivial or `φ`-irreducible of a common order `n`, has order a power of `n`.

Extract a maximal `SupIndep` subfamily of the nonzero pieces.  By irreducibility it still spans `K`:
any piece meets the partial join in a `φ`-invariant subgroup `≤` the piece, hence `⊥` or the whole
piece — and `⊥` would let us enlarge the subfamily, contradicting maximality.  An independent
commuting spanning family realises `K` as the internal direct product `∏ ↥(S i)` (via
`Subgroup.noncommPiCoprod`, injective from independence and surjective from spanning), so
`|K| = ∏ |S i| = ∏ n = n ^ k`.

Applied to the chief factor `H̄` under the restricted `U`-action, with the pieces the `U W₁`-orbit of
a minimal `U`-invariant `S₀` (each `U`-irreducible of order `|S₀| = p^d`), this gives `|H̄| = (p^d)^k`,
i.e. `q = d·k` — the divisibility `d ∣ q` underlying the Clifford dichotomy (`q` prime ⟹ `d ∈ {1, q}`). -/
theorem exists_supIndep_aInvariant_family_of_iSup {K : Type*} [Group K] [Finite K]
    {A : Type*} [Group A] {φ : A →* MulAut K} {ι : Type*} [Finite ι]
    {S : ι → Subgroup K} {n : ℕ}
    (hcomm : ∀ x y : K, Commute x y)
    (hspan : ⨆ i, S i = ⊤)
    (hinv : ∀ i, IsAInvariant φ (S i))
    (hirr : ∀ i, ∀ J : Subgroup K, IsAInvariant φ J → J ≤ S i → J = ⊥ ∨ J = S i)
    (hcard : ∀ i, S i ≠ ⊥ → Nat.card ↥(S i) = n) :
    ∃ t : Finset ι, t.SupIndep S ∧ (∀ i ∈ t, S i ≠ ⊥) ∧ (⨆ i ∈ t, S i = ⊤) ∧
      Nat.card K = n ^ t.card := by
  classical
  -- `K` is abelian, so its subgroup lattice is modular (used to enlarge `SupIndep` families).
  letI : CommGroup K := { (inferInstance : Group K) with mul_comm := fun a b => (hcomm a b).eq }
  -- Candidate finsets: `SupIndep` subfamilies of nonzero pieces.
  set cands : Finset (Finset ι) :=
    Finset.univ.filter (fun t => t.SupIndep S ∧ ∀ i ∈ t, S i ≠ ⊥) with hcands
  have hmem_cands : ∀ {t : Finset ι}, t ∈ cands ↔ t.SupIndep S ∧ ∀ i ∈ t, S i ≠ ⊥ := by
    intro t; rw [hcands, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)
  have hempty : (∅ : Finset ι) ∈ cands :=
    hmem_cands.mpr ⟨Finset.supIndep_empty S, by simp⟩
  -- Choose a candidate of maximal cardinality.
  obtain ⟨t, ht_mem, ht_max⟩ := cands.exists_max_image Finset.card ⟨∅, hempty⟩
  obtain ⟨ht_si, ht_ne⟩ := hmem_cands.mp ht_mem
  -- The maximal subfamily already spans `K`.
  have hspan_t : ⨆ i ∈ t, S i = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hspan]
    refine iSup_le fun j => ?_
    by_cases hj0 : S j = ⊥
    · rw [hj0]; exact bot_le
    · have hBinv : IsAInvariant φ (⨆ i ∈ t, S i) :=
        IsAInvariant.iSup fun i => IsAInvariant.iSup fun _ => hinv i
      rcases hirr j (S j ⊓ ⨆ i ∈ t, S i) (IsAInvariant.inf (hinv j) hBinv) inf_le_left with
        hbot | heq
      · -- `S j ⊓ B = ⊥`: enlarging `t` by `j` stays a candidate, contradicting maximality.
        exfalso
        have hjt : j ∉ t := fun hj => hj0 (by
          have hle : S j ≤ ⨆ i ∈ t, S i :=
            le_iSup_of_le j (le_iSup_of_le hj le_rfl)
          rwa [inf_eq_left.mpr hle] at hbot)
        have hdisj : Disjoint (S j) (t.sup S) := by
          rw [Finset.sup_eq_iSup]; exact disjoint_iff.mpr hbot
        have hins_ne : ∀ i ∈ insert j t, S i ≠ ⊥ := by
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hj0
          · exact ht_ne i hi
        have hins_mem : insert j t ∈ cands := hmem_cands.mpr ⟨ht_si.insert hdisj, hins_ne⟩
        have hle_card := ht_max (insert j t) hins_mem
        rw [Finset.card_insert_of_notMem hjt] at hle_card
        omega
      · exact inf_eq_left.mp heq
  -- The independent, commuting, spanning subfamily makes `K` the internal direct product `∏ S i`.
  have hcomm_pair : Pairwise fun i j : (t : Finset ι) =>
      ∀ x y : K, x ∈ S ↑i → y ∈ S ↑j → Commute x y :=
    fun _ _ _ x y _ _ => hcomm x y
  have hrange : (Subgroup.noncommPiCoprod hcomm_pair).range = ⊤ := by
    rw [Subgroup.noncommPiCoprod_range, iSup_subtype]; exact hspan_t
  have hbij : Function.Bijective (Subgroup.noncommPiCoprod hcomm_pair) :=
    ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep ht_si.independent,
      MonoidHom.range_eq_top.mp hrange⟩
  refine ⟨t, ht_si, ht_ne, hspan_t, ?_⟩
  have hfac : ∀ i : (t : Finset ι), Nat.card ↥(S ↑i) = n := fun i => hcard ↑i (ht_ne ↑i i.2)
  calc Nat.card K = Nat.card (∀ i : (t : Finset ι), ↥(S ↑i)) :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = ∏ i : (t : Finset ι), Nat.card ↥(S ↑i) := Nat.card_pi
    _ = ∏ _i : (t : Finset ι), n := Finset.prod_congr rfl (fun i _ => hfac i)
    _ = n ^ t.card := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

/-- **(9.7) order step** (cardinality corollary): a finite group `K` whose elements pairwise commute,
the join `⨆ i, S i` of `φ`-invariant subgroups each trivial or `φ`-irreducible of common order `n`,
has order a power of `n`.  Forgets the `SupIndep` partition of
`exists_supIndep_aInvariant_family_of_iSup`. -/
theorem card_eq_pow_of_iSup_aInvariant_irreducible {K : Type*} [Group K] [Finite K]
    {A : Type*} [Group A] {φ : A →* MulAut K} {ι : Type*} [Finite ι]
    {S : ι → Subgroup K} {n : ℕ}
    (hcomm : ∀ x y : K, Commute x y)
    (hspan : ⨆ i, S i = ⊤)
    (hinv : ∀ i, IsAInvariant φ (S i))
    (hirr : ∀ i, ∀ J : Subgroup K, IsAInvariant φ J → J ≤ S i → J = ⊥ ∨ J = S i)
    (hcard : ∀ i, S i ≠ ⊥ → Nat.card ↥(S i) = n) :
    ∃ k, Nat.card K = n ^ k :=
  let ⟨t, _, _, _, h⟩ := exists_supIndep_aInvariant_family_of_iSup hcomm hspan hinv hirr hcard
  ⟨t.card, h⟩

/-! ### (9.7) Clifford orbit: translates of a `U`-irreducible piece

The Clifford decomposition restricts the `U W₁`-action on `H̄` to the normal kernel `U` and reads
off the orbit of a minimal `U`-invariant `S₀` under the full action.  The three lemmas below are the
group-theoretic core: an `A`-translate `φ a • S₀` of a `U`-invariant (resp. `U`-irreducible)
subgroup is again `U`-invariant (resp. `U`-irreducible) when `U ◁ A`, and translation preserves
order.  Combined with the spanning step `iSup_smul_eq_top_of_irreducible` and the order step
`card_eq_pow_of_iSup_aInvariant_irreducible`, they give `|H̄| = |S₀|^k`, hence `q = d·k`. -/

/-- **Clifford orbit, invariance.** If `U ◁ A` acts on `K` through `φ` and `S₀` is `U`-invariant
(invariant under `φ` restricted to `U`), then every `A`-translate `φ a • S₀` is again `U`-invariant:
for `u ∈ U`, `φ u • (φ a • S₀) = φ (u·a) • S₀ = φ a • (φ (a⁻¹·u·a) • S₀) = φ a • S₀` since
`a⁻¹·u·a ∈ U`. -/
theorem isAInvariant_comp_subtype_pointwise_smul {A K : Type*} [Group A] [Group K]
    {φ : A →* MulAut K} {U : Subgroup A} (hU : U.Normal)
    {S₀ : Subgroup K} (hS₀ : IsAInvariant (φ.comp U.subtype) S₀) (a : A) :
    IsAInvariant (φ.comp U.subtype) (φ a • S₀) := by
  intro u
  show φ ↑u • (φ a • S₀) = φ a • S₀
  have hmem : a⁻¹ * (↑u : A) * a ∈ U := by
    have h := hU.conj_mem (↑u) u.2 a⁻¹; rwa [inv_inv] at h
  rw [smul_smul, ← map_mul,
    show (↑u : A) * a = a * (a⁻¹ * ↑u * a) by group, map_mul, ← smul_smul]
  congr 1
  exact hS₀ ⟨a⁻¹ * ↑u * a, hmem⟩

/-- **Clifford orbit, irreducibility.** `A`-translates of a `U`-irreducible (minimal nonzero
`U`-invariant) subgroup `S₀` are again `U`-irreducible: a `U`-invariant `J ≤ φ a • S₀` pulls back to
`φ a⁻¹ • J ≤ S₀`, which is `⊥` or `S₀`, so `J = φ a • (φ a⁻¹ • J)` is `⊥` or `φ a • S₀`. -/
theorem forall_aInvariant_le_pointwise_smul {A K : Type*} [Group A] [Group K]
    {φ : A →* MulAut K} {U : Subgroup A} (hU : U.Normal) {S₀ : Subgroup K}
    (hirr₀ : ∀ J : Subgroup K, IsAInvariant (φ.comp U.subtype) J → J ≤ S₀ → J = ⊥ ∨ J = S₀)
    (a : A) (J : Subgroup K) (hJinv : IsAInvariant (φ.comp U.subtype) J) (hJle : J ≤ φ a • S₀) :
    J = ⊥ ∨ J = φ a • S₀ := by
  have hback : φ a • (φ a⁻¹ • J) = J := by
    rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  have hJ'inv : IsAInvariant (φ.comp U.subtype) (φ a⁻¹ • J) :=
    isAInvariant_comp_subtype_pointwise_smul hU hJinv a⁻¹
  have hJ'le : φ a⁻¹ • J ≤ S₀ := by
    have h := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := φ a⁻¹)).mpr hJle
    rwa [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h
  rcases hirr₀ (φ a⁻¹ • J) hJ'inv hJ'le with h | h
  · exact Or.inl (by rw [← hback, h, Subgroup.smul_bot])
  · exact Or.inr (by rw [← hback, h])

/-- **Clifford orbit, order.** Translation by an automorphism preserves order: `|φ a • S| = |S|`. -/
theorem card_pointwise_smul {A K : Type*} [Group A] [Group K] [Finite K]
    (φ : A →* MulAut K) (a : A) (S : Subgroup K) :
    Nat.card ↥(φ a • S) = Nat.card ↥S :=
  (Nat.card_congr (Subgroup.equivMapOfInjective S (φ a).toMonoidHom (φ a).injective).toEquiv).symm

/-! ### (9.7) The Singer mechanism for the chief factor (Clifford case (b))

When `U` acts irreducibly on the chief factor `H̄` (case (b)), the commutant `End_{𝔽ₚ[U]}(H̄)` is a
field, so the image of `U` in `Aut(H̄)` is cyclic of order dividing `p^q - 1`.  We package this at
the subgroup level via `SingerField`: an abelian group acting faithfully and irreducibly on an
elementary abelian `p`-group is cyclic with order dividing `|K| - 1`. -/

open OddOrder.RepresentationTheory in
/-- The descended representation `elabRepresentation p φ` on `Additive K` is irreducible exactly when
the `φ`-action is irreducible at the subgroup level (`K` nontrivial; every `φ`-invariant subgroup of
`K` is `⊥` or `⊤`).  `ZMod p`-submodules of `Additive K` are the subgroups of `K`
(`AddSubgroup.toZModSubmodule`/`toSubgroup'`) and the action correspondence is
`elabRepresentation_apply`.  Stated as `IsSimpleOrder (Subrepresentation …)` (= `IsIrreducible`,
definitionally) to avoid pulling in the `Field (ZMod p)` instance and its `ZMod`-semiring diamond. -/
theorem elabRepresentation_isIrreducible {A K : Type*} [Group A] [CommGroup K] {p : ℕ}
    [Module (ZMod p) (Additive K)] {φ : A →* MulAut K} (hnt : Nontrivial K)
    (hirr : ∀ J : Subgroup K, IsAInvariant φ J → J = ⊥ ∨ J = ⊤) :
    IsSimpleOrder (Subrepresentation (elabRepresentation p φ)) := by
  classical
  set Φ : Submodule (ZMod p) (Additive K) ≃o Subgroup K :=
    (AddSubgroup.toZModSubmodule p).symm.trans AddSubgroup.toSubgroup' with hΦ
  have hmem : ∀ (W : Submodule (ZMod p) (Additive K)) (x : K),
      x ∈ Φ W ↔ Additive.ofMul x ∈ W := fun W x => by
    simp only [hΦ, OrderIso.trans_apply, AddSubgroup.mem_toSubgroup',
      AddSubgroup.toZModSubmodule_symm, Submodule.mem_toAddSubgroup]
  have hbot_ne_top : (⊥ : Subrepresentation (elabRepresentation p φ)) ≠ ⊤ := by
    haveI : Nontrivial (Additive K) := hnt
    exact fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  haveI : Nontrivial (Subrepresentation (elabRepresentation p φ)) := ⟨⊥, ⊤, hbot_ne_top⟩
  refine IsSimpleOrder.of_forall_eq_top fun S hSne => ?_
  have hJinv : IsAInvariant φ (Φ S.toSubmodule) := by
    rw [isAInvariant_iff_smul_mem]
    intro a x hx
    rw [hmem] at hx ⊢
    exact S.apply_mem_toSubmodule a hx
  rcases hirr _ hJinv with hJbot | hJtop
  · refine absurd (Subrepresentation.toSubmodule_injective (show S.toSubmodule = ⊥ from ?_)) hSne
    rw [← Φ.symm_apply_apply S.toSubmodule, hJbot]; exact Φ.symm.map_bot
  · refine Subrepresentation.toSubmodule_injective (show S.toSubmodule = ⊤ from ?_)
    rw [← Φ.symm_apply_apply S.toSubmodule, hJtop]; exact Φ.symm.map_top

set_option backward.isDefEq.respectTransparency false in
open OddOrder.RepresentationTheory Representation in
/-- **Subgroup-level Singer mechanism.**  A finite *abelian* group `A` acting *faithfully* and
*irreducibly* (every `φ`-invariant subgroup of `K` is `⊥` or `⊤`) on a finite elementary abelian
`p`-group `K` is cyclic, with `|A|` dividing `|K| - 1`.  This is the structural heart of Peterfalvi
(9.7) case (b): a `U`-irreducible chief factor makes the image `Ū` cyclic of order dividing
`p^q - 1`.  Via `SingerField`: `K` becomes a simple `𝔽ₚ[A]`-module (`elabRepresentation_isIrreducible`),
realized inside the units of the Singer field, so `A ↪ Kˣ` is cyclic. -/
theorem isCyclic_card_dvd_of_aInvariant_irreducible_faithful_comm
    {A K : Type*} [Group A] [Finite A] [CommGroup K] [Finite K] {p : ℕ}
    [Module (ZMod p) (Additive K)] {φ : A →* MulAut K}
    (hcomm : ∀ a b : A, a * b = b * a) (hnt : Nontrivial K)
    (hirr : ∀ J : Subgroup K, IsAInvariant φ J → J = ⊥ ∨ J = ⊤)
    (hfaith : ∀ a : A, (∀ x : K, φ a x = x) → a = 1) :
    IsCyclic A ∧ Nat.card A ∣ Nat.card K - 1 := by
  haveI hirrep : IsSimpleOrder (Subrepresentation (elabRepresentation p φ)) :=
    elabRepresentation_isIrreducible hnt hirr
  haveI hsimp :
      IsSimpleModule (MonoidAlgebra (ZMod p) A) (elabRepresentation p φ).asModule := by
    rw [isSimpleModule_iff]
    exact (OrderIso.isSimpleOrder_iff
      Subrepresentation.subrepresentationSubmoduleOrderIso).mp hirrep
  haveI : Finite (elabRepresentation p φ).asModule := ‹Finite K›
  have hM : Nat.card (elabRepresentation p φ).asModule = Nat.card K := rfl
  -- Faithfulness in `𝔽ₚ[A]`-module terms: `of a • y = y` for all `y` ⟹ `φ a x = x` for all `x`.
  have hfaith' : ∀ a : A, (∀ y : (elabRepresentation p φ).asModule,
      MonoidAlgebra.of (ZMod p) A a • y = y) → a = 1 := by
    intro a ha
    refine hfaith a fun x => ?_
    have key : (elabRepresentation p φ).asModuleEquiv
        (MonoidAlgebra.of (ZMod p) A a •
          (elabRepresentation p φ).asModuleEquiv.symm (Additive.ofMul x)) = Additive.ofMul x := by
      rw [ha]; exact (elabRepresentation p φ).asModuleEquiv.apply_symm_apply _
    rw [asModuleEquiv_map_smul, asAlgebraHom_of,
      (elabRepresentation p φ).asModuleEquiv.apply_symm_apply, elabRepresentation_apply] at key
    exact Additive.ofMul.injective key
  obtain ⟨hcyc, hdvd⟩ :=
    isCyclic_and_card_dvd_of_faithful_irreducible_comm
      (E := A) (M := (elabRepresentation p φ).asModule) (p := p) hcomm hfaith'
  exact ⟨hcyc, by rwa [hM] at hdvd⟩

/-- **Fixed-point-freeness of an irreducible action with commuting image.**  If a group `A` acts on
a group `K` via `φ : A →* MulAut K` whose image is commutative (`hcomm : Commute (φ a) (φ b)`) and
irreducible (the only `A`-invariant subgroups are `⊥`/`⊤`, `hirr`), then every `a` with nontrivial
action `φ a ≠ 1` acts **fixed-point-freely**: `φ a x = x → x = 1`.

The fixed-point subgroup `Fix(φ a) = {y | φ a y = y}` is `A`-invariant — for `y` fixed by `φ a` and
any `b`, `φ a (φ b y) = φ b (φ a y) = φ b y` since `φ a`, `φ b` commute (`hcomm`) — so by
irreducibility it is `⊥` or `⊤`, and `⊤` would make `φ a = 1`.  This is the structural core of the
Frobenius action `H̄ ⋊ Ū` of Peterfalvi (9.7)(b)/(9.9): no Singer field model is needed, only the
irreducibility already supplied by Clifford case (b) and the commuting image (`U/C_U(H̄)` abelian).
The hypothesis is on the *image* (`Commute (φ a) (φ b)`), not on `A`, so it applies to the
`U`-action even though `U` itself is non-abelian. -/
theorem fixedPointFree_of_aInvariant_irreducible_comm
    {A K : Type*} [Group A] [Group K] {φ : A →* MulAut K}
    (hcomm : ∀ a b : A, Commute (φ a) (φ b))
    (hirr : ∀ J : Subgroup K, IsAInvariant φ J → J = ⊥ ∨ J = ⊤)
    (a : A) (ha : φ a ≠ 1) (x : K) (hx : φ a x = x) : x = 1 := by
  -- The fixed-point subgroup of `φ a`.
  let F : Subgroup K :=
    { carrier := {y | φ a y = y}
      one_mem' := map_one (φ a)
      mul_mem' := fun {y z} hy hz => by
        show φ a (y * z) = y * z
        rw [map_mul, show φ a y = y from hy, show φ a z = z from hz]
      inv_mem' := fun {y} hy => by
        show φ a y⁻¹ = y⁻¹
        rw [map_inv, show φ a y = y from hy] }
  have hxF : x ∈ F := hx
  -- `Fix(φ a)` is `A`-invariant: `φ a` commutes with every `φ b` (image of `φ` abelian).
  have hAinv : IsAInvariant φ F := isAInvariant_iff_smul_mem.mpr fun b y hy => by
    show φ a (φ b y) = φ b y
    have he : (φ a * φ b) y = (φ b * φ a) y := by rw [(hcomm a b).eq]
    rw [MulAut.mul_apply, MulAut.mul_apply, show φ a y = y from hy] at he
    exact he
  rcases hirr F hAinv with hbot | htop
  · -- `Fix(φ a) = ⊥`: the fixed point `x` is trivial.
    rw [hbot] at hxF; exact Subgroup.mem_bot.mp hxF
  · -- `Fix(φ a) = ⊤`: `φ a` is the identity, contradicting `φ a ≠ 1`.
    exact absurd (MulEquiv.ext fun y => by
      have hy : y ∈ F := htop ▸ Subgroup.mem_top y
      rw [MulAut.one_apply]; exact hy) ha

/-- **A fixed-point-free automorphism leaves no nontrivial character invariant** (abelian case).
If `α` is a fixed-point-free automorphism of a finite abelian group `K`, then any homomorphism
`θ : K →* M'` to a commutative group that is `α`-invariant (`θ (α x) = θ x` for all `x`) is trivial.

The displacement `x ↦ x / α x` is surjective (`MonoidHom.FixedPointFree.commutatorMap_surjective`),
and `θ (x / α x) = θ x / θ (α x) = 1` by invariance, so `θ` vanishes on all of `K`.  This is the
**character-side fixed-point-freeness** of the Frobenius action `H̄ ⋊ Ū` — for a nontrivial linear
character `θ ∈ Irr(H̄)` and `g ∉ C = C_U(H̄)` (so `φ_U(g)` is FPF by `chiefFactor_caseB_action_fpf`),
`θ` is *not* `φ_U(g)`-invariant, giving the inertia `I_U(θ) = C` underlying Peterfalvi (9.9). -/
theorem eq_one_of_invariant_of_fixedPointFree {K M' : Type*} [Group K] [Finite K] [CommGroup M']
    {α : MulAut K} (hα : MonoidHom.FixedPointFree α) {θ : K →* M'}
    (hinv : ∀ x : K, θ (α x) = θ x) : θ = 1 := by
  ext y
  obtain ⟨x, hx⟩ := hα.commutatorMap_surjective y
  rw [MonoidHom.commutatorMap_apply] at hx
  rw [MonoidHom.one_apply, ← hx, map_div, hinv, div_self']

open OddOrder.RepresentationTheory Representation in
/-- **An irreducible character of a finite abelian group is a linear character.**  For a finite
commutative group `Γ`, any irreducible character `φ` (`IsIrreducibleCharacter`) arises from a
homomorphism `θ : Γ →* ℂˣ` with `(θ g : ℂ) = φ g`.

Irreducible representations of a commutative group are `1`-dimensional
(`finrank_eq_one_of_isMulCommutative`), so each `ρ g` acts as a nonzero scalar `θ g` (extracted by
`exists_smul_eq_of_finrank_eq_one`), and the character `φ g = trace(ρ g) = θ g`.  This abelian
`Irr ↔ Hom(·, ℂˣ)` bridge lets `eq_one_of_invariant_of_fixedPointFree` apply to genuine irreducible
characters of the abelian chief factor `H̄`, giving the inertia `I_U(θ) = C` of Peterfalvi (9.9)
without realizing `H̄` as a subgroup. -/
theorem exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative
    {Γ : Type*} [Group Γ] [Finite Γ] [IsMulCommutative Γ]
    {φ : ClassFunction Γ ℂ} (hφ : IsIrreducibleCharacter φ) :
    ∃ θ : Γ →* ℂˣ, ∀ g, (θ g : ℂ) = φ g := by
  obtain ⟨V, _, _, _, ρ, hρ, hχ⟩ := hφ
  haveI : ρ.IsIrreducible := hρ
  have hfin : Module.finrank ℂ V = 1 :=
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
  haveI : FiniteDimensional ℂ V := .of_finrank_eq_succ hfin
  haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hfin
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  -- `span {x} = ⊤` (1-dimensional), so a linear map is determined by its value on `x`.
  have hspan : Submodule.span ℂ ({x} : Set V) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hfin]; exact finrank_span_singleton hx
  -- The scalar `c g` with `ρ g x = c g • x`.
  choose c hc using fun g => exists_smul_eq_of_finrank_eq_one hfin hx ((ρ g) x)
  -- `ρ g = c g • id` (agree on the spanning vector `x`).
  have hρeq : ∀ g, (ρ g : V →ₗ[ℂ] V) = c g • LinearMap.id := fun g => by
    refine LinearMap.ext_on hspan fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy; subst hy
    simpa [LinearMap.smul_apply] using (hc g).symm
  -- `c` is multiplicative and unital, and never zero (`ρ g` is invertible).
  have hc1 : c 1 = 1 := by
    have h := hc 1
    rw [map_one, Module.End.one_apply] at h
    have h2 : c 1 • x = (1 : ℂ) • x := by rw [one_smul]; exact h
    exact smul_left_injective ℂ hx h2
  have hcmul : ∀ g h, c (g * h) = c g * c h := fun g h => by
    have e1 : (ρ (g * h)) x = (c g * c h) • x := by
      rw [map_mul]
      show (ρ g) ((ρ h) x) = (c g * c h) • x
      rw [← hc h, map_smul, ← hc g, smul_smul, mul_comm]
    have key : c (g * h) • x = (c g * c h) • x := by rw [hc (g * h)]; exact e1
    exact smul_left_injective ℂ hx key
  have hcne : ∀ g, c g ≠ 0 := fun g hc0 => by
    have hρ0 : (ρ g : V →ₗ[ℂ] V) = 0 := by rw [hρeq g, hc0, zero_smul]
    have h1 : (ρ (g⁻¹) * ρ g : V →ₗ[ℂ] V) = ρ 1 := by rw [← map_mul, inv_mul_cancel]
    rw [hρ0, mul_zero, map_one] at h1
    exact zero_ne_one h1
  -- `φ g = trace(ρ g) = c g · finrank = c g`.
  have hφc : ∀ g, φ g = c g := fun g => by
    have hco : φ g = LinearMap.trace ℂ V (ρ g) := congrFun hχ g
    rw [hco, hρeq g, map_smul, LinearMap.trace_id, hfin]
    simp
  exact ⟨{ toFun := fun g => Units.mk0 (c g) (hcne g)
           map_one' := Units.ext (by simpa using hc1)
           map_mul' := fun g h => Units.ext (by simpa using hcmul g h) },
        fun g => by simpa using (hφc g).symm⟩

set_option backward.isDefEq.respectTransparency false in
open OddOrder.RepresentationTheory Representation in
/-- **Subgroup-level Singer fixed-point-free coprimality.**  Strengthens
`isCyclic_card_dvd_of_aInvariant_irreducible_faithful_comm` with a fixed-point-free `σ : MulAut K`:
if the only `a` whose action `φ a` commutes with `σ` is `a = 1`, then `|A|` is coprime to `p - 1`.

This is Peterfalvi (9.7) case (b)'s coprimality `Coprime |Ū| (p - 1)`: the image `Ū = φ.range`
embeds in the cyclic units `Kˣ` of the Singer field, and the prime subfield `𝔽ₚ*` (the
`𝔽ₚ`-scalars, central in `Aut K`) meets `Ū` only in `1` because an `𝔽ₚ`-scalar commutes with
`σ = φ(w)` and `σ` is fixed-point-free.  The `MulAut K`-action transports to the additive
`MulEquiv.toAdditive σ` on `(elabRepresentation p φ).asModule`; the rest is
`coprime_card_sub_one_of_faithful_irreducible_comm_fpf`. -/
theorem coprime_card_sub_one_of_aInvariant_irreducible_faithful_comm_fpf
    {A K : Type*} [Group A] [Finite A] [CommGroup K] [Finite K] {p : ℕ} [Fact p.Prime]
    [Module (ZMod p) (Additive K)] {φ : A →* MulAut K}
    (hcomm : ∀ a b : A, a * b = b * a) (hnt : Nontrivial K)
    (hirr : ∀ J : Subgroup K, IsAInvariant φ J → J = ⊥ ∨ J = ⊤)
    (hfaith : ∀ a : A, (∀ x : K, φ a x = x) → a = 1)
    (σ : MulAut K)
    (hfpf : ∀ a : A, (∀ x : K, σ (φ a x) = φ a (σ x)) → a = 1) :
    Nat.Coprime (Nat.card A) (p - 1) := by
  haveI hirrep : IsSimpleOrder (Subrepresentation (elabRepresentation p φ)) :=
    elabRepresentation_isIrreducible hnt hirr
  haveI hsimp :
      IsSimpleModule (MonoidAlgebra (ZMod p) A) (elabRepresentation p φ).asModule := by
    rw [isSimpleModule_iff]
    exact (OrderIso.isSimpleOrder_iff
      Subrepresentation.subrepresentationSubmoduleOrderIso).mp hirrep
  haveI : Finite (elabRepresentation p φ).asModule := ‹Finite K›
  -- Faithfulness in `𝔽ₚ[A]`-module terms (as in the cyclicity bridge).
  have hfaith' : ∀ a : A, (∀ y : (elabRepresentation p φ).asModule,
      MonoidAlgebra.of (ZMod p) A a • y = y) → a = 1 := by
    intro a ha
    refine hfaith a fun x => ?_
    have key : (elabRepresentation p φ).asModuleEquiv
        (MonoidAlgebra.of (ZMod p) A a •
          (elabRepresentation p φ).asModuleEquiv.symm (Additive.ofMul x)) = Additive.ofMul x := by
      rw [ha]; exact (elabRepresentation p φ).asModuleEquiv.apply_symm_apply _
    rw [asModuleEquiv_map_smul, asAlgebraHom_of,
      (elabRepresentation p φ).asModuleEquiv.apply_symm_apply, elabRepresentation_apply] at key
    exact Additive.ofMul.injective key
  -- The `MulAut K`-action `σ`, carried to an additive automorphism of `asModule = Additive K`.
  let τ : (elabRepresentation p φ).asModule ≃+ (elabRepresentation p φ).asModule :=
    { toFun := fun z => Additive.ofMul (σ (Additive.toMul z))
      invFun := fun z => Additive.ofMul (σ.symm (Additive.toMul z))
      left_inv := fun z => by simp
      right_inv := fun z => by simp
      map_add' := fun z w => by
        show Additive.ofMul (σ (Additive.toMul (z + w)))
          = Additive.ofMul (σ (Additive.toMul z)) + Additive.ofMul (σ (Additive.toMul w))
        rw [show Additive.toMul (z + w) = Additive.toMul z * Additive.toMul w from rfl, map_mul]
        rfl }
  -- The action `of a • z` is `ρ a z` (the descended representation).
  have hact : ∀ (a : A) (z : (elabRepresentation p φ).asModule),
      MonoidAlgebra.of (ZMod p) A a • z = (elabRepresentation p φ) a z := by
    intro a z
    have h2 := asModuleEquiv_map_smul (ρ := elabRepresentation p φ)
      (MonoidAlgebra.of (ZMod p) A a) z
    rw [asAlgebraHom_of] at h2
    simpa [Representation.asModuleEquiv] using h2
  -- Fixed-point-freeness in `𝔽ₚ[A]`-module terms.
  have hfpf' : ∀ a : A, (∀ y : (elabRepresentation p φ).asModule,
      τ (MonoidAlgebra.of (ZMod p) A a • y)
        = MonoidAlgebra.of (ZMod p) A a • τ y) → a = 1 := by
    intro a ha
    apply hfpf a
    intro x
    have h := ha (Additive.ofMul x)
    rw [hact, hact, elabRepresentation_apply] at h
    -- `h : τ (ofMul (φ a x)) = ρ a (τ (ofMul x))`, and `τ (ofMul w) = ofMul (σ w)`.
    have hτ : ∀ w : K, τ (Additive.ofMul w) = Additive.ofMul (σ w) := fun w => rfl
    rw [hτ, hτ, elabRepresentation_apply] at h
    exact Additive.ofMul.injective h
  exact coprime_card_sub_one_of_faithful_irreducible_comm_fpf
    (E := A) (M := (elabRepresentation p φ).asModule) hcomm hfaith' τ hfpf'

/-- **(9.7) case (a) bound.**  A group `A` acting on a group `K` of prime order `p` has its
action-image `φ.range` of order dividing `p - 1`: `K` is cyclic, so `MulAut K ≅ (ZMod p)ˣ` has order
`p - 1` (`IsCyclic.card_mulAut`), and `φ.range ≤ MulAut K`.  This is the `a ∣ p - 1` bound of
Peterfalvi (9.7) case (a) for `a = |A : C_A(K)| = |φ.range|` (the `U`-action on an order-`p` Clifford
factor `H₁` embeds `U/C_U(H₁)` into the cyclic `Aut(H₁)`). -/
theorem card_range_dvd_card_sub_one_of_prime_card {A K : Type*} [Group A] [Group K] [Finite K]
    (φ : A →* MulAut K) (hp : (Nat.card K).Prime) :
    Nat.card ↥φ.range ∣ Nat.card K - 1 := by
  haveI : Fact (Nat.card K).Prime := ⟨hp⟩
  haveI : IsCyclic K := isCyclic_of_prime_card rfl
  calc Nat.card ↥φ.range ∣ Nat.card (MulAut K) := Subgroup.card_subgroup_dvd_card _
    _ = Nat.totient (Nat.card K) := IsCyclic.card_mulAut K
    _ = Nat.card K - 1 := Nat.totient_prime hp

/-- **Restriction of a `φ`-invariant action to the invariant subgroup `S`.**  Each `φ a` maps `S`
bijectively onto itself, hence restricts to an automorphism of `↥S`; this is functorial in `a`,
giving a group homomorphism `A →* MulAut ↥S`.  (Used for (9.7) case (a): the `U`-action on an
order-`p` Clifford factor `H₁ ≤ H̄`.) -/
noncomputable def aInvariantRestrictAut {K A : Type*} [Group K] [Group A] {φ : A →* MulAut K}
    {S : Subgroup K} (hS : IsAInvariant φ S) : A →* MulAut ↥S where
  toFun a := (MulEquiv.subgroupMap (φ a) S).trans
    (MulEquiv.subgroupCongr ((pointwise_mulAut_smul_eq_map (φ a) S).symm.trans (hS a)))
  map_one' := by
    ext x
    simp only [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply,
      map_one, MulAut.one_apply]
  map_mul' a b := by
    ext x
    simp only [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply,
      map_mul, MulAut.mul_apply]

@[simp] theorem aInvariantRestrictAut_coe {K A : Type*} [Group K] [Group A] {φ : A →* MulAut K}
    {S : Subgroup K} (hS : IsAInvariant φ S) (a : A) (x : ↥S) :
    ((aInvariantRestrictAut hS a x : ↥S) : K) = φ a x := by
  simp only [aInvariantRestrictAut, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
    MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply]

/-- **(9.7) case (a) bound for a Clifford factor.**  The image of the restricted `A`-action on a
`φ`-invariant subgroup `S` of prime order has order dividing `|S| - 1`. -/
theorem aInvariantRestrictAut_range_card_dvd {K A : Type*} [Group K] [Group A] [Finite K]
    {φ : A →* MulAut K} {S : Subgroup K} (hS : IsAInvariant φ S) (hp : (Nat.card ↥S).Prime) :
    Nat.card ↥(aInvariantRestrictAut hS).range ∣ Nat.card ↥S - 1 :=
  card_range_dvd_card_sub_one_of_prime_card (aInvariantRestrictAut hS) hp

/-- **(9.7) Clifford dimension dichotomy** (the arithmetic heart of (9.7)).  Restricting the
`U W₁`-action on the chief factor `H̄ = H/H₀` to `U`, there is a minimal `U`-invariant `S₀ ≠ ⊥` of
order `p^d` with `0 < d` and `d ∣ q`.  Since `q` is prime, `d ∈ {1, q}`: the dichotomy of (9.7),
case (a) (`d = 1`, `U` semisimple into order-`p` pieces) vs case (b) (`d = q`, `U` irreducible).

Assembled from the spanning step (`iSup_smul_eq_top_of_irreducible`, on the `U W₁`-irreducible `H̄`),
the orbit lemmas (each `U W₁`-translate of `S₀` is `U`-irreducible of order `|S₀|`), and the order
step (`card_eq_pow_of_iSup_aInvariant_irreducible`): `|H̄| = |S₀|^k`, while `|H̄| = p^q`, so
`p^q = (p^d)^k`, i.e. `q = d·k`. -/
theorem chiefFactor_clifford_dim_dvd_q [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ∃ (d : ℕ) (S₀ : Subgroup (↥data.H ⧸ chief.N)),
      0 < d ∧ d ∣ data.q ∧ S₀ ≠ ⊥ ∧ Nat.card ↥S₀ = chief.p ^ d ∧
      IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) S₀ ∧
      (∀ J, IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J ≤ S₀ → J = ⊥ ∨ J = S₀) := by
  classical
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  haveI : chief.N.Normal := chief.N_normal
  haveI := Fact.mk chief.p_prime
  -- The descended `U W₁`-action on the chief factor `H̄` and its restriction to the kernel `U`.
  set act := typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant with hact
  set φU := act.φ.comp act.U.subtype with hφU
  have hUnorm : act.U.Normal := (typeP_uW1_frobenius data.typeP hU).isNormal
  have hKcard : Nat.card (↥data.H ⧸ chief.N) = chief.p ^ data.q := chiefFactor_quotient_card chief
  have hq_pos : 0 < data.q := Nat.card_pos
  haveI hKnt : Nontrivial (↥data.H ⧸ chief.N) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hKcard]; exact Nat.one_lt_pow hq_pos.ne' chief.p_prime.one_lt)
  -- A minimal nonzero `U`-invariant subgroup `S₀` (the `U`-irreducible Clifford piece).
  set T : Set (Subgroup (↥data.H ⧸ chief.N)) := {J | J ≠ ⊥ ∧ IsAInvariant φU J} with hT
  obtain ⟨S₀, ⟨hS₀ne, hS₀inv⟩, hS₀min⟩ :=
    (Set.toFinite T).exists_minimal ⟨⊤, top_ne_bot, IsAInvariant.top _⟩
  have hirr₀ : ∀ J, IsAInvariant φU J → J ≤ S₀ → J = ⊥ ∨ J = S₀ := by
    intro J hJinv hJle
    by_cases hJ0 : J = ⊥
    · exact Or.inl hJ0
    · exact Or.inr (le_antisymm hJle (hS₀min ⟨hJ0, hJinv⟩ hJle))
  -- `|S₀| = p^d` (subgroup of the elementary abelian `p`-group `H̄`).
  obtain ⟨d, hd⟩ := (chief.quotient_elementaryAbelian.to_subgroup S₀).isPGroup.exists_card_eq
  -- Spanning step (full action) + order step (restricted `U`-action) give `|H̄| = |S₀|^k`.
  have hspan : ⨆ a, act.φ a • S₀ = ⊤ :=
    iSup_smul_eq_top_of_irreducible (φ := act.φ) chief.quotient_chiefFactor hS₀ne
  obtain ⟨k, hk⟩ := card_eq_pow_of_iSup_aInvariant_irreducible
    (φ := φU) (S := fun a => act.φ a • S₀) (n := Nat.card ↥S₀)
    (fun x y => chief.quotient_elementaryAbelian.comm x y) hspan
    (fun a => isAInvariant_comp_subtype_pointwise_smul hUnorm hS₀inv a)
    (fun a J hJinv hJle => forall_aInvariant_le_pointwise_smul hUnorm hirr₀ a J hJinv hJle)
    (fun a _ => card_pointwise_smul act.φ a S₀)
  -- Arithmetic: `p^q = (p^d)^k = p^{d·k}`, so `q = d·k`.
  rw [hd, hKcard, ← pow_mul] at hk
  have hdk : data.q = d * k := Nat.pow_right_injective chief.p_prime.two_le hk
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h
    · rw [h0, pow_zero] at hd; exact absurd (Subgroup.card_eq_one.mp hd) hS₀ne
    · exact h
  exact ⟨d, S₀, hdpos, ⟨k, hdk⟩, hS₀ne, hd, hS₀inv, hirr₀⟩

/-- **(9.7) structural dichotomy** (the Clifford case split, read off the chief factor).  With
`q = |W₁|` prime, the chief factor `H̄` is, under the restricted `U`-action, *either*
`U`-irreducible (Clifford case (b): every `U`-invariant subgroup is `⊥` or `⊤`) *or* contains a
`U`-invariant subgroup of order `p` (Clifford case (a)).

This is the arithmetic dichotomy `d ∈ {1, q}` of `chiefFactor_clifford_dim_dvd_q` read through the
primality of `q`: the minimal nonzero `U`-invariant piece `S₀` has order `p^d` with `d ∣ q`, so
either `d = q` (`|S₀| = p^q = |H̄|`, hence `S₀ = ⊤`, and minimality forces `U`-irreducibility)
or `d = 1` (`|S₀| = p`).  Packaging the two cases into the carriers `CliffordCaseAData` /
`CliffordCaseBData` (the order-`p` factor pullback / the `End_{𝔽ₚ[U]}(H̄)` field model) is the
remaining work of `clifford_dichotomy`. -/
theorem chiefFactor_clifford_U_dichotomy [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) ∨
    (∃ S₀ : Subgroup (↥data.H ⧸ chief.N), S₀ ≠ ⊥ ∧
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) S₀ ∧ Nat.card ↥S₀ = chief.p ∧
        ∀ J, IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J ≤ S₀ → J = ⊥ ∨ J = S₀) := by
  obtain ⟨d, S₀, _hdpos, hdq, hS₀ne, hcard, hS₀inv, hirr₀⟩ :=
    chiefFactor_clifford_dim_dvd_q chief
  -- `q = |W₁|` is prime and `d ∣ q`, so `d = 1` or `d = q`.
  have hq_prime : (data.q).Prime := data.nontrivial.2.1
  rcases hq_prime.eq_one_or_self_of_dvd d hdq with hd1 | hdq2
  · -- `d = 1`: a `U`-invariant subgroup of order `p`.  Clifford case (a).
    exact Or.inr ⟨S₀, hS₀ne, hS₀inv, by rw [hcard, hd1, pow_one], hirr₀⟩
  · -- `d = q`: `|S₀| = p^q = |H̄|` ⟹ `S₀ = ⊤`; minimality ⟹ `U`-irreducible.  Case (b).
    have hS₀top : S₀ = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hcard, hdq2, chiefFactor_quotient_card chief])
    refine Or.inl fun J hJinv => ?_
    by_cases hJ : J = ⊥
    · exact Or.inl hJ
    · exact Or.inr
        (((hirr₀ J hJinv (le_top.trans_eq hS₀top.symm)).resolve_left hJ).trans hS₀top)

open OddOrder.RepresentationTheory Representation in
open scoped commutatorElement IsMulCommutative in
/-- **Peterfalvi (9.7) case (b), chief-factor Singer conclusion.**  When `U` acts irreducibly on
the chief factor `H̄ = H/H₀` (Clifford case (b) — the left branch of
`chiefFactor_clifford_U_dichotomy`), its image `Ū = φ_U(U) ≤ Aut(H̄)` is *cyclic*, of order
dividing `p^q - 1`.

`Ū` is abelian because `[U, U]` centralizes `H` (Peterfalvi (8.5.b),
`typeP_commutator_U_centralizes_H`): a commutator `⁅a, b⁆ ∈ [U, U]` acts trivially on `H̄`, so
`φ_U ⁅a, b⁆ = 1` and the image is commutative.  Faithfulness of the inclusion `Ū ↪ Aut(H̄)` and the
irreducibility transferred from the case-(b) hypothesis feed the subgroup-level Singer mechanism
`isCyclic_card_dvd_of_aInvariant_irreducible_faithful_comm`, with `H̄` the elementary abelian
`p`-group of order `p^q` (`chiefFactor_quotient_card`).  This is the structural core behind the
`Coprime u (p-1)` / `u ∣ (p^q-1)/(p-1)` divisibilities of `CliffordCaseBData` (which additionally
pin `u = |Ū|` and use the `W₁`-fixed-point-free refinement). -/
theorem chiefFactor_caseB_image_cyclic [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) :
    IsCyclic ↥(((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype).range) ∧
      Nat.card ↥(((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype).range) ∣ chief.p ^ data.q - 1 := by
  classical
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  haveI : chief.N.Normal := chief.N_normal
  haveI : NeZero chief.p := ⟨chief.p_prime.pos.ne'⟩
  set act := typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant with hact
  set φU := act.φ.comp act.U.subtype with hφU
  -- `H̄ = ↥H ⧸ N` is finite elementary abelian `p`, nontrivial, of order `p^q`.
  have hKcard : Nat.card (↥data.H ⧸ chief.N) = chief.p ^ data.q := chiefFactor_quotient_card chief
  have hq_pos : 0 < data.q := Nat.card_pos
  haveI hKnt : Nontrivial (↥data.H ⧸ chief.N) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hKcard]; exact Nat.one_lt_pow hq_pos.ne' chief.p_prime.one_lt)
  -- Module instances for the Singer mechanism, from `chief.quotient_elementaryAbelian`.
  letI : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  letI : CommGroup (↥data.H ⧸ chief.N) := inferInstance
  letI : Module (ZMod chief.p) (Additive (↥data.H ⧸ chief.N)) :=
    chief.quotient_elementaryAbelian.zmodModule
  -- An element of `U W₁` centralizing `H` acts trivially on `H̄`.
  have hcentral_triv : ∀ g : ↥(data.typeP.U ⊔ data.typeP.W1),
      (g : G) ∈ Subgroup.centralizer (data.typeP.H : Set G) → act.φ g = 1 := by
    intro g hg
    have hfix : ∀ x : ↥data.typeP.H, (typeP_conjAction data.typeP g) x = x := by
      intro x
      apply Subtype.ext
      rw [typeP_conjAction_apply]
      have hcom : (x : G) * (g : G) = (g : G) * (x : G) :=
        (Subgroup.mem_centralizer_iff.mp hg) (x : G) x.2
      rw [← hcom, mul_assoc, mul_inv_cancel, mul_one]
    ext y
    refine QuotientGroup.induction_on y ?_
    intro x
    show (act.φ g) (QuotientGroup.mk' chief.N x) = QuotientGroup.mk' chief.N x
    have hstep : (act.φ g) (QuotientGroup.mk' chief.N x)
        = QuotientGroup.mk' chief.N ((typeP_conjAction data.typeP g) x) := rfl
    rw [hstep, hfix x]
  -- `Ū = φU.range` is abelian: `φU ⁅a, b⁆ = 1` since `⁅a, b⁆` maps into `[U, U] ⊆ C(H)`.
  have hComm : ∀ a b : ↥act.U, Commute (φU a) (φU b) := by
    intro a b
    refine commutatorElement_eq_one_iff_commute.mp ?_
    rw [← map_commutatorElement φU a b]
    show act.φ (act.U.subtype ⁅a, b⁆) = 1
    apply hcentral_triv
    change ((data.typeP.U ⊔ data.typeP.W1).subtype.comp act.U.subtype) ⁅a, b⁆
        ∈ Subgroup.centralizer (data.typeP.H : Set G)
    rw [map_commutatorElement]
    exact typeP_commutator_U_centralizes_H data.typeP
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2))
  -- Package the data for the Singer mechanism.
  have hAcomm : ∀ s t : ↥(φU.range), s * t = t * s := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact Subtype.ext (hComm a b)
  have hirr : ∀ J : Subgroup (↥data.H ⧸ chief.N),
      IsAInvariant (φU.range).subtype J → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    apply hcaseB
    intro a
    exact hJ ⟨φU a, MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  have hfaith : ∀ a : ↥(φU.range),
      (∀ x : (↥data.H ⧸ chief.N), ((φU.range).subtype a) x = x) → a = 1 := by
    intro a ha
    have hone : (a : MulAut (↥data.H ⧸ chief.N)) = 1 := by
      ext x
      simpa using ha x
    exact Subtype.ext hone
  obtain ⟨hcyc, hdvd⟩ := isCyclic_card_dvd_of_aInvariant_irreducible_faithful_comm
    (A := ↥(φU.range)) (K := ↥data.H ⧸ chief.N) (p := chief.p)
    (φ := (φU.range).subtype) hAcomm hKnt hirr hfaith
  exact ⟨hcyc, by rwa [hKcard] at hdvd⟩

open OddOrder.RepresentationTheory Representation in
open scoped commutatorElement IsMulCommutative in
/-- **Peterfalvi (9.7) case (b), the fixed-point-free coprimality `Coprime |Ū| (p-1)`.**  When `U`
acts irreducibly on the chief factor `H̄ = H/H₀` (Clifford case (b)), the image `Ū = φ_U(U)` has
order coprime to `p - 1`.

This discharges the hard `coprime` hypothesis of `chiefFactor_caseB_image_dvd_norm` from the
Frobenius structure of `U W₁`: a nonidentity `w₀ ∈ W₁` acts on `Ū` fixed-point-freely.  Indeed if
`act.φ(w₀)` commutes with `φ_U(u)` then `⁅w₀, u⁆` acts trivially on `H̄`, so `u` lies in a
`w₀`-fixed coset of `C_U(H̄)`; Isaacs Cor 3.28 (`coprime_fixedPoints_quotient`) extracts a `w₀`-fixed
representative `c ∈ u·C_U(H̄)`, and `c ∈ C_U(w₀) = 1` by the Frobenius condition
(`centralizer_complement_le`, `U ⊓ W₁ = ⊥`), forcing `u ∈ C_U(H̄)`, i.e. `φ_U(u) = 1`.  The
fixed-point-free Singer bridge `coprime_card_sub_one_of_aInvariant_irreducible_faithful_comm_fpf`
then gives the coprimality. -/
theorem chiefFactor_caseB_image_coprime [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) :
    Nat.Coprime (Nat.card ↥(((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype).range)) (chief.p - 1) := by
  classical
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  haveI : chief.N.Normal := chief.N_normal
  haveI : NeZero chief.p := ⟨chief.p_prime.pos.ne'⟩
  haveI : Fact chief.p.Prime := ⟨chief.p_prime⟩
  set act := typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant with hact
  set φU := act.φ.comp act.U.subtype with hφU
  haveI hUnorm : act.U.Normal := (typeP_uW1_frobenius data.typeP hU).isNormal
  have hKcard : Nat.card (↥data.H ⧸ chief.N) = chief.p ^ data.q := chiefFactor_quotient_card chief
  have hq_pos : 0 < data.q := Nat.card_pos
  haveI hKnt : Nontrivial (↥data.H ⧸ chief.N) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hKcard]; exact Nat.one_lt_pow hq_pos.ne' chief.p_prime.one_lt)
  letI : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  letI : CommGroup (↥data.H ⧸ chief.N) := inferInstance
  letI : Module (ZMod chief.p) (Additive (↥data.H ⧸ chief.N)) :=
    chief.quotient_elementaryAbelian.zmodModule
  -- Abelianness, irreducibility, faithfulness of `Ū = φU.range` (as in `chiefFactor_caseB_image_cyclic`).
  have hcentral_triv : ∀ g : ↥(data.typeP.U ⊔ data.typeP.W1),
      (g : G) ∈ Subgroup.centralizer (data.typeP.H : Set G) → act.φ g = 1 := by
    intro g hg
    have hfix : ∀ x : ↥data.typeP.H, (typeP_conjAction data.typeP g) x = x := by
      intro x
      apply Subtype.ext
      rw [typeP_conjAction_apply]
      have hcom : (x : G) * (g : G) = (g : G) * (x : G) :=
        (Subgroup.mem_centralizer_iff.mp hg) (x : G) x.2
      rw [← hcom, mul_assoc, mul_inv_cancel, mul_one]
    ext y
    refine QuotientGroup.induction_on y ?_
    intro x
    show (act.φ g) (QuotientGroup.mk' chief.N x) = QuotientGroup.mk' chief.N x
    have hstep : (act.φ g) (QuotientGroup.mk' chief.N x)
        = QuotientGroup.mk' chief.N ((typeP_conjAction data.typeP g) x) := rfl
    rw [hstep, hfix x]
  have hComm : ∀ a b : ↥act.U, Commute (φU a) (φU b) := by
    intro a b
    refine commutatorElement_eq_one_iff_commute.mp ?_
    rw [← map_commutatorElement φU a b]
    show act.φ (act.U.subtype ⁅a, b⁆) = 1
    apply hcentral_triv
    change ((data.typeP.U ⊔ data.typeP.W1).subtype.comp act.U.subtype) ⁅a, b⁆
        ∈ Subgroup.centralizer (data.typeP.H : Set G)
    rw [map_commutatorElement]
    exact typeP_commutator_U_centralizes_H data.typeP
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2))
  have hAcomm : ∀ s t : ↥(φU.range), s * t = t * s := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact Subtype.ext (hComm a b)
  have hirr : ∀ J : Subgroup (↥data.H ⧸ chief.N),
      IsAInvariant (φU.range).subtype J → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    apply hcaseB
    intro a
    exact hJ ⟨φU a, MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  have hfaith : ∀ a : ↥(φU.range),
      (∀ x : (↥data.H ⧸ chief.N), ((φU.range).subtype a) x = x) → a = 1 := by
    intro a ha
    have hone : (a : MulAut (↥data.H ⧸ chief.N)) = 1 := by
      ext x
      simpa using ha x
    exact Subtype.ext hone
  -- The fixed-point-free witness: a nonidentity `w₀ ∈ W₁` inside `↥(U ⊔ W₁)`.
  obtain ⟨w, hwW1, hwne⟩ :=
    (data.typeP.W1.bot_or_exists_ne_one).resolve_left data.typeP.W1_nontrivial
  have hwUW1 : w ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_right hwW1
  set w₀ : ↥(data.typeP.U ⊔ data.typeP.W1) := ⟨w, hwUW1⟩ with hw₀def
  have hw₀E : w₀ ∈ act.E := by
    show (⟨w, hwUW1⟩ : ↥(data.typeP.U ⊔ data.typeP.W1)) ∈
      data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)
    rw [Subgroup.mem_subgroupOf]; exact hwW1
  have hw₀ne : w₀ ≠ 1 := fun h => hwne (Subtype.ext_iff.mp h)
  -- Conjugation action `ψ` of `U W₁` on the kernel `act.U`, and how `φU` transforms under it.
  set ψ : ↥(data.typeP.U ⊔ data.typeP.W1) →* MulAut ↥act.U := MulAut.conjNormal with hψdef
  have hψcoe : ∀ (g : ↥(data.typeP.U ⊔ data.typeP.W1)) (y : ↥act.U),
      (act.U.subtype (ψ g y) : ↥(data.typeP.U ⊔ data.typeP.W1)) =
        (g : ↥(data.typeP.U ⊔ data.typeP.W1)) * act.U.subtype y * g⁻¹ :=
    fun g y => MulAut.conjNormal_apply g y
  have hφUconj : ∀ (g : ↥(data.typeP.U ⊔ data.typeP.W1)) (y : ↥act.U),
      φU (ψ g y) = act.φ g * φU y * (act.φ g)⁻¹ := by
    intro g y
    have he : φU (ψ g y) = act.φ ((g : ↥(data.typeP.U ⊔ data.typeP.W1)) * act.U.subtype y * g⁻¹) := by
      show act.φ (act.U.subtype (ψ g y)) = _
      rw [hψcoe]
    rw [he, map_mul, map_mul, map_inv]; rfl
  -- The kernel `N = C_U(H̄)` of `φU`, and its `ψ`-invariance.
  set N : Subgroup ↥act.U := φU.ker with hNdef
  have hN_inv : IsAInvariant (ψ.comp (Subgroup.zpowers w₀).subtype) N := by
    rw [isAInvariant_iff_smul_mem]
    intro a y hy
    rw [hNdef, MonoidHom.mem_ker] at hy ⊢
    show φU (ψ ((Subgroup.zpowers w₀).subtype a) y) = 1
    rw [hφUconj, hy, mul_one, mul_inv_cancel]
  -- Coprimality and solvability inputs for Isaacs Cor 3.28.
  have hCop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers w₀)) (Nat.card ↥act.U) := by
    have hkc : Nat.Coprime (Nat.card ↥act.U) (Nat.card ↥act.E) :=
      (typeP_uW1_frobenius data.typeP hU).coprime_card_kernel_complement
    exact Nat.Coprime.coprime_dvd_left
      (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hw₀E)) hkc.symm
  have hSolv : IsSolvable ↥(Subgroup.zpowers w₀) ∨ IsSolvable ↥act.U :=
    Or.inl (isSolvable_of_comm fun a b => by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]; group))
  -- Apply the fixed-point-free Singer bridge.
  refine coprime_card_sub_one_of_aInvariant_irreducible_faithful_comm_fpf
    (A := ↥(φU.range)) (K := ↥data.H ⧸ chief.N) (p := chief.p) (φ := (φU.range).subtype)
    hAcomm hKnt hirr hfaith (act.φ w₀) ?_
  intro a ha
  obtain ⟨u₀, hu₀⟩ := a.2
  -- `↑a = φU u₀ = act.φ u₀'`, and `act.φ w₀` commutes with it.
  have ha1 : ((φU.range).subtype a : MulAut (↥data.H ⧸ chief.N)) = act.φ (act.U.subtype u₀) :=
    hu₀.symm
  have hCm : Commute (act.φ w₀) (act.φ (act.U.subtype u₀)) := by
    show act.φ w₀ * act.φ (act.U.subtype u₀) = act.φ (act.U.subtype u₀) * act.φ w₀
    apply MulEquiv.ext
    intro x
    rw [MulAut.mul_apply, MulAut.mul_apply, ← ha1]
    exact ha x
  -- `hg_fix`: each `w₀^k`-conjugate of `u₀` lands in `u₀ · N`.
  have hg_fix : ∀ aa : ↥(Subgroup.zpowers w₀),
      ∃ n ∈ N, (ψ.comp (Subgroup.zpowers w₀).subtype) aa u₀ = u₀ * n := by
    intro aa
    refine ⟨u₀⁻¹ * (ψ ((Subgroup.zpowers w₀).subtype aa) u₀), ?_, ?_⟩
    · rw [hNdef, MonoidHom.mem_ker, map_mul, map_inv, hφUconj]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp aa.2
      have hcaφ : act.φ ((Subgroup.zpowers w₀).subtype aa) = (act.φ w₀) ^ k := by
        rw [show (Subgroup.zpowers w₀).subtype aa = w₀ ^ k from hk.symm, map_zpow]
      have hcomm_k : Commute (act.φ ((Subgroup.zpowers w₀).subtype aa)) (φU u₀) := by
        rw [hcaφ]; exact hCm.zpow_left k
      rw [show act.φ ((Subgroup.zpowers w₀).subtype aa) * φU u₀ *
            (act.φ ((Subgroup.zpowers w₀).subtype aa))⁻¹ = φU u₀ by
        rw [hcomm_k.eq, mul_assoc, mul_inv_cancel, mul_one], inv_mul_cancel]
    · rw [MonoidHom.comp_apply, mul_inv_cancel_left]
  -- Isaacs Cor 3.28: a `w₀`-fixed representative `c ∈ u₀ · N`.
  obtain ⟨c, hc_fix, n, hn, hc_eq⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient
      (φ := ψ.comp (Subgroup.zpowers w₀).subtype) hCop hSolv hN_inv hg_fix
  -- `c` commutes with `w₀`, so `c ∈ C_U(w₀) ⊆ W₁`; as `c ∈ U`, `c = 1`.
  have hc_w₀ : ψ w₀ c = c := by
    have := hc_fix ⟨w₀, Subgroup.mem_zpowers w₀⟩
    rwa [MonoidHom.comp_apply] at this
  have hc_comm : (act.U.subtype c : ↥(data.typeP.U ⊔ data.typeP.W1)) * w₀ =
      w₀ * act.U.subtype c := by
    have h := congrArg act.U.subtype hc_w₀
    rw [hψcoe] at h
    -- `h : w₀ * subtype c * w₀⁻¹ = subtype c`
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hc_in_E : (act.U.subtype c : ↥(data.typeP.U ⊔ data.typeP.W1)) ∈ act.E := by
    refine (typeP_uW1_frobenius data.typeP hU).centralizer_complement_le w₀ hw₀E hw₀ne ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hc_comm
  have hc_in_U : (act.U.subtype c : ↥(data.typeP.U ⊔ data.typeP.W1)) ∈ act.U := c.2
  have hc1 : (act.U.subtype c : ↥(data.typeP.U ⊔ data.typeP.W1)) = 1 :=
    Subgroup.disjoint_def.mp (typeP_uW1_frobenius data.typeP hU).isComplement.disjoint
      hc_in_U hc_in_E
  have hc0 : c = 1 := act.U.subtype_injective (by rw [hc1, map_one])
  -- `1 = c = u₀ · n` ⟹ `u₀ ∈ N` ⟹ `φU u₀ = 1` ⟹ `a = 1`.
  rw [hc0] at hc_eq
  have hu₀N : u₀ ∈ N := by
    have : u₀ = n⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← hc_eq]
    rw [this]; exact N.inv_mem hn
  apply Subtype.ext
  rw [← hu₀, Subgroup.coe_one]
  exact (MonoidHom.mem_ker (f := φU)).mp hu₀N

open OddOrder.RepresentationTheory Representation in
open scoped commutatorElement IsMulCommutative in
/-- **Peterfalvi (9.7) case (b), the `u ∣ (p^q-1)/(p-1)` divisibility** (unconditional).

The Singer divisibility `|Ū| ∣ p^q-1` (`chiefFactor_caseB_image_cyclic`) upgrades to
`|Ū| ∣ (p^q-1)/(p-1)` via the fixed-point-free coprimality `Coprime |Ū| (p-1)`
(`chiefFactor_caseB_image_coprime`): since `(p-1) ∣ (p^q-1)` and `|Ū|` is coprime to `p-1`,
`|Ū|·(p-1) ∣ p^q-1`, hence `|Ū| ∣ (p^q-1)/(p-1)`.  This is the second case-(b) divisibility of
`CliffordCaseBData`, now established without any external coprimality hypothesis. -/
theorem chiefFactor_caseB_image_dvd_norm [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) :
    Nat.card ↥(((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype).range) ∣ (chief.p ^ data.q - 1) / (chief.p - 1) := by
  have hcop := chiefFactor_caseB_image_coprime chief hcaseB
  obtain ⟨_, hdvd⟩ := chiefFactor_caseB_image_cyclic chief hcaseB
  have hp1 : 1 ≤ chief.p := chief.p_prime.pos
  -- `(p-1) ∣ (p^q-1)` since `p ≡ 1 [MOD p-1]`.
  have hpd : (chief.p - 1) ∣ (chief.p ^ data.q - 1) := by
    have h1 : 1 ≡ chief.p [MOD chief.p - 1] := (Nat.modEq_iff_dvd' hp1).mpr (dvd_refl _)
    have h2 : 1 ^ data.q ≡ chief.p ^ data.q [MOD chief.p - 1] := h1.pow data.q
    rw [one_pow] at h2
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp h2
  -- `|Ū|·(p-1) ∣ p^q-1` (coprime), hence `|Ū| ∣ (p^q-1)/(p-1)`.
  have hmul := hcop.mul_dvd_of_dvd_of_dvd hdvd hpd
  exact (Nat.dvd_div_iff_mul_dvd hpd).mpr (by rwa [mul_comm] at hmul)

open scoped commutatorElement in
/-- **Peterfalvi (9.7) case (b): the `U`-action on `H̄` is fixed-point-free off `C = C_U(H̄)`.**
When `U` acts irreducibly on the chief factor `H̄ = H/H₀` (Clifford case (b)), any `g ∈ U` whose
image `φ_U(g)` is nontrivial (i.e. `g ∉ C`) acts fixed-point-freely on `H̄`: `φ_U(g)·x = x → x = 1`.

This is the structural heart of Peterfalvi (9.9) — `H̄ ⋊ Ū` is a Frobenius group, so a nontrivial
character `θ` of `H̄` has inertia `I(θ) ∩ U = C`, giving the degree `u = |U:C|` of the irreducible
characters of `HU` in `𝒳(H₀C')`.  The proof is pure Clifford theory: the image `Ū = φ_U(U)` is
abelian (`hComm`: `⁅a,b⁆ ∈ [U,U] ⊆ C_M(H)`) and acts irreducibly (`hcaseB`), so
`fixedPointFree_of_aInvariant_irreducible_comm` applies; the Singer field model is *not* needed. -/
theorem chiefFactor_caseB_action_fpf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hg : ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) g ≠ 1)
    (x : ↥data.H ⧸ chief.N)
    (hx : ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) g x = x) : x = 1 := by
  classical
  haveI : chief.N.Normal := chief.N_normal
  set act := typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant with hact
  set φU := act.φ.comp act.U.subtype with hφU
  -- An element of `U W₁` centralizing `H` acts trivially on `H̄`.
  have hcentral_triv : ∀ c : ↥(data.typeP.U ⊔ data.typeP.W1),
      (c : G) ∈ Subgroup.centralizer (data.typeP.H : Set G) → act.φ c = 1 := by
    intro c hc
    have hfix : ∀ z : ↥data.typeP.H, (typeP_conjAction data.typeP c) z = z := by
      intro z
      apply Subtype.ext
      rw [typeP_conjAction_apply]
      have hcom : (z : G) * (c : G) = (c : G) * (z : G) :=
        (Subgroup.mem_centralizer_iff.mp hc) (z : G) z.2
      rw [← hcom, mul_assoc, mul_inv_cancel, mul_one]
    ext y
    refine QuotientGroup.induction_on y ?_
    intro z
    show (act.φ c) (QuotientGroup.mk' chief.N z) = QuotientGroup.mk' chief.N z
    have hstep : (act.φ c) (QuotientGroup.mk' chief.N z)
        = QuotientGroup.mk' chief.N ((typeP_conjAction data.typeP c) z) := rfl
    rw [hstep, hfix z]
  -- `Ū = φU(U)` is abelian: `φU ⁅a, b⁆ = 1` since `⁅a, b⁆` maps into `[U, U] ⊆ C(H)`.
  have hComm : ∀ a b : ↥act.U, Commute (φU a) (φU b) := by
    intro a b
    refine commutatorElement_eq_one_iff_commute.mp ?_
    rw [← map_commutatorElement φU a b]
    show act.φ (act.U.subtype ⁅a, b⁆) = 1
    apply hcentral_triv
    change ((data.typeP.U ⊔ data.typeP.W1).subtype.comp act.U.subtype) ⁅a, b⁆
        ∈ Subgroup.centralizer (data.typeP.H : Set G)
    rw [map_commutatorElement]
    exact typeP_commutator_U_centralizes_H data.typeP
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2))
  exact fixedPointFree_of_aInvariant_irreducible_comm hComm hcaseB _ hg x hx

/-- **Peterfalvi (9.9): the `U`-action on `Irr(H̄)` is fixed-point-free off `C`.**  In Clifford
case (b), if a nontrivial irreducible character `θ` of the chief factor `H̄ = ↥H ⧸ N` is invariant
under the `U`-action `φ_U(g)`, then `g` acts trivially (`φ_U(g) = 1`, i.e. `g ∈ C = C_U(H̄)`).

This is the **character-side inertia** `I_U(θ) ⊆ C` of Peterfalvi (9.9.a), proven *realization-free*:
the abelian `Irr ↔ Hom` bridge (`exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative`)
turns `θ` into a linear character `θ̂`, and a `φ_U(g)`-invariant `θ̂` with `φ_U(g)` fixed-point-free
(`chiefFactor_caseB_action_fpf`, valid for `g ∉ C`) is trivial
(`eq_one_of_invariant_of_fixedPointFree`), contradicting `θ` nontrivial.  No realization of `H̄` as
a subgroup is needed; it works on the abstract quotient `↥H ⧸ N` with the abstract action `φ_U`. -/
theorem chiefFactor_caseB_char_inertia [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    {θ : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hθ : (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) ≠ trivialClassFunction _)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hinv : ∀ x, (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)
        (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
          (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype) g x)
          = (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x) :
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
      (typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U.subtype) g
        = 1 := by
  classical
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  by_contra hne
  have hfpf : MonoidHom.FixedPointFree
      (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
        (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) g) :=
    chiefFactor_caseB_action_fpf chief hcaseB g hne
  obtain ⟨θhom, hθhom⟩ :=
    exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative θ.isIrreducible
  have hinvhom : ∀ x, θhom (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
      chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
      chief.N_aInvariant).U.subtype) g x) = θhom x := fun x =>
    Units.ext (by rw [hθhom, hθhom]; exact hinv x)
  have h1 : θhom = 1 := eq_one_of_invariant_of_fixedPointFree hfpf hinvhom
  apply hθ
  ext x
  have hx := hθhom x
  rw [h1] at hx
  simpa using hx.symm

/-- **Inflation equivariance for the chief-factor action.**  The inflation map
`compHom (mk' N) : ClassFunction (↥H/N) → ClassFunction ↥H` intertwines the conjugation action
`typeP_conjAction a` on `↥H` (upstairs) with the descended action `quotientMulAutHom a` on the
chief factor `↥H/N` (downstairs): inflating `θ̄` and acting by `a` upstairs equals acting by `a`
downstairs and then inflating.  Immediate from `quotientMulAutHom_apply_mk'`
(`mk' N (a · h) = a · (mk' N h)`).

This is the algebraic core that turns the *concrete* conjugation invariance of an inflated
character into the *abstract* `φ_U`-invariance consumed by `chiefFactor_caseB_char_inertia`,
without realizing `H̄` as a subgroup. -/
theorem compHom_typeP_conjAction_inflation [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (a : ↥(data.typeP.U ⊔ data.typeP.W1))
    (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) :
    ClassFunction.compHom (typeP_conjAction data.typeP a).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N) θbar)
      = ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (ClassFunction.compHom (quotientMulAutHom chief.N_aInvariant a).toMonoidHom θbar) :=
  rfl

/-- **Char-inertia inflation, parametrized over the core stabilizer-triviality `hcore`.**
Strips the inflation (`compHom_typeP_conjAction_inflation`, `mk'` injective) from the `compHom`-fixing
hypothesis to feed the per-element action-invariance to `hcore`.  Case (b) supplies `hcore` as
`chiefFactor_caseB_char_inertia` (`U`-irreducible); case (a) via the non-Galois `Hpart` analysis. -/
theorem caseB_char_inertia_inflation_of_core [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hcore : ∀ (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U),
        (∀ x, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)
            (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
              (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
                chief.N_aInvariant).U.subtype) g x)
              = (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x) →
        ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
          (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype) g = 1)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hfix : ClassFunction.compHom (typeP_conjAction data.typeP
              ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
                chief.N_aInvariant).U.subtype g)).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))
            = ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) :
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
      (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) g = 1 := by
  rw [compHom_typeP_conjAction_inflation] at hfix
  have hfix2 := ClassFunction.compHom_injective_of_surjective
    (QuotientGroup.mk'_surjective chief.N) hfix
  apply hcore g
  intro x
  rw [show ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) g
      = quotientMulAutHom chief.N_aInvariant
          ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype g) from rfl]
  exact congrFun (congrArg (fun f : ClassFunction (↥data.H ⧸ chief.N) ℂ =>
    (f : (↥data.H ⧸ chief.N) → ℂ)) hfix2) x

theorem caseB_char_inertia_inflation [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hθbar : (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) ≠ trivialClassFunction _)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hfix : ClassFunction.compHom (typeP_conjAction data.typeP
              ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
                chief.N_aInvariant).U.subtype g)).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))
            = ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) :
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
      (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) g = 1 :=
  caseB_char_inertia_inflation_of_core (chiefFactor_caseB_char_inertia hcaseB hθbar) g hfix

/-! ### (9.9.a) realization: concrete `HU`-conjugation ↔ abstract `typeP_conjAction`

The (9.9.a) inertia of a constituent of `Res^{HU}_H χ` is computed by `ClassFunction.conjBy` in
`HU = (H ⊔ U).subgroupOf M`, with `H` realized as `hInHu data = (H.subgroupOf M).subgroupOf HU`.
The realization iso `hInHuEquivH : ↥(hInHu) ≃* ↥H` (composite of two `subgroupOfEquivOfLe`)
preserves the underlying `G`-element, so it intertwines `conjBy g` (for `g ∈ HU`) with the
abstract `typeP_conjAction a` (for `a ∈ U W₁` with the same `G`-image).  This is the last
realization step of (9.9.a)'s `I_U(θ) ⊆ C`: it turns a concrete `HU`-inertia hypothesis into the
`typeP_conjAction`-invariance consumed by `caseB_char_inertia_inflation`. -/

/-- The realization iso `↥(H-in-HU) ≃* ↥H`: `H` realized inside `HU = H ⊔ U` is `H`, via the
composite of `subgroupOfEquivOfLe (H.subgroupOf M ≤ HU)` and `subgroupOfEquivOfLe (H ≤ M)`. -/
noncomputable def hInHuEquivH {M : Subgroup G} (data : TypesIIIIIIVSetup M) :
    ↥(hInHu data) ≃* ↥data.H :=
  (Subgroup.subgroupOfEquivOfLe
      (Subgroup.subgroupOf_mono M (le_sup_left : data.H ≤ data.H ⊔ data.U))).trans
    (Subgroup.subgroupOfEquivOfLe (data.typeP.H_le.trans (derivedInG_le_self M)))

/-- The realization iso preserves the underlying `G`-element. -/
theorem hInHuEquivH_coe {M : Subgroup G} (data : TypesIIIIIIVSetup M) (h : ↥(hInHu data)) :
    ((hInHuEquivH data h : ↥data.H) : G) = (((h : ↥(huSub data)) : ↥M) : G) := rfl

/-- **(9.9.a) realization, conjugation equivariance.**  Under the iso
`hInHuEquivH : ↥(hInHu) ≃* ↥H`, the concrete conjugation `conjBy g` in `HU` (for `g ∈ HU`)
corresponds to the abstract conjugation `typeP_conjAction a` on `↥H` (for `a ∈ U W₁` with the same
`G`-image `↑g = ↑a`).  Both are conjugation by the same `G`-element, so the equality reduces to
`g·h·g⁻¹ = a·h·a⁻¹` in `G`. -/
theorem conjBy_compHom_hInHuEquivH {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (a : ↥(data.typeP.U ⊔ data.typeP.W1)) (g : ↥(huSub data))
    (hag : ((g : ↥M) : G) = (a : G)) (θ : ClassFunction ↥data.H ℂ) :
    ClassFunction.conjBy g (ClassFunction.compHom (hInHuEquivH data).toMonoidHom θ)
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (typeP_conjAction data.typeP a).toMonoidHom θ) := by
  ext h
  rw [ClassFunction.conjBy_apply, ClassFunction.compHom_apply, ClassFunction.compHom_apply,
    ClassFunction.compHom_apply]
  refine congrArg _ (Subtype.ext ?_)
  simp only [MulEquiv.coe_toMonoidHom, hInHuEquivH_coe, typeP_conjAction_apply,
    Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hag]

/-- **Realized stabilizer-triviality, parametrized over the char-inertia core `hcharInertia`.**
The case-agnostic transport: a `U`-element `a` realized by `g ∈ HU` fixing `θ₀` (`conjBy` form) is
turned into the `compHom (typeP_conjAction)` form (`conjBy_compHom_hInHuEquivH`, injective inflation)
and fed to `hcharInertia` to conclude `φ a = 1`.  Case (b) supplies `hcharInertia` as
`caseB_char_inertia_inflation`; case (a) via the non-Galois analog. -/
theorem caseB_inertia_realized_of_charInertia [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hcharInertia : ∀ (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U),
        ClassFunction.compHom (typeP_conjAction data.typeP
              ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
                chief.N_aInvariant).U.subtype g)).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))
            = ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) →
        ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
          (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype) g = 1)
    (a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (g : ↥(huSub data))
    (hag : ((g : ↥M) : G) =
      (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G))
    (hfix : ClassFunction.conjBy g
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) :
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
      (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) a = 1 := by
  rw [conjBy_compHom_hInHuEquivH data
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U.subtype a)
    g hag] at hfix
  exact hcharInertia a
    (ClassFunction.compHom_injective_of_surjective (hInHuEquivH data).surjective hfix)

theorem caseB_inertia_realized [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hθbar : (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) ≠ trivialClassFunction _)
    (a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (g : ↥(huSub data))
    (hag : ((g : ↥M) : G) =
      (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G))
    (hfix : ClassFunction.conjBy g
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) :
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
      (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) a = 1 :=
  caseB_inertia_realized_of_charInertia (caseB_char_inertia_inflation hcaseB hθbar) a g hag hfix

/-! ### (9.9.a) inertia lift: `I_{HU}(θ₀) = HC`

For the (9.9.a) Clifford degree we need the inertia in `HU` of the realized chief-factor character
`θ₀ = compHom (hInHuEquivH) (compHom (mk' N) θ̄)` to be exactly `HC = hInHu ⊔ cInHu`.  The two
inclusions:

* `cInHu ≤ I(θ₀)` (`cInHu_le_inertia`): `C = C_U(H̄)` acts trivially on the chief factor, so it fixes
  `θ₀` (the *easy* direction — `compHom_typeP_conjAction_inflation` + `quotientMulAutHom = 1` on the
  kernel `cSub`);
* `I(θ₀) ⊓ uInHu ≤ cInHu` (`inertia_inf_uInHu_le_cInHu`): the *hard* direction, exactly
  `caseB_inertia_realized` (any `U`-element fixing `θ₀` acts trivially on `H̄`).

Together with `H ≤ I(θ₀)` (automatic) and `H ⊔ U = ⊤`, the modular decomposition
`I(θ₀) = H ⊔ (I(θ₀) ⊓ U)` gives `I(θ₀) = HC` (`inertia_eq_hcInHu`). -/

/-- **`C ≤ I_{HU}(θ₀)`**: `C = C_U(H̄)` fixes the realized chief-factor character `θ₀` (it acts
trivially on `H̄`, so `quotientMulAutHom = 1` on `cSub = ker(uActionHom)`, and the inflation is
unchanged).  The easy half of the (9.9.a) inertia lift. -/
theorem cInHu_le_inertia [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)} :
    cInHu data chief ≤ ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) := by
  intro c hc
  rw [ClassFunction.mem_inertia]
  have hcG : ((c : ↥M) : G) ∈ cSub data chief := by
    simp only [cInHu, Subgroup.mem_subgroupOf] at hc; exact hc
  simp only [cSub, Subgroup.mem_map] at hcG
  obtain ⟨w, ⟨ĉ', hĉ', hĉ'w⟩, hwc⟩ := hcG
  have hq1 : quotientMulAutHom chief.N_aInvariant w = 1 := by rw [← hĉ'w]; exact hĉ'
  have hag : ((c : ↥M) : G) = (w : G) := hwc.symm
  rw [conjBy_compHom_hInHuEquivH data w c hag, compHom_typeP_conjAction_inflation, hq1]
  rfl

/-- **`I(θ₀) ⊓ U ≤ C`, parametrized over the realized stabilizer-triviality `hrealized`.**  The
case-agnostic part of the hard inertia direction: any `g ∈ I(θ₀) ⊓ U` realizes as a `U`-element `a`
whose `θ₀`-fixing (`mem_inertia`) feeds `hrealized` to conclude `a ∈ ker(uActionHom) = C`.  Case (b)
supplies `hrealized` as `caseB_inertia_realized`; case (a) via the non-Galois analog. -/
theorem inertia_inf_uInHu_le_cInHu_of_realized [Finite G] {M : Subgroup G}
    (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hrealized : ∀ (a : ↥((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U)) (g : ↥(huSub data)),
        (((g : ↥M) : G) = (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G)) →
        ClassFunction.conjBy g (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
            (ClassFunction.compHom (QuotientGroup.mk' chief.N)
              (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
          = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) →
        ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
          (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype) a = 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) ⊓ uInHu data
      ≤ cInHu data chief := by
  rintro g ⟨hgin, hgu⟩
  have hgU : ((g : ↥M) : G) ∈ data.typeP.U := by
    simp only [uInHu] at hgu; exact hgu
  have hgUW1 : ((g : ↥M) : G) ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_left hgU
  set a : ↥((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U) :=
    ⟨⟨((g : ↥M) : G), hgUW1⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha_def
  have hag : ((g : ↥M) : G)
      = (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) := rfl
  have hker : a ∈ (uActionHom data chief).ker :=
    hrealized a g hag (ClassFunction.mem_inertia.mp hgin)
  simp only [cInHu, Subgroup.mem_subgroupOf, cSub, Subgroup.mem_map]
  exact ⟨_, ⟨a, hker, rfl⟩, rfl⟩

theorem inertia_inf_uInHu_le_cInHu [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hθbar : (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) ≠ trivialClassFunction _) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) ⊓ uInHu data
      ≤ cInHu data chief :=
  inertia_inf_uInHu_le_cInHu_of_realized data chief (caseB_inertia_realized hcaseB hθbar)

/-- **Inertia lift `I_{HU}(θ₀) = HC`, parametrized over the hard direction** `I(θ₀) ⊓ U ≤ C`.  The
case-agnostic assembly: `⊇` from `H ≤ I(θ₀)` (`subgroup_le_inertia`) and `cInHu_le_inertia` (both
case-independent), `⊆` by the modular decomposition `g = h·u` (`H ⊔ U = ⊤`, `H ◁ HU`) with the
`U`-part `u ∈ I(θ₀) ⊓ U ≤ C` supplied by `hinf`.  Both Clifford cases instantiate `hinf`: case (b)
via `inertia_inf_uInHu_le_cInHu` (`U`-irreducible), case (a) via the non-Galois `Hpart` analysis. -/
theorem inertia_eq_hcInHu_of_inf_le [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hinf : ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) ⊓ uInHu data
      ≤ cInHu data chief) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cInHu data chief := by
  set θ₀ := ClassFunction.compHom (hInHuEquivH data).toMonoidHom
    (ClassFunction.compHom (QuotientGroup.mk' chief.N)
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) with hθ₀
  apply le_antisymm
  · intro g hg
    have hgtop : g ∈ hInHu data ⊔ uInHu data := hInHu_sup_uInHu_eq_top data ▸ Subgroup.mem_top g
    rw [Subgroup.mem_sup_of_normal_left] at hgtop
    obtain ⟨h, hh, u, hu, rfl⟩ := hgtop
    have hh_in : h ∈ ClassFunction.inertia (H := hInHu data) θ₀ :=
      ClassFunction.subgroup_le_inertia θ₀ hh
    have hu_in : u ∈ ClassFunction.inertia (H := hInHu data) θ₀ := by
      have hmem : h⁻¹ * (h * u) ∈ ClassFunction.inertia (H := hInHu data) θ₀ :=
        mul_mem (inv_mem hh_in) hg
      rwa [inv_mul_cancel_left] at hmem
    exact mul_mem (Subgroup.mem_sup_left hh)
      (Subgroup.mem_sup_right (hinf ⟨hu_in, hu⟩))
  · rw [sup_le_iff]
    exact ⟨ClassFunction.subgroup_le_inertia θ₀, cInHu_le_inertia data chief⟩

/-- **Peterfalvi (9.9.a), the inertia lift: `I_{HU}(θ₀) = HC`.**  The inertia in `HU` of the
realized chief-factor character `θ₀` is exactly the inertia subgroup `HC = hInHu ⊔ cInHu`.  `⊇` from
`H ≤ I(θ₀)` (automatic) and `cInHu_le_inertia`; `⊆` by decomposing `g ∈ I(θ₀)` as `h·u`
(`H ⊔ U = ⊤`, `H ◁ HU`), where `u = h⁻¹ g ∈ I(θ₀) ⊓ U ≤ C` (`inertia_inf_uInHu_le_cInHu`).  With
`HC ◁ HU` (`hcInHu_normal`) this makes `Ind_{HC}^{HU}` of an `HC`-character over `θ₀` irreducible. -/
theorem inertia_eq_hcInHu [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hθbar : (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) ≠ trivialClassFunction _) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cInHu data chief :=
  inertia_eq_hcInHu_of_inf_le data chief (inertia_inf_uInHu_le_cInHu data chief hcaseB hθbar)

/-- **Peterfalvi (9.7) case (b) carrier.**  When `U` acts irreducibly on the chief factor
`H̄ = H/H₀` (Clifford case (b), the left branch of `chiefFactor_clifford_U_dichotomy`), the
field-model divisibilities of `CliffordCaseBData` hold: with `chars.u = |Ū|` (pinned in
`Section11CharacterData.u_eq_card_quotient`), `Coprime |Ū| (p-1)` and `|Ū| ∣ (p^q-1)/(p-1)` are the
unconditional `chiefFactor_caseB_image_coprime` / `chiefFactor_caseB_image_dvd_norm`. -/
noncomputable def clifford_caseB_data [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) :
    CliffordCaseBData chars where
  field_model := True
  field_model_holds := trivial
  Ubar_cyclic := True
  Ubar_cyclic_holds := trivial
  u_coprime_p_sub_one := by
    rw [chars.u_eq_card_quotient]; exact chiefFactor_caseB_image_coprime chief hcaseB
  u_dvd_norm_quotient := by
    rw [chars.u_eq_card_quotient]; exact chiefFactor_caseB_image_dvd_norm chief hcaseB
  actsIrreducibly := hcaseB

/-- **Peterfalvi (9.7) case (a) carrier.**  When `H̄` contains a `U`-invariant order-`p` factor `S₀`
(Clifford case (a), the right branch of `chiefFactor_clifford_U_dichotomy`), the chief factor splits
as the internal direct product of `q = |W₁|` order-`p` factors — the `U W₁`-orbit of `S₀`, packaged
as a `Fin q`-family via the `SupIndep` partition of `exists_supIndep_aInvariant_family_of_iSup` — and
the `U`-action on `S₀` has image of order `a ∣ p - 1` (`aInvariantRestrictAut_range_card_dvd`). -/
noncomputable def clifford_caseA_data [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    {S₀ : Subgroup (↥data.H ⧸ chief.N)} (hS₀ne : S₀ ≠ ⊥)
    (hS₀inv : IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) S₀)
    (hS₀card : Nat.card ↥S₀ = chief.p)
    (hirr₀ : ∀ J, IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) J → J ≤ S₀ → J = ⊥ ∨ J = S₀) :
    CliffordCaseAData chars := by
  classical
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  haveI : chief.N.Normal := chief.N_normal
  set act := typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant with hact
  set φU := act.φ.comp act.U.subtype with hφU
  have hUnorm : act.U.Normal := (typeP_uW1_frobenius data.typeP hU).isNormal
  -- The `U W₁`-orbit of `S₀` spans `H̄` (irreducibility), giving a `SupIndep` family of order-`p`
  -- factors whose count `k` satisfies `|H̄| = |S₀|^k`.
  have hspan : ⨆ a, act.φ a • S₀ = ⊤ :=
    iSup_smul_eq_top_of_irreducible (φ := act.φ) chief.quotient_chiefFactor hS₀ne
  -- (`Exists` cannot be destructured into the `Type`-valued `CliffordCaseAData`; use `choose`.)
  have hexist := exists_supIndep_aInvariant_family_of_iSup
    (φ := φU) (S := fun a => act.φ a • S₀) (n := Nat.card ↥S₀)
    (fun x y => chief.quotient_elementaryAbelian.comm x y) hspan
    (fun a => isAInvariant_comp_subtype_pointwise_smul hUnorm hS₀inv a)
    (fun a J hJinv hJle => forall_aInvariant_le_pointwise_smul hUnorm hirr₀ a J hJinv hJle)
    (fun a _ => card_pointwise_smul act.φ a S₀)
  let t : Finset ↥(data.typeP.U ⊔ data.typeP.W1) := hexist.choose
  have ht_card : Nat.card (↥data.H ⧸ chief.N) = Nat.card ↥S₀ ^ t.card := hexist.choose_spec.2.2.2
  -- `|H̄| = p^t.card` and `|H̄| = p^q`, so `t.card = q`.
  rw [hS₀card, chiefFactor_quotient_card chief] at ht_card
  have ht_card_q : t.card = data.q :=
    (Nat.pow_right_injective chief.p_prime.two_le ht_card).symm
  -- Reindex the `q`-element orbit family by `Fin q`.
  let e : ↥t ≃ Fin data.q := t.equivFin.trans (finCongr ht_card_q)
  refine
    { Hpart := fun j => act.φ ↑(e.symm j) • S₀
      Hpart_order := fun j => (card_pointwise_smul act.φ _ S₀).trans hS₀card
      W1_transitive_on_parts := True
      W1_transitive_on_parts_holds := trivial
      a := Nat.card ↥(aInvariantRestrictAut hS₀inv).range
      a_pos := Nat.card_pos
      a_dvd_p_sub_one := ?_
      quotient_factors_cyclic_order_a := True
      quotient_factors_cyclic_order_a_holds := trivial
      Ubar_embeds_product := True
      Ubar_embeds_product_holds := trivial }
  -- `a = |U-image on S₀| ∣ |S₀| - 1 = p - 1` (the order-`p` factor is cyclic, `Aut ≅ (ZMod p)ˣ`).
  have hdvd := aInvariantRestrictAut_range_card_dvd hS₀inv (hS₀card ▸ chief.p_prime)
  rwa [hS₀card] at hdvd

/-- **Peterfalvi (9.7)**: the Clifford-theory dichotomy for the action on the chief factor `H/H_0`.

The case split is `chiefFactor_clifford_U_dichotomy`: `U` acts on `H̄ = H/H₀` either irreducibly
(case (b)) or with a `U`-invariant order-`p` factor (case (a)).  Each branch is packaged into its
carrier: `clifford_caseB_data` (the Singer field-model divisibilities `Coprime |Ū| (p-1)`,
`|Ū| ∣ (p^q-1)/(p-1)`, with `chars.u = |Ū|` pinned in `Section11CharacterData.u_eq_card_quotient`)
and `clifford_caseA_data` (the `q` order-`p` Clifford factors and the bound `a ∣ p-1`). -/
theorem clifford_dichotomy [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) :
    Nonempty (CliffordCaseAData chars) ∨ Nonempty (CliffordCaseBData chars) := by
  rcases chiefFactor_clifford_U_dichotomy chief with hcaseB | ⟨S₀, hS₀ne, hS₀inv, hS₀card, hirr₀⟩
  · exact Or.inr ⟨clifford_caseB_data chars hcaseB⟩
  · exact Or.inl ⟨clifford_caseA_data chars hS₀ne hS₀inv hS₀card hirr₀⟩

/-! ## (9.8)--(9.10): character counts in the two Clifford cases -/

/-- **Generic §9↔§6 reducible count over a carrier `K`** (Coq `PFsection9` `nb_redM`): for a
normal `K.subgroupOf M ◁ ↥M` with `K ≤ M'`, `W₁ ⊓ K = ⊥`, `W₂ ⊄ K`, and the chief-factor image
order `|W̄₂| = p`, the §9 family `𝒮(K)` contains exactly `p − 1` reducible characters.  Both
`K = H₀` and `K = H₀C` instantiate this (the unifying condition `K ∩ H = H₀` enters through the
`|W̄₂| = p` input).  The bijection `Irr(K̄) ⊇ B' ↔ {reducible 𝒮(K)}` is the inflation–induction
composite `χ̄ ↦ induceHU (compHom g χ̄) = compHom (mk' K) (induce K̄ χ̄)`. -/
theorem reducible_count_sOf_K [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (K : Subgroup G) [hKnorm : (K.subgroupOf M).Normal]
    (hN'le : K.subgroupOf M ≤ (derivedInG M).subgroupOf M)
    (hW1inf : data.W1.subgroupOf M ⊓ K.subgroupOf M = ⊥)
    (hW2notle : ¬ data.W2.subgroupOf M ≤ K.subgroupOf M)
    (hW2card : Nat.card ↥((data.W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      = chief.p) :
    {φ ∈ sOf data K | ¬ IsIrreducibleCharacter φ}.ncard = chief.p - 1 := by
  classical
  haveI hN : (K.subgroupOf M).Normal := hKnorm
  letI : Fintype ↥M := Fintype.ofFinite _
  have hKhu : K.subgroupOf M ≤ huSub data := by
    rw [huSub_eq_derivedInG_subgroupOf]; exact hN'le
  have hodd : Odd (Nat.card G) := hG.odd
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  have hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1) := by
    rw [show Nat.card ↥(derivedInG M) = Nat.card ↥data.typeP.H * Nat.card ↥data.typeP.U by
      rw [← data.typeP.derived_complement.card_mul,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeP.H_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeP.U_le).toEquiv]]
    exact (Nat.Coprime.mul_right (typeP_coprime_H_W1 data.typeP).symm
      (typeP_coprime_U_W1 data.typeP hU).symm).symm
  set h := chiefFactorQuotientHypothesisGen chief (K.subgroupOf M) hN'le hW1inf hW2notle hodd hHall with hh_def
  have hKeq : h.K = (huSub data).map (QuotientGroup.mk' (K.subgroupOf M)) :=
    chiefFactorQuotientHypothesisGen_K_eq chief (K.subgroupOf M) hN'le hW1inf hW2notle hodd hHall
  -- the inflation hom `g : ↥(huSub) →* ↥(h.K)`, surjective with kernel `H₀`
  set sm := (QuotientGroup.mk' (K.subgroupOf M)).subgroupMap (huSub data) with hsm_def
  set g : ↥(huSub data) →* ↥h.K :=
    (MulEquiv.subgroupCongr hKeq.symm).toMonoidHom.comp sm with hg_def
  have hg_surj : Function.Surjective g :=
    (MulEquiv.subgroupCongr hKeq.symm).surjective.comp
      ((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap_surjective (huSub data))
  have hg_ker : g.ker = (K.subgroupOf M).subgroupOf (huSub data) := by
    have hsmker : sm.ker = (K.subgroupOf M).subgroupOf (huSub data) := by
      rw [hsm_def, Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    rw [hg_def]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ (MulEquiv.subgroupCongr hKeq.symm).injective]
    rw [← MonoidHom.mem_ker, hsmker]
  -- instances for the §6 count, the commute, and `induceHU` (one shared scope, no diamonds)
  haveI : Invertible (Nat.card (↥M ⧸ (K.subgroupOf M)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : NeZero (Nat.card ↥h.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : Fintype ↥h.K := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥h.K : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible
      (Nat.card ↥((huSub data).map (QuotientGroup.mk' (K.subgroupOf M))) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- the commute / Φ-identity: `induceHU (compHom g χ̄) = compHom (mk' N) (induce h.K χ̄)`
  have hPhi : ∀ χbar : IrreducibleCharacter ↥h.K,
      induceHU data (ClassFunction.compHom g (χbar : ClassFunction ↥h.K ℂ))
        = ClassFunction.compHom (QuotientGroup.mk' (K.subgroupOf M))
            (ClassFunction.induce h.K (χbar : ClassFunction ↥h.K ℂ)) := by
    intro χbar
    have hunfold : ∀ Y : ClassFunction ↥(huSub data) ℂ,
        induceHU data Y = ClassFunction.induce (huSub data) Y := fun _ => rfl
    rw [hg_def, ← ClassFunction.compHom_comp, hunfold, hsm_def,
      induce_compHom_subgroupMap_mk' (K.subgroupOf M)
        (hKhu)
        (ClassFunction.compHom (MulEquiv.subgroupCongr hKeq.symm).toMonoidHom
          (χbar : ClassFunction ↥h.K ℂ))]
    congr 1
    exact induce_compHom_subgroupCongr hKeq.symm (χbar : ClassFunction ↥h.K ℂ)
  -- the §6 reducible-with-`H̄⊄ker` subset `B'` of `Irr(K̄)` (counted as `p − 1`)
  set B' : Set (IrreducibleCharacter ↥h.K) :=
    {χbar | ¬ IsIrreducibleCharacter (ClassFunction.induce h.K (χbar : ClassFunction ↥h.K ℂ))
      ∧ ¬ (((hInHu data).map g : Set ↥h.K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (χbar : ClassFunction ↥h.K ℂ))} with hB'_def
  have hW2H : h.W2.subgroupOf h.K ≤ (hInHu data).map g := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    have hW2eq : h.W2
        = (data.W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)) := rfl
    rw [hW2eq, Subgroup.mem_map] at hy
    obtain ⟨w, hw, hwy⟩ := hy
    rw [Subgroup.mem_subgroupOf] at hw
    have hwH : (w : G) ∈ data.H := (data.typeP.W2_le hw).1
    have hwHU : w ∈ huSub data := by
      rw [huSub, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_left hwH
    refine ⟨⟨w, hwHU⟩, ?_, ?_⟩
    · show (⟨w, hwHU⟩ : ↥(huSub data)) ∈ (data.H.subgroupOf M).subgroupOf (huSub data)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hwH
    · apply Subtype.ext
      have hco : ((g ⟨w, hwHU⟩ : ↥h.K) : ↥M ⧸ (K.subgroupOf M))
          = QuotientGroup.mk' (K.subgroupOf M) w := rfl
      rw [hco]; exact hwy
  -- image equality: `{φ ∈ 𝒮(H₀) | ¬ irr φ} = Φ '' B'`, `Φ χ̄ = induceHU (compHom g χ̄)`
  have himage : {φ ∈ sOf data K | ¬ IsIrreducibleCharacter φ}
      = (fun χbar : IrreducibleCharacter ↥h.K => induceHU data (ClassFunction.compHom g (χbar : ClassFunction ↥h.K ℂ))) '' B' := by
    ext φ
    simp only [Set.mem_sep_iff, Set.mem_image, hB'_def, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hφS, hred⟩
      rw [mem_sOf] at hφS
      obtain ⟨χ, hχxi, rfl⟩ := hφS
      rw [mem_xiOf] at hχxi
      obtain ⟨hχX, hχH0⟩ := hχxi
      have hgker_sub : (g.ker : Set ↥(huSub data)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ) := by
        rw [hg_ker]; exact hχH0
      obtain ⟨χbar, hχbar⟩ :=
        OddOrder.RepresentationTheory.exists_compHom_eq_of_subset_characterKernel hg_surj χ hgker_sub
      refine ⟨χbar, ⟨?_, ?_⟩, ?_⟩
      · rw [← isIrreducibleCharacter_compHom_mk'_iff (K.subgroupOf M), ← hPhi χbar, hχbar]
        exact hred
      · rw [← subset_characterKernel_compHom_iff g (χbar : ClassFunction ↥h.K ℂ) (hInHu data), hχbar]
        exact hχX
      · rw [hχbar]
    · rintro ⟨χbar, ⟨hred, hker⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [mem_sOf]
        refine ⟨⟨ClassFunction.compHom g (χbar : ClassFunction ↥h.K ℂ),
          IsIrreducibleCharacter.compHom_of_surjective hg_surj χbar.isIrreducible⟩, ?_, rfl⟩
        rw [mem_xiOf]
        refine ⟨?_, ?_⟩
        · show ¬ ((hInHu data : Set ↥(huSub data)) ⊆ _)
          rw [subset_characterKernel_compHom_iff g (χbar : ClassFunction ↥h.K ℂ) (hInHu data)]
          exact hker
        · rw [← hg_ker]
          intro x hx
          rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
          rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
            OddOrder.Peterfalvi.S03.characterDegree_def, ClassFunction.compHom_apply,
            ClassFunction.compHom_apply, hx, map_one]
      · rw [hPhi χbar, isIrreducibleCharacter_compHom_mk'_iff]
        exact hred
  -- injectivity of `Φ` on `B'`
  have hInj : Set.InjOn
      (fun χbar : IrreducibleCharacter ↥h.K => induceHU data (ClassFunction.compHom g (χbar : ClassFunction ↥h.K ℂ))) B' := by
    intro χbar hχbar χbar' _ heq
    simp only at heq
    rw [hPhi χbar, hPhi χbar'] at heq
    rw [hB'_def, Set.mem_setOf_eq] at hχbar
    exact h.induce_injective_on_reducible hχbar.1
      (ClassFunction.compHom_injective_of_surjective
        (QuotientGroup.mk'_surjective (K.subgroupOf M)) heq)
  -- conclude: `|{φ ∈ 𝒮(H₀) | ¬ irr}| = |B'| = w̄₂ − 1 = p − 1`
  rw [himage, hInj.ncard_image]
  have hcardW2 : Nat.card ↥h.W2 = chief.p := hW2card
  rw [hB'_def, ← Nat.card_coe_set_eq, ← hcardW2]
  exact h.card_reducible_Hnontrivial_induce_eq_W2_sub_one hW2H

theorem reducible_count_sOf_H0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    {φ ∈ sOf data chief.H0 | ¬ IsIrreducibleCharacter φ}.ncard = chief.p - 1 := by
  haveI := chiefFactor_H0_subgroupOf_normal chief
  refine reducible_count_sOf_K hG chief chief.H0
    (Subgroup.comap_mono (chief.H0_lt_H.le.trans data.typeP.H_le))
    (chiefFactor_W1_inf_H0_subgroupOf_eq_bot chief) ?_ (chiefFactor_card_W2bar chief)
  intro hle
  refine chiefFactor_W2_not_le_H0 chief (fun y hy => ?_)
  have hW2leM : data.W2 ≤ M := (data.typeP.W2_le.trans inf_le_left).trans (H_le_M data)
  have hyM : (⟨y, hW2leM hy⟩ : ↥M) ∈ data.W2.subgroupOf M := Subgroup.mem_subgroupOf.mpr hy
  exact Subgroup.mem_subgroupOf.mp (hle hyM)


/-- **Peterfalvi (9.8)**: character-count consequences in Clifford case (a).

Faithful to Peterfalvi (9.8.b,c,d) (count-statement audit, issue 2030):
* **(b)** `𝒮(H₀)` contains exactly `p-1` *reducible* characters; each has degree `qu` and lies
  in `𝒮(H₀C)`.
* **(c)** `𝒮(H₀C)` contains an *irreducible* character of degree `qu`.
* **(d)** `𝒮(H₀U')` contains at least `((p-1)/a)·(|U|/(a|U'|))` irreducible characters of
  degree `qa`.

All `𝒮(H₀·)` sets carry the `H₀`-join (`chief.H0 ⊔ ·`): Peterfalvi's `𝒮(H₀C)`/`𝒮(H₀U')` require
`H₀C`/`H₀U'` in the kernel, not `C`/`U'` alone.  Reducibility/irreducibility is
`IsIrreducibleCharacter`. -/
theorem caseA_character_counts [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseA : CliffordCaseAData chars) :
    {φ ∈ chars.SOf chief.H0 | ¬ IsIrreducibleCharacter φ}.ncard = chief.p - 1 ∧
      (∀ φ ∈ chars.SOf chief.H0, ¬ IsIrreducibleCharacter φ →
        φ 1 = ((data.q * chars.u : ℕ) : ℂ) ∧ φ ∈ chars.SOf (chief.H0 ⊔ chars.C)) ∧
      (∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.C), IsIrreducibleCharacter χ ∧
        χ 1 = ((data.q * chars.u : ℕ) : ℂ)) ∧
      ((chief.p - 1) / caseA.a) * (Nat.card ↥data.U / (caseA.a * Nat.card ↥chars.Uprime)) ≤
        {χ ∈ chars.SOf (chief.H0 ⊔ chars.Uprime) |
          IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard := by
  -- (9.8.b) reducible count is the §9↔§6 bijection `reducible_count_sOf_H0` (case-agnostic).
  refine ⟨reducible_count_sOf_H0 hG chief, ?_, ?_, ?_⟩
  · sorry
  · sorry
  · sorry

section
open scoped IsMulCommutative

/-- **`⁅H, H⁆ ≤ H₀`** (the chief factor `H̄ = H/H₀` is abelian): `derivedInG H ≤ H₀`.  Since
`↥H ⧸ N` is elementary abelian, `commutator ↥H ≤ N`, and mapping into `G` gives `derivedInG H ≤ H₀`.
A structural input of the (9.9.a) `⁅HC,HC⁆ ⊆ 𝒮(H₀C')`-kernel linearity. -/
theorem derivedInG_H_le_H0 {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    derivedInG data.H ≤ chief.H0 := by
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  rw [derivedInG, chief.H0_eq]
  apply Subgroup.map_mono
  rw [← QuotientGroup.ker_mk' chief.N]
  exact Abelianization.commutator_subset_ker (QuotientGroup.mk' chief.N)

/-- **`⁅C, H⁆ ≤ H₀`** (`C = C_U(H̄)` centralizes the chief factor): for `c ∈ C` and `h ∈ H`,
`c` acts trivially on `H̄ = H/H₀`, so `c h c⁻¹ ≡ h (mod H₀)` and `⁅c,h⁆ ∈ H₀`.  A structural
input of the (9.9.a) `⁅HC,HC⁆ ⊆ 𝒮(H₀C')`-kernel linearity. -/
theorem commutator_cSub_H_le_H0 [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    ⁅cSub data chief, data.H⁆ ≤ chief.H0 := by
  haveI := chief.N_normal
  rw [Subgroup.commutator_le]
  intro c hc h hh
  -- `c` is the `G`-image of a kernel element `z ∈ U W₁` (`uActionHom z = 1`).
  simp only [cSub, Subgroup.mem_map] at hc
  obtain ⟨z, ⟨a, ha_ker, ha_z⟩, hz_c⟩ := hc
  have hz1 : quotientMulAutHom chief.N_aInvariant z = 1 := by
    rw [← ha_z]; exact MonoidHom.mem_ker.mp ha_ker
  set hH : ↥data.H := ⟨h, hh⟩ with hhH
  set W : ↥data.H := typeP_conjAction data.typeP z hH * hH⁻¹ with hW
  -- `W ∈ N`: `mk W = (φ_U z)(mk h) · (mk h)⁻¹ = mk h · (mk h)⁻¹ = 1`.
  have hWN : W ∈ chief.N := by
    have hmk : (QuotientGroup.mk' chief.N) W = 1 := by
      rw [hW, map_mul, map_inv,
        ← OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk'
          chief.N_aInvariant z hH, hz1, MulAut.one_apply, mul_inv_cancel]
    have hker := MonoidHom.mem_ker.mpr hmk
    rwa [QuotientGroup.ker_mk'] at hker
  -- `⁅c,h⁆ = (W : G) ∈ H₀`.
  rw [chief.H0_eq]
  refine ⟨W, hWN, ?_⟩
  have hzc : ((z : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) = c := hz_c
  rw [hW, commutatorElement_def, map_mul, map_inv,
    show data.H.subtype (typeP_conjAction data.typeP z hH)
      = ((typeP_conjAction data.typeP z hH : ↥data.H) : G) from rfl,
    typeP_conjAction_apply, hzc]
  simp [hhH]

open scoped commutatorElement in
/-- **`H₀C ◁ M`** (Peterfalvi `Ptype_Fcore_extensions_normal`, the third structural input for the
`H₀C` reducible count, issue 1012): the normal subgroup `H₀ ⊔ C` of `M` realised as
`(H₀ ⊔ C).subgroupOf M ◁ ↥M`.  `M = H ⊔ (U ⊔ W₁)` (`M_complement`, `derivedInG = H ⊔ U`) normalizes
`H₀ ⊔ C` generator-class by generator-class: `M ≤ N(H₀)` (9.4) handles the `H₀` part throughout,
while the `C` part splits — `U W₁ ≤ N(C)` *exactly* (`cSub_normalized_by_uW1`), and `H` normalizes
`H₀C` because `⁅H, C⁆ ≤ H₀` (`commutator_cSub_H_le_H0`) lets `H₀` absorb the `H`-conjugates of `C`. -/
theorem chiefFactor_H0supC_subgroupOf_normal [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ((chief.H0 ⊔ cSub data chief).subgroupOf M).Normal := by
  have hH0CleM : chief.H0 ⊔ cSub data chief ≤ M :=
    (chiefFactor_H0supC_le_derived chief).trans (derivedInG_le_self M)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hH0CleM]
  -- A subgroup that conjugates `K` into itself normalizes `K` (the reverse inclusion is `g⁻¹`).
  have key : ∀ (K Hs : Subgroup G), (∀ g ∈ Hs, ConjAct.toConjAct g • K ≤ K) →
      Hs ≤ Subgroup.normalizer (K : Set G) := by
    intro K Hs hle g hg
    rw [← Subgroup.conjAct_pointwise_smul_iff]
    refine le_antisymm (hle g hg) ?_
    have h1 : ConjAct.toConjAct g • (ConjAct.toConjAct g⁻¹ • K) ≤ ConjAct.toConjAct g • K :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (hle g⁻¹ (inv_mem hg))
    rwa [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul] at h1
  -- `U W₁ ≤ N(H₀ ⊔ C)`: `U W₁ ≤ M ≤ N(H₀)` and `U W₁ ≤ N(C)` (`cSub_normalized_by_uW1`).
  have hUW1 : data.typeP.U ⊔ data.typeP.W1
      ≤ Subgroup.normalizer ((chief.H0 ⊔ cSub data chief : Subgroup G) : Set G) :=
    le_trans (le_inf (le_trans (sup_le (U_le_M data) data.typeP.W1_le) chief.H0_normalized_by_M)
      (cSub_normalized_by_uW1 data chief))
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup chief.H0 (cSub data chief))
  -- `H ≤ N(H₀ ⊔ C)`: `H ≤ N(H₀)` and `h C h⁻¹ ⊆ H₀ C` via `⁅H, C⁆ ≤ H₀`.
  have hH : data.typeP.H ≤ Subgroup.normalizer ((chief.H0 ⊔ cSub data chief : Subgroup G) : Set G) := by
    refine key _ _ (fun h hh => ?_)
    rw [Subgroup.smul_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.conjAct_pointwise_smul_eq_self (chief.H0_normalized_by_M (H_le_M data hh))]
      exact le_sup_left
    · intro x hx
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
      have hc₀ : (ConjAct.toConjAct h)⁻¹ • x ∈ cSub data chief := hx
      have hH0mem : ⁅h, (ConjAct.toConjAct h)⁻¹ • x⁆ ∈ chief.H0 := by
        have hcomm : ⁅h, (ConjAct.toConjAct h)⁻¹ • x⁆ ∈ ⁅data.typeP.H, cSub data chief⁆ :=
          Subgroup.commutator_mem_commutator hh hc₀
        rw [Subgroup.commutator_comm] at hcomm
        exact commutator_cSub_H_le_H0 data chief hcomm
      have hxeq : x = ⁅h, (ConjAct.toConjAct h)⁻¹ • x⁆ * ((ConjAct.toConjAct h)⁻¹ • x) := by
        rw [commutatorElement_def]
        simp only [ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct]
        group
      rw [hxeq]
      exact mul_mem (Subgroup.mem_sup_left hH0mem) (Subgroup.mem_sup_right hc₀)
  -- `M = H ⊔ (U ⊔ W₁)`.
  have hM'eq : derivedInG M = data.typeP.H ⊔ data.typeP.U := by
    rw [data.typeP.derivedInG_eq_fitting_sup_U, data.typeP.H_eq]
  have hMW1 : derivedInG M ⊔ data.typeP.W1 = M := by
    have hmap := congrArg (Subgroup.map M.subtype) data.typeP.M_complement.sup_eq_top
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left (derivedInG_le_self M), inf_of_le_left data.typeP.W1_le,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  have hMeq : M = data.typeP.H ⊔ (data.typeP.U ⊔ data.typeP.W1) := by
    rw [← sup_assoc, ← hM'eq, hMW1]
  exact hMeq.le.trans (sup_le hH hUW1)

end

/-- `derivedInG H = ⁅H, H⁆` (general): the image of `commutator ↥H` under the inclusion is the
commutator subgroup `⁅H,H⁆`. -/
theorem derivedInG_eq_commutator (H : Subgroup G) : derivedInG H = ⁅H, H⁆ := by
  rw [derivedInG, commutator_def, Subgroup.map_commutator]
  simp only [← H.subtype.range_eq_map, Subgroup.range_subtype]

section
open scoped commutatorElement

/-- **Peterfalvi (9.9.a): `H ⊔ C ≤ normalizer(H₀ ⊔ C')`.**  For a generator `x ∈ H ∪ C` and any
`k ∈ K = H₀C'`, `⁅x,k⁆ ∈ K`: by `closure_induction` on `k`, the base cases (`k ∈ H₀` or `k ∈ C'`) use
`⁅H,H₀⁆,⁅C,H₀⁆ ≤ H₀` and `⁅H,C'⁆ ≤ H₀`, `⁅C,C'⁆ ≤ C'`, and the inductive conjugations stay in `K`
since `K` is closed under conjugation by its own elements.  Then `x k x⁻¹ = ⁅x,k⁆·k ∈ K`. -/
theorem HsupC_le_normalizer_K [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    data.H ⊔ cSub data chief
      ≤ Subgroup.normalizer ((chief.H0 ⊔ cprimeSub data chief : Subgroup G) : Set G) := by
  haveI := chief.N_normal
  set K := chief.H0 ⊔ cprimeSub data chief with hKdef
  have hHH : ⁅data.H, data.H⁆ ≤ K :=
    le_trans ((derivedInG_eq_commutator data.H).symm.trans_le (derivedInG_H_le_H0 data chief))
      le_sup_left
  have hCH : ⁅cSub data chief, data.H⁆ ≤ K :=
    le_trans (commutator_cSub_H_le_H0 data chief) le_sup_left
  have hHC' : ⁅data.H, cSub data chief⁆ ≤ K := by rw [Subgroup.commutator_comm]; exact hCH
  have hCC : ⁅cSub data chief, cSub data chief⁆ ≤ K :=
    le_trans (derivedInG_eq_commutator (cSub data chief)).symm.le le_sup_right
  have hKclosure : K = Subgroup.closure (↑chief.H0 ∪ ↑(cprimeSub data chief) : Set G) := by
    rw [hKdef, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  -- For a generator `x ∈ H ∪ C` and any `k ∈ K`, `⁅x, k⁆ ∈ K`.
  have hcomm : ∀ x : G, (x ∈ data.H ∨ x ∈ cSub data chief) → ∀ k ∈ K, ⁅x, k⁆ ∈ K := by
    intro x hx k hk
    rw [hKclosure] at hk
    induction hk using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy0 | hyc'
      · rcases hx with hxH | hxC
        · exact hHH (Subgroup.commutator_mem_commutator hxH (chief.H0_lt_H.le hy0))
        · exact hCH (Subgroup.commutator_mem_commutator hxC (chief.H0_lt_H.le hy0))
      · rcases hx with hxH | hxC
        · exact hHC' (Subgroup.commutator_mem_commutator hxH (cprimeSub_le_C data chief hyc'))
        · exact hCC (Subgroup.commutator_mem_commutator hxC (cprimeSub_le_C data chief hyc'))
    | one => simpa using K.one_mem
    | mul a b ha hb iha ihb =>
      have haK : a ∈ K := by rw [hKclosure]; exact ha
      rw [show ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) by
        rw [commutatorElement_def, commutatorElement_def]; group]
      exact mul_mem iha (mul_mem (mul_mem haK ihb) (K.inv_mem haK))
    | inv a ha iha =>
      have haK : a ∈ K := by rw [hKclosure]; exact ha
      rw [show ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a by
        rw [commutatorElement_def, commutatorElement_def]; group]
      exact mul_mem (mul_mem (K.inv_mem haK) (K.inv_mem iha)) haK
  -- conclude normalizer membership for generators, then `sup_le`.
  have hnorm : ∀ x : G, (x ∈ data.H ∨ x ∈ cSub data chief) → x ∈ Subgroup.normalizer K := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · rw [show x * n * x⁻¹ = ⁅x, n⁆ * n by rw [commutatorElement_def]; group]
      exact mul_mem (hcomm x hx n hn) hn
    · have hxinv : x⁻¹ ∈ data.H ∨ x⁻¹ ∈ cSub data chief := by
        rcases hx with h | h
        · exact Or.inl (data.H.inv_mem h)
        · exact Or.inr ((cSub data chief).inv_mem h)
      have hkey := mul_mem (hcomm x⁻¹ hxinv _ hn) hn
      rw [show ⁅x⁻¹, x * n * x⁻¹⁆ * (x * n * x⁻¹) = n by
        rw [commutatorElement_def]; group] at hkey
      exact hkey
  exact sup_le (fun x hx => hnorm x (Or.inl hx)) (fun x hx => hnorm x (Or.inr hx))

/-- **Peterfalvi (9.9.a) commutator step**: `⁅HC, HC⁆ ≤ H₀C'`.  `K = H₀C'` is normal in `HC`
(`HsupC_le_normalizer_K`), and in the quotient `HC/K` the images of `H` and `C` commute and are
abelian (the four sub-commutators `⁅H,H⁆,⁅H,C⁆,⁅C,H⁆,⁅C,C⁆ ≤ K`), so `HC/K` is abelian, i.e.
`⁅HC,HC⁆ ≤ K`.  This is the kernel containment making the (9.9.a) `S(H₀C')`-constituents linear. -/
theorem commutator_HsupC_le_H0Cprime [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    ⁅data.H ⊔ cSub data chief, data.H ⊔ cSub data chief⁆
      ≤ chief.H0 ⊔ cprimeSub data chief := by
  haveI := chief.N_normal
  set HC := data.H ⊔ cSub data chief with hHCdef
  set K := chief.H0 ⊔ cprimeSub data chief with hKdef
  have hHH : ⁅data.H, data.H⁆ ≤ K :=
    le_trans ((derivedInG_eq_commutator data.H).symm.trans_le (derivedInG_H_le_H0 data chief))
      le_sup_left
  have hCH : ⁅cSub data chief, data.H⁆ ≤ K :=
    le_trans (commutator_cSub_H_le_H0 data chief) le_sup_left
  have hHC' : ⁅data.H, cSub data chief⁆ ≤ K := by rw [Subgroup.commutator_comm]; exact hCH
  have hCC : ⁅cSub data chief, cSub data chief⁆ ≤ K :=
    le_trans (derivedInG_eq_commutator (cSub data chief)).symm.le le_sup_right
  have hKle : K ≤ HC :=
    sup_le (le_trans chief.H0_lt_H.le le_sup_left)
      (le_trans (cprimeSub_le_C data chief) le_sup_right)
  haveI hK'normal : (K.subgroupOf HC).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mpr (HsupC_le_normalizer_K data chief)
  -- `commutator ↥HC ≤ K.subgroupOf HC` via the quotient `HC/K` being abelian.
  have hcomm : commutator ↥HC ≤ K.subgroupOf HC := by
    have hmk_surj := QuotientGroup.mk'_surjective (K.subgroupOf HC)
    set mk := QuotientGroup.mk' (K.subgroupOf HC) with hmk
    have hsub : ∀ P Q : Subgroup G, ⁅P, Q⁆ ≤ K →
        ⁅(P.subgroupOf HC).map mk, (Q.subgroupOf HC).map mk⁆ = ⊥ := by
      intro P Q hPQ
      rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, hmk, QuotientGroup.ker_mk',
        Subgroup.commutator_le]
      intro x hx y hy
      rw [Subgroup.mem_subgroupOf] at hx hy ⊢
      have hxy : ((⁅x, y⁆ : ↥HC) : G) = ⁅((x : ↥HC) : G), ((y : ↥HC) : G)⁆ := by
        simp [commutatorElement_def]
      rw [hxy]
      exact hPQ (Subgroup.commutator_mem_commutator hx hy)
    rw [← QuotientGroup.ker_mk' (K.subgroupOf HC), ← Subgroup.map_eq_bot_iff, commutator_def,
      Subgroup.map_commutator, Subgroup.map_top_of_surjective mk hmk_surj]
    have hAB : (data.H.subgroupOf HC).map mk ⊔ ((cSub data chief).subgroupOf HC).map mk = ⊤ := by
      rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
        show (data.H ⊔ cSub data chief).subgroupOf HC = ⊤ from Subgroup.subgroupOf_self HC,
        Subgroup.map_top_of_surjective mk hmk_surj]
    rw [← hAB, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.centralizer_sup]
    refine sup_le (le_inf ?_ ?_) (le_inf ?_ ?_)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hsub data.H data.H hHH)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hsub data.H (cSub data chief) hHC')
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hsub (cSub data chief) data.H hCH)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (hsub (cSub data chief) (cSub data chief) hCC)
  -- `⁅HC,HC⁆ = (commutator ↥HC).map subtype ≤ K ⊓ HC ≤ K`.
  calc ⁅data.H ⊔ cSub data chief, data.H ⊔ cSub data chief⁆
      = (commutator ↥HC).map HC.subtype := by rw [← derivedInG_eq_commutator]; rfl
    _ ≤ (K.subgroupOf HC).map HC.subtype := Subgroup.map_mono hcomm
    _ ≤ K := by rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left

/-- **(9.9.a) realized commutator bound**: `⁅HC, HC⁆ ⊆ 𝒮(H₀C')`-kernel, i.e. the realized commutator
`⁅hInHu ⊔ cInHu, hInHu ⊔ cInHu⁆` lands in the realized `H₀C'` inside `↥HU`.  Transport of
`commutator_HsupC_le_H0Cprime` along the inclusion `↥HU ↪ ↥M ↪ G` (`map_le_iff_le_comap`). -/
theorem commutator_hcInHu_le_realized [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    ⁅hInHu data ⊔ cInHu data chief, hInHu data ⊔ cInHu data chief⁆
      ≤ ((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) := by
  have hreal : ((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf (huSub data)
      = (chief.H0 ⊔ cprimeSub data chief).comap (M.subtype.comp (huSub data).subtype) := rfl
  have hmaple : (hInHu data ⊔ cInHu data chief).map (M.subtype.comp (huSub data).subtype)
      ≤ data.H ⊔ cSub data chief := by
    rw [Subgroup.map_sup]
    refine sup_le (le_trans ?_ le_sup_left) (le_trans ?_ le_sup_right)
    · have hh : hInHu data = data.H.comap (M.subtype.comp (huSub data).subtype) := by
        rw [hInHu, Subgroup.subgroupOf, Subgroup.subgroupOf, Subgroup.comap_comap]
      rw [hh]; exact Subgroup.map_comap_le _ _
    · have hc : cInHu data chief = (cSub data chief).comap (M.subtype.comp (huSub data).subtype) := by
        rw [cInHu, Subgroup.subgroupOf, Subgroup.subgroupOf, Subgroup.comap_comap]
      rw [hc]; exact Subgroup.map_comap_le _ _
  rw [hreal, ← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator]
  exact le_trans (Subgroup.commutator_mono hmaple hmaple) (commutator_HsupC_le_H0Cprime data chief)

end

/-- **(9.9.a) index step (C): `[U:C] = u`** realized form `(cInHu.subgroupOf uInHu).index = u`.
First isomorphism `U/C ≃ Ū` (the `U`-action image on the chief factor), with `u = |Ū|`. -/
theorem index_cInHu_subgroupOf_uInHu_eq_u [Finite G] {M : Subgroup G}
    (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data)
    (chars : Section11CharacterData data chief) :
    ((cInHu data chief).subgroupOf (uInHu data)).index = chars.u := by
  -- (I): `|C| · [U:C] = |U|`.
  have hI : Nat.card ↥(cSub data chief) * ((cInHu data chief).subgroupOf (uInHu data)).index
      = Nat.card ↥data.U := by
    have h := Subgroup.card_mul_index ((cInHu data chief).subgroupOf (uInHu data))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cInHu_le_uInHu data chief)).toEquiv,
      card_cInHu_eq data chief, card_uInHu_eq data] at h
    exact h
  -- (II): `|U| = u · |C|` (first iso for the `U`-action hom).
  have hu : chars.u = Nat.card ↥(uActionHom data chief).range := chars.u_eq_card_quotient
  have hII : Nat.card ↥data.U = chars.u * Nat.card ↥(cSub data chief) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (uActionHom data chief).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (uActionHom data chief)).toEquiv,
      ← card_cSub_eq_card_ker data chief, ← hu,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1)).toEquiv] at h
    exact h
  have hcancel : Nat.card ↥(cSub data chief)
      * ((cInHu data chief).subgroupOf (uInHu data)).index
      = Nat.card ↥(cSub data chief) * chars.u := by rw [hI, hII, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcancel

/-- **Constituent kernel inheritance (lies-over form).**  If `χ ∈ Irr Γ` lies over `θ ∈ Irr K`
for a subgroup `K ≤ Γ`, then every element of `K` lying in the character kernel of `χ` also lies in
the character kernel of `θ`: each constituent of `Res^Γ_K χ` inherits `χ`'s kernel containments.

This is the input that makes the (9.9.a) constituent `θ` of `Res^{HU}_H χ` trivial on the
chief-factor kernel `N` (since `H₀ ⊆ ker χ`), so `θ` is an inflation of an `H̄`-character. -/
theorem liesOver_mem_characterKernel {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {K : Subgroup Γ} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    {χ : IrreducibleCharacter Γ} {θ : IrreducibleCharacter ↥K}
    (hlo : IrreducibleCharacter.LiesOver K χ θ) {g : ↥K}
    (hg : ((g : Γ)) ∈ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction Γ ℂ)) :
    g ∈ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ) := by
  refine OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
    (ψ := ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
    (OddOrder.Peterfalvi.S08.isCharacter_restrict χ.isIrreducible.isCharacter K)
    θ.isIrreducible ?_ ?_
  · rw [IrreducibleCharacter.LiesOver, ClassFunction.restrictionMultiplicity_def] at hlo
    exact hlo
  · rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
      ClassFunction.restrict_apply]
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hg
    have h1 : ClassFunction.restrict K (χ : ClassFunction Γ ℂ) 1
        = (χ : ClassFunction Γ ℂ) 1 := by
      rw [ClassFunction.restrict_apply]; rfl
    rw [h1]; exact hg

/-- **Peterfalvi (9.9.a), the chief-factor constituent of `χ ∈ 𝒳(H₀)`.**

In Clifford case (b) (`U` acts irreducibly on `H̄ = H/H_0`), any `χ ∈ Irr(HU)` with `H ⊄ Ker χ`
(`χ ∈ 𝒳`) and `H_0 ⊆ Ker χ` lies over a chief-factor constituent `θ₀ ∈ Irr(H)`, realised in
inflation form `θ₀ = compHom (H̄ ≃ ·) (compHom (mk' N) θ̄)` for a nontrivial `θ̄ ∈ Irr(H̄)`.  Its
inertia group in `HU` is `HC` (`inertia_eq_hcInHu`, the case-(b) crux) and it is linear
(`θ₀(1) = 1`, `H̄` elementary abelian).  This is the shared extraction behind the (9.9.a) degree
statements `caseB_degree_qu` (`χ(1) = u` on `𝒳(H₀C')`) and `caseB_xi_H0_degree_dvd_u`
(`u ∣ χ(1)` on the larger `𝒳(H₀)`). -/
theorem caseB_exists_chiefFactorConstituent [Finite G]
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    {χ : IrreducibleCharacter ↥(huSub data)}
    (hχX : χ ∈ xiSet data)
    (hχH0 : ((chief.H0.subgroupOf M).subgroupOf (huSub data) : Set ↥(huSub data)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ)) :
    ∃ θ₀ : IrreducibleCharacter ↥(hInHu data),
      IrreducibleCharacter.LiesOver (hInHu data) χ θ₀ ∧
      IrreducibleCharacter.inertia (G := ↥(huSub data)) (H := hInHu data) θ₀
        = hInHu data ⊔ cInHu data chief ∧
      (θ₀ : ClassFunction ↥(hInHu data) ℂ) (1 : ↥(hInHu data)) = 1 := by
  classical
  haveI : Fintype ↥(huSub data) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype (IrreducibleCharacter ↥(hInHu data)) := Fintype.ofFinite _
  -- A nontrivial constituent `θ` of `Res^{HU}_H χ` (`H ⊄ Ker χ`).
  obtain ⟨θ, hθlo, hθnt⟩ :=
    OddOrder.RepresentationTheory.exists_constituent_not_subset_characterKernel
      (A := hInHu data) (B := hInHu data) le_rfl χ hχX
  -- The descent hom `f = (mk' N) ∘ hInHuEquivH : ↥(hInHu) → H̄ = ↥H ⧸ N`.
  set f : ↥(hInHu data) →* (↥data.H ⧸ chief.N) :=
    (QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom with hf
  have hfsurj : Function.Surjective f :=
    (QuotientGroup.mk'_surjective chief.N).comp (hInHuEquivH data).surjective
  -- `f.ker ⊆ ker θ`: `f x = 1` puts the `G`-coordinate of `x` in `H₀ ⊆ ker χ`.
  have hfker : (f.ker : Set ↥(hInHu data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥(hInHu data) ℂ) := by
    intro x hx
    have hxN : (hInHuEquivH data) x ∈ chief.N := by
      have hx1 : f x = 1 := hx
      rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx1
      exact hx1
    have hxH0 : (((x : ↥(huSub data)) : ↥M) : G) ∈ chief.H0 := by
      rw [chief.H0_eq, ← hInHuEquivH_coe data x]
      exact Subgroup.mem_map_of_mem data.H.subtype hxN
    have hxχ : (x : ↥(huSub data)) ∈
        OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ) := by
      apply hχH0
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hxH0
    exact liesOver_mem_characterKernel hθlo hxχ
  -- `θ` is an inflation: `θ = compHom f θbar` for some `θbar ∈ Irr(H̄)`.
  obtain ⟨θbar, hθbar⟩ :=
    OddOrder.RepresentationTheory.exists_compHom_eq_of_subset_characterKernel hfsurj θ hfker
  have hθeq : (θ : ClassFunction ↥(hInHu data) ℂ)
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) := by
    rw [← hθbar, hf, ClassFunction.compHom_comp]
  have hθbarnt : (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      ≠ trivialClassFunction _ := by
    intro h0
    apply hθnt
    rw [Subgroup.subgroupOf_self]
    intro y _
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
      hθeq, h0]
    simp [ClassFunction.compHom_apply, trivialClassFunction]
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) :=
    ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  refine ⟨θ, hθlo, ?_, ?_⟩
  · show ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
      (θ : ClassFunction ↥(hInHu data) ℂ) = hInHu data ⊔ cInHu data chief
    rw [hθeq]
    exact inertia_eq_hcInHu data chief caseB.actsIrreducibly hθbarnt
  · rw [hθeq]
    simp only [ClassFunction.compHom_apply, map_one]
    exact θbar.isIrreducible.apply_one_eq_one_of_isMulCommutative

/-- **Peterfalvi (9.9.a)**: every member of `𝒮(H₀C')` has degree `qu`.

For `φ = Ind_{HU}^M χ ∈ 𝒮(H₀C')` (so `χ ∈ 𝒳(H₀C')`, i.e. `χ ∈ Irr(HU)` with `H ⊄ Ker χ` and
`H₀C' ⊆ Ker χ`), `φ(1) = [M:HU]·χ(1) = q·χ(1)` (`induceHU_apply_one_eq_q_mul`), so it suffices to
show `χ(1) = u`.  That is the Clifford degree `χ(1) = [HU:HC]` via
`apply_one_eq_index_of_liesOver_linear_inertia`: `χ` lies over a nontrivial chief-factor character
`θ₀` (inflation of `θbar ∈ Irr(H̄)`, linear since `H̄` is abelian) whose inertia in `HU` is `HC`
(`inertia_eq_hcInHu`, case (b)), and over a linear `ψ ∈ Irr(HC)` (`[HC,HC] ⊆ Ker χ ⟹ ψ(1)=1`); the
degree sandwich forces `χ(1) = [HU:HC] = u`. -/
theorem caseB_degree_qu [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars) :
    ∀ φ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime), φ 1 = ((data.q * chars.u : ℕ) : ℂ) := by
  classical
  haveI : Fintype ↥(huSub data) := Fintype.ofFinite _
  haveI : Fintype ↥(hInHu data) := Fintype.ofFinite _
  haveI : Fintype ↥(hInHu data ⊔ cInHu data chief) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Invertible (Nat.card ↥(hInHu data ⊔ cInHu data chief) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro φ hφ
  rw [Section11CharacterData.SOf_eq, mem_sOf] at hφ
  obtain ⟨χ, hχ, rfl⟩ := hφ
  rw [induceHU_apply_one_eq_q_mul]
  -- Reduce `q·χ(1) = qu` to `χ(1) = u`.
  suffices hχu : (χ : ClassFunction ↥(huSub data) ℂ) (1 : ↥(huSub data)) = (chars.u : ℂ) by
    rw [hχu]; push_cast; ring
  -- Obligation 1: the chief-factor constituent `θ₀` (case-(b) crux, shared helper).  `χ ∈ 𝒳(H₀C')`
  -- supplies `χ ∈ 𝒳` (`hχ.1`) and, via `H₀ ≤ H₀C'`, the `H₀ ⊆ Ker χ` the helper needs.
  obtain ⟨θ₀, hθ₀over, hθ₀inertia, hθ₀deg⟩ :=
    caseB_exists_chiefFactorConstituent chars caseB hχ.1
      (subset_trans (SetLike.coe_subset_coe.mpr
        (Subgroup.subgroupOf_mono (huSub data) (Subgroup.subgroupOf_mono M le_sup_left))) hχ.2)
  -- Obligation 3: a constituent `ψ ∈ Irr(HC)` that `χ` lies over, linear.
  obtain ⟨ψ, hψover⟩ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.exists_liesOver
      (H := hInHu data ⊔ cInHu data chief) χ
  have hψdeg : (ψ : ClassFunction ↥(hInHu data ⊔ cInHu data chief) ℂ)
      (1 : ↥(hInHu data ⊔ cInHu data chief)) = 1 := by
    -- `ψ` is linear: `⁅HC,HC⁆ ⊆ ker χ`, so the constituent `ψ` factors through the abelian
    -- `HC/⁅HC,HC⁆`.
    haveI : IsMulCommutative (↥(hInHu data ⊔ cInHu data chief) ⧸
        commutator ↥(hInHu data ⊔ cInHu data chief)) :=
      inferInstanceAs (IsMulCommutative (Abelianization ↥(hInHu data ⊔ cInHu data chief)))
    refine OddOrder.RepresentationTheory.apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
      (N := commutator ↥(hInHu data ⊔ cInHu data chief)) ψ ?_
    intro g hg
    refine liesOver_mem_characterKernel hψover ?_
    refine hχ.2 ?_
    have hgmem : (g : ↥(huSub data))
        ∈ ⁅hInHu data ⊔ cInHu data chief, hInHu data ⊔ cInHu data chief⁆ := by
      rw [← derivedInG_eq_commutator]
      exact Subgroup.mem_map_of_mem _ hg
    exact commutator_hcInHu_le_realized data chief hgmem
  -- Clifford degree: `χ(1) = [HU:HC]`.
  have key := OddOrder.RepresentationTheory.apply_one_eq_index_of_liesOver_linear_inertia
    (H := hInHu data) (I := hInHu data ⊔ cInHu data chief)
    χ θ₀ ψ hθ₀over hθ₀inertia hθ₀deg hψover hψdeg
  -- Obligation 4: `[HU:HC] = u` = `[U:C]` (second iso (A) + first iso (C)).
  have hidx : (hInHu data ⊔ cInHu data chief).index = chars.u :=
    (index_hcInHu_eq_relindex_cInHu data chief).trans
      (index_cInHu_subgroupOf_uInHu_eq_u data chief chars)
  rw [key, hidx]

/-- **Peterfalvi (9.9.a), first sentence**: in Clifford case (b), every `χ ∈ 𝒳(H₀)` has degree
divisible by `u = |U:C|`.

`χ` lies over a chief-factor constituent `θ₀` whose inertia in `HU` is `HC`
(`caseB_exists_chiefFactorConstituent`), so the Clifford degree formula
`χ(1) = ⟨Res χ, θ₀⟩ · [HU:HC] · θ₀(1)`
(`apply_one_eq_restrictionMultiplicity_mul_index_inertia`) with `[HU:HC] = u` (`index_hcInHu_…`)
and the restriction multiplicity / `θ₀(1)` being natural numbers gives `u ∣ χ(1)`.  (On the smaller
`𝒳(H₀C')` this sharpens to `χ(1) = u`, `caseB_degree_qu`.)  Phrased on the natural-degree witness
`d` of `χ(1)`; this is the degree datum behind (9.9.b)'s `μ_j(1) = qu`. -/
theorem caseB_xi_H0_degree_dvd_u [Finite G]
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars) :
    ∀ χ ∈ chars.XOf chief.H0, ∀ d : ℕ,
      (χ : ClassFunction ↥(huSub data) ℂ) (1 : ↥(huSub data)) = (d : ℂ) → chars.u ∣ d := by
  classical
  haveI : Fintype ↥(huSub data) := Fintype.ofFinite _
  haveI : Fintype ↥(hInHu data) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype (IrreducibleCharacter ↥(hInHu data)) := Fintype.ofFinite _
  intro χ hχ d hd
  rw [Section11CharacterData.XOf_eq] at hχ
  obtain ⟨hχX, hχH0⟩ := hχ
  -- The chief-factor constituent `θ₀` (inertia `HC`).
  obtain ⟨θ₀, hθ₀over, hθ₀inertia, -⟩ :=
    caseB_exists_chiefFactorConstituent chars caseB hχX hχH0
  -- Clifford degree formula `χ(1) = e · [HU:HC] · θ₀(1)`, with `[HU:HC] = u`.
  have key := OddOrder.RepresentationTheory.apply_one_eq_restrictionMultiplicity_mul_index_inertia
    (H := hInHu data) χ θ₀ hθ₀over
  rw [hθ₀inertia] at key
  have hidx : (hInHu data ⊔ cInHu data chief).index = chars.u :=
    (index_hcInHu_eq_relindex_cInHu data chief).trans
      (index_cInHu_subgroupOf_uInHu_eq_u data chief chars)
  rw [hidx] at key
  -- The restriction multiplicity and `θ₀(1)` are natural numbers.
  obtain ⟨e, he⟩ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.restrictionMultiplicity_natCast
      (H := hInHu data) χ θ₀
  obtain ⟨d₀, -, hd₀, -⟩ := θ₀.isIrreducible.exists_natDegree_charValue_one_dvd_card
  rw [he, hd₀, hd] at key
  -- `(d : ℂ) = (e · u · d₀ : ℕ)`, so `d = e·u·d₀` and `u ∣ d`.
  have hdeq : d = e * chars.u * d₀ := by
    have hcast : (d : ℂ) = ((e * chars.u * d₀ : ℕ) : ℂ) := by push_cast; linear_combination key
    exact_mod_cast hcast
  exact ⟨e * d₀, by rw [hdeq]; ring⟩

/-- **Peterfalvi (9.9.b), degree part**: every member of `𝒮(H₀C)` has degree `qu`.

Immediate from `caseB_degree_qu` (degree `qu` on `𝒮(H₀C')`): since `C' = ⁅C,C⁆ ≤ C`
(`Cprime_le_C`), we have `H₀C' ≤ H₀C`, so `𝒮(H₀C) ⊆ 𝒮(H₀C')` (`sOf_antitone` — a larger kernel
demand selects fewer characters).  Thus the (9.9.b) degree claim (each reducible member of `𝒮(H₀)`
has degree `qu`) reduces to its membership claim (the reducibles lie in `𝒮(H₀C)`): once a reducible
`φ ∈ 𝒮(H₀)` is shown to lie in `𝒮(H₀C)`, this lemma gives its degree.  The membership itself is the
deep Clifford crux — reducible `Ind_{HU}^M χ` ⟺ `χ` is `W₁`/`M`-invariant, and via the direct
product `HC/H₀ = H̄ × (C/H₀)` the underlying `HC`-linear character is `C`-trivial (Peterfalvi
(9.9.b)/(9.8.b) shared subproof, Coq `PFsection9` `Part_a`). -/
theorem forall_mem_sOf_H0C_apply_one_eq_qu [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars) :
    ∀ φ ∈ chars.SOf (chief.H0 ⊔ chars.C), φ 1 = ((data.q * chars.u : ℕ) : ℂ) := by
  intro φ hφ
  refine caseB_degree_qu hG chars caseB φ ?_
  rw [Section11CharacterData.SOf_eq] at hφ ⊢
  exact sOf_antitone data (sup_le_sup_left chars.Cprime_le_C chief.H0) hφ

/-- **Peterfalvi (9.9.b), the `H₀C` reducible count** — parallel to `reducible_count_sOf_H0`.

`𝒮(H₀C)` contains exactly `p − 1` reducible characters.  The same §9↔§6 bijection as
`reducible_count_sOf_H0`, but with the `M/(H₀C)`-certain-type hypothesis: Peterfalvi (8.4.d) holds
for `L = M/(H₀C)` as well as `L = M/H₀`, and `W̄₂' = W₂`-image in `M/(H₀C)` still has order `p`
(`W₂ ∩ H₀C = W₂ ∩ H₀`, since `W₂ ≤ H` and `C ≤ U` meet `H` trivially).  Closing this is the
remaining work — a parallel of the `chiefFactorQuotientHypothesis` + bijection construction with the
normal subgroup `H₀ ⊔ C` in place of `H₀` (issue 1012). -/
theorem reducible_count_sOf_H0C [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) :
    {φ ∈ sOf data (chief.H0 ⊔ chars.C) | ¬ IsIrreducibleCharacter φ}.ncard = chief.p - 1 := by
  haveI := chiefFactor_H0_subgroupOf_normal chief
  haveI := chiefFactor_H0supC_subgroupOf_normal chief
  rw [show chars.C = cSub data chief from rfl]
  exact reducible_count_sOf_K hG chief (chief.H0 ⊔ cSub data chief)
    (Subgroup.comap_mono (chiefFactor_H0supC_le_derived chief))
    (chiefFactor_W1_inf_H0supC_subgroupOf_eq_bot chief)
    (chiefFactor_W2_not_le_H0supC chief)
    (chiefFactor_card_W2bar_H0supC chief)

/-- **Peterfalvi (9.9.b), membership**: every reducible member of `𝒮(H₀)` lies in `𝒮(H₀C)`.

A clean **cardinality** argument that avoids the full §9 character construction: `𝒮(H₀C) ⊆ 𝒮(H₀)`
(`sOf_antitone`, `H₀ ≤ H₀C`), so the reducibles of `𝒮(H₀C)` are a subset of those of `𝒮(H₀)`; both
number `p − 1` (`reducible_count_sOf_H0C` / `reducible_count_sOf_H0`).  A subset of equal finite
cardinality is the whole set (`Set.eq_of_subset_of_ncard_le`, finiteness from `p − 1 ≠ 0` as `p` is
prime).  Hence every reducible `𝒮(H₀)`-member already lies in `𝒮(H₀C)`.  Together with
`forall_mem_sOf_H0C_apply_one_eq_qu` (degree), this is the full (9.9.b) degree+membership conjunct. -/
theorem reducible_mem_sOf_H0C [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) :
    ∀ φ ∈ sOf data chief.H0, ¬ IsIrreducibleCharacter φ →
      φ ∈ sOf data (chief.H0 ⊔ chars.C) := by
  intro φ hφ hred
  have hBA : {ψ ∈ sOf data (chief.H0 ⊔ chars.C) | ¬ IsIrreducibleCharacter ψ}
      ⊆ {ψ ∈ sOf data chief.H0 | ¬ IsIrreducibleCharacter ψ} := by
    rintro ψ ⟨hψS, hψr⟩
    exact ⟨sOf_antitone data le_sup_left hψS, hψr⟩
  have hAfin : {ψ ∈ sOf data chief.H0 | ¬ IsIrreducibleCharacter ψ}.Finite :=
    Set.finite_of_ncard_ne_zero (by
      rw [reducible_count_sOf_H0 hG chief]
      exact Nat.sub_ne_zero_of_lt chief.p_prime.one_lt)
  have hAB : {ψ ∈ sOf data (chief.H0 ⊔ chars.C) | ¬ IsIrreducibleCharacter ψ}
      = {ψ ∈ sOf data chief.H0 | ¬ IsIrreducibleCharacter ψ} :=
    Set.eq_of_subset_of_ncard_le hBA
      (le_of_eq (by rw [reducible_count_sOf_H0 hG chief, reducible_count_sOf_H0C hG chars]))
      hAfin
  have hφmem : φ ∈ {ψ ∈ sOf data (chief.H0 ⊔ chars.C) | ¬ IsIrreducibleCharacter ψ} := by
    rw [hAB]; exact ⟨hφ, hred⟩
  exact hφmem.1

/-- **Peterfalvi (9.9)**: character-count consequences in Clifford case (b).

Faithful to Peterfalvi (9.9.a,b,c) (count-statement audit, issue 2030):
* **(a)** every member of `𝒮(H₀C')` has degree `qu` (each `χ ∈ 𝒳(H₀C')` has `χ(1)=u`, so its
  induction `Ind_{HU}^M χ` has degree `[M:HU]·u = qu`).
* **(b)** `𝒮(H₀)` contains exactly `p-1` reducible characters; each has degree `qu` and lies in
  `𝒮(H₀C)`.
* **(c)** if `𝒮(H₀C')` contains *no irreducible character*, then `C = 1` and `u = (p^q-1)/(p-1)`.

`𝒮(H₀C')`/`𝒮(H₀C)` carry the `H₀`-join (`chief.H0 ⊔ chars.Cprime` / `chief.H0 ⊔ chars.C`).  The
former vacuous `u ∣ qu` (always true) and the false `(𝒮(H₀)).ncard = p-1` (`𝒮(H₀)` also has
irreducibles) are replaced by the genuine (9.9.a)/(9.9.b) statements; the (9.9.c) trigger is
"contains no irreducible" (not `ncard = 0`: in the exceptional case `𝒮(H₀C') = 𝒮(H₀)` is
nonempty). -/
theorem caseB_character_counts [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars) :
    (∀ φ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime), φ 1 = ((data.q * chars.u : ℕ) : ℂ)) ∧
      {φ ∈ chars.SOf chief.H0 | ¬ IsIrreducibleCharacter φ}.ncard = chief.p - 1 ∧
      (∀ φ ∈ chars.SOf chief.H0, ¬ IsIrreducibleCharacter φ →
        φ 1 = ((data.q * chars.u : ℕ) : ℂ) ∧ φ ∈ chars.SOf (chief.H0 ⊔ chars.C)) ∧
      ((¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime), IsIrreducibleCharacter χ) →
        chars.C = ⊥ ∧ chars.u = (chief.p ^ data.q - 1) / (chief.p - 1)) := by
  -- (9.9.a) is the proven `caseB_degree_qu`; (9.9.b) is the §9↔§6 bijection `reducible_count_sOf_H0`;
  -- (9.9.b) degree/membership and (9.9.c) exceptional remain.
  refine ⟨caseB_degree_qu hG chars caseB, ?_, ?_, ?_⟩
  · exact reducible_count_sOf_H0 hG chief
  · intro φ hφ hred
    have hmem := reducible_mem_sOf_H0C hG chars φ hφ hred
    exact ⟨forall_mem_sOf_H0C_apply_one_eq_qu hG chars caseB φ hmem, hmem⟩
  · sorry

/-- **Peterfalvi (9.10)**: in the exceptional case where `𝒮(H₀C')` contains no irreducible
character of degree `qu`, the quotient semidirect product is Frobenius; in type II the full `H U`
subgroup is Frobenius with kernel `H`, and `u = (p^q-1)/(p-1)`.

The trigger set is `𝒮(H₀C')` (`chief.H0 ⊔ chars.Cprime`) — the `H₀C'` join, not `C` alone
(count-statement audit, issue 2030); the missing character is required *irreducible* of degree `qu`
(matching the negation of the (9.8.c)/(9.9) existence). -/
theorem exceptional_case_frobenius_realization [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars)
    (hno : ¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime),
        IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * chars.u : ℕ) : ℂ)) :
    chars.quotientSemidirectFrobenius ∧
      chars.u = (chief.p ^ data.q - 1) / (chief.p - 1) ∧
      (IsTypeII M →
        OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(data.H ⊔ data.U)
          (data.H.subgroupOf (data.H ⊔ data.U))
          (data.U.subgroupOf (data.H ⊔ data.U))) := by
  sorry

/-! ## (9.11): coherence for `S(H_0 C')` -/

/-- **Structural input for Peterfalvi (9.11) — §14-gated.**

The set `S(H_0 C')` of the type II/III/IV analysis carries the Sibley Dade setup of (6.8)
realizing `chars.tau / chars.S / chars.H0CprimeSupport` (a `SibleyTarget`).  Exhibiting this
witness is the maximal-subgroup structure obligation; once it lands, and once lane B supplies
the (6.8) proof body of `S08.sibleySetup_is_coherent`, `coherent_H0C_commutator` is
unconditional. -/
noncomputable def sibleyTarget_H0C [Fintype G]
    {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) :
    CoherenceWiring.SibleyTarget chars.tau chars.S chars.H0CprimeSupport := sorry

/-- **Peterfalvi (9.11)**: the set `S(H_0 C')` is coherent for the Dade map `τ`.

Wired to the (6.8) capstone `S08.sibleySetup_is_coherent` through the coherence-wiring bridge:
given the §14 structural witness `sibleyTarget_H0C`, coherence is exactly (6.8).  The eight
internal steps (9.11.1)--(9.11.8) of Peterfalvi's proof are subsumed by the (6.8) reduction;
this `def` carries no `sorry` of its own (its gaps are `sibleyTarget_H0C` and (6.8)). -/
noncomputable def coherent_H0C_commutator [Fintype G]
    {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) :
    OddOrder.Peterfalvi.S07.IsCoherent chars.tau chars.S chars.H0CprimeSupport :=
  CoherenceWiring.cohereOfSibleyTarget (sibleyTarget_H0C chars)

end OddOrder.Peterfalvi.S11

