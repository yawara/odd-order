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

/-- **Peterfalvi (9.9.a), abstract inertia reduction.**  In Clifford case (b), if the inflation
`compHom (mk' N) θ̄` of a nontrivial irreducible `θ̄ ∈ Irr(H̄)` is invariant under the conjugation
action `typeP_conjAction (g : U)` (i.e. `g` lies in the inertia of the inflated character, once
it is realized inside `HU`), then `g` acts trivially on the chief factor: `φ_U(g) = 1`
(`g ∈ C`).

Proof: `compHom_typeP_conjAction_inflation` rewrites the invariance to
`compHom (mk' N) (φ_U(g)·θ̄) = compHom (mk' N) θ̄`; inflation is injective
(`compHom_injective_of_surjective`, `mk' N` surjective), so `θ̄` is `φ_U(g)`-invariant, and
`chiefFactor_caseB_char_inertia` gives `φ_U(g) = 1`.  This reduces the character-side inertia
`I_U(θ) ⊆ C` of (9.9.a) to the single remaining step of producing the
`typeP_conjAction`-invariance from the concrete `HU`-conjugation inertia (the `conjBy`-realization
of `H̄`). -/
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
        chief.N_aInvariant).U.subtype) g = 1 := by
  rw [compHom_typeP_conjAction_inflation] at hfix
  have hfix2 := ClassFunction.compHom_injective_of_surjective
    (QuotientGroup.mk'_surjective chief.N) hfix
  apply chiefFactor_caseB_char_inertia hcaseB hθbar g
  intro x
  rw [show ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) g
      = quotientMulAutHom chief.N_aInvariant
          ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype g) from rfl]
  exact congrFun (congrArg (fun f : ClassFunction (↥data.H ⧸ chief.N) ℂ =>
    (f : (↥data.H ⧸ chief.N) → ℂ)) hfix2) x

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

/-- **Peterfalvi (9.9.a), concrete inertia ⟹ `g ∈ C`.**  The capstone combining the realization
(`conjBy_compHom_hInHuEquivH`) with the abstract reduction (`caseB_char_inertia_inflation`): in
Clifford case (b), if `g ∈ HU` (with `G`-image that of a `U`-element `a`) fixes the realized
inflation `Res`-constituent `compHom (hInHuEquivH) (compHom (mk' N) θ̄)` of a nontrivial
`θ̄ ∈ Irr(H̄)` (i.e. `g ∈ I_{HU}(θ)`), then `a` acts trivially on the chief factor: `φ_U(a) = 1`
(`a ∈ C`).  This is exactly the character-side inertia `I_U(θ) ⊆ C` of (9.9.a), now fully
concrete: the realization translates `conjBy` into `typeP_conjAction`-invariance, inflation strips
`compHom (hInHuEquivH)` and `compHom (mk' N)`, and `chiefFactor_caseB_char_inertia` concludes. -/
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
        chief.N_aInvariant).U.subtype) a = 1 := by
  rw [conjBy_compHom_hInHuEquivH data
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U.subtype a)
    g hag] at hfix
  exact caseB_char_inertia_inflation hcaseB hθbar a
    (ClassFunction.compHom_injective_of_surjective (hInHuEquivH data).surjective hfix)

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

/-- **`I_{HU}(θ₀) ⊓ U ≤ C`**: any `U`-element of `HU` fixing the realized chief-factor character
`θ₀` acts trivially on `H̄`, i.e. lies in `C` — exactly `caseB_inertia_realized`, with the action
element constructed from the `U`-realized `g`.  The hard half of the (9.9.a) inertia lift. -/
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
      ≤ cInHu data chief := by
  rintro g ⟨hgin, hgu⟩
  have hgU : ((g : ↥M) : G) ∈ data.typeP.U := by
    simp only [uInHu, Subgroup.mem_subgroupOf] at hgu; exact hgu
  have hgUW1 : ((g : ↥M) : G) ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_left hgU
  set a : ↥((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U) :=
    ⟨⟨((g : ↥M) : G), hgUW1⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha_def
  have hag : ((g : ↥M) : G)
      = (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) := rfl
  have hker : a ∈ (uActionHom data chief).ker :=
    caseB_inertia_realized hcaseB hθbar a g hag (ClassFunction.mem_inertia.mp hgin)
  simp only [cInHu, Subgroup.mem_subgroupOf, cSub, Subgroup.mem_map]
  exact ⟨_, ⟨a, hker, rfl⟩, rfl⟩

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
      (Subgroup.mem_sup_right (inertia_inf_uInHu_le_cInHu data chief hcaseB hθbar ⟨hu_in, hu⟩))
  · rw [sup_le_iff]
    exact ⟨ClassFunction.subgroup_le_inertia θ₀, cInHu_le_inertia data chief⟩

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
  sorry

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
  -- Obligation 1: extract a nontrivial chief-factor constituent `θ₀` (inflation form), with
  -- inertia `HC` and degree `1`.
  obtain ⟨θ₀, hθ₀over, hθ₀inertia, hθ₀deg⟩ :
      ∃ θ₀ : IrreducibleCharacter ↥(hInHu data),
        IrreducibleCharacter.LiesOver (hInHu data) χ θ₀ ∧
        IrreducibleCharacter.inertia (G := ↥(huSub data)) (H := hInHu data) θ₀
          = hInHu data ⊔ cInHu data chief ∧
        (θ₀ : ClassFunction ↥(hInHu data) ℂ) (1 : ↥(hInHu data)) = 1 := by
    classical
    haveI : Fintype (IrreducibleCharacter ↥(hInHu data)) := Fintype.ofFinite _
    -- `χ ∈ 𝒳` (so `H ⊄ ker χ`) and `χ ∈ 𝒳(H₀C')` (so `H₀C' ⊆ ker χ`).
    obtain ⟨hχX, hχker⟩ := hχ
    -- 1. A nontrivial constituent `θ` of `Res^{HU}_H χ` (`exists_constituent_not_subset…`).
    obtain ⟨θ, hθlo, hθnt⟩ :=
      OddOrder.RepresentationTheory.exists_constituent_not_subset_characterKernel
        (A := hInHu data) (B := hInHu data) le_rfl χ hχX
    -- 2. The descent hom `f = (mk' N) ∘ hInHuEquivH : ↥(hInHu) → H̄ = ↥H ⧸ N`.
    set f : ↥(hInHu data) →* (↥data.H ⧸ chief.N) :=
      (QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom with hf
    have hfsurj : Function.Surjective f :=
      (QuotientGroup.mk'_surjective chief.N).comp (hInHuEquivH data).surjective
    -- `f.ker ⊆ ker θ`: `f x = 1` means `hInHuEquivH x ∈ N`, so the `G`-coordinate of `x` lies in
    -- `H₀ ⊆ ker χ`, and the constituent `θ` inherits the kernel containment.
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
        apply hχker
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_sup_left hxH0
      exact liesOver_mem_characterKernel hθlo hxχ
    -- 3. `θ` is an inflation: `θ = compHom f θbar` for some `θbar ∈ Irr(H̄)`.
    obtain ⟨θbar, hθbar⟩ :=
      OddOrder.RepresentationTheory.exists_compHom_eq_of_subset_characterKernel hfsurj θ hfker
    -- The realized inflation form expected by `inertia_eq_hcInHu`.
    have hθeq : (θ : ClassFunction ↥(hInHu data) ℂ)
        = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
            (ClassFunction.compHom (QuotientGroup.mk' chief.N)
              (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) := by
      rw [← hθbar, hf, ClassFunction.compHom_comp]
    -- 4. `θbar` is nontrivial (else `θ` would be trivial, contradicting `hθnt`).
    have hθbarnt : (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)
        ≠ trivialClassFunction _ := by
      intro h0
      apply hθnt
      rw [Subgroup.subgroupOf_self]
      intro y _
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
        hθeq, h0]
      simp [ClassFunction.compHom_apply, trivialClassFunction]
    -- `H̄` is abelian (elementary abelian chief factor), so `θbar` is linear.
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
  -- Obligation 3: a constituent `ψ ∈ Irr(HC)` that `χ` lies over, linear.
  obtain ⟨ψ, hψover⟩ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.exists_liesOver
      (H := hInHu data ⊔ cInHu data chief) χ
  have hψdeg : (ψ : ClassFunction ↥(hInHu data ⊔ cInHu data chief) ℂ)
      (1 : ↥(hInHu data ⊔ cInHu data chief)) = 1 := by
    sorry
  -- Clifford degree: `χ(1) = [HU:HC]`.
  have key := OddOrder.RepresentationTheory.apply_one_eq_index_of_liesOver_linear_inertia
    (H := hInHu data) (I := hInHu data ⊔ cInHu data chief)
    χ θ₀ ψ hθ₀over hθ₀inertia hθ₀deg hψover hψdeg
  -- Obligation 4: `[HU:HC] = u`.
  have hidx : (hInHu data ⊔ cInHu data chief).index = chars.u := by
    sorry
  rw [key, hidx]

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
  sorry

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
