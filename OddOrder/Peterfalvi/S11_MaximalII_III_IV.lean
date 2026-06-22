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

/-- The character-theoretic setup of Peterfalvi (9.5).

`C`, `U'`, and `C'` denote the centralizer, commutator subgroup, and its
intersection with `C` used in the text.  The sets `X`, `S`, `XOf`, and `SOf`
record Peterfalvi's families of irreducible characters attached to subgroups
between `H_0` and `H U`. -/
structure Section11CharacterData {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) where
  C : Subgroup G
  C_le_U : C ≤ data.U
  Uprime : Subgroup G
  Uprime_le_U : Uprime ≤ data.U
  Cprime : Subgroup G
  Cprime_le_C : Cprime ≤ C
  u : ℕ
  u_eq_card_quotient : Prop
  u_eq_card_quotient_holds : u_eq_card_quotient
  X : Set (ClassFunction ↥M ℂ)
  S : Set (ClassFunction ↥M ℂ)
  XOf : Subgroup G → Set (ClassFunction ↥M ℂ)
  SOf : Subgroup G → Set (ClassFunction ↥M ℂ)
  H0CprimeSupport : Set ↥M
  tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  quotientSemidirectFrobenius : Prop

/-- Case (a) of Peterfalvi (9.7): `H/H_0` splits as a direct product of `q`
order-`p` factors permuted by `W_1`. -/
structure CliffordCaseAData {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief) where
  Hpart : Fin data.q → Subgroup G
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
the multiplicative group of a field of order `p^q`. -/
structure CliffordCaseBData {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief) where
  field_model : Prop
  field_model_holds : field_model
  Ubar_cyclic : Prop
  Ubar_cyclic_holds : Ubar_cyclic
  u_coprime_p_sub_one : Nat.Coprime chars.u (chief.p - 1)
  u_dvd_norm_quotient : chars.u ∣ (chief.p ^ data.q - 1) / (chief.p - 1)

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
theorem card_eq_pow_of_iSup_aInvariant_irreducible {K : Type*} [Group K] [Finite K]
    {A : Type*} [Group A] {φ : A →* MulAut K} {ι : Type*} [Finite ι]
    {S : ι → Subgroup K} {n : ℕ}
    (hcomm : ∀ x y : K, Commute x y)
    (hspan : ⨆ i, S i = ⊤)
    (hinv : ∀ i, IsAInvariant φ (S i))
    (hirr : ∀ i, ∀ J : Subgroup K, IsAInvariant φ J → J ≤ S i → J = ⊥ ∨ J = S i)
    (hcard : ∀ i, S i ≠ ⊥ → Nat.card ↥(S i) = n) :
    ∃ k, Nat.card K = n ^ k := by
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
  refine ⟨t.card, ?_⟩
  have hfac : ∀ i : (t : Finset ι), Nat.card ↥(S ↑i) = n := fun i => hcard ↑i (ht_ne ↑i i.2)
  calc Nat.card K = Nat.card (∀ i : (t : Finset ι), ↥(S ↑i)) :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = ∏ i : (t : Finset ι), Nat.card ↥(S ↑i) := Nat.card_pi
    _ = ∏ _i : (t : Finset ι), n := Finset.prod_congr rfl (fun i _ => hfac i)
    _ = n ^ t.card := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

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
          chief.N_aInvariant).U.subtype) S₀ ∧ Nat.card ↥S₀ = chief.p) := by
  obtain ⟨d, S₀, _hdpos, hdq, hS₀ne, hcard, hS₀inv, hirr₀⟩ :=
    chiefFactor_clifford_dim_dvd_q chief
  -- `q = |W₁|` is prime and `d ∣ q`, so `d = 1` or `d = q`.
  have hq_prime : (data.q).Prime := data.nontrivial.2.1
  rcases hq_prime.eq_one_or_self_of_dvd d hdq with hd1 | hdq2
  · -- `d = 1`: a `U`-invariant subgroup of order `p`.  Clifford case (a).
    exact Or.inr ⟨S₀, hS₀ne, hS₀inv, by rw [hcard, hd1, pow_one]⟩
  · -- `d = q`: `|S₀| = p^q = |H̄|` ⟹ `S₀ = ⊤`; minimality ⟹ `U`-irreducible.  Case (b).
    have hS₀top : S₀ = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hcard, hdq2, chiefFactor_quotient_card chief])
    refine Or.inl fun J hJinv => ?_
    by_cases hJ : J = ⊥
    · exact Or.inl hJ
    · exact Or.inr
        (((hirr₀ J hJinv (le_top.trans_eq hS₀top.symm)).resolve_left hJ).trans hS₀top)

/-- **Peterfalvi (9.7)**: the Clifford-theory dichotomy for the action on the
chief factor `H/H_0`.

The case split itself is `chiefFactor_clifford_U_dichotomy` (sorry-free): `U` acts on `H̄` either
irreducibly (case (b)) or with a `U`-invariant order-`p` factor (case (a)).  What remains is to
package each branch into its character-theoretic carrier — the `q` order-`p` factors and the bound
`a ∣ p-1` for case (a), and the field-model divisibilities `Coprime u (p-1)`,
`u ∣ (p^q-1)/(p-1)` for case (b).  The latter need the chief factor pinned as a 1-dimensional space
over `End_{𝔽ₚ[U]}(H̄)` (a finite division ring, hence a field by `littleWedderburn`), and require
`chars.u` to be tied to `|Ū|` (the carrier currently leaves `u` free via `u_eq_card_quotient`). -/
theorem clifford_dichotomy [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) :
    Nonempty (CliffordCaseAData chars) ∨ Nonempty (CliffordCaseBData chars) := by
  sorry

/-! ## (9.8)--(9.10): character counts in the two Clifford cases -/

/-- **Peterfalvi (9.8)**: character-count consequences in Clifford case (a). -/
theorem caseA_character_counts [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseA : CliffordCaseAData chars) :
    (∃ μ : Fin (chief.p - 1) → ClassFunction ↥M ℂ,
      Set.range μ ⊆ chars.SOf chief.H0 ∧
        ∀ j, μ j 1 = ((data.q * chars.u : ℕ) : ℂ)) ∧
      (∃ χ ∈ chars.SOf chars.C, χ 1 = ((data.q * chars.u : ℕ) : ℂ)) ∧
      ((chief.p - 1) / caseA.a) * (Nat.card ↥data.U / (caseA.a * Nat.card ↥chars.Uprime)) ≤
        (chars.SOf chars.Uprime).ncard := by
  sorry

/-- **Peterfalvi (9.9)**: character-count consequences in Clifford case (b). -/
theorem caseB_character_counts [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars) :
    chars.u ∣ data.q * chars.u ∧
      (∃ χ ∈ chars.SOf chars.Cprime, χ 1 = ((chars.u : ℕ) : ℂ)) ∧
      (chars.SOf chief.H0).ncard = chief.p - 1 ∧
      ((chars.SOf chars.Cprime).ncard = 0 →
        chars.C = ⊥ ∧ chars.u = (chief.p ^ data.q - 1) / (chief.p - 1)) := by
  sorry

/-- **Peterfalvi (9.10)**: in the exceptional case with no degree-`q u`
characters induced from `H C`, the quotient semidirect product is Frobenius; in
type II the full `H U` subgroup is Frobenius with kernel `H`. -/
theorem exceptional_case_frobenius_realization [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars)
    (hno : ¬ ∃ χ ∈ chars.SOf chars.C, χ 1 = ((data.q * chars.u : ℕ) : ℂ)) :
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
