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
import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF

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

/-- Peterfalvi's `H` in (9.2). -/
def H {M : Subgroup G} (data : TypesIIIIIIVSetup M) : Subgroup G :=
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

/-- Data for the chief factor `H/H_0` selected in Peterfalvi (9.4).

The quotient predicates are kept as named propositions until the project has a
settled API for solvable chief factors as modules for `M/H_0`. -/
structure ChiefFactorData {M : Subgroup G} (data : TypesIIIIIIVSetup M) where
  H0 : Subgroup G
  H0_lt_H : H0 < data.H
  H0_normalized_by_M : M ≤ Subgroup.normalizer (H0 : Set G)
  p : ℕ
  p_prime : p.Prime
  quotient_elementaryAbelian : Prop
  quotient_elementaryAbelian_holds : quotient_elementaryAbelian
  quotient_chiefFactor : Prop
  quotient_chiefFactor_holds : quotient_chiefFactor
  quotient_order : Nat.card ↥data.H = p ^ data.q * Nat.card ↥H0
  typeIII_IV_p_eq_W2 : IsTypeIII M ∨ IsTypeIV M → Nat.card ↥data.W2 = p
  U_noncentral_on_quotient : Prop
  U_noncentral_on_quotient_holds : U_noncentral_on_quotient

/-! ### §8 inputs to (9.3)

The two fixed-point-free §8 facts that (9.3) consumes are stated here as named obligations about
the *explicit* type-`P` data of the maximal subgroup, so that (9.3) cites them directly (its proof
body carries no `sorry` of its own).  Each is to be discharged by the §8/§10 local-analysis
development by wiring it to the cited canonical result; doing so makes (9.3) unconditional. -/

/-- **§8 input to (9.3)** — Peterfalvi (8.6.b II) + (8.12.b): for a maximal subgroup `M` of type II,
the Frobenius kernel `U` acts fixed-point-freely on `H = M_F`, i.e. `C_H(U) = 1`.

*Discharge route:* a nontrivial `C_H(U)` makes `C_G(U)` uniquely maximal (Peterfalvi (8.12) =
`OddOrder.Peterfalvi.S10.typeI_or_typeII_centralizer_unique`, applied to `U ≤ M`), forcing
`N_G(U) ⊆ M`, against `TypeIIData.normalizer_not_le` (8.6.b II).  The §8/§10 obligation. -/
theorem typeII_centralizer_U_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (data : TypePData M) (hM : M ∈ maximalSubgroups G) (hII : IsTypeII M) :
    data.H ⊓ Subgroup.centralizer (data.U : Set G) = ⊥ := by
  sorry

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
  -- `C_{H̄}(U) = 1`: it is `U W₁`-invariant (`U` is the normal Frobenius kernel) and `≠ H̄`.
  have hUnorm : (act'.U).Normal := (typeP_uW1_frobenius data hU).isNormal
  have hUinv : IsAInvariant act'.φ act'.fixedByU :=
    isAInvariant_fixedSubgroup_of_normal act'.φ hUnorm
  have hfixU : act'.fixedByU = ⊥ := (hirr _ hUinv).resolve_right hUntriv
  -- `|C_{H̄}(W₁)| ∣ p`: `C_{H̄}(W₁)` is the image of the cyclic `W₂ = C_H(W₁)`.
  have hdvd : Nat.card ↥act'.fixedByE ∣ p := by
    -- `C_{H̄}(W₁) = (C_H(W₁)).map (mk' N)` (Isaacs Cor 3.28).
    have hcopHW1 : Nat.Coprime
        (Nat.card ↥(data.W1.subgroupOf (data.U ⊔ data.W1))) (Nat.card ↥data.H) :=
      (typeP_coprime_H_uW1 data hU).symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
    haveI : IsSolvable ↥data.H := (typeP_coprimeAction data hU).H_solvable
    have hmap : (fixedSubgroup (typeP_conjAction data)
        (data.W1.subgroupOf (data.U ⊔ data.W1))).map (QuotientGroup.mk' N) = act'.fixedByE :=
      map_fixedSubgroup_eq_fixedSubgroup_quotient hN hcopHW1 (Or.inr inferInstance)
    -- `C_H(W₁) ≅ W₂` is cyclic, so its image `C_{H̄}(W₁)` is cyclic.
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
    have hcycE : IsCyclic ↥act'.fixedByE := by
      let f := (QuotientGroup.mk' N).comp (fixedSubgroup (typeP_conjAction data)
          (data.W1.subgroupOf (data.U ⊔ data.W1))).subtype
      have hrange : f.range = act'.fixedByE := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]; exact hmap
      rw [← hrange]
      exact isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
    exact card_dvd_prime_of_isCyclic_of_pow hpe.2 hcycE
  -- Wielandt's formula + the prime computation give `|H̄| = p^{|act'.E|} = p^q`.
  have hcard := coprimeFrobeniusAction_card_eq_prime_pow act' hfixU hp hdvd hHbar
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

/-- **Peterfalvi (9.4)**: existence of a nontrivial elementary abelian chief
factor `H/H_0` not centralized by `U`. -/
theorem exists_chiefFactorData [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (data : TypesIIIIIIVSetup M) :
    ∃ chief : ChiefFactorData data, chief.H0 < data.H := by
  sorry

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

/-- **Peterfalvi (9.6)**: after choosing `H_0`, the induced `U`-action is
nontrivial, `H/H_0` is a chief factor, and the relevant `W_2`-fixed part has
order `p`. -/
theorem chiefFactor_basic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    data.U ⊓ Subgroup.centralizer (data.H : Set G) ≠ data.U ∧
      chief.quotient_chiefFactor ∧ Nat.card ↥data.W2 = chief.p := by
  sorry

/-- **Peterfalvi (9.7)**: the Clifford-theory dichotomy for the action on the
chief factor `H/H_0`. -/
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
