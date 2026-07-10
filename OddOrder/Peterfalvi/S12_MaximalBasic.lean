/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_Section9Counts
import OddOrder.Peterfalvi.S12_TypeIIFrobenius
import OddOrder.Peterfalvi.S09_CertificateDischarge

/-!
# S12_MaximalBasic

Prefix-split from `OddOrder.Peterfalvi.S12_MaximalIII_IV_V` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# Peterfalvi Section 12: Maximal Subgroups of Types III, IV, and V

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 12, pp. 58--63.

Active-frontier leaf of the Section 12 formalization: (10.7) type-II derived
Frobenius, (10.8) non-coherence of the family `S`, (10.10) elimination of
type V, and the (11.8) orthogonality cluster
(`exists_zeta_residual_not_orthogonal` with its residual-coefficient
machinery).  The frozen upstream material — the scoped `FiniteInduce`
instances, the Hypothesis (10.1) carrier and its API, and the
(10.5)--(10.6) `omega_ij^sigma` grid / `tau1` chains — lives in
`S12_MaximalIII_IV_V_Core` (hub prefix-split 2026-07-02, issue 0076);
downstream imports of this module are unchanged.
-/

namespace OddOrder.Peterfalvi.S12
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## (10.7)--(10.8): Type II derived Frobenius and non-coherence -/

/-- A carrier for the conclusion of Peterfalvi (10.7): `[S,S]` is a Frobenius
group with kernel `S_F`. -/
structure DerivedFrobeniusData (S : Subgroup G) where
  kernel : Subgroup ↥(derivedInG S)
  complement : Subgroup ↥(derivedInG S)
  kernel_is_SF : Prop
  frobenius : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG S) kernel complement

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.7)**: if `S` is a maximal subgroup of type II, then `[S,S] = S^{(1)}` is a
Frobenius group with kernel `S_F` (Coq `Frob_der1_type2`, `PFsection10.v:549`).

The Frobenius structure is `typeII_HU_frobenius_of_coherent` (`S12_TypeIIFrobenius`): the
`S`-side §9 Clifford dichotomy either lands in the exceptional case — where Peterfalvi (9.10)
(`S11.exceptional_case_frobenius_realization`, proven) yields the `HU`-Frobenius directly — or
supplies an irreducible/reducible pair of equal degree `q·u`, which the (10.7) cross-isometry
computation refutes (`TypeIICrossIsometryData.elim`, proven, against the named left-branch gate
`exists_typeIICrossIsometryData`: T2-coherence (5.7) + shared-grid (5.8) + (8.18.b) support
disjointness).  The `coh`/`hSmax`/`hG` hypotheses (10.4)/(10.1) are what the dichotomy consumes. -/
theorem typeII_derived_frobenius [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSType : IsTypeII S) :
    ∃ data : DerivedFrobeniusData S, data.kernel_is_SF := by
  classical
  obtain ⟨td⟩ := hSType
  exact ⟨{ kernel := td.typeP.H.subgroupOf (derivedInG S)
           complement := td.typeP.U.subgroupOf (derivedInG S)
           kernel_is_SF := td.typeP.H.subgroupOf (derivedInG S)
             = (maxNilpotentNormalHall S).subgroupOf (derivedInG S)
           frobenius := typeII_HU_frobenius_of_coherent hG coh hSmax td },
         congrArg (·.subgroupOf (derivedInG S)) td.typeP.H_eq⟩

/-- **Closing arithmetic contradiction of Peterfalvi (10.8)** — the numerical heart of the
non-coherence proof, isolated from the character machinery.

The structural facts derived (under the *coherence* assumption) for the Type-II partner `S` are:
* `w₁ ≥ 3` and the Frobenius bound `|U| ≥ 2w₂+1 ≥ 7` (since `UW₂` is Frobenius and `w₂ ≥ 3`);
* the lower bound `|M'| ≥ (2w₁+1)·w₂`, from `|M'/M''| ≥ 2w₁+1` (the odd Frobenius group
  `(M'/M'')⋊W₁`, Peterfalvi (8.4.d)) and `|M''| ≥ w₂`.

The `(7.5)`/`(7.8.b)`/`(10.6.b)` norm-counting estimate, after the `G₁ ⊆ (H#)^G ∪ V^G` bound,
yields `w₁w₂/|M'| > 1 − 1/w₁ − 1/|U|`.  Its right side exceeds `1 − 1/3 − 1/7 > 1/2`, forcing
`|M'| < 2w₁w₂`; this contradicts `|M'| ≥ (2w₁+1)w₂ = 2w₁w₂ + w₂`.  Pure arithmetic over `ℚ`. -/
theorem typeII_noncoherence_arithmetic
    {w₁ w₂ u Mp : ℕ} (hw1 : 3 ≤ w₁) (hu : 7 ≤ u) (hw2 : 1 ≤ w₂)
    (hMp : (2 * w₁ + 1) * w₂ ≤ Mp)
    (hbound : (1 : ℚ) - 1 / (w₁ : ℚ) - 1 / (u : ℚ) < (w₁ : ℚ) * (w₂ : ℚ) / (Mp : ℚ)) :
    False := by
  have hw1q : (3 : ℚ) ≤ (w₁ : ℚ) := by exact_mod_cast hw1
  have huq : (7 : ℚ) ≤ (u : ℚ) := by exact_mod_cast hu
  have hw2q : (1 : ℚ) ≤ (w₂ : ℚ) := by exact_mod_cast hw2
  have hMppos : 0 < Mp := lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega)) hMp
  have hMpq : (0 : ℚ) < (Mp : ℚ) := by exact_mod_cast hMppos
  -- `1/w₁ ≤ 1/3` and `1/u ≤ 1/7`, so the coherence bound exceeds `1 − 1/3 − 1/7 > 1/2`.
  have h1 : 1 / (w₁ : ℚ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hw1q
  have h2 : 1 / (u : ℚ) ≤ 1 / 7 := one_div_le_one_div_of_le (by norm_num) huq
  have hhalf : (1 : ℚ) / 2 < (w₁ : ℚ) * (w₂ : ℚ) / (Mp : ℚ) := by
    have h112 : (1 : ℚ) - 1 / 3 - 1 / 7 > 1 / 2 := by norm_num
    linarith
  -- Clear the denominator: `Mp < 2·w₁w₂`.
  have hhalf' : (1 : ℚ) / 2 * (Mp : ℚ) < (w₁ : ℚ) * (w₂ : ℚ) := (lt_div_iff₀ hMpq).mp hhalf
  -- The lower bound `(2w₁+1)w₂ = 2·w₁w₂ + w₂ ≤ Mp` contradicts it.
  have hMpcast : 2 * ((w₁ : ℚ) * (w₂ : ℚ)) + (w₂ : ℚ) ≤ (Mp : ℚ) := by
    have : ((2 * w₁ + 1) * w₂ : ℚ) ≤ (Mp : ℚ) := by exact_mod_cast hMp
    push_cast at this; linarith
  linarith

/-- **Peterfalvi (10.8), structural lower bound** `(2w₁+1)·w₂ ≤ |M'|` (the `hMp` input to the
non-coherence arithmetic `typeII_noncoherence_arithmetic`).

Peterfalvi's "By (8.4.d), `(M'/M'')⋊W₁` is a Frobenius group of odd order; it follows that
`|M':M''| ≥ 2w₁+1`": the cyclic Hall complement `W₁` acts on the abelian section `M'/M''`
fixed-point-freely (its fixed points on `M'` are `C_{M'}(x) = W₂` by `TypePData.centralizer_W1`, and
`W₂ ⊆ M''` by `TypePData.W2_le`), so `w₁ ∣ |M':M''| − 1` (`S08.caseB_W1_dvd_index_of_centralizer_le`,
the `W₁`-conjugation action on `H = M'.subgroupOf M` with `M'' = ⁅H,H⁆`); with all orders odd and
`M'' < M'` (`M'` solvable nontrivial, `IsSolvable.commutator_lt_top_of_nontrivial`) this forces
`|M':M''| ≥ 2w₁+1` (`S08.two_mul_add_one_le_of_odd_dvd`).  Then `|M'| = |M''|·|M':M''| ≥ w₂·(2w₁+1)`
(`Subgroup.index_mul_card`) since `w₂ = |W₂| ≤ |M''|` (`W₂ ⊆ M''`).  Genuine group theory, **proven**
(sorryAx only via the upstream `typePData_W1_hall_coprime`, the shared §10 type-P coprimality). -/
theorem Hypothesis.card_derived_ge [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    (2 * hyp.w1 + 1) * hyp.w2 ≤ Nat.card ↥(derivedInG M) := by
  haveI := hyp.finiteG
  classical
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `derivedInG K = ⁅K, K⁆` (the commutator of `K` with itself in `G`).
  have hderiv : ∀ K : Subgroup G, derivedInG K = ⁅K, K⁆ := fun K => by
    rw [derivedInG, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  -- `H = M'` realised inside `↥M`; normal, `H.map subtype = M'`, `⁅H,H⁆.map subtype = M''`.
  set H : Subgroup ↥M := (derivedInG M).subgroupOf M with hHdef
  have hKcomm : H = _root_.commutator ↥M := by
    rw [hHdef, derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hHnorm : H.Normal := by rw [hKcomm]; infer_instance
  have hHmap : H.map M.subtype = derivedInG M := by
    rw [hHdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hM'le]
  have hmapcomm : (⁅H, H⁆ : Subgroup ↥M).map M.subtype = secondDerivedInAmbient M := by
    rw [Subgroup.map_commutator, hHmap, ← hderiv]; rfl
  have hW2leM' : hyp.typeP.W2 ≤ derivedInG M :=
    (hyp.typeP.W2_le.trans inf_le_right).trans (Subgroup.map_subtype_le _)
  -- `↥H` is solvable and nontrivial, so `M'' = ⁅H,H⁆ < H` and the index is `> 1`.
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hyp.maximal
  haveI hHsolv : IsSolvable ↥H :=
    solvable_of_solvable_injective (f := H.subtype) (Subgroup.subtype_injective H)
  haveI hHnt : Nontrivial ↥H := by
    have h1 : 1 < Nat.card ↥H := by
      rw [hHdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv]
      calc 1 < Nat.card ↥hyp.typeP.W2 :=
            (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W2_nontrivial
        _ ≤ Nat.card ↥(derivedInG M) := Subgroup.card_le_of_le hW2leM'
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  -- the FPF divisibility `w₁ ∣ |H : ⁅H,H⁆| − 1`.
  have hcardW1 : Nat.card ↥(hyp.W1.subgroupOf M) = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.typeP.W1_le).toEquiv
  have hcop : Nat.Coprime (Nat.card ↥(hyp.W1.subgroupOf M)) (Nat.card ↥H) := by
    rw [hcardW1, hHdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv]
    exact (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP).symm
  have hdvd : Nat.card ↥(hyp.W1.subgroupOf M) ∣ (_root_.commutator ↥H).index - 1 := by
    refine OddOrder.Peterfalvi.S08.caseB_W1_dvd_index_of_centralizer_le (hyp.W1.subgroupOf M) hcop
      (_root_.commutator ↥H) ?_
    intro a ha x hcomm
    have haW1 : ((↑(↑a : ↥M) : G)) ∈ hyp.W1 := Subgroup.mem_subgroupOf.mp a.2
    have hane : ((↑(↑a : ↥M) : G)) ≠ 1 := fun h => ha (Subtype.ext (Subtype.ext h))
    have hxM' : ((↑(↑x : ↥M) : G)) ∈ derivedInG M :=
      Subgroup.mem_subgroupOf.mp (hHdef ▸ x.2)
    have hcommG : ((↑(↑x : ↥M) : G)) * ((↑(↑a : ↥M) : G))
        = ((↑(↑a : ↥M) : G)) * ((↑(↑x : ↥M) : G)) := by
      simpa using (congrArg (fun t : ↥M => (↑t : G)) hcomm).symm
    have hxW2 : ((↑(↑x : ↥M) : G)) ∈ hyp.typeP.W2 := by
      rw [← hyp.typeP.centralizer_W1 _ haW1 hane]
      exact Subgroup.mem_inf.mpr ⟨hxM', Subgroup.mem_centralizer_singleton_iff.mpr hcommG⟩
    have key : (↑x : ↥M) ∈ (⁅H, H⁆ : Subgroup ↥M) := by
      refine (Subgroup.mem_map_iff_mem M.subtype_injective).mp ?_
      rw [hmapcomm]
      exact (hyp.typeP.W2_le.trans inf_le_right) hxW2
    exact OddOrder.Peterfalvi.S08.commutator_subgroupOf_self H ▸ Subgroup.mem_subgroupOf.mpr key
  -- `|H : ⁅H,H⁆| ≥ 2w₁ + 1` (odd Frobenius bound).
  have hidxgt : 1 < (_root_.commutator ↥H).index := by
    have hne1 : (_root_.commutator ↥H).index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one]
      exact (IsSolvable.commutator_lt_top_of_nontrivial ↥H).ne
    have hpos : (_root_.commutator ↥H).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    omega
  have hidxge : 2 * hyp.w1 + 1 ≤ (_root_.commutator ↥H).index := by
    have hw1odd : Odd hyp.w1 := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.W1)
    have hidxodd : Odd (_root_.commutator ↥H).index :=
      hG.odd.of_dvd_nat (dvd_trans (Subgroup.index_dvd_card _)
        (dvd_trans (Subgroup.card_subgroup_dvd_card H) (Subgroup.card_subgroup_dvd_card M)))
    exact OddOrder.Peterfalvi.S08.two_mul_add_one_le_of_odd_dvd hw1odd hidxodd
      (hcardW1 ▸ hdvd) hidxgt
  -- `|⁅H,H⁆| = |M''| ≥ w₂`.
  have hcommle : (⁅H, H⁆ : Subgroup ↥M) ≤ H := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hp hq) (H.inv_mem hp)) (H.inv_mem hq)
  have hcardge : hyp.w2 ≤ Nat.card ↥(_root_.commutator ↥H) := by
    have eMap := Subgroup.equivMapOfInjective (⁅H, H⁆ : Subgroup ↥M) M.subtype M.subtype_injective
    rw [← OddOrder.Peterfalvi.S08.commutator_subgroupOf_self,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcommle).toEquiv,
      Nat.card_congr eMap.toEquiv, hmapcomm]
    exact Subgroup.card_le_of_le (hyp.typeP.W2_le.trans inf_le_right)
  -- combine: `|M'| = |H| = |⁅H,H⁆|·|H:⁅H,H⁆| ≥ w₂·(2w₁+1)`.
  have hHcard : Nat.card ↥H = Nat.card ↥(derivedInG M) := by
    rw [hHdef]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv
  calc (2 * hyp.w1 + 1) * hyp.w2
      ≤ (_root_.commutator ↥H).index * Nat.card ↥(_root_.commutator ↥H) :=
        Nat.mul_le_mul hidxge hcardge
    _ = Nat.card ↥H := (_root_.commutator ↥H).index_mul_card
    _ = Nat.card ↥(derivedInG M) := hHcard

/-- **Peterfalvi (10.8), line-87 strict bound** `|A(M)|/|M| < 1/w₁`.

Since `A(M) = typePA M = (M')#` (`typePA_eq_sharpSubgroup_derivedInG`), `|A(M)| = |M'| − 1`; and
`|M| = w₁·|M'|` because `[M : M'] = w₁` (`TypePData.card_W1_eq_derived_index`,
`Subgroup.index_mul_card`).  Hence `|A(M)|/|M| = (|M'|−1)/(w₁·|M'|) < 1/w₁` (as `|M'| ≥ 1`, `w₁ ≥ 1`).
This is the strict inequality Peterfalvi (10.8) uses at line 87 to turn `w₁/|M'| ≥ 1 − |G₁|/|G| −
|A(M)|/|M|` into `> 1 − |G₁|/|G| − 1/w₁` (the `hA` consumed by `typeII_coherence_estimate_chain`). -/
theorem Hypothesis.card_typePA_div_card_lt_inv_w1 [Finite G]
    {M : Subgroup G} (hyp : Hypothesis M) :
    (Nat.card ↥(typePA M hyp.typeP) : ℚ) / (Nat.card ↥M : ℚ) < 1 / (hyp.w1 : ℚ) := by
  haveI := hyp.finiteG
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `|A(M)| = |M'| − 1` (sharp of the derived subgroup).
  have hcardA : Nat.card ↥(typePA M hyp.typeP) = Nat.card ↥(derivedInG M) - 1 := by
    rw [typePA_eq_sharpSubgroup_derivedInG, Nat.card_coe_set_eq]
    have hc : Nat.card ↥(derivedInG M) = ((derivedInG M : Set G)).ncard := by
      rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
    rw [sharpSubgroup, Set.ncard_sdiff (Set.singleton_subset_iff.mpr (derivedInG M).one_mem),
      Set.ncard_singleton, hc]
  -- `|M| = w₁·|M'|` since `[M : M'] = w₁`.
  have hcardM : Nat.card ↥M = hyp.w1 * Nat.card ↥(derivedInG M) := by
    have hidx : ((derivedInG M).subgroupOf M).index = hyp.w1 := by
      rw [Hypothesis.w1, Hypothesis.W1]; exact hyp.typeP.card_W1_eq_derived_index.symm
    have hsub : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv
    rw [← Subgroup.index_mul_card ((derivedInG M).subgroupOf M), hidx, hsub]
  -- arithmetic over `ℚ`.
  have hm1 : 1 ≤ Nat.card ↥(derivedInG M) := Nat.card_pos
  have hw1 : 1 ≤ hyp.w1 := Nat.card_pos
  rw [hcardA, hcardM, Nat.cast_sub hm1, Nat.cast_mul]
  have hmq : (0 : ℚ) < (Nat.card ↥(derivedInG M) : ℚ) := by exact_mod_cast hm1
  have hwq : (0 : ℚ) < (hyp.w1 : ℚ) := by exact_mod_cast hw1
  rw [div_lt_div_iff₀ (by positivity) hwq]
  push_cast
  nlinarith [hmq, hwq]

open scoped FiniteInduce in
/-- **`‖ζ^{τ₁}‖² = 1`** (Peterfalvi (10.8) line 81 input): the coherent extension `τ₁` of the Dade
isometry is an isometry on `ℤ[S]` (`coh.coherent.extension_inner_eq`), and `ζ = params.zeta ∈ S` is
irreducible (`params.zeta_irreducible`, `params.zeta_mem_S`), so `‖ζ^{τ₁}‖² = ‖ζ‖² = 1`.

This is the norm-one hypothesis that `S09.family_inequality` (7.5) demands of its character argument
`χ = ζ^{τ₁}`, so it is the bridge that lets the now-self-contained `toFamilyHypothesis71` feed the
(10.8) line-81 inequality. -/
theorem Hypothesis.inner_tau1_zeta_self_eq_one [Finite G] [Fintype G] {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params) :
    ClassFunction.inner (coh.tau1 params.zeta) (coh.tau1 params.zeta) = 1 := by
  have hspan : params.zeta ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) hyp.Sset :=
    Submodule.subset_span params.zeta_mem_S
  show ClassFunction.inner (coh.coherent.extension params.zeta)
    (coh.coherent.extension params.zeta) = 1
  rw [coh.coherent.extension_inner_eq params.zeta params.zeta hspan hspan]
  simpa using OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
    (⟨params.zeta, params.zeta_irreducible⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥M)
    (⟨params.zeta, params.zeta_irreducible⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥M)

/-- **The `(10.6.b)`-summed bound** (the analytic core of Peterfalvi (10.8) line 83): if a function
`χ : G → ℂ` takes **odd integer** values on a finite set `S` (in particular `|χ(g)| ≥ 1` there), then
`|S| ≤ Σ_{g ∈ S} ‖χ(g)‖²`.  General and reusable (no §10 hypotheses): per element, an odd integer
`m ≠ 0` has `‖(m : ℂ)‖² = |m|² ≥ 1`, and `Σ_S 1 = |S|`.  In the (10.8) proof this is applied to
`χ = ζ^{τ₁}` on `G₀ = {g | g ∉ Ã(M), (ord g).Coprime w₁}` via (10.6.b) `zeta_tau1_norm_ge_one`,
dropping the `G₀`-part of the (7.5) sum to reach line 83. -/
theorem card_le_sum_normSq_of_forall_eq_odd_intCast {ι : Type*} (S : Finset ι) {χ : ι → ℂ}
    (h : ∀ g ∈ S, ∃ m : ℤ, χ g = (m : ℂ) ∧ Odd m) :
    (S.card : ℝ) ≤ ∑ g ∈ S, ‖χ g‖ ^ 2 := by
  calc (S.card : ℝ) = ∑ _g ∈ S, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ g ∈ S, ‖χ g‖ ^ 2 := by
        refine Finset.sum_le_sum (fun g hg => ?_)
        obtain ⟨m, hm, hodd⟩ := h g hg
        have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hodd; omega
        have hnorm : ‖χ g‖ = |(m : ℝ)| := by rw [hm, Complex.norm_intCast]
        have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm0
        rw [hnorm]; nlinarith [h1, abs_nonneg ((m : ℝ))]

open scoped Classical FiniteInduce in
/-- **The `(10.6.b)`-summed bound for `ζ^{τ₁}`** — `|G₀| ≤ Σ_{g ∈ G₀} ‖ζ^{τ₁}(g)‖²` over
`G₀ = {g | g ∉ Ã(M), (ord g).Coprime w₁}`.  Composes `card_le_sum_normSq_of_forall_eq_odd_intCast`
(the analytic core) with the per-`g` (10.6.b) bound `tau1_values_and_norm_bound` (`ζ^{τ₁}(g)` is an
odd integer off `Ã(M)` at orders prime to `w₁`).  The 7 parameter conditions are exactly those
supplied by `exists_charParameters_full`.  This is the `G₀`-drop term Peterfalvi (10.8) uses to pass
from the family inequality (7.5) (line 81) to line 83. -/
theorem Hypothesis.sum_zeta_tau1_normSq_ge_card [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    ((Finset.univ.filter
        (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport ∧ (orderOf g).Coprime hyp.w1)).card : ℝ)
      ≤ ∑ g ∈ Finset.univ.filter
          (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport ∧ (orderOf g).Coprime hyp.w1),
          ‖coh.tau1 params.zeta g‖ ^ 2 := by
  classical
  apply card_le_sum_normSq_of_forall_eq_odd_intCast
  intro g hg
  rw [Finset.mem_filter] at hg
  exact (tau1_values_and_norm_bound hG coh hmu hos hzS hz1 hzconj hδpm hδj).2 g hg.2.1 hg.2.2

/-- **Restricting the Dade support shrinks it**: for `A₁ ⊆ A`, the Dade support of the restricted
hypothesis `hyp.restrict` is contained in that of `hyp` (`mem_dadeSupport_iff`: a witness
`a ∈ A₁, h ∈ H(a)` for the restriction is a witness `⟨a, _⟩ ∈ A` for `hyp`, since
`(hyp.restrict ..).H a = hyp.H ⟨a, _⟩`).  In the (10.8) line-83 step this gives `G₀ ⊆ famG₀`: the
`A_0(M)`-support complement `G₀` is inside the `A(M)`-support complement `famG₀` (the family `(7.4)`
support for `A(M) = typePA ⊆ typePA0 = A_0(M)`). -/
theorem dadeSupport_restrict_subset {A A₁ : Set G} {L : Subgroup G} [Fintype G]
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    (hyp.restrict hA₁A hA₁_norm).dadeSupport ⊆ hyp.dadeSupport := by
  intro g hg
  rw [OddOrder.Peterfalvi.S04.Hypothesis.mem_dadeSupport_iff] at hg ⊢
  obtain ⟨a, h, hh, hconj⟩ := hg
  exact ⟨⟨a.1, hA₁A a.2⟩, h, hh, hconj⟩

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.8), line 83** (the mechanical `(7.5)`+`(10.6.b)` combination): the `ρ`-norm of
`ζ^{τ₁}` for the one-member family `{(M, A(M))}` is bounded by `|A(M)|/|M|` plus the `|G₁|/|G|`-term
`(|famG₀| − |G₀|)/|G|`.

This is Peterfalvi (10.8) 04.12 line 81 → 83: apply the family inequality (7.5)
(`S09.family_inequality` on the now-self-contained `toFamilyHypothesis71`, with the norm-one
`inner_tau1_zeta_self_eq_one`) and drop the `G₀`-part of the sum via the `(10.6.b)` bound
(`sum_zeta_tau1_normSq_ge_card`, using `G₀ ⊆ famG₀` from `dadeSupport_restrict_subset` and
`‖·‖² ≥ 0` on the rest).  Pure real-arithmetic bookkeeping over the family inequality; the genuine
`‖ζ^{τ₁,ρ}‖²` lower bound (7.8.b) and the `|G₁|`-count (TI-counting, §9) are the remaining gates that
turn this into line 87 and the contradiction.  Here `famG₀ = (toFamilyHypothesis71).G0` is the
`A(M)`-support complement and `G₀ = {g ∉ Ã(M), (ord g).Coprime w₁}` the `A_0(M)`-support coprime
subset (`G₀ ⊆ famG₀`). -/
theorem Hypothesis.chiRhoNormSq_zeta_le_line83 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    (hyp.toFamilyHypothesis71).chiRhoNormSq (coh.tau1 params.zeta) 0
      ≤ (Nat.card ↥(typePA M hyp.typeP) : ℝ) / (Nat.card ↥M : ℝ)
        + (Nat.card G : ℝ)⁻¹ * ((Nat.card (hyp.toFamilyHypothesis71).G0 : ℝ)
          - ((Finset.univ.filter (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport
              ∧ (orderOf g).Coprime hyp.w1)).card : ℝ)) := by
  haveI := hyp.finiteG
  -- `F.A 0 = A(M)`, `F.L 0 = M` (structure projections).
  have hA0 : (hyp.toFamilyHypothesis71).A 0 = typePA M hyp.typeP := rfl
  have hL0 : (hyp.toFamilyHypothesis71).L 0 = M := rfl
  -- (7.5) line 81 (single member, `k = 1`).
  have h81 := OddOrder.Peterfalvi.S09.family_inequality (hyp.toFamilyHypothesis71)
    (coh.tau1 params.zeta) (hyp.inner_tau1_zeta_self_eq_one coh)
  rw [Fin.sum_univ_one, hA0, hL0] at h81
  -- `G₀ ⊆ famG₀`: a `g` off the `A_0(M)`-support is off the restricted `A(M)`-support.
  have hsub : Finset.univ.filter (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport
        ∧ (orderOf g).Coprime hyp.w1)
      ⊆ Finset.univ.filter (fun g : G => g ∈ (hyp.toFamilyHypothesis71).G0) := by
    intro g hg
    rw [Finset.mem_filter] at hg ⊢
    refine ⟨Finset.mem_univ g, fun i => ?_⟩
    have hsupp : ((hyp.toFamilyHypothesis71).hyp71 i).hyp.dadeSupport
        ⊆ hyp.dadeData.dade.dadeSupport :=
      dadeSupport_restrict_subset hyp.dadeData.dade Set.subset_union_left _
    exact fun hmem => hg.2.1 (hsupp hmem)
  -- drop the `G₀`-part: `|G₀| ≤ Σ_{G₀} ‖χ‖² ≤ Σ_{famG₀} ‖χ‖²`.
  have hdrop : ((Finset.univ.filter (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport
        ∧ (orderOf g).Coprime hyp.w1)).card : ℝ)
      ≤ ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ (hyp.toFamilyHypothesis71).G0),
          ‖(coh.tau1 params.zeta : G → ℂ) g‖ ^ 2 := by
    refine le_trans (hyp.sum_zeta_tau1_normSq_ge_card hG coh hmu hos hzS hz1 hzconj hδpm hδj) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => by positivity)
  -- rearrange the family inequality.
  have hGinv : (0 : ℝ) ≤ (Nat.card G : ℝ)⁻¹ := by positivity
  have hcS := mul_le_mul_of_nonneg_left hdrop hGinv
  rw [mul_sub] at h81 ⊢
  linarith [h81, hcS]

/-- **Peterfalvi (10.8), the analytic chain** (04.12 p.61, lines 87--99) — the pure-`ℚ` assembly
that turns the §7 norm output (line 87) and the §8 TI-counting bound (lines 89--91) into the
coherence bound `1 − 1/w₁ − 1/u < w₁w₂/|M'|`.

Faithful inputs (with `Mp = |M'|`, `cardH = |H| = |S_F|`, `cardS = |S|`, `u = |U|`, `g1g = |G₁|/|G|`):
* `hA` — the §7 output `w₁/|M'| > 1 − |G₁|/|G| − 1/w₁` (Peterfalvi line 87, from (7.5), (7.8.b),
  (10.6.b), and `|M'| ≥ 2w₁+1`);
* `hB` — the TI-counting bound `|G₁|/|G| ≤ (|H|−1)/|S| + (w₁w₂−w₁−w₂+1)/(w₁w₂)` (from the inclusion
  `G₁ ⊆ (H#)^G ∪ V^G` and the orbit cardinalities, Peterfalvi lines 89--91);
* `hS` — `|S| = |H|·|U|·w₂` (the Type-II partner `S = (H ⋊ U) ⋊ W₂`).

The derivation substitutes `(w₁w₂−w₁−w₂+1)/(w₁w₂) = 1 − 1/w₂ − 1/w₁ + 1/(w₁w₂)` and
`(|H|−1)/|S| ≤ |H|/|S| = 1/(|U|w₂)`, yielding `w₁/|M'| > 1/w₂ − 1/(w₁w₂) − 1/(|U|w₂)`, then
multiplies by `w₂`.  Pure arithmetic over `ℚ`; the genuine character/group inputs are `hA`/`hB`. -/
theorem typeII_coherence_estimate_chain
    {w₁ w₂ u cardH cardS Mp : ℕ} {g1g : ℚ}
    (hw1 : 1 ≤ w₁) (hw2 : 1 ≤ w₂) (hu : 1 ≤ u) (hH : 1 ≤ cardH)
    (hMp : 1 ≤ Mp) (hS : cardS = cardH * u * w₂)
    (hA : 1 - g1g - 1 / (w₁ : ℚ) < (w₁ : ℚ) / (Mp : ℚ))
    (hB : g1g ≤ ((cardH : ℚ) - 1) / (cardS : ℚ)
        + ((w₁ : ℚ) * w₂ - w₁ - w₂ + 1) / ((w₁ : ℚ) * w₂)) :
    (1 : ℚ) - 1 / (w₁ : ℚ) - 1 / (u : ℚ) < (w₁ : ℚ) * w₂ / (Mp : ℚ) := by
  have hw1q : (0 : ℚ) < w₁ := by exact_mod_cast hw1
  have hw2q : (0 : ℚ) < w₂ := by exact_mod_cast hw2
  have huq : (0 : ℚ) < u := by exact_mod_cast hu
  have hHq : (0 : ℚ) < cardH := by exact_mod_cast hH
  have hMpq : (0 : ℚ) < Mp := by exact_mod_cast hMp
  have hw1ne : (w₁ : ℚ) ≠ 0 := ne_of_gt hw1q
  have hw2ne : (w₂ : ℚ) ≠ 0 := ne_of_gt hw2q
  have hune : (u : ℚ) ≠ 0 := ne_of_gt huq
  have hScast : (cardS : ℚ) = (cardH : ℚ) * u * w₂ := by exact_mod_cast hS
  -- `(|H|−1)/|S| ≤ 1/(|U|w₂)` (drop the `−1`, then cancel `|H|`).
  have hHS : ((cardH : ℚ) - 1) / (cardS : ℚ) ≤ 1 / ((u : ℚ) * w₂) := by
    rw [hScast, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos huq hw2q]
  -- `(w₁w₂−w₁−w₂+1)/(w₁w₂) = 1 − 1/w₂ − 1/w₁ + 1/(w₁w₂)`.
  have hident : ((w₁ : ℚ) * w₂ - w₁ - w₂ + 1) / ((w₁ : ℚ) * w₂)
      = 1 - 1 / w₂ - 1 / w₁ + 1 / ((w₁ : ℚ) * w₂) := by
    field_simp
  -- `w₁/|M'| > 1/w₂ − 1/(w₁w₂) − 1/(|U|w₂)`.
  have hKey : 1 / (w₂ : ℚ) - 1 / ((w₁ : ℚ) * w₂) - 1 / ((u : ℚ) * w₂) < (w₁ : ℚ) / Mp := by
    rw [hident] at hB
    linarith [hA, hB, hHS]
  -- multiply by `w₂` and simplify the four products.
  have e1 : (w₂ : ℚ) * (1 / w₂) = 1 := by rw [mul_one_div, div_self hw2ne]
  have e2 : (w₂ : ℚ) * (1 / ((w₁ : ℚ) * w₂)) = 1 / w₁ := by
    rw [mul_one_div, mul_comm (w₁ : ℚ) w₂, div_mul_eq_div_div, div_self hw2ne]
  have e3 : (w₂ : ℚ) * (1 / ((u : ℚ) * w₂)) = 1 / u := by
    rw [mul_one_div, mul_comm (u : ℚ) w₂, div_mul_eq_div_div, div_self hw2ne]
  have e4 : (w₂ : ℚ) * ((w₁ : ℚ) / Mp) = (w₁ : ℚ) * w₂ / Mp := by ring
  have hmul := mul_lt_mul_of_pos_left hKey hw2q
  rw [mul_sub, mul_sub, e1, e2, e3, e4] at hmul
  linarith [hmul]

/-- **Peterfalvi (8.8) enriched: the Type-II partner's Frobenius factor `U` satisfies `|U| ≥ 7`.**

The (8.8) partner `S` — a Type-II maximal subgroup with `|S : [S,S]| = w₂`
(`exists_typeII_maximal_with_w2`) — has `[S,S] = S_F ⋊ U`, and `U ⋊ W₁(S)` is a Frobenius group
with kernel `U` (Peterfalvi (8.4), `S11.typeP_uW1_frobenius`).  Its kernel therefore satisfies
`|U| ≡ 1 (mod |W₁(S)|)` (`card_kernel_modEq_one`), and `|W₁(S)| = |S : [S,S]| = w₂`
(`TypePData.card_W1_eq_derived_index`).  As `|U|` and `w₂` both divide the odd `|G|` and `U ≠ 1`
(the Type-II nontrivial core), the odd-order forcing `two_mul_add_one_le_of_odd_dvd` gives
`|U| ≥ 2w₂+1`; since `w₂` is an odd prime (`w2_prime`), `w₂ ≥ 3` and hence `|U| ≥ 7`.

This is the `∃ u ≥ 7` witness — with its Type-II datum exposed for the `|S| = |S_F|·|U|·w₂` and
TI-counting inputs — that Peterfalvi (10.8)'s coherence estimate
(`typeII_coherence_contradiction_estimate`) consumes; cf. issue 1017 "(8.8) enrich". -/
theorem Hypothesis.exists_typeII_partner_card_U_ge_seven [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ (S : Subgroup G) (dII : TypeIIData S), S ∈ maximalSubgroups G ∧
      ((derivedInG S).subgroupOf S).index = hyp.w2 ∧
      7 ≤ Nat.card ↥dII.typeP.U := by
  obtain ⟨S, hSmax, hSII, hSidx⟩ := hyp.exists_typeII_maximal_with_w2 hG
  obtain ⟨dII⟩ := hSII
  refine ⟨S, dII, hSmax, hSidx, ?_⟩
  -- `|W₁(S)| = |S : [S,S]| = w₂`.
  have hW1card : Nat.card ↥dII.typeP.W1 = hyp.w2 := by
    rw [dII.typeP.card_W1_eq_derived_index]; exact hSidx
  -- `U ≠ 1` (the Type-II nontrivial core), hence `1 < |U|`.
  have hUne : dII.typeP.U ≠ ⊥ := dII.common.1
  have hUlt : 1 < Nat.card ↥dII.typeP.U := (Subgroup.one_lt_card_iff_ne_bot _).mpr hUne
  -- `U ⋊ W₁(S)` is Frobenius; its kernel obeys `|U| ≡ 1 (mod |W₁|)`.
  have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius dII.typeP hUne
  have hmod := hfrob.card_kernel_modEq_one
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at hmod
  -- `|W₁| ∣ |U| − 1`.
  have hdvd : Nat.card ↥dII.typeP.W1 ∣ Nat.card ↥dII.typeP.U - 1 :=
    (Nat.modEq_iff_dvd' hUlt.le).mp hmod.symm
  -- `|U|`, `|W₁|` odd (dividing the odd `|G|`).
  have hUodd : Odd (Nat.card ↥dII.typeP.U) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card dII.typeP.U)
  have hW1odd : Odd (Nat.card ↥dII.typeP.W1) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card dII.typeP.W1)
  -- odd-order forcing: `|U| ≥ 2|W₁|+1 = 2w₂+1`.
  have hge := OddOrder.Peterfalvi.S08.two_mul_add_one_le_of_odd_dvd hW1odd hUodd hdvd hUlt
  rw [hW1card] at hge
  -- `w₂ ≥ 3` (an odd prime), so `|U| ≥ 2·3+1 = 7`.
  have hw2prime : (hyp.w2).Prime := hyp.w2_prime hG
  have hw2odd : Odd hyp.w2 := hW1card ▸ hW1odd
  have hw2ge : 3 ≤ hyp.w2 := by
    have h2 := hw2prime.two_le
    obtain ⟨k, hk⟩ := hw2odd; omega
  omega

/-- **`V`-elements have order divisible by a `|W₁|`-prime** (the (8.10)/(10.8) support
bookkeeping): `v ∈ V = W ∖ (W₁ ∪ W₂)` factors as `v₁·v₂` with `v₁ ∈ W₁ ∖ {1}`
(`TypePData.exists_mul_eq_of_mem_W`; a trivial `W₁`-part would put `v ∈ W₂`), and any prime of
`orderOf v₁ ∣ |W₁|` divides `orderOf v` — a power killing `v` puts `v₁ ^ n ∈ W₁ ⊓ W₂ = ⊥`. -/
theorem exists_prime_dvd_orderOf_of_mem_typePV [Finite G] {M : Subgroup G}
    (data : TypePData M) {v : G} (hv : v ∈ typePV M data) :
    ∃ p : ℕ, p.Prime ∧ p ∣ orderOf v ∧ p ∣ Nat.card ↥data.W1 := by
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  obtain ⟨hvW, hvnot⟩ := hv
  rw [Set.mem_union] at hvnot
  push_neg at hvnot
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ :=
    data.exists_mul_eq_of_mem_W (SetLike.mem_coe.mp hvW)
  have hv₁ne : v₁ ≠ 1 := by
    rintro rfl
    exact hvnot.2 (by simpa using hv₂)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (fun h => hv₁ne (orderOf_eq_one_iff.mp h))
  have hpW1 : p ∣ Nat.card ↥data.W1 := by
    refine hpd.trans ?_
    have h1 : orderOf v₁ = orderOf (⟨v₁, hv₁⟩ : ↥data.W1) :=
      orderOf_injective data.W1.subtype data.W1.subtype_injective ⟨v₁, hv₁⟩
    rw [h1]
    exact orderOf_dvd_natCard _
  have hcomm : Commute v₁ v₂ := by
    haveI := data.W_cyclic
    letI : CommGroup ↥data.W := IsCyclic.commGroup
    have := mul_comm (⟨v₁, hW1le hv₁⟩ : ↥data.W) ⟨v₂, hW2le hv₂⟩
    exact Subtype.ext_iff.mp this
  refine ⟨p, hp, ?_, hpW1⟩
  have hkill : v₁ ^ orderOf (v₁ * v₂) = 1 := by
    have h1 : (v₁ * v₂) ^ orderOf (v₁ * v₂) = 1 := pow_orderOf_eq_one _
    rw [hcomm.mul_pow] at h1
    have hmem : v₁ ^ orderOf (v₁ * v₂) ∈ data.W1 ⊓ data.W2 := by
      refine ⟨data.W1.pow_mem hv₁ _, ?_⟩
      have heq : v₁ ^ orderOf (v₁ * v₂) = (v₂ ^ orderOf (v₁ * v₂))⁻¹ :=
        eq_inv_of_mul_eq_one_right (((hcomm.pow_pow _ _).symm.eq).trans h1)
      rw [heq]
      exact data.W2.inv_mem (data.W2.pow_mem hv₂ _)
    rwa [disjoint_iff.mp (typePData_disjoint_W1_W2 data), Subgroup.mem_bot] at hmem
  exact hpd.trans (orderOf_dvd_of_pow_eq_one hkill)

/-- **The `(S_F#)^G` union bound of the (10.8) TI-counting** (p. 60 line 91, `≤`-form): the
conjugacy saturation of the kernel sharp-set of a type-`P` maximal `S` has at most
`(|S_F| − 1)·[G : S]` elements.  `S` stabilises `H# = H ∖ {1}` under conjugation (`H ⊴ S`), so
the union bound `ncard_conjClassSet_le` applies with `L = S`; no TI-property is needed for the
upper bound. -/
theorem ncard_conjClassSet_sharp_H_le [Finite G] {S : Subgroup G} (data : TypePData S) :
    (conjClassSet ((data.H : Set G) \ {1})).ncard ≤ (Nat.card ↥data.H - 1) * S.index := by
  have hHle : data.H ≤ S := data.H_le.trans (Subgroup.map_subtype_le _)
  have hstab : ∀ l ∈ S, ∀ t ∈ (data.H : Set G) \ {1},
      l * t * l⁻¹ ∈ (data.H : Set G) \ {1} := by
    rintro l hl t ⟨htH, htne⟩
    have htH' : t ∈ data.H := htH
    have hnorm := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal S
    have hconj : l * t * l⁻¹ ∈ maxNilpotentNormalHall S := by
      have hmem := hnorm.conj_mem ⟨t, hHle htH'⟩
        (Subgroup.mem_subgroupOf.mpr (data.H_eq ▸ htH')) ⟨l, hl⟩
      exact Subgroup.mem_subgroupOf.mp hmem
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, data.H_eq]; exact hconj
    · intro h1
      apply htne
      rw [Set.mem_singleton_iff]
      have := congrArg (fun z => l⁻¹ * z * l) (Set.mem_singleton_iff.mp h1)
      simpa [mul_assoc] using this
  have hle := OddOrder.GroupTheory.ncard_conjClassSet_le (L := S) hstab
  have hA : ((data.H : Set G) \ {1}).ncard = Nat.card ↥data.H - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (by exact one_mem data.H),
      ← Nat.card_coe_set_eq]
    rfl
  rwa [hA] at hle

/-- **Type-`P` order factorization** `|M| = |M_F|·|U|·|W₁|`.  The type-`P` decomposition is a double
semidirect product `M = (H ⋊ U) ⋊ W₁`: `W₁` complements the derived subgroup `M' = [M,M]` in `M`
(`M_complement`, `|M| = |M'|·|W₁|`), and `U` complements the Fitting kernel `H = M_F` in `M'`
(`derived_complement`, `|M'| = |H|·|U|`).  For the Type-II partner `S` with `|W₁(S)| = w₂` this is
the `|S| = |S_F|·|U|·w₂` input (`hS`) to Peterfalvi (10.8)'s coherence estimate. -/
theorem typePData_card_eq_H_mul_U_mul_W1 [Finite G] {M : Subgroup G} (data : TypePData M) :
    Nat.card ↥M = Nat.card ↥data.H * Nat.card ↥data.U * Nat.card ↥data.W1 := by
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `|M'|·|W₁| = |M|` (the `M = M' ⋊ W₁` complement).
  have h1 : Nat.card ↥(derivedInG M) * Nat.card ↥data.W1 = Nat.card ↥M := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.W1_le).toEquiv]
    exact data.M_complement.card_mul
  -- `|H|·|U| = |M'|` (the `M' = H ⋊ U` complement).
  have h2 : Nat.card ↥data.H * Nat.card ↥data.U = Nat.card ↥(derivedInG M) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.H_le).toEquiv,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.U_le).toEquiv]
    exact data.derived_complement.card_mul
  calc Nat.card ↥M = Nat.card ↥(derivedInG M) * Nat.card ↥data.W1 := h1.symm
    _ = Nat.card ↥data.H * Nat.card ↥data.U * Nat.card ↥data.W1 := by rw [← h2]

open scoped Classical FiniteInduce in
open OddOrder.Peterfalvi.S09 in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (10.8), line 87 lower bound — the (7.8.b) ρ-norm bound for `ζ^{τ₁}`**:
`‖ζ^{τ₁,ρ}‖² ≥ 1 − ŵ₁/|M'|`.

This is Peterfalvi (7.8.b) specialised to the coherent extension `τ₁` of `ζ ∈ 𝒮` in the present
type-`P` `Hypothesis M`.  It is the M-side analogue of the §14 pattern
`MHypothesis.rhoNormSq_ge_lower` (`S16_NonExistenceG.lean`), which couples the `ρ`-norm to the
(7.8.b) Dade-integral engine `zetaNuRhoNormSqGeOfDade` (`S09_CertificateDischarge.lean`) via a
`Hypothesis78`-for-`M` certificate (`H = M'`, `ν = coh.tau1`).  Together with the proven line-83
**upper** bound (`chiRhoNormSq_zeta_le_line83`) and the strict `|A(M)|/|M| < 1/w₁`
(`card_typePA_div_card_lt_inv_w1`) this closes the (10.8) estimate's `hA` (line 87).

**Genuine, ungated lane-a gate** (the last §7 char-theoretic input to `hA`): the honest route is the
S16 `chiRhoNormSq_eq_zetaNuRhoNormSq` coupling ported to type-`P` `M`; it does **not** depend on the
(10.7) partner Frobenius structure (that gates only `hB`).  See
`notes/peterfalvi/s10_7_derived_frobenius.md` (2026-07-08 update²).

**Proof (type-`P` port of S16 `exists_M_hypothesis78`)**: assemble a §7 Dade certificate
`S09.Hypothesis78 G (typePA M) M` with `H = M' = derivedInG M`, `K = M'.subgroupOf M`, distinguished
`ζ_0 = Ind_K θ_0 = params.zeta` (placed by `exists_placed_induced_family`), and `ν = coh.tau1`, then
feed the (7.8.b) Dade-integral engine `zetaNuRhoNormSqGeOfDade`.  The `(7.8.a)` agreement `hagree`
bridges the *restricted* Dade map `toHypothesis71.τ` (over `A(M)`) to the *full* map
(`coherence_hagree_dadeMap`, over `A_0(M)`) via `S04.FullDadeIsometryData.restrict_apply`; the
`ζ_0^ν ⊥ 1_G` fact is `coherence_extension_orthogonal_constOne` (using the conjugate member `ζ̄_0`);
`2e+1 ≤ h` is `card_derived_ge`.  The engine bound `1 − e/h ≤ ‖ζ_0^{νρ}‖²` is then rewritten to the
goal via `e = w₁`, `h = |M'|`, and the `chiRhoNormSq = zetaNuRhoNormSq` bridge (mirroring
S16 `chiRhoNormSq_eq_zetaNuRhoNormSq`). -/
theorem Hypothesis.chiRhoNormSq_zeta_ge_line78 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    (1 : ℝ) - (hyp.w1 : ℝ) / (Nat.card ↥(derivedInG M) : ℝ)
      ≤ (hyp.toFamilyHypothesis71).chiRhoNormSq (coh.tau1 params.zeta) 0 := by
  haveI := hyp.finiteG
  classical
  -- **Setup**: `H = M' = derivedInG M`, `K = M'.subgroupOf M ⊴ M`.
  have hHL : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hKnormal0 : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  set K : Subgroup ↥M := (derivedInG M).subgroupOf M with hKdef
  haveI : K.Normal := hKnormal0
  have hHnorm : ∀ (l : ↥M) ⦃h : G⦄, h ∈ derivedInG M →
      (↑l : G) * h * (↑l : G)⁻¹ ∈ derivedInG M := by
    intro l h hh
    have hhM : h ∈ M := hHL hh
    have hmem : (⟨h, hhM⟩ : ↥M) ∈ K := (Subgroup.mem_subgroupOf).mpr hh
    have hconj := hKnormal0.conj_mem ⟨h, hhM⟩ hmem l
    rw [Subgroup.mem_subgroupOf] at hconj
    simpa using hconj
  have hAH : typePA M hyp.typeP = (derivedInG M : Set G) \ {1} :=
    typePA_eq_sharpSubgroup_derivedInG M hyp.typeP
  -- `M`-stability of `A(M) = typePA` (the input to `toHypothesis71`).
  have hnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ typePA M hyp.typeP →
      (↑l : G) * a * (↑l : G)⁻¹ ∈ typePA M hyp.typeP := fun l a ha =>
    ((Subgroup.mem_set_normalizer_iff).mp (hyp.le_normalizer_typePA l.2) a).mp ha
  -- **Placed induced family** with the distinguished `ζ_0 = Ind_K θ_0 = params.zeta`.
  obtain ⟨θz, hθz_ne, hθz_eq⟩ := hzS
  have hχ_range : params.zeta ∈ Set.range
      (fun φ : IrreducibleCharacter ↥K =>
        ClassFunction.induce K (φ : ClassFunction ↥K ℂ)) :=
    ⟨θz, hθz_eq.symm⟩
  have hχ_ne : params.zeta ≠ ClassFunction.induce K
      (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) := by
    rw [hθz_eq]; exact induce_ne_trivialChar_induce K θz hθz_ne
  obtain ⟨n, θ, ind1H, hind1H, hθ0eq, htriv, hinj, hcover⟩ :=
    exists_placed_induced_family K params.zeta hχ_range hχ_ne
  have hne_triv : ∀ i : Fin (n + 1), i ≠ ind1H →
      θ i ≠ trivialIrreducibleCharacter ↥K := by
    intro i hi hcontra
    apply hi; apply hinj
    show ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
      = ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
    rw [hcontra, htriv]
  have hSmem : ∀ i : Fin (n + 1), i ≠ ind1H →
      ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) ∈ hyp.Sset :=
    fun i hi => ⟨θ i, hne_triv i hi, rfl⟩
  -- **Degrees**: `d i = θ_i(1)`, `Ind(θ_0)(1) = [M:K] = w₁`, and `|M| = w₁·|M'|`.
  have hKindex : K.index = hyp.w1 := by
    rw [hKdef, Hypothesis.w1, Hypothesis.W1]; exact hyp.typeP.card_W1_eq_derived_index.symm
  have hcardM : Nat.card ↥M = hyp.w1 * Nat.card ↥(derivedInG M) := by
    have hsub : Nat.card ↥K = Nat.card ↥(derivedInG M) := by
      rw [hKdef]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
    rw [← Subgroup.index_mul_card K, hKindex, hsub]
  let d : Fin (n + 1) → ℂ := fun i => (θ i : ClassFunction ↥K ℂ) (1 : ↥K)
  have hd : ∀ i, d i = (θ i : ClassFunction ↥K ℂ) (1 : ↥K) := fun _ => rfl
  have hz0eq : ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥M)
      = params.zeta 1 := by rw [hθ0eq]
  have hdeg0 : ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥M)
      = (K.index : ℂ) := by
    rw [hz0eq, hz1, hKindex]
  have hdeg : ∀ i, ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) (1 : ↥M)
      = d i * ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥M) := by
    intro i
    rw [ClassFunction.induce_apply_one K (θ i : ClassFunction ↥K ℂ), hdeg0, hd i]; ring
  have hdeg_match : ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥M)
      = ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ) (1 : ↥M) := by
    rw [hdeg0, htriv]
    exact (induce_trivialChar_apply_eq_index K (Subgroup.one_mem _)).symm
  -- **Support** of the difference vectors in `A(M) = (M')#` and in `A_0(M)`.
  have psi_support : ∀ i, (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typePA M hyp.typeP) M := by
    intro i
    refine (induce_diff_support (θ i) (θ 0) (d i) (hdeg i)).trans ?_
    intro x hx
    rw [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff] at hx
    exact (mem_supportInSubgroup_sharp_subgroupOf_iff (derivedInG M) hAH x).mpr ⟨hx.1, hx.2⟩
  have hsupp_full : ∀ i, (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := by
    intro i
    refine (psi_support i).trans ?_
    intro x hx
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hx ⊢
    exact Set.mem_union_left _ hx
  have hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥K := htriv
  -- The restricted Dade isometry certificate for `H71.τ = toHypothesis71.τ`.
  have hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := M)
      hyp.toHypothesis71.τ :=
    ((hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).restrict Set.subset_union_left
      hnorm).toDadeIsometryData.isDadeIsometry
  -- **`ν`-isometry** on the family (`ν = coh.tau1 = coherent extension`).
  have hnu_isometry : ∀ i j : Fin (n + 1), i ≠ ind1H → j ≠ ind1H →
      ClassFunction.inner (coh.tau1 (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
          (coh.tau1 (ClassFunction.induce K (θ j : ClassFunction ↥K ℂ)))
        = ClassFunction.inner (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
          (ClassFunction.induce K (θ j : ClassFunction ↥K ℂ)) :=
    fun i j hi hj => coherence_extension_inner_eq_on_family coh.coherent (hSmem i hi) (hSmem j hj)
  -- **(7.8.a) agreement** — the restricted-vs-full Dade-map bridge.
  have hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      hyp.toHypothesis71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
          - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩
        = coh.tau1 (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
          - d i • coh.tau1 (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)) := by
    intro i hi0 hi_ind
    obtain ⟨deg_i, -, hdeg_i_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (θ i)
    have hcohag := coherence_hagree_dadeMap hyp.dadeData.dade hyp.hconj coh.coherent
      (hSmem i hi_ind) (hSmem 0 (Ne.symm hind1H)) (m0 := 1) (mi := deg_i) (by norm_num)
      (by rw [hd i, hdeg_i_eq, Nat.cast_one, div_one]) (hsupp_full i)
    have hbridge : hyp.toHypothesis71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
          - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩
        = (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).toDadeMap
          ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
            - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ),
            (ClassFunction.mem_supportedSubmodule).mpr (hsupp_full i)⟩ := by
      show ((hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).restrict Set.subset_union_left
          hnorm).toDadeMap ⟨_, psi_support i⟩ = _
      rw [OddOrder.Peterfalvi.S04.FullDadeIsometryData.restrict_apply]
      exact congrArg _ (Subtype.ext rfl)
    rw [hbridge]; exact hcohag
  -- **Assemble** the (7.8) Dade certificate.
  set H78 := hypothesis78OfDade hyp.toHypothesis71 hτ (derivedInG M) hHL hHnorm hAH θ hinj hcover
    d psi_support hdeg ind1H hind1H hzeta_ind1H hdeg_match coh.tau1 hnu_isometry hagree
    with hH78def
  -- `e = [M:M'] = w₁`, `h = |M'|`.
  have hci : H78.complementIndex = hyp.w1 := by
    have hcieq : H78.complementIndex = Nat.card ↥M / Nat.card ↥(derivedInG M) := rfl
    rw [hcieq, hcardM, Nat.mul_div_cancel _ Nat.card_pos]
  have hko : H78.kernelOrder = Nat.card ↥(derivedInG M) := rfl
  have hsmall : H78.smallIndex := by
    show 2 * H78.complementIndex + 1 ≤ H78.kernelOrder
    rw [hci, hko]
    have hMp := hyp.card_derived_ge hG
    have hw2 : 0 < hyp.w2 := Nat.card_pos
    calc 2 * hyp.w1 + 1 = (2 * hyp.w1 + 1) * 1 := (mul_one _).symm
      _ ≤ (2 * hyp.w1 + 1) * hyp.w2 := Nat.mul_le_mul_left _ hw2
      _ ≤ Nat.card ↥(derivedInG M) := hMp
  -- **(7.8.a) coefficient** `a`.
  obtain ⟨a, ha⟩ := exists_betaDecomp_a H78
    (Submodule.sub_mem _
      (ClassFunction.induce_mem_ZIrr K (θ ind1H).property.mem_ZIrr)
      (ClassFunction.induce_mem_ZIrr K (θ 0).property.mem_ZIrr))
    (coh.coherent.extension_mem_ZIrr _ (Submodule.subset_span (hSmem 0 (Ne.symm hind1H))))
  -- **`ζ_0^ν ⊥ 1_G`** via the conjugate member `ζ̄_0 = Ind_K θ̄_0 ∈ S`.
  obtain ⟨θ0', hθ0'coe⟩ : ∃ t : IrreducibleCharacter ↥K,
      (t : ClassFunction ↥K ℂ) = (θ 0 : ClassFunction ↥K ℂ).conj :=
    ⟨⟨(θ 0 : ClassFunction ↥K ℂ).conj, (θ 0).isIrreducible.conj⟩, rfl⟩
  have hθ0_ne : θ 0 ≠ trivialIrreducibleCharacter ↥K := hne_triv 0 (Ne.symm hind1H)
  have hθ0'_ne : θ0' ≠ trivialIrreducibleCharacter ↥K := by
    intro h
    apply hθ0_ne
    have hcoe : (θ 0 : ClassFunction ↥K ℂ).conj = trivialClassFunction ↥K := by
      rw [← hθ0'coe]
      simpa using congrArg (fun c : IrreducibleCharacter ↥K => (c : ClassFunction ↥K ℂ)) h
    apply Subtype.ext
    show (θ 0 : ClassFunction ↥K ℂ) = trivialClassFunction ↥K
    rw [← ClassFunction.conj_conj (θ 0 : ClassFunction ↥K ℂ), hcoe]
    exact trivialClassFunction_isReal
  have hnorm0 : ClassFunction.inner (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
      (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)) = 1 := by
    rw [hθ0eq]
    simpa using irreducibleCharacter_inner_eq_ite
      (⟨params.zeta, params.zeta_irreducible⟩ : IrreducibleCharacter ↥M)
      (⟨params.zeta, params.zeta_irreducible⟩ : IrreducibleCharacter ↥M)
  have hnorm0' : ClassFunction.inner (ClassFunction.induce K (θ0' : ClassFunction ↥K ℂ))
      (ClassFunction.induce K (θ0' : ClassFunction ↥K ℂ)) = 1 := by
    rw [hθ0'coe, ← ClassFunction.induce_conj, inner_conj_conj, hnorm0, star_one]
  have hne_zeta : (⟨params.zeta, params.zeta_irreducible⟩ : IrreducibleCharacter ↥M)
      ≠ ⟨params.zeta.conj, params.zeta_irreducible.conj⟩ := by
    intro h
    exact hzconj
      (congrArg (fun c : IrreducibleCharacter ↥M => (c : ClassFunction ↥M ℂ)) h).symm
  have horth : ClassFunction.inner (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
      (ClassFunction.induce K (θ0' : ClassFunction ↥K ℂ)) = 0 := by
    rw [hθ0'coe, ← ClassFunction.induce_conj, hθ0eq]
    have hite := irreducibleCharacter_inner_eq_ite
      (⟨params.zeta, params.zeta_irreducible⟩ : IrreducibleCharacter ↥M)
      (⟨params.zeta.conj, params.zeta_irreducible.conj⟩ : IrreducibleCharacter ↥M)
    rw [if_neg hne_zeta] at hite
    simpa using hite
  have hdeg' : ClassFunction.induce K (θ0' : ClassFunction ↥K ℂ) (1 : ↥M)
      = 1 * ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥M) := by
    rw [one_mul, ClassFunction.induce_apply_one, ClassFunction.induce_apply_one]
    congr 1
    rw [hθ0'coe, ClassFunction.conj_apply]
    obtain ⟨m, -, hm⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (θ 0)
    rw [hm, star_natCast]
  have hsupp : (ClassFunction.induce K (θ0' : ClassFunction ↥K ℂ)
        - ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆ hyp.A0 := by
    have hds := induce_diff_support θ0' (θ 0) 1 hdeg'
    rw [one_smul] at hds
    intro x hx
    have hxd := hds hx
    rw [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff] at hxd
    have hmem := (mem_supportInSubgroup_sharp_subgroupOf_iff (derivedInG M) hAH x).mpr
      ⟨hxd.1, hxd.2⟩
    show x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hmem ⊢
    exact Set.mem_union_left _ hmem
  have hζ0_1 : ClassFunction.inner (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
      (Hypothesis71.constOne ↥M) = 0 := inner_induce_constOne_eq_zero K (θ 0) hθ0_ne
  have hζ0'_1 : ClassFunction.inner (ClassFunction.induce K (θ0' : ClassFunction ↥K ℂ))
      (Hypothesis71.constOne ↥M) = 0 := inner_induce_constOne_eq_zero K θ0' hθ0'_ne
  have hτ_smul : ∀ (c : ℂ) (x : ClassFunction ↥M ℂ), hyp.tau (c • x) = c • hyp.tau x :=
    dadeIntegralCharacterMap_smul_complex hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)
  have htau1 : ∀ φ : ClassFunction ↥M ℂ, φ.support ⊆ hyp.A0 →
      ClassFunction.inner (hyp.tau φ) (Hypothesis71.constOne G)
        = ClassFunction.inner φ (Hypothesis71.constOne ↥M) := by
    intro φ hφ
    rw [show hyp.tau φ = hyp.dadeData.dade.dadeMap (k := ℂ)
        ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩ from
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) hφ]
    exact inner_tau_supported_constOne
      ({ hyp := hyp.dadeData.dade
         τ := hyp.dadeData.dade.dadeMap (k := ℂ)
         isDadeMap := hyp.dadeData.dade.isDadeMap_dadeMap
         hConjInvariant := hyp.hconj } : Hypothesis71 G (typePA0 M hyp.typeP) M)
      ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩
  have hζ0'mem : ClassFunction.induce K (θ0' : ClassFunction ↥K ℂ) ∈ hyp.Sset :=
    ⟨θ0', hθ0'_ne, rfl⟩
  have hzeta0nu : ClassFunction.inner
      (coh.tau1 (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)))
      (Hypothesis71.constOne G) = 0 :=
    coherence_extension_orthogonal_constOne coh.coherent hτ_smul htau1
      (hSmem 0 (Ne.symm hind1H)) hζ0'mem hnorm0 hnorm0' horth hsupp hζ0_1 hζ0'_1
  -- **The (7.8.b) engine bound** `1 − e/h ≤ ‖ζ_0^{νρ}‖²`.
  have hbound : (1 : ℝ) - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)
      ≤ H78.zetaNuRhoNormSq :=
    zetaNuRhoNormSqGeOfDade hyp.toHypothesis71 hτ (derivedInG M) hHL hHnorm hAH θ hinj hcover d
      psi_support hdeg ind1H hind1H hzeta_ind1H hdeg_match coh.tau1 hnu_isometry hagree hzeta0nu
      hnorm0 a ha hsmall
  -- **Norm bridge** `chiRhoNormSq = zetaNuRhoNormSq` (mirrors S16's norm-bridge lemma).
  have hpsi : coh.tau1 params.zeta = H78.nu (H78.hyp76.zeta H78.zetaDistinct) := by
    show coh.tau1 params.zeta = coh.tau1 (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
    rw [hθ0eq]
  have hnorm_eq : (hyp.toFamilyHypothesis71).chiRhoNormSq (coh.tau1 params.zeta) 0
      = H78.zetaNuRhoNormSq := by
    have hH71 : H78.hyp76.hyp71 = hyp.toHypothesis71 := rfl
    have hcf : ((hyp.toFamilyHypothesis71).hyp71 0).chiRhoCF (coh.tau1 params.zeta)
        = H78.zetaNuRho := by
      show hyp.toHypothesis71.chiRhoCF (coh.tau1 params.zeta) = H78.zetaNuRho
      rw [Hypothesis78.zetaNuRho, hH71, ← hpsi]
    simp only [FamilyHypothesis71.chiRhoNormSq, Hypothesis78.zetaNuRhoNormSq, hcf]
    congr 1
  rw [hnorm_eq, ← hci, ← hko]
  exact hbound

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.8), norm-counting estimate** (the §7 analytic heart, the `hbound` input to
`typeII_noncoherence_arithmetic`).

Under the coherence assumption, Peterfalvi's character-sum estimate produces a Type-II partner `S`
(Theorem (8.8)) whose Frobenius factor `U` satisfies `|U| ≥ 2w₂+1 ≥ 7` (as `UW₂` is Frobenius),
together with the inequality `1 − 1/w₁ − 1/|U| < w₁w₂/|M'|`.  The derivation combines:
* the family inequality (7.5) (`S09.family_inequality`) over `G₀ ∪ G₁`;
* (10.6.b) (`tau1_values_and_norm_bound`, **proven**) bounding the character values off `Ã(M)`;
* (7.8.b) giving `‖χ^ρ‖² ≥ 1 − ŵ₁/|M'|`;
* the TI-counting `G₁ ⊆ (H#)^G ∪ V^G` (using (8.6.a)/(8.11)/(10.7) for the partner `S`).

Isolated here as the single remaining genuine character-theoretic gate of (10.8) (lane-b W3): the
arithmetic closer and the structural bound `|M'| ≥ (2w₁+1)w₂` are discharged separately.  The `u`
is the partner's `|U|`; bundled existentially because (10.8) only consumes `∃ u ≥ 7` with the bound.
See `notes/peterfalvi/s12_10_8_noncoherence.md`. -/
theorem typeII_coherence_contradiction_estimate [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params) :
    ∃ u : ℕ, 7 ≤ u ∧
      (1 : ℚ) - 1 / (hyp.w1 : ℚ) - 1 / (u : ℚ)
        < (hyp.w1 : ℚ) * (hyp.w2 : ℚ) / (Nat.card ↥(derivedInG M) : ℚ) := by
  classical
  -- Reconstruct the (10.3) character parameters `params'` supplying the 7 grid/`ζ` properties that
  -- the line-83/(7.8.b) bounds consume; the coherence datum `coh.coherent` is params-independent.
  -- The estimate carries no explicit `[Invertible …]` binders, so `coh` (and hence `coh'`) uses the
  -- `FiniteInduce`-scoped instances that the line-83/(7.8.b) lemmas expect.
  obtain ⟨params', hmu, hos, hzS, hz1, hzconj, hδpm, hδj⟩ := hyp.exists_charParameters_full hG
  let coh' : CoherentHypothesis hyp params' := ⟨coh.coherent⟩
  -- The Type-II partner `S` (Theorem (8.8)) with `|U| ≥ 7` and `|S : [S,S]| = w₂`.
  obtain ⟨S, dII, hSmax, hSidx, hU7⟩ := hyp.exists_typeII_partner_card_U_ge_seven hG
  refine ⟨Nat.card ↥dII.typeP.U, hU7, ?_⟩
  -- `|W₁(S)| = w₂` and the partner order factorization `|S| = |S_F|·|U|·w₂` (input `hS`).
  have hW1card : Nat.card ↥dII.typeP.W1 = hyp.w2 := by
    rw [dII.typeP.card_W1_eq_derived_index]; exact hSidx
  have hS_struct : Nat.card ↥S = Nat.card ↥dII.typeP.H * Nat.card ↥dII.typeP.U * hyp.w2 := by
    rw [typePData_card_eq_H_mul_U_mul_W1 dII.typeP, hW1card]
  -- the proven line-83 **upper** bound and the (7.8.b) **lower** bound for `‖ζ^{τ₁,ρ}‖²`.
  have h83 := hyp.chiRhoNormSq_zeta_le_line83 hG coh' hmu hos hzS hz1 hzconj hδpm hδj
  have h78 := hyp.chiRhoNormSq_zeta_ge_line78 hG coh' hmu hos hzS hz1 hzconj hδpm hδj
  -- the concrete `|G₁|/|G|` term (the line-83 middle term), over `ℚ`.
  set g1g : ℚ := ((Nat.card (hyp.toFamilyHypothesis71).G0 : ℚ)
      - ((Finset.univ.filter (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport
          ∧ (orderOf g).Coprime hyp.w1)).card : ℚ)) / (Nat.card G : ℚ) with hg1g_def
  -- `hA` (line 87): line-83 (upper) + (7.8.b) (lower) + `|A(M)|/|M| < 1/w₁` (proven), over `ℝ`,
  -- reflected to `ℚ`.
  have hA : (1 : ℚ) - g1g - 1 / (hyp.w1 : ℚ) < (hyp.w1 : ℚ) / (Nat.card ↥(derivedInG M) : ℚ) := by
    have hpaR : (Nat.card ↥(typePA M hyp.typeP) : ℝ) / (Nat.card ↥M : ℝ) < 1 / (hyp.w1 : ℝ) := by
      have h := (Rat.cast_lt (K := ℝ)).mpr hyp.card_typePA_div_card_lt_inv_w1
      push_cast at h; exact h
    have hg1gR : (g1g : ℝ) = (Nat.card G : ℝ)⁻¹ * ((Nat.card (hyp.toFamilyHypothesis71).G0 : ℝ)
        - ((Finset.univ.filter (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport
            ∧ (orderOf g).Coprime hyp.w1)).card : ℝ)) := by
      rw [hg1g_def]; push_cast; rw [div_eq_inv_mul]
    rw [← Rat.cast_lt (K := ℝ)]
    push_cast
    linarith [h78, h83, hpaR, hg1gR]
  -- `hB` (TI-counting): `|G₁|/|G| ≤ (|S_F|−1)/|S| + (w₁w₂−w₁−w₂+1)/(w₁w₂)`.
  -- The remaining genuine gate — the inclusion `G₁ ⊆ (S_F#)^G ∪ V^G` and its orbit cardinalities
  -- (Peterfalvi (10.8) lines 89--91), which use the Type-II partner Frobenius structure (10.7)
  -- (`typeII_derived_frobenius`) + (8.6.a)/(8.11).  See `notes/peterfalvi/s10_7_derived_frobenius.md`.
  have hB : g1g ≤ ((Nat.card ↥dII.typeP.H : ℚ) - 1) / (Nat.card ↥S : ℚ)
      + ((hyp.w1 : ℚ) * hyp.w2 - hyp.w1 - hyp.w2 + 1) / ((hyp.w1 : ℚ) * hyp.w2) := by
    sorry
  -- assemble via the proven pure-`ℚ` analytic chain (lines 87--99).
  have hw1 : 1 ≤ hyp.w1 := Nat.card_pos
  have hw2 : 1 ≤ hyp.w2 := Nat.card_pos
  have hu : 1 ≤ Nat.card ↥dII.typeP.U := by omega
  have hH : 1 ≤ Nat.card ↥dII.typeP.H := Nat.card_pos
  have hMp : 1 ≤ Nat.card ↥(derivedInG M) := Nat.card_pos
  exact typeII_coherence_estimate_chain hw1 hw2 hu hH hMp hS_struct hA hB

open scoped FiniteInduce in
/-- **Peterfalvi (10.8)**: under Hypothesis (10.1), the character family `S` is
not coherent.

The proof is Peterfalvi's contradiction, assembled from its three faithful pieces: assuming `S`
coherent, build the `(10.4)` coherent-extension datum (`CoherentHypothesis`, with the `(10.3)`
parameters from `w2_prime_and_parameter_independence`); the structural bound
`|M'| ≥ (2w₁+1)w₂` (`card_derived_ge`), the norm-counting estimate
`1 − 1/w₁ − 1/|U| < w₁w₂/|M'|` with `|U| ≥ 7` (`typeII_coherence_contradiction_estimate`), and the
pure-`ℚ` arithmetic contradiction (`typeII_noncoherence_arithmetic`) together give `False`. -/
theorem S_not_coherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) :
    ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0) := by
  rintro ⟨hcoh⟩
  obtain ⟨params, -⟩ := w2_prime_and_parameter_independence hG hyp
  let coh : CoherentHypothesis hyp params := ⟨hcoh⟩
  -- structural inputs to the (10.8) arithmetic.  `w₁ ≥ 3`: `w₁ = |W₁|` is odd (divides `|G|`) and
  -- `> 1` (`W₁ ≠ ⊥`), hence `≥ 3` — derived without the `FiniteInduce`-scoped `tic` to avoid the
  -- explicit-vs-scoped `Fintype G` clash.
  have hw1odd : Odd hyp.w1 :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.W1)
  have hw1gt : 1 < hyp.w1 :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
  have hw1 : 3 ≤ hyp.w1 := by
    obtain ⟨k, hk⟩ := hw1odd; omega
  have hw2 : 1 ≤ hyp.w2 := Nat.card_pos
  have hMp : (2 * hyp.w1 + 1) * hyp.w2 ≤ Nat.card ↥(derivedInG M) := hyp.card_derived_ge hG
  obtain ⟨u, hu7, hbound⟩ := typeII_coherence_contradiction_estimate hG coh
  exact typeII_noncoherence_arithmetic hw1 hu7 hw2 hMp hbound

end OddOrder.Peterfalvi.S12
