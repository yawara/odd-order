/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_Section9Counts

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

/-- **Peterfalvi (10.7)**: if `S` is a maximal subgroup of type II, then `[S,S] = S^{(1)}` is a
Frobenius group with kernel `S_F` (Coq `Frob_der1_type2`, `PFsection10.v:549`).

**Status (genuine partial reduction).**  The datum is built with the *genuine* kernel `S_F` and
complement `U` — the type-`P` decomposition `M' = S_F ⋊ U` (`TypePData.derived_complement`) — and
**four of the five `IsFrobeniusGroup` fields are honestly proven**: `isNormal` (`S_F ⊴ [S,S]`,
since `S ≤ N_G(S_F)` and `[S,S] ≤ S`), `isComplement` (verbatim `derived_complement`), and both
nontriviality clauses; the `kernel_is_SF` identity is likewise proven.  The **sole residual
`sorry`** is `conj_frobenius`: that the *full* complement `U` acts fixed-point-freely on `S_F`.

This residual is NOT a structural transport.  The type-`F` datum of `[S,S]`
(`TypeIIData.derived_typeF` / `isTypeF_derivedInG_of_isTypeP2`) yields only the *sub-complement*
`U₀`-Frobenius `frobenius_HU0`, and `U` is not cyclic in general (`U₀ = U` fails, so
`typeF_frobenius_of_card_eq_exponent` does not apply).  Peterfalvi's proof (mmd §10) is the
character-theoretic contradiction: were `HU` not Frobenius, (9.10)/(9.8.b)/(9.9.b) give a reducible
`ν_r ∈ 𝒯` and an irreducible `λ ∈ 𝒯 ∩ Irr S` of equal degree; by (5.7) the 4-element family
`{λ,λ̄,ν_r,ν̄_r}` is coherent, and (5.8) plus the Dade orthogonality (from (8.10)/(8.15)/(8.18.b) +
Hyp (10.1)) force a contradiction.  The coherence of that `T2` family is the (9.11) assembly flagged
open in `S07_Subcoherent` (only the uniform-degree base case is landed; the non-Galois
pair-adjoining induction is not).  Tracking: issue 1017.  Sibling sorry for the same content:
`exceptional_case_frobenius_realization` (S11, case-B/`H₀ = 1`-gated). -/
theorem typeII_derived_frobenius [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSType : IsTypeII S) :
    ∃ data : DerivedFrobeniusData S, data.kernel_is_SF := by
  classical
  obtain ⟨td⟩ := hSType
  -- `[S,S] = derivedInG S ≤ S`.
  have hM'le : derivedInG S ≤ S := Subgroup.map_subtype_le _
  -- `H = S_F` is normal in `[S,S]`: `S ≤ N_G(S_F)` (as `S_F = maxNilpotentNormalHall S`) and
  -- `[S,S] ≤ S`.
  have hHn : (td.typeP.H.subgroupOf (derivedInG S)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer td.typeP.H_le).mpr ?_
    have hnS : S ≤ Subgroup.normalizer (td.typeP.H : Set G) := by
      rw [td.typeP.H_eq]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer S
    exact hM'le.trans hnS
  -- `H = S_F ≠ 1`: read off the type-`F` structure of `[S,S]`, whose Fitting kernel is `S_F`.
  have hHne : td.typeP.H ≠ ⊥ := by
    have h := td.derived_typeF.some.H_nontrivial
    rwa [td.derived_typeF.some.H_eq, td.derived_fitting_eq] at h
  -- `U ≠ 1`: the (8.6) nontrivial core carried by type II.
  have hUne : td.typeP.U ≠ ⊥ := td.common.1
  -- Both factors remain nontrivial as subgroups of `[S,S]` (each is `≤ derivedInG S`).
  have hkne : td.typeP.H.subgroupOf (derivedInG S) ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_of_le_left td.typeP.H_le]; exact hHne
  have hcne : td.typeP.U.subgroupOf (derivedInG S) ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_of_le_left td.typeP.U_le]; exact hUne
  -- Assemble the Frobenius datum.  Four of the five fields are genuine; the fixed-point-free
  -- `conj_frobenius` is the single honest residual (see the theorem docstring).
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG S)
      (td.typeP.H.subgroupOf (derivedInG S)) (td.typeP.U.subgroupOf (derivedInG S)) :=
    { isNormal := hHn
      isComplement := td.typeP.derived_complement
      ne_bot_kernel := hkne
      ne_bot_complement := hcne
      conj_frobenius := by
        -- ⚠ **THE SINGLE HONEST GAP OF (10.7)** — fixed-point-free core (Coq `Frob_der1_type2`).
        -- Goal: no nontrivial `u ∈ U` centralises a nontrivial `h ∈ H = S_F`, i.e. `U` acts
        -- Frobenius-ly on `S_F`.  Genuine character-theoretic content (see docstring); the
        -- `coh`/`hSmax`/`_hG` hypotheses (10.4)/(10.1) are what its honest proof consumes.
        sorry }
  exact ⟨{ kernel := td.typeP.H.subgroupOf (derivedInG S)
           complement := td.typeP.U.subgroupOf (derivedInG S)
           kernel_is_SF := td.typeP.H.subgroupOf (derivedInG S)
             = (maxNilpotentNormalHall S).subgroupOf (derivedInG S)
           frobenius := hfrob },
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
    rw [sharpSubgroup, Set.ncard_diff (Set.singleton_subset_iff.mpr (derivedInG M).one_mem),
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

open scoped FiniteInduce in
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
theorem typeII_coherence_contradiction_estimate [Finite G] [Fintype G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params) :
    ∃ u : ℕ, 7 ≤ u ∧
      (1 : ℚ) - 1 / (hyp.w1 : ℚ) - 1 / (u : ℚ)
        < (hyp.w1 : ℚ) * (hyp.w2 : ℚ) / (Nat.card ↥(derivedInG M) : ℚ) := by
  sorry

/-- **Peterfalvi (10.8)**: under Hypothesis (10.1), the character family `S` is
not coherent.

The proof is Peterfalvi's contradiction, assembled from its three faithful pieces: assuming `S`
coherent, build the `(10.4)` coherent-extension datum (`CoherentHypothesis`, with the `(10.3)`
parameters from `w2_prime_and_parameter_independence`); the structural bound
`|M'| ≥ (2w₁+1)w₂` (`card_derived_ge`), the norm-counting estimate
`1 − 1/w₁ − 1/|U| < w₁w₂/|M'|` with `|U| ≥ 7` (`typeII_coherence_contradiction_estimate`), and the
pure-`ℚ` arithmetic contradiction (`typeII_noncoherence_arithmetic`) together give `False`. -/
theorem S_not_coherent [Finite G] [Fintype G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
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

/-! ## (10.9)--(10.11): the Type V elimination and the case-B remark -/

open scoped FiniteInduce in
/-- **§10 column-`0` row-`0` is the trivial character** (the `μ_{00} = 1_M` anchor, Peterfalvi
(4.3.a)/(4.5)): the `(0,0)` entry of the materialized `μ`-grid is the trivial class function of `M`.
This is the §6 certain-type anchor `certainType_zero_column_anchor.2` read through the `muGrid`
definition (same reconstruction as `muGrid_zero_column_apply_one`). -/
theorem Hypothesis.muGrid_zero_zero_eq_trivial [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    hyp.muGrid hG hodd 0 0 = trivialClassFunction (↥M) := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hdual0 : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1 := by
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
      finCardEquivCharacterGroup_zero]
  have hrow0 : (finCongr hcardW1.symm (0 : Fin hyp.w1)) = 0 := by apply Fin.ext; simp
  have e00 : hyp.muGrid hG hodd 0 0
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).mu
          (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  rw [e00, hdual0, hrow0, h.certainType_zero_column_anchor.2]

open scoped FiniteInduce in
/-- **§10 `⟨μ_0, 1_M⟩ = 1`** (Peterfalvi (10.9), the `a_{00}` constant term, M-side): the column-`0`
sum `μ_0 = ∑_i μ_{i0}` has principal multiplicity `1`, since `μ_{00} = 1_M` (anchor,
`muGrid_zero_zero_eq_trivial`) contributes `1` and the remaining `μ_{i0}` (`i ≠ 0`) are orthogonal to
`μ_{00}` (column-`0` orthonormality, `muGrid_inner_within_column`). -/
theorem Hypothesis.muColumnZero_inner_trivial [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) :
    ClassFunction.inner (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0)
        (trivialClassFunction (↥M)) = 1 := by
  haveI := hyp.finiteG
  classical
  haveI : NeZero hyp.w1 := ⟨by
    have h3 : (3 : ℕ) ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
    omega⟩
  rw [← hyp.muGrid_zero_zero_eq_trivial hG hodd, inner_sum_left]
  rw [Finset.sum_eq_single (0 : Fin hyp.w1)]
  · exact hyp.muGrid_inner_self hG hodd 0 0
  · intro i _ hi
    exact hyp.muGrid_inner_within_column hG hodd 0 hi
  · intro h; exact absurd (Finset.mem_univ _) h

open scoped FiniteInduce in
/-- **Peterfalvi (10.9)**: when `w_1 < w_2`, the residual character `χ = ζ^{τ₁}` of the
`(10.9)` decomposition `(μ_0 − ζ)^τ = ∑_i ω_{i0}^σ − χ` is orthogonal to the aligned `σ`-grid
`(Irr W)^σ`, and `‖χ‖² = 1`.

This is the keystone of the Type-V elimination (10.10): the column-`0` decomposition
`τ(μ_0 − ζ) = ∑_i ω_{i0}^σ − ζ^{τ₁}` (STEP 1, `tau_muColumnZero_sub_zeta_eq`) determines the residual
`ζ^{τ₁}`; the (3.8) trichotomy (`sigmaCoeff_trichotomy`) on `ψ = τ(μ_0 − ζ)` (which vanishes on `V`,
has `NC(ψ) ≤ w₁ + 1 < 2w₁`, and the odd-order gap `w₁ + 2 ≤ w₂`) forces the `σ`-coefficient grid of
`ψ` to be the *single constant column* `j = 0` with value `1` (the principal column, anchored by
`a_{00} = ⟨ψ, 1_G⟩ = ⟨μ_0 − ζ, 1_M⟩ = 1` via the (2.7) adjoint `tau_inner_trivial`).  The single-row
branch is excluded by `‖ζ^{τ₁}‖² = 1` (a `−1` row coefficient would force `‖ζ^{τ₁}‖² ≥ w₂ − 1 > 1`),
and the all-zero branch by `a_{00} = 1 ≠ 0`.  In the surviving column branch
`⟨ζ^{τ₁}, ω_{ij}^σ⟩ = (if j = 0 then 1 else 0) − a(ρ i, κ j) = 0`. -/
theorem orthogonality_of_w1_lt_w2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hw : hyp.w1 < hyp.w2) :
    (∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
        ClassFunction.inner (coh.tau1 params.zeta) (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = 0)
      ∧ ClassFunction.inner (coh.tau1 params.zeta) (coh.tau1 params.zeta) = 1 := by
  haveI := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  -- the §5 `G`-level TI-cyclic hypothesis + Dade application (the ready (10.5) `σ` pattern).
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  haveI : Fintype ((tic.W1.subgroupOf tic.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype ((tic.W2.subgroupOf tic.W) →* ℂˣ) := Fintype.ofFinite _
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  have hcardW1 : Nat.card ↥tic.W1 = hyp.w1 := rfl
  have hcardW2 : Nat.card ↥tic.W2 = hyp.w2 := rfl
  -- the product structure `ω_{ij}^σ = chiFam(ρ i, κ j)`.
  obtain ⟨ρ, κ, hρinj, hκinj, hprod⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_product hG hodd
  -- abbreviation: the `(μ_0 − ζ)^τ` virtual character `ψ`.
  set ψ : ClassFunction G ℂ :=
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - params.zeta) with hψ
  -- STEP 1: `ψ = ∑_{i'} ω_{i'0}^σ − ζ^{τ₁}`.
  have hstep1 : ψ = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
      - coh.tau1 params.zeta := by
    rw [hψ]; exact hyp.tau_muColumnZero_sub_zeta_eq hG coh hmu hos hzS hz1 hzconj hδpm hδj
  -- `‖ζ^{τ₁}‖² = 1` (the second conjunct, used in both the row exclusion and the output).
  have hnorm1 : ClassFunction.inner (coh.tau1 params.zeta) (coh.tau1 params.zeta) = 1 :=
    hyp.zeta_tau1_inner_self hG hodd coh hzS params.zeta_irreducible
  -- `ζ^{τ₁} ∈ ZIrr G`, norm `1`.
  have hzZ : coh.tau1 params.zeta ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr params.zeta (Submodule.subset_span hzS)
  -- the σ-coefficient of `ψ` at the *product* index `(ρ i, κ j)` equals `⟨ψ, ω_{ij}^σ⟩`.
  have hcoeff_prod : ∀ i j, tic.sigmaCoeff hVeq app ψ (ρ i, κ j)
      = ClassFunction.inner ψ (hyp.alignedOmegaSigmaGrid hG hodd i j) := by
    intro i j
    change ClassFunction.inner ψ (tic.chiFam hVeq app (ρ i, κ j))
      = ClassFunction.inner ψ (hyp.alignedOmegaSigmaGrid hG hodd i j)
    rw [hprod i j]
  -- the value of `⟨ψ, ω_{ij}^σ⟩` via STEP 1 and σ-grid orthonormality.
  have hpsiOmega : ∀ i j, ClassFunction.inner ψ (hyp.alignedOmegaSigmaGrid hG hodd i j)
      = (if j = 0 then (1 : ℂ) else 0)
        - ClassFunction.inner (coh.tau1 params.zeta) (hyp.alignedOmegaSigmaGrid hG hodd i j) := by
    intro i j
    rw [hstep1, ClassFunction.inner_sub_left, inner_sum_left]
    congr 1
    rw [Finset.sum_eq_single i]
    · rw [hyp.alignedOmegaSigmaGrid_inner hG hodd i i 0 j]
      by_cases hj : j = 0
      · rw [if_pos ⟨rfl, hj.symm⟩, if_pos hj]
      · rw [if_neg (fun hh => hj hh.2.symm), if_neg hj]
    · intro i' _ hi'
      rw [hyp.alignedOmegaSigmaGrid_inner hG hodd i' i 0 j, if_neg (fun hh => hi' hh.1)]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- `a_{00} = 1`: `⟨ψ, ω_{00}^σ⟩ = ⟨ψ, 1_G⟩ = ⟨μ_0 − ζ, 1_M⟩ = 1`.
  have hsupp : ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - params.zeta).support ⊆ hyp.A0 :=
    hyp.muColumnZero_sub_zeta_support hG hodd hzS hz1
  have hzeta_triv : ClassFunction.inner params.zeta (trivialClassFunction (↥M)) = 0 := by
    have hzmem : params.zeta ∈ irreducibleCharacters (↥M) :=
      mem_irreducibleCharacters.mpr params.zeta_irreducible
    have htmem : trivialClassFunction (↥M) ∈ irreducibleCharacters (↥M) :=
      mem_irreducibleCharacters.mpr trivialClassFunction_isIrreducible
    rw [irr_cf_inner hzmem htmem, if_neg ?_]
    intro hcontra
    have h1 : params.zeta 1 = trivialClassFunction (↥M) 1 :=
      congrArg (fun f : ClassFunction (↥M) ℂ => (f : (↥M) → ℂ) 1) hcontra
    rw [hz1, trivialClassFunction_apply] at h1
    have h3 : (3 : ℕ) ≤ hyp.w1 := hcardW1 ▸ tic.three_le_card_W1
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast h1
    omega
  have ha00 : ClassFunction.inner ψ (hyp.alignedOmegaSigmaGrid hG hodd 0 0) = 1 := by
    rw [hyp.alignedOmegaSigmaGrid_zero_zero hG hodd, hψ, hyp.tau_inner_trivial hsupp,
      ClassFunction.inner_sub_left, hyp.muColumnZero_inner_trivial hG hodd, hzeta_triv, sub_zero]
  -- the σ-coefficient at the *product* `(ρ 0, κ 0)` is `1`.
  have ha00coeff : tic.sigmaCoeff hVeq app ψ (ρ 0, κ 0) = 1 := by
    rw [hcoeff_prod 0 0, ha00]
  -- `ψ` vanishes on `V` (it is `A_0(M)`-supported, and the Dade isometry vanishes off the
  -- `M`-conjugates of `A_0(M)`, which `V` avoids; more directly via `tau_apply_of_mem_typePV`).
  have hpsiV : ∀ v ∈ tic.V, ψ v = 0 := by
    intro v hv
    have hvM : v ∈ M := typePData_W_le_self hyp.typeP (SetLike.mem_coe.mp hv.1)
    rw [hψ, hyp.tau_apply_of_mem_typePV hsupp hv hvM]
    -- `μ_0 − ζ` vanishes at `v ∈ V` (both `μ_0` and `ζ` are induced from the normal `M'`, `v ∉ M'`).
    have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
    have hnotmem : (⟨v, hvM⟩ : ↥M) ∉ (derivedInG M).subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]; exact OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.typeP hv
    obtain ⟨θ, _hθne, hζeq⟩ := hzS
    have hζv : params.zeta ⟨v, hvM⟩ = 0 := by
      rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hnotmem
    have hμv : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) ⟨v, hvM⟩ = 0 :=
      hyp.muGrid_column_sum_vanishes_off_derived hG hodd 0 hnotmem
    rw [ClassFunction.sub_apply, hμv, hζv, sub_zero]
  -- `NC(ψ) ≤ w₁ + 1 < 2·w₁`: the `σ`-coefficient support sits in
  -- `{(ρ i, κ 0) | i} ∪ {pq | ⟨ζ^{τ₁}, χ_pq⟩ ≠ 0}`, of cardinalities `≤ w₁` and `≤ 1`.
  have hNC : tic.sigmaNC hVeq app ψ < 2 * Nat.card ↥tic.W1 := by
    have h3 : (3 : ℕ) ≤ hyp.w1 := hcardW1 ▸ tic.three_le_card_W1
    -- the two covering sets: the column-`0` product indices, and the `ζ^{τ₁}` support.
    set S0 : Set _ := Set.range (fun i : Fin hyp.w1 => (ρ i, κ 0)) with hS0
    set Sz : Set _ :=
      {pq | ClassFunction.inner (coh.tau1 params.zeta) (tic.chiFam hVeq app pq) ≠ 0} with hSz
    have hsub : {pq | tic.sigmaCoeff hVeq app ψ pq ≠ 0} ⊆ S0 ∪ Sz := by
      intro pq hpq
      by_contra hcon
      simp only [hS0, hSz, Set.mem_union, Set.mem_range, Set.mem_setOf_eq, not_or, not_not,
        not_exists] at hcon
      apply hpq
      -- `⟨ψ, χ_pq⟩ = ∑_{i'} ⟨ω_{i'0}^σ, χ_pq⟩ − ⟨ζ^{τ₁}, χ_pq⟩`; the second term is `0` (hcon.2),
      -- and `⟨ω_{i'0}^σ, χ_pq⟩ = ⟨χ_{(ρ i', κ 0)}, χ_pq⟩ = 0` since `pq ≠ (ρ i', κ 0)` (hcon.1).
      show ClassFunction.inner ψ (tic.chiFam hVeq app pq) = 0
      rw [hstep1, ClassFunction.inner_sub_left, hcon.2, sub_zero, inner_sum_left]
      refine Finset.sum_eq_zero (fun i' _ => ?_)
      rw [hprod i' 0,
        show ClassFunction.inner (tic.chiFam hVeq app (ρ i', κ 0)) (tic.chiFam hVeq app pq)
          = if (ρ i', κ 0) = pq then (1 : ℂ) else 0 from (tic.chiFam_spec hVeq app).2.2.1 _ _,
        if_neg (fun he => hcon.1 i' he)]
    have hS0card : S0.ncard ≤ hyp.w1 := by
      rw [hS0, show (Set.range (fun i : Fin hyp.w1 => (ρ i, κ 0)))
          = (fun i : Fin hyp.w1 => (ρ i, κ 0)) '' Set.univ from by rw [Set.image_univ]]
      refine le_trans (Set.ncard_image_le (Set.finite_univ)) ?_
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hSzcard : Sz.ncard ≤ 1 := tic.ncard_inner_chiFam_ne_zero_le_one hVeq app hzZ hnorm1
    have hbound : tic.sigmaNC hVeq app ψ ≤ hyp.w1 + 1 := by
      calc tic.sigmaNC hVeq app ψ
          = {pq | tic.sigmaCoeff hVeq app ψ pq ≠ 0}.ncard := rfl
        _ ≤ (S0 ∪ Sz).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ S0.ncard + Sz.ncard := Set.ncard_union_le _ _
        _ ≤ hyp.w1 + 1 := by gcongr
    rw [hcardW1]; omega
  -- the odd-order gap `w₁ + 2 ≤ w₂`.
  have hgap : Nat.card ↥tic.W1 + 2 ≤ Nat.card ↥tic.W2 := by
    have hodd1 : Odd (Nat.card ↥tic.W1) :=
      tic.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le tic.W1_le_W)
    have hodd2 : Odd (Nat.card ↥tic.W2) :=
      tic.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le tic.W2_le_W)
    have hlt : Nat.card ↥tic.W1 < Nat.card ↥tic.W2 := by rw [hcardW1, hcardW2]; exact hw
    obtain ⟨a, ha⟩ := hodd1
    obtain ⟨b, hb⟩ := hodd2
    omega
  -- apply the (3.8) trichotomy to `ψ`.
  rcases tic.sigmaCoeff_trichotomy hVeq app hpsiV hgap hNC with
    hall | ⟨j₀, c, hc, hcol, hrest⟩ | ⟨i₀, c, hc, hrow, hrest⟩
  · -- all-zero branch: contradicts `a_{00} = 1`.
    exact absurd (ha00coeff.symm.trans (hall (ρ 0, κ 0))) one_ne_zero
  · -- single-column branch: this is the desired conclusion.
    -- `a_{00} ≠ 0` forces `κ 0 = j₀` and `c = 1`.
    have hκ0 : κ 0 = j₀ := by
      by_contra hne
      exact absurd (ha00coeff.symm.trans (hrest (ρ 0) (κ 0) hne)) one_ne_zero
    have hc1 : c = 1 := by
      rw [hκ0] at ha00coeff; rw [hcol (ρ 0)] at ha00coeff; exact ha00coeff
    refine ⟨fun i j => ?_, hnorm1⟩
    -- `a(ρ i, κ j) = if κ j = j₀ then c else 0 = if j = 0 then 1 else 0`.
    have hval : tic.sigmaCoeff hVeq app ψ (ρ i, κ j) = (if j = 0 then (1 : ℂ) else 0) := by
      by_cases hj : j = 0
      · subst hj; rw [hκ0, hcol (ρ i), hc1, if_pos rfl]
      · rw [hrest (ρ i) (κ j) (fun he => hj (hκinj (he.trans hκ0.symm))), if_neg hj]
    -- combine with `⟨ψ, ω_{ij}^σ⟩ = (if j=0 then 1 else 0) − ⟨ζ^{τ₁}, ω_{ij}^σ⟩`.
    have h2 := hcoeff_prod i j
    rw [hval, hpsiOmega i j] at h2
    -- `(if j=0 then 1 else 0) = (if j=0 then 1 else 0) − ⟨ζ^{τ₁}, ω_{ij}^σ⟩` ⟹ `⟨…⟩ = 0`.
    linear_combination h2
  · -- single-row branch: excluded by `‖ζ^{τ₁}‖² = 1`.
    -- `a_{00} ≠ 0` forces `ρ 0 = i₀` and `c = 1`, so `a(ρ 0, κ j) = 1` for all `j`;
    -- hence `⟨ζ^{τ₁}, ω_{0j}^σ⟩ = -1 ≠ 0` for every `j ≠ 0`.  But `ζ^{τ₁}` is a norm-`1`
    -- virtual character with at most ONE nonzero inner product against the orthonormal
    -- `χ`-family (`ncard_inner_chiFam_ne_zero_le_one`), while `w₂ ≥ 3` supplies two distinct
    -- such indices `(ρ 0, κ 1), (ρ 0, κ 2)` — contradiction.
    exfalso
    have hi0 : ρ 0 = i₀ := by
      by_contra hne
      exact absurd (ha00coeff.symm.trans (hrest (ρ 0) (κ 0) hne)) one_ne_zero
    have hc1 : c = 1 := by rw [hi0] at ha00coeff; rw [hrow (κ 0)] at ha00coeff; exact ha00coeff
    -- two distinct nonzero columns, from `w₂ ≥ 3`.
    have h3w2 : (3 : ℕ) ≤ hyp.w2 := hcardW2 ▸ tic.three_le_card_W2
    let j1 : Fin hyp.w2 := ⟨1, by omega⟩
    let j2 : Fin hyp.w2 := ⟨2, by omega⟩
    have hj1 : j1 ≠ 0 := Fin.ne_of_val_ne (by simp [j1])
    have hj2 : j2 ≠ 0 := Fin.ne_of_val_ne (by simp [j2])
    -- for any `j ≠ 0`: `⟨ζ^{τ₁}, χ_{(ρ 0, κ j)}⟩ = -1` (from `a(ρ 0, κ j) = 1`).
    have hrowval : ∀ j : Fin hyp.w2, j ≠ 0 →
        ClassFunction.inner (coh.tau1 params.zeta) (tic.chiFam hVeq app (ρ 0, κ j)) = -1 := by
      intro j hj
      have hacoeff : tic.sigmaCoeff hVeq app ψ (ρ 0, κ j) = 1 := by
        rw [hi0, hrow (κ j), hc1]
      have h2 := hcoeff_prod 0 j
      rw [hacoeff, hpsiOmega 0 j, if_neg hj] at h2
      -- `1 = -⟨ζ^{τ₁}, ω_{0j}^σ⟩`, and `ω_{0j}^σ = χ_{(ρ 0, κ j)}`.
      have h3 : ClassFunction.inner (coh.tau1 params.zeta)
          (hyp.alignedOmegaSigmaGrid hG hodd 0 j) = -1 := by linear_combination h2
      rw [← hprod 0 j]; exact h3
    have hP1 : (ρ 0, κ j1) ∈
        {pq | ClassFunction.inner (coh.tau1 params.zeta) (tic.chiFam hVeq app pq) ≠ 0} := by
      change ClassFunction.inner (coh.tau1 params.zeta) (tic.chiFam hVeq app (ρ 0, κ j1)) ≠ 0
      rw [hrowval j1 hj1]; norm_num
    have hP2 : (ρ 0, κ j2) ∈
        {pq | ClassFunction.inner (coh.tau1 params.zeta) (tic.chiFam hVeq app pq) ≠ 0} := by
      change ClassFunction.inner (coh.tau1 params.zeta) (tic.chiFam hVeq app (ρ 0, κ j2)) ≠ 0
      rw [hrowval j2 hj2]; norm_num
    -- the two indices are distinct (`κ` injective, `1 ≠ 2`).
    have hPne : (ρ 0, κ j1) ≠ (ρ 0, κ j2) := by
      intro he
      have hκe : κ j1 = κ j2 := (Prod.ext_iff.mp he).2
      have hjeq : j1 = j2 := hκinj hκe
      exact absurd hjeq (by simp [j1, j2, Fin.ext_iff])
    -- but the nonzero-coefficient set has `ncard ≤ 1` — contradiction.
    have hle1 := tic.ncard_inner_chiFam_ne_zero_le_one hVeq app hzZ hnorm1
    exact hPne ((Set.ncard_le_one_iff (Set.toFinite _)).mp hle1 hP1 hP2)

open scoped FiniteInduce in
/-- **Peterfalvi (10.9)/(11.8.4) norm**: `‖μ_0 − ζ‖² = w₁ + 1` for an irreducible `ζ ∈ S` of degree
`w₁`, where `μ_0 = ∑_i μ_{i0}` is the column-`0` sum.  Expand: `‖μ_0‖² = w₁` (orthonormality of the
`μ_{i0}`, `muGrid_column_sum_inner_self`), `⟨μ_0, ζ⟩ = 0` (the degree mismatch `μ_{i0}(1) = 1 ≠ w₁`,
`muGrid_inner_eq_zero_of_apply_one_ne`), and `‖ζ‖² = 1`.  This is the `M`-side norm used by the
coherence-free (10.9) (`‖(μ_0 − ζ)^τ‖² = w₁ + 1` via the Dade isometry, hence `NC ≤ w₁ + 1`) and by
Peterfalvi (11.8.4) (`‖χ‖² = ‖μ_0 − ζ‖² − q = 1`). -/
theorem inner_muColumnZero_sub_zeta_self [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) {ζ : ClassFunction ↥M ℂ}
    (hzirr : IsIrreducibleCharacter ζ) (hz1 : ζ 1 = (hyp.w1 : ℂ)) :
    ClassFunction.inner ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) - ζ)
        ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) - ζ) = ((hyp.w1 + 1 : ℕ) : ℂ) := by
  haveI := hyp.finiteG
  have hodd : Odd (Nat.card G) := hG.odd
  have h3 : (3 : ℕ) ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  have hμ0perp : ClassFunction.inner (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) ζ = 0 := by
    rw [inner_sum_left]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    refine hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hzirr ?_
    rw [hyp.muGrid_zero_column_apply_one hG hodd i, hz1]
    intro he
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast he.symm
    omega
  have hζμ0 : ClassFunction.inner ζ (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hμ0perp, star_zero]
  have hζζ : ClassFunction.inner ζ ζ = 1 := by
    have hzmem : ζ ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hzirr
    rw [irr_cf_inner hzmem hzmem, if_pos rfl]
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    hyp.muGrid_column_sum_inner_self hG hodd 0, hμ0perp, hζμ0, hζζ]
  push_cast; ring

open scoped FiniteInduce in
/-- **Peterfalvi (10.9), coherence-free σ-coefficient form**.  Under Hypothesis (10.1), for any
irreducible `ζ ∈ S = inducedFamily M` of degree `ζ(1) = w₁`, if `w₁ < w₂` then the `σ`-coefficient
grid of `ψ = (μ_0 − ζ)^τ` is the single constant column `j = 0` with value `1`:
`⟨ψ, ω_{ij}^σ⟩ = (if j = 0 then 1 else 0)` for all `i, j`.

Unlike `orthogonality_of_w1_lt_w2`, this needs **no coherence** of `S` (it does not identify the
residual as `ζ^{τ₁}`).  The argument is the (3.8) trichotomy (`sigmaCoeff_trichotomy`) applied to
`ψ`, which vanishes on `V` and is anchored by `a_{00} = ⟨μ_0 − ζ, 1_M⟩ = 1`.  The **coherence-free**
norm bound `‖ψ‖² = ‖μ_0 − ζ‖² = w₁ + 1` (Dade isometry `tau_inner_eq_of_supported`, orthonormality
of the `μ_{i0}` `muGrid_column_sum_inner_self`, the degree-mismatch `⟨μ_{i0}, ζ⟩ = 0`, and
`‖ζ‖² = 1`) gives `NC(ψ) ≤ w₁ + 1 < 2w₁` by Bessel
(`ncard_sigmaCoeff_ne_zero_le_of_inner_self_natCast`).  The all-zero branch is excluded by
`a_{00} = 1`; the single-row branch by `NC ≥ w₂ > w₁ + 1` (a full row carries `w₂` nonzero
coefficients, but the odd-order gap forces `w₁ + 2 ≤ w₂`).  This is the form consumed by Peterfalvi
(11.9.b) (`q > p`), where `S` is *not* coherent (10.8). -/
theorem inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {ζ : ClassFunction ↥M ℂ} (hzS : ζ ∈ inducedFamily M) (hzirr : IsIrreducibleCharacter ζ)
    (hz1 : ζ 1 = (hyp.w1 : ℂ)) (hw : hyp.w1 < hyp.w2) :
    ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = (if j = 0 then (1 : ℂ) else 0) := by
  haveI := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  haveI : Fintype ((tic.W1.subgroupOf tic.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype ((tic.W2.subgroupOf tic.W) →* ℂˣ) := Fintype.ofFinite _
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  have hcardW1 : Nat.card ↥tic.W1 = hyp.w1 := rfl
  have hcardW2 : Nat.card ↥tic.W2 = hyp.w2 := rfl
  obtain ⟨ρ, κ, hρinj, hκinj, hprod⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_product hG hodd
  set ψ : ClassFunction G ℂ :=
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ) with hψ
  -- the σ-coefficient at the product index `(ρ i, κ j)` equals `⟨ψ, ω_{ij}^σ⟩`.
  have hcoeff_prod : ∀ i j, tic.sigmaCoeff hVeq app ψ (ρ i, κ j)
      = ClassFunction.inner ψ (hyp.alignedOmegaSigmaGrid hG hodd i j) := by
    intro i j
    change ClassFunction.inner ψ (tic.chiFam hVeq app (ρ i, κ j))
      = ClassFunction.inner ψ (hyp.alignedOmegaSigmaGrid hG hodd i j)
    rw [hprod i j]
  -- `μ_0 − ζ` is `A_0`-supported.
  have hsupp : ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ).support ⊆ hyp.A0 :=
    hyp.muColumnZero_sub_zeta_support hG hodd hzS hz1
  -- `⟨ζ, 1_M⟩ = 0` (degree `w₁ > 1`).
  have hzeta_triv : ClassFunction.inner ζ (trivialClassFunction (↥M)) = 0 := by
    have hzmem : ζ ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hzirr
    have htmem : trivialClassFunction (↥M) ∈ irreducibleCharacters (↥M) :=
      mem_irreducibleCharacters.mpr trivialClassFunction_isIrreducible
    rw [irr_cf_inner hzmem htmem, if_neg ?_]
    intro hcontra
    have h1 : ζ 1 = trivialClassFunction (↥M) 1 :=
      congrArg (fun f : ClassFunction (↥M) ℂ => (f : (↥M) → ℂ) 1) hcontra
    rw [hz1, trivialClassFunction_apply] at h1
    have h3 : (3 : ℕ) ≤ hyp.w1 := hcardW1 ▸ tic.three_le_card_W1
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast h1
    omega
  -- `a_{00} = ⟨ψ, ω_{00}^σ⟩ = ⟨μ_0 − ζ, 1_M⟩ = 1`.
  have ha00 : ClassFunction.inner ψ (hyp.alignedOmegaSigmaGrid hG hodd 0 0) = 1 := by
    rw [hyp.alignedOmegaSigmaGrid_zero_zero hG hodd, hψ, hyp.tau_inner_trivial hsupp,
      ClassFunction.inner_sub_left, hyp.muColumnZero_inner_trivial hG hodd, hzeta_triv, sub_zero]
  have ha00coeff : tic.sigmaCoeff hVeq app ψ (ρ 0, κ 0) = 1 := by
    rw [hcoeff_prod 0 0, ha00]
  -- `ψ` vanishes on `V`.
  have hpsiV : ∀ v ∈ tic.V, ψ v = 0 := by
    intro v hv
    have hvM : v ∈ M := typePData_W_le_self hyp.typeP (SetLike.mem_coe.mp hv.1)
    rw [hψ, hyp.tau_apply_of_mem_typePV hsupp hv hvM]
    have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
    have hnotmem : (⟨v, hvM⟩ : ↥M) ∉ (derivedInG M).subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]; exact OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.typeP hv
    obtain ⟨θ, _hθne, hζeq⟩ := hzS
    have hζv : ζ ⟨v, hvM⟩ = 0 := by
      rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hnotmem
    have hμv : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) ⟨v, hvM⟩ = 0 :=
      hyp.muGrid_column_sum_vanishes_off_derived hG hodd 0 hnotmem
    rw [ClassFunction.sub_apply, hμv, hζv, sub_zero]
  -- `ψ ∈ ZIrr G` and the coherence-free norm `‖ψ‖² = w₁ + 1`.
  have hμ0Z : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) ∈ ZIrr ↥M :=
    Submodule.sum_mem _ (fun i _ => (hyp.muGrid_isIrreducible hG hodd i 0).mem_ZIrr)
  have hdiffZ : ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ) ∈ ZIrr ↥M :=
    Submodule.sub_mem _ hμ0Z hzirr.mem_ZIrr
  have hψZ : ψ ∈ ZIrr G := by
    rw [hψ]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hyp.hconj hsupp hdiffZ
  have hψnorm : ClassFunction.inner ψ ψ = ((hyp.w1 + 1 : ℕ) : ℂ) := by
    rw [hψ, hyp.tau_inner_eq_of_supported hsupp hsupp,
      inner_muColumnZero_sub_zeta_self hG hyp hzirr hz1]
  -- NC bound (Bessel) and the `< 2w₁` form.
  have hNC : tic.sigmaNC hVeq app ψ ≤ hyp.w1 + 1 :=
    tic.ncard_sigmaCoeff_ne_zero_le_of_inner_self_natCast hVeq app hψZ hψnorm
  have hNC2 : tic.sigmaNC hVeq app ψ < 2 * Nat.card ↥tic.W1 := by
    have h3 : (3 : ℕ) ≤ hyp.w1 := hcardW1 ▸ tic.three_le_card_W1
    rw [hcardW1]; omega
  -- the odd-order gap `w₁ + 2 ≤ w₂`.
  have hgap : Nat.card ↥tic.W1 + 2 ≤ Nat.card ↥tic.W2 := by
    have hodd1 : Odd (Nat.card ↥tic.W1) :=
      tic.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le tic.W1_le_W)
    have hodd2 : Odd (Nat.card ↥tic.W2) :=
      tic.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le tic.W2_le_W)
    have hlt : Nat.card ↥tic.W1 < Nat.card ↥tic.W2 := by rw [hcardW1, hcardW2]; exact hw
    obtain ⟨a, ha⟩ := hodd1
    obtain ⟨b, hb⟩ := hodd2
    omega
  -- apply the (3.8) trichotomy.
  rcases tic.sigmaCoeff_trichotomy hVeq app hpsiV hgap hNC2 with
    hall | ⟨j₀, c, hc, hcol, hrest⟩ | ⟨i₀, c, hc, hrow, hrest⟩
  · -- all-zero branch: contradicts `a_{00} = 1`.
    exact absurd (ha00coeff.symm.trans (hall (ρ 0, κ 0))) one_ne_zero
  · -- single-column branch: the desired conclusion.
    have hκ0 : κ 0 = j₀ := by
      by_contra hne
      exact absurd (ha00coeff.symm.trans (hrest (ρ 0) (κ 0) hne)) one_ne_zero
    have hc1 : c = 1 := by
      rw [hκ0] at ha00coeff; rw [hcol (ρ 0)] at ha00coeff; exact ha00coeff
    intro i j
    have hval : tic.sigmaCoeff hVeq app ψ (ρ i, κ j) = (if j = 0 then (1 : ℂ) else 0) := by
      by_cases hj : j = 0
      · subst hj; rw [hκ0, hcol (ρ i), hc1, if_pos rfl]
      · rw [hrest (ρ i) (κ j) (fun he => hj (hκinj (he.trans hκ0.symm))), if_neg hj]
    rw [← hcoeff_prod i j, hval]
  · -- single-row branch: a full `i₀`-row has `w₂` nonzero coefficients, so `NC ≥ w₂ > w₁ + 1`.
    exfalso
    have hinj : Function.Injective (fun q : (tic.W2.subgroupOf tic.W) →* ℂˣ => (i₀, q)) :=
      fun a b h => (Prod.ext_iff.mp h).2
    have hrowsub : Set.range (fun q : (tic.W2.subgroupOf tic.W) →* ℂˣ => (i₀, q))
        ⊆ {pq | tic.sigmaCoeff hVeq app ψ pq ≠ 0} := by
      rintro _ ⟨q, rfl⟩
      simp only [Set.mem_setOf_eq]
      rw [hrow q]; exact hc
    have hrowcard : (Set.range (fun q : (tic.W2.subgroupOf tic.W) →* ℂˣ => (i₀, q))).ncard
        = hyp.w2 := by
      rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj,
        tic.card_charGroup_subgroupOf tic.W2_le_W, hcardW2]
    have hge : hyp.w2 ≤ tic.sigmaNC hVeq app ψ := by
      rw [← hrowcard]
      exact Set.ncard_le_ncard hrowsub (Set.toFinite _)
    rw [hcardW1, hcardW2] at hgap
    omega

open scoped FiniteInduce in
/-- **Peterfalvi (10.9), residual-orthogonal form** (coherence-free).  When `w₁ < w₂`, the residual
`(μ_0 − ζ)^τ − ∑_{i} ω_{i0}^σ` is orthogonal to every `ω_{ij}^σ`, i.e. to `(Irr W)^σ`.  Immediate
from the σ-coefficient form `inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2`
(`⟨ψ, ω_{ij}^σ⟩ = (if j = 0 then 1 else 0)`) together with the σ-grid orthonormality
(`∑_{i'} ⟨ω_{i'0}^σ, ω_{ij}^σ⟩ = (if j = 0 then 1 else 0)`).  This is the orthogonality that
Peterfalvi (11.9.b) contradicts against (11.8) to force `q > p`. -/
theorem residual_alignedOmegaSigma_inner_eq_zero_of_w1_lt_w2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {ζ : ClassFunction ↥M ℂ} (hzS : ζ ∈ inducedFamily M) (hzirr : IsIrreducibleCharacter ζ)
    (hz1 : ζ 1 = (hyp.w1 : ℂ)) (hw : hyp.w1 < hyp.w2) :
    ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' 0) - ζ))
          - ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i' 0)
        (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = 0 := by
  haveI := hyp.finiteG
  classical
  intro i j
  rw [ClassFunction.inner_sub_left, inner_sum_left,
    inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2 hG hyp hzS hzirr hz1 hw i j,
    Finset.sum_eq_single i]
  · rw [hyp.alignedOmegaSigmaGrid_inner hG hG.odd i i 0 j]
    by_cases hj : j = 0
    · subst hj; simp
    · rw [if_neg hj, if_neg (fun hh => hj hh.2.symm), sub_zero]
  · intro i' _ hi'
    rw [hyp.alignedOmegaSigmaGrid_inner hG hG.odd i' i 0 j, if_neg (fun hh => hi' hh.1)]
  · intro h; exact absurd (Finset.mem_univ _) h

open scoped FiniteInduce in
/-- **Peterfalvi (11.9.b), the `q > p` reduction** (modulo (11.8)).  For an irreducible
`ζ ∈ S = inducedFamily M` of degree `w₁`, given the genuine (11.8) non-orthogonality `h118`
(`(μ_0 − ζ)^τ − ∑ ω_{i0}^σ` is **not** orthogonal to `(Irr W)^σ`), it follows that `w₂ < w₁`
(i.e. `q > p`).

This is the textbook (11.9.b) argument "follows from (10.9) and (11.8)": were `w₁ < w₂`, the
coherence-free (10.9) (`residual_alignedOmegaSigma_inner_eq_zero_of_w1_lt_w2`) would make the
residual orthogonal to `(Irr W)^σ`, contradicting `h118`; and `w₁ ≠ w₂` because `|W₁|, |W₂|` are
coprime with `w₁ ≥ 3`.  The hypothesis `h118` is the genuine (11.8) statement, here an explicit
obligation; its honest proof (Peterfalvi (11.8.1)–(11.8.6)) is the remaining §11 character content
(lane-b W3, issue 2020), and the consumer is `card_kappaHall_lt_of_isTypeIIIorIV`
(`|K*| < |K|`, `q = |W₁| = |K|`, `p = |W₂| = |K*|`). -/
theorem w2_lt_w1_of_residual_not_orthogonal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {ζ : ClassFunction ↥M ℂ} (hzS : ζ ∈ inducedFamily M) (hzirr : IsIrreducibleCharacter ζ)
    (hz1 : ζ 1 = (hyp.w1 : ℂ))
    (h118 : ¬ ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' 0) - ζ))
          - ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i' 0)
        (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = 0) :
    hyp.w2 < hyp.w1 := by
  haveI := hyp.finiteG
  have h3 : (3 : ℕ) ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hG.odd).three_le_card_W1
  have hne : hyp.w1 ≠ hyp.w2 := by
    intro he
    have hcop : Nat.Coprime hyp.w1 hyp.w2 := typePData_coprime_card_W1_W2 hyp.typeP
    rw [← he] at hcop
    have hgcd : Nat.gcd hyp.w1 hyp.w1 = 1 := hcop
    rw [Nat.gcd_self] at hgcd
    omega
  rcases lt_trichotomy hyp.w1 hyp.w2 with hlt | heq | hgt
  · exact absurd
      (residual_alignedOmegaSigma_inner_eq_zero_of_w1_lt_w2 hG hyp hzS hzirr hz1 hlt) h118
  · exact absurd heq hne
  · exact hgt

open scoped FiniteInduce in
/-- **Coherence of an equal-degree subfamily of `S`** (Peterfalvi (5.7)/(1.4) for §11): an injective
family `χ : Fin n → Irr(M)` (`n ≥ 2`) of irreducible characters, each a member of
`S = inducedFamily M` and all of the *same degree*, is coherent for the §10 Dade isometry `τ`.

This is the (11.8) materialization bridge.  Every input of the equal-degree coherence producer
`coherentEqualDegree_fromDade` is discharged from the §10 `Hypothesis` data with no opaque field:
* the `(5.1)` base map is `τ = dadeIntegralCharacterMap hyp.dadeData.dade …` (definitionally `hyp.tau`);
* the support is `A₀(M) = supportInSubgroup (typePA0 M) M` (definitionally `hyp.A0`);
* the signed-difference supports `(χⱼ − χ₀).support ⊆ A₀(M)` are `inducedFamily_sub_support` (the
  members share a degree, so each difference vanishes off `M'^#`);
* `1 ∉ A₀(M)` is `S04.Hypothesis.ne_one` (`A₀ ⊆ G^#`).

Applied to the degree-`w₁` subfamily `S(HC)` (the `(u−1)/q ≥ 2` degree-`q = w₁` constituents of the
`(U/C) ⋊ W₁` Frobenius), it gives the `S₁ = S(HC)` coherence `τ₁` the (11.8) contradiction consumes;
the remaining content is enumerating `S(HC)` as such a family. -/
noncomputable def Hypothesis.inducedFamily_isCoherent_of_equalDegreeFamily [Finite G]
    {M : Subgroup G}
    (hyp : Hypothesis M) {n : ℕ} [NeZero n] (hn : 2 ≤ n) (χ : Fin n → IrreducibleCharacter (↥M))
    (hχinj : Function.Injective χ)
    (hmem : ∀ j, (χ j : ClassFunction ↥M ℂ) ∈ inducedFamily M)
    (hdeg : ∀ j, ((χ j : ClassFunction ↥M ℂ) : ↥M → ℂ) 1
      = ((χ 0 : ClassFunction ↥M ℂ) : ↥M → ℂ) 1) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (Set.range (fun j => (χ j : ClassFunction ↥M ℂ))) hyp.A0 := by
  haveI := hyp.finiteG
  have h1notA : (1 : G) ∉ typePA0 M hyp.typeP := fun h => hyp.dadeData.dade.ne_one h rfl
  have hsuppdiff : ∀ j, (irreducibleCharacterDifference χ j).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := fun j =>
    hyp.inducedFamily_sub_support (hmem j) (hmem 0) (hdeg j)
  exact OddOrder.Peterfalvi.S07.coherentEqualDegree_fromDade hyp.dadeData.dade hyp.hconj hn χ
    hχinj hdeg hsuppdiff h1notA

/-- **The degree-`w₁` irreducible subfamily `S(HC) = S₁`** of `S = inducedFamily M`: the
uniform-degree family whose (5.7) coherence `τ₁` the (11.8) contradiction consumes.  Abbreviates the
recurring `{φ ∈ S | φ irreducible, φ(1) = w₁}` set comprehension so the (11.8.5)
extension-generalization lemmas can quantify over an arbitrary coherent extension
`coh : IsCoherent hyp.tau hyp.SHCSet hyp.A0` (both `SHC_isCoherent` and the branch-2 swap
`SHC_swap` are such). -/
abbrev Hypothesis.SHCSet [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    Set (ClassFunction ↥M ℂ) :=
  {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
    ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))}

open scoped FiniteInduce in
/-- **Peterfalvi (11.8)/(5.7): coherence of `S₁ = S(HC)`**, the uniform degree-`w₁` irreducible
subfamily of `S = inducedFamily M`.

This materializes the coq `cohS1 : coherent S1 M^# tau := uniform_degree_coherence scohS1`
(`PFsection11.v`): the degree-`w₁` irreducible members of `S` all share the degree `w₁`, so the
equal-degree coherence producer applies.  The family is enumerated as a `Finset` of *bundled*
irreducible characters (`IrreducibleCharacter ↥M = {φ // IsIrreducibleCharacter φ}`); `Finset.equivFin`
gives an injective `Fin n` indexing for free, and `inducedFamily_isCoherent_of_equalDegreeFamily`
discharges the rest.  Nonemptiness with `n ≥ 2` is the conjugate pair `{ζ, ζ̄}` of the degree-`w₁`
witness `exists_zeta_in_inducedFamily_degree_w1` (distinct since `S` has no real characters,
`inducedFamily_hasNoRealCharacters`).

This is the `S₁`-coherence the (11.8) contradiction consumes (with `S₂ = S(C) − S(HC)` and a glue to
build full `S(C)` coherence, contradicting (11.3)/(10.8)). -/
noncomputable def Hypothesis.SHC_isCoherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} hyp.A0 := by
  haveI := hyp.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  -- `s` = the bundled degree-`w₁` irreducible members of `S`.
  set p : IrreducibleCharacter ↥M → Prop := fun χ =>
    (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
      ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ) with hp
  set s : Finset (IrreducibleCharacter ↥M) := Finset.univ.filter p with hs_def
  have hmem_s : ∀ χ, χ ∈ s ↔ p χ := fun χ => by
    rw [hs_def, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)
  -- the enumerating family, injective for free via `Finset.equivFin`.
  set χfam : Fin s.card → IrreducibleCharacter ↥M :=
    fun j => (s.equivFin.symm j : IrreducibleCharacter ↥M) with hχfam
  have hχfam_mem : ∀ j, χfam j ∈ s := fun j => (s.equivFin.symm j).2
  have hinj : Function.Injective χfam := fun a b h =>
    s.equivFin.symm.injective (Subtype.ext h)
  have hmem : ∀ j, (χfam j : ClassFunction ↥M ℂ) ∈ inducedFamily M := fun j =>
    ((hmem_s _).mp (hχfam_mem j)).1
  have hdegfam : ∀ j, ((χfam j : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ) := fun j =>
    ((hmem_s _).mp (hχfam_mem j)).2
  -- `n ≥ 2`: the conjugate pair `{ζ, ζ̄}` of the degree-`w₁` witness (a `Prop`, so the `∃`-witness
  -- elimination is confined to this proof — the enclosing goal `IsCoherent …` is `Type`-valued).
  have hcard : 2 ≤ s.card := by
    obtain ⟨ζ, hζS, hζirr, hζ1⟩ := exists_zeta_in_inducedFamily_degree_w1 hyp.typeP hG.odd
      (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)
    have hζ1' : ((ζ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ) := hζ1
    have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
    have hζc1 : ((ζ.conj : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ) := by
      rw [ClassFunction.conj_apply, hζ1', star_natCast]
    have hζi_s : (⟨ζ, hζirr⟩ : IrreducibleCharacter ↥M) ∈ s := (hmem_s _).mpr ⟨hζS, hζ1'⟩
    have hζci_s : (⟨ζ.conj, hζirr.conj⟩ : IrreducibleCharacter ↥M) ∈ s :=
      (hmem_s _).mpr ⟨hζcS, hζc1⟩
    have hne : (⟨ζ.conj, hζirr.conj⟩ : IrreducibleCharacter ↥M) ≠ ⟨ζ, hζirr⟩ := by
      intro h
      exact inducedFamily_hasNoRealCharacters hModd hζS (congrArg Subtype.val h)
    have hsub : ({⟨ζ.conj, hζirr.conj⟩, ⟨ζ, hζirr⟩} : Finset (IrreducibleCharacter ↥M)) ⊆ s := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact hζci_s
      · rw [Finset.mem_singleton] at hx'; exact hx' ▸ hζi_s
    exact (Finset.card_pair hne).symm.trans_le (Finset.card_le_card hsub)
  haveI : NeZero s.card := ⟨by omega⟩
  have hdeg : ∀ j, ((χfam j : ClassFunction ↥M ℂ) : ↥M → ℂ) 1
      = ((χfam 0 : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 := fun j => by rw [hdegfam j, hdegfam 0]
  -- coherence on the range, then identify the range with `S₁ = S(HC)`.
  have hcoh := hyp.inducedFamily_isCoherent_of_equalDegreeFamily hcard χfam hinj hmem hdeg
  have hrange : (Set.range fun j => (χfam j : ClassFunction ↥M ℂ)) =
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} := by
    ext φ
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨hmem j, (χfam j).2, hdegfam j⟩
    · rintro ⟨hφS, hφirr, hφ1⟩
      have hsφ : (⟨φ, hφirr⟩ : IrreducibleCharacter ↥M) ∈ s := (hmem_s _).mpr ⟨hφS, hφ1⟩
      exact ⟨s.equivFin ⟨⟨φ, hφirr⟩, hsφ⟩, by simp [hχfam]⟩
  rw [hrange] at hcoh
  exact hcoh

open scoped FiniteInduce in
/-- **General constant-degree coherence** — the degree-`d` irreducible subfamily of `S =
inducedFamily M` is coherent.  Generalizes `SHC_isCoherent` (which fixes `d = w₁`) to an arbitrary
degree `d`: the irreducible degree-`d` members of `S` form an equal-degree family, so the R-datum-free
(5.7)/Dade constant-degree engine `inducedFamily_isCoherent_of_equalDegreeFamily` applies.  `≥ 2`
members follow from one witness `ζ` (`hex`) plus its distinct conjugate `ζ̄` (odd order ⇒ no real
characters, `inducedFamily_hasNoRealCharacters`).  This is the constant-degree base case of the
Peterfalvi (9.11) `Ptype_core_coherence` induction (the degree-`qa`/`qu` uniform subfamily on which
`uniform_degree_coherence` fires before the conjugate-pair extension). -/
noncomputable def Hypothesis.inducedFamily_degreeSubfamily_isCoherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) (d : ℕ)
    (hex : ∃ ζ : ClassFunction ↥M ℂ, ζ ∈ inducedFamily M ∧ IsIrreducibleCharacter ζ ∧
      ((ζ : ↥M → ℂ) 1 = (d : ℂ))) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (d : ℂ))} hyp.A0 := by
  haveI := hyp.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  set p : IrreducibleCharacter ↥M → Prop := fun χ =>
    (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
      ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (d : ℂ) with hp
  set s : Finset (IrreducibleCharacter ↥M) := Finset.univ.filter p with hs_def
  have hmem_s : ∀ χ, χ ∈ s ↔ p χ := fun χ => by
    rw [hs_def, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)
  set χfam : Fin s.card → IrreducibleCharacter ↥M :=
    fun j => (s.equivFin.symm j : IrreducibleCharacter ↥M) with hχfam
  have hχfam_mem : ∀ j, χfam j ∈ s := fun j => (s.equivFin.symm j).2
  have hinj : Function.Injective χfam := fun a b h =>
    s.equivFin.symm.injective (Subtype.ext h)
  have hmem : ∀ j, (χfam j : ClassFunction ↥M ℂ) ∈ inducedFamily M := fun j =>
    ((hmem_s _).mp (hχfam_mem j)).1
  have hdegfam : ∀ j, ((χfam j : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (d : ℂ) := fun j =>
    ((hmem_s _).mp (hχfam_mem j)).2
  have hcard : 2 ≤ s.card := by
    obtain ⟨ζ, hζS, hζirr, hζ1⟩ := hex
    have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
    have hζc1 : ((ζ.conj : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (d : ℂ) := by
      rw [ClassFunction.conj_apply, hζ1, star_natCast]
    have hζi_s : (⟨ζ, hζirr⟩ : IrreducibleCharacter ↥M) ∈ s := (hmem_s _).mpr ⟨hζS, hζ1⟩
    have hζci_s : (⟨ζ.conj, hζirr.conj⟩ : IrreducibleCharacter ↥M) ∈ s :=
      (hmem_s _).mpr ⟨hζcS, hζc1⟩
    have hne : (⟨ζ.conj, hζirr.conj⟩ : IrreducibleCharacter ↥M) ≠ ⟨ζ, hζirr⟩ := by
      intro h
      exact inducedFamily_hasNoRealCharacters hModd hζS (congrArg Subtype.val h)
    have hsub : ({⟨ζ.conj, hζirr.conj⟩, ⟨ζ, hζirr⟩} : Finset (IrreducibleCharacter ↥M)) ⊆ s := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact hζci_s
      · rw [Finset.mem_singleton] at hx'; exact hx' ▸ hζi_s
    exact (Finset.card_pair hne).symm.trans_le (Finset.card_le_card hsub)
  haveI : NeZero s.card := ⟨by omega⟩
  have hdeg : ∀ j, ((χfam j : ClassFunction ↥M ℂ) : ↥M → ℂ) 1
      = ((χfam 0 : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 := fun j => by rw [hdegfam j, hdegfam 0]
  have hcoh := hyp.inducedFamily_isCoherent_of_equalDegreeFamily hcard χfam hinj hmem hdeg
  have hrange : (Set.range fun j => (χfam j : ClassFunction ↥M ℂ)) =
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (d : ℂ))} := by
    ext φ
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨hmem j, (χfam j).2, hdegfam j⟩
    · rintro ⟨hφS, hφirr, hφ1⟩
      have hsφ : (⟨φ, hφirr⟩ : IrreducibleCharacter ↥M) ∈ s := (hmem_s _).mpr ⟨hφS, hφ1⟩
      exact ⟨s.equivFin ⟨⟨φ, hφirr⟩, hsφ⟩, by simp [hχfam]⟩
  rw [hrange] at hcoh
  exact hcoh

open scoped FiniteInduce in
/-- **Per-member `R`-datum for an irreducible `S = inducedFamily M`-member** (the (5.2.d)
`CharacterDifferenceImage` for `τ`).  For an irreducible `χ ∈ S`, the conjugate-pair keystone
`{χ, χ̄}` has `A₀`-supported difference (`inducedFamily_sub_support`, `χ̄` a member of equal degree)
and `χ` is non-real (odd order, `inducedFamily_hasNoRealCharacters`), so `dadeCharacterDifferenceImageOfDiff`
produces the (5.2.d) image datum for the genuine Dade map `τ = dadeIntegralCharacterMap …`.  This is
the irreducible half of the `subcoherent(S_ H0C')` `R`-datum feeding the Peterfalvi (9.11)
core-coherence induction (the reducible `μ`-column half is separate, `tau_muGrid_row_diff`). -/
noncomputable def Hypothesis.inducedFamily_irreducible_Rdatum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (χ : IrreducibleCharacter ↥M) (hχ : (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M) :
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage hyp.tau (χ : ClassFunction ↥M ℂ) := by
  haveI := hyp.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hne : (χ : ClassFunction ↥M ℂ).conj ≠ (χ : ClassFunction ↥M ℂ) :=
    inducedFamily_hasNoRealCharacters hModd hχ
  have hreal : ¬ ClassFunction.IsReal (χ : ClassFunction ↥M ℂ) := fun h => hne h
  have hcS : (χ : ClassFunction ↥M ℂ).conj ∈ inducedFamily M :=
    inducedFamily_closedUnderConjugate M hχ
  have hdeg : ((χ : ClassFunction ↥M ℂ).conj : ↥M → ℂ) 1 = ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 := by
    obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
    simp only [ClassFunction.conj_apply, hd, star_natCast]
  have hdiffsupp : ((χ : ClassFunction ↥M ℂ).conj - (χ : ClassFunction ↥M ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M :=
    hyp.inducedFamily_sub_support hcS hχ hdeg
  exact OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff hyp.dadeData.dade hyp.hconj χ
    hreal hdiffsupp

/-- **`ℤ[S(HC)]`-vanishing-at-`1` combinations are `A_0`-supported** (the Peterfalvi (5.x)
`ℤ[S, M^#] = ℤ[S, A_0]` condition for the uniform degree-`w₁` family `S(HC)`).  Since every member
`χ ∈ S(HC)` has the same degree `χ(1) = w₁`, any `φ = ∑ c_χ χ ∈ ℤ[S(HC)]` with `φ(1) = 0` has
`w₁·∑ c_χ = 0`, hence `∑ c_χ = 0`, so `φ = ∑ c_χ (χ − χ₀)` collapses to a combination of the
`A_0`-supported differences `χ − χ₀` (`inducedFamily_sub_support`).  Proved by `span_induction` on the
strengthened invariant `(ψ − (ψ(1)·w₁⁻¹)·χ₀).support ⊆ A_0` (closed under `+`/`•`, `= χ − χ₀` on
generators), specialized at `φ(1) = 0`.  This is the `hspan` hypothesis of the Galois-equivariance
`IsCoherent.extension_mapRingEquiv_comm` for the `S(HC)`-coherent `τ₁`. -/
theorem Hypothesis.SHC_zSpan_vanish_support [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan
      {ψ : ClassFunction ↥M ℂ | ψ ∈ inducedFamily M ∧ IsIrreducibleCharacter ψ ∧
        ((ψ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))})
    (hφ1 : φ 1 = 0) :
    φ.support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  classical
  have hw1ne : (hyp.w1 : ℂ) ≠ 0 := by
    have h1 : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
    exact_mod_cast Nat.cast_ne_zero.mpr (by omega : hyp.w1 ≠ 0)
  obtain ⟨χ₀, hχ₀S, hχ₀irr, hχ₀1⟩ := exists_zeta_in_inducedFamily_degree_w1 hyp.typeP hG.odd
    (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)
  suffices hstrong : ∀ ψ ∈ OddOrder.Peterfalvi.S07.zSpan
      {ψ : ClassFunction ↥M ℂ | ψ ∈ inducedFamily M ∧ IsIrreducibleCharacter ψ ∧
        ((ψ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))},
      (ψ - (ψ 1 * (hyp.w1 : ℂ)⁻¹) • χ₀).support ⊆ hyp.A0 by
    have h := hstrong φ hφ
    rwa [hφ1, zero_mul, zero_smul, sub_zero] at h
  intro ψ hψ
  induction hψ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨hxS, _hxirr, hx1⟩ := hx
        rw [hx1, mul_inv_cancel₀ hw1ne, one_smul]
        exact hyp.inducedFamily_sub_support hxS hχ₀S (hx1.trans hχ₀1.symm)
    | zero => simp
    | add x y _ _ hx hy =>
        have hrw : (x + y - ((x + y) 1 * (hyp.w1 : ℂ)⁻¹) • χ₀)
            = (x - (x 1 * (hyp.w1 : ℂ)⁻¹) • χ₀) + (y - (y 1 * (hyp.w1 : ℂ)⁻¹) • χ₀) := by
          rw [ClassFunction.add_apply]; module
        rw [hrw]
        exact (ClassFunction.support_add_subset _ _).trans (Set.union_subset hx hy)
    | smul c x _ hx =>
        have hrw : (c • x - ((c • x) 1 * (hyp.w1 : ℂ)⁻¹) • χ₀)
            = (c : ℂ) • (x - (x 1 * (hyp.w1 : ℂ)⁻¹) • χ₀) := by
          rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply]; module
        rw [hrw]
        exact (ClassFunction.support_smul_subset _ _).trans hx

open scoped FiniteInduce in
/-- **The `S(HC)`-coherent extension `τ₁` commutes with complex conjugation** (Peterfalvi (5.9)(a) /
`cfConjC_Dade_coherent`): for a degree-`w₁` irreducible `ζ ∈ S = inducedFamily M`,
`(ζ^{τ₁})‾ = (ζ‾)^{τ₁}`.  This instantiates the general Galois-equivariance
`IsCoherent.extension_mapRingEquiv_comm` at `σc = conjAe` for the landed `SHC_isCoherent`
coherence: the `A_0`-support condition `hspan` is `SHC_zSpan_vanish_support`, `S` is closed under
conjugation (`inducedFamily_closedUnderConjugate` + `IsIrreducibleCharacter.conj` + degree), the
images lie in `ℤ[Irr G]` (`extension_mem_ZIrr`), and `|S| ≥ 2` via the conjugate pair `{ζ, ζ‾}`
(`inducedFamily_hasNoRealCharacters` in odd order).  This is the `τ₁`-side Galois-equivariance
feeding the (11.8.3) reality `β‾ = β`. -/
theorem Hypothesis.SHC_extension_conj [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {χ : ClassFunction ↥M ℂ} (hχS : χ ∈ inducedFamily M) (hχirr : IsIrreducibleCharacter χ)
    (hχ1 : χ 1 = (hyp.w1 : ℂ)) :
    ((hyp.SHC_isCoherent hG).extension χ).conj = (hyp.SHC_isCoherent hG).extension χ.conj := by
  haveI := hyp.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hbridge : ∀ X : ClassFunction ↥M ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  simp only [hbridge]
  refine (hyp.SHC_isCoherent hG).extension_mapRingEquiv_comm subset_rfl
    (fun ψ hψ => mem_irreducibleCharacters.mpr hψ.2.1)
    (fun ψ hψ hψ1 => hyp.SHC_zSpan_vanish_support hG hψ hψ1)
    Complex.conjAe.toRingEquiv ?_
    (fun ψ hψ => (hyp.SHC_isCoherent hG).extension_mem_ZIrr ψ (Submodule.subset_span hψ))
    ⟨hχS, hχirr, hχ1⟩ ?_
  · rintro ψ ⟨hψS, hψirr, hψ1⟩
    exact ⟨by rw [← hbridge]; exact inducedFamily_closedUnderConjugate M hψS,
      by rw [← hbridge]; exact hψirr.conj,
      by rw [← hbridge, ClassFunction.conj_apply, hψ1, star_natCast]⟩
  · exact ⟨χ.conj, ⟨inducedFamily_closedUnderConjugate M hχS, hχirr.conj, by
      rw [ClassFunction.conj_apply, hχ1, star_natCast]⟩,
      fun h => inducedFamily_hasNoRealCharacters hModd hχS h⟩

/-- **Generic isometry-normalization of a coherent extension**: for any coherent extension `coh`
of `τ` over a set `S` of irreducible characters, an irreducible `ζ ∈ S` has `‖coh ζ‖² = ‖ζ‖² = 1`.
The extension-agnostic core of `SHC_extension_inner_self`, reusable for both `SHC_isCoherent`
and the (11.8.4) branch-2 swap `SHC_swap` (the (11.8.5) extension-generalization). -/
theorem _root_.OddOrder.Peterfalvi.S07.IsCoherent.inner_extension_self_eq_one
    {L H : Type*} [Group L] [Group H] [Fintype L] [Fintype H]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card H : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L H}
    {S : Set (ClassFunction L ℂ)} {A : Set L}
    (coh : OddOrder.Peterfalvi.S07.IsCoherent τ S A)
    {ζ : ClassFunction L ℂ} (hζS : ζ ∈ S) (hζirr : IsIrreducibleCharacter ζ) :
    ClassFunction.inner (coh.extension ζ) (coh.extension ζ) = 1 := by
  rw [coh.extension_inner_eq _ _ (Submodule.subset_span hζS) (Submodule.subset_span hζS),
    OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]

/-- **Generic orthogonality of coherent images of distinct irreducibles**: for a coherent extension
`coh` over `S`, distinct irreducibles `φ, ψ ∈ S` have `⟨coh φ, coh ψ⟩ = ⟨φ, ψ⟩ = 0`.  The
extension-agnostic core of `SHC_extension_inner_of_ne`. -/
theorem _root_.OddOrder.Peterfalvi.S07.IsCoherent.inner_extension_eq_zero_of_ne
    {L H : Type*} [Group L] [Group H] [Fintype L] [Fintype H]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card H : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L H}
    {S : Set (ClassFunction L ℂ)} {A : Set L}
    (coh : OddOrder.Peterfalvi.S07.IsCoherent τ S A)
    {φ ψ : ClassFunction L ℂ} (hφS : φ ∈ S) (hφirr : IsIrreducibleCharacter φ)
    (hψS : ψ ∈ S) (hψirr : IsIrreducibleCharacter ψ) (hne : φ ≠ ψ) :
    ClassFunction.inner (coh.extension φ) (coh.extension ψ) = 0 := by
  rw [coh.extension_inner_eq _ _ (Submodule.subset_span hφS) (Submodule.subset_span hψS),
    OddOrder.RepresentationTheory.irr_cf_inner hφirr hψirr, if_neg hne]

open scoped FiniteInduce in
/-- **`‖ζ^{τ₁}‖² = 1` for the `S(HC)`-coherent extension** (α-grid `S₁`-`τ₁` input to (11.8.2)).
The `S(HC)`-coherence `τ₁ = SHC_isCoherent.extension` is an isometry on `ℤ[S(HC)]`
(`extension_inner_eq`) and the degree-`w₁` irreducible `ζ ∈ S(HC)`, so `‖ζ^{τ₁}‖² = ‖ζ‖² = 1`.
Specializes the generic `IsCoherent.inner_extension_self_eq_one` to `coh = SHC_isCoherent`. -/
theorem Hypothesis.SHC_extension_inner_self [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ClassFunction.inner (coh.extension ζ) (coh.extension ζ) = 1 :=
  coh.inner_extension_self_eq_one ⟨hζS, hζirr, hζ1⟩ hζirr

open scoped FiniteInduce in
/-- **`⟨α_{ij}^τ, ζ^{τ₁}⟩ ∈ ℤ` for the `S(HC)`-coherent extension** (α-grid `S₁`-`τ₁` input to
(11.8.2)).  Both `α_{ij}^τ = hyp.tau(μ_{ij} − δ·μ_{i0} − n·ζ)` (`muGridAlpha_tau_mem_ZIrr`,
coherence-free) and `ζ^{τ₁} = SHC_isCoherent.extension ζ` (`extension_mem_ZIrr`, since `ζ ∈ S(HC)`)
lie in `ℤ·Irr G`, so their inner product is an integer.  This is the integrality that the (11.8.2)
`a`-coefficient argument consumes, now available from `SHC_isCoherent` alone (no full-`S` `coh`). -/
theorem Hypothesis.muGridAlpha_tau_inner_SHC_extension_mem_int [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ) :
    ∃ m : ℤ, ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (m : ℂ) := by
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  have hζZ : coh.extension ζ ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
  exact ClassFunction.inner_mem_ZIrr_int hαZ hζZ

open scoped FiniteInduce in
/-- **`⟨φ^{τ₁}, ψ^{τ₁}⟩ = 0` for distinct `S(HC)` members** (α-grid `S₁`-`τ₁` input to (11.8.2)).
Together with `SHC_extension_inner_self` (`‖φ^{τ₁}‖² = 1`) this says the coherent images
`{φ^{τ₁} : φ ∈ S(HC)}` form an **orthonormal family** — the `S₁^{τ₁}` basis against which the
(11.8.2) decomposition `α_{ij}^τ = X − nζ^{τ₁} + a·∑_{λ∈S₁} λ^{τ₁}` projects.  Proof: `τ₁` is an
isometry on `ℤ[S(HC)]` (`extension_inner_eq`), so `(φ^{τ₁}, ψ^{τ₁}) = (φ, ψ) = 0` for distinct
irreducibles.  Available from `SHC_isCoherent` alone (no full-`S` `coh`). -/
theorem Hypothesis.SHC_extension_inner_of_ne [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    {φ ψ : ClassFunction ↥M ℂ}
    (hφS : φ ∈ inducedFamily M) (hφirr : IsIrreducibleCharacter φ) (hφ1 : φ 1 = (hyp.w1 : ℂ))
    (hψS : ψ ∈ inducedFamily M) (hψirr : IsIrreducibleCharacter ψ) (hψ1 : ψ 1 = (hyp.w1 : ℂ))
    (hne : φ ≠ ψ) :
    ClassFunction.inner (coh.extension φ) (coh.extension ψ) = 0 :=
  coh.inner_extension_eq_zero_of_ne
    ⟨hφS, hφirr, hφ1⟩ hφirr ⟨hψS, hψirr, hψ1⟩ hψirr hne

open scoped FiniteInduce in
/-- **SHC-coherence analog of `tau_zeta_sub_conj_eq_tau1`** (α-grid `S₁`-`τ₁` bridge for (11.8.5)).
For a degree-`w₁` irreducible `ζ ∈ S(HC)`, the Dade image of the supported difference `ζ − ζ̄`
equals the `S(HC)`-coherent split `ζ^{τ₁} − ζ̄^{τ₁}`.  Since `ζ, ζ̄ ∈ S(HC)` and `ζ − ζ̄` is supported
on `A₀`, it lies in the supported lattice `ℤ[S(HC), A₀]` where `SHC_isCoherent.extension` agrees with
`hyp.tau` (`extends_on_supported`); `extension`-linearity (`map_sub`) then splits it.

This is the essential SHC ingredient of the (5.3.b) `⟨ω^σ, ζ^{τ₁}⟩ = 0` argument (via
`inner_left_eq_zero_of_inner_sub_eq_zero` and the coherence-free `(ζ − ζ̄)^τ ⊥ ω^σ`), which the
(11.8.5) `a = 0` step needs — the by-contradiction has `SHC_isCoherent` but not the full-`S` `coh`. -/
theorem Hypothesis.tau_zeta_sub_conj_eq_SHC_extension [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    hyp.tau (ζ - ζ.conj)
      = coh.extension ζ - coh.extension ζ.conj := by
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hζc1 : ζ.conj 1 = (hyp.w1 : ℂ) := by
    rw [ClassFunction.conj_apply, hζ1, star_natCast]
  have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
    Submodule.subset_span ⟨hζS, hζirr, hζ1⟩
  have hspanζc : ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
    Submodule.subset_span ⟨hζcS, hζcirr, hζc1⟩
  have hmem : (ζ - ζ.conj) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} hyp.A0 :=
    ⟨Submodule.sub_mem _ hspanζ hspanζc, hyp.zeta_sub_conj_support hG hodd hζS hζirr⟩
  rw [← coh.extends_on_supported _ hmem, map_sub]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.3), the column-conjugation index at row `0`** ((3.9)(a)/(4.9)(a) on the
row-`0` grids; the `w₂`-side companion of `exists_rowInv_alignedOmegaSigma_conj`, Coq
`cfAut_cycTIiso`/`prTIirr_aut` + `aut_Iirr_eq0`): there is a column index `k` — the
**column-inversion** index, `χ₂(k) = χ₂(j)⁻¹` on the `W₂`-dual — such that complex conjugation
sends the row-`0` grid values at column `j` to the row-`0` values at column `k`, simultaneously
for the `σ`-grid (`(ω_{0j}^σ)‾ = ω_{0k}^σ`, the (3.9) Galois commutation) and for the `M`-side
`μ`-grid (`μ̄_{0j} = μ_{0k}`, the (4.9)(a) conjugation closure; the trivial row-`0` dual is fixed
by inversion, so the row does not move), with matching column signs `δ_k = δ_j` (the (4.9)(a)
sign bridge `δ_j·μ̄_{0j} = δ_k·μ_{0k}` against the common irreducible `μ_{0k}`).  Moreover
`k = 0 ↔ j = 0` (inversion fixes only the trivial column pointer; Coq `aut_Iirr_eq0`), which is
what lets the (11.8.3) reality argument apply the β-independence at column `k`. -/
theorem Hypothesis.exists_colInv_alignedOmegaSigma_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (j : Fin hyp.w2) :
    ∃ k : Fin hyp.w2,
      (k = 0 ↔ j = 0)
      ∧ ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
          (hyp.alignedOmegaSigmaGrid hG hodd 0 j)
        = hyp.alignedOmegaSigmaGrid hG hodd 0 k
      ∧ ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (hyp.muGrid hG hodd 0 j)
        = hyp.muGrid hG hodd 0 k
      ∧ hyp.muColumnSign hG hodd k = hyp.muColumnSign hG hodd j := by
  haveI := hyp.finiteG
  classical
  -- reconstruct the `let`s of `alignedOmegaSigmaGrid`/`muGrid`/`muColumnSign`
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- the `W₂`-dual of an arbitrary column `b`
  let χ₂ : Fin hyp.w2 → ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := fun b =>
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm b)
  -- the column-inversion translated index
  let k : Fin hyp.w2 :=
    finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm ((χ₂ j)⁻¹))
  -- the column dual at `k` is the inverse dual at `j`
  have hχ₂k : χ₂ k = (χ₂ j)⁻¹ := by
    show finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (finCongr hcardW2sub
        ((finCardEquivCharacterGroup _).symm ((χ₂ j)⁻¹)))) = (χ₂ j)⁻¹
    rw [show finCongr hcardW2sub.symm (finCongr hcardW2sub
          ((finCardEquivCharacterGroup _).symm ((χ₂ j)⁻¹)))
        = (finCardEquivCharacterGroup _).symm ((χ₂ j)⁻¹) from by simp]
    exact (finCardEquivCharacterGroup _).apply_symm_apply _
  -- the trivial-column detector: `χ₂ b = 1 ↔ b = 0`
  have hzero : ∀ b : Fin hyp.w2, χ₂ b = 1 ↔ b = 0 := by
    intro b
    constructor
    · intro hb
      rw [← finCardEquivCharacterGroup_zero (h.W2.subgroupOf (h.W1 ⊔ h.W2))] at hb
      have hb0 : finCongr hcardW2sub.symm b = 0 := (finCardEquivCharacterGroup _).injective hb
      exact Fin.ext (by simpa using congrArg Fin.val hb0)
    · intro hb
      show finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm b) = 1
      rw [hb, show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
        finCardEquivCharacterGroup_zero]
  -- `k = 0 ↔ j = 0` (the Coq `aut_Iirr_eq0`)
  have hk0 : k = 0 ↔ j = 0 := by rw [← hzero k, ← hzero j, hχ₂k, inv_eq_one]
  -- §5 `G`-level TI-cyclic hypothesis (for `σ`) and the `W ≤ M ≤ G` transport
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- the transported row-`0` linear character of `tic.W` at column `b`
  let ξ : Fin hyp.w2 → (↥tic.W →* ℂˣ) := fun b =>
    (h.sdiffTICyclicHypothesis.omegaProdChar
      (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) (χ₂ b)).comp e.toMonoidHom
  -- `alignedOmegaSigmaGrid 0 b = σ(ω ξ_b)` for any column `b`
  have step1 : ∀ b, hyp.alignedOmegaSigmaGrid hG hodd 0 b
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd)
          (tic.omega (ξ b) : ClassFunction ↥tic.W ℂ) := by
    intro b
    change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd)
        (tic.omega (ξ b) : ClassFunction ↥tic.W ℂ)
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd)
          (tic.omega (ξ b) : ClassFunction ↥tic.W ℂ)
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  -- the row-`0` dual is trivial (so inversion fixes it)
  have hχ1 : h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1)) = 1 := by
    rw [show (finCongr hcardW1.symm (0 : Fin hyp.w1)) = 0 from by simp, h.w1CharEquiv_zero]
  -- `ξ_j⁻¹ = ξ_k` (`omegaProdChar` inverts coordinatewise; the trivial row factor is fixed)
  have hχ1inv : (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1)))⁻¹
      = h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1)) := by
    rw [hχ1]; exact inv_one
  have hξinv : (ξ j)⁻¹ = ξ k := by
    have hprod : (h.sdiffTICyclicHypothesis.omegaProdChar
          (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) (χ₂ j))⁻¹
        = h.sdiffTICyclicHypothesis.omegaProdChar
            (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) (χ₂ k) := by
      rw [OddOrder.Peterfalvi.S06.omegaProdChar_inv, hχ₂k]
      exact congrArg
        (fun c => h.sdiffTICyclicHypothesis.omegaProdChar c ((χ₂ j)⁻¹)) hχ1inv
    show ((h.sdiffTICyclicHypothesis.omegaProdChar
        (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) (χ₂ j)).comp e.toMonoidHom)⁻¹
      = (h.sdiffTICyclicHypothesis.omegaProdChar
        (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) (χ₂ k)).comp e.toMonoidHom
    refine MonoidHom.ext fun w => Units.val_injective ?_
    rw [MonoidHom.comp_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, ← hprod,
      MonoidHom.inv_apply]
  -- σ-side: `(ω_{0j}^σ)‾ = ω_{0k}^σ` ((3.9) commutation + conjugation inverts the source)
  have hconjσ : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
      (hyp.alignedOmegaSigmaGrid hG hodd 0 j) = hyp.alignedOmegaSigmaGrid hG hodd 0 k := by
    rw [step1 j, step1 k,
      tic.sigma_mapRingEquiv_comm rfl (hyp.canonicalFullDadeApp hG hodd) _ _,
      OddOrder.Peterfalvi.S06.galoisMap_conj_omega, hξinv]
  -- the row-`0` index is fixed by the (4.9)(a) row inversion
  have hrow0 : OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm (0 : Fin hyp.w1))
      = finCongr hcardW1.symm (0 : Fin hyp.w1) := by
    rw [OddOrder.Peterfalvi.S06.rowInv, hχ1, inv_one]
    exact h.w1CharEquiv.symm_apply_eq.mpr hχ1.symm
  -- μ-side: `μ̄_{0j} = μ_{0k}` ((4.9)(a) conjugation closure at the fixed row `0`)
  have hμconj : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (hyp.muGrid hG hodd 0 j)
      = hyp.muGrid hG hodd 0 k := by
    have ej : hyp.muGrid hG hodd 0 j
        = ((h.columnFamily (χ₂ j)).mu (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid; rfl
    have ek : hyp.muGrid hG hodd 0 k
        = ((h.columnFamily (χ₂ k)).mu (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid; rfl
    rw [ej, ek, ← IrreducibleCharacter.galoisMap_apply_coe,
      OddOrder.Peterfalvi.S06.certainType_mu_conj_eq h (χ₂ j) (finCongr hcardW1.symm 0),
      hrow0]
    exact congrArg
      (fun c => ((h.columnFamily c).mu (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ))
      hχ₂k.symm
  -- sign match `δ_k = δ_j` ((4.9)(a) sign bridge against the common irreducible `μ_{0k}`)
  have hsign : hyp.muColumnSign hG hodd k = hyp.muColumnSign hG hodd j := by
    have esj : hyp.muColumnSign hG hodd j = (h.columnFamily (χ₂ j)).sign := by
      unfold Hypothesis.muColumnSign; rfl
    have esk : hyp.muColumnSign hG hodd k = (h.columnFamily (χ₂ k)).sign := by
      unfold Hypothesis.muColumnSign; rfl
    have hbr := OddOrder.Peterfalvi.S06.certainType_mu_conj_bridge h (χ₂ j)
      (finCongr hcardW1.symm 0)
    rw [← IrreducibleCharacter.galoisMap_apply_coe,
      OddOrder.Peterfalvi.S06.certainType_mu_conj_eq h (χ₂ j) (finCongr hcardW1.symm 0),
      ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily (χ₂ j)).sign
        (((h.columnFamily ((χ₂ j)⁻¹)).mu (OddOrder.Peterfalvi.S06.rowInv h
          (finCongr hcardW1.symm 0))) : ClassFunction ↥M ℂ),
      ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily ((χ₂ j)⁻¹)).sign
        (((h.columnFamily ((χ₂ j)⁻¹)).mu (OddOrder.Peterfalvi.S06.rowInv h
          (finCongr hcardW1.symm 0))) : ClassFunction ↥M ℂ)] at hbr
    have hI := congrArg (fun φ => ClassFunction.inner φ
      (((h.columnFamily ((χ₂ j)⁻¹)).mu (OddOrder.Peterfalvi.S06.rowInv h
        (finCongr hcardW1.symm 0))) : ClassFunction ↥M ℂ)) hbr
    simp only [ClassFunction.inner_smul_left, irreducibleCharacter_inner_eq_ite, if_true,
      mul_one] at hI
    rw [esk, esj, hχ₂k]
    exact_mod_cast hI.symm
  exact ⟨k, hk0, hconjσ, hμconj, hsign⟩

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.3) first part, row independence of `β`** (Coq `betaE`, row move): the
(11.8.3) residual `β_{ij} = α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ) + nζ^{τ₁}` at row `i` equals the
row-`0` residual `β_{0j}`.  The `nζ` tails of `α_{ij}` and `α_{0j}` cancel, so the difference of
the `τ`-arguments is the four-corner `μ_{ij} − μ_{0j} − δμ_{i0} + δμ_{00}`, whose Dade image is
`δ·(ω_{ij}^σ − ω_{0j}^σ − ω_{i0}^σ + ω_{00}^σ)` — the δ-scaled Peterfalvi (4.10), threaded here as
`h410` until the §10 instantiation of Hypothesis (4.6) lands (issue 9004) — and the `ω`-corners
cancel against the `δ(ω_{ij}^σ − ω_{i0}^σ)` terms. -/
theorem Hypothesis.beta_row_eq [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) (j : Fin hyp.w2) {ζ : ClassFunction ↥M ℂ} {δ : ℤ} {n : ℕ}
    (h410 : hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd 0 j
          - (δ : ℂ) • hyp.muGrid hG hodd i 0 + (δ : ℂ) • hyp.muGrid hG hodd 0 0)
        = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd 0 j
          - hyp.alignedOmegaSigmaGrid hG hodd i 0 + hyp.alignedOmegaSigmaGrid hG hodd 0 0)) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
      + (n : ℂ) • coh.extension ζ
    = hyp.tau (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
      - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd 0 j - hyp.alignedOmegaSigmaGrid hG hodd 0 0)
      + (n : ℂ) • coh.extension ζ := by
  have harg : (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
        + (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd 0 j
          - (δ : ℂ) • hyp.muGrid hG hodd i 0 + (δ : ℂ) • hyp.muGrid hG hodd 0 0) := by
    module
  rw [harg, map_add, h410]
  module

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.3) first part, column independence of `β` at row `0`** (Coq `betaE`, column
move): for two columns `j, k` of the *same* sign `δ`, the row-`0` residuals agree,
`β_{0j} = β_{0k}`.
The `−δμ_{00} − nζ` tails of `α_{0j}` and `α_{0k}` are identical, so the difference of the
`τ`-arguments is `μ_{0j} − μ_{0k}`, whose Dade image is `δ·(ω_{0j}^σ − ω_{0k}^σ)` — the row-`0`
Peterfalvi (4.8), threaded here as `h48` until the §10 instantiation of Hypothesis (4.6) lands
(issue 9004). -/
theorem Hypothesis.beta_column_eq_zeroRow [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (j k : Fin hyp.w2) {ζ : ClassFunction ↥M ℂ} {δ : ℤ} {n : ℕ}
    (h48 : hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
        = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd 0 j
            - hyp.alignedOmegaSigmaGrid hG hodd 0 k)) :
    hyp.tau (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
      - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd 0 j - hyp.alignedOmegaSigmaGrid hG hodd 0 0)
      + (n : ℂ) • coh.extension ζ
    = hyp.tau (hyp.muGrid hG hodd 0 k - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
      - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd 0 k - hyp.alignedOmegaSigmaGrid hG hodd 0 0)
      + (n : ℂ) • coh.extension ζ := by
  have harg : (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
      = (hyp.muGrid hG hodd 0 k - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
        + (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k) := by
    module
  rw [harg, map_add, h48]
  module

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.3), `β` is real** (Coq `Rbeta`): the (11.8.3) residual
`β = α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ) + nζ^{τ₁}` satisfies `β̄ = β`.  This discharges the `hβr`
hypothesis of the (11.8.5) capstone `residualCoeff_eq_zero`.

Proof (Coq `PFsection11.v` 823-831): reduce to row `0` (`beta_row_eq`, the threaded (4.10)); apply
complex conjugation through each term — `(α_{0j}^τ)‾ = (ᾱ_{0j})^τ` (`tau_mapRingEquiv_comm`, the
`A₀`-support from `muGrid_alpha_support`), `ᾱ_{0j} = μ_{0k} − δμ_{00} − nζ̄` and
`(ω_{0j}^σ)‾ = ω_{0k}^σ`, `(ω_{00}^σ)‾ = ω_{00}^σ` (the column-conjugation index `k`,
`exists_colInv_alignedOmegaSigma_conj`), and `(ζ^{τ₁})‾ = ζ̄^{τ₁}` (`SHC_extension_conj`, odd
order).  The conjugate is thus `β_{0k}` computed at `ζ̄`; the `S(HC)`-coherence
`τ(ζ − ζ̄) = ζ^{τ₁} − ζ̄^{τ₁}` (`tau_zeta_sub_conj_eq_SHC_extension`) trades `ζ̄` back for `ζ`,
giving `β̄ = β_{0k}`; finally `β_{0k} = β_{0j}` by the column move (`beta_column_eq_zeroRow`, the
threaded row-`0` (4.8) at the conjugate column `k ≠ 0`).

The Peterfalvi (4.8)/(4.10) inputs are threaded as `h48`/`h410` until the §10 instantiation of
Hypothesis (4.6) lands (issue 9004); everything else is proved. -/
theorem Hypothesis.beta_isReal [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hconj : ∀ {χ : ClassFunction ↥M ℂ}, χ ∈ inducedFamily M → IsIrreducibleCharacter χ →
      χ 1 = (hyp.w1 : ℂ) → (coh.extension χ).conj = coh.extension χ.conj)
    (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg0 : hyp.muGrid hG hodd 0 j 1 = (d : ℂ)) (hμ00 : hyp.muGrid hG hodd 0 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (h410 : hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd 0 j
          - (δ : ℂ) • hyp.muGrid hG hodd i 0 + (δ : ℂ) • hyp.muGrid hG hodd 0 0)
        = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd 0 j
          - hyp.alignedOmegaSigmaGrid hG hodd i 0 + hyp.alignedOmegaSigmaGrid hG hodd 0 0))
    (h48 : ∀ k : Fin hyp.w2, k ≠ 0 →
        hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
          = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd 0 j
              - hyp.alignedOmegaSigmaGrid hG hodd 0 k)) :
    ClassFunction.IsReal
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        + (n : ℂ) • coh.extension ζ) := by
  haveI := hyp.finiteG
  classical
  -- reduce to row `0` (the threaded (4.10) row move)
  have hrow := hyp.beta_row_eq hG coh hodd i j (ζ := ζ) (n := n) h410
  rw [ClassFunction.IsReal, hrow]
  -- the `.conj = mapRingEquiv conjAe` bridges
  have hbridgeG : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hbridgeM : ∀ X : ClassFunction ↥M ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  -- the column-conjugation index `k` (piece 1) at `j` and at `0`
  obtain ⟨k, hk0iff, hσconj, hμconj, hsign⟩ := hyp.exists_colInv_alignedOmegaSigma_conj hG hodd j
  have hk0 : k ≠ 0 := fun hk => hj0 (hk0iff.mp hk)
  obtain ⟨k₀, hk₀iff, hσ0, hμ0conj, -⟩ := hyp.exists_colInv_alignedOmegaSigma_conj hG hodd 0
  rw [hk₀iff.mpr rfl] at hσ0 hμ0conj
  -- distribute the conjugation over the three terms of `β_{0j}` (pointwise)
  have hdist : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
      (hyp.tau (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd 0 j
            - hyp.alignedOmegaSigmaGrid hG hodd 0 0)
        + (n : ℂ) • coh.extension ζ)
      = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
          (hyp.tau (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ))
        - (δ : ℂ) • (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
            (hyp.alignedOmegaSigmaGrid hG hodd 0 j)
          - ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
            (hyp.alignedOmegaSigmaGrid hG hodd 0 0))
        + (n : ℂ) • ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
            (coh.extension ζ) := by
    ext g
    simp only [ClassFunction.mapRingEquiv_apply, ClassFunction.add_apply, ClassFunction.sub_apply,
      ClassFunction.smul_apply, map_add, map_sub, map_mul, map_intCast, map_natCast]
  -- conjugate of the `M`-side argument: `ᾱ_{0j} = μ_{0k} − δμ_{00} − nζ̄`
  have hαconj : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
      (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
      = hyp.muGrid hG hodd 0 k - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ.conj := by
    have hdistM : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
        (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
        = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (hyp.muGrid hG hodd 0 j)
          - (δ : ℂ) • ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
              (hyp.muGrid hG hodd 0 0)
          - (n : ℂ) • ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv ζ := by
      ext g
      simp only [ClassFunction.mapRingEquiv_apply, ClassFunction.sub_apply,
        ClassFunction.smul_apply, map_sub, map_mul, map_intCast, map_natCast]
    rw [hdistM, hμconj, hμ0conj, ← hbridgeM]
  -- conjugate the three terms: `τ`-Galois (piece 2), σ-grid (piece 1), `τ₁`-Galois (piece 3)
  have hτcomm := hyp.tau_mapRingEquiv_comm Complex.conjAe.toRingEquiv
    (hyp.muGrid_alpha_support hG hodd (i := 0) hj0 hζS hdeg0 hμ00 hζ1 hnf hδj)
  have hζτ : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
      (coh.extension ζ) = coh.extension ζ.conj := by
    rw [← hbridgeG, hconj hζS hζirr hζ1]
  rw [hbridgeG, hdist, hσconj, hσ0, hζτ, ← hτcomm, hαconj]
  -- trade `ζ̄` for `ζ` through the `S(HC)`-coherence, landing on `β_{0k}`
  have hcoh := hyp.tau_zeta_sub_conj_eq_SHC_extension hG coh hodd hζS hζirr hζ1
  have hswap : (hyp.muGrid hG hodd 0 k - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ.conj)
      = (hyp.muGrid hG hodd 0 k - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
        + (n : ℂ) • (ζ - ζ.conj) := by
    module
  have hnτ : hyp.tau ((n : ℂ) • (ζ - ζ.conj)) = (n : ℂ) • hyp.tau (ζ - ζ.conj) := by
    rw [show (n : ℂ) • (ζ - ζ.conj) = ((n : ℤ) : ℂ) • (ζ - ζ.conj) from by norm_num,
      Int.cast_smul_eq_zsmul ℂ (n : ℤ), map_zsmul,
      show (n : ℂ) • hyp.tau (ζ - ζ.conj) = ((n : ℤ) : ℂ) • hyp.tau (ζ - ζ.conj) from by norm_num,
      Int.cast_smul_eq_zsmul ℂ (n : ℤ)]
  rw [hswap, map_add, hnτ, hcoh]
  -- the `β_{0j} = β_{0k}` column move (the threaded row-`0` (4.8) at the conjugate column)
  have hcol := hyp.beta_column_eq_zeroRow hG coh hodd j k (ζ := ζ) (n := n) (h48 k hk0)
  rw [hcol]
  -- assemble: both sides are `β_{0k}` up to the cancelling `nζ^{τ₁}` swap terms
  module

open scoped FiniteInduce in
/-- **Peterfalvi (5.3.b) for the S(HC)-coherent extension** (the (11.8.5) `a = 0` input).  For a
degree-`w₁` irreducible `ζ ∈ S(HC)`, the coherent image `ζ^{τ₁} = SHC_isCoherent.extension ζ` is
orthogonal to every aligned `σ`-grid vector `ω_{ij}^σ`.

Port of the intermediate of `tau1_zeta_vanishes_on_typePV` to the `S(HC)`-coherence (the by-contra
lacks the full-`S` `coh`).  Writing `ω_{ij}^σ = χ_{P j}` (`exists_alignedOmegaSigmaGrid_chiFam_family`,
the *same* `tic`/`canonicalFullDadeApp`), the difference `ζ^{τ₁} − ζ̄^{τ₁} = (ζ − ζ̄)^τ`
(`tau_zeta_sub_conj_eq_SHC_extension`) has `≤ 2 < min(w₁, w₂)` nonzero `σ`-coefficients (each of
`ζ^{τ₁}, ζ̄^{τ₁}` has `≤ 1`, being norm-`1` — `ncard_inner_chiFam_ne_zero_le_one`), so
`sigmaCoeff_eq_zero_of_sigmaNC_lt` gives `⟨ζ^{τ₁} − ζ̄^{τ₁}, χ_{P j}⟩ = 0`; the norm-`1` projection
`inner_left_eq_zero_of_inner_sub_eq_zero` (orthonormal `{ζ^{τ₁}, ζ̄^{τ₁}}` via `SHC_extension_inner_*`)
then upgrades this to `⟨ζ^{τ₁}, χ_{P j}⟩ = 0`. -/
theorem Hypothesis.SHC_extension_inner_alignedOmegaSigma_eq_zero [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) (i : Fin hyp.w1) (j : Fin hyp.w2) :
    ClassFunction.inner (coh.extension ζ)
      (hyp.alignedOmegaSigmaGrid hG hodd i j) = 0 := by
  haveI := hyp.finiteG
  classical
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  obtain ⟨P, _hPinj, hPeq⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  rw [hPeq j]
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hζc1 : ζ.conj 1 = (hyp.w1 : ℂ) := by rw [ClassFunction.conj_apply, hζ1, star_natCast]
  have haZ : coh.extension ζ ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
  have hbZ : coh.extension ζ.conj ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ.conj (Submodule.subset_span ⟨hζcS, hζcirr, hζc1⟩)
  have ha1 : ClassFunction.inner (coh.extension ζ)
      (coh.extension ζ) = 1 := hyp.SHC_extension_inner_self hG coh hζS hζirr hζ1
  have hb1 : ClassFunction.inner (coh.extension ζ.conj)
      (coh.extension ζ.conj) = 1 :=
    hyp.SHC_extension_inner_self hG coh hζcS hζcirr hζc1
  have hab : ClassFunction.inner (coh.extension ζ)
      (coh.extension ζ.conj) = 0 :=
    hyp.SHC_extension_inner_of_ne hG coh hζS hζirr hζ1 hζcS hζcirr hζc1 (fun h => hζne h.symm)
  have hvanish : ∀ w ∈ tic.V, hyp.tau (ζ - ζ.conj) w = 0 := fun w hw =>
    hyp.tau_zeta_sub_conj_vanishes_on_typePV hG hodd hζS hζirr hw
  have hNC : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
      < min (Nat.card ↥tic.W1) (Nat.card ↥tic.W2) := by
    have hbound : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj)) ≤ 2 := by
      have hsub : {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0} ⊆
          {pq | ClassFunction.inner (coh.extension ζ)
              (tic.chiFam hVeq app pq) ≠ 0} ∪
          {pq | ClassFunction.inner (coh.extension ζ.conj)
              (tic.chiFam hVeq app pq) ≠ 0} := by
        intro pq hpq
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
        apply hpq
        change ClassFunction.inner (hyp.tau (ζ - ζ.conj)) (tic.chiFam hVeq app pq) = 0
        rw [hyp.tau_zeta_sub_conj_eq_SHC_extension hG coh hodd hζS hζirr hζ1,
          ClassFunction.inner_sub_left, hcon.1, hcon.2, sub_zero]
      calc tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
          = {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0}.ncard := rfl
        _ ≤ ({pq | ClassFunction.inner (coh.extension ζ)
                (tic.chiFam hVeq app pq) ≠ 0} ∪
              {pq | ClassFunction.inner (coh.extension ζ.conj)
                (tic.chiFam hVeq app pq) ≠ 0}).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ {pq | ClassFunction.inner (coh.extension ζ)
                (tic.chiFam hVeq app pq) ≠ 0}.ncard +
              {pq | ClassFunction.inner (coh.extension ζ.conj)
                (tic.chiFam hVeq app pq) ≠ 0}.ncard :=
            Set.ncard_union_le _ _
        _ ≤ 1 + 1 := by
            gcongr
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app haZ ha1
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app hbZ hb1
        _ = 2 := rfl
    have h3a := tic.three_le_card_W1
    have h3b := tic.three_le_card_W2
    omega
  have hL3 : tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) (P j) = 0 :=
    tic.sigmaCoeff_eq_zero_of_sigmaNC_lt hVeq app hvanish hNC (P j)
  have hdiff : ClassFunction.inner (coh.extension ζ
      - coh.extension ζ.conj) (tic.chiFam hVeq app (P j)) = 0 := by
    rw [← hyp.tau_zeta_sub_conj_eq_SHC_extension hG coh hodd hζS hζirr hζ1]; exact hL3
  have hsZ : tic.chiFam hVeq app (P j) ∈ ZIrr G := (tic.chiFam_spec hVeq app).2.1 (P j)
  have hs1 : ClassFunction.inner (tic.chiFam hVeq app (P j)) (tic.chiFam hVeq app (P j)) = 1 := by
    rw [(tic.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  exact inner_left_eq_zero_of_inner_sub_eq_zero haZ hsZ ha1 hb1 hs1 hab hdiff

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `ζ^{τ₁}` vanishes on `V`, S(HC)-coherent version** (the (11.8.2)/(11.8.5)
input).  For a degree-`w₁` irreducible `ζ ∈ S(HC)` with `ζ̄ ≠ ζ`, the S(HC)-coherent image
`ζ^{τ₁} = SHC_isCoherent.extension ζ` vanishes on `V = typePV`.

Port of `tau1_zeta_vanishes_on_typePV` to the `S(HC)`-coherence (the (11.8) by-contradiction lacks
the full-`S` `coh`).  Same argument as `SHC_extension_inner_alignedOmegaSigma_eq_zero`, but concluded
against every `χ_{pq}` (`eq_zero_of_mem_V_of_inner_chiFam_eq_zero`, Peterfalvi (3.2.d)) rather than a
single aligned grid vector: `(ζ − ζ̄)^τ = ζ^{τ₁} − ζ̄^{τ₁}` (`tau_zeta_sub_conj_eq_SHC_extension`)
vanishes on `V` with `NC ≤ 2 < min(w₁, w₂)`, so `sigmaCoeff_eq_zero_of_sigmaNC_lt` gives
`⟨ζ^{τ₁} − ζ̄^{τ₁}, χ_{pq}⟩ = 0`, and the norm-`1` projection `inner_left_eq_zero_of_inner_sub_eq_zero`
(orthonormal `{ζ^{τ₁}, ζ̄^{τ₁}}`) upgrades it to `⟨ζ^{τ₁}, χ_{pq}⟩ = 0` for every `pq`. -/
theorem Hypothesis.SHC_tau1_zeta_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {v : G} (hv : v ∈ typePV M hyp.typeP) :
    coh.extension ζ v = 0 := by
  haveI := hyp.finiteG
  classical
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hζc1 : ζ.conj 1 = (hyp.w1 : ℂ) := by rw [ClassFunction.conj_apply, hζ1, star_natCast]
  have haZ : coh.extension ζ ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
  have hbZ : coh.extension ζ.conj ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ.conj (Submodule.subset_span ⟨hζcS, hζcirr, hζc1⟩)
  have ha1 : ClassFunction.inner (coh.extension ζ)
      (coh.extension ζ) = 1 := hyp.SHC_extension_inner_self hG coh hζS hζirr hζ1
  have hb1 : ClassFunction.inner (coh.extension ζ.conj)
      (coh.extension ζ.conj) = 1 :=
    hyp.SHC_extension_inner_self hG coh hζcS hζcirr hζc1
  have hab : ClassFunction.inner (coh.extension ζ)
      (coh.extension ζ.conj) = 0 :=
    hyp.SHC_extension_inner_of_ne hG coh hζS hζirr hζ1 hζcS hζcirr hζc1 (fun h => hζne h.symm)
  have hvanish : ∀ w ∈ tic.V, hyp.tau (ζ - ζ.conj) w = 0 := fun w hw =>
    hyp.tau_zeta_sub_conj_vanishes_on_typePV hG hodd hζS hζirr hw
  have hNC : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
      < min (Nat.card ↥tic.W1) (Nat.card ↥tic.W2) := by
    have hbound : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj)) ≤ 2 := by
      have hsub : {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0} ⊆
          {pq | ClassFunction.inner (coh.extension ζ)
              (tic.chiFam hVeq app pq) ≠ 0} ∪
          {pq | ClassFunction.inner (coh.extension ζ.conj)
              (tic.chiFam hVeq app pq) ≠ 0} := by
        intro pq hpq
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
        apply hpq
        change ClassFunction.inner (hyp.tau (ζ - ζ.conj)) (tic.chiFam hVeq app pq) = 0
        rw [hyp.tau_zeta_sub_conj_eq_SHC_extension hG coh hodd hζS hζirr hζ1,
          ClassFunction.inner_sub_left, hcon.1, hcon.2, sub_zero]
      calc tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
          = {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0}.ncard := rfl
        _ ≤ ({pq | ClassFunction.inner (coh.extension ζ)
                (tic.chiFam hVeq app pq) ≠ 0} ∪
              {pq | ClassFunction.inner (coh.extension ζ.conj)
                (tic.chiFam hVeq app pq) ≠ 0}).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ {pq | ClassFunction.inner (coh.extension ζ)
                (tic.chiFam hVeq app pq) ≠ 0}.ncard +
              {pq | ClassFunction.inner (coh.extension ζ.conj)
                (tic.chiFam hVeq app pq) ≠ 0}.ncard :=
            Set.ncard_union_le _ _
        _ ≤ 1 + 1 := by
            gcongr
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app haZ ha1
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app hbZ hb1
        _ = 2 := rfl
    have h3a := tic.three_le_card_W1
    have h3b := tic.three_le_card_W2
    omega
  refine tic.eq_zero_of_mem_V_of_inner_chiFam_eq_zero hVeq app (fun a' b' => ?_) hv
  have hL3 : tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) (a', b') = 0 :=
    tic.sigmaCoeff_eq_zero_of_sigmaNC_lt hVeq app hvanish hNC (a', b')
  have hdiff : ClassFunction.inner (coh.extension ζ
      - coh.extension ζ.conj) (tic.chiFam hVeq app (a', b')) = 0 := by
    rw [← hyp.tau_zeta_sub_conj_eq_SHC_extension hG coh hodd hζS hζirr hζ1]; exact hL3
  have hsZ : tic.chiFam hVeq app (a', b') ∈ ZIrr G := (tic.chiFam_spec hVeq app).2.1 (a', b')
  have hs1 : ClassFunction.inner (tic.chiFam hVeq app (a', b')) (tic.chiFam hVeq app (a', b')) = 1 := by
    rw [(tic.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  exact inner_left_eq_zero_of_inner_sub_eq_zero haZ hsZ ha1 hb1 hs1 hab hdiff

open scoped FiniteInduce in
/-- **`S(HC)` `τ₁`-image vanishes on `V`** for any degree-`w₁` irreducible `χ ∈ inducedFamily M`.
The non-reality hypothesis `χ̄ ≠ χ` of `SHC_tau1_zeta_vanishes_on_typePV` is discharged via
`inducedFamily_degree_w1_conj_ne` (Peterfalvi (1.1)), so this needs only `χ ∈ S(HC)`.  Used to vanish
the `∑_{λ∈S₁} λ^{τ₁}` correction of the (11.8.2) residual `X = α^τ + nζ^{τ₁} − a∑λ^{τ₁}` on `V` in
the general `a ∈ {0, 2}` case. -/
theorem Hypothesis.SHC_extension_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    {χ : ClassFunction ↥M ℂ} (hχS : χ ∈ inducedFamily M) (hχirr : IsIrreducibleCharacter χ)
    (hχ1 : χ 1 = (hyp.w1 : ℂ)) {v : G} (hv : v ∈ typePV M hyp.typeP) :
    coh.extension χ v = 0 :=
  hyp.SHC_tau1_zeta_vanishes_on_typePV hG coh hodd hχS hχirr hχ1
    (hyp.inducedFamily_degree_w1_conj_ne hG hχirr hχ1) hv

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `ψ = X − δ(ω^σ diff)` vanishes on `V`, S(HC)-coherent version** (`a = 0`
form).  Port of `muGridPsi_vanishes_on_typePV` to `S(HC)`-coherence: with `X = α_{ij}^τ + n·ζ^{τ₁}`
(`ζ^{τ₁} = SHC_isCoherent.extension ζ`), the virtual character `ψ = X − δ·(ω_{ij}^σ − ω_{i0}^σ)`
vanishes on `V = typePV`.  Combines the value-on-`V` leg `tau_muGridAlpha_apply_eq_on_typePV`
(`α^τ = δ(ω^σ diff)` on `V`, coherence-free) with `SHC_tau1_zeta_vanishes_on_typePV`
(`ζ^{τ₁}` vanishes on `V`).  For the general `(11.8.2)` residual `X = α^τ + n·ζ^{τ₁} − a·∑λ^{τ₁}`
(`a ∈ {0, 2}`) the extra `∑λ^{τ₁}` also vanishes on `V` (each `λ ∈ S(HC)`, same lemma). -/
theorem Hypothesis.SHC_muGridPsi_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    {i : Fin hyp.w1} {j : Fin hyp.w2} (hj : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    {v : G} (hv : v ∈ typePV M hyp.typeP) :
    (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        + (n : ℂ) • coh.extension ζ
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
            - hyp.alignedOmegaSigmaGrid hG hodd i 0)) v = 0 := by
  have hleg := hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hj hζS hdeg hμ0 hζ1 hnf hδj hv
  have hζv := hyp.SHC_tau1_zeta_vanishes_on_typePV hG coh hodd hζS hζirr hζ1 hζne hv
  simp only [ClassFunction.sub_apply, ClassFunction.add_apply, ClassFunction.smul_apply] at hleg ⊢
  rw [hleg, hζv]
  simp

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖X‖² = 2` and `X ⊥ ζ^{τ₁}`, S(HC)-coherent version** (`a = 0`), where
`X = α_{ij}^τ + n·ζ^{τ₁}` (`ζ^{τ₁} = SHC_isCoherent.extension ζ`).  Given the `a = 0` inner product
`⟨α_{ij}^τ, ζ^{τ₁}⟩ = −n` (`muGridAlpha_tau_residual_norm` with `a = 0`), with `‖α_{ij}^τ‖² = 2 + n²`
(`muGridAlpha_tau_inner_self`) and `‖ζ^{τ₁}‖² = 1` (`SHC_extension_inner_self`):
`⟨X, ζ^{τ₁}⟩ = ⟨α^τ, ζ^{τ₁}⟩ + n‖ζ^{τ₁}‖² = −n + n = 0` and
`‖X‖² = ‖α^τ‖² + 2n⟨α^τ, ζ^{τ₁}⟩ + n²‖ζ^{τ₁}‖² = (2+n²) − 2n² + n² = 2`.  SHC port of
`muGridAlpha_tau_X_inner`, the norm-`2` input to the SHC Dade-image trichotomy (SHC `alpha_tau_image`). -/
theorem Hypothesis.SHC_muGridAlpha_tau_X_inner [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1)
    (hα0 : ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = -(n : ℂ)) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.extension ζ)
        (coh.extension ζ) = 0
    ∧ ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.extension ζ)
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.extension ζ) = 2 := by
  have hnorm_a := hyp.muGridAlpha_tau_inner_self hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
    hdζ h0ζ hδpm
  have hzz := hyp.SHC_extension_inner_self hG coh hζS hζirr hζ1
  have hα0' : ClassFunction.inner (coh.extension ζ)
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      = -(n : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hα0, star_neg, star_natCast]
  constructor
  · simp only [ClassFunction.inner_add_left, ClassFunction.inner_smul_left, hα0, hzz, mul_one]
    ring
  · simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hα0, hα0', hnorm_a, hzz, star_natCast, mul_one]
    ring

open scoped FiniteInduce in
/-- **Peterfalvi (10.5) Dade-image identity, S(HC)-coherent version** (`a = 0`):
`α_{ij}^τ = δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}` with `ζ^{τ₁} = SHC_isCoherent.extension ζ`, given the
`a = 0` inner product `⟨α_{ij}^τ, ζ^{τ₁}⟩ = −n` (`muGridAlpha_tau_residual_norm` with `a = 0`).

SHC port of `tau_muGridAlpha_eq` (the full-`coh` (10.5) endgame, which the (11.8) by-contradiction
cannot use).  Writing `X = α_{ij}^τ + n·ζ^{τ₁}` (`∈ ℤ[Irr G]`, `‖X‖² = 2` via
`SHC_muGridAlpha_tau_X_inner`), the aligned `σ`-grid entries are `χ`-family members
(`exists_alignedOmegaSigmaGrid_chiFam_family`) and `ψ = X − δ(ω^σ diff)` vanishes on `V`
(`SHC_muGridPsi_vanishes_on_typePV`), so the norm-`2` Dade-image trichotomy
`eq_smul_chiFam_diff_of_vanishOnV` forces `X = δ(ω_{ij}^σ − ω_{i0}^σ)`. -/
theorem Hypothesis.SHC_tau_muGridAlpha_eq [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1)
    (hα0 : ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = -(n : ℂ)) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - (n : ℂ) • coh.extension ζ := by
  haveI := hyp.finiteG
  classical
  have hXfacts := hyp.SHC_muGridAlpha_tau_X_inner hG coh hodd i hj0 hζS hζirr hζ1 hdeg hμ0 hnf hδj
    hdζ h0ζ hδpm hα0
  have hτ1ζZ : coh.extension ζ ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  have hXZ : hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      + (n : ℂ) • coh.extension ζ ∈ ZIrr G := by
    refine Submodule.add_mem _ hαZ ?_
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hτ1ζZ n
  obtain ⟨P, hPinj, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  have hPne : P j ≠ P 0 := fun h => hj0 (hPinj h)
  have hPj' : tic.chiFam hVeq app (P j) = hyp.alignedOmegaSigmaGrid hG hodd i j := (hP j).symm
  have hP0' : tic.chiFam hVeq app (P 0) = hyp.alignedOmegaSigmaGrid hG hodd i 0 := (hP 0).symm
  have hψV : ∀ v ∈ tic.V,
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.extension ζ
        - (δ : ℂ) • (tic.chiFam hVeq app (P j) - tic.chiFam hVeq app (P 0))) v = 0 := by
    intro v hv
    rw [hPj', hP0']
    exact hyp.SHC_muGridPsi_vanishes_on_typePV hG coh hodd hj0 hζS hζirr hζ1 hζne hdeg hμ0 hnf hδj hv
  rw [eq_sub_iff_add_eq, ← hPj', ← hP0']
  exact tic.eq_smul_chiFam_diff_of_vanishOnV hVeq app hXZ hXfacts.2 hPne hδpm hψV

open scoped FiniteInduce in
/-- **General `S(HC)`-coherence split** `(ζ − η)^τ = ζ^{τ₁} − η^{τ₁}` for degree-`w₁` irreducibles
`ζ, η ∈ S(HC)` (α-grid `S₁`-`τ₁` input to (11.8.2)).  Generalizes `tau_zeta_sub_conj_eq_SHC_extension`
(the `η = ζ̄` case) to an arbitrary `S(HC)` member: since `ζ, η ∈ S(HC)` have equal degree `w₁`, the
difference `ζ − η` is `A₀`-supported (`inducedFamily_sub_support`) and lies in `ℤ[S(HC)]`, where
`SHC_isCoherent.extension` agrees with `hyp.tau` (`extends_on_supported`). -/
theorem Hypothesis.tau_sub_eq_SHC_extension [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    {ζ η : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hηS : η ∈ inducedFamily M) (hηirr : IsIrreducibleCharacter η) (hη1 : η 1 = (hyp.w1 : ℂ)) :
    hyp.tau (ζ - η)
      = coh.extension ζ - coh.extension η := by
  have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
    Submodule.subset_span ⟨hζS, hζirr, hζ1⟩
  have hspanη : η ∈ OddOrder.Peterfalvi.S07.zSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
    Submodule.subset_span ⟨hηS, hηirr, hη1⟩
  have hmem : (ζ - η) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} hyp.A0 :=
    ⟨Submodule.sub_mem _ hspanζ hspanη, hyp.inducedFamily_sub_support hζS hηS (hζ1.trans hη1.symm)⟩
  rw [← coh.extends_on_supported _ hmem, map_sub]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.2), the `S₁^{τ₁}`-projection coefficient relation**:
`(α_{ij}^τ, ζ^{τ₁}) − (α_{ij}^τ, η^{τ₁}) = −n` for any degree-`w₁` irreducible `η ∈ S(HC)`, `η ≠ ζ`.
Combining the general split `(ζ − η)^τ = ζ^{τ₁} − η^{τ₁}` (`tau_sub_eq_SHC_extension`), the `τ`-isometry
on the supported `α_{ij}` and `ζ − η` (`tau_inner_eq_of_supported`), and the source value `−n`
(`muGridAlpha_inner_zeta_sub_irr`).  Since the orthonormal `{λ^{τ₁} : λ ∈ S₁}` gives
`(α_{ij}^τ, λ^{τ₁})` as the projection coefficient, this forces `(α_{ij}^τ, η^{τ₁}) = a` (constant in
`η ≠ ζ`) and `(α_{ij}^τ, ζ^{τ₁}) = a − n` — the coefficient structure of the (11.8.2) decomposition
`α_{ij}^τ = X − nζ^{τ₁} + a∑_{λ∈S₁}λ^{τ₁}`. -/
theorem Hypothesis.muGridAlpha_tau_inner_SHC_extension_sub [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ η : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hηS : η ∈ inducedFamily M) (hηirr : IsIrreducibleCharacter η)
    (hη1 : η 1 = (hyp.w1 : ℂ)) (hηne : η ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ)
      - ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension η) = -(n : ℂ) := by
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hζηsupp : (ζ - η).support ⊆ hyp.A0 :=
    hyp.inducedFamily_sub_support hζS hηS (hζ1.trans hη1.symm)
  rw [← ClassFunction.inner_sub_right,
    ← hyp.tau_sub_eq_SHC_extension hG coh hζS hζirr hζ1 hηS hηirr hη1,
    hyp.tau_inner_eq_of_supported hαsupp hζηsupp,
    hyp.muGridAlpha_inner_zeta_sub_irr hG hodd i j hζirr hηirr hdζ h0ζ (hη1.trans hζ1.symm) hηne]

open scoped FiniteInduce in
/-- **`SHC_isCoherent.extension` is injective on `S(HC)`** (α-grid `S₁`-`τ₁` input to (11.8.2)):
distinct degree-`w₁` irreducibles of `S(HC)` have distinct coherent images.  Immediate from the
orthonormality (`SHC_extension_inner_self` = 1, `SHC_extension_inner_of_ne` = 0): if the images
coincided, `1 = ⟨φ^{τ₁}, φ^{τ₁}⟩ = ⟨φ^{τ₁}, ψ^{τ₁}⟩ = 0`.  Needed to materialize
`{λ^{τ₁} : λ ∈ S(HC)}` as an orthonormal `Finset` for the (11.8.2) integer projection
(`exists_intProjection_of_orthonormal_ZIrr`). -/
theorem Hypothesis.SHC_extension_inj [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    {φ ψ : ClassFunction ↥M ℂ}
    (hφS : φ ∈ inducedFamily M) (hφirr : IsIrreducibleCharacter φ) (hφ1 : φ 1 = (hyp.w1 : ℂ))
    (hψS : ψ ∈ inducedFamily M) (hψirr : IsIrreducibleCharacter ψ) (hψ1 : ψ 1 = (hyp.w1 : ℂ))
    (heq : coh.extension φ = coh.extension ψ) :
    φ = ψ := by
  by_contra hne
  have h0 : ClassFunction.inner (coh.extension φ) (coh.extension ψ) = 0 :=
    coh.inner_extension_eq_zero_of_ne ⟨hφS, hφirr, hφ1⟩ hφirr ⟨hψS, hψirr, hψ1⟩ hψirr hne
  have h1 : ClassFunction.inner (coh.extension φ) (coh.extension ψ) = 1 := by
    rw [← heq]; exact coh.inner_extension_self_eq_one ⟨hφS, hφirr, hφ1⟩ hφirr
  rw [h0] at h1
  exact one_ne_zero h1.symm

open scoped Classical FiniteInduce in
/-- **`{λ^{τ₁} : λ ∈ S(HC)}` as an orthonormal `ZIrr` `Finset`** (α-grid (11.8.2) setup).  The
coherent images of the degree-`w₁` irreducibles of `S(HC)` form an orthonormal family of virtual
characters of `G`, ready for the integer projection `exists_intProjection_of_orthonormal_ZIrr` of
`α_{ij}^τ` in (11.8.2).  Materialized as the image of the `S(HC)` `IrreducibleCharacter` `Finset`
(the same filter used by `SHC_isCoherent`) under `extension`; orthonormality is
`SHC_extension_inner_self`/`SHC_extension_inner_of_ne` + the injectivity `SHC_extension_inj`. -/
theorem Hypothesis.exists_SHC_extension_orthonormal [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) :
    ∃ R : Finset (ClassFunction G ℂ),
      (∀ β ∈ R, β ∈ ZIrr G) ∧
      (∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0) ∧
      (∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
        φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R) ∧
      (∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) := by
  haveI := hyp.finiteG
  classical
  set s : Finset (IrreducibleCharacter ↥M) :=
    Finset.univ.filter (fun χ => (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
      (χ : ClassFunction ↥M ℂ) 1 = (hyp.w1 : ℂ)) with hs
  refine ⟨s.image (fun χ : IrreducibleCharacter ↥M =>
      coh.extension (χ : ClassFunction ↥M ℂ)), ?_, ?_, ?_, ?_⟩
  · intro β hβ
    rw [Finset.mem_image] at hβ
    obtain ⟨χ, hχs, rfl⟩ := hβ
    rw [hs, Finset.mem_filter] at hχs
    exact coh.extension_mem_ZIrr _
      (Submodule.subset_span ⟨hχs.2.1, χ.2, hχs.2.2⟩)
  · intro α hα β hβ
    rw [Finset.mem_image] at hα hβ
    obtain ⟨χ, hχs, rfl⟩ := hα
    obtain ⟨χ', hχ's, rfl⟩ := hβ
    rw [hs, Finset.mem_filter] at hχs hχ's
    by_cases hχχ' : χ = χ'
    · subst hχχ'; rw [if_pos rfl]
      exact coh.inner_extension_self_eq_one ⟨hχs.2.1, χ.2, hχs.2.2⟩ χ.2
    · have hne : (χ : ClassFunction ↥M ℂ) ≠ (χ' : ClassFunction ↥M ℂ) :=
        fun h => hχχ' (Subtype.ext h)
      rw [coh.inner_extension_eq_zero_of_ne ⟨hχs.2.1, χ.2, hχs.2.2⟩ χ.2 ⟨hχ's.2.1, χ'.2, hχ's.2.2⟩
          χ'.2 hne,
        if_neg (fun hαβ => hχχ' (Subtype.ext
          (hyp.SHC_extension_inj hG coh hχs.2.1 χ.2 hχs.2.2 hχ's.2.1 χ'.2 hχ's.2.2 hαβ)))]
  · intro φ hφS hφirr hφ1
    rw [Finset.mem_image]
    exact ⟨⟨φ, hφirr⟩, by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hφS, hφ1⟩, rfl⟩
  · intro β hβ
    rw [Finset.mem_image] at hβ
    obtain ⟨χ, hχs, rfl⟩ := hβ
    rw [hs, Finset.mem_filter] at hχs
    exact ⟨χ, hχs.2.1, χ.2, hχs.2.2, rfl⟩

/-- **Peterfalvi (11.8.2) arithmetic core**: the integer inequality `n·(a² − 2a) ≤ 2` with `2 ≤ n`
forces `a ∈ {0, 1, 2}`.  (If `a ∉ {0, 1, 2}` then `a ≤ −1` or `a ≥ 3`, so `a² − 2a ≥ 3` and
`n·(a² − 2a) ≥ 2·3 = 6 > 2`.)  This is the numeric heart of (11.8.2)'s `a = 0/1/2` conclusion, fed by
the projection-norm bound `(a − n)² + (|S₁| − 1)a² ≤ n² + 2` once `|S₁| = n` (Peterfalvi (11.8.1)). -/
theorem charParam_a_mem_of_norm_ineq {a : ℤ} {n : ℕ} (hn : 2 ≤ n)
    (h : (n : ℤ) * (a ^ 2 - 2 * a) ≤ 2) : a = 0 ∨ a = 1 ∨ a = 2 := by
  have hn2 : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  by_contra hcon
  push_neg at hcon
  obtain ⟨ha0, ha1, ha2⟩ := hcon
  have ha : a ≤ -1 ∨ 3 ≤ a := by omega
  have hge : 3 ≤ a ^ 2 - 2 * a := by rcases ha with h | h <;> nlinarith
  nlinarith [hge, hn2]

open scoped Classical FiniteInduce in
/-- **Parseval with orthogonal remainder** for the integer projection of a virtual character onto an
orthonormal `ZIrr` family.  For `φ ∈ ZIrr G` and an orthonormal family `R ⊆ ZIrr G`, the integer
projection `exists_intProjection_of_orthonormal_ZIrr` gives coefficients `c` and remainder `Y ⊥ R`
with `φ = ∑ c_α·α + Y`; then `‖φ‖² = ∑_{α∈R} c_α² + ‖Y‖²` (`inner_self_orthonormalSum_eq_sum_sq`,
the cross terms vanishing by `Y ⊥ R`).  This is the (11.8.2) projection-norm identity feeding
`(a − n)² + (|S₁| − 1)a² ≤ ‖α^τ‖²`. -/
theorem inner_self_eq_sum_sq_add_of_intProjection [Finite G] {φ : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) {R : Finset (ClassFunction G ℂ)} (hZ : ∀ α ∈ R, α ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0) :
    ∃ (c : ClassFunction G ℂ → ℤ) (Y : ClassFunction G ℂ),
      (∀ α ∈ R, ClassFunction.inner φ α = (c α : ℂ)) ∧
      ClassFunction.inner φ φ = (∑ α ∈ R, (c α : ℂ) ^ 2) + ClassFunction.inner Y Y ∧
      (∀ α ∈ R, ClassFunction.inner Y α = 0) ∧
      φ = (∑ α ∈ R, (c α : ℂ) • α) + Y ∧ Y ∈ ZIrr G := by
  obtain ⟨c, Y, hcoeff, hdecomp, hYorth⟩ :=
    OddOrder.RepresentationTheory.ClassFunction.exists_intProjection_of_orthonormal_ZIrr hφ hZ horth
  refine ⟨c, Y, hcoeff, ?_, hYorth, hdecomp, ?_⟩
  · have hXY : ClassFunction.inner (∑ α ∈ R, (c α : ℂ) • α) Y = 0 := by
      rw [inner_sum_left]
      refine Finset.sum_eq_zero fun a ha => ?_
      rw [ClassFunction.inner_smul_left]
      have haY : ClassFunction.inner a Y = 0 := by
        rw [inner_conj_symm Y a, hYorth a ha, star_zero]
      rw [haY, mul_zero]
    have hYX : ClassFunction.inner Y (∑ α ∈ R, (c α : ℂ) • α) = 0 := by
      rw [inner_sum_right]
      refine Finset.sum_eq_zero fun a ha => ?_
      rw [OddOrder.RepresentationTheory.inner_smul_right, hYorth a ha, mul_zero]
    conv_lhs => rw [hdecomp]
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right, ClassFunction.inner_add_right,
      inner_self_orthonormalSum_eq_sum_sq horth, hXY, hYX]
    ring
  · have hsumZ : (∑ α ∈ R, (c α : ℂ) • α) ∈ ZIrr G :=
      Submodule.sum_mem _ fun α hα => by
        rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem (hZ α hα) _
    have hYeq : Y = φ - (∑ α ∈ R, (c α : ℂ) • α) := by rw [hdecomp]; abel
    rw [hYeq]; exact Submodule.sub_mem _ hφ hsumZ

open scoped Classical in
/-- **Sum of squares with one distinguished coefficient.**  If `e ∈ R`, `f e = x`, and `f β = y` for
every `β ∈ R` with `β ≠ e`, then `∑_{β∈R} (f β)² = x² + (|R| − 1)·y²`.  Used in (11.8.2) to evaluate
`∑_{λ∈S(HC)} c(λ^{τ₁})² = (a − n)² + (|S₁| − 1)·a²` (the `ζ^{τ₁}` coefficient is `a − n`, every other
coefficient is `a`). -/
theorem sum_sq_eq_of_split {R : Finset (ClassFunction G ℂ)} {e : ClassFunction G ℂ} (he : e ∈ R)
    {f : ClassFunction G ℂ → ℤ} {x y : ℤ} (hx : f e = x)
    (hy : ∀ β ∈ R, β ≠ e → f β = y) :
    (∑ β ∈ R, (f β : ℂ) ^ 2) = (x : ℂ) ^ 2 + ((R.card : ℂ) - 1) * (y : ℂ) ^ 2 := by
  classical
  rw [← Finset.add_sum_erase R (fun β => (f β : ℂ) ^ 2) he]
  have he2 : ((f e : ℂ)) ^ 2 = (x : ℂ) ^ 2 := by rw [hx]
  have hsum : ∑ β ∈ R.erase e, (f β : ℂ) ^ 2 = ((R.erase e).card : ℂ) * (y : ℂ) ^ 2 := by
    rw [Finset.sum_congr rfl fun β hβ => by
          rw [hy β (Finset.mem_of_mem_erase hβ) (Finset.ne_of_mem_erase hβ)],
      Finset.sum_const, nsmul_eq_mul]
  have hcard : ((R.erase e).card : ℂ) = (R.card : ℂ) - 1 := by
    have h1 : 1 ≤ R.card := Finset.card_pos.mpr ⟨e, he⟩
    rw [Finset.card_erase_of_mem he, Nat.cast_sub h1, Nat.cast_one]
  rw [he2, hsum, hcard]

open scoped FiniteInduce in
/-- **Integer bound from a Parseval remainder.**  If `(A : ℂ) + ⟨Y, Y⟩ = (B : ℂ)` with `A, B ∈ ℤ`,
then `A ≤ B` — since `⟨Y, Y⟩` is a non-negative real (`inner_self_re_nonneg`).  Turns the (11.8.2)
Parseval equality `∑ c_β² + ‖Y‖² = ‖α^τ‖²` into the inequality `∑ c_β² ≤ ‖α^τ‖²`. -/
theorem int_le_of_add_inner_self_eq [Finite G] {A B : ℤ} {Y : ClassFunction G ℂ}
    (h : (A : ℂ) + ClassFunction.inner Y Y = (B : ℂ)) : A ≤ B := by
  have hnn : (0 : ℝ) ≤ (ClassFunction.inner Y Y).re := inner_self_re_nonneg Y
  have hre := congrArg Complex.re h
  rw [Complex.add_re, Complex.intCast_re, Complex.intCast_re] at hre
  have hle : (A : ℝ) ≤ (B : ℝ) := by linarith
  exact_mod_cast hle

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.2), residual decomposition + norm.**  Projecting `α_{ij}^τ` onto the
orthonormal `S₁^{τ₁} = R` (`exists_intProjection`) gives integer coefficients `c_β = ⟨α_{ij}^τ, β⟩`
and remainder `Y ⊥ R` (this `Y` is Peterfalvi's residual `X`, with `α_{ij}^τ = X − nζ^{τ₁} +
a·∑_{λ∈S₁} λ^{τ₁}`).  The coefficient relation (`muGridAlpha_tau_inner_SHC_extension_sub`, cont.³²)
forces `c(η^{τ₁}) = a` (constant, `η ≠ ζ`) with `a := c(ζ^{τ₁}) + n`, so `⟨α_{ij}^τ, ζ^{τ₁}⟩ =
c(ζ^{τ₁}) = a − n`.  Parseval (`inner_self_eq_sum_sq_add_of_intProjection`) + the sum split
(`sum_sq_eq_of_split`) + `‖α_{ij}^τ‖² = 2 + n²` (`muGridAlpha_tau_inner_self`) give the residual norm
`‖X‖² = 2 + n² − ((a−n)² + (n−1)a²)`.  With `‖X‖² ≥ 0` (`int_le_of_add_inner_self_eq`) this is
`n(a²−2a) ≤ 2`, whence `a ∈ {0,1,2}` (`charParam_a_mem_of_norm_ineq`); and for `a = 0` or `a = 2`
the norm collapses to `‖X‖² = 2` — the input to Peterfalvi's `X = ω_{ij}^σ − ω_{i0}^σ`.

`R` and `|R| = n` are supplied by the caller: `R` from `exists_SHC_extension_orthonormal`, and
`|R| = n` is the (11.8.1) `|S₁| = n` (gated on the §9↔§10 carrier bridge). -/
theorem Hypothesis.muGridAlpha_tau_residual_norm [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) :
    ∃ (a : ℤ) (Y : ClassFunction G ℂ),
      (a = 0 ∨ a = 1 ∨ a = 2) ∧
      (∀ β ∈ R, ClassFunction.inner Y β = 0) ∧
      ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (a : ℂ) - (n : ℂ) ∧
      ClassFunction.inner Y Y
        = (2 : ℂ) + (n : ℂ) ^ 2 - (((a : ℂ) - (n : ℂ)) ^ 2 + ((n : ℂ) - 1) * (a : ℂ) ^ 2) ∧
      ((a = 0 ∨ a = 2) → ClassFunction.inner Y Y = 2) ∧
      Y ∈ ZIrr G ∧
      (∀ v ∈ typePV M hyp.typeP,
        Y v = hyp.tau
          (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) v) ∧
      hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        = Y - (n : ℂ) • coh.extension ζ + (a : ℂ) • ∑ β ∈ R, β := by
  classical
  have hζR : coh.extension ζ ∈ R := hRmem ζ hζS hζirr hζ1
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  obtain ⟨c, Y, hcoeff, hnorm, hYorth, hdecomp, hYZ⟩ :=
    inner_self_eq_sum_sq_add_of_intProjection hαZ hZ horth
  set a : ℤ := c (coh.extension ζ) + (n : ℤ) with hadef
  have hcζ : c (coh.extension ζ) = a - (n : ℤ) := by rw [hadef]; ring
  have hcη : ∀ β ∈ R, β ≠ coh.extension ζ → c β = a := by
    intro β hβR hβne
    obtain ⟨η, hηS, hηirr, hη1, rfl⟩ := hRrev β hβR
    have hηζ : η ≠ ζ := fun h => hβne (by rw [h])
    have hsub := hyp.muGridAlpha_tau_inner_SHC_extension_sub hG coh hodd i hj0 hζS hζirr hζ1
      hηS hηirr hη1 hηζ hdeg hμ0 hnf hδj hdζ h0ζ
    rw [hcoeff _ hζR, hcoeff _ (hRmem η hηS hηirr hη1)] at hsub
    have hcast : ((c (coh.extension η) : ℤ) : ℂ) = ((a : ℤ) : ℂ) := by
      rw [hadef]; push_cast; push_cast at hsub; linear_combination -hsub
    exact_mod_cast hcast
  have hsplit := sum_sq_eq_of_split hζR hcζ hcη
  rw [hRn] at hsplit
  have hnorm2 := hyp.muGridAlpha_tau_inner_self hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
    hdζ h0ζ hδpm
  rw [hnorm2, hsplit] at hnorm
  have hnormY : ClassFunction.inner Y Y
      = (2 : ℂ) + (n : ℂ) ^ 2 - (((a : ℂ) - (n : ℂ)) ^ 2 + ((n : ℂ) - 1) * (a : ℂ) ^ 2) := by
    push_cast at hnorm ⊢
    linear_combination -hnorm
  have hbound : a = 0 ∨ a = 1 ∨ a = 2 := by
    have hineq : (a - (n : ℤ)) ^ 2 + ((n : ℤ) - 1) * a ^ 2 ≤ 2 + (n : ℤ) ^ 2 := by
      apply int_le_of_add_inner_self_eq (Y := Y)
      push_cast at hnorm ⊢
      linear_combination -hnorm
    have hfinal : (n : ℤ) * (a ^ 2 - 2 * a) ≤ 2 := by nlinarith [hineq]
    exact charParam_a_mem_of_norm_ineq hn2 hfinal
  have hYV : ∀ v ∈ typePV M hyp.typeP,
      Y v = hyp.tau
        (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) v := by
    intro v hv
    have hsumv : (∑ β ∈ R, (c β : ℂ) • β) v = 0 := by
      rw [ClassFunction.finset_sum_apply]
      refine Finset.sum_eq_zero fun β hβR => ?_
      obtain ⟨φ, hφS, hφirr, hφ1, rfl⟩ := hRrev β hβR
      rw [ClassFunction.smul_apply,
        hyp.SHC_extension_vanishes_on_typePV hG coh hodd hφS hφirr hφ1 hv, mul_zero]
    have hYeq : Y = hyp.tau
        (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (∑ β ∈ R, (c β : ℂ) • β) := by rw [hdecomp]; abel
    rw [hYeq, ClassFunction.sub_apply, hsumv, sub_zero]
  have hdecompA : hyp.tau
      (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = Y - (n : ℂ) • coh.extension ζ + (a : ℂ) • ∑ β ∈ R, β := by
    have hkey : (∑ β ∈ R, (c β : ℂ) • β)
        = -((n : ℂ) • coh.extension ζ) + (a : ℂ) • ∑ β ∈ R, β := by
      rw [Finset.smul_sum,
        ← Finset.add_sum_erase R (fun β => (c β : ℂ) • β) hζR,
        ← Finset.add_sum_erase R (fun β => (a : ℂ) • β) hζR, hcζ]
      have herase : ∑ β ∈ R.erase (coh.extension ζ), (c β : ℂ) • β
          = ∑ β ∈ R.erase (coh.extension ζ), (a : ℂ) • β :=
        Finset.sum_congr rfl fun β hβ => by
          rw [hcη β (Finset.mem_of_mem_erase hβ) (Finset.ne_of_mem_erase hβ)]
      rw [herase]; push_cast; module
    rw [hdecomp, hkey]; abel
  refine ⟨a, Y, hbound, hYorth, ?_, hnormY, ?_, hYZ, hYV, hdecompA⟩
  · rw [hcoeff _ hζR, hcζ]; push_cast; ring
  · intro ha02
    rw [hnormY]
    rcases ha02 with h | h <;> rw [h] <;> push_cast <;> ring

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.2), the `a ∈ {0, 1, 2}` bound** — the projection of
`muGridAlpha_tau_residual_norm` onto just the coefficient `a` and `⟨α_{ij}^τ, ζ^{τ₁}⟩ = a − n`. -/
theorem Hypothesis.muGridAlpha_tau_proj_a_mem [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) :
    ∃ a : ℤ, (a = 0 ∨ a = 1 ∨ a = 2) ∧
      ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (a : ℂ) - (n : ℂ) := by
  obtain ⟨a, _, ha, _, hinner, _, _, _, _, _⟩ := hyp.muGridAlpha_tau_residual_norm hG coh hodd i hj0 hζS
    hζirr hζ1 hdeg hμ0 hnf hδj hdζ h0ζ hδpm hn2 hRn hZ horth hRmem hRrev
  exact ⟨a, ha, hinner⟩

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.2), the residual is a `σ`-grid difference** (general `a ∈ {0, 2}` case):
the residual `X = α_{ij}^τ + n·ζ^{τ₁} − a·∑_{λ∈S₁} λ^{τ₁}` (`= Y`, the `S₁^{τ₁}`-orthogonal Parseval
remainder) equals `δ·(ω_{ij}^σ − ω_{i0}^σ)` when `a ∈ {0, 2}` (`‖X‖² = 2`).

Feeds the (11.8.5) `a = 0` argument (`β = a·∑λ^{τ₁}` then (5.3.b)).  From
`muGridAlpha_tau_residual_norm` the residual `Y` satisfies `‖Y‖² = 2` (for `a ∈ {0, 2}`),
`Y ∈ ℤ[Irr G]`, and — crucially — `Y = α_{ij}^τ` on `V` (the `∑λ^{τ₁}` correction vanishes there, each
`λ ∈ S(HC)` being a non-real degree-`w₁` irreducible, `SHC_extension_vanishes_on_typePV`).  Then
`ψ = Y − δ(ω^σ diff)` vanishes on `V` (with the value-on-`V` leg `tau_muGridAlpha_apply_eq_on_typePV`,
`α^τ = δ(ω^σ diff)` there), so the norm-`2` Dade-image trichotomy `eq_smul_chiFam_diff_of_vanishOnV`
forces `Y = δ(ω_{ij}^σ − ω_{i0}^σ)`. -/
theorem Hypothesis.SHC_residual_eq_omegaSigma_diff [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) :
    ∃ (a : ℤ) (Y : ClassFunction G ℂ),
      (a = 0 ∨ a = 1 ∨ a = 2) ∧
      ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (a : ℂ) - (n : ℂ) ∧
      ((a = 0 ∨ a = 2) → Y = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
          - hyp.alignedOmegaSigmaGrid hG hodd i 0)) ∧
      hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        = Y - (n : ℂ) • coh.extension ζ + (a : ℂ) • ∑ β ∈ R, β := by
  obtain ⟨a, Y, hbound, hYorth, hinner, hnorm, hnorm2case, hYZ, hYV, hdecompA⟩ :=
    hyp.muGridAlpha_tau_residual_norm hG coh hodd i hj0 hζS hζirr hζ1 hdeg hμ0 hnf hδj hdζ h0ζ hδpm hn2
      hRn hZ horth hRmem hRrev
  refine ⟨a, Y, hbound, hinner, ?_, hdecompA⟩
  intro ha02
  haveI := hyp.finiteG
  classical
  obtain ⟨P, hPinj, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  have hPne : P j ≠ P 0 := fun h => hj0 (hPinj h)
  have hPj' : tic.chiFam hVeq app (P j) = hyp.alignedOmegaSigmaGrid hG hodd i j := (hP j).symm
  have hP0' : tic.chiFam hVeq app (P 0) = hyp.alignedOmegaSigmaGrid hG hodd i 0 := (hP 0).symm
  have hψV : ∀ v ∈ tic.V,
      (Y - (δ : ℂ) • (tic.chiFam hVeq app (P j) - tic.chiFam hVeq app (P 0))) v = 0 := by
    intro v hv
    rw [hPj', hP0']
    have hleg := hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj hv
    rw [ClassFunction.sub_apply, hYV v hv, hleg, sub_self]
  rw [← hPj', ← hP0']
  exact tic.eq_smul_chiFam_diff_of_vanishOnV hVeq app hYZ (hnorm2case ha02) hPne hδpm hψV

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5) `G`-side `ω`-grid pairing** `(ω_{ij}^σ − ω_{i0}^σ, ∑_r ω_{r0}^σ) = −1`
(`0 < j`).  By `alignedOmegaSigmaGrid_inner`: `(ω_{ij}^σ, ω_{r0}^σ) = 0` (`j ≠ 0`) and
`(ω_{i0}^σ, ω_{r0}^σ) = [i = r]`, so the sum is `0 − 1 = −1`.  Feeds the `(α_{ij}^τ, ∑ω_{r0}^σ) = −δ`
step of the (11.8.5) two-way computation. -/
theorem Hypothesis.alignedOmegaSigma_diff_inner_zeroColumnSum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) :
    ClassFunction.inner
        (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = -1 := by
  classical
  rw [ClassFunction.inner_sub_left, OddOrder.RepresentationTheory.inner_sum_right,
    OddOrder.RepresentationTheory.inner_sum_right]
  have h1 : ∀ r : Fin hyp.w1, ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hodd i j)
      (hyp.alignedOmegaSigmaGrid hG hodd r 0) = 0 := fun r => by
    rw [hyp.alignedOmegaSigmaGrid_inner hG hodd i r j 0, if_neg]; rintro ⟨_, h⟩; exact hj0 h
  have h2 : ∀ r : Fin hyp.w1, ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hodd i 0)
      (hyp.alignedOmegaSigmaGrid hG hodd r 0) = (if i = r then (1 : ℂ) else 0) := fun r => by
    rw [hyp.alignedOmegaSigmaGrid_inner hG hodd i r 0 0]; simp
  rw [Finset.sum_congr rfl (fun r _ => h1 r), Finset.sum_congr rfl (fun r _ => h2 r),
    Finset.sum_const_zero, Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  ring

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5) `G`-side (5.3.b) sum** `(ζ^{τ₁}, ∑_r ω_{r0}^σ) = 0`: each
`(ζ^{τ₁}, ω_{r0}^σ) = 0` (`SHC_extension_inner_alignedOmegaSigma_eq_zero`), summed over the rows. -/
theorem Hypothesis.SHC_extension_inner_zeroColumnOmegaSigma_sum [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) :
    ClassFunction.inner (coh.extension ζ)
        (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = 0 := by
  rw [OddOrder.RepresentationTheory.inner_sum_right]
  refine Finset.sum_eq_zero fun r _ => ?_
  exact hyp.SHC_extension_inner_alignedOmegaSigma_eq_zero hG coh hodd hζS hζirr hζ1 hζne r 0

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5) `G`-side (5.3.b) sum over `S₁`** `(∑_{β∈R} β, ∑_r ω_{r0}^σ) = 0`: each
`β = λ^{τ₁}` (`hRrev`) is a degree-`w₁` `S(HC)` coherent image, non-real (`inducedFamily_degree_w1_conj_ne`),
so `(λ^{τ₁}, ∑_r ω_{r0}^σ) = 0` (`SHC_extension_inner_zeroColumnOmegaSigma_sum`), summed over `R`. -/
theorem Hypothesis.R_sum_inner_zeroColumnOmegaSigma_sum [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    {R : Finset (ClassFunction G ℂ)}
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) :
    ClassFunction.inner (∑ β ∈ R, β)
        (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = 0 := by
  rw [inner_sum_left]
  refine Finset.sum_eq_zero fun β hβR => ?_
  obtain ⟨φ, hφS, hφirr, hφ1, rfl⟩ := hRrev β hβR
  exact hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG coh hodd hφS hφirr hφ1
    (hyp.inducedFamily_degree_w1_conj_ne hG hφirr hφ1)

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.4), dichotomy form.**  Under the (11.8) contradiction hypothesis — the
residual `(μ₀ − ζ)^τ − ∑_r ω_{r0}^σ` is orthogonal to every `ω_{ij}^σ` — the Dade image
`(μ₀ − ζ)^τ` differs from `∑_r ω_{r0}^σ` by a **single signed coherent extension**: either
`(μ₀ − ζ)^τ = ∑_r ω_{r0}^σ − ζ^{τ₁}` (the normalized (11.8.4) form), or the degree-`w₁` family
`S₁ = S(HC)` is the bare conjugate pair `{ζ, ζ̄}` and `(μ₀ − ζ)^τ = ∑_r ω_{r0}^σ + ζ̄^{τ₁}`.

Textbook proof (p. 66): write `(μ₀ − ζ)^τ = ∑_r ω_{r0}^σ − χ`.  The orthogonality hypothesis pins
`⟨(μ₀ − ζ)^τ, ω_{r0}^σ⟩ = 1`, so `‖χ‖² = ‖μ₀ − ζ‖² − w₁ = 1` (Dade isometry on the `A₀`-supported
lattice, `‖μ₀ − ζ‖² = w₁ + 1` from `inner_muColumnZero_sub_zeta_self`).  Computing
`⟨(μ₀ − ζ)^τ, (ζ − ζ̄)^τ⟩ = ⟨μ₀ − ζ, ζ − ζ̄⟩ = −1` against the supported split
`(ζ − ζ̄)^τ = ζ^{τ₁} − ζ̄^{τ₁}` and the (5.3.b) orthogonalities `⟨λ^{τ₁}, ∑_r ω_{r0}^σ⟩ = 0` gives
`⟨χ, ζ^{τ₁}⟩ − ⟨χ, ζ̄^{τ₁}⟩ = 1`, with both inner products integers (`ZIrr` pairing) of square
`≤ 1` (Cauchy–Schwarz in the unit-norm integral lattice), whence `⟨χ, ζ^{τ₁}⟩ = 1` (then
`χ = ζ^{τ₁}` by positive definiteness) or `⟨χ, ζ̄^{τ₁}⟩ = −1` (then `χ = −ζ̄^{τ₁}`).  In the second
case any third family member `λ ∈ S₁ − {ζ, ζ̄}` would give
`1 = ⟨μ₀ − ζ, λ − ζ⟩ = ⟨(μ₀ − ζ)^τ, λ^{τ₁} − ζ^{τ₁}⟩ = 0`, so `S₁ = {ζ, ζ̄}`.

The textbook's "we may assume" is the replacement of `τ₁` by its negated conjugate-swap
`λ ↦ −(λ̄)^{τ₁}` in the second branch — deferred to the consumer, since the swap is again a
coherent extension of `τ` on `ℤ[S₁]` precisely because `S₁ = {ζ, ζ̄}` (every `A₀`-supported lattice
element is then an integer multiple of `ζ − ζ̄`). -/
theorem Hypothesis.tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (horth : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
          - ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i' 0)
        (hyp.alignedOmegaSigmaGrid hG hodd i j) = 0) :
    hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - (hyp.SHC_isCoherent hG).extension ζ
    ∨ ((∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
          lam 1 = (hyp.w1 : ℂ) → lam = ζ ∨ lam = ζ.conj) ∧
        hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
          = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
            + (hyp.SHC_isCoherent hG).extension ζ.conj) := by
  haveI := hyp.finiteG
  classical
  have h3 : (3 : ℕ) ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  -- generic unit-norm integral-lattice toolkit: the Cauchy–Schwarz bound `m² ≤ 1` and the
  -- positive-definiteness equalities `⟨A, θ⟩ = ±1 → A = ±θ` for unit-norm `A`, `θ`.
  have hbound : ∀ (A θ : ClassFunction G ℂ) (m : ℤ),
      ClassFunction.inner A A = 1 → ClassFunction.inner A θ = (m : ℂ) →
      ClassFunction.inner θ θ = 1 → m * m ≤ 1 := by
    intro A θ m hA hm hθ
    have hθA : ClassFunction.inner θ A = (m : ℂ) := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hm, star_intCast]
    have hval : ClassFunction.inner (A - (m : ℂ) • θ) (A - (m : ℂ) • θ)
        = ((1 - m * m : ℤ) : ℂ) := by
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, hA, hm, hθA, hθ,
        star_intCast]
      push_cast
      ring
    have hre := OddOrder.RepresentationTheory.inner_self_re_nonneg (A - (m : ℂ) • θ)
    rw [hval] at hre
    have h1 : (0 : ℝ) ≤ ((1 - m * m : ℤ) : ℝ) := by simpa using hre
    have h2 : (0 : ℤ) ≤ 1 - m * m := by exact_mod_cast h1
    linarith
  have heq : ∀ A θ : ClassFunction G ℂ, ClassFunction.inner A A = 1 →
      ClassFunction.inner A θ = 1 → ClassFunction.inner θ θ = 1 → A = θ := by
    intro A θ hA hAθ hθ
    have hθA : ClassFunction.inner θ A = 1 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hAθ, star_one]
    have hz : ClassFunction.inner (A - θ) (A - θ) = 0 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, hA, hAθ, hθA, hθ]
      ring
    have h0 : A - θ = 0 := by
      refine OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero ?_
      rw [hz]
      simp
    exact sub_eq_zero.mp h0
  have heqneg : ∀ A θ : ClassFunction G ℂ, ClassFunction.inner A A = 1 →
      ClassFunction.inner A θ = -1 → ClassFunction.inner θ θ = 1 → A = -θ := by
    intro A θ hA hAθ hθ
    have hθA : ClassFunction.inner θ A = -1 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hAθ]
      simp
    have hz : ClassFunction.inner (A + θ) (A + θ) = 0 := by
      rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
        ClassFunction.inner_add_right, hA, hAθ, hθA, hθ]
      ring
    have h0 : A + θ = 0 := by
      refine OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero ?_
      rw [hz]
      simp
    exact add_eq_zero_iff_eq_neg.mp h0
  -- conjugate-family facts for `ζ`
  have hζne : ζ.conj ≠ ζ := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hζc1 : ζ.conj 1 = (hyp.w1 : ℂ) := by
    rw [ClassFunction.conj_apply, hζ1, star_natCast]
  have hζmem : ζ ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hζirr
  have hζcmem : ζ.conj ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hζcirr
  -- supports
  have hsupp : ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ).support ⊆ hyp.A0 :=
    hyp.muColumnZero_sub_zeta_support hG hodd hζS hζ1
  have hsuppd : (ζ - ζ.conj).support ⊆ hyp.A0 := hyp.zeta_sub_conj_support hG hodd hζS hζirr
  -- `ψ = (μ₀ − ζ)^τ ∈ ZIrr G`
  have hμ0Z : (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) ∈ ZIrr ↥M :=
    Submodule.sum_mem _ (fun i _ => (hyp.muGrid_isIrreducible hG hodd i 0).mem_ZIrr)
  have hdiffZ : ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) ∈ ZIrr ↥M :=
    Submodule.sub_mem _ hμ0Z hζirr.mem_ZIrr
  have hψZ : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hyp.hconj hsupp hdiffZ
  have heζZ : (hyp.SHC_isCoherent hG).extension ζ ∈ ZIrr G :=
    (hyp.SHC_isCoherent hG).extension_mem_ZIrr ζ (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
  have heζcZ : (hyp.SHC_isCoherent hG).extension ζ.conj ∈ ZIrr G :=
    (hyp.SHC_isCoherent hG).extension_mem_ZIrr ζ.conj
      (Submodule.subset_span ⟨hζcS, hζcirr, hζc1⟩)
  -- `M`-side orthogonality facts
  have hμζ : ClassFunction.inner (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) ζ = 0 := by
    rw [inner_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr ?_
    rw [hyp.muGrid_zero_column_apply_one hG hodd i, hζ1]
    intro he
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast he.symm
    omega
  have hμζc : ClassFunction.inner (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) ζ.conj = 0 := by
    rw [inner_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζcirr ?_
    rw [hyp.muGrid_zero_column_apply_one hG hodd i, hζc1]
    intro he
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast he.symm
    omega
  have hζζ : ClassFunction.inner ζ ζ = 1 := by
    rw [irr_cf_inner hζmem hζmem, if_pos rfl]
  have hζζc : ClassFunction.inner ζ ζ.conj = 0 := by
    rw [irr_cf_inner hζmem hζcmem, if_neg hζne.symm]
  -- `G`-side norm bookkeeping under the orthogonality hypothesis
  have hΩr : ∀ r : Fin hyp.w1,
      ClassFunction.inner (∑ r' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r' 0)
        (hyp.alignedOmegaSigmaGrid hG hodd r 0) = 1 := by
    intro r
    rw [inner_sum_left, Finset.sum_eq_single r]
    · rw [hyp.alignedOmegaSigmaGrid_inner hG hodd r r 0 0, if_pos ⟨rfl, rfl⟩]
    · intro r' _ hne
      rw [hyp.alignedOmegaSigmaGrid_inner hG hodd r' r 0 0, if_neg fun h => hne h.1]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hψr : ∀ r : Fin hyp.w1,
      ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hodd r 0) = 1 := by
    intro r
    have h := horth r 0
    rw [ClassFunction.inner_sub_left, sub_eq_zero] at h
    exact h.trans (hΩr r)
  have hψΩ : ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_congr rfl fun r _ => hψr r, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hΩψ : ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hψΩ, star_natCast]
  have hΩnorm : ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_congr rfl fun r _ => hΩr r, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hψnorm : ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = ((hyp.w1 + 1 : ℕ) : ℂ) := by
    rw [hyp.tau_inner_eq_of_supported hsupp hsupp]
    exact inner_muColumnZero_sub_zeta_self hG hyp hζirr hζ1
  -- `χ = ∑_r ω_{r0}^σ − (μ₀ − ζ)^τ` has norm `1`
  have hχnorm : ClassFunction.inner
      ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = 1 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hΩnorm, hΩψ, hψΩ, hψnorm]
    push_cast
    ring
  -- the (5.3.b) orthogonalities `⟨∑_r ω_{r0}^σ, λ^{τ₁}⟩ = 0`
  have heΩ : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ)
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = 0 :=
    hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG (hyp.SHC_isCoherent hG) hodd hζS hζirr hζ1 hζne
  have hΩe : ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
      ((hyp.SHC_isCoherent hG).extension ζ) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, heΩ, star_zero]
  have hζcne : (ζ.conj).conj ≠ ζ.conj := by
    rw [ClassFunction.conj_conj]
    exact hζne.symm
  have heΩc : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = 0 :=
    hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG (hyp.SHC_isCoherent hG) hodd hζcS hζcirr hζc1 hζcne
  have hΩec : ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
      ((hyp.SHC_isCoherent hG).extension ζ.conj) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, heΩc, star_zero]
  -- the integer coefficients `s = ⟨ψ, ζ^{τ₁}⟩`, `t = ⟨ψ, ζ̄^{τ₁}⟩` with `s − t = −1`
  obtain ⟨s, hs⟩ := ClassFunction.inner_mem_ZIrr_int hψZ heζZ
  obtain ⟨t, ht⟩ := ClassFunction.inner_mem_ZIrr_int hψZ heζcZ
  have hGside : ClassFunction.inner
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (hyp.tau (ζ - ζ.conj)) = -1 := by
    rw [hyp.tau_inner_eq_of_supported hsupp hsuppd, ClassFunction.inner_sub_left,
      ClassFunction.inner_sub_right, ClassFunction.inner_sub_right, hμζ, hμζc, hζζ, hζζc]
    ring
  rw [hyp.tau_zeta_sub_conj_eq_SHC_extension hG (hyp.SHC_isCoherent hG) hodd hζS hζirr hζ1,
    ClassFunction.inner_sub_right, hs, ht] at hGside
  have hstz : s - t = -1 := by exact_mod_cast hGside
  -- Cauchy–Schwarz bounds and the integer dichotomy `s = −1 ∨ t = 1`
  have hee : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ)
      ((hyp.SHC_isCoherent hG).extension ζ) = 1 :=
    hyp.SHC_extension_inner_self hG (hyp.SHC_isCoherent hG) hζS hζirr hζ1
  have heec : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
      ((hyp.SHC_isCoherent hG).extension ζ.conj) = 1 :=
    hyp.SHC_extension_inner_self hG (hyp.SHC_isCoherent hG) hζcS hζcirr hζc1
  have hmA : ClassFunction.inner
      ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      ((hyp.SHC_isCoherent hG).extension ζ) = ((-s : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, hΩe, hs]
    push_cast
    ring
  have hmAc : ClassFunction.inner
      ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      ((hyp.SHC_isCoherent hG).extension ζ.conj) = ((-t : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, hΩec, ht]
    push_cast
    ring
  have hs2 : s * s ≤ 1 := by
    have h := hbound _ _ (-s) hχnorm hmA hee
    have h' : s * s = -s * -s := by ring
    rw [h']
    exact h
  have ht2 : t * t ≤ 1 := by
    have h := hbound _ _ (-t) hχnorm hmAc heec
    have h' : t * t = -t * -t := by ring
    rw [h']
    exact h
  have hsle : s ≤ 1 := by nlinarith [mul_self_nonneg (s - 1)]
  have hsge : -1 ≤ s := by nlinarith [mul_self_nonneg (s + 1)]
  have htle : t ≤ 1 := by nlinarith [mul_self_nonneg (t - 1)]
  have htge : -1 ≤ t := by nlinarith [mul_self_nonneg (t + 1)]
  have hcase : s = -1 ∨ t = 1 := by omega
  rcases hcase with hsval | htval
  · -- `⟨χ, ζ^{τ₁}⟩ = 1`: `χ = ζ^{τ₁}`, the normalized (11.8.4) form
    left
    have hAe : ClassFunction.inner
        ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        ((hyp.SHC_isCoherent hG).extension ζ) = 1 := by
      rw [ClassFunction.inner_sub_left, hΩe, hs, hsval]
      push_cast
      ring
    have hχe := heq _ _ hχnorm hAe hee
    rw [← hχe]
    abel
  · -- `⟨χ, ζ̄^{τ₁}⟩ = −1`: `χ = −ζ̄^{τ₁}` and `S₁ = {ζ, ζ̄}`
    right
    have hAec : ClassFunction.inner
        ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        ((hyp.SHC_isCoherent hG).extension ζ.conj) = -1 := by
      rw [ClassFunction.inner_sub_left, hΩec, ht, htval]
      push_cast
      ring
    have hχec := heqneg _ _ hχnorm hAec heec
    have hψeq : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          + (hyp.SHC_isCoherent hG).extension ζ.conj := by
      rw [sub_eq_iff_eq_add] at hχec
      rw [hχec]
      abel
    refine ⟨fun lam hlamS hlamirr hlam1 => ?_, hψeq⟩
    by_contra hboth
    rw [not_or] at hboth
    obtain ⟨hlamzeta, hlamzetac⟩ := hboth
    have hlamne : lam.conj ≠ lam := hyp.inducedFamily_degree_w1_conj_ne hG hlamirr hlam1
    have hmulam : ClassFunction.inner (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) lam = 0 := by
      rw [inner_sum_left]
      refine Finset.sum_eq_zero fun i _ => ?_
      refine hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hlamirr ?_
      rw [hyp.muGrid_zero_column_apply_one hG hodd i, hlam1]
      intro he
      have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast he.symm
      omega
    have hlammem : lam ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hlamirr
    have hzetalam : ClassFunction.inner ζ lam = 0 := by
      rw [irr_cf_inner hζmem hlammem, if_neg (Ne.symm hlamzeta)]
    have hsupplam : (lam - ζ).support ⊆ hyp.A0 :=
      hyp.inducedFamily_sub_support hlamS hζS (by rw [hlam1, hζ1])
    have hGlam : ClassFunction.inner
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        (hyp.tau (lam - ζ)) = 1 := by
      rw [hyp.tau_inner_eq_of_supported hsupp hsupplam, ClassFunction.inner_sub_left,
        ClassFunction.inner_sub_right, ClassFunction.inner_sub_right, hmulam, hμζ, hzetalam, hζζ]
      ring
    have hspanlam : lam ∈ OddOrder.Peterfalvi.S07.zSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
      Submodule.subset_span ⟨hlamS, hlamirr, hlam1⟩
    have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
      Submodule.subset_span ⟨hζS, hζirr, hζ1⟩
    have hmemsupp : (lam - ζ) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} hyp.A0 :=
      ⟨Submodule.sub_mem _ hspanlam hspanζ, hsupplam⟩
    have htaulam : hyp.tau (lam - ζ) = (hyp.SHC_isCoherent hG).extension lam
        - (hyp.SHC_isCoherent hG).extension ζ := by
      rw [← (hyp.SHC_isCoherent hG).extends_on_supported _ hmemsupp, map_sub]
    have heOmegalam : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension lam)
        (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = 0 :=
      hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG (hyp.SHC_isCoherent hG) hodd hlamS hlamirr hlam1 hlamne
    have hOmegalam : ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        ((hyp.SHC_isCoherent hG).extension lam) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, heOmegalam, star_zero]
    have heclam : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
        ((hyp.SHC_isCoherent hG).extension lam) = 0 :=
      hyp.SHC_extension_inner_of_ne hG (hyp.SHC_isCoherent hG) hζcS hζcirr hζc1 hlamS hlamirr hlam1 (Ne.symm hlamzetac)
    have hece : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
        ((hyp.SHC_isCoherent hG).extension ζ) = 0 :=
      hyp.SHC_extension_inner_of_ne hG (hyp.SHC_isCoherent hG) hζcS hζcirr hζc1 hζS hζirr hζ1 hζne
    rw [htaulam, ClassFunction.inner_sub_right, hψeq, ClassFunction.inner_add_left,
      ClassFunction.inner_add_left, hOmegalam, heclam, hΩe, hece] at hGlam
    norm_num at hGlam

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.4), the branch-2 "we may assume" swap.**  When the degree-`w₁` family
`S₁ = S(HC)` is the bare conjugate pair `{ζ, ζ̄}` (the second branch of
`tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal`), the map `φ ↦ −(ζ̄-side extension of φ̄)`, i.e.
`SHC_swap.extension φ = −(SHC_isCoherent.extension φ.conj)`, is again a **coherent extension of `τ`
to `ℤ[S(HC)]`** — the textbook's replacement of `ζ^{τ₁}, ζ̄^{τ₁}` by `−ζ̄^{τ₁}, −ζ^{τ₁}` (p. 66).

The four `IsCoherent` fields:
* **isometry on `ℤ[S(HC)]`**: `S(HC)` is closed under conjugation (`inducedFamily` is, degrees are
  preserved), so `φ̄, ψ̄ ∈ ℤ[S(HC)]`; `⟨SHC(φ̄), SHC(ψ̄)⟩ = ⟨φ̄, ψ̄⟩ = star⟨φ,ψ⟩ = ⟨φ,ψ⟩`
  (`inner_conj_conj` and the reality of a `ZIrr` pairing);
* **agrees with `τ` on `ℤ[S(HC), A₀]`**: this is where `S(HC) = {ζ, ζ̄}` is used — every
  `A₀`-supported element of `span{ζ, ζ̄}` is a multiple `a(ζ − ζ̄)` (value at `1` is `(a+b)w₁ = 0`), on which
  `SHC_swap` and `SHC` both send `ζ − ζ̄ ↦ ζ^{τ₁} − ζ̄^{τ₁} = τ(ζ − ζ̄)`;
* **maps into `ZIrr`** and **nonzero-supported witness `ζ − ζ̄`**: inherited from `SHC`.

Combined with the dichotomy this gives the h114-producing extension in *both* branches (branch 1:
`SHC_isCoherent`; branch 2: this swap), i.e. Peterfalvi's "we may assume `(μ₀−ζ)^τ = ∑ω − ζ^{τ₁}`"
holds for a canonical choice of coherent `τ₁`. -/
noncomputable def Hypothesis.SHC_swap [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (htwo : ∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
      lam 1 = (hyp.w1 : ℂ) → lam = ζ ∨ lam = ζ.conj) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} hyp.A0 := by
  haveI := hyp.finiteG
  classical
  set SHCset : Set (ClassFunction ↥M ℂ) :=
    {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} with hSHCset
  -- the `ζ̄`-side degree-`w₁` conjugate facts
  have hζne : ζ.conj ≠ ζ := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hζc1 : ζ.conj 1 = (hyp.w1 : ℂ) := by rw [ClassFunction.conj_apply, hζ1, star_natCast]
  have hζmem : ζ ∈ SHCset := ⟨hζS, hζirr, hζ1⟩
  have hζcmem : ζ.conj ∈ SHCset := ⟨hζcS, hζcirr, hζc1⟩
  -- `SHCset` is closed under conjugation.
  have hconj_closed : ∀ φ ∈ SHCset, φ.conj ∈ SHCset := by
    rintro φ ⟨hφS, hφirr, hφ1⟩
    exact ⟨inducedFamily_closedUnderConjugate M hφS, hφirr.conj, by
      rw [ClassFunction.conj_apply, hφ1, star_natCast]⟩
  -- the swap extension `φ ↦ −SHC(φ̄)`, packaged as an integral character map.
  set ext' : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G :=
    -((hyp.SHC_isCoherent hG).extension.comp
      (ClassFunction.mapRingEquivLinear (G := ↥M) Complex.conjAe.toRingEquiv)) with hext'def
  have hconjbridge : ∀ φ : ClassFunction ↥M ℂ,
      ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv φ = φ.conj := fun φ => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hext'apply : ∀ φ : ClassFunction ↥M ℂ,
      ext' φ = -((hyp.SHC_isCoherent hG).extension φ.conj) := by
    intro φ
    rw [hext'def, LinearMap.neg_apply, LinearMap.comp_apply,
      ClassFunction.mapRingEquivLinear_apply, hconjbridge]
  have hconj_zsmul : ∀ (n : ℤ) (x : ClassFunction ↥M ℂ), (n • x).conj = n • x.conj := by
    intro n x
    rw [← hconjbridge (n • x), ClassFunction.mapRingEquiv_zsmul, hconjbridge x]
  -- span-level conjugation closure.
  have hspan_conj : ∀ φ : ClassFunction ↥M ℂ, φ ∈ OddOrder.Peterfalvi.S07.zSpan SHCset →
      φ.conj ∈ OddOrder.Peterfalvi.S07.zSpan SHCset := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hconj_closed x hx)
    | zero => rw [ClassFunction.conj_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [ClassFunction.conj_add]; exact Submodule.add_mem _ hx hy
    | smul n x _ hx => rw [hconj_zsmul]; exact Submodule.smul_mem _ n hx
  -- span elements are `ZIrr`-members (so pairings are integers, hence real).
  have hspan_ZIrr : ∀ φ : ClassFunction ↥M ℂ, φ ∈ OddOrder.Peterfalvi.S07.zSpan SHCset →
      φ ∈ ZIrr ↥M := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hx.2.1.mem_ZIrr
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul n x _ hx => exact Submodule.smul_mem _ n hx
  refine ⟨⟨ζ - ζ.conj, ⟨?_, ?_⟩, ?_⟩, ext', ?_, ?_, ?_⟩
  · -- `ζ − ζ̄ ∈ ℤ[S(HC)]`
    exact Submodule.sub_mem _ (Submodule.subset_span hζmem) (Submodule.subset_span hζcmem)
  · -- `ζ − ζ̄` is `A₀`-supported
    exact hyp.zeta_sub_conj_support hG hodd hζS hζirr
  · -- `ζ − ζ̄ ≠ 0`
    intro h
    exact hζne (sub_eq_zero.mp h).symm
  · -- **isometry on `ℤ[S(HC)]`**
    intro φ ψ hφ hψ
    have hφc := hspan_conj φ hφ
    have hψc := hspan_conj ψ hψ
    rw [hext'apply φ, hext'apply ψ, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
      neg_neg, (hyp.SHC_isCoherent hG).extension_inner_eq _ _ hφc hψc,
      OddOrder.RepresentationTheory.inner_conj_conj]
    obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int (hspan_ZIrr φ hφ) (hspan_ZIrr ψ hψ)
    rw [hm, star_intCast]
  · -- **agrees with `τ` on `ℤ[S(HC), A₀]`** — uses `S(HC) = {ζ, ζ̄}`
    rintro φ ⟨hφspan, hφsupp⟩
    -- `S(HC) = {ζ, ζ̄}` as sets, so `ℤ[S(HC)] = span{ζ, ζ̄}`.
    have hset_eq : SHCset = {ζ, ζ.conj} := by
      apply Set.eq_of_subset_of_subset
      · rintro x ⟨hxS, hxirr, hx1⟩
        exact htwo x hxS hxirr hx1
      · rintro x (rfl | rfl)
        · exact hζmem
        · exact hζcmem
    have hφpair : φ ∈ Submodule.span ℤ ({ζ, ζ.conj} : Set (ClassFunction ↥M ℂ)) := by
      rwa [OddOrder.Peterfalvi.S07.zSpan, hset_eq] at hφspan
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hφpair
    -- support in `A₀` (which excludes `1`) forces the value at `1` to vanish, so `a + b = 0`.
    have h1notA : (1 : ↥M) ∉ hyp.A0 := by
      intro h1
      have hg : ((1 : ↥M) : G) ∈ typePA0 M hyp.typeP := h1
      rw [OneMemClass.coe_one] at hg
      exact hyp.dadeData.dade.ne_one hg rfl
    have hφ1 : φ 1 = 0 := by
      by_contra hne
      exact h1notA (hφsupp (Function.mem_support.mpr hne))
    have hval1 : (a : ℂ) * (hyp.w1 : ℂ) + (b : ℂ) * (hyp.w1 : ℂ) = 0 := by
      have hc := congrArg (fun f : ClassFunction ↥M ℂ => (f : ↥M → ℂ) 1) hab
      simp only [← Int.cast_smul_eq_zsmul ℂ, ClassFunction.add_apply,
        ClassFunction.smul_apply] at hc
      rw [hζ1, hζc1] at hc
      rw [hc]; exact hφ1
    have hw1ne : (hyp.w1 : ℂ) ≠ 0 := by
      have h3 : (3 : ℕ) ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
      exact_mod_cast (by omega : hyp.w1 ≠ 0)
    have hab0 : a + b = 0 := by
      have hfac : ((a : ℂ) + (b : ℂ)) * (hyp.w1 : ℂ) = 0 := by linear_combination hval1
      have hz : (a : ℂ) + (b : ℂ) = 0 := (mul_eq_zero.mp hfac).resolve_right hw1ne
      exact_mod_cast hz
    have hb : b = -a := by omega
    -- so `φ = a(ζ − ζ̄)`.
    have hφeq : φ = (a : ℤ) • (ζ - ζ.conj) := by
      rw [← hab, hb]; module
    -- both `SHC_swap` and `τ` send `ζ − ζ̄ ↦ ζ^{τ₁} − ζ̄^{τ₁}`.
    have hswapdiff : ext' (ζ - ζ.conj)
        = (hyp.SHC_isCoherent hG).extension ζ - (hyp.SHC_isCoherent hG).extension ζ.conj := by
      rw [map_sub, hext'apply ζ, hext'apply ζ.conj, ClassFunction.conj_conj]
      abel
    have htaudiff : hyp.tau (ζ - ζ.conj)
        = (hyp.SHC_isCoherent hG).extension ζ - (hyp.SHC_isCoherent hG).extension ζ.conj :=
      hyp.tau_zeta_sub_conj_eq_SHC_extension hG (hyp.SHC_isCoherent hG) hodd hζS hζirr hζ1
    rw [hφeq, map_zsmul, map_zsmul, hswapdiff, htaudiff]
  · -- **maps into `ZIrr`**
    intro φ hφ
    rw [hext'apply φ]
    exact neg_mem ((hyp.SHC_isCoherent hG).extension_mem_ZIrr φ.conj (hspan_conj φ hφ))

open scoped FiniteInduce in
/-- **h114 for the branch-2 swap.**  In the second branch of
`tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal` (`S(HC) = {ζ, ζ̄}` and
`(μ₀−ζ)^τ = ∑ω_{r0}^σ + ζ̄^{τ₁}`), the swapped coherent extension `SHC_swap` satisfies the
normalized (11.8.4) identity `(μ₀−ζ)^τ = ∑ω_{r0}^σ − SHC_swap.extension ζ`: indeed
`SHC_swap.extension ζ = −ζ̄^{τ₁}`, so `∑ω − SHC_swap(ζ) = ∑ω + ζ̄^{τ₁} = (μ₀−ζ)^τ`.  This is the
h114-form the (11.8.5) capstone consumes, now available in branch 2 with the swapped `τ₁`. -/
theorem Hypothesis.SHC_swap_h114 [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (htwo : ∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
      lam 1 = (hyp.w1 : ℂ) → lam = ζ ∨ lam = ζ.conj)
    (hbranch2 : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          + (hyp.SHC_isCoherent hG).extension ζ.conj) :
    hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension ζ := by
  haveI := hyp.finiteG
  classical
  have hswapζ : (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension ζ
      = -((hyp.SHC_isCoherent hG).extension ζ.conj) := by
    change (-((hyp.SHC_isCoherent hG).extension.comp
      (ClassFunction.mapRingEquivLinear (G := ↥M) Complex.conjAe.toRingEquiv))) ζ = _
    rw [LinearMap.neg_apply, LinearMap.comp_apply, ClassFunction.mapRingEquivLinear_apply,
      show ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv ζ = ζ.conj from by
        ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl]
  rw [hswapζ, sub_neg_eq_add, hbranch2]

open scoped FiniteInduce in
/-- **The branch-2 swap commutes with complex conjugation** (the `hconj` P4 input the (11.8.5)
capstone `residualCoeff_eq_zero` needs for the swap branch).  For a degree-`w₁` irreducible
`χ ∈ S(HC)`, `(SHC_swap.extension χ)‾ = SHC_swap.extension χ‾`.  Both sides equal `−SHC(χ‾‾)`:
`SHC_swap.extension φ = −SHC(φ‾)`, so `(SHC_swap χ)‾ = (−SHC(χ‾))‾ = −(SHC(χ‾))‾ = −SHC(χ‾‾)`
(the last by `SHC_extension_conj` at `χ‾`), while `SHC_swap χ‾ = −SHC(χ‾‾)` directly. -/
theorem Hypothesis.SHC_swap_conj [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (htwo : ∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
      lam 1 = (hyp.w1 : ℂ) → lam = ζ ∨ lam = ζ.conj)
    {χ : ClassFunction ↥M ℂ} (hχS : χ ∈ inducedFamily M) (hχirr : IsIrreducibleCharacter χ)
    (hχ1 : χ 1 = (hyp.w1 : ℂ)) :
    ((hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension χ).conj
      = (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension χ.conj := by
  haveI := hyp.finiteG
  classical
  have hχcS : χ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hχS
  have hχcirr : IsIrreducibleCharacter χ.conj := hχirr.conj
  have hχc1 : χ.conj 1 = (hyp.w1 : ℂ) := by rw [ClassFunction.conj_apply, hχ1, star_natCast]
  have hswap : ∀ φ : ClassFunction ↥M ℂ, (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension φ
      = -((hyp.SHC_isCoherent hG).extension φ.conj) := fun φ => by
    change (-((hyp.SHC_isCoherent hG).extension.comp
      (ClassFunction.mapRingEquivLinear (G := ↥M) Complex.conjAe.toRingEquiv))) φ = _
    rw [LinearMap.neg_apply, LinearMap.comp_apply, ClassFunction.mapRingEquivLinear_apply,
      show ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv φ = φ.conj from by
        ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl]
  rw [hswap χ, hswap χ.conj, ClassFunction.conj_neg,
    hyp.SHC_extension_conj hG hχcS hχcirr hχc1]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.4), the h114-producing coherent extension.**  Under the (11.8) contradiction
hypothesis (the residual `(μ₀ − ζ)^τ − ∑_r ω_{r0}^σ` is orthogonal to `(Irr W)^σ`), there is a
coherent extension `ν` of `τ` to `ℤ[S(HC)]` for which the normalized (11.8.4) identity
`(μ₀ − ζ)^τ = ∑_r ω_{r0}^σ − ν.extension ζ` holds.  In the generic (first-branch) case `ν` is the
canonical `SHC_isCoherent`; in the degenerate `S(HC) = {ζ, ζ̄}` case `ν` is the conjugate-swap
`SHC_swap` — Peterfalvi's "we may assume `(μ₀ − ζ)^τ = ∑ω_{i0}^σ − ζ^{τ₁}`" (p. 66), now a clean
`∃`-statement with no residual sorry.  This is the interface the (11.8.5) capstone consumes once its
`τ₁`-machinery is taken over an arbitrary coherent extension. -/
theorem Hypothesis.exists_coherent_extension_h114_of_orthogonal [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (horth : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
          - ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i' 0)
        (hyp.alignedOmegaSigmaGrid hG hodd i j) = 0) :
    ∃ ν : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0,
      (∀ {χ : ClassFunction ↥M ℂ}, χ ∈ inducedFamily M → IsIrreducibleCharacter χ →
        χ 1 = (hyp.w1 : ℂ) → (ν.extension χ).conj = ν.extension χ.conj) ∧
      hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) - ν.extension ζ := by
  rcases hyp.tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal hG hodd hζS hζirr hζ1 horth with
    h1 | ⟨htwo, h2⟩
  · exact ⟨hyp.SHC_isCoherent hG,
      (fun hχS hχirr hχ1 => hyp.SHC_extension_conj hG hχS hχirr hχ1), h1⟩
  · exact ⟨hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo,
      (fun hχS hχirr hχ1 => hyp.SHC_swap_conj hG hodd hζS hζirr hζ1 htwo hχS hχirr hχ1),
      hyp.SHC_swap_h114 hG hodd hζS hζirr hζ1 htwo h2⟩

open scoped Classical in
/-- **Cross-Parseval for a virtual character.**  For `Δ ∈ ZIrr G` and any `φ`,
`⟨φ, Δ⟩ = ∑_{χ : Irr} ⟨φ, χ⟩ · ⟨Δ, χ⟩`.  From the Fourier reconstruction `Δ = ∑_χ ⟨Δ,χ⟩·χ`
(`sum_inner_irreducibleCharacter_smul`) and `inner_smul_right`; the `star` from conjugate-linearity
vanishes because `⟨Δ,χ⟩` is a real integer (`mem_ZIrr_inner_int`). -/
theorem mem_ZIrr_inner_eq_sum_over_irr [Finite G] [Fintype G] [Fintype (IrreducibleCharacter G)]
    [Invertible (Nat.card G : ℂ)] {φ Δ : ClassFunction G ℂ} (hΔ : Δ ∈ ZIrr G) :
    ClassFunction.inner φ Δ
      = ∑ χ : IrreducibleCharacter G,
          ClassFunction.inner φ (χ : ClassFunction G ℂ)
            * ClassFunction.inner Δ (χ : ClassFunction G ℂ) := by
  conv_lhs => rw [← OddOrder.RepresentationTheory.sum_inner_irreducibleCharacter_smul Δ]
  rw [OddOrder.RepresentationTheory.inner_sum_right]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [OddOrder.RepresentationTheory.inner_smul_right]
  obtain ⟨m, hm⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int χ hΔ
  rw [hm, star_intCast, mul_comm]

/-- **Parity of a sum over a fixed-point-free involution** with an involution-invariant integer
weight.  If `g` is a fixed-point-free involution on `s` and `f (g a) = f a` for all `a ∈ s`, then
`∑_{a ∈ s} f a` is even — each orbit `{a, g a}` contributes `2·f a`.  (Proof via `ZMod 2`:
`(f a : ZMod 2) + (f (g a) : ZMod 2) = 2·(f a) = 0`, so `Finset.sum_involution` kills the sum mod 2.)
This is the combinatorial core of the Peterfalvi (11.8.5) "`a` even from `β` real" parity — the
conjugation involution `χ ↦ χ̄` on `Irr G ∖ {1}` is fixed-point-free by Peterfalvi (1.1). -/
theorem even_sum_of_involution {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℤ}
    (g : ∀ a ∈ s, α) (g_mem : ∀ a ha, g a ha ∈ s) (g_ne : ∀ a ha, g a ha ≠ a)
    (g_inv : ∀ a ha, g (g a ha) (g_mem a ha) = a) (hf : ∀ a ha, f (g a ha) = f a) :
    Even (∑ a ∈ s, f a) := by
  suffices h : ((∑ a ∈ s, f a : ℤ) : ZMod 2) = 0 by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by push_cast at hk; omega⟩
  rw [Int.cast_sum]
  refine Finset.sum_involution g ?_ (fun a ha _ => g_ne a ha) g_mem g_inv
  intro a ha
  rw [hf a ha]
  exact CharTwo.add_self_eq_zero _

/-- **Inner product of two conjugated class functions** `⟨φ̄, ψ̄⟩ = conj ⟨φ, ψ⟩`.  Pointwise:
`∑_g star(φ g)·ψ g = conj (∑_g φ g · star(ψ g))`, and `⅟|G|` is real. -/
theorem inner_conj_conj [Fintype G] [Invertible (Nat.card G : ℂ)] (φ ψ : ClassFunction G ℂ) :
    ClassFunction.inner φ.conj ψ.conj = star (ClassFunction.inner φ ψ) := by
  have hsum : ClassFunction.innerSum φ.conj ψ.conj = star (ClassFunction.innerSum φ ψ) := by
    rw [ClassFunction.innerSum, ClassFunction.innerSum, star_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ClassFunction.conj_apply, ClassFunction.conj_apply, star_mul, star_star, mul_comm]
  have hcard : (Nat.card G : ℂ) ≠ 0 := (isUnit_of_invertible (Nat.card G : ℂ)).ne_zero
  refine mul_left_cancel₀ hcard ?_
  rw [ClassFunction.card_mul_inner, hsum, ← ClassFunction.card_mul_inner, star_mul, star_natCast,
    mul_comm]

/-- For a **real** `Δ ∈ ZIrr G`, the Fourier coefficient is `conjPerm`-symmetric:
`⟨Δ, χ̄⟩ = ⟨Δ, χ⟩`.  Since `Δ̄ = Δ` (`IsReal`), `⟨Δ, χ̄⟩ = ⟨Δ̄, χ̄⟩ = conj⟨Δ,χ⟩` (`inner_conj_conj`),
and `⟨Δ,χ⟩` is a real integer (`mem_ZIrr_inner_int`), so the `conj` is inert. -/
theorem inner_conjPerm_eq_of_isReal [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {Δ : ClassFunction G ℂ} (hΔ : Δ ∈ ZIrr G) (hr : ClassFunction.IsReal Δ)
    (χ : IrreducibleCharacter G) :
    ClassFunction.inner Δ
        ((IrreducibleCharacter.conjPerm G χ : IrreducibleCharacter G) : ClassFunction G ℂ)
      = ClassFunction.inner Δ (χ : ClassFunction G ℂ) := by
  rw [IrreducibleCharacter.conjPerm_apply_coe]
  have key : ClassFunction.inner Δ ((χ : ClassFunction G ℂ).conj)
      = ClassFunction.inner Δ.conj ((χ : ClassFunction G ℂ).conj) := by rw [hr]
  rw [key, inner_conj_conj]
  obtain ⟨m, hm⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int χ hΔ
  rw [hm, star_intCast]

open scoped Classical in
/-- **Parity of the inner product of two real virtual characters orthogonal to `1`** (Peterfalvi
(11.8.5) "`a` even from `β` real").  For `Δ₁, Δ₂ ∈ ZIrr G` (odd `G`) that are real (`IsReal`) — hence
with `conjPerm`-symmetric Fourier coefficients `⟨Δᵢ, χ̄⟩ = ⟨Δᵢ, χ⟩` — with `⟨Δ₂, 1⟩ = 0` (only one
factor need be orthogonal to `1`, since the `χ = 1` term `c₁(1)·c₂(1)` vanishes), the integer
`⟨Δ₁, Δ₂⟩` is even.  Cross-Parseval (`mem_ZIrr_inner_eq_sum_over_irr`) gives
`⟨Δ₁,Δ₂⟩ = ∑_χ c₁(χ)c₂(χ)` with `cᵢ(χ) = ⟨Δᵢ,χ⟩ ∈ ℤ`; the `χ = 1` term vanishes, and on `Irr ∖ {1}`
the conjugation involution `conjPerm` is fixed-point-free (`conjPerm_eq_self_iff` +
`not_isReal_of_ne_trivial_of_odd_card'`) with `cᵢ` invariant, so `even_sum_of_involution` applies. -/
theorem even_inner_of_conjPerm_symmetric [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (hodd : Odd (Nat.card G))
    {Δ₁ Δ₂ : ClassFunction G ℂ} (h₁ : Δ₁ ∈ ZIrr G) (h₂ : Δ₂ ∈ ZIrr G)
    (hr₁ : ClassFunction.IsReal Δ₁) (hr₂ : ClassFunction.IsReal Δ₂)
    (htriv₂ : ClassFunction.inner Δ₂ (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0) :
    ∃ z : ℤ, ClassFunction.inner Δ₁ Δ₂ = (z : ℂ) ∧ Even z := by
  have hsym₁ := fun χ => inner_conjPerm_eq_of_isReal h₁ hr₁ χ
  have hsym₂ := fun χ => inner_conjPerm_eq_of_isReal h₂ hr₂ χ
  choose c₁ hc₁ using fun χ : IrreducibleCharacter G =>
    OddOrder.RepresentationTheory.mem_ZIrr_inner_int χ h₁
  choose c₂ hc₂ using fun χ : IrreducibleCharacter G =>
    OddOrder.RepresentationTheory.mem_ZIrr_inner_int χ h₂
  have hz : ClassFunction.inner Δ₁ Δ₂
      = ((∑ χ : IrreducibleCharacter G, c₁ χ * c₂ χ : ℤ) : ℂ) := by
    rw [mem_ZIrr_inner_eq_sum_over_irr h₂]
    push_cast
    exact Finset.sum_congr rfl fun χ _ => by rw [hc₁ χ, hc₂ χ]
  refine ⟨_, hz, ?_⟩
  have hc2t : c₂ (trivialIrreducibleCharacter G) = 0 := by
    have hh := hc₂ (trivialIrreducibleCharacter G); rw [htriv₂] at hh; exact_mod_cast hh.symm
  have hsymc₁ : ∀ χ, c₁ (IrreducibleCharacter.conjPerm G χ) = c₁ χ := fun χ => by
    have hh := ((hc₁ (IrreducibleCharacter.conjPerm G χ)).symm.trans (hsym₁ χ)).trans (hc₁ χ)
    exact_mod_cast hh
  have hsymc₂ : ∀ χ, c₂ (IrreducibleCharacter.conjPerm G χ) = c₂ χ := fun χ => by
    have hh := ((hc₂ (IrreducibleCharacter.conjPerm G χ)).symm.trans (hsym₂ χ)).trans (hc₂ χ)
    exact_mod_cast hh
  have htrivfix : IrreducibleCharacter.conjPerm G (trivialIrreducibleCharacter G)
      = trivialIrreducibleCharacter G :=
    (IrreducibleCharacter.conjPerm_eq_self_iff (trivialIrreducibleCharacter G)).mpr (by simp)
  rw [← Finset.add_sum_erase Finset.univ (fun χ => c₁ χ * c₂ χ)
      (Finset.mem_univ (trivialIrreducibleCharacter G)),
    hc2t, mul_zero, zero_add]
  refine even_sum_of_involution (fun χ _ => IrreducibleCharacter.conjPerm G χ)
    (fun χ hχ => ?_) (fun χ hχ => ?_) (fun χ _ => (IrreducibleCharacter.conjPerm G).left_inv χ)
    (fun χ _ => by rw [hsymc₁, hsymc₂])
  · rw [Finset.mem_erase] at hχ ⊢
    refine ⟨fun h => hχ.1 ?_, Finset.mem_univ _⟩
    exact (IrreducibleCharacter.conjPerm G).injective (h.trans htrivfix.symm)
  · rw [Finset.mem_erase] at hχ
    intro h
    exact OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card' hodd hχ.1
      ((IrreducibleCharacter.conjPerm_eq_self_iff χ).mp h)

open scoped Classical FiniteInduce in
/-- **The `σ`-column sum `∑_r ω_{r0}^σ` is real** (Peterfalvi (3.9)(a)).  The column-`0` `σ`-images
are permuted by the row-conjugation involution `σ` (`exists_rowInv_alignedOmegaSigma_conj`:
`conj ω_{r0}^σ = ω_{σr,0}^σ`), so the sum is conjugation-invariant.  This is the `M`-side reality
feeding the (11.8.5) `a = ⟨∑ω_{r0}^σ, β⟩` parity (`even_inner_of_conjPerm_symmetric`). -/
theorem Hypothesis.sum_alignedOmegaSigma_zeroColumn_isReal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    ClassFunction.IsReal (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) := by
  haveI := hyp.finiteG
  classical
  choose σ hσ using fun i => hyp.exists_rowInv_alignedOmegaSigma_conj hG hodd i
  have hbridge : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hgridinj : ∀ a b : Fin hyp.w1,
      hyp.alignedOmegaSigmaGrid hG hodd a 0 = hyp.alignedOmegaSigmaGrid hG hodd b 0 → a = b := by
    intro a b hab
    by_contra hne
    have hii := hyp.alignedOmegaSigmaGrid_inner hG hodd a b 0 0
    rw [← hab, hyp.alignedOmegaSigmaGrid_inner hG hodd a a 0 0, if_pos ⟨rfl, rfl⟩,
      if_neg (fun h => hne h.1)] at hii
    exact one_ne_zero hii
  have hσinv : Function.Involutive σ := fun r => by
    apply hgridinj
    calc hyp.alignedOmegaSigmaGrid hG hodd (σ (σ r)) 0
        = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
            (hyp.alignedOmegaSigmaGrid hG hodd (σ r) 0) := ((hσ (σ r)).1).symm
      _ = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
            (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
              (hyp.alignedOmegaSigmaGrid hG hodd r 0)) := by rw [(hσ r).1]
      _ = hyp.alignedOmegaSigmaGrid hG hodd r 0 := by
            rw [← hbridge, ← hbridge, ClassFunction.conj_conj]
  have hconjsum : ∀ s : Finset (Fin hyp.w1),
      (∑ r ∈ s, hyp.alignedOmegaSigmaGrid hG hodd r 0).conj
        = ∑ r ∈ s, (hyp.alignedOmegaSigmaGrid hG hodd r 0).conj := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, ClassFunction.conj_add, ih, Finset.sum_insert ha]
  rw [ClassFunction.IsReal, hconjsum Finset.univ,
    show (∑ r : Fin hyp.w1, (hyp.alignedOmegaSigmaGrid hG hodd r 0).conj)
        = ∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd (σ r) 0 from
      Finset.sum_congr rfl fun r _ => by rw [hbridge]; exact (hσ r).1]
  exact Equiv.sum_comp (Equiv.ofBijective σ hσinv.bijective)
    (fun r => hyp.alignedOmegaSigmaGrid hG hodd r 0)

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5), the "`a` even" step** (assembled).  If `a = ⟨∑_r ω_{r0}^σ, β⟩` with `β` a
real virtual character orthogonal to `1_G` (Peterfalvi (11.8.3): `β` is `i,j`-independent and real),
then `a` is even.  Both factors are real (`∑ω_{r0}^σ` via `sum_alignedOmegaSigma_zeroColumn_isReal`,
`β` by hypothesis) and lie in `ℤ[Irr G]`, and `β ⊥ 1`, so `even_inner_of_conjPerm_symmetric` gives
the parity.  This excludes `a = 1` (odd), so with `a ∈ {0,1,2}` (11.8.2) it forces `a ∈ {0,2}`, the
input to `charParam_a_eq_zero_of_residualEq`. -/
theorem Hypothesis.a_even_of_eq_inner_sumOmegaSigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {β : ClassFunction G ℂ} (hβZ : β ∈ ZIrr G)
    (hβr : ClassFunction.IsReal β)
    (hβ1 : ClassFunction.inner β (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0)
    {a : ℤ} (ha : (a : ℂ)
      = ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) β) :
    Even a := by
  haveI := hyp.finiteG
  have hωZ : (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) ∈ ZIrr G :=
    Submodule.sum_mem _ fun r _ => hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hodd r 0
  have hωr := hyp.sum_alignedOmegaSigma_zeroColumn_isReal hG hodd
  obtain ⟨z, hz, hev⟩ := even_inner_of_conjPerm_symmetric hodd hωZ hβZ hωr hβr hβ1
  have haz : a = z := by
    have hcast : (a : ℂ) = (z : ℂ) := ha.trans hz
    exact_mod_cast hcast
  rw [haz]; exact hev

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5), `β ⊥ 1_G`** (`i ≠ 0`): `⟨α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ) + nζ^{τ₁},
1_G⟩ = 0`.  Via the Dade adjoint `tau_inner_trivial` (`⟨α_{ij}^τ, 1_G⟩ = ⟨α_{ij}, 1_M⟩ = 0`, `hα1M`);
`1_G = ω_{00}^σ` (`alignedOmegaSigmaGrid_zero_zero`), so `⟨ω_{ij}^σ − ω_{i0}^σ, 1_G⟩ = 0`
(`alignedOmegaSigmaGrid_inner`, using `i ≠ 0`); and `⟨ζ^{τ₁}, 1_G⟩ = 0`
(Peterfalvi (5.3.b), `SHC_extension_inner_alignedOmegaSigma_eq_zero`).  This is the `β ⊥ 1` input to
the `a`-even parity `a_even_of_eq_inner_sumOmegaSigma`. -/
theorem Hypothesis.beta_inner_trivial [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (hi0 : i ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hα1M : ClassFunction.inner
      (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      (trivialClassFunction ↥M) = 0) :
    ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        + (n : ℂ) • coh.extension ζ)
      (trivialClassFunction G) = 0 := by
  have hsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hατ1 : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      (trivialClassFunction G) = 0 := by
    rw [hyp.tau_inner_trivial hsupp]; exact hα1M
  have hωdiff1 : ClassFunction.inner
      (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
      (trivialClassFunction G) = 0 := by
    rw [← hyp.alignedOmegaSigmaGrid_zero_zero hG hodd, ClassFunction.inner_sub_left,
      hyp.alignedOmegaSigmaGrid_inner hG hodd i 0 j 0,
      hyp.alignedOmegaSigmaGrid_inner hG hodd i 0 0 0,
      if_neg (fun h => hi0 h.1), if_neg (fun h => hi0 h.1), sub_zero]
  have hζτ1 : ClassFunction.inner (coh.extension ζ)
      (trivialClassFunction G) = 0 := by
    rw [← hyp.alignedOmegaSigmaGrid_zero_zero hG hodd]
    exact hyp.SHC_extension_inner_alignedOmegaSigma_eq_zero hG coh hodd hζS hζirr hζ1 hζne 0 0
  rw [ClassFunction.inner_add_left, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    ClassFunction.inner_smul_left, hατ1, hωdiff1, hζτ1, mul_zero, mul_zero, sub_zero, add_zero]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5), `β ∈ ℤ[Irr G]`**: the (11.8.3) residual `β = α_{ij}^τ − δ(ω_{ij}^σ −
ω_{i0}^σ) + nζ^{τ₁}` is a virtual character.  `α_{ij}^τ ∈ ZIrr` (`muGridAlpha_tau_mem_ZIrr`), the
aligned `σ`-grid entries `∈ ZIrr` (`alignedOmegaSigmaGrid_mem_ZIrr`), and `ζ^{τ₁} ∈ ZIrr`
(`SHC_isCoherent.extension_mem_ZIrr`); `ZIrr G` is closed under `ℤ`/`ℕ`-linear combinations. -/
theorem Hypothesis.beta_mem_ZIrr [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ) :
    (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        + (n : ℂ) • coh.extension ζ) ∈ ZIrr G := by
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  have hζτZ : coh.extension ζ ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
  have hωZ : (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
      ∈ ZIrr G :=
    Submodule.sub_mem _ (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hodd i j)
      (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hodd i 0)
  refine Submodule.add_mem _ (Submodule.sub_mem _ hαZ ?_) ?_
  · rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem hωZ δ
  · rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hζτZ n

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5), `⟨α_{ij}, 1_M⟩ = 0` for `i ≠ 0`**: the pre-Dade residual
`α_{ij} = μ_{ij} − δμ_{i0} − nζ` is orthogonal to the principal character of `M`.  The principal
character sits at the grid origin `μ_{00} = 1_M` (`muGrid_zero_zero_eq_trivial`), so for `i ≠ 0`,
`j ≠ 0` all three constituents avoid it: `⟨μ_{ij}, 1_M⟩ = ⟨μ_{ij}, μ_{00}⟩ = 0` (cross-column,
`j ≠ 0`), `⟨μ_{i0}, 1_M⟩ = ⟨μ_{i0}, μ_{00}⟩ = 0` (within-column, `i ≠ 0`), and `⟨ζ, 1_M⟩ = 0`
(`ζ(1) = w₁ > 1 ≠ 1`).  This discharges the `hα1M` hypothesis of `beta_inner_trivial`, making
`β ⊥ 1_G` unconditional for `i ≠ 0`. -/
theorem Hypothesis.muGridAlpha_inner_trivial_M [Finite G] {M : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)] (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {i : Fin hyp.w1} (hi0 : i ≠ 0) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    {δ : ℤ} {n : ℕ} :
    ClassFunction.inner
        (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (trivialClassFunction (↥M)) = 0 := by
  have hμij : ClassFunction.inner (hyp.muGrid hG hodd i j) (trivialClassFunction (↥M)) = 0 := by
    rw [← hyp.muGrid_zero_zero_eq_trivial hG hodd]
    exact hyp.muGrid_inner_cross_column hG hodd i 0 hj0
  have hμi0 : ClassFunction.inner (hyp.muGrid hG hodd i 0) (trivialClassFunction (↥M)) = 0 := by
    rw [← hyp.muGrid_zero_zero_eq_trivial hG hodd]
    exact hyp.muGrid_inner_within_column hG hodd 0 hi0
  have hζ : ClassFunction.inner ζ (trivialClassFunction (↥M)) = 0 := by
    have hzmem : ζ ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hζirr
    have htmem : trivialClassFunction (↥M) ∈ irreducibleCharacters (↥M) :=
      mem_irreducibleCharacters.mpr trivialClassFunction_isIrreducible
    rw [irr_cf_inner hzmem htmem, if_neg ?_]
    intro hcontra
    have h1 : ζ 1 = trivialClassFunction (↥M) 1 :=
      congrArg (fun f : ClassFunction (↥M) ℂ => (f : (↥M) → ℂ) 1) hcontra
    rw [hζ1, trivialClassFunction_apply] at h1
    have hw1 : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast h1
    omega
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_left, hμij, hμi0, hζ,
    mul_zero, mul_zero, sub_zero, sub_zero]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5), the parity anchor `a = (∑_r ω_{r0}^σ, β)`**: the residual coefficient `a`
(defined by `(α_{ij}^τ, ζ^{τ₁}) = a − n`, `hinner`) equals the `σ`-grid inner product of the (11.8.3)
residual `β = α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ) + nζ^{τ₁}`.  This is the identity feeding the parity
assembly `a_even_of_eq_inner_sumOmegaSigma` (β real virtual character ⊥ 1 ⇒ `a` even), the input
that excludes `a = 1` unconditionally.  Computation: `(α_{ij}^τ, ∑_r ω_{r0}^σ) = a − δ` (from
`muGridAlpha_tau_inner_zeroColumnSum_sub_zeta` `= n − δ`, the (11.8.4) rewrite `h114`, and `hinner`);
`(ω^σ diff, ∑ω) = −1` (`alignedOmegaSigma_diff_inner_zeroColumnSum`); `(ζ^{τ₁}, ∑ω) = 0`
(`SHC_extension_inner_zeroColumnOmegaSigma_sum`, (5.3.b)) — so `(β, ∑ω) = (a − δ) − δ·(−1) + 0 = a`,
and conjugate-symmetry gives `(∑ω, β) = a`.  The `δ` in `β`'s coefficient cancels the `δ` from the
`α^τ` term, so this holds for **all** `δ` (not only `δ = 1`). -/
theorem Hypothesis.muGridAlpha_a_eq_inner_sumOmegaSigma_beta [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) {a : ℤ}
    (hinner : ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (a : ℂ) - (n : ℂ))
    (h114 : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - coh.extension ζ) :
    (a : ℂ) = ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
          + (n : ℂ) • coh.extension ζ) := by
  have hαω : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = (a : ℂ) - (δ : ℂ) := by
    have h := hyp.muGridAlpha_tau_inner_zeroColumnSum_sub_zeta hG hodd i hj0 hζS hζirr hζ1 hdeg hμ0
      hnf hδj hdζ h0ζ
    rw [h114, ClassFunction.inner_sub_right, hinner] at h
    linear_combination h
  have hβω : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        + (n : ℂ) • coh.extension ζ)
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = (a : ℂ) := by
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left, hαω,
      hyp.alignedOmegaSigma_diff_inner_zeroColumnSum hG hodd i hj0,
      hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG coh hodd hζS hζirr hζ1 hζne,
      star_natCast, star_intCast]
    ring
  rw [OddOrder.RepresentationTheory.inner_conj_symm, hβω, star_intCast]

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5), `a = 0` under the (11.8.4) hypothesis** (the residual-orthogonal case).
Given the (11.8.4) by-contradiction consequence `(μ₀ − ζ)^τ = ∑_r ω_{r0}^σ − ζ^{τ₁}` (`μ₀ = ∑ μ_{i'0}`),
the two-way computation of `(α_{ij}^τ, (μ₀ − ζ)^τ)` forces `a = 0` when `a ∈ {0, 2}`:
* `M`-side (via the Dade isometry, `muGridAlpha_tau_inner_zeroColumnSum_sub_zeta`): `= n − δ`;
* `G`-side (via (11.8.4) + the residual decomposition `α_{ij}^τ = δ(ω^σ diff) − nζ^{τ₁} + a∑β`
  for `a ∈ {0, 2}`, `SHC_residual_eq_omegaSigma_diff`, with `(ω^σ diff, ∑ω_{r0}^σ) = −1`
  (`alignedOmegaSigma_diff_inner_zeroColumnSum`) and the (5.3.b) orthogonalities
  `(ζ^{τ₁}, ∑ω) = (∑β, ∑ω) = 0`): `= −δ − (a − n) = n − δ − a`.
Equating gives `a = 0`.  With the parity `a` even (Peterfalvi (11.8.3), `β` real, excluding `a = 1`)
this is the full (11.8.5): under the residual-orthogonality assumption every column coefficient
`a = 0`, the key input to (11.8.6)'s `μ_j^{τ₂} = ∑ ω_{ij}^σ` coherence contradiction. -/
theorem Hypothesis.charParam_a_eq_zero_of_residualEq [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ)
    (h114 : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - coh.extension ζ) :
    ∃ a : ℤ, (a = 0 ∨ a = 1 ∨ a = 2) ∧
      ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (a : ℂ) - (n : ℂ) ∧
      (Even a → a = 0) := by
  obtain ⟨a, Y, hbound, hinner, hYeq, hdecompA⟩ :=
    hyp.SHC_residual_eq_omegaSigma_diff hG coh hodd i hj0 hζS hζirr hζ1 hdeg hμ0 hnf hδj hdζ h0ζ hδpm
      hn2 hRn hZ horth hRmem hRrev
  refine ⟨a, hbound, hinner, ?_⟩
  intro heven
  -- `a` even and `a ∈ {0,1,2}` gives `a ∈ {0,2}` (Peterfalvi (11.8.3)/(11.8.5): the parity `a` even
  -- from `β` real excludes `a = 1`).
  have ha02 : a = 0 ∨ a = 2 := by
    rcases hbound with h | h | h
    · exact Or.inl h
    · obtain ⟨k, hk⟩ := heven; omega
    · exact Or.inr h
  have hζne := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have hYd := hYeq ha02
  have htrans := hyp.muGridAlpha_tau_inner_zeroColumnSum_sub_zeta hG hodd i hj0 hζS hζirr hζ1
    hdeg hμ0 hnf hδj hdζ h0ζ
  rw [h114] at htrans
  have hαω : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = -(δ : ℂ) := by
    rw [hdecompA, hYd]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left,
      hyp.alignedOmegaSigma_diff_inner_zeroColumnSum hG hodd i hj0,
      hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG coh hodd hζS hζirr hζ1 hζne,
      hyp.R_sum_inner_zeroColumnOmegaSigma_sum hG coh hodd hRrev,
      star_natCast, star_intCast]
    ring
  rw [ClassFunction.inner_sub_right, hαω, hinner] at htrans
  have ha0 : (a : ℂ) = 0 := by linear_combination -htrans
  exact_mod_cast ha0

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5), unconditional `a = 0`**.  Combines the conditional (11.8.5)
`charParam_a_eq_zero_of_residualEq` (which gives `a ∈ {0,1,2}` and the implication
`Even a → a = 0`) with the parity assembly: the (11.8.3) residual
`β = α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ) + nζ^{τ₁}` is a virtual character (`beta_mem_ZIrr`) orthogonal
to `1_G` (`beta_inner_trivial`, its `hα1M` discharged by `muGridAlpha_inner_trivial_M` for `i ≠ 0`),
**real** (`beta_isReal`, the (11.8.3) reality), and `a = (∑_r ω_{r0}^σ, β)`
(`muGridAlpha_a_eq_inner_sumOmegaSigma_beta`); so `a` is even
(`a_even_of_eq_inner_sumOmegaSigma`, the general reality-parity of an integer inner product of
real virtual characters one of which is `⊥ 1_G` in odd order), which excludes `a = 1`.  Hence
`a = 0` unconditionally, i.e. `(α_{ij}^τ, ζ^{τ₁}) = −n`.  This is the full (11.8.5).

The formerly-threaded row-`0` (4.8)/(4.10) Dade identities `h48`/`h410` are now **discharged**
from the §10 instantiation of Hypothesis (4.6) (`tau_muGrid_zeroRow_diff` /
`tau_muGrid_fourCorner` via `toHypothesis46`, issue 9004); the residual input is the
`w₂`-primality `hw2` they need for the (10.3) cross-column degree constancy. -/
theorem Hypothesis.residualCoeff_eq_zero [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hconj : ∀ {χ : ClassFunction ↥M ℂ}, χ ∈ inducedFamily M → IsIrreducibleCharacter χ →
      χ 1 = (hyp.w1 : ℂ) → (coh.extension χ).conj = coh.extension χ.conj)
    (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (hi0 : i ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ} (hw2 : (hyp.w2).Prime)
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n) (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ)
    (h114 : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - coh.extension ζ) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = -(n : ℂ) := by
  -- the (4.8)/(4.10) Dade identities, discharged from the §10 instantiation of (4.6)
  have hdeg0 : hyp.muGrid hG hodd 0 j 1 = (d : ℂ) :=
    (hyp.muGrid_apply_one_eq hG hodd hw2 0 i hj0 hj0).trans hdeg
  have h410 : hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd 0 j
        - (δ : ℂ) • hyp.muGrid hG hodd i 0 + (δ : ℂ) • hyp.muGrid hG hodd 0 0)
      = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd 0 j
        - hyp.alignedOmegaSigmaGrid hG hodd i 0 + hyp.alignedOmegaSigmaGrid hG hodd 0 0) := by
    have := hyp.tau_muGrid_fourCorner hG hodd i j
    rwa [hδj] at this
  have h48 : ∀ k : Fin hyp.w2, k ≠ 0 →
      hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
        = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd 0 j
            - hyp.alignedOmegaSigmaGrid hG hodd 0 k) := fun k hk => by
    have := hyp.tau_muGrid_zeroRow_diff hG hodd hw2 hj0 hk
    rwa [hδj] at this
  have hβr := hyp.beta_isReal hG coh hconj hodd i hj0 hζS hζirr hζ1 hdeg0
    (hyp.muGrid_zero_column_apply_one hG hodd 0) hnf hδj h410 h48
  obtain ⟨a, hbound, hinner, heven_imp⟩ := hyp.charParam_a_eq_zero_of_residualEq hG coh hodd i hj0 hζS
    hζirr hζ1 hdeg hμ0 hnf hδj hdζ h0ζ hδpm hn2 hRn hZ horth hRmem hRrev h114
  have hζne := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have ha := hyp.muGridAlpha_a_eq_inner_sumOmegaSigma_beta hG coh hodd i hj0 hζS hζirr hζ1 hζne hdeg hμ0
    hnf hδj hdζ h0ζ hinner h114
  have hβZ := hyp.beta_mem_ZIrr hG coh hodd i hj0 hζS hζirr hζ1 hdeg hμ0 hnf hδj
  have hβ1 : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        + (n : ℂ) • coh.extension ζ)
      (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0 :=
    hyp.beta_inner_trivial hG coh hodd i hj0 hi0 hζS hζirr hζ1 hζne hdeg hμ0 hnf hδj
      (hyp.muGridAlpha_inner_trivial_M hG hodd hi0 hj0 hζirr hζ1)
  have heven := hyp.a_even_of_eq_inner_sumOmegaSigma hG hodd hβZ hβr hβ1 ha
  have ha0 : a = 0 := heven_imp heven
  rw [ha0] at hinner
  rw [hinner]; ring

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.6) opening identity** `(μ_j − dζ)^τ = ∑_i ω_{ij}^σ − dζ^{τ₁}` (`0 < j`, `δ = 1`).
Given the `a = 0` Dade images `α_{ij}^τ = ω_{ij}^σ − ω_{i0}^σ − nζ^{τ₁}` for all `i` (`halpha`,
Peterfalvi (11.8.2)+(11.8.5), `SHC_tau_muGridAlpha_eq` at `δ = 1`) and the (11.8.4) value
`(μ₀ − ζ)^τ = ∑_i ω_{i0}^σ − ζ^{τ₁}` (`h114`), the `M`-level identity `μ_j − dζ = (μ₀ − ζ) + ∑_i α_{ij}`
(needs `d = w₁·n + 1`, i.e. `δ = 1`) maps through the linear Dade isometry `τ` (`map_add`, `map_sum`)
to `∑_i ω_{i0}^σ − ζ^{τ₁} + ∑_i (ω_{ij}^σ − ω_{i0}^σ − nζ^{τ₁}) = ∑_i ω_{ij}^σ − dζ^{τ₁}`.  This is the
key step of (11.8.6): with `μ_j^{τ₂} = ∑_i ω_{ij}^σ` (via (4.9)/(5.8)) it makes `S(C) = S₁ ∪ S₂`
coherent, contradicting (11.3). -/
theorem Hypothesis.tau_muColumnSum_sub_zeta_eq_of_alphaImage [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (j : Fin hyp.w2) {ζ : ClassFunction ↥M ℂ} {d n : ℕ} (hd : (d : ℂ) = (hyp.w1 : ℂ) * (n : ℂ) + 1)
    (halpha : ∀ i : Fin hyp.w1,
      hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        = hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0
          - (n : ℂ) • coh.extension ζ)
    (h114 : hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)
        = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
          - coh.extension ζ) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ)
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
        - (d : ℂ) • coh.extension ζ := by
  have hMlevel : ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ)
      = ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)
        + ∑ i : Fin hyp.w1, (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) := by
    have hαe : (∑ i : Fin hyp.w1, (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        = (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0)
          - ((hyp.w1 : ℂ) * (n : ℂ)) • ζ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul, mul_comm]
    rw [hαe, hd]; module
  rw [hMlevel, map_add, h114, map_sum, Finset.sum_congr rfl (fun i _ => halpha i)]
  have hsum : (∑ i : Fin hyp.w1, (hyp.alignedOmegaSigmaGrid hG hodd i j
        - hyp.alignedOmegaSigmaGrid hG hodd i 0
        - (n : ℂ) • coh.extension ζ))
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
        - (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - ((hyp.w1 : ℂ) * (n : ℂ)) • coh.extension ζ := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul, mul_comm]
  rw [hsum, hd]; module

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5)+(11.8.6 opening), the assembled column identity**
`(μ_j − dζ)^τ = ∑_i ω_{ij}^σ − dζ^{τ₁}` (`0 < j`, `δ = 1`).  Assembles the (11.8.5) `a = 0` residual
coefficient into the full column Dade image: for every row `i ≠ 0`, `residualCoeff_eq_zero` gives
`(α_{ij}^τ, ζ^{τ₁}) = −n`, whence `SHC_tau_muGridAlpha_eq` gives the image
`α_{ij}^τ = ω_{ij}^σ − ω_{i0}^σ − nζ^{τ₁}`; the `i = 0` image follows from any `i ≠ 0` one via the
four-corner (4.10) identity `tau_muGrid_fourCorner` (the `nζ` cancels in `α_{ij} − α_{0j}`, and
`μ_{0j} − μ_{00} − nζ = (α_{ij}) − (μ_{ij} − μ_{0j} − μ_{i0} + μ_{00})`).  With `δ = 1`
(`d = w₁·n + 1`) the (11.8.6) opening `tau_muColumnSum_sub_zeta_eq_of_alphaImage` then linearly
assembles the column sum.  The `S(HC)`-coherent extension `coh` and its orthonormal image data `R`
(`= coh.extension '' S(HC)`, `|R| = n`) are the (11.8.1)/(5.7) inputs; `h114` is the (11.8.4)
normalization; `δ = 1`, `n`, and the `R` cardinality `|S(HC)| = n` are the §9 (11.8.1) counts. -/
theorem Hypothesis.tau_muColumnSum_sub_dzeta_eq_of_residualData [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hconj : ∀ {χ : ClassFunction ↥M ℂ}, χ ∈ inducedFamily M → IsIrreducibleCharacter χ →
      χ 1 = (hyp.w1 : ℂ) → (coh.extension χ).conj = coh.extension χ.conj)
    (hodd : Odd (Nat.card G)) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d n : ℕ} (hw2 : (hyp.w2).Prime)
    (hd : (d : ℂ) = (hyp.w1 : ℂ) * (n : ℂ) + 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - 1)
    (hdegall : ∀ i : Fin hyp.w1, hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0all : ∀ i : Fin hyp.w1, hyp.muGrid hG hodd i 0 1 = 1)
    (hδj : hyp.muColumnSign hG hodd j = 1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n) (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ)
    (h114 : hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) - coh.extension ζ) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ)
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
        - (d : ℂ) • coh.extension ζ := by
  have hw1 : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
  have hdℕ : d = hyp.w1 * n + 1 := by exact_mod_cast hd
  have hw1le : hyp.w1 ≤ hyp.w1 * n := Nat.le_mul_of_pos_right _ (by omega)
  have hdgt : hyp.w1 < d := by omega
  have hζne : ζ.conj ≠ ζ := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have hdζall : ∀ i : Fin hyp.w1, hyp.muGrid hG hodd i j 1 ≠ ζ 1 := fun i => by
    rw [hdegall i, hζ1]; exact_mod_cast (by omega : d ≠ hyp.w1)
  have h0ζall : ∀ i : Fin hyp.w1, hyp.muGrid hG hodd i 0 1 ≠ ζ 1 := fun i => by
    rw [hμ0all i, hζ1]; exact_mod_cast (by omega : (1 : ℕ) ≠ hyp.w1)
  -- the row-`i` Dade image `α_{ij}^τ = ω_{ij}^σ − ω_{i0}^σ − nζ^{τ₁}` for `i ≠ 0`
  have halpha_ne : ∀ i : Fin hyp.w1, i ≠ 0 →
      hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        = hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0
          - (n : ℂ) • coh.extension ζ := by
    intro i hi0
    have hα0 := hyp.residualCoeff_eq_zero hG coh hconj hodd i hj0 hi0 hζS hζirr hζ1 hw2
      (hdegall i) (hμ0all i) hnf hδj (hdζall i) (h0ζall i) (Or.inl rfl) hn2 hRn hZ horth hRmem hRrev
      h114
    have himg := hyp.SHC_tau_muGridAlpha_eq hG coh hodd i hj0 hζS hζirr hζ1 hζne (hdegall i)
      (hμ0all i) hnf hδj (hdζall i) (h0ζall i) (Or.inl rfl) hα0
    simpa only [Int.cast_one, one_smul] using himg
  -- the row-`0` image via the four-corner identity from row `i₁ = 1 ≠ 0`
  have halpha : ∀ i : Fin hyp.w1,
      hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        = hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0
          - (n : ℂ) • coh.extension ζ := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      set i₁ : Fin hyp.w1 := ⟨1, by omega⟩ with hi1def
      have hi1 : i₁ ≠ 0 := by rw [hi1def]; simp [Fin.ext_iff]
      have h410 := hyp.tau_muGrid_fourCorner hG hodd i₁ j
      rw [hδj] at h410
      simp only [Int.cast_one, one_smul] at h410
      have key : hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ
          = (hyp.muGrid hG hodd i₁ j - hyp.muGrid hG hodd i₁ 0 - (n : ℂ) • ζ)
            - (hyp.muGrid hG hodd i₁ j - hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd i₁ 0
                + hyp.muGrid hG hodd 0 0) := by module
      rw [key, map_sub, halpha_ne i₁ hi1, h410]; module
    · exact halpha_ne i hi0
  exact hyp.tau_muColumnSum_sub_zeta_eq_of_alphaImage hG hodd coh j hd halpha h114

open scoped Classical FiniteInduce in
/-- **The orthonormal coherent image `R = coh.extension '' S(HC)`** (Peterfalvi (11.8.1)/(5.7)):
the image of the degree-`w₁` irreducible subfamily `S(HC)` under an `S(HC)`-coherent extension `coh`
is a Finset of mutually orthonormal virtual characters in `ℤ[Irr G]`.  The `extension` isometry
(`extension_inner_eq`) carries the orthonormal irreducibles of `S(HC)` (`irr_cf_inner`) to an
orthonormal set — also giving injectivity, so `|R| = |S(HC)|` — and lands them in `ℤ[Irr G]`
(`extension_mem_ZIrr`).  This materializes the `R` data (`hZ`/`horth`/`hRmem`/`hRrev`) the (11.8.5)
`residualCoeff_eq_zero`/`tau_muColumnSum_sub_dzeta_eq_of_residualData` consume; only the cardinality
value `|S(HC)| = n` remains the §9 (11.8.1) count (`caseB_degree_qu` + Frobenius `(u−1)/q`). -/
theorem Hypothesis.exists_coherentImage_SHC [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) :
    ∃ R : Finset (ClassFunction G ℂ),
      (∀ β ∈ R, β ∈ ZIrr G) ∧
      (∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0) ∧
      (∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
        φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R) ∧
      (∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ,
        φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) ∧
      R.card = (Finset.univ.filter (fun χ : IrreducibleCharacter ↥M =>
        (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
          ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ))).card := by
  haveI := hyp.finiteG
  classical
  set p : IrreducibleCharacter ↥M → Prop := fun χ =>
    (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
      ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ) with hp
  set s : Finset (IrreducibleCharacter ↥M) := Finset.univ.filter p with hs_def
  have hmem_s : ∀ χ, χ ∈ s ↔ p χ := fun χ => by
    rw [hs_def, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)
  -- each `χ ∈ s` is a member of `S(HC) = SHCSet`, hence lies in `zSpan SHCSet`
  have hspan : ∀ χ : IrreducibleCharacter ↥M, χ ∈ s →
      (χ : ClassFunction ↥M ℂ) ∈ OddOrder.Peterfalvi.S07.zSpan hyp.SHCSet := fun χ hχ =>
    Submodule.subset_span ⟨((hmem_s χ).mp hχ).1, χ.2, ((hmem_s χ).mp hχ).2⟩
  set f : IrreducibleCharacter ↥M → ClassFunction G ℂ :=
    fun χ => coh.extension (χ : ClassFunction ↥M ℂ) with hf
  -- the extension isometry carries the orthonormal `χ ∈ s` to an orthonormal image
  have hiso : ∀ χ χ' : IrreducibleCharacter ↥M, χ ∈ s → χ' ∈ s →
      ClassFunction.inner (f χ) (f χ') = if χ = χ' then (1 : ℂ) else 0 := by
    intro χ χ' hχ hχ'
    rw [hf, coh.extension_inner_eq _ _ (hspan χ hχ) (hspan χ' hχ'),
      irr_cf_inner (mem_irreducibleCharacters.mpr χ.2) (mem_irreducibleCharacters.mpr χ'.2)]
    simp only [Subtype.coe_inj]
  have hinjOn : ∀ χ ∈ s, ∀ χ' ∈ s, f χ = f χ' → χ = χ' := by
    intro χ hχ χ' hχ' hfeq
    by_contra hne
    have h1 : ClassFunction.inner (f χ) (f χ') = 0 := by rw [hiso χ χ' hχ hχ', if_neg hne]
    have h2 : ClassFunction.inner (f χ) (f χ') = 1 := by
      rw [hfeq, hiso χ' χ' hχ' hχ', if_pos rfl]
    rw [h1] at h2; exact one_ne_zero h2.symm
  refine ⟨s.image f, ?_, ?_, ?_, ?_, ?_⟩
  · -- hZ
    intro β hβ
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hβ
    exact coh.extension_mem_ZIrr _ (hspan χ hχ)
  · -- horth
    intro α hα β hβ
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hα
    obtain ⟨χ', hχ', rfl⟩ := Finset.mem_image.mp hβ
    rw [hiso χ χ' hχ hχ']
    by_cases hc : χ = χ'
    · rw [if_pos hc, if_pos (by rw [hc])]
    · rw [if_neg hc, if_neg (fun h => hc (hinjOn χ hχ χ' hχ' h))]
  · -- hRmem
    intro φ hφS hφirr hφ1
    exact Finset.mem_image.mpr ⟨⟨φ, hφirr⟩, (hmem_s _).mpr ⟨hφS, hφ1⟩, rfl⟩
  · -- hRrev
    intro β hβ
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hβ
    obtain ⟨hφS, hφ1⟩ := (hmem_s χ).mp hχ
    exact ⟨(χ : ClassFunction ↥M ℂ), hφS, χ.2, hφ1, rfl⟩
  · -- cardinality: injective on `s`
    exact Finset.card_image_of_injOn hinjOn

open scoped Classical FiniteInduce in
/-- **`S(HC) = S₁` is orthonormal** (Peterfalvi (11.8), the `S₁` side of the (11.8.6) union).
Every member of `S(HC)` is an irreducible character of `M` (`SHCSet` filters `inducedFamily` by
`IsIrreducibleCharacter`), so `⟨φ, ψ⟩ = [φ = ψ]` by `irr_cf_inner`.  This is the orthonormal-`X`
input the (6.8.1) union glue `exists_integralCharacterMap_glue_of_orthonormal` takes for `S₁` in the
(11.8.6) τ₂ union (`coherent_Sset_of_column_identities`). -/
theorem Hypothesis.SHCSet_orthonormal [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {φ ψ : ClassFunction ↥M ℂ} (hφ : φ ∈ hyp.SHCSet) (hψ : ψ ∈ hyp.SHCSet) :
    ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 :=
  irr_cf_inner (mem_irreducibleCharacters.mpr hφ.2.1) (mem_irreducibleCharacters.mpr hψ.2.1)

open scoped FiniteInduce in
/-- **Degree of an `inducedFamily` member factors through `w₁`**: `Ind_{M'}^M θ (1) = w₁ · θ(1)`,
since `[M : M'] = w₁` (`TypePData.card_W1_eq_derived_index`; `M' = derivedInG M`).  This is the
foundational (11.8.1) degree-factoring for the world-bridge: the degree of any member `y = Ind θ`
of `S = inducedFamily M` is `w₁` times a source degree `θ(1)`, so the two-degree-class structure
`{w₁, qu = d·w₁}` of `𝒮(C)` reduces to `θ(1) ∈ {1, d}`.  (The reducible members' `θ(1) = d` is the
§9 `reducible_mem_sOf_H0_apply_one_eq_qu` content; this lemma supplies the `[M:M']`-factoring half.) -/
theorem Hypothesis.induce_derived_apply_one_eq_w1_mul [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M)
    (θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M)) :
    (ClassFunction.induce ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)) (1 : ↥M)
      = (hyp.w1 : ℂ) * (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) (1 : ↥((derivedInG M).subgroupOf M)) := by
  haveI := hyp.finiteG
  have hidx : ((derivedInG M).subgroupOf M).index = hyp.w1 :=
    hyp.typeP.card_W1_eq_derived_index.symm
  rw [ClassFunction.induce_apply_one, hidx]

open scoped FiniteInduce in
/-- **(11.8.1) column degree**: for `k ≠ 0`, the μ-grid column sum `μ_k = ∑ᵢ μ_{ik}` has degree
`q·u` (= `w₁·|Ū| = qu`).  `muGrid_column_sum_mem_sOf_H0_and_reducible` (μ_k is a reducible
`𝒮(H₀)`-member) composed with `reducible_mem_sOf_H0_apply_one_eq_qu` (reducible `𝒮(H₀)`-members have
degree `q·u`, §9 (9.8.b)/(9.9.b)).  This is the concrete `ψ₀`-witness degree for the (11.8.6) `hgen`
bundled `S₂`-structure: a column `μ_k ∈ Sset \ SHCSet` (reducible → not in the irreducible `SHCSet`,
`muGrid_column_sum_mem_inducedFamily`) of degree `qu`. -/
theorem Hypothesis.muGrid_column_sum_apply_one_eq_qu [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hnt : TypePNontrivialCore M hyp.typeP)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetup htype hnt))
    (k : Fin hyp.w2) (hk : k ≠ 0) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k) (1 : ↥M)
      = (((hyp.toTypesIIIIIIVSetup htype hnt).q *
          (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u : ℕ) : ℂ) := by
  haveI := hyp.finiteG
  obtain ⟨hmem, hred⟩ :=
    hyp.muGrid_column_sum_mem_sOf_H0_and_reducible hG htype hnt chief k hk
  exact reducible_mem_sOf_H0_apply_one_eq_qu hG
    (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief)
    (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k) hmem hred

open scoped FiniteInduce in
/-- **Peterfalvi (9.5)/(4.5.b): a reducible `S = inducedFamily M`-member is a nonzero μ-column.**
For `y = Ind_{M'}^M θ ∈ inducedFamily M` (`θ ∈ Irr(M')`, `θ ≠ 1`) with `Ind_{M'}^M θ` *reducible*,
there is a column index `k ≠ 0` with `y = ∑ᵢ μ_{ik}`.

This is the (9.5)/(11.5) family identification, closed via the §6 residue theory rather than a
prime-TI port.  Since `M' = HU = h.K` (`toCertainTypeHypothesis`), `θ` is an irreducible of `K`, and
the (4.5.b) reducibility criterion `induce_not_isIrreducible_iff` forces `θ = chiRestrict χ₂` (a
column `χ_j`, via the inertia computation `I_L(χ) = K`).  Then `induce_restrict_certainType_eq`
identifies `Ind_K^M (chiRestrict χ₂) = ∑ᵢ μ_{ik}` (the μ-grid column), where `k` is the column of
`χ₂`; `θ ≠ 1` excludes the trivial column (`chiRestrict_one_eq_trivial`, `finCardEquivCharacterGroup`
sends `0` to `1`), giving `k ≠ 0`. -/
theorem Hypothesis.exists_muGrid_column_eq_of_inducedFamily_reducible [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G))
    {y : ClassFunction ↥M ℂ} (hyS : y ∈ inducedFamily M)
    (hred : ¬ IsIrreducibleCharacter y) :
    ∃ k : Fin hyp.w2, k ≠ 0 ∧ y = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- `y = Ind_{h.K} θ` (`h.K = M'` defeq), `θ ≠ 1`.
  obtain ⟨θ, hθne, hyeq⟩ := hyS
  rw [hyeq] at hred
  -- (4.5.b) reducibility criterion: `θ = chiRestrict χ₂` for some column `χ₂`.
  obtain ⟨χ₂, hχ₂⟩ := (h.induce_not_isIrreducible_iff θ).mp hred
  -- the column index of `χ₂`.
  set k : Fin hyp.w2 := finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂) with hkdef
  have hχ₂k : finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k) = χ₂ := by
    have hkk : finCongr hcardW2sub.symm k = (finCardEquivCharacterGroup _).symm χ₂ := by
      rw [hkdef]; ext; simp
    rw [hkk, Equiv.apply_symm_apply]
  refine ⟨k, ?_, ?_⟩
  · -- `k ≠ 0`: else `χ₂ = 1` and `θ = chiRestrict 1 = 1`, contradicting `θ ≠ 1`.
    intro hk0
    apply hθne
    have hχ₂1 : χ₂ = 1 := by
      rw [← hχ₂k, hk0]
      have h0 : finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 := by ext; simp
      rw [h0, finCardEquivCharacterGroup_zero]
    rw [← hχ₂, hχ₂1]
    -- `chiRestrict 1 = trivial ↥h.K`, defeq to `trivial ↥M'`.
    exact h.chiRestrict_one_eq_trivial
  · -- `y = ∑ᵢ μ_{ik}` via `Ind_K^M (chiRestrict χ₂) = ∑ᵢ μ_{ik}`.
    have h2 : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
        = ClassFunction.induce h.K (h.chiRestrict χ₂ : ClassFunction ↥h.K ℂ) := by
      rw [h.coe_chiRestrict, h.induce_restrict_certainType_eq,
        ← Equiv.sum_comp (finCongr hcardW1.symm)
          (fun i' => ((h.columnFamily χ₂).mu i' : ClassFunction ↥M ℂ))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show hyp.muGrid hG hodd i k
        = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu
            (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) from by unfold Hypothesis.muGrid; rfl,
        hχ₂k]
    -- `y = Ind_{M'} θ = Ind_{h.K} (chiRestrict χ₂) = ∑ᵢ μ_{ik}` (last `induce` step defeq via `M' = h.K`).
    rw [h2, hχ₂]
    exact hyeq

open scoped FiniteInduce in
/-- **Reducible members of `S = inducedFamily M` have degree `q·u = qu`** — the reducible-side of the
(11.8.1) uniform-degree structure of `𝒮₂ = Sset \ SHCSet`.  A reducible `inducedFamily`-member is a
nonzero μ-column (`exists_muGrid_column_eq_of_inducedFamily_reducible`, the (9.5)/(4.5.b) family
identification), which lies in `𝒮(H₀) = sOf ... chief.H0` (`muGrid_column_sum_mem_sOf_H0_and_reducible`);
then `reducible_mem_sOf_H0_apply_one_eq_qu` gives degree `q·u`. -/
theorem Hypothesis.inducedFamily_reducible_apply_one_eq_qu [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hnt : TypePNontrivialCore M hyp.typeP)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetup htype hnt))
    {y : ClassFunction ↥M ℂ} (hyS : y ∈ inducedFamily M) (hred : ¬ IsIrreducibleCharacter y) :
    y (1 : ↥M) = (((hyp.toTypesIIIIIIVSetup htype hnt).q *
        (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u : ℕ) : ℂ) := by
  haveI := hyp.finiteG
  have hmem : y ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetup htype hnt) chief.H0 := by
    -- (9.5)/(4.5.b) family identification: the reducible `inducedFamily`-member is a nonzero
    -- μ-column (`exists_muGrid_column_eq_of_inducedFamily_reducible`), which lies in `𝒮(H₀)`.
    obtain ⟨k, hk, hyk⟩ :=
      hyp.exists_muGrid_column_eq_of_inducedFamily_reducible hG hG.odd hyS hred
    rw [hyk]
    exact (hyp.muGrid_column_sum_mem_sOf_H0_and_reducible hG htype hnt chief k hk).1
  exact reducible_mem_sOf_H0_apply_one_eq_qu hG
    (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief) y hmem hred

open scoped FiniteInduce in
/-- ⚠️ **OVER-STRONG — this uniform-degree statement is FALSE for non-Galois type III/IV; do NOT
build new work on it or attempt to close its remaining `sorry`.**  See **issue 1019** and
`notes/peterfalvi/s13_11_8_orthogonality.md` update³⁷.

The claim "`∀ y ∈ Sset \ SHCSet, y(1) = qu`" (`Sset = inducedFamily M`) requires the whole non-`SHCSet`
part of `S = S_1` to have the single degree `qu`.  But in the **non-Galois** case Peterfalvi (9.8)
(Coq `typeP_nonGalois_characters`, PFsection9.v:845–855) produces irreducibles of degree `q·a` with
`a := |U : C_U(·)| > 1` and `q·a ≠ q·u` (the parameters `u = |Ū|` and `a` genuinely differ); these lie
in `inducedFamily M \ SHCSet` with degree `≠ qu`, so the irreducible-side below is **not provable**.
The correct mechanism (Coq PFsection11.v:104/206) treats `S_1` as merely `subcoherent` and extends
coherence from the smaller `S(H₀C)` via `bounded_seqIndD_coherence` (Pf (6.x)) — **no uniform degree**.
This lemma (and its consumer `hgen_of_S2_uniform_degree`, hence the `hgen` bullet of
`coherent_Sset_of_column_identities`) is the deprecated uniform-degree route; it is to be replaced by
the bounded-coherence redesign (issue 1019).

**The reducible half is genuinely true** and stays sorry-free
(`inducedFamily_reducible_apply_one_eq_qu`: reducible members ARE the degree-`qu` μ-columns); only the
irreducible half is the false over-statement. -/
theorem Hypothesis.Sset_diff_SHCSet_apply_one_eq_qu [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hnt : TypePNontrivialCore M hyp.typeP)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetup htype hnt))
    {y : ClassFunction ↥M ℂ} (hy : y ∈ hyp.Sset \ hyp.SHCSet) :
    y (1 : ↥M) = (((hyp.toTypesIIIIIIVSetup htype hnt).q *
        (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u : ℕ) : ℂ) := by
  haveI := hyp.finiteG
  by_cases hirr : IsIrreducibleCharacter y
  · -- ⚠️ FALSE branch (issue 1019): an irreducible `y ∈ Sset \ SHCSet` of degree `≠ w₁` need NOT have
    -- degree `qu` — in the non-Galois case (9.8)(d) it can have degree `q·a` (`a > 1`, `q·a ≠ q·u`).
    -- This `sorry` is unclosable; the (11.8.6) coherence must instead use `bounded_seqIndD_coherence`.
    sorry
  · exact hyp.inducedFamily_reducible_apply_one_eq_qu hG htype hnt chief hy.1 hirr

open scoped FiniteInduce in
/-- **Degree of an `S₁ = S(HC)`-span element is an integer multiple of `w₁`.**  Every member of
`SHCSet` has degree `w₁` (by definition, third conjunct), so `ψ ∈ ℤ[S(HC)]` has `ψ(1) = s·w₁` with
`s ∈ ℤ` the coefficient sum (`span_induction`).  This is the `S₁`-side degree-ratio input of the
(11.8.6) generation `hgen` — the analogue of S08 `certainTypeSet_span_apply_one_eq_intMul`. -/
theorem Hypothesis.SHCSet_span_apply_one_eq_intMul [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {ψ : ClassFunction ↥M ℂ} (hψ : ψ ∈ Submodule.span ℤ hyp.SHCSet) :
    ∃ s : ℤ, ψ 1 = (s : ℂ) * (hyp.w1 : ℂ) := by
  classical
  induction hψ using Submodule.span_induction with
  | mem x hx => exact ⟨1, by rw [hx.2.2]; push_cast; ring⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨sx, hsx⟩ := hx; obtain ⟨sy, hsy⟩ := hy
      exact ⟨sx + sy, by rw [ClassFunction.add_apply, hsx, hsy]; push_cast; ring⟩
  | smul c x _ hx =>
      obtain ⟨sx, hsx⟩ := hx
      exact ⟨c * sx, by
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hsx]; push_cast; ring⟩

open scoped FiniteInduce in
/-- **Degree of an `S₂ = S(C) − S(HC)`-span element is an integer multiple of `qu`**, given that all
`S₂` members share degree `qu` (the (11.8.1) uniform reducible degree — supplied as a hypothesis,
§9-gated).  `span_induction`, as `SHCSet_span_apply_one_eq_intMul`.  The `S₂`-side degree-ratio input
of the (11.8.6) generation `hgen`. -/
theorem Hypothesis.Sset_diff_span_apply_one_eq_intMul [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M) {qu : ℕ}
    (hS2deg : ∀ y ∈ hyp.Sset \ hyp.SHCSet, (y : ↥M → ℂ) 1 = (qu : ℂ))
    {ψ : ClassFunction ↥M ℂ} (hψ : ψ ∈ Submodule.span ℤ (hyp.Sset \ hyp.SHCSet)) :
    ∃ s : ℤ, ψ 1 = (s : ℂ) * (qu : ℂ) := by
  classical
  induction hψ using Submodule.span_induction with
  | mem x hx => exact ⟨1, by rw [hS2deg x hx]; push_cast; ring⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨sx, hsx⟩ := hx; obtain ⟨sy, hsy⟩ := hy
      exact ⟨sx + sy, by rw [ClassFunction.add_apply, hsx, hsy]; push_cast; ring⟩
  | smul c x _ hx =>
      obtain ⟨sx, hsx⟩ := hx
      exact ⟨c * sx, by
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hsx]; push_cast; ring⟩

open scoped FiniteInduce in
/-- **`S(HC) ⊥ (S − S(HC))`** (the source-orthogonality `hsrc_ortho` input for the (11.8.6) union):
`S(HC)` and `S₂ = S(C) − S(HC)` are disjoint subsets of `S = inducedFamily M`, so a member of each
is a distinct pair of `inducedFamily` characters, orthogonal by `inducedFamily_pairwiseOrthogonal`.
This is the set-level `X ⊥ Y` the (6.8.1) union glue `exists_integralCharacterMap_glue_of_orthonormal`
takes (with `X = S(HC)`, `Y = S₂`). -/
theorem Hypothesis.SHCSet_inner_diff_eq_zero [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {x y : ClassFunction ↥M ℂ} (hx : x ∈ hyp.SHCSet) (hy : y ∈ hyp.Sset \ hyp.SHCSet) :
    ClassFunction.inner x y = 0 := by
  haveI := hyp.finiteG
  have hne : x ≠ y := fun h => hy.2 (h ▸ hx)
  exact inducedFamily_pairwiseOrthogonal hx.1 hy.1 hne

open scoped FiniteInduce in
/-- **`ℤ[S(HC)] ⊥ ℤ[S₂]`** (span-level `hsrc_ortho` for the (11.8.6) union): the `ℤ`-lattices spanned
by `S(HC)` and `S₂ = S(C) − S(HC)` are orthogonal, lifted from the set-level
`SHCSet_inner_diff_eq_zero` by bi-additivity of the inner product (`span_induction` on both
arguments).  This is the exact `hsrc_ortho` hypothesis
`coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` takes for the τ₂ union. -/
theorem Hypothesis.span_inner_SHCSet_diff_eq_zero [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {u v : ClassFunction ↥M ℂ}
    (hu : u ∈ Submodule.span ℤ hyp.SHCSet) (hv : v ∈ Submodule.span ℤ (hyp.Sset \ hyp.SHCSet)) :
    ClassFunction.inner u v = 0 := by
  haveI := hyp.finiteG
  have hright : ∀ x ∈ hyp.SHCSet, ∀ w ∈ Submodule.span ℤ (hyp.Sset \ hyp.SHCSet),
      ClassFunction.inner x w = 0 := by
    intro x hx w hw
    induction hw using Submodule.span_induction with
    | mem y hy => exact hyp.SHCSet_inner_diff_eq_zero hx hy
    | zero => rw [ClassFunction.inner_zero_right]
    | add y z _ _ ihy ihz => rw [ClassFunction.inner_add_right, ihy, ihz, add_zero]
    | smul a y _ ih =>
        rw [← Int.cast_smul_eq_zsmul ℂ a y,
          OddOrder.RepresentationTheory.inner_smul_right, ih, mul_zero]
  induction hu using Submodule.span_induction with
  | mem x hx => exact hright x hx v hv
  | zero => rw [ClassFunction.inner_zero_left]
  | add x z _ _ ihx ihz => rw [ClassFunction.inner_add_left, ihx, ihz, add_zero]
  | smul a x _ ih =>
      rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, ih, mul_zero]

open scoped FiniteInduce in
/-- **`S(HC) ⊆ S`** (the `X ⊆ X ∪ Y` inclusion for the (11.8.6) union): every member of
`S(HC) = {φ ∈ S | φ irreducible, φ(1) = w₁}` is in `S = inducedFamily M` by the first conjunct of
its defining comprehension.  Trivial, but named so the (11.8.6) set-decomposition
`Sset_eq_SHCSet_union_diff` and future gluing consumers can cite it. -/
theorem Hypothesis.SHCSet_subset_Sset [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.SHCSet ⊆ hyp.Sset :=
  fun _ hφ => hφ.1

open scoped FiniteInduce in
/-- **`S(C) = S(HC) ∪ (S(C) − S(HC))`** (the set-level decomposition `S = S₁ ∪ S₂` of the (11.8.6)
union): `S(HC) ⊆ S` (`SHCSet_subset_Sset`), so `S = S(HC) ∪ (S ∖ S(HC))` by `Set.union_diff_cancel`.
This is the exact `rw` that turns the (11.8.6) goal `IsCoherent τ S A₀` into the union form
`IsCoherent τ (S(HC) ∪ S₂) A₀` the S07 gluing engine
(`coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`) concludes — with `X = S(HC)`
(coherent by `coh`), `Y = S₂ = S ∖ S(HC)` (coherent by (9.11)/(11.7)). -/
theorem Hypothesis.Sset_eq_SHCSet_union_diff [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.Sset = hyp.SHCSet ∪ (hyp.Sset \ hyp.SHCSet) :=
  (Set.union_diff_cancel hyp.SHCSet_subset_Sset).symm

open scoped FiniteInduce in
/-- ⚠️ **Over-broad family, part of the uniform-degree route (issue 1019).**  Here `S₂` is taken as
`hyp.Sset \ hyp.SHCSet = inducedFamily M \ S(HC) = S_1 \ S(HC)`, but Peterfalvi's `S₂` is the narrower
`S(C) \ S(HC)` (with the `C`-kernel condition).  The coherence of the full `S_1 \ S(HC)` is not a
standalone fact — in Coq `S_1` is merely `subcoherent`, and its coherence is *derived* from `S(H₀C)`
coherence via `bounded_seqIndD_coherence`.  This obligation should be re-scoped in the redesign
(narrow to `S(C)` / `S(H₀C)`, then extend via bounded coherence).

**Peterfalvi (11.8.6) prerequisite: `S₂ = S(C) − S(HC)` is coherent** (the `hY` gluing input;
§9/§14-gated, named obligation).

This is Peterfalvi's "By (9.11), `𝒮(H₀C') − 𝒮(HC')` is coherent, whence `𝒮₂` is coherent by (11.7)"
(mmd 04.13 L67).  It is the `S₂`-side coherence `hY` that `coherent_Sset_of_glued` and the (11.8.6)
capstone `coherent_Sset_of_column_identities` consume — with `S₂ = hyp.Sset \ hyp.SHCSet` (the
`S(C) − S(HC)` difference of the pinned §10 induced family).

Reduction status (see `notes/peterfalvi/s13_11_8_orthogonality.md` update²⁶): the underlying content
is (9.11) `S11.coherent_H0C_commutator`, itself gated on `S11.sibleyTarget_H0C` (§14 Sibley setup +
lane-b (6.8)).  Three carrier obstructions block a direct sorry-free cite of (9.11) here:
(1) the `S11.Section11CharacterData` bridge `mkSection11CharacterData` sets `H0CprimeSupport := ∅`,
but `IsCoherent … ∅` is unconstructible (`zSupportedSpan S ∅ = {0}` kills `nonzero`);
(2) (9.11) is stated for the *difference* `𝒮(H₀C') − 𝒮(HC')`, whereas the repo's
`coherent_H0C_commutator` concludes on the *full* `chars.S = sSet data`;
(3) the world-bridge `sSet`/`sOf` (§9) ↔ `inducedFamily` (§10) `𝒮₂ = hyp.Sset ∖ hyp.SHCSet` is
unformalized.  Honest close = re-port (9.11) as `SOf`-difference coherence + (11.7) collapse, deep
char work coordinated with §14/lane-b.  Left as a single §14-gated `sorry` of the correct
difference-coherence signature (NOT a false-hypothesis hoist). -/
theorem Hypothesis.coherent_Sset_diff_SHCSet [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Sset \ hyp.SHCSet) hyp.A0) := by
  sorry

open scoped Classical FiniteInduce in
/-- **(11.8.6) gluing wrapper: `S(C) = S(HC) ∪ S₂` coherence from the glued `τ₃` data** (sorry-free).
The pure-algebra half of Peterfalvi (11.8.6): given the two coherences `coh` (`S(HC) = S₁`, `τ₁`) and
`hY` (`S₂ = S(C) − S(HC)`, `τ₂`), a glued integral map `ν` agreeing with `coh.extension` on `S₁` and
with `hY.extension` on `S₂` (`hagreeX`/`hagreeY` — Peterfalvi's `τ₃`), the mixed isometry `hmixed`,
and the supported cross-diagonal set `D` on which `ν = τ` (`hDτ`, the `hcol` column identities feed
this) with the enlarged generation hypothesis `hgen`, the full family `S = S(C)` is coherent.

This packages the S07 gluing engine `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`
for the (11.8.6) union: the source-orthogonality `hsrc_ortho` is discharged internally from the
landed `span_inner_SHCSet_diff_eq_zero` (`S₁ ⊥ S₂` at span level), and the conclusion is rewritten
from the union form to `hyp.Sset` via `Sset_eq_SHCSet_union_diff`.  What remains for the caller is
exactly the genuine (11.8.6) glue data: `hY` (the §9/§14-gated `S₂` coherence) and the `τ₃`
construction (`ν`, `hagreeX`, `hagreeY`, `hmixed`, `D`, `hDτ`, `hgen`) driven by `hcol`. -/
noncomputable def Hypothesis.coherent_Sset_of_glued [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Sset \ hyp.SHCSet) hyp.A0)
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G)
    (hagreeX : ∀ x ∈ hyp.SHCSet, ν x = coh.extension x)
    (hagreeY : ∀ y ∈ hyp.Sset \ hyp.SHCSet, ν y = hY.extension y)
    (hmixed : ∀ x ∈ hyp.SHCSet, ∀ y ∈ hyp.Sset \ hyp.SHCSet,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (D : Set (ClassFunction ↥M ℂ)) (hDτ : ∀ d ∈ D, ν d = hyp.tau d)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.SHCSet ∪ (hyp.Sset \ hyp.SHCSet)) hyp.A0 ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan hyp.SHCSet hyp.A0 ∪
        OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Sset \ hyp.SHCSet) hyp.A0 ∪ D)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0 := by
  haveI := hyp.finiteG
  rw [hyp.Sset_eq_SHCSet_union_diff]
  exact OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal
    coh hY ν hagreeX hagreeY
    (fun _ hu _ hv => hyp.span_inner_SHCSet_diff_eq_zero hu hv) hmixed D hDτ hgen

open scoped Classical FiniteInduce in
/-- **(11.8.6) `τ₃` glue map `ν` exists** — obligation-2 of the capstone, discharged (issue 9016).
From the two coherences `coh` (`S₁ = S(HC)`) and `hY` (`S₂ = S(C) − S(HC)`) there is an integral
map `ν` agreeing with `coh.extension` on `S₁` and with `hY.extension` on `S₂` (Peterfalvi's `τ₃`).

Both `S₁` and `S₂` are subsets of `S = inducedFamily M`, which is **pairwise orthogonal**
(`inducedFamily_pairwiseOrthogonal`) with members of **nonzero norm** (`inducedFamily_inner_self_ne_zero`)
and **finite** (`inducedFamily_finite`); and `S₁ ⊥ S₂` (`SHCSet_inner_diff_eq_zero`).  So the S07
non-orthonormal glue `exists_integralCharacterMap_glue_of_orthogonal` applies **directly** — the
reducible degree-`qu` members of `S₂` are handled by the norm-rescaling in
`coherentImageMapGlueOrthogonal`, so no orthonormality of `S₂` is needed.

This supplies the `ν` + `hagreeX`/`hagreeY` inputs of `coherent_Sset_of_glued`, reducing the
(11.8.6) residual to the genuine (6.8.1) character content — the mixed isometry `hmixed`
(image-side orthogonality, the `b ≡ 0` congruence) and the supported cross-diagonals `D`/`hDτ`/`hgen`
fed by the column identities `hcol`, together with `hY` itself (the §9/§14-gated `S₂` coherence). -/
theorem Hypothesis.exists_glue_nu [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Sset \ hyp.SHCSet) hyp.A0) :
    ∃ ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G,
      (∀ x ∈ hyp.SHCSet, ν x = coh.extension x) ∧
      (∀ y ∈ hyp.Sset \ hyp.SHCSet, ν y = hY.extension y) := by
  haveI := hyp.finiteG
  classical
  have hSfin : (inducedFamily M).Finite := inducedFamily_finite
  exact OddOrder.Peterfalvi.S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthogonal
    (hSfin.subset fun _ hx => hx.1) (hSfin.subset fun _ hy => hy.1)
    (fun _ hx _ hx' hne => inducedFamily_pairwiseOrthogonal hx.1 hx'.1 hne)
    (fun _ hx => inducedFamily_inner_self_ne_zero hx.1)
    (fun _ hy _ hy' hne => inducedFamily_pairwiseOrthogonal hy.1 hy'.1 hne)
    (fun _ hy => inducedFamily_inner_self_ne_zero hy.1)
    (fun _ hx _ hy => hyp.SHCSet_inner_diff_eq_zero hx hy)
    coh.extension hY.extension

open scoped FiniteInduce in
/-- **`ℤ[S₂]`-vanishing-at-`1` combinations are `A_0`-supported**, given `S₂ = S(C) − S(HC)` has
uniform degree `qu` (the (11.8.1) reducible degree — supplied as a §9-gated hypothesis) with a
witness member `ψ₀`.  The `S₂`-analogue of `SHC_zSpan_vanish_support`: `φ = ∑ eⱼ ψⱼ ∈ ℤ[S₂]` with
`φ(1) = 0` has `qu·∑eⱼ = 0`, so `∑eⱼ = 0`, collapsing `φ` to `A_0`-supported differences `ψ − ψ₀`
(`inducedFamily_sub_support`, equal degree `qu`).  `span_induction` on the strengthened invariant
`(ψ − (ψ(1)·qu⁻¹)·ψ₀).support ⊆ A_0`.  The `S₂`-side `A_0`-support input of the (11.8.6) `hgen`. -/
theorem Hypothesis.Sset_diff_zSpan_vanish_support [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M) {qu : ℕ} (hqune : (qu : ℂ) ≠ 0)
    (hS2deg : ∀ y ∈ hyp.Sset \ hyp.SHCSet, (y : ↥M → ℂ) 1 = (qu : ℂ))
    {ψ₀ : ClassFunction ↥M ℂ} (hψ₀ : ψ₀ ∈ hyp.Sset \ hyp.SHCSet)
    {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ Submodule.span ℤ (hyp.Sset \ hyp.SHCSet)) (hφ1 : φ 1 = 0) :
    φ.support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  classical
  have hψ₀S : ψ₀ ∈ inducedFamily M := hψ₀.1
  have hψ₀1 : (ψ₀ : ↥M → ℂ) 1 = (qu : ℂ) := hS2deg ψ₀ hψ₀
  suffices hstrong : ∀ ψ ∈ Submodule.span ℤ (hyp.Sset \ hyp.SHCSet),
      (ψ - (ψ 1 * (qu : ℂ)⁻¹) • ψ₀).support ⊆ hyp.A0 by
    have h := hstrong φ hφ
    rwa [hφ1, zero_mul, zero_smul, sub_zero] at h
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem x hx =>
      have hxS : x ∈ inducedFamily M := hx.1
      have hx1 : (x : ↥M → ℂ) 1 = (qu : ℂ) := hS2deg x hx
      rw [hx1, mul_inv_cancel₀ hqune, one_smul]
      exact hyp.inducedFamily_sub_support hxS hψ₀S (hx1.trans hψ₀1.symm)
  | zero => simp
  | add x y _ _ hx hy =>
      have hrw : (x + y - ((x + y) 1 * (qu : ℂ)⁻¹) • ψ₀)
          = (x - (x 1 * (qu : ℂ)⁻¹) • ψ₀) + (y - (y 1 * (qu : ℂ)⁻¹) • ψ₀) := by
        rw [ClassFunction.add_apply]; module
      rw [hrw]
      exact (ClassFunction.support_add_subset _ _).trans (Set.union_subset hx hy)
  | smul c x _ hx =>
      have hrw : (c • x - ((c • x) 1 * (qu : ℂ)⁻¹) • ψ₀)
          = (c : ℂ) • (x - (x 1 * (qu : ℂ)⁻¹) • ψ₀) := by
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply]; module
      rw [hrw]
      exact (ClassFunction.support_smul_subset _ _).trans hx

open scoped FiniteInduce in
/-- ⚠️ **Deprecated uniform-degree route (issue 1019).**  This lemma is true *as stated* (it is
conditional on `hS2deg`), but its hypothesis `hS2deg` = "`S₂ = Sset \ SHCSet` has uniform degree `qu`"
is **`Sset_diff_SHCSet_apply_one_eq_qu`, which is FALSE for non-Galois type III/IV** (degree-`qa`
irreducibles, `qa ≠ qu`).  So this generator can only be *applied* in the Galois case and is part of
the deprecated uniform-degree strategy; the (11.8.6) redesign replaces it with the Coq route
`bounded_seqIndD_coherence` (Pf (6.x)).  Kept for now because the reducible-side degree fact it
relies on is genuine; do not build new consumers on the `hS2deg` interface.

**(11.8.6) generation `hgen`** — the ungated degree-0 sublattice generation, given `S₂` has
uniform degree `qu = d·w₁` (the (11.8.1) reducible degree, §9-gated hypothesis `hS2deg`) with a
witness column `ψ₀`.  Peterfalvi (6.8.1) generation for the (11.8.6) union: the degree-0 sublattice
of `ℤ[S₁ ∪ S₂]` is generated by the supported sublattices `ℤ[S₁,A₀]`, `ℤ[S₂,A₀]` and the single
cross-diagonal `ψ₀ − dζ ∈ D`.  A supported `φ = φ_X + φ_Y` (`φ(1) = 0`) has `φ_X(1) = s_X·w₁`,
`φ_Y(1) = s_Y·qu`, and supportedness forces `s_X = −s_Y·d` (since `qu = d·w₁`, `w₁ ≠ 0`); then
`φ = (φ_X + (s_Y·d)ζ) + (φ_Y − s_Y·ψ₀) + s_Y·(ψ₀ − dζ)` with the first two supported (degree 0) and
in `ℤ[S₁]`/`ℤ[S₂]` (`SHC_zSpan_vanish_support` / `Sset_diff_zSpan_vanish_support`), the third in
`ℤ[D]`.  Only the `S₂` uniform-degree structure `hS2deg` is §9-gated; the generation itself is
pure lattice/degree algebra.  This discharges the `hgen` input of `coherent_Sset_of_glued`. -/
theorem Hypothesis.hgen_of_S2_uniform_degree [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {qu d : ℕ} (hqune : (qu : ℂ) ≠ 0) (hqu : (qu : ℂ) = (d : ℂ) * (hyp.w1 : ℂ))
    (hS2deg : ∀ y ∈ hyp.Sset \ hyp.SHCSet, (y : ↥M → ℂ) 1 = (qu : ℂ))
    {ζ : ClassFunction ↥M ℂ} (hζ : ζ ∈ hyp.SHCSet)
    {ψ₀ : ClassFunction ↥M ℂ} (hψ₀ : ψ₀ ∈ hyp.Sset \ hyp.SHCSet)
    (D : Set (ClassFunction ↥M ℂ)) (hD : (ψ₀ - (d : ℂ) • ζ) ∈ D) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.SHCSet ∪ (hyp.Sset \ hyp.SHCSet)) hyp.A0 ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan hyp.SHCSet hyp.A0 ∪
        OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Sset \ hyp.SHCSet) hyp.A0 ∪ D) := by
  haveI := hyp.finiteG
  classical
  have hw1ne : (hyp.w1 : ℂ) ≠ 0 := by
    have h1lt : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
    exact_mod_cast Nat.cast_ne_zero.mpr (by omega : hyp.w1 ≠ 0)
  have hζ1 : (ζ : ↥M → ℂ) 1 = (hyp.w1 : ℂ) := hζ.2.2
  intro φ hφ
  obtain ⟨hφspan, hφsupp⟩ := hφ
  have hφ1 : (φ : ↥M → ℂ) 1 = 0 := by
    by_contra h
    have hmem : ((1 : ↥M) : G) ∈ typePA0 M hyp.typeP :=
      hφsupp (ClassFunction.mem_support.mpr h)
    exact hyp.dadeData.dade.ne_one hmem (by simp)
  rw [OddOrder.Peterfalvi.S07.zSpan, Submodule.span_union] at hφspan
  obtain ⟨φX, hφX, φY, hφY, hsum⟩ := Submodule.mem_sup.mp hφspan
  obtain ⟨sX, hsX⟩ := hyp.SHCSet_span_apply_one_eq_intMul hφX
  obtain ⟨sY, hsY⟩ := hyp.Sset_diff_span_apply_one_eq_intMul hS2deg hφY
  have hdeg0 : (sX : ℂ) * hyp.w1 + (sY : ℂ) * qu = 0 := by
    have hc := congrArg (fun ψ : ClassFunction ↥M ℂ => (ψ : ↥M → ℂ) 1) hsum
    simp only [ClassFunction.add_apply] at hc
    rw [hsX, hsY, hφ1] at hc
    exact hc
  have hsX_eq : (sX : ℂ) = -((sY : ℂ) * (d : ℂ)) := by
    have hthis := hdeg0; rw [hqu] at hthis
    have h0 : ((sX : ℂ) + (sY : ℂ) * (d : ℂ)) * (hyp.w1 : ℂ) = 0 := by linear_combination hthis
    have h1 := (mul_eq_zero.mp h0).resolve_right hw1ne
    linear_combination h1
  have hAX1 : ((φX + (sY * (d : ℤ)) • ζ) : ClassFunction ↥M ℂ) 1 = 0 := by
    rw [ClassFunction.add_apply, hsX, ← Int.cast_smul_eq_zsmul ℂ (sY * d) ζ,
      ClassFunction.smul_apply, hζ1]
    push_cast
    linear_combination (hyp.w1 : ℂ) * hsX_eq
  have hAY1 : ((φY - (sY : ℤ) • ψ₀) : ClassFunction ↥M ℂ) 1 = 0 := by
    rw [ClassFunction.sub_apply, hsY, ← Int.cast_smul_eq_zsmul ℂ sY ψ₀,
      ClassFunction.smul_apply, hS2deg ψ₀ hψ₀]
    push_cast; ring
  have hAXspan : (φX + (sY * (d : ℤ)) • ζ) ∈ Submodule.span ℤ hyp.SHCSet :=
    Submodule.add_mem _ hφX (Submodule.smul_mem _ _ (Submodule.subset_span hζ))
  have hAYspan : (φY - (sY : ℤ) • ψ₀) ∈ Submodule.span ℤ (hyp.Sset \ hyp.SHCSet) :=
    Submodule.sub_mem _ hφY (Submodule.smul_mem _ _ (Submodule.subset_span hψ₀))
  have hAXsupp : (φX + (sY * (d : ℤ)) • ζ).support ⊆ hyp.A0 :=
    hyp.SHC_zSpan_vanish_support hG hAXspan hAX1
  have hAYsupp : (φY - (sY : ℤ) • ψ₀).support ⊆ hyp.A0 :=
    hyp.Sset_diff_zSpan_vanish_support hqune hS2deg hψ₀ hAYspan hAY1
  have hφeq : φ = (φX + (sY * (d : ℤ)) • ζ) + (φY - (sY : ℤ) • ψ₀)
      + (sY : ℤ) • (ψ₀ - (d : ℂ) • ζ) := by
    rw [← hsum, ← Int.cast_smul_eq_zsmul ℂ (sY * d) ζ, ← Int.cast_smul_eq_zsmul ℂ sY ψ₀,
      ← Int.cast_smul_eq_zsmul ℂ sY (ψ₀ - (d : ℂ) • ζ)]
    push_cast
    module
  rw [hφeq]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_left _ ⟨hAXspan, hAXsupp⟩))
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_right _ ⟨hAYspan, hAYsupp⟩))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_union_right _ hD))

open scoped FiniteInduce in
/-- ⚠️ **Its `hgen` bullet is on the deprecated uniform-degree route (issue 1019).**  That bullet
cites `Sset_diff_SHCSet_apply_one_eq_qu`, whose irreducible half is FALSE for non-Galois type III/IV,
so the capstone cannot be completed as designed.  The target (coherence of `inducedFamily M = S_1`,
contradicting (10.8)) is correct, but the route must be rebuilt via `bounded_seqIndD_coherence`
(Pf (6.x), Coq PFsection11.v:206): establish coherence of the smaller `S(H₀C)` and *extend* it to
`S_1` by the nilpotency/size bound — no uniform degree.  The `ν`-glue, `hmixed`/`hDτ` scaffolding and
the `hgen` algebra are reusable pieces of the redesign; the uniform-degree `hS2deg` input is not.

**Peterfalvi (11.8.6), the τ₂ union-coherence** (the deep capstone step, named obligation).
From the column identities `(μ_j − dζ)^τ = ∑_i ω_{ij}^σ − dζ^{τ₁}` (`0 < j`, all rows; `τ₁ = coh`),
the whole family `S = S(C) = inducedFamily M` is coherent.  Peterfalvi's argument: `S₂ = S(C) − S(HC)`
is coherent (`τ₂`) by (11.7)/(9.11) (`coherent_Sset_diff_SHCSet`); the column identities give
`μ_j^{τ₂} = ∑_i ω_{ij}^σ` (via (4.9)/(5.8)), so the `τ₁` (= `coh`) and `τ₂` extensions glue into a
coherent extension of the whole `S(C) = S₁ ∪ S₂`.

**Reduction (this session)**: the pure-algebra glue is factored out as the sorry-free wrapper
`coherent_Sset_of_glued` (decomposition `Sset_eq_SHCSet_union_diff` → S07
`coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`, with `S₁ ⊥ S₂` supplied by
`span_inner_SHCSet_diff_eq_zero`).  What that wrapper still needs from here is exactly two things:
* `hY` = `coherent_Sset_diff_SHCSet` — the §9/§14-gated `S₂`-coherence (see there for the carrier
  obstructions);
* the `τ₃` glue data — a glued integral map `ν` agreeing with `coh.extension` on `S₁` and with
  `hY.extension` on `S₂`, plus the supported cross-diagonals `D = {∑_i μ_{ij} − dζ}` on which
  `ν = τ` (`hDτ`, fed by `hcol`) and the enlarged generation `hgen`.

The `ν` construction is the genuine remaining (11.8.6) content: since `S₂` is **not** orthonormal
(its members are the reducible/degree-`qu` induced `μ_j`), the Fourier glue
`exists_integralCharacterMap_glue_of_orthonormal` does **not** apply, and no general "glue two
coherence extensions over a non-orthonormal family" constructor exists in `S07` — building it (the
τ₃ that restricts to `τ` on the shared supported lattice, Peterfalvi (5.3.b)/(5.5)/(6.8.1) style) is
the deep step this `sorry` still stands for.  See `notes/peterfalvi/s13_11_8_orthogonality.md`. -/
theorem Hypothesis.coherent_Sset_of_column_identities [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hnt : TypePNontrivialCore M hyp.typeP)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetup htype hnt))
    (hw2 : 2 ≤ hyp.w2)
    (hd1 : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muGrid hG hG.odd 0 j 1 ≠ 1)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ}
    (hdu : (d : ℂ) = ((hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u : ℂ))
    (hcol : ∀ j : Fin hyp.w2, j ≠ 0 →
      hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) - (d : ℂ) • ζ)
        = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i j)
          - (d : ℂ) • coh.extension ζ) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0) := by
  haveI := hyp.finiteG
  classical
  -- **obligation-2 (`ν`) is discharged** by `exists_glue_nu` (issue 9016); `hY` is the §9/§14-gated
  -- `S₂`-coherence (sorried-cite via `coherent_Sset_diff_SHCSet`).  The `τ₃` glue then reduces the
  -- (11.8.6) union-coherence to exactly the genuine (6.7)/(5.8) character content, isolated below.
  obtain ⟨hY⟩ := hyp.coherent_Sset_diff_SHCSet hG
  obtain ⟨ν, hagreeX, hagreeY⟩ := hyp.exists_glue_nu coh hY
  refine ⟨hyp.coherent_Sset_of_glued coh hY ν hagreeX hagreeY ?_
    {φ | ∃ j : Fin hyp.w2, j ≠ 0 ∧
      φ = (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) - (d : ℂ) • ζ} ?_ ?_⟩
  · -- `hmixed` → the **(6.7) image-side orthogonality**: after `hagreeX`/`hagreeY` and the source
    -- orthogonality `⟨x,y⟩ = 0` (`SHCSet_inner_diff_eq_zero`), the residual is
    -- `⟨coh.extension x, hY.extension y⟩ = 0` — Peterfalvi's `b ≡ 0` congruence, a property of the
    -- two coherent extensions beyond bare `IsCoherent` (§14/BG §15-gated via `hY`'s Sibley structure).
    intro x hx y hy
    rw [hagreeX x hx, hagreeY y hy, hyp.SHCSet_inner_diff_eq_zero hx hy]
    sorry
  · -- `hDτ` → the **(5.8) column identity**: on the cross-diagonal `∑ᵢ μ_{ij} − dζ`, `hcol` rewrites
    -- the base map `τ`, leaving `ν (∑ᵢ μ_{ij} − dζ) = ∑ᵢ ω^σ_{ij} − d·coh.extension ζ`.  Via
    -- `hagreeX` (ζ ∈ S₁) and `hagreeY` (the reducible column sum ∈ S₂) this is
    -- `hY.extension (∑ᵢ μ_{ij}) = ∑ᵢ ω^σ_{ij}` — the (5.8) identity for `hY`'s extension (§14-gated).
    intro d' hd'
    obtain ⟨j, hj, rfl⟩ := hd'
    rw [hcol j hj]
    sorry
  · -- `hgen` → **discharged by `hgen_of_S2_uniform_degree`** (this session): the (6.8.1) generation
    -- ALGEBRA is landed sorry-free.  Its only §9-gated input is the `S₂` uniform-degree structure —
    -- `S₂ = S(C) − S(HC)` all of degree `qu = d·w₁` (the (11.8.1) reducible decomposition) with a
    -- column witness `ψ₀ = ∑ᵢ μ_{ij₀} ∈ D` — bundled here as a single §9 obligation (NOT a vacuous
    -- hoist: it is the genuine (11.8.1) two-degree-class structure of `𝒮(C)`, §9/world-bridge-gated).
    have hζmem : ζ ∈ hyp.SHCSet := ⟨hζS, hζirr, hζ1⟩
    obtain ⟨ψ₀, hψ₀, hDmem⟩ : ∃ ψ₀ ∈ hyp.Sset \ hyp.SHCSet,
        (ψ₀ - (d : ℂ) • ζ) ∈ {φ : ClassFunction ↥M ℂ | ∃ j : Fin hyp.w2, j ≠ 0 ∧
          φ = (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) - (d : ℂ) • ζ} := by
      -- column witness: a nonzero μ-column `μ_{j₀}` (`w₂ ≥ 2`) is reducible
      -- (`muGrid_column_sum_mem_sOf_H0_and_reducible` ⟹ ∉ `SHCSet`) and `∈ inducedFamily`
      -- (`muGrid_column_sum_mem_inducedFamily`), with `μ_{j₀} − dζ ∈ D` by definition of `D`.
      obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin hyp.w2, j₀ ≠ 0 :=
        ⟨⟨1, by omega⟩, Fin.ne_of_val_ne (by simp)⟩
      exact ⟨∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j₀,
        ⟨hyp.muGrid_column_sum_mem_inducedFamily hG hG.odd j₀ (hd1 j₀ hj₀),
          fun hmem => (hyp.muGrid_column_sum_mem_sOf_H0_and_reducible hG htype hnt chief j₀ hj₀).2
            hmem.2.1⟩,
        j₀, hj₀, rfl⟩
    refine hyp.hgen_of_S2_uniform_degree hG ?_ ?_
      (fun y hy => hyp.Sset_diff_SHCSet_apply_one_eq_qu hG htype hnt chief hy) hζmem hψ₀ _ hDmem
    · -- `hqune`: `q·u ≠ 0` (both positive cardinalities).
      have hqpos : 0 < (hyp.toTypesIIIIIIVSetup htype hnt).q := by
        change 0 < hyp.w1; exact Nat.card_pos
      exact_mod_cast Nat.mul_ne_zero hqpos.ne' Nat.card_pos.ne'
    · -- `hqu`: `(q·u : ℂ) = d·w₁` via `q = w₁` (rfl) and `hdu` (`d = u`).
      have hq : (hyp.toTypesIIIIIIVSetup htype hnt).q = hyp.w1 := rfl
      rw [Nat.cast_mul, hq, ← hdu]; ring

open scoped FiniteInduce in
/-- **Peterfalvi (11.8), the genuine non-orthogonality** (lane-b W3 obligation, issue 2020).

Under Hypothesis (10.1), there is an irreducible `ζ ∈ S = inducedFamily M` of degree `w₁` —
Peterfalvi's `ζ ∈ S(HC)`, a degree-`q` constituent of the constant-degree family `S₁ = S(HC)`
(the `(U/C) ⋊ W₁` Frobenius gives `(u−1)/q` irreducibles of degree `q`) — for which the residual
`(μ₀ − ζ)^τ − ∑_i ω_{i0}^σ` is **not** orthogonal to `(Irr W)^σ`.

This is the deep orthogonality calculation Peterfalvi (11.8.1)–(11.8.6): by contradiction, assuming
the residual orthogonal makes `S(C)` coherent (via the `τ₁`/`τ₂` extensions from (5.7)/(11.7) and the
`σ`-grid identities), contradicting (11.3) (`S13.S_H0C_not_coherent`).  It is the **sole** remaining
genuine §11 character content of (11.9.b): the `w₂ < w₁` reduction it feeds
(`w2_lt_w1_of_residual_not_orthogonal`) and the carrier translation (`|K| = w₁` from the derived
index, `|K*| = w₂` from `card_Msigma_inf_centralizer_eq_card_W2`) are proven, so discharging this
closes `card_kappaHall_lt_of_isTypeIIIorIV` (the unique bare `feitThompson` sorry).  See
`notes/peterfalvi/s13_11_8_orthogonality.md` for the full formalization plan. -/
theorem exists_zeta_residual_not_orthogonal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (hM2 : secondDerivedInAmbient M
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1) :
    ∃ ζ : ClassFunction ↥M ℂ, ζ ∈ inducedFamily M ∧ IsIrreducibleCharacter ζ ∧
      ζ 1 = (hyp.w1 : ℂ) ∧
      ¬ ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
        ClassFunction.inner
          ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' 0) - ζ))
            - ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i' 0)
          (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = 0 := by
  -- Peterfalvi's (10.2)/(10.3) character parameters of (10.4): `params.zeta` is the degree-`w₁`
  -- irreducible of (10.2) (`ζ ∈ S(HC)`), with the `μ`/`ω^σ`-grids, `δ = ±1` and column-sign data —
  -- the (10.6.b) conditions the (11.8.1)–(11.8.6) `σ`-grid identities consume.
  obtain ⟨params, hmu, -, hzS, hz1, -, hδpm, hδindep⟩ := hyp.exists_charParameters_full hG
  refine ⟨params.zeta, hzS, params.zeta_irreducible, hz1, ?_⟩
  -- The deep non-orthogonality calculation Peterfalvi (11.8.1)–(11.8.6): by contradiction, the
  -- residual `(μ₀−ζ)^τ − ∑ᵢ ω_{i0}^σ` being orthogonal to `(Irr W)^σ` forces the (5.6) coherence of
  -- the whole family `S = S(HC) ∪ (S(C)−S(HC))`, contradicting (10.8) `S_not_coherent`.
  intro h_orth
  -- (11.8.1) `δ = 1` (§9 count).
  have hδ1 : params.delta = 1 := hyp.charParam_delta_eq_one hG htype params hmu hδpm
  -- (11.8.4) the coherent extension `ν` and the `h114` value, from the orthogonality assumption.
  obtain ⟨ν, hνconj, h114⟩ :=
    hyp.exists_coherent_extension_h114_of_orthogonal hG hG.odd hzS params.zeta_irreducible hz1 h_orth
  -- (11.8.1)/(5.7) the orthonormal coherent image `R`; its cardinality `|R| = n` is the §9 count.
  obtain ⟨R, hZ, hRorth, hRmem, hRrev, hRcard⟩ := hyp.exists_coherentImage_SHC ν
  have hRn : R.card = params.n :=
    hRcard.trans (hyp.card_SHCSet_filter_eq_charParam_n hG htype params hmu hδpm hM2 hHcard)
  -- degree relations at `δ = 1`.
  have hnf : (params.n : ℤ) * (hyp.w1 : ℤ) = (params.d : ℤ) - 1 := by rw [← hδ1]; exact params.n_formula
  have hd : (params.d : ℂ) = (hyp.w1 : ℂ) * (params.n : ℂ) + 1 := by
    have h : (params.n : ℂ) * (hyp.w1 : ℂ) = (params.d : ℂ) - 1 := by exact_mod_cast hnf
    linear_combination -h
  have hμ0all : ∀ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0 1 = 1 :=
    fun i => hyp.muGrid_zero_column_apply_one hG hG.odd i
  -- (11.8.2)–(11.8.6 opening) the column identities `(μ_j − dζ)^τ = ∑_i ω_{ij}^σ − dζ^{τ₁}`.
  have hcol : ∀ j : Fin hyp.w2, j ≠ 0 →
      hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) - (params.d : ℂ) • params.zeta)
        = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i j)
          - (params.d : ℂ) • ν.extension params.zeta := by
    intro j hj
    have hdegall : ∀ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j 1 = (params.d : ℂ) :=
      fun i => hmu ▸ params.degree_independent i j hj
    have hδjj : hyp.muColumnSign hG hG.odd j = 1 := (hδindep j hj).trans hδ1
    exact hyp.tau_muColumnSum_sub_dzeta_eq_of_residualData hG ν hνconj hG.odd hj hzS
      params.zeta_irreducible hz1 params.w2_prime hd hnf hdegall hμ0all hδjj params.two_le_n
      hRn hZ hRorth hRmem hRrev h114
  -- (11.8.6) the τ₂ union makes `S = S(C)` coherent, contradicting (10.8) `S_not_coherent`.
  -- Thread the §9 datum (htype ⟹ hnt, chief) and `d = u` (`charParam_d_eq_u`) into the capstone so
  -- its `hgen` consumes the world-bridge `Sset_diff_SHCSet_apply_one_eq_qu` (this session).
  have hnt : TypePNontrivialCore M hyp.typeP := typePNontrivialCore_of_isTypeIIIorIV htype hyp.typeP
  obtain ⟨chief, -⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetup htype hnt)
  have hdu : (params.d : ℂ)
      = ((hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u : ℂ) := by
    exact_mod_cast hyp.charParam_d_eq_u hG htype params hmu hnt chief
  -- `w₂ ≥ 2` (`params.w2_prime`) and the μ-grid degree `μ_{0j}(1) = d > 1` (`degree_independent` +
  -- `d_gt_one`) feed the capstone's `ψ₀` column witness (reducible `μ_{j₀} ∈ Sset \ SHCSet`).
  have hw2 : 2 ≤ hyp.w2 := params.w2_prime.two_le
  have hd1 : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muGrid hG hG.odd 0 j 1 ≠ 1 := by
    intro j hj
    have hdeg : hyp.muGrid hG hG.odd 0 j 1 = (params.d : ℂ) :=
      hmu ▸ params.degree_independent 0 j hj
    rw [hdeg]
    exact_mod_cast (show params.d ≠ 1 by have := params.d_gt_one; omega)
  exact S_not_coherent hG hyp
    (hyp.coherent_Sset_of_column_identities hG ν htype hnt chief hw2 hd1 hzS
      params.zeta_irreducible hz1 hdu hcol)

open scoped FiniteInduce in
/-- **Peterfalvi (11.9.b)**: for the §10 hypothesis on a type-III/IV/V maximal subgroup, `w₂ < w₁`
(`q > p`).  Combines the genuine (11.8) (`exists_zeta_residual_not_orthogonal`) with the
coherence-free `w₂ < w₁` reduction (`w2_lt_w1_of_residual_not_orthogonal`). -/
theorem w2_lt_w1_of_hypothesis [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (hM2 : secondDerivedInAmbient M
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1) :
    hyp.w2 < hyp.w1 := by
  obtain ⟨ζ, hζS, hζirr, hζ1, h118⟩ :=
    exists_zeta_residual_not_orthogonal hG hyp htype hM2 hHcard
  exact w2_lt_w1_of_residual_not_orthogonal hG hyp hζS hζirr hζ1 h118

/-- **Peterfalvi (10.10.1), pure arithmetic**: for the type-V case (c) parameters — `p = w₂` prime,
`w₁ ∣ p+1` (both odd, `w₁ > 1`), and the Huppert bound `|H:H'| = p² ≤ 4w₁²+1` (6.5.a) — one has
`p = 2w₁ − 1`, hence `w₁ < p = w₂`.

Writing `p+1 = 2k·w₁` (`m := (p+1)/w₁` is even, since `p+1` is even and `w₁` odd), the bound gives
`(2kw₁−1)² ≤ 4w₁²+1`, i.e. `w₁(k²−1) ≤ k`; with `w₁ ≥ 2`, `k ≥ 1` this forces `k = 1`.  Mirrors the
`typeII_noncoherence_arithmetic` pattern (the analytic/structural inputs are isolated). -/
theorem typeV_param_arithmetic {p w₁ : ℕ} (hpodd : Odd p) (hw1odd : Odd w₁) (hw1 : 1 < w₁)
    (hdvd : w₁ ∣ p + 1) (hbound : p ^ 2 ≤ 4 * w₁ ^ 2 + 1) :
    p = 2 * w₁ - 1 ∧ w₁ < p := by
  obtain ⟨m, hm⟩ := hdvd
  -- `m` is even: `p+1` is even (`p` odd) and `w₁` is odd.
  have hm_even : Even m := by
    have hp1even : Even (p + 1) := Odd.add_one hpodd
    rw [hm] at hp1even
    rcases Nat.even_mul.mp hp1even with h | h
    · exact absurd h (Nat.not_even_iff_odd.mpr hw1odd)
    · exact h
  obtain ⟨k, hk⟩ := hm_even
  have hpk : p + 1 = 2 * w₁ * k := by rw [hm, hk]; ring
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h1
    · rw [h0, Nat.mul_zero] at hpk; omega
    · exact h1
  -- `k = 1` from the bound (over `ℤ` to avoid `ℕ`-subtraction).
  have hk1 : k = 1 := by
    have hpZ : (p : ℤ) = 2 * w₁ * k - 1 := by
      have : (p : ℤ) + 1 = 2 * (w₁ : ℤ) * k := by exact_mod_cast hpk
      linarith
    have hboundZ : (p : ℤ) ^ 2 ≤ 4 * (w₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hbound
    rw [hpZ] at hboundZ
    have hw1Z : (2 : ℤ) ≤ w₁ := by exact_mod_cast hw1
    have hkZ : (1 : ℤ) ≤ k := by exact_mod_cast hkpos
    have hkle : (k : ℤ) ≤ 1 := by
      nlinarith [hboundZ, hw1Z, hkZ, mul_nonneg (by linarith : (0:ℤ) ≤ (w₁:ℤ) - 2)
        (by nlinarith : (0:ℤ) ≤ (k:ℤ)^2 - 1), sq_nonneg ((k:ℤ) - 1)]
    omega
  subst hk1
  constructor
  · omega
  · omega

/-- **Peterfalvi (10.10.1)--(10.10.4)**: if Hypothesis (10.1) holds with `M` of type V, then the
type-V parameter calculation forces `S` to be coherent.

De-scaffolded: the conclusion is now the *genuine* coherence `Nonempty (IsCoherent τ S A₀)` only,
dropping the former opaque `typeV_parameter_formula`/`typeV_coherence_formula : Prop` conjuncts
(unprovable for generic `params`; producers set them `True`).  The remaining `sorry` is the honest
(10.10.1)–(10.10.4) coherence argument: case (a) of Def (8.7) gives coherence by (6.8); case (b) is
excluded by (6.5.c); case (c) (`|H| = p³`, `w₁ ∣ p+1`) runs the parameter calculation
(`typeV_param_arithmetic` gives `p = 2w₁−1`, then `d = p`, `δ = −1`, `n = 2`) and the σ-grid column
identities (reusing the (11.8) `muGrid`/`alignedOmegaSigmaGrid`/coherent-extension machinery).
Gated on the §6/§8 coherence inputs (6.5.a/6.8) and the type-V `|H| = p³` structure. -/
theorem typeV_forces_coherence [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} (hV : IsTypeV M) (params : CharacterParameters hyp) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0) := by
  sorry

open scoped FiniteInduce in
/-- **Peterfalvi (10.10)**: `G` has no maximal subgroup of type V.

By (10.8) (`S_not_coherent`) the family `S` of any type-III/IV/V maximal is not
coherent; but a type-V maximal forces `S` to be coherent by (10.10.1)–(10.10.4)
(`typeV_forces_coherence`).  These now refer to the *genuine* Dade isometry,
induced family, and support carried by the faithful (10.1) `Hypothesis` (built by
`exists_hypothesis_of_typeIIIorIVorV`), so the contradiction is honest. -/
theorem no_typeV_maximal [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M := by
  rintro ⟨M, hMmax, hMV⟩
  obtain ⟨hyp⟩ := exists_hypothesis_of_typeIIIorIVorV hG hMmax (Or.inr (Or.inr hMV))
  obtain ⟨params, -⟩ := w2_prime_and_parameter_independence hG hyp
  exact S_not_coherent hG hyp (typeV_forces_coherence hG hMV params)

/-- The case-(b) data in Peterfalvi (8.8), used in the remark (10.11). -/
structure Theorem88CaseBData (G : Type*) [Group G] where
  S : Subgroup G
  T : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W : Subgroup G
  S_maximal : S ∈ maximalSubgroups G
  T_maximal : T ∈ maximalSubgroups G
  S_ne_T : S ≠ T
  W_eq : W = W1 ⊔ W2
  W_cyclic : IsCyclic ↥W
  S_nonI : IsTypeNonI S
  T_nonI : IsTypeNonI T
  one_typeII : IsTypeII S ∨ IsTypeII T
  /-- (8.8.b1): `W₁ ≤ S` and `S = [S,S] ⋊ W₁` (so `W₁` complements `S' = [S,S]` in `S`). -/
  W1_le_S : W1 ≤ S
  W2_le_T : W2 ≤ T
  S_compl : Subgroup.IsComplement' ((derivedInG S).subgroupOf S) (W1.subgroupOf S)
  T_compl : Subgroup.IsComplement' ((derivedInG T).subgroupOf T) (W2.subgroupOf T)

/-- A non-type-I maximal subgroup that is not of type V (so of type II/III/IV) carries type-`P`
data whose `W₁` has prime order — Peterfalvi (8.6.a), via `TypePNontrivialCore`.  Type V is
excluded by Theorem (10.10) `no_typeV_maximal`. -/
private theorem caseB_typeP_prime_W1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hnonI : IsTypeNonI M) :
    ∃ data : TypePData M, (Nat.card ↥data.W1).Prime := by
  rcases hnonI with h | h | h | h
  · exact ⟨h.some.typeP, h.some.common.2.1⟩
  · exact ⟨h.some.typeP, h.some.common.2.1⟩
  · exact ⟨h.some.typeP, h.some.common.2.1⟩
  · exact absurd ⟨M, hM, h⟩ (no_typeV_maximal hG)

/-- **Peterfalvi (10.11), first assertion**: in case (b) of Theorem (8.8), the
orders of `W_1` and `W_2` are prime.

By Theorem (10.10) `no_typeV_maximal`, the non-type-I subgroups `S`, `T` are of type II/III/IV,
whose type-`P` `W₁` has prime order (8.6.a).  The case-(b) factors `W₁`, `W₂` complement the
derived subgroups of `S`, `T` (8.8.b1, `S_compl`/`T_compl`), so they share the orders
`|S : S'|`, `|T : T'|` with the respective type-`P` `W₁` (`card_W1_eq_derived_index`) — hence prime. -/
theorem theorem88_caseB_prime_orders [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (caseB : Theorem88CaseBData G) :
    (Nat.card ↥caseB.W1).Prime ∧ (Nat.card ↥caseB.W2).Prime := by
  have hW1 : Nat.card ↥caseB.W1 = ((derivedInG caseB.S).subgroupOf caseB.S).index := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe caseB.W1_le_S).toEquiv,
      ← caseB.S_compl.symm.index_eq_card]
  have hW2 : Nat.card ↥caseB.W2 = ((derivedInG caseB.T).subgroupOf caseB.T).index := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe caseB.W2_le_T).toEquiv,
      ← caseB.T_compl.symm.index_eq_card]
  refine ⟨?_, ?_⟩
  · obtain ⟨dataS, hSp⟩ := caseB_typeP_prime_W1 hG caseB.S_maximal caseB.S_nonI
    rw [hW1, ← dataS.card_W1_eq_derived_index]; exact hSp
  · obtain ⟨dataT, hTp⟩ := caseB_typeP_prime_W1 hG caseB.T_maximal caseB.T_nonI
    rw [hW2, ← dataT.card_W1_eq_derived_index]; exact hTp

/-- **Peterfalvi (10.11), Type II assertion**: for a type-II maximal subgroup,
the §11 family `S(H_0 C')` specializes to a coherent set. -/
theorem typeII_section11_coherence [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M}
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData data}
    (chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent chars.tau chars.S chars.H0CprimeSupport) := by
  exact ⟨OddOrder.Peterfalvi.S11.coherent_H0C_commutator chars⟩

end OddOrder.Peterfalvi.S12
