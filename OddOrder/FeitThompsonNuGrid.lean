import OddOrder.FeitThompsonSetup
import OddOrder.Peterfalvi.S15_HonestTypeP2A0

/-!
# Peterfalvi certain-Type-T ν-grid

This file constructs the canonical T-side grid used in Peterfalvi (4.3)--(4.9) and (13.1).
It mirrors the S-side `muS` supply from the certain-type hypothesis on the partner maximal
subgroup, keeping the producer below the final Section 16 assembly.
-/

namespace OddOrder

open OddOrder.BG
open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.RepresentationTheory
open scoped Pointwise

section
open scoped OddOrder.Peterfalvi.S15.FiniteInduce

namespace Section16CharacterData

variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G)
  (mp : Section16MaximalPair G)
variable (tp : Section16TypePStructure mp)
variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

/-! ## S/T-shared `ω` and the T-side grid -/

/-- The `G`-element-preserving equiv
`↥certainTypeT.sdiff.W ≃* ↥certainTypeS.sdiff.W` through `↥tp.W`. -/
noncomputable def eTS :
    ↥(mp.certainTypeT hG).sdiffTICyclicHypothesis.W ≃*
      ↥(mp.certainTypeS hG).sdiffTICyclicHypothesis.W :=
  (gridEquivE_T hG mp tp).symm.trans (gridEquivE hG mp tp)

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- The round-trip through `tp.W`. -/
theorem eTS_gridEquivE_T (w : ↥tp.W) :
    eTS hG mp tp (gridEquivE_T hG mp tp w) = gridEquivE hG mp tp w := by
  simp only [eTS, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

/-- T-side column dual on `W₂_T = mp.K`. -/
noncomputable def colT (i : Fin tp.q) :
    ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W2.subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ :=
  (((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
        ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)) 1).comp
      (eTS hG mp tp).toMonoidHom).comp
    ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W2.subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W).subtype

/-- T-side row dual on `W₁_T = mp.Kstar`. -/
noncomputable def rowDualT (j : Fin tp.p) :
    ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W1.subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ :=
  (((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
      1 (chi2enum hG mp tp j)).comp (eTS hG mp tp).toMonoidHom).comp
    ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W1.subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W).subtype

/-- `colT i` agrees with the S-side dual on a transported `mp.K`-element. -/
theorem colT_apply_mem_K (i : Fin tp.q) (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    colT hG mp tp i ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W2 hG mp tp w hw⟩
      = (mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)
          ⟨gridEquivE hG mp tp w, gridEquivE_mem_W1 hG mp tp w hw⟩ := by
  rw [colT, MonoidHom.comp_apply, MonoidHom.comp_apply]
  change (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
      ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)) 1
      (eTS hG mp tp (gridEquivE_T hG mp tp w)) = _
  rw [eTS_gridEquivE_T]
  exact omegaProdCharS_apply_mem_K hG mp tp _ 1 w hw

/-- The base T-side column dual is trivial. -/
theorem colT_zero : colT hG mp tp ⟨0, tp.q_prime.pos⟩ = 1 := by
  ext x
  simp [colT, eqQ_zero, Peterfalvi.S05.TICyclicHypothesis.omegaProdChar]
  rfl

/-- Column-index negation is inversion of the transported T-side column dual. -/
theorem colT_finNeg (i : Fin tp.q) :
    colT hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
      = (colT hG mp tp i)⁻¹ := by
  have heq :
      eqQ hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
        = ⟨(Nat.card ↥(mp.certainTypeS hG).W1 - ((eqQ hG mp tp i : Fin _) : ℕ))
              % Nat.card ↥(mp.certainTypeS hG).W1,
            Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))⟩ := by
    apply Fin.ext
    simp only [eqQ, finCongr_apply, Fin.val_cast, OddOrder.Peterfalvi.S15.finNeg]
    rw [cardCertainTypeS_W1 hG mp tp]
  rw [colT, colT, heq,
    (mp.certainTypeS hG).w1CharEquiv_finNeg (eqQ hG mp tp i)]
  ext w
  simp [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar,
    Units.val_inv_eq_inv_val]
  exact Units.val_inv_eq_inv_val _

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- `rowDualT j` agrees with the S-side dual on a transported `mp.Kstar`-element. -/
theorem rowDualT_apply_mem_Kstar (j : Fin tp.p) (w : ↥tp.W)
    (hw : (w : G) ∈ mp.Kstar) :
    rowDualT hG mp tp j
        ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W1 hG mp tp w hw⟩
      = chi2enum hG mp tp j
          ⟨gridEquivE hG mp tp w, gridEquivE_mem_W2 hG mp tp w hw⟩ := by
  rw [rowDualT, MonoidHom.comp_apply, MonoidHom.comp_apply]
  change (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
      1 (chi2enum hG mp tp j) (eTS hG mp tp (gridEquivE_T hG mp tp w)) = _
  rw [eTS_gridEquivE_T]
  exact omegaProdCharS_apply_mem_Kstar hG mp tp 1 _ w hw

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- The base row dual is trivial. -/
theorem rowDualT_zero : rowDualT hG mp tp ⟨0, tp.p_prime.pos⟩ = 1 := by
  rw [rowDualT, chi2enum_zero,
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_one,
    MonoidHom.one_comp, MonoidHom.one_comp]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- Row-index negation is inversion of the transported T-side row dual. -/
theorem rowDualT_finNeg (j : Fin tp.p) :
    rowDualT hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)
      = (rowDualT hG mp tp j)⁻¹ := by
  rw [rowDualT, rowDualT, chi2enum_finNeg hG mp tp j]
  ext w
  simp [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar]
variable [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)]

/-- T-side row index corresponding to `rowDualT`. -/
noncomputable def rowT (j : Fin tp.p) : Fin (Nat.card ↥(mp.certainTypeT hG).W1) :=
  (mp.certainTypeT hG).w1CharEquiv.symm (rowDualT hG mp tp j)

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- The distinguished T-side row index is zero. -/
theorem rowT_zero : rowT hG mp tp ⟨0, tp.p_prime.pos⟩ = 0 := by
  rw [rowT, rowDualT_zero]
  exact (mp.certainTypeT hG).w1CharEquiv.symm_apply_eq.mpr
    ((mp.certainTypeT hG).w1CharEquiv_zero).symm

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- The transported row enumeration intertwines `finNeg` with the certain-type `rowInv`. -/
theorem rowT_finNeg_eq_rowInv (j : Fin tp.p) :
    rowT hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)
      = OddOrder.Peterfalvi.S06.rowInv (mp.certainTypeT hG) (rowT hG mp tp j) := by
  apply (mp.certainTypeT hG).w1CharEquiv.injective
  rw [OddOrder.Peterfalvi.S06.w1CharEquiv_rowInv, rowT,
    Equiv.apply_symm_apply, rowDualT_finNeg hG mp tp j]
  congr 1
  rw [rowT, Equiv.apply_symm_apply]

/-- The shared `ω`-grid expressed through `certainTypeT`. -/
noncomputable def omegaT (i : Fin tp.q) (j : Fin tp.p) : ClassFunction ↥tp.W ℂ :=
  ClassFunction.compHom (gridEquivE_T hG mp tp).toMonoidHom
    ((mp.certainTypeT hG).chiColumn (colT hG mp tp i) (rowT hG mp tp j) :
      ClassFunction ↥(mp.certainTypeT hG).sdiffTICyclicHypothesis.W ℂ)

/-- The S- and T-side constructions give the same shared `ω`-grid. -/
theorem omegaS_eq_omegaT (i : Fin tp.q) (j : Fin tp.p) :
    omegaS hG mp tp i j = omegaT hG mp tp i j := by
  have hrow : (mp.certainTypeT hG).w1CharEquiv (rowT hG mp tp j) =
      rowDualT hG mp tp j := by
    rw [rowT, Equiv.apply_symm_apply]
  have key : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.omegaProdChar
          (rowDualT hG mp tp j) (colT hG mp tp i)).comp
          (gridEquivE_T hG mp tp).toMonoidHom
      = ((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
          ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i))
          (chi2enum hG mp tp j)).comp (gridEquivE hG mp tp).toMonoidHom := by
    apply monoidHom_eq_of_eqOn_W1_W2
    · intro w hw
      rw [tp.W1_eq_K hG] at hw
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [omegaProdCharT_apply_mem_K hG mp tp _ _ w hw,
        colT_apply_mem_K hG mp tp i w hw]
      exact (omegaProdCharS_apply_mem_K hG mp tp _ _ w hw).symm
    · intro w hw
      rw [tp.W2_eq_Kstar hG] at hw
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [omegaProdCharT_apply_mem_Kstar hG mp tp _ _ w hw,
        rowDualT_apply_mem_Kstar hG mp tp j w hw]
      exact (omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hw).symm
  simp only [omegaS, omegaT, Peterfalvi.S06.Hypothesis.chiColumn,
    Peterfalvi.S05.TICyclicHypothesis.omega]
  rw [hrow, ClassFunction.compHom_linearIrreducibleCharacter,
    ClassFunction.compHom_linearIrreducibleCharacter, key]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.3)/(3.4)**: the shared `ω`-grid is orthonormal. -/
theorem omegaS_inner (i k : Fin tp.q) (j l : Fin tp.p) :
    ClassFunction.inner (omegaS hG mp tp i j) (omegaS hG mp tp k l)
      = if i = k ∧ j = l then 1 else 0 := by
  rw [omegaS, omegaS, ClassFunction.inner_compHom_mulEquiv (gridEquivE hG mp tp)]
  simp only [Peterfalvi.S06.Hypothesis.chiColumn]
  rw [(mp.certainTypeS hG).sdiffTICyclicHypothesis.omega_inner]
  by_cases h : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
  · have hne : (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
        ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)) (chi2enum hG mp tp j)
        ≠ (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
          ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp k)) (chi2enum hG mp tp l) := by
      intro hc
      obtain ⟨h1, h2⟩ :=
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_inj hc
      exact h ⟨(eqQ hG mp tp).injective
          ((mp.certainTypeS hG).w1CharEquiv_injective h1),
        (chi2enum hG mp tp).injective h2⟩
    rw [if_neg hne, if_neg h]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- Distinct index pairs give distinct members of the shared `ω`-grid. -/
theorem omegaS_pair_injective :
    Function.Injective
      (fun ij : Fin tp.q × Fin tp.p => omegaS hG mp tp ij.1 ij.2) := by
  intro ⟨i, j⟩ ⟨k, l⟩ hω
  change omegaS hG mp tp i j = omegaS hG mp tp k l at hω
  by_contra hne
  have h1 := omegaS_inner hG mp tp i k j l
  rw [hω] at h1
  have h2 := omegaS_inner hG mp tp k k l l
  rw [h1] at h2
  have hcond : ¬ (i = k ∧ j = l) := fun ⟨h1', h2'⟩ => hne (by rw [h1', h2'])
  rw [if_neg hcond, if_pos (⟨rfl, rfl⟩ : k = k ∧ l = l)] at h2
  exact zero_ne_one h2

/-- The transported T-side row enumeration is injective. -/
theorem rowT_injective : Function.Injective (rowT hG mp tp) := by
  intro j l hrow
  have hω : omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j =
      omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ l := by
    rw [omegaS_eq_omegaT hG mp tp, omegaS_eq_omegaT hG mp tp]
    simp only [omegaT, hrow]
  have hp : ((⟨0, tp.q_prime.pos⟩ : Fin tp.q), j) =
      ((⟨0, tp.q_prime.pos⟩ : Fin tp.q), l) :=
    omegaS_pair_injective hG mp tp hω
  exact congrArg Prod.snd hp

/-- The transported T-side column enumeration is injective. -/
theorem colT_injective : Function.Injective (colT hG mp tp) := by
  intro i k hcol
  have hω : omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩ =
      omegaS hG mp tp k ⟨0, tp.p_prime.pos⟩ := by
    rw [omegaS_eq_omegaT hG mp tp, omegaS_eq_omegaT hG mp tp]
    simp only [omegaT, hcol]
  have hp : (i, (⟨0, tp.p_prime.pos⟩ : Fin tp.p)) =
      (k, (⟨0, tp.p_prime.pos⟩ : Fin tp.p)) :=
    omegaS_pair_injective hG mp tp hω
  exact congrArg Prod.fst hp

/-- The transported T-side row enumeration is bijective. -/
theorem rowT_bijective : Function.Bijective (rowT hG mp tp) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨rowT_injective hG mp tp, ?_⟩
  simp only [Fintype.card_fin]
  exact (cardCertainTypeT_W1 hG mp tp).symm

/-- Reindexing equivalence for the T-side rows. -/
noncomputable def rowTEquiv :
    Fin tp.p ≃ Fin (Nat.card ↥(mp.certainTypeT hG).W1) :=
  Equiv.ofBijective (rowT hG mp tp) (rowT_bijective hG mp tp)

/-- The transported T-side column enumeration is bijective in the certain-type column-dual
presentation. -/
theorem colT_bijective : Function.Bijective
    (fun i : Fin tp.q =>
      show (((mp.certainTypeT hG).W2.subgroupOf
        ((mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2)) →* ℂˣ) from
        colT hG mp tp i) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨fun _ _ h => colT_injective hG mp tp h, ?_⟩
  have hcard :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.card_charGroup_subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W2_le_W
  change Nat.card (((mp.certainTypeT hG).W2.subgroupOf
      ((mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2)) →* ℂˣ) =
    Nat.card ↥(mp.certainTypeT hG).W2 at hcard
  simp only [Fintype.card_fin]
  rw [← Nat.card_eq_fintype_card]
  exact (hcard.trans (cardCertainTypeT_W2 hG mp tp)).symm

/-- Reindexing equivalence for the T-side columns. -/
noncomputable def colTEquiv :
    Fin tp.q ≃
      (((mp.certainTypeT hG).W2.subgroupOf
        ((mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2)) →* ℂˣ) :=
  Equiv.ofBijective
    (fun i : Fin tp.q =>
      show (((mp.certainTypeT hG).W2.subgroupOf
        ((mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2)) →* ℂˣ) from
        colT hG mp tp i)
    (colT_bijective hG mp tp)

/-- T-side `ν`-grid from the certain-type characters of `mp.T`. -/
noncomputable def nuT (i : Fin tp.q) (j : Fin tp.p) : ClassFunction ↥mp.T ℂ :=
  (((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).mu
      (rowT hG mp tp j) : ClassFunction ↥mp.T ℂ)

/-- T-side signs `δ'`. -/
noncomputable def deltaPrimeT (i : Fin tp.q) : ℤ :=
  ((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).sign

/-- Every entry of the canonical T-side `ν`-grid is irreducible. -/
theorem nuT_irreducible (i : Fin tp.q) (j : Fin tp.p) :
    IsIrreducibleCharacter (nuT hG mp tp i j) :=
  (((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).mu
    (rowT hG mp tp j)).isIrreducible

/-- Within each T-side row, the canonical `ν`-characters are pairwise distinct. -/
theorem nuT_row_injective (i : Fin tp.q) :
    Function.Injective (fun j : Fin tp.p => nuT hG mp tp i j) := by
  intro j l hν
  apply rowT_injective hG mp tp
  apply ((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).injective
  exact IrreducibleCharacter.ext hν

/-- **Peterfalvi (4.3.b), T-side**: the canonical `ν`-grid is orthonormal. -/
theorem nuT_orthonormal (i k : Fin tp.q) (j l : Fin tp.p) :
    ClassFunction.inner (nuT hG mp tp i j) (nuT hG mp tp k l)
      = if i = k ∧ j = l then 1 else 0 := by
  simp only [nuT]
  rw [irreducibleCharacter_inner_eq_ite]
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
    · rw [if_neg (fun hc => hjl (rowT_injective hG mp tp
          ((((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).injective) hc))),
        if_neg (by simp [hjl])]
  · rw [if_neg ((mp.certainTypeT hG).columnFamily_mu_ne
        (fun hc => hik (colT_injective hG mp tp hc)) _ _),
      if_neg (by simp [hik])]

/-- **Peterfalvi (4.3.c), T-side** (Coq `prTIirr_id`, `PFsection4.v:403`): on
`W ∖ W₁` the canonical `ν`-grid is the signed shared `ω`-grid,
`ν_{ij}(w) = δ'_i·ω_{ij}(w)`. -/
theorem nuT_apply_of_not_mem_W1 (i : Fin tp.q) (j : Fin tp.p) (w : G)
    (hwW : w ∈ tp.W) (hwT : w ∈ mp.T) (hw1 : w ∉ (tp.W1 : Set G)) :
    nuT hG mp tp i j ⟨w, hwT⟩
      = (deltaPrimeT hG mp tp i : ℂ) * omegaS hG mp tp i j ⟨w, hwW⟩ := by
  have hjoin : (⟨w, hwT⟩ : ↥mp.T) ∈
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W := by
    rw [← tpW_subgroupOf_T_eq hG mp tp]
    exact Subgroup.mem_subgroupOf.mpr hwW
  have hnot : (⟨w, hwT⟩ : ↥mp.T) ∉ ((mp.certainTypeT hG).W2 : Set ↥mp.T) := by
    intro hmem
    apply hw1
    rw [tp.W1_eq_K hG]
    have hk := (certainTypeT_W2_eq hG mp) ▸ hmem
    exact Subgroup.mem_subgroupOf.mp hk
  have hv : (⟨w, hwT⟩ : ↥mp.T) ∈
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.V :=
    ⟨SetLike.mem_coe.mpr hjoin, hnot⟩
  have h43c := (mp.certainTypeT hG).certainType_apply_eq_of_mem_V
    (colT hG mp tp i) (rowT hG mp tp j) hv
  refine (show nuT hG mp tp i j ⟨w, hwT⟩ =
      (((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).mu
        (rowT hG mp tp j) : ClassFunction ↥mp.T ℂ) ⟨w, hwT⟩ from rfl).trans
    (h43c.trans ?_)
  rw [omegaS_eq_omegaT hG mp tp i j, omegaT, ClassFunction.compHom_apply]
  show (((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).sign : ℂ) * _
      = (deltaPrimeT hG mp tp i : ℂ) * _
  congr 1

/-- **Peterfalvi (4.3.d), T-side**: `ν_{ij}(1) ≡ δ'_i (mod p)`. -/
theorem nuT_degree_modEq_deltaPrime (i : Fin tp.q) (j : Fin tp.p) : ∃ a : ℤ,
    nuT hG mp tp i j 1 = (deltaPrimeT hG mp tp i : ℂ) + (tp.p : ℂ) * (a : ℂ) := by
  obtain ⟨a, ha⟩ := (mp.certainTypeT hG).certainType_degree_modEq
    (colT hG mp tp i) (rowT hG mp tp j)
  refine ⟨a, ?_⟩
  have hp : (tp.p : ℂ) = (Nat.card ↥(mp.certainTypeT hG).W1 : ℂ) := by
    rw [cardCertainTypeT_W1 hG mp tp]
  simp only [nuT, deltaPrimeT, hp]
  exact ha

/-- **Peterfalvi (4.4), T-side**: the base sign is `δ'_0 = 1`. -/
theorem deltaPrimeT_zero_eq_one :
    deltaPrimeT hG mp tp ⟨0, tp.q_prime.pos⟩ = 1 := by
  rw [deltaPrimeT, colT_zero hG mp tp]
  exact ((mp.certainTypeT hG).certainType_zero_column_anchor).1

/-- **Peterfalvi (4.5.a), T-side**: each canonical `ν`-row sum is induced from an
irreducible character of `T'`, and a non-anchor row is nontrivial on `tp.W1`. -/
theorem nuT_rowSum_eq_induce (i : Fin tp.q) :
    ∃ ψ : ClassFunction ↥((derivedInG mp.T).subgroupOf mp.T) ℂ,
      IsIrreducibleCharacter ψ ∧
      (∑ j : Fin tp.p, nuT hG mp tp i j) =
        ClassFunction.induce ((derivedInG mp.T).subgroupOf mp.T) ψ ∧
      (i ≠ ⟨0, tp.q_prime.pos⟩ →
        ¬ (((tp.W1.subgroupOf mp.T).subgroupOf
            ((derivedInG mp.T).subgroupOf mp.T) :
              Set ↥((derivedInG mp.T).subgroupOf mp.T)) ⊆
          Peterfalvi.S03.characterKernel ψ)) := by
  refine ⟨ClassFunction.restrict ((derivedInG mp.T).subgroupOf mp.T)
      (((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).mu 0 :
        ClassFunction ↥mp.T ℂ), ?_, ?_, ?_⟩
  · exact (mp.certainTypeT hG).certainTypeRestrict_isIrreducible _
  · calc
      (∑ j : Fin tp.p, nuT hG mp tp i j) =
          ∑ j' : Fin (Nat.card ↥(mp.certainTypeT hG).W1),
            (((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).mu j' :
              ClassFunction ↥mp.T ℂ) := by
        simp only [nuT]
        exact Equiv.sum_comp (rowTEquiv hG mp tp)
          (fun j' => (((mp.certainTypeT hG).columnFamily
            (colT hG mp tp i)).mu j' : ClassFunction ↥mp.T ℂ))
      _ = _ := ((mp.certainTypeT hG).induce_restrict_certainType_eq _).symm
  · intro hine hsub
    have hχ₂ne : colT hG mp tp i ≠ 1 := by
      rw [← colT_zero hG mp tp]
      exact fun h => hine (colT_injective hG mp tp h)
    refine (mp.certainTypeT hG).not_subset_characterKernel_chiRestrict_of_ne_one
      hχ₂ne ?_
    have hseq : ((tp.W1.subgroupOf mp.T).subgroupOf
          ((derivedInG mp.T).subgroupOf mp.T)) =
        (((mp.certainTypeT hG).W2).subgroupOf
          ((derivedInG mp.T).subgroupOf mp.T)) := by
      rw [certainTypeT_W2_eq hG mp, tp.W1_eq_K hG]
    exact hseq ▸ hsub

/-- The Dade-free Hypothesis (4.6) core on `mp.T`, reconciled with an arbitrary T-side
`TypePData`.  Its certain-type parent is exactly the canonical `nuT` producer. -/
noncomputable def hyp46TmpCore (Tdata : TypePData mp.T)
    (hW1 : Tdata.W1 = tp.W2) (hW2 : Tdata.W2 = tp.W1) :
    OddOrder.Peterfalvi.S06.Hypothesis46Core
      (OddOrder.Peterfalvi.S15.honestTypeP2ASet mp.T) mp.T :=
  { toHypothesis := mp.certainTypeT hG
    L_normalizes_A := fun l _ ha =>
      OddOrder.Peterfalvi.S15.honestTypeP2ASet_conj_mem l.2 ha
    tic := OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis Tdata hG.odd
    tic_W1 := by
      change Tdata.W1 = _
      rw [certainTypeT_W1_eq, Subgroup.map_subgroupOf_eq_of_le mp.Kstar_le_T,
        hW1, tp.W2_eq_Kstar hG]
    tic_W2 := by
      change Tdata.W2 = _
      rw [certainTypeT_W2_eq, Subgroup.map_subgroupOf_eq_of_le (k_le_T hG mp),
        hW2, tp.W1_eq_K hG]
    tic_V := rfl
    subH := (OddOrder.BG.Ch3.S10.Msigma mp.T).subgroupOf mp.T
    subH_normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    W2_le_subH := by
      rw [certainTypeT_W2_eq, ← tp.W1_eq_K hG, ← hW2]
      refine Subgroup.subgroupOf_mono mp.T ?_
      have hW2H : Tdata.W2 ≤ Tdata.H := le_trans Tdata.W2_le inf_le_left
      rw [Tdata.H_eq] at hW2H
      exact le_trans hW2H
        (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG mp.T_maximal)
    subH_le_K := by
      rw [certainTypeT_K_eq]
      exact Subgroup.subgroupOf_mono mp.T
        (OddOrder.BG.Ch3.S10.Msigma_le_derived hG mp.T_maximal)
    A_covers := by
      intro hh hhσ hh1 x hx hx1
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxC, hxD⟩ := hx
      rw [certainTypeT_K_eq, Subgroup.mem_subgroupOf] at hxD
      rw [Subgroup.mem_subgroupOf] at hhσ
      rw [Subgroup.mem_centralizer_iff] at hxC
      rw [OddOrder.Peterfalvi.S15.mem_honestTypeP2ASet]
      refine ⟨hxD, ?_, (hh : G), ⟨hhσ, ?_⟩, ?_⟩
      · simpa using hx1
      · simpa using hh1
      · rw [Subgroup.mem_centralizer_iff]
        rintro g rfl
        have hcomm := hxC (hh : ↥mp.T) rfl
        have := congrArg (mp.T.subtype) hcomm
        simpa using this }

/-- **Peterfalvi (4.8), conclusion (1), T-side** (Coq `prDade_sub_TIirr_on`): for
non-anchor equal-degree rows, `ν_{ij} - ν_{kj}` is supported in
`A₀(T) = A(T) ∪ (V_T)^T`. -/
theorem nuT_diff_support (Tdata : TypePData mp.T) (_hU : Tdata.U = tp.V)
    (hW1 : Tdata.W1 = tp.W2) (hW2 : Tdata.W2 = tp.W1)
    (j : Fin tp.p) {i k : Fin tp.q}
    (hi0 : i ≠ ⟨0, tp.q_prime.pos⟩) (hk0 : k ≠ ⟨0, tp.q_prime.pos⟩)
    (hdeg : nuT hG mp tp i j 1 = nuT hG mp tp k j 1) :
    (nuT hG mp tp i j - nuT hG mp tp k j).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S15.honestTypeP2A0Set mp.T Tdata) mp.T := by
  classical
  haveI : NeZero (Nat.card ↥(hyp46TmpCore hG mp tp Tdata hW1 hW2).W1) :=
    inferInstanceAs (NeZero (Nat.card ↥(mp.certainTypeT hG).W1))
  have hχi : colT hG mp tp i ≠ 1 := by
    intro hc
    exact hi0 (colT_injective hG mp tp (hc.trans (colT_zero hG mp tp).symm))
  have hχk : colT hG mp tp k ≠ 1 := by
    intro hc
    exact hk0 (colT_injective hG mp tp (hc.trans (colT_zero hG mp tp).symm))
  intro z hz
  rw [OddOrder.RepresentationTheory.ClassFunction.mem_support] at hz
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  exact OddOrder.Peterfalvi.S06.certainType_diff_supp_subset_A0
    (hyp46TmpCore hG mp tp Tdata hW1 hW2) hχi hχk (rowT hG mp tp j) hdeg hz

/-- **Peterfalvi (4.9.a), T-side**: complex conjugation pairs the canonical grid by
`ν̄_{ij} = ν_{-i,-j}`. -/
theorem nuT_conj (i : Fin tp.q) (j : Fin tp.p) :
    (nuT hG mp tp i j).conj
      = nuT hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
          (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j) := by
  have hg2 := congrArg
    (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥mp.T =>
      (χ : ClassFunction ↥mp.T ℂ))
    (OddOrder.Peterfalvi.S06.certainType_mu_conj_eq (mp.certainTypeT hG)
      (colT hG mp tp i) (rowT hG mp tp j))
  simp only [IrreducibleCharacter.galoisMap_apply_coe] at hg2
  rw [nuT, nuT, colT_finNeg hG mp tp i, rowT_finNeg_eq_rowInv hG mp tp j,
    ClassFunction.conj_eq_mapRingEquiv_conjAe]
  exact hg2

/-- **Peterfalvi (9.8)/(9.11), T-side reverse dichotomy**: every reducible member of a
kernel-filter family over `T'` is a non-anchor canonical `ν`-row sum. -/
theorem nuT_reducible_dichotomy {X : Subgroup ↥mp.T} {ψ : ClassFunction ↥mp.T ℂ}
    (hψ : ψ ∈ Peterfalvi.S08.inducedKernelFamily
      ((derivedInG mp.T).subgroupOf mp.T) X)
    (hred : ¬ IsIrreducibleCharacter ψ) :
    ∃ i : Fin tp.q, i ≠ ⟨0, tp.q_prime.pos⟩ ∧
      ψ = ∑ j : Fin tp.p, nuT hG mp tp i j := by
  classical
  haveI hcyc : IsCyclic ↥((mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2) :=
    (mp.certainTypeT hG).isCyclic_sup
  letI : CommGroup ↥((mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2) :=
    IsCyclic.commGroup
  letI : Fintype ↥mp.T := Fintype.ofFinite _
  letI : Fintype ↥(mp.certainTypeT hG).K := Fintype.ofFinite _
  letI : Fintype ↥((mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2) :=
    Fintype.ofFinite _
  obtain ⟨θ, hθne, hθker, rfl⟩ := hψ
  have hFk : ∀ i : Fin tp.q, (∑ j : Fin tp.p, nuT hG mp tp i j) =
      ClassFunction.induce (mp.certainTypeT hG).K
        (((mp.certainTypeT hG).chiRestrict (colTEquiv hG mp tp i) :
          ClassFunction ↥(mp.certainTypeT hG).K ℂ)) := by
    intro i
    rw [(mp.certainTypeT hG).coe_chiRestrict,
      (mp.certainTypeT hG).induce_restrict_certainType_eq]
    simp only [nuT]
    exact Equiv.sum_comp (rowTEquiv hG mp tp)
      (fun j' => (((mp.certainTypeT hG).columnFamily
        (colT hG mp tp i)).mu j' : ClassFunction ↥mp.T ℂ))
  obtain ⟨χ₂', hχ₂'⟩ :=
    ((mp.certainTypeT hG).induce_not_isIrreducible_iff θ).mp hred
  have hχ₂'ne : χ₂' ≠ 1 := by
    rintro rfl
    rw [(mp.certainTypeT hG).chiRestrict_one_eq_trivial] at hχ₂'
    exact hθne hχ₂'.symm
  refine ⟨(colTEquiv hG mp tp).symm χ₂', ?_, ?_⟩
  · intro h0
    apply hχ₂'ne
    calc
      χ₂' = colTEquiv hG mp tp ((colTEquiv hG mp tp).symm χ₂') :=
        (Equiv.apply_symm_apply _ _).symm
      _ = colTEquiv hG mp tp ⟨0, tp.q_prime.pos⟩ := by rw [h0]
      _ = 1 := colT_zero hG mp tp
  · rw [hFk, Equiv.apply_symm_apply, hχ₂']
    exact rfl

/-- **Peterfalvi (13.1.e), T-side**:
`Ind_W^T (ω_{ij} - ω_{i0}) = δ'_i (ν_{ij} - ν_{i0})`. -/
theorem nuT_definition (i : Fin tp.q) (j : Fin tp.p) :
    ClassFunction.induce (tp.W.subgroupOf mp.T)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq tp.W_eq_inter).trans inf_le_right)).toMonoidHom
          (omegaS hG mp tp i j - omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩))
      = (deltaPrimeT hG mp tp i : ℂ) •
          (nuT hG mp tp i j - nuT hG mp tp i ⟨0, tp.p_prime.pos⟩) := by
  have key : ∀ l : Fin tp.p,
      ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq tp.W_eq_inter).trans inf_le_right)).toMonoidHom
          (omegaS hG mp tp i l)
        = ClassFunction.compHom
            (MulEquiv.subgroupCongr (tpW_subgroupOf_T_eq hG mp tp)).toMonoidHom
            ((mp.certainTypeT hG).chiColumn (colT hG mp tp i) (rowT hG mp tp l) :
              ClassFunction ↥(mp.certainTypeT hG).sdiffTICyclicHypothesis.W ℂ) := by
    intro l
    rw [omegaS_eq_omegaT hG mp tp i l, omegaT, ClassFunction.compHom_comp]
    congr 1
  rw [ClassFunction.compHom_sub, key j, key ⟨0, tp.p_prime.pos⟩,
    ← ClassFunction.compHom_sub,
    rowT_zero hG mp tp,
    induce_compHom_subgroupCongr (tpW_subgroupOf_T_eq hG mp tp)]
  simp only [deltaPrimeT, nuT, rowT_zero hG mp tp, Int.cast_smul_eq_zsmul]
  exact (mp.certainTypeT hG).induce_chiColumn_diff_mu_diff
    (colT hG mp tp i) (rowT hG mp tp j)

end Section16CharacterData
end
end OddOrder
