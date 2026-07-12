import OddOrder.Peterfalvi.S16_NonExistenceG.TGapNonorthogonality

/-!
# Peterfalvi §11.8: T-side grid enumeration alignment

This leaf aligns the concrete S12 sigma-grid source characters with the
abstract S15 omega/eta grid.  It begins with the full character-grid
equivalence; the subsequent factorwise layer separates it into the transposed
zero-preserving row and column equivalences required by (11.8).
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- Transport a multiplicative character along equality of its subgroup
carrier. -/
noncomputable def monoidHomTransportSubgroupEq {H K : Subgroup G}
    (h : H = K) (χ : H →* ℂˣ) : K →* ℂˣ :=
  χ.comp (MulEquiv.subgroupCongr h.symm).toMonoidHom

/-- Transport does not change the value of the underlying ambient element. -/
theorem monoidHomTransportSubgroupEq_apply {H K : Subgroup G}
    (h : H = K) (χ : H →* ℂˣ) (x : K) :
    monoidHomTransportSubgroupEq h χ x =
      χ ⟨x, h.symm ▸ x.property⟩ := by
  rfl

/-- The abstract S15 omega-grid as an explicit equivalence with all complex
linear characters of `W`. -/
noncomputable def omegaMonoidHomEquiv [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    (Fin base.q × Fin base.p) ≃ (↥base.W →* ℂˣ) :=
  Equiv.ofBijective
    (fun ij => omegaMonoidHom base ij.1 ij.2)
    (omegaMonoidHom_bijective base)

@[simp] theorem omegaMonoidHomEquiv_apply [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (ij : Fin base.q × Fin base.p) :
    omegaMonoidHomEquiv base ij = omegaMonoidHom base ij.1 ij.2 := rfl

/-- The S12 aligned-grid source character, transported onto the shared S15
subgroup `W`. -/
noncomputable def alignedOmegaSourceCharacterOnBase [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W) (hodd : Odd (Nat.card G))
    (i : Fin s12.w1) (j : Fin s12.w2) : ↥base.W →* ℂˣ :=
  monoidHomTransportSubgroupEq hW
    (s12.alignedOmegaSourceCharacter hG hodd i j)

/-- The eta-grid pointer selected by the transported S12 source character. -/
noncomputable def alignedOmegaEtaIndex [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W) (hodd : Odd (Nat.card G))
    (i : Fin s12.w1) (j : Fin s12.w2) : Fin base.q × Fin base.p :=
  (omegaMonoidHomEquiv base).symm
    (alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i j)

/-- The omega character at `alignedOmegaEtaIndex` is exactly the transported
S12 source character. -/
theorem omegaMonoidHom_alignedOmegaEtaIndex [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W) (hodd : Odd (Nat.card G))
    (i : Fin s12.w1) (j : Fin s12.w2) :
    omegaMonoidHom base (alignedOmegaEtaIndex hG base s12 hW hodd i j).1
        (alignedOmegaEtaIndex hG base s12 hW hodd i j).2 =
      alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i j := by
  exact (omegaMonoidHomEquiv base).apply_symm_apply _

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The concrete S12 source-character grid is jointly injective.  This peels
off, in order, transport along the subgroup isomorphism, the product-character
equivalence, and the two normalized factor-character enumerations. -/
theorem alignedOmegaSourceCharacter_injective [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    Function.Injective (fun ij : Fin s12.w1 × Fin s12.w2 =>
      s12.alignedOmegaSourceCharacter hG hodd ij.1 ij.2) := by
  classical
  intro ⟨i, j⟩ ⟨i', j'⟩ hij
  let h := (s12.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) :=
    ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : s12.typeP.W1 ≤ M := s12.typeP.W1_le
  have hW2le : s12.typeP.W2 ≤ M :=
    OddOrder.Peterfalvi.S12.typePData_W2_le_self s12.typeP
  have hcardW1 : Nat.card ↥h.W1 = s12.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = s12.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) :=
    ⟨Nat.card_pos.ne'⟩
  let χ₂ : Fin s12.w2 → (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    fun k => OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup _
      (finCongr hcardW2sub.symm k)
  let tic := OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis
    s12.typeP hodd
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe
      (OddOrder.Peterfalvi.S12.typePData_W_le_self s12.typeP)).symm.trans
      (MulEquiv.subgroupCongr
        (OddOrder.Peterfalvi.S12.typePData_sup_subgroupOf_eq s12.typeP).symm)
  have hsource : ∀ a b, s12.alignedOmegaSourceCharacter hG hodd a b =
      (h.sdiffTICyclicHypothesis.omegaProdChar
        (h.w1CharEquiv (finCongr hcardW1.symm a)) (χ₂ b)).comp
          e.toMonoidHom := by
    intro a b
    unfold OddOrder.Peterfalvi.S12.Hypothesis.alignedOmegaSourceCharacter
    rfl
  change s12.alignedOmegaSourceCharacter hG hodd i j =
    s12.alignedOmegaSourceCharacter hG hodd i' j' at hij
  rw [hsource i j, hsource i' j'] at hij
  have hprod := (MonoidHom.cancel_right (MulEquiv.surjective e)).mp hij
  have hfactors := h.sdiffTICyclicHypothesis.omegaProdChar_inj hprod
  apply Prod.ext
  · exact (finCongr hcardW1.symm).injective
      (h.w1CharEquiv.injective hfactors.1)
  · exact (finCongr hcardW2sub.symm).injective
      ((OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup _).injective
        hfactors.2)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The aligned S12 source character separates as its column-zero character
times its row-zero character.  This is the honest factorization used to build
a coordinate-respecting eta reindex; it does not assume that the abstract S15
omega labels are already separable. -/
theorem alignedOmegaSourceCharacter_eq_mul_axes [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin s12.w1) (j : Fin s12.w2) :
    s12.alignedOmegaSourceCharacter hG hodd i j =
      s12.alignedOmegaSourceCharacter hG hodd i 0 *
        s12.alignedOmegaSourceCharacter hG hodd 0 j := by
  classical
  let h := (s12.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) :=
    ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : s12.typeP.W1 ≤ M := s12.typeP.W1_le
  have hW2le : s12.typeP.W2 ≤ M :=
    OddOrder.Peterfalvi.S12.typePData_W2_le_self s12.typeP
  have hcardW1 : Nat.card ↥h.W1 = s12.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = s12.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) :=
    ⟨Nat.card_pos.ne'⟩
  let χ₂ : Fin s12.w2 → (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    fun k => OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup _
      (finCongr hcardW2sub.symm k)
  let tic := OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis
    s12.typeP hodd
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe
      (OddOrder.Peterfalvi.S12.typePData_W_le_self s12.typeP)).symm.trans
      (MulEquiv.subgroupCongr
        (OddOrder.Peterfalvi.S12.typePData_sup_subgroupOf_eq s12.typeP).symm)
  have hsource : ∀ a b, s12.alignedOmegaSourceCharacter hG hodd a b =
      (h.sdiffTICyclicHypothesis.omegaProdChar
        (h.w1CharEquiv (finCongr hcardW1.symm a)) (χ₂ b)).comp
          e.toMonoidHom := by
    intro a b
    unfold OddOrder.Peterfalvi.S12.Hypothesis.alignedOmegaSourceCharacter
    rfl
  have hrow0 : h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin s12.w1)) = 1 := by
    rw [show finCongr hcardW1.symm (0 : Fin s12.w1) = 0 from by ext; simp,
      h.w1CharEquiv_zero]
  have hcol0 : χ₂ 0 = 1 := by
    change OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup _
      (finCongr hcardW2sub.symm (0 : Fin s12.w2)) = 1
    rw [show finCongr hcardW2sub.symm (0 : Fin s12.w2) = 0 from by ext; simp,
      OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup_zero]
  rw [hsource i j, hsource i 0, hsource 0 j]
  rw [hrow0, hcol0]
  have hp := h.sdiffTICyclicHypothesis.omegaProdChar_mul
    (h.w1CharEquiv (finCongr hcardW1.symm i)) 1 1 (χ₂ j)
  simp only [mul_one, one_mul] at hp
  rw [hp]
  rfl

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The source row-zero character is trivial on the first type-P factor.
After reconciliation this factor is the target `W₂`. -/
theorem alignedOmegaSourceCharacter_zero_row_apply_of_mem_W1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis M)
    (hodd : Odd (Nat.card G)) (j : Fin s12.w2)
    (x : ↥(OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis
      s12.typeP hodd).W)
    (hx : (x : G) ∈ s12.typeP.W1) :
    s12.alignedOmegaSourceCharacter hG hodd 0 j x = 1 := by
  classical
  let h := (s12.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) :=
    ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : s12.typeP.W1 ≤ M := s12.typeP.W1_le
  have hW2le : s12.typeP.W2 ≤ M :=
    OddOrder.Peterfalvi.S12.typePData_W2_le_self s12.typeP
  have hcardW1 : Nat.card ↥h.W1 = s12.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = s12.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) :=
    ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup _
      (finCongr hcardW2sub.symm j)
  let tic := OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis
    s12.typeP hodd
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe
      (OddOrder.Peterfalvi.S12.typePData_W_le_self s12.typeP)).symm.trans
      (MulEquiv.subgroupCongr
        (OddOrder.Peterfalvi.S12.typePData_sup_subgroupOf_eq s12.typeP).symm)
  have hsource : s12.alignedOmegaSourceCharacter hG hodd 0 j =
      (h.sdiffTICyclicHypothesis.omegaProdChar
        (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin s12.w1))) χ₂).comp
          e.toMonoidHom := by
    unfold OddOrder.Peterfalvi.S12.Hypothesis.alignedOmegaSourceCharacter
    rfl
  have hrow0 : h.w1CharEquiv
      (finCongr hcardW1.symm (0 : Fin s12.w1)) = 1 := by
    rw [show finCongr hcardW1.symm (0 : Fin s12.w1) = 0 from by ext; simp,
      h.w1CharEquiv_zero]
  rw [hsource, MonoidHom.comp_apply]
  apply Units.ext
  change (h.chiColumn χ₂
    (finCongr hcardW1.symm (0 : Fin s12.w1)) :
      ClassFunction h.sdiffTICyclicHypothesis.W ℂ) (e.toMonoidHom x) = 1
  have hex : e.toMonoidHom x ∈ h.sdiffTICyclicHypothesis.W1.subgroupOf
      h.sdiffTICyclicHypothesis.W := by
    apply Subgroup.mem_subgroupOf.mpr
    change (x : G) ∈ s12.typeP.W1
    exact hx
  have hsnd : h.sdiffTICyclicHypothesis.wSnd (e.toMonoidHom x) =
      (1 : h.W2.subgroupOf (h.W1 ⊔ h.W2)) :=
    h.sdiffTICyclicHypothesis.wSnd_eq_one_of_mem_W1 hex
  have hchi : χ₂ (h.sdiffTICyclicHypothesis.wSnd (e.toMonoidHom x)) = 1 := by
    rw [hsnd, map_one]
  rw [OddOrder.Peterfalvi.S06.Hypothesis.chiColumn,
    h.sdiffTICyclicHypothesis.omega_apply]
  change (((h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin s12.w1)))
      (h.sdiffTICyclicHypothesis.wFst (e.toMonoidHom x)) *
      χ₂ (h.sdiffTICyclicHypothesis.wSnd (e.toMonoidHom x)) : ℂˣ) : ℂ) = 1
  rw [Units.val_mul, hrow0, MonoidHom.one_apply, Units.val_one,
    hchi, Units.val_one, one_mul]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The source column-zero character is trivial on the second type-P factor.
After reconciliation this factor is the target `W₁`. -/
theorem alignedOmegaSourceCharacter_zero_column_apply_of_mem_W2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin s12.w1)
    (x : ↥(OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis
      s12.typeP hodd).W)
    (hx : (x : G) ∈ s12.typeP.W2) :
    s12.alignedOmegaSourceCharacter hG hodd i 0 x = 1 := by
  classical
  let h := (s12.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) :=
    ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : s12.typeP.W1 ≤ M := s12.typeP.W1_le
  have hW2le : s12.typeP.W2 ≤ M :=
    OddOrder.Peterfalvi.S12.typePData_W2_le_self s12.typeP
  have hcardW1 : Nat.card ↥h.W1 = s12.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = s12.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) :=
    ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup _
      (finCongr hcardW2sub.symm (0 : Fin s12.w2))
  let tic := OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis
    s12.typeP hodd
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe
      (OddOrder.Peterfalvi.S12.typePData_W_le_self s12.typeP)).symm.trans
      (MulEquiv.subgroupCongr
        (OddOrder.Peterfalvi.S12.typePData_sup_subgroupOf_eq s12.typeP).symm)
  have hsource : s12.alignedOmegaSourceCharacter hG hodd i 0 =
      (h.sdiffTICyclicHypothesis.omegaProdChar
        (h.w1CharEquiv (finCongr hcardW1.symm i)) χ₂).comp e.toMonoidHom := by
    unfold OddOrder.Peterfalvi.S12.Hypothesis.alignedOmegaSourceCharacter
    rfl
  have hcol0 : χ₂ = 1 := by
    change OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup _
      (finCongr hcardW2sub.symm (0 : Fin s12.w2)) = 1
    rw [show finCongr hcardW2sub.symm (0 : Fin s12.w2) = 0 from by ext; simp,
      OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup_zero]
  rw [hsource, MonoidHom.comp_apply]
  apply Units.ext
  change (h.chiColumn χ₂ (finCongr hcardW1.symm i) :
    ClassFunction h.sdiffTICyclicHypothesis.W ℂ) (e.toMonoidHom x) = 1
  have hex : e.toMonoidHom x ∈ h.sdiffTICyclicHypothesis.W2.subgroupOf
      h.sdiffTICyclicHypothesis.W := by
    apply Subgroup.mem_subgroupOf.mpr
    change (x : G) ∈ s12.typeP.W2
    exact hx
  have hfst : h.sdiffTICyclicHypothesis.wFst (e.toMonoidHom x) =
      (1 : h.W1.subgroupOf (h.W1 ⊔ h.W2)) :=
    h.sdiffTICyclicHypothesis.wFst_eq_one_of_mem_W2 hex
  have hfirst : h.w1CharEquiv (finCongr hcardW1.symm i)
      (h.sdiffTICyclicHypothesis.wFst (e.toMonoidHom x)) = 1 := by
    rw [hfst, map_one]
  have hsecond : χ₂
      (h.sdiffTICyclicHypothesis.wSnd (e.toMonoidHom x)) = 1 := by
    rw [hcol0, MonoidHom.one_apply]
  rw [OddOrder.Peterfalvi.S06.Hypothesis.chiColumn,
    h.sdiffTICyclicHypothesis.omega_apply]
  change (((h.w1CharEquiv (finCongr hcardW1.symm i))
      (h.sdiffTICyclicHypothesis.wFst (e.toMonoidHom x)) *
      χ₂ (h.sdiffTICyclicHypothesis.wSnd (e.toMonoidHom x)) : ℂˣ) : ℂ) = 1
  rw [Units.val_mul, hfirst, Units.val_one, hsecond, Units.val_one, one_mul]

/-- Restriction of the transported source row-zero axis to the target `W₁`.
Under the reconciled T-side factor swap, this is the source `W₂` axis. -/
noncomputable def alignedOmegaSourceW1Restriction [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W) (hodd : Odd (Nat.card G))
    (j : Fin s12.w2) : ↥(base.W1.subgroupOf base.W) →* ℂˣ :=
  (alignedOmegaSourceCharacterOnBase hG base s12 hW hodd 0 j).comp
    (base.W1.subgroupOf base.W).subtype

/-- Restriction of the transported source column-zero axis to target `W₂`.
Under the reconciled T-side factor swap, this is the source `W₁` axis. -/
noncomputable def alignedOmegaSourceW2Restriction [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W) (hodd : Odd (Nat.card G))
    (i : Fin s12.w1) : ↥(base.W2.subgroupOf base.W) →* ℂˣ :=
  (alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i 0).comp
    (base.W2.subgroupOf base.W).subtype

/-- The target `W₁` zero-column label selected by a source `W₂`-axis
character. -/
noncomputable def alignedOmegaColumnIndex [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W) (hodd : Odd (Nat.card G))
    (j : Fin s12.w2) : Fin base.q :=
  (omegaW1RestrictionEquiv base).symm
    (alignedOmegaSourceW1Restriction hG base s12 hW hodd j)

/-- The target `W₂` zero-row label selected by a source `W₁`-axis
character. -/
noncomputable def alignedOmegaRowIndex [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W) (hodd : Odd (Nat.card G))
    (i : Fin s12.w1) : Fin base.p :=
  (omegaW2RestrictionEquiv base).symm
    (alignedOmegaSourceW2Restriction hG base s12 hW hodd i)

/-- The target column-zero omega character selected from the source `W₂`
axis equals that transported source character on all of `W`. -/
theorem omegaMonoidHom_alignedOmegaColumnIndex [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (_hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) (j : Fin s12.w2) :
    omegaMonoidHom base
        (alignedOmegaColumnIndex hG base s12 hW hodd j)
        ⟨0, base.p_prime.pos⟩ =
      alignedOmegaSourceCharacterOnBase hG base s12 hW hodd 0 j := by
  apply monoidHom_eq_of_eq_on_W1_W2 base
  · intro x
    have hx := DFunLike.congr_fun
      ((omegaW1RestrictionEquiv base).apply_symm_apply
        (alignedOmegaSourceW1Restriction hG base s12 hW hodd j)) x
    exact hx
  · intro y
    have htarget : omegaMonoidHom base
        (alignedOmegaColumnIndex hG base s12 hW hodd j)
        ⟨0, base.p_prime.pos⟩ y = 1 := by
      apply Units.ext
      change base.omega (alignedOmegaColumnIndex hG base s12 hW hodd j)
        ⟨0, base.p_prime.pos⟩ y = 1
      exact base.omega_col_zero_apply_of_mem_W2 _ y
        (Subgroup.mem_subgroupOf.mp y.property)
    have hsource : alignedOmegaSourceCharacterOnBase
        hG base s12 hW hodd 0 j y = 1 := by
      rw [alignedOmegaSourceCharacterOnBase,
        monoidHomTransportSubgroupEq_apply]
      apply alignedOmegaSourceCharacter_zero_row_apply_of_mem_W1
      exact hW2.symm ▸ Subgroup.mem_subgroupOf.mp y.property
    exact htarget.trans hsource.symm

/-- The target row-zero omega character selected from the source `W₁` axis
equals that transported source character on all of `W`. -/
theorem omegaMonoidHom_alignedOmegaRowIndex [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (_hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) (i : Fin s12.w1) :
    omegaMonoidHom base ⟨0, base.q_prime.pos⟩
        (alignedOmegaRowIndex hG base s12 hW hodd i) =
      alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i 0 := by
  apply monoidHom_eq_of_eq_on_W1_W2 base
  · intro x
    have htarget : omegaMonoidHom base ⟨0, base.q_prime.pos⟩
        (alignedOmegaRowIndex hG base s12 hW hodd i) x = 1 := by
      apply Units.ext
      change base.omega ⟨0, base.q_prime.pos⟩
        (alignedOmegaRowIndex hG base s12 hW hodd i) x = 1
      exact base.omega_row_zero_apply_of_mem_W1 _ x
        (Subgroup.mem_subgroupOf.mp x.property)
    have hsource : alignedOmegaSourceCharacterOnBase
        hG base s12 hW hodd i 0 x = 1 := by
      rw [alignedOmegaSourceCharacterOnBase,
        monoidHomTransportSubgroupEq_apply]
      apply alignedOmegaSourceCharacter_zero_column_apply_of_mem_W2
      exact hW1.symm ▸ Subgroup.mem_subgroupOf.mp x.property
    exact htarget.trans hsource.symm
  · intro y
    have hy := DFunLike.congr_fun
      ((omegaW2RestrictionEquiv base).apply_symm_apply
        (alignedOmegaSourceW2Restriction hG base s12 hW hodd i)) y
    exact hy

/-- The transported source character at `(0,0)` is the trivial character.
The proof uses the two reconciled factors rather than any global uniqueness
claim for the sigma map. -/
theorem alignedOmegaSourceCharacterOnBase_zero_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) :
    alignedOmegaSourceCharacterOnBase hG base s12 hW hodd 0 0 = 1 := by
  apply monoidHom_eq_of_eq_on_W1_W2 base
  · intro x
    rw [alignedOmegaSourceCharacterOnBase,
      monoidHomTransportSubgroupEq_apply, MonoidHom.one_apply]
    apply alignedOmegaSourceCharacter_zero_column_apply_of_mem_W2
    exact hW1.symm ▸ Subgroup.mem_subgroupOf.mp x.property
  · intro y
    rw [alignedOmegaSourceCharacterOnBase,
      monoidHomTransportSubgroupEq_apply, MonoidHom.one_apply]
    apply alignedOmegaSourceCharacter_zero_row_apply_of_mem_W1
    exact hW2.symm ▸ Subgroup.mem_subgroupOf.mp y.property

/-- The transposed source-column index preserves the distinguished zero. -/
theorem alignedOmegaColumnIndex_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) :
    alignedOmegaColumnIndex hG base s12 hW hodd 0 =
      ⟨0, base.q_prime.pos⟩ := by
  rw [alignedOmegaColumnIndex,
    show alignedOmegaSourceW1Restriction hG base s12 hW hodd 0 = 1 by
      unfold alignedOmegaSourceW1Restriction
      rw [alignedOmegaSourceCharacterOnBase_zero_zero
        hG base s12 hW hW1 hW2 hodd, MonoidHom.one_comp]]
  exact omegaW1RestrictionEquiv_symm_one base

/-- The transposed source-row index preserves the distinguished zero. -/
theorem alignedOmegaRowIndex_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) :
    alignedOmegaRowIndex hG base s12 hW hodd 0 =
      ⟨0, base.p_prime.pos⟩ := by
  rw [alignedOmegaRowIndex,
    show alignedOmegaSourceW2Restriction hG base s12 hW hodd 0 = 1 by
      unfold alignedOmegaSourceW2Restriction
      rw [alignedOmegaSourceCharacterOnBase_zero_zero
        hG base s12 hW hW1 hW2 hodd, MonoidHom.one_comp]]
  exact omegaW2RestrictionEquiv_symm_one base

set_option maxHeartbeats 1000000 in
-- The concrete source-grid injectivity proof has a large reducible subgroup term.
/-- The source `W₂` labels inject into the target `W₁` zero-column labels. -/
theorem alignedOmegaColumnIndex_injective [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) :
    Function.Injective (alignedOmegaColumnIndex hG base s12 hW hodd) := by
  intro j k hjk
  have hchars : alignedOmegaSourceCharacterOnBase
      hG base s12 hW hodd 0 j =
      alignedOmegaSourceCharacterOnBase hG base s12 hW hodd 0 k := by
    rw [← omegaMonoidHom_alignedOmegaColumnIndex
        hG base s12 hW hW1 hW2 hodd j,
      ← omegaMonoidHom_alignedOmegaColumnIndex
        hG base s12 hW hW1 hW2 hodd k, hjk]
  have hsource : s12.alignedOmegaSourceCharacter hG hodd 0 j =
      s12.alignedOmegaSourceCharacter hG hodd 0 k := by
    exact (MonoidHom.cancel_right
      (MulEquiv.surjective (MulEquiv.subgroupCongr hW.symm))).mp hchars
  have hp : ((0, j) : Fin s12.w1 × Fin s12.w2) = (0, k) :=
    alignedOmegaSourceCharacter_injective hG s12 hodd hsource
  exact congrArg Prod.snd hp

set_option maxHeartbeats 1000000 in
-- The concrete source-grid injectivity proof has a large reducible subgroup term.
/-- The source `W₁` labels inject into the target `W₂` zero-row labels. -/
theorem alignedOmegaRowIndex_injective [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) :
    Function.Injective (alignedOmegaRowIndex hG base s12 hW hodd) := by
  intro i k hik
  have hchars : alignedOmegaSourceCharacterOnBase
      hG base s12 hW hodd i 0 =
      alignedOmegaSourceCharacterOnBase hG base s12 hW hodd k 0 := by
    rw [← omegaMonoidHom_alignedOmegaRowIndex
        hG base s12 hW hW1 hW2 hodd i,
      ← omegaMonoidHom_alignedOmegaRowIndex
        hG base s12 hW hW1 hW2 hodd k, hik]
  have hsource : s12.alignedOmegaSourceCharacter hG hodd i 0 =
      s12.alignedOmegaSourceCharacter hG hodd k 0 := by
    exact (MonoidHom.cancel_right
      (MulEquiv.surjective (MulEquiv.subgroupCongr hW.symm))).mp hchars
  have hp : ((i, 0) : Fin s12.w1 × Fin s12.w2) = (k, 0) :=
    alignedOmegaSourceCharacter_injective hG s12 hodd hsource
  exact congrArg Prod.fst hp

/-- The transposed source-column label map is bijective. -/
theorem alignedOmegaColumnIndex_bijective [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) :
    Function.Bijective (alignedOmegaColumnIndex hG base s12 hW hodd) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨alignedOmegaColumnIndex_injective
    hG base s12 hW hW1 hW2 hodd, ?_⟩
  simp only [Fintype.card_fin]
  rw [show s12.w2 = Nat.card ↥s12.typeP.W2 from rfl, hW1,
    ← base.q_eq_card_W1]

/-- The transposed source-row label map is bijective. -/
theorem alignedOmegaRowIndex_bijective [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) :
    Function.Bijective (alignedOmegaRowIndex hG base s12 hW hodd) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨alignedOmegaRowIndex_injective
    hG base s12 hW hW1 hW2 hodd, ?_⟩
  simp only [Fintype.card_fin]
  rw [show s12.w1 = Nat.card ↥s12.typeP.W1 from rfl, hW2,
    ← base.p_eq_card_W2]

/-- Zero-preserving transposed enumeration of the source `W₂` axis by the
target `W₁` axis. -/
noncomputable def alignedOmegaColumnEquiv [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) : Fin s12.w2 ≃ Fin base.q :=
  Equiv.ofBijective (alignedOmegaColumnIndex hG base s12 hW hodd)
    (alignedOmegaColumnIndex_bijective hG base s12 hW hW1 hW2 hodd)

/-- Zero-preserving transposed enumeration of the source `W₁` axis by the
target `W₂` axis. -/
noncomputable def alignedOmegaRowEquiv [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) : Fin s12.w1 ≃ Fin base.p :=
  Equiv.ofBijective (alignedOmegaRowIndex hG base s12 hW hodd)
    (alignedOmegaRowIndex_bijective hG base s12 hW hW1 hW2 hodd)

@[simp] theorem alignedOmegaColumnEquiv_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) :
    alignedOmegaColumnEquiv hG base s12 hW hW1 hW2 hodd 0 =
      ⟨0, base.q_prime.pos⟩ :=
  alignedOmegaColumnIndex_zero hG base s12 hW hW1 hW2 hodd

@[simp] theorem alignedOmegaRowEquiv_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) :
    alignedOmegaRowEquiv hG base s12 hW hW1 hW2 hodd 0 =
      ⟨0, base.p_prime.pos⟩ :=
  alignedOmegaRowIndex_zero hG base s12 hW hW1 hW2 hodd

/-- Transporting the honest source factorization to the common subgroup
preserves its product form. -/
theorem alignedOmegaSourceCharacterOnBase_eq_mul_axes [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W) (hodd : Odd (Nat.card G))
    (i : Fin s12.w1) (j : Fin s12.w2) :
    alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i j =
      alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i 0 *
        alignedOmegaSourceCharacterOnBase hG base s12 hW hodd 0 j := by
  apply MonoidHom.ext
  intro x
  change s12.alignedOmegaSourceCharacter hG hodd i j _ =
    s12.alignedOmegaSourceCharacter hG hodd i 0 _ *
      s12.alignedOmegaSourceCharacter hG hodd 0 j _
  exact DFunLike.congr_fun
    (alignedOmegaSourceCharacter_eq_mul_axes hG s12 hodd i j) _

/-- Coordinate-respecting full omega label: map the two source axes to the
transposed target zero axes, multiply those target characters, and only then
use the full omega exhaustion.  No separability of the pre-existing abstract
omega labels is assumed. -/
noncomputable def alignedOmegaProductIndex [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G))
    (i : Fin s12.w1) (j : Fin s12.w2) : Fin base.q × Fin base.p :=
  (omegaMonoidHomEquiv base).symm
    (omegaMonoidHom base
        (alignedOmegaColumnEquiv hG base s12 hW hW1 hW2 hodd j)
        ⟨0, base.p_prime.pos⟩ *
      omegaMonoidHom base ⟨0, base.q_prime.pos⟩
        (alignedOmegaRowEquiv hG base s12 hW hW1 hW2 hodd i))

/-- The character at the product-selected label is precisely the transported
source grid character. -/
theorem omegaMonoidHom_alignedOmegaProductIndex [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G))
    (i : Fin s12.w1) (j : Fin s12.w2) :
    omegaMonoidHom base
        (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j).1
        (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j).2 =
      alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i j := by
  rw [show omegaMonoidHom base
      (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j).1
      (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j).2 =
        omegaMonoidHomEquiv base
          (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j) from rfl,
    alignedOmegaProductIndex, Equiv.apply_symm_apply]
  change omegaMonoidHom base
      (alignedOmegaColumnIndex hG base s12 hW hodd j)
      ⟨0, base.p_prime.pos⟩ *
    omegaMonoidHom base ⟨0, base.q_prime.pos⟩
      (alignedOmegaRowIndex hG base s12 hW hodd i) =
    alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i j
  rw [
    omegaMonoidHom_alignedOmegaColumnIndex hG base s12 hW hW1 hW2 hodd j,
    omegaMonoidHom_alignedOmegaRowIndex hG base s12 hW hW1 hW2 hodd i,
    mul_comm]
  exact (alignedOmegaSourceCharacterOnBase_eq_mul_axes
    hG base s12 hW hodd i j).symm

/-- The factorwise product construction selects the same full omega entry as
the direct source-character pointer. -/
theorem alignedOmegaProductIndex_eq_alignedOmegaEtaIndex [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G))
    (i : Fin s12.w1) (j : Fin s12.w2) :
    alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j =
      alignedOmegaEtaIndex hG base s12 hW hodd i j := by
  apply (omegaMonoidHomEquiv base).injective
  rw [omegaMonoidHomEquiv_apply, omegaMonoidHomEquiv_apply,
    omegaMonoidHom_alignedOmegaProductIndex,
    omegaMonoidHom_alignedOmegaEtaIndex]

/-- On the source zero column, the product-selected label is exactly the
target zero-row axis label. -/
theorem alignedOmegaProductIndex_zero_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) (i : Fin s12.w1) :
    alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i 0 =
      (⟨0, base.q_prime.pos⟩,
        alignedOmegaRowEquiv hG base s12 hW hW1 hW2 hodd i) := by
  apply (omegaMonoidHomEquiv base).injective
  rw [omegaMonoidHomEquiv_apply,
    omegaMonoidHom_alignedOmegaProductIndex,
    omegaMonoidHomEquiv_apply]
  change alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i 0 =
    omegaMonoidHom base ⟨0, base.q_prime.pos⟩
      (alignedOmegaRowIndex hG base s12 hW hodd i)
  exact (omegaMonoidHom_alignedOmegaRowIndex
    hG base s12 hW hW1 hW2 hodd i).symm

/-- On the source zero row, the product-selected label is exactly the target
zero-column axis label. -/
theorem alignedOmegaProductIndex_zero_row [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) (j : Fin s12.w2) :
    alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd 0 j =
      (alignedOmegaColumnEquiv hG base s12 hW hW1 hW2 hodd j,
        ⟨0, base.p_prime.pos⟩) := by
  apply (omegaMonoidHomEquiv base).injective
  rw [omegaMonoidHomEquiv_apply,
    omegaMonoidHom_alignedOmegaProductIndex,
    omegaMonoidHomEquiv_apply]
  change alignedOmegaSourceCharacterOnBase hG base s12 hW hodd 0 j =
    omegaMonoidHom base (alignedOmegaColumnIndex hG base s12 hW hodd j)
      ⟨0, base.p_prime.pos⟩
  exact (omegaMonoidHom_alignedOmegaColumnIndex
    hG base s12 hW hW1 hW2 hodd j).symm

/-- The coordinate-respecting eta grid obtained from the factorwise product
pointer. -/
noncomputable def alignedOmegaEtaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G))
    (i : Fin s12.w1) (j : Fin s12.w2) : ClassFunction G ℂ :=
  base.eta
    (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j).1
    (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j).2

/-- The source zero column is the target eta zero row, with the transposed
row equivalence. -/
theorem alignedOmegaEtaGrid_zero_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) (i : Fin s12.w1) :
    alignedOmegaEtaGrid hG base s12 hW hW1 hW2 hodd i 0 =
      base.eta ⟨0, base.q_prime.pos⟩
        (alignedOmegaRowEquiv hG base s12 hW hW1 hW2 hodd i) := by
  rw [alignedOmegaEtaGrid, alignedOmegaProductIndex_zero_column]

/-- The source zero row is the target eta zero column, with the transposed
column equivalence. -/
theorem alignedOmegaEtaGrid_zero_row [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) (j : Fin s12.w2) :
    alignedOmegaEtaGrid hG base s12 hW hW1 hW2 hodd 0 j =
      base.eta (alignedOmegaColumnEquiv hG base s12 hW hW1 hW2 hodd j)
        ⟨0, base.p_prime.pos⟩ := by
  rw [alignedOmegaEtaGrid, alignedOmegaProductIndex_zero_row]

/-- Reindexing the transported S12 source grid through the full omega-grid
equivalence remains jointly injective. -/
theorem alignedOmegaEtaIndex_injective [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W) (hodd : Odd (Nat.card G)) :
    Function.Injective (fun ij : Fin s12.w1 × Fin s12.w2 =>
      alignedOmegaEtaIndex hG base s12 hW hodd ij.1 ij.2) := by
  intro a b hab
  have htransport : alignedOmegaSourceCharacterOnBase
      hG base s12 hW hodd a.1 a.2 =
      alignedOmegaSourceCharacterOnBase hG base s12 hW hodd b.1 b.2 :=
    (omegaMonoidHomEquiv base).symm.injective hab
  have hsource : s12.alignedOmegaSourceCharacter hG hodd a.1 a.2 =
      s12.alignedOmegaSourceCharacter hG hodd b.1 b.2 := by
    exact (MonoidHom.cancel_right
      (MulEquiv.surjective (MulEquiv.subgroupCongr hW.symm))).mp htransport
  exact alignedOmegaSourceCharacter_injective hG s12 hodd hsource

/-- The factorwise product pointer is jointly injective. -/
theorem alignedOmegaProductIndex_injective [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) :
    Function.Injective (fun ij : Fin s12.w1 × Fin s12.w2 =>
      alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd ij.1 ij.2) := by
  intro ⟨i, j⟩ ⟨k, l⟩ hij
  change alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j =
    alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd k l at hij
  rw [alignedOmegaProductIndex_eq_alignedOmegaEtaIndex
      hG base s12 hW hW1 hW2 hodd i j,
    alignedOmegaProductIndex_eq_alignedOmegaEtaIndex
      hG base s12 hW hW1 hW2 hodd k l] at hij
  exact alignedOmegaEtaIndex_injective hG base s12 hW hodd hij

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The coordinate-respecting eta grid is orthonormal in its source
coordinates. -/
theorem alignedOmegaEtaGrid_orthonormal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G))
    (i k : Fin s12.w1) (j l : Fin s12.w2) :
    ClassFunction.inner
        (alignedOmegaEtaGrid hG base s12 hW hW1 hW2 hodd i j)
        (alignedOmegaEtaGrid hG base s12 hW hW1 hW2 hodd k l) =
      if i = k ∧ j = l then 1 else 0 := by
  rw [alignedOmegaEtaGrid, alignedOmegaEtaGrid, eta_orthonormal]
  by_cases h : i = k ∧ j = l
  · rcases h with ⟨rfl, rfl⟩
    simp
  · have hindex : ¬ (
        (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j).1 =
            (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd k l).1 ∧
          (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j).2 =
            (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd k l).2) := by
      intro hp
      apply h
      have hpairs : alignedOmegaProductIndex
          hG base s12 hW hW1 hW2 hodd i j =
          alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd k l :=
        Prod.ext hp.1 hp.2
      have hs : ((i, j) : Fin s12.w1 × Fin s12.w2) = (k, l) :=
        alignedOmegaProductIndex_injective
          hG base s12 hW hW1 hW2 hodd hpairs
      exact ⟨congrArg Prod.fst hs, congrArg Prod.snd hs⟩
    rw [if_neg hindex, if_neg h]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The concrete S12 sigma-grid and the abstract S15 eta-grid agree on the
shared regular set after reindexing by `alignedOmegaEtaIndex`.  Both sides
restore the same transported multiplicative character there. -/
theorem alignedOmegaSigmaGrid_apply_eq_eta_alignedIndex [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W) (hodd : Odd (Nat.card G))
    (hV : typePV base.T s12.typeP =
      (base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G)))
    (i : Fin s12.w1) (j : Fin s12.w2) {v : G}
    (hv : v ∈ typePV base.T s12.typeP) :
    s12.alignedOmegaSigmaGrid hG hodd i j v =
      base.eta (alignedOmegaEtaIndex hG base s12 hW hodd i j).1
        (alignedOmegaEtaIndex hG base s12 hW hodd i j).2 v := by
  have hvreg := hv
  rw [hV] at hvreg
  have hvW : v ∈ base.W := hvreg.1
  have hvnot : v ∉ (base.W1 : Set G) ∪ (base.W2 : Set G) := hvreg.2
  rw [s12.alignedOmegaSigmaGrid_apply_eq_sourceCharacter hG hodd i j hv,
    base.eta_eq_tau_omega,
    base.tau3_apply_of_regular _ v hvW hvnot]
  have hchars := omegaMonoidHom_alignedOmegaEtaIndex
    hG base s12 hW hodd i j
  have hval := DFunLike.congr_fun hchars (⟨v, hvW⟩ : ↥base.W)
  have hvalC := congrArg (fun z : ℂˣ => (z : ℂ)) hval
  rw [omegaMonoidHom_coe, alignedOmegaSourceCharacterOnBase,
    monoidHomTransportSubgroupEq_apply] at hvalC
  calc
    ((s12.alignedOmegaSourceCharacter hG hodd i j
        ⟨v, hv.1⟩ : ℂˣ) : ℂ) =
        ((s12.alignedOmegaSourceCharacter hG hodd i j
          (MulEquiv.subgroupCongr hW.symm ⟨v, hvW⟩) : ℂˣ) : ℂ) := by
            congr 2
    _ = base.omega (alignedOmegaEtaIndex hG base s12 hW hodd i j).1
          (alignedOmegaEtaIndex hG base s12 hW hodd i j).2
          ⟨v, hvW⟩ := hvalC.symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The concrete S12 sigma grid agrees on the regular set with the
coordinate-respecting, zero-axis-preserving eta grid. -/
theorem alignedOmegaSigmaGrid_apply_eq_alignedOmegaEtaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G))
    (hV : typePV base.T s12.typeP =
      (base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G)))
    (i : Fin s12.w1) (j : Fin s12.w2) {v : G}
    (hv : v ∈ typePV base.T s12.typeP) :
    s12.alignedOmegaSigmaGrid hG hodd i j v =
      alignedOmegaEtaGrid hG base s12 hW hW1 hW2 hodd i j v := by
  rw [alignedOmegaEtaGrid,
    alignedOmegaProductIndex_eq_alignedOmegaEtaIndex]
  exact alignedOmegaSigmaGrid_apply_eq_eta_alignedIndex
    hG base s12 hW hodd hV i j hv

end OddOrder.Peterfalvi.S16
