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
  let row : (h.sdiffTICyclicHypothesis.W1.subgroupOf
      h.sdiffTICyclicHypothesis.W) →* ℂˣ :=
    h.w1CharEquiv (finCongr hcardW1.symm i)
  let col : (h.sdiffTICyclicHypothesis.W2.subgroupOf
      h.sdiffTICyclicHypothesis.W) →* ℂˣ := χ₂ j
  have hp := h.sdiffTICyclicHypothesis.omegaProdChar_mul row 1 1 col
  have hrowmul : row * 1 = row := mul_one row
  have hcolmul : 1 * col = col := one_mul col
  rw [hrowmul, hcolmul] at hp
  have hpcomp := congrArg
    (fun f : h.sdiffTICyclicHypothesis.W →* ℂˣ => f.comp e.toMonoidHom) hp
  rw [MonoidHom.mul_comp] at hpcomp
  exact hpcomp

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
    omegaMonoidHom_alignedOmegaRowIndex hG base s12 hW hW1 hW2 hodd i]
  exact (@mul_comm (↥base.W →* ℂˣ) _
      (alignedOmegaSourceCharacterOnBase hG base s12 hW hodd 0 j)
      (alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i 0)).trans
    (alignedOmegaSourceCharacterOnBase_eq_mul_axes
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

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.8), eta pair-difference rigidity.**
A norm-two virtual character agreeing with `s • (η_{P₁} − η_{P₂})` for two
*arbitrary distinct* grid labels on the conjugacy saturation of the shared
regular set equals that difference globally.  The abstract engine
`S05.orthonormalGrid_diff_rigidity` already permits arbitrary distinct grid
points; this removes the same-row/same-column specialization, which the
aligned product labels of the transposed T-side grid do not satisfy (no
separability of the abstract omega labels is assumed). -/
theorem eta_pair_diff_rigidity [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {X : ClassFunction G ℂ} (hXZ : X ∈ ZIrr G)
    (hX2 : ClassFunction.inner X X = 2)
    {P1 P2 : Fin base.q × Fin base.p} (hP : P1 ≠ P2)
    {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hvanish : ∀ x ∈ conjClassSet
      ((base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G))),
      (X - (s : ℂ) • (base.eta P1.1 P1.2 - base.eta P2.1 P2.2)) x = 0) :
    X = (s : ℂ) • (base.eta P1.1 P1.2 - base.eta P2.1 P2.2) := by
  classical
  have hcardq : Nat.card (Fin base.q) = base.q :=
    Nat.card_eq_fintype_card.trans (Fintype.card_fin _)
  have hcardp : Nat.card (Fin base.p) = base.p :=
    Nat.card_eq_fintype_card.trans (Fintype.card_fin _)
  have hsep : ∀ (i i' : Fin base.q) (j j' : Fin base.p),
      ClassFunction.inner
          (X - (s : ℂ) • (base.eta P1.1 P1.2 - base.eta P2.1 P2.2))
          (base.eta i j) +
        ClassFunction.inner
          (X - (s : ℂ) • (base.eta P1.1 P1.2 - base.eta P2.1 P2.2))
          (base.eta i' j') =
      ClassFunction.inner
          (X - (s : ℂ) • (base.eta P1.1 P1.2 - base.eta P2.1 P2.2))
          (base.eta i j') +
        ClassFunction.inner
          (X - (s : ℂ) • (base.eta P1.1 P1.2 - base.eta P2.1 P2.2))
          (base.eta i' j) := by
    intro i i' j j'
    have h1 := inner_eta_grid_relation base hvanish i j
    have h2 := inner_eta_grid_relation base hvanish i' j'
    have h3 := inner_eta_grid_relation base hvanish i j'
    have h4 := inner_eta_grid_relation base hvanish i' j
    linear_combination h1 + h2 - h3 - h4
  have hmain := OddOrder.Peterfalvi.S05.orthonormalGrid_diff_rigidity
    (fun pq : Fin base.q × Fin base.p => base.eta pq.1 pq.2)
    (fun pq => eta_mem_ZIrr base pq.1 pq.2)
    (fun a => by simpa using eta_orthonormal base a.1 a.1 a.2 a.2)
    (fun a b hab => by
      rw [eta_orthonormal base a.1 b.1 a.2 b.2, if_neg]
      rintro ⟨h1, h2⟩
      exact hab (Prod.ext h1 h2))
    (by rw [hcardq]; exact base.three_le_q)
    (by rw [hcardp]; exact base.three_le_p)
    (by rw [hcardq]; exact base.q_odd)
    (by rw [hcardp]; exact base.p_odd)
    (by
      rw [hcardq, hcardp]
      exact (Nat.coprime_primes base.q_prime base.p_prime).mpr
        (Ne.symm base.p_ne_q))
    hXZ hX2 (P1 := P1) (P2 := P2) hP hs hsep
  simpa using hmain

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.8)/(11.8.2), eta pair classifier from regular values.**
The type-P regular-value bridge for an arbitrary distinct pair of eta labels:
if a norm-two virtual character agrees on the type-P regular set with a
signed difference of two eta entries, it equals that difference globally. -/
theorem eta_pair_diff_classifier_of_typePV_value [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {M : Subgroup G} (data : TypePData M)
    (hV : typePV M data =
      (base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G)))
    {P1 P2 : Fin base.q × Fin base.p} (hP : P1 ≠ P2)
    {s : ℤ} (hs : s = 1 ∨ s = -1)
    {source : ClassFunction G ℂ}
    (hsource : ∀ v ∈ typePV M data,
      source v = ((s : ℂ) • (base.eta P1.1 P1.2 - base.eta P2.1 P2.2)) v) :
    ∀ {Y : ClassFunction G ℂ}, Y ∈ ZIrr G →
      ClassFunction.inner Y Y = 2 →
      (∀ v ∈ typePV M data, Y v = source v) →
      Y = (s : ℂ) • (base.eta P1.1 P1.2 - base.eta P2.1 P2.2) := by
  intro Y hYZ hY2 hYsource
  apply eta_pair_diff_rigidity base hYZ hY2 hP hs
  intro x hx
  obtain ⟨w, hw, g, hg⟩ := hx
  have hconj : IsConj w x := isConj_iff.mpr ⟨g, hg⟩
  have hwV : w ∈ typePV M data := hV.symm ▸ hw
  rw [ClassFunction.sub_apply, ← Y.of_isConj hconj,
    ← (((s : ℂ) • (base.eta P1.1 P1.2 - base.eta P2.1 P2.2)).of_isConj hconj),
    hYsource w hwV, hsource w hwV, sub_self]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.8.2), concrete `hclassify` for the aligned transposed
eta grid.**  This discharges the norm-two residual classifier input of
`S12.Hypothesis.SHC_residual_eq_grid_diff` and
`S12.Hypothesis.charParam_a_eq_zero_of_grid_residualEq` at
`grid := alignedOmegaEtaGrid`: the regular-value pin comes from
`tau_muGridAlpha_apply_eq_of_grid_value_alignment` together with the
sigma/eta regular-value agreement, and the global upgrade is the eta
pair-difference rigidity.  No global equality of sigma isometries is used. -/
theorem alignedOmegaEtaGrid_classifier [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G))
    (hV : typePV base.T s12.typeP =
      (base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G)))
    {i : Fin s12.w1} {j : Fin s12.w2} (hj : j ≠ 0)
    {ζ : ClassFunction ↥base.T ℂ}
    (hζS : ζ ∈ OddOrder.Peterfalvi.S12.inducedFamily base.T)
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : s12.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : s12.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (s12.w1 : ℂ))
    (hnf : (n : ℤ) * (s12.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : s12.muColumnSign hG hodd j = δ)
    (hδpm : δ = 1 ∨ δ = -1) :
    ∀ {Y : ClassFunction G ℂ}, Y ∈ ZIrr G →
      ClassFunction.inner Y Y = 2 →
      (∀ v ∈ typePV base.T s12.typeP,
        Y v = s12.tau (s12.muGrid hG hodd i j -
          (δ : ℂ) • s12.muGrid hG hodd i 0 - (n : ℂ) • ζ) v) →
      Y = (δ : ℂ) •
        (alignedOmegaEtaGrid hG base s12 hW hW1 hW2 hodd i j -
          alignedOmegaEtaGrid hG base s12 hW hW1 hW2 hodd i 0) := by
  have hsource := s12.tau_muGridAlpha_apply_eq_of_grid_value_alignment
    hG hodd hj hζS hdeg hμ0 hζ1 hnf hδj
    (alignedOmegaEtaGrid hG base s12 hW hW1 hW2 hodd)
    (fun k {v} hv => alignedOmegaSigmaGrid_apply_eq_alignedOmegaEtaGrid
      hG base s12 hW hW1 hW2 hodd hV i k hv)
  have hPne : alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j ≠
      alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i 0 := by
    intro h
    have hpair : ((i, j) : Fin s12.w1 × Fin s12.w2) = (i, 0) :=
      alignedOmegaProductIndex_injective hG base s12 hW hW1 hW2 hodd h
    exact hj (congrArg Prod.snd hpair)
  intro Y hYZ hY2 hYsource
  exact eta_pair_diff_classifier_of_typePV_value base s12.typeP hV hPne hδpm
    (fun v hv => (hsource v hv).trans rfl) hYZ hY2 hYsource

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.9)(a)** (Coq `eq_in_cycTIiso`): a norm-one virtual character
agreeing with an eta-grid entry on the regular set `Ŵ = W ∖ (W₁ ∪ W₂)` equals
that entry globally.  The difference `ψ = η_A − φ` vanishes on the conjugacy
saturation of `Ŵ`, so its coefficient grid satisfies the (3.7) relation; each
of `η_A` and `φ` is norm-one, so `ψ` has at most two nonzero grid coefficients,
and the (3.8) small-support case forces them all to vanish.  In particular
`⟨φ, η_A⟩ = 1`, and the norm computation gives `ψ = 0`.

This is the rigidity behind Coq's `cycTIisoC`/`cycTIiso_irrel`: it upgrades the
regular-value agreement of two independently constructed sigma isometries to a
global equality of their grid entries, without any uniqueness assumption on
the isometries themselves. -/
theorem eta_eq_of_norm_one_regular_value_eq [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {φ : ClassFunction G ℂ} (hφZ : φ ∈ ZIrr G)
    (hφ1 : ClassFunction.inner φ φ = 1)
    (A : Fin base.q × Fin base.p)
    (hvals : ∀ w : G, w ∈ (base.W : Set G) →
      w ∉ (base.W1 : Set G) ∪ (base.W2 : Set G) →
      φ w = base.eta A.1 A.2 w) :
    φ = base.eta A.1 A.2 := by
  classical
  set ψ : ClassFunction G ℂ := base.eta A.1 A.2 - φ with hψ
  have hvanish : ∀ x ∈ conjClassSet
      ((base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G))), ψ x = 0 := by
    intro x hx
    obtain ⟨w, hw, g, hg⟩ := hx
    have hconj : IsConj w x := isConj_iff.mpr ⟨g, hg⟩
    rw [← ψ.of_isConj hconj, hψ, ClassFunction.sub_apply,
      hvals w hw.1 hw.2, sub_self]
  -- the orthonormal grid family, packaged for the norm-one support bound
  have hgridZ : ∀ pq : Fin base.q × Fin base.p,
      base.eta pq.1 pq.2 ∈ ZIrr G := fun pq => eta_mem_ZIrr base pq.1 pq.2
  have hgridDiag : ∀ a : Fin base.q × Fin base.p,
      ClassFunction.inner (base.eta a.1 a.2) (base.eta a.1 a.2) = 1 :=
    fun a => by simpa using eta_orthonormal base a.1 a.1 a.2 a.2
  have hgridOff : ∀ a b : Fin base.q × Fin base.p, a ≠ b →
      ClassFunction.inner (base.eta a.1 a.2) (base.eta b.1 b.2) = 0 :=
    fun a b hab => by
      rw [eta_orthonormal base a.1 b.1 a.2 b.2, if_neg]
      rintro ⟨h1, h2⟩
      exact hab (Prod.ext h1 h2)
  -- ψ has at most two nonzero grid coefficients
  have hηNC := OddOrder.Peterfalvi.S05.ncard_inner_grid_ne_zero_le_one
    (fun pq : Fin base.q × Fin base.p => base.eta pq.1 pq.2)
    hgridZ hgridDiag hgridOff (hgridZ A) (hgridDiag A)
  have hφNC := OddOrder.Peterfalvi.S05.ncard_inner_grid_ne_zero_le_one
    (fun pq : Fin base.q × Fin base.p => base.eta pq.1 pq.2)
    hgridZ hgridDiag hgridOff hφZ hφ1
  have hNCset : {x : Fin base.q × Fin base.p |
      ClassFunction.inner ψ (base.eta x.1 x.2) ≠ 0}.ncard ≤ 2 := by
    have hsub : {x : Fin base.q × Fin base.p |
        ClassFunction.inner ψ (base.eta x.1 x.2) ≠ 0} ⊆
        {x : Fin base.q × Fin base.p |
          ClassFunction.inner (base.eta A.1 A.2) (base.eta x.1 x.2) ≠ 0} ∪
        {x : Fin base.q × Fin base.p |
          ClassFunction.inner φ (base.eta x.1 x.2) ≠ 0} := by
      intro x hx
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
      apply hx
      rw [hψ, ClassFunction.inner_sub_left, hcon.1, hcon.2, sub_zero]
    calc {x : Fin base.q × Fin base.p |
          ClassFunction.inner ψ (base.eta x.1 x.2) ≠ 0}.ncard
        ≤ ({x : Fin base.q × Fin base.p |
            ClassFunction.inner (base.eta A.1 A.2) (base.eta x.1 x.2) ≠ 0} ∪
          {x : Fin base.q × Fin base.p |
            ClassFunction.inner φ (base.eta x.1 x.2) ≠ 0}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ {x : Fin base.q × Fin base.p |
            ClassFunction.inner (base.eta A.1 A.2) (base.eta x.1 x.2) ≠ 0}.ncard +
          {x : Fin base.q × Fin base.p |
            ClassFunction.inner φ (base.eta x.1 x.2) ≠ 0}.ncard :=
          Set.ncard_union_le _ _
      _ ≤ 2 := by omega
  have hNC : (Finset.univ.filter fun x : Fin base.q × Fin base.p =>
      ClassFunction.inner ψ (base.eta x.1 x.2) ≠ 0).card ≤ 2 := by
    calc (Finset.univ.filter fun x : Fin base.q × Fin base.p =>
          ClassFunction.inner ψ (base.eta x.1 x.2) ≠ 0).card
        = {x : Fin base.q × Fin base.p |
            ClassFunction.inner ψ (base.eta x.1 x.2) ≠ 0}.toFinset.card := by
          rw [Set.toFinset_setOf]
      _ = {x : Fin base.q × Fin base.p |
            ClassFunction.inner ψ (base.eta x.1 x.2) ≠ 0}.ncard :=
          (Set.ncard_eq_toFinset_card' _).symm
      _ ≤ 2 := hNCset
  -- (3.7) + (3.8) small support: every grid coefficient of ψ vanishes
  have hzero := grid_eq_zero_of_relation_of_card_le_two
    base.three_le_q base.three_le_p
    (a := fun i j => ClassFunction.inner ψ (base.eta i j))
    ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩
    (fun i j => inner_eta_grid_relation base hvanish i j) hNC
  -- in particular `⟨φ, η_A⟩ = 1`, and the norm computation kills ψ
  have hA : ClassFunction.inner φ (base.eta A.1 A.2) = 1 := by
    have h0 := hzero A.1 A.2
    rw [hψ, ClassFunction.inner_sub_left] at h0
    linear_combination hgridDiag A - h0
  have hAsymm : ClassFunction.inner (base.eta A.1 A.2) φ = 1 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hA]
    simp
  have hself : ClassFunction.inner ψ ψ = 0 := by
    rw [hψ]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right]
    rw [hφ1, hA, hAsymm, hgridDiag A]
    ring
  have hfin := eq_zero_of_inner_self_re_eq_zero (φ := ψ) (by rw [hself]; simp)
  rw [hψ, sub_eq_zero] at hfin
  exact hfin.symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Global sigma/eta grid identification** (Coq `cycTIisoC` for the T-side
transposition): each concrete S12 aligned sigma-grid entry *equals* the
corresponding coordinate-respecting eta-grid entry, globally.  The entry is a
norm-one virtual character agreeing with the eta entry on the shared regular
set, so (3.9)(a) rigidity applies.  This upgrades the landed regular-value
alignment to the global grid equality consumed by the transposed (11.8)
transport, with no carrier change and no sigma-map uniqueness assumption. -/
theorem alignedOmegaSigmaGrid_eq_alignedOmegaEtaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G))
    (hV : typePV base.T s12.typeP =
      (base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G)))
    (i : Fin s12.w1) (j : Fin s12.w2) :
    s12.alignedOmegaSigmaGrid hG hodd i j =
      alignedOmegaEtaGrid hG base s12 hW hW1 hW2 hodd i j := by
  have hnorm : ClassFunction.inner
      (s12.alignedOmegaSigmaGrid hG hodd i j)
      (s12.alignedOmegaSigmaGrid hG hodd i j) = 1 := by
    rw [s12.alignedOmegaSigmaGrid_inner hG hodd i i j j]
    simp
  exact eta_eq_of_norm_one_regular_value_eq base
    (s12.alignedOmegaSigmaGrid_mem_ZIrr hG hodd i j) hnorm
    (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j)
    (fun w hwW hwnot => by
      have hv : w ∈ typePV base.T s12.typeP := by
        rw [hV]; exact ⟨hwW, hwnot⟩
      exact alignedOmegaSigmaGrid_apply_eq_alignedOmegaEtaGrid
        hG base s12 hW hW1 hW2 hodd hV i j hv)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.8), eta-grid endpoint** (Coq `FTtype34_not_ortho_cycTIiso`):
the Section 12 residual of a degree-`w₁` member `ζ` is *not* orthogonal to the
shared eta grid.  This transports the canonical refuter
`S13.zeta_residual_not_orthogonal_H0C_of_refuter` through the global sigma/eta
grid identification: the zero-column sum becomes the eta zero-row sum via the
zero-preserving transposed row enumeration, and each pairing entry is hit
through the aligned product pointer.  The Dade-image identification of the
source is taken as the `himage` input (discharged by
`s12Tau_zeroColumn_sub_eq_tSideDadeMap` at the (14.9) consumer). -/
theorem member_residual_not_orthogonal_eta_of_refuter [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hV : typePV base.T s12.typeP =
      (base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G)))
    (htype : IsTypeIII base.T ∨ IsTypeIV base.T)
    (hM2 : secondDerivedInAmbient base.T =
      s12.typeP.H ⊔
        (s12.typeP.U ⊓ Subgroup.centralizer (s12.typeP.H : Set G)))
    (hHcard : Nat.card ↥s12.typeP.H = s12.w2 ^ s12.w1)
    (hrefute : ∀ s13hyp : OddOrder.Peterfalvi.S13.Hypothesis base.T,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        s13hyp.base.tau (s13hyp.SOf s13hyp.H0C) s13hyp.base.A0))
    (zeta : ClassFunction ↥base.T ℂ)
    (hzetaS : zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily base.T)
    (hzetairr : IsIrreducibleCharacter zeta)
    (hzeta1 : zeta 1 = (s12.w1 : ℂ))
    (source : ClassFunction G ℂ)
    (himage : s12.tau
        ((∑ i' : Fin s12.w1, s12.muGrid hG hG.odd i' 0) - zeta) = source) :
    ¬ ∀ (i : Fin base.q) (j : Fin base.p),
      ClassFunction.inner
        (source - ∑ j' : Fin base.p, base.eta ⟨0, base.q_prime.pos⟩ j')
        (base.eta i j) = 0 := by
  intro horth
  apply OddOrder.Peterfalvi.S13.zeta_residual_not_orthogonal_H0C_of_refuter hG s12 htype hM2
    hHcard hrefute hzetaS hzetairr hzeta1
  intro i j
  have hglobal : ∀ (a : Fin s12.w1) (b : Fin s12.w2),
      s12.alignedOmegaSigmaGrid hG hG.odd a b =
        alignedOmegaEtaGrid hG base s12 hW hW1 hW2 hG.odd a b :=
    fun a b => alignedOmegaSigmaGrid_eq_alignedOmegaEtaGrid
      hG base s12 hW hW1 hW2 hG.odd hV a b
  have hsum : (∑ i' : Fin s12.w1, s12.alignedOmegaSigmaGrid hG hG.odd i' 0) =
      ∑ j' : Fin base.p, base.eta ⟨0, base.q_prime.pos⟩ j' := by
    calc (∑ i' : Fin s12.w1, s12.alignedOmegaSigmaGrid hG hG.odd i' 0)
        = ∑ i' : Fin s12.w1, base.eta ⟨0, base.q_prime.pos⟩
            (alignedOmegaRowEquiv hG base s12 hW hW1 hW2 hG.odd i') := by
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [hglobal i' 0, alignedOmegaEtaGrid_zero_column]
      _ = ∑ j' : Fin base.p, base.eta ⟨0, base.q_prime.pos⟩ j' := by
          simpa using Equiv.sum_comp
            (alignedOmegaRowEquiv hG base s12 hW hW1 hW2 hG.odd)
            (fun j' : Fin base.p => base.eta ⟨0, base.q_prime.pos⟩ j')
  rw [himage, hsum, hglobal i j]
  exact horth
    (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hG.odd i j).1
    (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hG.odd i j).2

end OddOrder.Peterfalvi.S16
