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

end OddOrder.Peterfalvi.S16
