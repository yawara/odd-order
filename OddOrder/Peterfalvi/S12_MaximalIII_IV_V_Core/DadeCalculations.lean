import OddOrder.Peterfalvi.S12_MaximalIII_IV_V_Core.CharacterParameters

/-!
# Peterfalvi (10.5)-(10.6) — Dade-isometry calculations

Split from the former monolithic `OddOrder.Peterfalvi.S12_MaximalIII_IV_V_Core` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S12
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ## (10.5)--(10.6): Dade-isometry calculations -/

open scoped FiniteInduce in
/-- **Peterfalvi (4.8) on the §10 aligned grid, row `0`** (coherence-free): for two nonzero
columns `j, k`, `(μ_{0j} − μ_{0k})^τ = δ_j·(ω_{0j}^σ − ω_{0k}^σ)`, where `τ = hyp.tau`,
`ω^σ = alignedOmegaSigmaGrid`, and `δ_j = muColumnSign j`.

This is the §6 isometry identity `certainType_diff_dade_eq` cited through the (8.15)
instantiation `toHypothesis46`: the §10 Dade map is *definitionally* the certain-type
`dadeIntegralCharacterMap h46.dade0 h46.tau`, `muGrid`/`muColumnSign` unfold to the §6
`columnFamily` data (`unfold … rfl`), the equal-degree input is the (10.3) cross-column
constancy `muGrid_apply_one_eq` (whence `hw2`), and the §6 σ-image `certainTypeOmegaSigma`
is the aligned grid (the ω-arguments agree pointwise along `ticWEquivSdiffW = e`).  This
discharges the `h48` thread of the (11.8.3)/(11.8.5) β-reality argument (issue 9004). -/
theorem Hypothesis.tau_muGrid_zeroRow_diff [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (hw2 : (hyp.w2).Prime)
    {j k : Fin hyp.w2} (hj : j ≠ 0) (hk : k ≠ 0) :
    hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
      = (hyp.muColumnSign hG hodd j : ℂ) •
          (hyp.alignedOmegaSigmaGrid hG hodd 0 j - hyp.alignedOmegaSigmaGrid hG hodd 0 k) := by
  haveI := hyp.finiteG
  classical
  by_cases hjk : j = k
  · subst hjk
    simp
  -- §6 host context (the standard `muGrid`/`alignedOmegaSigmaGrid` let-context)
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  set χ₂ := finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
    (finCongr hcardW2sub.symm j) with hχ₂def
  set χ₂' := finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
    (finCongr hcardW2sub.symm k) with hχ₂'def
  set i0 : Fin (Nat.card h.W1) := finCongr hcardW1.symm (0 : Fin hyp.w1) with hi0def
  -- §5 tic context
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  set h46 := hyp.toHypothesis46 hG hodd with hh46
  haveI : NeZero (Nat.card ↥h46.W1) := hNeZ1
  -- column-character facts
  have hcol_ne : ∀ (l : Fin hyp.w2), l ≠ 0 →
      finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
        (finCongr hcardW2sub.symm l) ≠ 1 := by
    intro l hl heq
    rw [← finCardEquivCharacterGroup_zero (h.W2.subgroupOf (h.W1 ⊔ h.W2))] at heq
    have hl0 : finCongr hcardW2sub.symm l = 0 := (finCardEquivCharacterGroup _).injective heq
    apply hl
    have hval : (l : ℕ) = 0 := by simpa using congrArg Fin.val hl0
    exact Fin.ext hval
  have hχ₂ne1 : χ₂ ≠ 1 := hcol_ne j hj
  have hχ₂'ne1 : χ₂' ≠ 1 := hcol_ne k hk
  have hχne : χ₂ ≠ χ₂' := by
    intro heq
    apply hjk
    rw [hχ₂def, hχ₂'def] at heq
    have := (finCardEquivCharacterGroup _).injective heq
    have hval : (j : ℕ) = (k : ℕ) := by simpa using congrArg Fin.val this
    exact Fin.ext hval
  -- `muGrid` unfolds (definitional, the `unfold … rfl` idiom)
  have emj : hyp.muGrid hG hodd 0 j = ((h.columnFamily χ₂).mu i0 : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid
    rfl
  have emk : hyp.muGrid hG hodd 0 k = ((h.columnFamily χ₂').mu i0 : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid
    rfl
  -- equal degree: the (10.3) cross-column constancy
  have hdeg : ((h.columnFamily χ₂).mu i0 : ClassFunction ↥M ℂ) 1
      = ((h.columnFamily χ₂').mu i0 : ClassFunction ↥M ℂ) 1 := by
    rw [← emj, ← emk]
    exact hyp.muGrid_apply_one_eq hG hodd hw2 0 0 hj hk
  -- σ-bridge: `certainTypeOmegaSigma (toHypothesis46) = alignedOmegaSigmaGrid`
  have hpt : ∀ g : ↥tic.W, OddOrder.Peterfalvi.S06.ticWEquivSdiffW h46 g = e g := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    rw [OddOrder.Peterfalvi.S06.coe_ticWEquivSdiffW]
    show (g : G) = ((MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm
        ((Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm g) : ↥M) : G)
    rw [MulEquiv.subgroupCongr_apply]
    rfl
  have hbridge : ∀ (χc : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
      (ic : Fin (Nat.card h.W1)) (ii : Fin hyp.w1) (jj : Fin hyp.w2),
      χc = finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
        (finCongr hcardW2sub.symm jj) →
      ic = finCongr hcardW1.symm ii →
      OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χc ic
      = hyp.alignedOmegaSigmaGrid hG hodd ii jj := by
    rintro χc ic ii jj rfl rfl
    have harg : ((OddOrder.Peterfalvi.S06.ticVdiff h46).omega
          (OddOrder.Peterfalvi.S06.omegaProdCharTic h46
            (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
              (finCongr hcardW2sub.symm jj)) (finCongr hcardW1.symm ii))
            : ClassFunction (OddOrder.Peterfalvi.S06.ticVdiff h46).W ℂ)
        = ClassFunction.compHom e.toMonoidHom
            ((h.chiColumn (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
                (finCongr hcardW2sub.symm jj)) (finCongr hcardW1.symm ii)
              : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)) := by
      ext g
      rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply,
        ClassFunction.compHom_apply,
        show e.toMonoidHom g = OddOrder.Peterfalvi.S06.ticWEquivSdiffW h46 g from (hpt g).symm]
      exact OddOrder.Peterfalvi.S06.omegaProdCharTic_apply h46 _ _ g
    show (OddOrder.Peterfalvi.S06.ticVdiff h46).sigma rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication h46)
        ((OddOrder.Peterfalvi.S06.ticVdiff h46).omega
          (OddOrder.Peterfalvi.S06.omegaProdCharTic h46 _ (finCongr hcardW1.symm ii)))
      = hyp.alignedOmegaSigmaGrid hG hodd ii jj
    rw [harg]
    unfold Hypothesis.alignedOmegaSigmaGrid
    rfl
  -- `hyp.tau` on the (4.8) supported difference is the certain-type Dade map
  have hsupp : (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (typePA M hyp.typeP ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M :=
    ClassFunction.mem_supportedSubmodule.mp
      (OddOrder.Peterfalvi.S06.certainTypeDiffSupported h46 hχ₂ne1 hχ₂'ne1 i0 hdeg).2
  have happly : hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
      = h46.tau.toDadeMap
          (OddOrder.Peterfalvi.S06.certainTypeDiffSupported h46 hχ₂ne1 hχ₂'ne1 i0 hdeg) := by
    have h1 : hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
        = h46.dade0.dadeMap (k := ℂ)
            ⟨hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k,
              ClassFunction.mem_supportedSubmodule.mpr hsupp⟩ :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support h46.dade0 h46.tau hsupp
    rw [h1, show h46.tau.toDadeMap = h46.dade0.dadeMap (k := ℂ) from
      OddOrder.Peterfalvi.S04.IsDadeMap.unique h46.tau.toDadeIsometryData.isDadeMap
        h46.dade0.isDadeMap_dadeMap]
    have hval : hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k
        = ((h.columnFamily χ₂).mu i0 : ClassFunction ↥M ℂ)
          - ((h.columnFamily χ₂').mu i0 : ClassFunction ↥M ℂ) := by
      rw [emj, emk]
    exact congrArg _ (Subtype.ext hval)
  -- assemble: (4.8) + σ-bridge + sign reconciliation
  have esign : hyp.muColumnSign hG hodd j = (h46.columnFamily χ₂).sign := by
    unfold Hypothesis.muColumnSign
    rfl
  rw [happly]
  refine (OddOrder.Peterfalvi.S06.certainType_diff_dade_eq h46 hχne hχ₂ne1 hχ₂'ne1 i0 hdeg).trans ?_
  rw [hbridge χ₂ i0 0 j hχ₂def hi0def, hbridge χ₂' i0 0 k hχ₂'def hi0def,
    ← Int.cast_smul_eq_zsmul ℂ]
  exact congrArg (fun s : ℤ => (s : ℂ) •
    (hyp.alignedOmegaSigmaGrid hG hodd 0 j - hyp.alignedOmegaSigmaGrid hG hodd 0 k)) esign.symm

open scoped FiniteInduce in
/-- **Peterfalvi (4.10) on the §10 aligned grid** (coherence-free, `δ_j`-scaled): the four-corner
Dade identity `(μ_{ij} − μ_{0j} − δ_j μ_{i0} + δ_j μ_{00})^τ = δ_j·(ω_{ij}^σ − ω_{0j}^σ − ω_{i0}^σ
+ ω_{00}^σ)`.

This is the §6 `fourCorner_dade_eq` cited through the (8.15) instantiation `toHypothesis46`
(same bridging as `tau_muGrid_zeroRow_diff`), with the book's `δ_j(μ_{ij} − μ_{0j}) − (μ_{i0} −
μ_{00})` form rescaled by `δ_j` (`δ_j² = 1`, `muColumnSign_eq_one_or_neg_one`) and the trivial
column-`0` sign `δ_0 = 1` (`muColumnSign_zero`) absorbed.  This discharges the `h410` thread of
the (11.8.3)/(11.8.5) β-reality argument (issue 9004). -/
theorem Hypothesis.tau_muGrid_fourCorner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) (j : Fin hyp.w2) :
    hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd 0 j
        - (hyp.muColumnSign hG hodd j : ℂ) • hyp.muGrid hG hodd i 0
        + (hyp.muColumnSign hG hodd j : ℂ) • hyp.muGrid hG hodd 0 0)
      = (hyp.muColumnSign hG hodd j : ℂ) •
          (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd 0 j
            - hyp.alignedOmegaSigmaGrid hG hodd i 0 + hyp.alignedOmegaSigmaGrid hG hodd 0 0) := by
  haveI := hyp.finiteG
  classical
  -- §6 host context
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  set χ₂ := finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
    (finCongr hcardW2sub.symm j) with hχ₂def
  set i' : Fin (Nat.card h.W1) := finCongr hcardW1.symm i with hi'def
  have hi00 : (0 : Fin (Nat.card h.W1)) = finCongr hcardW1.symm (0 : Fin hyp.w1) := by
    apply Fin.ext; simp
  have hdual0 : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1 := by
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
      finCardEquivCharacterGroup_zero]
  -- §5 tic context
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  set h46 := hyp.toHypothesis46 hG hodd with hh46
  haveI : NeZero (Nat.card ↥h46.W1) := hNeZ1
  -- signs: `δ_j` matches the §6 column sign, and the trivial column has sign `1`
  have esign : hyp.muColumnSign hG hodd j = (h.columnFamily χ₂).sign := by
    unfold Hypothesis.muColumnSign
    rfl
  have hδ1 : (h.columnFamily
      (1 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).sign = 1 := by
    have e0 : hyp.muColumnSign hG hodd 0 = (h.columnFamily
        (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
          (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).sign := by
      unfold Hypothesis.muColumnSign
      rfl
    rw [hyp.muColumnSign_zero hG hodd, hdual0] at e0
    exact e0.symm
  -- σ-bridge (as in `tau_muGrid_zeroRow_diff`)
  have hpt : ∀ g : ↥tic.W, OddOrder.Peterfalvi.S06.ticWEquivSdiffW h46 g = e g := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    rw [OddOrder.Peterfalvi.S06.coe_ticWEquivSdiffW]
    show (g : G) = ((MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm
        ((Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm g) : ↥M) : G)
    rw [MulEquiv.subgroupCongr_apply]
    rfl
  have hbridge : ∀ (χc : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
      (ic : Fin (Nat.card h.W1)) (ii : Fin hyp.w1) (jj : Fin hyp.w2),
      χc = finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
        (finCongr hcardW2sub.symm jj) →
      ic = finCongr hcardW1.symm ii →
      OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χc ic
      = hyp.alignedOmegaSigmaGrid hG hodd ii jj := by
    rintro χc ic ii jj rfl rfl
    have harg : ((OddOrder.Peterfalvi.S06.ticVdiff h46).omega
          (OddOrder.Peterfalvi.S06.omegaProdCharTic h46
            (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
              (finCongr hcardW2sub.symm jj)) (finCongr hcardW1.symm ii))
            : ClassFunction (OddOrder.Peterfalvi.S06.ticVdiff h46).W ℂ)
        = ClassFunction.compHom e.toMonoidHom
            ((h.chiColumn (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
                (finCongr hcardW2sub.symm jj)) (finCongr hcardW1.symm ii)
              : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)) := by
      ext g
      rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply,
        ClassFunction.compHom_apply,
        show e.toMonoidHom g = OddOrder.Peterfalvi.S06.ticWEquivSdiffW h46 g from (hpt g).symm]
      exact OddOrder.Peterfalvi.S06.omegaProdCharTic_apply h46 _ _ g
    show (OddOrder.Peterfalvi.S06.ticVdiff h46).sigma rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication h46)
        ((OddOrder.Peterfalvi.S06.ticVdiff h46).omega
          (OddOrder.Peterfalvi.S06.omegaProdCharTic h46 _ (finCongr hcardW1.symm ii)))
      = hyp.alignedOmegaSigmaGrid hG hodd ii jj
    rw [harg]
    unfold Hypothesis.alignedOmegaSigmaGrid
    rfl
  -- the (4.10) four-corner carrier and its `A₀`-support
  set u : ClassFunction ↥M ℂ :=
    (h.columnFamily χ₂).signedDifference i'
      - (h.columnFamily (1 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).signedDifference i'
    with hudef
  have hsupp : u.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (typePA M hyp.typeP ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M :=
    ClassFunction.mem_supportedSubmodule.mp
      (OddOrder.Peterfalvi.S06.fourCornerDiffSupported h46 χ₂ i').2
  have happly : hyp.tau u = h46.tau.toDadeMap
      (OddOrder.Peterfalvi.S06.fourCornerDiffSupported h46 χ₂ i') := by
    have h1 : hyp.tau u = h46.dade0.dadeMap (k := ℂ)
        ⟨u, ClassFunction.mem_supportedSubmodule.mpr hsupp⟩ :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support h46.dade0 h46.tau hsupp
    rw [h1, show h46.tau.toDadeMap = h46.dade0.dadeMap (k := ℂ) from
      OddOrder.Peterfalvi.S04.IsDadeMap.unique h46.tau.toDadeIsometryData.isDadeMap
        h46.dade0.isDadeMap_dadeMap]
    exact congrArg _ (Subtype.ext rfl)
  -- the target τ-argument is `δ_j • u` (`δ_j² = 1`, `δ_0 = 1`)
  have hXeq : hyp.muGrid hG hodd i j - hyp.muGrid hG hodd 0 j
      - (hyp.muColumnSign hG hodd j : ℂ) • hyp.muGrid hG hodd i 0
      + (hyp.muColumnSign hG hodd j : ℂ) • hyp.muGrid hG hodd 0 0
      = (hyp.muColumnSign hG hodd j : ℂ) • u := by
    rw [hudef,
      OddOrder.RepresentationTheory.SignedIrreducibleDifferenceFamily.signedDifference_apply,
      OddOrder.RepresentationTheory.SignedIrreducibleDifferenceFamily.signedDifference_apply,
      hδ1, one_zsmul, ← esign]
    have emij : hyp.muGrid hG hodd i j
        = ((h.columnFamily χ₂).mu i' : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid
      rfl
    have em0j : hyp.muGrid hG hodd 0 j
        = ((h.columnFamily χ₂).mu (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid
      rfl
    have emi0 : hyp.muGrid hG hodd i 0
        = ((h.columnFamily (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
            (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).mu i' : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid
      rfl
    have em00 : hyp.muGrid hG hodd 0 0
        = ((h.columnFamily (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
            (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).mu (finCongr hcardW1.symm 0)
          : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid
      rfl
    rw [emij, em0j, emi0, em00, hdual0, ← hi00]
    simp only [OddOrder.RepresentationTheory.SignedIrreducibleDifferenceFamily.difference,
      OddOrder.RepresentationTheory.SignedIrreducibleDifferenceFamily.classFunction]
    rcases hyp.muColumnSign_eq_one_or_neg_one hG hodd j with hδ | hδ <;> rw [hδ] <;> push_cast <;>
      module
  rw [hXeq, Int.cast_smul_eq_zsmul ℂ, map_smul, happly]
  rw [show h46.tau.toDadeMap (OddOrder.Peterfalvi.S06.fourCornerDiffSupported h46 χ₂ i')
      = OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ i'
        - OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ 0
        - (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 1 i'
          - OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 1 0) from
    OddOrder.Peterfalvi.S06.fourCorner_dade_eq h46 χ₂ i']
  have hb1 : OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ i'
      = hyp.alignedOmegaSigmaGrid hG hodd i j := hbridge χ₂ i' i j hχ₂def hi'def
  have hb2 : OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ 0
      = hyp.alignedOmegaSigmaGrid hG hodd 0 j := hbridge χ₂ 0 0 j hχ₂def hi00
  have hb3 : OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 1 i'
      = hyp.alignedOmegaSigmaGrid hG hodd i 0 := hbridge 1 i' i 0 hdual0.symm hi'def
  have hb4 : OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 1 0
      = hyp.alignedOmegaSigmaGrid hG hodd 0 0 := hbridge 1 0 0 0 hdual0.symm hi00
  rw [hb1, hb2, hb3, hb4, ← Int.cast_smul_eq_zsmul ℂ]
  module

/-- **Peterfalvi (10.5), support half**: for `0 < j < w₂`, the virtual character `α_{ij}` is
supported on `A_0(M)`.  This is now a genuine (dade0-free) theorem, carried by the
`CharacterParameters` field `alpha_support` and discharged in the producer from
`Hypothesis.muGrid_alpha_support`. -/
theorem alpha_support [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} (params : CharacterParameters hyp) :
    ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → (params.alpha i j).support ⊆ hyp.A0 :=
  params.alpha_support

open scoped FiniteInduce in
/-- **§10 Dade value on `V`** (Peterfalvi's "by definition of `τ`").  For a class function `φ` on
`M` supported on `A_0(M)`, the Dade image `φ^τ = hyp.tau φ` *restores* `φ`'s value at any
`v ∈ V = typePV M`: `(φ^τ)(v) = φ(v)`.

Since `V = typePV ⊆ V^M ⊆ A_0(M)` (`subset_conjClassSetIn`), this is exactly the
value-on-support property `dadeIntegralCharacterMap_apply_mem` of the genuine §10 Dade isometry
`hyp.tau`.  It is the reusable "agrees/vanishes on `V` by definition of `τ`" step underlying the
Dade-image half of (10.5) (`α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ)` vanishes on `V`), and the (10.6.b) /
(10.9) value computations. -/
theorem Hypothesis.tau_apply_of_mem_typePV [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {φ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0)
    {v : G} (hv : v ∈ typePV M hyp.typeP) (hvM : v ∈ M) :
    hyp.tau φ v = φ ⟨v, hvM⟩ := by
  haveI := hyp.finiteG
  have hvA0 : v ∈ typePA0 M hyp.typeP := by
    rw [typePA0]
    exact Set.mem_union_right _ (OddOrder.GroupTheory.subset_conjClassSetIn hv)
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_mem hyp.dadeData.dade
    (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) hφ hvA0

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), the Dade-image value on `V`** (the "vanishes on `V`" leg of the Dade-image
half): on the exceptional set `V = typePV`, the Dade image `α_{ij}^τ` of the virtual character
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` equals `δ·(ω_{ij}^σ − ω_{i0}^σ)`, where `ω^σ` is the *aligned*
σ-grid `alignedOmegaSigmaGrid` (the σ-image of the same ω that `μ` is built from).

This is Peterfalvi's step *"By (3.2.c), (4.3.c) and the definition of `τ`, `α_{ij}^τ − δ(ω_{ij}^σ −
ω_{i0}^σ)` vanishes on `V`"*, assembled from:
* the cornerstone `tau_apply_of_mem_typePV` — `α` is supported on `A_0(M)` (the support half,
  `muGrid_alpha_support`), so `τ` restores `α`'s value on `V`;
* the reconciliation `muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV` —
  `μ_{ij}(v) = δ_j·ω_{ij}^σ(v)` on `V`, both at `j` and at column `0`;
* `muColumnSign_zero` — `δ_0 = 1`;
* `ζ` vanishing on `V` — `ζ` is induced from the normal `M' = [M,M]` and `v ∉ M'`
  (`typePData_typePV_not_mem_derived`).

It is the reusable on-`V` identity feeding the `(10.5)`/`(10.6.b)`/`(10.9)` value computations; the
*global* Dade-image identity additionally requires the `a = 0` norm/Cauchy–Schwarz argument and the
(3.8) trichotomy. -/
theorem Hypothesis.tau_muGridAlpha_apply_eq_on_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {i : Fin hyp.w1} {j : Fin hyp.w2} (hj : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    {v : G} (hv : v ∈ typePV M hyp.typeP) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) v
      = ((δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
          - hyp.alignedOmegaSigmaGrid hG hodd i 0)) v := by
  haveI := hyp.finiteG
  classical
  -- `v ∈ M` (`V ⊆ W ⊆ M`).
  have hvM : v ∈ M := typePData_W_le_self hyp.typeP (SetLike.mem_coe.mp hv.1)
  -- The (10.5) support half, so `τ` restores `α` on `V`.
  have hsupp := hyp.muGrid_alpha_support hG hodd hj hζS hdeg hμ0 hζ1 hnf hδj
  rw [hyp.tau_apply_of_mem_typePV hsupp hv hvM]
  -- `ζ` vanishes on `V`: induced from the normal `M'`, and `v ∉ M'`.
  have hζv : ζ ⟨v, hvM⟩ = 0 := by
    obtain ⟨θ, _hθne, hζeq⟩ := hζS
    have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
    have hnotmem : (⟨v, hvM⟩ : ↥M) ∉ (derivedInG M).subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]
      exact OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.typeP hv
    rw [hζeq]
    exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hnotmem
  -- Evaluate `α ⟨v⟩` via the reconciliation (`μ = δ_j·ω^σ`), `δ_0 = 1`, and `ζ(v) = 0`.
  rw [ClassFunction.sub_apply, ClassFunction.sub_apply, ClassFunction.smul_apply,
    ClassFunction.smul_apply,
    hyp.muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV hG hodd i j hv hvM,
    hyp.muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV hG hodd i 0 hv hvM,
    hδj, hyp.muColumnSign_zero hG hodd, hζv,
    ClassFunction.smul_apply, ClassFunction.sub_apply]
  push_cast
  ring

open scoped FiniteInduce in
/-- **§10 Dade isometry on the support lattice** (the inner-product half of (10.5)/(10.6)): the
genuine Dade map `τ = hyp.tau` preserves the class-function inner product on functions supported in
`A_0(M)`.  This is the §7 `dadeIntegralCharacterMap_inner_eq_on_supported_span` for the (8.15) Dade
data `hyp.dadeData`, instantiated on the two-element set `{φ, ψ}` whose members are `A_0`-supported.

It is the isometry input to the (10.5) `a = 0` argument: every `(α_{ij}^τ, …)` inner product is
computed on the `M`-side via this transfer, since `α_{ij}` is `A_0`-supported by
`muGrid_alpha_support`. -/
theorem Hypothesis.tau_inner_eq_of_supported [Finite G] {M : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M)
    {φ ψ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0) (hψ : ψ.support ⊆ hyp.A0) :
    ClassFunction.inner (hyp.tau φ) (hyp.tau ψ) = ClassFunction.inner φ ψ := by
  haveI := hyp.finiteG
  classical
  have hS : ∀ s ∈ ({φ, ψ} : Set (ClassFunction ↥M ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact hφ
    · exact hψ
  have hφ' : φ ∈ OddOrder.Peterfalvi.S07.zSpan ({φ, ψ} : Set (ClassFunction ↥M ℂ)) :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hψ' : ψ ∈ OddOrder.Peterfalvi.S07.zSpan ({φ, ψ} : Set (ClassFunction ↥M ℂ)) :=
    Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dadeData.dade hyp.hconj hS hφ' hψ'

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖α_{ij}^τ‖² = 2 + n²`**: the Dade image `α_{ij}^τ` has the same norm as
`α_{ij}`.  The genuine Dade map `τ` is an isometry on `A_0`-supported functions
(`tau_inner_eq_of_supported`), and `α_{ij}` is `A_0`-supported (`muGrid_alpha_support`), so
`‖α_{ij}^τ‖² = ‖α_{ij}‖² = 2 + n²` (`muGridAlpha_inner_self`).  This is the `‖α_{ij}^τ‖²` factor of
the (10.5) Cauchy–Schwarz bound `d²a² ≤ ‖α_{ij}^τ‖²‖μ_k^{τ₁}‖² = (2 + n²)w₁`. -/
theorem Hypothesis.muGridAlpha_tau_inner_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      = 2 + (n : ℂ) ^ 2 := by
  haveI := hyp.finiteG
  classical
  have hsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  rw [hyp.tau_inner_eq_of_supported hsupp hsupp]
  exact hyp.muGridAlpha_inner_self hG hodd i hj0 hζirr hdζ h0ζ hδpm

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}, ζ − ζ̄) = −n`** (M-side): the inner product of
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` against `ζ − ζ̄`.  The certain-type characters `μ_{ij}`, `μ_{i0}`
are degree-distinct from `ζ` and its conjugate `ζ̄` (both of degree `w₁ = ζ(1)`), so they are
orthogonal to both (`muGrid_inner_eq_zero_of_apply_one_ne`); `ζ ≠ ζ̄` (no real characters) gives
`(ζ, ζ̄) = 0`, while `(ζ, ζ) = 1`.  The only surviving term is `−n·(ζ, ζ) = −n`.

This is the `M`-side of the `(α_{ij}^τ, (ζ−ζ̄)^τ) = (α_{ij}, ζ−ζ̄) = −n` step of the (10.5)
`a = 0` argument (`ζ − ζ̄` is `A_0`-supported, so the Dade isometry transfers it). -/
theorem Hypothesis.muGridAlpha_inner_zeta_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζne : ζ.conj ≠ ζ)
    {δ : ℤ} {n : ℕ}
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (ζ - ζ.conj) = -(n : ℂ) := by
  haveI := hyp.finiteG
  classical
  have hconjirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  -- `ζ̄(1) = ζ(1)`: the degree is a real natural number, fixed by `star`.
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  have hμijζ : ClassFunction.inner (hyp.muGrid hG hodd i j) ζ = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hζirr hdζ
  have hμi0ζ : ClassFunction.inner (hyp.muGrid hG hodd i 0) ζ = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr h0ζ
  have hμijζc : ClassFunction.inner (hyp.muGrid hG hodd i j) ζ.conj = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hconjirr (by rw [hconj1]; exact hdζ)
  have hμi0ζc : ClassFunction.inner (hyp.muGrid hG hodd i 0) ζ.conj = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hconjirr (by rw [hconj1]; exact h0ζ)
  have hζζ : ClassFunction.inner ζ ζ = 1 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]
  have hζζc : ClassFunction.inner ζ ζ.conj = 0 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hconjirr, if_neg (Ne.symm hζne)]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, hμijζ, hμi0ζ, hμijζc, hμi0ζc, hζζ, hζζc,
    star_intCast, star_natCast, mul_zero, zero_mul, sub_zero, zero_sub, mul_one]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.2), `(α_{ij}, ζ − η) = −n`** for any degree-`w₁` irreducible `η ∈ S(HC)`
distinct from `ζ`.  General-`η` companion of `muGridAlpha_inner_zeta_sub_conj` (the `η = ζ̄` case):
since `η` has the same degree as `ζ` (`hη1 : η(1) = ζ(1)`), both `μ_{ij}, μ_{i0}` are degree-distinct
from — hence orthogonal to — `η` (`muGrid_inner_eq_zero_of_apply_one_ne`), and `(ζ, η) = 0`
(`η ≠ ζ`, both irreducible), so only the `−nζ` term survives:
`(α_{ij}, ζ − η) = −n(ζ, ζ) = −n` (independent of `δ`).

This is the source value that (11.8.2) lifts (via the `τ`-isometry) to `(α_{ij}^τ, (ζ − η)^τ) = −n`
for every `η ∈ S₁ = S(HC)`, `η ≠ ζ` — pinning the `ζ^{τ₁}`-coefficient of the `α_{ij}^τ` projection
onto the orthonormal `S₁^{τ₁}` (`SHC_extension_inner_*`) to `−n`. -/
theorem Hypothesis.muGridAlpha_inner_zeta_sub_irr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {ζ η : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hηirr : IsIrreducibleCharacter η)
    {δ : ℤ} {n : ℕ}
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hη1 : η 1 = ζ 1) (hηne : η ≠ ζ) :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (ζ - η) = -(n : ℂ) := by
  haveI := hyp.finiteG
  classical
  have hμijζ : ClassFunction.inner (hyp.muGrid hG hodd i j) ζ = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hζirr hdζ
  have hμi0ζ : ClassFunction.inner (hyp.muGrid hG hodd i 0) ζ = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr h0ζ
  have hμijη : ClassFunction.inner (hyp.muGrid hG hodd i j) η = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hηirr (by rw [hη1]; exact hdζ)
  have hμi0η : ClassFunction.inner (hyp.muGrid hG hodd i 0) η = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hηirr (by rw [hη1]; exact h0ζ)
  have hζζ : ClassFunction.inner ζ ζ = 1 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]
  have hζη : ClassFunction.inner ζ η = 0 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hηirr, if_neg (Ne.symm hηne)]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, hμijζ, hμi0ζ, hμijη, hμi0η, hζζ, hζη,
    star_intCast, star_natCast, mul_zero, zero_mul, sub_zero, zero_sub, mul_one]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}, μ_k − dζ̄) = 0`** (M-side, `0 < k < w₂`, `k ≠ j`): the inner
product of `α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` against `μ_k − dζ̄`, where `μ_k = ∑_{0≤i'<w₁} μ_{i'k}`
is the `W₂`-column-`k` sum.  Since `k ≠ j` and `k ≠ 0`, every `μ_{i'k}` is cross-column-orthogonal
to `μ_{ij}` and `μ_{i0}` (`muGrid_inner_cross_column`), and degree-distinct from `ζ`
(`hkζ`), so `(α_{ij}, μ_k) = 0`; and `(α_{ij}, ζ̄) = 0` (degree distinctness + `(ζ, ζ̄) = 0`), so
`(α_{ij}, dζ̄) = 0`.  Hence `(α_{ij}, μ_k − dζ̄) = 0`.

This is the `M`-side of the `(α_{ij}^τ, μ_k^{τ₁} − dζ̄^{τ₁}) = (α_{ij}, μ_k − dζ̄) = 0` step of
the (10.5) `a = 0` argument (whence `(α_{ij}^τ, μ_k^{τ₁}) = da`). -/
theorem Hypothesis.muGridAlpha_inner_muColumn_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j k : Fin hyp.w2)
    (hjk : j ≠ k) (hk0 : k ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζne : ζ.conj ≠ ζ)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    {δ : ℤ} {n d : ℕ} :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k) - (d : ℂ) • ζ.conj) = 0 := by
  haveI := hyp.finiteG
  classical
  have hconjirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  -- `(α_{ij}, ζ̄) = 0`: `μ_{ij}, μ_{i0}` degree-distinct from `ζ̄`, and `(ζ, ζ̄) = 0`.
  have hαζc : ClassFunction.inner
      (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ζ.conj = 0 := by
    have a1 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hconjirr (by rw [hconj1]; exact hdζ)
    have a2 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hconjirr (by rw [hconj1]; exact h0ζ)
    have a3 : ClassFunction.inner ζ ζ.conj = 0 := by
      rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hconjirr, if_neg (Ne.symm hζne)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, a1, a2, a3,
      mul_zero, sub_zero]
  -- `(α_{ij}, μ_{i'k}) = 0` for each `i'`: cross-column (`k ≠ j`, `k ≠ 0`) + degree (`k`-column ≠ ζ).
  have hrow : ∀ i' : Fin hyp.w1,
      ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (hyp.muGrid hG hodd i' k) = 0 := by
    intro i'
    have h1 := hyp.muGrid_inner_cross_column hG hodd i i' hjk
    have h2 := hyp.muGrid_inner_cross_column hG hodd i i' (Ne.symm hk0)
    have h3 : ClassFunction.inner ζ (hyp.muGrid hG hodd i' k) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i' k) ζ,
        hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i' k hζirr (hkζ i'), star_zero]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, h1, h2, h3,
      mul_zero, sub_zero]
  rw [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_sum_right,
    Finset.sum_eq_zero (fun i' _ => hrow i'),
    OddOrder.RepresentationTheory.inner_smul_right, hαζc, mul_zero, sub_zero]

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(a), `(α_{ij}, μ_j − dζ̄) = 1`** (M-side, `0 < j < w₂`): the diagonal
companion of `muGridAlpha_inner_muColumn_sub_conj`, where `μ_j = ∑_{0≤i'<w₁} μ_{i'j}` is the
`W₂`-column-`j` sum (the column of `μ_{ij}` itself).  Within column `j` the `μ_{i'j}` are
orthonormal (`muGrid_inner_self`/`muGrid_inner_within_column`), so `(μ_{ij}, μ_j) = 1`; `μ_{i0}` and
`ζ` are cross-column resp. degree-distinct from column `j` (`muGrid_inner_cross_column`, `hjζ`), so
`(δμ_{i0}, μ_j) = (nζ, μ_j) = 0`, giving `(α_{ij}, μ_j) = 1`; and `(α_{ij}, ζ̄) = 0` (degree
distinctness + `(ζ, ζ̄) = 0`).  Hence `(α_{ij}, μ_j − dζ̄) = 1`.

This is the `M`-side opening `1 = (α_{ij}, μ_j − dζ̄)` of Peterfalvi (10.6)(a), feeding the
`(δ(ω_{ij}^σ − ω_{i0}^σ), μ_j^{τ₁}) = 1` step (then Peterfalvi (5.8) gives the summed isometry
`μ_j^{τ₁} = δ∑_i ω_{ij}^σ`). -/
theorem Hypothesis.muGridAlpha_inner_muColumn_self_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζne : ζ.conj ≠ ζ)
    (hjζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 ≠ ζ 1)
    (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) {δ : ℤ} {n d : ℕ} :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j) - (d : ℂ) • ζ.conj) = 1 := by
  haveI := hyp.finiteG
  classical
  have hconjirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  -- `(α_{ij}, ζ̄) = 0`: `μ_{ij}, μ_{i0}` degree-distinct from `ζ̄`, and `(ζ, ζ̄) = 0`.
  have hαζc : ClassFunction.inner
      (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ζ.conj = 0 := by
    have a1 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hconjirr
      (by rw [hconj1]; exact hjζ i)
    have a2 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hconjirr
      (by rw [hconj1]; exact h0ζ)
    have a3 : ClassFunction.inner ζ ζ.conj = 0 := by
      rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hconjirr, if_neg (Ne.symm hζne)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, a1, a2, a3,
      mul_zero, sub_zero]
  -- `(α_{ij}, μ_{i'j}) = δ_{i,i'}`: within-column orthonormal; `μ_{i0}, ζ` off column `j`.
  have hrow : ∀ i' : Fin hyp.w1,
      ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (hyp.muGrid hG hodd i' j) = (if i = i' then (1 : ℂ) else 0) := by
    intro i'
    have h1 : ClassFunction.inner (hyp.muGrid hG hodd i j) (hyp.muGrid hG hodd i' j)
        = (if i = i' then (1 : ℂ) else 0) := by
      by_cases hii' : i = i'
      · rw [if_pos hii', ← hii']; exact hyp.muGrid_inner_self hG hodd i j
      · rw [if_neg hii']; exact hyp.muGrid_inner_within_column hG hodd j hii'
    have h2 := hyp.muGrid_inner_cross_column hG hodd i i' (Ne.symm hj0)
    have h3 : ClassFunction.inner ζ (hyp.muGrid hG hodd i' j) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i' j) ζ,
        hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i' j hζirr (hjζ i'), star_zero]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, h1, h2, h3,
      mul_zero, sub_zero]
  rw [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right, hαζc,
    mul_zero, sub_zero, OddOrder.RepresentationTheory.inner_sum_right,
    Finset.sum_congr rfl (fun i' _ => hrow i')]
  simp

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5) M-side inner product** `(α_{ij}, μ₀ − ζ) = n − δ`, where `μ₀ = ∑_{i'} μ_{i'0}`
is the column-`0` sum (`0 < j`).  Within column `0` the `μ_{i'0}` are orthonormal, so only `i' = i`
survives in `(δ·μ_{i0}, μ₀)`, giving `−δ`; `μ_{ij}` (column `j ≠ 0`) is cross-column to column `0`;
`ζ` (degree `w₁ > 1`) is degree-distinct from every `μ_{i'0}` (degree `1`) and from `μ_{ij}`/`μ_{i0}`,
and `(ζ, ζ) = 1` gives `(α_{ij}, ζ) = −n`.  Hence `(α_{ij}, μ₀ − ζ) = −δ − (−n) = n − δ`.  This is the
`M`-side of the (11.8.5) two-way computation of `((μ₀ − ζ)^τ, α_{ij}^τ) = (μ₀ − ζ, α_{ij})` (Dade
isometry), which together with the `G`-side (via (11.8.4)) forces `a = 0`. -/
theorem Hypothesis.muGridAlpha_inner_zeroColumnSum_sub_zeta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) {δ : ℤ} {n : ℕ} :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) = (n : ℂ) - (δ : ℂ) := by
  haveI := hyp.finiteG
  classical
  have hw1 : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
  have hcol0ζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0 1 ≠ ζ 1 := fun i' => by
    rw [hyp.muGrid_zero_column_apply_one hG hodd i', hζ1]
    intro he; have : hyp.w1 = 1 := by exact_mod_cast he.symm
    omega
  -- `(α_{ij}, ζ) = −n`: `μ_{ij}`, `μ_{i0}` degree-distinct from `ζ`, and `(ζ, ζ) = 1`.
  have hαζ : ClassFunction.inner
      (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ζ = -(n : ℂ) := by
    have a1 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hζirr hdζ
    have a2 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr h0ζ
    have a3 : ClassFunction.inner ζ ζ = 1 := by
      rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, a1, a2, a3,
      mul_zero, sub_zero, mul_one, zero_sub]
  -- `(α_{ij}, μ_{i'0}) = −δ·[i = i']`.
  have hrow : ∀ i' : Fin hyp.w1,
      ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (hyp.muGrid hG hodd i' 0) = (if i = i' then -(δ : ℂ) else 0) := by
    intro i'
    have h1 := hyp.muGrid_inner_cross_column hG hodd i i' hj0
    have h2 : ClassFunction.inner (hyp.muGrid hG hodd i 0) (hyp.muGrid hG hodd i' 0)
        = (if i = i' then (1 : ℂ) else 0) := by
      by_cases hii' : i = i'
      · rw [if_pos hii', ← hii']; exact hyp.muGrid_inner_self hG hodd i 0
      · rw [if_neg hii']; exact hyp.muGrid_inner_within_column hG hodd 0 hii'
    have h3 : ClassFunction.inner ζ (hyp.muGrid hG hodd i' 0) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i' 0) ζ,
        hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i' 0 hζirr (hcol0ζ i'), star_zero]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, h1, h2, h3,
      mul_zero, zero_sub, sub_zero]
    by_cases hii' : i = i' <;> simp [hii']
  rw [ClassFunction.inner_sub_right, hαζ, OddOrder.RepresentationTheory.inner_sum_right,
    Finset.sum_congr rfl (fun i' _ => hrow i'), Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  ring

open scoped FiniteInduce in
/-- **§10 support of an equal-degree difference in `S`** (Peterfalvi (10.5)/(11.8)): for two members
`ζ₁, ζ₂ ∈ S = inducedFamily M` of *equal degree* (`ζ₁(1) = ζ₂(1)`), the difference `ζ₁ − ζ₂` is
supported in `A_0(M)`.  Both are induced from the normal `M' = [M,M]`, hence vanish off `M'`; and
`(ζ₁ − ζ₂)(1) = 0`, so the support lies in `M'^# = M' − {1}`.  Every element of `M'^#` centralizes
itself, hence lies in `A(M) ⊆ A_0(M)` (the left disjunct of `typePA0`, as in `muGrid_alpha_support`).

This is the `hsuppdiff` precondition feeding the (5.7)/(1.4) equal-degree coherence producer
`coherentEqualDegree_fromDade` on the degree-`w₁` subfamily `S(HC)` (Peterfalvi (11.8)); the
conjugate-pair special case `ζ₂ = ζ̄` is `zeta_sub_conj_support`, used in the `(α_{ij}^τ, (ζ−ζ̄)^τ)`
step of the (10.5) `a = 0` argument. -/
theorem Hypothesis.inducedFamily_sub_support [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {ζ₁ ζ₂ : ClassFunction ↥M ℂ} (hζ₁ : ζ₁ ∈ inducedFamily M) (hζ₂ : ζ₂ ∈ inducedFamily M)
    (hdeg : ζ₁ 1 = ζ₂ 1) :
    (ζ₁ - ζ₂).support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ₁, _hθ₁ne, hζ₁eq⟩ := hζ₁
  obtain ⟨θ₂, _hθ₂ne, hζ₂eq⟩ := hζ₂
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζ₁vanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ₁ w = 0 := fun {w} hw => by
    rw [hζ₁eq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  have hζ₂vanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ₂ w = 0 := fun {w} hw => by
    rw [hζ₂eq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  intro z hz
  rw [ClassFunction.mem_support] at hz
  -- `z ∈ M'`: else `ζ₁ z = ζ₂ z = 0`.
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    apply hz
    rw [ClassFunction.sub_apply, hζ₁vanish hzK, hζ₂vanish hzK, sub_zero]
  -- `z ≠ 1`: `(ζ₁ − ζ₂)(1) = 0` by equal degree.
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hz
    rw [ClassFunction.sub_apply, hdeg, sub_self]
  have hzM' : (z : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp hzK
  show (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
    ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

open scoped FiniteInduce in
/-- **§10 support of `ζ − ζ̄`** (Peterfalvi (10.5), `a = 0` argument): the difference `ζ − ζ̄` of a
degree-`w₁` irreducible `ζ ∈ S` and its conjugate is supported in `A_0(M)`.  The conjugate-pair
special case of `inducedFamily_sub_support`: `ζ̄ = ζ.conj ∈ S` (`inducedFamily_closedUnderConjugate`)
has the same degree `ζ̄(1) = ζ(1)` (the degree is a real natural number).

This makes `ζ − ζ̄` `A_0`-supported, so the Dade isometry `τ` transfers it
(`tau_inner_eq_of_supported`) in the `(α_{ij}^τ, (ζ−ζ̄)^τ) = (α_{ij}, ζ−ζ̄)` step. -/
theorem Hypothesis.zeta_sub_conj_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ) :
    (ζ - ζ.conj).support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  -- `ζ̄(1) = ζ(1)`: the degree is a real natural number.
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  exact hyp.inducedFamily_sub_support hζS (inducedFamily_closedUnderConjugate M hζS) hconj1.symm

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}^τ, (ζ−ζ̄)^τ) = −n`**: the Dade-image inner product, transferred to
the `M`-side.  Both `α_{ij}` (`muGrid_alpha_support`) and `ζ − ζ̄` (`zeta_sub_conj_support`) are
`A_0`-supported, so the Dade isometry `τ` preserves their inner product
(`tau_inner_eq_of_supported`), and the `M`-side value is `−n`
(`muGridAlpha_inner_zeta_sub_conj`).  This is the `(α_{ij}^τ, (ζ−ζ̄)^τ) = (α_{ij}, ζ−ζ̄) = −n` step
of the (10.5) `a = 0` argument. -/
theorem Hypothesis.muGridAlpha_tau_inner_zeta_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau (ζ - ζ.conj)) = -(n : ℂ) := by
  haveI := hyp.finiteG
  classical
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hζsupp := hyp.zeta_sub_conj_support hG hodd hζS hζirr
  rw [hyp.tau_inner_eq_of_supported hαsupp hζsupp]
  exact hyp.muGridAlpha_inner_zeta_sub_conj hG hodd i j hζirr hζne hdζ h0ζ

open scoped FiniteInduce in
/-- **§10 support of `μ_k − dζ̄`** (Peterfalvi (10.5), `a = 0` argument): the column sum
`μ_k = ∑_{i} μ_{ik}` (an induced character of degree `dw₁`) minus `d` times the conjugate `ζ̄` (also
degree `w₁`) is supported in `A_0(M)`.  Both `μ_k` and `ζ̄` are induced from the normal `M'`, hence
vanish off `M'` (`muGrid_column_sum_vanishes_off_derived`, induced-from-`M'` for `ζ̄`); and the
degrees cancel, `(μ_k − dζ̄)(1) = dw₁ − dw₁ = 0`, so the support lies in `M'^# ⊆ A(M) ⊆ A_0(M)`.

This is the companion of `zeta_sub_conj_support`: it makes `μ_k − dζ̄` `A_0`-supported, so the Dade
isometry `τ` transfers `(α_{ij}, μ_k − dζ̄) = (α_{ij}^τ, (μ_k − dζ̄)^τ)` with no adjunction. -/
theorem Hypothesis.muColumn_sub_conj_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (k : Fin hyp.w2)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    {d : ℕ} (hcol1 : ∀ i, hyp.muGrid hG hodd i k 1 = (d : ℂ)) (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • ζ.conj).support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζvanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ w = 0 := fun {w} hw => by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  -- evaluation of a finite sum of class functions at a point is the sum of values.
  have hsumapply : ∀ (w : ↥M), (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) w
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k w := by
    intro w
    refine Finset.univ.induction_on (motive := fun s =>
      (∑ i ∈ s, hyp.muGrid hG hodd i k) w = ∑ i ∈ s, hyp.muGrid hG hodd i k w) ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  intro z hz
  rw [ClassFunction.mem_support] at hz
  -- `z ∈ M'`: else `μ_k z = ζ̄ z = 0`.
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    apply hz
    rw [ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.conj_apply,
      hyp.muGrid_column_sum_vanishes_off_derived hG hodd k hzK, hζvanish hzK, star_zero,
      mul_zero, sub_zero]
  -- `z ≠ 1`: `(μ_k − dζ̄)(1) = dw₁ − dw₁ = 0`.
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hz
    rw [ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.conj_apply, hζ1,
      hsumapply 1, Finset.sum_congr rfl (fun i _ => hcol1 i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, star_natCast]
    ring
  have hzM' : (z : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp hzK
  show (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
    ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

open scoped FiniteInduce in
/-- **`∑_{i'} μ_{i'0} − ζ` is `A_0`-supported** (Peterfalvi (11.8.5)).  The column-`0` sum `μ₀` and the
degree-`w₁` irreducible `ζ` are both induced from the normal `M' = [M,M]`, so both vanish off `M'`;
and `(μ₀ − ζ)(1) = w₁·1 − w₁ = 0`, so the support lies in `M'^# ⊆ A_0`.  Companion of
`muColumn_sub_conj_support` with `k = 0`, `d = 1` and `ζ` in place of `ζ̄`, used to transport the
(11.8.5) `M`-side inner product `(α_{ij}, μ₀ − ζ)` to the Dade image via `tau_inner_eq_of_supported`. -/
theorem Hypothesis.zeroColumnSum_sub_zeta_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ).support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζvanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ w = 0 := fun {w} hw => by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  have hsumapply : ∀ (w : ↥M), (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) w
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0 w := by
    intro w
    refine Finset.univ.induction_on (motive := fun s =>
      (∑ i ∈ s, hyp.muGrid hG hodd i 0) w = ∑ i ∈ s, hyp.muGrid hG hodd i 0 w) ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  intro z hz
  rw [ClassFunction.mem_support] at hz
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    apply hz
    rw [ClassFunction.sub_apply,
      hyp.muGrid_column_sum_vanishes_off_derived hG hodd 0 hzK, hζvanish hzK, sub_zero]
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hz
    rw [ClassFunction.sub_apply, hζ1, hsumapply 1,
      Finset.sum_congr rfl (fun i _ => hyp.muGrid_zero_column_apply_one hG hodd i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  have hzM' : (z : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp hzK
  show (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
    ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5), `M`-side transferred to the Dade image** `(α_{ij}^τ, (μ₀ − ζ)^τ) = n − δ`,
where `μ₀ = ∑_{i'} μ_{i'0}`.  Both `α_{ij}` (`muGrid_alpha_support`) and `μ₀ − ζ`
(`zeroColumnSum_sub_zeta_support`) are `A_0`-supported, so the Dade isometry `τ` preserves their inner
product (`tau_inner_eq_of_supported`), and the `M`-side value is `n − δ`
(`muGridAlpha_inner_zeroColumnSum_sub_zeta`).  Under the (11.8.4) by-contradiction hypothesis
`(μ₀ − ζ)^τ = ∑ ω_{r0}^σ − ζ^{τ₁}`, this becomes `(α_{ij}^τ, ∑ ω_{r0}^σ − ζ^{τ₁}) = n − δ`, whose
`G`-side expansion (via the residual decomposition `α_{ij}^τ = δ(ω^σ diff) − nζ^{τ₁} + a∑β`) equals
`n − δ − a`, forcing `a = 0`. -/
theorem Hypothesis.muGridAlpha_tau_inner_zeroColumnSum_sub_zeta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = (n : ℂ) - (δ : ℂ) := by
  haveI := hyp.finiteG
  classical
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hμsupp := hyp.zeroColumnSum_sub_zeta_support hG hodd hζS hζirr hζ1
  rw [hyp.tau_inner_eq_of_supported hαsupp hμsupp]
  exact hyp.muGridAlpha_inner_zeroColumnSum_sub_zeta hG hodd i j hj0 hζirr hζ1 hdζ h0ζ

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}^τ, (μ_k − dζ̄)^τ) = 0`** (`0 < k < w₂`, `k ≠ j`): the Dade-image
inner product, transferred to the `M`-side.  Both `α_{ij}` (`muGrid_alpha_support`) and `μ_k − dζ̄`
(`muColumn_sub_conj_support`) are `A_0`-supported, so the Dade isometry `τ` preserves their inner
product (`tau_inner_eq_of_supported`), and the `M`-side value is `0`
(`muGridAlpha_inner_muColumn_sub_conj`).

Since `μ_k`, `ζ̄ ∈ ℤ[S]`, on the coherent side `(μ_k − dζ̄)^τ = (μ_k − dζ̄)^{τ₁} = μ_k^{τ₁} − dζ̄^{τ₁}`
(the coherent extension agrees with `τ` on this `A_0`-supported lattice element), so this is the
`(α_{ij}^τ, μ_k^{τ₁} − dζ̄^{τ₁}) = 0` step of the (10.5) `a = 0` argument, whence
`(α_{ij}^τ, μ_k^{τ₁}) = da`.  No Dade–coherence adjunction is needed: the combination `μ_k − dζ̄`,
not `μ_k` alone, is supported. -/
theorem Hypothesis.muGridAlpha_tau_inner_muColumn_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ)) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k) - (d : ℂ) • ζ.conj)) = 0 := by
  haveI := hyp.finiteG
  classical
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hμsupp := hyp.muColumn_sub_conj_support hG hodd k hζS hζirr hcol1 hζ1
  rw [hyp.tau_inner_eq_of_supported hαsupp hμsupp]
  exact hyp.muGridAlpha_inner_muColumn_sub_conj hG hodd i j k hjk hk0 hζirr hζne hkζ hdζ h0ζ

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(a), `(α_{ij}^τ, (μ_j − dζ̄)^τ) = 1`** (diagonal, `0 < j < w₂`): the
Dade-image inner product transferred to the `M`-side.  Both `α_{ij}` (`muGrid_alpha_support`) and
the diagonal column `μ_j − dζ̄` (`muColumn_sub_conj_support`) are `A_0`-supported, so `τ` preserves
the inner product (`tau_inner_eq_of_supported`); the `M`-side value is `1` (the diagonal
`muGridAlpha_inner_muColumn_self_sub_conj`, vs `0` for the off-diagonal companion).

This is the opening `1 = (α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁})` of Peterfalvi (10.6)(a) (on the coherent
side `(μ_j − dζ̄)^τ = μ_j^{τ₁} − dζ̄^{τ₁}`, `tau_muColumn_sub_conj_eq_tau1`), which by Peterfalvi
(5.8) gives the summed isometry `μ_j^{τ₁} = δ∑_i ω_{ij}^σ` (the (10.6)(a) conclusion). -/
theorem Hypothesis.muGridAlpha_tau_inner_muColumn_self_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hjζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 = (d : ℂ)) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j) - (d : ℂ) • ζ.conj)) = 1 := by
  haveI := hyp.finiteG
  classical
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hμsupp := hyp.muColumn_sub_conj_support hG hodd j hζS hζirr hcol1 hζ1
  rw [hyp.tau_inner_eq_of_supported hαsupp hμsupp]
  exact hyp.muGridAlpha_inner_muColumn_self_sub_conj hG hodd i j hj0 hζirr hζne hjζ h0ζ

/-- **§10 τ/τ₁ compatibility on `ζ − ζ̄`** (Peterfalvi (10.5), `a = 0` argument): the Dade image
`(ζ − ζ̄)^τ` equals `ζ^{τ₁} − ζ̄^{τ₁}` for the coherent extension `τ₁`.  Since `ζ ∈ S` and
`ζ̄ ∈ S` (`inducedFamily_closedUnderConjugate`), the difference `ζ − ζ̄` lies in the supported
lattice `ℤ[S, A_0]` (`zeta_sub_conj_support`), where `τ₁` agrees with `τ`
(`coherent.extends_on_supported`); linearity of `τ₁` (`map_sub`) then splits the image.

This converts the pure-`τ` identity `(α_{ij}^τ, (ζ−ζ̄)^τ) = −n`
(`muGridAlpha_tau_inner_zeta_sub_conj`) into the `τ₁` form, giving `(α_{ij}^τ, ζ̄^{τ₁}) = a`
(with `a − n := (α_{ij}^τ, ζ^{τ₁})`) in the (10.5) `a = 0` argument. -/
theorem Hypothesis.tau_zeta_sub_conj_eq_tau1 [Finite G] [Fintype G] {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ) :
    hyp.tau (ζ - ζ.conj) = coh.tau1 ζ - coh.tau1 ζ.conj := by
  have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hζS
  have hspanζc : ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.subset_span (inducedFamily_closedUnderConjugate M hζS)
  have hmem : (ζ - ζ.conj) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Sset hyp.A0 :=
    ⟨Submodule.sub_mem _ hspanζ hspanζc, hyp.zeta_sub_conj_support hG hodd hζS hζirr⟩
  rw [← coh.coherent.extends_on_supported _ hmem, map_sub]
  rfl

open scoped FiniteInduce in
/-- **§10 τ/τ₁ compatibility on `μ_k − dζ̄`** (Peterfalvi (10.5), `a = 0` argument): the Dade image
`(μ_k − dζ̄)^τ` equals `μ_k^{τ₁} − dζ̄^{τ₁}` for the coherent extension `τ₁`.  Since
`μ_k = ∑_i μ_{ik} ∈ S` (`muGrid_column_sum_mem_inducedFamily`) and `ζ̄ ∈ S`
(`inducedFamily_closedUnderConjugate`), the combination `μ_k − dζ̄` lies in the supported lattice
`ℤ[S, A_0]` (`muColumn_sub_conj_support`), where `τ₁` agrees with `τ`
(`coherent.extends_on_supported`); `τ₁`-linearity (`map_sub`, `map_nsmul`) then splits the image.

This converts `(α_{ij}^τ, (μ_k − dζ̄)^τ) = 0` (`muGridAlpha_tau_inner_muColumn_sub_conj`) into the
`τ₁` form, giving `(α_{ij}^τ, μ_k^{τ₁}) = da` in the (10.5) `a = 0` argument. -/
theorem Hypothesis.tau_muColumn_sub_conj_eq_tau1 [Finite G] [Fintype G] {M : Subgroup G}
    [Fintype ↥M] [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (k : Fin hyp.w2) {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    {d : ℕ} (hcol1 : ∀ i, hyp.muGrid hG hodd i k 1 = (d : ℂ)) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • ζ.conj)
      = coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • coh.tau1 ζ.conj := by
  have hμkS := hyp.muGrid_column_sum_mem_inducedFamily hG hodd k hdk1
  have hspanμ : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
      ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hμkS
  have hspanζc : ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.subset_span (inducedFamily_closedUnderConjugate M hζS)
  have hsmulmem : (d : ℂ) • ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hspanζc d
  have hmem : ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • ζ.conj)
      ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Sset hyp.A0 :=
    ⟨Submodule.sub_mem _ hspanμ hsmulmem,
      hyp.muColumn_sub_conj_support hG hodd k hζS hζirr hcol1 hζ1⟩
  rw [← coh.coherent.extends_on_supported _ hmem, map_sub]
  congr 1
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, Nat.cast_smul_eq_nsmul]
  rfl

/-- **The (10.5) `a = 0` numeric core.**  If `a ∈ ℤ` satisfies the Cauchy–Schwarz bound
`(d·a)² ≤ (2+n²)w₁` with `d = nw₁ + δ`, `δ = ±1`, `w₁ ≥ 3` (odd, since `|G|` is odd) and `n ≥ 2`
(even and positive), then `a = 0`.  Else `a² ≥ 1` gives `d² ≤ (2+n²)w₁`, but `d² = (nw₁+δ)² >
(2+n²)w₁` for `w₁ ≥ 3, n ≥ 2` — a contradiction (Peterfalvi: "`n < 2`, contradicting `n` even,
`n > 0`"). -/
private theorem cauchySchwarz_numeric {d n w₁ : ℕ} {δ a : ℤ}
    (hd : (d : ℤ) = (n : ℤ) * (w₁ : ℤ) + δ) (hδ : δ = 1 ∨ δ = -1) (hw1 : 3 ≤ w₁) (hn2 : 2 ≤ n)
    (hbound : ((d : ℝ) * (a : ℝ)) ^ 2 ≤ (2 + (n : ℝ) ^ 2) * (w₁ : ℝ)) : a = 0 := by
  by_contra ha
  have ha1 : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ a ^ 2 := by
      rcases lt_or_gt_of_ne ha with h | h <;> nlinarith [sq_nonneg a]
    exact_mod_cast this
  have hdpos : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  have hd2 : ((d : ℝ)) ^ 2 ≤ (2 + (n : ℝ) ^ 2) * (w₁ : ℝ) := by nlinarith [hbound, ha1, hdpos]
  have hdR : (d : ℝ) = (n : ℝ) * (w₁ : ℝ) + (δ : ℝ) := by exact_mod_cast hd
  have hw1R : (3 : ℝ) ≤ (w₁ : ℝ) := by exact_mod_cast hw1
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hδR : (δ : ℝ) = 1 ∨ (δ : ℝ) = -1 := by rcases hδ with h | h <;> [left; right] <;> exact_mod_cast h
  rw [hdR] at hd2
  rcases hδR with hδ1 | hδ1 <;> rw [hδ1] at hd2 <;>
    nlinarith [hd2, hw1R, hn2R, mul_nonneg (by linarith : (0:ℝ) ≤ (w₁:ℝ) - 3) (by linarith : (0:ℝ) ≤ (n:ℝ) - 2),
      mul_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ) - 2) (by linarith : (0:ℝ) ≤ (n:ℝ) - 2),
      mul_nonneg (by linarith : (0:ℝ) ≤ (w₁:ℝ) - 3) (by linarith : (0:ℝ) ≤ (w₁:ℝ) - 3)]

/-- **Cauchy–Schwarz for the class-function inner product** (real-part form): for class functions
`φ, ψ` of any finite group `H`, `⟨φ, ψ⟩.re² ≤ ⟨φ, φ⟩.re · ⟨ψ, ψ⟩.re`.

Proof by the discriminant: the real quadratic `t ↦ ⟨φ − tψ, φ − tψ⟩.re = ⟨ψ,ψ⟩.re·t² −
2⟨φ,ψ⟩.re·t + ⟨φ,φ⟩.re` is `≥ 0` for every real `t` (positive semidefiniteness,
`inner_self_re_nonneg`), so its discriminant is `≤ 0` (`discrim_le_zero`).  This is the
`(α_{ij}^τ, μ_k^{τ₁})² ≤ ‖α_{ij}^τ‖²·‖μ_k^{τ₁}‖²` of the (10.5) `a = 0` argument. -/
private theorem classFunction_inner_re_sq_le {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (φ ψ : ClassFunction H ℂ) :
    (ClassFunction.inner φ ψ).re ^ 2
      ≤ (ClassFunction.inner φ φ).re * (ClassFunction.inner ψ ψ).re := by
  have hquad : ∀ t : ℝ, 0 ≤ (ClassFunction.inner ψ ψ).re * (t * t)
      + (-2 * (ClassFunction.inner φ ψ).re) * t + (ClassFunction.inner φ φ).re := by
    intro t
    have key : ClassFunction.inner (φ - (t : ℂ) • ψ) (φ - (t : ℂ) • ψ)
        = ClassFunction.inner φ φ - (t : ℂ) * ClassFunction.inner φ ψ
          - (t : ℂ) * ClassFunction.inner ψ φ + (t : ℂ) * (t : ℂ) * ClassFunction.inner ψ ψ := by
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
        Complex.star_def, Complex.conj_ofReal]
      ring
    have hre : (ClassFunction.inner (φ - (t : ℂ) • ψ) (φ - (t : ℂ) • ψ)).re
        = (ClassFunction.inner ψ ψ).re * (t * t)
          + (-2 * (ClassFunction.inner φ ψ).re) * t + (ClassFunction.inner φ φ).re := by
      rw [key, OddOrder.RepresentationTheory.inner_conj_symm φ ψ]
      simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
        zero_mul, mul_zero, sub_zero, add_zero]
      ring
    rw [← hre]
    exact inner_self_re_nonneg _
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith [hd]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}^τ, μ_k^{τ₁}) = da`** (`0 < k < w₂`, `k ≠ j`): the key inner
product of the (10.5) `a = 0` argument, where `a := (α_{ij}^τ, ζ^{τ₁}) + n`.

From the two pure-`τ` Dade-image identities and their `τ₁` forms:
* `(α_{ij}^τ, (ζ−ζ̄)^τ) = −n` (`muGridAlpha_tau_inner_zeta_sub_conj`) with `(ζ−ζ̄)^τ = ζ^{τ₁}−ζ̄^{τ₁}`
  (`tau_zeta_sub_conj_eq_tau1`) gives `(α_{ij}^τ, ζ̄^{τ₁}) = (α_{ij}^τ, ζ^{τ₁}) + n = a`;
* `(α_{ij}^τ, (μ_k−dζ̄)^τ) = 0` (`muGridAlpha_tau_inner_muColumn_sub_conj`) with
  `(μ_k−dζ̄)^τ = μ_k^{τ₁}−dζ̄^{τ₁}` (`tau_muColumn_sub_conj_eq_tau1`) gives
  `(α_{ij}^τ, μ_k^{τ₁}) = d·(α_{ij}^τ, ζ̄^{τ₁}) = d·a`.

This `d·a` is the `(α_{ij}^τ, μ_k^{τ₁})` term of the Cauchy–Schwarz bound
`d²a² ≤ ‖α_{ij}^τ‖²·‖μ_k^{τ₁}‖² = (2+n²)w₁`. -/
theorem Hypothesis.muGridAlpha_tau1_inner_muColumn [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k))
      = (d : ℂ) * (ClassFunction.inner
          (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
          (coh.tau1 ζ) + (n : ℂ)) := by
  -- `(α^τ, ζ̄^{τ₁}) = (α^τ, ζ^{τ₁}) + n` from the `ζ − ζ̄` identity.
  have h12 := hyp.muGridAlpha_tau_inner_zeta_sub_conj hG hodd i hj0 hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ
  rw [hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr,
    ClassFunction.inner_sub_right] at h12
  -- `(α^τ, μ_k^{τ₁}) = d·(α^τ, ζ̄^{τ₁})` from the `μ_k − dζ̄` identity.
  have h45 := hyp.muGridAlpha_tau_inner_muColumn_sub_conj hG hodd i hj0 k hjk hk0 hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ hkζ hcol1
  rw [hyp.tau_muColumn_sub_conj_eq_tau1 hG hodd k coh hζS hζirr hcol1 hζ1 hdk1,
    ClassFunction.inner_sub_right,
    OddOrder.RepresentationTheory.inner_smul_right, star_natCast] at h45
  linear_combination h45 - (d : ℂ) * h12

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(a), `(α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁}) = 1`** (diagonal): the coherent-side
form of the G-side diagonal inner product `muGridAlpha_tau_inner_muColumn_self_sub_conj`.  Since
`μ_j = ∑_i μ_{ij} ∈ S` (`muGrid_column_sum_mem_inducedFamily`) and `ζ̄ ∈ S`, the supported
combination `(μ_j − dζ̄)^τ` splits as `μ_j^{τ₁} − dζ̄^{τ₁}` (`tau_muColumn_sub_conj_eq_tau1`).

This is the reduction opening `1 = (α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁})` of Peterfalvi (10.6)(a);
dropping the `⊥ Im σ` terms (`ζ^{τ₁}, ζ̄^{τ₁} ⊥ Im σ`, `ζ^{τ₁} ⊥ μ_j^{τ₁}`) gives
`(δ(ω_{ij}^σ − ω_{i0}^σ), μ_j^{τ₁}) = 1`, and Peterfalvi (5.8) then yields the summed isometry
`μ_j^{τ₁} = δ∑_i ω_{ij}^σ` (the (10.6)(a) conclusion, still gated on (5.8)). -/
theorem Hypothesis.muGridAlpha_tau1_inner_muColumn_self_sub_conj [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hjζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 = (d : ℂ))
    (hdj1 : hyp.muGrid hG hodd 0 j 1 ≠ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j)
          - (d : ℂ) • coh.tau1 ζ.conj) = 1 := by
  have hG_side := hyp.muGridAlpha_tau_inner_muColumn_self_sub_conj hG hodd i hj0 hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj h0ζ hjζ hcol1
  rwa [hyp.tau_muColumn_sub_conj_eq_tau1 hG hodd j coh hζS hζirr hcol1 hζ1 hdj1] at hG_side

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖μ_k^{τ₁}‖² = w₁`** (`0 < k < w₂`): the coherent extension `τ₁` is an
isometry on `ℤ[S]`, and `μ_k = ∑_i μ_{ik} ∈ S` (`muGrid_column_sum_mem_inducedFamily`), so
`‖μ_k^{τ₁}‖² = ‖μ_k‖² = w₁` (`coherent.extension_inner_eq` + `muGrid_column_sum_inner_self`).

This is the `‖μ_k^{τ₁}‖²` factor of the (10.5) Cauchy–Schwarz bound
`d²a² = (α_{ij}^τ, μ_k^{τ₁})² ≤ ‖α_{ij}^τ‖²·‖μ_k^{τ₁}‖² = (2+n²)w₁`. -/
theorem Hypothesis.muColumn_tau1_inner_self [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (k : Fin hyp.w2) {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    ClassFunction.inner (coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k))
        (coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)) = (hyp.w1 : ℂ) := by
  have hμkS := hyp.muGrid_column_sum_mem_inducedFamily hG hodd k hdk1
  have hspan : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
      ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hμkS
  show ClassFunction.inner (coh.coherent.extension (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k))
      (coh.coherent.extension (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)) = (hyp.w1 : ℂ)
  rw [coh.coherent.extension_inner_eq _ _ hspan hspan]
  exact hyp.muGrid_column_sum_inner_self hG hodd k

open scoped FiniteInduce in
/-- **§10 `α_{ij}^τ` is a virtual character of `G`** (Peterfalvi (10.5)): `α_{ij} = μ_{ij} − δ·μ_{i0}
− n·ζ` is a virtual character of `M` (`muGrid_isIrreducible`, `ζ` irreducible) and is `A_0`-supported
(`muGrid_alpha_support`), so its Dade image lies in `ℤ[Irr G]`
(`dadeIntegralCharacterMap_mem_ZIrr_of_supported`).  Together with `ζ^{τ₁}, μ_k^{τ₁} ∈ ℤ[Irr G]` this
makes the inner products of the `a = 0` argument integers. -/
theorem Hypothesis.muGridAlpha_tau_mem_ZIrr [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2}
    (hj0 : j ≠ 0) {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ∈ ZIrr G := by
  haveI := hyp.finiteG
  have hαZ : (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ∈ ZIrr ↥M := by
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (hyp.muGrid_isIrreducible hG hodd i j).mem_ZIrr ?_) ?_
    · rw [Int.cast_smul_eq_zsmul]
      exact zsmul_mem (hyp.muGrid_isIrreducible hG hodd i 0).mem_ZIrr δ
    · rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hζirr.mem_ZIrr n
  have hsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dadeData.dade hyp.hconj hsupp hαZ

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `a = 0`**: the integer `a = (α_{ij}^τ, ζ^{τ₁}) + n` of the (10.5) Cauchy–
Schwarz argument vanishes, i.e. `(α_{ij}^τ, ζ^{τ₁}) = −n`.

`(α_{ij}^τ, ζ^{τ₁}) = m ∈ ℤ` (`α_{ij}^τ, ζ^{τ₁} ∈ ℤ[Irr G]`, `inner_mem_ZIrr_int`); set `a = m + n`.
Then `(α_{ij}^τ, μ_k^{τ₁}) = da` (`muGridAlpha_tau1_inner_muColumn`), and Cauchy–Schwarz
(`classFunction_inner_re_sq_le`) with `‖α_{ij}^τ‖² = 2 + n²` (`muGridAlpha_tau_inner_self`) and
`‖μ_k^{τ₁}‖² = w₁` (`muColumn_tau1_inner_self`) gives `(da)² ≤ (2+n²)w₁`.  By the numeric core
(`cauchySchwarz_numeric`; `d = nw₁+δ`, `δ = ±1`, `w₁ ≥ 3` odd, `n ≥ 2` even) this forces `a = 0`. -/
theorem Hypothesis.muGridAlpha_tau1_zeta_eq_neg_n [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hw1 : 3 ≤ hyp.w1) (hn2 : 2 ≤ n) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.tau1 ζ) = -(n : ℂ) := by
  haveI := hyp.finiteG
  classical
  -- `(α^τ, ζ^{τ₁}) = m ∈ ℤ`.
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  have hζZ : coh.tau1 ζ ∈ ZIrr G := coh.coherent.extension_mem_ZIrr ζ (Submodule.subset_span hζS)
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hαZ hζZ
  -- `(α^τ, μ_k^{τ₁}) = d·(m + n)` and the two norms.
  have hda := hyp.muGridAlpha_tau1_inner_muColumn hG hodd i hj0 k hjk hk0 coh hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ hkζ hcol1 hdk1
  rw [hm] at hda
  have hnorm_a := hyp.muGridAlpha_tau_inner_self hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
    hdζ h0ζ hδpm
  have hnorm_mu := hyp.muColumn_tau1_inner_self hG hodd k coh hdk1
  -- Cauchy–Schwarz, with the three inner products substituted.
  have hcs := classFunction_inner_re_sq_le
    (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
    (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k))
  rw [hda, hnorm_a, hnorm_mu] at hcs
  have hre1 : ((d : ℂ) * ((m : ℂ) + (n : ℂ))).re = (d : ℝ) * ((m : ℝ) + (n : ℝ)) := by
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  have hre2 : ((2 : ℂ) + (n : ℂ) ^ 2).re = 2 + (n : ℝ) ^ 2 := by
    simp [Complex.add_re, pow_two, Complex.mul_re, Complex.mul_im]
  rw [hre1, hre2, Complex.natCast_re] at hcs
  -- Apply the numeric core with `a = m + n`.
  have ha0 : m + (n : ℤ) = 0 := by
    refine cauchySchwarz_numeric (d := d) (n := n) (w₁ := hyp.w1) (δ := δ) (a := m + n)
      (by linarith [hnf]) hδpm hw1 hn2 ?_
    push_cast
    convert hcs using 2
  rw [hm]
  have hmn : m = -(n : ℤ) := by omega
  rw [hmn]; push_cast; ring

open scoped FiniteInduce in
/-- **§10 `‖ζ^{τ₁}‖² = 1`** (Peterfalvi (10.5)): the coherent extension `τ₁` is an isometry on
`ℤ[S]` and `ζ ∈ S` is irreducible, so `‖ζ^{τ₁}‖² = ‖ζ‖² = 1`. -/
theorem Hypothesis.zeta_tau1_inner_self [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ) :
    ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ) = 1 := by
  have hspan : ζ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hζS
  show ClassFunction.inner (coh.coherent.extension ζ) (coh.coherent.extension ζ) = 1
  rw [coh.coherent.extension_inner_eq _ _ hspan hspan,
    OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]

open scoped FiniteInduce in
/-- **`ζ^{τ₁} ⊥ ζ̄^{τ₁}`** (Peterfalvi (10.6)(a) reduction): the coherent images of the degree-`w₁`
irreducible `ζ` and its conjugate `ζ̄` are orthogonal.  As `ζ, ζ̄ ∈ 𝒮`
(`inducedFamily_closedUnderConjugate`) and `τ₁ = coh.extension` is an isometry on `ℤ[𝒮]`
(`extension_inner_eq`), `(ζ^{τ₁}, ζ̄^{τ₁}) = (ζ, ζ̄) = 0` (`ζ ≠ ζ̄`, both irreducible).

One of the three orthogonalities dropping out of the (10.6)(a) reduction `(α_{ij}^τ, μ_j^{τ₁} −
dζ̄^{τ₁}) = (δ(ω_{ij}^σ − ω_{i0}^σ), μ_j^{τ₁})`; the remaining `ζ̄^{τ₁} ⊥ Im σ`
is the §5 (5.3.b)/(5.5) input still to be formalised. -/
theorem Hypothesis.zeta_tau1_inner_conj [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) :
    ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ.conj) = 0 := by
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hspan : ζ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hζS
  have hspanc : ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hζcS
  show ClassFunction.inner (coh.coherent.extension ζ) (coh.coherent.extension ζ.conj) = 0
  rw [coh.coherent.extension_inner_eq _ _ hspan hspanc,
    OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr.conj, if_neg (Ne.symm hζne)]

open scoped FiniteInduce in
/-- **`ζ^{τ₁} ⊥ μ_k^{τ₁}`** (Peterfalvi (10.6)(a) reduction): the coherent image of the degree-`w₁`
irreducible `ζ` is orthogonal to that of the column character `μ_k = ∑_i μ_{ik} ∈ 𝒮`.  By the
isometry, `(ζ^{τ₁}, μ_k^{τ₁}) = (ζ, ∑_i μ_{ik}) = ∑_i (ζ, μ_{ik}) = 0`, each summand `0` by the
degree mismatch `μ_{ik}(1) = d ≠ w₁ = ζ(1)` (`muGrid_inner_eq_zero_of_apply_one_ne` + conjugate
symmetry).  A second orthogonality of the (10.6)(a) reduction (see `zeta_tau1_inner_conj`). -/
theorem Hypothesis.zeta_tau1_inner_muColumn [Finite G] {M : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (k : Fin hyp.w2) {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    ClassFunction.inner (coh.tau1 ζ)
        (coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)) = 0 := by
  have hμkS := hyp.muGrid_column_sum_mem_inducedFamily hG hodd k hdk1
  have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hζS
  have hspanμ : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
      ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hμkS
  show ClassFunction.inner (coh.coherent.extension ζ)
    (coh.coherent.extension (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)) = 0
  rw [coh.coherent.extension_inner_eq _ _ hspanζ hspanμ,
    OddOrder.RepresentationTheory.inner_sum_right]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have h0 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i k hζirr (hkζ i)
  rw [OddOrder.RepresentationTheory.inner_conj_symm, h0, star_zero]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖X‖² = 2` and `X ⊥ ζ^{τ₁}`** where `X = α_{ij}^τ + n·ζ^{τ₁}`: with
`(α_{ij}^τ, ζ^{τ₁}) = −n` (`a = 0`, `muGridAlpha_tau1_zeta_eq_neg_n`), `‖α_{ij}^τ‖² = 2 + n²`
(`muGridAlpha_tau_inner_self`) and `‖ζ^{τ₁}‖² = 1` (`zeta_tau1_inner_self`):
`(X, ζ^{τ₁}) = (α_{ij}^τ, ζ^{τ₁}) + n‖ζ^{τ₁}‖² = −n + n = 0`, and
`‖X‖² = ‖α_{ij}^τ‖² + 2n·(α_{ij}^τ, ζ^{τ₁}) + n²‖ζ^{τ₁}‖² = (2+n²) − 2n² + n² = 2`.

So `α_{ij}^τ = X − n·ζ^{τ₁}` with `X` a virtual character of `G` orthogonal to `ζ^{τ₁}` of squared
norm `2` — the decomposition the (10.5) `(v)`/`(vi)` argument (`NC(ψ) ≤ 4`, (3.8)) operates on. -/
theorem Hypothesis.muGridAlpha_tau_X_inner [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hw1 : 3 ≤ hyp.w1) (hn2 : 2 ≤ n) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.tau1 ζ) (coh.tau1 ζ) = 0
    ∧ ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.tau1 ζ)
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.tau1 ζ) = 2 := by
  have ha0 := hyp.muGridAlpha_tau1_zeta_eq_neg_n hG hodd i hj0 k hjk hk0 coh hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ hkζ hcol1 hdk1 hδpm hw1 hn2
  have hnorm_a := hyp.muGridAlpha_tau_inner_self hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
    hdζ h0ζ hδpm
  have hzz := hyp.zeta_tau1_inner_self hG hodd coh hζS hζirr
  have ha0' : ClassFunction.inner (coh.tau1 ζ)
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)) = -(n : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, ha0, star_neg, star_natCast]
  constructor
  · simp only [ClassFunction.inner_add_left, ClassFunction.inner_smul_left, ha0, hzz, mul_one]
    ring
  · simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      ha0, ha0', hnorm_a, hzz, star_natCast, mul_one]
    ring

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), (vi) precursor — `ψ` vanishes on `V`**: the virtual character
`ψ = α_{ij}^τ + n·ζ^{τ₁} − δ(ω_{ij}^σ − ω_{i0}^σ)` (this is `X − δ(ω^σ diff)` of the (10.5) endgame,
since `α^τ = X − nζ^{τ₁}`) vanishes on `V`.

Combines the value-on-`V` leg `tau_muGridAlpha_apply_eq_on_typePV` (`α^τ = δ(ω^σ diff)` on `V`, by
(3.2.c)/(4.3.c) and the definition of `τ`) with the vanishing of `ζ^{τ₁}` on `V` (`hζvanish`, the
§5/§7 input of (10.5): "By (5.3.b), (5.5) and (3.2.d), `ζ^{τ₁}` vanishes on `V`").  The remaining
step to `alpha_tau_image` is `NC(ψ) ≤ 4 < 2·inf(w₁,w₂)` + Theorem (3.8)
(`S05.sigmaCoeff_trichotomy`, requiring a `FullDadeApplication` for the type-`P` `TICyclicHypothesis`)
forcing `ψ ⊥ ω^σ`, hence `ψ = 0`. -/
theorem Hypothesis.muGridPsi_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {i : Fin hyp.w1} {j : Fin hyp.w2} (hj : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hζvanish : ∀ v ∈ typePV M hyp.typeP, coh.tau1 ζ v = 0)
    {v : G} (hv : v ∈ typePV M hyp.typeP) :
    (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        + (n : ℂ) • coh.tau1 ζ
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
            - hyp.alignedOmegaSigmaGrid hG hodd i 0)) v = 0 := by
  have hleg := hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hj hζS hdeg hμ0 hζ1 hnf hδj hv
  simp only [ClassFunction.sub_apply, ClassFunction.add_apply, ClassFunction.smul_apply] at hleg ⊢
  rw [hleg, hζvanish v hv]
  simp

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(ζ − ζ̄)^τ` vanishes on `V`** (the "by definition of `τ`" step underlying
the (5.3.b)/(5.5)/(3.2.d) `ζ^{τ₁}`-vanishing argument).  Since `ζ` is induced from the normal
`M' = [M,M]` and every `v ∈ V = typePV` lies outside `M'` (`typePData_typePV_not_mem_derived`),
both `ζ` and its conjugate `ζ̄` vanish at `v`; the difference `ζ − ζ̄` is `A_0(M)`-supported
(`zeta_sub_conj_support`), so the Dade isometry restores its value at `v`
(`tau_apply_of_mem_typePV`), giving `(ζ − ζ̄)^τ(v) = 0`. -/
theorem Hypothesis.tau_zeta_sub_conj_vanishes_on_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) {v : G} (hv : v ∈ typePV M hyp.typeP) :
    hyp.tau (ζ - ζ.conj) v = 0 := by
  haveI := hyp.finiteG
  classical
  have hvM : v ∈ M := typePData_W_le_self hyp.typeP (SetLike.mem_coe.mp hv.1)
  have hsupp := hyp.zeta_sub_conj_support hG hodd hζS hζirr
  rw [hyp.tau_apply_of_mem_typePV hsupp hv hvM]
  -- `ζ` (induced from the normal `M'`) vanishes at `v ∉ M'`, hence so does `ζ̄ = star ∘ ζ`.
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hnotmem : (⟨v, hvM⟩ : ↥M) ∉ (derivedInG M).subgroupOf M := by
    rw [Subgroup.mem_subgroupOf]
    exact OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.typeP hv
  have hζv : ζ ⟨v, hvM⟩ = 0 := by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hnotmem
  rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hζv, star_zero, sub_zero]

open scoped FiniteInduce in
/-- **`(χ − χ̄)^τ` is orthogonal to every aligned `σ`-grid entry** (Peterfalvi (5.3.b),
generalised from `ζ` to any irreducible member of `S`): the difference image vanishes on `V`
(`tau_zeta_sub_conj_vanishes_on_typePV`), lies in `ℤ[Irr G]` with norm `2`, so by the
`(3.7)/(3.8)` all-zero trichotomy (`sigmaCoeff_eq_zero_of_vanishOnV`) every `σ`-coefficient —
in particular every `⟨·, ω_{ik}^σ⟩` — vanishes.  This is the (5.2.e) member-vs-column
orthogonality core (issue 2022). -/
theorem Hypothesis.tau_chidiff_inner_alignedOmega_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {χ : ClassFunction ↥M ℂ}
    (hχS : χ ∈ inducedFamily M) (hχirr : IsIrreducibleCharacter χ)
    (i : Fin hyp.w1) (k : Fin hyp.w2) :
    ClassFunction.inner (hyp.tau (χ - χ.conj))
      (hyp.alignedOmegaSigmaGrid hG hodd i k) = 0 := by
  haveI := hyp.finiteG
  classical
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  -- `T`-facts
  have hχcS : χ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hχS
  have hχcirr : IsIrreducibleCharacter χ.conj := hχirr.conj
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hχne : χ.conj ≠ χ := inducedFamily_hasNoRealCharacters hModd hχS
  have hvanish : ∀ w ∈ tic.V, hyp.tau (χ - χ.conj) w = 0 := fun w hw =>
    hyp.tau_zeta_sub_conj_vanishes_on_typePV hG hodd hχS hχirr hw
  have hsupp := hyp.zeta_sub_conj_support hG hodd hχS hχirr
  have hTZ : hyp.tau (χ - χ.conj) ∈ ZIrr G := by
    refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hyp.hconj hsupp ?_
    exact Submodule.sub_mem _ hχirr.mem_ZIrr hχcirr.mem_ZIrr
  have hT2 : ClassFunction.inner (hyp.tau (χ - χ.conj)) (hyp.tau (χ - χ.conj)) = 2 := by
    have hset : ∀ s ∈ ({χ - χ.conj} : Set (ClassFunction ↥M ℂ)), s.support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := by
      rintro s rfl
      exact hsupp
    have hmem : χ - χ.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
        ({χ - χ.conj} : Set (ClassFunction ↥M ℂ)) := Submodule.subset_span rfl
    have hpres := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
      hyp.dadeData.dade hyp.hconj hset hmem hmem
    rw [show hyp.tau = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) from rfl, hpres,
      ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right]
    have h11 : ClassFunction.inner χ χ = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite
        (⟨χ, hχirr⟩ : IrreducibleCharacter ↥M) ⟨χ, hχirr⟩
    have hcc : ClassFunction.inner χ.conj χ.conj = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite
        (⟨χ.conj, hχcirr⟩ : IrreducibleCharacter ↥M) ⟨χ.conj, hχcirr⟩
    have hcross : ClassFunction.inner χ χ.conj = 0 :=
      inducedFamily_pairwiseOrthogonal hχS hχcS (Ne.symm hχne)
    have hcross' : ClassFunction.inner χ.conj χ = 0 :=
      inducedFamily_pairwiseOrthogonal hχcS hχS hχne
    rw [h11, hcc, hcross, hcross']
    ring
  -- engine + `P`-enumeration
  have hall := tic.sigmaCoeff_eq_zero_of_vanishOnV hVeq app hTZ hT2 hvanish
  obtain ⟨P, hPinj, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  have hk := hall (P k)
  rw [show tic.sigmaCoeff hVeq app (hyp.tau (χ - χ.conj)) (P k)
      = ClassFunction.inner (hyp.tau (χ - χ.conj)) (tic.chiFam hVeq app (P k)) from rfl,
    ← hP k] at hk
  exact hk

/-- **Norm-`1` projection orthogonality.**  If `a, s ∈ ℤ[Irr G]` with `‖a‖² = ‖b‖² = ‖s‖² = 1`,
`a ⊥ b`, and the difference `a − b` is orthogonal to `s`, then `a ⊥ s`.

Since `⟨a,s⟩ = ⟨b,s⟩ =: x ∈ ℤ` (`a, s ∈ ℤ[Irr G]`, `inner_mem_ZIrr_int`), the projection norm
`‖s − x·a − x·b‖² = 1 − 2x² ≥ 0` forces `2x² ≤ 1`, hence `x = 0`.  This is the integral-geometry
core that lets the §10 `ζ^{τ₁}`-vanishing argument bypass the (5.4)/(5.5) `R(ζ)` machinery:
applied with `a = ζ^{τ₁}`, `b = ζ̄^{τ₁}`, `s = ω^σ`, the orthogonality of `(ζ − ζ̄)^τ = a − b` to the
`σ`-image (Peterfalvi (5.3.b), via (3.8)) gives `ζ^{τ₁} ⊥ ω^σ` directly. -/
theorem inner_left_eq_zero_of_inner_sub_eq_zero {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {a b s : ClassFunction G ℂ} (haZ : a ∈ ZIrr G) (hsZ : s ∈ ZIrr G)
    (ha1 : ClassFunction.inner a a = 1) (hb1 : ClassFunction.inner b b = 1)
    (hs1 : ClassFunction.inner s s = 1) (hab : ClassFunction.inner a b = 0)
    (hdiff : ClassFunction.inner (a - b) s = 0) :
    ClassFunction.inner a s = 0 := by
  obtain ⟨x, hx⟩ := ClassFunction.inner_mem_ZIrr_int haZ hsZ
  -- `⟨b,s⟩ = ⟨a,s⟩ = x` from `⟨a − b, s⟩ = 0`.
  have hbs : ClassFunction.inner b s = (x : ℂ) := by
    rw [ClassFunction.inner_sub_left, hx, sub_eq_zero] at hdiff
    exact hdiff.symm
  -- the conjugate-symmetric companions (`x` is real, being an integer).
  have hsa : ClassFunction.inner s a = (x : ℂ) := by
    rw [inner_conj_symm a s, hx, star_intCast]
  have hsb : ClassFunction.inner s b = (x : ℂ) := by
    rw [inner_conj_symm b s, hbs, star_intCast]
  have hba : ClassFunction.inner b a = 0 := by
    rw [inner_conj_symm a b, hab, star_zero]
  -- the projection norm `‖s − x·a − x·b‖² = 1 − 2x²`.
  have key : ClassFunction.inner (s - (x : ℂ) • a - (x : ℂ) • b)
      (s - (x : ℂ) • a - (x : ℂ) • b) = 1 - 2 * (x : ℂ) ^ 2 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      ha1, hb1, hs1, hab, hba, hx, hbs, hsa, hsb, star_intCast]
    ring
  have hnn := inner_self_re_nonneg (s - (x : ℂ) • a - (x : ℂ) • b)
  rw [key] at hnn
  have hcast : (1 : ℂ) - 2 * (x : ℂ) ^ 2 = ((1 - 2 * x ^ 2 : ℤ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.intCast_re] at hnn
  have hint : (0 : ℤ) ≤ 1 - 2 * x ^ 2 := by exact_mod_cast hnn
  have h0 : (0 : ℤ) ≤ x ^ 2 := sq_nonneg x
  have hsq : x ^ 2 = 0 := by omega
  have hx0 : x = 0 := by rw [pow_two] at hsq; exact mul_self_eq_zero.mp hsq
  rw [hx, hx0, Int.cast_zero]

open scoped FiniteInduce in
/-- **Per-element orthogonality of a difference-image family** (Peterfalvi (5.5)-style upgrade):
if `s` is a norm-`1` virtual character orthogonal to the *sum* `(χ−χ̄)^τ = ∑ R(χ)`, then `s` is
orthogonal to each element of `R(χ)`.  With `β := T − α` (the complementary part), `α − (−β) = T`
and the norm-`1` projection lemma applies. -/
theorem OrthonormalCharacterImageFamily.elt_inner_eq_zero {M : Subgroup G} [Finite G]
    [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥M : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G} {χ : ClassFunction ↥M ℂ}
    (R : OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily τ χ)
    {α : ClassFunction G ℂ} (hα : α ∈ R.imageSet)
    {s : ClassFunction G ℂ} (hsZ : s ∈ ZIrr G)
    (hs1 : ClassFunction.inner s s = 1)
    (hT2 : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - χ.conj)) = 2)
    (hTs : ClassFunction.inner (τ (χ - χ.conj)) s = 0) :
    ClassFunction.inner α s = 0 := by
  classical
  set T := τ (χ - χ.conj) with hT
  have hTsum : T = ∑ β ∈ R.imageSet, β := R.image_eq
  have hαZ : α ∈ ZIrr G := R.mem_ZIrr α hα
  have hα1 : ClassFunction.inner α α = 1 := by
    have := R.orthonormal α hα α hα
    rwa [if_pos rfl] at this
  have hTZ : T ∈ ZIrr G := by
    rw [hTsum]
    exact Submodule.sum_mem _ fun β hβ => R.mem_ZIrr β hβ
  have hαT : ClassFunction.inner α T = 1 := by
    rw [hTsum, OddOrder.RepresentationTheory.inner_sum_right, Finset.sum_eq_single α]
    · rw [hα1]
    · intro β hβ hne
      have := R.orthonormal α hα β hβ
      rwa [if_neg (fun h => hne h.symm)] at this
    · intro habs
      exact absurd hα habs
  -- `b := −(T − α)`; then `α − b = T`
  set b : ClassFunction G ℂ := -(T - α) with hb
  have hbZ : b ∈ ZIrr G := by
    rw [hb]
    exact Submodule.neg_mem _ (Submodule.sub_mem _ hTZ hαZ)
  have hbb : ClassFunction.inner b b = 1 := by
    have hexp : ClassFunction.inner (T - α) (T - α)
        = ClassFunction.inner T T - ClassFunction.inner T α
          - ClassFunction.inner α T + ClassFunction.inner α α := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right]
      ring
    have hTα : ClassFunction.inner T α = 1 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hαT]
      norm_num
    rw [hb, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg,
      hexp, hT2, hTα, hαT, hα1]
    ring
  have hαb : ClassFunction.inner α b = 0 := by
    have hTα : ClassFunction.inner α (T - α) = 0 := by
      rw [ClassFunction.inner_sub_right, hαT, hα1]
      ring
    rw [hb, ClassFunction.inner_neg_right, hTα, neg_zero]
  have hdiff : ClassFunction.inner (α - b) s = 0 := by
    have : α - b = T := by
      rw [hb]
      abel
    rw [this]
    exact hTs
  exact inner_left_eq_zero_of_inner_sub_eq_zero hαZ hsZ hα1 hbb hs1 hαb hdiff


open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `ζ^{τ₁}` vanishes on `V`** (the genuine §5/§7 input, the textbook's
"By (5.3.b), (5.5) and (3.2.d), `ζ^{τ₁}` vanishes on `V`").

Reorganized to avoid the (5.4)/(5.5) `R(ζ)`-extraction machinery, using the integral norm-`1`
projection (`inner_left_eq_zero_of_inner_sub_eq_zero`) instead:
* `(ζ − ζ̄)^τ = ζ^{τ₁} − ζ̄^{τ₁}` vanishes on `V` (`tau_zeta_sub_conj_vanishes_on_typePV`) and has
  `NC ≤ 2 < min(w₁, w₂)`: each of `ζ^{τ₁}`, `ζ̄^{τ₁}` is a norm-`1` virtual character with at most
  one nonzero `σ`-coefficient (`ncard_inner_chiFam_ne_zero_le_one`), so by the (3.8) corollary
  `sigmaCoeff_eq_zero_of_sigmaNC_lt` every `σ`-coefficient of `(ζ − ζ̄)^τ` vanishes (Peterfalvi
  (5.3.b));
* `ζ^{τ₁}, ζ̄^{τ₁}` are orthonormal norm-`1` virtual characters (coherence isometry on `ℤ[S]`), so
  the projection lemma upgrades `⟨ζ^{τ₁} − ζ̄^{τ₁}, χ_{pq}⟩ = 0` to `⟨ζ^{τ₁}, χ_{pq}⟩ = 0`
  (Peterfalvi (5.5));
* orthogonality to every `χ_{pq} = ω_{pq}^σ` forces `ζ^{τ₁}` to vanish on `V` (Peterfalvi (3.2.d),
  `eq_zero_of_mem_V_of_inner_chiFam_eq_zero`).

This is the last analytic input of the (10.5) Dade-image identity; with the value-on-`V` leg it
gives `ψ = X − δ(ω^σ diff)` vanishing on `V` (`muGridPsi_vanishes_on_typePV`), unconditionally. -/
theorem Hypothesis.tau1_zeta_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {v : G} (hv : v ∈ typePV M hyp.typeP) :
    coh.tau1 ζ v = 0 := by
  haveI := hyp.finiteG
  classical
  -- the §5 `G`-level TI-cyclic hypothesis + Dade application (the ready (10.5) `σ` pattern).
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    ⟨tic.toDadeHypothesis.fullDadeIsometryData
      (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl))⟩
  have hVeq : tic.V = tic.Vdiff := rfl
  -- `ζ̄ ∈ S` irreducible; the `τ₁`-images are orthonormal norm-`1` virtual characters of `G`.
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have haZ : coh.tau1 ζ ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr ζ (Submodule.subset_span hζS)
  have hbZ : coh.tau1 ζ.conj ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr ζ.conj (Submodule.subset_span hζcS)
  have ha1 : ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ) = 1 :=
    hyp.zeta_tau1_inner_self hG hodd coh hζS hζirr
  have hb1 : ClassFunction.inner (coh.tau1 ζ.conj) (coh.tau1 ζ.conj) = 1 :=
    hyp.zeta_tau1_inner_self hG hodd coh hζcS hζcirr
  have hab : ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ.conj) = 0 := by
    change ClassFunction.inner (coh.coherent.extension ζ) (coh.coherent.extension ζ.conj) = 0
    rw [coh.coherent.extension_inner_eq _ _ (Submodule.subset_span hζS)
        (Submodule.subset_span hζcS),
      OddOrder.RepresentationTheory.irr_cf_inner hζirr hζcirr, if_neg (fun h => hζne h.symm)]
  -- `(ζ − ζ̄)^τ` vanishes on `V`, with `NC ≤ 2 < min(w₁, w₂)`.
  have hvanish : ∀ w ∈ tic.V, hyp.tau (ζ - ζ.conj) w = 0 := fun w hw =>
    hyp.tau_zeta_sub_conj_vanishes_on_typePV hG hodd hζS hζirr hw
  have hNC : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
      < min (Nat.card ↥tic.W1) (Nat.card ↥tic.W2) := by
    have hbound : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj)) ≤ 2 := by
      have hsub : {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0} ⊆
          {pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0} ∪
          {pq | ClassFunction.inner (coh.tau1 ζ.conj) (tic.chiFam hVeq app pq) ≠ 0} := by
        intro pq hpq
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
        apply hpq
        change ClassFunction.inner (hyp.tau (ζ - ζ.conj)) (tic.chiFam hVeq app pq) = 0
        rw [hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr,
          ClassFunction.inner_sub_left, hcon.1, hcon.2, sub_zero]
      calc tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
          = {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0}.ncard := rfl
        _ ≤ ({pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0} ∪
              {pq | ClassFunction.inner (coh.tau1 ζ.conj) (tic.chiFam hVeq app pq) ≠ 0}).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ {pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0}.ncard +
              {pq | ClassFunction.inner (coh.tau1 ζ.conj) (tic.chiFam hVeq app pq) ≠ 0}.ncard :=
            Set.ncard_union_le _ _
        _ ≤ 1 + 1 := by
            gcongr
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app haZ ha1
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app hbZ hb1
        _ = 2 := rfl
    have h3a := tic.three_le_card_W1
    have h3b := tic.three_le_card_W2
    omega
  -- (3.2.d): orthogonality to every `χ_{pq}` forces vanishing on `V`.
  refine tic.eq_zero_of_mem_V_of_inner_chiFam_eq_zero hVeq app (fun a' b' => ?_) hv
  have hL3 : tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) (a', b') = 0 :=
    tic.sigmaCoeff_eq_zero_of_sigmaNC_lt hVeq app hvanish hNC (a', b')
  have hdiff : ClassFunction.inner (coh.tau1 ζ - coh.tau1 ζ.conj)
      (tic.chiFam hVeq app (a', b')) = 0 := by
    rw [← hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr]; exact hL3
  have hsZ : tic.chiFam hVeq app (a', b') ∈ ZIrr G := (tic.chiFam_spec hVeq app).2.1 (a', b')
  have hs1 : ClassFunction.inner (tic.chiFam hVeq app (a', b'))
      (tic.chiFam hVeq app (a', b')) = 1 := by
    rw [(tic.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  exact inner_left_eq_zero_of_inner_sub_eq_zero haZ hsZ ha1 hb1 hs1 hab hdiff

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), Dade-image half (grid level)**: the genuine `μ`-grid statement of the
Dade-image identity, `α_{ij}^τ = δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}`, with `ω^σ` the *aligned*
`σ`-grid `alignedOmegaSigmaGrid` and `α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ`.

This is the full (10.5) endgame.  Writing `X = α_{ij}^τ + n·ζ^{τ₁}`, the goal reduces to
`X = δ·(ω_{ij}^σ − ω_{i0}^σ)`.  Now `X` is a virtual character of `G` with `‖X‖² = 2`
(`muGridAlpha_tau_X_inner`), the aligned `σ`-grid entries are members `χ_{P_{ij}}` of the
orthonormal `σ`-image family (`exists_alignedOmegaSigmaGrid_chiFam_family`), and the difference
`X − δ·(ω_{ij}^σ − ω_{i0}^σ)` vanishes on `V` (`muGridPsi_vanishes_on_typePV` together with the
`ζ^{τ₁}`-vanishing `tau1_zeta_vanishes_on_typePV`).  The norm-`2` Dade-image trichotomy
`eq_smul_chiFam_diff_of_vanishOnV` (the §5 generalisation of the §6 `(4.8)` endgame) then forces
`X = δ·(χ_{P_{ij}} − χ_{P_{i0}})`.  (`alpha_tau_image` is the thin `CharacterParameters` corollary.) -/
theorem Hypothesis.tau_muGridAlpha_eq [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hw1 : 3 ≤ hyp.w1) (hn2 : 2 ≤ n) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - (n : ℂ) • coh.tau1 ζ := by
  haveI := hyp.finiteG
  classical
  -- `X = α_{ij}^τ + n·ζ^{τ₁}` has `‖X‖² = 2` and lies in `ℤ[Irr G]`.
  have hXfacts := hyp.muGridAlpha_tau_X_inner hG hodd i hj0 k hjk hk0 coh hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ hkζ hcol1 hdk1 hδpm hw1 hn2
  have hτ1ζZ : coh.tau1 ζ ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr ζ (Submodule.subset_span hζS)
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  have hXZ : hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      + (n : ℂ) • coh.tau1 ζ ∈ ZIrr G := by
    refine Submodule.add_mem _ hαZ ?_
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hτ1ζZ n
  -- the aligned `σ`-grid entries as `χ`-family members (piece 1).
  obtain ⟨P, hPinj, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  have hPne : P j ≠ P 0 := fun h => hj0 (hPinj h)
  have hPj' : tic.chiFam hVeq app (P j) = hyp.alignedOmegaSigmaGrid hG hodd i j := (hP j).symm
  have hP0' : tic.chiFam hVeq app (P 0) = hyp.alignedOmegaSigmaGrid hG hodd i 0 := (hP 0).symm
  -- `ψ = X − δ·(ω_{ij}^σ − ω_{i0}^σ)` vanishes on `V`.
  have hζvanish : ∀ v ∈ typePV M hyp.typeP, coh.tau1 ζ v = 0 :=
    fun v hv => hyp.tau1_zeta_vanishes_on_typePV hG hodd coh hζS hζirr hζne hv
  have hψV : ∀ v ∈ tic.V,
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.tau1 ζ
        - (δ : ℂ) • (tic.chiFam hVeq app (P j) - tic.chiFam hVeq app (P 0))) v = 0 := by
    intro v hv
    rw [hPj', hP0']
    exact hyp.muGridPsi_vanishes_on_typePV hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj coh hζvanish hv
  -- the norm-`2` Dade-image trichotomy.
  rw [eq_sub_iff_add_eq, ← hPj', ← hP0']
  exact tic.eq_smul_chiFam_diff_of_vanishOnV hVeq app hXZ hXfacts.2 hPne hδpm hψV

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), coherence-free row-difference form**: for nontrivial columns
`j ≠ k` in the same row `i`, `(μ_{ij} − μ_{ik})^τ = δ·(ω_{ij}^σ − ω_{ik}^σ)`.

Unlike `alpha_tau_image` this needs **no** `CoherentHypothesis`: the `n·ζ` legs of the two
`α`'s cancel in the row difference (equal degrees, (10.3) `degree_independent`), so the
`V`-vanishing legs (`tau_muGridAlpha_apply_eq_on_typePV`, coherence-free) subtract to give the
`ψ`-vanishing, and the norm-2 trichotomy engine applies to `X = (μ_{ij} − μ_{ik})^τ` directly.
This is the repo analogue of Coq's coherence-free `FTtypeP_subcoherent` `R`-datum for the
μ-grid (issue 2022, the (5.2.d) reducible-column route). -/
theorem Hypothesis.tau_muGrid_row_diff [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hodd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hodd j = params.delta)
    (i : Fin hyp.w1) {j k : Fin hyp.w2} (hj0 : j ≠ 0) (hk0 : k ≠ 0) (hjk : j ≠ k) :
    hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k)
      = (params.delta : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
          - hyp.alignedOmegaSigmaGrid hG hodd i k) := by
  haveI := hyp.finiteG
  classical
  -- degrees and the `α`-difference identity
  have hdegj : hyp.muGrid hG hodd i j 1 = (params.d : ℂ) := by
    rw [← hmu]; exact params.degree_independent i j hj0
  have hdegk : hyp.muGrid hG hodd i k 1 = (params.d : ℂ) := by
    rw [← hmu]; exact params.degree_independent i k hk0
  have hμ0 : hyp.muGrid hG hodd i 0 1 = 1 := hyp.muGrid_zero_column_apply_one hG hodd i
  have hα : hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k
      = params.alpha i j - params.alpha i k := by
    rw [params.alpha_def, params.alpha_def, hmu]
    abel
  -- `X ∈ ℤ[Irr G]`: the difference is `A₀`-supported and integral
  have hsupp : (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k).support ⊆ hyp.A0 := by
    rw [hα]
    intro x hx
    rw [ClassFunction.mem_support, ClassFunction.sub_apply] at hx
    by_cases h1 : params.alpha i j x = 0
    · refine params.alpha_support i k hk0 ?_
      rw [ClassFunction.mem_support]
      intro h2
      exact hx (by rw [h1, h2, sub_zero])
    · exact params.alpha_support i j hj0 (ClassFunction.mem_support.mpr h1)
  -- `X ∈ ℤ[Irr G]` via the two `α`-legs
  have hXZ : hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k) ∈ ZIrr G := by
    rw [hα, params.alpha_def, params.alpha_def, hmu, map_sub]
    exact Submodule.sub_mem _
      (hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hzS params.zeta_irreducible hdegj hμ0 hz1
        params.n_formula (hδj j hj0))
      (hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hk0 hzS params.zeta_irreducible hdegk hμ0 hz1
        params.n_formula (hδj k hk0))
  -- `‖X‖² = 2`: Dade preserves the inner product on the supported difference
  have hsrc : ClassFunction.inner
      (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k)
      (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k) = 2 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right,
      hyp.muGrid_inner_self hG hodd i j, hyp.muGrid_inner_self hG hodd i k,
      hyp.muGrid_inner_cross_column hG hodd i i hjk,
      hyp.muGrid_inner_cross_column hG hodd i i (Ne.symm hjk)]
    ring
  have hX2 : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k))
      (hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k)) = 2 := by
    have hset : ∀ s ∈ ({hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k} :
        Set (ClassFunction ↥M ℂ)), s.support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := by
      rintro s rfl
      exact hsupp
    have hmem : hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k ∈
        OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
          ({hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k} :
            Set (ClassFunction ↥M ℂ)) :=
      Submodule.subset_span rfl
    have hpres := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
      hyp.dadeData.dade hyp.hconj hset hmem hmem
    rw [show hyp.tau = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) from rfl]
    rw [hpres]
    exact hsrc
  -- the σ-grid enumeration and the trichotomy engine
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  obtain ⟨P, hPinj, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  have hPj' : tic.chiFam hVeq app (P j) = hyp.alignedOmegaSigmaGrid hG hodd i j := (hP j).symm
  have hPk' : tic.chiFam hVeq app (P k) = hyp.alignedOmegaSigmaGrid hG hodd i k := (hP k).symm
  have hPne : P j ≠ P k := fun h => hjk (hPinj h)
  have hψV : ∀ v ∈ tic.V,
      (hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k)
        - (params.delta : ℂ) • (tic.chiFam hVeq app (P j) - tic.chiFam hVeq app (P k))) v
        = 0 := by
    intro v hv
    have hlegj := hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hj0 hzS hdegj hμ0 hz1
      params.n_formula (hδj j hj0) hv
    have hlegk := hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hk0 hzS hdegk hμ0 hz1
      params.n_formula (hδj k hk0) hv
    have hXv : hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k) v
        = ((params.delta : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
            - hyp.alignedOmegaSigmaGrid hG hodd i k)) v := by
      rw [hα, params.alpha_def, params.alpha_def, hmu, map_sub, ClassFunction.sub_apply,
        hlegj, hlegk]
      simp only [ClassFunction.smul_apply, ClassFunction.sub_apply]
      ring
    rw [ClassFunction.sub_apply, hXv, hPj', hPk']
    simp only [ClassFunction.smul_apply, ClassFunction.sub_apply]
    ring
  rw [← hPj', ← hPk']
  exact tic.eq_smul_chiFam_diff_of_vanishOnV hVeq app hXZ hX2 hPne hδpm hψV

open scoped FiniteInduce in
/-- **Column-sum form of `tau_muGrid_row_diff`** (coherence-free (10.5) for columns):
`(μ_j − μ_k)^τ = δ·(∑ω_{ij}^σ − ∑ω_{ik}^σ)` for nontrivial columns `j ≠ k`. -/
theorem Hypothesis.tau_muGrid_columnSum_diff_cohFree [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hodd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hodd j = params.delta)
    {j k : Fin hyp.w2} (hj0 : j ≠ 0) (hk0 : k ≠ 0) (hjk : j ≠ k) :
    hyp.tau (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j
        - ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) =
      (params.delta : ℂ) • (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j
        - ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i k) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    hyp.tau_muGrid_row_diff hG hodd hmu hzS hz1 hδpm hδj i hj0 hk0 hjk

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), Dade-image half** (`CharacterParameters` corollary).  For the (10.2)/(10.3)
character data — the `μ`-grid (`hmu`), the aligned `σ`-grid (`hos`), the degree-`w₁` irreducible `ζ`
of (10.2) (`hzS`/`hz1`) and the column sign `δ = ±1` (`hδpm`/`hδj`) — the Dade image of
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` is `δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}`.

Thin corollary of the grid identity `tau_muGridAlpha_eq`.  All arithmetic inputs are discharged from
the (10.3) data carried by `CharacterParameters` (`degree_independent`, `n_formula`, `d_gt_one`,
`two_le_n`) and the structural bounds `w₁, w₂ ≥ 3` (`three_le_card_W1/W2`): the auxiliary nontrivial
column `k ≠ j`, the degree distinctness `d ≠ w₁`/`1 ≠ w₁`, and the parity `n ≥ 2` (Peterfalvi (10.3),
now `params.two_le_n`).  The only hypotheses beyond the (10.2)/(10.3) construction pins are `hzconj`
— the non-realness `ζ̄ ≠ ζ` (Peterfalvi (1.1): a nontrivial irreducible of an odd-order group is not
real; carried per the §10 (10.5) chain convention, derivable via
`not_isReal_of_ne_trivial_of_odd_card'`). -/
theorem alpha_tau_image [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 →
        hyp.tau (params.alpha i j) =
          (params.delta : ℂ) • (params.omegaSigma i j - params.omegaSigma i 0)
            - (params.n : ℂ) • coh.tau1 params.zeta := by
  haveI := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  have hn2 : 2 ≤ params.n := params.two_le_n
  -- structural bounds `w₁, w₂ ≥ 3` from the §10 TI-cyclic hypothesis.
  have hw1 : 3 ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  have hw2 : 3 ≤ hyp.w2 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W2
  intro i j hj0
  -- choose an auxiliary nontrivial column `k ≠ j` (possible as `w₂ ≥ 3`).
  obtain ⟨k, hjk, hk0⟩ : ∃ k : Fin hyp.w2, j ≠ k ∧ k ≠ 0 := by
    have h1lt : 1 < hyp.w2 := by omega
    have h2lt : 2 < hyp.w2 := by omega
    by_cases h : j = ⟨1, h1lt⟩
    · exact ⟨⟨2, h2lt⟩, by rw [h]; exact Fin.ne_of_val_ne (by simp),
        Fin.ne_of_val_ne (by simp)⟩
    · exact ⟨⟨1, h1lt⟩, h, Fin.ne_of_val_ne (by simp)⟩
  -- (10.3) degree facts on the `μ`-grid.
  have hdeg : hyp.muGrid hG hodd i j 1 = (params.d : ℂ) := by
    rw [← hmu]; exact params.degree_independent i j hj0
  have hμ0 : hyp.muGrid hG hodd i 0 1 = 1 := hyp.muGrid_zero_column_apply_one hG hodd i
  have hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (params.d : ℂ) := fun i' => by
    rw [← hmu]; exact params.degree_independent i' k hk0
  have hd1 : params.d ≠ 1 := by have := params.d_gt_one; omega
  have hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1 := by rw [hcol1 0]; exact_mod_cast hd1
  -- `d ≠ w₁` from `d = n·w₁ + δ`, `n ≥ 2`, `w₁ ≥ 3`, `δ = ±1`.
  have hdw1 : params.d ≠ hyp.w1 := by
    have hf : (params.d : ℤ) = (params.n : ℤ) * (hyp.w1 : ℤ) + params.delta := by
      linarith [params.n_formula]
    have hn2Z : (2 : ℤ) ≤ (params.n : ℤ) := by exact_mod_cast hn2
    have hw1Z : (3 : ℤ) ≤ (hyp.w1 : ℤ) := by exact_mod_cast hw1
    intro he
    have heZ : (params.d : ℤ) = (hyp.w1 : ℤ) := by exact_mod_cast he
    rcases hδpm with h | h <;> rw [h] at hf <;> nlinarith [hf, heZ, hn2Z, hw1Z]
  have hdζ : hyp.muGrid hG hodd i j 1 ≠ params.zeta 1 := by
    rw [hdeg, hz1]; exact_mod_cast hdw1
  have h0ζ : hyp.muGrid hG hodd i 0 1 ≠ params.zeta 1 := by
    rw [hμ0, hz1]; intro he; have : hyp.w1 = 1 := by exact_mod_cast he.symm
    omega
  have hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ params.zeta 1 := fun i' => by
    rw [hcol1 i', hz1]; exact_mod_cast hdw1
  -- discharge via the grid identity `tau_muGridAlpha_eq`.
  rw [params.alpha_def, hmu, hos]
  exact hyp.tau_muGridAlpha_eq hG hodd i hj0 k hjk hk0 coh hzS params.zeta_irreducible hzconj
    hdeg hμ0 hz1 params.n_formula (hδj j hj0) hdζ h0ζ hkζ hcol1 hdk1 hδpm hw1 hn2

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(a) reduction**: `(ω_{ij}^σ − ω_{i0}^σ, μ_j^{τ₁}) = δ` for `0 < j < w₂`.

This is the inner-product identity opening the (10.6)(a) proof:
`1 = (α_{ij}, μ_j − dζ̄) = (α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁}) = (δ(ω_{ij}^σ − ω_{i0}^σ), μ_j^{τ₁})`.
From the diagonal reduction `(α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁}) = 1`
(`muGridAlpha_tau1_inner_muColumn_self_sub_conj`), the vanishing `(α_{ij}^τ, ζ̄^{τ₁}) = 0`
(from `(α_{ij}^τ, ζ^{τ₁}) = −n` (`muGridAlpha_tau1_zeta_eq_neg_n`, the (10.5) `a = 0`) and
`(α_{ij}^τ, ζ̄^{τ₁}) = (α_{ij}^τ, ζ^{τ₁}) + n` (`muGridAlpha_tau_inner_zeta_sub_conj`)), the (10.5)
Dade image `α_{ij}^τ = δ(ω_{ij}^σ − ω_{i0}^σ) − nζ^{τ₁}` (`alpha_tau_image`) and `(ζ^{τ₁}, μ_j^{τ₁}) = 0`
(`zeta_tau1_inner_muColumn`): `1 = (α_{ij}^τ, μ_j^{τ₁}) = δ(ω_{ij}^σ − ω_{i0}^σ, μ_j^{τ₁})`, hence
`(ω_{ij}^σ − ω_{i0}^σ, μ_j^{τ₁}) = δ` (`δ² = 1`).  This pins the `j`-column coefficient of
`μ_j^{τ₁}` along `ω_{ij}^σ` to `δ` for every `i`, which together with `‖μ_j^{τ₁}‖² = w₁` forces the
(10.6)(a) summed isometry `μ_j^{τ₁} = δ∑_i ω_{ij}^σ` (see `muColumn_tau1_pin`).  Crucially this
specialised reduction avoids Peterfalvi's general (5.8) machinery (separability / `σ`-coefficients):
the diagonal inner product `= 1` directly determines the `j`-column. -/
theorem Hypothesis.omegaSigmaDiff_inner_muColumn_tau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j : Fin hyp.w2} (hj0 : j ≠ 0) (i : Fin hyp.w1) :
    ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j
        - hyp.alignedOmegaSigmaGrid hG hG.odd i 0)
        (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' j)) = (params.delta : ℂ) := by
  haveI := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  -- discharge the standard (10.3) degree/parity hypotheses (cf. `alpha_tau_image`).
  have hn2 : 2 ≤ params.n := params.two_le_n
  have hw1 : 3 ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  have hw2 : 3 ≤ hyp.w2 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W2
  obtain ⟨k, hjk, hk0⟩ : ∃ k : Fin hyp.w2, j ≠ k ∧ k ≠ 0 := by
    have h1lt : 1 < hyp.w2 := by omega
    have h2lt : 2 < hyp.w2 := by omega
    by_cases h : j = ⟨1, h1lt⟩
    · exact ⟨⟨2, h2lt⟩, by rw [h]; exact Fin.ne_of_val_ne (by simp), Fin.ne_of_val_ne (by simp)⟩
    · exact ⟨⟨1, h1lt⟩, h, Fin.ne_of_val_ne (by simp)⟩
  have hdeg : hyp.muGrid hG hodd i j 1 = (params.d : ℂ) := by
    rw [← hmu]; exact params.degree_independent i j hj0
  have hμ0 : hyp.muGrid hG hodd i 0 1 = 1 := hyp.muGrid_zero_column_apply_one hG hodd i
  have hcolj : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 = (params.d : ℂ) := fun i' => by
    rw [← hmu]; exact params.degree_independent i' j hj0
  have hcolk : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (params.d : ℂ) := fun i' => by
    rw [← hmu]; exact params.degree_independent i' k hk0
  have hd1 : params.d ≠ 1 := by have := params.d_gt_one; omega
  have hdj1 : hyp.muGrid hG hodd 0 j 1 ≠ 1 := by rw [hcolj 0]; exact_mod_cast hd1
  have hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1 := by rw [hcolk 0]; exact_mod_cast hd1
  have hdw1 : params.d ≠ hyp.w1 := by
    have hf : (params.d : ℤ) = (params.n : ℤ) * (hyp.w1 : ℤ) + params.delta := by
      linarith [params.n_formula]
    have hn2Z : (2 : ℤ) ≤ (params.n : ℤ) := by exact_mod_cast hn2
    have hw1Z : (3 : ℤ) ≤ (hyp.w1 : ℤ) := by exact_mod_cast hw1
    intro he
    have heZ : (params.d : ℤ) = (hyp.w1 : ℤ) := by exact_mod_cast he
    rcases hδpm with h | h <;> rw [h] at hf <;> nlinarith [hf, heZ, hn2Z, hw1Z]
  have hdζ : hyp.muGrid hG hodd i j 1 ≠ params.zeta 1 := by rw [hdeg, hz1]; exact_mod_cast hdw1
  have h0ζ : hyp.muGrid hG hodd i 0 1 ≠ params.zeta 1 := by
    rw [hμ0, hz1]; intro he; have : hyp.w1 = 1 := by exact_mod_cast he.symm
    omega
  have hjζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 ≠ params.zeta 1 := fun i' => by
    rw [hcolj i', hz1]; exact_mod_cast hdw1
  have hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ params.zeta 1 := fun i' => by
    rw [hcolk i', hz1]; exact_mod_cast hdw1
  have hζirr := params.zeta_irreducible
  have hδjj := hδj j hj0
  -- (1) the diagonal reduction `(α^τ, μ_j^{τ₁} − dζ̄^{τ₁}) = 1`.
  have hdiag := hyp.muGridAlpha_tau1_inner_muColumn_self_sub_conj hG hodd i hj0 coh hzS hζirr
    hzconj hdeg hμ0 hz1 params.n_formula hδjj h0ζ hjζ hcolj hdj1
  -- (2) `(α^τ, ζ^{τ₁}) = −n` (the (10.5) `a = 0`).
  have haζ := hyp.muGridAlpha_tau1_zeta_eq_neg_n hG hodd i hj0 k hjk hk0 coh hzS hζirr hzconj
    hdeg hμ0 hz1 params.n_formula hδjj hdζ h0ζ hkζ hcolk hdk1 hδpm hw1 hn2
  -- (3) `(α^τ, ζ^{τ₁}) − (α^τ, ζ̄^{τ₁}) = −n`, hence `(α^τ, ζ̄^{τ₁}) = 0`.
  have hzsc := hyp.muGridAlpha_tau_inner_zeta_sub_conj hG hodd i hj0 hzS hζirr hzconj
    hdeg hμ0 hz1 params.n_formula hδjj hdζ h0ζ
  rw [hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hzS hζirr, ClassFunction.inner_sub_right] at hzsc
  have haζbar : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (params.delta : ℂ) • hyp.muGrid hG hodd i 0
        - (params.n : ℂ) • params.zeta)) (coh.tau1 params.zeta.conj) = 0 := by
    linear_combination haζ - hzsc
  -- (4) `(α^τ, μ_j^{τ₁}) = 1`.
  rw [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right, haζbar,
    mul_zero, sub_zero] at hdiag
  -- (5) substitute the (10.5) Dade image and drop the `ζ^{τ₁}` term (`(ζ^{τ₁}, μ_j^{τ₁}) = 0`).
  have hαimg := alpha_tau_image hG coh hmu hos hzS hz1 hzconj hδpm hδj i j hj0
  rw [params.alpha_def, hmu, hos] at hαimg
  have hζμ := hyp.zeta_tau1_inner_muColumn hG hodd j coh hzS hζirr hjζ hdj1
  rw [hαimg, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    ClassFunction.inner_smul_left, hζμ, mul_zero, sub_zero] at hdiag
  -- `δ · (ω_{ij}^σ − ω_{i0}^σ, μ_j^{τ₁}) = 1`, so the inner product is `δ` (`δ² = 1`).
  have hδsq : (params.delta : ℂ) * (params.delta : ℂ) = 1 := by
    rcases hδpm with h | h <;> rw [h] <;> norm_num
  calc ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j
          - hyp.alignedOmegaSigmaGrid hG hG.odd i 0)
        (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' j))
      = (params.delta : ℂ) * ((params.delta : ℂ) * ClassFunction.inner
          (hyp.alignedOmegaSigmaGrid hG hG.odd i j - hyp.alignedOmegaSigmaGrid hG hG.odd i 0)
          (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' j))) := by
        rw [← mul_assoc, hδsq, one_mul]
    _ = (params.delta : ℂ) * 1 := by rw [hdiag]
    _ = (params.delta : ℂ) := mul_one _

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), column difference (per row)**: for two nontrivial columns `j, k ≠ 0`, the
Dade image of the difference `μ_{ij} − μ_{ik}` of certain-type characters is
`δ·(ω_{ij}^σ − ω_{ik}^σ)`.

The `−δ·μ_{i0} − n·ζ` tails of `α_{ij}` and `α_{ik}` are identical, so `μ_{ij} − μ_{ik} =
α_{ij} − α_{ik}`, and applying `alpha_tau_image` to both columns the `−n·ζ^{τ₁}` parts cancel.  This
is the per-row ingredient of the column image-family `image_eq` (the §10 analogue of the Peterfalvi
(4.9) summed Dade identity), feeding the (5.5)-for-columns route to (10.6)(a). -/
theorem tau_muGrid_column_diff [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (i : Fin hyp.w1) {j k : Fin hyp.w2} (hj0 : j ≠ 0) (hk0 : k ≠ 0) :
    hyp.tau (hyp.muGrid hG hG.odd i j - hyp.muGrid hG hG.odd i k) =
      (params.delta : ℂ) • (hyp.alignedOmegaSigmaGrid hG hG.odd i j
        - hyp.alignedOmegaSigmaGrid hG hG.odd i k) := by
  have hatj := alpha_tau_image hG coh hmu hos hzS hz1 hzconj hδpm hδj i j hj0
  have hatk := alpha_tau_image hG coh hmu hos hzS hz1 hzconj hδpm hδj i k hk0
  have halpha : hyp.muGrid hG hG.odd i j - hyp.muGrid hG hG.odd i k
      = params.alpha i j - params.alpha i k := by
    rw [params.alpha_def, params.alpha_def, hmu]; abel
  rw [halpha, map_sub, hatj, hatk, hos]
  simp only [smul_sub]; abel

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), column-sum difference**: summing `tau_muGrid_column_diff` over the rows
`0 ≤ i < w₁`, the Dade image of the difference of the two column characters `μ_j = ∑_i μ_{ij}` and
`μ_k = ∑_i μ_{ik}` (`j, k ≠ 0`) is `δ·(∑_i ω_{ij}^σ − ∑_i ω_{ik}^σ)`.

This is the §10 analogue of the Peterfalvi (4.9) summed Dade identity: it computes
`(μ_j − μ_k)^τ = ∑_{α ∈ R} α` over the signed `σ`-image family
`R = {δ·ω_{ij}^σ} ∪ {−δ·ω_{ik}^σ}`, the `image_eq` field of the column image family used by the
(5.5)-for-columns route to (10.6)(a). -/
theorem tau_muGrid_columnSum_diff [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j k : Fin hyp.w2} (hj0 : j ≠ 0) (hk0 : k ≠ 0) :
    hyp.tau (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j
        - ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k) =
      (params.delta : ℂ) • (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i j
        - ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i k) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    tau_muGrid_column_diff hG coh hmu hos hzS hz1 hzconj hδpm hδj i hj0 hk0

open scoped FiniteInduce in
/-- **Peterfalvi (5.8)/(10.6)(a), `μ_k^{τ₁}` vanishes on `V`**: the coherent image of the column
character `μ_k = ∑_i μ_{ik}` (`k ≠ 0`) vanishes on `V = typePV`.  This is the "vanishes on `V`"
hypothesis of the (5.8) `σ`-coefficient full-column endgame `eq_smul_chiFam_column_of_vanishOnV`.

Running Peterfalvi's (5.8) argument with `χ = ζ̄` (a degree-`w₁` irreducible of `S ∩ Irr(L)`, the
conjugate of `ζ`): by (4.7) the combination `μ_k − dζ̄` is `A_0(M)`-supported
(`muColumn_sub_conj_support`), so the Dade isometry restores its value on `V`
(`tau_apply_of_mem_typePV`); both `μ_k` and `ζ̄` (induced from the normal `M'`) vanish at `v ∉ M'`
(`typePData_typePV_not_mem_derived`), giving `(μ_k − dζ̄)^τ(v) = 0`.  Splitting
`(μ_k − dζ̄)^τ = μ_k^{τ₁} − dζ̄^{τ₁}` (`tau_muColumn_sub_conj_eq_tau1`) and discharging the
already-established `ζ̄^{τ₁}`-vanishing (`tau1_zeta_vanishes_on_typePV` for `ζ̄`) forces
`μ_k^{τ₁}(v) = 0`.

Crucially this route avoids the `ζ̄^{τ₁} ⊥ Im σ` (§5 (5.3.b)/(5.5)) input that the direct (10.6)(a)
reduction would require: the `(5.5)`-for-columns decomposition determines `μ_k^{τ₁}` directly, and
its vanishing on `V` uses only the (already-honest) single-character `ζ̄^{τ₁}`-vanishing plus (4.7). -/
theorem Hypothesis.muColumn_tau1_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (k : Fin hyp.w2) {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} (hcol1 : ∀ i, hyp.muGrid hG hodd i k 1 = (d : ℂ))
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1)
    {v : G} (hv : v ∈ typePV M hyp.typeP) :
    coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) v = 0 := by
  haveI := hyp.finiteG
  classical
  have hvM : v ∈ M := typePData_W_le_self hyp.typeP (SetLike.mem_coe.mp hv.1)
  -- `(μ_k − dζ̄)^τ(v) = 0`: `A_0`-supported (4.7), and `μ_k`, `ζ̄` vanish at `v ∉ M'`.
  have hsupp := hyp.muColumn_sub_conj_support hG hodd k hζS hζirr hcol1 hζ1
  have hτvan : hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • ζ.conj) v = 0 := by
    rw [hyp.tau_apply_of_mem_typePV hsupp hv hvM]
    obtain ⟨θ, _hθne, hζeq⟩ := hζS
    have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
    have hnotmem : (⟨v, hvM⟩ : ↥M) ∉ (derivedInG M).subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]
      exact OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.typeP hv
    have hμv : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) ⟨v, hvM⟩ = 0 :=
      hyp.muGrid_column_sum_vanishes_off_derived hG hodd k hnotmem
    have hζv : ζ ⟨v, hvM⟩ = 0 := by
      rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hnotmem
    simp only [ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.conj_apply, hμv,
      hζv, star_zero, mul_zero, sub_zero]
  -- split `(μ_k − dζ̄)^τ = μ_k^{τ₁} − dζ̄^{τ₁}` and discharge `ζ̄^{τ₁}(v) = 0`.
  rw [hyp.tau_muColumn_sub_conj_eq_tau1 hG hodd k coh hζS hζirr hcol1 hζ1 hdk1] at hτvan
  have hζcvan : coh.tau1 ζ.conj v = 0 := by
    have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
    have hζcne : ζ.conj.conj ≠ ζ.conj := by
      intro h; rw [ClassFunction.conj_conj] at h; exact hζne h.symm
    exact hyp.tau1_zeta_vanishes_on_typePV hG hodd coh hζcS hζirr.conj hζcne hv
  simp only [ClassFunction.sub_apply, ClassFunction.smul_apply, hζcvan, mul_zero,
    sub_zero] at hτvan
  exact hτvan

open scoped FiniteInduce in
/-- **§10 conjugate column** (Peterfalvi (4.9)(a) at §10): for a nontrivial column `j ≠ 0`, the
complex conjugate of the column character `μ_j = ∑_i μ_{ij}` is another nontrivial column
`μ_{j'} = ∑_i μ_{ij'}` with `j' ≠ 0` and `j' ≠ j` (`j'` is the column of `χ₂⁻¹`).

Reduces to the §6 `certainType_columnSum_conj` (`μ̄_j = ∑_i μ_{i,χ₂⁻¹}`), which (issue 1010, HUB) is
now stated on the structural `Hypothesis ↥M`, hence applies to the §10 muGrid host
`(hyp.toCertainTypeHypothesis hG hodd).toHypothesis`.  The `muGrid ↔ columnFamily` row reindexing
gives `∑_i μ_{ij} = ∑_{i'} (h.columnFamily (χ₂ j)).mu i'`; complex conjugation (`ClassFunction.conj`
= `mapRingEquiv conj` pointwise) sends it to the `χ₂⁻¹`-column.  `j' ≠ 0` from
`finCardEquivCharacterGroup_zero` (the column-`0` dual is trivial) and `j' ≠ j` from the odd order of
the column character group (`W_odd`/`card_charGroup_W2`, no involutions; the `column_inv_ne_self`
argument inlined).  This is the conjugate-column input `(μ_j)‾ = μ_{j'}` for the (5.5)-for-columns
route to (10.6)(a): `tau_muGrid_columnSum_diff` (with `k = j'`) then supplies the column
`OrthonormalCharacterImageFamily.image_eq` field `τ(μ_j − μ̄_j) = ∑ R(μ_j)`. -/
theorem Hypothesis.exists_conj_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {j : Fin hyp.w2} (hj0 : j ≠ 0) :
    ∃ j' : Fin hyp.w2, j' ≠ 0 ∧ j' ≠ j ∧
      (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j).conj
        = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j' := by
  haveI := hyp.finiteG
  haveI : Finite ↥M := inferInstance
  classical
  -- reconstruct the §6 structural host (as in `muGrid`)
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
  -- the column character as a function of the index
  let χ₂ : Fin hyp.w2 → ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
    fun jj => finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm jj)
  -- the `muGrid ↔ columnFamily` row-reindexing bridge
  have hbridge : ∀ jj : Fin hyp.w2,
      ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i jj
        = ∑ i' : Fin (Nat.card h.W1), ((h.columnFamily (χ₂ jj)).mu i' : ClassFunction ↥M ℂ) := by
    intro jj
    rw [← Equiv.sum_comp (finCongr hcardW1.symm)
      (fun i' => ((h.columnFamily (χ₂ jj)).mu i' : ClassFunction ↥M ℂ))]
    exact Finset.sum_congr rfl (fun i _ => by unfold Hypothesis.muGrid; rfl)
  -- `ClassFunction.conj = mapRingEquiv conj` pointwise
  have hconjbridge : ∀ X : ClassFunction ↥M ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  -- `χ₂` injective; `χ₂ jj = 1 ↔ jj = 0`
  have hχ₂inj : Function.Injective χ₂ := fun a b hab =>
    (finCongr hcardW2sub.symm).injective ((finCardEquivCharacterGroup _).injective hab)
  have hχ₂one : ∀ jj : Fin hyp.w2, χ₂ jj = 1 ↔ jj = 0 := by
    intro jj
    rw [show (1 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
        = finCardEquivCharacterGroup _ 0 from (finCardEquivCharacterGroup_zero _).symm,
      (finCardEquivCharacterGroup _).injective.eq_iff]
    constructor
    · intro he; exact (finCongr hcardW2sub.symm).injective (by rw [he]; simp)
    · intro he; subst he; simp
  -- the conjugate-column index `j'` with `χ₂ j' = (χ₂ j)⁻¹`
  let j' : Fin hyp.w2 :=
    (finCongr hcardW2sub.symm).symm ((finCardEquivCharacterGroup _).symm (χ₂ j)⁻¹)
  have hj'χ : χ₂ j' = (χ₂ j)⁻¹ := by simp only [χ₂, j', Equiv.apply_symm_apply]
  have hχ₂jne : χ₂ j ≠ 1 := fun he => hj0 ((hχ₂one j).mp he)
  -- `(χ₂ j)⁻¹ ≠ χ₂ j` (column char group has odd order — no involutions; `column_inv_ne_self` inline)
  have hinvne : (χ₂ j)⁻¹ ≠ χ₂ j := by
    have hodd' : Odd (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)) := by
      rw [h.card_charGroup_W2]
      exact h.W_odd.of_dvd_nat (Subgroup.card_dvd_of_le le_sup_right)
    intro heq
    apply hχ₂jne
    have hsq : (χ₂ j) ^ 2 = 1 := by
      have hm := mul_inv_cancel (χ₂ j); rw [heq] at hm; rwa [pow_two]
    have hcardodd : Odd (orderOf (χ₂ j)) := hodd'.of_dvd_nat (orderOf_dvd_natCard (χ₂ j))
    have h1 : orderOf (χ₂ j) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq) with h2 | h2
      · exact h2
      · exact absurd (h2 ▸ hcardodd) (by decide)
    exact orderOf_eq_one_iff.mp h1
  refine ⟨j', ?_, ?_, ?_⟩
  · -- `j' ≠ 0`
    intro he
    exact hχ₂jne (inv_eq_one.mp (hj'χ ▸ (hχ₂one j').mpr he))
  · -- `j' ≠ j`
    intro he
    exact hinvne (hj'χ ▸ (congrArg χ₂ he))
  · -- the conjugate identity, via the generalized §6 `certainType_columnSum_conj`
    rw [hbridge j, hbridge j', hconjbridge,
      OddOrder.Peterfalvi.S06.certainType_columnSum_conj h (χ₂ j), hj'χ]

/-- **§10 `R(μ_j)` member family** (Peterfalvi (5.3.b) at §10).  Indexed by `Bool × Fin w₁`:
`(false, i) ↦ δ·ω_{ij}^σ`, `(true, i) ↦ −δ·ω_{ij'}^σ` (sign `δ = params.delta`, columns `j`, `j'`).
Its image is the orthonormal difference-image family `R(μ_j)` of the column
`OrthonormalCharacterImageFamily`. -/
noncomputable def Hypothesis.columnRImage [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (δ : ℤ) (j j' : Fin hyp.w2) :
    Bool × Fin hyp.w1 → ClassFunction G ℂ
  | (false, i) => (δ : ℂ) • hyp.alignedOmegaSigmaGrid hG hodd i j
  | (true, i) => (-(δ : ℂ)) • hyp.alignedOmegaSigmaGrid hG hodd i j'

open scoped FiniteInduce in
/-- **Orthonormality of `R(μ_j)`** at §10: the signed σ-image family `columnRImage` is orthonormal,
`⟨R p, R q⟩ = δ_{p,q}`.  The sign `δ = ±1` gives `δ·δ̄ = 1`, the σ-grid orthonormality
`alignedOmegaSigmaGrid_inner` supplies `⟨ω_{ij}^σ, ω_{i'j'}^σ⟩ = [i=i' ∧ j=j']`, and the two halves
(`j ≠ j'`) are cross-orthogonal. -/
theorem Hypothesis.columnRImage_inner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    {j j' : Fin hyp.w2} (hjj' : j ≠ j') (p q : Bool × Fin hyp.w1) :
    ClassFunction.inner (hyp.columnRImage hG hodd δ j j' p) (hyp.columnRImage hG hodd δ j j' q)
      = if p = q then (1 : ℂ) else 0 := by
  have hδstar : star ((δ : ℂ)) = (δ : ℂ) := by rcases hδ with h | h <;> rw [h] <;> norm_num
  have hδsq : (δ : ℂ) * (δ : ℂ) = 1 := by rcases hδ with h | h <;> rw [h] <;> norm_num
  obtain ⟨bp, ip⟩ := p
  obtain ⟨bq, iq⟩ := q
  cases bp <;> cases bq <;>
    simp only [Hypothesis.columnRImage, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hyp.alignedOmegaSigmaGrid_inner hG hodd,
      hδstar, star_neg, mul_neg, neg_mul, neg_neg, Prod.mk.injEq, reduceCtorEq, false_and,
      true_and, and_true, eq_self_iff_true, ↓reduceIte]
  · -- (false,false): same column `j`, `δ²·[ip=iq] = [ip=iq]`
    rw [← mul_assoc, hδsq, one_mul]
  · -- (false,true): cross column `j ≠ j'`
    rw [if_neg (fun hcon => hjj' hcon.2)]; ring
  · -- (true,false): cross column `j' ≠ j`
    rw [if_neg (fun hcon => hjj' hcon.2.symm)]; ring
  · -- (true,true): same column `j'`, `δ²·[ip=iq] = [ip=iq]`
    rw [← mul_assoc, hδsq, one_mul]

open scoped FiniteInduce in
/-- `R(μ_j)` is injective on `Bool × Fin w₁` (distinct orthonormal vectors are distinct). -/
theorem Hypothesis.columnRImage_injective [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    {j j' : Fin hyp.w2} (hjj' : j ≠ j') :
    Function.Injective (hyp.columnRImage hG hodd δ j j') := by
  intro p q hpq
  by_contra hpqne
  have h0 := hyp.columnRImage_inner hG hodd hδ hjj' p q
  rw [if_neg hpqne, hpq, hyp.columnRImage_inner hG hodd hδ hjj', if_pos rfl] at h0
  exact one_ne_zero h0

open scoped FiniteInduce in
/-- The sum of the §10 `R(μ_j)` family over `Bool × Fin w₁` is `δ·∑_i (ω_{ij}^σ − ω_{ij'}^σ)`, the
image side of the (10.6)(a) summed isometry (`tau_muGrid_columnSum_diff`). -/
theorem Hypothesis.columnRImage_sum [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (δ : ℤ) (j j' : Fin hyp.w2) :
    ∑ p : Bool × Fin hyp.w1, hyp.columnRImage hG hodd δ j j' p
      = (δ : ℂ) • ∑ i : Fin hyp.w1, (hyp.alignedOmegaSigmaGrid hG hodd i j
          - hyp.alignedOmegaSigmaGrid hG hodd i j') := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, Finset.smul_sum]
  simp only [Hypothesis.columnRImage, neg_smul, smul_sub]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by abel)

open scoped Classical FiniteInduce in
/-- **§10 column `OrthonormalCharacterImageFamily`** (Peterfalvi (5.2.d) for the reducible column
`μ_j`): the difference-image family `R(μ_j) = {δ·ω_{ij}^σ} ∪ {−δ·ω_{ij'}^σ}` of the column character
`μ_j = ∑_i μ_{ij}` against the §10 Dade isometry `hyp.tau`.  This is the §10 analogue of the §6
`certainTypeR`, built directly on `hyp.tau` (an `IntegralCharacterMap`) instead of the §6 Dade map.

The `image_eq` field `hyp.tau(μ_j − μ̄_j) = ∑ R(μ_j)` combines the conjugate-column identity
`μ̄_j = μ_{j'}` (`hconj`, from `exists_conj_column`), the (10.5) summed isometry
`tau_muGrid_columnSum_diff` (`hyp.tau(μ_j − μ_{j'}) = δ(∑ω_{ij}^σ − ∑ω_{ij'}^σ)`), and
`columnRImage_sum`; `orthonormal`/`mem_ZIrr` come from `columnRImage_inner`/`_injective` and
`alignedOmegaSigmaGrid_mem_ZIrr`.  Feeding `ofProjection` (with `coh.tau1`, ψ = 0), the (5.5)
`eq_sum_of_psi_eq_zero` then computes `μ_j^{τ₁} = ∑_{E ⊆ R(μ_j)} α`. -/
noncomputable def Hypothesis.columnImageFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j j' : Fin hyp.w2} (hj0 : j ≠ 0) (hj'0 : j' ≠ 0) (hjj' : j ≠ j')
    (hconj : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j).conj
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j') :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.tau
      (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) where
  imageSet := Finset.univ.image (hyp.columnRImage hG hG.odd params.delta j j')
  mem_ZIrr := by
    intro α hα
    rw [Finset.mem_image] at hα
    obtain ⟨⟨b, i⟩, _, rfl⟩ := hα
    cases b
    · simp only [Hypothesis.columnRImage]
      rw [Int.cast_smul_eq_zsmul]
      exact (ZIrr G).smul_mem _ (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i j)
    · simp only [Hypothesis.columnRImage]
      rw [neg_smul, Int.cast_smul_eq_zsmul]
      exact neg_mem ((ZIrr G).smul_mem _ (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i j'))
  orthonormal := by
    intro α hα β hβ
    rw [Finset.mem_image] at hα hβ
    obtain ⟨p, _, rfl⟩ := hα
    obtain ⟨q, _, rfl⟩ := hβ
    rw [hyp.columnRImage_inner hG hG.odd hδpm hjj']
    by_cases hpq : p = q
    · subst hpq; simp
    · rw [if_neg hpq,
        if_neg (fun he => hpq (hyp.columnRImage_injective hG hG.odd hδpm hjj' he))]
  image_eq := by
    rw [hconj, tau_muGrid_columnSum_diff hG coh hmu hos hzS hz1 hzconj hδpm hδj hj0 hj'0,
      Finset.sum_image (fun p _ q _ hpq => hyp.columnRImage_injective hG hG.odd hδpm hjj' hpq),
      hyp.columnRImage_sum, Finset.sum_sub_distrib]


open scoped Classical FiniteInduce in
/-- **§10 column `OrthonormalCharacterImageFamily`, coherence-free** ((5.2.d) for the reducible column
`μ_j`): the difference-image family `R(μ_j) = {δ·ω_{ij}^σ} ∪ {−δ·ω_{ij'}^σ}` of the column character
`μ_j = ∑_i μ_{ij}` against the §10 Dade isometry `hyp.tau`.  This is the §10 analogue of the §6
`certainTypeR`, built directly on `hyp.tau` (an `IntegralCharacterMap`) instead of the §6 Dade map.

The `image_eq` field `hyp.tau(μ_j − μ̄_j) = ∑ R(μ_j)` combines the conjugate-column identity
`μ̄_j = μ_{j'}` (`hconj`, from `exists_conj_column`), the (10.5) summed isometry
`tau_muGrid_columnSum_diff` (`hyp.tau(μ_j − μ_{j'}) = δ(∑ω_{ij}^σ − ∑ω_{ij'}^σ)`), and
`columnRImage_sum`; `orthonormal`/`mem_ZIrr` come from `columnRImage_inner`/`_injective` and
`alignedOmegaSigmaGrid_mem_ZIrr`.  Feeding `ofProjection` (with `coh.tau1`, ψ = 0), the (5.5)
`eq_sum_of_psi_eq_zero` then computes `μ_j^{τ₁} = ∑_{E ⊆ R(μ_j)} α`. -/
noncomputable def Hypothesis.columnImageFamilyCohFree [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j j' : Fin hyp.w2} (hj0 : j ≠ 0) (hj'0 : j' ≠ 0) (hjj' : j ≠ j')
    (hconj : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j).conj
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j') :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.tau
      (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) where
  imageSet := Finset.univ.image (hyp.columnRImage hG hG.odd params.delta j j')
  mem_ZIrr := by
    intro α hα
    rw [Finset.mem_image] at hα
    obtain ⟨⟨b, i⟩, _, rfl⟩ := hα
    cases b
    · simp only [Hypothesis.columnRImage]
      rw [Int.cast_smul_eq_zsmul]
      exact (ZIrr G).smul_mem _ (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i j)
    · simp only [Hypothesis.columnRImage]
      rw [neg_smul, Int.cast_smul_eq_zsmul]
      exact neg_mem ((ZIrr G).smul_mem _ (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i j'))
  orthonormal := by
    intro α hα β hβ
    rw [Finset.mem_image] at hα hβ
    obtain ⟨p, _, rfl⟩ := hα
    obtain ⟨q, _, rfl⟩ := hβ
    rw [hyp.columnRImage_inner hG hG.odd hδpm hjj']
    by_cases hpq : p = q
    · subst hpq; simp
    · rw [if_neg hpq,
        if_neg (fun he => hpq (hyp.columnRImage_injective hG hG.odd hδpm hjj' he))]
  image_eq := by
    rw [hconj, hyp.tau_muGrid_columnSum_diff_cohFree hG hG.odd hmu hzS hz1 hδpm hδj hj0 hj'0 hjj',
      Finset.sum_image (fun p _ q _ hpq => hyp.columnRImage_injective hG hG.odd hδpm hjj' hpq),
      hyp.columnRImage_sum, Finset.sum_sub_distrib]

open scoped Classical FiniteInduce in
/-- **§10 column image family exists** (issue 1009): the conjugate column `j'`
(`exists_conj_column`) packages the column `OrthonormalCharacterImageFamily` for `μ_j` together with
the `j' ≠ 0` datum (so the downstream `ofProjection`/(5.5) can read off `R(μ_j)`). -/
theorem Hypothesis.exists_columnImageFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j : Fin hyp.w2} (hj0 : j ≠ 0) :
    ∃ j' : Fin hyp.w2, j' ≠ 0 ∧ j' ≠ j ∧
      Nonempty (OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.tau
        (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)) := by
  obtain ⟨j', hj'0, hj'j, hconj⟩ := hyp.exists_conj_column hG hG.odd hj0
  exact ⟨j', hj'0, hj'j, ⟨hyp.columnImageFamily hG coh hmu hos hzS hz1 hzconj hδpm hδj hj0 hj'0
    (Ne.symm hj'j) hconj⟩⟩

open scoped Classical FiniteInduce in
/-- **§10 (5.5) for the column `μ_j`** (Peterfalvi (5.5) applied to the reducible column character):
`μ_j^{τ₁} = ∑_{α ∈ E} α` for some `E ⊆ R(μ_j)` with `|E| = ‖μ_j‖² = w₁`.

Builds the (5.4) `CharacterPsiDecomposition` for `(μ_j, ψ = 0)` against `τ = hyp.tau`,
`τ₁ = coh.tau1` via `ofProjection` — the column `OrthonormalCharacterImageFamily`
(`columnImageFamily`) supplies `R(μ_j)`; the coherence isometry `coh.coherent` supplies the
lattice-relative inner-preservation (`extension_inner_eq`, on `ℤ[S] ⊇ {μ_j − μ̄_j, μ_j}`), the
`τ`-agreement (`extends_on_supported`, `μ_j − μ̄_j` is `A_0`-supported), and the `ZIrr`-membership
(`extension_mem_ZIrr`, `μ_j ∈ S`); the orthogonalities `⟨μ_j, 0⟩ = ⟨μ̄_j, 0⟩ = 0` are trivial and
`⟨μ_j, μ̄_j⟩ = 0` is the cross-column Gram entry (`muGrid_inner_cross_column`, `j ≠ j'`).  Then
`eq_sum_of_psi_eq_zero` extracts the (5.5) sum.  This is the second-to-last step of (10.6)(a); the
final (5.8) full-column endgame then pins `E` to the single full column `{δ·ω_{ij}^σ}`. -/
theorem Hypothesis.exists_muColumn_tau1_eq_sum_R [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hd1 : ∀ jj : Fin hyp.w2, jj ≠ 0 → hyp.muGrid hG hG.odd 0 jj 1 ≠ 1)
    {j : Fin hyp.w2} (hj0 : j ≠ 0) :
    ∃ j' : Fin hyp.w2, j' ≠ 0 ∧ j' ≠ j ∧
      ∃ E ⊆ Finset.univ.image (hyp.columnRImage hG hG.odd params.delta j j'),
        coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) = ∑ α ∈ E, α ∧
          (E.card : ℂ) = (hyp.w1 : ℂ) := by
  haveI := hyp.finiteG
  classical
  obtain ⟨j', hj'0, hj'j, hconj⟩ := hyp.exists_conj_column hG hG.odd hj0
  set χ := ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j with hχdef
  have hχS : χ ∈ inducedFamily M := hyp.muGrid_column_sum_mem_inducedFamily hG hG.odd j (hd1 j hj0)
  have hχcS : χ.conj ∈ inducedFamily M := by
    rw [hχdef, hconj]; exact hyp.muGrid_column_sum_mem_inducedFamily hG hG.odd j' (hd1 j' hj'0)
  -- `χ − χ̄ = ∑_i (α_{ij} − α_{ij'})` is `A_0`-supported and lies in `ℤ[S]`.
  have hμdiff : χ - χ.conj
      = ∑ i : Fin hyp.w1, (params.alpha i j - params.alpha i j') := by
    rw [hχdef, hconj, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [params.alpha_def, params.alpha_def, hmu]; abel
  have hsumsupp : ∀ s : Finset (Fin hyp.w1),
      (∑ i ∈ s, (params.alpha i j - params.alpha i j')).support ⊆ hyp.A0 := by
    intro s
    induction s using Finset.induction with
    | empty => rw [Finset.sum_empty, ClassFunction.support_zero]; exact Set.empty_subset _
    | insert i s hi ih =>
        rw [Finset.sum_insert hi]
        refine (ClassFunction.support_add_subset _ _).trans (Set.union_subset ?_ ih)
        exact (ClassFunction.support_sub_subset _ _).trans
          (Set.union_subset (params.alpha_support i j hj0) (params.alpha_support i j' hj'0))
  have hsuppmem : (χ - χ.conj) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Sset hyp.A0 :=
    ⟨Submodule.sub_mem _ (Submodule.subset_span hχS) (Submodule.subset_span hχcS),
      by rw [hμdiff]; exact hsumsupp Finset.univ⟩
  -- the running coherence isometry preserves inner products on `ℤ[S] ⊇ zSpan {χ − χ̄, χ − 0}`.
  have hspan : OddOrder.Peterfalvi.S07.zSpan (L := ↥M) {χ - χ.conj, χ - 0}
      ≤ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.sub_mem _ (Submodule.subset_span hχS) (Submodule.subset_span hχcS)
    · rw [sub_zero]; exact Submodule.subset_span hχS
  -- `⟨μ_j, μ̄_j⟩ = 0` (cross-column Gram entry).
  have hχχbar : ClassFunction.inner χ χ.conj = 0 := by
    rw [hχdef, hconj, OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    exact Finset.sum_eq_zero fun i' _ => hyp.muGrid_inner_cross_column hG hG.odd i i' hj'j.symm
  -- assemble the (5.4) decomposition via `ofProjection` and apply (5.5).
  let R := hyp.columnImageFamily hG coh hmu hos hzS hz1 hzconj hδpm hδj hj0 hj'0 (Ne.symm hj'j) hconj
  let D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau χ 0 :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection R coh.tau1
      (fun φ ζ hφ hζ => coh.coherent.extension_inner_eq φ ζ (hspan hφ) (hspan hζ))
      (coh.coherent.extends_on_supported _ hsuppmem)
      (by rw [sub_zero]; exact coh.coherent.extension_mem_ZIrr χ (Submodule.subset_span hχS))
      (by rw [ClassFunction.inner_zero_right])
      (by rw [ClassFunction.inner_zero_right])
      hχχbar
  obtain ⟨_, hτ1, E, hEsub, hEsum, hEcard⟩ := D.eq_sum_of_psi_eq_zero
  refine ⟨j', hj'0, hj'j, E, hEsub, ?_, ?_⟩
  · rw [← hEsum]; exact hτ1
  · rw [hEcard, hχdef, hyp.muGrid_column_sum_inner_self hG hG.odd j]

open scoped FiniteInduce in
/-- **§10 column-independent `τ₁`-residual** (the reduction step of Peterfalvi (10.6)(a)): for any
two nontrivial columns `j, k ≠ 0`, the coherent images satisfy
`μ_j^{τ₁} − μ_k^{τ₁} = δ·(∑_i ω_{ij}^σ − ∑_i ω_{ik}^σ)`, i.e. the residual
`μ_j^{τ₁} − δ·∑_i ω_{ij}^σ` does **not depend on the column `j`**.

This is the honest §10-native column reduction of (10.6)(a): the difference
`μ_j − μ_k = ∑_i(α_{ij} − α_{ik})` is `A_0(M)`-supported (each `α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` is,
`CharacterParameters.alpha_support`), so the coherent extension agrees there with the Dade isometry
`τ` (`CoherentHypothesis.coherent.extends_on_supported`), and
`τ(μ_j − μ_k) = δ·(∑ω_{ij}^σ − ∑ω_{ik}^σ)` is the landed (10.5) column-sum identity
`tau_muGrid_columnSum_diff`.  Combined with `map_sub` for `τ₁` this gives the column-independence,
reducing the full (10.6)(a) `μ_j^{τ₁} = δ·∑_i ω_{ij}^σ` to a single column — the remaining content
being the (5.8) full-column endgame that pins that one column. -/
theorem Hypothesis.muColumn_tau1_diff_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j k : Fin hyp.w2} (hj0 : j ≠ 0) (hk0 : k ≠ 0)
    (hdj1 : hyp.muGrid hG hG.odd 0 j 1 ≠ 1) (hdk1 : hyp.muGrid hG hG.odd 0 k 1 ≠ 1) :
    coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
        - coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k)
      = (params.delta : ℂ) • (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i j
          - ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i k) := by
  haveI := hyp.finiteG
  classical
  -- `μ_j − μ_k = ∑_i (α_{ij} − α_{ik})` (the `δμ_{i0}`, `nζ` tails cancel).
  have hμdiff : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
      - (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k)
        = ∑ i : Fin hyp.w1, (params.alpha i j - params.alpha i k) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [params.alpha_def, params.alpha_def, hmu]; abel
  -- each partial sum `∑_{i∈s}(α_{ij} − α_{ik})` is `A_0`-supported (induction; `α_{ij}` is).
  have hsumsupp : ∀ s : Finset (Fin hyp.w1),
      (∑ i ∈ s, (params.alpha i j - params.alpha i k)).support ⊆ hyp.A0 := by
    intro s
    induction s using Finset.induction with
    | empty => rw [Finset.sum_empty, ClassFunction.support_zero]; exact Set.empty_subset _
    | insert i s hi ih =>
        rw [Finset.sum_insert hi]
        refine (ClassFunction.support_add_subset _ _).trans (Set.union_subset ?_ ih)
        exact (ClassFunction.support_sub_subset _ _).trans
          (Set.union_subset (params.alpha_support i j hj0) (params.alpha_support i k hk0))
  -- `μ_j − μ_k ∈ ℤ[S, A_0]`: in `ℤ[S]` (both column sums lie in `S`), supported on `A_0`.
  have hmem : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
        - (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k)
      ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Sset hyp.A0 := by
    refine ⟨Submodule.sub_mem _
      (Submodule.subset_span (hyp.muGrid_column_sum_mem_inducedFamily hG hG.odd j hdj1))
      (Submodule.subset_span (hyp.muGrid_column_sum_mem_inducedFamily hG hG.odd k hdk1)), ?_⟩
    rw [hμdiff]; exact hsumsupp Finset.univ
  -- `τ₁(μ_j − μ_k) = τ(μ_j − μ_k) = δ·(∑ω_{ij}^σ − ∑ω_{ik}^σ)`.
  have key : coh.tau1 ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
      - (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k))
        = hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
          - (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k)) :=
    coh.coherent.extends_on_supported _ hmem
  rw [map_sub] at key
  rw [key, tau_muGrid_columnSum_diff hG coh hmu hos hzS hz1 hzconj hδpm hδj hj0 hk0]

open scoped FiniteInduce in
/-- **(10.6.a) reduces to a single column**: if the summed isometry `μ_{j₀}^{τ₁} = δ·∑_i ω_{i j₀}^σ`
holds for **one** nontrivial column `j₀ ≠ 0`, then it holds for **every** nontrivial column `j ≠ 0`.

Immediate from the column-independence `muColumn_tau1_diff_eq`: for any `j ≠ 0`,
`μ_j^{τ₁} = μ_{j₀}^{τ₁} + (μ_j^{τ₁} − μ_{j₀}^{τ₁}) = δ·∑_i ω_{i j₀}^σ + δ·(∑_i ω_{ij}^σ − ∑_i ω_{i j₀}^σ)
= δ·∑_i ω_{ij}^σ`.  This isolates the remaining content of the full (10.6)(a) summed isometry to the
**(5.8) full-column endgame on a single column `j₀`** (which, once the column
`OrthonormalCharacterImageFamily` is available — HUB issue 1010 — pins that one column). -/
theorem Hypothesis.muColumn_tau1_eq_of_single_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hd1 : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muGrid hG hG.odd 0 j 1 ≠ 1)
    {j₀ : Fin hyp.w2} (hj₀0 : j₀ ≠ 0)
    (hpin : coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j₀)
      = (params.delta : ℂ) • ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i j₀) :
    ∀ j : Fin hyp.w2, j ≠ 0 →
      coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
        = (params.delta : ℂ) • ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i j := by
  intro j hj0
  have hdiff := hyp.muColumn_tau1_diff_eq hG coh hmu hos hzS hz1 hzconj hδpm hδj hj0 hj₀0
    (hd1 j hj0) (hd1 j₀ hj₀0)
  -- `μ_j^{τ₁} = (μ_j^{τ₁} − μ_{j₀}^{τ₁}) + μ_{j₀}^{τ₁}`, then substitute the two known pieces.
  have hrw : coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
      = (coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
          - coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j₀))
        + coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j₀) := by abel
  rw [hrw, hdiff, hpin, smul_sub]; abel

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.6)(a) summed isometry**: for every nontrivial column `0 < j < w₂`,
`μ_j^{τ₁} = δ·∑_i ω_{ij}^σ`.

This is the §10 specialisation of Peterfalvi's (5.8) — proved here *without* the general (5.8)
machinery (separability / `σ`-coefficients), using only the (10.6)(a) reduction and a cardinality
count.  By (5.5) (`exists_muColumn_tau1_eq_sum_R`), `μ_j^{τ₁} = ∑_{x ∈ T} R(x)` where
`R = R(μ_j) = {δ·ω_{ij}^σ}∪{−δ·ω_{ij'}^σ}` (`columnRImage`, `j'` the conjugate column) is an
orthonormal family and `|T| = ‖μ_j^{τ₁}‖² = w₁`.  The reduction
`(ω_{ij}^σ − ω_{i0}^σ, μ_j^{τ₁}) = δ` (`omegaSigmaDiff_inner_muColumn_tau1`) computes, against the
`T`-sum, to `δ·[(false, i) ∈ T]` (the cross-column `j'` and the trivial column `0` are orthogonal);
since `δ ≠ 0`, every `(false, i) ∈ T`.  So `{false} × univ ⊆ T` with both of cardinality `w₁`, forcing
`T = {false} × univ` and `μ_j^{τ₁} = ∑_i δ·ω_{ij}^σ = δ·∑_i ω_{ij}^σ`. -/
theorem Hypothesis.muColumn_tau1_pin [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hd1 : ∀ jj : Fin hyp.w2, jj ≠ 0 → hyp.muGrid hG hG.odd 0 jj 1 ≠ 1)
    {j : Fin hyp.w2} (hj0 : j ≠ 0) :
    coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
      = (params.delta : ℂ) • ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i j := by
  haveI := hyp.finiteG
  classical
  -- (5.5): `μ_j^{τ₁} = ∑_{α ∈ E} α` for `E ⊆ R(μ_j)`, `|E| = w₁`.
  obtain ⟨j', hj'0, hj'j, E, hEsub, hEsum, hEcard⟩ :=
    hyp.exists_muColumn_tau1_eq_sum_R hG coh hmu hos hzS hz1 hzconj hδpm hδj hd1 hj0
  set R := hyp.columnRImage hG hG.odd params.delta j j' with hRdef
  have hRinj : Function.Injective R := hyp.columnRImage_injective hG hG.odd hδpm (Ne.symm hj'j)
  -- the preimage `T ⊆ Bool × Fin w₁` of `E` under the injective family `R`.
  set T : Finset (Bool × Fin hyp.w1) := Finset.univ.filter (fun x => R x ∈ E) with hTdef
  have hImT : T.image R = E := by
    apply Finset.ext; intro α
    simp only [Finset.mem_image, hTdef, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hα
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp (hEsub hα)
      exact ⟨x, by rw [hx]; exact hα, hx⟩
  have hSumT : ∑ x ∈ T, R x = ∑ α ∈ E, α := by
    rw [← hImT, Finset.sum_image (fun x _ y _ h => hRinj h)]
  have hCardT : T.card = hyp.w1 := by
    have hc : (T.image R).card = E.card := by rw [hImT]
    rw [Finset.card_image_of_injOn (fun x _ y _ h => hRinj h)] at hc
    rw [hc]; exact_mod_cast hEcard
  -- `μ_j^{τ₁} = ∑_{x ∈ T} R x`.
  have hμT : coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) = ∑ x ∈ T, R x := by
    rw [hEsum, hSumT]
  -- inner product of `ω_{ij}^σ − ω_{i0}^σ` against each `R(x)` (only `x = (false, i)` survives).
  have hval : ∀ (i : Fin hyp.w1) (x : Bool × Fin hyp.w1),
      ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j
        - hyp.alignedOmegaSigmaGrid hG hG.odd i 0) (R x)
      = if x = (false, i) then (params.delta : ℂ) else 0 := by
    intro i x
    have hδstar : star ((params.delta : ℂ)) = (params.delta : ℂ) := by
      rcases hδpm with h | h <;> rw [h] <;> norm_num
    obtain ⟨b, i'⟩ := x
    cases b <;>
      simp only [hRdef, Hypothesis.columnRImage, ClassFunction.inner_sub_left,
        OddOrder.RepresentationTheory.inner_smul_right, hyp.alignedOmegaSigmaGrid_inner hG hG.odd,
        hδstar, star_neg, Prod.mk.injEq, reduceCtorEq, false_and, true_and, and_true,
        eq_self_iff_true, ↓reduceIte, mul_one, mul_zero, mul_neg, neg_mul, neg_neg]
    · -- (false, i'): `δ · [i = i'] − δ · [i = i' ∧ 0 = j] = if i' = i then δ else 0`
      rw [if_neg (show ¬(i = i' ∧ (0 : Fin hyp.w2) = j) from fun hh => hj0 hh.2.symm),
        mul_zero, sub_zero]
      by_cases hii : i = i'
      · rw [if_pos hii, mul_one, if_pos hii.symm]
      · rw [if_neg hii, mul_zero, if_neg (fun h => hii h.symm)]
    · -- (true, i'): both columns orthogonal (`j ≠ j'`, `j' ≠ 0`)
      rw [if_neg (show ¬(i = i' ∧ j = j') from fun hh => hj'j hh.2.symm),
        if_neg (show ¬(i = i' ∧ (0 : Fin hyp.w2) = j') from fun hh => hj'0 hh.2.symm)]
      ring
  -- the (10.6)(a) reduction forces every `(false, i) ∈ T`.
  have hfalseT : ∀ i : Fin hyp.w1, (false, i) ∈ T := by
    intro i
    by_contra hni
    have hRi := hyp.omegaSigmaDiff_inner_muColumn_tau1 hG coh hmu hos hzS hz1 hzconj hδpm hδj hj0 i
    rw [hμT, OddOrder.RepresentationTheory.inner_sum_right] at hRi
    rw [show (∑ x ∈ T, ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j
          - hyp.alignedOmegaSigmaGrid hG hG.odd i 0) (R x))
        = if (false, i) ∈ T then (params.delta : ℂ) else 0 by
      rw [Finset.sum_congr rfl (fun x _ => hval i x)]; exact Finset.sum_ite_eq' T (false, i) _,
      if_neg hni] at hRi
    rcases hδpm with h | h <;> rw [h] at hRi <;> norm_num at hRi
  -- `{false} × univ ⊆ T` and `|T| = w₁ = |{false} × univ|`, so `T = {false} × univ`.
  have hFsub : Finset.univ.image (fun i : Fin hyp.w1 => (false, i)) ⊆ T := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hfalseT i
  have hFinj : Function.Injective (fun i : Fin hyp.w1 => (false, i)) :=
    fun a b h => congrArg Prod.snd h
  have hFcard : (Finset.univ.image (fun i : Fin hyp.w1 => (false, i))).card = hyp.w1 := by
    rw [Finset.card_image_of_injective _ hFinj, Finset.card_univ, Fintype.card_fin]
  have hTeq : T = Finset.univ.image (fun i : Fin hyp.w1 => (false, i)) :=
    (Finset.eq_of_subset_of_card_le hFsub (by rw [hFcard, hCardT])).symm
  -- conclude: `μ_j^{τ₁} = ∑_i δ·ω_{ij}^σ = δ·∑_i ω_{ij}^σ`.
  rw [hμT, hTeq, Finset.sum_image (fun a _ b _ h => hFinj h)]
  simp only [hRdef, Hypothesis.columnRImage]
  rw [Finset.smul_sum]

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(b) reduction identity** (the `Ã(M)`-independent half of (10.6)(b)):
`τ(μ_0 − ζ) = ∑_i ω_{i0}^σ − ζ^{τ₁}` as a class function on `G`.

Picks a fixed nontrivial column `k`; the `M`-level identity
`δ(μ_0 − ζ) = (μ_k − dζ) − ∑_i α_{ik}` (from `α_{ik} = μ_{ik} − δμ_{i0} − nζ` and `d = w₁n + δ`)
is mapped through the `ℤ`-linear Dade map `τ`.  Then `τ(μ_k − dζ) = δ∑_i ω_{ik}^σ − dζ^{τ₁}`
(`μ_k − dζ = (μ_k − dζ̄) + d(ζ̄ − ζ)` reduces it to `tau_muColumn_sub_conj_eq_tau1` +
`tau_zeta_sub_conj_eq_tau1`, then `muColumn_tau1_pin` for `μ_k^{τ₁}`) and
`τ(α_{ik}) = δ(ω_{ik}^σ − ω_{i0}^σ) − nζ^{τ₁}` (`alpha_tau_image`); the `δ∑ω_{ik}^σ` cancel and
`(w₁n − d)ζ^{τ₁} = −δζ^{τ₁}`, giving `δ·τ(μ_0 − ζ) = δ∑ω_{i0}^σ − δζ^{τ₁}`; cancel `δ` (`δ² = 1`).

This is `STEP 1` of (10.6)(b) (issue 1009); the remaining `STEP 2` (`τ(μ_0 − ζ)` vanishes off `Ã(M)`,
the tame support) + `STEP 3` parity then give `|ζ^{τ₁}(g)| ≥ 1`. -/
theorem Hypothesis.tau_muColumnZero_sub_zeta_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) - params.zeta)
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i 0) - coh.tau1 params.zeta := by
  haveI := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  -- a fixed nontrivial column `k`.
  have hw2 : 3 ≤ hyp.w2 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W2
  obtain ⟨k, hk0⟩ : ∃ k : Fin hyp.w2, k ≠ 0 :=
    ⟨⟨1, by omega⟩, Fin.ne_of_val_ne (by simp)⟩
  have hcolk : ∀ i, hyp.muGrid hG hodd i k 1 = (params.d : ℂ) := fun i => by
    rw [← hmu]; exact params.degree_independent i k hk0
  have hd1 : params.d ≠ 1 := by have := params.d_gt_one; omega
  have hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1 := by rw [hcolk 0]; exact_mod_cast hd1
  have hd1k : ∀ jj : Fin hyp.w2, jj ≠ 0 → hyp.muGrid hG hodd 0 jj 1 ≠ 1 := fun jj hjj => by
    rw [← hmu, params.degree_independent 0 jj hjj]; exact_mod_cast hd1
  -- `d = w₁·n + δ`.
  have hd : (params.d : ℂ) = (hyp.w1 : ℂ) * (params.n : ℂ) + (params.delta : ℂ) := by
    have h : (params.n : ℂ) * (hyp.w1 : ℂ) = (params.d : ℂ) - (params.delta : ℂ) := by
      exact_mod_cast params.n_formula
    linear_combination -h
  -- `τ` commutes with the natural scalar `d`.
  have hsmul_tau : ∀ (x : ClassFunction ↥M ℂ),
      hyp.tau ((params.d : ℂ) • x) = (params.d : ℂ) • hyp.tau x := fun x => by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul (R := ℂ)]
  -- `τ(μ_k − dζ) = δ∑ω_{ik}^σ − dζ^{τ₁}` via the conjugate decomposition.
  have htauμk : hyp.tau ((∑ i, hyp.muGrid hG hodd i k) - (params.d : ℂ) • params.zeta)
      = (params.delta : ℂ) • (∑ i, hyp.alignedOmegaSigmaGrid hG hodd i k)
        - (params.d : ℂ) • coh.tau1 params.zeta := by
    have hdecomp : (∑ i, hyp.muGrid hG hodd i k) - (params.d : ℂ) • params.zeta
        = ((∑ i, hyp.muGrid hG hodd i k) - (params.d : ℂ) • params.zeta.conj)
          + (params.d : ℂ) • (params.zeta.conj - params.zeta) := by
      rw [smul_sub]; abel
    have htauzc : hyp.tau (params.zeta.conj - params.zeta)
        = coh.tau1 params.zeta.conj - coh.tau1 params.zeta := by
      rw [show params.zeta.conj - params.zeta = -(params.zeta - params.zeta.conj) by abel, map_neg,
        hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hzS params.zeta_irreducible]
      abel
    rw [hdecomp, map_add,
      hyp.tau_muColumn_sub_conj_eq_tau1 hG hodd k coh hzS params.zeta_irreducible hcolk hz1 hdk1,
      hsmul_tau, htauzc,
      muColumn_tau1_pin hG coh hmu hos hzS hz1 hzconj hδpm hδj hd1k hk0]
    module
  -- `τ(α_{ik}) = δ(ω_{ik}^σ − ω_{i0}^σ) − nζ^{τ₁}` (the (10.5) Dade image).
  have htauα : ∀ i, hyp.tau (params.alpha i k)
      = (params.delta : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i k
          - hyp.alignedOmegaSigmaGrid hG hodd i 0) - (params.n : ℂ) • coh.tau1 params.zeta := by
    intro i
    have h := alpha_tau_image hG coh hmu hos hzS hz1 hzconj hδpm hδj i k hk0
    rwa [hos] at h
  -- the `M`-level identity `δ(μ_0 − ζ) = (μ_k − dζ) − ∑_i α_{ik}`.
  have hMlevel : (params.delta : ℂ) • ((∑ i, hyp.muGrid hG hodd i 0) - params.zeta)
      = ((∑ i, hyp.muGrid hG hodd i k) - (params.d : ℂ) • params.zeta) - ∑ i, params.alpha i k := by
    have hαe : (∑ i, params.alpha i k)
        = (∑ i, hyp.muGrid hG hodd i k) - (params.delta : ℂ) • (∑ i, hyp.muGrid hG hodd i 0)
          - ((hyp.w1 : ℂ) * (params.n : ℂ)) • params.zeta := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [params.alpha_def, hmu]),
        Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul]
    rw [hαe, hd]; module
  -- `∑_i (δ(ω_{ik}^σ − ω_{i0}^σ) − nζ^{τ₁}) = δ(∑ω_{ik}^σ − ∑ω_{i0}^σ) − (w₁n)ζ^{τ₁}`.
  have hsum_α : (∑ i, ((params.delta : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i k
        - hyp.alignedOmegaSigmaGrid hG hodd i 0) - (params.n : ℂ) • coh.tau1 params.zeta))
      = (params.delta : ℂ) • ((∑ i, hyp.alignedOmegaSigmaGrid hG hodd i k)
          - ∑ i, hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - ((hyp.w1 : ℂ) * (params.n : ℂ)) • coh.tau1 params.zeta := by
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [← Finset.smul_sum, Finset.sum_sub_distrib]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (R := ℂ),
        smul_smul]
  -- map the `M`-level identity through `τ` and substitute the three images.
  have hscaled : (params.delta : ℂ) • hyp.tau ((∑ i, hyp.muGrid hG hodd i 0) - params.zeta)
      = (params.delta : ℂ) • ((∑ i, hyp.alignedOmegaSigmaGrid hG hodd i 0)
          - coh.tau1 params.zeta) := by
    have hkey := congrArg hyp.tau hMlevel
    rw [Int.cast_smul_eq_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul (R := ℂ)] at hkey
    rw [hkey, map_sub, htauμk, map_sum, Finset.sum_congr rfl (fun i _ => htauα i), hsum_α, hd]
    module
  -- cancel `δ` (`δ² = 1`).
  have hδsq : (params.delta : ℂ) * (params.delta : ℂ) = 1 := by
    rcases hδpm with h | h <;> rw [h] <;> norm_num
  calc hyp.tau ((∑ i, hyp.muGrid hG hodd i 0) - params.zeta)
      = (params.delta : ℂ) • ((params.delta : ℂ)
          • hyp.tau ((∑ i, hyp.muGrid hG hodd i 0) - params.zeta)) := by
        rw [smul_smul, hδsq, one_smul]
    _ = (params.delta : ℂ) • ((params.delta : ℂ) • ((∑ i, hyp.alignedOmegaSigmaGrid hG hodd i 0)
          - coh.tau1 params.zeta)) := by rw [hscaled]
    _ = (∑ i, hyp.alignedOmegaSigmaGrid hG hodd i 0) - coh.tau1 params.zeta := by
        rw [smul_smul, hδsq, one_smul]

open scoped FiniteInduce in
/-- **§10 (2.7) adjoint at the trivial character**: for an `A_0`-supported class function `φ` on `M`,
the Dade image `φ^τ = hyp.tau φ` has the same trivial-character multiplicity as `φ`,
`⟨φ^τ, 1_G⟩ = ⟨φ, 1_M⟩`.

The genuine §10 Dade isometry `hyp.tau` agrees on the supported subspace with the §4 Dade map
`hyp.dadeData.dade.dadeMap` (`dadeIntegralCharacterMap_apply_of_support`); the Peterfalvi (2.7) adjoint
formula `adjoint_formula` with `χ = 1_G` gives `⟨dadeMap ⟨φ,_⟩, 1_G⟩ = ⟨φ, ψ⟩`, where the coset
average `ψ = adjointAverageFun 1_G` is the constant `1` (`|H(a)|⁻¹·∑_{x ∈ H(a)} 1 = 1`), i.e. the
trivial character `1_M`.  This is the `a_{00} = ((μ_0 − ζ)^τ, 1_G) = (μ_0 − ζ, 1_M)` computation
underlying Peterfalvi (10.9). -/
theorem Hypothesis.tau_inner_trivial [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {φ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0) :
    ClassFunction.inner (hyp.tau φ) (trivialClassFunction G)
      = ClassFunction.inner φ (trivialClassFunction (↥M)) := by
  haveI := hyp.finiteG
  classical
  have hmem : φ ∈ ClassFunction.supportedSubmodule (G := ↥M) (k := ℂ)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M) :=
    (ClassFunction.mem_supportedSubmodule).mpr hφ
  -- `hyp.tau φ = dadeMap ⟨φ, supported⟩` on the supported subspace.
  have he : hyp.tau φ = hyp.dadeData.dade.dadeMap (k := ℂ) ⟨φ, hmem⟩ := by
    change OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) φ
      = hyp.dadeData.dade.dadeMap (k := ℂ) ⟨φ, hmem⟩
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade _ hφ]
  -- the coset average of `1_G` is the constant `1` (= `1_M`).
  have hψ : ∀ a : {a : G // a ∈ typePA0 M hyp.typeP},
      (trivialClassFunction (↥M)) ⟨a.1, hyp.dadeData.dade.subset_L a.2⟩
        = OddOrder.Peterfalvi.S04.adjointAverageFun hyp.dadeData.dade (trivialClassFunction G)
            ⟨a.1, hyp.dadeData.dade.subset_L a.2⟩ := by
    intro a
    rw [OddOrder.Peterfalvi.S04.adjointAverageFun, dif_pos a.2]
    simp only [trivialClassFunction_apply, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_univ, ← Nat.card_eq_fintype_card]
    rw [inv_mul_cancel₀]
    exact_mod_cast Nat.card_pos.ne'
  rw [he]
  exact OddOrder.Peterfalvi.S04.adjoint_formula hyp.dadeData.dade hyp.dadeData.dade.dadeMap
    (hyp.dadeData.dade.isDadeMap_dadeMap (k := ℂ)) hyp.hconj ⟨φ, hmem⟩ (trivialClassFunction G)
    (trivialClassFunction (↥M)) hψ

open scoped FiniteInduce in
/-- **§10 Dade isometry vanishes off the tame support `Ã(M) = dadeSupport`.**  For a class function
`φ` on `M` supported on `A_0(M)`, the Dade image `φ^τ = hyp.tau φ` *vanishes* at any
`g ∉ Ã(M) = hyp.dadeData.dade.dadeSupport`.

The genuine §10 Dade isometry `hyp.tau` is `S07.dadeIntegralCharacterMap hyp.dadeData.dade …`; on the
supported subspace it agrees with the §4 Dade map `hyp.dadeData.dade.dadeMap`
(`dadeIntegralCharacterMap_apply_of_support`), which vanishes off `dadeSupport`
(`IsDadeMap.map_eq_zero_of_not_mem_dadeSupport`).  This is the general "vanishes off `Ã(M)`" companion
of `dadeIntegralCharacterMap_apply_one_eq_zero` (the `g = 1` special case), and the `Ã(M)`-vanishing
step of (10.6)(b) (issue 1009, STEP 2). -/
theorem Hypothesis.tau_apply_eq_zero_of_not_mem_dadeSupport [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M) {φ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0)
    {g : G} (hg : g ∉ hyp.dadeData.dade.dadeSupport) :
    hyp.tau φ g = 0 := by
  haveI := hyp.finiteG
  classical
  show OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) φ g = 0
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade _ hφ]
  exact (hyp.dadeData.dade.isDadeMap_dadeMap (k := ℂ)).map_eq_zero_of_not_mem_dadeSupport
    (⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩ :
      OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ (typePA0 M hyp.typeP) M) g hg

open scoped FiniteInduce in
/-- **§10 support of `μ_0 − ζ`** (Peterfalvi (10.6)(b), the `Ã(M)`-vanishing leg): the column-`0`
sum `μ_0 = ∑_i μ_{i0}` (an induced character of degree `w₁`, since each `μ_{i0}(1) = 1`) minus a
degree-`w₁` irreducible `ζ ∈ S` (induced from `M'`) is supported in `A_0(M)`.

Both `μ_0` and `ζ` are induced from the normal `M' = [M,M]`, hence vanish off `M'`
(`muGrid_column_sum_vanishes_off_derived`; induced-from-`M'` for `ζ`); and the degrees cancel,
`(μ_0 − ζ)(1) = w₁ − w₁ = 0` (`muGrid_zero_column_apply_one`), so the support lies in
`M'^# ⊆ A(M) ⊆ A_0(M)`.

This is the companion of `muColumn_sub_conj_support`/`zeta_sub_conj_support`: it makes `μ_0 − ζ`
`A_0`-supported, so the Dade isometry `τ` vanishes on it off `Ã(M)`
(`tau_apply_eq_zero_of_not_mem_dadeSupport`).  Together with the (10.6)(b) reduction identity
`τ(μ_0 − ζ) = ∑_i ω_{i0}^σ − ζ^{τ₁}` (`tau_muColumnZero_sub_zeta_eq`) it yields the pointwise
identity `ζ^{τ₁}(g) = ∑_i ω_{i0}^σ(g)` off `Ã(M)`. -/
theorem Hypothesis.muColumnZero_sub_zeta_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ).support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζvanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ w = 0 := fun {w} hw => by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  have hsumapply : ∀ (w : ↥M), (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) w
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0 w := by
    intro w
    refine Finset.univ.induction_on (motive := fun s =>
      (∑ i ∈ s, hyp.muGrid hG hodd i 0) w = ∑ i ∈ s, hyp.muGrid hG hodd i 0 w) ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  intro z hz
  rw [ClassFunction.mem_support] at hz
  -- `z ∈ M'`: else `μ_0 z = ζ z = 0`.
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    apply hz
    rw [ClassFunction.sub_apply, hyp.muGrid_column_sum_vanishes_off_derived hG hodd 0 hzK,
      hζvanish hzK, sub_zero]
  -- `z ≠ 1`: `(μ_0 − ζ)(1) = w₁ − w₁ = 0`.
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hz
    rw [ClassFunction.sub_apply, hζ1, hsumapply 1,
      Finset.sum_congr rfl (fun i _ => hyp.muGrid_zero_column_apply_one hG hodd i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sub_self]
  have hzM' : (z : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp hzK
  show (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
    ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(b), STEP 2** (the `Ã(M)`-vanishing reduction): off the tame support
`Ã(M) = dadeSupport`, the coherent image `ζ^{τ₁}` agrees with the column-`0` σ-sum,
`ζ^{τ₁}(g) = ∑_i ω_{i0}^σ(g)` for `g ∉ hyp.dadeData.dade.dadeSupport`.

Combines the (10.6)(b) reduction identity `τ(μ_0 − ζ) = ∑_i ω_{i0}^σ − ζ^{τ₁}`
(`tau_muColumnZero_sub_zeta_eq`, STEP 1) with the vanishing of `τ(μ_0 − ζ)` off `Ã(M)`
(`tau_apply_eq_zero_of_not_mem_dadeSupport`, since `μ_0 − ζ` is `A_0`-supported by
`muColumnZero_sub_zeta_support`).  This is STEP 2 of (10.6)(b) (issue 1009); the remaining STEP 3
(parity of `∑_i ω_{i0}^σ(g)` using `ω_{00}^σ = 1_G` and the conjugate-pairing of the `i > 0`
terms) then gives `|ζ^{τ₁}(g)| ≥ 1`. -/
theorem Hypothesis.zeta_tau1_apply_eq_omegaSigma_sum_of_not_mem_dadeSupport [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {g : G} (hg : g ∉ hyp.dadeData.dade.dadeSupport) :
    coh.tau1 params.zeta g
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g := by
  haveI := hyp.finiteG
  -- STEP 1: `τ(μ_0 − ζ) = ∑_i ω_{i0}^σ − ζ^{τ₁}` as class functions on `G`.
  have hstep1 := hyp.tau_muColumnZero_sub_zeta_eq hG coh hmu hos hzS hz1 hzconj hδpm hδj
  -- `μ_0 − ζ` is `A_0`-supported, so `τ(μ_0 − ζ)` vanishes off `Ã(M)`.
  have hsupp := hyp.muColumnZero_sub_zeta_support hG hG.odd hzS hz1
  have hvanish := hyp.tau_apply_eq_zero_of_not_mem_dadeSupport hsupp hg
  -- Evaluate the STEP 1 identity at `g` (`ClassFunction` is a `CoeFun`, not `DFunLike`).
  have heval : hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) - params.zeta) g
      = ((∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i 0)
          - coh.tau1 params.zeta) g :=
    congrArg (fun f : ClassFunction G ℂ => (f : G → ℂ) g) hstep1
  -- Cancel the vanishing left-hand side.
  rw [ClassFunction.sub_apply, hvanish] at heval
  linear_combination heval

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(b), STEP 3 — integrality of the column-`0` σ-grid value** ((3.9)(c) on the
aligned grid): for `g : G` of order prime to `w₁`, each `ω_{i0}^σ(g)` is a rational integer.

The aligned grid is `ω_{i0}^σ = σ(ω(ξ_i))` for the transported linear character
`ξ_i = (omegaProdChar (w1CharEquiv i) χ₂).comp e` of `tic.W` (column-`0` dual `χ₂ = 1`).  As column
`0` is trivial, `ξ_i` factors through `W₁` (`omegaProdChar_one_right`), so `orderOf ξ_i ∣ |W₁| = w₁`;
since `(orderOf g)` is coprime to `w₁` it is coprime to `orderOf ξ_i`, and (3.9)(c)
(`exists_intCast_sigma_omega_apply`) gives the integer. -/
theorem Hypothesis.exists_intCast_alignedOmegaSigmaGrid_zero_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {g : G}
    (hg : (orderOf g).Coprime hyp.w1) :
    ∃ n : ℤ, hyp.alignedOmegaSigmaGrid hG hodd i 0 g = (n : ℂ) := by
  haveI := hyp.finiteG
  classical
  -- reconstruct the `let`s of `alignedOmegaSigmaGrid`
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
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2))
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- the transported linear character `ξ` of `tic.W`
  let ξ : ↥tic.W →* ℂˣ :=
    (h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv (finCongr hcardW1.symm i)) χ₂).comp
      e.toMonoidHom
  -- `alignedOmegaSigmaGrid i 0 = σ(ω ξ)` (mirror the `step1` of the χ-family lemma; `ω = lin`).
  have step1 : hyp.alignedOmegaSigmaGrid hG hodd i 0
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (tic.omega ξ : ClassFunction ↥tic.W ℂ) := by
    change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd)
        (tic.omega ξ : ClassFunction ↥tic.W ℂ)
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (tic.omega ξ : ClassFunction ↥tic.W ℂ)
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  -- column `0` dual is trivial, so `ξ = (w1CharEquiv …).comp wFst ∘ e` factors through `W₁`.
  have hχ₂ : χ₂ = 1 := by
    show finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1
    rw [show (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 0 from by simp,
      finCardEquivCharacterGroup_zero]
  -- `(w1CharEquiv …) ^ w₁ = 1` from `|Ŵ₁| = |W₁| = w₁` (Pontryagin self-duality).
  have hcardDual : Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) = hyp.w1 :=
    (h.sdiffTICyclicHypothesis.card_charGroup_subgroupOf
      h.sdiffTICyclicHypothesis.W1_le_W).trans hcardW1
  have hχ1pow : (h.w1CharEquiv (finCongr hcardW1.symm i)) ^ hyp.w1 = 1 := by
    have := pow_card_eq_one' (x := h.w1CharEquiv (finCongr hcardW1.symm i))
    rwa [hcardDual] at this
  -- column `0` trivial ⟹ `ξ` factors through `W₁` as `(w1CharEquiv …).comp wFst ∘ e`.
  have hξeq : ξ = ((h.w1CharEquiv (finCongr hcardW1.symm i)).comp
      h.sdiffTICyclicHypothesis.wFst).comp e.toMonoidHom := by
    have hpc : (h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv (finCongr hcardW1.symm i)) χ₂)
        = (h.w1CharEquiv (finCongr hcardW1.symm i)).comp h.sdiffTICyclicHypothesis.wFst := by
      rw [hχ₂]
      exact h.sdiffTICyclicHypothesis.omegaProdChar_one_right _
    exact congrArg (fun f => f.comp e.toMonoidHom) hpc
  -- `ξ ^ w₁ = 1` pointwise.
  have hξpow : ξ ^ hyp.w1 = 1 := by
    refine MonoidHom.ext fun w => Units.val_injective ?_
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, MonoidHom.one_apply, Units.val_one, hξeq,
      MonoidHom.comp_apply, MonoidHom.comp_apply, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply,
      hχ1pow, MonoidHom.one_apply, Units.val_one]
  have hdvd : orderOf ξ ∣ hyp.w1 := orderOf_dvd_of_pow_eq_one hξpow
  have hcop : (orderOf g).Coprime (orderOf ξ) := hg.coprime_dvd_right hdvd
  obtain ⟨n, hn⟩ :=
    tic.exists_intCast_sigma_omega_apply rfl (hyp.canonicalFullDadeApp hG hodd) ξ hcop
  exact ⟨n, by rw [step1]; exact hn⟩

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(b), STEP 3 — the principal grid value** ((4.4)/(3.2)(b)): the `(0,0)` entry
of the aligned σ-grid is the trivial character `1_G`, `ω_{00}^σ = 1_G`.

For `i = 0`, column `0`: the source `ξ_{00} = (omegaProdChar (w1CharEquiv 0) χ₂).comp e` is trivial —
`w1CharEquiv 0 = 1` (`w1CharEquiv_zero`), `χ₂ = 1` (column `0`), so `omegaProdChar 1 1 = 1`
(`omegaProdChar_one_one`) and `(1).comp e = 1`.  Then `tic.omega 1 = 1_{tic.W}` and
`1_{tic.W}^σ = 1_G` (`sigma_trivial`). -/
theorem Hypothesis.alignedOmegaSigmaGrid_zero_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    hyp.alignedOmegaSigmaGrid hG hodd 0 0 = trivialClassFunction G := by
  haveI := hyp.finiteG
  classical
  -- reconstruct the `let`s of `alignedOmegaSigmaGrid`
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
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2))
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  let ξ : ↥tic.W →* ℂˣ :=
    (h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1)))
      χ₂).comp e.toMonoidHom
  -- `alignedOmegaSigmaGrid 0 0 = σ(ω ξ)` (mirror the `step1` of the χ-family lemma).
  have step1 : hyp.alignedOmegaSigmaGrid hG hodd 0 0
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (tic.omega ξ : ClassFunction ↥tic.W ℂ) := by
    change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd)
        (tic.omega ξ : ClassFunction ↥tic.W ℂ)
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (tic.omega ξ : ClassFunction ↥tic.W ℂ)
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  -- both indices trivial ⟹ `ξ = 1`.
  have hχ₂ : χ₂ = 1 := by
    show finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1
    rw [show (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 0 from by simp,
      finCardEquivCharacterGroup_zero]
  have hχ1 : h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1)) = 1 := by
    rw [show (finCongr hcardW1.symm (0 : Fin hyp.w1)) = 0 from by simp, h.w1CharEquiv_zero]
  have hξ1 : ξ = 1 := by
    have hpc : h.sdiffTICyclicHypothesis.omegaProdChar
        (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) χ₂ = 1 := by
      rw [hχ₂, hχ1]; exact h.sdiffTICyclicHypothesis.omegaProdChar_one_one
    show (h.sdiffTICyclicHypothesis.omegaProdChar
      (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) χ₂).comp e.toMonoidHom = 1
    rw [hpc, MonoidHom.one_comp]
  -- `tic.omega 1 = 1_{tic.W}`, and `1_{tic.W}^σ = 1_G`.
  have homega1 : (tic.omega (1 : ↥tic.W →* ℂˣ) : ClassFunction ↥tic.W ℂ)
      = trivialClassFunction ↥tic.W := by ext w; simp
  rw [step1, hξ1, homega1, OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_trivial]

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(b), STEP 3 — the row-conjugation involution** ((3.9)(a)/(4.9)(a) on the
aligned column-`0` grid): complex conjugation of `ω_{i0}^σ` is again a column-`0` grid value
`ω_{i'0}^σ`, where `i' = rowInv i` is the **row-inversion** index (`w1CharEquiv i' =
(w1CharEquiv i)⁻¹`); moreover `i' = i ↔ i = 0` (in the odd-order dual `Ŵ₁`, `χ⁻¹ = χ ⟺ χ = 1`), and
`i ↦ i'` is an involution.

`mapRingEquiv conj (ω_{i0}^σ) = sigma(galoisMap conj (ω(ξ_i))) = sigma(ω(ξ_i⁻¹))`
(`sigma_mapRingEquiv_comm` + `galoisMap_conj_omega`), and `ξ_i⁻¹ = ξ_{i'}` since
`omegaProdChar χ₁ χ₂` inverts coordinatewise (`omegaProdChar_inv`), `w1CharEquiv (rowInv i) =
(w1CharEquiv i)⁻¹` (`w1CharEquiv_rowInv`) and `χ₂⁻¹ = χ₂` (column `0` is trivial).  This is the
(3.9)(a) ingredient that pairs the `i > 0` terms of `∑_i ω_{i0}^σ(g)`. -/
theorem Hypothesis.exists_rowInv_alignedOmegaSigma_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) :
    ∃ i' : Fin hyp.w1,
      ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
          (hyp.alignedOmegaSigmaGrid hG hodd i 0)
        = hyp.alignedOmegaSigmaGrid hG hodd i' 0
      ∧ (i' = i ↔ i = 0)
      ∧ (∀ j' : Fin hyp.w1,
          (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
              (hyp.alignedOmegaSigmaGrid hG hodd i' 0)
            = hyp.alignedOmegaSigmaGrid hG hodd j' 0) → j' = i) := by
  haveI := hyp.finiteG
  classical
  -- reconstruct the `let`s of `alignedOmegaSigmaGrid`
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
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2))
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- the transported linear character `ξ_a` of `tic.W` for any row `a`
  let ξ : Fin hyp.w1 → (↥tic.W →* ℂˣ) := fun a =>
    (h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv (finCongr hcardW1.symm a)) χ₂).comp
      e.toMonoidHom
  -- `alignedOmegaSigmaGrid a 0 = σ(ω ξ_a)` for any row `a`.
  have step1 : ∀ a, hyp.alignedOmegaSigmaGrid hG hodd a 0
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (tic.omega (ξ a) : ClassFunction ↥tic.W ℂ) := by
    intro a
    change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd)
        (tic.omega (ξ a) : ClassFunction ↥tic.W ℂ)
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (tic.omega (ξ a) : ClassFunction ↥tic.W ℂ)
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  -- column `0` dual is trivial: `χ₂ = 1` (so `χ₂⁻¹ = χ₂`).
  have hχ₂ : χ₂ = 1 := by
    show finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1
    rw [show (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 0 from by simp,
      finCardEquivCharacterGroup_zero]
  -- the row-inversion translated index
  let i' : Fin hyp.w1 :=
    finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i))
  -- `finCongr` round-trip: `finCongr hcardW1.symm i' = rowInv (finCongr hcardW1.symm i)`.
  have hround : finCongr hcardW1.symm i'
      = OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i) := by
    show finCongr hcardW1.symm
        (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i)))
      = OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i)
    simp
  -- `χ₂⁻¹ = χ₂` (column `0` is trivial).
  have hχ₂inv : χ₂⁻¹ = χ₂ := by rw [hχ₂, inv_one]
  -- key: `mapRingEquiv conj (ω_{a0}^σ) = ω_{a'0}^σ` for a row `a` with translated index `a'`.
  have hconj : ∀ a : Fin hyp.w1,
      ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (hyp.alignedOmegaSigmaGrid hG hodd a 0)
        = hyp.alignedOmegaSigmaGrid hG hodd
            (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a))) 0 := by
    intro a
    have hroundA : finCongr hcardW1.symm
        (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a)))
      = OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a) := by simp
    -- `ξ_a⁻¹ = ξ_{a'}`.
    have hξinv : (ξ a)⁻¹
        = ξ (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a))) := by
      -- the underlying `omegaProdChar` factors invert; `χ₂⁻¹ = χ₂`, row inverts via `rowInv`.
      have hprod : (h.sdiffTICyclicHypothesis.omegaProdChar
            (h.w1CharEquiv (finCongr hcardW1.symm a)) χ₂)⁻¹
          = h.sdiffTICyclicHypothesis.omegaProdChar
              (h.w1CharEquiv (finCongr hcardW1.symm
                (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a)))))
                χ₂ := by
        rw [hroundA, OddOrder.Peterfalvi.S06.w1CharEquiv_rowInv,
          OddOrder.Peterfalvi.S06.omegaProdChar_inv, hχ₂]
        congr 1
      show ((h.sdiffTICyclicHypothesis.omegaProdChar
          (h.w1CharEquiv (finCongr hcardW1.symm a)) χ₂).comp e.toMonoidHom)⁻¹
        = (h.sdiffTICyclicHypothesis.omegaProdChar
          (h.w1CharEquiv (finCongr hcardW1.symm
            (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a)))))
              χ₂).comp e.toMonoidHom
      refine MonoidHom.ext fun w => Units.val_injective ?_
      rw [MonoidHom.comp_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, ← hprod,
        MonoidHom.inv_apply]
    rw [step1 a, step1 (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a))),
      tic.sigma_mapRingEquiv_comm rfl (hyp.canonicalFullDadeApp hG hodd) _ _,
      OddOrder.Peterfalvi.S06.galoisMap_conj_omega, hξinv]
  -- oddness of the dual `Ŵ₁` (from `Odd |G|` via `W₁ ≤ M ≤ G` and Pontryagin).
  have hcardDual : Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) = hyp.w1 :=
    (h.sdiffTICyclicHypothesis.card_charGroup_subgroupOf
      h.sdiffTICyclicHypothesis.W1_le_W).trans hcardW1
  have hoddM : Odd (Nat.card ↥M) := Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card M)
  have hoddW1 : Odd (Nat.card ↥h.W1) :=
    Odd.of_dvd_nat hoddM (Subgroup.card_subgroup_dvd_card h.W1)
  -- in the odd-order dual, `χ⁻¹ = χ ⟹ χ = 1`.
  have hsq_one : ∀ χ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ, χ⁻¹ = χ → χ = 1 := by
    intro χ hχ
    haveI : Finite ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := Finite.of_fintype _
    have hx2 : χ ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [← hχ]; exact inv_mul_cancel χ
    have h2 : orderOf χ ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have hc : orderOf χ ∣ Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := orderOf_dvd_natCard χ
    have hcop : Nat.Coprime 2 (Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)) := by
      rw [Nat.coprime_two_left, hcardDual, ← hcardW1]; exact hoddW1
    have hg : orderOf χ ∣ Nat.gcd 2 (Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)) :=
      Nat.dvd_gcd h2 hc
    rw [hcop.gcd_eq_one] at hg
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  refine ⟨i', hconj i, ?_, ?_⟩
  · -- `i' = i ↔ i = 0`.
    constructor
    · intro hii
      have hceq : (h.w1CharEquiv (finCongr hcardW1.symm i))⁻¹
          = h.w1CharEquiv (finCongr hcardW1.symm i) := by
        rw [← OddOrder.Peterfalvi.S06.w1CharEquiv_rowInv, ← hround, hii]
      have hx1 : h.w1CharEquiv (finCongr hcardW1.symm i) = 1 := hsq_one _ hceq
      have hz : finCongr hcardW1.symm i = 0 :=
        h.w1CharEquiv.injective (hx1.trans h.w1CharEquiv_zero.symm)
      have h0 : i = finCongr hcardW1 (0 : Fin (Nat.card h.W1)) := by rw [← hz]; simp
      rw [h0]; simp
    · intro hi0
      have hz : finCongr hcardW1.symm i = 0 := by rw [hi0]; simp
      show finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i)) = i
      rw [hz]
      have hrow0 : OddOrder.Peterfalvi.S06.rowInv h (0 : Fin (Nat.card h.W1)) = 0 := by
        rw [OddOrder.Peterfalvi.S06.rowInv, h.w1CharEquiv_zero, inv_one]
        exact h.w1CharEquiv.symm_apply_eq.mpr h.w1CharEquiv_zero.symm
      rw [hrow0, hi0]; simp
  · -- involution: applying the construction to `i'` returns `i`.
    intro j' hj'
    have hkey := hconj i'
    rw [hj'] at hkey
    have hii : finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i')) = i := by
      rw [hround, OddOrder.Peterfalvi.S06.rowInv_rowInv]; simp
    rw [hii] at hkey
    -- `hkey : ω_{j'0}^σ = ω_{i0}^σ`.  Conclude `j' = i` via grid orthonormality.
    by_contra hne
    have hortho := hyp.alignedOmegaSigmaGrid_inner hG hodd j' i 0 0
    rw [hkey, hyp.alignedOmegaSigmaGrid_inner hG hodd i i 0 0, if_pos ⟨rfl, rfl⟩,
      if_neg (fun hc => hne hc.1)] at hortho
    exact one_ne_zero hortho

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(b), STEP 3 — the parity bound** (the (10.6)(b) target): off the tame support
`Ã(M)`, at a `g` of order prime to `w₁`, the coherent image `ζ^{τ₁}(g)` is an **odd integer**.

By STEP 2 (`zeta_tau1_apply_eq_omegaSigma_sum_of_not_mem_dadeSupport`),
`ζ^{τ₁}(g) = ∑_i ω_{i0}^σ(g)`.  Each `ω_{i0}^σ(g)` is a rational integer `n_i`
(`exists_intCast_alignedOmegaSigmaGrid_zero_column`, (3.9)(c)), so `ζ^{τ₁}(g) = (∑_i n_i : ℤ)`.
The terms pair under the row-conjugation involution `i ↦ i'` (`exists_rowInv_alignedOmegaSigma_conj`,
(3.9)(a)): `n_{i'} = n_i` (conjugation fixes the real integer), and the unique fixed point `i = 0`
carries the principal value `n_0 = 1` (`alignedOmegaSigmaGrid_zero_zero`, `ω_{00}^σ = 1_G`).  Hence the
off-principal terms sum to an even integer and `∑_i n_i = 1 + even` is odd; in particular
`|ζ^{τ₁}(g)| ≥ 1`.  This closes (10.6)(b) (issue 1009). -/
theorem Hypothesis.zeta_tau1_norm_ge_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {g : G} (hg : g ∉ hyp.dadeData.dade.dadeSupport) (hgord : (orderOf g).Coprime hyp.w1) :
    ∃ m : ℤ, coh.tau1 params.zeta g = (m : ℂ) ∧ Odd m := by
  haveI := hyp.finiteG
  classical
  -- STEP 2: `ζ^{τ₁}(g) = ∑_i ω_{i0}^σ(g)`.
  have hstep2 := hyp.zeta_tau1_apply_eq_omegaSigma_sum_of_not_mem_dadeSupport
    hG coh hmu hos hzS hz1 hzconj hδpm hδj hg
  -- push the application through the finite sum (CoeFun, not DFunLike).
  have hsumapply : (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g
      = ∑ i : Fin hyp.w1, (hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g := by
    refine Finset.univ.induction_on (motive := fun s =>
      (∑ i ∈ s, hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g
        = ∑ i ∈ s, (hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g) ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  -- (3.9)(c): each `ω_{i0}^σ(g)` is a rational integer `n i`.
  have hint : ∀ i : Fin hyp.w1,
      ∃ n : ℤ, (hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g = (n : ℂ) := fun i =>
    hyp.exists_intCast_alignedOmegaSigmaGrid_zero_column hG hG.odd i hgord
  let n : Fin hyp.w1 → ℤ := fun i => (hint i).choose
  have hn : ∀ i, (hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g = (n i : ℂ) := fun i => (hint i).choose_spec
  -- `m := ∑ n i`, and `ζ^{τ₁}(g) = (m : ℂ)`.
  have hval : coh.tau1 params.zeta g = ((∑ i : Fin hyp.w1, n i : ℤ) : ℂ) := by
    rw [hstep2, hsumapply]
    push_cast
    exact Finset.sum_congr rfl (fun i _ => hn i)
  refine ⟨∑ i : Fin hyp.w1, n i, hval, ?_⟩
  -- the row-conjugation involution `ρ` ((3.9)(a)).
  have hB : ∀ a : Fin hyp.w1, ∃ i' : Fin hyp.w1,
      ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (hyp.alignedOmegaSigmaGrid hG hG.odd a 0)
        = hyp.alignedOmegaSigmaGrid hG hG.odd i' 0
      ∧ (i' = a ↔ a = 0)
      ∧ (∀ j' : Fin hyp.w1,
          (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
              (hyp.alignedOmegaSigmaGrid hG hG.odd i' 0)
            = hyp.alignedOmegaSigmaGrid hG hG.odd j' 0) → j' = a) := fun a =>
    hyp.exists_rowInv_alignedOmegaSigma_conj hG hG.odd a
  let ρ : Fin hyp.w1 → Fin hyp.w1 := fun a => (hB a).choose
  have hρconj : ∀ a, ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
        (hyp.alignedOmegaSigmaGrid hG hG.odd a 0)
      = hyp.alignedOmegaSigmaGrid hG hG.odd (ρ a) 0 := fun a => (hB a).choose_spec.1
  have hρfix : ∀ a, ρ a = a ↔ a = 0 := fun a => (hB a).choose_spec.2.1
  have hρinv : ∀ a, ρ (ρ a) = a := fun a => (hB a).choose_spec.2.2 (ρ (ρ a)) (hρconj (ρ a))
  -- the involution preserves `n`: `n (ρ a) = n a` (conjugation fixes the real integer).
  have hnρ : ∀ a, n (ρ a) = n a := by
    intro a
    have hc := congrArg (fun f : ClassFunction G ℂ => (f : G → ℂ) g) (hρconj a)
    simp only [ClassFunction.mapRingEquiv_apply] at hc
    rw [hn a, hn (ρ a), map_intCast] at hc
    exact_mod_cast hc.symm
  -- `n 0 = 1` (the principal value `ω_{00}^σ = 1_G`).
  have hn0 : n 0 = 1 := by
    have h00 := hyp.alignedOmegaSigmaGrid_zero_zero hG hG.odd
    have := hn 0
    rw [h00, trivialClassFunction_apply] at this
    exact_mod_cast this.symm
  -- off-principal terms sum to an even integer (fixed-point-free involution on `univ ∖ {0}`).
  have heven : (2 : ℤ) ∣ ∑ i ∈ Finset.univ.erase (0 : Fin hyp.w1), n i := by
    have hz : ((∑ i ∈ Finset.univ.erase (0 : Fin hyp.w1), n i : ℤ) : ZMod 2) = 0 := by
      push_cast
      refine Finset.sum_involution (fun a _ => ρ a) ?_ ?_ ?_ ?_
      · intro a _
        rw [hnρ a]; exact CharTwo.add_self_eq_zero _
      · intro a ha _ hcontra
        exact (Finset.mem_erase.mp ha).1 ((hρfix a).mp hcontra)
      · intro a ha
        rw [Finset.mem_erase] at ha ⊢
        refine ⟨fun hcontra => ha.1 ?_, Finset.mem_univ _⟩
        have hca : ρ a = 0 := hcontra
        calc a = ρ (ρ a) := (hρinv a).symm
          _ = ρ 0 := by rw [hca]
          _ = 0 := (hρfix 0).mpr rfl
      · intro a _; exact hρinv a
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hz
  -- `∑ n i = n 0 + (even) = 1 + even` is odd.
  have hsplit : (∑ i : Fin hyp.w1, n i)
      = n 0 + ∑ i ∈ Finset.univ.erase (0 : Fin hyp.w1), n i :=
    (Finset.add_sum_erase Finset.univ n (Finset.mem_univ 0)).symm
  rw [hsplit, hn0]
  rcases heven with ⟨c, hc⟩
  exact ⟨c, by rw [hc]; ring⟩

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)**: the sums of `omega_ij^sigma` describe the `tau1`
images, and outside the tame support the value of `zeta^tau1` has norm at least
one.

Conjunct (a) (the summed isometry) is the genuine `muColumn_tau1_pin` (the §10 specialisation of
(5.8)).  Conjunct (b) (the (10.6)(b) parity bound) is now genuine and proven: off `Ã(M) = dadeSupport`,
at `g` of order prime to `w₁`, `ζ^{τ₁}(g)` is an **odd integer** (`zeta_tau1_norm_ge_one`), hence
`|ζ^{τ₁}(g)| ≥ 1` — replacing the former opaque `zeta_tau1_norm_bound` placeholder field.  The
(10.3)/(10.5) carrier pins (`hmu`/`hos`/`hzS`/`hz1`/`hzconj`/`hδpm`/`hδj`) are discharged by the
constructed `params` (`w2_prime_and_parameter_independence`). -/
theorem tau1_values_and_norm_bound [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    (∀ (j : Fin hyp.w2), j ≠ 0 →
        coh.tau1 (∑ i : Fin hyp.w1, params.mu i j) =
          (params.delta : ℂ) • ∑ i : Fin hyp.w1, params.omegaSigma i j) ∧
      (∀ (g : G), g ∉ hyp.dadeData.dade.dadeSupport → (orderOf g).Coprime hyp.w1 →
          ∃ m : ℤ, coh.tau1 params.zeta g = (m : ℂ) ∧ Odd m) := by
  have hd1 : ∀ jj : Fin hyp.w2, jj ≠ 0 → hyp.muGrid hG hG.odd 0 jj 1 ≠ 1 := by
    intro jj hjj
    rw [← hmu, params.degree_independent 0 jj hjj]
    exact_mod_cast (by have := params.d_gt_one; omega : params.d ≠ 1)
  refine ⟨fun j hj0 => ?_, ?_⟩
  · -- (10.6)(a): the summed isometry `μ_j^{τ₁} = δ·∑_i ω_{ij}^σ`.
    rw [hmu, hos]
    exact hyp.muColumn_tau1_pin hG coh hmu hos hzS hz1 hzconj hδpm hδj hd1 hj0
  · -- (10.6)(b): off `Ã(M)`, at `g` of order prime to `w₁`, `ζ^{τ₁}(g)` is an odd integer
    -- (`zeta_tau1_norm_ge_one`); in particular `|ζ^{τ₁}(g)| ≥ 1`.
    intro g hg hgord
    exact hyp.zeta_tau1_norm_ge_one hG coh hmu hos hzS hz1 hzconj hδpm hδj hg hgord


end OddOrder.Peterfalvi.S12

