/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_CharacterDegreeEnginesSSide

/-!
# Peterfalvi §13 (pp. 75-86) — the `T`-side chosen-base (7.6) datum and distinguished index

Prefix-split from `S15_CharacterDegreeEngines.lean` (1,500-line watch, issue 2035 #90): the
`S`-side τ₁-supply engines, `CharacterDegreeCore`, and the `S`-side chosen-base cCoeff layer
stay upstream in `S15_CharacterDegreeEnginesSSide.lean`; this file keeps the module name (so
downstream imports are unchanged) and carries the **`T`-side twin** (issue 2035 #22 発見 2):
`Q_sharp_hypothesis76_base` (the `(T, Q^#)` chosen-base (7.6) datum) and
`exists_muT_index_core` (the (13.8)-for-`T` distinguished index, Peterfalvi (13.3.c)-at-`T`).
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **The (13.5)/(7.6) datum for `(T, Q^#)` with a chosen `𝒯₁`-base** (issue 2035 更新 #22
発見 2, the `T`-side twin of `H_sharp_hypothesis76_base`): the `Q_sharp_hypothesis76` mirror
through `hypothesis76OfDadeBase`, pinning `ζ₀ = Ind_Q^T φ₀` for a *given* `φ₀` —
Peterfalvi's per-application base choice for the `T`-side (13.5) of the (13.8)-for-`T`
estimate (`ζ₀ ∈ 𝒯₁`, i.e. `Q ⊄ Ker φ₀`; the trivial-base instance leaves the (13.5.a/b/c)
coefficient claims genuinely undetermined, exactly as on the `S`-side). -/
noncomputable def Q_sharp_hypothesis76_base [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.T)) :
    OddOrder.Peterfalvi.S09.Hypothesis76 G
      (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) hyp.T := by
  refine OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDadeBase
    (Q_sharp_hypothesis71 hG hyp hvd)
    (((Q_sharp_dadeHypothesis hG hyp hvd).fullDadeIsometryData
      (Q_sharp_hconj hG hyp hvd)).toDadeIsometryData.isDadeIsometry) hyp.Q ?_ ?_ rfl φ₀
  · rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  · intro l h hh
    have hnorm : Subgroup.normalizer (hyp.Q : Set G) = hyp.T := normalizer_Q_eq_T hG hyp
    have hlnorm : (l : G) ∈ Subgroup.normalizer (hyp.Q : Set G) := by
      rw [hnorm]; exact l.2
    exact (Subgroup.mem_set_normalizer_iff.mp hlnorm h).mp hh

open scoped FiniteInduce in
/-- **The chosen-base `(T, Q^#)` family pins `ζ₀ = Ind_Q^T φ₀`** (mirror of
`H_sharp_hypothesis76_base_zeta_zero`). -/
theorem Q_sharp_hypothesis76_base_zeta_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.T)) :
    (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta 0
      = ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
          (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ) := by
  unfold Q_sharp_hypothesis76_base
  exact OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDadeBase_zeta_zero _ _ _ _ _ _ _

set_option maxHeartbeats 1600000 in
-- The (7.6)-family bookkeeping (constituent expansion + per-index coefficient computation)
-- elaborates as a single large proof term; the default budget covers only part of it.
open OddOrder.Peterfalvi.S11 in
open scoped Classical in
open scoped FiniteInduce in
/-- **The `T`-side (13.3.c) distinguished index over a chosen base, general form**
(Peterfalvi (13.8)-for-`T`, issue 0116):
with the (7.6) family `Q_sharp_hypothesis76_base` based at `ζ₀ = Ind_Q^T φ₀` (`Q ⊄ Ker φ₀`,
and either `Ind φ₀` irreducible or its `η₁₀` coefficient zero), under `D = ⊥` (so
`K = QD = Q`) there is a family index `i₁` carrying a
ν-row (`ζ_{i₁} = ν_r = ∑_j ν_{rj}`) with `⟨τψ_{i₁}, η₁₀⟩ = δ = ±1`, and every other
`Q`-nonkernel coefficient vanishes; `‖ζ_{i₁}‖² = p` and `ζ_{i₁}(1) = pv`.

Lives here (not `S15_Tau1T`) because `Q_sharp_hypothesis76_base` is declared in this file,
which imports `S15_Tau1T` (the reverse import would be a cycle).  The commutativity of `Q`
(the abelian half of the (13.2.b)-for-`T` `Q_elementaryAbelian`, constructed from the general
type-`P` chief-factor collapse) enters as the explicit input `hQcomm`: it pins the
family degrees (`ζ_i(1) = [T:Q]`, so `d ≡ 1`) and the degree-one hypotheses of the (13.2.e)
bridge `tau1T_ofHonest_apply_induce_sub`. -/
theorem Hypothesis.exists_muT_index_core_of_base_condition [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hD : hyp.D = ⊥)
    (hQcomm : IsMulCommutative ↥hyp.Q)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.T))
    (hφ₀Q : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
        Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)))
    (hφ₀base :
      OddOrder.RepresentationTheory.IsIrreducibleCharacter
          (ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
            (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)) ∨
        ClassFunction.inner
          (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
              (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ))) hyp.eta10 = 0) :
    ∃ (i₁ : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1)) (δ : ℤ), 0 < i₁ ∧
      ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁)) ∧
      δ ^ 2 = 1 ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i₁ = (δ : ℂ) ∧
      (∀ i : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i)) →
        (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i = 0) ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zetaNormSq i₁ = (hyp.p : ℂ) ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁ 1 = ((hyp.p * hyp.v : ℕ) : ℂ) := by
  classical
  set data := hyp.toTypesIIIIIIVSetupT hG hvd with hdata
  set HU : Subgroup ↥hyp.T := huSub data with hHU
  have hHUeq : HU = (derivedInG hyp.T).subgroupOf hyp.T :=
    huSub_eq_derivedInG_subgroupOf data
  haveI hHUnorm : HU.Normal := huSub_normal data
  -- Subgroup bookkeeping: `Q ≤ T`, `Q.subgroupOf T` normal & abelian, `K = QD = Q` (`hD`),
  -- `Q ≤ T' = HU`.
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  haveI hQnorm : (hyp.Q.subgroupOf hyp.T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQT).mpr (by
      rw [hyp.Q_eq_TF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T)
  haveI hQsubComm : IsMulCommutative ↥(hyp.Q.subgroupOf hyp.T) := by
    have e := Subgroup.subgroupOfEquivOfLe hQT
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hQcomm.is_comm.comm (e a) (e b))⟩⟩
  have hKQ : hyp.K.subgroupOf hyp.T = hyp.Q.subgroupOf hyp.T := by
    have h : hyp.K = hyp.Q := by
      change hyp.Q ⊔ hyp.D = hyp.Q
      rw [hD, sup_bot_eq]
    rw [h]
  have hQle : hyp.Q.subgroupOf hyp.T ≤ HU := by
    rw [hHUeq]
    refine Subgroup.subgroupOf_mono hyp.T ?_
    rw [hyp.T_deriv_eq_QV]
    exact le_sup_left
  -- degree-one values on `Irr (Q.subgroupOf T)` (from `hQcomm`)
  have hdeg1 : ∀ θ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ → θ 1 = 1 := fun _ hθ =>
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative hθ
  -- η-row inner products against `η₁₀`
  have hetaRow : ∀ a : Fin hyp.q,
      ClassFunction.inner (∑ j : Fin hyp.p, hyp.eta a j) hyp.eta10
        = if a = ⟨1, hyp.q_prime.one_lt⟩ then 1 else 0 := by
    intro a
    rw [show hyp.eta10 = hyp.eta ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ from rfl,
      OddOrder.RepresentationTheory.inner_sum_left]
    by_cases ha : a = ⟨1, hyp.q_prime.one_lt⟩
    · rw [if_pos ha,
        Finset.sum_eq_single_of_mem ⟨0, hyp.p_prime.pos⟩ (Finset.mem_univ _)
          (fun j _ hj => by
            rw [hyp.eta_orthonormal a ⟨1, hyp.q_prime.one_lt⟩ j ⟨0, hyp.p_prime.pos⟩,
              if_neg (fun h => hj h.2)]),
        hyp.eta_orthonormal a ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩,
        if_pos ⟨ha, rfl⟩]
    · rw [if_neg ha]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hyp.eta_orthonormal a ⟨1, hyp.q_prime.one_lt⟩ j ⟨0, hyp.p_prime.pos⟩,
        if_neg (fun h => ha h.1)]
  -- the pinned (13.3.c)-`T` row: a nonzero row `r` and a sign `δ = ±1` with
  -- `⟨τ₁T(ν_r), η₁₀⟩ = δ`, all other nonzero rows `τ₁T`-orthogonal to `η₁₀`
  obtain ⟨r, δ, hr0, hδpm, hkeyr, hkey⟩ :
      ∃ (r : Fin hyp.q) (δ : ℤ), r ≠ ⟨0, hyp.q_prime.pos⟩ ∧ (δ = 1 ∨ δ = -1) ∧
        ClassFunction.inner
          (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (∑ j : Fin hyp.p, hyp.nu r j)) hyp.eta10 = (δ : ℂ) ∧
        ∀ s : Fin hyp.q, s ≠ ⟨0, hyp.q_prime.pos⟩ → s ≠ r →
          ClassFunction.inner
            (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
              (∑ j : Fin hyp.p, hyp.nu s j)) hyp.eta10 = 0 := by
    have h1q : (⟨1, hyp.q_prime.one_lt⟩ : Fin hyp.q) ≠ ⟨0, hyp.q_prime.pos⟩ := by
      intro h
      exact absurd (congrArg Fin.val h) one_ne_zero
    rcases hyp.tau1T_ofHonest_nuRow_formula hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief with
      hclean | ⟨hq3, hflip⟩
    · -- clean branch: `r = 1`, `δ = 1`
      refine ⟨⟨1, hyp.q_prime.one_lt⟩, 1, h1q, Or.inl rfl, ?_, ?_⟩
      · rw [hclean ⟨1, hyp.q_prime.one_lt⟩ h1q, hetaRow, if_pos rfl]
        norm_num
      · intro s hs0 hsr
        rw [hclean s hs0, hetaRow, if_neg hsr]
    · -- `q = 3` sign-flip branch: `r = 2`, `δ = −1` (row 2 flips onto η-row 1)
      have h2lt : 2 < hyp.q := by omega
      have h2q : (⟨2, h2lt⟩ : Fin hyp.q) ≠ ⟨0, hyp.q_prime.pos⟩ := by
        intro h
        exact absurd (congrArg Fin.val h) (by norm_num)
      have h21 : (⟨2, h2lt⟩ : Fin hyp.q) ≠ ⟨1, hyp.q_prime.one_lt⟩ := by
        intro h
        exact absurd (congrArg Fin.val h) (by norm_num)
      refine ⟨⟨2, h2lt⟩, -1, h2q, Or.inr rfl, ?_, ?_⟩
      · rw [hflip ⟨2, h2lt⟩ ⟨1, hyp.q_prime.one_lt⟩ h2q h1q h21,
          ClassFunction.inner_neg_left, hetaRow, if_pos rfl]
        norm_num
      · intro s hs0 hsr
        have hs1 : s = ⟨1, hyp.q_prime.one_lt⟩ := by
          have hlt := s.isLt
          have hv0 : s.val ≠ 0 := fun h => hs0 (Fin.ext h)
          have hv2 : s.val ≠ 2 := fun h => hsr (Fin.ext h)
          have hv1 : s.val = 1 := by omega
          exact Fin.ext hv1
        subst hs1
        rw [hflip ⟨1, hyp.q_prime.one_lt⟩ ⟨2, h2lt⟩ h1q h2q (fun h => h21 h.symm),
          ClassFunction.inner_neg_left, hetaRow, if_neg h21, neg_zero]
  -- (13.3.a)-at-`T`: `ν_r = Ind_K^T θ_r`, transported to the `Q`-spelling via `K = Q`
  obtain ⟨θr, hθrirr, hθr1, hνeqK⟩ := hyp.nu_i_isIndQD hG pins r hr0
  set θrQ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ :=
    ClassFunction.compHom (MulEquiv.subgroupCongr hKQ.symm).toMonoidHom θr with hθrQdef
  have hθrQirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter θrQ :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hKQ.symm).surjective hθrirr
  have hνeqQ : (∑ j : Fin hyp.p, hyp.nu r j)
      = ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θrQ := by
    rw [hνeqK]
    exact (OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKQ.symm θr).symm
  have hνmem : (∑ j : Fin hyp.p, hyp.nu r j) ∈ sSet data :=
    sOf_subset_sSet data chief.H0 (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief r hr0)
  -- `Q ⊄ Ker ν_r`: the `𝒳`-source witness survives kernel descent through `HU ⊴ T`
  have hQkerNu : ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (∑ j : Fin hyp.p, hyp.nu r j)) := by
    intro hsub
    obtain ⟨ξ, hξ, hξeq⟩ := hνmem
    have hξker : ¬ ((hInHu data : Set ↥HU) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (ξ : ClassFunction ↥HU ℂ)) := hξ
    obtain ⟨x, hxIn, hxKer⟩ := Set.not_subset.mp hξker
    have hxQ : ((x : ↥hyp.T)) ∈ hyp.Q.subgroupOf hyp.T := by
      have h1 : ((x : ↥hyp.T)) ∈ data.H.subgroupOf hyp.T :=
        Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hxIn)
      rwa [hyp.toTypesIIIIIIVSetupT_H_eq hG hvd] at h1
    have hxker2 : ((x : ↥hyp.T)) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce HU (ξ : ClassFunction ↥HU ℂ)) := by
      have h2 := hsub hxQ
      rwa [hξeq, induceHU_eq_induce data] at h2
    have hdesc := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      ξ.isIrreducible x.2 hxker2
    exact hxKer (by simpa using hdesc)
  -- full-group kernel negation for the transported source `θrQ`
  have hθrQfull : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
      Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θrQ) := by
    intro hker
    apply hQkerNu
    rw [hνeqQ]
    exact OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf le_rfl θrQ hker
  -- `Q`-spelled τ₁T bricks, transported through `K.subgroupOf T = Q.subgroupOf T`
  have himgQ : ((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T)).map
      (MulEquiv.subgroupCongr hKQ).toMonoidHom
      = (hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have hkerK : ∀ θ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ,
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
          Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
          Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (ClassFunction.compHom (MulEquiv.subgroupCongr hKQ).toMonoidHom θ)) := by
    intro θ hθ hcon
    rw [OddOrder.RepresentationTheory.subset_characterKernel_compHom_iff, himgQ] at hcon
    exact hθ hcon
  have hbridgeQ : ∀ θ θ' : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ' →
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
          Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
          Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ') →
      hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ
            - ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ')
        = ClassFunction.induce hyp.T
            (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ
              - ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ') := by
    intro θ θ' hθirr hθ'irr hθQ hθ'Q
    have h := hyp.tau1T_ofHonest_apply_induce_sub hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
      (ClassFunction.compHom (MulEquiv.subgroupCongr hKQ).toMonoidHom θ)
      (ClassFunction.compHom (MulEquiv.subgroupCongr hKQ).toMonoidHom θ')
      (OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
        (MulEquiv.subgroupCongr hKQ).surjective hθirr)
      (OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
        (MulEquiv.subgroupCongr hKQ).surjective hθ'irr)
      (by rw [ClassFunction.compHom_apply, map_one, hdeg1 θ hθirr])
      (by rw [ClassFunction.compHom_apply, map_one, hdeg1 θ' hθ'irr])
      (hkerK θ hθQ) (hkerK θ' hθ'Q)
    rwa [OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKQ θ,
      OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKQ θ'] at h
  have hetaQbrick : ∀ θ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
          Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter
        (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ) →
      ClassFunction.inner
        (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ)) hyp.eta10 = 0 := by
    intro θ hθirr hθQ hind
    have h := hyp.tau1T_ofHonest_induce_inner_eta hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
      ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩
      (ClassFunction.compHom (MulEquiv.subgroupCongr hKQ).toMonoidHom θ)
      (OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
        (MulEquiv.subgroupCongr hKQ).surjective hθirr)
      (hkerK θ hθQ)
      (by rwa [OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKQ θ])
    rw [OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKQ θ] at h
    rw [show hyp.eta10 = hyp.eta ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ from rfl,
      OddOrder.RepresentationTheory.inner_conj_symm, h, star_zero]
  have hφ₀eta : ClassFunction.inner
      (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
        (ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
          (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ))) hyp.eta10 = 0 := by
    rcases hφ₀base with hφ₀irr | hφ₀orth
    · exact hetaQbrick (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)
        φ₀.isIrreducible hφ₀Q hφ₀irr
    · exact hφ₀orth
  -- distinct `Q`-inductions are orthogonal
  have hInd0 : ∀ θ ψ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.Q.subgroupOf hyp.T),
      ClassFunction.induce (hyp.Q.subgroupOf hyp.T) (θ : ClassFunction _ ℂ)
          ≠ ClassFunction.induce (hyp.Q.subgroupOf hyp.T) (ψ : ClassFunction _ ℂ) →
      ClassFunction.inner
        (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) (θ : ClassFunction _ ℂ))
        (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) (ψ : ClassFunction _ ℂ)) = 0 := by
    intro θ ψ hne
    refine OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj θ ψ
      (fun g heq => hne ?_)
    have h1 : ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
        ((OddOrder.RepresentationTheory.IrreducibleCharacter.conjBy g θ :
          OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.T)) :
            ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)
        = ClassFunction.induce (hyp.Q.subgroupOf hyp.T) (θ : ClassFunction _ ℂ) := by
      rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy]
      exact OddOrder.RepresentationTheory.ClassFunction.induce_conjBy_eq
        (G := ↥hyp.T) (H := hyp.Q.subgroupOf hyp.T) g _
    rw [← h1, heq]
  -- ⟨τ₁T(Ind_Q^T θ), η₁₀⟩ = 0 for every `Q`-nonkernel irreducible source with `Ind θ ≠ ν_r`:
  -- two-stage constituent expansion over `HU`, per-constituent (5.3.b)/(13.3.c) dispatch
  have hTau1IndEta : ∀ θ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
          Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ ≠ ∑ j : Fin hyp.p, hyp.nu r j →
      ClassFunction.inner
        (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ)) hyp.eta10 = 0 := by
    intro θ hθirr hθQ hθne
    -- transport onto `Q-in-HU`
    have hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom θ) :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
        (Subgroup.subgroupOfEquivOfLe hQle).surjective hθirr
    have hθ'Q : ¬ ((((hyp.Q.subgroupOf hyp.T).subgroupOf HU).subgroupOf
          ((hyp.Q.subgroupOf hyp.T).subgroupOf HU) :
        Set ↥((hyp.Q.subgroupOf hyp.T).subgroupOf HU)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom θ)) := by
      rw [OddOrder.RepresentationTheory.subset_characterKernel_compHom_iff]
      have himg : (((hyp.Q.subgroupOf hyp.T).subgroupOf HU).subgroupOf
            ((hyp.Q.subgroupOf hyp.T).subgroupOf HU)).map
            (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom
          = (hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) := by
        ext y
        rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
          Subgroup.mem_subgroupOf]
        rfl
      rw [himg]
      exact hθQ
    -- two-stage constituent expansion with `ℕ`-coefficients
    have hzeta : ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ
        = ∑ s : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU,
            ClassFunction.inner
              (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom θ)
              (ClassFunction.restrict ((hyp.Q.subgroupOf hyp.T).subgroupOf HU)
                (s : ClassFunction ↥HU ℂ))
              • ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) := by
      rw [← OddOrder.RepresentationTheory.induce_induce_subgroupOf hQle θ,
        OddOrder.RepresentationTheory.induce_eq_sum_inner_restrict_smul
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom θ),
        ClassFunction.induce_sum]
      exact Finset.sum_congr rfl fun s _ => ClassFunction.induce_smul _ _ _
    have hcoefNat : ∀ s : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU, ∃ n : ℕ,
        ClassFunction.inner
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom θ)
          (ClassFunction.restrict ((hyp.Q.subgroupOf hyp.T).subgroupOf HU)
            (s : ClassFunction ↥HU ℂ)) = (n : ℂ) := by
      intro s
      have hResChar : IsCharacter (ClassFunction.restrict
          ((hyp.Q.subgroupOf hyp.T).subgroupOf HU) (s : ClassFunction ↥HU ℂ)) :=
        OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter _
      obtain ⟨n, hn⟩ := hResChar.exists_natCast_inner_irreducible hθ'irr
      exact ⟨n, by rw [OddOrder.RepresentationTheory.inner_conj_symm, hn, star_natCast]⟩
    choose k hk using hcoefNat
    have hmem : ∀ s : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU, k s ≠ 0 →
        ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) ∈ sSet data := by
      intro s hks
      rw [mem_sSet]
      refine ⟨s, ?_, rfl⟩
      change ¬ ((hInHu data : Set ↥HU) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction ↥HU ℂ))
      have hHInHu : (hInHu data : Set ↥HU)
          = ((hyp.Q.subgroupOf hyp.T).subgroupOf HU : Set ↥HU) := by
        congr 1
        change (data.H.subgroupOf hyp.T).subgroupOf HU
          = (hyp.Q.subgroupOf hyp.T).subgroupOf HU
        rw [hyp.toTypesIIIIIIVSetupT_H_eq hG hvd]
      rw [hHInHu]
      have hs : ClassFunction.inner
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom θ)
          (ClassFunction.restrict ((hyp.Q.subgroupOf hyp.T).subgroupOf HU)
            (s : ClassFunction ↥HU ℂ)) ≠ 0 := by
        rw [hk s]
        exact_mod_cast hks
      exact constituent_P_not_subset_characterKernel ((hyp.Q.subgroupOf hyp.T).subgroupOf HU)
        ((hyp.Q.subgroupOf hyp.T).subgroupOf HU)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom θ) hθ'irr hθ'Q s hs
    -- expand the τ₁T-image and dispatch per constituent
    have hzetaN : ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ
        = ∑ s : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU,
            k s • ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) := by
      rw [hzeta]
      exact Finset.sum_congr rfl fun s _ => by rw [hk s, Nat.cast_smul_eq_nsmul]
    rw [hzetaN, map_sum, OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun s _ => ?_
    rcases Nat.eq_zero_or_pos (k s) with hk0 | hkpos
    · rw [hk0, zero_smul, map_zero, ClassFunction.inner_zero_left]
    · rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ (k s), ClassFunction.inner_smul_left]
      suffices hterm0 : ClassFunction.inner
          (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))) hyp.eta10 = 0 by
        rw [hterm0, mul_zero]
      by_cases hsirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
          (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))
      · -- irreducible constituent: (5.3.b)-`T` grid orthogonality
        exact hyp.tau1T_ofHonest_image_inner_eta_eq_zero hG hnoV pins hvd hTP Tdata hU hW1 hW2
          chief (hmem s hkpos.ne') hsirr ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩
      · -- reducible constituent: a nonzero ν-row `ν_{s₀}` with `s₀ ≠ r`
        obtain ⟨s₀, hs₀ne, heqrow⟩ :=
          hyp.sSet_reducible_eq_nuRowSum hG pins hvd (hmem s hkpos.ne') hsirr
        by_cases hs₀r : s₀ = r
        · -- `s₀ = r` would make `ν_r` a constituent of `Ind_Q θ`, contradicting
          -- `⟨Ind_Q θ, ν_r⟩ = 0` (distinct-source `Q`-inductions are orthogonal)
          exfalso
          subst hs₀r
          have hzmu : ClassFunction.inner (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ)
              (∑ j : Fin hyp.p, hyp.nu s₀ j) = 0 := by
            rw [hνeqQ]
            exact hInd0 ⟨θ, hθirr⟩ ⟨θrQ, hθrQirr⟩ fun h => hθne (h.trans hνeqQ.symm)
          have hexp : ClassFunction.inner (ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θ)
              (∑ j : Fin hyp.p, hyp.nu s₀ j)
              = ∑ s' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU, (k s' : ℂ) *
                  ClassFunction.inner (ClassFunction.induce HU (s' : ClassFunction ↥HU ℂ))
                    (∑ j : Fin hyp.p, hyp.nu s₀ j) := by
            rw [hzeta, OddOrder.RepresentationTheory.inner_sum_left]
            refine Finset.sum_congr rfl fun s' _ => ?_
            rw [hk s', ClassFunction.inner_smul_left]
          have hterm : ∀ s' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU, ∃ n : ℕ,
              (k s' : ℂ) * ClassFunction.inner
                (ClassFunction.induce HU (s' : ClassFunction ↥HU ℂ))
                (∑ j : Fin hyp.p, hyp.nu s₀ j) = (n : ℂ) := by
            intro s'
            rcases Nat.eq_zero_or_pos (k s') with h0 | hpos
            · exact ⟨0, by rw [h0]; simp⟩
            · by_cases heq : ClassFunction.induce HU (s' : ClassFunction ↥HU ℂ)
                  = ∑ j : Fin hyp.p, hyp.nu s₀ j
              · refine ⟨k s' * hyp.p, ?_⟩
                rw [heq, hyp.nuRow_inner pins s₀ s₀, if_pos rfl]
                push_cast
                ring
              · exact ⟨0, by rw [sSet_pairwiseOrthogonal data (hmem s' hpos.ne') hνmem heq,
                  mul_zero, Nat.cast_zero]⟩
          choose n hn using hterm
          have hsumC : ∑ s' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU,
              ((n s' : ℕ) : ℂ) = 0 := by
            rw [Finset.sum_congr rfl fun s' _ => (hn s').symm, ← hexp, hzmu]
          have hsumN : ∑ s' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥HU,
              n s' = 0 := by
            rw [← Nat.cast_sum] at hsumC
            exact_mod_cast hsumC
          have hn0 : n s = 0 := (Finset.sum_eq_zero_iff.mp hsumN) s (Finset.mem_univ s)
          have hcontra : ((n s : ℕ) : ℂ) ≠ 0 := by
            rw [← hn s, heqrow, hyp.nuRow_inner pins s₀ s₀, if_pos rfl]
            exact mul_ne_zero (Nat.cast_ne_zero.mpr hkpos.ne')
              (Nat.cast_ne_zero.mpr hyp.p_prime.pos.ne')
          exact hcontra (by rw [hn0, Nat.cast_zero])
        · -- `s₀ ≠ r`: the pinned η-row inner product vanishes
          rw [heqrow]
          exact hkey s₀ hs₀ne hs₀r
  -- the distinguished family index: the family cover at the transported ν_r-source
  obtain ⟨i₁, hi₁0⟩ :=
    (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_family_cover ⟨θrQ, hθrQirr⟩
  have hζi₁ : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁
      = ∑ j : Fin hyp.p, hyp.nu r j := by
    rw [hi₁0, hνeqQ]
    congr!
  have hζ0 : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta 0
      = ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
          (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ) :=
    Q_sharp_hypothesis76_base_zeta_zero hG hyp hvd φ₀
  have hi₁pos : 0 < i₁ := by
    rw [Fin.pos_iff_ne_zero]
    intro h0
    have hbaseEq : (∑ j : Fin hyp.p, hyp.nu r j)
        = ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
            (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ) := by
      rw [← hζi₁, h0, hζ0]
    have hinnerEq := congrArg
      (fun χ : ClassFunction ↥hyp.T ℂ => ClassFunction.inner
        (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief χ) hyp.eta10)
      hbaseEq
    rw [hkeyr, hφ₀eta] at hinnerEq
    rcases hδpm with hδ | hδ <;> rw [hδ] at hinnerEq <;> norm_num at hinnerEq
  -- family degrees are constant (`Q` abelian) ⟹ `d ≡ 1`
  have hzeta_one : ∀ j : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1),
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta j 1
        = ((hyp.Q.subgroupOf hyp.T).index : ℂ) := by
    intro j
    obtain ⟨θ0, hθ0⟩ := (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_induced j
    obtain ⟨θQ, hθQirr, hθQeq⟩ : ∃ θQ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ,
        OddOrder.RepresentationTheory.IsIrreducibleCharacter θQ ∧
        (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta j
          = ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θQ :=
      ⟨θ0.val, θ0.2, by rw [hθ0]; congr!⟩
    rw [hθQeq, ClassFunction.induce_apply_one, hdeg1 θQ hθQirr, mul_one]
  have hidx0 : ((hyp.Q.subgroupOf hyp.T).index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := hyp.Q.subgroupOf hyp.T)
  have hd1 : ∀ j : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1),
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).d j = 1 := by
    intro j
    have h := (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_one_eq_d_mul j
    rw [hzeta_one j, hzeta_one 0] at h
    field_simp at h
    exact h.symm
  -- conjunct 4: the distinguished coefficient is `δ`
  have hc1 : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i₁ = (δ : ℂ) := by
    rw [show (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i₁
        = ClassFunction.inner
            ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).hyp71.τ
              ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).psiSupp i₁)) hyp.eta10 from rfl,
      show (Q_sharp_hypothesis76_base hG hyp hvd φ₀).hyp71.τ
        = (Q_sharp_hypothesis71 hG hyp hvd).τ from rfl,
      Q_sharp_tau_eq_induce hG hyp hvd]
    have hψ : (((Q_sharp_hypothesis76_base hG hyp hvd φ₀).psiSupp i₁) :
        ClassFunction ↥hyp.T ℂ)
        = ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θrQ
          - ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
              (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ) := by
      rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1 i₁, one_smul, hζi₁, hζ0, hνeqQ]
    rw [hψ,
      ← hbridgeQ θrQ (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ) hθrQirr
        φ₀.isIrreducible hθrQfull hφ₀Q,
      map_sub, ClassFunction.inner_sub_left, ← hνeqQ, hkeyr,
      hφ₀eta,
      sub_zero]
  -- conjunct 5: all other `Q`-nonkernel coefficients vanish
  have hmid : ∀ i : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1), 0 < i → i ≠ i₁ →
      ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i)) →
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i = 0 := by
    intro i _hipos hine hiP
    obtain ⟨θi0, hθi0⟩ := (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_induced i
    obtain ⟨θiQ, hθiQirr, hθiQeq⟩ : ∃ θiQ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ,
        OddOrder.RepresentationTheory.IsIrreducibleCharacter θiQ ∧
        (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i
          = ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θiQ :=
      ⟨θi0.val, θi0.2, by rw [hθi0]; congr!⟩
    have hθiQfull : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
        Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θiQ) := by
      intro hker
      apply hiP
      rw [hθiQeq]
      exact OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf le_rfl θiQ hker
    have hne : ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θiQ
        ≠ ∑ j : Fin hyp.p, hyp.nu r j := by
      intro heq
      exact hine ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_injective
        (by rw [hθiQeq, heq, hζi₁]))
    rw [show (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i
        = ClassFunction.inner
            ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).hyp71.τ
              ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).psiSupp i)) hyp.eta10 from rfl,
      show (Q_sharp_hypothesis76_base hG hyp hvd φ₀).hyp71.τ
        = (Q_sharp_hypothesis71 hG hyp hvd).τ from rfl,
      Q_sharp_tau_eq_induce hG hyp hvd]
    have hψi : (((Q_sharp_hypothesis76_base hG hyp hvd φ₀).psiSupp i) :
        ClassFunction ↥hyp.T ℂ)
        = ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θiQ
          - ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
              (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ) := by
      rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1 i, one_smul, hθiQeq, hζ0]
    rw [hψi,
      ← hbridgeQ θiQ (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)
        hθiQirr φ₀.isIrreducible hθiQfull hφ₀Q,
      map_sub, ClassFunction.inner_sub_left,
      hφ₀eta,
      hTau1IndEta θiQ hθiQirr hθiQfull hne,
      sub_zero]
  -- conjuncts 6, 7 and the sign square
  have hnormSq : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zetaNormSq i₁ = (hyp.p : ℂ) := by
    rw [show (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zetaNormSq i₁
        = ClassFunction.inner ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁)
            ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁) from rfl,
      hζi₁, hyp.nuRow_inner pins r r, if_pos rfl]
  have hdegVal : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁ 1
      = ((hyp.p * hyp.v : ℕ) : ℂ) := by
    rw [hζi₁, hyp.nuRow_apply_one hG pins r hr0]
    push_cast
    ring
  have hδ2 : δ ^ 2 = 1 := by
    rcases hδpm with h | h <;> rw [h] <;> norm_num
  refine ⟨i₁, δ, hi₁pos, ?_, hδ2, hc1, hmid, hnormSq, hdegVal⟩
  rw [hζi₁]
  exact hQkerNu

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The `T`-side (13.3.c) distinguished index over an irreducibly induced base**
(Peterfalvi (13.8)-for-`T`, issue 2035 #90): compatibility form of
`exists_muT_index_core_of_base_condition`. -/
theorem Hypothesis.exists_muT_index_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hD : hyp.D = ⊥)
    (hQcomm : IsMulCommutative ↥hyp.Q)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.T))
    (hφ₀Q : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
        Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)))
    (hφ₀irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
        (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ))) :
    ∃ (i₁ : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1)) (δ : ℤ), 0 < i₁ ∧
      ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁)) ∧
      δ ^ 2 = 1 ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i₁ = (δ : ℂ) ∧
      (∀ i : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i)) →
        (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i = 0) ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zetaNormSq i₁ = (hyp.p : ℂ) ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁ 1 = ((hyp.p * hyp.v : ℕ) : ℂ) := by
  exact hyp.exists_muT_index_core_of_base_condition hG hnoV pins hvd hTP Tdata hU hW1 hW2
    chief hD hQcomm φ₀ hφ₀Q (Or.inl hφ₀irr)

section GenericAlphaIntegrality

/-! ### The (13.5.a) integrality over an abstract (7.6) datum

Generic forms of the `α(1) ∈ ℤ` integrality of the correction term `hypothesis76AlphaFun`
(Peterfalvi (13.5.a) "`α(1) = qb` with `b` an integer", integrality half), over any
`H76 : Hypothesis76 G A L` and kernel subgroup `P' ≤ L` — the abstract layer shared by the
`S`-side (`H_sharp_alphaCF_restrict_mem_ZIrr` route) and the `T`-side ((13.8):
`Q_sharp_hypothesis76_base`, `P' = Q.subgroupOf T`). -/

variable {A : Set G} {L : Subgroup G}

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **Generic (13.5.a) integrality of the correction at `1`**: with integer (7.7.a) coefficients
`c_i ∈ ℤ`, the `P'`-kernel tail `α = hypothesis76AlphaFun` restricts on `K = H76.H` to
`∑ c_i • ((1/‖ζ_i‖²)·Res ζ_i) ∈ ℤ[Irr K]` (each normalized restriction is the conjugate-orbit
character, `hypothesis76_inv_normSq_restrict_zeta_mem_ZIrr`), so `α(1) ∈ ℤ`
(`exists_int_apply_one_of_mem_ZIrr`).  The generic form of the
`H_sharp_alphaCF_restrict_mem_ZIrr`-route to Peterfalvi (13.5) "`α(1) = qb` with `b` an
integer"; instantiated by the `T`-side at `Q_sharp_hypothesis76_base`
(`exists_etaT_alphaFun_one_int_core`). -/
theorem hypothesis76AlphaFun_one_int [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ)
    (hc : ∀ i : Fin (H76.n + 1), ∃ z : ℤ, H76.cCoeff χ i = (z : ℂ)) :
    ∃ α1 : ℤ, hypothesis76AlphaFun H76 P' χ 1 = (α1 : ℂ) := by
  classical
  have hres := hypothesis76AlphaCF_restrict_mem_ZIrr H76 P' χ hc
  obtain ⟨z, hz⟩ := OddOrder.Algebra.exists_int_apply_one_of_mem_ZIrr hres
  refine ⟨z, ?_⟩
  simpa [ClassFunction.restrict_apply] using hz

end GenericAlphaIntegrality

open scoped Classical in
open scoped FiniteInduce in
/-- **The `T`-side (7.7.a) coefficients of a virtual character are integers** (mirror of
`H_sharp_cCoeff_int` over the chosen-base `(T, Q^#)` family): `c_i = ⟨τψ_i, χ⟩` with both
arguments virtual characters — `ψ_i = ζ_i − d_i ζ_0` has `d_i = 1` (all family degrees are
`[T : Q]` since `Q` is abelian, the explicit input `hQcomm` — the abelian half of the
(13.2.b)-for-`T` "Q elementary abelian") and the Dade image `τψ_i ∈ ℤ[Irr G]` ((2.10)
`preserves_virtualCharacters` of the `(T, Q^#)` TI-isometry). -/
theorem Q_sharp_hypothesis76_base_cCoeff_int [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (hQcomm : IsMulCommutative ↥hyp.Q)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.T))
    {χ : ClassFunction G ℂ} (hχ : χ ∈ ZIrr G) :
    ∀ i : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1),
      ∃ z : ℤ, (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff χ i = (z : ℂ) := by
  classical
  intro i
  set K : Subgroup ↥hyp.T := (Q_sharp_hypothesis76_base hG hyp hvd φ₀).H.subgroupOf hyp.T
    with hKdef
  haveI hKnorm : K.Normal :=
    OddOrder.Peterfalvi.S09.Cert.subgroupOf_normal_of_conj
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).H_normal_in_L
  -- `K ≅ Q` is abelian, so every `θ_j` is linear and all `ζ_j` have degree `[T:K]`.
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  haveI hKcomm : IsMulCommutative ↥K := by
    have e := Subgroup.subgroupOfEquivOfLe
      (show (Q_sharp_hypothesis76_base hG hyp hvd φ₀).H ≤ hyp.T from hQT)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hQcomm.is_comm.comm (e a) (e b))⟩⟩
  -- Degrees: `ζ_j(1) = [T:K]` for every `j`, so the degree ratio is `1`.
  have hzeta_one : ∀ j : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1),
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta j 1 = (K.index : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_induced j
    have hθ1 : (θ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        θ.2
    rw [hθ, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one]
  have hidx0 : (K.index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := K)
  have hd1 : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).d i = 1 := by
    have h := (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_one_eq_d_mul i
    rw [hzeta_one i, hzeta_one 0] at h
    field_simp at h
    exact h.symm
  -- `ψ_i = ζ_i − ζ_0 ∈ ℤ[Irr T]`.
  have hzetaZ : ∀ j : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1),
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta j ∈ ZIrr ↥hyp.T := by
    intro j
    obtain ⟨θ, hθ⟩ := (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_induced j
    rw [hθ]
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr K (θ.2.mem_ZIrr)
  have hψZ : ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).psiSupp i : ClassFunction ↥hyp.T ℂ)
      ∈ ZIrr ↥hyp.T := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1, one_smul]
    exact Submodule.sub_mem _ (hzetaZ i) (hzetaZ 0)
  -- The Dade image is a virtual character ((2.10) `preserves_virtualCharacters`).
  have hτeq : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).hyp71.τ
      = ((Q_sharp_dadeHypothesis hG hyp hvd).fullDadeIsometryData
          (Q_sharp_hconj hG hyp hvd)).toDadeIsometryData.toDadeMap := rfl
  have hpres : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).hyp71.τ
      ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).psiSupp i) ∈ ZIrr G := by
    rw [hτeq]
    exact ((Q_sharp_dadeHypothesis hG hyp hvd).fullDadeIsometryData
      (Q_sharp_hconj hG hyp hvd)).preserves_virtualCharacters _ hψZ
  -- `c_i = ⟨τψ_i, χ⟩ ∈ ℤ`.
  rw [OddOrder.Peterfalvi.S09.Hypothesis76.cCoeff]
  exact ClassFunction.inner_mem_ZIrr_int hpres hχ

open scoped Classical in
open scoped FiniteInduce in
/-- **The `T`-side correction has integer value at `1`** over the chosen base — the core
restatement of `exists_etaT_alphaFun_one_int` (Peterfalvi (13.5.a)-for-`T` integrality,
issue 2035 #22 T-side twin): `α(1) ∈ ℤ` for the `Q`-kernel tail `α = hypothesis76AlphaFun` of
the `(T, Q^#)` (7.7.a) decomposition of `η₁₀`.  The commutativity of `Q` (the abelian half of
the (13.2.b)-for-`T` `Q_elementaryAbelian`, available before (14.9)) enters as the explicit
input `hQcomm`: it makes `α|_Q ∈ ℤ[Irr Q]`
via the integer (7.7.a) coefficients (`Q_sharp_hypothesis76_base_cCoeff_int`, using
`η₁₀ ∈ ℤ[Irr G]` = `eta10_mem_ZIrr`) through the generic route
(`hypothesis76AlphaFun_one_int`). -/
theorem Hypothesis.exists_etaT_alphaFun_one_int_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1)
    (hQcomm : IsMulCommutative ↥hyp.Q)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.T)) :
    ∃ α1 : ℤ, hypothesis76AlphaFun (Q_sharp_hypothesis76_base hG hyp hvd φ₀)
      (hyp.Q.subgroupOf hyp.T) hyp.eta10 1 = (α1 : ℂ) :=
  hypothesis76AlphaFun_one_int (Q_sharp_hypothesis76_base hG hyp hvd φ₀)
    (hyp.Q.subgroupOf hyp.T) hyp.eta10
    (Q_sharp_hypothesis76_base_cCoeff_int hG hyp hvd hQcomm φ₀ hyp.eta10_mem_ZIrr)

end OddOrder.Peterfalvi.S15
