/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibley

/-!
# Peterfalvi Appendix IV: the Feit–Sibley Theorem — supporting layer (pp. 145–150)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix IV, pp. 145–150.  Support for the Theorem `feit_sibley_coherence`
(campaign issue 1054): the derived subgroups `S' = [S,S]` and `Q' = [Q,Q]` of the
"Hypotheses and Notation" block (p. 145) with their elementary group-theoretic
facts, feeding the Remark (`𝒮(Q')` is coherent), the reduction steps (1)–(3) and
the endgame (4)–(8) of pp. 146–150.

The statements live in the `Hypothesis` namespace of
`OddOrder.Peterfalvi.Appendices.FeitSibley` and extend the structure API of that
file.
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

open scoped commutatorElement ComplexOrder

variable {G : Type*} [Group G]

namespace Hypothesis

variable (hyp : Hypothesis G)

/-! ## The derived subgroups `S' = [S,S]` and `Q' = [Q,Q]` (p. 145) -/

/-- **`S' = [S,S]`** (p. 145, "Set `S' = [S,S]`"). -/
def Sder : Subgroup G := ⁅hyp.S, hyp.S⁆

/-- **`Q' = [Q,Q]`** (p. 145, "`Q' = [Q,Q]`"). -/
def Qder : Subgroup G := ⁅hyp.Q, hyp.Q⁆

theorem Sder_le_S : hyp.Sder ≤ hyp.S := by
  change ⁅hyp.S, hyp.S⁆ ≤ hyp.S
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  exact hyp.S.mul_mem (hyp.S.mul_mem (hyp.S.mul_mem hg hh) (hyp.S.inv_mem hg))
    (hyp.S.inv_mem hh)

theorem Qder_le_Q : hyp.Qder ≤ hyp.Q := by
  change ⁅hyp.Q, hyp.Q⁆ ≤ hyp.Q
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  exact hyp.Q.mul_mem (hyp.Q.mul_mem (hyp.Q.mul_mem hg hh) (hyp.Q.inv_mem hg))
    (hyp.Q.inv_mem hh)

theorem Sder_le_H : hyp.Sder ≤ hyp.H :=
  le_trans hyp.Sder_le_S hyp.S_le_H

theorem Qder_le_H : hyp.Qder ≤ hyp.H :=
  le_trans hyp.Qder_le_Q hyp.Q_le_H

/-- Conjugation by `h ∈ H` fixes `Q` as a set: `Q^h = Q` (both inclusions of the
elementwise normality `Q ⊴ H`). -/
theorem Q_map_conj_eq {h : G} (hh : h ∈ hyp.H) :
    hyp.Q.map (MulAut.conj h).toMonoidHom = hyp.Q := by
  apply le_antisymm
  · rintro _ ⟨x, hxQ, rfl⟩
    exact hyp.Q_normal_in_H h hh x hxQ
  · intro x hxQ
    refine ⟨h⁻¹ * x * h, ?_, ?_⟩
    · have := hyp.Q_normal_in_H h⁻¹ (hyp.H.inv_mem hh) x hxQ
      simpa using this
    · simp [MulAut.conj]
      group

/-- **`Q' ⊴ H`** (elementwise): `H`-conjugation fixes `Q` (`Q_map_conj_eq`), hence
fixes `[Q,Q]` (`Subgroup.map_commutator`). -/
theorem Qder_conj_mem_of_mem_H {h : G} (hh : h ∈ hyp.H) {x : G}
    (hx : x ∈ hyp.Qder) : h * x * h⁻¹ ∈ hyp.Qder := by
  have hmap : hyp.Qder.map (MulAut.conj h).toMonoidHom = hyp.Qder := by
    change (⁅hyp.Q, hyp.Q⁆ : Subgroup G).map (MulAut.conj h).toMonoidHom = ⁅hyp.Q, hyp.Q⁆
    rw [Subgroup.map_commutator, hyp.Q_map_conj_eq hh]
  rw [← hmap]
  exact ⟨x, hx, rfl⟩

theorem Sder_le_Q : hyp.Sder ≤ hyp.Q :=
  le_trans hyp.Sder_le_S hyp.S_le_Q

/-- `Q'.subgroupOf H ⊴ ↥H`, the `Subgroup.Normal` instance form of
`Qder_conj_mem_of_mem_H`. -/
theorem Qder_subgroupOf_H_normal : (hyp.Qder.subgroupOf hyp.H).Normal := by
  constructor
  intro x hx g
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  simpa using hyp.Qder_conj_mem_of_mem_H g.2 hx

/-- `𝒮(Q')` is closed under complex conjugation: `χ̄` is irreducible when `χ` is,
`Q₁ ⊄ Ker χ̄` iff `Q₁ ⊄ Ker χ` (conjugating the constancy equation), and likewise
`Q' ⊆ Ker` is preserved.  This is the conjugation-closure input for the coherence
of `𝒮(Q')` (Remark, p. 145). -/
theorem conj_mem_SsetOf_Qder [Finite G] {χ : ClassFunction ↥hyp.H ℂ}
    (hχ : χ ∈ hyp.SsetOf hyp.Qder) : χ.conj ∈ hyp.SsetOf hyp.Qder := by
  obtain ⟨⟨hirr, hker1⟩, hkerQ'⟩ := hχ
  refine ⟨⟨hirr.conj, ?_⟩, ?_⟩
  · -- `Q₁ ⊄ Ker χ̄` from `Q₁ ⊄ Ker χ`
    intro hall
    apply hker1
    intro x hxQ1
    have := hall x hxQ1
    rw [ClassFunction.conj_apply, ClassFunction.conj_apply] at this
    exact star_injective this
  · -- `Q' ⊆ Ker χ̄` from `Q' ⊆ Ker χ`
    intro x hxQ'
    rw [ClassFunction.conj_apply, ClassFunction.conj_apply, hkerQ' x hxQ']

/-! ## `H = Q ⋊ D` counting: `[H : Q] = d` -/

/-- `Q.subgroupOf H` and `D.subgroupOf H` are complements in `↥H` (subtype form of
`H = Q ⋊ D`): disjointness is `Q ∩ D = 1`, coverage is `Q·D = H`
(`exists_mem_Q_mul_mem_D_subtype`). -/
theorem isComplement'_Q_D :
    (hyp.Q.subgroupOf hyp.H).IsComplement' (hyp.D.subgroupOf hyp.H) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [Subgroup.disjoint_def]
    intro x hxQ hxD
    rw [Subgroup.mem_subgroupOf] at hxQ hxD
    have hbot : (x : G) ∈ hyp.Q ⊓ hyp.D := ⟨hxQ, hxD⟩
    rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
    exact Subtype.ext hbot
  · ext g
    simp only [Set.mem_univ, iff_true]
    obtain ⟨q, hqQ, δ, hδD, rfl⟩ := hyp.exists_mem_Q_mul_mem_D_subtype g
    exact Set.mul_mem_mul (Subgroup.mem_subgroupOf.mpr hqQ)
      (Subgroup.mem_subgroupOf.mpr hδD)

/-- `|Q| · |D| = |H|` (from `isComplement'_Q_D`). -/
theorem card_Q_mul_card_D : Nat.card ↥hyp.Q * Nat.card ↥hyp.D = Nat.card ↥hyp.H := by
  have h := hyp.isComplement'_Q_D.card_mul
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q_le_H).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.D_le_H).toEquiv] at h

/-- **`[H : Q] = d`**: the index of `Q.subgroupOf H` in `↥H` is `d = |D|`. -/
theorem index_Q_subgroupOf_eq_d [Finite G] :
    (hyp.Q.subgroupOf hyp.H).index = hyp.d := by
  have hcardQ : Nat.card ↥(hyp.Q.subgroupOf hyp.H) = Nat.card ↥hyp.Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q_le_H).toEquiv
  have hmul : (hyp.Q.subgroupOf hyp.H).index * Nat.card ↥hyp.Q
      = Nat.card ↥hyp.D * Nat.card ↥hyp.Q := by
    calc (hyp.Q.subgroupOf hyp.H).index * Nat.card ↥hyp.Q
        = (hyp.Q.subgroupOf hyp.H).index * Nat.card ↥(hyp.Q.subgroupOf hyp.H) := by
          rw [hcardQ]
      _ = Nat.card ↥hyp.H := Subgroup.index_mul_card _
      _ = Nat.card ↥hyp.Q * Nat.card ↥hyp.D := hyp.card_Q_mul_card_D.symm
      _ = Nat.card ↥hyp.D * Nat.card ↥hyp.Q := mul_comm _ _
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul

/-! ## Degrees on `𝒮(Q')` (Remark, p. 145): every member has degree `d` -/

section CharacterLayer

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
variable [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- **A member `φ ∈ Irr(Q)` inducing into `𝒮(Q')` is trivial on `Q'`**: if
`Ind_Q^H φ` is irreducible and constant on `Q'` (`LeKer`), then `φ` is constant on
`Q'.subgroupOf Q`.  Mirror of the Lemma 2(a) kernel argument with `Q₁` replaced by
`Q'`: a nontrivial constituent `θ ∈ Irr(Q')` of `Res φ` would, through the θ-part
bound (`restrictionMultiplicity_mul_le_restrictionMultiplicity`, with
`⟨Res_Q Ind φ, φ⟩ = 1` by Frobenius reciprocity and irreducibility of `Ind φ`),
give `Ind φ` a nontrivial `Q'`-constituent, which a character constant on `Q'`
cannot have (`restrictionMultiplicity_eq_zero_of_forall_eq_one`). -/
theorem forall_eq_one_of_leKer_Qder [Finite G]
    {φ : ClassFunction ↥(hyp.Q.subgroupOf hyp.H) ℂ} (hφirr : IsIrreducibleCharacter φ)
    (hindirr : IsIrreducibleCharacter
      (ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ))
    (hker : hyp.LeKer (ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ) hyp.Qder) :
    ∀ y : ↥((hyp.Qder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)),
      φ (y : ↥(hyp.Q.subgroupOf hyp.H)) = φ 1 := by
  classical
  have hHT : hyp.Qder.subgroupOf hyp.H ≤ hyp.Q.subgroupOf hyp.H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hyp.Qder_le_Q (Subgroup.mem_subgroupOf.mp hx))
  -- finiteness / invertibility bookkeeping
  letI : Fintype ↥(hyp.Q.subgroupOf hyp.H) := Fintype.ofFinite _
  letI : Fintype ↥(hyp.Qder.subgroupOf hyp.H) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(hyp.Qder.subgroupOf hyp.H) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Fintype ↥((hyp.Qder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) :=
    Fintype.ofFinite _
  letI : Invertible
      ((Nat.card ↥((hyp.Qder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Finite (IrreducibleCharacter
      ↥((hyp.Qder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))) :=
    finite_irreducibleCharacter
  letI : Fintype (IrreducibleCharacter
      ↥((hyp.Qder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))) := Fintype.ofFinite _
  by_contra hcon
  -- a nontrivial constituent `θ'' ∈ Irr(Q'-in-Q)` of `Res φ`
  obtain ⟨θ'', hθ''ne, hθ''over⟩ := exists_ne_trivial_liesOver_of_not_forall_eq_one
    (⟨φ, hφirr⟩ : IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.H)) hcon
  -- transport `θ''` to `Irr(Q'-in-H)` along `↥(Q'-in-Q) ≃* ↥(Q'-in-H)`
  have hθirr : IsIrreducibleCharacter (ClassFunction.compHom
      (Subgroup.subgroupOfEquivOfLe hHT).symm.toMonoidHom
      (θ'' : ClassFunction
        ↥((hyp.Qder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) ℂ)) :=
    IsIrreducibleCharacter.compHom_of_surjective
      (Subgroup.subgroupOfEquivOfLe hHT).symm.surjective θ''.isIrreducible
  have hθne : (⟨_, hθirr⟩ : IrreducibleCharacter ↥(hyp.Qder.subgroupOf hyp.H))
      ≠ trivialIrreducibleCharacter _ := fun h =>
    compHom_mulEquiv_ne_trivial (Subgroup.subgroupOfEquivOfLe hHT).symm
      (fun hc => hθ''ne (Subtype.ext hc)) (congrArg Subtype.val h)
  have hround : ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).symm.toMonoidHom
        (θ'' : ClassFunction
          ↥((hyp.Qder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) ℂ))
      = (θ'' : ClassFunction
          ↥((hyp.Qder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) ℂ) :=
    compHom_toMonoidHom_compHom_symm (Subgroup.subgroupOfEquivOfLe hHT) _
  -- `Ind φ` constant on `Q'` kills the transported θ-multiplicity …
  have hzero := restrictionMultiplicity_eq_zero_of_forall_eq_one
    (N := hyp.Qder.subgroupOf hyp.H) (ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ)
    (fun x => hker (x : ↥hyp.H) (Subgroup.mem_subgroupOf.mp x.2)) hθne
  simp only [IrreducibleCharacter.coe_mk] at hzero
  -- … but the θ-part bound forces it nonzero
  have hfrob := inner_induce_coe_eq_restrictionMultiplicity (G := ↥hyp.H)
    (⟨φ, hφirr⟩ : IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.H))
    (⟨ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ, hindirr⟩ :
      IrreducibleCharacter ↥hyp.H)
  have hself := irreducibleCharacter_inner_eq_ite (G := ↥hyp.H)
    (⟨ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ, hindirr⟩ :
      IrreducibleCharacter ↥hyp.H)
    (⟨ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ, hindirr⟩ :
      IrreducibleCharacter ↥hyp.H)
  rw [if_pos rfl] at hself
  simp only [IrreducibleCharacter.coe_mk] at hfrob hself
  have hfirst := hfrob.symm.trans hself
  have hbound := restrictionMultiplicity_mul_le_restrictionMultiplicity (G := ↥hyp.H) hHT
    (⟨ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ, hindirr⟩ :
      IrreducibleCharacter ↥hyp.H)
    (⟨φ, hφirr⟩ : IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.H)) hθirr
  simp only [IrreducibleCharacter.coe_mk] at hbound
  rw [hfirst, one_mul, hround, hzero] at hbound
  have hnonneg := ClassFunction.restrictionMultiplicity_nonneg
    ((hyp.Qder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) hφirr
    θ''.isIrreducible
  exact hθ''over (le_antisymm hbound hnonneg)

omit [Fintype G] [Fintype ↥hyp.H] in
/-- **All members of `𝒮(Q')` have degree `d`** (Remark, p. 145).  By Lemma 2(a),
`χ = Ind_Q^H φ` with `φ ∈ Irr(Q)`; `Q' ⊆ Ker χ` forces `φ` to be constant on
`Q'.subgroupOf Q` (`forall_eq_one_of_leKer_Qder`), and the quotient of `Q` by a
subgroup containing `[Q,Q]` is abelian, so `φ(1) = 1`
(`apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient`); hence
`χ(1) = [H:Q]·φ(1) = d` (`induce_apply_one`, `index_Q_subgroupOf_eq_d`). -/
theorem apply_one_eq_d_of_mem_SsetOf_Qder [Finite G] {χ : ClassFunction ↥hyp.H ℂ}
    (hχ : χ ∈ hyp.SsetOf hyp.Qder) : χ (1 : ↥hyp.H) = (hyp.d : ℂ) := by
  classical
  letI : Fintype ↥hyp.H := Fintype.ofFinite _
  letI : Fintype ↥(hyp.Q.subgroupOf hyp.H) := Fintype.ofFinite _
  obtain ⟨hχS, hkerQ'⟩ := hχ
  have hχS' := hχS
  rw [Sset_eq_induced_of_Q hyp] at hχS'
  obtain ⟨φ, ⟨hφirr, _⟩, rfl⟩ := hχS'
  have hindirr : IsIrreducibleCharacter
      (ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ) := hχS.1
  -- `φ` is constant on `Q'.subgroupOf Q`
  have hconst := hyp.forall_eq_one_of_leKer_Qder hφirr hindirr hkerQ'
  -- the quotient of `Q` by `Q'.subgroupOf Q ⊇ [Q,Q]`-image is abelian
  have hcommN : ∀ a b : ↥(hyp.Q.subgroupOf hyp.H),
      ⁅a, b⁆ ∈ (hyp.Qder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H) := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hcoe : ((((⁅a, b⁆ : ↥(hyp.Q.subgroupOf hyp.H)) : ↥hyp.H)) : G)
        = ⁅(((a : ↥hyp.H)) : G), (((b : ↥hyp.H)) : G)⁆ := by
      simp [commutatorElement_def]
    rw [hcoe]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2)
  haveI hNnorm : ((hyp.Qder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).Normal := by
    constructor
    intro n hn g
    rw [show g * n * g⁻¹ = n * ⁅n⁻¹, g⁆ by rw [commutatorElement_def]; group]
    exact Subgroup.mul_mem _ hn (hcommN n⁻¹ g)
  haveI : IsMulCommutative (↥(hyp.Q.subgroupOf hyp.H) ⧸
      (hyp.Qder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) := by
    constructor
    constructor
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        rw [show (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ by rw [commutatorElement_def]; group]
        exact hcommN _ _
  -- `φ(1) = 1` (linear character of an abelian quotient)
  have hφ1 : φ (1 : ↥(hyp.Q.subgroupOf hyp.H)) = 1 := by
    have h := apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
      (N := (hyp.Qder.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))
      (⟨φ, hφirr⟩ : IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.H))
      (fun x hx => by
        rw [OddOrder.Peterfalvi.S03.mem_characterKernel]
        exact hconst ⟨x, hx⟩)
    simpa using h
  -- degree formula
  rw [ClassFunction.induce_apply_one, hyp.index_Q_subgroupOf_eq_d, hφ1, mul_one]

omit [Fintype G] [Fintype ↥hyp.H] in
/-- `𝒮` is a finite set: by Lemma 2(a) it is contained in the image of the finite
type `Irr(Q)` under `φ ↦ Ind_Q^H φ`. -/
theorem Sset_finite [Finite G] : hyp.Sset.Finite := by
  classical
  letI : Fintype ↥hyp.H := Fintype.ofFinite _
  letI : Fintype ↥(hyp.Q.subgroupOf hyp.H) := Fintype.ofFinite _
  haveI : Finite (IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.H)) :=
    finite_irreducibleCharacter
  rw [Sset_eq_induced_of_Q hyp]
  apply Set.Finite.image
  have hsub : {φ : ClassFunction ↥(hyp.Q.subgroupOf hyp.H) ℂ | IsIrreducibleCharacter φ ∧
      ¬ ∀ x : ↥(hyp.Q.subgroupOf hyp.H), ((x : ↥hyp.H) : G) ∈ hyp.Q1 → φ x = φ 1}
      ⊆ Set.range (fun θ : IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.H) =>
        (θ : ClassFunction ↥(hyp.Q.subgroupOf hyp.H) ℂ)) := fun φ hφ => ⟨⟨φ, hφ.1⟩, rfl⟩
  exact (Set.finite_range _).subset hsub

omit [Fintype G] [Invertible (Nat.card G : ℂ)]
  [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)] in
/-- **Distinct members of `𝒮` are orthogonal** (they are distinct irreducible
characters): the `pairwise_orthogonal` input for the §7 coherence hypothesis. -/
theorem Sset_pairwiseOrthogonal :
    OddOrder.Peterfalvi.S03.PairwiseOrthogonal hyp.Sset := by
  intro χ ψ hχ hψ hne
  have hite := irreducibleCharacter_inner_eq_ite (G := ↥hyp.H)
    (⟨χ, hχ.1⟩ : IrreducibleCharacter ↥hyp.H) (⟨ψ, hψ.1⟩ : IrreducibleCharacter ↥hyp.H)
  rw [if_neg (fun h => hne (congrArg Subtype.val h))] at hite
  simpa using hite

omit [Fintype G] [Fintype ↥hyp.H] in
/-- **`|𝒮(Q')| ≥ 2` from nonemptiness** (Remark, p. 145): a member `χ₀ ∈ 𝒮(Q')`
comes with its complex conjugate `χ̄₀ ∈ 𝒮(Q')` (`conj_mem_SsetOf_Qder`), and
`χ̄₀ ≠ χ₀` because no member of `𝒮` is real (Lemma 2(c),
`hasNoRealCharacters_Sset`, under `d` and `|Q₁|` odd). -/
theorem two_le_ncard_SsetOf_Qder [Finite G] (hd : Odd hyp.d)
    (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    (hne : (hyp.SsetOf hyp.Qder).Nonempty) :
    2 ≤ (hyp.SsetOf hyp.Qder).ncard := by
  classical
  obtain ⟨χ0, hχ0⟩ := hne
  have hχ0c : χ0.conj ∈ hyp.SsetOf hyp.Qder := hyp.conj_mem_SsetOf_Qder hχ0
  have hnoreal := hasNoRealCharacters_Sset hyp hd hQ1odd
  have hne0 : χ0 ≠ χ0.conj := by
    intro h
    exact hnoreal (SsetOf_subset hyp hyp.Qder hχ0) h.symm
  have hfin : (hyp.SsetOf hyp.Qder).Finite :=
    (hyp.Sset_finite).subset (SsetOf_subset hyp hyp.Qder)
  calc 2 = ({χ0, χ0.conj} : Set (ClassFunction ↥hyp.H ℂ)).ncard :=
        (Set.ncard_pair hne0).symm
    _ ≤ (hyp.SsetOf hyp.Qder).ncard :=
        Set.ncard_le_ncard (by rintro x (rfl | rfl); exacts [hχ0, hχ0c]) hfin

end CharacterLayer

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
