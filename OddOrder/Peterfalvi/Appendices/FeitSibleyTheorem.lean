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

/-- **`S ⊴ Q`** (direct-product factor, elementwise form): for `q ∈ Q` and `s' ∈ S`,
`q s' q⁻¹ ∈ S`.  Writing `q = s·y` (`s ∈ S`, `y ∈ Q₁`), the `Q₁`-part centralises
`s'`, so `q s' q⁻¹ = s s' s⁻¹ ∈ S`.  Mirror of `Q1_conj_mem_of_mem_Q`. -/
theorem S_conj_mem_of_mem_Q {q : G} (hq : q ∈ hyp.Q) {x : G} (hx : x ∈ hyp.S) :
    q * x * q⁻¹ ∈ hyp.S := by
  rw [← SetLike.mem_coe, ← hyp.S_mul_Q1_eq_Q] at hq
  obtain ⟨s, hs, y, hy, hsy⟩ := Set.mem_mul.mp hq
  rw [SetLike.mem_coe] at hs hy
  subst hsy
  have hcomm : x * y = y * x := (hyp.S_commutes_Q1 x hx y hy)
  have hrw : s * y * x * (s * y)⁻¹ = s * x * s⁻¹ := by
    calc s * y * x * (s * y)⁻¹ = s * (y * x * y⁻¹) * s⁻¹ := by group
      _ = s * (x * y * y⁻¹) * s⁻¹ := by rw [← hcomm]
      _ = s * x * s⁻¹ := by group
  rw [hrw]
  exact hyp.S.mul_mem (hyp.S.mul_mem hs hx) (hyp.S.inv_mem hs)

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

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥hyp.H]
  [Invertible (Nat.card ↥hyp.H : ℂ)]
  [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)] in
theorem one_notMem_A : (1 : ↥hyp.H) ∉ hyp.A := fun h => h.2 rfl

omit [Fintype G] [Fintype ↥hyp.H] [Invertible (Nat.card G : ℂ)]
  [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)] in
/-- **Member differences of `𝒮(Q')` are supported on `A = Q^#`**: at `1` both members
take the common degree `d` (`apply_one_eq_d_of_mem_SsetOf_Qder`), and off `Q` both
vanish (Lemma 2(a) corollary `apply_eq_zero_of_mem_Sset_of_not_mem_Q`). -/
theorem diff_support_subset_A_of_mem_SsetOf_Qder [Finite G]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]
    {a b : ClassFunction ↥hyp.H ℂ} (ha : a ∈ hyp.SsetOf hyp.Qder)
    (hb : b ∈ hyp.SsetOf hyp.Qder) :
    ((a - b : ClassFunction ↥hyp.H ℂ)).support ⊆ hyp.A := by
  letI : Fintype ↥hyp.H := Fintype.ofFinite _
  intro x hx
  rw [ClassFunction.mem_support] at hx
  by_contra hxA
  apply hx
  rw [ClassFunction.sub_apply]
  by_cases hx1 : x = 1
  · subst hx1
    rw [hyp.apply_one_eq_d_of_mem_SsetOf_Qder ha, hyp.apply_one_eq_d_of_mem_SsetOf_Qder hb,
      sub_self]
  · have hxQ : (x : G) ∉ hyp.Q := fun hQ => hxA ⟨hQ, hx1⟩
    rw [apply_eq_zero_of_mem_Sset_of_not_mem_Q hyp (SsetOf_subset hyp hyp.Qder ha) hxQ,
      apply_eq_zero_of_mem_Sset_of_not_mem_Q hyp (SsetOf_subset hyp hyp.Qder hb) hxQ,
      sub_self]

/-- **The Lemma 2(b) isometry on the `A`-supported `𝒮(Q')`-sublattice** — the
`tau_isometry_diff` field of the §7 hypothesis for `𝒮(Q')`.  An `A`-supported
member of `ℤ[𝒮(Q')]` lies in `ℤ[𝒮]` (span monotonicity along `𝒮(Q') ⊆ 𝒮`) and
vanishes at `1` (`1 ∉ A`), so `induction_isometry_on_degree_zero` applies. -/
theorem tau_inner_eq_of_supported_SsetOf_Qder [Finite G]
    ⦃φ ψ : ClassFunction ↥hyp.H ℂ⦄
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      (hyp.SsetOf hyp.Qder) hyp.A)
    (hψ : ψ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      (hyp.SsetOf hyp.Qder) hyp.A) :
    ClassFunction.inner (hyp.tau φ) (hyp.tau ψ) = ClassFunction.inner φ ψ := by
  have hmono : OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.H) (hyp.SsetOf hyp.Qder)
      ≤ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.H) hyp.Sset :=
    Submodule.span_mono (SsetOf_subset hyp hyp.Qder)
  have hφ1 : φ (1 : ↥hyp.H) = 0 := by
    by_contra h0
    exact hyp.one_notMem_A (hφ.2 (ClassFunction.mem_support.mpr h0))
  have hψ1 : ψ (1 : ↥hyp.H) = 0 := by
    by_contra h0
    exact hyp.one_notMem_A (hψ.2 (ClassFunction.mem_support.mpr h0))
  exact (induction_isometry_on_degree_zero hyp φ ψ (hmono hφ.1) (hmono hψ.1) hφ1 hψ1).1

/-- **The (5.2.d) difference image for a member of `𝒮(Q')`** — the
`difference_image` field of the §7 hypothesis: `τ(χ − χ̄)` is a signed difference
`ε·(μ − ν)` of two distinct irreducibles of `G`.  Mirror of
`dadeCharacterDifferenceImageOfDiff` for `τ = Ind_H^G`: the (1.4) inputs are
discharged from Lemma 2(b) (`tau_mem_ZIrr`, `tau_apply_one`,
`tau_inner_eq_of_supported_SsetOf_Qder`) since both keystone differences (`0` and
`χ̄ − χ`) lie in the `A`-supported `𝒮(Q')`-sublattice, and non-reality is
Lemma 2(c). -/
noncomputable def ssetOfQderDifferenceImage [Finite G] (hd : Odd hyp.d)
    (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    {χ : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.SsetOf hyp.Qder) :
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage hyp.tau χ := by
  classical
  have hχS : χ ∈ hyp.Sset := SsetOf_subset hyp hyp.Qder hχ
  have hχc : χ.conj ∈ hyp.SsetOf hyp.Qder := hyp.conj_mem_SsetOf_Qder hχ
  set χb : IrreducibleCharacter ↥hyp.H := ⟨χ, hχS.1⟩ with hχb
  set fam : Fin 2 → IrreducibleCharacter ↥hyp.H :=
    OddOrder.Peterfalvi.S07.conjPairFamily (L := ↥hyp.H) χb with hfam
  have hfam0 : (fam 0 : ClassFunction ↥hyp.H ℂ) = χ := by
    simp [hfam, OddOrder.Peterfalvi.S07.conjPairFamily, hχb]
  have hfam1 : (fam 1 : ClassFunction ↥hyp.H ℂ) = χ.conj := by
    simp [hfam, OddOrder.Peterfalvi.S07.conjPairFamily, hχb]
  have hdiff0 : irreducibleCharacterDifference fam 0 = 0 := by
    simp [irreducibleCharacterDifference]
  have hdiff1 : irreducibleCharacterDifference fam 1 = χ.conj - χ := by
    simp only [irreducibleCharacterDifference, hfam1, hfam0]
  -- both keystone differences lie in the `A`-supported `𝒮(Q')`-sublattice
  have hmem : ∀ i, irreducibleCharacterDifference fam i
      ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
        (hyp.SsetOf hyp.Qder) hyp.A := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [hdiff0]
      exact ⟨Submodule.zero_mem _,
        fun x hx => absurd (ClassFunction.zero_apply x) (ClassFunction.mem_support.mp hx)⟩
    · rw [hdiff1]
      exact ⟨Submodule.sub_mem _ (Submodule.subset_span hχc) (Submodule.subset_span hχ),
        hyp.diff_support_subset_A_of_mem_SsetOf_Qder hχc hχ⟩
  refine OddOrder.Peterfalvi.S07.characterDifferenceImageOfIsometry hyp.tau χb
    ((hasNoRealCharacters_Sset hyp hd hQ1odd) hχS) ?_ ?_ ?_
  · -- virtual images
    change ∀ i, isometryDifferenceImage hyp.tau fam i ∈ ZIrr G
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · change hyp.tau (irreducibleCharacterDifference fam 0) ∈ ZIrr G
      rw [hdiff0, map_zero]
      exact Submodule.zero_mem _
    · change hyp.tau (irreducibleCharacterDifference fam 1) ∈ ZIrr G
      rw [hdiff1]
      exact hyp.tau_mem_ZIrr (Submodule.sub_mem _
        (Submodule.subset_span (SsetOf_subset hyp hyp.Qder hχc))
        (Submodule.subset_span hχS))
  · -- vanish at `1`
    change ∀ i, isometryDifferenceImage hyp.tau fam i (1 : G) = 0
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · change hyp.tau (irreducibleCharacterDifference fam 0) (1 : G) = 0
      rw [hdiff0, map_zero]
      exact ClassFunction.zero_apply _
    · change hyp.tau (irreducibleCharacterDifference fam 1) (1 : G) = 0
      rw [hdiff1]
      refine hyp.tau_apply_one ?_
      rw [ClassFunction.sub_apply, hyp.apply_one_eq_d_of_mem_SsetOf_Qder hχc,
        hyp.apply_one_eq_d_of_mem_SsetOf_Qder hχ, sub_self]
  · -- isometry on the keystone differences (uniform via the supported sublattice)
    intro i j
    exact hyp.tau_inner_eq_of_supported_SsetOf_Qder (hmem i) (hmem j)

/-- **(5.2.e) orthogonality of the `𝒮(Q')` difference images** — the
`difference_images_orthogonal` field.  Mirror of `Sset_differenceImages_orthogonal`
(S14): the pairing of the signed images reduces along the Lemma 2(b) isometry to
`⟨φ − φ̄, χ − χ̄⟩`, whose four cross terms vanish by pairwise orthogonality. -/
theorem ssetOfQderDifferenceImages_orthogonal [Finite G] (hd : Odd hyp.d)
    (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    {φ χ : ClassFunction ↥hyp.H ℂ} (hφ : φ ∈ hyp.SsetOf hyp.Qder)
    (hχ : χ ∈ hyp.SsetOf hyp.Qder)
    (h1 : ClassFunction.inner φ χ = 0) (h2 : ClassFunction.inner φ χ.conj = 0) :
    (hyp.ssetOfQderDifferenceImage hd hQ1odd hφ).Orthogonal
      (hyp.ssetOfQderDifferenceImage hd hQ1odd hχ) := by
  have hφc := hyp.conj_mem_SsetOf_Qder hφ
  have hχc := hyp.conj_mem_SsetOf_Qder hχ
  have hself : ∀ ⦃ζ : ClassFunction ↥hyp.H ℂ⦄, ζ ∈ hyp.Sset →
      ClassFunction.inner ζ ζ = 1 := by
    intro ζ hζ
    have h := irreducibleCharacter_inner_eq_ite (G := ↥hyp.H)
      (⟨ζ, hζ.1⟩ : IrreducibleCharacter ↥hyp.H) (⟨ζ, hζ.1⟩ : IrreducibleCharacter ↥hyp.H)
    rw [if_pos rfl] at h
    simpa using h
  refine
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage.orthogonal_of_signedDifference_inner_eq_zero
    _ _ ?_
  rw [← (hyp.ssetOfQderDifferenceImage hd hQ1odd hφ).image_conjugateDifference,
      ← (hyp.ssetOfQderDifferenceImage hd hQ1odd hχ).image_conjugateDifference]
  change ClassFunction.inner (hyp.tau (φ - φ.conj)) (hyp.tau (χ - χ.conj)) = 0
  have hmemφ : (φ - φ.conj : ClassFunction ↥hyp.H ℂ)
      ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
        (hyp.SsetOf hyp.Qder) hyp.A :=
    ⟨Submodule.sub_mem _ (Submodule.subset_span hφ) (Submodule.subset_span hφc),
      hyp.diff_support_subset_A_of_mem_SsetOf_Qder hφ hφc⟩
  have hmemχ : (χ - χ.conj : ClassFunction ↥hyp.H ℂ)
      ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
        (hyp.SsetOf hyp.Qder) hyp.A :=
    ⟨Submodule.sub_mem _ (Submodule.subset_span hχ) (Submodule.subset_span hχc),
      hyp.diff_support_subset_A_of_mem_SsetOf_Qder hχ hχc⟩
  rw [hyp.tau_inner_eq_of_supported_SsetOf_Qder hmemφ hmemχ]
  have hne1 : φ.conj ≠ χ := by
    intro heq
    have hcc : χ.conj = φ := by rw [← heq, ClassFunction.conj_conj]
    rw [hcc, hself (SsetOf_subset hyp hyp.Qder hφ)] at h2
    exact one_ne_zero h2
  have hne2 : φ.conj ≠ χ.conj := by
    intro heq
    have hpc : φ = χ := by
      have h := congrArg ClassFunction.conj heq
      rwa [ClassFunction.conj_conj, ClassFunction.conj_conj] at h
    rw [hpc, hself (SsetOf_subset hyp hyp.Qder hχ)] at h1
    exact one_ne_zero h1
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, h1, h2,
    hyp.Sset_pairwiseOrthogonal (SsetOf_subset hyp hyp.Qder hφc)
      (SsetOf_subset hyp hyp.Qder hχ) hne1,
    hyp.Sset_pairwiseOrthogonal (SsetOf_subset hyp hyp.Qder hφc)
      (SsetOf_subset hyp hyp.Qder hχc) hne2]
  ring

/-- **Remark (p. 145): `𝒮(Q')` is coherent** with respect to the Lemma 2(b)
isometry `τ = Ind_H^G`, given `d` and `|Q₁|` odd and `𝒮(Q') ≠ ∅`.  All members
have the common degree `d` (`apply_one_eq_d_of_mem_SsetOf_Qder`), so this is
Lemma 1(b) via the equal-degree §7 producer `coherent_of_constant_degree`, with
the §7 (5.2) hypothesis assembled from Lemmas 2(b) and 2(c).

The book derives nonemptiness (`|𝒮(Q')| ≥ 2`) from the odd Frobenius group
`O_{2'}(Q₁) ⋊ D`; here the conjugate pair supplies the second member
(`two_le_ncard_SsetOf_Qder`) and nonemptiness is an explicit hypothesis,
discharged at the Theorem's call site from the nontrivial abelianisation of the
`p`-group `Q₁`. -/
theorem ssetOf_Qder_coherent [Finite G] (hd : Odd hyp.d)
    (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    (hne : (hyp.SsetOf hyp.Qder).Nonempty) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsetOf hyp.Qder) hyp.A) := by
  classical
  have hself : ∀ ⦃ζ : ClassFunction ↥hyp.H ℂ⦄, ζ ∈ hyp.Sset →
      ClassFunction.inner ζ ζ = 1 := by
    intro ζ hζ
    have h := irreducibleCharacter_inner_eq_ite (G := ↥hyp.H)
      (⟨ζ, hζ.1⟩ : IrreducibleCharacter ↥hyp.H) (⟨ζ, hζ.1⟩ : IrreducibleCharacter ↥hyp.H)
    rw [if_pos rfl] at h
    simpa using h
  refine OddOrder.Peterfalvi.S07.coherent_of_constant_degree
    { tau := hyp.tau
      tau_isometry_diff := fun φ ψ hφ hψ =>
        hyp.tau_inner_eq_of_supported_SsetOf_Qder hφ hψ
      conjugate_closed := fun χ hχ => hyp.conj_mem_SsetOf_Qder hχ
      no_real_characters := (hasNoRealCharacters_Sset hyp hd hQ1odd).mono
        (SsetOf_subset hyp hyp.Qder)
      pairwise_orthogonal := fun χ ψ hχ hψ hne' =>
        hyp.Sset_pairwiseOrthogonal (SsetOf_subset hyp hyp.Qder hχ)
          (SsetOf_subset hyp hyp.Qder hψ) hne'
      difference_image := fun χ hχ => hyp.ssetOfQderDifferenceImage hd hQ1odd hχ
      difference_images_orthogonal := fun φ χ hφ hχ h1 h2 =>
        hyp.ssetOfQderDifferenceImages_orthogonal hd hQ1odd hφ hχ h1 h2 }
    ((hyp.Sset_finite).subset (SsetOf_subset hyp hyp.Qder))
    (hyp.two_le_ncard_SsetOf_Qder hd hQ1odd hne)
    (fun ζ hζ => hself (SsetOf_subset hyp hyp.Qder hζ))
    (fun a ha b hb => hyp.tau_mem_ZIrr (Submodule.sub_mem _
      (Submodule.subset_span (SsetOf_subset hyp hyp.Qder ha))
      (Submodule.subset_span (SsetOf_subset hyp hyp.Qder hb))))
    (fun a ha b hb => by
      change a (1 : ↥hyp.H) = b (1 : ↥hyp.H)
      rw [hyp.apply_one_eq_d_of_mem_SsetOf_Qder ha,
        hyp.apply_one_eq_d_of_mem_SsetOf_Qder hb])
    (fun a ha => by
      change a (1 : ↥hyp.H) ≠ 0
      rw [hyp.apply_one_eq_d_of_mem_SsetOf_Qder ha]
      exact Nat.cast_ne_zero.mpr (hyp.d_pos).ne')
    hyp.one_notMem_A
    (fun a ha b hb => hyp.diff_support_subset_A_of_mem_SsetOf_Qder ha hb)

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥hyp.H : ℂ)] in
/-- **Induction preserves `Q'`-constancy**: if `φ ∈ CF(Q)` is constant (`= φ(1)`) on
the `Q'`-part, then `Ind_Q^H φ` is constant on `Q'` (`LeKer`).  Every induction
term at `x ∈ Q'` evaluates `φ` at an `H`-conjugate of `x`, which stays in
`Q' ⊆ Q` (`Qder_conj_mem_of_mem_H`), where `φ` takes the value `φ(1)`; so all
`|H|` terms agree with the corresponding terms at `1`. -/
theorem leKer_induce_Qder_of_forall [Finite G]
    {φ : ClassFunction ↥(hyp.Q.subgroupOf hyp.H) ℂ}
    (hconst : ∀ y : ↥(hyp.Q.subgroupOf hyp.H), ((y : ↥hyp.H) : G) ∈ hyp.Qder →
      φ y = φ 1) :
    hyp.LeKer (ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ) hyp.Qder := by
  intro x hxQ'
  have hterm : ∀ g : ↥hyp.H, (g : G) ∈ hyp.Qder → ∀ h : ↥hyp.H,
      ClassFunction.induceTerm (hyp.Q.subgroupOf hyp.H) φ h g = φ 1 := by
    intro g hg h
    have hconjG : ((h⁻¹ * g * h : ↥hyp.H) : G) ∈ hyp.Qder := by
      have := hyp.Qder_conj_mem_of_mem_H (hyp.H.inv_mem h.2) hg
      simpa [mul_assoc] using this
    have hmem : h⁻¹ * g * h ∈ hyp.Q.subgroupOf hyp.H :=
      Subgroup.mem_subgroupOf.mpr (hyp.Qder_le_Q hconjG)
    rw [ClassFunction.induceTerm_of_mem φ hmem]
    exact hconst ⟨h⁻¹ * g * h, hmem⟩ hconjG
  have h1Q' : ((1 : ↥hyp.H) : G) ∈ hyp.Qder := by
    simp
  rw [ClassFunction.induce_apply, ClassFunction.induce_apply]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [hterm x hxQ' h, hterm 1 h1Q' h]

end CharacterLayer

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
