/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3Proposition
import OddOrder.Peterfalvi.Appendices.Suzuki.StandardModelFGH
import OddOrder.Peterfalvi.Appendices.Suzuki.PointCoordinates
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerInductionBridge

/-!
# Peterfalvi Part II, Ch. IV §3, Corollary 1

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3, p. 132:

> **Corollary 1.** Under the hypothesis of the proposition, `O^{2′}(G) ≅ PSU(3, q)`.
>
> **Proof.** If `G` satisfies the hypothesis of the proposition, `Q` and `f` are well
> defined by the specification of `q`.  By the lemma of §1,
> `O^{2′}(G) = ⟨Q^x | x ∈ G⟩` is then determined up to isomorphism.

"`Q` and `f` are well defined by the specification of `q`" is the content of the
Proposition, in the form `proposition_inverseFormula_of_ne_one`: read in the unitary
coordinates, `f` is `ρ ↦ (ρ̄/y, 1/y)` throughout `Q^#`.  The standard model's own `f` is
the same map (`standardModel_f_rootHom`, read off the Bruhat relation), so the coordinate
isomorphism `unitaryRootEquiv` intertwines the two — which is exactly the input of the
Lemma of §1.

This file supplies that isomorphism.

## Main results

* `Hypothesis.exists_mulEquiv_intertwining_f` — `Q ≃* Q'` intertwining `f` with the
  standard model's `f'`.
* `closure_conj_standardRootSubgroup_eq_top` — `⟨Q'^x⟩ = ⊤` in `standardPermGroup q`.
* `Hypothesis.exists_mulEquiv_standardPermGroup` — Corollary 1's isomorphism, together
  with the equivariant bijection of point sets.
* `Hypothesis.nonempty_psu3InductionTarget`,
  `Hypothesis.nonempty_theoremAConclusion_psu3` — Corollary 1 in the shape Theorem A's
  conclusion takes: `O^{2′}(G)` with the standard `PSU(3, q)` action.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair
open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

section /- Ch. IV §3, Corollary 1: `Q` and `f` are the standard ones (p. 132) -/

/-- **`Q` and `f` are the standard ones** (Peterfalvi Part II, Ch. IV §3, Corollary 1,
p. 132).

The unitary coordinates identify `Q` with `RootGroup q` coordinate by coordinate
(`unitaryRootEquiv`), and under that identification the Proposition's formula for `f` is
`RootGroup.reciprocal` — which is the standard model's `f` (`standardModel_f_rootHom`).
So the isomorphism intertwines the two mappings, which is the hypothesis `hεf` of the
Lemma of §1 (`conjQMulEquivOfData`, `exists_conjQMulEquiv_actionEquiv`).

The Proposition enters only through `hform`, its conclusion. -/
theorem exists_mulEquiv_intertwining_f (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {m : ℕ} (hn : 1 < m)
    {f' g' h' : ↥(standardPermGroup m) → ↥(standardPermGroup m)}
    (H' : IsFGH (standardBorel m) (standardRootSubgroup m) (psuTorusHom m).range
      (weylElement m) f' g' h')
    (M : hyp.QuotientFieldModel m)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    (hform : ∀ (ρ : G) (hρQ : ρ ∈ hyp.Q), ρ ≠ 1 →
      (Ψ ⟨f ρ, hfQ ρ hρQ⟩).quotient
          = (Ψ ⟨ρ, hρQ⟩).quotient /
            Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
        Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfQ ρ hρQ⟩)
          = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹) :
    ∃ εQ : ↥hyp.Q ≃* ↥(standardHypothesis m hn).Q,
      ∀ (x : ↥hyp.Q) (hx1 : (x : G) ≠ 1),
        ((εQ ⟨f (x : G), H.f_mem x.2 hx1⟩ : ↥(standardHypothesis m hn).Q)
            : ↥(standardPermGroup m))
          = f' ((εQ x : ↥(standardHypothesis m hn).Q) : ↥(standardPermGroup m)) := by
  classical
  have hm : 0 < m := Nat.zero_lt_one.trans hn
  haveI : Fintype M.E := Fintype.ofFinite _
  haveI : Fintype (Field m) := Fintype.ofFinite _
  have hcards : Fintype.card M.E = Fintype.card (Field m) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, M.card,
      natCard_field m hm, ← pow_mul]
    congr 1
    omega
  set σ : M.E ≃+* Field m := FiniteField.ringEquivOfCardEq hcards with hσ
  set ε : ↥hyp.Q ≃* RootGroup m :=
    Ψ.trans (Suzuki2Groups.unitaryRootEquiv hm M.card hu σ) with hε
  refine ⟨ε.trans (rootEquivStandardRoot m), fun x hx1 => ?_⟩
  -- the image of `x` is a nontrivial root element
  have h1 : ε x ≠ 1 := by
    intro hc
    have hx : x = 1 := ε.injective (by rw [hc, map_one])
    exact hx1 (by rw [hx]; rfl)
  obtain ⟨hA, hB⟩ := hform (x : G) x.2 hx1
  have hxf : (⟨f (x : G), H.f_mem x.2 hx1⟩ : ↥hyp.Q) = ⟨f (x : G), hfQ (x : G) x.2⟩ := rfl
  have hrec : ε ⟨f (x : G), H.f_mem x.2 hx1⟩ = RootGroup.reciprocal (ε x) h1 := by
    rw [hxf]
    exact Suzuki2Groups.unitaryRootEquiv_reciprocal hm M.card hu σ hA hB h1
  change (rootHom m (ε ⟨f (x : G), H.f_mem x.2 hx1⟩) : ↥(standardPermGroup m))
    = f' (rootHom m (ε x))
  rw [hrec, standardModel_f_rootHom hn H' (ε x) h1]

omit hyp in
/-- **`⟨Q'^x | x⟩ = PSU(3, q)`**: the normal closure of the root subgroup in the standard
model is everything, since that group is simple. -/
theorem closure_conj_standardRootSubgroup_eq_top {m : ℕ} (hn : 1 < m) :
    Subgroup.closure (⋃ y : ↥(standardPermGroup m),
        ((fun q => y⁻¹ * q * y) '' ((standardRootSubgroup m : Subgroup ↥(standardPermGroup m))
          : Set ↥(standardPermGroup m))))
      = ⊤ := by
  haveI := standardPermGroup_isSimpleGroup hn
  rw [closure_iUnion_conj_eq_normalClosure]
  have hnorm : (Subgroup.normalClosure
      ((standardRootSubgroup m : Subgroup ↥(standardPermGroup m)) :
        Set ↥(standardPermGroup m))).Normal :=
    Subgroup.normalClosure_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal _ hnorm with hbot | htop
  · exfalso
    have hle : (standardRootSubgroup m : Subgroup ↥(standardPermGroup m))
        ≤ Subgroup.normalClosure _ := Subgroup.le_normalClosure
    rw [hbot, le_bot_iff] at hle
    have hcard : Nat.card ↥(standardRootSubgroup m) = 2 ^ (3 * m) :=
      natCard_standardRootSubgroup m (Nat.zero_lt_one.trans hn)
    have hbotcard : Nat.card ↥(⊥ : Subgroup ↥(standardPermGroup m)) = 1 := by simp
    rw [hle, hbotcard] at hcard
    have hlt : (1 : ℕ) < 2 ^ (3 * m) := Nat.one_lt_two_pow (by omega)
    omega
  · exact htop

/-- **Peterfalvi Part II, Ch. IV §3, Corollary 1** (p. 132), in the form the Lemma of §1
delivers it:

  `⟨Q^x | x ∈ G⟩ ≃* PSU(3, q)`,

together with a bijection `Ω ≃ Unital q` intertwining the two actions.  With `Q` a Sylow
`2`-subgroup the left-hand side is `O^{2′}(G)`
(`closure_iUnion_conj_eq_primeComplementResidual`), which is the book's statement. -/
theorem exists_mulEquiv_standardPermGroup (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {m : ℕ} (hn : 1 < m)
    (M : hyp.QuotientFieldModel m)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    (hform : ∀ (ρ : G) (hρQ : ρ ∈ hyp.Q), ρ ≠ 1 →
      (Ψ ⟨f ρ, hfQ ρ hρQ⟩).quotient
          = (Ψ ⟨ρ, hρQ⟩).quotient /
            Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
        Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfQ ρ hρQ⟩)
          = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹) :
    ∃ (e : ↥(Subgroup.closure (⋃ y : G, ((fun q => y⁻¹ * q * y) '' (hyp.Q : Set G))))
          ≃* ↥(standardPermGroup m))
        (α : Ω ≃ Unital m),
      ∀ (l : ↥(Subgroup.closure (⋃ y : G, ((fun q => y⁻¹ * q * y) '' (hyp.Q : Set G)))))
        (ω : Ω), α ((l : G) • ω) = ((e l : ↥(standardPermGroup m)) • α ω) := by
  classical
  obtain ⟨f', g', h', H', -, -, -⟩ := exists_standardModel_fgh hn
  obtain ⟨εQ, hεf⟩ :=
    hyp.exists_mulEquiv_intertwining_f H hn H' M hu Ψ hfQ hform
  obtain ⟨e, α, hα⟩ := hyp.exists_conjQMulEquiv_actionEquiv (standardHypothesis m hn) H
    H' hyp.normalCore_H_eq_bot (standardHypothesis m hn).normalCore_H_eq_bot εQ hεf
  refine ⟨e.trans ((MulEquiv.subgroupCongr
    (closure_conj_standardRootSubgroup_eq_top hn)).trans Subgroup.topEquiv), α, hα⟩

/-- **Corollary 1, in Theorem A's coordinates** (Peterfalvi Part II, Ch. IV §3, p. 132):
`O^{2′}(G)` is `PSU(3, q)` acting on its Hermitian unital.

`Q` is a Sylow `2`-subgroup (`Setup.exists_sylow_two_eq`), so the `⟨Q^x | x ∈ G⟩` of the
Lemma of §1 is `O^{2′}(G)`. -/
theorem nonempty_psu3InductionTarget (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {m : ℕ} (hn : 1 < m)
    (M : hyp.QuotientFieldModel m)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    (hform : ∀ (ρ : G) (hρQ : ρ ∈ hyp.Q), ρ ≠ 1 →
      (Ψ ⟨f ρ, hfQ ρ hρQ⟩).quotient
          = (Ψ ⟨ρ, hρQ⟩).quotient /
            Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
        Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfQ ρ hρQ⟩)
          = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹)
    (hQ2 : IsPGroup 2 ↥hyp.Q) :
    Nonempty (PSU3InductionTarget (Omega := Ω)
      (Subgroup.primeComplementResidual 2 G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSQ⟩ := hyp.rankOneSetup.exists_sylow_two_eq hQ2 hyp.D_odd hyp.Q_even
  have hLeq : Subgroup.closure (⋃ y : G, ((fun q => y⁻¹ * q * y) '' (hyp.Q : Set G)))
      = Subgroup.primeComplementResidual 2 G := by
    rw [← hSQ]
    exact closure_iUnion_conj_eq_primeComplementResidual S
  obtain ⟨e, α, hα⟩ := hyp.exists_mulEquiv_standardPermGroup H hn M hu Ψ hfQ hform
  refine ⟨{ n := m
            one_lt_n := hn
            groupEquiv := (MulEquiv.subgroupCongr hLeq).symm.trans e
            actionEquiv := { toFun := α, map_smul' := fun l ω => ?_ }
            actionEquiv_bijective := α.bijective }⟩
  exact hα ((MulEquiv.subgroupCongr hLeq).symm l) ω

/-- **Peterfalvi Part II, Ch. IV §3, Corollary 1** (p. 132) as an instance of Theorem A's
conclusion: `L = O^{2′}(G)` is normal of odd index and carries the standard `PSU(3, q)`
model.

Normality and the odd index are general facts about `O^{2′}`
(`primeComplementResidual_normal`, `primeComplementResidual_index_coprime`). -/
theorem nonempty_theoremAConclusion_psu3 (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {m : ℕ} (hn : 1 < m)
    (M : hyp.QuotientFieldModel m)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    (hform : ∀ (ρ : G) (hρQ : ρ ∈ hyp.Q), ρ ≠ 1 →
      (Ψ ⟨f ρ, hfQ ρ hρQ⟩).quotient
          = (Ψ ⟨ρ, hρQ⟩).quotient /
            Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
        Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfQ ρ hρQ⟩)
          = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹)
    (hQ2 : IsPGroup 2 ↥hyp.Q) :
    Nonempty (TheoremAConclusion G Ω) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨data⟩ := hyp.nonempty_psu3InductionTarget H hn M hu Ψ hfQ hform hQ2
  refine ⟨{ L := Subgroup.primeComplementResidual 2 G
            normal := inferInstance
            oddIndex := ?_
            target := TheoremATarget.psu3 data }⟩
  exact Nat.coprime_two_left.mp
    (Subgroup.primeComplementResidual_index_coprime (G := G) 2)

end

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
