/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CaseBCoherence

/-!
# Peterfalvi §8: Case (B) coherence — the `τ₂` assembly

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, pp. 30-37, the **(6.8.2)** branch of the (6.8) coherence capstone.

This continues `S08_CaseBCoherence` (which holds the §3 helpers, (6.8.2.1), and the (6.8.2.2)
decomposition + uniform Y-coherence witness `exists_Ycoherence_hgood_caseB`).  Here we assemble the
decomposition into the case-(B) `X ∪ Y` coherence:

* the **general** good-case `X`-structure (consuming an arbitrary `Y`-coherence witness `cY`, as
  produced by `exists_Ycoherence_hgood_caseB`),
* the crux `α^τ = X − |H:Z|·cY η₁`,
* **(6.8.2.3)** the `X`-side `(χ − a η₁)^τ` decomposition ([Is] Lemma 2.27),
* the final `τ₂` assembly.

Reference note: `notes/peterfalvi/s08_6_8_assembly_plan.md` ("session 40 cont.⁹+").
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(6.8.2.2) good-case `X`-structure, general `Y`-coherence witness.**  The `cY`-parametrized
version of `orthogonal_tau_indW2_add_extension_caseB`: for *any* `Y`-coherence witness `cY` (e.g. the
swapped witness from `exists_Ycoherence_hgood_caseB` in the `|Y| = 2` edge), the good value
`⟨α^τ, cY.extension η₁⟩ = −|H:Z|` makes `X := α^τ + |H:Z|·cY.extension η₁` orthogonal to the whole
family `{cY.extension η}` and lie in `ℤ[Irr G]`, giving `α^τ = X − |H:Z|·cY.extension η₁`.

The agreement `cY.extension η − cY.extension η₁ = (η − η₁)^τ` is `cY.extends_on_supported` + `map_sub`
(inlined, since `cY` need not be `coherentYset`). -/
theorem SibleyDadeHypothesis.orthogonal_tau_indW2_add_extension_general_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) (hW2comm : W2 ≤ ⁅H, H⁆)
    [Invertible (Nat.card ↥W2 : ℂ)]
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (h1 : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) 1
      = ((W2.subgroupOf H).index : ℂ) * η₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
      = -((W2.subgroupOf H).index : ℂ)) :
    (∀ η ∈ hyp.Yset,
        ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
            - ((W2.subgroupOf H).index : ℂ) • η₁)
          + ((W2.subgroupOf H).index : ℂ) • cY.extension η₁)
          (cY.extension η) = 0)
      ∧ hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
          - ((W2.subgroupOf H).index : ℂ) • η₁)
          + ((W2.subgroupOf H).index : ℂ) • cY.extension η₁ ∈ ZIrr G := by
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  classical
  have hYon : ∀ η η', η ∈ hyp.Yset → η' ∈ hyp.Yset →
      ClassFunction.inner (cY.extension η) (cY.extension η')
        = if η = η' then (1 : ℂ) else 0 := by
    intro η η' hη hη'
    rw [cY.extension_inner_eq η η' (Submodule.subset_span hη) (Submodule.subset_span hη')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η', hyp.isIrreducibleCharacter_of_mem_Yset hη'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hcoeff0 : ∀ η ∈ hyp.Yset, η ≠ η₁ →
      ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η) = 0 := by
    intro η hη hne
    have hconst := hyp.inner_tau_indW2_sub_smul_tau_Yset_diff hW2H hW2comm φ hη₁ hη hne
      ((W2.subgroupOf H).index : ℂ) h1
    have hsuppd : (η - η₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη₁)
        ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη₁).symm)
    have htaud : hyp.tau (η - η₁) = cY.extension η - cY.extension η₁ := by
      rw [← cY.extends_on_supported (η - η₁)
        ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁), hsuppd⟩,
        map_sub]
    rw [htaud, ClassFunction.inner_sub_right, hgood] at hconst
    linear_combination hconst
  have he₁e₁ : ClassFunction.inner (cY.extension η₁) (cY.extension η₁) = 1 := by
    rw [hYon η₁ η₁ hη₁ hη₁, if_pos rfl]
  refine ⟨?_, ?_⟩
  · intro η hη
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left]
    by_cases hee : η = η₁
    · subst hee; rw [hgood, he₁e₁]; ring
    · rw [hcoeff0 η hη hee, hYon η₁ η hη₁ hη, if_neg (Ne.symm hee)]; ring
  · have hsuppX : (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁).support
        ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.support_indW2_sub_smul_subset_sharpImage hW2H φ hη₁ _ h1
    have hsrcZ : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁ ∈ ZIrr (↥L) := by
      rw [Nat.cast_smul_eq_nsmul]
      exact sub_mem (ClassFunction.induce_mem_ZIrr W2 (IsIrreducibleCharacter.mem_ZIrr φ.2))
        (nsmul_mem (hyp.isIrreducibleCharacter_of_mem_Yset hη₁).mem_ZIrr (W2.subgroupOf H).index)
    have hvZ : hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁) ∈ ZIrr G :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        hyp.dade hyp.hconj hsuppX hsrcZ
    have he₁Z : ((W2.subgroupOf H).index : ℂ) • cY.extension η₁ ∈ ZIrr G := by
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem (cY.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁)) (W2.subgroupOf H).index
    exact add_mem hvZ he₁Z

/-- **Peterfalvi (6.8.2.2): the `X − |H:Z|·Y` decomposition.**  For `α = Ind^L_{W₂}φ − |H:Z|·η₁`
(`φ` nontrivial linear), there is a `Y`-coherence witness `cY` and an `X ∈ ℤ[Irr G]` orthogonal to the
whole family `{cY.extension η : η ∈ Y}` with `α^τ = X − |H:Z|·cY.extension η₁`.

Combines the uniform good-value witness `exists_Ycoherence_hgood_caseB` (handling the `|Y| = 2`
relabel) with the general `X`-structure `orthogonal_tau_indW2_add_extension_general_caseB`.  This is
the case-(B) decomposition consumed by the τ₂ assembly (Peterfalvi (6.8.2)); `Y := cY.extension η₁`
is the (6.8.2.2) `Y` (`= η₁^{τ₁}`, or `−η₂^{τ₁}` in the edge).  `hc2`/`hFPF` are the deferred
`W₁`-FPF-on-`H/W₂` inputs. -/
theorem SibleyDadeHypothesis.exists_decomposition_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    (hc2 : 2 ≤ (W2.subgroupOf H).index)
    (hFPF : (W2.index : ℤ) < ((W2.subgroupOf H).index : ℤ) ^ 2) :
    ∃ (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
        (X : ClassFunction G ℂ),
      (∀ η ∈ hyp.Yset, ClassFunction.inner X (cY.extension η) = 0)
        ∧ X ∈ ZIrr G
        ∧ hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
            - ((W2.subgroupOf H).index : ℂ) • η₁)
          = X - ((W2.subgroupOf H).index : ℂ) • cY.extension η₁ := by
  haveI : Fintype ↥W2 := Fintype.ofFinite _
  have hW2H : W2 ≤ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]; intro a ha b hb; rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    exact hW2comm.trans hle
  have h1 : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) 1
      = ((W2.subgroupOf H).index : ℂ) * η₁ 1 := by
    rw [ClassFunction.induce_apply_one, hφ1, mul_one, hyp.Yset_apply_one hη₁]
    have hidx : W2.index = (W2.subgroupOf H).index * H.index :=
      (Subgroup.relIndex_mul_index hW2H).symm
    rw [hidx, hyp.index_H_eq_card_W1]; push_cast; ring
  obtain ⟨cY, hgood⟩ :=
    hyp.exists_Ycoherence_hgood_caseB hcop hp hHp hprime hW2comm hW2cen hη₁ φ hφ1 hφ hc2 hFPF
  obtain ⟨horth, hXZ⟩ :=
    hyp.orthogonal_tau_indW2_add_extension_general_caseB hW2H hW2comm cY hη₁ φ hφ1 h1 hgood
  refine ⟨cY, hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
      - ((W2.subgroupOf H).index : ℂ) • η₁)
      + ((W2.subgroupOf H).index : ℂ) • cY.extension η₁, horth, hXZ, ?_⟩
  abel

end OddOrder.Peterfalvi.S08
