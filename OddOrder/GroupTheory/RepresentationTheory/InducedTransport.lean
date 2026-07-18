/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter
import OddOrder.GroupTheory.RepresentationTheory.CharacterCompleteness
import OddOrder.GroupTheory.RepresentationTheory.ColumnOrthogonality

/-!
# Transport lemmas for induced class functions

Generic (group-theory-only) transport lemmas for `ClassFunction.induce`:

* `induce_eq_sum_inner_restrict_smul` — constituent decomposition of an induced character,
  `Ind^M_N φ = ∑_{θ ∈ Irr M} ⟨φ, Res_N θ⟩ • θ` (Fourier expansion + Frobenius reciprocity);
* `inner_compHom_of_mulEquiv` — the class-function inner product is preserved by pullback
  along a group isomorphism;
* `induce_induce_subgroupOf` — induction in stages, `Ind^M_H (Ind^H_{K≤H} ψ) = Ind^M_K ψ`.

Extracted (hub prefix-split, issue 9005) from `OddOrder/Peterfalvi/S08_CaseBCoherence2.lean`,
where they supported the Peterfalvi (6.8.2.3) assembly; shared here so that
`GroupTheory/RepresentationTheory/**` consumers (Isaacs 6.11 Clifford correspondence,
issue 9002) can cite them without importing the Peterfalvi tree.
-/

namespace OddOrder.RepresentationTheory

/-- **Constituent decomposition of an induced character**.  For any class function `φ` of a
subgroup `N ≤ M`, the induced character expands in the `Irr M` basis with coefficients the
Frobenius multiplicities: `Ind^M_N φ = ∑_{θ ∈ Irr M} ⟨φ, Res_N θ⟩ • θ`.  Fourier expansion
(`sum_inner_irreducibleCharacter_smul`) plus Frobenius reciprocity
(`inner_induce_eq_inner_restrict`) on each coefficient. -/
theorem induce_eq_sum_inner_restrict_smul {M : Type*} [Group M] [Fintype M]
    [Invertible (Nat.card M : ℂ)] {N : Subgroup M} [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    (φ : ClassFunction ↥N ℂ) :
    ClassFunction.induce N φ
      = ∑ θ : IrreducibleCharacter M,
        ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
          • (θ : ClassFunction M ℂ) := by
  conv_lhs => rw [← sum_inner_irreducibleCharacter_smul (ClassFunction.induce N φ)]
  exact Finset.sum_congr rfl
    (fun θ _ => by rw [ClassFunction.inner_induce_eq_inner_restrict])

/-- **The class-function inner product is preserved by pullback along a group isomorphism.**  For a
`MulEquiv e : H ≃* G` and `a, b ∈ CF(G)`, `⟨a ∘ e, b ∘ e⟩_H = ⟨a, b⟩_G`: reindexing the inner sum
`∑_{h ∈ H} a(e h)·\overline{b(e h)} = ∑_{g ∈ G} a(g)·\overline{b(g)}` along the bijection `e` (and
`|H| = |G|`). -/
theorem inner_compHom_of_mulEquiv {G' H' : Type*} [Group G'] [Group H'] [Fintype G'] [Fintype H']
    [Invertible (Nat.card G' : ℂ)] [Invertible (Nat.card H' : ℂ)]
    (e : H' ≃* G') (a b : ClassFunction G' ℂ) :
    ClassFunction.inner (ClassFunction.compHom e.toMonoidHom a)
        (ClassFunction.compHom e.toMonoidHom b) = ClassFunction.inner a b := by
  have hcard : (Nat.card H' : ℂ) = (Nat.card G' : ℂ) := by rw [Nat.card_congr e.toEquiv]
  have hsum : (∑ h : H', (ClassFunction.compHom e.toMonoidHom a) h *
        star ((ClassFunction.compHom e.toMonoidHom b) h))
      = ∑ g : G', a g * star (b g) := by
    simp only [ClassFunction.compHom_apply]
    exact Equiv.sum_comp e.toEquiv (fun g => a g * star (b g))
  have hinv : ⅟(Nat.card H' : ℂ) = ⅟(Nat.card G' : ℂ) :=
    invOf_eq_right_inv (by rw [hcard, mul_invOf_self])
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.inner_eq_inv_card_mul_innerSum,
    ClassFunction.innerSum, ClassFunction.innerSum, hsum, hinv]

/-- **Induction in stages**.  For nested subgroups `K ≤ H ≤ M`, inducing a class function `ψ` of
`K` to `M` in one step agrees with inducing first to `H` (of `ψ` transported to `K.subgroupOf H`)
and then to `M`: `Ind^M_H (Ind^H_{K.subgroupOf H} (ψ ∘ e)) = Ind^M_K ψ`, where
`e : K.subgroupOf H ≃* K`.

Proved by completeness (`classFunction_eq_zero_of_orthogonal`): for every `χ ∈ Irr M`, double
Frobenius reciprocity reduces `⟨LHS, χ⟩` to `⟨ψ∘e, Res_{K.subgroupOf H}(Res_H χ)⟩`, the restriction
`Res_{K.subgroupOf H}(Res_H χ) = (Res_K χ)∘e` is the same `M`-value, and `inner_compHom_of_mulEquiv`
strips the transport to give `⟨ψ, Res_K χ⟩ = ⟨Ind^M_K ψ, χ⟩` (Frobenius). -/
theorem induce_induce_subgroupOf {M : Type*} [Group M] [Fintype M] [Invertible (Nat.card M : ℂ)]
    {K H : Subgroup M} (hKH : K ≤ H)
    [Fintype ↥H] [Finite ↥K] [Finite ↥(K.subgroupOf H)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card ↥(K.subgroupOf H) : ℂ)]
    (ψ : ClassFunction ↥K ℂ) :
    ClassFunction.induce H (ClassFunction.induce (K.subgroupOf H)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom ψ))
      = ClassFunction.induce K ψ := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  haveI : Fintype ↥(K.subgroupOf H) := Fintype.ofFinite _
  set e := Subgroup.subgroupOfEquivOfLe hKH with he
  have hres : ∀ χ : IrreducibleCharacter M,
      ClassFunction.restrict (K.subgroupOf H)
          (ClassFunction.restrict H (χ : ClassFunction M ℂ))
        = ClassFunction.compHom e.toMonoidHom (ClassFunction.restrict K (χ : ClassFunction M ℂ)) :=
            by
    intro χ; ext y
    rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply, ClassFunction.compHom_apply,
      ClassFunction.restrict_apply]
    congr 1
  refine sub_eq_zero.mp (classFunction_eq_zero_of_orthogonal _ (fun χ => ?_))
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_induce_eq_inner_restrict,
    ClassFunction.inner_induce_eq_inner_restrict, hres χ, inner_compHom_of_mulEquiv,
    ClassFunction.inner_induce_eq_inner_restrict, sub_self]

end OddOrder.RepresentationTheory
