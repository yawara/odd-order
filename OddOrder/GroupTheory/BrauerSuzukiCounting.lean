/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.BrauerSuzukiInvolutions
import OddOrder.GroupTheory.BrauerSuzukiCharacter
import OddOrder.GroupTheory.RepresentationTheory.ClassSumCoefficientFormula

/-!
# Brauer–Suzuki: counting involution pairs (Gorenstein Ch. 12, towards Lemma 1.8)

**Gorenstein, *Finite Groups*, Ch. 12, Lemma 1.8** derives the character relation
`1 + χ₁(u)²/χ₁(1) − χ(u)²/χ(1) = 0` from the class-sum structure-constant formula `(9.4.2)`
applied to `β(y) = #{(u, v) : u, v involutions, uv = y}`.

This file assembles the pieces on the counting side.  Working with the *class-summed*
coefficient `classSumCoeff K K Cs` (over the whole target class `Cs`) rather than the
per-element `β(y)` lets us reuse `classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter`
directly.  The involutions of `G` form the single conjugacy class `K = mk z`
(`isConj_z_iff_orderOf_eq_two`), and:

* `classSumCoeff K K Cs = 0` whenever `Cs` has even order, because the product of two
  involutions has odd order (`odd_orderOf_mul_of_involution`).
-/

open OddOrder.RepresentationTheory

namespace OddOrder.GroupTheory

/-- `IsConj` preserves order. -/
theorem orderOf_eq_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  exact SemiconjBy.orderOf_eq c (show SemiconjBy c a (c * a * c⁻¹) by
    change c * a = c * a * c⁻¹ * c; group)

namespace QuaternionSylowSetup

variable {G : Type*} [Group G] [Finite G] (Q : QuaternionSylowSetup G)

/-- The conjugacy class `K` of involutions of `G` (all involutions are conjugate to `z`). -/
def involutionClass : ConjClasses G := ConjClasses.mk Q.z

include Q

/-- `u` lies in the involution class iff `u` is an involution. -/
theorem mk_eq_involutionClass_iff {u : G} :
    ConjClasses.mk u = Q.involutionClass ↔ orderOf u = 2 := by
  rw [involutionClass, ConjClasses.mk_eq_mk_iff_isConj, Q.isConj_z_iff_orderOf_eq_two]

/-- **`classSumCoeff K K Cs = 0` for a class `Cs` of even order** (towards Gorenstein Lemma 1.8):
no ordered pair of involutions multiplies to an element of `Cs`, since the product of two
involutions has odd order (`odd_orderOf_mul_of_involution`) while every element of `Cs` has the
same even order. -/
theorem classSumCoeff_involutionClass_eq_zero_of_even
    [Fintype G] [DecidableEq (ConjClasses G)] {Cs : ConjClasses G}
    (hCs : Even (orderOf Cs.out)) :
    classSumCoeff Q.involutionClass Q.involutionClass Cs = 0 := by
  classical
  rw [classSumCoeff, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨u, v⟩ -
  rintro ⟨hu, hv, huv⟩
  have hu2 : orderOf u = 2 := Q.mk_eq_involutionClass_iff.mp hu
  have hv2 : orderOf v = 2 := Q.mk_eq_involutionClass_iff.mp hv
  have hodd : Odd (orderOf (u * v)) := Q.odd_orderOf_mul_of_involution hu2 hv2
  have hconj : IsConj (u * v) Cs.out := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj, huv, conjClass_mk_out]
  rw [orderOf_eq_of_isConj hconj] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) hCs

/-- **`∑_Cs classSumCoeff K K Cs · θ*(Cs.out) = 0`** (Gorenstein Lemma 1.8, `β·θ* = 0` summed
by class).  Each term vanishes: if `Cs.out` has even order then `classSumCoeff K K Cs = 0`
(`classSumCoeff_involutionClass_eq_zero_of_even`); if it has odd order then `θ*(Cs.out) = 0`
(`thetaStar_apply_eq_zero_of_odd`, Lemma 1.6). -/
theorem sum_classSumCoeff_thetaStar_eq_zero
    [Fintype G] [Fintype ↥Q.N] [Fintype (ConjClasses G)] [DecidableEq (ConjClasses G)]
    [Invertible (Nat.card ↥Q.N : ℂ)] [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    ∑ Cs : ConjClasses G,
      (classSumCoeff Q.involutionClass Q.involutionClass Cs : ℂ) * Q.thetaStar Cs.out = 0 := by
  apply Finset.sum_eq_zero
  intro Cs _
  rcases Nat.even_or_odd (orderOf Cs.out) with heven | hodd
  · rw [Q.classSumCoeff_involutionClass_eq_zero_of_even heven, Nat.cast_zero, zero_mul]
  · rw [Q.thetaStar_apply_eq_zero_of_odd hodd, mul_zero]

/-- **The `(9.4.2)`-weighted class sum equals the inner product `⟨θ*, χ⟩`** (Gorenstein
Lemma 1.8, the bridge from the class-sum formula to character multiplicities).  Summing
`θ*(Cs.out)·χ(Cs.out⁻¹)` weighted by `1/|C_G(Cs.out)|` over conjugacy classes reproduces the
normalized inner product `⟨θ*, χ⟩ = ⅟|G| · ∑_g θ*(g)·conj(χ(g))`, using the orbit-stabilizer
identity `|Cs|·|C_G(Cs.out)| = |G|` and `χ(g⁻¹) = conj(χ(g))`. -/
theorem sum_thetaStar_char_div_centralizer_eq_inner
    [Fintype G] [Fintype ↥Q.N] [Fintype (ConjClasses G)]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥Q.N : ℂ)]
    [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] (χ : IrreducibleCharacter G) :
    ∑ Cs : ConjClasses G, Q.thetaStar Cs.out * (χ : ClassFunction G ℂ) Cs.out⁻¹
        / (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ)
      = ClassFunction.inner Q.thetaStar (χ : ClassFunction G ℂ) := by
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum,
    classFunction_innerSum_eq_sum_conjClasses, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Cs _ => ?_
  -- reconcile the representative `conjugacyClassRepresentative Cs` with `Cs.out`
  have hrepconj : IsConj (conjugacyClassRepresentative Cs) Cs.out := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj, conjugacyClassRepresentative_mk_eq, conjClass_mk_out]
  have hθ : Q.thetaStar (conjugacyClassRepresentative Cs) = Q.thetaStar Cs.out :=
    Q.thetaStar.of_isConj hrepconj
  have hχ : (χ : ClassFunction G ℂ) (conjugacyClassRepresentative Cs)
      = (χ : ClassFunction G ℂ) Cs.out :=
    (χ : ClassFunction G ℂ).of_isConj hrepconj
  rw [hθ, hχ, irreducibleCharacter_apply_inv]
  -- orbit-stabilizer: `|Cs|·|C_G(Cs.out)| = |G|`
  have hcent : (conjugacyClassSize Cs : ℂ)
      * (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ) = (Nat.card G : ℂ) := by
    have h := conjugacyClassSize_mk_mul_card_centralizer_cast (G := G) Cs.out
    rwa [conjClass_mk_out] at h
  have hgne : (Nat.card G : ℂ) ≠ 0 := Invertible.ne_zero _
  have hcentne : (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hcent; exact hgne hcent.symm
  -- `1/|C_G(Cs.out)| = |Cs| · 1/|G|`
  have hc_inv : (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ)⁻¹
      = (conjugacyClassSize Cs : ℂ) * (Nat.card G : ℂ)⁻¹ := by
    field_simp
    linear_combination -hcent
  rw [invOf_eq_inv, div_eq_mul_inv, hc_inv]; ring

/-- **`∑_χ (|K|·χ(u))²/χ(1) · ⟨θ*, χ⟩ = 0`** (Gorenstein Lemma 1.8, the character-sum form).
Substituting the class-sum formula `(9.4.2)` into `sum_classSumCoeff_thetaStar_eq_zero` and
recognizing the resulting weighted class sum as `⟨θ*, χ⟩`
(`sum_thetaStar_char_div_centralizer_eq_inner`) turns the vanishing class sum into a vanishing
sum over irreducible characters. -/
theorem sum_degWeight_inner_eq_zero
    [Fintype G] [Fintype ↥Q.N]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥Q.N : ℂ)]
    [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    ∑ χ : IrreducibleCharacter G,
        ((Nat.card { x : G // ConjClasses.mk x = Q.involutionClass } : ℂ)
              * (χ : ClassFunction G ℂ) Q.involutionClass.out
            * ((Nat.card { x : G // ConjClasses.mk x = Q.involutionClass } : ℂ)
              * (χ : ClassFunction G ℂ) Q.involutionClass.out)
          / (χ : ClassFunction G ℂ) 1)
          * ClassFunction.inner Q.thetaStar (χ : ClassFunction G ℂ) = 0 := by
  classical
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  rw [← Q.sum_classSumCoeff_thetaStar_eq_zero]
  -- rewrite `⟨θ*, χ⟩` as the weighted class sum, then swap the order of summation
  rw [Finset.sum_congr rfl fun χ _ => by
    rw [← Q.sum_thetaStar_char_div_centralizer_eq_inner χ, Finset.mul_sum], Finset.sum_comm]
  refine Finset.sum_congr rfl fun Cs _ => ?_
  -- per class `Cs`: the inner `∑_χ` reassembles the `(9.4.2)` right-hand side
  have h942 := classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter
    (G := G) Q.involutionClass Q.involutionClass Cs
  have hgne : (Nat.card G : ℂ) ≠ 0 := Invertible.ne_zero _
  have hcent : (conjugacyClassSize Cs : ℂ)
      * (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ) = (Nat.card G : ℂ) := by
    have h := conjugacyClassSize_mk_mul_card_centralizer_cast (G := G) Cs.out
    rwa [conjClass_mk_out] at h
  have hcentne : (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hcent; exact hgne hcent.symm
  -- factor `θ*(Cs.out)/|C_G|` out of the `∑_χ` (abstracting the `χ`-dependent factors as
  -- `a, b` to avoid coercion friction), then use `(9.4.2)`
  have reorder : ∀ a b : ℂ, a * (Q.thetaStar Cs.out * b
        / (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ))
      = Q.thetaStar Cs.out / (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ) * (a * b) :=
    fun a b => by ring
  simp_rw [reorder]
  rw [← Finset.mul_sum, ← h942]
  field_simp

/-- **Gorenstein Ch.12 Lemma 1.8**: for the decomposition `θ* = 1_G + χ₁ − χ` (Lemma 1.5),
`1 + χ₁(u)²/χ₁(1) − χ(u)²/χ(1) = 0`, where `u` is an involution (the class-`K` representative).
Collapsing `sum_degWeight_inner_eq_zero` by `⟨θ*, ψ⟩ = δ_{1,ψ} + δ_{χ₁,ψ} − δ_{χ,ψ}`
(orthonormality) leaves the three terms `|K|²·(1 + χ₁(u)²/χ₁(1) − χ(u)²/χ(1)) = 0`; dividing by
`|K|² ≠ 0` gives the relation. -/
theorem lem_1_8_relation
    [Fintype G] [Fintype ↥Q.N] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥Q.N : ℂ)]
    [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] {χ₁ χd : IrreducibleCharacter G}
    (hdecomp : Q.thetaStar = trivialClassFunction G + (χ₁ : ClassFunction G ℂ)
      - (χd : ClassFunction G ℂ)) :
    1 + (χ₁ : ClassFunction G ℂ) Q.involutionClass.out ^ 2 / (χ₁ : ClassFunction G ℂ) 1
      - (χd : ClassFunction G ℂ) Q.involutionClass.out ^ 2 / (χd : ClassFunction G ℂ) 1 = 0 := by
  classical
  have hB2 := Q.sum_degWeight_inner_eq_zero
  set N := (Nat.card { x : G // ConjClasses.mk x = Q.involutionClass } : ℂ) with hN
  set u₀ := Q.involutionClass.out with hu₀
  -- `∑_χ g(χ)·⟨a, χ⟩ = g(a)` by orthonormality (only the `χ = a` term survives); stated for
  -- a class function `a` so it applies uniformly to `1_G`, `χ₁`, `χ`
  have hcollapse : ∀ a : ClassFunction G ℂ, a ∈ irreducibleCharacters G →
      ∑ χ : IrreducibleCharacter G,
          (N * (χ : ClassFunction G ℂ) u₀ * (N * (χ : ClassFunction G ℂ) u₀)
            / (χ : ClassFunction G ℂ) 1) * ClassFunction.inner a (χ : ClassFunction G ℂ)
        = N * a u₀ * (N * a u₀) / a 1 := by
    intro a ha
    rw [Finset.sum_eq_single (⟨a, mem_irreducibleCharacters.mp ha⟩ : IrreducibleCharacter G)]
    · simp only [IrreducibleCharacter.coe_mk]
      rw [irr_cf_inner ha ha, if_pos rfl, mul_one]
    · intro b _ hb
      rw [irr_cf_inner ha (mem_irreducibleCharacters.mpr b.2),
        if_neg (fun h => hb (Subtype.ext h).symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- expand `⟨θ*, χ⟩ = ⟨1_G, χ⟩ + ⟨χ₁, χ⟩ − ⟨χ, χ⟩` (ground rewrite of `θ*`) and collapse each sum
  simp only [hdecomp, ClassFunction.inner_sub_left, ClassFunction.inner_add_left,
    mul_add, mul_sub] at hB2
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    hcollapse _ (mem_irreducibleCharacters.mpr trivialClassFunction_isIrreducible),
    hcollapse _ (mem_irreducibleCharacters.mpr χ₁.2),
    hcollapse _ (mem_irreducibleCharacters.mpr χd.2)] at hB2
  -- `g(1_G) = N²` since the trivial character is `1` everywhere
  simp only [trivialClassFunction_apply] at hB2
  -- `N ≠ 0` (the class `K` is nonempty: `z ∈ K`)
  have hNpos : 0 < Nat.card { x : G // ConjClasses.mk x = Q.involutionClass } := by
    have : Nonempty { x : G // ConjClasses.mk x = Q.involutionClass } :=
      ⟨Q.z, by rw [involutionClass]⟩
    exact Nat.card_pos
  have hNne : N ≠ 0 := by rw [hN]; exact_mod_cast hNpos.ne'
  -- factor `N²` and divide
  have hfactor : N * 1 * (N * 1) / 1
      + N * (χ₁ : ClassFunction G ℂ) u₀ * (N * (χ₁ : ClassFunction G ℂ) u₀)
        / (χ₁ : ClassFunction G ℂ) 1
      - N * (χd : ClassFunction G ℂ) u₀ * (N * (χd : ClassFunction G ℂ) u₀)
        / (χd : ClassFunction G ℂ) 1
      = N ^ 2 * (1 + (χ₁ : ClassFunction G ℂ) u₀ ^ 2 / (χ₁ : ClassFunction G ℂ) 1
          - (χd : ClassFunction G ℂ) u₀ ^ 2 / (χd : ClassFunction G ℂ) 1) := by
    ring
  rw [hfactor] at hB2
  exact (mul_eq_zero.mp hB2).resolve_left (pow_ne_zero 2 hNne)

/-- **Gorenstein Ch.12 Lemma 1.9**: `G` possesses a **non-linear** irreducible character `χ`
(degree `≥ 2`) whose kernel contains **every involution** (`χ(u) = χ(1)` for `orderOf u = 2`).
From Lemma 1.8's relation, together with `χ(u) = 1 + χ₁(u)` (Lemma 1.6) and `χ(1) = χ₁(1) + 1`
(Lemma 1.5), clearing denominators reduces to `(χ(u) − χ(1))² = 0`; and any involution is
conjugate to the class representative, so `χ` is constant on all of them. -/
theorem lem_1_9
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥Q.N : ℂ)]
    [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    ∃ χ : IrreducibleCharacter G, (∃ d : ℕ, 2 ≤ d ∧ (χ : ClassFunction G ℂ) 1 = (d : ℂ)) ∧
      ∀ u : G, orderOf u = 2 → (χ : ClassFunction G ℂ) u = (χ : ClassFunction G ℂ) 1 := by
  haveI : Fintype G := Fintype.ofFinite _
  haveI : Fintype ↥Q.N := Fintype.ofFinite _
  obtain ⟨χ₁, χ, _, _, _, hdecomp, hdeg⟩ := Q.thetaStar_decomposition
  have h18 := Q.lem_1_8_relation hdecomp
  set u₀ := Q.involutionClass.out with hu₀
  -- `u₀` is an involution, so `θ*(u₀) = 0` and `χ(u₀) = 1 + χ₁(u₀)`
  have hu₀2 : orderOf u₀ = 2 := Q.mk_eq_involutionClass_iff.mp (conjClass_mk_out _)
  have hval : (χ : ClassFunction G ℂ) u₀ = (χ₁ : ClassFunction G ℂ) u₀ + 1 :=
    Q.apply_eq_of_thetaStar_apply_eq_zero hdecomp (Q.thetaStar_apply_eq_zero_of_orderOf_eq_two hu₀2)
  -- character degrees are positive integers, hence nonzero
  obtain ⟨d, hdpos, hd1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  obtain ⟨d1, hd1pos, hd11⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ₁
  have hχ1ne : (χ : ClassFunction G ℂ) 1 ≠ 0 := by rw [hd1]; exact_mod_cast hdpos.ne'
  have hχ₁1ne : (χ₁ : ClassFunction G ℂ) 1 ≠ 0 := by rw [hd11]; exact_mod_cast hd1pos.ne'
  -- `(χ(u₀) − χ(1))² = 0`
  have hχ₁u : (χ₁ : ClassFunction G ℂ) u₀ = (χ : ClassFunction G ℂ) u₀ - 1 := by rw [hval]; ring
  have hχ₁1 : (χ₁ : ClassFunction G ℂ) 1 = (χ : ClassFunction G ℂ) 1 - 1 := by rw [hdeg]; ring
  have hq1 : (χ : ClassFunction G ℂ) 1 - 1 ≠ 0 := by rw [← hχ₁1]; exact hχ₁1ne
  have hsq0 : ((χ : ClassFunction G ℂ) u₀ - (χ : ClassFunction G ℂ) 1) ^ 2 = 0 := by
    rw [hχ₁u, hχ₁1] at h18
    field_simp [hχ1ne, hq1] at h18
    linear_combination h18
  have hval0 : (χ : ClassFunction G ℂ) u₀ = (χ : ClassFunction G ℂ) 1 :=
    sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq0)
  refine ⟨χ, ⟨d1 + 1, by omega, ?_⟩, ?_⟩
  · rw [hdeg, hd11]; push_cast; ring
  · -- any involution `u` is conjugate to `u₀`, so `χ(u) = χ(u₀) = χ(1)`
    intro u hu
    rw [(χ : ClassFunction G ℂ).of_isConj (Q.isConj_of_orderOf_eq_two hu hu₀2), hval0]

end QuaternionSylowSetup

end OddOrder.GroupTheory
