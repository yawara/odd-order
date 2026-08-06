/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BrauerSuzukiEndgame
import OddOrder.GroupTheory.RepresentationTheory.Modular.WedderburnKernel

/-!
# The "analysis at `t`", assembled — Navarro pp. 142–145 in one statement

`OddOrder.Algebra.exists_eq_of_columns_of_odd_degrees` runs Navarro's integer computation and
returns a nontrivial `χ` with `χ(t) = χ(1)`; `exists_proper_normal_of_character_eq` turns such a
`χ` into the proper normal subgroup containing `t`.  This file composes the two, so that the whole
character-theoretic core of the `Q₈` case reads

> **given the four columns of the analysis at `y` and at `t` as integer columns with Navarro's
> pairing table, the involution lies in a proper normal subgroup.**

The columns are indexed by all of `Irr(G)`, not just by `Irr(B_0)`: outside the principal block
they are zero, which changes none of the sums.  That avoids carrying a subtype of `Irr(G)` and its
inclusion around.

Everything below is hypothesis-parameterised and `sorry`-free; what remains for the `Q₈` case is to
*supply* those hypotheses from a `2`-modular system over `𝓞_ℂ_[2]` (issue 9506, task F).

## Main results

* `OddOrder.RepresentationTheory.Modular.character_one_eq_card` — the degree column is integral
* `OddOrder.RepresentationTheory.Modular.exists_intCast_character_of_involution` — so is the
  column of values at the involution
* `OddOrder.RepresentationTheory.Modular.exists_proper_normal_of_columns`
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra

variable {K G : Type*} [Field K] [CharZero K] [Group G] [Fintype G] [Fintype (ConjClasses G)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι'] [Invertible (Nat.card G : K)]

/-! ### Two of the six columns are integral for free -/

omit [CharZero K] [Fintype G] [Fintype (ConjClasses G)] [∀ i, Nonempty (m i)] [Fintype ι']
  [Invertible (Nat.card G : K)] in
set_option linter.unusedFintypeInType false in
/-- **The degree column is `dim` of the matrix block.**  So `gdeg k = card (m k)` is the integer
column the endgame wants, and it is `≥ 1` because every block is nonempty. -/
theorem character_one_eq_card (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K) (k : ι') :
    (wedderburnRepresentation e k).character 1 = ((Fintype.card (m k) : ℤ) : K) := by
  rw [Representation.char_one, Module.finrank_fintype_fun_eq_card]
  push_cast
  rfl

omit [Fintype G] [Fintype (ConjClasses G)] [∀ i, Nonempty (m i)] [Fintype ι']
  [Invertible (Nat.card G : K)] in
set_option linter.unusedFintypeInType false in
/-- **The column of values at an involution is integral** —
`exists_intCast_character_of_mul_self_eq_one` for every block at once. -/
theorem exists_intCast_character_of_involution
    (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K) {t : G} (ht : t * t = 1) :
    ∃ Tval : ι' → ℤ, ∀ k, ((Tval k : ℤ) : K) = (wedderburnRepresentation e k).character t := by
  choose Tval hTval using fun k : ι' =>
    OddOrder.RepresentationTheory.exists_intCast_character_of_mul_self_eq_one
      (wedderburnRepresentation e k) two_ne_zero ht
  exact ⟨Tval, fun k => (hTval k).symm⟩

omit [Fintype G] [Fintype (ConjClasses G)] [∀ i, Nonempty (m i)] [Fintype ι']
  [Invertible (Nat.card G : K)] in
set_option linter.unusedFintypeInType false in
/-- **The trivial block is `1 × 1`**, read off its character: `χ_{i₀}(1) = 1`. -/
theorem card_eq_one_of_character_eq_one (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
    {i₀ : ι'} (hi₀ : ∀ g : G, (wedderburnRepresentation e i₀).character g = 1) :
    ((Fintype.card (m i₀) : ℤ)) = 1 := by
  have h : ((Fintype.card (m i₀) : ℤ) : K) = ((1 : ℤ) : K) := by
    rw [← character_one_eq_card e i₀, hi₀ 1, Int.cast_one]
  exact Int.cast_injective h

omit [Field K] [CharZero K] [Group G] [Fintype G] [Fintype (ConjClasses G)]
  [∀ i, DecidableEq (m i)] [Fintype ι'] [Invertible (Nat.card G : K)] in
set_option linter.unusedFintypeInType false in
/-- The degrees are at least `1`. -/
theorem one_le_card (k : ι') : (1 : ℤ) ≤ (Fintype.card (m k) : ℤ) := by
  exact_mod_cast Fintype.card_pos (α := m k)

set_option linter.unusedFintypeInType false in
/-- **The character-theoretic core of the `Q₈` case of Brauer–Suzuki.**

`a = D^y_0` and `b, c, d = D^t_0, D^t_1, D^t_2` are the four integer columns produced by the
"analysis at `y`" and the "analysis at `t`", `gdeg` is the column of degrees and `Tval` the column
of values at the involution `t`.  Given Navarro's pairing table (p. 141), the values at the trivial
character (p. 141), the expansion `χ(t) = D^t_0 + ψ_1(1) D^t_1 + ψ_2(1) D^t_2` with odd
`ψ_i(1)`, the congruence `χ(t) ≡ χ(y) mod 2` and Burnside's relation (10), the involution `t` lies
in a proper normal subgroup — the kernel of the character the computation produces.

The expansion and the congruence are only asked for on a predicate `Q` — in the application,
`χ ∈ Irr(B_0(G))`, which is where Navarro's display on p. 141 holds — together with `hzero`, the
vanishing of the four columns off `Q`.  The pairing table, in contrast, is stated over all of
`Irr(G)`: `hzero` makes the sums the same either way, so no subtype of `Irr(G)` is needed. -/
theorem exists_proper_normal_of_columns (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
    {t : G} (ht : t * t = 1) {i₀ : ι'}
    (hi₀ : ∀ g : G, (wedderburnRepresentation e i₀).character g = 1)
    {a b c d gdeg Tval : ι' → ℤ} {s₁ s₂ : ℤ}
    (hgdeg : ∀ k, ((gdeg k : ℤ) : K) = (wedderburnRepresentation e k).character 1)
    (hTval : ∀ k, ((Tval k : ℤ) : K) = (wedderburnRepresentation e k).character t)
    (haa : ∑ k, a k * a k = 4) (hbb : ∑ k, b k * b k = 4) (hcc : ∑ k, c k * c k = 4)
    (hdd : ∑ k, d k * d k = 4) (hab : ∑ k, a k * b k = 0) (hac : ∑ k, a k * c k = 0)
    (had : ∑ k, a k * d k = 0) (hbc : ∑ k, b k * c k = 2) (hbd : ∑ k, b k * d k = 2)
    (hcd : ∑ k, c k * d k = 2)
    (hga : ∑ k, gdeg k * a k = 0) (hgb : ∑ k, gdeg k * b k = 0) (hgc : ∑ k, gdeg k * c k = 0)
    (hgd : ∑ k, gdeg k * d k = 0)
    (hg0 : gdeg i₀ = 1) (hgpos : ∀ k, 1 ≤ gdeg k)
    (ha0 : a i₀ = 1) (hb0 : b i₀ = 1) (hc0 : c i₀ = 0) (hd0 : d i₀ = 0)
    {Q : ι' → Prop} (hT : ∀ k, Q k → Tval k = b k + s₁ * c k + s₂ * d k)
    (hs₁ : Odd s₁) (hs₂ : Odd s₂)
    (hcong : ∀ k, Q k → (2 : ℤ) ∣ (a k + Tval k))
    (hzero : ∀ k, ¬ Q k → a k = 0 ∧ b k = 0 ∧ c k = 0 ∧ d k = 0)
    (h10 : ∀ v : ι' → ℤ, (∀ k, 2 * v k = a k + b k - c k - d k) →
      ∀ i j : ι', i ≠ i₀ → j ≠ i₀ → i ≠ j → v i = 1 → v j = -1 →
        (∀ k, k ≠ i₀ → k ≠ i → k ≠ j → v k = 0) →
        gdeg i * gdeg j + Tval i ^ 2 * gdeg j - Tval j ^ 2 * gdeg i = 0) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ t ∈ N := by
  obtain ⟨k, hk, hkeq⟩ := OddOrder.Algebra.exists_eq_of_columns_of_odd_degrees haa hbb hcc hdd
    hab hac had hbc hbd hcd hga hgb hgc hgd hg0 hgpos ha0 hb0 hc0 hd0 hT hs₁ hs₂ hcong hzero h10
  refine exists_proper_normal_of_character_eq e hk hi₀ ht ?_
  rw [← hgdeg k, ← hTval k, hkeq]

end OddOrder.RepresentationTheory.Modular
