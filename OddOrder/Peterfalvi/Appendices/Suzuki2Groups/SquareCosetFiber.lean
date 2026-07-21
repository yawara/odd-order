/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.InvariantSummands

/-!
# Peterfalvi Part II, Ch. I §3, Lemma 5: the square fiber of a summand

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, Lemma 5, p. 107.

In the Suzuki setting `Q₀ = Z(Q)` is central of exponent two, so squaring in
`Q` is constant on `Q₀`-cosets and descends to a *function* (not a
homomorphism) `cosetSquare : Q ⧸ Q₀ → Q`.  On an invariant summand `X̄` of
order `q = |Q₀|`, this function restricts to a bijection from `X̄ \ {1}`
onto the involutions `Q₀ \ {1}`: it is equivariant for the `K`-action,
nonidentity cosets have nonidentity squares because all involutions lie in
`Q₀`, transitivity of `K` on the involutions makes it surjective, and equal
cardinalities upgrade surjectivity to bijectivity.

This is the source counting `|{x ∈ X | x² = s}| = (q² − q)/(q − 1) = q`: the
fiber of the square map over a fixed involution `s` is a single `Q₀`-coset,
supplied here through the unique-fiber corollary.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.Isaacs.Ch03
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

universe uK uP

variable {P : Type uP} [Group P]

/-! ## The coset square function -/

section CosetSquare

variable (Z : Subgroup P) [Z.Normal]
variable (hZle : Z ≤ Subgroup.center P) (hZsq : ∀ z ∈ Z, z ^ 2 = 1)

/-- Squaring is constant on the cosets of a central subgroup of exponent
two, hence descends to a function on the quotient.  It is not a group
homomorphism in general. -/
def cosetSquare : P ⧸ Z → P :=
  fun q => Quotient.liftOn' q (fun x => x ^ 2) (by
    intro x y hxy
    have hu : x⁻¹ * y ∈ Z := QuotientGroup.leftRel_apply.mp hxy
    have hcomm : Commute x (x⁻¹ * y) :=
      Subgroup.mem_center_iff.mp (hZle hu) x
    have hyu : y = x * (x⁻¹ * y) := by group
    calc x ^ 2 = x ^ 2 * (x⁻¹ * y) ^ 2 := by
          rw [hZsq _ hu, mul_one]
      _ = (x * (x⁻¹ * y)) ^ 2 := (hcomm.mul_pow 2).symm
      _ = y ^ 2 := by rw [← hyu])

omit [Z.Normal] in
@[simp]
theorem cosetSquare_mk (x : P) :
    cosetSquare Z hZle hZsq (QuotientGroup.mk x) = x ^ 2 := rfl

omit [Z.Normal] in
/-- The coset square lands in `Z` when all squares do. -/
theorem cosetSquare_mem (hAgemo : ∀ x : P, x ^ 2 ∈ Z) (q : P ⧸ Z) :
    cosetSquare Z hZle hZsq q ∈ Z := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  exact hAgemo x

/-- Only the identity coset has identity square, provided every involution
lies in `Z`. -/
theorem cosetSquare_eq_one_iff (hinv : ∀ x : P, x ^ 2 = 1 → x ∈ Z)
    (q : P ⧸ Z) :
    cosetSquare Z hZle hZsq q = 1 ↔ q = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [cosetSquare_mk]
  constructor
  · intro h1
    exact (QuotientGroup.eq_one_iff x).mpr (hinv x h1)
  · intro h1
    exact hZsq x ((QuotientGroup.eq_one_iff x).mp h1)

/-- The coset square is equivariant: the induced quotient action commutes
with squaring representatives. -/
theorem cosetSquare_equivariant {K : Type uK} [Group K]
    {rho : K →* MulAut P} (hZinv : IsAInvariant rho Z) (k : K) (q : P ⧸ Z) :
    cosetSquare Z hZle hZsq (quotientMulAutHom hZinv k q) =
      rho k (cosetSquare Z hZle hZsq q) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [show quotientMulAutHom hZinv k (QuotientGroup.mk x) =
      QuotientGroup.mk (rho k x) from rfl,
    cosetSquare_mk, cosetSquare_mk, map_pow]

end CosetSquare

/-! ## The square bijection on an invariant summand -/

section SquareBijection

variable [Finite P]
variable {K : Type uK} [Group K]
variable {Z : Subgroup P} [Z.Normal]
variable (hZle : Z ≤ Subgroup.center P) (hZsq : ∀ z ∈ Z, z ^ 2 = 1)
variable {rho : K →* MulAut P} (hZinv : IsAInvariant rho Z)

/-- **The square fiber bijection** (Peterfalvi Part II, Ch. I §3, Lemma 5,
p. 107).  On an invariant summand `X̄` of order `|Z|` the coset square maps
`X̄ \ {1}` bijectively onto `Z \ {1}`: nonidentity cosets have nonidentity
central squares, equivariance and transitivity of `K` on `Z \ {1}` give
surjectivity, and the equal cardinalities give injectivity. -/
theorem bijOn_cosetSquare
    (hAgemo : ∀ x : P, x ^ 2 ∈ Z) (hinv : ∀ x : P, x ^ 2 = 1 → x ∈ Z)
    {Xbar : Subgroup (P ⧸ Z)}
    (hXinv : IsAInvariant (quotientMulAutHom hZinv) Xbar)
    (hXcard : Nat.card ↥Xbar = Nat.card ↥Z)
    (htransZ : ∀ s₁ s₂ : P, s₁ ∈ Z → s₁ ≠ 1 → s₂ ∈ Z → s₂ ≠ 1 →
      ∃ k : K, rho k s₁ = s₂) :
    Set.BijOn (cosetSquare Z hZle hZsq)
      ((Xbar : Set (P ⧸ Z)) \ {1}) ((Z : Set P) \ {1}) := by
  classical
  have hmapsTo : Set.MapsTo (cosetSquare Z hZle hZsq)
      ((Xbar : Set (P ⧸ Z)) \ {1}) ((Z : Set P) \ {1}) := by
    rintro q ⟨-, hq1⟩
    simp only [Set.mem_singleton_iff] at hq1
    refine ⟨cosetSquare_mem Z hZle hZsq hAgemo q, ?_⟩
    intro h1
    simp only [Set.mem_singleton_iff] at h1
    exact hq1 ((cosetSquare_eq_one_iff Z hZle hZsq hinv q).mp h1)
  have hsurjOn : Set.SurjOn (cosetSquare Z hZle hZsq)
      ((Xbar : Set (P ⧸ Z)) \ {1}) ((Z : Set P) \ {1}) := by
    rintro s ⟨hsZ, hs1⟩
    simp only [Set.mem_singleton_iff] at hs1
    have hsZ' : s ∈ Z := hsZ
    have hXnontrivial : Xbar ≠ ⊥ := by
      intro hbot
      have hZtwo : 1 < Nat.card ↥Z := by
        refine (Subgroup.one_lt_card_iff_ne_bot Z).mpr ?_
        intro hZbot
        rw [hZbot, Subgroup.mem_bot] at hsZ'
        exact hs1 hsZ'
      rw [hbot, Subgroup.card_bot] at hXcard
      omega
    obtain ⟨q₁, hq₁X, hq₁bot⟩ :=
      SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hXnontrivial)
    have hq₁1 : q₁ ≠ 1 := by
      intro h1
      exact hq₁bot (by rw [h1]; exact Subgroup.one_mem ⊥)
    have hs₁mem : cosetSquare Z hZle hZsq q₁ ∈ Z :=
      cosetSquare_mem Z hZle hZsq hAgemo q₁
    have hs₁ne : cosetSquare Z hZle hZsq q₁ ≠ 1 := by
      intro h1
      exact hq₁1 ((cosetSquare_eq_one_iff Z hZle hZsq hinv q₁).mp h1)
    obtain ⟨k, hk⟩ := htransZ _ s hs₁mem hs₁ne hsZ' hs1
    refine ⟨quotientMulAutHom hZinv k q₁, ⟨hXinv.smul_mem k hq₁X, ?_⟩, ?_⟩
    · intro h1
      simp only [Set.mem_singleton_iff] at h1
      exact hq₁1 ((quotientMulAutHom hZinv k).injective
        (by rw [h1, map_one]))
    · rw [cosetSquare_equivariant Z hZle hZsq hZinv k q₁, hk]
  have hXset : (Xbar : Set (P ⧸ Z)).ncard = (Z : Set P).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
      SetLike.coe_sort_coe, hXcard]
  have hncard : ((Xbar : Set (P ⧸ Z)) \ {1}).ncard =
      ((Z : Set P) \ {1}).ncard :=
    calc ((Xbar : Set (P ⧸ Z)) \ {1}).ncard
        = (Xbar : Set (P ⧸ Z)).ncard - 1 :=
          Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem Xbar)
      _ = (Z : Set P).ncard - 1 := by rw [hXset]
      _ = ((Z : Set P) \ {1}).ncard :=
          (Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem Z)).symm
  have himage : cosetSquare Z hZle hZsq '' ((Xbar : Set (P ⧸ Z)) \ {1}) =
      (Z : Set P) \ {1} :=
    Set.Subset.antisymm (Set.MapsTo.image_subset hmapsTo) hsurjOn
  have hinjOn : Set.InjOn (cosetSquare Z hZle hZsq)
      ((Xbar : Set (P ⧸ Z)) \ {1}) := by
    apply Set.injOn_of_ncard_image_eq
    · rw [himage, hncard]
    · exact Set.toFinite _
  exact ⟨hmapsTo, hinjOn, hsurjOn⟩

/-- **Uniqueness of the square fiber over a fixed involution**: there is
exactly one coset of the summand whose square is `s`. -/
theorem existsUnique_cosetSquare_eq
    (hAgemo : ∀ x : P, x ^ 2 ∈ Z) (hinv : ∀ x : P, x ^ 2 = 1 → x ∈ Z)
    {Xbar : Subgroup (P ⧸ Z)}
    (hXinv : IsAInvariant (quotientMulAutHom hZinv) Xbar)
    (hXcard : Nat.card ↥Xbar = Nat.card ↥Z)
    (htransZ : ∀ s₁ s₂ : P, s₁ ∈ Z → s₁ ≠ 1 → s₂ ∈ Z → s₂ ≠ 1 →
      ∃ k : K, rho k s₁ = s₂)
    {s : P} (hs : s ∈ Z) (hs1 : s ≠ 1) :
    ∃ q ∈ Xbar, cosetSquare Z hZle hZsq q = s ∧
      ∀ r ∈ Xbar, cosetSquare Z hZle hZsq r = s → r = q := by
  have hbij := bijOn_cosetSquare hZle hZsq hZinv hAgemo hinv hXinv hXcard
    htransZ
  obtain ⟨q, hqmem, hq⟩ := hbij.surjOn ⟨hs, hs1⟩
  refine ⟨q, hqmem.1, hq, ?_⟩
  intro r hrX hr
  by_cases hr1 : r = 1
  · exfalso
    apply hs1
    rw [← hr, hr1]
    exact (cosetSquare_eq_one_iff Z hZle hZsq hinv 1).mpr rfl
  · exact hbij.injOn ⟨hrX, hr1⟩ hqmem (hr.trans hq.symm)

end SquareBijection

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
