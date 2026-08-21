/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.ClassSumAlgebra
import OddOrder.GroupTheory.RepresentationTheory.RealClassTISubset
import OddOrder.GroupTheory.RepresentationTheory.SchurCenterBound
import OddOrder.GroupTheory.RepresentationTheory.SumCharacterInvariants

/-!
# Peterfalvi (6.7), odd-order assembly

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), (6.7),
pp. 31–32.  Let `P` be a Sylow `p`-subgroup of `G`, `L = N_G(P)` of **odd** order, `P^#` a
TI-subset of `G`, `Z ⊴ L` with `1 ≠ Z ≤ Z(P)` and `|C_L(z)|` independent of `z ∈ Z^#`.  If
`ψ ∈ Irr G` is constant on `Z^#` then `ψ(z) ≡ ψ(1) (mod |P|)` (as algebraic integers).

`ClassSumAlgebra.peterfalvi_67` proves this with two inputs left as hypotheses; this file
discharges them and assembles the odd-order form `peterfalvi_67_of_odd`:

* `hreal` (`⟦z⁻¹⟧ ≠ ⟦z⟧`): from `|L|` odd via
  `RealClassTISubset.not_isConj_inv_of_isTISubset` (an element of an odd-order group
  conjugate to its inverse is trivial, transported through the TI condition);
* `hone` (`a₁₁ ≡ 1 + a₁₂ (mod |P|)`): the **trivial-character specialization** of the
  (6.7.2)–(6.7.3) machinery (`nonidentityZClassCoeffSum_cong_of_isTISubset`): for the
  trivial representation `ω(C) = |C|` and `ψ(z) = ψ(1) = 1`, so the same collapsed
  congruences with the coprime factor `|C₁|` cancelled yield the structure-constant
  congruence.

The conclusion is the `[ALGMOD |P|]` congruence of character values; consumers upgrade to a
`ℤ`-congruence where they separately know `ψ(z) ∈ ℤ` (in (6.8.2.2) the integrality comes
from the decomposition `Res_Z ψ = a·ρ_Z + b·1_Z`), using that a rational algebraic integer
is an integer (`OddOrder.RepresentationTheory.isIntegral_rat_imp_int`).
-/

namespace OddOrder.RepresentationTheory

-- 類和の中核 (`classSum` ほか) は `ClassSumCore` の一般係数環版。
open OddOrder.GroupTheory.CenterClassSum

open OddOrder.AlgInt

local notation3 "ω" ρ:max C:max => centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩

variable {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]

/-! ### The first conclusion of (6.7): `ψ(z) ∈ ℤ` -/

omit [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] in
/-- **Peterfalvi (6.7), first conclusion** (p. 32): a character that is **constant on `Z^#`** takes
an *integer* value there.  No Sylow, TI or odd-order hypothesis enters — this is the opening line
of the book's proof of (6.7):

> Since `(Res_Z^G ψ, 1_Z) ∈ ℕ`, `ψ(z) ∈ ℚ`, and, since `ψ(z)` is an algebraic integer, `ψ(z) ∈ ℤ`.

The multiplicity `(Res_Z ψ, 1_Z) = dim V^Z` comes from
`sum_character_eq_card_mul_finrank_invariants` applied to the restriction `ρ ∘ Z.subtype`:
constancy on `Z^#` collapses the sum to
`ψ(1) + (|Z| − 1)·ψ(z) = ∑_{w ∈ Z} ψ(w) = |Z| · dim V^Z`, exhibiting `ψ(z)` as the *rational*
`(|Z| · dim V^Z − dim V)/(|Z| − 1)` (the denominator is nonzero because `z ≠ 1` puts two elements
in `Z`).  Being also an algebraic integer (`character_isIntegral`) it is an integer
(`isIntegral_rat_imp_int`). -/
theorem exists_int_character_of_constant_on_nonidentity [Finite G] (ρ : Representation ℂ G V)
    {Z : Subgroup G} {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1)
    (hconst : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 → ρ.character w = ρ.character z) :
    ∃ n : ℤ, ρ.character z = (n : ℂ) := by
  classical
  have : Fintype ↥Z := Fintype.ofFinite _
  let ρZ : Representation ℂ ↥Z V := ρ.comp Z.subtype
  set N : ℕ := Fintype.card ↥Z with hNdef
  -- `Z` contains the two distinct elements `1` and `z`, so `N ≥ 2`.
  have hzne : (⟨z, hzZ⟩ : ↥Z) ≠ 1 := by simpa [Subtype.ext_iff] using hz1
  have : Nontrivial ↥Z := ⟨⟨⟨z, hzZ⟩, 1, hzne⟩⟩
  have hN2 : 2 ≤ N := Fintype.one_lt_card
  have hNne : ((N : ℂ) - 1) ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    have : N ≠ 1 := by omega
    simpa using (Nat.cast_injective (R := ℂ)).ne this
  have : Invertible ((Fintype.card ↥Z : ℂ)) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr (by omega : Fintype.card ↥Z ≠ 0))
  -- `∑_{w ∈ Z} ψ(w) = |Z| · dim V^Z`.
  have hsum := sum_character_eq_card_mul_finrank_invariants ρZ
  -- Constancy on `Z^#` collapses the left-hand side.
  have hsplit : ∑ w : ↥Z, ρZ.character w
      = ρ.character 1 + ((N : ℂ) - 1) * ρ.character z := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ↥Z))]
    have hcongr : ∀ w ∈ Finset.univ.erase (1 : ↥Z), ρZ.character w = ρ.character z := by
      intro w hw
      exact hconst w.2 fun h => (Finset.ne_of_mem_erase hw) (OneMemClass.coe_eq_one.mp h)
    have h2 : ∑ w ∈ Finset.univ.erase (1 : ↥Z), ρZ.character w
        = ((N : ℂ) - 1) * ρ.character z := by
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, nsmul_eq_mul]
      congr 1
      rw [← hNdef, Nat.cast_sub (by omega), Nat.cast_one]
    rw [h2]
    rfl
  rw [hsplit, ρ.char_one] at hsum
  -- `ψ(z)` is the rational `(N·m − d)/(N − 1)`.
  set m : ℕ := Module.finrank ℂ ρZ.invariants with hm
  set d : ℕ := Module.finrank ℂ V with hd
  have hq : ((((N : ℚ) * m - d) / ((N : ℚ) - 1) : ℚ) : ℂ) = ρ.character z := by
    push_cast
    rw [div_eq_iff hNne]
    linear_combination -hsum
  obtain ⟨n, hn⟩ := isIntegral_rat_imp_int (q := ((N : ℚ) * m - d) / ((N : ℚ) - 1))
    (by rw [hq]; exact character_isIntegral ρ z)
  exact ⟨n, by rw [← hq, hn]⟩

/-- **The trivial-character instance of (6.7.2)–(6.7.3)**: under the (6.7) Sylow/TI setup
the collapsed nonidentity-`Z` structure-constant sums satisfy
`a₁₁ ≡ 1 + a₁₂ (mod |P|)`.

For the trivial representation the central character is `ω(C) = |C|` and all character
values are `1`, so the two collapsed (6.7.2) congruences at `(1,1)` and `(1,2)` combine and
the coprime factor `q = |C₁|` cancels, leaving the structure-constant congruence that
`peterfalvi_67` consumes as its `hone` input. -/
theorem nonidentityZClassCoeffSum_cong_of_isTISubset [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {Z : Subgroup G}
    (hZP : Z ≤ (P : Subgroup G))
    (hZnormal : (Z.subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G))).Normal)
    (hti : OddOrder.GroupTheory.IsTISubset ((P : Set G) \ {1})
      (Subgroup.normalizer ((P : Subgroup G) : Set G)))
    {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1)
    (hPz : (P : Subgroup G) ≤ Subgroup.centralizer {z})
    (hreal : ConjClasses.mk z⁻¹ ≠ ConjClasses.mk z)
    (hcardconst : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 →
      Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ({w} : Set G)) =
        Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ({z} : Set G))) :
    nonidentityZClassCoeffSum Z (ConjClasses.mk z) (ConjClasses.mk z)
      ≡ 1 + nonidentityZClassCoeffSum Z (ConjClasses.mk z) (ConjClasses.mk z⁻¹)
        [ALGMOD (Nat.card (P : Subgroup G) : ℤ)] := by
  classical
  set ρ₀ : Representation ℂ G ℂ := Representation.trivial ℂ G ℂ with hρ₀
  have : ρ₀.IsIrreducible := isIrreducible_complex_rep ρ₀
  have hchar0 : ∀ g : G, ρ₀.character g = 1 := by
    intro g
    simp [hρ₀, Representation.character]
  let C₁ : ConjClasses G := ConjClasses.mk z
  let C₂ : ConjClasses G := ConjClasses.mk z⁻¹
  let α : ℂ := ω ρ₀ C₁
  let a₁₁ : ℂ := nonidentityZClassCoeffSum Z C₁ C₁
  let a₁₂ : ℂ := nonidentityZClassCoeffSum Z C₁ C₂
  let q : ℤ := Nat.card { x : G // ConjClasses.mk x = C₁ }
  have hzA : z ∈ (P : Set G) \ {1} := ⟨hZP hzZ, by simpa using hz1⟩
  have hωconst : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 → ω ρ₀ (ConjClasses.mk w) = α := by
    intro w hwZ hw1
    have hwA : w ∈ (P : Set G) \ {1} := ⟨hZP hwZ, by simpa using hw1⟩
    exact centralCharacterOfRep_eq_of_tiSubset_card_eq_of_character_eq ρ₀ hti hwA hzA
      (hcardconst hwZ hw1) (by rw [hchar0, hchar0])
  have hC₁ : ∃ y : G, y ∈ Z ∧ y ≠ 1 ∧ ConjClasses.mk y = C₁ := ⟨z, hzZ, hz1, rfl⟩
  have hC₂ : ∃ y : G, y ∈ Z ∧ y ≠ 1 ∧ ConjClasses.mk y = C₂ :=
    ⟨z⁻¹, Z.inv_mem hzZ, inv_ne_one.mpr hz1, rfl⟩
  have hcoeff11 : (classSum C₁ * classSum C₁ : MonoidAlgebra ℂ G).coeff (1 : G) = 0 := by
    rw [classSum_mul_apply_one_eq_classSumCoeff_one]
    rw [show classSumCoeff C₁ C₁ 1 = 0 by
      simpa [C₁] using classSumCoeff_self_one_eq_zero z hreal]
    norm_num
  have hcoeff12 : (classSum C₁ * classSum C₂ : MonoidAlgebra ℂ G).coeff (1 : G) = (q : ℂ) := by
    rw [classSum_mul_apply_one_eq_classSumCoeff_one]
    rw [show classSumCoeff C₁ C₂ 1 = Nat.card { x : G // ConjClasses.mk x = C₁ } by
      simpa [C₁, C₂] using classSumCoeff_self_inv_one_eq_card z]
    simp [q]
  have h11raw := centralCharacterOfRep_classSum_mul_cong_collapse_of_isTISubset ρ₀ P hZP
    hZnormal hti hC₁ hC₁ (α := α) hωconst
  have h12raw := centralCharacterOfRep_classSum_mul_cong_collapse_of_isTISubset ρ₀ P hZP
    hZnormal hti hC₁ hC₂ (α := α) hωconst
  have hωC₂ : ω ρ₀ C₂ = α := by
    simpa [C₂] using hωconst (Z.inv_mem hzZ) (inv_ne_one.mpr hz1)
  have h11 : (1 : ℂ) * α ^ 2 ≡ 1 * (a₁₁ * α)
      [ALGMOD (Nat.card (P : Subgroup G) : ℤ)] := by
    simpa [C₁, α, a₁₁, pow_two, hcoeff11, hchar0] using h11raw
  have h12 : (1 : ℂ) * α ^ 2 ≡ 1 * ((q : ℂ) + a₁₂ * α)
      [ALGMOD (Nat.card (P : Subgroup G) : ℤ)] := by
    simpa [C₁, C₂, α, a₁₂, q, pow_two, hcoeff12, hωC₂, hchar0] using h12raw
  have hsubst : (1 : ℂ) * α = (q : ℂ) * 1 := by
    have h := character_one_mul_centralCharacterOfRep_mk ρ₀ z
    simpa [C₁, α, q, hchar0] using h
  have hcop : IsCoprime q (Nat.card (P : Subgroup G) : ℤ) := by
    simpa [C₁, q] using coprime_card_class_card_sylow P hPz
  have ha₁₁ : IsIntegral ℤ a₁₁ := by
    simpa [a₁₁, C₁] using nonidentityZClassCoeffSum_isIntegral Z C₁ C₁
  have ha₁₂ : IsIntegral ℤ a₁₂ := by
    simpa [a₁₂, C₁, C₂] using nonidentityZClassCoeffSum_isIntegral Z C₁ C₂
  have hcomb := peterfalvi_673_combine h11 h12
  have hfinal := peterfalvi_673_cancel hcop isIntegral_one isIntegral_one ha₁₁ ha₁₂
    hsubst hcomb
  simpa [a₁₁, a₁₂, C₁, C₂] using hfinal

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Peterfalvi (6.7)** (odd-order form, mmd 04.8 L86).  Let `P` be a Sylow `p`-subgroup of
`G` with `L = N_G(P)` of **odd** order and `P^#` a TI-subset of `G`; let `Z ⊴ L` with
`Z ≤ P`, `z ∈ Z^#` centralized by `P` (the `Z ≤ Z(P)` instance at `z`), and `|C_L(·)|`
constant on `Z^#`.  If the irreducible character `ψ = χ_ρ` is constant on `Z^#`, then

`ψ(z) ≡ ψ(1) (mod |P|)`

as algebraic integers.  The two non-hypothesis inputs of `peterfalvi_67` are discharged:
`⟦z⁻¹⟧ ≠ ⟦z⟧` from oddness of `|L|`, and the structure-constant congruence from the
trivial-character specialization. -/
theorem peterfalvi_67_of_odd [Finite G] (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {Z : Subgroup G}
    (hZP : Z ≤ (P : Subgroup G))
    (hZnormal : (Z.subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G))).Normal)
    (hti : OddOrder.GroupTheory.IsTISubset ((P : Set G) \ {1})
      (Subgroup.normalizer ((P : Subgroup G) : Set G)))
    (hodd : Odd (Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G))))
    {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1)
    (hPz : (P : Subgroup G) ≤ Subgroup.centralizer {z})
    (hconst : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 →
      ρ.character w = ρ.character z ∧
        Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G))) :
    ρ.character z ≡ ρ.character 1 [ALGMOD (Nat.card (P : Subgroup G) : ℤ)] := by
  have hreal : ConjClasses.mk z⁻¹ ≠ ConjClasses.mk z := by
    rw [Ne, ConjClasses.mk_eq_mk_iff_isConj]
    exact not_isConj_inv_of_isTISubset P hodd hti (hZP hzZ) hz1
  exact peterfalvi_67 ρ P hZP hZnormal hti hzZ hz1 hPz hreal hconst
    (nonidentityZClassCoeffSum_cong_of_isTISubset P hZP hZnormal hti hzZ hz1 hPz hreal
      (fun w hw h1 => (hconst hw h1).2))

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Peterfalvi (6.7), both conclusions** (p. 32).  The book states two things about `ψ(z)` for
`z ∈ Z^#`:

> Then, for `z ∈ Z^#`, `ψ(z) ∈ ℤ` and `ψ(z) ≡ ψ(1) (mod |P|)`.

`peterfalvi_67_of_odd` supplies the second (as the algebraic-integer congruence `[ALGMOD |P|]`,
which is the book's own reading of the notation) and
`exists_int_character_of_constant_on_nonidentity` the first.  Since both values are then integers
(`ψ(1) = dim V`), the congruence sharpens to an ordinary divisibility in `ℤ`
(`int_dvd_of_cong_intCast`) — the form consumers previously had to assemble by hand. -/
theorem peterfalvi_67_int_dvd_of_odd [Finite G] (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {Z : Subgroup G}
    (hZP : Z ≤ (P : Subgroup G))
    (hZnormal : (Z.subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G))).Normal)
    (hti : OddOrder.GroupTheory.IsTISubset ((P : Set G) \ {1})
      (Subgroup.normalizer ((P : Subgroup G) : Set G)))
    (hodd : Odd (Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G))))
    {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1)
    (hPz : (P : Subgroup G) ≤ Subgroup.centralizer {z})
    (hconst : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 →
      ρ.character w = ρ.character z ∧
        Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G))) :
    ∃ n : ℤ, ρ.character z = (n : ℂ) ∧
      (Nat.card (P : Subgroup G) : ℤ) ∣ n - (Module.finrank ℂ V : ℤ) := by
  obtain ⟨n, hn⟩ := exists_int_character_of_constant_on_nonidentity ρ hzZ hz1
    (fun w hw h1 => (hconst hw h1).1)
  refine ⟨n, hn, ?_⟩
  have hcong := peterfalvi_67_of_odd ρ P hZP hZnormal hti hodd hzZ hz1 hPz hconst
  rw [hn, ρ.char_one] at hcong
  have hPne : (Nat.card (P : Subgroup G) : ℤ) ≠ 0 := by
    have hpos : 0 < Nat.card (P : Subgroup G) := Nat.card_pos
    exact_mod_cast hpos.ne'
  refine int_dvd_of_cong_intCast hPne ?_
  have hcast : (((Module.finrank ℂ V : ℤ)) : ℂ) = ((Module.finrank ℂ V : ℕ) : ℂ) := by
    push_cast
    ring
  rw [hcast]
  exact hcong

end OddOrder.RepresentationTheory
