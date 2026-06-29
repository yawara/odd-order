/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Norm.Transitivity
import OddOrder.GroupTheory.RepresentationTheory.ClassSumAlgebra
import OddOrder.GroupTheory.RepresentationTheory.ZIrr
import OddOrder.GroupTheory.RepresentationTheory.LinearCharacter
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter

/-!
# Peterfalvi (1.10): cyclotomic congruences of character values

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §1, p. 7,
result **(1.10)**.

This file develops the cyclotomic-integer arithmetic behind Peterfalvi (1.10):

* **(1.10.b)** `int_dvd_of_zeta_sub_one_dvd`: in a `p`-th cyclotomic field `L` over `ℚ`
  (`p` an odd prime, `ζ` a primitive `p`-th root of unity), if an integer `n` factors as
  `n = (ζ - 1) · a` with `a` an algebraic integer, then `p ∣ n`.  This is the divisibility
  half of (1.10), used (with (1.10.a)) in Peterfalvi (12.16) and (13.5).

The number-theoretic core is a norm computation: `N_{L/ℚ}(ζ - 1) = p`
(`IsPrimitiveRoot.norm_sub_one_of_prime_ne_two'`), `N(n) = n^{[L:ℚ]} = n^{p-1}`, and
`N(a) ∈ ℤ` (the norm of an algebraic integer), so `n^{p-1} = p · N(a)` and `p ∣ n`.
-/

namespace OddOrder.RepresentationTheory

open Polynomial Module

/-- `(1 - ε) ∣ (ε^k - 1)` in any commutative ring (the elementary divisibility behind (1.10.a)):
`ε^k - 1 = (ε - 1)·∑_{i<k} ε^i = (1 - ε)·(-∑_{i<k} ε^i)`.  Applied with `ε` a `p`-th root of unity
and `ε^k = α(x)` for a linear character `α` and an order-`p` element `x`. -/
theorem one_sub_dvd_pow_sub_one {R : Type*} [CommRing R] (ε : R) (k : ℕ) :
    (1 - ε) ∣ (ε ^ k - 1) :=
  ⟨-(∑ i ∈ Finset.range k, ε ^ i), by rw [← geom_sum_mul ε k]; ring⟩

/-- **Peterfalvi (1.10.a), per-linear-character core**: for a linear character `α : A → ℂˣ` of a
finite group `A`, a `p`-th-power-trivial element `x` (`x^p = 1`) and any `y`, the difference
`α(xy) - α(y)` is `(1 - ε)` times an algebraic integer (`ε` a primitive `p`-th root of unity).

Proof: `α(xy) - α(y) = (α(x) - 1)·α(y)`; `α(x)^p = 1` so `α(x) = ε^k`; `ε^k - 1 = (1-ε)·(-∑ εⁱ)`;
and `α(y)` is a root of unity, hence integral.  This is the linear-character building block of the
restriction-decomposition proof of (1.10.a) (`⟨x,y⟩` abelian ⟹ constituents are linear). -/
theorem exists_integral_linearChar_apply_sub {p : ℕ} (hp : 0 < p) {ε : ℂ}
    (hε : IsPrimitiveRoot ε p) {A : Type*} [Group A] [Finite A] (α : A →* ℂˣ)
    {x y : A} (hx : x ^ p = 1) :
    ∃ z : ℂ, IsIntegral ℤ z ∧ (α (x * y) : ℂ) - (α y : ℂ) = (1 - ε) * z := by
  haveI : NeZero p := ⟨hp.ne'⟩
  -- `α(x)` is a `p`-th root of unity, hence `= ε^k`
  have hαxp : (α x : ℂ) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hx, map_one, Units.val_one]
  obtain ⟨k, _, hk⟩ := hε.eq_pow_of_pow_eq_one hαxp
  -- `α(y)` is a root of unity (order divides `|A|`), hence integral
  have hαy : IsIntegral ℤ (α y : ℂ) := by
    refine isIntegral_of_pow_eq_one (n := Nat.card A) Nat.card_pos.ne' ?_
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  refine ⟨-(∑ i ∈ Finset.range k, ε ^ i) * (α y : ℂ), ?_, ?_⟩
  · have hε_mem : ε ∈ integralClosure ℤ ℂ := hε.isIntegral hp
    have hsum : IsIntegral ℤ (∑ i ∈ Finset.range k, ε ^ i) :=
      Subalgebra.sum_mem _ (fun i _ => Subalgebra.pow_mem _ hε_mem i)
    exact hsum.neg.mul hαy
  · have hgeom : ε ^ k - 1 = (1 - ε) * (-(∑ i ∈ Finset.range k, ε ^ i)) := by
      rw [← geom_sum_mul ε k]; ring
    rw [map_mul, Units.val_mul, ← hk]
    linear_combination (α y : ℂ) * hgeom

/-- **Peterfalvi (1.10.b)** (abstract cyclotomic form): in a `p`-th cyclotomic field `L` over `ℚ`
(`p` an odd prime), if an integer `n` is divisible by `ζ - 1` (`ζ` a primitive `p`-th root of
unity) with an algebraic-integer quotient `a`, then `p ∣ n`.

Norm argument: `N_{L/ℚ}(ζ - 1) = p`, `N(n) = n^{p-1}`, `N(a) ∈ ℤ`, so `n^{p-1} = p·N(a)`. -/
theorem int_dvd_of_zeta_sub_one_dvd {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    {n : ℤ} {a : L} (ha : IsIntegral ℤ a)
    (h : (algebraMap ℤ L n) = (ζ - 1) * a) :
    (p : ℤ) ∣ n := by
  haveI : NumberField L := inferInstance
  have hirr : Irreducible (cyclotomic p ℚ) := cyclotomic.irreducible_rat hp.out.pos
  -- the relative degree `[L : ℚ] = p - 1`
  have hfr : finrank ℚ L = p - 1 := by
    rw [IsCyclotomicExtension.finrank L hirr]; exact Nat.totient_prime hp.out
  -- take field norms `N_{L/ℚ}` of both sides
  have hN := congrArg (Algebra.norm ℚ) h
  rw [map_mul, hζ.norm_sub_one_of_prime_ne_two' hirr hp2] at hN
  -- `N(algebraMap ℤ L n) = (n : ℚ)^(p-1)`
  have hNn : Algebra.norm ℚ (algebraMap ℤ L n) = (n : ℚ) ^ (p - 1) := by
    have he : algebraMap ℤ L n = algebraMap ℚ L (n : ℚ) := by simp
    rw [he, Algebra.norm_algebraMap, hfr]
  -- `N(a)` is a rational integer, say `m`
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Algebra.norm ℚ a = (m : ℚ) := by
    have hint : IsIntegral ℤ (Algebra.norm ℚ a) := Algebra.isIntegral_norm ℚ ha
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    exact ⟨y, by rw [← hy]; simp⟩
  rw [hNn, hm] at hN
  -- `(n:ℚ)^(p-1) = p * m`, so as integers `n^(p-1) = p*m`, hence `p ∣ n`
  have hZ : (n : ℤ) ^ (p - 1) = (p : ℤ) * m := by exact_mod_cast hN
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  exact hpZ.dvd_of_dvd_pow ⟨m, hZ⟩

/-- **Peterfalvi (1.10.a)** (full, virtual-character form): for a finite **abelian** group `A`, a
virtual character `χ ∈ ℤ[Irr A]`, a `p`-th-power-trivial element `x` (`x^p = 1`) and any `y`, the
difference `χ(xy) - χ(y)` is `(1 - ε)` times an algebraic integer (`ε` a primitive `p`-th root).

Proof: the set of class functions with this property is a `ℤ`-submodule (closed under `+`, `ℤ`-smul,
contains `0`); it contains every irreducible character of `A` — each is a linear character
(`exists_linearIrreducibleCharacter_eq_of_isMulCommutative`) so the per-linear-character core
`exists_integral_linearChar_apply_sub` applies — hence it contains `ℤ[Irr A] = span ℤ (Irr A)`. -/
theorem exists_integral_zirr_apply_sub {p : ℕ} (hp : 0 < p) {ε : ℂ} (hε : IsPrimitiveRoot ε p)
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A] {χ : ClassFunction A ℂ}
    (hχ : χ ∈ ZIrr A) {x y : A} (hx : x ^ p = 1) :
    ∃ z : ℂ, IsIntegral ℤ z ∧ χ (x * y) - χ y = (1 - ε) * z := by
  -- the property, as a `ℤ`-submodule of `CF(A)`.
  let M : Submodule ℤ (ClassFunction A ℂ) :=
    { carrier := {ψ | ∃ z : ℂ, IsIntegral ℤ z ∧ ψ (x * y) - ψ y = (1 - ε) * z}
      zero_mem' := ⟨0, isIntegral_zero, by simp⟩
      add_mem' := by
        rintro ψ₁ ψ₂ ⟨z₁, hz₁, e₁⟩ ⟨z₂, hz₂, e₂⟩
        exact ⟨z₁ + z₂, hz₁.add hz₂, by
          simp only [ClassFunction.add_apply]; linear_combination e₁ + e₂⟩
      smul_mem' := by
        rintro c ψ ⟨z, hz, e⟩
        have hcz : IsIntegral ℤ ((c : ℂ) * z) :=
          (isIntegral_algebraMap (R := ℤ) (x := c)).mul hz
        refine ⟨(c : ℂ) * z, hcz, ?_⟩
        have happ : ∀ g, (c • ψ) g = (c : ℂ) * ψ g := fun g => by
          show c • ψ g = (c : ℂ) * ψ g
          rw [zsmul_eq_mul]
        rw [happ, happ]; linear_combination (c : ℂ) * e }
  -- every irreducible character of `A` lies in `M`.
  have hsub : irreducibleCharacters A ⊆ (M : Set (ClassFunction A ℂ)) := by
    intro α hα
    obtain ⟨θ, hθ⟩ :=
      (mem_irreducibleCharacters.mp hα).exists_linearIrreducibleCharacter_eq_of_isMulCommutative
    obtain ⟨z, hz, he⟩ := exists_integral_linearChar_apply_sub hp hε θ hx
    refine ⟨z, hz, ?_⟩
    rw [← hθ]; simpa using he
  -- conclude: `χ ∈ ZIrr A = span ℤ (Irr A) ≤ M`.
  rw [ZIrr_eq_span] at hχ
  exact Submodule.span_le.mpr hsub hχ

/-- **Peterfalvi (1.10.a)** (`G`-form, commuting elements): for a virtual character `ψ ∈ ℤ[Irr G]` of
any finite group `G`, an order-dividing-`p` element `x` (`x^p = 1`) and any `y` **commuting** with
`x`, `ψ(xy) - ψ(y)` is `(1 - ε)` times an algebraic integer.

Reduce to the abelian subgroup `A = ⟨x, y⟩` (commutative since `x, y` commute): `Res_A ψ ∈ ℤ[Irr A]`
(`restrict_mem_ZIrr`), and `exists_integral_zirr_apply_sub` applies, with `(Res_A ψ)(a) = ψ(a)`. -/
theorem exists_integral_apply_sub_of_commute {p : ℕ} (hp : 0 < p) {ε : ℂ}
    (hε : IsPrimitiveRoot ε p) {G : Type*} [Group G] [Finite G]
    {ψ : ClassFunction G ℂ} (hψ : ψ ∈ ZIrr G) {x y : G} (hx : x ^ p = 1) (hxy : Commute x y) :
    ∃ z : ℂ, IsIntegral ℤ z ∧ ψ (x * y) - ψ y = (1 - ε) * z := by
  set A := Subgroup.closure ({x, y} : Set G) with hA
  haveI : IsMulCommutative ↥A := by
    refine Subgroup.isMulCommutative_closure (fun a ha b hb => ?_)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hxy
    · exact hxy.symm
    · exact Commute.refl _
  have hxA : x ∈ A := Subgroup.subset_closure (by simp)
  have hyA : y ∈ A := Subgroup.subset_closure (by simp)
  have hres : ClassFunction.restrict A ψ ∈ ZIrr ↥A := ClassFunction.restrict_mem_ZIrr A hψ
  have hx' : (⟨x, hxA⟩ : ↥A) ^ p = 1 := by
    apply Subtype.ext; push_cast; exact hx
  obtain ⟨z, hz, he⟩ := exists_integral_zirr_apply_sub hp hε hres
    (x := ⟨x, hxA⟩) (y := ⟨y, hyA⟩) hx'
  refine ⟨z, hz, ?_⟩
  rwa [ClassFunction.restrict_apply, ClassFunction.restrict_apply,
    show ((⟨x, hxA⟩ * ⟨y, hyA⟩ : ↥A) : G) = x * y from rfl,
    show ((⟨y, hyA⟩ : ↥A) : G) = y from rfl] at he

end OddOrder.RepresentationTheory
