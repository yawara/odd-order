/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.AugmentationIdeal
import OddOrder.Algebra.DefectNumber
import OddOrder.Algebra.RelativeTraceCharacter
import OddOrder.GroupTheory.RepresentationTheory.Modular.PModularSystem

/-!
# The height of an ordinary character is non-negative

**Navarro (3.24)** measures the degree of `χ ∈ Irr(B)` against the defect of `B`: writing
`ν` for the `p`-adic valuation and `a = ν(|G|)`,

`ν(χ(1)) = a - d(B) + ht(χ)`

with `ht(χ) ≥ 0`.  The inequality `ν(χ(1)) ≥ a - d(B)` — which is what makes the *height* a
natural number — is proved here, and it needs none of the apparatus of Chapter 3 (no valuation
theory, no generalized characters, no `~` functions).  It is the following two-line argument:

* a defect group `D` of the block idempotent `f_B` writes it as a relative trace,
  `f_B = Tr^G_D(c)`;
* the character of a representation is a class function on `𝒪[G]`, so it turns that sum of
  `[G : D]` conjugates into `[G : D]` times one term;
* `f_B` acts as the identity in a representation belonging to `B`, so the left-hand side is
  `χ(1)`.

Hence `χ(1) = [G : D] · χ(c)` with `χ(c) ∈ 𝒪`, i.e. `[G : D] ∣ χ(1)`.  Since `|D| = p^{d(B)}`,
the `p`-part of `[G : D]` is `p^{a - d(B)}`.

The two ingredients are `OddOrder.GroupAlgebra.index_dvd_finrank` (pure algebra, any commutative
base ring) and `OddOrder.RepresentationTheory.Modular.pow_dvd_of_natCast_pow_dvd` (which reads
the divisibility back in `ℕ`, using only that `𝒪` is local of characteristic `0` with residue
characteristic `p`).

## Main results

* `OddOrder.RepresentationTheory.Modular.pow_dvd_finrank_of_mem_relTraceIdeal` — for any subgroup
  `D` with `f ∈ 𝒪[G]^G_D`, the `p`-part of `[G : D]` divides the degree
* `OddOrder.RepresentationTheory.Modular.pow_defect_dvd_finrank` — the height inequality
  `ν(χ(1)) ≥ ν(|G|) - d`, with `d` the defect of `f`
* `OddOrder.RepresentationTheory.Modular.defect_eq_factorization_of_apply_eq_one` — full defect:
  a one-dimensional representation in which `f` acts as the identity forces `d = ν(|G|)`
* `OddOrder.RepresentationTheory.Modular.defect_eq_factorization_of_residue_augmentation_ne_zero`
  — the form the principal block uses
-/

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra IsLocalRing

open scoped OddOrder.Conjugation

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
variable {G : Type*} [Group G] [Finite G]
variable {L : Type*} [AddCommGroup L] [Module 𝒪 L] [Module.Free 𝒪 L] [Module.Finite 𝒪 L]

/-- **The `p`-part of `[G : D]` divides the degree**, for any subgroup `D` such that the relative
trace ideal `𝒪[G]^G_D` contains an element acting as the identity.

With `D` a defect group of a block idempotent `f_B` and `ψ` a representation in `B` this is the
height inequality; see `pow_defect_dvd_finrank`. -/
theorem pow_dvd_finrank_of_mem_relTraceIdeal (hp : p.Prime)
    (ψ : MonoidAlgebra 𝒪 G →ₐ[𝒪] Module.End 𝒪 L) {D : Subgroup G} {f : MonoidAlgebra 𝒪 G}
    (hf : f ∈ GAlgebra.relTraceIdeal D ⊤) (hψ : ψ f = 1) :
    p ^ ((Nat.card G).factorization p - (Nat.card ↥D).factorization p)
      ∣ Module.finrank 𝒪 L := by
  have : Fact p.Prime := ⟨hp⟩
  -- `[G : D]` carries the `p`-part `p ^ (a - d)` by Lagrange
  have hcard : Nat.card ↥D * D.index = Nat.card G := D.card_mul_index
  have hDne : Nat.card ↥D ≠ 0 := Nat.card_pos.ne'
  have hine : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hfac : (Nat.card G).factorization p
      = (Nat.card ↥D).factorization p + (D.index).factorization p := by
    rw [← hcard, Nat.factorization_mul hDne hine]
    rfl
  have hdvdIndex : p ^ ((Nat.card G).factorization p - (Nat.card ↥D).factorization p)
      ∣ D.index := by
    rw [hfac, Nat.add_sub_cancel_left]
    exact Nat.ordProj_dvd _ _
  -- push the divisibility through `𝒪`
  have h1 : ((p ^ ((Nat.card G).factorization p - (Nat.card ↥D).factorization p) : ℕ) : 𝒪)
      ∣ ((D.index : ℕ) : 𝒪) := Nat.cast_dvd_cast hdvdIndex
  have h2 : ((D.index : ℕ) : 𝒪) ∣ ((Module.finrank 𝒪 L : ℕ) : 𝒪) :=
    GroupAlgebra.index_dvd_finrank ψ hf hψ
  exact pow_dvd_of_natCast_pow_dvd hp (h1.trans h2)

/-- **The height inequality** `ν(χ(1)) ≥ ν(|G|) - d`: the degree of a representation in which the
`G`-fixed element `f` acts as the identity is divisible by `p ^ (ν(|G|) - d)`, where `d` is the
defect of `f`.

For `f = f_B` the block idempotent of `B` and `χ ∈ Irr(B)` this says that the height
`ν(χ(1)) - ν(|G|) + d(B)` is a non-negative integer, which is the numerical content of
Navarro (3.24). -/
theorem pow_defect_dvd_finrank (hp : p.Prime)
    (ψ : MonoidAlgebra 𝒪 G →ₐ[𝒪] Module.End 𝒪 L) {f : MonoidAlgebra 𝒪 G}
    (hfix : ∀ g : G, g • f = f) (hψ : ψ f = 1) :
    p ^ ((Nat.card G).factorization p - GAlgebra.defect p hfix) ∣ Module.finrank 𝒪 L :=
  pow_dvd_finrank_of_mem_relTraceIdeal hp ψ (GAlgebra.isDefectGroup_defectGroup hfix).mem hψ

/-! ### Full defect

A `G`-fixed element carrying a *one-dimensional* representation — for the principal block
idempotent, the augmentation — has a defect group of index prime to `p`, hence a Sylow
`p`-subgroup.  This is `d(B_0) = ν(|G|)`: the principal block has full defect, so that `1_G`,
of degree `1`, has height zero. -/

/-- **A natural number whose image in `𝒪` is a unit is prime to `p`.** -/
theorem not_dvd_of_isUnit_natCast {n : ℕ} (h : IsUnit ((n : ℕ) : 𝒪)) : ¬ p ∣ n := by
  rintro ⟨m, rfl⟩
  have hmem : ((p * m : ℕ) : 𝒪) ∈ maximalIdeal 𝒪 := by
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ natCast_prime_mem_maximalIdeal
  exact ((mem_maximalIdeal _).mp hmem) h

/-- **Full defect.**  A `G`-fixed element sent to `1` by an algebra map `𝒪[G] →ₐ 𝒪` — a
one-dimensional representation in which it acts as the identity — has a defect group of index
prime to `p`, so its defect is `ν(|G|)`.

Applied to the principal block idempotent and the augmentation, this is `d(B_0) = ν(|G|)`: the
defect group of the principal block is a Sylow `p`-subgroup.  Together with
`pow_defect_dvd_finrank` it says that `1_G` has height zero in `B_0`. -/
theorem defect_eq_factorization_of_apply_eq_one (ψ : MonoidAlgebra 𝒪 G →ₐ[𝒪] 𝒪)
    {f : MonoidAlgebra 𝒪 G} (hfix : ∀ g : G, g • f = f) (hψ : ψ f = 1) :
    GAlgebra.defect p hfix = (Nat.card G).factorization p := by
  have hidx : ¬ p ∣ (GAlgebra.defectGroup hfix).index :=
    not_dvd_of_isUnit_natCast (GroupAlgebra.isUnit_index_of_mem_relTraceIdeal ψ
      (GAlgebra.isDefectGroup_defectGroup hfix).mem hψ)
  have hcard : Nat.card ↥(GAlgebra.defectGroup hfix) * (GAlgebra.defectGroup hfix).index
      = Nat.card G := (GAlgebra.defectGroup hfix).card_mul_index
  have hDne : Nat.card ↥(GAlgebra.defectGroup hfix) ≠ 0 := Nat.card_pos.ne'
  have hine : (GAlgebra.defectGroup hfix).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hfac : (Nat.card G).factorization p
      = (Nat.card ↥(GAlgebra.defectGroup hfix)).factorization p := by
    rw [← hcard, Nat.factorization_mul hDne hine]
    simp [Nat.factorization_eq_zero_of_not_dvd hidx]
  exact hfac.symm

/-- In a local ring an idempotent with nonzero residue is `1`: it is a unit, and `a(a-1) = 0`. -/
theorem eq_one_of_isIdempotentElem_of_residue_ne_zero {a : 𝒪} (ha : IsIdempotentElem a)
    (h : residue 𝒪 a ≠ 0) : a = 1 := by
  have hu : IsUnit a := isUnit_iff_residue_ne_zero.mpr h
  have hz : a * (a - 1) = 0 := by rw [mul_sub, mul_one, ha.eq, sub_self]
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp hz)

/-- **A `G`-fixed idempotent whose augmentation survives reduction has full defect.**

This is `d(B_0) = ν(|G|)`: the block idempotent `f_{B_0}` of the principal block is `G`-fixed
(being central) and idempotent, and its augmentation reduces to `λ_{B_0}(e_{B_0}) = 1 ≠ 0`, so
its defect group is a Sylow `p`-subgroup.  Combined with `pow_defect_dvd_finrank` this says that
the trivial character, of degree `1`, has height zero. -/
theorem defect_eq_factorization_of_residue_augmentation_ne_zero {f : MonoidAlgebra 𝒪 G}
    (hfix : ∀ g : G, g • f = f) (hf : IsIdempotentElem f)
    (h : residue 𝒪 (OddOrder.Algebra.augmentation 𝒪 G f) ≠ 0) :
    GAlgebra.defect p hfix = (Nat.card G).factorization p :=
  defect_eq_factorization_of_apply_eq_one (OddOrder.Algebra.augmentation 𝒪 G) hfix
    (eq_one_of_isIdempotentElem_of_residue_ne_zero (hf.map (OddOrder.Algebra.augmentation 𝒪 G)) h)

end OddOrder.RepresentationTheory.Modular

