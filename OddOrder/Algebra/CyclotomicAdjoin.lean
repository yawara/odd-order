/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import OddOrder.Algebra.AdicCompletePi

/-!
# The cyclotomic extension `A[ζ_n] = A[X]/Φ_n`

The coefficient ring of the modular character theory has to satisfy two competing demands
(issue 9506): its residue field must be algebraically closed of characteristic `p` — which
`𝕎(𝔽̄_p)` provides — and its fraction field must contain `ζ_{exp G}`, which `𝕎(𝔽̄_p)` does *not*
when `p` divides `exp G`.  The fix is the ramified extension `A[ζ_{p^a}]`, presented here as
`A[X]/Φ_{p^a}`.

What this file supplies is the *module-theoretic* half, which is all that the completeness argument
needs: `Φ_n` is monic, so `A[X]/Φ_n` is free of rank `deg Φ_n` over `A`, and a finite free module
over an `I`-adically complete ring is `I`-adically complete (`isAdicComplete_of_basis`).

Combined with `isAdicComplete_of_le_of_pow_le` — and with `𝔪_B^{φ(p^a)} ⊆ 𝔪_A·B`, which comes from
`Φ_{p^a} ≡ (X-1)^{φ(p^a)}` in characteristic `p` — this gives `IsAdicComplete (maximalIdeal B) B`,
the hypothesis that the block idempotents are lifted along.

## Main results

* `OddOrder.Algebra.cyclotomicPowerBasis` — the power basis `1, ζ, …, ζ^{deg Φ_n - 1}`
* `OddOrder.Algebra.isAdicComplete_cyclotomicAdjoin` — `A[ζ_n]` inherits `I`-adic completeness
* `OddOrder.Algebra.cyclotomic_prime_pow_charP` — `Φ_{p^k} = (X-1)^{p^k - p^{k-1}}` in
  characteristic `p` (the exponent is `φ(p^k)`)
* `OddOrder.Algebra.sub_one_pow_mem_map_maximalIdeal` — the totally ramified estimate
  `(ζ - 1)^{φ(p^k)} ∈ 𝔪_A·B`
* `OddOrder.Algebra.cyclotomicToResidueField` — the reduction `B → k` at `ζ ↦ 1`, and its
  surjectivity
* `OddOrder.Algebra.Ideal.sup_pow_le` — `(I ⊔ J)^n ≤ I ⊔ J^n`
* `OddOrder.Algebra.ker_cyclotomicToResidueField_le` /
  `OddOrder.Algebra.ker_cyclotomicToResidueField_isMaximal` — the kernel is maximal and sits
  inside `𝔪_A·B ⊔ ⟨ζ - 1⟩`
* `OddOrder.Algebra.isAdicComplete_ker_cyclotomicToResidueField` /
  `OddOrder.Algebra.isLocalRing_cyclotomicAdjoin` — **`B` is a complete local ring**
* `OddOrder.Algebra.residueFieldEquivCyclotomicAdjoin` /
  `OddOrder.Algebra.maximalIdeal_cyclotomicAdjoin` /
  `OddOrder.Algebra.residueFieldEquiv` — its residue field is that of `A`
-/

namespace OddOrder.Algebra

open Polynomial

variable (n : ℕ) (A : Type*) [CommRing A]

/-- **The power basis `1, ζ, …, ζ^{deg Φ_n - 1}` of `A[X]/Φ_n`.**  The cyclotomic polynomial is
monic, so the quotient is free on the powers of the root. -/
noncomputable def cyclotomicPowerBasis : PowerBasis A (AdjoinRoot (cyclotomic n A)) :=
  AdjoinRoot.powerBasis' (cyclotomic.monic n A)

instance : Module.Free A (AdjoinRoot (cyclotomic n A)) :=
  Module.Free.of_basis (cyclotomicPowerBasis n A).basis

instance : Module.Finite A (AdjoinRoot (cyclotomic n A)) :=
  Module.Finite.of_basis (cyclotomicPowerBasis n A).basis

/-- **`A[ζ_n]` is `I`-adically complete when `A` is** — it is a finite free `A`-module. -/
theorem isAdicComplete_cyclotomicAdjoin (I : Ideal A) [IsAdicComplete I A] :
    IsAdicComplete I (AdjoinRoot (cyclotomic n A)) :=
  isAdicComplete_of_basis I (Finite.of_fintype _) (cyclotomicPowerBasis n A).basis

/-- **`Φ_{p^k} = (X - 1)^{φ(p^k)}` in characteristic `p`.**  Specialisation of
`Polynomial.cyclotomic_mul_prime_pow_eq` at `m = 1`, where `Φ_1 = X - 1`.

This is what makes `A[ζ_{p^k}] ⧸ 𝔪_A` a local Artinian ring — hence `A[ζ_{p^k}]` local — and
`𝔪_B^{φ(p^k)} ⊆ 𝔪_A·B`, the totally ramified estimate that `isAdicComplete_of_le_of_pow_le`
consumes. -/
theorem cyclotomic_prime_pow_charP (R : Type*) [CommRing R] {q k : ℕ} [Fact (Nat.Prime q)]
    [CharP R q] (hk : 0 < k) :
    cyclotomic (q ^ k) R = (X - 1) ^ (q ^ k - q ^ (k - 1)) := by
  have h := cyclotomic_mul_prime_pow_eq R (p := q) (m := 1)
    (by simpa [Nat.dvd_one] using (Fact.out : Nat.Prime q).ne_one) hk
  rwa [mul_one, cyclotomic_one] at h

/-! ### The totally ramified estimate `(ζ - 1)^{φ} ∈ 𝔪_A·B` -/

open IsLocalRing in
/-- **`(ζ - 1)^{q^k - q^{k-1}} ∈ 𝔪_A·B`.**  In characteristic `q` the cyclotomic polynomial is
`(X - 1)^{φ(q^k)}` (`cyclotomic_prime_pow_charP`), so the difference
`(X - 1)^{φ(q^k)} - Φ_{q^k}` has all its coefficients in `𝔪_A`; evaluating at the root and using
`Φ_{q^k}(ζ) = 0` leaves `(ζ - 1)^{φ(q^k)}` inside `𝔪_A·B`.

This is the totally ramified estimate: no isomorphism `B ⧸ 𝔪_A·B ≅ k[X]/((X-1)^φ)` is needed. -/
theorem sub_one_pow_mem_map_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A]
    {q k : ℕ} [Fact (Nat.Prime q)] [CharP (ResidueField A) q] (hk : 0 < k) :
    (AdjoinRoot.root (cyclotomic (q ^ k) A) - 1) ^ (q ^ k - q ^ (k - 1))
      ∈ Ideal.map (algebraMap A (AdjoinRoot (cyclotomic (q ^ k) A))) (maximalIdeal A) := by
  classical
  set P : A[X] := (X - 1) ^ (q ^ k - q ^ (k - 1)) - cyclotomic (q ^ k) A with hP
  have hcoeff : ∀ i, P.coeff i ∈ maximalIdeal A := by
    intro i
    have hmap : P.map (residue A) = 0 := by
      rw [hP, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_one, map_cyclotomic, cyclotomic_prime_pow_charP (ResidueField A) hk,
        sub_self]
    have hc := congrArg (fun w : (ResidueField A)[X] => w.coeff i) hmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
    rwa [← RingHom.mem_ker, ker_residue] at hc
  have hroot : (AdjoinRoot.root (cyclotomic (q ^ k) A) - 1) ^ (q ^ k - q ^ (k - 1))
      = Polynomial.aeval (AdjoinRoot.root (cyclotomic (q ^ k) A)) P := by
    rw [hP, map_sub, map_pow, map_sub, Polynomial.aeval_X, map_one, AdjoinRoot.aeval_eq,
      AdjoinRoot.mk_self, sub_zero]
  rw [hroot, Polynomial.aeval_eq_sum_range]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hcoeff i))

/-! ### An ideal-theoretic step -/

/-- **`(I ⊔ J)^n ≤ I ⊔ J^n`.**  In the expansion of the `n`-th power every term except `J^n`
carries a factor from `I`.  Used with `J = ⟨ζ - 1⟩` and `J^{φ} ≤ I = 𝔪_A·B` to see that the
maximal ideal of `B` is `𝔪_A·B`-adically cofinal. -/
theorem Ideal.sup_pow_le {R : Type*} [CommRing R] (I J : Ideal R) :
    ∀ n : ℕ, (I ⊔ J) ^ n ≤ I ⊔ J ^ n
  | 0 => by simp
  | (n + 1) => by
    refine le_trans (le_of_eq (pow_succ _ _)) ?_
    refine le_trans (Ideal.mul_mono_left (Ideal.sup_pow_le I J n)) ?_
    rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact le_sup_of_le_left Ideal.mul_le_left
    · exact le_sup_of_le_left Ideal.mul_le_left
    · exact le_sup_of_le_left Ideal.mul_le_right
    · exact le_sup_of_le_right (le_of_eq (pow_succ J n).symm)

/-! ### The reduction `B → k` at `ζ ↦ 1` -/

open IsLocalRing in
/-- **The ring map `B → k` sending `ζ` to `1`.**  It is well defined because
`Φ_{q^k}(1) = q` (`Polynomial.eval_one_cyclotomic_prime_pow`), which is `0` in the residue field.

Its kernel is the maximal ideal of `B`; that is what makes `B` local with residue field `k`. -/
noncomputable def cyclotomicToResidueField {A : Type*} [CommRing A] [IsLocalRing A]
    {q k : ℕ} [Fact (Nat.Prime q)] [CharP (ResidueField A) q] (hk : 0 < k) :
    AdjoinRoot (cyclotomic (q ^ k) A) →+* ResidueField A :=
  AdjoinRoot.lift (residue A) 1 (by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [Polynomial.eval₂_eq_eval_map, map_cyclotomic, hj,
      eval_one_cyclotomic_prime_pow (R := ResidueField A) j]
    exact CharP.cast_eq_zero _ q)

open IsLocalRing in
@[simp]
theorem cyclotomicToResidueField_of {A : Type*} [CommRing A] [IsLocalRing A]
    {q k : ℕ} [Fact (Nat.Prime q)] [CharP (ResidueField A) q] (hk : 0 < k) (a : A) :
    cyclotomicToResidueField hk (AdjoinRoot.of (cyclotomic (q ^ k) A) a) = residue A a :=
  AdjoinRoot.lift_of _

open IsLocalRing in
@[simp]
theorem cyclotomicToResidueField_root {A : Type*} [CommRing A] [IsLocalRing A]
    {q k : ℕ} [Fact (Nat.Prime q)] [CharP (ResidueField A) q] (hk : 0 < k) :
    cyclotomicToResidueField hk (AdjoinRoot.root (cyclotomic (q ^ k) A)) = 1 :=
  AdjoinRoot.lift_root _

open IsLocalRing in
/-- **`B → k` is onto** — it already is on the constants. -/
theorem cyclotomicToResidueField_surjective {A : Type*} [CommRing A] [IsLocalRing A]
    {q k : ℕ} [Fact (Nat.Prime q)] [CharP (ResidueField A) q] (hk : 0 < k) :
    Function.Surjective (cyclotomicToResidueField (A := A) (q := q) (k := k) hk) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨AdjoinRoot.of _ a, cyclotomicToResidueField_of hk a⟩

open IsLocalRing in
/-- **`ker (B → k) ≤ 𝔪_A·B ⊔ ⟨ζ - 1⟩`.**  Write a representative as `P = C (P(1)) + (X - 1)·Q`
(`Polynomial.dvd_iff_isRoot`); the constant `P(1)` lies in `𝔪_A` exactly because the image
vanishes. -/
theorem ker_cyclotomicToResidueField_le {A : Type*} [CommRing A] [IsLocalRing A]
    {q k : ℕ} [Fact (Nat.Prime q)] [CharP (ResidueField A) q] (hk : 0 < k) :
    RingHom.ker (cyclotomicToResidueField (A := A) (q := q) (k := k) hk)
      ≤ Ideal.map (algebraMap A (AdjoinRoot (cyclotomic (q ^ k) A))) (maximalIdeal A)
        ⊔ Ideal.span {AdjoinRoot.root (cyclotomic (q ^ k) A) - 1} := by
  intro x hx
  obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [RingHom.mem_ker, cyclotomicToResidueField, AdjoinRoot.lift_mk] at hx
  have hconst : P.eval 1 ∈ maximalIdeal A := by
    rw [← ker_residue, RingHom.mem_ker]
    have h1 : (1 : ResidueField A) = residue A 1 := (map_one _).symm
    rw [h1, Polynomial.eval₂_at_apply] at hx
    -- `hx : residue A (P.eval 1) = 0`
    simpa using hx
  obtain ⟨Q, hQ⟩ : (Polynomial.X - Polynomial.C (1 : A)) ∣ P - Polynomial.C (P.eval 1) := by
    rw [Polynomial.dvd_iff_isRoot]
    simp [Polynomial.IsRoot]
  have hsplit : P = Polynomial.C (P.eval 1) + (Polynomial.X - Polynomial.C (1 : A)) * Q := by
    rw [← hQ]; ring
  rw [hsplit, map_add, map_mul]
  refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
  · exact Ideal.mem_map_of_mem _ hconst
  · refine Ideal.mul_mem_right _ _ (Ideal.subset_span ?_)
    simp [Set.mem_singleton_iff, map_sub, AdjoinRoot.mk_X]

open IsLocalRing in
/-- **`ker (B → k)` is a maximal ideal** — the quotient is the field `k`. -/
theorem ker_cyclotomicToResidueField_isMaximal {A : Type*} [CommRing A] [IsLocalRing A]
    {q k : ℕ} [Fact (Nat.Prime q)] [CharP (ResidueField A) q] (hk : 0 < k) :
    (RingHom.ker (cyclotomicToResidueField (A := A) (q := q) (k := k) hk)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (cyclotomicToResidueField_surjective hk)

/-! ### `B` is local, and `𝔪_B`-adically complete -/

open IsLocalRing in
/-- **`B` is `ker(B → k)`-adically complete.**  The kernel `N` satisfies `𝔪_A·B ≤ N` and
`N^{φ(q^k)} ≤ 𝔪_A·B` (段 302/304/305), so the two filtrations are cofinal and
`isAdicComplete_of_le_of_pow_le` transfers the completeness that `B` has as a finite free
`A`-module. -/
theorem isAdicComplete_ker_cyclotomicToResidueField {A : Type*} [CommRing A] [IsLocalRing A]
    {q k : ℕ} [Fact (Nat.Prime q)] [CharP (ResidueField A) q]
    [IsAdicComplete (maximalIdeal A) A] (hk : 0 < k) :
    IsAdicComplete (RingHom.ker (cyclotomicToResidueField (A := A) (q := q) (k := k) hk))
      (AdjoinRoot (cyclotomic (q ^ k) A)) := by
  set B := AdjoinRoot (cyclotomic (q ^ k) A)
  set I : Ideal B := Ideal.map (algebraMap A B) (maximalIdeal A) with hI
  set J : Ideal B := Ideal.span {AdjoinRoot.root (cyclotomic (q ^ k) A) - 1} with hJ
  set N := RingHom.ker (cyclotomicToResidueField (A := A) (q := q) (k := k) hk) with hN
  have : IsAdicComplete I B :=
    (IsAdicComplete.map_algebraMap_iff (I := maximalIdeal A) (M := B)).mpr
      (isAdicComplete_cyclotomicAdjoin (q ^ k) A (maximalIdeal A))
  have hφ : q ^ k - q ^ (k - 1) ≠ 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have hlt : q ^ j < q ^ j.succ :=
      Nat.pow_lt_pow_right (Fact.out : Nat.Prime q).one_lt (Nat.lt_succ_self j)
    simp only [Nat.succ_sub_one]
    omega
  have hIN : I ≤ N := by
    rw [hI, hN, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, AdjoinRoot.algebraMap_eq,
      cyclotomicToResidueField_of hk a, ← RingHom.mem_ker, ker_residue]
    exact ha
  have hJφ : J ^ (q ^ k - q ^ (k - 1)) ≤ I := by
    rw [hJ, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact sub_one_pow_mem_map_maximalIdeal hk
  have hNφ : N ^ (q ^ k - q ^ (k - 1)) ≤ I :=
    le_trans (pow_le_pow_left' (ker_cyclotomicToResidueField_le hk) _)
      (le_trans (Ideal.sup_pow_le I J _) (sup_le le_rfl hJφ))
  exact isAdicComplete_of_le_of_pow_le hφ hNφ hIN

open IsLocalRing in
/-- **`A[ζ_{q^k}]` is a local ring** with maximal ideal `ker(B → k)` — the adic completeness of
`isAdicComplete_ker_cyclotomicToResidueField` at a *maximal* ideal forces locality. -/
theorem isLocalRing_cyclotomicAdjoin {A : Type*} [CommRing A] [IsLocalRing A]
    {q k : ℕ} [Fact (Nat.Prime q)] [CharP (ResidueField A) q]
    [IsAdicComplete (maximalIdeal A) A] (hk : 0 < k) :
    IsLocalRing (AdjoinRoot (cyclotomic (q ^ k) A)) := by
  have := ker_cyclotomicToResidueField_isMaximal (A := A) (q := q) (k := k) hk
  have := isAdicComplete_ker_cyclotomicToResidueField (A := A) (q := q) (k := k) hk
  exact isLocalRing_of_isAdicComplete_maximal
    (RingHom.ker (cyclotomicToResidueField (A := A) (q := q) (k := k) hk))

/-! ### The residue field of `B` is `k` -/

open IsLocalRing in
/-- **`B ⧸ ker(B → k) ≅ k`.**  The map is onto (`cyclotomicToResidueField_surjective`), so the
first isomorphism theorem applies.  Together with `maximalIdeal_cyclotomicAdjoin` this identifies
the residue field of `B` with that of `A` — in particular the extension does not enlarge it, so
algebraic closedness is inherited. -/
noncomputable def residueFieldEquivCyclotomicAdjoin {A : Type*} [CommRing A] [IsLocalRing A]
    {q k : ℕ} [Fact (Nat.Prime q)] [CharP (ResidueField A) q] (hk : 0 < k) :
    (AdjoinRoot (cyclotomic (q ^ k) A) ⧸
        RingHom.ker (cyclotomicToResidueField (A := A) (q := q) (k := k) hk))
      ≃+* ResidueField A :=
  RingHom.quotientKerEquivOfSurjective (cyclotomicToResidueField_surjective hk)

open IsLocalRing in
/-- **The maximal ideal of `B` is `ker(B → k)`** — a local ring has only one maximal ideal. -/
theorem maximalIdeal_cyclotomicAdjoin {A : Type*} [CommRing A] [IsLocalRing A]
    {q k : ℕ} [Fact (Nat.Prime q)] [CharP (ResidueField A) q]
    [IsAdicComplete (maximalIdeal A) A] (hk : 0 < k) :
    letI := isLocalRing_cyclotomicAdjoin (A := A) (q := q) (k := k) hk
    maximalIdeal (AdjoinRoot (cyclotomic (q ^ k) A))
      = RingHom.ker (cyclotomicToResidueField (A := A) (q := q) (k := k) hk) := by
  let := isLocalRing_cyclotomicAdjoin (A := A) (q := q) (k := k) hk
  exact (IsLocalRing.eq_maximalIdeal
    (ker_cyclotomicToResidueField_isMaximal (A := A) (q := q) (k := k) hk)).symm

open IsLocalRing in
/-- **`ResidueField B ≃+* ResidueField A`** — the totally ramified extension does not enlarge the
residue field, so `IsAlgClosed` and `CharP … q` transfer to `B`. -/
noncomputable def residueFieldEquiv {A : Type*} [CommRing A] [IsLocalRing A]
    {q k : ℕ} [Fact (Nat.Prime q)] [CharP (ResidueField A) q]
    [IsAdicComplete (maximalIdeal A) A] (hk : 0 < k) :
    letI := isLocalRing_cyclotomicAdjoin (A := A) (q := q) (k := k) hk
    ResidueField (AdjoinRoot (cyclotomic (q ^ k) A)) ≃+* ResidueField A :=
  letI := isLocalRing_cyclotomicAdjoin (A := A) (q := q) (k := k) hk
  (Ideal.quotEquivOfEq (maximalIdeal_cyclotomicAdjoin (A := A) (q := q) (k := k) hk)).trans
    (residueFieldEquivCyclotomicAdjoin hk)

end OddOrder.Algebra
