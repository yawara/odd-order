/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Module.NatInt
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import OddOrder.GroupTheory.RepresentationTheory.RowOrthogonality

/-!
# Fourier coefficients of virtual characters

For a finite group `G` with `|G|` invertible in `ℂ`, the irreducible characters are
orthonormal (`characterTableRowOrthogonality`).  A virtual character `φ ∈ ZIrr G` is a
finite `ℤ`-linear combination of irreducibles, so its "Fourier coefficient" at an
irreducible `χ` is the inner product `⟨φ, χ⟩`, and this coefficient is an **integer**.

This file develops that coefficient API, the prerequisite (layer 2) for the finite
combinatorial core of Peterfalvi §3 (1.4) (`isometry_difference_pair_structure`): the images
`τ (χ_i - χ_0) ∈ ZIrr G` have integer Fourier coefficients, and the norm / mutual inner
products are sums of products of those integers (Parseval), which the combinatorial argument
then constrains.

No spanning statement (`#Irr = #conj-classes`) is needed — only that each `φ ∈ ZIrr G`
already lies in the `ℤ`-span of the orthonormal irreducibles.

Reference issue: `issues/0025-peterfalvi-isometry-difference-core.md` (layer 2).
-/

namespace OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

open scoped Classical in
/-- Orthonormality of irreducible characters in inner-product form:
`⟨χ, ψ⟩ = δ_{χ,ψ}`.  This is `characterTableRowOrthogonality` restated through the
`ClassFunction.inner` pairing. -/
theorem irreducibleCharacter_inner_eq_ite (χ ψ : IrreducibleCharacter G) :
    ClassFunction.inner (χ : ClassFunction G ℂ) (ψ : ClassFunction G ℂ) =
      if χ = ψ then 1 else 0 := by
  by_cases h : χ = ψ
  · subst h
    rw [if_pos rfl, ← characterTableRowPairing_eq_inner]
    exact characterTableRowOrthogonality.1 χ
  · rw [if_neg h, ← characterTableRowPairing_eq_inner]
    exact characterTableRowOrthogonality.2 h

/-- The Fourier coefficient `⟨φ, χ⟩` of a virtual character `φ ∈ ZIrr G` at an irreducible
character `χ` is an integer. -/
theorem mem_ZIrr_inner_int (χ : IrreducibleCharacter G) {φ : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) :
    ∃ m : ℤ, ClassFunction.inner φ (χ : ClassFunction G ℂ) = (m : ℂ) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      have heq := irreducibleCharacter_inner_eq_ite (⟨x, hx⟩ : IrreducibleCharacter G) χ
      rw [show ((⟨x, hx⟩ : IrreducibleCharacter G) : ClassFunction G ℂ) = x from rfl] at heq
      by_cases h : (⟨x, hx⟩ : IrreducibleCharacter G) = χ
      · refine ⟨1, ?_⟩; rw [heq, if_pos h]; norm_num
      · refine ⟨0, ?_⟩; rw [heq, if_neg h]; norm_num
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨mx, hmx⟩ := ihx
      obtain ⟨my, hmy⟩ := ihy
      refine ⟨mx + my, ?_⟩
      rw [ClassFunction.inner_add_left, hmx, hmy]
      push_cast; ring
  | smul a x _ ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨a * m, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, hm]
      push_cast; ring

omit [Finite G] in
/-- Left-linearity of `ClassFunction.inner` over a finite sum. -/
theorem inner_sum_left {ι : Type*} (s : Finset ι) (f : ι → ClassFunction G ℂ)
    (ψ : ClassFunction G ℂ) :
    ClassFunction.inner (∑ i ∈ s, f i) ψ =
      ∑ i ∈ s, ClassFunction.inner (f i) ψ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.inner_add_left, ih]

open scoped Classical in
/-- Orthonormality at the level of irreducible class functions (not the subtype index):
for `a, b` in `irreducibleCharacters G`, `⟨a, b⟩ = δ_{a,b}`. -/
theorem irr_cf_inner {a b : ClassFunction G ℂ}
    (ha : a ∈ irreducibleCharacters G) (hb : b ∈ irreducibleCharacters G) :
    ClassFunction.inner a b = if a = b then (1 : ℂ) else 0 := by
  have key := irreducibleCharacter_inner_eq_ite
    (⟨a, ha⟩ : IrreducibleCharacter G) (⟨b, hb⟩ : IrreducibleCharacter G)
  simp only [IrreducibleCharacter.coe_mk] at key
  rw [key]
  by_cases h : a = b
  · rw [if_pos h, if_pos (Subtype.ext h)]
  · rw [if_neg h, if_neg fun he => h (Subtype.ext_iff.mp he)]

omit [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- A virtual character `φ ∈ ZIrr G` is a finite `ℂ`-linear combination of irreducible
characters with integer coefficients (recorded as a `Finsupp` supported on `Irr(G)`). -/
theorem mem_ZIrr_repr {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) :
    ∃ c : ClassFunction G ℂ →₀ ℤ, (↑c.support ⊆ irreducibleCharacters G) ∧
      φ = ∑ a ∈ c.support, (c a : ℂ) • a := by
  rw [ZIrr_eq_span] at hφ
  obtain ⟨c, hsupp, hsum⟩ := Submodule.mem_span_set.mp hφ
  refine ⟨c, hsupp, ?_⟩
  rw [← hsum, Finsupp.sum]
  exact Finset.sum_congr rfl fun a _ => (Int.cast_smul_eq_zsmul ℂ (c a) a).symm

open scoped Classical in
/-- The Fourier coefficient of an integer span representation is recovered by the inner
product: `⟨∑ c_a • a, χ⟩ = c_χ`. -/
theorem inner_eq_coeff_of_repr (χ : IrreducibleCharacter G)
    {c : ClassFunction G ℂ →₀ ℤ} (hsupp : ↑c.support ⊆ irreducibleCharacters G) :
    ClassFunction.inner (∑ a ∈ c.support, (c a : ℂ) • a) (χ : ClassFunction G ℂ) =
      (c (χ : ClassFunction G ℂ) : ℂ) := by
  rw [inner_sum_left]
  have hχ : (χ : ClassFunction G ℂ) ∈ irreducibleCharacters G := χ.mem_irreducibleCharacters
  have step : (∑ a ∈ c.support, ClassFunction.inner ((c a : ℂ) • a) (χ : ClassFunction G ℂ))
      = ∑ a ∈ c.support, (if a = (χ : ClassFunction G ℂ) then (c a : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [ClassFunction.inner_smul_left, irr_cf_inner (hsupp (Finset.mem_coe.mpr ha)) hχ,
      mul_ite, mul_one, mul_zero]
  rw [step, Finset.sum_ite_eq' c.support (χ : ClassFunction G ℂ) (fun a => (c a : ℂ))]
  by_cases hmem : (χ : ClassFunction G ℂ) ∈ c.support
  · rw [if_pos hmem]
  · rw [if_neg hmem, Finsupp.notMem_support_iff.mp hmem, Int.cast_zero]

omit [Finite G] in
/-- Conjugate-linearity of `ClassFunction.inner` over a scalar in the right argument. -/
theorem inner_smul_right (c : ℂ) (φ ψ : ClassFunction G ℂ) :
    ClassFunction.inner φ (c • ψ) = star c * ClassFunction.inner φ ψ := by
  have h : ClassFunction.innerSum φ (c • ψ) = star c * ClassFunction.innerSum φ ψ := by
    rw [ClassFunction.innerSum, ClassFunction.innerSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ClassFunction.smul_apply, star_mul']
    ring
  rw [ClassFunction.inner, ClassFunction.inner, h]; ring

omit [Finite G] in
/-- **Conjugate symmetry of `ClassFunction.inner`:** `⟨ψ, φ⟩ = conj ⟨φ, ψ⟩`.
The unscaled sum `∑ φ(g) conj(ψ(g))` is conjugate-symmetric, and the normalizing factor
`⅟|G|` is real. -/
theorem inner_conj_symm (φ ψ : ClassFunction G ℂ) :
    ClassFunction.inner ψ φ = star (ClassFunction.inner φ ψ) := by
  have hsum : ClassFunction.innerSum ψ φ = star (ClassFunction.innerSum φ ψ) := by
    rw [ClassFunction.innerSum, ClassFunction.innerSum, star_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [star_mul', star_star, mul_comm]
  have hcard : star (⅟(Nat.card G : ℂ)) = ⅟(Nat.card G : ℂ) := by
    rw [show (⅟(Nat.card G : ℂ)) = ((Nat.card G : ℂ))⁻¹ from invOf_eq_inv _,
      star_inv₀, Complex.star_def, Complex.conj_natCast]
  rw [ClassFunction.inner, ClassFunction.inner, hsum, star_mul', hcard]

omit [Finite G] in
/-- Right-linearity of `ClassFunction.inner` over a finite sum. -/
theorem inner_sum_right {ι : Type*} (φ : ClassFunction G ℂ) (s : Finset ι)
    (f : ι → ClassFunction G ℂ) :
    ClassFunction.inner φ (∑ i ∈ s, f i) =
      ∑ i ∈ s, ClassFunction.inner φ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.inner_add_right, ih]

/-- **Parseval (norm form)** for an integer span representation: the squared norm is the
sum of squared integer coefficients. -/
theorem inner_self_eq_sum_sq_of_repr {c : ClassFunction G ℂ →₀ ℤ}
    (hsupp : ↑c.support ⊆ irreducibleCharacters G) :
    ClassFunction.inner (∑ a ∈ c.support, (c a : ℂ) • a)
        (∑ a ∈ c.support, (c a : ℂ) • a) =
      ∑ a ∈ c.support, (c a : ℂ) ^ 2 := by
  rw [inner_sum_right]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [inner_smul_right]
  have hb' : b ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr hb)
  have hcoeff : ClassFunction.inner (∑ a ∈ c.support, (c a : ℂ) • a) b = (c b : ℂ) := by
    have h := inner_eq_coeff_of_repr (⟨b, hb'⟩ : IrreducibleCharacter G) hsupp
    rwa [show ((⟨b, hb'⟩ : IrreducibleCharacter G) : ClassFunction G ℂ) = b from rfl] at h
  rw [hcoeff, star_intCast]; ring

/-- A virtual character `φ ∈ ZIrr G` has integer Fourier coefficients and its squared norm
is the sum of their squares. -/
theorem mem_ZIrr_inner_self_eq_sum_sq {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) :
    ∃ c : ClassFunction G ℂ →₀ ℤ, (↑c.support ⊆ irreducibleCharacters G) ∧
      φ = ∑ a ∈ c.support, (c a : ℂ) • a ∧
      ClassFunction.inner φ φ = ∑ a ∈ c.support, (c a : ℂ) ^ 2 := by
  obtain ⟨c, hsupp, hrepr⟩ := mem_ZIrr_repr hφ
  refine ⟨c, hsupp, hrepr, ?_⟩
  rw [hrepr]
  exact inner_self_eq_sum_sq_of_repr hsupp

/-- Finite integer-vector combinatorics: if integer coefficients on a finite set `s`
are all nonzero and their squares sum to `2`, then `s` has exactly two elements, each
with coefficient `±1`. -/
theorem exists_pair_of_sum_sq_eq_two {ι : Type*} [DecidableEq ι] {s : Finset ι} {c : ι → ℤ}
    (hne : ∀ a ∈ s, c a ≠ 0) (hsum : ∑ a ∈ s, c a ^ 2 = 2) :
    ∃ α β : ι, α ≠ β ∧ s = {α, β} ∧
      (c α = 1 ∨ c α = -1) ∧ (c β = 1 ∨ c β = -1) := by
  classical
  have hsq2 : ∀ n : ℤ, n ^ 2 ≠ 2 := by
    intro n hn
    have h1 : (n - 1) * (n + 1) = 1 := by linear_combination hn
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
  have hge : ∀ a ∈ s, 1 ≤ c a ^ 2 := fun a ha => by
    have h := Int.one_le_abs (hne a ha)
    calc (1 : ℤ) = 1 ^ 2 := by ring
      _ ≤ |c a| ^ 2 := by gcongr
      _ = c a ^ 2 := sq_abs (c a)
  have hcard2 : s.card ≤ 2 := by
    have hle : (s.card : ℤ) ≤ ∑ a ∈ s, c a ^ 2 := by
      calc (s.card : ℤ) = ∑ _a ∈ s, (1 : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ∑ a ∈ s, c a ^ 2 := Finset.sum_le_sum hge
    rw [hsum] at hle
    omega
  have hcard : s.card = 2 := by
    rcases Nat.lt_or_ge s.card 2 with hlt | hge2
    · interval_cases hc : s.card
      · rw [Finset.card_eq_zero] at hc; subst hc; simp at hsum
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
        rw [Finset.sum_singleton] at hsum
        exact absurd hsum (hsq2 (c a))
    · omega
  obtain ⟨α, β, hαβ, rfl⟩ := Finset.card_eq_two.mp hcard
  rw [Finset.sum_pair hαβ] at hsum
  have h1 := hge α (by simp)
  have h2 := hge β (by simp)
  have hα1 : c α ^ 2 = 1 := by omega
  have hβ1 : c β ^ 2 = 1 := by omega
  refine ⟨α, β, hαβ, rfl, ?_, ?_⟩
  · rw [pow_two] at hα1; exact mul_self_eq_one_iff.mp hα1
  · rw [pow_two] at hβ1; exact mul_self_eq_one_iff.mp hβ1

/-! ### Integer Cauchy–Schwarz on a coefficient vector

The numeric core of Peterfalvi §7 (5.4): for an integer `c`, `c ≤ c²`, with
equality exactly when `c ∈ {0, 1}`.  Summed over a finite index set this gives
`∑ c ≤ ∑ c²` and the tight equality `∀ a, c a ∈ {0, 1}`.  These are pure `ℤ`
facts used to turn the orthonormal Parseval identities into the (5.4.a)
inequality `‖χ‖² ≤ ‖X‖²` and the (5.4.b) reconstruction `X = ∑_{α ∈ E} α`. -/

/-- For an integer `c`, `c ≤ c²` (since `c (c - 1) ≥ 0`). -/
theorem int_le_sq (c : ℤ) : c ≤ c ^ 2 := by nlinarith [sq_nonneg (c - 1), sq_nonneg c]

/-- Equality `c = c²` holds for an integer iff `c ∈ {0, 1}`. -/
theorem int_eq_sq_iff (c : ℤ) : c = c ^ 2 ↔ c = 0 ∨ c = 1 := by
  constructor
  · intro h
    have : c * (c - 1) = 0 := by ring_nf; linarith [h]
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rintro (rfl | rfl) <;> norm_num

/-- **Finite integer Cauchy–Schwarz.** `∑_{a ∈ s} c a ≤ ∑_{a ∈ s} (c a)²`. -/
theorem finset_sum_le_sum_sq {ι : Type*} (s : Finset ι) (c : ι → ℤ) :
    ∑ a ∈ s, c a ≤ ∑ a ∈ s, (c a) ^ 2 :=
  Finset.sum_le_sum fun a _ => int_le_sq (c a)

/-- **Tightness of integer Cauchy–Schwarz.** The sum and the sum of squares are
equal iff every coefficient is `0` or `1`. -/
theorem finset_sum_eq_sum_sq_iff {ι : Type*} (s : Finset ι) (c : ι → ℤ) :
    (∑ a ∈ s, c a = ∑ a ∈ s, (c a) ^ 2) ↔ ∀ a ∈ s, c a = 0 ∨ c a = 1 := by
  constructor
  · intro h a ha
    exact (int_eq_sq_iff (c a)).mp
      ((Finset.sum_eq_sum_iff_of_le fun a _ => int_le_sq (c a)).mp h a ha)
  · intro h
    exact Finset.sum_congr rfl fun a ha => (int_eq_sq_iff (c a)).mpr (h a ha)

/-! ### Parseval on an arbitrary orthonormal finite family

Peterfalvi's `R(χ)` in (5.2.d) is an **orthonormal subset of `ℤ[Irr G]`** (norm-`1`,
pairwise-orthogonal virtual characters — not necessarily single irreducibles).  The (5.4)
argument only needs the Parseval identities for such a family: the Fourier coefficient of
an integer combination `X = ∑ c_a • α_a` at a basis vector `α_b` is `c_b`, and the squared
norm is `∑ c_a²`.  These lemmas are stated for a `Finset` carrying an explicit
orthonormality hypothesis `⟨α_a, α_b⟩ = δ_{a,b}`, so they apply verbatim once the family is
extracted from the gateway struct. -/

open scoped Classical in
omit [Finite G] in
/-- **Coefficient recovery in an orthonormal family.** If `⟨a, b⟩ = δ_{a,b}` for all
`a, b ∈ s`, then the Fourier coefficient of `X = ∑_{a ∈ s} (c a) • a` at `b ∈ s` is `c b`. -/
theorem inner_orthonormalSum_eq_coeff {s : Finset (ClassFunction G ℂ)} {c : ClassFunction G ℂ → ℤ}
    (horth : ∀ a ∈ s, ∀ b ∈ s, ClassFunction.inner a b = if a = b then (1 : ℂ) else 0)
    {b : ClassFunction G ℂ} (hb : b ∈ s) :
    ClassFunction.inner (∑ a ∈ s, (c a : ℂ) • a) b = (c b : ℂ) := by
  classical
  rw [inner_sum_left]
  have step : (∑ a ∈ s, ClassFunction.inner ((c a : ℂ) • a) b)
      = ∑ a ∈ s, (if a = b then (c a : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [ClassFunction.inner_smul_left, horth a ha b hb, mul_ite, mul_one, mul_zero]
  rw [step, Finset.sum_ite_eq' s b (fun a => (c a : ℂ)), if_pos hb]

open scoped Classical in
omit [Finite G] in
/-- **Parseval (norm form) for an orthonormal family.** With `⟨a, b⟩ = δ_{a,b}` on `s`, the
squared norm of `X = ∑_{a ∈ s} (c a) • a` is `∑_{a ∈ s} (c a)²`. -/
theorem inner_self_orthonormalSum_eq_sum_sq {s : Finset (ClassFunction G ℂ)}
    {c : ClassFunction G ℂ → ℤ}
    (horth : ∀ a ∈ s, ∀ b ∈ s, ClassFunction.inner a b = if a = b then (1 : ℂ) else 0) :
    ClassFunction.inner (∑ a ∈ s, (c a : ℂ) • a) (∑ a ∈ s, (c a : ℂ) • a) =
      ∑ a ∈ s, (c a : ℂ) ^ 2 := by
  rw [inner_sum_right]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [inner_smul_right, inner_orthonormalSum_eq_coeff horth hb, star_intCast]
  ring

open scoped Classical in
omit [Finite G] in
/-- **Inner product against the all-ones sum.** With `⟨a, b⟩ = δ_{a,b}` on `s`, the inner
product of `X = ∑_{a ∈ s} (c a) • a` against the unsigned sum `∑_{a ∈ s} a` is `∑_{a ∈ s} c a`.
This is the middle identity of Peterfalvi (5.4.a): `‖χ‖² = ⟨X, ∑_{α} α⟩ = ∑_{α} ⟨X, α⟩`. -/
theorem inner_orthonormalSum_sum_eq_sum_coeff {s : Finset (ClassFunction G ℂ)}
    {c : ClassFunction G ℂ → ℤ}
    (horth : ∀ a ∈ s, ∀ b ∈ s, ClassFunction.inner a b = if a = b then (1 : ℂ) else 0) :
    ClassFunction.inner (∑ a ∈ s, (c a : ℂ) • a) (∑ a ∈ s, a) =
      ∑ a ∈ s, (c a : ℂ) := by
  rw [inner_sum_right]
  refine Finset.sum_congr rfl fun b hb => ?_
  exact inner_orthonormalSum_eq_coeff horth hb

set_option backward.isDefEq.respectTransparency false in
omit [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- An irreducible representation has positive dimension. -/
theorem finrank_pos_of_isIrreducible {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    0 < Module.finrank ℂ V := by
  haveI := hρ
  haveI : Nontrivial V :=
    IsSimpleModule.nontrivial (R := MonoidAlgebra ℂ G) (M := ρ.asModule)
  exact Module.finrank_pos

omit [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- The degree of an irreducible character is a positive integer: `χ(1) = (d : ℂ)` with
`0 < d` (the dimension of the underlying representation). -/
theorem irreducibleCharacter_apply_one_eq_pos_natCast (χ : IrreducibleCharacter G) :
    ∃ d : ℕ, 0 < d ∧ ((χ : ClassFunction G ℂ) : G → ℂ) 1 = (d : ℂ) := by
  obtain ⟨V, _, _, _, ρ, hρ, hχ⟩ := χ.isIrreducible
  exact ⟨Module.finrank ℂ V, finrank_pos_of_isIrreducible ρ hρ, by
    rw [congrFun hχ 1, ρ.char_one]⟩

/-- **Norm-2 virtual character is a difference of two distinct irreducible characters.**
If `φ ∈ ZIrr G` has squared norm `2` and vanishes at `1`, then `φ = α - β` for distinct
irreducible characters `α, β`.  This is the layer-2 → layer-3 bridge for Peterfalvi §3
(1.4): each isometric image `τ (χ_i - χ_0)` becomes a named difference of irreducibles. -/
theorem exists_irr_sub_irr_of_inner_self_two {φ : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) (hnorm : ClassFunction.inner φ φ = 2) (hone : φ (1 : G) = 0) :
    ∃ α β : IrreducibleCharacter G, α ≠ β ∧
      φ = (α : ClassFunction G ℂ) - (β : ClassFunction G ℂ) := by
  classical
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hφ
  have hsumC : ∑ a ∈ c.support, (c a : ℂ) ^ 2 = 2 := hsq.symm.trans hnorm
  have hsumZ : ∑ a ∈ c.support, c a ^ 2 = 2 := by exact_mod_cast hsumC
  have hne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  obtain ⟨α₀, β₀, hαβ, hs, hcα, hcβ⟩ := exists_pair_of_sum_sq_eq_two hne hsumZ
  have hα₀ : α₀ ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hβ₀ : β₀ ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  rw [hs, Finset.sum_pair hαβ] at hrepr
  obtain ⟨dα, hdα, hα1⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨α₀, hα₀⟩ : IrreducibleCharacter G)
  obtain ⟨dβ, hdβ, hβ1⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨β₀, hβ₀⟩ : IrreducibleCharacter G)
  simp only [IrreducibleCharacter.coe_mk] at hα1 hβ1
  have hone' : (c α₀ : ℂ) * (dα : ℂ) + (c β₀ : ℂ) * (dβ : ℂ) = 0 := by
    have h := hone
    rw [hrepr] at h
    simpa only [ClassFunction.add_apply, ClassFunction.smul_apply, hα1, hβ1] using h
  have hdegne : ((dα + dβ : ℕ) : ℂ) ≠ 0 := by rw [Nat.cast_ne_zero]; omega
  rcases hcα with hcα | hcα <;> rcases hcβ with hcβ | hcβ
  · -- (+1, +1): impossible by degree positivity
    exfalso
    rw [hcα, hcβ] at hone'
    simp only [Int.cast_one, one_mul] at hone'
    rw [← Nat.cast_add] at hone'
    exact hdegne hone'
  · -- (+1, -1): φ = α₀ - β₀
    refine ⟨⟨α₀, hα₀⟩, ⟨β₀, hβ₀⟩, fun h => hαβ (congrArg Subtype.val h), ?_⟩
    rw [hrepr, hcα, hcβ]
    simp only [IrreducibleCharacter.coe_mk, Int.cast_one, Int.cast_neg, one_smul, neg_one_smul]
    abel
  · -- (-1, +1): φ = β₀ - α₀
    refine ⟨⟨β₀, hβ₀⟩, ⟨α₀, hα₀⟩, fun h => hαβ (congrArg Subtype.val h).symm, ?_⟩
    rw [hrepr, hcα, hcβ]
    simp only [IrreducibleCharacter.coe_mk, Int.cast_one, Int.cast_neg, one_smul, neg_one_smul]
    abel
  · -- (-1, -1): impossible by degree positivity
    exfalso
    rw [hcα, hcβ] at hone'
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at hone'
    have h2 : (dα : ℂ) + (dβ : ℂ) = 0 := by linear_combination -hone'
    rw [← Nat.cast_add] at h2
    exact hdegne h2

end OddOrder.RepresentationTheory
