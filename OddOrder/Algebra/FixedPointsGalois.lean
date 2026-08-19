/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.Ring.Action.End
import Mathlib.Algebra.Ring.Action.Subobjects

/-!
# The Galois correspondence for a group of field automorphisms

Let `F` be a finite field and let `B ≤ RingAut F` be a subgroup.  Artin's lemma
says `[F : F^B] = |B|`.  This file records the consequence used in the odd order
theorem: an automorphism that fixes `F^B` pointwise already lies in `B`.

This is one half of the fundamental theorem of Galois theory, phrased for
`RingAut F` rather than for the algebra automorphisms `E ≃ₐ[F] E` that
`IntermediateField.fixingSubgroup_fixedField` uses.  Peterfalvi's Part II needs
it in the form "`V` acts as a group of field automorphisms on `Q₀` and, by the
theorem of Galois, `C_V(C_{Q₀}(P)) = P`" (Ch. III §1 Proposition, p. 117), where
the automorphism group is handed over as an abstract subgroup of `RingAut F`.

## Main results

* `OddOrder.RingAut.finrank_fixedSet` — Artin's lemma `[F : F^B] = |B|`.
* `OddOrder.RingAut.fixer_fixedSet` — `B` is *all* of the automorphisms fixing
  `F^B` pointwise.
* `OddOrder.RingAut.mem_of_fixes_fixedPoints` — if `σ : RingAut F` fixes every
  element that all of `B` fixes, then `σ ∈ B`.
* `OddOrder.RingAut.eq_of_fixedSet_eq` — subgroups of `RingAut F` with the same
  fixed set are equal.
* `OddOrder.RingAut.orderOf_dvd_of_card_eq_pow` — the order of an automorphism
  divides the degree over the prime field.
* `OddOrder.RingAut.three_le_of_odd_orderOf` — Peterfalvi's "`|F| > 8`, since `θ`
  is of odd order" (Part II, Ch. IV §3 (3), p. 130).
-/

namespace OddOrder.RingAut

variable {F : Type*} [Field F] [Finite F]

instance finite_ringAut : Finite (_root_.RingAut F) :=
  Finite.of_injective (fun e : _root_.RingAut F => (e : F → F)) fun e₁ e₂ h => by
    ext x; exact congrFun h x

/-- The elements of `F` fixed by every member of `B`.  This is the underlying
set of the fixed subfield `F^B`. -/
def fixedSet (B : Subgroup (_root_.RingAut F)) : Set F :=
  {x : F | ∀ τ ∈ B, τ x = x}

/-- The group of all automorphisms of `F` fixing the set `s` pointwise. -/
def fixer (s : Set F) : Subgroup (_root_.RingAut F) where
  carrier := {τ : _root_.RingAut F | ∀ x ∈ s, τ x = x}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb x hx => by
    change a (b x) = x
    rw [hb x hx, ha x hx]
  inv_mem' := fun {a} ha x hx => a.symm_apply_eq.mpr (ha x hx).symm

omit [Finite F] in
@[simp] theorem mem_fixedSet_iff {B : Subgroup (_root_.RingAut F)} {x : F} :
    x ∈ fixedSet B ↔ ∀ τ ∈ B, τ x = x := Iff.rfl

omit [Finite F] in
@[simp] theorem mem_fixer_iff {s : Set F} {τ : _root_.RingAut F} :
    τ ∈ fixer s ↔ ∀ x ∈ s, τ x = x := Iff.rfl

omit [Finite F] in
theorem fixedSet_eq_subfield (B : Subgroup (_root_.RingAut F)) :
    fixedSet B = (FixedPoints.subfield (↥B) F : Set F) := by
  ext x
  exact ⟨fun hx (τ : ↥B) => hx (τ : _root_.RingAut F) τ.2, fun hx τ hτ => hx ⟨τ, hτ⟩⟩

omit [Finite F] in
/-- `fixedSet` is antitone: a bigger group fixes fewer points. -/
theorem fixedSet_antitone {B B' : Subgroup (_root_.RingAut F)} (h : B ≤ B') :
    fixedSet B' ⊆ fixedSet B :=
  fun _ hx τ hτ => hx τ (h hτ)

omit [Finite F] in
theorem le_fixer_fixedSet (B : Subgroup (_root_.RingAut F)) :
    B ≤ fixer (fixedSet B) :=
  fun _ hτ _ hx => hx _ hτ

omit [Finite F] in
/-- Adding all automorphisms that fix `F^B` does not shrink the fixed set. -/
theorem fixedSet_fixer_fixedSet (B : Subgroup (_root_.RingAut F)) :
    fixedSet (fixer (fixedSet B)) = fixedSet B :=
  le_antisymm (fixedSet_antitone (le_fixer_fixedSet B)) fun _ hx _ hτ => hτ _ hx

/-- **Artin's lemma**, in the form `[F : F^B] = |B|` for a subgroup `B` of the
full automorphism group of a finite field `F`. -/
theorem finrank_fixedSet (B : Subgroup (_root_.RingAut F)) :
    Module.finrank (FixedPoints.subfield (↥B) F) F = Nat.card B := by
  have : Fintype (↥B) := Fintype.ofFinite _
  have : FaithfulSMul (↥B) F :=
    ⟨fun {b₁ b₂} h => Subtype.ext (eq_of_smul_eq_smul (α := F) fun x => h x)⟩
  rw [FixedPoints.finrank_eq_card (↥B) F, Nat.card_eq_fintype_card]

/-- Subgroups of `RingAut F` with the same fixed set have the same order,
by Artin's lemma. -/
theorem natCard_eq_of_fixedSet_eq {B B' : Subgroup (_root_.RingAut F)}
    (h : fixedSet B = fixedSet B') : Nat.card B = Nat.card B' := by
  have hsub : FixedPoints.subfield (↥B) F = FixedPoints.subfield (↥B') F :=
    SetLike.ext' (by rw [← fixedSet_eq_subfield, ← fixedSet_eq_subfield, h])
  rw [← finrank_fixedSet B, ← finrank_fixedSet B', hsub]

/-- **The Galois correspondence for `RingAut F`.**  A subgroup `B` is exactly
the group of automorphisms fixing `F^B` pointwise.

Artin's counting argument: `fixer (F^B)` contains `B` and has the same fixed
set, hence the same order, hence equals `B`. -/
theorem fixer_fixedSet (B : Subgroup (_root_.RingAut F)) :
    fixer (fixedSet B) = B :=
  (Subgroup.eq_of_le_of_card_ge (le_fixer_fixedSet B)
    (le_of_eq (natCard_eq_of_fixedSet_eq (fixedSet_fixer_fixedSet B)))).symm

/-- **The theorem of Galois**, in the form Peterfalvi uses: an automorphism of
`F` fixing `F^B` pointwise lies in `B`. -/
theorem mem_of_fixes_fixedPoints {B : Subgroup (_root_.RingAut F)}
    {σ : _root_.RingAut F} (hσ : ∀ x ∈ fixedSet B, σ x = x) : σ ∈ B :=
  fixer_fixedSet B ▸ hσ

/-- Subgroups of `RingAut F` are determined by their fixed sets. -/
theorem eq_of_fixedSet_eq {B B' : Subgroup (_root_.RingAut F)}
    (h : fixedSet B = fixedSet B') : B = B' := by
  rw [← fixer_fixedSet B, ← fixer_fixedSet B', h]

/-- **The order of a field automorphism divides the degree over the prime field.**

Artin's lemma applied to `B = ⟨θ⟩`: the fixed field `F^B` has index `orderOf θ` in `F`,
so `|F| = |F^B|^{orderOf θ}`; both cardinalities being powers of `p`, the exponent
`orderOf θ` divides `m`.

This is the arithmetic behind Peterfalvi's "`|F| > 8`, since `θ` is of odd order"
(Part II, Ch. IV §3 (3), p. 130): an automorphism of odd order `> 1` forces `m` to have
an odd divisor `> 1`, hence `m ≥ 3`. -/
theorem orderOf_dvd_of_card_eq_pow {p m : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Nat.card F = p ^ m) (θ : _root_.RingAut F) : orderOf θ ∣ m := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fintype ↥(FixedPoints.subfield (↥(Subgroup.zpowers θ)) F) := Fintype.ofFinite _
  have : CharP ↥(FixedPoints.subfield (↥(Subgroup.zpowers θ)) F) p :=
    Subfield.charP (FixedPoints.subfield (↥(Subgroup.zpowers θ)) F) p
  have hrank : Module.finrank ↥(FixedPoints.subfield (↥(Subgroup.zpowers θ)) F) F
      = orderOf θ := by
    rw [finrank_fixedSet, Nat.card_zpowers]
  obtain ⟨k, -, hk⟩ := FiniteField.card (K := ↥(FixedPoints.subfield (↥(Subgroup.zpowers θ)) F)) p
  have hFcard : Fintype.card F = p ^ ((k : ℕ) * orderOf θ) := by
    rw [Module.card_eq_pow_finrank
      (K := ↥(FixedPoints.subfield (↥(Subgroup.zpowers θ)) F)) (V := F), hk, hrank, ← pow_mul]
  have hm : m = (k : ℕ) * orderOf θ := by
    refine Nat.pow_right_injective (Fact.out (p := p.Prime)).two_le ?_
    change p ^ m = p ^ ((k : ℕ) * orderOf θ)
    rw [← hFcard, ← hcard, Nat.card_eq_fintype_card]
  exact ⟨(k : ℕ), by rw [hm, Nat.mul_comm]⟩

/-- **"`|F| > 8`, since `θ` is of odd order"** (Peterfalvi Part II, Ch. IV §3 (3), p. 130).

A nontrivial automorphism of odd order has order an odd divisor `> 1` of the degree `m`,
so `m ≥ 3`.  Over `𝐅₂` that is the book's `|F| ≥ 8`.

The odd order of `θ`, not any bound on `|F|`, is what the book uses: the counting of
§3 (3) fails over `𝐅₄`, whose only nontrivial automorphism is the Frobenius — and that
one is excluded because its order is `2`.

⚠ `θ` here is an automorphism of `F` itself, as in the book (its `θ` comes from the
type-`B` datum, which lives on `F` — `TypeBData.phi`).  The corresponding automorphism of
the quadratic extension `E` may well have even order: the `q`-Frobenius of `E` restricts
to the identity on `F`. -/
theorem three_le_of_odd_orderOf {p m : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Nat.card F = p ^ m) {θ : _root_.RingAut F} (hodd : Odd (orderOf θ))
    (hne : θ ≠ 1) : 3 ≤ m := by
  have hdvd := orderOf_dvd_of_card_eq_pow hcard θ
  have h1 : orderOf θ ≠ 1 := fun hc => hne (orderOf_eq_one_iff.mp hc)
  obtain ⟨j, hj⟩ := hodd
  have h3 : 3 ≤ orderOf θ := by omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    have hone : Nat.card F = 1 := by rw [hcard]; simp
    exact one_ne_zero (α := F)
      (Finite.card_le_one_iff_subsingleton.mp (le_of_eq hone) |>.elim _ _)
  exact le_trans h3 (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd)

end OddOrder.RingAut
