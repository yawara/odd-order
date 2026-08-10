/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import OddOrder.Algebra.PowerMonomialIndependence

/-!
# The relation lattice of BG Appendix C, Problem 1

Let `F` be a finite field with prime field `K`.  The *relation lattice* of an exponent `e` is the
`K`-span of the triples

`L_e = span_K { (a, a^e, a^{e²}) : a ∈ Fˣ } ≤ F³`,

and **Lemma D** of `notes/bg/appC_problem1_partial_resolution.md` (issue 0180) says that
`L_e = F³` as soon as the exponents `1, e, e²` are "independent of the Frobenius", i.e. the `3q`
numbers `e^k · |K|^j` are pairwise incongruent modulo `|Fˣ|`.

This file supplies the two ingredients that turn the independence of power monomials
(`OddOrder.PowerMonomial`) into that spanning statement:

* **trace duality** — a subset of `F³` spans iff nothing annihilates it under the trace pairing
  `((l,m,n), (a,b,c)) ↦ Tr(l a + m b + n c)`.  This rests on `Algebra.traceForm_nondegenerate`:
  every `K`-linear functional on `F` is `a ↦ Tr(l · a)`;
* **the annihilator computation** — expanding the trace of `l a + m a^e + n a^{e²}` gives a
  combination of `3q` power monomials, so Dedekind independence kills `l`, `m` and `n`.

## Main results

* `exists_trace_repr` — every `K`-linear functional on a finite field is a trace form.
* `span_eq_top_of_trace_annihilator` — the trace-duality spanning criterion for `F³`.
* `span_triples_eq_top` — **Lemma D**: the relation lattice is everything.
-/

namespace OddOrder.RelationLattice

open Module OddOrder.PowerMonomial

section Duality

variable {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F] [Algebra.IsSeparable K F]

/-- **Every `K`-linear functional on a finite field is a trace form.**  The trace form is
nondegenerate (`Algebra.traceForm_nondegenerate`), hence a perfect pairing in finite dimension, so
`l ↦ Tr(l · −)` is onto the dual space. -/
theorem exists_trace_repr (ℓ : F →ₗ[K] K) :
    ∃ l : F, ∀ a : F, ℓ a = Algebra.trace K F (l * a) := by
  haveI : Module.Finite K F := Module.Finite.of_finite
  set e := (Algebra.traceForm K F).toDual (traceForm_nondegenerate K F) with he
  refine ⟨e.symm ℓ, fun a => ?_⟩
  have happ : e (e.symm ℓ) = ℓ := LinearEquiv.apply_symm_apply e ℓ
  calc ℓ a = e (e.symm ℓ) a := by rw [happ]
    _ = Algebra.trace K F (e.symm ℓ * a) := rfl

/-- **Trace duality: a spanning criterion for `F³`.**  A set of triples spans `F³` over the base
field as soon as no non-zero `(l, m, n)` annihilates it under the trace pairing.

A proper submodule is killed by a non-zero functional, and by `exists_trace_repr` every functional
on `F³` is `(a, b, c) ↦ Tr(l a + m b + n c)`. -/
theorem span_eq_top_of_trace_annihilator (T : Set (F × F × F))
    (h : ∀ l m n : F, (∀ t ∈ T, Algebra.trace K F (l * t.1 + m * t.2.1 + n * t.2.2) = 0) →
      l = 0 ∧ m = 0 ∧ n = 0) :
    Submodule.span K T = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hfbot⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr hne) inferInstance
  -- the three coordinate functionals, and their trace representatives
  obtain ⟨l, hl⟩ := exists_trace_repr (K := K) (f.comp (LinearMap.inl K F (F × F)))
  obtain ⟨m, hm⟩ := exists_trace_repr (K := K)
    (f.comp ((LinearMap.inr K F (F × F)).comp (LinearMap.inl K F F)))
  obtain ⟨n, hn⟩ := exists_trace_repr (K := K)
    (f.comp ((LinearMap.inr K F (F × F)).comp (LinearMap.inr K F F)))
  have hsplit : ∀ t : F × F × F,
      f t = Algebra.trace K F (l * t.1 + m * t.2.1 + n * t.2.2) := by
    rintro ⟨a, b, c⟩
    have hdecomp : ((a, b, c) : F × F × F) = LinearMap.inl K F (F × F) a +
        ((LinearMap.inr K F (F × F)) ((LinearMap.inl K F F) b) +
          (LinearMap.inr K F (F × F)) ((LinearMap.inr K F F) c)) := by
      simp
    have ha := hl a
    have hb := hm b
    have hc := hn c
    simp only [LinearMap.comp_apply] at ha hb hc
    change f ((a, b, c) : F × F × F) = Algebra.trace K F (l * a + m * b + n * c)
    conv_lhs => rw [hdecomp]
    rw [map_add, map_add, ha, hb, hc, ← map_add, ← map_add]
    congr 1
    ring
  have hzero : ∀ x ∈ Submodule.span K T, f x = 0 := by
    intro x hx
    have hmem : f x ∈ Submodule.map f (Submodule.span K T) := Submodule.mem_map_of_mem hx
    rw [hfbot] at hmem
    simpa using hmem
  obtain ⟨hl0, hm0, hn0⟩ := h l m n fun t ht => by
    rw [← hsplit t]
    exact hzero t (Submodule.subset_span ht)
  refine hf0 (LinearMap.ext fun t => ?_)
  rw [hsplit t, hl0, hm0, hn0]
  simp

end Duality

section LemmaD

open Finset

variable {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F] [Algebra.IsSeparable K F]

omit [Algebra.IsSeparable K F] in
/-- **Lemma D, the annihilator computation.**  If the `3 · [F : K]` expanded exponents
`d i · |K|ʲ` give pairwise distinct power maps, then a triple `(l, m, n)` whose trace form
`Tr(l a^{d 0} + m a^{d 1} + n a^{d 2})` vanishes on every unit is zero. -/
theorem eq_zero_of_forall_trace_triple_eq_zero (d : Fin 3 → ℕ) {l m n : F} {r c : ℕ}
    (hr : Module.finrank K F = r) (hc : Nat.card K = c)
    (hD : Function.Injective fun x : Fin 3 × Fin r => powHom F (d x.1 * c ^ (x.2 : ℕ)))
    (h : ∀ a : Fˣ, Algebra.trace K F
      (l * (a : F) ^ d 0 + m * (a : F) ^ d 1 + n * (a : F) ^ d 2) = 0) :
    l = 0 ∧ m = 0 ∧ n = 0 := by
  subst hr; subst hc
  have hzero := eq_zero_of_forall_trace_sum_eq_zero (K := K) d ![l, m, n] hD (fun a => by
    rw [Fin.sum_univ_three]
    simpa [← map_add] using h a)
  exact ⟨by simpa using hzero 0, by simpa using hzero 1, by simpa using hzero 2⟩

/-- **Lemma D.**  If the `3 · [F : K]` expanded exponents `d i · |K|ʲ` give pairwise distinct power
maps, the triples `(a^{d 0}, a^{d 1}, a^{d 2})` span `F³` over the base field. -/
theorem span_triples_eq_top (d : Fin 3 → ℕ) {r c : ℕ}
    (hr : Module.finrank K F = r) (hc : Nat.card K = c)
    (hD : Function.Injective fun x : Fin 3 × Fin r => powHom F (d x.1 * c ^ (x.2 : ℕ))) :
    Submodule.span K {t : F × F × F |
      ∃ a : Fˣ, t = ((a : F) ^ d 0, (a : F) ^ d 1, (a : F) ^ d 2)} = ⊤ := by
  refine span_eq_top_of_trace_annihilator _ fun l m n hann => ?_
  refine eq_zero_of_forall_trace_triple_eq_zero d hr hc hD fun a => ?_
  exact hann _ ⟨a, rfl⟩

/-- **Lemma D on a subgroup covering `Fˣ` up to sign.**  In the application the triples are only
available for `a` in the norm-one subgroup `S`, which together with `-S` exhausts `Fˣ`.  Odd
exponents turn the trace form into an *odd* function of `a`, so its vanishing on `S` already
forces the vanishing on `Fˣ` and Lemma D applies unchanged.

For `F = 𝔽_{3^q}` the norm-one subgroup is the group of squares, of index two, and `-1` is a
non-square, so `hcov` holds. -/
theorem span_triples_subgroup_eq_top (d : Fin 3 → ℕ) (hodd : ∀ i, Odd (d i)) {S : Subgroup Fˣ}
    (hcov : ∀ a : Fˣ, a ∈ S ∨ -a ∈ S) {r c : ℕ}
    (hr : Module.finrank K F = r) (hc : Nat.card K = c)
    (hD : Function.Injective fun x : Fin 3 × Fin r => powHom F (d x.1 * c ^ (x.2 : ℕ))) :
    Submodule.span K {t : F × F × F |
      ∃ a ∈ S, t = ((a : F) ^ d 0, (a : F) ^ d 1, (a : F) ^ d 2)} = ⊤ := by
  refine span_eq_top_of_trace_annihilator _ fun l m n hann => ?_
  refine eq_zero_of_forall_trace_triple_eq_zero d hr hc hD fun a => ?_
  rcases hcov a with ha | ha
  · exact hann _ ⟨a, ha, rfl⟩
  · have h0 := hann _ ⟨-a, ha, rfl⟩
    have hneg : ∀ i, ((-a : Fˣ) : F) ^ d i = -((a : F) ^ d i) := fun i => by
      rw [Units.val_neg, (hodd i).neg_pow]
    have harg : l * ((-a : Fˣ) : F) ^ d 0 + m * ((-a : Fˣ) : F) ^ d 1 +
        n * ((-a : Fˣ) : F) ^ d 2 =
          -(l * (a : F) ^ d 0 + m * (a : F) ^ d 1 + n * (a : F) ^ d 2) := by
      rw [hneg 0, hneg 1, hneg 2]; ring
    rw [harg, map_neg, neg_eq_zero] at h0
    exact h0

end LemmaD

end OddOrder.RelationLattice
