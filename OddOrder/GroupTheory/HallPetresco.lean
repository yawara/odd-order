/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.FormalCollection

/-!
# The Hall–Petresco formula: the expanded word

This file sets up the word Hall's collecting process is applied to, following
Mann's proof (Dixon–du Sautoy–Mann–Segal, *Analytic Pro-p Groups*, 2nd ed.,
Appendix A).

The trick of that proof is to *de-specialise*.  Instead of collecting `x₁ⁿ ⋯ x_mⁿ`
directly — where one has to count how often each commutator appears — one gives
every one of the `n` copies of a generator its own letter.  Take variables

`(g, j) : G × L`,  `g` a generator, `j` a *slot*,

and the word `expandedWord`, which lists the variables generator by generator
and, inside each generator, slot by slot.  The assignment `assign A` attached to
a set `A` of slots sends `(g, j)` to `g` if `j ∈ A` and to `1` otherwise, so

`evalWord (assign A) (expandedWord L xs) = x₁^{|A|} ⋯ x_m^{|A|}`

(`evalWord_expandedWord` below) — the same group element for every `A` of the
same size, which is what eventually forces the collected blocks to depend only
on `|A|` and produces the binomial exponents by counting subsets.
-/

namespace OddOrder.GroupTheory

namespace HallPetresco

open FormalCommutator

variable {G : Type*} [Group G] {L : Type*} [Fintype L] [DecidableEq L]

/-! ## Counting slots -/

/-- An ordered product of copies of a single element is a power. -/
theorem prod_map_ite_eq_pow {ι : Type*} (g : G) (p : ι → Prop) [DecidablePred p] (l : List ι) :
    (l.map fun j => if p j then g else 1).prod = g ^ l.countP fun j => decide (p j) := by
  induction l with
  | nil => simp
  | cons j t ih =>
      rw [List.map_cons, List.prod_cons, ih, List.countP_cons]
      by_cases hj : p j
      · simp [hj, pow_succ']
      · simp [hj]

/-- Counting the slots of `A` among all slots returns `|A|`. -/
theorem countP_toList_mem (A : Finset L) :
    (Finset.univ : Finset L).toList.countP (fun j => decide (j ∈ A)) = A.card := by
  have hnodup : ((Finset.univ : Finset L).toList.filter fun j => decide (j ∈ A)).Nodup :=
    (Finset.nodup_toList _).filter _
  have htf : ((Finset.univ : Finset L).toList.filter fun j => decide (j ∈ A)).toFinset = A := by
    ext j; simp
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup hnodup, htf]

/-! ## The expanded word -/

/-- The assignment attached to a set `A` of slots: the variable `(g, j)` takes
the value `g` when its slot lies in `A`, and `1` otherwise. -/
def assign (A : Finset L) : G × L → G := fun p => if p.2 ∈ A then p.1 else 1

@[simp] theorem assign_apply (A : Finset L) (g : G) (j : L) :
    assign A (g, j) = if j ∈ A then g else 1 := rfl

/-- Variables are labelled by their slot. -/
abbrev slot : G × L → L := Prod.snd

/-- **The expanded word.**  One variable per generator and slot, listed
generator by generator and, within a generator, slot by slot. -/
noncomputable def expandedWord (L : Type*) [Fintype L] [DecidableEq L] (xs : List G) :
    List (FormalCommutator (G × L)) :=
  xs.flatMap fun g => (Finset.univ : Finset L).toList.map fun j => FreeMagma.of (g, j)

/-- Every factor of the expanded word is a bare variable, so its support is a
single slot. -/
theorem support_of_mem_expandedWord {xs : List G} {c : FormalCommutator (G × L)}
    (hc : c ∈ expandedWord L xs) : ∃ j : L, support slot c = {j} := by
  simp only [expandedWord, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨g, _, j, _, rfl⟩ := hc
  exact ⟨j, rfl⟩

/-- **The specialisation.**  Evaluating the expanded word at the assignment of a
slot set `A` gives `x₁^{|A|} ⋯ x_m^{|A|}`: it depends on `A` only through `|A|`. -/
theorem evalWord_expandedWord (xs : List G) (A : Finset L) :
    evalWord (assign A) (expandedWord L xs) = (xs.map fun g => g ^ A.card).prod := by
  rw [expandedWord, evalWord_flatMap]
  refine congrArg List.prod (List.map_congr_left fun g _ => ?_)
  rw [evalWord, List.map_map]
  have hcomp : (eval (assign A) ∘ fun j : L => (FreeMagma.of (g, j) : FormalCommutator (G × L)))
      = fun j : L => if j ∈ A then g else 1 := rfl
  rw [hcomp, prod_map_ite_eq_pow g (· ∈ A), countP_toList_mem]

end HallPetresco

end OddOrder.GroupTheory
