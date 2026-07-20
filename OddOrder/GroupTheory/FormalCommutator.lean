/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.Main
import Mathlib.Algebra.Free

/-!
# Formal commutators and formal words

P. Hall's collecting process rewrites an ordered product of group elements by
repeatedly applying `u v = v u [u, v]`.  Each swap creates a new factor which is
a *commutator of the two factors swapped*, so the bookkeeping the process needs
is not about group elements but about the **commutator trees** that record how a
factor was built.  This file sets up those trees.

A formal commutator over an alphabet `X` is an element of `FreeMagma X`: either
a variable, or a formal bracket of two formal commutators.  Two invariants ride
along:

* its **weight**, the number of variable occurrences (`FreeMagma.length`), which
  bounds how deep in the lower central series its value lies;
* its **support** relative to a labelling `label : X → L`, the finite set of
  labels occurring in it.  The collecting process sorts factors by support, and
  the point of the whole argument is that a factor whose support has `k`
  elements has weight at least `k`, hence value in `γ_k`.

## Commutator convention

`eval` uses the **classical** bracket `[a, b] = a⁻¹ b⁻¹ a b` rather than
mathlib's `⁅a, b⁆ = a b a⁻¹ b⁻¹`.  The reason is `eval_mul_comm`:

`E u * E v = E v * E u * E (u * v)`,

the swap identity the collecting process runs on, holds *on the nose* for the
classical bracket, whereas mathlib's convention would force an inverse into the
formal tree.  The two conventions differ only by inverting both arguments
(`[a, b] = ⁅a⁻¹, b⁻¹⁆`, recorded as `eval_mul_eq_commutatorElement`), so the
lower-central-series bookkeeping is unaffected.

## Main results

* `FormalCommutator.eval_mul_comm` — the swap identity.
* `FormalCommutator.card_support_le_weight` — `|support| ≤ weight`.
* `FormalCommutator.eval_mem_lowerCentralSeries` — a formal commutator of
  weight `w` evaluates into the book's `γ_w`, i.e. `lowerCentralSeries (w - 1)`.
* `FormalCommutator.evalWord_mem_lowerCentralSeries` — hence an ordered product
  of formal commutators all of weight `≥ w` lies in `γ_w`.
-/

namespace OddOrder.GroupTheory

open scoped commutatorElement

/-- A **formal commutator** over the alphabet `X`: a variable, or a formal
bracket of two formal commutators.  This is `FreeMagma X`; the alias records the
intended reading. -/
abbrev FormalCommutator (X : Type*) := FreeMagma X

namespace FormalCommutator

variable {X : Type*} {L : Type*} {G : Type*} [Group G]

/-! ## Weight -/

/-- The **weight** of a formal commutator: its number of variable occurrences. -/
abbrev weight (c : FormalCommutator X) : ℕ := c.length

@[simp] theorem weight_of (x : X) : weight (FreeMagma.of x) = 1 := rfl

@[simp] theorem weight_mul (u v : FormalCommutator X) :
    weight (u * v) = weight u + weight v := rfl

theorem weight_pos (c : FormalCommutator X) : 0 < weight c := FreeMagma.length_pos c

/-! ## Support -/

variable [DecidableEq L]

/-- The **support** of a formal commutator relative to a labelling `label`: the
finite set of labels of the variables occurring in it. -/
def support (label : X → L) : FormalCommutator X → Finset L
  | FreeMagma.of x => {label x}
  | u * v => support label u ∪ support label v

@[simp] theorem support_of (label : X → L) (x : X) :
    support label (FreeMagma.of x) = {label x} := rfl

@[simp] theorem support_mul (label : X → L) (u v : FormalCommutator X) :
    support label (u * v) = support label u ∪ support label v := rfl

theorem support_nonempty (label : X → L) (c : FormalCommutator X) :
    (support label c).Nonempty := by
  induction c using FreeMagma.recOnMul with
  | ih1 x => exact ⟨label x, by simp⟩
  | ih2 u v hu _ => exact hu.mono Finset.subset_union_left

/-- **The weight bound.**  A formal commutator whose support has `k` elements
has at least `k` variable occurrences.  This is the whole reason Hall's process
produces membership in `γ_k`: sorting the factors by support automatically sorts
them by depth in the lower central series. -/
theorem card_support_le_weight (label : X → L) (c : FormalCommutator X) :
    (support label c).card ≤ weight c := by
  induction c using FreeMagma.recOnMul with
  | ih1 x => simp
  | ih2 u v hu hv =>
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [weight_mul]
      exact Nat.add_le_add hu hv

/-! ## Evaluation -/

/-- Evaluation of a formal commutator at an assignment `f : X → G`, using the
classical bracket `[a, b] = a⁻¹ b⁻¹ a b` (see the module docstring). -/
def eval (f : X → G) : FormalCommutator X → G
  | FreeMagma.of x => f x
  | u * v => (eval f u)⁻¹ * (eval f v)⁻¹ * eval f u * eval f v

@[simp] theorem eval_of (f : X → G) (x : X) : eval f (FreeMagma.of x) = f x := rfl

@[simp] theorem eval_mul (f : X → G) (u v : FormalCommutator X) :
    eval f (u * v) = (eval f u)⁻¹ * (eval f v)⁻¹ * eval f u * eval f v := rfl

/-- The classical bracket is mathlib's bracket with both arguments inverted. -/
theorem eval_mul_eq_commutatorElement (f : X → G) (u v : FormalCommutator X) :
    eval f (u * v) = ⁅(eval f u)⁻¹, (eval f v)⁻¹⁆ := by
  rw [eval_mul, commutatorElement_def, inv_inv, inv_inv, mul_assoc, mul_assoc]

/-- **The swap identity**, the single rewrite the collecting process performs:
exchanging two adjacent factors costs exactly their formal bracket. -/
theorem eval_mul_comm (f : X → G) (u v : FormalCommutator X) :
    eval f u * eval f v = eval f v * eval f u * eval f (u * v) := by
  rw [eval_mul]; group

/-- A formal commutator of weight `w` evaluates into the book's `γ_w`, i.e.
mathlib's `lowerCentralSeries (w - 1)`. -/
theorem eval_mem_lowerCentralSeries (f : X → G) (c : FormalCommutator X) :
    eval f c ∈ (⊤ : Subgroup G).lowerCentralSeries (weight c - 1) := by
  induction c using FreeMagma.recOnMul with
  | ih1 x => exact Subgroup.mem_top _
  | ih2 u v hu hv =>
      have hmem := OddOrder.Isaacs.Ch04.commutator_lowerCentralSeries_le
        (G := G) (weight u - 1) (weight v - 1)
        (Subgroup.commutator_mem_commutator
          ((Subgroup.inv_mem_iff _).mpr hu) ((Subgroup.inv_mem_iff _).mpr hv))
      rw [eval_mul_eq_commutatorElement]
      have hw : weight u - 1 + (weight v - 1) + 1 = weight (u * v) - 1 := by
        have := weight_pos u
        have := weight_pos v
        rw [weight_mul]; omega
      rwa [hw] at hmem

/-- Monotone form: weight at least `w` puts the value in `γ_w`. -/
theorem eval_mem_lowerCentralSeries_of_le (f : X → G) {c : FormalCommutator X} {w : ℕ}
    (hw : w ≤ weight c) :
    eval f c ∈ (⊤ : Subgroup G).lowerCentralSeries (w - 1) :=
  (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.sub_le_sub_right hw 1)
    (eval_mem_lowerCentralSeries f c)

/-! ## Formal words -/

/-- A **formal word** is an ordered list of formal commutators; it evaluates to
the ordered product of their values. -/
def evalWord (f : X → G) (l : List (FormalCommutator X)) : G := (l.map (eval f)).prod

@[simp] theorem evalWord_nil (f : X → G) : evalWord f ([] : List (FormalCommutator X)) = 1 := rfl

@[simp] theorem evalWord_cons (f : X → G) (c : FormalCommutator X)
    (l : List (FormalCommutator X)) :
    evalWord f (c :: l) = eval f c * evalWord f l := rfl

theorem evalWord_append (f : X → G) (l₁ l₂ : List (FormalCommutator X)) :
    evalWord f (l₁ ++ l₂) = evalWord f l₁ * evalWord f l₂ := by
  simp [evalWord, List.map_append]

/-- A word of bare variables evaluates to the ordered product of their values. -/
@[simp] theorem evalWord_map_of (f : X → G) (l : List X) :
    evalWord f (l.map FreeMagma.of) = (l.map f).prod := by
  simp [evalWord, List.map_map, Function.comp_def]

/-- Evaluation turns a concatenation of subwords into the product of their
values. -/
theorem evalWord_flatMap {ι : Type*} (f : X → G) (l : List ι)
    (F : ι → List (FormalCommutator X)) :
    evalWord f (l.flatMap F) = (l.map fun a => evalWord f (F a)).prod := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.flatMap_cons, evalWord_append, ih, List.map_cons, List.prod_cons]

/-- The swap identity at the level of words: exchanging the first two factors of
a word costs one extra factor, their formal bracket. -/
theorem evalWord_swap (f : X → G) (u v : FormalCommutator X)
    (l : List (FormalCommutator X)) :
    evalWord f (u :: v :: l) = evalWord f (v :: u :: (u * v) :: l) := by
  simp only [evalWord_cons, ← mul_assoc]
  rw [eval_mul_comm f u v]

/-! ## Substitution

Hall's argument compares one formal word evaluated at different assignments: the
assignment attached to a set `A` of labels kills every variable labelled outside
`A`.  The two lemmas below say what that does — factors whose support escapes
`A` die, and the surviving factors do not notice which `A ⊇ support` was used.
-/

section Substitution

/-- **Killing labels outside `A` kills every factor whose support escapes `A`.** -/
theorem eval_eq_one_of_not_subset (label : X → L) {A : Finset L} {f : X → G}
    (hf : ∀ x : X, label x ∉ A → f x = 1) {c : FormalCommutator X}
    (hc : ¬ support label c ⊆ A) : eval f c = 1 := by
  induction c using FreeMagma.recOnMul with
  | ih1 x =>
      have hx : label x ∉ A := by
        simpa [support_of, Finset.singleton_subset_iff] using hc
      simp [hf x hx]
  | ih2 u v hu hv =>
      rw [support_mul, Finset.union_subset_iff] at hc
      rw [eval_mul]
      rcases not_and_or.mp hc with h | h
      · rw [hu h]; group
      · rw [hv h]; group

/-- **Only the labels in the support matter.**  Two assignments agreeing on the
variables whose labels occur in `c` give `c` the same value. -/
theorem eval_congr (label : X → L) {f f' : X → G} {c : FormalCommutator X}
    (h : ∀ x : X, label x ∈ support label c → f x = f' x) : eval f c = eval f' c := by
  induction c using FreeMagma.recOnMul with
  | ih1 x => exact h x (by simp)
  | ih2 u v hu hv =>
      rw [eval_mul, eval_mul, hu fun x hx => h x (by simp [hx]),
        hv fun x hx => h x (by simp [hx])]

/-- Word form of `eval_eq_one_of_not_subset`. -/
theorem evalWord_eq_one_of_not_subset (label : X → L) {A : Finset L} {f : X → G}
    (hf : ∀ x : X, label x ∉ A → f x = 1) {l : List (FormalCommutator X)}
    (hl : ∀ c ∈ l, ¬ support label c ⊆ A) : evalWord f l = 1 := by
  induction l with
  | nil => simp
  | cons c t ih =>
      rw [evalWord_cons, eval_eq_one_of_not_subset label hf (hl c (by simp)),
        ih fun d hd => hl d (List.mem_cons_of_mem _ hd), one_mul]

/-- Word form of `eval_congr`. -/
theorem evalWord_congr (label : X → L) {f f' : X → G} {l : List (FormalCommutator X)}
    (h : ∀ c ∈ l, ∀ x : X, label x ∈ support label c → f x = f' x) :
    evalWord f l = evalWord f' l := by
  induction l with
  | nil => simp
  | cons c t ih =>
      rw [evalWord_cons, evalWord_cons, eval_congr label (h c (by simp)),
        ih fun d hd => h d (List.mem_cons_of_mem _ hd)]

end Substitution

/-- An ordered product of formal commutators all of weight at least `w` lies in
the book's `γ_w`. -/
theorem evalWord_mem_lowerCentralSeries (f : X → G) {l : List (FormalCommutator X)} {w : ℕ}
    (hl : ∀ c ∈ l, w ≤ weight c) :
    evalWord f l ∈ (⊤ : Subgroup G).lowerCentralSeries (w - 1) := by
  induction l with
  | nil => simp
  | cons c t ih =>
      refine Subgroup.mul_mem _ (eval_mem_lowerCentralSeries_of_le f (hl c (by simp))) ?_
      exact ih fun d hd => hl d (List.mem_cons_of_mem _ hd)

end FormalCommutator

end OddOrder.GroupTheory
