/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.FormalCommutator

/-!
# The collecting process on formal words

One pass of P. Hall's collecting process picks a class of factors — here
described by an arbitrary predicate `sel` — and moves all of them to the front
of the word, paying one formal bracket for every transposition
(`FormalCommutator.evalWord_swap`).

The pass terminates because each transposition swaps a *selected* factor past an
*unselected* one and creates the bracket of the two, which is again unselected;
so the number of selected factors drops by exactly one per extraction.  Rather
than turn that into a well-founded recursion, `collectAux` takes an explicit
fuel argument and the termination content becomes the counting lemma
`extract_spec`.  Running it with fuel `l.countP sel` is what `collect_split`
does.

The "created brackets stay unselected" hypothesis is not available for an
arbitrary word: in Hall's argument it holds only because the factors still in
play all have support at least as large as the one being collected.  That side
condition is carried here as an abstract invariant `P` which is preserved by
bracketing.

## Main results

* `FormalCommutator.evalWord_extract` — extraction does not change the value.
* `FormalCommutator.extract_spec` — the extracted factor is selected, the
  invariant survives, and the selected count drops by one.
* `FormalCommutator.collect_split` — running the pass with fuel `l.countP sel`
  splits the word into a prefix of selected factors followed by a suffix with
  none, without changing its value.
-/

namespace OddOrder.GroupTheory

namespace FormalCommutator

variable {X : Type*} {G : Type*} [Group G]

/-! ## One extraction -/

/-- Bubble the first `sel`-factor to the front of the word, recording the formal
bracket created at each transposition.  Returns the extracted factor together
with the rest of the word. -/
def extract (sel : FormalCommutator X → Bool) :
    List (FormalCommutator X) → Option (FormalCommutator X × List (FormalCommutator X))
  | [] => none
  | u :: l =>
      if sel u then some (u, l)
      else
        match extract sel l with
        | none => none
        | some (v, r) => some (v, u :: (u * v) :: r)

@[simp] theorem extract_nil (sel : FormalCommutator X → Bool) :
    extract sel ([] : List (FormalCommutator X)) = none := rfl

theorem extract_cons (sel : FormalCommutator X → Bool) (u : FormalCommutator X)
    (l : List (FormalCommutator X)) :
    extract sel (u :: l) =
      if sel u then some (u, l)
      else
        match extract sel l with
        | none => none
        | some (v, r) => some (v, u :: (u * v) :: r) := rfl

/-- Extraction preserves the value of the word: the brackets it records are
exactly the cost of the transpositions it performs. -/
theorem evalWord_extract (f : X → G) (sel : FormalCommutator X → Bool)
    {l : List (FormalCommutator X)} {v : FormalCommutator X}
    {r : List (FormalCommutator X)} (h : extract sel l = some (v, r)) :
    evalWord f l = evalWord f (v :: r) := by
  induction l generalizing v r with
  | nil => simp at h
  | cons u t ih =>
      rw [extract_cons] at h
      by_cases hu : sel u
      · rw [if_pos hu, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      · rw [if_neg hu] at h
        cases hext : extract sel t with
        | none => rw [hext] at h; exact absurd h (by simp)
        | some z =>
            obtain ⟨w, s⟩ := z
            rw [hext, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [evalWord_cons, ih hext, evalWord_cons, ← mul_assoc,
              eval_mul_comm f u w]
            simp only [evalWord_cons, mul_assoc]

/-- If no factor is selected the pass halts. -/
theorem countP_eq_zero_of_extract_eq_none (sel : FormalCommutator X → Bool)
    {l : List (FormalCommutator X)} (h : extract sel l = none) :
    l.countP sel = 0 := by
  induction l with
  | nil => simp
  | cons u t ih =>
      rw [extract_cons] at h
      by_cases hu : sel u
      · rw [if_pos hu] at h; exact absurd h (by simp)
      · rw [if_neg hu] at h
        cases hext : extract sel t with
        | none => simp [List.countP_cons, hu, ih hext]
        | some z => rw [hext] at h; exact absurd h (by simp)

/-- **The counting lemma** behind termination.  Under an invariant `P` that is
inherited by formal brackets and that forbids a created bracket from being
selected, one extraction pulls out a selected factor, keeps the invariant, and
lowers the number of selected factors by exactly one. -/
theorem extract_spec (sel : FormalCommutator X → Bool) {P : FormalCommutator X → Prop}
    (hP : ∀ u v : FormalCommutator X, P u → P (u * v))
    (hclosed : ∀ u v : FormalCommutator X, P u → ¬ sel u → sel v → ¬ sel (u * v))
    {l : List (FormalCommutator X)} {v : FormalCommutator X}
    {r : List (FormalCommutator X)} (hl : ∀ c ∈ l, P c) (h : extract sel l = some (v, r)) :
    sel v ∧ P v ∧ (∀ c ∈ r, P c) ∧ l.countP sel = r.countP sel + 1 := by
  induction l generalizing v r with
  | nil => simp at h
  | cons u t ih =>
      rw [extract_cons] at h
      by_cases hu : sel u
      · rw [if_pos hu, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hu, hl u (by simp), fun c hc => hl c (List.mem_cons_of_mem _ hc),
          by simp [hu]⟩
      · rw [if_neg hu] at h
        cases hext : extract sel t with
        | none => rw [hext] at h; exact absurd h (by simp)
        | some z =>
            obtain ⟨w, s⟩ := z
            rw [hext, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hselv, hPv, hPs, hcount⟩ :=
              ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)) hext
            have hPu : P u := hl u (by simp)
            refine ⟨hselv, hPv, ?_, ?_⟩
            · intro c hc
              rcases List.mem_cons.mp hc with rfl | hc
              · exact hPu
              rcases List.mem_cons.mp hc with rfl | hc
              · exact hP _ _ hPu
              · exact hPs c hc
            · have hbr : sel (u * w) = false := by
                simpa using hclosed u w hPu hu hselv
              have hu' : sel u = false := by simpa using hu
              simp only [List.countP_cons, hu', hbr, Bool.false_eq_true, if_false,
                Nat.add_zero]
              omega

/-! ## One full pass -/

/-- Perform at most `n` extractions, accumulating the extracted factors at the
front.  The fuel `n` replaces a well-founded recursion; `collect_split` runs it
with the only value that matters, `l.countP sel`. -/
def collectAux (sel : FormalCommutator X → Bool) :
    ℕ → List (FormalCommutator X) → List (FormalCommutator X)
  | 0, l => l
  | n + 1, l =>
      match extract sel l with
      | none => l
      | some (v, r) => v :: collectAux sel n r

@[simp] theorem collectAux_zero (sel : FormalCommutator X → Bool)
    (l : List (FormalCommutator X)) : collectAux sel 0 l = l := rfl

theorem collectAux_succ (sel : FormalCommutator X → Bool) (n : ℕ)
    (l : List (FormalCommutator X)) :
    collectAux sel (n + 1) l =
      match extract sel l with
      | none => l
      | some (v, r) => v :: collectAux sel n r := rfl

theorem collectAux_succ_some (sel : FormalCommutator X → Bool) (n : ℕ)
    {l : List (FormalCommutator X)} {v : FormalCommutator X}
    {r : List (FormalCommutator X)} (h : extract sel l = some (v, r)) :
    collectAux sel (n + 1) l = v :: collectAux sel n r := by
  rw [collectAux_succ, h]

theorem collectAux_succ_none (sel : FormalCommutator X → Bool) (n : ℕ)
    {l : List (FormalCommutator X)} (h : extract sel l = none) :
    collectAux sel (n + 1) l = l := by
  rw [collectAux_succ, h]

/-- A pass preserves the value of the word. -/
theorem evalWord_collectAux (f : X → G) (sel : FormalCommutator X → Bool) :
    ∀ (n : ℕ) (l : List (FormalCommutator X)),
      evalWord f (collectAux sel n l) = evalWord f l := by
  intro n
  induction n with
  | zero => intro l; rfl
  | succ n ih =>
      intro l
      cases hext : extract sel l with
      | none => rw [collectAux_succ_none sel n hext]
      | some z =>
          obtain ⟨v, r⟩ := z
          rw [collectAux_succ_some sel n hext, evalWord_cons, ih, ← evalWord_cons,
            ← evalWord_extract f sel hext]

/-- **One full collecting pass.**  Running the extraction with fuel
`l.countP sel` sorts the word into the selected factors, in order, followed by a
tail containing none of them — at the cost of the recorded brackets, and without
changing the value of the word. -/
theorem collect_split (sel : FormalCommutator X → Bool) {P : FormalCommutator X → Prop}
    (hP : ∀ u v : FormalCommutator X, P u → P (u * v))
    (hclosed : ∀ u v : FormalCommutator X, P u → ¬ sel u → sel v → ¬ sel (u * v)) :
    ∀ (n : ℕ) (l : List (FormalCommutator X)), l.countP sel = n → (∀ c ∈ l, P c) →
      ∃ p s : List (FormalCommutator X),
        collectAux sel n l = p ++ s ∧ (∀ c ∈ p, sel c) ∧ s.countP sel = 0 ∧
          (∀ c ∈ p ++ s, P c) := by
  intro n
  induction n with
  | zero =>
      intro l hcount hl
      exact ⟨[], l, by simp, by simp, hcount, by simpa using hl⟩
  | succ n ih =>
      intro l hcount hl
      cases hext : extract sel l with
      | none =>
          rw [countP_eq_zero_of_extract_eq_none sel hext] at hcount
          exact absurd hcount (by omega)
      | some z =>
          obtain ⟨v, r⟩ := z
          obtain ⟨hselv, hPv, hPr, hcr⟩ := extract_spec sel hP hclosed hl hext
          obtain ⟨p, s, hsplit, hpsel, hs0, hPps⟩ := ih r (by omega) hPr
          refine ⟨v :: p, s, by rw [collectAux_succ_some sel n hext, hsplit]; rfl,
            ?_, hs0, ?_⟩
          · intro c hc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact hselv
            · exact hpsel c hc
          · intro c hc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact hPv
            · exact hPps c hc

end FormalCommutator

end OddOrder.GroupTheory
