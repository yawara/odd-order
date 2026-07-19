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
bracketing.  (The invariant only has to survive the brackets the process
actually creates, so `hP` may assume that the right factor is selected and the
left one is not — exactly the situation of a transposition.)

## Main results

* `FormalCommutator.evalWord_extract` — extraction does not change the value.
* `FormalCommutator.extract_spec` — the extracted factor is selected, the
  invariant survives, and the selected count drops by one.
* `FormalCommutator.collect_split` — running the pass with fuel `l.countP sel`
  splits the word into a prefix of selected factors followed by a suffix with
  none, without changing its value.
* `FormalCommutator.card_lt_card_support_mul` — a transposition performed while
  collecting a support `T` creates a factor of *strictly larger* support.
* `FormalCommutator.split_level` — running the passes for all supports of one
  cardinality `k` splits the word into one exact-support block per support,
  followed by a residue whose factors all have support of cardinality `> k`.
* `FormalCommutator.exists_split_supports` — **the collecting process**: running
  all levels leaves no residue, so every formal word equals the concatenation of
  one exact-support block per nonempty support, ordered by cardinality.
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
    (hP : ∀ u v : FormalCommutator X, P u → ¬ sel u → sel v → P (u * v))
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
              · exact hP _ _ hPu hu hselv
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
    (hP : ∀ u v : FormalCommutator X, P u → ¬ sel u → sel v → P (u * v))
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

/-! ## One level of the process

Hall's process runs the passes above once for each possible support, in
increasing order of the support's cardinality.  Sorting by cardinality is what
makes the passes fit together: a bracket created while collecting a support `T`
has support *strictly larger* than `T` (`card_lt_card_support_mul`), so it can
never disturb another support of the same cardinality, and after the whole level
is done every surviving factor has support of cardinality at least `k + 1`.
-/

section Level

variable {L : Type*} [DecidableEq L]

/-- The selector "this factor has support exactly `T`". -/
def supportSel (label : X → L) (T : Finset L) (c : FormalCommutator X) : Bool :=
  decide (support label c = T)

@[simp] theorem supportSel_eq_true_iff (label : X → L) (T : Finset L)
    (c : FormalCommutator X) :
    supportSel label T c = true ↔ support label c = T := by simp [supportSel]

/-- **A transposition strictly grows the support.**  If `u` survived the pass for
`T` (its support is not `T`, and is at least as large), then bracketing it with a
factor of support exactly `T` produces a factor whose support is strictly larger
than `T`.  This is why collecting one support never disturbs another support of
the same size. -/
theorem card_lt_card_support_mul (label : X → L) {T : Finset L} {u v : FormalCommutator X}
    (hu : T.card ≤ (support label u).card) (hune : support label u ≠ T)
    (hv : support label v = T) :
    T.card < (support label (u * v)).card := by
  rw [support_mul, hv]
  have hsub : T ⊆ support label u ∪ T := Finset.subset_union_right
  rcases lt_or_eq_of_le (Finset.card_le_card hsub) with h | h
  · exact h
  · refine absurd ?_ hune
    have hEq : T = support label u ∪ T :=
      Finset.eq_of_subset_of_card_le hsub (le_of_eq h.symm)
    exact Finset.eq_of_subset_of_card_le (hEq ▸ Finset.subset_union_left) hu

/-- **One level of the collecting process.**  Let `Ts` list supports all of
cardinality `k`, and let every factor of `l` have support of cardinality at least
`k`, those of cardinality exactly `k` being listed in `Ts`.  Then `l` can be
rewritten, without changing its value, as one block per member of `Ts` — the
block for `T` consisting of factors of support exactly `T` — followed by a
residue in which every factor has support of cardinality at least `k + 1`. -/
theorem split_level (label : X → L) (k : ℕ) :
    ∀ Ts : List (Finset L), (∀ T ∈ Ts, T.card = k) →
      ∀ l : List (FormalCommutator X),
        (∀ c ∈ l, k ≤ (support label c).card ∧
          ((support label c).card = k → support label c ∈ Ts)) →
        ∃ (blocks : List (List (FormalCommutator X))) (res : List (FormalCommutator X)),
          List.Forall₂ (fun T q => ∀ c ∈ q, support label c = T) Ts blocks ∧
          (∀ f : X → G, evalWord f l = evalWord f (blocks.flatten ++ res)) ∧
          ∀ c ∈ res, k + 1 ≤ (support label c).card := by
  intro Ts
  induction Ts with
  | nil =>
      intro _ l hl
      refine ⟨[], l, List.Forall₂.nil, fun f => by simp, ?_⟩
      intro c hc
      obtain ⟨hge, hmem⟩ := hl c hc
      rcases eq_or_lt_of_le hge with heq | hlt
      · exact absurd (hmem heq.symm) (by simp)
      · omega
  | cons T Ts' ih =>
      intro hcard l hl
      have hT : T.card = k := hcard T (by simp)
      set sel := supportSel label T with hsel
      set P : FormalCommutator X → Prop := fun c =>
        k ≤ (support label c).card ∧
          ((support label c).card = k → support label c ∈ T :: Ts') with hPdef
      -- a bracket created by the pass has strictly larger support, so it is
      -- neither selected nor of cardinality `k`
      have hgrow : ∀ u v : FormalCommutator X, P u → ¬ sel u → sel v →
          k < (support label (u * v)).card := by
        intro u v hPu hu hv
        have hune : support label u ≠ T := by
          simpa [hsel, supportSel] using hu
        have hveq : support label v = T := by simpa [hsel] using hv
        have := card_lt_card_support_mul label (hT ▸ hPu.1) hune hveq
        omega
      have hP : ∀ u v : FormalCommutator X, P u → ¬ sel u → sel v → P (u * v) := by
        intro u v hPu hu hv
        have h := hgrow u v hPu hu hv
        exact ⟨le_of_lt h, fun hk => absurd hk (by omega)⟩
      have hclosed : ∀ u v : FormalCommutator X, P u → ¬ sel u → sel v → ¬ sel (u * v) := by
        intro u v hPu hu hv
        have h := hgrow u v hPu hu hv
        simp only [hsel, supportSel_eq_true_iff]
        intro hcon
        rw [hcon, hT] at h
        omega
      obtain ⟨p, s, hsplit, hpsel, hs0, hPps⟩ :=
        collect_split sel hP hclosed (l.countP sel) l rfl (fun c hc => hl c hc)
      have hvalue : ∀ f : X → G, evalWord f l = evalWord f p * evalWord f s := by
        intro f
        rw [← evalWord_collectAux f sel (l.countP sel) l, hsplit, evalWord_append]
      have hsne : ∀ c ∈ s, support label c ≠ T := by
        intro c hc
        have := List.countP_eq_zero.mp hs0 c hc
        simpa [hsel, supportSel] using this
      obtain ⟨blocks', res', hforall', hval', hres'⟩ :=
        ih (fun T' hT' => hcard T' (List.mem_cons_of_mem _ hT')) s (by
          intro c hc
          obtain ⟨hge, hmem⟩ := hPps c (List.mem_append_right p hc)
          refine ⟨hge, fun hk => ?_⟩
          rcases List.mem_cons.mp (hmem hk) with h | h
          · exact absurd h (hsne c hc)
          · exact h)
      refine ⟨p :: blocks', res', List.Forall₂.cons (fun c hc => ?_) hforall', ?_, hres'⟩
      · simpa [hsel] using hpsel c hc
      · intro f
        rw [hvalue f, hval' f, List.flatten_cons, List.append_assoc, evalWord_append,
          evalWord_append, evalWord_append]

/-! ## The whole process

Running the levels in increasing order of cardinality exhausts the word: after
level `k` every surviving factor has support of cardinality `> k`, and no
support can be larger than `L` itself.
-/

variable [Fintype L]

/-- All subsets of `L` of a given cardinality, as a list. -/
noncomputable def levelList (L : Type*) [Fintype L] [DecidableEq L] (k : ℕ) :
    List (Finset L) :=
  (Finset.univ.powersetCard k).toList

theorem card_of_mem_levelList {k : ℕ} {T : Finset L} (h : T ∈ levelList L k) : T.card = k :=
  (Finset.mem_powersetCard.mp (Finset.mem_toList.mp h)).2

theorem mem_levelList {k : ℕ} {T : Finset L} (h : T.card = k) : T ∈ levelList L k :=
  Finset.mem_toList.mpr (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h⟩)

/-- The list of all supports of cardinality `k, k+1, …, k+K-1`, in that order. -/
noncomputable def supportList (L : Type*) [Fintype L] [DecidableEq L] (k K : ℕ) :
    List (Finset L) :=
  (List.range' k K).flatMap (levelList L)

/-- **Running `K` consecutive levels.**  Starting from a word all of whose
factors have support of cardinality at least `k`, the levels `k, …, k+K-1`
rewrite it — without changing its value — into one exact-support block per
support of those cardinalities, followed by a residue whose factors all have
support of cardinality at least `k + K`. -/
theorem split_levels (label : X → L) :
    ∀ (K k : ℕ) (l : List (FormalCommutator X)),
      (∀ c ∈ l, k ≤ (support label c).card) →
      ∃ (blocks : List (List (FormalCommutator X))) (res : List (FormalCommutator X)),
        List.Forall₂ (fun T q => ∀ c ∈ q, support label c = T) (supportList L k K) blocks ∧
        (∀ f : X → G, evalWord f l = evalWord f (blocks.flatten ++ res)) ∧
        ∀ c ∈ res, k + K ≤ (support label c).card := by
  intro K
  induction K with
  | zero =>
      intro k l hl
      exact ⟨[], l, by simp [supportList], fun f => by simp, by simpa using hl⟩
  | succ K ih =>
      intro k l hl
      obtain ⟨blocks₁, res₁, hforall₁, hval₁, hres₁⟩ :=
        split_level (G := G) label k (levelList L k) (fun _ hT => card_of_mem_levelList hT) l
          (fun c hc => ⟨hl c hc, fun hk => mem_levelList hk⟩)
      obtain ⟨blocks₂, res₂, hforall₂, hval₂, hres₂⟩ := ih (k + 1) res₁ hres₁
      refine ⟨blocks₁ ++ blocks₂, res₂, ?_, ?_, ?_⟩
      · have hcat : supportList L k (K + 1) = levelList L k ++ supportList L (k + 1) K := by
          simp [supportList, List.range'_succ]
        rw [hcat]
        exact List.rel_append hforall₁ hforall₂
      · intro f
        rw [hval₁ f, evalWord_append, hval₂ f, evalWord_append, List.flatten_append,
          evalWord_append, evalWord_append, mul_assoc]
      · intro c hc
        have := hres₂ c hc
        omega

/-- **The collecting process.**  Every formal word is equal, as a group element,
to the concatenation of one block per nonempty support, ordered by cardinality,
the block for `S` consisting of factors whose support is exactly `S`.

There is no residue: a surviving factor would need a support larger than `L`. -/
theorem exists_split_supports (label : X → L) (l : List (FormalCommutator X)) :
    ∃ blocks : List (List (FormalCommutator X)),
      List.Forall₂ (fun T q => ∀ c ∈ q, support label c = T)
        (supportList L 1 (Fintype.card L)) blocks ∧
      ∀ f : X → G, evalWord f l = evalWord f blocks.flatten := by
  obtain ⟨blocks, res, hforall, hval, hres⟩ :=
    split_levels (G := G) label (Fintype.card L) 1 l
      (fun c _ => Finset.card_pos.mpr (support_nonempty label c))
  refine ⟨blocks, hforall, ?_⟩
  have hnil : res = [] := by
    rcases res with _ | ⟨c, t⟩
    · rfl
    · have hcard : (support label c).card ≤ Fintype.card L := by
        simpa [Finset.card_univ] using Finset.card_le_univ (support label c)
      exact absurd (hres c (by simp)) (by omega)
  intro f
  rw [hval f, hnil, List.append_nil]

end Level

end FormalCommutator

end OddOrder.GroupTheory
