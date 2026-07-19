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

/-! ## Restricting to a slot set

Collect the expanded word **once**; the blocks produced are combinatorial data,
independent of which assignment is substituted afterwards.  Substituting
`assign A` then kills exactly the blocks whose support escapes `A`, and leaves
the others unaware of `A` — each of them evaluates as if only its own slots
existed.
-/

/-- The value of the block attached to a support, evaluated at the assignment of
that very support.  By `evalWord_congr` this is what any `assign A` with
`A ⊇ S` returns. -/
def blockValue (blk : Finset L → List (FormalCommutator (G × L))) (S : Finset L) : G :=
  evalWord (assign S) (blk S)

/-- **Substituting a slot set.**  In a decomposition of a word into exact-support
blocks, the assignment of `A` kills every block whose support is not contained in
`A` and evaluates the remaining ones independently of `A`. -/
theorem map_evalWord_blk_eq {supports : List (Finset L)}
    {blk : Finset L → List (FormalCommutator (G × L))}
    (hblk : ∀ S ∈ supports, ∀ c ∈ blk S, support slot c = S) (A : Finset L) :
    (supports.map fun S => evalWord (assign A) (blk S)).prod
      = (supports.map fun S => if S ⊆ A then blockValue blk S else 1).prod := by
  refine congrArg List.prod (List.map_congr_left fun S hS => ?_)
  by_cases hSA : S ⊆ A
  · rw [if_pos hSA]
    refine evalWord_congr slot fun c hc x hx => ?_
    rw [hblk S hS c hc] at hx
    simp [assign, hx, hSA hx]
  · rw [if_neg hSA]
    refine evalWord_eq_one_of_not_subset (A := A) slot
      (fun x hx => by simp only [assign, if_neg hx]) ?_
    intro c hc
    rw [hblk S hS c hc]
    exact hSA

/-- **The specialised collection formula.**  Fix a decomposition of the expanded
word into exact-support blocks.  Then for every slot set `A`,

`x₁^{|A|} ⋯ x_m^{|A|} = ∏_{∅ ≠ S ⊆ A} blockValue S`,

the product taken in increasing order of `|S|`.  The left-hand side depends on
`A` only through `|A|`, while the right-hand side depends on it only through
which subsets `A` has — the tension that forces `blockValue S` to depend only on
`|S|`, and produces the binomial exponents by counting subsets. -/
theorem prod_pow_card_eq {xs : List G} {blk : Finset L → List (FormalCommutator (G × L))}
    (hblk : ∀ S ∈ supportList L 1 (Fintype.card L), ∀ c ∈ blk S, support slot c = S)
    (hval : ∀ f : G × L → G, evalWord f (expandedWord L xs)
      = ((supportList L 1 (Fintype.card L)).map fun S => evalWord f (blk S)).prod)
    (A : Finset L) :
    (xs.map fun g => g ^ A.card).prod
      = ((supportList L 1 (Fintype.card L)).map
          fun S => if S ⊆ A then blockValue blk S else 1).prod := by
  rw [← evalWord_expandedWord xs A, hval, map_evalWord_blk_eq hblk A]

/-! ## Counting subsets: where the binomial coefficients come from

The support list is the concatenation of its cardinality levels, so the product
above splits level by level.  Inside level `k` only the subsets of `A` survive,
there are `C(|A|, k)` of them, and — once they are known to have a common value —
their ordered product is that value raised to `C(|A|, k)`.
-/

/-- An ordered product over a concatenation of blocks. -/
theorem prod_map_flatMap {α β : Type*} (l : List α) (g : α → List β) (F : β → G) :
    ((l.flatMap g).map F).prod = (l.map fun a => ((g a).map F).prod).prod := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.map_append, List.prod_append, ih]

/-- Entries multiplied by `1` may be dropped from an ordered product. -/
theorem prod_map_ite_eq_prod_filter {α : Type*} (p : α → Prop) [DecidablePred p] (h : α → G)
    (l : List α) :
    (l.map fun a => if p a then h a else 1).prod
      = ((l.filter fun a => decide (p a)).map h).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.prod_cons, ih, List.filter_cons]
      by_cases hp : p a <;> simp [hp]

/-- **The count.**  Among all supports of cardinality `k`, exactly `C(|A|, k)`
are contained in `A`. -/
theorem length_filter_levelList (A : Finset L) (k : ℕ) :
    ((levelList L k).filter fun S => decide (S ⊆ A)).length = A.card.choose k := by
  have hnd : ((levelList L k).filter fun S => decide (S ⊆ A)).Nodup :=
    (nodup_levelList k).filter _
  have htf : ((levelList L k).filter fun S => decide (S ⊆ A)).toFinset = A.powersetCard k := by
    ext S
    simp [levelList, Finset.mem_powersetCard, and_comm]
  rw [← List.toFinset_card_of_nodup hnd, htf, Finset.card_powersetCard]

/-- **One level contributes a binomial power.**  If all the subsets of `A` of
cardinality `k` carry the same value `v`, the level-`k` factor of the collection
formula is `v ^ C(|A|, k)`. -/
theorem prod_level_eq_pow {A : Finset L} {k : ℕ} {F : Finset L → G} {v : G}
    (hF : ∀ S ∈ levelList L k, S ⊆ A → F S = v) :
    ((levelList L k).map fun S => if S ⊆ A then F S else 1).prod = v ^ A.card.choose k := by
  rw [prod_map_ite_eq_prod_filter (· ⊆ A) F,
    List.prod_eq_pow_card _ v ?_, List.length_map, length_filter_levelList]
  intro x hx
  obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_filter] at hS
  exact hF S hS.1 (of_decide_eq_true hS.2)

/-- The collection formula, split into cardinality levels. -/
theorem prod_supportList_eq_levels (F : Finset L → G) (k K : ℕ) :
    ((supportList L k K).map F).prod
      = ((List.range' k K).map fun i => ((levelList L i).map F).prod).prod :=
  prod_map_flatMap _ _ _

/-- Splitting an ordered product over `[1, …, N]` at an index `n` past which all
factors are trivial. -/
theorem prod_range'_split_of_eq_one (F : ℕ → G) {n N : ℕ} (h1 : 1 ≤ n) (hn : n ≤ N)
    (htail : ∀ k, n < k → F k = 1) :
    ((List.range' 1 N).map F).prod = ((List.range' 1 (n - 1)).map F).prod * F n := by
  have hcat : List.range' 1 N = List.range' 1 (n - 1) ++ List.range' n (N - n + 1) := by
    have h := @List.range'_append 1 (n - 1) (N - n + 1) 1
    rw [show 1 + 1 * (n - 1) = n by omega, show n - 1 + (N - n + 1) = N by omega] at h
    exact h.symm
  have htailprod : ((List.range' (n + 1) (N - n)).map F).prod = 1 := by
    refine List.prod_eq_one fun z hz => ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    exact htail k (List.mem_range'_1.mp hk).1
  rw [hcat, List.map_append, List.prod_append,
    show N - n + 1 = (N - n) + 1 from rfl, Nat.add_comm (N - n) 1,
    show (1 : ℕ) + (N - n) = (N - n) + 1 by omega, List.range'_succ, List.map_cons,
    List.prod_cons, htailprod, mul_one]

/-! ## The blocks depend only on the size of their support

This is the heart of Mann's argument.  Reading the collection formula for a slot
set `A` and splitting it at level `|A|` gives

`x₁^{|A|} ⋯ x_m^{|A|} = (levels below |A|) · blockValue A`,

and the left-hand side depends on `A` only through `|A|`.  By induction on `|A|`
the lower levels also depend only on `|A|`, so two sets of the same size force
the same top block.
-/

section BlockValue

variable {xs : List G} {blk : Finset L → List (FormalCommutator (G × L))}

/-- The level-`k` factor of the collection formula for the slot set `B`. -/
private noncomputable def levelFactor (blk : Finset L → List (FormalCommutator (G × L)))
    (B : Finset L) (k : ℕ) : G :=
  ((levelList L k).map fun S => if S ⊆ B then blockValue blk S else 1).prod

/-- **The collection formula, split at the top level.** -/
private theorem prod_pow_eq_levels_mul
    (hblk : ∀ S ∈ supportList L 1 (Fintype.card L), ∀ c ∈ blk S, support slot c = S)
    (hval : ∀ f : G × L → G, evalWord f (expandedWord L xs)
      = ((supportList L 1 (Fintype.card L)).map fun S => evalWord f (blk S)).prod)
    {B : Finset L} {n : ℕ} (hB : B.card = n) (hBne : B.Nonempty) :
    (xs.map fun g => g ^ n).prod
      = ((List.range' 1 (n - 1)).map (levelFactor blk B)).prod * blockValue blk B := by
  have hn1 : 1 ≤ n := hB ▸ Finset.card_pos.mpr hBne
  have hnN : n ≤ Fintype.card L := by
    rw [← hB]; simpa [Finset.card_univ] using Finset.card_le_univ B
  have htail : ∀ k, n < k → levelFactor blk B k = 1 := by
    intro k hk
    refine List.prod_eq_one fun z hz => ?_
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hz
    have hSB : ¬ S ⊆ B := fun hsub => by
      have := Finset.card_le_card hsub
      rw [card_of_mem_levelList hS, hB] at this
      omega
    simp [hSB]
  have htop : levelFactor blk B n = blockValue blk B := by
    have hF : ∀ S ∈ levelList L n, S ⊆ B → blockValue blk S = blockValue blk B := by
      intro S hS hsub
      rw [Finset.eq_of_subset_of_card_le hsub (by rw [card_of_mem_levelList hS, hB])]
    rw [levelFactor, prod_level_eq_pow hF, hB, Nat.choose_self, pow_one]
  have h1 := prod_pow_card_eq hblk hval B
  rw [hB] at h1
  rw [h1, prod_supportList_eq_levels, ← htop]
  exact prod_range'_split_of_eq_one _ hn1 hnN htail

/-- **The key step of Mann's proof.**  A collected block depends only on the
*size* of its support. -/
theorem blockValue_eq_of_card_eq
    (hblk : ∀ S ∈ supportList L 1 (Fintype.card L), ∀ c ∈ blk S, support slot c = S)
    (hval : ∀ f : G × L → G, evalWord f (expandedWord L xs)
      = ((supportList L 1 (Fintype.card L)).map fun S => evalWord f (blk S)).prod) :
    ∀ n : ℕ, ∀ A A' : Finset L, A.card = n → A'.card = n → A.Nonempty → A'.Nonempty →
      blockValue blk A = blockValue blk A' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro A A' hA hA' hAne hA'ne
      have hprefix : ((List.range' 1 (n - 1)).map (levelFactor blk A)).prod
          = ((List.range' 1 (n - 1)).map (levelFactor blk A')).prod := by
        refine congrArg List.prod (List.map_congr_left fun k hk => ?_)
        obtain ⟨hk1, hk2⟩ := List.mem_range'_1.mp hk
        have hkn : k < n := by omega
        obtain ⟨T, hTA, hT⟩ := Finset.exists_subset_card_eq (s := A) (n := k) (by omega)
        obtain ⟨T', hTA', hT'⟩ := Finset.exists_subset_card_eq (s := A') (n := k) (by omega)
        have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
        have hT'ne : T'.Nonempty := Finset.card_pos.mp (by omega)
        have hcommon : ∀ (B T₀ : Finset L), B.card = n → T₀ ⊆ B → T₀.card = k → T₀.Nonempty →
            levelFactor blk B k = blockValue blk T₀ ^ (n.choose k) := by
          intro B T₀ hB hT₀B hT₀ hT₀ne
          have hF : ∀ S ∈ levelList L k, S ⊆ B → blockValue blk S = blockValue blk T₀ := by
            intro S hS _
            exact ih k hkn S T₀ (card_of_mem_levelList hS) hT₀
              (Finset.card_pos.mp (by rw [card_of_mem_levelList hS]; omega)) hT₀ne
          rw [levelFactor, prod_level_eq_pow hF, hB]
        rw [hcommon A T hA hTA hT hTne, hcommon A' T' hA' hTA' hT' hT'ne,
          ih k hkn T T' hT hT' hTne hT'ne]
      have hAeq := prod_pow_eq_levels_mul hblk hval hA hAne
      have hA'eq := prod_pow_eq_levels_mul hblk hval hA' hA'ne
      rw [hAeq, hprefix] at hA'eq
      exact mul_left_cancel hA'eq

end BlockValue

end HallPetresco

end OddOrder.GroupTheory
