/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3Preliminary

/-!
# Peterfalvi Part II, Ch. IV §2, step (11): the sequences `(u_i), (v_i), (d_i)`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §2, p. 125.

Step (11) builds, from a normalized representative `ω` with `f(ω) = (ω y)^ζ`, sequences

  `u₁ = 0`,  `v₁ = α`,  `d₁ = ζ`,
  `u_{i+1} = 1/(α + u_i)`,  `v_{i+1} = v_i + u_{i+1} d_i^{-(1+σ)}`,
  `d_{i+1} = d_i ζ u_{i+1}^{-2τ}`,

carrying the invariant `f(ω(0,u_i)) = (ω(0,v_i))^{d_i}`, and stops when `u_i = α`.

Here the sequence is built in the group, where `stepEleven_step` is the whole content of
one step: a state is a triple `(z, w, d)` — the book's `((0,u_i), (0,v_i), d_i)` — and
the step is

  `z' = s^a`,  `w' = w · (s^a)^{d⁻¹}`,  `d' = d ζ a⁻²`,   where  `s^{a⁻¹} = y z`.

The `a ∈ K` exists exactly when `y z ≠ 1`, which is the book's stopping rule `u_i ≠ α`.
When it does not, `stepElevenNext` leaves the state alone; the invariant is then carried
by *every* index with no side condition, and the book's sequences are the entries before
the first repetition.  (That index is `m − 1` by step (15).)

The book's own formulas are these read off in the coordinates of the standard model:
`s^a = (0, u_{i+1})` forces `a = u_{i+1}^τ`, whence `a⁻² = u_{i+1}^{-2τ}`, and
`(0,u)^{d⁻¹} = (0, d^{-(1+σ)} u)`.

## Main results

* `Hypothesis.stepElevenNext`, `Hypothesis.stepElevenSeq` — the step and the sequence.
* `Hypothesis.exists_mem_K_conj_eq_mul` — the step is available while `y z ≠ 1`.
* `Hypothesis.stepElevenSeq_spec` — the invariant `f(ω z_i) = (ω w_i)^{d_i}`, together
  with `z_i, w_i ∈ Q₀` and `d_i ∈ D`, at every index.
* `Hypothesis.stepElevenSeq_succ_of_ne` — the explicit form of one step, for reading the
  recursion off in coordinates.
* `Hypothesis.stepElevenSeq_coset` — `d_i` lies in the coset `ζ^i K`.
* `Hypothesis.stepEighteen_step`, `Hypothesis.stepEighteen_unroll` — the recursion of
  step (18) for `h` along the same sequence, and its closed form with the `K`-part tied to
  that of `d_i`.
* `Hypothesis.stepElevenSeq_fst_mem_orbitSet`,
  `Hypothesis.stepElevenSeq_pow_ne_one`, `Hypothesis.exists_stop_lt_orderOf` — the
  length half of step (15): the sequence lies in the set step (8) counts, so its `d_i`
  never lie in `K`, so it must stop before `ζ^i` returns to `1`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

/-- **The step of the recursion (11) is available exactly while `u_i ≠ α`**
(Peterfalvi Part II, p. 125): for `z ∈ Q₀` with `y z ≠ 1` there is an `a ∈ K` with
`s^{a⁻¹} = y z`.

`K` is transitive on `Q₀^#` with base point `s` (`exists_mem_KSet_conj_eq_of_mem_Q0`),
so the only obstruction is `y z = 1`. -/
theorem exists_mem_K_conj_eq_mul {y z : G} (hyQ0 : y ∈ hyp.Q0) (hzQ0 : z ∈ hyp.Q0)
    (hne : y * z ≠ 1) :
    ∃ a ∈ hyp.K, a * hyp.distinguishedInvolution * a⁻¹ = y * z := by
  obtain ⟨b, hbKSet, hb⟩ :=
    hyp.exists_mem_KSet_conj_eq_of_mem_Q0 (hyp.Q0.mul_mem hyQ0 hzQ0) hne
  refine ⟨b⁻¹, ?_, ?_⟩
  · have hmem : b⁻¹ ∈ (hyp.K : Set G) := by
      rw [hyp.coe_K]
      exact hyp.inv_mem_KSet hbKSet
    exact hmem
  · rwa [inv_inv]

open Classical in
/-- **One step of the recursion (11)** (Peterfalvi Part II, p. 125), as an operation on
states.

A state `(z, w, d)` stands for the book's `((0,u_i), (0,v_i), d_i)` and carries the
invariant `f(ω z) = (ω w)^d`.  Choosing `a ∈ K` with `s^{a⁻¹} = y z`, step (10) advances
it to `(s^a, w · (s^a)^{d⁻¹}, d ζ a⁻²)`.

If no such `a` exists — the book's stopping rule `u_i = α` — the state is returned
unchanged, which is what lets `stepElevenSeq_spec` hold at every index. -/
noncomputable def stepElevenNext (ζ y : G) (T : G × G × G) : G × G × G :=
  if hex : ∃ a ∈ hyp.K, a * hyp.distinguishedInvolution * a⁻¹ = y * T.1 then
    ((hex.choose)⁻¹ * hyp.distinguishedInvolution * hex.choose,
      T.2.1 * (T.2.2 * ((hex.choose)⁻¹ * hyp.distinguishedInvolution * hex.choose) *
        T.2.2⁻¹),
      T.2.2 * ζ * ((hex.choose)⁻¹) ^ 2)
  else T

/-- **The sequence of states of (11)** (Peterfalvi Part II, p. 125), started at
`(1, y, ζ)` — the book's `u₁ = 0`, `v₁ = α`, `d₁ = ζ`. -/
noncomputable def stepElevenSeq (ζ y : G) (i : ℕ) : G × G × G :=
  Nat.rec (1, y, ζ) (fun _ T => hyp.stepElevenNext ζ y T) i

@[simp] theorem stepElevenSeq_zero (ζ y : G) :
    hyp.stepElevenSeq ζ y 0 = (1, y, ζ) := rfl

@[simp] theorem stepElevenSeq_succ (ζ y : G) (i : ℕ) :
    hyp.stepElevenSeq ζ y (i + 1)
      = hyp.stepElevenNext ζ y (hyp.stepElevenSeq ζ y i) := rfl

/-- **The explicit form of one step**, for reading the recursion off in coordinates: as
long as the stopping condition has not been reached, the next state is
`(s^a, w · (s^a)^{d⁻¹}, d ζ a⁻²)` for an `a ∈ K` with `s^{a⁻¹} = y z`.

The book's `u_{i+1} = 1/(α + u_i)` is the coordinate of `s^a`, its `d_{i+1} = d_i ζ
u_{i+1}^{-2τ}` the third component (`a = u_{i+1}^τ`), and its
`v_{i+1} = v_i + u_{i+1}d_i^{-(1+σ)}` the second. -/
theorem stepElevenSeq_succ_of_ne (ζ y : G) (i : ℕ)
    (hex : ∃ a ∈ hyp.K, a * hyp.distinguishedInvolution * a⁻¹
      = y * (hyp.stepElevenSeq ζ y i).1) :
    ∃ a ∈ hyp.K, a * hyp.distinguishedInvolution * a⁻¹
        = y * (hyp.stepElevenSeq ζ y i).1 ∧
      hyp.stepElevenSeq ζ y (i + 1)
        = (a⁻¹ * hyp.distinguishedInvolution * a,
            (hyp.stepElevenSeq ζ y i).2.1 *
              ((hyp.stepElevenSeq ζ y i).2.2 *
                (a⁻¹ * hyp.distinguishedInvolution * a) *
                (hyp.stepElevenSeq ζ y i).2.2⁻¹),
            (hyp.stepElevenSeq ζ y i).2.2 * ζ * (a⁻¹) ^ 2) := by
  classical
  refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
  rw [hyp.stepElevenSeq_succ, stepElevenNext, dif_pos hex]

/-- The entries of the sequence stay where they should: `z_i, w_i ∈ Q₀` and `d_i ∈ D`.

This needs neither `f` nor step (10) — only that `K ≤ D` normalizes `Q₀` and that
`ζ ∈ W ≤ V ≤ D`. -/
theorem stepElevenSeq_mem {ζ y : G} (hζ : ζ ∈ hyp.W) (hyQ0 : y ∈ hyp.Q0) (i : ℕ) :
    (hyp.stepElevenSeq ζ y i).1 ∈ hyp.Q0 ∧ (hyp.stepElevenSeq ζ y i).2.1 ∈ hyp.Q0 ∧
      (hyp.stepElevenSeq ζ y i).2.2 ∈ hyp.D := by
  classical
  have hsQ0 : hyp.distinguishedInvolution ∈ hyp.Q0 :=
    ⟨hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_mem_H⟩
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζ)
  induction i with
  | zero => exact ⟨hyp.Q0.one_mem, hyQ0, hζD⟩
  | succ k ih =>
    obtain ⟨hz, hw, hd⟩ := ih
    rw [hyp.stepElevenSeq_succ, stepElevenNext]
    by_cases hex : ∃ a ∈ hyp.K, a * hyp.distinguishedInvolution * a⁻¹
        = y * (hyp.stepElevenSeq ζ y k).1
    · rw [dif_pos hex]
      have haD : hex.choose ∈ hyp.D := hyp.K_le_D hex.choose_spec.1
      have hsa : (hex.choose)⁻¹ * hyp.distinguishedInvolution * hex.choose ∈ hyp.Q0 := by
        have hmem := hyp.conj_mem_Q0_of_mem_D (hyp.D.inv_mem haD) hsQ0
        rwa [inv_inv] at hmem
      exact ⟨hsa, hyp.Q0.mul_mem hw (hyp.conj_mem_Q0_of_mem_D hd hsa),
        hyp.D.mul_mem (hyp.D.mul_mem hd hζD) (pow_mem (hyp.D.inv_mem haD) 2)⟩
    · rw [dif_neg hex]
      exact ⟨hz, hw, hd⟩

/-- **Step (11)** (Peterfalvi Part II, p. 125): the sequence carries the invariant

  `f(ω z_i) = (ω w_i)^{d_i}`

at every index.

The base case is the normalization `f(ω) = (ω y)^ζ` itself, and the step is
`stepEleven_step`; where the book's sequence stops, `stepElevenNext` repeats the state,
so nothing has to be said about the length here.

Together with `stepElevenSeq_mem` this puts every `z_i` into the set of `x ∈ Q₀` whose
`f(ω x)` lies in the `D`-orbit of `ω` modulo `Q₀` — the set counted by step (8). -/
theorem stepElevenSeq_spec (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) (i : ℕ) :
    f (ω * (hyp.stepElevenSeq ζ y i).1)
      = ((hyp.stepElevenSeq ζ y i).2.2)⁻¹ *
          (ω * (hyp.stepElevenSeq ζ y i).2.1) * (hyp.stepElevenSeq ζ y i).2.2 := by
  classical
  induction i with
  | zero =>
    rw [hyp.stepElevenSeq_zero]
    simpa using hfω
  | succ k ih =>
    rw [hyp.stepElevenSeq_succ, stepElevenNext]
    by_cases hex : ∃ a ∈ hyp.K, a * hyp.distinguishedInvolution * a⁻¹
        = y * (hyp.stepElevenSeq ζ y k).1
    · rw [dif_pos hex]
      obtain ⟨haK, ha⟩ := hex.choose_spec
      exact hyp.stepEleven_step H hC2 hζ hωQ hωQ0 hyQ0 haK hfω ha ih
    · rw [dif_neg hex]
      exact ih

/-- **The `K`-coset of `d_i` is `ζ^i K`** (Peterfalvi Part II, p. 126, behind step (15)).

Each step multiplies `d` by `ζ` and by a square from `K`, and `ζ` centralizes `K`, so
the coset advances by exactly one power of `ζ` per step, starting from `d₁ = ζ`.

This is what turns step (7)'s injection `x ↦ a_x K` into the length count: the cosets
`ζ^i K` are pairwise distinct because `K ∩ W = 1`, and step (8) forbids the trivial one,
so the sequence can run only while `ζ^i ≠ 1`, i.e. for `i ≤ m − 1`. -/
theorem stepElevenSeq_coset {ζ y : G} (hζ : ζ ∈ hyp.W) (hyQ0 : y ∈ hyp.Q0) (n : ℕ)
    (hns : ∀ i < n, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1) :
    ∃ k ∈ hyp.K, (hyp.stepElevenSeq ζ y n).2.2 = ζ ^ (n + 1) * k := by
  classical
  induction n with
  | zero => exact ⟨1, hyp.K.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨k, hkK, hk⟩ := ih fun i hi => hns i (by omega)
    have hex : ∃ a ∈ hyp.K, a * hyp.distinguishedInvolution * a⁻¹
        = y * (hyp.stepElevenSeq ζ y n).1 :=
      hyp.exists_mem_K_conj_eq_mul hyQ0 (hyp.stepElevenSeq_mem hζ hyQ0 n).1
        (hns n (by omega))
    obtain ⟨a, haK, -, hstep⟩ := hyp.stepElevenSeq_succ_of_ne ζ y n hex
    have hcomm : k * ζ = ζ * k := hyp.commute_of_mem_W_of_mem_K hζ hkK
    refine ⟨k * (a⁻¹) ^ 2, hyp.K.mul_mem hkK (pow_mem (hyp.K.inv_mem haK) 2), ?_⟩
    rw [hstep]
    change (hyp.stepElevenSeq ζ y n).2.2 * ζ * (a⁻¹) ^ 2
      = ζ ^ (n + 1 + 1) * (k * (a⁻¹) ^ 2)
    rw [hk]
    calc ζ ^ (n + 1) * k * ζ * (a⁻¹) ^ 2
        = ζ ^ (n + 1) * (k * ζ) * (a⁻¹) ^ 2 := by group
      _ = ζ ^ (n + 1) * (ζ * k) * (a⁻¹) ^ 2 := by rw [hcomm]
      _ = ζ ^ (n + 1 + 1) * (k * (a⁻¹) ^ 2) := by rw [pow_succ]; group

/-- **Every `z_i` is one of the elements step (8) counts** (Peterfalvi Part II, p. 126,
step (15)): the invariant of (11) is literally the membership condition of the set whose
cardinality step (8) computes, taken at `ω' = ω`.

Step (15)'s assertion that the `u ∈ F` with `f(ω(0,u))` in the `KW`-orbit of `ω̄` are
exactly the `u_i` is the statement that this inclusion is an equality; the count on the
right is `|W| − 1` (`ncard_eq_card_W_sub_one_of_f_eq_conj_self`). -/
theorem stepElevenSeq_fst_mem_orbitSet (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) (i : ℕ) :
    (hyp.stepElevenSeq ζ y i).1 ∈ {x : G | x ∈ hyp.Q0 ∧ ∃ w ∈ hyp.Q0, ∃ a ∈ hyp.D,
      f (ω * x) = a⁻¹ * (ω * w) * a} := by
  obtain ⟨hz, hw, hd⟩ := hyp.stepElevenSeq_mem hζ hyQ0 i
  exact ⟨hz, _, hw, _, hd, hyp.stepElevenSeq_spec H hC2 hζ hωQ hωQ0 hyQ0 hfω i⟩

/-- **The sequence runs only while `ζ^i ≠ 1`** (Peterfalvi Part II, p. 126, step (15)).

Step (8)'s sharpening `not_mem_K_of_f_eq_conj_self` says the conjugator in
`f(ω x) = (ω y)^a` — with the *same* `ω` on both sides, which is exactly the invariant of
(11) — never lies in `K`.  Since `d_i` lies in the coset `ζ^i K`, that forbids
`ζ^i = 1`. -/
theorem stepElevenSeq_pow_ne_one (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) (n : ℕ)
    (hns : ∀ i < n, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1) :
    ζ ^ (n + 1) ≠ 1 := by
  intro hpow
  obtain ⟨k, hkK, hk⟩ := hyp.stepElevenSeq_coset hζ hyQ0 n hns
  obtain ⟨hz, hw, hd⟩ := hyp.stepElevenSeq_mem hζ hyQ0 n
  refine hyp.not_mem_K_of_f_eq_conj_self H hC2 hωQ hωQ0 hz hw hd
    (hyp.stepElevenSeq_spec H hC2 hζ hωQ hωQ0 hyQ0 hfω n) ?_
  rw [hk, hpow, one_mul]
  exact hkK

/-- **The sequence stops within `m − 1` steps** (Peterfalvi Part II, p. 126, step (15)):
the stopping rule `u_i = α` is reached at some index below `orderOf ζ − 1`.

With `ζ` a generator of `W`, `orderOf ζ` is `m = |W|`, so — with this file's indexing,
which is the book's shifted by one — the book's sequences run for `1 ≤ i ≤ m − 1` and no
further, which is the length assertion of step (15). -/
theorem exists_stop_lt_orderOf (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) :
    ∃ i < orderOf ζ - 1, y * (hyp.stepElevenSeq ζ y i).1 = 1 := by
  by_contra hcon
  push Not at hcon
  refine hyp.stepElevenSeq_pow_ne_one H hC2 hζ hωQ hωQ0 hyQ0 hfω (orderOf ζ - 1) hcon ?_
  rw [Nat.sub_add_cancel (orderOf_pos ζ)]
  exact pow_orderOf_eq_one ζ

/-! ## Step (18): the recursion for `h` along the same sequence (p. 127)

Step (18) proves `(h(ω)ζ⁻¹)^m = 1` by running (H6) along the sequence of (11).  Its
first display,

  `h(ω(0,u_i)) = h(ω) h((ω(0,α))^ζ(0,u_i⁻¹)) u_i^{2τ}
              = h(ω) h(ω(0,u_{i-1}))^ζ u_i = (h(ω)ζ⁻¹) h(ω(0,u_{i-1})) (ζ u_i)`,

is `stepEighteen_step` below.  The `(0,u_{i-1})` in the middle is not an accident of the
coordinates: the step of (11) picks `a ∈ K` with `s^{a⁻¹} = y z_{i-1}`, so
`y · s^{a⁻¹} = z_{i-1}` exactly, `y` being an involution.
-/

/-- **The recursion of step (18)** (Peterfalvi Part II, p. 127): along one step of (11),

  `h(ω s^a) = h(ω) · h(ω z)^ζ · a²`,   where `s^{a⁻¹} = y z`.

This is (H6) at `x = ω`, `y = s^a`, with step (1) supplying `g(s^a) = s^{a⁻¹}` and
`h(s^a) = a²`, and (H4) pulling the `ζ` of the normalization `f(ω) = (ω y)^ζ` back out
of `h`; the twist `ζ^t` is `ζ` because `ζ ∈ W ≤ V` centralizes `t`.

The book's `a² = u_i^{2τ}` is the coordinate reading of the last factor, and its
`(h(ω)ζ⁻¹)h(ω(0,u_{i-1}))(ζu_i)` is this regrouped. -/
theorem stepEighteen_step (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ζ ω y z a : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hzQ0 : z ∈ hyp.Q0) (haK : a ∈ hyp.K)
    (hfω : f ω = ζ⁻¹ * (ω * y) * ζ)
    (ha : a * hyp.distinguishedInvolution * a⁻¹ = y * z) :
    h (ω * (a⁻¹ * hyp.distinguishedInvolution * a))
      = h ω * (ζ⁻¹ * h (ω * z) * ζ) * a ^ 2 := by
  have hsQ0 : hyp.distinguishedInvolution ∈ hyp.Q0 :=
    ⟨hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_mem_H⟩
  have haKSet : a ∈ hyp.KSet := by
    have hx : a ∈ (hyp.K : Set G) := haK
    rwa [hyp.coe_K] at hx
  have haD : a ∈ hyp.D := hyp.K_le_D haK
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζ)
  have hsa : a⁻¹ * hyp.distinguishedInvolution * a ∈ hyp.Q0 := by
    have hmem := hyp.conj_mem_Q0_of_mem_D (hyp.D.inv_mem haD) hsQ0
    rwa [inv_inv] at hmem
  have hsainv : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D haD hsQ0
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  obtain ⟨-, hωsaQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hsa
  have hωsa1 : ω * (a⁻¹ * hyp.distinguishedInvolution * a) ≠ 1 :=
    fun hc => hωsaQ0 (hc ▸ hyp.Q0.one_mem)
  obtain ⟨hωzQ, hωzQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hzQ0
  have hωz1 : ω * z ≠ 1 := fun hc => hωzQ0 (hc ▸ hyp.Q0.one_mem)
  have hsaQ : a⁻¹ * hyp.distinguishedInvolution * a ∈ hyp.Q :=
    hyp.rankOneSetup.DQ a haD _ hyp.distinguishedInvolution_mem_Q
  obtain ⟨-, -, -, e6⟩ := hSix hyp.rankOneSetup H hωQ hω1 hsaQ
    (hyp.conj_distinguishedInvolution_ne_one a) hωsa1
  obtain ⟨-, hg1, hh1⟩ := hyp.fgh_at_conj_distinguishedInvolution H hC2 haKSet
  rw [e6, hg1, hh1]
  have hy2 : y * y = 1 := by
    have hsq := hyQ0.1
    rwa [sq] at hsq
  have hζc : ζ * (a * hyp.distinguishedInvolution * a⁻¹)
      = (a * hyp.distinguishedInvolution * a⁻¹) * ζ := hyp.W_centralizes_Q0 hζ hsainv
  have harg : f ω * (a * hyp.distinguishedInvolution * a⁻¹) = ζ⁻¹ * (ω * z) * ζ := by
    rw [hfω]
    calc ζ⁻¹ * (ω * y) * ζ * (a * hyp.distinguishedInvolution * a⁻¹)
        = ζ⁻¹ * (ω * y) * (ζ * (a * hyp.distinguishedInvolution * a⁻¹)) := by group
      _ = ζ⁻¹ * (ω * y) * ((a * hyp.distinguishedInvolution * a⁻¹) * ζ) := by rw [hζc]
      _ = ζ⁻¹ * (ω * (y * (a * hyp.distinguishedInvolution * a⁻¹))) * ζ := by group
      _ = ζ⁻¹ * (ω * (y * (y * z))) * ζ := by rw [ha]
      _ = ζ⁻¹ * (ω * z) * ζ := by rw [← mul_assoc y y z, hy2, one_mul]
  rw [harg]
  obtain ⟨-, -, e4⟩ := hThree hyp.rankOneSetup H hωzQ hωz1 hζD
  have htζt : hyp.t * ζ * hyp.t = ζ := by
    have hc := hyp.commute_t_of_mem_V (hyp.W_le_V hζ)
    rw [← hc.eq, mul_assoc, hyp.rankOneSetup.invol, mul_one]
  rw [e4, htζt]

/-- **The closed form of step (18)** (Peterfalvi Part II, p. 127):

  `h(ω z_i) = (h(ω)ζ⁻¹)^i · h(ω) · (ζ^i k⁻¹)`,   where `d_i = ζ^{i+1} k`, `k ∈ K`.

Unrolling `stepEighteen_step` collects one `h(ω)ζ⁻¹` on the left and one `ζ a²` on the
right per step, and `ζ` centralizes `K`, so the `ζ`'s gather into `ζ^i` and the squares
into a single element of `K`.

The element accumulated here is the *inverse* of the one accumulated by
`stepElevenSeq_coset` — each step contributes `a²` to the first and `a⁻²` to the second —
so the two are recorded together: that is what lets step (15)'s `k = 1` be fed straight
into step (18).  The book's own bookkeeping is the closed form
`(α/(β^i + β^{-i}))^{2τ}` for the `K`-part of `d_i`, which at `i = m − 1` is `1` because
`c_{m-1} = α`.

The book's display

  `h(ω(0,u_i)) = (h(ω)ζ⁻¹)^i ζ^i (α/(β^i + β^{-i}))`

differs only in having `h(ω)` absorbed, `h(ω(0,u_1)) = h(ω)` being the base case. -/
theorem stepEighteen_unroll (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) (n : ℕ)
    (hns : ∀ i < n, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1) :
    ∃ k ∈ hyp.K, (hyp.stepElevenSeq ζ y n).2.2 = ζ ^ (n + 1) * k ∧
      h (ω * (hyp.stepElevenSeq ζ y n).1)
        = (h ω * ζ⁻¹) ^ n * h ω * (ζ ^ n * k⁻¹) := by
  induction n with
  | zero =>
    refine ⟨1, hyp.K.one_mem, by simp, ?_⟩
    rw [hyp.stepElevenSeq_zero]
    simp
  | succ n ih =>
    obtain ⟨k, hkK, hkcoset, hk⟩ := ih fun i hi => hns i (by omega)
    have hz : (hyp.stepElevenSeq ζ y n).1 ∈ hyp.Q0 := (hyp.stepElevenSeq_mem hζ hyQ0 n).1
    obtain ⟨a, haK, ha, hstep⟩ :=
      hyp.stepElevenSeq_succ_of_ne ζ y n
        (hyp.exists_mem_K_conj_eq_mul hyQ0 hz (hns n (by omega)))
    have hfst : (hyp.stepElevenSeq ζ y (n + 1)).1
        = a⁻¹ * hyp.distinguishedInvolution * a := by rw [hstep]
    have hcomm : k * ζ = ζ * k := hyp.commute_of_mem_W_of_mem_K hζ hkK
    have hkinv : k⁻¹ * ζ = ζ * k⁻¹ :=
      hyp.commute_of_mem_W_of_mem_K hζ (hyp.K.inv_mem hkK)
    refine ⟨k * (a⁻¹) ^ 2, hyp.K.mul_mem hkK (pow_mem (hyp.K.inv_mem haK) 2), ?_, ?_⟩
    · rw [hstep]
      change (hyp.stepElevenSeq ζ y n).2.2 * ζ * (a⁻¹) ^ 2
        = ζ ^ (n + 1 + 1) * (k * (a⁻¹) ^ 2)
      rw [hkcoset]
      calc ζ ^ (n + 1) * k * ζ * (a⁻¹) ^ 2
          = ζ ^ (n + 1) * (k * ζ) * (a⁻¹) ^ 2 := by group
        _ = ζ ^ (n + 1) * (ζ * k) * (a⁻¹) ^ 2 := by rw [hcomm]
        _ = ζ ^ (n + 1 + 1) * (k * (a⁻¹) ^ 2) := by rw [pow_succ]; group
    · have hinvprod : (k * (a⁻¹) ^ 2)⁻¹ = k⁻¹ * a ^ 2 := by
        have hcm := hyp.commute_of_mem_K (hyp.K.inv_mem hkK) (pow_mem haK 2)
        rw [mul_inv_rev, hcm]
        congr 1
        group
      rw [hfst, hyp.stepEighteen_step H hC2 hζ hωQ hωQ0 hyQ0 hz haK hfω ha, hk,
        pow_succ' (h ω * ζ⁻¹) n, pow_succ ζ n, hinvprod]
      calc h ω * (ζ⁻¹ * ((h ω * ζ⁻¹) ^ n * h ω * (ζ ^ n * k⁻¹)) * ζ) * a ^ 2
          = (h ω * ζ⁻¹) * (h ω * ζ⁻¹) ^ n * h ω * (ζ ^ n * (k⁻¹ * ζ)) * a ^ 2 := by group
        _ = (h ω * ζ⁻¹) * (h ω * ζ⁻¹) ^ n * h ω * (ζ ^ n * (ζ * k⁻¹)) * a ^ 2 := by
            rw [hkinv]
        _ = (h ω * ζ⁻¹) * (h ω * ζ⁻¹) ^ n * h ω * (ζ ^ n * ζ * (k⁻¹ * a ^ 2)) := by group

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
