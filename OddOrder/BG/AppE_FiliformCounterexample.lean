/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.FinCases

/-!
# BG Proposition E.4 is false as printed: the Lie-ring core of the counterexample

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, Proposition E.4 (p. 162) and display `(E.23)` (p. 163).

**Proposition E.4 as printed is false.**  This leaf machine-checks the mathematical core of
the counterexample found on 2026-07-21 (issue 3021 (53)/(54), master note
`notes/bg/appE_e4_counterexample_2026_07_21.md`): the *exceptional* filiform Lie ring `Q₆`
(Vergne) over `𝔽₁₉₇`, whose Lazard group satisfies every printed hypothesis of
Theorem E.3 + Proposition E.4 while violating E.4's conclusion that `C_S(Z₂(S))` is abelian.
The missing hypothesis is that `S` is **non-exceptional** in the sense of
Leedham-Green–McKay (equivalently: positive degree of commutativity; equivalently: all
two-step centralizers coincide), which is exactly what BG's unproved display `(E.23)`
(*"Similarly one can show"*) needs.  Appendix E is unpublished work of Feit and Thompson
(BG, preface), so no published original exists to consult.

## What is machine-checked here

Everything lives on the explicit 6-dimensional space `V = Fin 6 → ZMod 197` with basis
`a, b, e₂, e₃, e₄, e₅` (indices `0`–`5`) and the bracket `br` with the five nonzero products

`[a,b] = e₂,  [b,e₂] = e₃,  [b,e₃] = e₄,  [a,e₄] = e₅,  [e₂,e₃] = e₅`.

* `br_leibniz` / `br_self` / bilinearity — `br` is a genuine Lie bracket (**Jacobi holds**;
  this is the single most fragile claim of the counterexample and the reason this leaf
  exists).
* `lcs_five_eq_bot`, `e5_mem_lcs_four` — the lower central series has shape
  `6, 4, 3, 2, 1, 0`: nilpotency class exactly `5` (maximal class, and `5 < p = 197`).
* `degree_of_commutativity_zero` — `[γ₂, γ₃] ≠ 0` while `γ₆ = ⊥`: the degree of
  commutativity is `0`, i.e. `Q₆` is exceptional.
* `br_beta` / `beta_iterate_card` / `beta_iterate_fixed_eq_zero` — the diagonal map `β`
  with eigenvalues `ζ^(1,8,9,17,25,26)`, `ζ = 16` of order `49`, is a bracket automorphism
  generating `B ≅ C₄₉` acting **fixed-point-freely** (the "B acts regularly" hypothesis).
* `centralizer_v_iff` — `C_L(v) = K·v ⊕ K·e₅` for `v = a + b`: Theorem E.3's hypothesis
  `C_R(R₀) = R₀ × R₁` (with `R₀ = Exp(K·v)` of order `p`, `R₁ = Exp(K·e₅)` cyclic).
* `alpha_smul_v` — `α = β^[7]` (order `7 = q`) acts on `K·v` as the scalar `ζ⁷`:
  "A fixes `R₀`", with `A = ⟨α⟩ ≤ B` of prime order `q = 7 ≠ p`, `p ∤ |B| = 49`.
* `beta_not_fixes_v` — `β` does *not* fix `K·v`: Proposition E.4's hypothesis
  "B does not fix `R₀`".
* `memT_iff` + `T_not_abelian` — `T := C_L(Z₂(L)) = {x | x 0 = 0}` is a **hyperplane**
  (the index-`p` clause of E.4, which does survive) that is **not abelian**:
  `b, e₂ ∈ T` but `[b, e₂] = e₃ ≠ 0`.  This refutes E.4's abelian clause.
* `e23_fails_at_two` — BG's display `(E.23)` predicts `β`-eigenvalue `t₀t² = ζ¹⁰` on the
  chain element `w₂ = [[b,v],v]`; the actual eigenvalue is `ζ¹⁷ ≠ ζ¹⁰`.  This locates the
  precise false step in BG's proof sketch.
* `bg_propE4_lie_counterexample` — headline bundle of the above.

## What is *not* machine-checked (deliberate)

The transfer from this Lie ring to its **Lazard group** `S = Exp(L)` (an exponent-`p`
group of order `p⁶` and class `5 < p`, with `γᵢ(S) = Exp(γᵢ(L))`, corresponding
automorphisms, centralizers and upper central series) is the classical Lazard
correspondence for class `< p` and is left as prose — see the master note.  A full
group-level refutation (constructing `S` as an iterated `SemidirectProduct` and
instantiating `RegularOperatorSetup`) is recorded as a follow-up in issue 3021 (55).

Design note: we deliberately do **not** register a `LieRing` instance on `V`.  `V` is a
Pi type of commutative rings, so mathlib already endows it with the *commutator* bracket
(`Ring.instBracket`, identically zero here); registering a second bracket instance would
create a diamond.  The named lemmas `br_leibniz`, `br_self`, `br_add_left`, … carry the
full Lie-ring content without the typeclass.
-/

namespace OddOrder.BG.AppE.Filiform

/-- The prime field `𝔽₁₉₇`.  `p = 197` is the least prime `≡ 1 (mod 49)`, which is what
lets the order-`49` grading automorphism act diagonally with split eigenvalues. -/
abbrev K : Type := ZMod 197

/-- The underlying 6-dimensional coordinate space of the Lie ring `Q₆`. -/
abbrev V : Type := Fin 6 → K

instance : Fact (Nat.Prime 197) := ⟨by norm_num⟩

/-! ### The bracket and its Lie-ring axioms -/

/-- The `Q₆` bracket in coordinates `(a, b, e₂, e₃, e₄, e₅) = (0, …, 5)`.  The five
structure products are `[a,b] = e₂`, `[b,e₂] = e₃`, `[b,e₃] = e₄`, `[a,e₄] = e₅`,
`[e₂,e₃] = e₅`; the last one is the exceptional product that makes the degree of
commutativity zero, and the whole point of the leaf is that Jacobi tolerates it. -/
def br (x y : V) : V := fun k =>
  if k = 2 then x 0 * y 1 - x 1 * y 0
  else if k = 3 then x 1 * y 2 - x 2 * y 1
  else if k = 4 then x 1 * y 3 - x 3 * y 1
  else if k = 5 then (x 0 * y 4 - x 4 * y 0) + (x 2 * y 3 - x 3 * y 2)
  else 0

theorem br_add_left (x x' y : V) : br (x + x') y = br x y + br x' y := by
  funext k
  fin_cases k <;> simp [br] <;> ring

theorem br_add_right (x y y' : V) : br x (y + y') = br x y + br x y' := by
  funext k
  fin_cases k <;> simp [br] <;> ring

theorem br_smul_left (c : K) (x y : V) : br (c • x) y = c • br x y := by
  funext k
  fin_cases k <;> simp [br] <;> ring

theorem br_smul_right (c : K) (x y : V) : br x (c • y) = c • br x y := by
  funext k
  fin_cases k <;> simp [br] <;> ring

theorem br_self (x : V) : br x x = 0 := by
  funext k
  fin_cases k <;> simp [br] <;> ring

theorem br_antisymm (x y : V) : br x y = -br y x := by
  funext k
  fin_cases k <;> simp [br] <;> ring

/-- **The Jacobi identity** (in Leibniz form), the delicate claim of the whole
counterexample: the exceptional product `[e₂,e₃] = e₅` is *compatible* with Jacobi — the
only nontrivial triple is `(a, b, e₃)`, where `[a,[b,e₃]] = [a,e₄] = e₅` is cancelled by
`[e₃,[a,b]] = [e₃,e₂] = -e₅`. -/
theorem br_leibniz (x y z : V) : br x (br y z) = br (br x y) z + br y (br x z) := by
  funext k
  fin_cases k <;> simp [br] <;> ring

/-! ### Basis vectors and the distinguished elements -/

/-- `a`: the first generator (uniserial direction). -/
def eA : V := fun k => if k = 0 then 1 else 0

/-- `b`: the second generator (the `T`-direction, eigenvalue `t₀ = ζ⁸`). -/
def eB : V := fun k => if k = 1 then 1 else 0

/-- `e₂` spans `γ₂/γ₃`. -/
def e2 : V := fun k => if k = 2 then 1 else 0

/-- `e₃` spans `γ₃/γ₄`. -/
def e3 : V := fun k => if k = 3 then 1 else 0

/-- `e₄` spans `γ₄/γ₅`; together with `e₅` it spans `Z₂(L)`. -/
def e4 : V := fun k => if k = 4 then 1 else 0

/-- `e₅` spans the centre `Z(L) = γ₅`; `R₁ = Exp(K·e₅)` in Theorem E.3's notation. -/
def e5 : V := fun k => if k = 5 then 1 else 0

/-- `v = a + b`: the generator of `R₀ = Exp(K·v)`, the order-`p` subgroup of
Theorem E.3.  It has to sit *diagonally* across the two `β`-eigenlines — that is exactly
why `B = ⟨β⟩` does not fix `R₀` while `A = ⟨β⁷⟩` (scalar on `L₁`) does. -/
def v : V := fun k => if k = 0 then 1 else if k = 1 then 1 else 0

/-! ### The lower central series: class exactly `5`, degree of commutativity `0`

`lcs n` is `γ_{n+1}(L)` in textbook numbering (`lcs 0 = γ₁ = L`). -/

/-- Lower central series, `lcs n = γ_{n+1}(L)`. -/
def lcs : ℕ → Submodule K V
  | 0 => ⊤
  | n + 1 => Submodule.span K {z | ∃ x y, y ∈ lcs n ∧ z = br x y}

theorem lcs_succ (n : ℕ) :
    lcs (n + 1) = Submodule.span K {z | ∃ x y, y ∈ lcs n ∧ z = br x y} := rfl

/-- The coordinate-vanishing submodule `{x | ∀ i ∈ s, x i = 0}`. -/
def coordVanish (s : Finset (Fin 6)) : Submodule K V where
  carrier := {x | ∀ i ∈ s, x i = 0}
  add_mem' := fun ha hb i hi => by rw [Pi.add_apply, ha i hi, hb i hi, add_zero]
  zero_mem' := fun i _ => rfl
  smul_mem' := fun c x hx i hi => by rw [Pi.smul_apply, hx i hi, smul_zero]

theorem mem_coordVanish {s : Finset (Fin 6)} {x : V} :
    x ∈ coordVanish s ↔ ∀ i ∈ s, x i = 0 := Iff.rfl

theorem lcs_one_le : lcs 1 ≤ coordVanish {0, 1} := by
  rw [lcs_succ, Submodule.span_le]
  rintro z ⟨x, y, -, rfl⟩ i hi
  fin_cases hi <;> simp [br]

theorem lcs_two_le : lcs 2 ≤ coordVanish {0, 1, 2} := by
  rw [lcs_succ, Submodule.span_le]
  rintro z ⟨x, y, hy, rfl⟩ i hi
  have h0 := lcs_one_le hy 0 (by decide)
  have h1 := lcs_one_le hy 1 (by decide)
  fin_cases hi <;> simp [br, h0, h1]

theorem lcs_three_le : lcs 3 ≤ coordVanish {0, 1, 2, 3} := by
  rw [lcs_succ, Submodule.span_le]
  rintro z ⟨x, y, hy, rfl⟩ i hi
  have h0 := lcs_two_le hy 0 (by decide)
  have h1 := lcs_two_le hy 1 (by decide)
  have h2 := lcs_two_le hy 2 (by decide)
  fin_cases hi <;> simp [br, h0, h1, h2]

theorem lcs_four_le : lcs 4 ≤ coordVanish {0, 1, 2, 3, 4} := by
  rw [lcs_succ, Submodule.span_le]
  rintro z ⟨x, y, hy, rfl⟩ i hi
  have h0 := lcs_three_le hy 0 (by decide)
  have h1 := lcs_three_le hy 1 (by decide)
  have h2 := lcs_three_le hy 2 (by decide)
  have h3 := lcs_three_le hy 3 (by decide)
  fin_cases hi <;> simp [br, h0, h1, h2, h3]

/-- `γ₆(L) = 0`: the class is at most `5` — in particular `< p = 197`, which is what the
(prose) Lazard transfer to an exponent-`p` group needs. -/
theorem lcs_five_eq_bot : lcs 5 = ⊥ := by
  rw [eq_bot_iff, lcs_succ, Submodule.span_le]
  rintro z ⟨x, y, hy, rfl⟩
  have h0 := lcs_four_le hy 0 (by decide)
  have h1 := lcs_four_le hy 1 (by decide)
  have h2 := lcs_four_le hy 2 (by decide)
  have h3 := lcs_four_le hy 3 (by decide)
  have h4 := lcs_four_le hy 4 (by decide)
  have hz : br x y = 0 := by
    funext k
    fin_cases k <;> simp [br, h0, h1, h2, h3, h4]
  simp [hz]

theorem e2_mem_lcs_one : e2 ∈ lcs 1 :=
  Submodule.subset_span ⟨eA, eB, Submodule.mem_top, by decide⟩

theorem e3_mem_lcs_two : e3 ∈ lcs 2 :=
  Submodule.subset_span ⟨eB, e2, e2_mem_lcs_one, by decide⟩

theorem e4_mem_lcs_three : e4 ∈ lcs 3 :=
  Submodule.subset_span ⟨eB, e3, e3_mem_lcs_two, by decide⟩

/-- `γ₅(L) ≠ 0`: together with `lcs_five_eq_bot` the nilpotency class is exactly `5`,
so `L` is of maximal class (dimension `6`). -/
theorem e5_mem_lcs_four : e5 ∈ lcs 4 :=
  Submodule.subset_span ⟨eA, e4, e4_mem_lcs_three, by decide⟩

/-- **The degree of commutativity is zero** (`Q₆` is *exceptional* in the sense of
Leedham-Green–McKay): `e₂ ∈ γ₂`, `e₃ ∈ γ₃`, yet `[e₂,e₃] = e₅ ≠ 0` while
`γ_{2+3+1} = γ₆ = 0`.  Positive degree of commutativity — the hypothesis missing from
Proposition E.4 — would demand `[γ₂,γ₃] ≤ γ₆`. -/
theorem degree_of_commutativity_zero :
    e2 ∈ lcs 1 ∧ e3 ∈ lcs 2 ∧ br e2 e3 ≠ 0 ∧ lcs 5 = ⊥ :=
  ⟨e2_mem_lcs_one, e3_mem_lcs_two, by decide, lcs_five_eq_bot⟩

/-! ### The upper central series and the subring `T = C_L(Z₂(L))` -/

/-- Membership in the centre `Z(L)`. -/
def IsCentral (x : V) : Prop := ∀ y, br x y = 0

/-- Membership in the second centre `Z₂(L)`. -/
def IsUpperCentral2 (x : V) : Prop := ∀ y, IsCentral (br x y)

/-- Membership in `T = C_L(Z₂(L))`, the Lie analogue of BG's `C_S(Z₂(S))`. -/
def MemT (x : V) : Prop := ∀ z, IsUpperCentral2 z → br x z = 0

theorem isCentral_iff {x : V} : IsCentral x ↔ ∃ t : K, x = t • e5 := by
  constructor
  · intro h
    have hA2 := congrFun (h eA) 2
    have hA5 := congrFun (h eA) 5
    have hB2 := congrFun (h eB) 2
    have hB3 := congrFun (h eB) 3
    have hB4 := congrFun (h eB) 4
    simp [br, eA, eB] at hA2 hA5 hB2 hB3 hB4
    refine ⟨x 5, ?_⟩
    funext k
    fin_cases k <;> simp [e5, hA2, hA5, hB2, hB3, hB4]
  · rintro ⟨t, rfl⟩
    intro y
    funext k
    fin_cases k <;> simp [br, e5]

theorem isUpperCentral2_iff {x : V} :
    IsUpperCentral2 x ↔ x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 := by
  constructor
  · intro h
    obtain ⟨tA, hA⟩ := isCentral_iff.mp (h eA)
    obtain ⟨tB, hB⟩ := isCentral_iff.mp (h eB)
    have hA2 := congrFun hA 2
    have hB2 := congrFun hB 2
    have hB3 := congrFun hB 3
    have hB4 := congrFun hB 4
    simp [br, eA, eB, e5] at hA2 hB2 hB3 hB4
    exact ⟨hB2, hA2, hB3, hB4⟩
  · rintro ⟨h0, h1, h2, h3⟩ y
    rw [isCentral_iff]
    refine ⟨-(x 4 * y 0), ?_⟩
    funext k
    fin_cases k <;> simp [br, e5, h0, h1, h2, h3]

/-- `T = C_L(Z₂(L))` is exactly the coordinate hyperplane `{x | x 0 = 0}` — the Lie
analogue of the *index-`p`* clause of Proposition E.4, which survives in the
counterexample (it is only the abelian clause that fails). -/
theorem memT_iff {x : V} : MemT x ↔ x 0 = 0 := by
  constructor
  · intro h
    have h4 : IsUpperCentral2 e4 :=
      isUpperCentral2_iff.mpr ⟨by decide, by decide, by decide, by decide⟩
    have h5 := congrFun (h e4 h4) 5
    simpa [br, e4] using h5
  · intro h0 z hz
    obtain ⟨z0, z1, z2, z3⟩ := isUpperCentral2_iff.mp hz
    funext k
    fin_cases k <;> simp [br, h0, z0, z1, z2, z3]

/-- **The refutation of E.4's abelian clause**: `b` and `e₂` both lie in
`T = C_L(Z₂(L))`, but `[b, e₂] = e₃ ≠ 0`.  (In the Lazard group: `C_S(Z₂(S))` has index
`p` but is *not* abelian, contradicting Proposition E.4's conclusion.) -/
theorem T_not_abelian : MemT eB ∧ MemT e2 ∧ br eB e2 ≠ 0 :=
  ⟨memT_iff.mpr (by decide), memT_iff.mpr (by decide), by decide⟩

/-! ### Theorem E.3's centralizer hypothesis: `C_L(v) = K·v ⊕ K·e₅` -/

/-- `C_L(v) = K·v ⊕ K·e₅`: the Lie analogue of Theorem E.3's hypothesis
`C_R(R₀) = R₀ × R₁` with `R₀ = Exp(K·v)` of order `p` and `R₁ = Exp(K·e₅)` cyclic
(here of order `p`, sitting in the centre). -/
theorem centralizer_v_iff {x : V} :
    br v x = 0 ↔ ∃ s t : K, x = s • v + t • e5 := by
  constructor
  · intro h
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    have h5 := congrFun h 5
    simp [br, v] at h2 h3 h4 h5
    have h1 : x 1 = x 0 := sub_eq_zero.mp h2
    refine ⟨x 0, x 5, ?_⟩
    funext k
    fin_cases k <;> simp [v, e5, h1, h3, h4, h5]
  · rintro ⟨s, t, rfl⟩
    funext k
    fin_cases k <;> simp [br, v, e5]

/-! ### The fixed-point-free `C₄₉`-action: `β` and `α = β⁷` -/

/-- `ζ = 16`, a fixed element of order `49` in `𝔽₁₉₇ˣ` (`197 = 4·49 + 1`). -/
def zeta : K := 16

/-- The `β`-weights on the basis `(a, b, e₂, e₃, e₄, e₅)`.  They are *exactly* additive
along all five structure products (`1+8 = 9`, `8+9 = 17`, `8+17 = 25`, `1+25 = 26`,
`9+17 = 26` — the last coincidence is what lets the exceptional product carry a
`β`-action), and all six are units mod `49`. -/
def w : Fin 6 → ℕ := fun i =>
  if i = 0 then 1 else if i = 1 then 8 else if i = 2 then 9
  else if i = 3 then 17 else if i = 4 then 25 else 26

/-- The diagonal automorphism `β` with eigenvalue `ζ^(w i)` on the `i`-th basis line.
`B = ⟨β⟩ ≅ C₄₉` is the operator group of Proposition E.4 (abelian, `p ∤ 49`). -/
def β (x : V) : V := fun i => zeta ^ w i * x i

theorem beta_add (x y : V) : β (x + y) = β x + β y := by
  funext i
  simp [β, mul_add]

/-- `β` preserves the bracket: it is a Lie-ring automorphism.  Coordinatewise this is the
exact additivity of the weights along the structure products. -/
theorem br_beta (x y : V) : br (β x) (β y) = β (br x y) := by
  funext k
  fin_cases k <;> simp [br, β, w] <;> ring

theorem beta_iterate_apply (m : ℕ) (x : V) (i : Fin 6) :
    (β^[m] x) i = zeta ^ (m * w i) * x i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    change zeta ^ w i * (β^[m] x) i = _
    rw [ih]
    ring

/-- `β⁴⁹ = 1`: `B = ⟨β⟩` is (a quotient of) `C₄₉`; together with
`beta_iterate_fixed_eq_zero` at `m = 7` it has order exactly `49`. -/
theorem beta_iterate_card : β^[49] = id := by
  funext x
  funext i
  rw [beta_iterate_apply, pow_mul, show zeta ^ 49 = 1 by decide, one_pow, one_mul]
  rfl

theorem zeta_pow_ne_one_of_lt : ∀ r < 49, 0 < r → zeta ^ r ≠ 1 := by decide

theorem zeta_pow_eq_one_iff {n : ℕ} : zeta ^ n = 1 ↔ 49 ∣ n := by
  constructor
  · intro h
    by_contra hnd
    have hsplit : n = 49 * (n / 49) + n % 49 := (Nat.div_add_mod n 49).symm
    rw [hsplit, pow_add, pow_mul, show zeta ^ 49 = 1 by decide, one_pow, one_mul] at h
    exact zeta_pow_ne_one_of_lt _ (Nat.mod_lt _ (by omega))
      (Nat.pos_of_ne_zero fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)) h
  · rintro ⟨k, rfl⟩
    rw [pow_mul, show zeta ^ 49 = 1 by decide, one_pow]

/-- **The fixed-point-free (regular) action**: every nontrivial power of `β` fixes only
`0`.  This is the "B acts regularly on R" hypothesis of Proposition E.4, and (restricted
to powers of `α = β⁷`) the "A acts regularly" hypothesis of Theorem E.3.  The proof is
that every weight is a unit mod `49`. -/
theorem beta_iterate_fixed_eq_zero {m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ 48) {x : V}
    (hfix : β^[m] x = x) : x = 0 := by
  funext i
  have hcoord : zeta ^ (m * w i) * x i = x i := by
    have hi := congrFun hfix i
    rwa [beta_iterate_apply] at hi
  have hne : zeta ^ (m * w i) ≠ 1 := by
    intro heq
    have hdvd : (49 : ℕ) ∣ m * w i := zeta_pow_eq_one_iff.mp heq
    have hcop : Nat.Coprime 49 (w i) := by fin_cases i <;> decide
    have h49m : (49 : ℕ) ∣ m := hcop.dvd_of_dvd_mul_right hdvd
    have := Nat.le_of_dvd (by omega) h49m
    omega
  have hzero : (zeta ^ (m * w i) - 1) * x i = 0 := by
    rw [sub_mul, one_mul, hcoord, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/-- `α = β⁷` is the scalar `ζ⁷` on the line `K·v`: "A fixes `R₀`" (Theorem E.3).  On the
whole plane `L₁` it is the scalar `r = ζ⁷` (`ζ⁵⁶ = ζ⁴⁹·ζ⁷ = ζ⁷`), matching BG's `(E.22)`
— the α-side of BG's argument is *correct*; only the β-side `(E.23)` fails. -/
theorem alpha_smul_v : β^[7] v = zeta ^ 7 • v := by
  funext i
  rw [beta_iterate_apply]
  change zeta ^ (7 * w i) * v i = zeta ^ 7 * v i
  fin_cases i <;> simp [v, w] <;> decide

/-- `β` does **not** fix the line `K·v`: Proposition E.4's hypothesis "B does not fix
`R₀`".  (`β v = (ζ, ζ⁸, 0, …)` is not proportional to `v = (1, 1, 0, …)` since
`ζ⁷ ≠ 1`.) -/
theorem beta_not_fixes_v : ¬ ∃ s : K, β v = s • v := by
  rintro ⟨s, hs⟩
  have h0 : zeta ^ w 0 * v 0 = s * v 0 := congrFun hs 0
  have h1 : zeta ^ w 1 * v 1 = s * v 1 := congrFun hs 1
  rw [show w 0 = 1 from rfl, show v 0 = 1 from rfl, mul_one, mul_one] at h0
  rw [show w 1 = 8 from rfl, show v 1 = 1 from rfl, mul_one, mul_one] at h1
  exact (by decide : (zeta : K) ^ 8 ≠ zeta ^ 1) (h1.trans h0.symm)

/-! ### The precise failure of BG's display `(E.23)` -/

/-- **`(E.23)` is false at level `i = 2`.**  BG sets `w₀ = b`, `wᵢ = [wᵢ₋₁, v]` and claims
(*"Similarly one can show"*) that `β` acts on `wᵢ` with eigenvalue `tᵢ = t₀tⁱ`, i.e.
`ζ^(8+i)`.  The actual chain is `w₂ = [[b,v],v] = e₃` with eigenvalue `ζ¹⁷`, whereas the
prediction is `ζ¹⁰`; they differ because `ζ⁷ ≠ 1`.  (Levels `0` and `1` do agree —
weights `8, 9` — which is presumably what made the claim look "similar".) -/
theorem e23_fails_at_two :
    br (br eB v) v ≠ 0 ∧
      β (br (br eB v) v) = zeta ^ 17 • br (br eB v) v ∧
      zeta ^ 17 ≠ zeta ^ 10 :=
  ⟨by decide, by decide, by decide⟩

/-! ### Headline -/

/-- **BG Proposition E.4 fails for the exceptional filiform `Q₆` — Lie-ring core.**
The bundle of machine-checked facts refuting Proposition E.4 as printed; see the module
docstring for the dictionary to BG's group-level hypotheses and for the (prose) Lazard
transfer.  Master note: `notes/bg/appE_e4_counterexample_2026_07_21.md`. -/
theorem bg_propE4_lie_counterexample :
    -- a genuine Lie bracket (Jacobi in Leibniz form)
    (∀ x y z : V, br x (br y z) = br (br x y) z + br y (br x z)) ∧
    -- β is a bracket automorphism with β⁴⁹ = 1 …
    (∀ x y : V, br (β x) (β y) = β (br x y)) ∧ β^[49] = id ∧
    -- … acting fixed-point-freely: `B ≅ C₄₉` acts regularly
    (∀ m, 1 ≤ m → m ≤ 48 → ∀ x : V, β^[m] x = x → x = 0) ∧
    -- Theorem E.3's centralizer hypothesis: C_L(v) = K·v ⊕ K·e₅
    (∀ x : V, br v x = 0 ↔ ∃ s t : K, x = s • v + t • e5) ∧
    -- A = ⟨β⁷⟩ (order 7 = q) fixes R₀ = K·v …
    β^[7] v = zeta ^ 7 • v ∧
    -- … but B does not fix R₀
    (¬ ∃ s : K, β v = s • v) ∧
    -- VIOLATION of E.4's conclusion: T = C_L(Z₂) is the hyperplane {x 0 = 0}, yet nonabelian
    (∀ x : V, MemT x ↔ x 0 = 0) ∧ MemT eB ∧ MemT e2 ∧ br eB e2 ≠ 0 :=
  ⟨br_leibniz, br_beta, beta_iterate_card, fun _ h1 h2 _ hx =>
    beta_iterate_fixed_eq_zero h1 h2 hx, fun _ => centralizer_v_iff, alpha_smul_v,
    beta_not_fixes_v, fun _ => memT_iff, T_not_abelian.1, T_not_abelian.2.1,
    T_not_abelian.2.2⟩

end OddOrder.BG.AppE.Filiform
