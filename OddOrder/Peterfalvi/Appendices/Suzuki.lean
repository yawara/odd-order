/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Peterfalvi Part II: A Theorem of Suzuki — hypotheses (A1)–(A3)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, pp. 97–134.

This file states the global hypotheses **(A1)–(A3)** of Part II honestly
(`Hypothesis`), together with the standing notation `K`, `V = C_D(t)` and
`W = C_V(K)` (p. 98) and their first consequences.  Suzuki's Theorem A
asserts that under (A1)–(A3) there is a normal subgroup `L ⊴ G` of odd
index isomorphic to `PSL(2,q)`, `Sz(q)` or `PSU(3,q)` (`q` a power of
two, `q > 2`) in its standard doubly transitive action; Chapters I–IV of
Part II are formalized on top of this file, and the final assembly of
Theorem A will be stated once the target-group material (`Sz`, `PSU₃`)
is in place.

* (A1): `G` is a finite group acting doubly transitively on `Ω`; `H` is a
  point stabilizer; `t` an involution outside `H`; `D = H ∩ H^t`; `Q ≤ H`
  with `H = Q ⋊ D` (internally), `|Q|` even and `|D|` odd.
* (A2): the action is faithful.
* (A3): `G` has 2-rank `≥ 2`, i.e. it contains an elementary abelian
  subgroup of order 4.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open MulAction

open scoped Pointwise

/-! ## Hypotheses (A1)–(A3) -/

/-- **Peterfalvi Part II, hypotheses (A1)–(A3)** (p. 97).  The internal
semidirect decomposition `H = Q ⋊ D` is recorded as in the book's
notation section (p. 99): `Q` is normal in `H`, `Q ∩ D = 1` and
`Q D = H`. -/
structure Hypothesis (G Ω : Type*) [Group G] [MulAction G Ω]
    [Finite G] where
  /-- the base point of `Ω`; `H` is its stabilizer -/
  basept : Ω
  /-- (A1): the action is doubly transitive -/
  doubly_transitive : IsMultiplyPretransitive G Ω 2
  /-- (A2): the action is faithful -/
  faithful : FaithfulSMul G Ω
  H : Subgroup G
  Q : Subgroup G
  D : Subgroup G
  H_def : H = stabilizer G basept
  /-- the distinguished involution `t ∈ G - H` -/
  t : G
  t_sq : t ^ 2 = 1
  t_ne_one : t ≠ 1
  t_not_mem_H : t ∉ H
  D_def : D = H ⊓ H.map (MulAut.conj t).toMonoidHom
  Q_le_H : Q ≤ H
  Q_normal_in_H : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q
  Q_inf_D_eq_bot : Q ⊓ D = ⊥
  Q_mul_D_eq_H : (Q : Set G) * (D : Set G) = (H : Set G)
  Q_even : Even (Nat.card Q)
  D_odd : Odd (Nat.card D)
  /-- (A3): `G` has 2-rank at least two -/
  two_rank_ge_two : ∃ E : Subgroup G, Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## Standing notation: `K`, `V`, `W` (p. 98) -/

/-- `K = {x ∈ D | x^t = x⁻¹}` (p. 98) — the elements of `D` inverted by
`t`.  (In general this is only a subset of `G`, closed under inversion
and squaring; it is identified as a subgroup later in Chapter I.) -/
def KSet : Set G :=
  {x | x ∈ hyp.D ∧ hyp.t * x * hyp.t = x⁻¹}

/-- `V = C_D(t)` (p. 98). -/
def V : Subgroup G :=
  hyp.D ⊓ Subgroup.centralizer {hyp.t}

/-- `W = C_V(K)` (p. 98). -/
def W : Subgroup G :=
  hyp.V ⊓ Subgroup.centralizer hyp.KSet

/-! ## First consequences of the axioms -/

include hyp in
lemma nonempty_Omega : Nonempty Ω := ⟨hyp.basept⟩

lemma t_inv_eq : hyp.t⁻¹ = hyp.t := by
  have h2 := hyp.t_sq
  rw [pow_two] at h2
  exact inv_eq_of_mul_eq_one_right h2

lemma D_le_H : hyp.D ≤ hyp.H := by
  rw [hyp.D_def]
  exact inf_le_left

lemma V_le_D : hyp.V ≤ hyp.D := inf_le_left

lemma W_le_V : hyp.W ≤ hyp.V := inf_le_left

/-- Members of `V` commute with `t`. -/
lemma commute_t_of_mem_V {v : G} (hv : v ∈ hyp.V) :
    Commute v hyp.t :=
  Subgroup.mem_centralizer_singleton_iff.mp hv.2

/-- Membership in `D = H ∩ H^t`, in conjugation form. -/
lemma mem_D_iff {x : G} :
    x ∈ hyp.D ↔ x ∈ hyp.H ∧ hyp.t⁻¹ * x * hyp.t ∈ hyp.H := by
  rw [hyp.D_def, Subgroup.mem_inf]
  refine and_congr_right fun _ => ?_
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

/-- `t` normalizes `D` (p. 100, implicit in the canonical form). -/
lemma t_conj_mem_D {x : G} (hx : x ∈ hyp.D) :
    hyp.t⁻¹ * x * hyp.t ∈ hyp.D := by
  rw [mem_D_iff] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  refine ⟨h2, ?_⟩
  have h3 : hyp.t⁻¹ * (hyp.t⁻¹ * x * hyp.t) * hyp.t = x := by
    rw [hyp.t_inv_eq]
    have h4 := hyp.t_sq
    rw [pow_two] at h4
    calc hyp.t * (hyp.t * x * hyp.t) * hyp.t
        = (hyp.t * hyp.t) * x * (hyp.t * hyp.t) := by group
      _ = x := by rw [h4, one_mul, mul_one]
  rw [h3]
  exact h1

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
