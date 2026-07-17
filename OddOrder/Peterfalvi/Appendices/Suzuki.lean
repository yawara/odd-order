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

/-- `g ∉ H` exactly means `g` moves the base point. -/
lemma smul_basept_ne_of_not_mem_H {g : G} (hg : g ∉ hyp.H) :
    g • hyp.basept ≠ hyp.basept := by
  intro h2
  exact hg (hyp.H_def ▸ mem_stabilizer_iff.mpr h2)

/-- `D` is the pointwise stabilizer of the pair `(basept, t • basept)`. -/
lemma D_eq_stabilizer_inf :
    hyp.D = stabilizer G hyp.basept ⊓ stabilizer G (hyp.t • hyp.basept) := by
  rw [hyp.D_def, hyp.H_def, stabilizer_smul_eq_stabilizer_map_conj]

/-! ## Chapter I §1, Proposition 1 (p. 100) -/

omit [Finite G] in
/-- Conjugation moves two-point stabilizers to two-point stabilizers. -/
private lemma stabilizer_inf_map_conj (k : G) (α β : Ω) :
    (stabilizer G α ⊓ stabilizer G β).map (MulAut.conj k).toMonoidHom =
      stabilizer G (k • α) ⊓ stabilizer G (k • β) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj,
    stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.map_inf _ _ _ (MulEquiv.injective (MulAut.conj k))

/-- **Peterfalvi Part II, Ch. I Prop 1 (a)** (p. 100) — for `g ∉ H`, the
intersection `H^g ∩ H` is conjugate to `D` by an element of `H`.  (Here
`H^g` denotes `g H g⁻¹`; as `g` ranges over `G - H` this is the same
family as the book's `g⁻¹ H g`.) -/
lemma exists_mem_H_conj_inf_eq_D {g : G} (hg : g ∉ hyp.H) :
    ∃ h ∈ hyp.H,
      ((hyp.H.map (MulAut.conj g).toMonoidHom ⊓ hyp.H).map
        (MulAut.conj h).toMonoidHom) = hyp.D := by
  have hgω : g • hyp.basept ≠ hyp.basept := hyp.smul_basept_ne_of_not_mem_H hg
  have htω : hyp.t • hyp.basept ≠ hyp.basept :=
    hyp.smul_basept_ne_of_not_mem_H hyp.t_not_mem_H
  obtain ⟨k, hk1, hk2⟩ :=
    (is_two_pretransitive_iff.mp hyp.doubly_transitive)
      (Ne.symm hgω) (Ne.symm htω)
  refine ⟨k, hyp.H_def ▸ mem_stabilizer_iff.mpr hk1, ?_⟩
  have h2 : hyp.H.map (MulAut.conj g).toMonoidHom ⊓ hyp.H =
      stabilizer G hyp.basept ⊓ stabilizer G (g • hyp.basept) := by
    rw [hyp.H_def, ← stabilizer_smul_eq_stabilizer_map_conj, inf_comm]
  rw [h2, stabilizer_inf_map_conj, hk1, hk2, ← hyp.D_eq_stabilizer_inf]

/-- **Peterfalvi Part II, Ch. I Prop 1 (a)**, second clause — `|H^g ∩ H|`
is odd for `g ∉ H`. -/
lemma odd_card_conj_inf {g : G} (hg : g ∉ hyp.H) :
    Odd (Nat.card
      ↥(hyp.H.map (MulAut.conj g).toMonoidHom ⊓ hyp.H)) := by
  obtain ⟨h, _hh, heq⟩ := hyp.exists_mem_H_conj_inf_eq_D hg
  have hcard : Nat.card
      ↥(hyp.H.map (MulAut.conj g).toMonoidHom ⊓ hyp.H) =
      Nat.card hyp.D := by
    rw [← heq]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective _ _
        (MulEquiv.injective (MulAut.conj h))).toEquiv
  rw [hcard]
  exact hyp.D_odd

/-- **Peterfalvi Part II, Ch. I Prop 1 (b)** (p. 100) — a nontrivial
subgroup of `Q` has its normalizer inside `H`. -/
lemma normalizer_le_H_of_le_Q {X : Subgroup G} (hX : X ≤ hyp.Q)
    (hX1 : X ≠ ⊥) : Subgroup.normalizer (X : Set G) ≤ hyp.H := by
  intro g hg
  by_contra hgH
  -- `X ≤ H^g ∩ H`
  have hXle : X ≤ hyp.H.map (MulAut.conj g).toMonoidHom ⊓ hyp.H := by
    intro x hx
    rw [Subgroup.mem_inf]
    refine ⟨?_, hyp.Q_le_H (hX hx)⟩
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have h2 := (Subgroup.mem_set_normalizer_iff''.mp hg x).mp hx
    exact hyp.Q_le_H (hX h2)
  obtain ⟨h, hh, heq⟩ := hyp.exists_mem_H_conj_inf_eq_D hgH
  -- conjugating by `h` lands `X` inside `Q ⊓ D = ⊥`
  have h3 : X.map (MulAut.conj h).toMonoidHom ≤ hyp.Q ⊓ hyp.D := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    have hxy' : h * x * h⁻¹ = y := hxy
    constructor
    · rw [← hxy']
      exact hyp.Q_normal_in_H h hh x (hX hx)
    · rw [← heq]
      exact ⟨x, hXle hx, hxy⟩
  rw [hyp.Q_inf_D_eq_bot, le_bot_iff, Subgroup.map_eq_bot_iff] at h3
  have h4 : (MulAut.conj h).toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).mpr (MulEquiv.injective (MulAut.conj h))
  rw [h4, le_bot_iff] at h3
  exact hX1 h3

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
