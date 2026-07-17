/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Sylow
import OddOrder.BG.Ch1_Preliminary.S01b_Prop116
import OddOrder.BG.Ch2_Uniqueness.S07_Theorem74

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

/-! ## The dictionary: `Q` is regular on `Ω - {basept}` (p. 100)

The book identifies `Ω` with the conjugates of `H` and uses throughout that
`Q` acts regularly (simply transitively) on `Ω - {H}`.  Here this is the
statement that `x ↦ x • (t • basept)` is a bijection from `Q` onto
`{ω | ω ≠ basept}`, from which the order formula
`|G| = |Q| |D| (|Q| + 1)` follows. -/

include hyp in
/-- `Ω` is finite (the orbit map from the finite `G` is onto). -/
lemma finite_Omega : Finite Ω := by
  have h2 := hyp.doubly_transitive
  have : IsPretransitive G Ω := isPretransitive_of_is_two_pretransitive
  exact Finite.of_surjective (fun g : G => g • hyp.basept)
    fun ω => MulAction.exists_smul_eq G hyp.basept ω

lemma smul_basept_eq_of_mem_H {h : G} (hh : h ∈ hyp.H) :
    h • hyp.basept = hyp.basept := by
  rw [hyp.H_def] at hh
  exact hh

/-- The stabilizer of `t • basept` is `H^t`. -/
lemma stabilizer_t_basept :
    stabilizer G (hyp.t • hyp.basept) =
      hyp.H.map (MulAut.conj hyp.t).toMonoidHom := by
  rw [hyp.H_def, stabilizer_smul_eq_stabilizer_map_conj]

lemma smul_t_basept_eq_of_mem_D {d : G} (hd : d ∈ hyp.D) :
    d • (hyp.t • hyp.basept) = hyp.t • hyp.basept := by
  rw [hyp.D_def] at hd
  exact mem_stabilizer_iff.mp (hyp.stabilizer_t_basept ▸ hd.2)

/-- `H` is transitive on `Ω - {basept}`. -/
lemma exists_mem_H_smul_eq {ω₁ ω₂ : Ω} (h1 : ω₁ ≠ hyp.basept)
    (h2 : ω₂ ≠ hyp.basept) : ∃ h ∈ hyp.H, h • ω₁ = ω₂ := by
  obtain ⟨g, hg1, hg2⟩ :=
    (is_two_pretransitive_iff.mp hyp.doubly_transitive)
      (Ne.symm h1) (Ne.symm h2)
  exact ⟨g, hyp.H_def ▸ mem_stabilizer_iff.mpr hg1, hg2⟩

/-- Elements of `Q` move `t • basept` off the base point. -/
lemma Q_smul_t_basept_ne {x : G} (hx : x ∈ hyp.Q) :
    x • (hyp.t • hyp.basept) ≠ hyp.basept := by
  intro heq
  have h2 := congrArg (fun ω : Ω => x⁻¹ • ω) heq
  simp only [inv_smul_smul] at h2
  rw [hyp.smul_basept_eq_of_mem_H (inv_mem (hyp.Q_le_H hx))] at h2
  exact hyp.smul_basept_ne_of_not_mem_H hyp.t_not_mem_H h2

/-- **The dictionary** (p. 100): the orbit map `x ↦ x • (t • basept)` is a
bijection from `Q` onto `Ω - {basept}`, i.e. `Q` is regular on `Ω - {H}`. -/
noncomputable def qRegularEquiv : hyp.Q ≃ {ω : Ω // ω ≠ hyp.basept} :=
  Equiv.ofBijective
    (fun x => ⟨(x : G) • (hyp.t • hyp.basept), hyp.Q_smul_t_basept_ne x.2⟩)
    (by
      constructor
      · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
        simp only [Subtype.mk.injEq] at hxy ⊢
        have hst : y⁻¹ * x ∈ stabilizer G (hyp.t • hyp.basept) := by
          rw [mem_stabilizer_iff, mul_smul, hxy, inv_smul_smul]
        have hQ : y⁻¹ * x ∈ hyp.Q := mul_mem (inv_mem hy) hx
        have hD : y⁻¹ * x ∈ hyp.D := by
          rw [hyp.D_def]
          exact Subgroup.mem_inf.mpr
            ⟨hyp.Q_le_H hQ, hyp.stabilizer_t_basept ▸ hst⟩
        have hbot : y⁻¹ * x ∈ hyp.Q ⊓ hyp.D := ⟨hQ, hD⟩
        rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
        exact (inv_mul_eq_one.mp hbot).symm
      · rintro ⟨ω, hω⟩
        have htne : hyp.t • hyp.basept ≠ hyp.basept :=
          hyp.smul_basept_ne_of_not_mem_H hyp.t_not_mem_H
        obtain ⟨h, hh, hsmul⟩ := hyp.exists_mem_H_smul_eq htne hω
        have hmem : h ∈ (hyp.Q : Set G) * (hyp.D : Set G) := by
          rw [hyp.Q_mul_D_eq_H]; exact hh
        obtain ⟨q, hq, d, hd, rfl⟩ := hmem
        refine ⟨⟨q, hq⟩, ?_⟩
        simp only [Subtype.mk.injEq]
        rw [mul_smul, hyp.smul_t_basept_eq_of_mem_D hd] at hsmul
        exact hsmul)

/-- `|Ω| = |Q| + 1`. -/
lemma card_Omega : Nat.card Ω = Nat.card hyp.Q + 1 := by
  classical
  have : Finite Ω := hyp.finite_Omega
  calc Nat.card Ω
      = Nat.card (Option {ω : Ω // ω ≠ hyp.basept}) :=
        (Nat.card_congr (Equiv.optionSubtypeNe hyp.basept)).symm
    _ = Nat.card {ω : Ω // ω ≠ hyp.basept} + 1 := Finite.card_option
    _ = Nat.card hyp.Q + 1 := by
        rw [Nat.card_congr hyp.qRegularEquiv.symm]

/-- `|H| = |Q| |D|` (from the decomposition `H = Q ⋊ D`). -/
lemma card_H_eq : Nat.card hyp.H = Nat.card hyp.Q * Nat.card hyp.D := by
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : hyp.Q × hyp.D =>
      (⟨(p.1 : G) * (p.2 : G), by
        rw [← SetLike.mem_coe, ← hyp.Q_mul_D_eq_H]
        exact Set.mul_mem_mul p.1.2 p.2.2⟩ : hyp.H))
    ⟨?_, ?_⟩)).symm
  · rintro ⟨⟨q₁, hq₁⟩, ⟨d₁, hd₁⟩⟩ ⟨⟨q₂, hq₂⟩, ⟨d₂, hd₂⟩⟩ heq
    simp only [Subtype.mk.injEq] at heq
    have key : q₂⁻¹ * q₁ = d₂ * d₁⁻¹ := by
      have h' := congrArg (fun z : G => q₂⁻¹ * z * d₁⁻¹) heq
      simpa [mul_assoc] using h'
    have hbot : q₂⁻¹ * q₁ ∈ hyp.Q ⊓ hyp.D :=
      ⟨hyp.Q.mul_mem (hyp.Q.inv_mem hq₂) hq₁,
        key ▸ hyp.D.mul_mem hd₂ (hyp.D.inv_mem hd₁)⟩
    rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
    have hq : q₁ = q₂ := (inv_mul_eq_one.mp hbot).symm
    subst hq
    have hd : d₁ = d₂ := mul_left_cancel heq
    simp [hd]
  · rintro ⟨h, hh⟩
    have hmem : h ∈ (hyp.Q : Set G) * (hyp.D : Set G) := by
      rw [hyp.Q_mul_D_eq_H]; exact hh
    obtain ⟨q, hq, d, hd, rfl⟩ := hmem
    exact ⟨⟨⟨q, hq⟩, ⟨d, hd⟩⟩, rfl⟩

/-- `|G| = |Q| |D| (|Q| + 1)` (proof of Prop 1(c), p. 100). -/
lemma card_G_eq :
    Nat.card G = Nat.card hyp.Q * Nat.card hyp.D * (Nat.card hyp.Q + 1) := by
  have h2 := hyp.doubly_transitive
  have : IsPretransitive G Ω := isPretransitive_of_is_two_pretransitive
  have h1 : Nat.card hyp.H * hyp.H.index = Nat.card G :=
    hyp.H.card_mul_index
  have hidx : hyp.H.index = Nat.card Ω := by
    rw [hyp.H_def]
    exact index_stabilizer_of_transitive G hyp.basept
  rw [← h1, hidx, hyp.card_Omega, hyp.card_H_eq]

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

/-- **Peterfalvi Part II, Ch. I Prop 1 (c)** (p. 100) — `Q` contains a Sylow
`2`-subgroup of `G`.  (From `|G| = |Q| · |D|(|Q| + 1)` with odd cofactor
`|D|(|Q| + 1)`.) -/
lemma exists_sylow_two_le_Q : ∃ P : Sylow 2 G, (P : Subgroup G) ≤ hyp.Q := by
  have hQ0 : Nat.card hyp.Q ≠ 0 := Nat.card_pos.ne'
  have hodd : Odd (Nat.card hyp.D * (Nat.card hyp.Q + 1)) :=
    hyp.D_odd.mul (Even.add_one hyp.Q_even)
  have hm0 : Nat.card hyp.D * (Nat.card hyp.Q + 1) ≠ 0 :=
    fun h => by simp [h] at hodd
  have hfact : (Nat.card G).factorization 2 =
      (Nat.card hyp.Q).factorization 2 := by
    rw [hyp.card_G_eq, mul_assoc, Nat.factorization_mul hQ0 hm0,
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd)), add_zero]
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 hyp.Q) := Sylow.nonempty
  have hcard : Nat.card ((P₀ : Subgroup hyp.Q).map hyp.Q.subtype) =
      2 ^ (Nat.card G).factorization 2 := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ hyp.Q.subtype
      hyp.Q.subtype_injective).toEquiv.symm, hfact]
    exact P₀.card_eq_multiplicity
  exact ⟨Sylow.ofCard _ hcard, by
    rw [Sylow.coe_ofCard]
    exact Subgroup.map_subtype_le _⟩

/-- **Peterfalvi Part II, Ch. I Prop 1 (d)** (p. 100), first half —
`N_G(Q) = H`. -/
lemma normalizer_Q_eq_H : Subgroup.normalizer (hyp.Q : Set G) = hyp.H := by
  refine le_antisymm ?_ ?_
  · refine hyp.normalizer_le_H_of_le_Q le_rfl ?_
    intro hbot
    have heven := hyp.Q_even
    rw [hbot, Subgroup.card_bot] at heven
    simp at heven
  · intro h hh
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    constructor
    · exact fun hn => hyp.Q_normal_in_H h hh n hn
    · intro hn
      have h2 := hyp.Q_normal_in_H h⁻¹ (inv_mem hh) _ hn
      simpa [mul_assoc] using h2

/-- **Peterfalvi Part II, Ch. I Prop 1 (d)** (p. 100), second half —
`N_G(H) = H` (`H` is self-normalizing). -/
lemma normalizer_H_eq_H : Subgroup.normalizer (hyp.H : Set G) = hyp.H := by
  refine le_antisymm ?_ Subgroup.le_normalizer
  intro g hg
  by_contra hgH
  have hmap : hyp.H.map (MulAut.conj g).toMonoidHom = hyp.H := by
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    rw [Subgroup.mem_set_normalizer_iff''] at hg
    exact (hg x).symm
  have hodd := hyp.odd_card_conj_inf hgH
  rw [hmap, inf_idem] at hodd
  have heven : Even (Nat.card hyp.H) := by
    rw [hyp.card_H_eq]
    exact hyp.Q_even.mul_right _
  exact Nat.not_even_iff_odd.mpr hodd heven

section Prop1e

open OddOrder.Isaacs OddOrder.Isaacs.Ch06 OddOrder.BG.Ch2.S07

/-- Under (A3), `Q` itself contains an elementary abelian subgroup of order
`4` (used in the proof of Prop 1(e), p. 100: conjugate the four-group of
(A3) into the Sylow `2`-subgroup of `G` provided by Prop 1(c)). -/
lemma exists_four_subgroup_le_Q :
    ∃ X : Subgroup G, X ≤ hyp.Q ∧ Nat.card X = 4 ∧ ∀ x ∈ X, x ^ 2 = 1 := by
  classical
  obtain ⟨E, hE4, hEsq⟩ := hyp.two_rank_ge_two
  have hE2 : IsPGroup 2 E := fun e => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by
      push_cast
      exact hEsq (e : G) e.2)⟩
  obtain ⟨P', hEP'⟩ := hE2.exists_le_sylow
  obtain ⟨P, hPQ⟩ := hyp.exists_sylow_two_le_Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P' P
  refine ⟨MulAut.conj g • E, ?_, ?_, ?_⟩
  · calc MulAut.conj g • E
        ≤ MulAut.conj g • (P' : Subgroup G) :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hEP'
      _ = ((g • P' : Sylow 2 G) : Subgroup G) := Sylow.coe_subgroup_smul.symm
      _ = (P : Subgroup G) := by rw [hg]
      _ ≤ hyp.Q := hPQ
  · rw [← hE4]
    exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) E).toEquiv).symm
  · intro x hx
    have he := hEsq _ (Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hx)
    simp only [MulAut.smul_def, MulAut.conj_inv_apply] at he
    have h1 : g⁻¹ * x ^ 2 * g = 1 := by rw [← he, sq, sq]; group
    have h2 := congrArg (fun z : G => g * z * g⁻¹) h1
    simpa [mul_assoc] using h2

/-- **Peterfalvi Part II, Ch. I Prop 1 (e)** (p. 100) — since `G` has 2-rank
`≥ 2` (hypothesis (A3)), `O_{2'}(G) = ⋂_{x ∈ G} H^x`, the normal core of `H`.

Forward inclusion: the four-group `X ≤ Q` of (A3)+(c) acts coprimely on
`O_{2'}(G)`, which is therefore generated by the centralizers `C(x)`,
`x ∈ X^#` ([HB] Ch. X Lemma 1.9 = BG Prop 1.16, here
`nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'`); each `C(x)` lies
in `H` by Prop 1(b).  Reverse: `⋂ H^x ≤ H^t ∩ H` has odd order by Prop 1(a)
and is normal, hence lies in `O_{2'}(G)`. -/
theorem oPiCore_two_compl_eq_normalCore :
    Ch03.oPiCore ({2}ᶜ : Set ℕ) G = hyp.H.normalCore := by
  classical
  -- `normalCore H ≤ O_{2'}(G)`: odd order (Prop 1(a)) and normal.
  have hcore_odd : Odd (Nat.card hyp.H.normalCore) := by
    have hle : hyp.H.normalCore ≤
        hyp.H.map (MulAut.conj hyp.t).toMonoidHom ⊓ hyp.H := by
      intro x hx
      refine Subgroup.mem_inf.mpr ⟨?_, hyp.H.normalCore_le hx⟩
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
      have h2 := hx hyp.t⁻¹
      rwa [inv_inv] at h2
    have hdvd := Subgroup.card_dvd_of_le hle
    have hoddinf := hyp.odd_card_conj_inf hyp.t_not_mem_H
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero] at hoddinf ⊢
    exact fun h2 => hoddinf (h2.trans hdvd)
  have hcore_le : hyp.H.normalCore ≤ Ch03.oPiCore ({2}ᶜ : Set ℕ) G := by
    refine Ch03.Subgroup.IsPiGroup.le_oPiCore ?_
    intro p hp
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hcore_odd))
      (Nat.mem_primeFactors.mp hp).2.1
  -- `O_{2'}(G) ≤ H` via four-group coprime generation.
  obtain ⟨X, hXQ, hX4, hXsq⟩ := hyp.exists_four_subgroup_le_Q
  have hOodd : Odd (Nat.card (Ch03.oPiCore ({2}ᶜ : Set ℕ) G)) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    have h2' : 2 ∈ (Nat.card (Ch03.oPiCore ({2}ᶜ : Set ℕ) G)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, Nat.card_pos.ne'⟩
    have h3 := Ch03.oPiCore.isPiGroup ({2}ᶜ : Set ℕ) 2 h2'
    simp at h3
  have hXcomm : IsMulCommutative X := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hinv : ∀ z ∈ X, z⁻¹ = z := fun z hz =>
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hXsq z hz)
    push_cast
    calc (a : G) * b = ((a : G) * b)⁻¹ :=
          (hinv _ (mul_mem a.2 b.2)).symm
      _ = (b : G)⁻¹ * (a : G)⁻¹ := mul_inv_rev _ _
      _ = (b : G) * a := by rw [hinv _ b.2, hinv _ a.2]
  have hXnc : ¬ IsCyclic X := by
    intro hcyc
    obtain ⟨gen, hgen⟩ := hcyc.exists_generator
    have hord : orderOf gen = 4 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hgen]
      exact hX4
    have hdvd : orderOf gen ∣ 2 := orderOf_dvd_of_pow_eq_one
      (Subtype.ext (by push_cast; exact hXsq _ gen.2))
    rw [hord] at hdvd
    norm_num at hdvd
  have hXO_norm : X ≤ Subgroup.normalizer
      ((Ch03.oPiCore ({2}ᶜ : Set ℕ) G : Subgroup G) : Set G) := by
    intro x hxX
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    simp only [SetLike.mem_coe]
    constructor
    · exact fun hn => (Ch03.oPiCore.normal _ _).conj_mem n hn x
    · intro hn
      have h2 := (Ch03.oPiCore.normal _ _).conj_mem _ hn x⁻¹
      simpa [mul_assoc] using h2
  have hO_inv : Ch03.IsAInvariant (conjAction X)
      (Ch03.oPiCore ({2}ᶜ : Set ℕ) G) :=
    isAInvariant_conjAction_iff.mpr hXO_norm
  have hcop : Nat.Coprime (Nat.card X)
      (Nat.card (Ch03.oPiCore ({2}ᶜ : Set ℕ) G)) := by
    rw [hX4, (by norm_num : (4 : ℕ) = 2 ^ 2)]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hOodd)
  haveI := hXcomm
  have htop := OddOrder.BG.Ch1.S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'
    hO_inv.restrict hcop hXnc
  have hle2 : nontrivialActionFixedByClosure hO_inv.restrict ≤
      (hyp.H ⊓ Ch03.oPiCore ({2}ᶜ : Set ℕ) G).subgroupOf
        (Ch03.oPiCore ({2}ᶜ : Set ℕ) G) := by
    rw [nontrivialActionFixedByClosure_le_iff]
    intro b hb
    rw [actionFixedBy_conjAction_restrict]
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    have hzmem := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨?_, hzmem.1⟩
    have hbG : (b : G) ≠ 1 := fun h => hb (Subtype.ext h)
    -- `C_G(b) ≤ N_G(⟨b⟩) ≤ H` (Prop 1(b))
    have hcnorm : Subgroup.centralizer ({(b : G)} : Set G) ≤
        Subgroup.normalizer
          ((Subgroup.zpowers (b : G) : Subgroup G) : Set G) := by
      intro c hc
      have hcomm : Commute c (b : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hc
      have hfix : ∀ k : ℤ, c * (b : G) ^ k * c⁻¹ = (b : G) ^ k := fun k => by
        rw [(hcomm.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
      rw [Subgroup.mem_set_normalizer_iff]
      intro n
      simp only [SetLike.mem_coe]
      constructor
      · intro hn
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← hk, hfix]⟩
      · intro hn
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
        have h3 : n = c⁻¹ * (b : G) ^ k * c := by rw [hk]; group
        rw [h3]
        calc (b : G) ^ k = c⁻¹ * (c * (b : G) ^ k * c⁻¹) * c := by group
          _ = c⁻¹ * (b : G) ^ k * c := by rw [hfix]
    have hcent_le : Subgroup.centralizer ({(b : G)} : Set G) ≤ hyp.H :=
      hcnorm.trans (hyp.normalizer_le_H_of_le_Q
        (Subgroup.zpowers_le.mpr (hXQ b.2))
        (fun hbot => hbG (Subgroup.zpowers_eq_bot.mp hbot)))
    exact hcent_le hzmem.2
  rw [htop, top_le_iff, Subgroup.subgroupOf_eq_top] at hle2
  exact le_antisymm
    (Subgroup.normal_le_normalCore.mpr (hle2.trans inf_le_left))
    hcore_le

end Prop1e

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
