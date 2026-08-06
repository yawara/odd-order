/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.TheoremANonTrivialV
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionNonSimple

/-!
# Peterfalvi Part II, Ch. III §1: the case `V = 1`, and the induction of Theorem A

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. III §1, p. 115.

> Suppose that `V = 1`.  We know that `G` is doubly transitive on `Ω` and the elements of
> `D^#` have only two fixed points (Chapter I, §1, Proposition 6(c)).  Furthermore,
> `|Ω| = |Q| + 1` is odd and `O_{2′}(G) = 1` by (A2), (A3) and Chapter I, §1, Proposition
> 1(e), whence `G` has no normal subgroup which is regular on `Ω`.  Thus `G` is a
> Zassenhaus group.  By [HB], Chapter XI, Theorem 11.16, `G` is isomorphic to `PSL(2, q)`
> or to `Sz(q)`, and the conclusion of Theorem A is valid.

Both clauses of "`G` is a Zassenhaus group" are *proved* here; only the classification
itself is taken from the literature, as in the book, and it appears as the explicit
predicate `ZassenhausClassification` rather than as an axiom or a `sorry`.

## Main results

* `Hypothesis.eq_one_of_three_fixedPoints_of_V_eq_bot` — when `V = 1`, the stabilizer of
  three distinct points is trivial.  Two-transitivity moves two of the points onto the
  base pair, so the element lies in `D`, and Ch. I §1 Prop 6(c) conjugates `⟨g⟩` into
  `V = 1`.
* `Hypothesis.natCard_normal_ne_natCard_Omega` — no normal subgroup has order `|Ω|`, so
  in particular none is regular.  `|Ω| = |Q| + 1` is odd and every non-trivial normal
  subgroup has even order (`even_card_of_normal_ne_bot`, i.e. `O_{2′}(G) = 1`).
* `ZassenhausClassification` — the cited theorem, [HB] Ch. XI Thm 11.16.
* `theoremA` — **🎯 Suzuki's Theorem A**, by strong induction on `|G|`: the case `V ≠ 1`
  is Chapters II–IV (`nonempty_theoremAConclusion_of_V_ne_bot`), the case `V = 1` is the
  cited classification.

## Axiom status

`theoremA` is axiom-clean and registered in `AxiomsCheck` (2026-08-07); the cited
classification enters as the explicit `ZassenhausClassification` argument, not as an axiom.
The last `sorry` on this chain, `brauerSuzuki_quaternionSylow_q8` in Chapter II, was closed
with the modular character theory of issues 0147 / 9506.  See `TheoremANonTrivialV`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

universe u v

namespace Hypothesis

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- **`V = 1` makes three-point stabilizers trivial** (Peterfalvi Part II, Ch. III §1,
p. 115: "the elements of `D^#` have only two fixed points (Chapter I, §1, Proposition
6(c))").

Two-transitivity carries `a, b` onto the base pair `basept`, `t · basept`, so the
conjugate `g^h` lies in `D = G_{basept} ∩ G_{t·basept}`; it also fixes `h · c`, a third
point, so `⟨g^h⟩` is conjugate in `D` to a subgroup of `V` (Ch. I §1 Prop 6(c)) — and
`V = 1`. -/
theorem eq_one_of_three_fixedPoints_of_V_eq_bot (hV : hyp.V = ⊥)
    {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {g : G} (hga : g • a = a) (hgb : g • b = b) (hgc : g • c = c) : g = 1 := by
  classical
  haveI := hyp.finite_Omega
  have htb : hyp.basept ≠ hyp.t • hyp.basept := fun hcon =>
    hyp.smul_basept_ne_of_not_mem_H hyp.t_not_mem_H hcon.symm
  obtain ⟨h, hha, hhb⟩ :=
    (MulAction.is_two_pretransitive_iff.mp hyp.doubly_transitive) hab htb
  -- the conjugate fixes the base pair and the image of `c`
  have hfix : ∀ ω : Ω, g • ω = ω → (h * g * h⁻¹) • (h • ω) = h • ω := by
    intro ω hω
    rw [mul_smul, mul_smul, inv_smul_smul, hω]
  have hb1 : (h * g * h⁻¹) • hyp.basept = hyp.basept := by rw [← hha]; exact hfix a hga
  have hb2 : (h * g * h⁻¹) • (hyp.t • hyp.basept) = hyp.t • hyp.basept := by
    rw [← hhb]; exact hfix b hgb
  have hb3 : (h * g * h⁻¹) • (h • c) = h • c := hfix c hgc
  have hgD : h * g * h⁻¹ ∈ hyp.D := by
    rw [hyp.D_eq_stabilizer_inf]
    exact ⟨MulAction.mem_stabilizer_iff.mpr hb1, MulAction.mem_stabilizer_iff.mpr hb2⟩
  -- `⟨g^h⟩ ≤ D` has three fixed points
  have hXD : Subgroup.zpowers (h * g * h⁻¹) ≤ hyp.D := Subgroup.zpowers_le.mpr hgD
  have hmem : ∀ ω : Ω, (h * g * h⁻¹) • ω = ω →
      ω ∈ MulAction.fixedPoints (Subgroup.zpowers (h * g * h⁻¹)) Ω := by
    intro ω hω
    refine mem_fixedPoints_iff_forall.mpr fun x hx => ?_
    exact MulAction.mem_stabilizer_iff.mp
      ((Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hω)) hx)
  have hne13 : hyp.basept ≠ h • c := by
    rw [← hha]; exact fun hcon => hac (MulAction.injective h hcon)
  have hne23 : hyp.t • hyp.basept ≠ h • c := by
    rw [← hhb]; exact fun hcon => hbc (MulAction.injective h hcon)
  have hsub : ({hyp.basept, hyp.t • hyp.basept, h • c} : Set Ω)
      ⊆ MulAction.fixedPoints (Subgroup.zpowers (h * g * h⁻¹)) Ω := by
    rintro z (rfl | rfl | rfl)
    · exact hmem _ hb1
    · exact hmem _ hb2
    · exact hmem _ hb3
  have h3 : 3 ≤ (MulAction.fixedPoints (Subgroup.zpowers (h * g * h⁻¹)) Ω).ncard := by
    calc (3 : ℕ)
        = ({hyp.basept, hyp.t • hyp.basept, h • c} : Set Ω).ncard := by
          rw [Set.ncard_insert_of_notMem (by simp [htb, hne13]),
            Set.ncard_insert_of_notMem (by simp [hne23]), Set.ncard_singleton]
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  -- Ch. I §1 Prop 6(c) conjugates it into `V = 1`
  obtain ⟨k, -, hkV⟩ := hyp.exists_conj_mem_D_map_le_V hXD h3
  rw [hV, le_bot_iff] at hkV
  have hmap : k * (h * g * h⁻¹) * k⁻¹ = 1 := by
    have hmem' : k * (h * g * h⁻¹) * k⁻¹ ∈
        (Subgroup.zpowers (h * g * h⁻¹)).map (MulAut.conj k).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers _)
    rw [hkV, Subgroup.mem_bot] at hmem'
    exact hmem'
  have hconj : h * g * h⁻¹ = 1 := by
    have hcalc : h * g * h⁻¹ = k⁻¹ * (k * (h * g * h⁻¹) * k⁻¹) * k := by group
    rw [hcalc, hmap]; group
  have hcalc : g = h⁻¹ * (h * g * h⁻¹) * h := by group
  rw [hcalc, hconj]; group

include hyp in
/-- **No normal subgroup is regular on `Ω`** (Peterfalvi Part II, Ch. III §1, p. 115:
"`|Ω| = |Q| + 1` is odd and `O_{2′}(G) = 1` … whence `G` has no normal subgroup which is
regular on `Ω`"), in the sharper form that no normal subgroup even has order `|Ω|`.

`|Ω| = |Q| + 1` is odd because `|Q|` is even (axiom), while every non-trivial normal
subgroup has even order — that is `O_{2′}(G) = 1` (`even_card_of_normal_ne_bot`, from
(A2), (A3) and Ch. I §1 Prop 1(e)). -/
theorem natCard_normal_ne_natCard_Omega (N : Subgroup G) (hN : N.Normal) :
    Nat.card ↥N ≠ Nat.card Ω := by
  classical
  haveI := hyp.finite_Omega
  intro hcard
  have hQpos : 0 < Nat.card ↥hyp.Q := Nat.card_pos
  have hodd : Odd (Nat.card Ω) := by
    rw [hyp.card_Omega]; exact hyp.Q_even.add_one
  have hNbot : N ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    rw [hyp.card_Omega] at hcard
    omega
  exact (Nat.not_odd_iff_even.mpr (hcard ▸ hyp.even_card_of_normal_ne_bot N hN hNbot)) hodd

end Hypothesis

/-! ## The cited classification, and the induction -/

/-- **[HB], Ch. XI, Thm 11.16 — the classification of Zassenhaus groups.**

This is the single result Peterfalvi Part II, Ch. III §1 takes from the literature
(p. 115):

> Thus `G` is a Zassenhaus group.  By [HB], Chapter XI, Theorem 11.16, `G` is isomorphic
> to `PSL(2, q)` or to `Sz(q)`, and the conclusion of Theorem A is valid.

Its two hypotheses are exactly what the book verifies before citing it, and both are
theorems here: the stabilizer of three points is trivial
(`Hypothesis.eq_one_of_three_fixedPoints_of_V_eq_bot`) and no normal subgroup is regular,
in the sharper form "no normal subgroup has order `|Ω|`"
(`Hypothesis.natCard_normal_ne_natCard_Omega`).

Carrying it as a `Prop` argument — rather than an `axiom` or a `sorry` — keeps the
boundary of the formalization visible: `theoremA` is a theorem *about* what the cited
classification gives. -/
def ZassenhausClassification : Prop :=
  ∀ {A : Type u} {Λ : Type v} [Group A] [MulAction A Λ] [Finite A] (_ : Hypothesis A Λ),
    (∀ a b c : Λ, a ≠ b → a ≠ c → b ≠ c →
      ∀ g : A, g • a = a → g • b = b → g • c = c → g = 1) →
    (∀ N : Subgroup A, N.Normal → Nat.card ↥N ≠ Nat.card Λ) →
    Nonempty (Hypothesis.TheoremAConclusion A Λ)

/-- The induction of Theorem A, run up to a bound on `|G|`. -/
theorem nonempty_theoremAConclusion_of_natCard_le (hcl : ZassenhausClassification.{u, v})
    (n : ℕ) : ∀ {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G],
      Nat.card G ≤ n → ∀ _hyp : Hypothesis G Ω,
        Nonempty (Hypothesis.TheoremAConclusion G Ω) := by
  induction n with
  | zero =>
      intro G Ω _ _ _ hle _
      exact absurd hle (Nat.not_le.mpr Nat.card_pos)
  | succ k ihk =>
      intro G Ω _ _ _ hle hyp
      have ih : Hypothesis.TheoremAInductionBelow G Ω := by
        intro A Λ _ _ _ hlt hypA
        exact ihk (by omega) hypA
      rcases eq_or_ne hyp.V ⊥ with hV | hV
      · exact hcl hyp
          (fun _ _ _ hab hac hbc _ hga hgb hgc =>
            hyp.eq_one_of_three_fixedPoints_of_V_eq_bot hV hab hac hbc hga hgb hgc)
          (hyp.natCard_normal_ne_natCard_Omega)
      · exact hyp.nonempty_theoremAConclusion_of_V_ne_bot hV ih

/-- **🎯🎯🎯🎯🎯🎯🎯🎯 Peterfalvi Part II, Suzuki's Theorem A** (pp. 97–134).

Under the standing hypothesis (A1)–(A3) — `G` doubly transitive and faithful on `Ω`, with
the two-point stabilizer `D` of odd order, `Q` of even order and `G` of 2-rank `≥ 2` —
the subgroup `O^{2′}(G)` is normal of odd index in `G` and carries one of the three
standard models `PSL(2, q)`, `Sz(q)`, `PSU(3, q)`, acting on `Ω` as the standard model
does on its own point set.

The proof is the book's induction on `|G|` (Ch. I §3):

* `V ≠ 1` — Chapters II, III and IV
  (`Hypothesis.nonempty_theoremAConclusion_of_V_ne_bot`);
* `V = 1` — `G` is a Zassenhaus group of odd degree, and the cited classification
  ([HB], Ch. XI, Thm 11.16 = `ZassenhausClassification`) finishes.

Axiom-clean apart from the explicit `ZassenhausClassification` argument; see the module
docstring. -/
theorem theoremA (hcl : ZassenhausClassification.{u, v}) {G : Type u} {Ω : Type v}
    [Group G] [MulAction G Ω] [Finite G] (hyp : Hypothesis G Ω) :
    Nonempty (Hypothesis.TheoremAConclusion G Ω) :=
  nonempty_theoremAConclusion_of_natCard_le hcl (Nat.card G) le_rfl hyp

end OddOrder.Peterfalvi.Appendices.Suzuki
