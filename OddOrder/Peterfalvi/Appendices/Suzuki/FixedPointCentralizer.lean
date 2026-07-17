/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerStructure

/-!
# Peterfalvi Part II, Ch. I §1: Proposition 6 (centralizers on fixed points)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §1, pp. 101–102.

For `X ≤ D` with at least three fixed points on `Ω` (written `Ω_X`,
here `MulAction.fixedPoints X Ω`):

* **Prop 6 (a)**: `C_G(X)` is doubly transitive on `Ω_X`, and
  `C_H(X) = C_Q(X) ⋊ C_D(X)`.  The engine is that `C_Q(X)` is regular on
  `Ω_X - {basept}` (`cQRegularEquiv`): if `y ∈ Q` maps `t • basept` into
  `Ω_X`, conjugating by `x ∈ X` and using the regularity of `Q` on
  `Ω - {basept}` forces `y ∈ C_Q(X)`.  The symmetric statement for
  `Ω_X - {t • basept}` is the same lemma applied to the conjugate
  hypothesis `hyp.symm`.
* **Prop 6 (b)**: `|C_Q(X)|` is even.
* **Prop 6 (c)**: `X` is conjugate in `D` to a subgroup of `V`.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

open MulAction

open scoped Pointwise

/-! ## The fixed-point set `Ω_X` -/

omit [Finite G] in
/-- Membership in `Ω_X = fixedPoints X Ω`, phrased over elements of `G`. -/
lemma mem_fixedPoints_iff_forall {X : Subgroup G} {ω : Ω} :
    ω ∈ fixedPoints X Ω ↔ ∀ x ∈ X, x • ω = ω := by
  rw [mem_fixedPoints]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h m => h m m.2⟩

variable {X : Subgroup G}

/-- The base point is fixed by any `X ≤ D` (p. 102). -/
lemma basept_mem_fixedPoints (hXD : X ≤ hyp.D) :
    hyp.basept ∈ fixedPoints X Ω :=
  mem_fixedPoints_iff_forall.mpr fun _ hx =>
    hyp.smul_basept_eq_of_mem_H (hyp.D_le_H (hXD hx))

/-- The point `t • basept` is fixed by any `X ≤ D` (p. 102). -/
lemma t_smul_basept_mem_fixedPoints (hXD : X ≤ hyp.D) :
    hyp.t • hyp.basept ∈ fixedPoints X Ω :=
  mem_fixedPoints_iff_forall.mpr fun _ hx =>
    hyp.smul_t_basept_eq_of_mem_D (hXD hx)

omit [Finite G] in
/-- `C_G(X)` preserves `Ω_X`. -/
lemma smul_mem_fixedPoints_of_mem_centralizer {c : G}
    (hc : c ∈ Subgroup.centralizer (X : Set G)) {ω : Ω}
    (hω : ω ∈ fixedPoints X Ω) : c • ω ∈ fixedPoints X Ω := by
  rw [mem_fixedPoints_iff_forall] at hω ⊢
  intro x hx
  have hcx : x * c = c * x := Subgroup.mem_centralizer_iff.mp hc x hx
  calc x • c • ω = (x * c) • ω := (mul_smul x c ω).symm
    _ = (c * x) • ω := by rw [hcx]
    _ = c • x • ω := mul_smul c x ω
    _ = c • ω := by rw [hω x hx]

/-! ## Prop 6 (a), engine: `C_Q(X)` is regular on `Ω_X - {basept}` (p. 102) -/

/-- **Peterfalvi Part II, Ch. I Prop 6 (a)** (p. 102), key step — if `y ∈ Q`
moves `t • basept` to a fixed point of `X`, then `y` centralizes `X`.
(`(xyx⁻¹) • (t • basept) = y • (t • basept)` for `x ∈ X`, and `Q` is
regular on `Ω - {basept}`.) -/
lemma mem_centralizer_of_mem_Q_of_smul_mem_fixedPoints (hXD : X ≤ hyp.D)
    {y : G} (hy : y ∈ hyp.Q)
    (hfix : y • (hyp.t • hyp.basept) ∈ fixedPoints X Ω) :
    y ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxH : x ∈ hyp.H := hyp.D_le_H (hXD hx)
  have hconj : x * y * x⁻¹ ∈ hyp.Q := hyp.Q_normal_in_H x hxH y hy
  have hxinv : x⁻¹ • (hyp.t • hyp.basept) = hyp.t • hyp.basept :=
    hyp.smul_t_basept_eq_of_mem_D (hyp.D.inv_mem (hXD hx))
  have hsmul : (x * y * x⁻¹) • (hyp.t • hyp.basept) =
      y • (hyp.t • hyp.basept) := by
    calc (x * y * x⁻¹) • (hyp.t • hyp.basept)
        = x • y • x⁻¹ • (hyp.t • hyp.basept) := by
          rw [mul_smul, mul_smul]
      _ = x • (y • (hyp.t • hyp.basept)) := by rw [hxinv]
      _ = y • (hyp.t • hyp.basept) :=
          mem_fixedPoints_iff_forall.mp hfix x hx
  have hinj : (⟨x * y * x⁻¹, hconj⟩ : hyp.Q) = ⟨y, hy⟩ :=
    hyp.qRegularEquiv.injective (Subtype.ext hsmul)
  have h3 : x * y * x⁻¹ = y := congrArg Subtype.val hinj
  calc x * y = (x * y * x⁻¹) * x := by group
    _ = y * x := by rw [h3]

/-- Conversely, `C_Q(X)` maps `t • basept` into `Ω_X`. -/
lemma smul_t_basept_mem_fixedPoints_of_mem_centralizer (hXD : X ≤ hyp.D)
    {y : G} (hy : y ∈ Subgroup.centralizer (X : Set G)) :
    y • (hyp.t • hyp.basept) ∈ fixedPoints X Ω :=
  smul_mem_fixedPoints_of_mem_centralizer hy
    (hyp.t_smul_basept_mem_fixedPoints hXD)

/-- **Peterfalvi Part II, Ch. I Prop 6 (a)** (p. 102), first clause —
`C_Q(X)` is regular on `Ω_X - {basept}`: the orbit map
`y ↦ y • (t • basept)` is a bijection from `C_Q(X)` onto
`Ω_X - {basept}`. -/
noncomputable def cQRegularEquiv (hXD : X ≤ hyp.D) :
    ↥(hyp.Q ⊓ Subgroup.centralizer (X : Set G)) ≃
      {ω : Ω // ω ∈ fixedPoints X Ω ∧ ω ≠ hyp.basept} :=
  Equiv.ofBijective
    (fun y => ⟨(y : G) • (hyp.t • hyp.basept),
      hyp.smul_t_basept_mem_fixedPoints_of_mem_centralizer hXD y.2.2,
      hyp.Q_smul_t_basept_ne y.2.1⟩)
    (by
      constructor
      · rintro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ hxy
        simp only [Subtype.mk.injEq] at hxy
        have hinj : (⟨y₁, hy₁.1⟩ : hyp.Q) = ⟨y₂, hy₂.1⟩ :=
          hyp.qRegularEquiv.injective (Subtype.ext hxy)
        have hval : y₁ = y₂ := congrArg Subtype.val hinj
        exact Subtype.ext hval
      · rintro ⟨ω, hωfix, hωne⟩
        obtain ⟨⟨y, hy⟩, hsmul⟩ :=
          hyp.qRegularEquiv.surjective ⟨ω, hωne⟩
        have hval : y • (hyp.t • hyp.basept) = ω :=
          congrArg Subtype.val hsmul
        have hyc : y ∈ Subgroup.centralizer (X : Set G) :=
          hyp.mem_centralizer_of_mem_Q_of_smul_mem_fixedPoints hXD hy
            (hval ▸ hωfix)
        exact ⟨⟨y, hy, hyc⟩, Subtype.ext hval⟩)

/-- `|Ω_X| = |C_Q(X)| + 1` (p. 102). -/
lemma ncard_fixedPoints (hXD : X ≤ hyp.D) :
    (fixedPoints X Ω).ncard =
      Nat.card ↥(hyp.Q ⊓ Subgroup.centralizer (X : Set G)) + 1 := by
  classical
  have : Finite Ω := hyp.finite_Omega
  have hmem : hyp.basept ∈ fixedPoints X Ω := hyp.basept_mem_fixedPoints hXD
  have hins : fixedPoints X Ω =
      insert hyp.basept (fixedPoints X Ω \ {hyp.basept}) := by
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hmem]
  rw [hins, Set.ncard_insert_of_notMem (by simp)]
  congr 1
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    ((Equiv.subtypeEquivRight fun ω =>
        (Set.mem_sdiff_singleton (a := ω))).trans
      (hyp.cQRegularEquiv hXD).symm)

/-- Surjectivity of the orbit map, extracted: every fixed point other than
`basept` is `y • (t • basept)` for some `y ∈ C_Q(X)`. -/
lemma exists_mem_cQ_smul_t_basept_eq (hXD : X ≤ hyp.D) {ω : Ω}
    (hω : ω ∈ fixedPoints X Ω) (hne : ω ≠ hyp.basept) :
    ∃ y ∈ hyp.Q ⊓ Subgroup.centralizer (X : Set G),
      y • (hyp.t • hyp.basept) = ω := by
  obtain ⟨y, hy⟩ := (hyp.cQRegularEquiv hXD).surjective ⟨ω, hω, hne⟩
  exact ⟨(y : G), y.2, congrArg Subtype.val hy⟩

/-- The symmetric statement (the book's "similarly", p. 102), via the
conjugate hypothesis `hyp.symm`: every fixed point other than `t • basept`
is `c • basept` for some `c ∈ C_{Q^t}(X)`; we record the two consequences
used downstream (`c` centralizes `X` and fixes `t • basept`). -/
lemma exists_mem_centralizer_smul_basept_eq (hXD : X ≤ hyp.D) {ω : Ω}
    (hω : ω ∈ fixedPoints X Ω) (hne : ω ≠ hyp.t • hyp.basept) :
    ∃ c ∈ Subgroup.centralizer (X : Set G),
      c • hyp.basept = ω ∧ c • (hyp.t • hyp.basept) = hyp.t • hyp.basept := by
  have hXD' : X ≤ hyp.symm.D := hXD
  obtain ⟨y, hy⟩ := (hyp.symm.cQRegularEquiv hXD').surjective ⟨ω, hω, hne⟩
  have hval : (y : G) • (hyp.symm.t • hyp.symm.basept) = ω :=
    congrArg Subtype.val hy
  rw [hyp.symm_t_smul_basept] at hval
  refine ⟨(y : G), y.2.2, hval, ?_⟩
  exact hyp.symm.smul_basept_eq_of_mem_H (hyp.symm.Q_le_H y.2.1)

/-! ## Prop 6 (a): `C_G(X)` is doubly transitive on `Ω_X` (p. 102) -/

/-- If `|Ω_X| ≥ 3` there is a fixed point besides `basept` and
`t • basept`. -/
lemma exists_third_fixedPoint (h3 : 3 ≤ (fixedPoints X Ω).ncard) :
    ∃ ω₀ ∈ fixedPoints X Ω,
      ω₀ ≠ hyp.basept ∧ ω₀ ≠ hyp.t • hyp.basept := by
  by_contra hcon
  push Not at hcon
  have hsub : fixedPoints X Ω ⊆ {hyp.basept, hyp.t • hyp.basept} := by
    intro ω hω
    rcases eq_or_ne ω hyp.basept with h | h
    · exact Set.mem_insert_iff.mpr (Or.inl h)
    · exact Set.mem_insert_iff.mpr (Or.inr (hcon ω hω h))
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({hyp.basept, hyp.t • hyp.basept} : Set Ω).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  omega

/-- Transitivity normal form: every fixed point can be moved to `basept`
by `C_G(X)` (uses `|Ω_X| ≥ 3` to bridge `t • basept → basept` through a
third fixed point). -/
lemma exists_mem_centralizer_smul_eq_basept (hXD : X ≤ hyp.D)
    (h3 : 3 ≤ (fixedPoints X Ω).ncard) {ω : Ω}
    (hω : ω ∈ fixedPoints X Ω) :
    ∃ c ∈ Subgroup.centralizer (X : Set G), c • ω = hyp.basept := by
  -- a `swap` element moving `t • basept` to `basept`
  have hswap : ∃ c ∈ Subgroup.centralizer (X : Set G),
      c • (hyp.t • hyp.basept) = hyp.basept := by
    obtain ⟨ω₀, hω₀, hω₀b, hω₀t⟩ := hyp.exists_third_fixedPoint h3
    obtain ⟨y, hy, hysmul⟩ := hyp.exists_mem_cQ_smul_t_basept_eq hXD hω₀ hω₀b
    obtain ⟨c, hc, hcsmul, -⟩ :=
      hyp.exists_mem_centralizer_smul_basept_eq hXD hω₀ hω₀t
    refine ⟨c⁻¹ * y, mul_mem (inv_mem hc) hy.2, ?_⟩
    rw [mul_smul, hysmul, ← hcsmul, inv_smul_smul]
  rcases eq_or_ne ω hyp.basept with rfl | hne
  · exact ⟨1, one_mem _, one_smul _ _⟩
  · obtain ⟨y, hy, hysmul⟩ := hyp.exists_mem_cQ_smul_t_basept_eq hXD hω hne
    obtain ⟨c, hc, hcsmul⟩ := hswap
    refine ⟨c * y⁻¹, mul_mem hc (inv_mem hy.2), ?_⟩
    rw [mul_smul, ← hysmul, inv_smul_smul, hcsmul]

/-- **Peterfalvi Part II, Ch. I Prop 6 (a)** (p. 102) — `C_G(X)` is
transitive on `Ω_X`. -/
theorem exists_mem_centralizer_smul_eq (hXD : X ≤ hyp.D)
    (h3 : 3 ≤ (fixedPoints X Ω).ncard) {ω₁ ω₂ : Ω}
    (h1 : ω₁ ∈ fixedPoints X Ω) (h2 : ω₂ ∈ fixedPoints X Ω) :
    ∃ c ∈ Subgroup.centralizer (X : Set G), c • ω₁ = ω₂ := by
  obtain ⟨c₁, hc₁, hc₁s⟩ := hyp.exists_mem_centralizer_smul_eq_basept hXD h3 h1
  obtain ⟨c₂, hc₂, hc₂s⟩ := hyp.exists_mem_centralizer_smul_eq_basept hXD h3 h2
  refine ⟨c₂⁻¹ * c₁, mul_mem (inv_mem hc₂) hc₁, ?_⟩
  rw [mul_smul, hc₁s, ← hc₂s, inv_smul_smul]

/-- Doubly transitive normal form: any pair of distinct fixed points can
be moved to `(basept, t • basept)` by `C_G(X)`. -/
lemma exists_mem_centralizer_smul_pair_basept (hXD : X ≤ hyp.D)
    (h3 : 3 ≤ (fixedPoints X Ω).ncard) {α₁ α₂ : Ω}
    (hα₁ : α₁ ∈ fixedPoints X Ω) (hα₂ : α₂ ∈ fixedPoints X Ω)
    (hne : α₁ ≠ α₂) :
    ∃ c ∈ Subgroup.centralizer (X : Set G),
      c • α₁ = hyp.basept ∧ c • α₂ = hyp.t • hyp.basept := by
  obtain ⟨c₀, hc₀, hc₀s⟩ := hyp.exists_mem_centralizer_smul_eq_basept hXD h3 hα₁
  have hα₂' : c₀ • α₂ ∈ fixedPoints X Ω :=
    smul_mem_fixedPoints_of_mem_centralizer hc₀ hα₂
  have hα₂ne : c₀ • α₂ ≠ hyp.basept := by
    rw [← hc₀s]
    exact fun h => hne (smul_left_cancel c₀ h).symm
  obtain ⟨y, hy, hysmul⟩ := hyp.exists_mem_cQ_smul_t_basept_eq hXD hα₂' hα₂ne
  refine ⟨y⁻¹ * c₀, mul_mem (inv_mem hy.2) hc₀, ?_, ?_⟩
  · rw [mul_smul, hc₀s,
      hyp.smul_basept_eq_of_mem_H (inv_mem (hyp.Q_le_H hy.1))]
  · rw [mul_smul, ← hysmul, inv_smul_smul]

/-- **Peterfalvi Part II, Ch. I Prop 6 (a)** (p. 102), first clause —
`C_G(X)` is doubly transitive on `Ω_X` (elementwise form; the bundled
`IsMultiplyPretransitive` for the induced action is deferred to the point
of use, Ch. I §3). -/
theorem exists_mem_centralizer_smul_pair (hXD : X ≤ hyp.D)
    (h3 : 3 ≤ (fixedPoints X Ω).ncard) {α₁ α₂ β₁ β₂ : Ω}
    (hα₁ : α₁ ∈ fixedPoints X Ω) (hα₂ : α₂ ∈ fixedPoints X Ω)
    (hβ₁ : β₁ ∈ fixedPoints X Ω) (hβ₂ : β₂ ∈ fixedPoints X Ω)
    (hαne : α₁ ≠ α₂) (hβne : β₁ ≠ β₂) :
    ∃ c ∈ Subgroup.centralizer (X : Set G),
      c • α₁ = β₁ ∧ c • α₂ = β₂ := by
  obtain ⟨cα, hcα, hcα1, hcα2⟩ :=
    hyp.exists_mem_centralizer_smul_pair_basept hXD h3 hα₁ hα₂ hαne
  obtain ⟨cβ, hcβ, hcβ1, hcβ2⟩ :=
    hyp.exists_mem_centralizer_smul_pair_basept hXD h3 hβ₁ hβ₂ hβne
  refine ⟨cβ⁻¹ * cα, mul_mem (inv_mem hcβ) hcα, ?_, ?_⟩
  · rw [mul_smul, hcα1, ← hcβ1, inv_smul_smul]
  · rw [mul_smul, hcα2, ← hcβ2, inv_smul_smul]

/-! ## Prop 6 (a): `C_H(X) = C_Q(X) ⋊ C_D(X)` (p. 102) -/

/-- **Peterfalvi Part II, Ch. I Prop 6 (a)** (p. 102), second clause —
`C_H(X) = C_Q(X) ⋊ C_D(X)`: the product decomposition (the semidirect
structure — `C_Q(X)` normal, trivial intersection — is inherited from
`H = Q ⋊ D`). -/
theorem cQ_mul_cD_eq_cH (hXD : X ≤ hyp.D) :
    ((hyp.Q ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) *
      ((hyp.D ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) =
      ((hyp.H ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
  apply subset_antisymm
  · rintro - ⟨q, hq, d, hd, rfl⟩
    rw [SetLike.mem_coe] at hq hd ⊢
    obtain ⟨hqQ, hqc⟩ := Subgroup.mem_inf.mp hq
    obtain ⟨hdD, hdc⟩ := Subgroup.mem_inf.mp hd
    exact Subgroup.mem_inf.mpr
      ⟨hyp.H.mul_mem (hyp.Q_le_H hqQ) (hyp.D_le_H hdD), mul_mem hqc hdc⟩
  · intro h hh
    rw [SetLike.mem_coe] at hh
    obtain ⟨hhH, hhc⟩ := Subgroup.mem_inf.mp hh
    have hmem : h ∈ (hyp.Q : Set G) * (hyp.D : Set G) := by
      rw [hyp.Q_mul_D_eq_H]; exact hhH
    obtain ⟨q, hq, d, hd, rfl⟩ := hmem
    have hfix : q • (hyp.t • hyp.basept) ∈ fixedPoints X Ω := by
      have hqd : (q * d) • (hyp.t • hyp.basept) = q • (hyp.t • hyp.basept) := by
        rw [mul_smul, hyp.smul_t_basept_eq_of_mem_D hd]
      rw [← hqd]
      exact smul_mem_fixedPoints_of_mem_centralizer hhc
        (hyp.t_smul_basept_mem_fixedPoints hXD)
    have hqc : q ∈ Subgroup.centralizer (X : Set G) :=
      hyp.mem_centralizer_of_mem_Q_of_smul_mem_fixedPoints hXD hq hfix
    have hdc : d ∈ Subgroup.centralizer (X : Set G) := by
      have hd2 : d = q⁻¹ * (q * d) := by group
      rw [hd2]
      exact mul_mem (inv_mem hqc) hhc
    exact ⟨q, SetLike.mem_coe.mpr (Subgroup.mem_inf.mpr ⟨hq, hqc⟩),
      d, SetLike.mem_coe.mpr (Subgroup.mem_inf.mpr ⟨hd, hdc⟩), rfl⟩

/-- `|C_H(X)| = |C_Q(X)| |C_D(X)|` (from the decomposition of Prop 6 (a)). -/
lemma card_cH_eq (hXD : X ≤ hyp.D) :
    Nat.card ↥(hyp.H ⊓ Subgroup.centralizer (X : Set G)) =
      Nat.card ↥(hyp.Q ⊓ Subgroup.centralizer (X : Set G)) *
        Nat.card ↥(hyp.D ⊓ Subgroup.centralizer (X : Set G)) := by
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : ↥(hyp.Q ⊓ Subgroup.centralizer (X : Set G)) ×
        ↥(hyp.D ⊓ Subgroup.centralizer (X : Set G)) =>
      (⟨(p.1 : G) * (p.2 : G), by
        rw [← SetLike.mem_coe, ← hyp.cQ_mul_cD_eq_cH hXD]
        exact Set.mul_mem_mul p.1.2 p.2.2⟩ :
          ↥(hyp.H ⊓ Subgroup.centralizer (X : Set G))))
    ⟨?_, ?_⟩)).symm
  · rintro ⟨⟨q₁, hq₁⟩, ⟨d₁, hd₁⟩⟩ ⟨⟨q₂, hq₂⟩, ⟨d₂, hd₂⟩⟩ heq
    simp only [Subtype.mk.injEq] at heq
    have key : q₂⁻¹ * q₁ = d₂ * d₁⁻¹ := by
      have h' := congrArg (fun z : G => q₂⁻¹ * z * d₁⁻¹) heq
      simpa [mul_assoc] using h'
    have hbot : q₂⁻¹ * q₁ ∈ hyp.Q ⊓ hyp.D :=
      ⟨hyp.Q.mul_mem (hyp.Q.inv_mem hq₂.1) hq₁.1,
        key ▸ hyp.D.mul_mem hd₂.1 (hyp.D.inv_mem hd₁.1)⟩
    rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
    have hq : q₁ = q₂ := (inv_mul_eq_one.mp hbot).symm
    subst hq
    have hd : d₁ = d₂ := mul_left_cancel heq
    simp [hd]
  · rintro ⟨h, hh⟩
    have hmem : h ∈
        ((hyp.Q ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) *
          ((hyp.D ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
      rw [hyp.cQ_mul_cD_eq_cH hXD]
      exact hh
    obtain ⟨q, hq, d, hd, rfl⟩ := hmem
    exact ⟨⟨⟨q, hq⟩, ⟨d, hd⟩⟩, rfl⟩

/-! ## Prop 6 (b): `|C_Q(X)|` is even (p. 102) -/

/-- **Peterfalvi Part II, Ch. I Prop 6 (b)** (p. 102) — `|C_Q(X)|` is even.

The pair-swap `(basept, t • basept) ↦ (t • basept, basept)` from (a) is an
element of `C_G(X)` of even order, giving an involution `u ∈ C_G(X)`; `u`
is conjugate to an involution of `Q` (Prop 2), so it fixes a point
`ω' ∈ Ω_X` (via `C_G(u₀) ≤ H`, Prop 1(b)); moving `ω'` to `basept` by
transitivity conjugates `u` into `C_H(X)`, so `|C_H(X)| = |C_Q(X)||C_D(X)|`
is even, and `|C_D(X)|` is odd. -/
theorem even_card_cQ (hXD : X ≤ hyp.D)
    (h3 : 3 ≤ (fixedPoints X Ω).ncard) :
    Even (Nat.card ↥(hyp.Q ⊓ Subgroup.centralizer (X : Set G))) := by
  classical
  have htb : hyp.t • hyp.basept ≠ hyp.basept :=
    hyp.smul_basept_ne_of_not_mem_H hyp.t_not_mem_H
  -- a pair-swap element of `C_G(X)`
  obtain ⟨c, hc, hc1, hc2⟩ := hyp.exists_mem_centralizer_smul_pair hXD h3
    (hyp.basept_mem_fixedPoints hXD) (hyp.t_smul_basept_mem_fixedPoints hXD)
    (hyp.t_smul_basept_mem_fixedPoints hXD) (hyp.basept_mem_fixedPoints hXD)
    (Ne.symm htb) htb
  -- `c` has even order (an odd-order element with `c² ∈ Stab(basept)` would
  -- itself stabilize `basept`, but `c • basept = t • basept ≠ basept`)
  have hc2mem : c ^ 2 ∈ stabilizer G hyp.basept := by
    rw [mem_stabilizer_iff, pow_two, mul_smul, hc1, hc2]
  have hordc : Even (orderOf c) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨j, hj⟩ := hodd
    have hcmem : c ∈ stabilizer G hyp.basept := by
      have hcpow : c = (c ^ 2) ^ (j + 1) := by
        rw [← pow_mul, show 2 * (j + 1) = orderOf c + 1 by omega,
          pow_succ, pow_orderOf_eq_one, one_mul]
      rw [hcpow]
      exact pow_mem hc2mem (j + 1)
    rw [mem_stabilizer_iff] at hcmem
    rw [hcmem] at hc1
    exact htb hc1.symm
  -- the involution `u = c ^ k`, `orderOf c = 2k`
  obtain ⟨k, hk⟩ := hordc
  have hk0 : k ≠ 0 := by
    intro h
    have := orderOf_pos c
    omega
  have hu2 : (c ^ k) ^ 2 = 1 := by
    rw [← pow_mul, show k * 2 = orderOf c by omega, pow_orderOf_eq_one]
  have hu1 : c ^ k ≠ 1 := by
    intro h
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0)
      (orderOf_dvd_of_pow_eq_one h)
    omega
  have huc : c ^ k ∈ Subgroup.centralizer (X : Set G) := pow_mem hc k
  -- `u` fixes a point of `Ω_X`: it is conjugate to an involution `u₀ ∈ Q`
  obtain ⟨u₀, hu₀Q, hu₀2, hu₀1⟩ := hyp.exists_involution_mem_Q
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (hyp.isConj_of_involutions hu₀2 hu₀1 hu2 hu1)
  -- hg : g * u₀ * g⁻¹ = c ^ k
  have hω'fix : g • hyp.basept ∈ fixedPoints X Ω := by
    rw [mem_fixedPoints_iff_forall]
    intro x hx
    have hxu : x * c ^ k = c ^ k * x :=
      Subgroup.mem_centralizer_iff.mp huc x hx
    have hcomm : (g⁻¹ * x * g) * u₀ = u₀ * (g⁻¹ * x * g) := by
      have hu₀eq : u₀ = g⁻¹ * c ^ k * g := by rw [← hg]; group
      rw [hu₀eq]
      calc (g⁻¹ * x * g) * (g⁻¹ * c ^ k * g)
          = g⁻¹ * (x * c ^ k) * g := by group
        _ = g⁻¹ * (c ^ k * x) * g := by rw [hxu]
        _ = (g⁻¹ * c ^ k * g) * (g⁻¹ * x * g) := by group
    have hmemH : g⁻¹ * x * g ∈ hyp.H :=
      hyp.centralizer_le_H_of_mem_Q hu₀Q hu₀1
        (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
    have hfixb : (g⁻¹ * x * g) • hyp.basept = hyp.basept :=
      hyp.smul_basept_eq_of_mem_H hmemH
    calc x • g • hyp.basept
        = g • ((g⁻¹ * x * g) • hyp.basept) := by
          rw [← mul_smul, ← mul_smul]
          congr 1
          group
      _ = g • hyp.basept := by rw [hfixb]
  have huω' : (c ^ k) • (g • hyp.basept) = g • hyp.basept := by
    rw [← hg]
    calc (g * u₀ * g⁻¹) • g • hyp.basept
        = (g * u₀) • hyp.basept := by
          rw [← mul_smul]
          congr 1
          group
      _ = g • (u₀ • hyp.basept) := mul_smul _ _ _
      _ = g • hyp.basept := by
          rw [hyp.smul_basept_eq_of_mem_H (hyp.Q_le_H hu₀Q)]
  -- conjugate `u` into `C_H(X)` by transitivity, so `|C_H(X)|` is even
  obtain ⟨c', hc', hc's⟩ :=
    hyp.exists_mem_centralizer_smul_eq_basept hXD h3 hω'fix
  have hvc : c' * c ^ k * c'⁻¹ ∈ Subgroup.centralizer (X : Set G) :=
    mul_mem (mul_mem hc' huc) (inv_mem hc')
  have hc'inv : c'⁻¹ • hyp.basept = g • hyp.basept := by
    have h := congrArg (fun ω : Ω => c'⁻¹ • ω) hc's.symm
    simpa using h
  have hvH : c' * c ^ k * c'⁻¹ ∈ hyp.H := by
    rw [hyp.H_def, mem_stabilizer_iff]
    calc (c' * c ^ k * c'⁻¹) • hyp.basept
        = c' • (c ^ k) • c'⁻¹ • hyp.basept := by
          rw [mul_smul, mul_smul]
      _ = c' • (c ^ k) • (g • hyp.basept) := by rw [hc'inv]
      _ = c' • (g • hyp.basept) := by rw [huω']
      _ = hyp.basept := hc's
  have hv2 : (c' * c ^ k * c'⁻¹) ^ 2 = 1 := by
    have hexp : (c' * c ^ k * c'⁻¹) ^ 2 = c' * (c ^ k) ^ 2 * c'⁻¹ := by
      rw [pow_two, pow_two]
      group
    rw [hexp, hu2, mul_one, mul_inv_cancel]
  have hv1 : c' * c ^ k * c'⁻¹ ≠ 1 := by
    intro h
    apply hu1
    calc c ^ k = c'⁻¹ * (c' * c ^ k * c'⁻¹) * c' := by group
      _ = c'⁻¹ * 1 * c' := by rw [h]
      _ = 1 := by group
  have heven : Even (Nat.card ↥(hyp.H ⊓ Subgroup.centralizer (X : Set G))) :=
    even_card_of_sq_eq_one_mem (Subgroup.mem_inf.mpr ⟨hvH, hvc⟩) hv2 hv1
  -- `|C_H(X)| = |C_Q(X)||C_D(X)|` with `|C_D(X)|` odd
  rw [hyp.card_cH_eq hXD] at heven
  have hoddD : Odd (Nat.card ↥(hyp.D ⊓ Subgroup.centralizer (X : Set G))) :=
    Nat.coprime_two_left.mp
      ((Nat.coprime_two_left.mpr hyp.D_odd).coprime_dvd_right
        (Subgroup.card_dvd_of_le inf_le_left))
  rcases Nat.even_mul.mp heven with h | h
  · exact h
  · exact absurd h (Nat.not_even_iff_odd.mpr hoddD)

/-! ## Prop 6 (c): `X` is conjugate in `D` to a subgroup of `V` (p. 102) -/

/-- **Peterfalvi Part II, Ch. I Prop 6 (c)** (p. 102) — `X` is conjugate in
`D` to a subgroup of `V`.  By (b) and Cauchy, `C_Q(X)` contains an
involution `u`; by Prop 3, `u = s^k` for some `k ∈ K`; then
`X ≤ C_D(s^k)`, i.e. `X^k ≤ C_D(s) = V` (Prop 5). -/
theorem exists_conj_mem_D_map_le_V (hXD : X ≤ hyp.D)
    (h3 : 3 ≤ (fixedPoints X Ω).ncard) :
    ∃ k ∈ hyp.D, X.map (MulAut.conj k).toMonoidHom ≤ hyp.V := by
  classical
  obtain ⟨u, hu, hu2, hu1⟩ :=
    exists_sq_eq_one_of_even_card (hyp.even_card_cQ hXD h3)
  obtain ⟨huQ, huc⟩ := Subgroup.mem_inf.mp hu
  -- `u = s^k` for some `k ∈ K` (Prop 3)
  have humem : u ∈ {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} :=
    ⟨hu2, hu1, hyp.Q_le_H huQ⟩
  rw [← hyp.image_conj_KSet_eq_involutions_H hyp.distinguishedInvolution_mem_H
    hyp.distinguishedInvolution_sq hyp.distinguishedInvolution_ne_one] at humem
  obtain ⟨k, hkK, hks⟩ := humem
  refine ⟨k, hkK.1, ?_⟩
  rw [hyp.V_eq_centralizer_distinguishedInvolution]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  have heq : (MulAut.conj k).toMonoidHom x = k * x * k⁻¹ := rfl
  rw [heq]
  refine Subgroup.mem_inf.mpr
    ⟨hyp.D.mul_mem (hyp.D.mul_mem hkK.1 (hXD hx)) (hyp.D.inv_mem hkK.1), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxu : x * u = u * x := Subgroup.mem_centralizer_iff.mp huc x hx
  have hs_eq : hyp.distinguishedInvolution = k * u * k⁻¹ := by
    rw [← hks]; group
  rw [hs_eq]
  exact calc (k * x * k⁻¹) * (k * u * k⁻¹) = k * (x * u) * k⁻¹ := by group
    _ = k * (u * x) * k⁻¹ := by rw [hxu]
    _ = (k * u * k⁻¹) * (k * x * k⁻¹) := by group

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
