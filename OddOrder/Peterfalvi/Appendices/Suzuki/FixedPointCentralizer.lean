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

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
