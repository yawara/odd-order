/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3StepFifteen

/-!
# Peterfalvi Part II, Ch. IV §2, step (13): the sequence of (11) in coordinates

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §2, p. 126.

`PSU3Sequence` builds the sequence of step (11) inside the group and `PSU3FieldArithmetic`
gives the closed form `u_i = c_{i-1}/c_i` of step (13); this file is the bridge, i.e. the
book's "By (11), we then obtain, by induction on `i`, …".

The normalized coordinate of the `i`-th entry,

  `U_i = coord(z_i) / coord(s)`,

satisfies the book's recursion `U_{i+1} = 1/(α + U_i)` with `U_0 = 0` — because the step
of (11) picks `a ∈ K` with `a s a⁻¹ = y z_i` and sets `z_{i+1} = a⁻¹ s a`, and the
`K`-action is multiplication by the scalar `μ(a)^d` in the coordinate
(`centerCoord_conj`).  So `μ(a)^d = α + U_i` and `U_{i+1} = μ(a)^{-d}`.

`betaRatio` satisfies the same recursion (`betaRatio_succ`, the book's (13)), so the two
agree as long as the sequence runs.

## Main results

* `Hypothesis.IsCenterCoordAction` — the scalar-action hypothesis carried around by
  `centerCoord_conj`, named.
* `Hypothesis.centerCoord_conj_eq` — the `K`-action in coordinates, stated with the
  conjugate given by an equation rather than by the shape `a x a⁻¹`.
* `Hypothesis.stepElevenCoord` — the normalized coordinate `U_i`.
* `Hypothesis.stepElevenCoord_succ` — the recursion `U_{i+1} = 1/(α + U_i)`.
* `Hypothesis.stepElevenCoord_eq_betaRatio` — `U_i` is the book's `u_{i+1}`.
* `Hypothesis.stepElevenSeq_ne_one_iff` — the stopping rule in coordinates: the sequence
  runs at `i` exactly when `β^{i+2} ≠ 1`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

/-- **The scalar form of the `K`-action on the centre coordinate**, as produced by
`exists_center_coordinate_equiv`: conjugation by `k` multiplies the coordinate by
`μ(k)^d`.

Named so that the statements of this file do not have to repeat it. -/
def IsCenterCoordAction {m : ℕ} (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ) : Prop :=
  ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
    ((ι (Additive.ofMul (hyp.centerKHom k z)) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
      = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
        ((ι (Additive.ofMul z) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)

/-- The coordinate depends only on the element, not on the membership proof. -/
theorem centerCoord_congr {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    {x x' : G} (hx : x ∈ hyp.Q0) (hx' : x' ∈ hyp.Q0) (heq : x = x') :
    hyp.centerCoord s M ι hx = hyp.centerCoord s M ι hx' := by
  subst heq
  rfl

/-- **The `K`-action in coordinates**, with the conjugate identified by an equation.

`centerCoord_conj` states the same fact with the conjugate written literally as
`a x a⁻¹`, which forces callers to match that shape; here it is enough to know
`a x a⁻¹ = w`. -/
theorem centerCoord_conj_eq {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : hyp.IsCenterCoordAction M ι d)
    {a : G} (ha : a ∈ hyp.K) {x w : G} (hx : x ∈ hyp.Q0) (hw : w ∈ hyp.Q0)
    (hval : a * x * a⁻¹ = w) :
    hyp.centerCoord s M ι hw
      = ((M.mu (hyp.kActor ha, 1) ^ d : M.Eˣ) : M.E) * hyp.centerCoord s M ι hx := by
  rw [hyp.centerCoord_congr s M ι hw (hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D ha) hx) hval.symm]
  exact hyp.centerCoord_conj s M ι d hequiv ha hx

/-- `kActor` inverts: `conjQByK` is a homomorphism. -/
theorem kActor_inv {a : G} (ha : a ∈ hyp.K) (hai : a⁻¹ ∈ hyp.K) :
    hyp.kActor hai = (hyp.kActor ha)⁻¹ := by
  apply Subtype.ext
  change hyp.conjQByK ⟨a⁻¹, hai⟩ = (hyp.conjQByK ⟨a, ha⟩)⁻¹
  rw [← map_inv]
  rfl

/-- The coordinate of `s` is nonzero: `s ≠ 1`. -/
theorem centerCoord_distinguishedInvolution_ne_zero {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) :
    hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0 ≠ 0 := by
  rw [Ne, hyp.centerCoord_eq_zero_iff s M ι]
  exact hyp.distinguishedInvolution_ne_one

/-- **The normalized coordinate of the `i`-th entry of the sequence of (11)** — the book's
`u_{i+1}`, with the model's `coord s` divided out (the book normalizes `s = (0,1)`, so it
does not see the division). -/
noncomputable def stepElevenCoord {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    {ζ y : G} (hζ : ζ ∈ hyp.W) (hyQ0 : y ∈ hyp.Q0) (n : ℕ) : M.E :=
  hyp.centerCoord s M ι (hyp.stepElevenSeq_mem hζ hyQ0 n).1
    / hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0

/-- `U₀ = 0`, the book's `u₁ = 0`. -/
@[simp] theorem stepElevenCoord_zero {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    {ζ y : G} (hζ : ζ ∈ hyp.W) (hyQ0 : y ∈ hyp.Q0) :
    hyp.stepElevenCoord s M ι hζ hyQ0 0 = 0 := by
  rw [stepElevenCoord,
    (hyp.centerCoord_eq_zero_iff s M ι (hyp.stepElevenSeq_mem hζ hyQ0 0).1).mpr rfl, zero_div]

/-- **The recursion of (11) in coordinates** (Peterfalvi Part II, p. 125):
`U_{i+1} = 1/(α + U_i)`, where `α = coord(y)/coord(s)`.

The step picks `a ∈ K` with `a s a⁻¹ = y z_i`, so in coordinates `μ(a)^d = α + U_i`; and
`z_{i+1} = a⁻¹ s a`, whose coordinate is `μ(a)^{-d}`. -/
theorem stepElevenCoord_succ {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : hyp.IsCenterCoordAction M ι d)
    {ζ y : G} (hζ : ζ ∈ hyp.W) (hyQ0 : y ∈ hyp.Q0) (n : ℕ)
    (hne : y * (hyp.stepElevenSeq ζ y n).1 ≠ 1) :
    hyp.stepElevenCoord s M ι hζ hyQ0 (n + 1)
      = (hyp.centerCoord s M ι hyQ0
          / hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0
        + hyp.stepElevenCoord s M ι hζ hyQ0 n)⁻¹ := by
  classical
  have hσ0 := hyp.centerCoord_distinguishedInvolution_ne_zero s M ι
  obtain ⟨a, haK, ha, hstep⟩ := hyp.stepElevenSeq_succ_of_ne ζ y n
    (hyp.exists_mem_K_conj_eq_mul hyQ0 (hyp.stepElevenSeq_mem hζ hyQ0 n).1 hne)
  have haiK : a⁻¹ ∈ hyp.K := hyp.K.inv_mem haK
  -- the scalar of `a` is `α + U_n`
  have h1 : ((M.mu (hyp.kActor haK, 1) ^ d : M.Eˣ) : M.E)
      * hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0
      = hyp.centerCoord s M ι hyQ0
        + hyp.centerCoord s M ι (hyp.stepElevenSeq_mem hζ hyQ0 n).1 := by
    rw [← hyp.centerCoord_mul s M ι hyQ0 (hyp.stepElevenSeq_mem hζ hyQ0 n).1]
    exact (hyp.centerCoord_conj_eq s M ι d hequiv haK hyp.distinguishedInvolution_mem_Q0
      (hyp.Q0.mul_mem hyQ0 (hyp.stepElevenSeq_mem hζ hyQ0 n).1) ha).symm
  -- the coordinate of `z_{n+1}` is the inverse scalar
  have h2 : hyp.centerCoord s M ι (hyp.stepElevenSeq_mem hζ hyQ0 (n + 1)).1
      = ((M.mu (hyp.kActor haiK, 1) ^ d : M.Eˣ) : M.E)
        * hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0 := by
    refine hyp.centerCoord_conj_eq s M ι d hequiv haiK hyp.distinguishedInvolution_mem_Q0
      (hyp.stepElevenSeq_mem hζ hyQ0 (n + 1)).1 ?_
    have hfst : (hyp.stepElevenSeq ζ y (n + 1)).1
        = a⁻¹ * hyp.distinguishedInvolution * a := by rw [hstep]
    rw [hfst]
    group
  have hpair : ((hyp.kActor haiK, (1 : ↥hyp.W)))
      = ((hyp.kActor haK, (1 : ↥hyp.W)))⁻¹ := by
    rw [hyp.kActor_inv haK haiK]
    simp
  have hinvval : ((M.mu (hyp.kActor haiK, 1) ^ d : M.Eˣ) : M.E)
      = (((M.mu (hyp.kActor haK, 1) ^ d : M.Eˣ) : M.E))⁻¹ := by
    rw [hpair, map_inv, inv_zpow, Units.val_inv_eq_inv_val]
  -- assemble
  have hval : ((M.mu (hyp.kActor haK, 1) ^ d : M.Eˣ) : M.E)
      = hyp.centerCoord s M ι hyQ0
          / hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0
        + hyp.stepElevenCoord s M ι hζ hyQ0 n := by
    rw [stepElevenCoord, ← add_div, ← h1, mul_div_assoc, div_self hσ0, mul_one]
  rw [stepElevenCoord, h2, hinvval, ← hval, mul_div_assoc, div_self hσ0, mul_one]

/-- **Step (13)** (Peterfalvi Part II, p. 126): the sequence of (11) is the closed form
`u_i = c_{i-1}/c_i`.

Both satisfy `U_{i+1} = 1/(α + U_i)` from `U_0 = 0`: the group side by
`stepElevenCoord_succ`, the field side by `betaRatio_succ`.  The hypotheses are the two
conditions under which the respective recursions are available — the sequence has not yet
stopped, and `c_{i+1} ≠ 0`, i.e. `β^{i+1} ≠ 1`. -/
theorem stepElevenCoord_eq_betaRatio {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : hyp.IsCenterCoordAction M ι d)
    {ζ y : G} (hζ : ζ ∈ hyp.W) (hyQ0 : y ∈ hyp.Q0) {β : M.E} (hβ : β ≠ 0)
    (hα : β + β⁻¹
      = hyp.centerCoord s M ι hyQ0
        / hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0)
    (n : ℕ) (hns : ∀ i < n, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1)
    (hpow : ∀ i, 1 ≤ i → i ≤ n → β ^ i ≠ 1) :
    hyp.stepElevenCoord s M ι hζ hyQ0 n = betaRatio β n := by
  have h2 : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  induction n with
  | zero => rw [hyp.stepElevenCoord_zero s M ι hζ hyQ0, betaRatio_zero h2]
  | succ n ih =>
    have hprev := ih (fun i hi => hns i (by omega)) (fun i h1 h2 => hpow i h1 (by omega))
    have hcne : betaSum β (n + 1) ≠ 0 := by
      rw [Ne, betaSum_eq_zero_iff h2 hβ]
      exact hpow (n + 1) (by omega) (by omega)
    rw [hyp.stepElevenCoord_succ s M ι d hequiv hζ hyQ0 n (hns n (by omega)), hprev,
      betaRatio_succ h2 hβ hα n hcne]

/-- **The stopping rule in coordinates**: the sequence of (11) can take another step at
index `n` exactly when `β^{n+2} ≠ 1`.

The step is available when `y z_n ≠ 1`, i.e. when `α + U_n ≠ 0`; and
`α + u_{n+1} = c_{n+2}/c_{n+1}` by `add_betaSum_div`, which vanishes exactly when
`β^{n+2} = 1`. -/
theorem stepElevenSeq_ne_one_iff {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : hyp.IsCenterCoordAction M ι d)
    {ζ y : G} (hζ : ζ ∈ hyp.W) (hyQ0 : y ∈ hyp.Q0) {β : M.E} (hβ : β ≠ 0)
    (hα : β + β⁻¹
      = hyp.centerCoord s M ι hyQ0
        / hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0)
    (n : ℕ) (hns : ∀ i < n, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1)
    (hpow : ∀ i, 1 ≤ i → i ≤ n + 1 → β ^ i ≠ 1) :
    y * (hyp.stepElevenSeq ζ y n).1 ≠ 1 ↔ β ^ (n + 2) ≠ 1 := by
  have h2 : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have hσ0 := hyp.centerCoord_distinguishedInvolution_ne_zero s M ι
  have hU := hyp.stepElevenCoord_eq_betaRatio s M ι d hequiv hζ hyQ0 hβ hα n hns
    (fun i hi hin => hpow i hi (by omega))
  have hcne : betaSum β (n + 1) ≠ 0 := by
    rw [Ne, betaSum_eq_zero_iff h2 hβ]
    exact hpow (n + 1) (by omega) le_rfl
  -- the stopping rule says `coord y + coord z_n = 0`
  have hzero : y * (hyp.stepElevenSeq ζ y n).1 = 1
      ↔ hyp.centerCoord s M ι hyQ0
          / hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0
        + hyp.stepElevenCoord s M ι hζ hyQ0 n = 0 := by
    rw [stepElevenCoord, ← add_div, div_eq_zero_iff]
    rw [← hyp.centerCoord_mul s M ι hyQ0 (hyp.stepElevenSeq_mem hζ hyQ0 n).1,
      hyp.centerCoord_eq_zero_iff s M ι]
    simp [hσ0]
  rw [Ne, hzero, hU, ← hα]
  simp only [betaRatio]
  rw [add_betaSum_div h2 hβ rfl n hcne, div_eq_zero_iff]
  constructor
  · intro hh hpow2
    exact hh (Or.inl ((betaSum_eq_zero_iff h2 hβ (n + 2)).mpr hpow2))
  · intro hh hor
    rcases hor with hor | hor
    · exact hh ((betaSum_eq_zero_iff h2 hβ (n + 2)).mp hor)
    · exact hcne hor

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
