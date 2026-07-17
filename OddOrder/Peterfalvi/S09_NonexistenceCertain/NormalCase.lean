import OddOrder.Peterfalvi.S09_NonexistenceCertain.Hypothesis71

/-!
# Peterfalvi (7.6)-(7.7) — normal-subgroup case A = H#

Split from the former monolithic `OddOrder.Peterfalvi.S09_NonexistenceCertain` (directory split,
issue 0103).
-/
namespace OddOrder.Peterfalvi.S09
open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)
open OddOrder.GroupTheory (IsTISubset)
open OddOrder.RepresentationTheory
open scoped Pointwise

variable {G : Type*} [Group G]


section Section_7_6_to_7_7

/-! ### (7.6)-(7.7): normal-subgroup case `A = H^#`

Specializes Hypothesis (7.1) to the situation where `A = H \ {1}` for a normal
subgroup `H ⊴ L`, with the family `T = {ζ_0, ..., ζ_n}` of induced characters
`Ind_H^L θ`.  The headline outputs are:

* `Hypothesis76` — the (7.6) data bundle, carrying `H ⊴ L`, `A = H^#`, the
  family `(ζ_i, d_i)` of induced characters and degree ratios, the support
  proofs that `ψ_i = ζ_i - d_i ζ_0 ∈ CF(L,A)`, and the **(7.7.a) certificate**
  expressing `χ^ρ` linearly through `(ζ_i)_{i≥1}` with coefficients
  `c̄_i / ‖ζ_i‖²` (where `c_i = (ψ_i^τ, χ)`).

* `Hypothesis76.chiRho_explicit_formula` — Peterfalvi (7.7.a): for `x ∈ A`,
  `χ^ρ(x) = Σ_{i≥1} c̄_i / ‖ζ_i‖² · ζ_i(x)`.

* `Hypothesis76.chiRho_norm_sq_double_sum` — Peterfalvi (7.7.b): the
  double-sum form
  `‖χ^ρ‖² = Σ_{i,j≥1} c̄_i c_j / ‖ζ_i‖² ‖ζ_j‖² · ((ζ_i, ζ_j) - ζ_i(1)·conj(ζ_j(1))/|L|)`,
  obtained by inner-product expansion of (7.7.a) using `ζ_i` supported on `H`.

The (7.7.a) statement is carried as a structural certificate (`chiRho_decomp`)
rather than proved here: it encodes Peterfalvi's basis argument
("ψ_i span CF(L,A)") which depends on the induced/restricted character
decomposition theory not yet formalized in this file.  Once that decomposition
is available the field can be discharged by a constructor.  (7.7.b) is then
proved here as a direct corollary by inner-product expansion. -/

/-- **Peterfalvi (7.6) Hypothesis.**

Carries (in addition to Hypothesis (7.1) + the Dade-isometry property):
* a normal subgroup `H ⊴ L` (with `H ≤ L` and `L`-conjugation closure);
* the assumption `A = H \ {1}`;
* the family `(ζ_i)_{i ≤ n}` of distinct induced characters `Ind_H^L θ` and
  the degree ratios `d_i` (so `ζ_i(1) = d_i · ζ_0(1)`);
* the support fact that `ζ_i` vanishes outside `H` (induced characters from a
  normal subgroup are supported on `H`);
* the (7.7.a) decomposition certificate
  (`chiRho_decomp` — Peterfalvi's basis argument applied to `CF(L,A)`).

Note: `ζ_i` are stored as raw class functions on `L` (without identifying them
with specific induced characters); the support and degree-ratio fields are the
properties needed to derive (7.7.a)-(7.7.b). -/
structure Hypothesis76 (G : Type*) [Group G] [Fintype G]
    (A : Set G) (L : Subgroup G) [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  /-- The underlying Hypothesis (7.1) with chosen Dade map `τ`. -/
  hyp71 : Hypothesis71 G A L
  /-- `τ` is a Dade isometry. -/
  isDadeIsometry : OddOrder.Peterfalvi.S04.IsDadeIsometry
    (G := G) (k := ℂ) (L := L) hyp71.τ
  /-- The normal subgroup `H` of `L`. -/
  H : Subgroup G
  /-- `H ≤ L`. -/
  H_le_L : H ≤ L
  /-- `H ⊴ L`: `L` normalizes `H` (so `H.subgroupOf L` is normal in `L`). -/
  H_normal_in_L : ∀ (l : L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H
  /-- `A = H \ {1}` (the "sharp"). -/
  A_eq_H_sharp : A = (H : Set G) \ {1}
  /-- Cardinality of the family `T = {ζ_0, ..., ζ_n}` minus one. -/
  n : ℕ
  /-- The family `T = {ζ_0, ..., ζ_n}` of induced characters (distinct). -/
  zeta : Fin (n + 1) → ClassFunction L ℂ
  /-- Degree ratios `d_i = ζ_i(1) / ζ_0(1)`. -/
  d : Fin (n + 1) → ℂ
  /-- `ζ_i` vanishes outside `H` (a normal subgroup): `Ind_H^L θ` is supported
  on `H` since `H = ⋃_g g H g⁻¹`. -/
  zeta_eq_zero_of_not_mem_H : ∀ (i : Fin (n + 1)) (x : L),
    (x : G) ∉ H → zeta i x = 0
  /-- The degree-ratio relation `ζ_i(1) = d_i · ζ_0(1)`. -/
  zeta_one_eq_d_mul : ∀ i : Fin (n + 1), zeta i (1 : L) = d i * zeta 0 (1 : L)
  /-- `ψ_i = ζ_i - d_i ζ_0` is supported on `A` (= `H \ {1}`).  Follows from
  `zeta_eq_zero_of_not_mem_H` + `zeta_one_eq_d_mul` + `A_eq_H_sharp`; carried
  as a field so the (7.7.a) certificate can name the `SupportedClassFunctions`
  value inline. -/
  psi_support : ∀ i : Fin (n + 1),
    (zeta i - d i • zeta 0).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L
  /-- **Induced-ness of the family** (Peterfalvi (7.6): `T = {Ind_H^L θ}`): each `ζ_i` is the
  induction of an irreducible character of `H`.  Stated with the canonical `Fintype`/`Invertible`
  instances (both classes are subsingletons, so consumers can bridge to their own instances by
  `Subsingleton.elim`).  This is what the Peterfalvi (13.5.a) integrality reads: `Res_H ζ_i` is
  `‖ζ_i‖²` times the sum of the `L`-conjugates of `θ_i` (Mackey), a genuine character of `H`. -/
  zeta_induced : ∀ i : Fin (n + 1),
    haveI : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
    haveI : Invertible (Nat.card ↥(H.subgroupOf L) : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    ∃ θ : IrreducibleCharacter ↥(H.subgroupOf L),
      zeta i = ClassFunction.induce (H.subgroupOf L) (θ : ClassFunction _ ℂ)
  /-- **Distinctness of the family** (Peterfalvi (7.6): the `ζ_i` are *distinct* induced
  characters): the enumeration is injective.  What pins "`i ≠ i₁ ⟹ ζ_i ≠ λ`" in the (13.5)
  middle-coefficient computation (`lambda_tau1_cCoeff`). -/
  zeta_injective : Function.Injective zeta
  /-- **Exhaustiveness of the family** (Peterfalvi (7.6): `T = {Ind_H^L θ | θ ∈ Irr H}` ranges
  over *all* `θ`): every induced irreducible appears at some family index — the converse
  direction to `zeta_induced`, same canonical-instance convention.  This is what places the
  (13.5)/(13.6) distinguished `λ = Ind_H^S θ` at a family index (`exists_lambda_index`). -/
  zeta_family_cover :
    haveI : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
    haveI : Invertible (Nat.card ↥(H.subgroupOf L) : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    ∀ φ : IrreducibleCharacter ↥(H.subgroupOf L),
      ∃ i : Fin (n + 1),
        zeta i = ClassFunction.induce (H.subgroupOf L) (φ : ClassFunction _ ℂ)
  /-- **Peterfalvi (7.7.a) certificate.**  For every `χ ∈ CF(G)` and `x ∈ A`,
  `χ^ρ(x) = Σ_{i≥1} c̄_i / ‖ζ_i‖² · ζ_i(x)`, where
  `c_i = (ψ_i^τ, χ)_G` and `ψ_i = ζ_i - d_i ζ_0`.

  Encodes Peterfalvi's CF(L,A)-basis argument (see proof of (7.7.a), p.39):
  the ψ_i (for i ≥ 1) span CF(L,A) modulo `ψ_0 = 0`, allowing the
  inner-product equations
  `c_j = (ψ_j, χ^ρ)` to determine `χ^ρ` on `A` linearly through the `ζ_i`. -/
  chiRho_decomp : ∀ (χ : ClassFunction G ℂ) (x : L), (x : G) ∈ A →
    hyp71.chiRho χ x =
      ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)),
        (star (ClassFunction.inner
          (hyp71.τ ⟨zeta i - d i • zeta 0, psi_support i⟩) χ) /
          ClassFunction.inner (zeta i) (zeta i)) * zeta i x

namespace Hypothesis76

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G} [Fintype L]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- `ψ_i = ζ_i - d_i · ζ_0` as a member of `CF(L,A)`. -/
noncomputable def psiSupp (H76 : Hypothesis76 G A L) (i : Fin (H76.n + 1)) :
    OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L :=
  ⟨H76.zeta i - H76.d i • H76.zeta 0, H76.psi_support i⟩

@[simp] theorem psiSupp_coe (H76 : Hypothesis76 G A L) (i : Fin (H76.n + 1)) :
    ((H76.psiSupp i : OddOrder.Peterfalvi.S04.SupportedClassFunctions
        (G := G) ℂ A L) : ClassFunction L ℂ) =
      H76.zeta i - H76.d i • H76.zeta 0 := rfl

/-- Peterfalvi's coefficient `c_i = (ψ_i^τ, χ)_G` for `1 ≤ i ≤ n`.  Also defined
for `i = 0`, where it equals zero (since `ψ_0 = ζ_0 - d_0 ζ_0 = 0` after the
degree-ratio identity, but we do not enforce `d_0 = 1` here). -/
noncomputable def cCoeff (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) (i : Fin (H76.n + 1)) : ℂ :=
  ClassFunction.inner (H76.hyp71.τ (H76.psiSupp i)) χ

/-- The squared norm `‖ζ_i‖² = (ζ_i, ζ_i)_L` as a complex number. -/
noncomputable def zetaNormSq (H76 : Hypothesis76 G A L) (i : Fin (H76.n + 1)) : ℂ :=
  ClassFunction.inner (H76.zeta i) (H76.zeta i)

/-- **Peterfalvi (7.7.a).**  For `χ ∈ CF(G)` and `x ∈ A`,
`χ^ρ(x) = Σ_{i ≥ 1} c̄_i / ‖ζ_i‖² · ζ_i(x)`. -/
theorem chiRho_explicit_formula (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) {x : L} (hx : (x : G) ∈ A) :
    H76.hyp71.chiRho χ x =
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i x :=
  H76.chiRho_decomp χ x hx

/-- The class function `S_χ = Σ_{i ≥ 1} c̄_i / ‖ζ_i‖² · ζ_i ∈ CF(L)`.  By
(7.7.a), `S_χ` agrees with `χ^ρ` on `A`.  Off `H`, `S_χ` vanishes (each `ζ_i`
does), and on `H \ A = {1}`, `S_χ(1) = Σ_{i≥1} c̄_i d_i ζ_0(1) / ‖ζ_i‖²` is in
general nonzero.  Used to package (7.7.b) via inner-product expansion. -/
noncomputable def chiRhoLinearCombo (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) : ClassFunction L ℂ :=
  ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
    (star (H76.cCoeff χ i) / H76.zetaNormSq i) • H76.zeta i

omit [Fintype G] [Fintype L] [Invertible (Nat.card L : ℂ)]
  [Invertible (Nat.card G : ℂ)] in
/-- Pointwise evaluation of a finite sum of class functions.  Provable by
straightforward induction; collected here as a local helper. -/
private theorem classFunction_finsum_apply
    {ι : Type*} (s : Finset ι) (f : ι → ClassFunction L ℂ) (x : L) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
          ClassFunction.add_apply, ih]

@[simp] theorem chiRhoLinearCombo_apply (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) (x : L) :
    H76.chiRhoLinearCombo χ x =
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i x := by
  classical
  unfold chiRhoLinearCombo
  rw [classFunction_finsum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ClassFunction.smul_apply]

/-- `S_χ` vanishes outside `H` (as a subset of `L`). -/
theorem chiRhoLinearCombo_eq_zero_of_not_mem_H (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) {x : L} (hx : (x : G) ∉ H76.H) :
    H76.chiRhoLinearCombo χ x = 0 := by
  classical
  rw [chiRhoLinearCombo_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [H76.zeta_eq_zero_of_not_mem_H i x hx, mul_zero]

/-- `1 ∉ A` (since `A = H \ {1}`). -/
theorem one_not_mem_A (H76 : Hypothesis76 G A L) : (1 : G) ∉ A := by
  rw [H76.A_eq_H_sharp]
  rintro ⟨_, h⟩
  exact h rfl

/-- For `x ∈ L` with `(x : G) ∈ H` and `(x : G) ≠ 1`, we have `(x : G) ∈ A`. -/
theorem mem_A_of_mem_H_and_ne_one (H76 : Hypothesis76 G A L) {x : L}
    (hxH : (x : G) ∈ H76.H) (hx1 : (x : G) ≠ 1) : (x : G) ∈ A := by
  rw [H76.A_eq_H_sharp]
  exact ⟨hxH, hx1⟩

/-- The (7.7.a) substitution: `χ^ρ(x) = S_χ(x)` for `x ∈ A`. -/
theorem chiRho_eq_chiRhoLinearCombo_of_mem_A (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) {x : L} (hx : (x : G) ∈ A) :
    H76.hyp71.chiRho χ x = H76.chiRhoLinearCombo χ x := by
  rw [chiRhoLinearCombo_apply]
  exact H76.chiRho_explicit_formula χ hx

/-- `χ^ρ` vanishes outside `H` (since `A ⊆ H`). -/
theorem chiRho_eq_zero_of_not_mem_H (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) {x : L} (hx : (x : G) ∉ H76.H) :
    H76.hyp71.chiRho χ x = 0 := by
  have hxA : (x : G) ∉ A := by
    intro h
    rw [H76.A_eq_H_sharp] at h
    exact hx h.1
  exact H76.hyp71.chiRho_of_not_mem χ hxA

open scoped Classical in
/-- **Pointwise key lemma** for (7.7.b): the difference `χ^ρ - S_χ` is
supported at `(1 : L)`, where its value is `-S_χ(1)`. -/
theorem chiRho_sub_chiRhoLinearCombo_apply (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) (x : L) :
    H76.hyp71.chiRho χ x - H76.chiRhoLinearCombo χ x =
      if x = 1 then -H76.chiRhoLinearCombo χ 1 else 0 := by
  by_cases hx1 : x = 1
  · subst hx1
    have h_chiRho_one : H76.hyp71.chiRho χ 1 = 0 :=
      H76.hyp71.chiRho_of_not_mem χ (by
        rw [show ((1 : L) : G) = (1 : G) from rfl]
        exact H76.one_not_mem_A)
    rw [h_chiRho_one, if_pos rfl, zero_sub]
  · rw [if_neg hx1]
    by_cases hxH : (x : G) ∈ H76.H
    · -- (x : G) ∈ H and x ≠ 1, so we need (x : G) ≠ 1
      have hx_coe_ne_one : (x : G) ≠ 1 := by
        intro h
        apply hx1
        ext
        rw [h]
        rfl
      have hxA : (x : G) ∈ A := H76.mem_A_of_mem_H_and_ne_one hxH hx_coe_ne_one
      rw [H76.chiRho_eq_chiRhoLinearCombo_of_mem_A χ hxA, sub_self]
    · -- (x : G) ∉ H: both terms zero
      rw [H76.chiRho_eq_zero_of_not_mem_H χ hxH,
          H76.chiRhoLinearCombo_eq_zero_of_not_mem_H χ hxH, sub_self]

/-- The inner sum `Σ_{x ∈ L} χ^ρ(x) · conj(χ^ρ(x))` equals
`Σ_{x} S_χ(x) · conj(S_χ(x)) - S_χ(1) · conj(S_χ(1))`, since they differ only
at `x = 1`. -/
theorem innerSum_chiRho_eq (H76 : Hypothesis76 G A L) (χ : ClassFunction G ℂ) :
    ClassFunction.innerSum (H76.hyp71.chiRhoCF χ) (H76.hyp71.chiRhoCF χ) =
      ClassFunction.innerSum (H76.chiRhoLinearCombo χ) (H76.chiRhoLinearCombo χ) -
        H76.chiRhoLinearCombo χ 1 * star (H76.chiRhoLinearCombo χ 1) := by
  classical
  -- Both sides are Σ_{x ∈ L} f(x); compare pointwise.
  have hpt : ∀ x : L,
      (H76.hyp71.chiRhoCF χ) x * star ((H76.hyp71.chiRhoCF χ) x) =
        H76.chiRhoLinearCombo χ x * star (H76.chiRhoLinearCombo χ x) -
          (if x = 1 then
            H76.chiRhoLinearCombo χ 1 * star (H76.chiRhoLinearCombo χ 1)
           else 0) := by
    intro x
    -- chiRhoCF x = chiRho x; chiRhoCF_apply lets us rewrite the LHS.
    rw [Hypothesis71.chiRhoCF_apply]
    by_cases hx1 : x = 1
    · subst hx1
      have h_chi : H76.hyp71.chiRho χ 1 = 0 :=
        H76.hyp71.chiRho_of_not_mem χ (by
          rw [show ((1 : L) : G) = (1 : G) from rfl]
          exact H76.one_not_mem_A)
      rw [h_chi, star_zero, mul_zero, if_pos rfl, sub_self]
    · rw [if_neg hx1]
      by_cases hxH : (x : G) ∈ H76.H
      · have hx_coe_ne_one : (x : G) ≠ 1 := by
          intro h
          apply hx1
          ext
          rw [h]
          rfl
        have hxA : (x : G) ∈ A := H76.mem_A_of_mem_H_and_ne_one hxH hx_coe_ne_one
        rw [H76.chiRho_eq_chiRhoLinearCombo_of_mem_A χ hxA, sub_zero]
      · rw [H76.chiRho_eq_zero_of_not_mem_H χ hxH,
            H76.chiRhoLinearCombo_eq_zero_of_not_mem_H χ hxH,
            star_zero, mul_zero, sub_zero]
  -- Apply hpt and sum
  unfold ClassFunction.innerSum
  rw [show (∑ g : L, (H76.hyp71.chiRhoCF χ) g * star ((H76.hyp71.chiRhoCF χ) g)) =
      ∑ g : L, (H76.chiRhoLinearCombo χ g * star (H76.chiRhoLinearCombo χ g) -
        (if g = 1 then
          H76.chiRhoLinearCombo χ 1 * star (H76.chiRhoLinearCombo χ 1)
         else 0)) from
    Finset.sum_congr rfl (fun g _ => hpt g)]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_ite_eq' Finset.univ (1 : L) (fun _ =>
    H76.chiRhoLinearCombo χ 1 * star (H76.chiRhoLinearCombo χ 1))]
  rw [if_pos (Finset.mem_univ _)]

/-- **Inner-product of `S_χ` with itself** as a double sum over `i, j ≥ 1`:
`(S_χ, S_χ) = Σ_{i, j ≥ 1} (c̄_i c_j / (‖ζ_i‖² ‖ζ_j‖²)) · (ζ_i, ζ_j)`.

(`star_div` cancels the conjugate in the smul-right, using that `‖ζ_i‖²` is
fixed by `star` — true here because `inner_self_eq_ofReal`.) -/
theorem inner_chiRhoLinearCombo_self
    (H76 : Hypothesis76 G A L) (χ : ClassFunction G ℂ) :
    ClassFunction.inner (H76.chiRhoLinearCombo χ) (H76.chiRhoLinearCombo χ) =
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        ∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          (star (H76.cCoeff χ i) * H76.cCoeff χ j /
            (H76.zetaNormSq i * H76.zetaNormSq j)) *
            ClassFunction.inner (H76.zeta i) (H76.zeta j) := by
  classical
  unfold chiRhoLinearCombo
  -- Expand inner of two sums as a double sum, via `inner_sum_left` then
  -- `inner_sum_right` on each summand.
  rw [OddOrder.RepresentationTheory.inner_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [OddOrder.RepresentationTheory.inner_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right]
  -- Goal: (star c_i / ‖ζ_i‖²) * (star (star c_j / ‖ζ_j‖²) * (ζ_i, ζ_j))
  --       = (star c_i * c_j / (‖ζ_i‖² * ‖ζ_j‖²)) * (ζ_i, ζ_j)
  rw [show star ((star (H76.cCoeff χ j) / H76.zetaNormSq j) : ℂ) =
        H76.cCoeff χ j / star (H76.zetaNormSq j) from by
    rw [star_div₀, star_star]]
  -- Now reduce: ‖ζ_j‖² is fixed by star (since inner_self is real).
  have h_star_norm : star (H76.zetaNormSq j) = H76.zetaNormSq j :=
    Hypothesis71.ClassFunction.star_inner_self _
  rw [h_star_norm]
  ring

/-- The value `S_χ(1) · conj(S_χ(1))` as a double sum.  Uses
`ζ_i(1) = d_i ζ_0(1)` and `star (‖ζ_i‖²) = ‖ζ_i‖²`. -/
theorem chiRhoLinearCombo_one_mul_star (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) :
    H76.chiRhoLinearCombo χ 1 * star (H76.chiRhoLinearCombo χ 1) =
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        ∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          (star (H76.cCoeff χ i) * H76.cCoeff χ j /
            (H76.zetaNormSq i * H76.zetaNormSq j)) *
            (H76.zeta i 1 * star (H76.zeta j 1)) := by
  classical
  rw [chiRhoLinearCombo_apply]
  rw [star_sum]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  -- LHS term: (star c_i / ‖ζ_i‖²) * ζ_i(1) * star ((star c_j / ‖ζ_j‖²) * ζ_j(1))
  rw [show star (((star (H76.cCoeff χ j) / H76.zetaNormSq j) * H76.zeta j 1) : ℂ) =
        (H76.cCoeff χ j / star (H76.zetaNormSq j)) * star (H76.zeta j 1) from by
    rw [star_mul', star_div₀, star_star]]
  have h_star_norm : star (H76.zetaNormSq j) = H76.zetaNormSq j :=
    Hypothesis71.ClassFunction.star_inner_self _
  rw [h_star_norm]
  ring

/-- **Peterfalvi (7.7.b).**  `‖χ^ρ‖²` has the double-sum form:
`‖χ^ρ‖² = Σ_{i,j ≥ 1} c̄_i c_j / ‖ζ_i‖² ‖ζ_j‖² · ((ζ_i, ζ_j) - ζ_i(1) · conj(ζ_j(1)) / |L|)`.

Proof: by (7.7.a), `χ^ρ` agrees with the linear combination `S_χ` on `A` and
vanishes off `A`; `S_χ` also vanishes off `H` (since each `ζ_i` does).  Thus
`χ^ρ - S_χ` is supported at `x = 1` only, where its value is `-S_χ(1)`.
Subtracting `S_χ(1) · conj(S_χ(1))` from `Σ_L S_χ(x) · conj(S_χ(x))` yields
`Σ_L χ^ρ(x) · conj(χ^ρ(x))`, and dividing by `|L|` and rearranging gives
the displayed double-sum. -/
theorem chiRho_norm_sq_double_sum (H76 : Hypothesis76 G A L)
    (χ : ClassFunction G ℂ) :
    ClassFunction.inner (H76.hyp71.chiRhoCF χ) (H76.hyp71.chiRhoCF χ) =
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        ∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          (star (H76.cCoeff χ i) * H76.cCoeff χ j /
            (H76.zetaNormSq i * H76.zetaNormSq j)) *
          (ClassFunction.inner (H76.zeta i) (H76.zeta j) -
            H76.zeta i 1 * star (H76.zeta j 1) / (Nat.card L : ℂ)) := by
  classical
  -- Step 1: inner χ^ρ χ^ρ = (1/|L|) innerSum χ^ρ χ^ρ.
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, invOf_eq_inv]
  -- Step 2: apply innerSum_chiRho_eq.
  rw [H76.innerSum_chiRho_eq χ]
  -- Step 3: rewrite innerSum S S = |L| · inner S S, then expand inner S S.
  rw [show ClassFunction.innerSum (H76.chiRhoLinearCombo χ) (H76.chiRhoLinearCombo χ) =
      (Nat.card L : ℂ) *
        ClassFunction.inner (H76.chiRhoLinearCombo χ) (H76.chiRhoLinearCombo χ) from
    (ClassFunction.card_mul_inner _ _).symm]
  rw [H76.inner_chiRhoLinearCombo_self χ, H76.chiRhoLinearCombo_one_mul_star χ]
  -- Step 4: distribute (1/|L|) over the difference and unify the two double sums.
  rw [mul_sub]
  have hL_ne : (Nat.card L : ℂ) ≠ 0 := Invertible.ne_zero _
  rw [show (Nat.card L : ℂ)⁻¹ *
      ((Nat.card L : ℂ) *
        ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          ∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
            (star (H76.cCoeff χ i) * H76.cCoeff χ j /
              (H76.zetaNormSq i * H76.zetaNormSq j)) *
            ClassFunction.inner (H76.zeta i) (H76.zeta j)) =
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        ∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          (star (H76.cCoeff χ i) * H76.cCoeff χ j /
            (H76.zetaNormSq i * H76.zetaNormSq j)) *
          ClassFunction.inner (H76.zeta i) (H76.zeta j) from by
    rw [← mul_assoc, inv_mul_cancel₀ hL_ne, one_mul]]
  rw [show (Nat.card L : ℂ)⁻¹ *
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        ∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          (star (H76.cCoeff χ i) * H76.cCoeff χ j /
            (H76.zetaNormSq i * H76.zetaNormSq j)) *
            (H76.zeta i 1 * star (H76.zeta j 1)) =
      ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        ∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          (star (H76.cCoeff χ i) * H76.cCoeff χ j /
            (H76.zetaNormSq i * H76.zetaNormSq j)) *
            (H76.zeta i 1 * star (H76.zeta j 1) / (Nat.card L : ℂ)) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring]
  -- Combine into one sum with the inner difference.
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

open scoped Classical in
/-- **The abelian rebase identity for the (7.6) family** (issue 2035 #79/#80): when the normal
`H` is abelian (all its irreducible characters are linear), the family `(ζ_i)` — which
enumerates the distinct induced irreducibles bijectively (`zeta_injective` /
`zeta_family_cover`) — satisfies `∑_i ζ_i(x)/‖ζ_i‖² = 0` at every `x ≠ 1`.  The
`Hypothesis76`-level packaging of `sum_image_induce_div_normSq_apply_eq_zero`. -/
theorem zeta_sum_div_normSq_apply_eq_zero (H76 : Hypothesis76 G A L)
    (hab : haveI : Fintype ↥(H76.H.subgroupOf L) := Fintype.ofFinite _
      ∀ θ : IrreducibleCharacter ↥(H76.H.subgroupOf L),
        θ.toClassFunction (1 : ↥(H76.H.subgroupOf L)) = 1)
    {x : L} (hx : x ≠ 1) :
    ∑ i : Fin (H76.n + 1), H76.zeta i x / H76.zetaNormSq i = 0 := by
  classical
  letI : Fintype ↥(H76.H.subgroupOf L) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(H76.H.subgroupOf L) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (H76.H.subgroupOf L).Normal := by
    refine ⟨fun h hmem l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hmem ⊢
    exact H76.H_normal_in_L l hmem
  -- the ζ-enumeration is the image of `Irr H` under induction
  have himg : (Finset.univ : Finset (Fin (H76.n + 1))).image H76.zeta
      = (Finset.univ : Finset (IrreducibleCharacter ↥(H76.H.subgroupOf L))).image
          (fun θ => OddOrder.RepresentationTheory.ClassFunction.induce
            (H76.H.subgroupOf L) θ.toClassFunction) := by
    ext φ
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨θ, hθ⟩ := H76.zeta_induced i
      exact ⟨θ, hθ.symm⟩
    · rintro ⟨θ, rfl⟩
      obtain ⟨i, hi⟩ := H76.zeta_family_cover θ
      exact ⟨i, hi⟩
  calc ∑ i : Fin (H76.n + 1), H76.zeta i x / H76.zetaNormSq i
      = ∑ i : Fin (H76.n + 1),
          (fun φ : OddOrder.RepresentationTheory.ClassFunction ↥L ℂ =>
            φ x / ClassFunction.inner φ φ) (H76.zeta i) :=
        Finset.sum_congr rfl fun i _ => by rw [zetaNormSq]
    _ = ∑ φ ∈ (Finset.univ : Finset (Fin (H76.n + 1))).image H76.zeta,
          φ x / ClassFunction.inner φ φ := by
        rw [Finset.sum_image (fun i _ j _ h => H76.zeta_injective h)]
    _ = ∑ φ ∈ (Finset.univ : Finset (IrreducibleCharacter ↥(H76.H.subgroupOf L))).image
          (fun θ => OddOrder.RepresentationTheory.ClassFunction.induce
            (H76.H.subgroupOf L) θ.toClassFunction),
          φ x / ClassFunction.inner φ φ := by rw [himg]
    _ = 0 :=
        OddOrder.RepresentationTheory.sum_image_induce_div_normSq_apply_eq_zero
          (H := H76.H.subgroupOf L) hab hx

open scoped Classical in
/-- **The rebased (7.7.a)** (Peterfalvi (13.5.a); issue 2035 #79/#80): for an abelian `H` the
(7.7.a) decomposition can be re-based at any family index `i₀ ≠ 0` — the coefficients become
the *differences* `c_i − c_{i₀}` (computable through τ₁-coherence for `P`-non-kernel *pairs*,
unlike the trivial-base absolute coefficients), at the cost of one explicit `ζ_0`-term with
coefficient `−c̄_{i₀}`:

`χ^ρ(x) = ∑_{i ≥ 1, i ≠ i₀} ((c̄_i − c̄_{i₀})/‖ζ_i‖²)·ζ_i(x) − (c̄_{i₀}/‖ζ_0‖²)·ζ_0(x)`.

Follows from the base-`0` certificate (`chiRho_decomp`) by adding `c̄_{i₀}` times the abelian
rebase identity (`zeta_sum_div_normSq_apply_eq_zero`). -/
theorem chiRho_decomp_rebased (H76 : Hypothesis76 G A L)
    (hab : haveI : Fintype ↥(H76.H.subgroupOf L) := Fintype.ofFinite _
      ∀ θ : IrreducibleCharacter ↥(H76.H.subgroupOf L),
        θ.toClassFunction (1 : ↥(H76.H.subgroupOf L)) = 1)
    (i₀ : Fin (H76.n + 1)) (hi₀ : 0 < i₀)
    (χ : ClassFunction G ℂ) {x : L} (hxA : (x : G) ∈ A) :
    H76.hyp71.chiRho χ x =
      (∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).erase i₀,
        (star (H76.cCoeff χ i - H76.cCoeff χ i₀) / H76.zetaNormSq i) * H76.zeta i x)
      - (star (H76.cCoeff χ i₀) / H76.zetaNormSq 0) * H76.zeta 0 x := by
  classical
  have hx1 : x ≠ 1 := by
    intro h
    apply H76.one_not_mem_A
    rw [h] at hxA
    simpa using hxA
  have hzero := H76.zeta_sum_div_normSq_apply_eq_zero hab hx1
  -- split `univ = insert 0 (Ioi 0)` and `Ioi 0 = insert i₀ ((Ioi 0).erase i₀)`
  have huniv : (Finset.univ : Finset (Fin (H76.n + 1)))
      = insert (0 : Fin (H76.n + 1)) (Finset.Ioi 0) := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_Ioi, true_iff]
    rcases eq_or_ne j 0 with h | h
    · exact Or.inl h
    · exact Or.inr (Fin.pos_iff_ne_zero.mpr h)
  have h0notIoi : (0 : Fin (H76.n + 1)) ∉ Finset.Ioi (0 : Fin (H76.n + 1)) := by
    simp
  have hIoi : Finset.Ioi (0 : Fin (H76.n + 1))
      = insert i₀ ((Finset.Ioi (0 : Fin (H76.n + 1))).erase i₀) :=
    (Finset.insert_erase (Finset.mem_Ioi.mpr hi₀)).symm
  have hi₀mem : i₀ ∉ (Finset.Ioi (0 : Fin (H76.n + 1))).erase i₀ := by
    simp
  -- the rebase identity, split along the same decomposition
  have hzero' : H76.zeta 0 x / H76.zetaNormSq 0
      + (H76.zeta i₀ x / H76.zetaNormSq i₀
        + ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).erase i₀,
            H76.zeta i x / H76.zetaNormSq i) = 0 := by
    calc H76.zeta 0 x / H76.zetaNormSq 0
        + (H76.zeta i₀ x / H76.zetaNormSq i₀
          + ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).erase i₀,
              H76.zeta i x / H76.zetaNormSq i)
        = ∑ i : Fin (H76.n + 1), H76.zeta i x / H76.zetaNormSq i := by
          rw [huniv, Finset.sum_insert h0notIoi, hIoi, Finset.sum_insert hi₀mem,
            Finset.erase_insert hi₀mem]
      _ = 0 := hzero
  -- expand the base-`0` certificate along `Ioi 0 = {i₀} ∪ ((Ioi 0).erase i₀)`
  rw [H76.chiRho_explicit_formula χ hxA]
  conv_lhs => rw [hIoi, Finset.sum_insert hi₀mem]
  -- pure algebra: subtract `star c_{i₀} ·` (rebase identity)
  have hexp : ∀ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).erase i₀,
      (star (H76.cCoeff χ i - H76.cCoeff χ i₀) / H76.zetaNormSq i) * H76.zeta i x
        = (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i x
          - star (H76.cCoeff χ i₀) * (H76.zeta i x / H76.zetaNormSq i) := by
    intro i _
    rw [star_sub]
    ring
  have hRHS : ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).erase i₀,
      (star (H76.cCoeff χ i - H76.cCoeff χ i₀) / H76.zetaNormSq i) * H76.zeta i x
      = (∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).erase i₀,
          (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i x)
        - star (H76.cCoeff χ i₀)
            * ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).erase i₀,
                H76.zeta i x / H76.zetaNormSq i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hexp
  have hrearr : ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).erase i₀,
      H76.zeta i x / H76.zetaNormSq i
      = -(H76.zeta 0 x / H76.zetaNormSq 0) - H76.zeta i₀ x / H76.zetaNormSq i₀ := by
    linear_combination hzero'
  rw [hRHS, hrearr]
  ring

end Hypothesis76

end Section_7_6_to_7_7

end OddOrder.Peterfalvi.S09
