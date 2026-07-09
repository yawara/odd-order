/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S07_Coherence
import OddOrder.Peterfalvi.S06_CertainHypothesis46
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.FixedPointFree
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.GroupTheory.RepresentationTheory.SylowTICongruence
import OddOrder.GroupTheory.RepresentationTheory.LinearCharacter
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
import OddOrder.GroupTheory.RepresentationTheory.InflationCharacter
import OddOrder.BG.Ch1_Preliminary.S03_FrobeniusActions
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Peterfalvi §8: Coherence theorems — infrastructure core

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, pp. 30-37.

Frozen infrastructure for the §8 coherence theorems, prefix-split (2026-06-11, granularity
rule) from `S08_CoherenceTheorems.lean`, which remains the active leaf (the (6.8) capstone
`sibleySetup_is_coherent` and its consumer interfaces) and imports this file.  Contents:
the `ClassFunction` conjugation helpers, the solvable-normal filtration setup (6.1) and
descent (6.4), the `SibleyDadeHypothesis` carrier (6.8 (a)/(b)/(c)) with its full lemma
suite — the (6.2)/(6.3)/(6.5) arithmetic, the θ-bound, the B1/B2 coherence engines, the
(6.6) prime-power step data, the first-obstruction decomposition, and the Frobenius/case-A
producers.

Reference note: `notes/peterfalvi/s08_coherence_theorems.md`.
-/

namespace OddOrder.RepresentationTheory

namespace ClassFunction

end ClassFunction

variable {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]


open scoped Classical in
/-- **Fourier expansion of a class function** in the orthonormal basis of irreducible characters:
`φ = ∑_{χ ∈ Irr Γ} ⟨φ, χ⟩ • χ`.  From completeness (`classFunction_eq_zero_of_orthogonal`): the
difference `φ − ∑ ⟨φ,χ⟩•χ` is orthogonal to every irreducible (orthonormality
`irreducibleCharacter_inner_eq_ite`), hence `0`.  Used in (6.8.1) to expand `Res^G_L(η₁^{τ₁})` and
split its `X`-part (whose coefficients `⟨·,χᵢ⟩` are governed by Res-orthogonality) from the
`Z ⊆ ker` part (constant on `Z`). -/
theorem classFunction_eq_sum_inner_smul (φ : ClassFunction Γ ℂ) :
    φ = ∑ a : IrreducibleCharacter Γ,
      ClassFunction.inner φ (a : ClassFunction Γ ℂ) • (a : ClassFunction Γ ℂ) := by
  refine eq_of_sub_eq_zero (classFunction_eq_zero_of_orthogonal _ (fun b => ?_))
  rw [ClassFunction.inner_sub_left, inner_sum_left]
  have hstep : (∑ a : IrreducibleCharacter Γ,
      ClassFunction.inner
        (ClassFunction.inner φ (a : ClassFunction Γ ℂ) • (a : ClassFunction Γ ℂ))
        (b : ClassFunction Γ ℂ)) = ClassFunction.inner φ (b : ClassFunction Γ ℂ) := by
    rw [Finset.sum_eq_single b]
    · rw [ClassFunction.inner_smul_left, irreducibleCharacter_inner_eq_ite b b, if_pos rfl, mul_one]
    · intro a _ hab
      rw [ClassFunction.inner_smul_left, irreducibleCharacter_inner_eq_ite a b, if_neg hab, mul_zero]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  rw [hstep, sub_self]

open scoped Classical in
/-- **Regular-character difference value over the non-inflated irreducibles** (mmd 04.8 L168,
combined `(ρ_Γ − ρ_{Γ/N})(z) − (…)(1)` value).  For `N ⊴ Γ` and `z ∈ N^#`,
`∑_{χ ∈ Irr Γ, N ⊄ ker χ} χ(1)·(χ(z) − χ(1)) = -|Γ|`.  This is
`(-|Γ⧸N|) − (|Γ| − |Γ⧸N|) = -|Γ|`, from `sumNonInflatedDegreeMulChar_of_mem` (the `χ(z)` part) and
`sumNonInflatedDegreeSq` (the `χ(1)` part). -/
theorem sum_filter_degree_mul_charValue_sub_eq (N : Subgroup Γ) [N.Normal]
    {z : Γ} (hz : z ∈ N) (hz1 : z ≠ 1) :
    ∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
        ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
        (a : ClassFunction Γ ℂ) 1 * ((a : ClassFunction Γ ℂ) z - (a : ClassFunction Γ ℂ) 1)
      = -(Nat.card Γ : ℂ) := by
  haveI : Finite Γ := Finite.of_fintype Γ
  have hsplit : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
        ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
        (a : ClassFunction Γ ℂ) 1 * ((a : ClassFunction Γ ℂ) z - (a : ClassFunction Γ ℂ) 1))
      = (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
          ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
          (a : ClassFunction Γ ℂ) 1 * (a : ClassFunction Γ ℂ) z)
        - (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
            ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
            (a : ClassFunction Γ ℂ) 1 * (a : ClassFunction Γ ℂ) 1) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun a _ => by ring)
  have h2 : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
        ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
        (a : ClassFunction Γ ℂ) 1 * (a : ClassFunction Γ ℂ) 1)
      = (Nat.card Γ : ℂ) - (Nat.card (Γ ⧸ N) : ℂ) := by
    rw [show (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
          ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
          (a : ClassFunction Γ ℂ) 1 * (a : ClassFunction Γ ℂ) 1)
        = ∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
          ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
          ((a : ClassFunction Γ ℂ) 1) ^ 2 from
        Finset.sum_congr rfl (fun a _ => by rw [pow_two])]
    exact sumNonInflatedDegreeSq (N := N)
  rw [hsplit, sumNonInflatedDegreeMulChar_of_mem (N := N) hz hz1, h2]; ring

open scoped Classical in
/-- **Bessel's inequality (integer-coefficient form).**  For an orthonormal family `s` of class
functions (`⟨a,b⟩ = δ_{a,b}` on `s`) and any `v` whose Fourier coefficients on `s` are integers
(`⟨v,a⟩ = β a`), the sum of squared coefficients is bounded by the squared norm:
`∑_{a∈s} (β a)² ≤ (⟨v,v⟩).re`.

Pythagoras on `v = (v − p) + p` with `p = ∑_{a∈s} (β a)•a` the orthogonal projection:
`⟨v,p⟩ = ⟨p,v⟩ = ⟨p,p⟩ = ∑(β a)²` (Parseval `inner_self_orthonormalSum_eq_sum_sq` + conjugate
symmetry), so `⟨v−p,v−p⟩ = ⟨v,v⟩ − ∑(β a)²`; non-negativity of `‖v−p‖²`
(`inner_self_re_nonneg`) gives the bound. -/
theorem sum_sq_le_inner_self_re {s : Finset (ClassFunction Γ ℂ)}
    (horth : ∀ a ∈ s, ∀ b ∈ s, ClassFunction.inner a b = if a = b then (1 : ℂ) else 0)
    (v : ClassFunction Γ ℂ) {β : ClassFunction Γ ℂ → ℤ}
    (hβ : ∀ a ∈ s, ClassFunction.inner v a = (β a : ℂ)) :
    ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℝ) ≤ (ClassFunction.inner v v).re := by
  classical
  set p : ClassFunction Γ ℂ := ∑ a ∈ s, (β a : ℂ) • a with hp
  have hsumcast : ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ) = ∑ a ∈ s, ((β a : ℂ)) ^ 2 := by
    push_cast; ring
  have hvp : ClassFunction.inner v p = ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ) := by
    rw [hp, inner_sum_right, hsumcast]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [inner_smul_right, hβ a ha, star_intCast]; ring
  have hpp : ClassFunction.inner p p = ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ) := by
    rw [hp, inner_self_orthonormalSum_eq_sum_sq horth, hsumcast]
  have hpv : ClassFunction.inner p v = ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ) := by
    rw [inner_conj_symm v p, hvp, star_intCast]
  have hkey : ClassFunction.inner (v - p) (v - p)
      = ClassFunction.inner v v - ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hvp, hpv, hpp]; ring
  have hnn := inner_self_re_nonneg (v - p)
  rw [hkey, Complex.sub_re] at hnn
  have hcast : (((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ)).re = ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℝ) :=
    Complex.intCast_re _
  rw [hcast] at hnn
  linarith

end OddOrder.RepresentationTheory

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

/-! ### (6.6) `X`-characterization helpers (T7): constituent inherits a kernel containment

The (6.6) `X = {χ∈Irr L | Z⊄Ker χ}` characterization needs "an irreducible constituent `χ` of a
genuine character `ψ` inherits `g ∈ Ker ψ`".  Both directions of the characterization route this
through a *genuine* character (`Res_H φ` for `⊆`, `Ind_K^L θ` for `⊇`) — never applying the Dade
isometry to the unsupported `χ` itself — which is why [Is] Lemma 2.21 is **not** needed. -/

/-- **(H0)** the restriction `Res^Γ_H φ` of a genuine character is genuine. -/
theorem isCharacter_restrict {Γ : Type*} [Group Γ] [Finite Γ] {φ : ClassFunction Γ ℂ}
    (hφ : IsCharacter φ) (H : Subgroup Γ) :
    IsCharacter (ClassFunction.restrict H φ) := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := hφ
  have hφeq : φ = repCharacterClassFunction ρ :=
    ClassFunction.ext fun g => by rw [repCharacterClassFunction_apply]; exact congrFun hρ g
  rw [hφeq, ClassFunction.restrict_repCharacterClassFunction H ρ]
  exact repCharacterClassFunction_isCharacter (ρ.comp H.subtype)

/-- **(H1, decomposition form)** an irreducible constituent inherits a kernel containment of a
non-negative integer combination.  If `ψ = ∑_{a ∈ supp m} (m a) • a` is a finite `ℕ`-combination
of irreducible characters (`m : ClassFunction Γ ℂ →₀ ℕ` supported on `Irr Γ`) and `χ` is a
summand with `m χ ≠ 0`, then `g ∈ Ker ψ` forces `g ∈ Ker χ`.

This repackages the (6.6) G2.2 keystone
`OddOrder.Peterfalvi.S03.irreducibleCharacter_mem_characterKernel_of_natSum_value_eq` from a
`Finsupp` decomposition: the family of summands is totalized to an `IrreducibleCharacter`-valued
function off the support, and the kernel hypothesis `ψ(g) = ψ(1)` is read as the keystone's
value-equality hypothesis. -/
theorem characterKernel_subset_of_natFinsupp_eq_sum {Γ : Type*} [Group Γ] [Finite Γ]
    {ψ : ClassFunction Γ ℂ} {m : ClassFunction Γ ℂ →₀ ℕ}
    (hsupp : (↑m.support : Set (ClassFunction Γ ℂ)) ⊆ irreducibleCharacters Γ)
    (hsum : ψ = ∑ a ∈ m.support, (m a : ℂ) • a)
    {χ : ClassFunction Γ ℂ} (hχ : IsIrreducibleCharacter χ) (hmχ : m χ ≠ 0)
    {g : Γ} (hg : g ∈ OddOrder.Peterfalvi.S03.characterKernel ψ) :
    g ∈ OddOrder.Peterfalvi.S03.characterKernel χ := by
  classical
  set χfam : ClassFunction Γ ℂ → IrreducibleCharacter Γ :=
    fun a => if h : IsIrreducibleCharacter a then (⟨a, h⟩ : IrreducibleCharacter Γ)
      else trivialIrreducibleCharacter Γ with hχfam_def
  have hfam : ∀ a, IsIrreducibleCharacter a →
      ((χfam a : IrreducibleCharacter Γ) : ClassFunction Γ ℂ) = a := by
    intro a h; simp only [hχfam_def, dif_pos h]
  have hirr : ∀ a ∈ m.support, IsIrreducibleCharacter a := fun a ha =>
    mem_irreducibleCharacters.mp (hsupp (Finset.mem_coe.mpr ha))
  set d : ClassFunction Γ ℂ → ℕ :=
    fun a => if h : IsIrreducibleCharacter a then
      (h.exists_natDegree_charValue_one_dvd_card).choose else 0 with hd_def
  have hdeg : ∀ a ∈ m.support, ((χfam a : ClassFunction Γ ℂ)) 1 = (d a : ℂ) := by
    intro a ha
    have h := hirr a ha
    rw [hfam a h]
    simp only [hd_def, dif_pos h]
    exact (h.exists_natDegree_charValue_one_dvd_card).choose_spec.2.1
  have hsumapp : ∀ x : Γ, ψ x = ∑ a ∈ m.support, (m a : ℂ) * a x := by
    intro x
    rw [hsum]
    simp only [ClassFunction.finset_sum_apply, ClassFunction.smul_apply]
  have hgg : ψ g = ψ 1 := by
    have h := hg
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def] at h
    exact h
  have hval : ∑ a ∈ m.support, (m a : ℂ) * ((χfam a : ClassFunction Γ ℂ)) g
      = ∑ a ∈ m.support, (m a : ℂ) * ((χfam a : ClassFunction Γ ℂ)) 1 := by
    have eL : ∑ a ∈ m.support, (m a : ℂ) * ((χfam a : ClassFunction Γ ℂ)) g = ψ g := by
      rw [hsumapp g]; exact Finset.sum_congr rfl fun a ha => by rw [hfam a (hirr a ha)]
    have eR : ∑ a ∈ m.support, (m a : ℂ) * ((χfam a : ClassFunction Γ ℂ)) 1 = ψ 1 := by
      rw [hsumapp 1]; exact Finset.sum_congr rfl fun a ha => by rw [hfam a (hirr a ha)]
    rw [eL, eR, hgg]
  have hkey :=
    OddOrder.Peterfalvi.S03.irreducibleCharacter_mem_characterKernel_of_natSum_value_eq
      (g := g) m.support (fun a => m a) χfam d hdeg hval χ
      (Finsupp.mem_support_iff.mpr hmχ) hmχ
  rwa [hfam χ hχ] at hkey

/-- **(H1, genuine form)** an irreducible constituent of a genuine character inherits a kernel
containment.  If `ψ` is a genuine character, `χ` is irreducible with `⟨ψ, χ⟩ ≠ 0` (a constituent),
then `g ∈ Ker ψ` forces `g ∈ Ker χ`.  This is `characterKernel_subset_of_natFinsupp_eq_sum`
applied to the `ℕ`-decomposition `IsCharacter.exists_natFinsupp_eq_sum` of `ψ`, whose
`χ`-coefficient is the nonzero Fourier multiplicity `⟨ψ, χ⟩`. -/
theorem characterKernel_subset_of_isCharacter_of_inner_ne_zero {Γ : Type*} [Group Γ]
    [Fintype Γ] [Invertible (Nat.card Γ : ℂ)] {ψ : ClassFunction Γ ℂ} (hψ : IsCharacter ψ)
    {χ : ClassFunction Γ ℂ} (hχ : IsIrreducibleCharacter χ)
    (hχψ : ClassFunction.inner ψ χ ≠ 0)
    {g : Γ} (hg : g ∈ OddOrder.Peterfalvi.S03.characterKernel ψ) :
    g ∈ OddOrder.Peterfalvi.S03.characterKernel χ := by
  obtain ⟨m, hsupp, hsum, hcoeff⟩ := hψ.exists_natFinsupp_eq_sum
  have hmχ : m χ ≠ 0 := fun h0 => hχψ (by rw [← hcoeff χ hχ, h0, Nat.cast_zero])
  exact characterKernel_subset_of_natFinsupp_eq_sum hsupp hsum hχ hmχ hg

/-! ### Cross-family inner products of two coherent Dade extensions

Two coherence extensions `τ₁, τ₂` built from the **same** §4 Dade base map agree with it on their
supported lattices (`extends_on_supported`), so on *supported* virtual characters their cross inner
products and degree-`0` values are governed by the Dade isometry alone — independent of which set
each comes from.  These are the (4.1) inputs for the (6.8.1) `himg_ortho`: with `x = χᵢ − dᵢχ₁`,
`y = ηⱼ − η₁` (degree-matched differences, supported on `H^#`),
`inner_extension_eq_inner_of_supported` gives `⟨τ₂ x, τ₁ y⟩ = ⟨x, y⟩` (`= 0` by `X ⊥ Y`), the
difference-orthogonality, and `extension_apply_one_eq_zero_of_supported` gives the
`(α − β)(1) = 0` / `(u•γ − v•δ)(1) = 0` hypotheses of
`pairwise_inner_eq_zero_of_orthogonal_signedDifference`. -/

section DadeCoherenceUnion

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
  {A : Set G} {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

/-- **Difference-orthogonality (Peterfalvi (4.1) input).**  For two coherences `hX`, `hY` w.r.t. the
**same** §4 Dade base map and supported lattice elements `x ∈ ℤ[X, A]`, `y ∈ ℤ[Y, A]`, the cross
inner product of the extensions equals the source inner product:
`⟨hX.extension x, hY.extension y⟩ = ⟨x, y⟩`.  Both extensions agree with the Dade map on the
supported lattice (`extends_on_supported`), reducing to the Dade isometry
`dadeIntegralCharacterMap_inner_eq_on_supported_span` (applied on the pair `{x, y}`). -/
theorem inner_extension_eq_inner_of_supported
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {X Y : Set (ClassFunction ↥L ℂ)}
    (hX : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) X
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (hY : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) Y
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    {x y : ClassFunction ↥L ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S07.zSupportedSpan X
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (hy : y ∈ OddOrder.Peterfalvi.S07.zSupportedSpan Y
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L)) :
    ClassFunction.inner (hX.extension x) (hY.extension y) = ClassFunction.inner x y := by
  rw [hX.extends_on_supported x hx, hY.extends_on_supported y hy]
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hconj
    (S := ({x, y} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hx.2
        · exact hy.2)
    (Submodule.subset_span (Set.mem_insert x _))
    (Submodule.subset_span (Set.mem_insert_of_mem x rfl))

/-- A coherent Dade extension sends a supported lattice element to a function vanishing at `1`:
`(hX.extension x)(1) = 0` for `x ∈ ℤ[X, A]`.  (`extends_on_supported` to the Dade map, then
`dadeIntegralCharacterMap_apply_one_eq_zero`.)  Supplies the degree-`0` hypotheses of (4.1). -/
theorem extension_apply_one_eq_zero_of_supported
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {X : Set (ClassFunction ↥L ℂ)}
    (hX : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) X
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    {x : ClassFunction ↥L ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S07.zSupportedSpan X
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L)) :
    (hX.extension x) (1 : G) = 0 := by
  rw [hX.extends_on_supported x hx]
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero hyp hconj hx.2

end DadeCoherenceUnion

/-- **Peterfalvi (6.8.1) norm-bound forcing** (mmd 04.8 L176).  In the (6.8.1) `b ≡ c ≡ 0 mod a`
argument, after `(6.7)` gives `a ∣ b` (write `b = a·x`), the norm identity
`1 + a² = ‖(χ₁ − aη₁)^τ‖² = ‖X‖² + (b − a)² + (m − 1)·b²` with `‖X‖² ≥ 0` gives the bound
`(b − a)² + (m − 1)·b² ≤ 1 + a²`; with `a ≥ 2` and `m ≥ 2` (`m = |Y|`) this forces `b = 0` — or the
edge case `b = a`, `m = 2`, which the textbook reduces to `b = 0` by relabelling
`η₁^{τ₁} ↔ −η₂^{τ₁}`.  (`b = ±2a` and `b = −a` are excluded since `4a² > 1 + a²` for `a ≥ 2`.) -/
theorem eq_zero_or_edge_of_dvd_of_normBound {a b m : ℤ}
    (ha : 2 ≤ a) (hm : 2 ≤ m) (hdvd : a ∣ b)
    (hnorm : (b - a) ^ 2 + (m - 1) * b ^ 2 ≤ 1 + a ^ 2) :
    b = 0 ∨ (b = a ∧ m = 2) := by
  obtain ⟨x, rfl⟩ := hdvd
  have ha0 : (0 : ℤ) < a := by linarith
  -- `b² = (a·x)² ≤ 1 + a²` (drop `(b−a)² ≥ 0` and the `(m−2)·b² ≥ 0` slack).
  have hb2 : (a * x) ^ 2 ≤ 1 + a ^ 2 := by
    nlinarith [sq_nonneg (a * x - a), mul_nonneg (by linarith : (0 : ℤ) ≤ m - 2) (sq_nonneg (a * x))]
  -- Hence `x² ≤ 1`: otherwise `x² ≥ 2` gives `2a² ≤ a²x² ≤ 1 + a²`, i.e. `a² ≤ 1`, contradicting `a ≥ 2`.
  have hx2 : x ^ 2 ≤ 1 := by
    by_contra h
    push_neg at h
    have hx2' : 2 ≤ x ^ 2 := h
    nlinarith [hb2, mul_pos ha0 ha0, mul_le_mul_of_nonneg_left hx2' (le_of_lt (mul_pos ha0 ha0))]
  have hxlo : -1 ≤ x := by nlinarith [hx2, sq_nonneg (x + 1)]
  have hxhi : x ≤ 1 := by nlinarith [hx2, sq_nonneg (x - 1)]
  interval_cases x
  · -- `x = -1` (`b = -a`): `4a² + (m−1)a² ≤ 1 + a²` is impossible.
    exfalso; nlinarith [hnorm, ha, hm]
  · -- `x = 0`: `b = 0`.
    left; ring
  · -- `x = 1` (`b = a`): `(m−1)a² ≤ 1 + a²` forces `m = 2`.
    right
    refine ⟨by ring, ?_⟩
    nlinarith [hnorm, ha, hm]

section DadeReciprocity

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
  {A : Set G} {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

/-- In the **TI Dade situation** (`hyp.H a = ⊥`, e.g. `H^#` a TI-subset with normalizer `L`), the
(2.7) adjoint averaging map collapses to plain evaluation: `adjointAverageFun hyp χ a = χ(a)`.  The
average `|H(a)|⁻¹ ∑_{x ∈ H(a)} χ(ax)` over the trivial group `H(a) = ⊥` is the single term
`χ(a·1) = χ(a)`. -/
theorem adjointAverageFun_eq_of_H_eq_bot
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (χ : ClassFunction G ℂ)
    (a : {a : G // a ∈ A}) (hH : hyp.H a = ⊥) :
    OddOrder.Peterfalvi.S04.adjointAverageFun hyp χ ⟨a.1, hyp.subset_L a.2⟩ = χ a.1 := by
  classical
  simp only [OddOrder.Peterfalvi.S04.adjointAverageFun]
  rw [dif_pos a.2]
  have hHa : hyp.H ⟨a.1, a.2⟩ = ⊥ := hH
  have hconst : ∀ x : ↥(hyp.H ⟨a.1, a.2⟩), χ (a.1 * (x : G)) = χ a.1 := by
    intro x
    have hx1 : (x : G) ∈ (⊥ : Subgroup G) := by rw [← hHa]; exact x.2
    rw [Subgroup.mem_bot.mp hx1, mul_one]
  have hHne : (Nat.card (hyp.H ⟨a.1, a.2⟩) : ℂ) ≠ 0 := by
    have : 0 < Nat.card (hyp.H ⟨a.1, a.2⟩) := Nat.card_pos
    exact_mod_cast this.ne'
  rw [Finset.sum_congr rfl (fun x _ => hconst x), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hHne, one_mul]

/-- **Dade reciprocity (TI case).**  For the §4 Dade base map of a TI Hypothesis (`hyp.H a = ⊥`),
a *supported* `α ∈ CF(L, A)` and any `ψ ∈ CF(G)`:

`⟨α^τ, ψ⟩_G = ⟨α, Res_L^G ψ⟩_L`.

This is the (2.7) `adjoint_formula` specialized to the TI situation, where the adjoint average of
`ψ` is `Res_L^G ψ` (`adjointAverageFun_eq_of_H_eq_bot`).  It is the gateway to the (6.8.1)
`Res_L(η₁^{τ₁})` decomposition: it converts the `G`-side pairing of a Dade image with `ψ` into the
`L`-side pairing of the supported source with `Res_L ψ`. -/
theorem inner_dadeIntegralCharacterMap_eq_inner_restrict
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (hH : ∀ a : {a : G // a ∈ A}, hyp.H a = ⊥)
    {α : ClassFunction ↥L ℂ}
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (ψ : ClassFunction G ℂ) :
    ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj) α) ψ
      = ClassFunction.inner α (ClassFunction.restrict L ψ) := by
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp _ hαsupp]
  refine OddOrder.Peterfalvi.S04.adjoint_formula hyp (hyp.dadeMap (k := ℂ))
    (hyp.isDadeMap_dadeMap (k := ℂ)) hconj
    ⟨α, (ClassFunction.mem_supportedSubmodule).mpr hαsupp⟩ ψ (ClassFunction.restrict L ψ)
    (fun a => ?_)
  rw [adjointAverageFun_eq_of_H_eq_bot hyp ψ a (hH a), ClassFunction.restrict_apply]

end DadeReciprocity

open scoped ComplexOrder in
/-- The inner product of two genuine characters is `≥ 0`.  Decompose the right argument into a
non-negative integer combination of irreducibles (`exists_natFinsupp_eq_sum`); each summand
`⟨χ, a⟩` is `≥ 0` by `inner_irreducible_nonneg`, and the multiplicities are non-negative. -/
theorem inner_isCharacter_nonneg {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {χ ψ : ClassFunction Γ ℂ}
    (hχ : IsCharacter χ) (hψ : IsCharacter ψ) :
    0 ≤ ClassFunction.inner χ ψ := by
  obtain ⟨m, hsupp, hsum, _⟩ := hψ.exists_natFinsupp_eq_sum
  rw [hsum, inner_sum_right]
  refine Finset.sum_nonneg fun a ha => ?_
  have ha' : IsIrreducibleCharacter a :=
    mem_irreducibleCharacters.mp (hsupp (Finset.mem_coe.mpr ha))
  rw [OddOrder.RepresentationTheory.inner_smul_right, star_natCast]
  exact mul_nonneg (Nat.cast_nonneg _) (hχ.inner_irreducible_nonneg ha')

set_option linter.unusedFintypeInType false in
open scoped ComplexOrder in
/-- **(H2)** the induced character `Ind_H^Γ θ` of a genuine character `θ` decomposes as a
non-negative integer combination of irreducibles, with multiplicity `⟨Ind θ, ψ⟩` at `ψ ∈ Irr Γ`.
Since `induce` lives only at the class-function level (`IsCharacter (Ind θ)` is not directly
available), the decomposition is reconstructed from `Ind θ ∈ ZIrr Γ` (`induce_mem_ZIrr`) plus the
non-negativity of `⟨Ind θ, ψ⟩ = ⟨θ, Res ψ⟩` (Frobenius reciprocity and `inner_isCharacter_nonneg`),
pushed through `Int.toNat`. -/
theorem induce_exists_natFinsupp_eq_sum {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {H : Subgroup Γ} [Fintype ↥H]
    [Invertible (Nat.card ↥H : ℂ)] {θ : ClassFunction ↥H ℂ} (hθ : IsCharacter θ) :
    ∃ m : ClassFunction Γ ℂ →₀ ℕ, (↑m.support ⊆ irreducibleCharacters Γ) ∧
      ClassFunction.induce H θ = ∑ a ∈ m.support, (m a : ℂ) • a ∧
      ∀ ψ : ClassFunction Γ ℂ, IsIrreducibleCharacter ψ →
        (m ψ : ℂ) = ClassFunction.inner (ClassFunction.induce H θ) ψ := by
  classical
  obtain ⟨c, hsupp, hsum⟩ := mem_ZIrr_repr (ClassFunction.induce_mem_ZIrr H hθ.mem_ZIrr)
  have hcoeff : ∀ ψ : ClassFunction Γ ℂ, ψ ∈ irreducibleCharacters Γ →
      (c ψ : ℂ) = ClassFunction.inner (ClassFunction.induce H θ) ψ := by
    intro ψ hψ
    have h := inner_eq_coeff_of_repr (⟨ψ, hψ⟩ : IrreducibleCharacter Γ) hsupp
    rw [show ((⟨ψ, hψ⟩ : IrreducibleCharacter Γ) : ClassFunction Γ ℂ) = ψ from rfl] at h
    rw [← h, hsum]
  have hcnn : ∀ ψ : ClassFunction Γ ℂ, ψ ∈ c.support → 0 ≤ c ψ := by
    intro ψ hψsupp
    have hψ : ψ ∈ irreducibleCharacters Γ := hsupp (Finset.mem_coe.mpr hψsupp)
    have hψirr : IsIrreducibleCharacter ψ := mem_irreducibleCharacters.mp hψ
    have hnn : (0 : ℂ) ≤ ClassFunction.inner (ClassFunction.induce H θ) ψ := by
      rw [ClassFunction.inner_induce_eq_inner_restrict]
      exact inner_isCharacter_nonneg hθ (isCharacter_restrict hψirr.isCharacter H)
    have : (0 : ℂ) ≤ (c ψ : ℂ) := by rw [hcoeff ψ hψ]; exact hnn
    exact_mod_cast this
  refine ⟨Finsupp.mapRange Int.toNat Int.toNat_zero c, ?_, ?_, ?_⟩
  · refine subset_trans ?_ hsupp
    intro ψ hψ
    exact Finset.mem_coe.mpr (Finsupp.support_mapRange (Finset.mem_coe.mp hψ))
  · have hsupp_eq : (Finsupp.mapRange Int.toNat Int.toNat_zero c).support = c.support := by
      apply Finset.Subset.antisymm Finsupp.support_mapRange
      intro a ha
      rw [Finsupp.mem_support_iff, Finsupp.mapRange_apply]
      have : 0 < c a := lt_of_le_of_ne (hcnn a ha) (Ne.symm (Finsupp.mem_support_iff.mp ha))
      omega
    rw [hsum, hsupp_eq]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finsupp.mapRange_apply]
    have : 0 < c a := lt_of_le_of_ne (hcnn a ha) (Ne.symm (Finsupp.mem_support_iff.mp ha))
    rw [← Int.cast_natCast (R := ℂ) (Int.toNat (c a)), Int.toNat_of_nonneg (le_of_lt this)]
  · intro ψ hψ
    rw [Finsupp.mapRange_apply, ← hcoeff ψ hψ]
    have hnn : 0 ≤ c ψ := by
      by_cases hsupp_mem : ψ ∈ c.support
      · exact hcnn ψ hsupp_mem
      · rw [Finsupp.notMem_support_iff.mp hsupp_mem]
    rw [← Int.cast_natCast (R := ℂ) (Int.toNat (c ψ)), Int.toNat_of_nonneg hnn]

set_option linter.unusedFintypeInType false in
/-- **(H2, character form)** the induced character `Ind_H^Γ θ` of a genuine character `θ` is
itself a genuine character.  Combines the non-negative-integer decomposition
`induce_exists_natFinsupp_eq_sum` (`Ind θ = ∑ mₐ·a` with `mₐ ∈ ℕ`, `a ∈ Irr Γ`) with its
converse `isCharacter_of_natFinsupp_eq_sum` (a `ℕ`-combination of irreducible characters is a
genuine character).  This is **brick 2** of the Frobenius-reciprocity route to the Peterfalvi
`(6.2)` `θ`-bound a-half. -/
theorem isCharacter_induce {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {H : Subgroup Γ} [Fintype ↥H]
    [Invertible (Nat.card ↥H : ℂ)] {θ : ClassFunction ↥H ℂ} (hθ : IsCharacter θ) :
    IsCharacter (ClassFunction.induce H θ) := by
  obtain ⟨m, hsupp, hsum, _⟩ := induce_exists_natFinsupp_eq_sum hθ
  exact isCharacter_of_natFinsupp_eq_sum m hsupp hsum

set_option linter.unusedFintypeInType false in
/-- **Peterfalvi (6.2) `θ`-bound, a-half** (the Clifford/induction half).  For an irreducible
character `θ` of a finite group `K` and a subgroup `C ≤ K`, there is an irreducible character
`φ` of `C` of which `θ` is a constituent of `Ind_C^K φ` (`⟨Ind_C^K φ, θ⟩ ≠ 0`), and whose
degree controls `θ`'s: `θ(1) ≤ |K : C|·φ(1)`.

By Frobenius reciprocity `θ` is a constituent of `Ind_C^K φ` for some `φ ∈ Irr C`
(`exists_inner_induce_ne_zero`, equivalently `φ` is a constituent of `Res^K_C θ`).  Since `φ` is
a genuine character, so is `Ind_C^K φ` (`isCharacter_induce`, brick 2), so the
constituent-degree bound `IsCharacter.apply_one_re_le_of_inner_ne_zero` (brick 1) gives
`θ(1) ≤ (Ind_C^K φ)(1) = |K : C|·φ(1)` (`induce_apply_one`).  Combined with the section degree
bound `degree_sq_le_index_of_central_quotient` (`φ(1)² ≤ |C : D|`, the b-half) this yields the
full `(6.2)` degree bound `θ(1) ≤ |K : C|·√|C : D|`. -/
theorem theta_degree_le_index_mul_constituent {K : Type*} [Group K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] (C : Subgroup K) [Fintype ↥C]
    [Invertible (Nat.card ↥C : ℂ)] (θ : IrreducibleCharacter K) :
    ∃ φ : IrreducibleCharacter C,
      ClassFunction.inner (ClassFunction.induce C (φ : ClassFunction ↥C ℂ))
          (θ : ClassFunction K ℂ) ≠ 0 ∧
      ((θ : ClassFunction K ℂ) 1).re ≤ (C.index : ℝ) * ((φ : ClassFunction ↥C ℂ) 1).re := by
  obtain ⟨φ, hφ⟩ := OddOrder.Peterfalvi.S03.exists_inner_induce_ne_zero (H := C) θ
  refine ⟨φ, hφ, ?_⟩
  have hind : IsCharacter (ClassFunction.induce C (φ : ClassFunction ↥C ℂ)) :=
    isCharacter_induce φ.isIrreducible.isCharacter
  have hbound := hind.apply_one_re_le_of_inner_ne_zero θ.isIrreducible hφ
  rw [ClassFunction.induce_apply_one] at hbound
  rwa [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at hbound

set_option linter.unusedFintypeInType false in
/-- **Peterfalvi (6.2) `θ`-bound** (full degree bound).  For an irreducible character `θ` of a
finite group `K`, a subgroup `C ≤ K`, and a section `N ◁ C` with `N ≤ D ≤ C`, `θ` trivial on `N`
(after restriction to `C`) and `D ⧸ N` central in `C ⧸ N`, the degree of `θ` is bounded:
`θ(1) ≤ |K : C|·√|C : D|`.

Assembled from the two halves: the a-half `theta_degree_le_index_mul_constituent`
(`θ(1) ≤ |K:C|·φ(1)` for an `Ind`-constituent `φ ∈ Irr C` of `θ`) and the section b-half
`degree_sq_le_index_of_central_quotient` (`φ(1)² ≤ |C:D|`).  The `φ` produced by the a-half is a
constituent of `Res^K_C θ` (Frobenius reciprocity `inner_induce_eq_inner_restrict` +
`inner_conj_symm`), so `N ⊆ Ker(Res^K_C θ)` forces `N ⊆ Ker φ` (constituent kernel inheritance
`characterKernel_subset_of_isCharacter_of_inner_ne_zero`), discharging the b-half's kernel
hypothesis.  Then `φ(1) = d` with `d² ≤ |C:D|` gives `φ(1) ≤ √|C:D|` (`Real.le_sqrt_of_sq_le`),
and multiplying by `|K:C| ≥ 0` closes the bound. -/
theorem theta_degree_le_index_mul_sqrt_index {K : Type*} [Group K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] (θ : IrreducibleCharacter K) (C : Subgroup K) [Fintype ↥C]
    [Invertible (Nat.card ↥C : ℂ)] {N : Subgroup ↥C} [N.Normal] (D : Subgroup ↥C) (hND : N ≤ D)
    (hθN : (↑N : Set ↥C) ⊆ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.restrict C (θ : ClassFunction K ℂ)))
    (hcentral : D.map (QuotientGroup.mk' N) ≤ Subgroup.center (↥C ⧸ N)) :
    ((θ : ClassFunction K ℂ) 1).re ≤ (C.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  obtain ⟨φ, hφne, hφbound⟩ := theta_degree_le_index_mul_constituent C θ
  -- `φ` is a constituent of `Res^K_C θ`: reciprocity turns `⟨Ind φ, θ⟩ ≠ 0` into `⟨φ, Res θ⟩ ≠ 0`,
  -- and conjugate symmetry flips it to `⟨Res θ, φ⟩ ≠ 0`.
  have hφRes : ClassFunction.inner (φ : ClassFunction ↥C ℂ)
      (ClassFunction.restrict C (θ : ClassFunction K ℂ)) ≠ 0 := by
    rw [← ClassFunction.inner_induce_eq_inner_restrict]; exact hφne
  have hres_inner : ClassFunction.inner (ClassFunction.restrict C (θ : ClassFunction K ℂ))
      (φ : ClassFunction ↥C ℂ) ≠ 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm]; exact star_ne_zero.mpr hφRes
  -- constituent kernel inheritance: `N ⊆ Ker(Res θ) ⟹ N ⊆ Ker φ`.
  have hkerφ : (↑N : Set ↥C) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (φ : ClassFunction ↥C ℂ) := fun n hn =>
    characterKernel_subset_of_isCharacter_of_inner_ne_zero
      (isCharacter_restrict θ.isIrreducible.isCharacter C) φ.isIrreducible hres_inner (hθN hn)
  -- the b-half: `φ(1) = d` with `d² ≤ |C:D|`.
  obtain ⟨d, hd1, hd2⟩ :=
    degree_sq_le_index_of_central_quotient (N := N) φ D hND hkerφ hcentral
  have hφ1re : ((φ : ClassFunction ↥C ℂ) 1).re = (d : ℝ) := by
    rw [hd1]; exact Complex.natCast_re d
  have hd_le : (d : ℝ) ≤ Real.sqrt (D.index : ℝ) :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast hd2)
  calc ((θ : ClassFunction K ℂ) 1).re
      ≤ (C.index : ℝ) * ((φ : ClassFunction ↥C ℂ) 1).re := hφbound
    _ = (C.index : ℝ) * (d : ℝ) := by rw [hφ1re]
    _ ≤ (C.index : ℝ) * Real.sqrt (D.index : ℝ) :=
        mul_le_mul_of_nonneg_left hd_le (Nat.cast_nonneg _)

/-- **Restriction kernel inheritance.**  If `θ` is trivial on a subgroup `M ≤ K` (i.e.
`M ⊆ characterKernel θ`), then its restriction `Res_C θ` to a subgroup `C ≤ K` is trivial on
`M.subgroupOf C = M ∩ C` (viewed in `C`).  Used by (6.2): a member `ψ = Ind_H^L θ ∈ S(B)` has
source `θ` trivial on `B`, so `Res_C θ` is trivial on `B.subgroupOf C`, discharging the `θ`-bound's
kernel hypothesis. -/
theorem characterKernel_restrict_subgroupOf {K : Type*} [Group K] {θ : ClassFunction K ℂ}
    (C : Subgroup K) {M : Subgroup K}
    (hM : (M : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel θ) :
    ((M.subgroupOf C : Subgroup ↥C) : Set ↥C) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.restrict C θ) := by
  intro c hc
  have hker : (θ : ClassFunction K ℂ) (↑c : K) = (θ : ClassFunction K ℂ) 1 :=
    hM (Subgroup.mem_subgroupOf.mp hc)
  simp only [OddOrder.Peterfalvi.S03.mem_characterKernel,
    OddOrder.Peterfalvi.S03.characterDegree_def, ClassFunction.restrict_apply,
    OneMemClass.coe_one]
  exact hker

set_option linter.unusedFintypeInType false in
/-- **(H2, kernel form)** an irreducible constituent `χ` of an induced character `Ind_H^Γ θ`
(`θ` genuine, `⟨Ind θ, χ⟩ ≠ 0`) inherits a kernel containment of `Ind θ`.  The `ℕ`-decomposition
`induce_exists_natFinsupp_eq_sum` feeds `characterKernel_subset_of_natFinsupp_eq_sum`. -/
theorem characterKernel_subset_of_inner_induce_ne_zero {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {H : Subgroup Γ} [Fintype ↥H]
    [Invertible (Nat.card ↥H : ℂ)] {θ : ClassFunction ↥H ℂ} (hθ : IsCharacter θ)
    {χ : ClassFunction Γ ℂ} (hχ : IsIrreducibleCharacter χ)
    (hχψ : ClassFunction.inner (ClassFunction.induce H θ) χ ≠ 0)
    {g : Γ} (hg : g ∈ OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.induce H θ)) :
    g ∈ OddOrder.Peterfalvi.S03.characterKernel χ := by
  obtain ⟨m, hsupp, hsum, hcoeff⟩ := induce_exists_natFinsupp_eq_sum hθ
  have hmχ : m χ ≠ 0 := fun h0 => hχψ (by rw [← hcoeff χ hχ, h0, Nat.cast_zero])
  exact characterKernel_subset_of_natFinsupp_eq_sum hsupp hsum hχ hmχ hg

/- 6: Some coherence theorems (pp. 30-37) -/

/-- **Finite set of irreducible characters → injective `Fin k` enumeration.**  A finite set `T` of
class functions all of which are irreducible characters is enumerated by an injective family
`χ : Fin k → IrreducibleCharacter Γ` whose underlying-class-function range is exactly `T`.  This is
the bridge to the `Fin n`-indexed family interface of `coherentEqualDegree_fromDade` (the base
block `S₀`). -/
theorem exists_finEnum_irreducible {Γ : Type*} [Group Γ] {T : Set (ClassFunction Γ ℂ)}
    (hTfin : T.Finite) (hTirr : ∀ χ ∈ T, IsIrreducibleCharacter χ) :
    ∃ (k : ℕ) (χ : Fin k → IrreducibleCharacter Γ),
      Function.Injective χ ∧ Set.range (fun j => (χ j : ClassFunction Γ ℂ)) = T := by
  classical
  haveI : Fintype T := hTfin.fintype
  let e := Fintype.equivFin T
  refine ⟨Fintype.card T, fun j => ⟨(e.symm j : ClassFunction Γ ℂ), hTirr _ (e.symm j).2⟩, ?_, ?_⟩
  · intro i j hij
    have h : (e.symm i : ClassFunction Γ ℂ) = (e.symm j : ClassFunction Γ ℂ) :=
      congrArg (fun c : IrreducibleCharacter Γ => (c : ClassFunction Γ ℂ)) hij
    exact e.symm.injective (Subtype.ext h)
  · ext φ
    constructor
    · rintro ⟨j, rfl⟩
      exact (e.symm j).2
    · intro hφ
      exact ⟨e ⟨φ, hφ⟩, by simp⟩

/-- Reindex a sum over the `Finset` of a range by the indexing family: for an injective `f` over a
finite domain, `∑_{x ∈ (Set.range f).toFinset} g x = ∑ j, g (f j)`.  Used to turn the `S₁`-set
degree-square sum of the (6.2) bound into the `Fin k` member-family sum produced by B1. -/
theorem sum_toFinset_range_eq {α β M : Type*} [Fintype α] [DecidableEq β] [AddCommMonoid M]
    {f : α → β} (hinj : Function.Injective f) (g : β → M) :
    ∑ x ∈ (Set.range f).toFinset, g x = ∑ j, g (f j) := by
  rw [Set.toFinset_range, Finset.sum_image (fun a _ b _ h => hinj h)]

/-- **(T8 leaf 10, combinatorial core) the conjugate-pair cover of `X` over a base `S₀`.**

Given a finite set `X` of irreducible characters of `Γ`, closed under conjugation and with no real
characters (Peterfalvi (1.1): for `|Γ|` odd a nontrivial irreducible is non-self-conjugate), and a
conjugation-closed base `S₀ ⊆ X`, the complement `X ∖ S₀` is a disjoint union of conjugate pairs
`{χ, χ̄}`.  This packages the data and facts consumed by `peterfalvi_66_coherence_of_X_from_dade`:
the degree-monotone enumeration `e` (`exists_monotoneDegreeEnum`), the pair list `pair`/`N` with its
irreducible first components `hpairχ`, the inclusions and index-level cover, plus the two facts the
per-step (5.6) `DadeChainStep` needs — each adjoined pair is **disjoint from the prefix**
`pairUnion S₀ pair j` (so `χⱼ, χ̄ⱼ ⊥ S₁`) and **degree-monotone** (so the (5.6) degree gap
can hold).

Construction: the conjugate-index involution `cidx i` (`e (cidx i) = (e i).conj`, fixed-point-free
by no-real, preserving `∉ S₀`), the index transversal `T = {i | e i ∉ S₀ ∧ i < cidx i}` sorted by
`Finset.orderEmbOfFin`, and `pair j = (e tⱼ, (e tⱼ).conj)` for the `j`-th transversal index `tⱼ`. -/
theorem exists_conjugatePairCover {Γ : Type*} [Group Γ]
    {X S₀ : Set (ClassFunction Γ ℂ)}
    (hXfin : X.Finite)
    (hXconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate X)
    (hXreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters X)
    (hXirr : ∀ χ ∈ X, IsIrreducibleCharacter χ)
    (hS₀conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₀) :
    ∃ (e : Fin X.ncard → ClassFunction Γ ℂ)
      (pair : ℕ → ClassFunction Γ ℂ × ClassFunction Γ ℂ) (N : ℕ)
      (hpairχ : ∀ i, i < N → IrreducibleCharacter Γ),
      (∀ χ ∈ X, ∃ i, e i = χ) ∧
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j ⊆ X) ∧
      (∀ i : Fin X.ncard, e i ∈ S₀ ∨
        ∃ j, j < N ∧ e i ∈ OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j) ∧
      (∀ (i : ℕ) (hi : i < N),
        (pair i).1 = ((hpairχ i hi : IrreducibleCharacter Γ) : ClassFunction Γ ℂ)) ∧
      (∀ (i : ℕ) (hi : i < N),
        (pair i).2 = ((hpairχ i hi : IrreducibleCharacter Γ) : ClassFunction Γ ℂ).conj) ∧
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair j)) ∧
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) := by
  classical
  obtain ⟨e, he_inj, he_mem, he_surj, he_mono⟩ :=
    OddOrder.Peterfalvi.S07.exists_monotoneDegreeEnum (L := Γ) hXfin
  -- conjugate-index involution `cidx`
  have hconjX : ∀ i, (e i).conj ∈ X := fun i => hXconj (he_mem i)
  let cidx : Fin X.ncard → Fin X.ncard := fun i => (he_surj _ (hconjX i)).choose
  have hcidx : ∀ i, e (cidx i) = (e i).conj := fun i => (he_surj _ (hconjX i)).choose_spec
  have hcidx_invol : ∀ i, cidx (cidx i) = i := fun i =>
    he_inj (by rw [hcidx (cidx i), hcidx i, ClassFunction.conj_conj])
  have hcidx_inj : Function.Injective cidx := fun a b h => by
    rw [← hcidx_invol a, h, hcidx_invol b]
  have hcidx_ne : ∀ i, cidx i ≠ i := by
    intro i hfix
    apply hXreal (he_mem i)
    show (e i).conj = e i
    rw [← hcidx i, hfix]
  have hcidx_notS₀ : ∀ {i}, e i ∉ S₀ → e (cidx i) ∉ S₀ := by
    intro i hi hc
    rw [hcidx i] at hc
    exact hi (by simpa using hS₀conj hc)
  -- index transversal `T`, enumerated by `orderEmbOfFin`
  let T : Finset (Fin X.ncard) := Finset.univ.filter (fun i => e i ∉ S₀ ∧ i < cidx i)
  let t : Fin T.card → Fin X.ncard := fun j => T.orderEmbOfFin rfl j
  have htmono : StrictMono t := (T.orderEmbOfFin rfl).strictMono
  have ht_mem : ∀ j, t j ∈ T := fun j => T.orderEmbOfFin_mem rfl j
  have ht_spec : ∀ j, e (t j) ∉ S₀ ∧ t j < cidx (t j) := fun j =>
    (Finset.mem_filter.mp (ht_mem j)).2
  have ht_range : ∀ i ∈ T, ∃ j, t j = i := by
    intro i hi
    have hmem : i ∈ Set.range (T.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hi
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj⟩
  -- the pair list
  let pair : ℕ → ClassFunction Γ ℂ × ClassFunction Γ ℂ := fun j =>
    if hj : j < T.card then (e (t ⟨j, hj⟩), (e (t ⟨j, hj⟩)).conj) else (0, 0)
  have hpair_eq : ∀ (j : ℕ) (hj : j < T.card),
      pair j = (e (t ⟨j, hj⟩), (e (t ⟨j, hj⟩)).conj) := fun j hj => dif_pos hj
  have hfst : ∀ (j : ℕ) (hj : j < T.card), (pair j).1 = e (t ⟨j, hj⟩) := by
    intro j hj; rw [hpair_eq j hj]
  have hsnd : ∀ (j : ℕ) (hj : j < T.card), (pair j).2 = e (cidx (t ⟨j, hj⟩)) := by
    intro j hj; rw [hpair_eq j hj]; exact (hcidx _).symm
  refine ⟨e, pair, T.card, fun i hi => ⟨e (t ⟨i, hi⟩), hXirr _ (he_mem _)⟩,
    he_surj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- each pair lies in `X`
    intro j hj φ hφ
    simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff,
      hfst j hj, hsnd j hj] at hφ
    rcases hφ with rfl | rfl
    · exact he_mem _
    · exact he_mem _
  · -- index-level cover
    intro i
    by_cases hiS₀ : e i ∈ S₀
    · exact Or.inl hiS₀
    · refine Or.inr ?_
      rcases lt_or_gt_of_ne (hcidx_ne i) with hlt | hgt
      · -- `cidx i < i` ⟹ `cidx i ∈ T`, and `e i` is the second component of its pair
        have hcT : cidx i ∈ T := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hcidx_notS₀ hiS₀, by rw [hcidx_invol]; exact hlt⟩
        obtain ⟨j, hj⟩ := ht_range _ hcT
        refine ⟨j.val, j.isLt, ?_⟩
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff]
        refine Or.inr ?_
        rw [hsnd j.val j.isLt]
        have hci : cidx (t ⟨j.val, j.isLt⟩) = i := by
          rw [(hj : t ⟨j.val, j.isLt⟩ = cidx i)]; exact hcidx_invol i
        rw [hci]
      · -- `i < cidx i` ⟹ `i ∈ T`, and `e i` is the first component of its pair
        have hiT : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS₀, hgt⟩
        obtain ⟨j, hj⟩ := ht_range _ hiT
        refine ⟨j.val, j.isLt, ?_⟩
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff]
        refine Or.inl ?_
        rw [hfst j.val j.isLt]
        exact congrArg e hj.symm
  · -- `(pair i).1 = χᵢ`
    intro i hi; rw [hfst i hi]
  · -- `(pair i).2 = χ̄ᵢ`
    intro i hi; rw [hsnd i hi, hcidx]
  · -- each pair is disjoint from the prefix accumulated before it
    intro j hj
    rw [Set.disjoint_left]
    intro φ hφj hφu
    rw [OddOrder.Peterfalvi.S07.mem_pairUnion] at hφu
    simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff,
      hfst j hj, hsnd j hj] at hφj
    rcases hφu with hS₀mem | ⟨k, hkj, hφk⟩
    · rcases hφj with rfl | rfl
      · exact (ht_spec ⟨j, hj⟩).1 hS₀mem
      · exact hcidx_notS₀ (ht_spec ⟨j, hj⟩).1 hS₀mem
    · have hk : k < T.card := hkj.trans hj
      simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff,
        hfst k hk, hsnd k hk] at hφk
      have htlt : t ⟨k, hk⟩ < t ⟨j, hj⟩ := htmono (Fin.mk_lt_mk.mpr hkj)
      have hjT := (ht_spec ⟨j, hj⟩).2
      rcases hφj with hj1 | hj1 <;> rcases hφk with hk1 | hk1
      · have hee : t ⟨j, hj⟩ = t ⟨k, hk⟩ := he_inj (hj1.symm.trans hk1)
        rw [hee] at htlt; exact absurd htlt (lt_irrefl _)
      · have heq : t ⟨j, hj⟩ = cidx (t ⟨k, hk⟩) := he_inj (hj1.symm.trans hk1)
        have hc : cidx (t ⟨j, hj⟩) = t ⟨k, hk⟩ := by rw [heq, hcidx_invol]
        rw [hc] at hjT; exact absurd (hjT.trans htlt) (lt_irrefl _)
      · have heq : cidx (t ⟨j, hj⟩) = t ⟨k, hk⟩ := he_inj (hj1.symm.trans hk1)
        rw [heq] at hjT; exact absurd (hjT.trans htlt) (lt_irrefl _)
      · have hee : t ⟨j, hj⟩ = t ⟨k, hk⟩ := hcidx_inj (he_inj (hj1.symm.trans hk1))
        rw [hee] at htlt; exact absurd htlt (lt_irrefl _)
  · -- adjacent pairs are degree-monotone
    intro j hj1
    have hj : j < T.card := by omega
    rw [hfst j hj, hfst (j + 1) hj1]
    exact he_mono (htmono.monotone (Fin.mk_le_mk.mpr (by omega)))

/-- **Conjugate-pair cover without the irreducibility hypothesis** — the (6.8.3)/case-(c2)
generalization of `exists_conjugatePairCover`.  Identical construction, but `X` is an arbitrary
conjugation-closed real-free set (NOT required irreducible).  The cost is dropping the
`IrreducibleCharacter`-typed `hpairχ` output: the pairs are returned as plain `ClassFunction`s with the
direct conjugate relation `(pair i).2 = ((pair i).1).conj`.  Needed for (6.8.3) in case (c2), where the
set `S` contains the `w₂ − 1` reducible induced characters (so the break-pair `ψ` may be reducible).
The irreducibility hypothesis `hXirr` was used in the original *only* to package the pairs as
`IrreducibleCharacter`s; the conjugate-pair involution itself uses only `hXreal` + `hXconj`. -/
theorem exists_conjugatePairCover_general {Γ : Type*} [Group Γ]
    {X S₀ : Set (ClassFunction Γ ℂ)}
    (hXfin : X.Finite)
    (hXconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate X)
    (hXreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters X)
    (hS₀conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₀) :
    ∃ (e : Fin X.ncard → ClassFunction Γ ℂ)
      (pair : ℕ → ClassFunction Γ ℂ × ClassFunction Γ ℂ) (N : ℕ),
      (∀ χ ∈ X, ∃ i, e i = χ) ∧
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j ⊆ X) ∧
      (∀ i : Fin X.ncard, e i ∈ S₀ ∨
        ∃ j, j < N ∧ e i ∈ OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j) ∧
      (∀ (i : ℕ), i < N → (pair i).2 = ((pair i).1).conj) ∧
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair j)) ∧
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) := by
  classical
  obtain ⟨e, he_inj, he_mem, he_surj, he_mono⟩ :=
    OddOrder.Peterfalvi.S07.exists_monotoneDegreeEnum (L := Γ) hXfin
  have hconjX : ∀ i, (e i).conj ∈ X := fun i => hXconj (he_mem i)
  let cidx : Fin X.ncard → Fin X.ncard := fun i => (he_surj _ (hconjX i)).choose
  have hcidx : ∀ i, e (cidx i) = (e i).conj := fun i => (he_surj _ (hconjX i)).choose_spec
  have hcidx_invol : ∀ i, cidx (cidx i) = i := fun i =>
    he_inj (by rw [hcidx (cidx i), hcidx i, ClassFunction.conj_conj])
  have hcidx_inj : Function.Injective cidx := fun a b h => by
    rw [← hcidx_invol a, h, hcidx_invol b]
  have hcidx_ne : ∀ i, cidx i ≠ i := by
    intro i hfix
    apply hXreal (he_mem i)
    show (e i).conj = e i
    rw [← hcidx i, hfix]
  have hcidx_notS₀ : ∀ {i}, e i ∉ S₀ → e (cidx i) ∉ S₀ := by
    intro i hi hc
    rw [hcidx i] at hc
    exact hi (by simpa using hS₀conj hc)
  let T : Finset (Fin X.ncard) := Finset.univ.filter (fun i => e i ∉ S₀ ∧ i < cidx i)
  let t : Fin T.card → Fin X.ncard := fun j => T.orderEmbOfFin rfl j
  have htmono : StrictMono t := (T.orderEmbOfFin rfl).strictMono
  have ht_mem : ∀ j, t j ∈ T := fun j => T.orderEmbOfFin_mem rfl j
  have ht_spec : ∀ j, e (t j) ∉ S₀ ∧ t j < cidx (t j) := fun j =>
    (Finset.mem_filter.mp (ht_mem j)).2
  have ht_range : ∀ i ∈ T, ∃ j, t j = i := by
    intro i hi
    have hmem : i ∈ Set.range (T.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hi
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj⟩
  let pair : ℕ → ClassFunction Γ ℂ × ClassFunction Γ ℂ := fun j =>
    if hj : j < T.card then (e (t ⟨j, hj⟩), (e (t ⟨j, hj⟩)).conj) else (0, 0)
  have hpair_eq : ∀ (j : ℕ) (hj : j < T.card),
      pair j = (e (t ⟨j, hj⟩), (e (t ⟨j, hj⟩)).conj) := fun j hj => dif_pos hj
  have hfst : ∀ (j : ℕ) (hj : j < T.card), (pair j).1 = e (t ⟨j, hj⟩) := by
    intro j hj; rw [hpair_eq j hj]
  have hsnd : ∀ (j : ℕ) (hj : j < T.card), (pair j).2 = e (cidx (t ⟨j, hj⟩)) := by
    intro j hj; rw [hpair_eq j hj]; exact (hcidx _).symm
  refine ⟨e, pair, T.card, he_surj, ?_, ?_, ?_, ?_, ?_⟩
  · -- each pair lies in `X`
    intro j hj φ hφ
    simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff,
      hfst j hj, hsnd j hj] at hφ
    rcases hφ with rfl | rfl
    · exact he_mem _
    · exact he_mem _
  · -- index-level cover
    intro i
    by_cases hiS₀ : e i ∈ S₀
    · exact Or.inl hiS₀
    · refine Or.inr ?_
      rcases lt_or_gt_of_ne (hcidx_ne i) with hlt | hgt
      · have hcT : cidx i ∈ T := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hcidx_notS₀ hiS₀, by rw [hcidx_invol]; exact hlt⟩
        obtain ⟨j, hj⟩ := ht_range _ hcT
        refine ⟨j.val, j.isLt, ?_⟩
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff]
        refine Or.inr ?_
        rw [hsnd j.val j.isLt]
        have hci : cidx (t ⟨j.val, j.isLt⟩) = i := by
          rw [(hj : t ⟨j.val, j.isLt⟩ = cidx i)]; exact hcidx_invol i
        rw [hci]
      · have hiT : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS₀, hgt⟩
        obtain ⟨j, hj⟩ := ht_range _ hiT
        refine ⟨j.val, j.isLt, ?_⟩
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff]
        refine Or.inl ?_
        rw [hfst j.val j.isLt]
        exact congrArg e hj.symm
  · -- conjugate relation `(pair i).2 = ((pair i).1).conj`
    intro i hi
    rw [hfst i hi, hsnd i hi, hcidx]
  · -- each pair is disjoint from the prefix accumulated before it
    intro j hj
    rw [Set.disjoint_left]
    intro φ hφj hφu
    rw [OddOrder.Peterfalvi.S07.mem_pairUnion] at hφu
    simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff,
      hfst j hj, hsnd j hj] at hφj
    rcases hφu with hS₀mem | ⟨k, hkj, hφk⟩
    · rcases hφj with rfl | rfl
      · exact (ht_spec ⟨j, hj⟩).1 hS₀mem
      · exact hcidx_notS₀ (ht_spec ⟨j, hj⟩).1 hS₀mem
    · have hk : k < T.card := hkj.trans hj
      simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff,
        hfst k hk, hsnd k hk] at hφk
      have htlt : t ⟨k, hk⟩ < t ⟨j, hj⟩ := htmono (Fin.mk_lt_mk.mpr hkj)
      have hjT := (ht_spec ⟨j, hj⟩).2
      rcases hφj with hj1 | hj1 <;> rcases hφk with hk1 | hk1
      · have hee : t ⟨j, hj⟩ = t ⟨k, hk⟩ := he_inj (hj1.symm.trans hk1)
        rw [hee] at htlt; exact absurd htlt (lt_irrefl _)
      · have heq : t ⟨j, hj⟩ = cidx (t ⟨k, hk⟩) := he_inj (hj1.symm.trans hk1)
        have hc : cidx (t ⟨j, hj⟩) = t ⟨k, hk⟩ := by rw [heq, hcidx_invol]
        rw [hc] at hjT; exact absurd (hjT.trans htlt) (lt_irrefl _)
      · have heq : cidx (t ⟨j, hj⟩) = t ⟨k, hk⟩ := he_inj (hj1.symm.trans hk1)
        rw [heq] at hjT; exact absurd (hjT.trans htlt) (lt_irrefl _)
      · have hee : t ⟨j, hj⟩ = t ⟨k, hk⟩ := hcidx_inj (he_inj (hj1.symm.trans hk1))
        rw [hee] at htlt; exact absurd htlt (lt_irrefl _)
  · -- adjacent pairs are degree-monotone
    intro j hj1
    have hj : j < T.card := by omega
    rw [hfst j hj, hfst (j + 1) hj1]
    exact he_mono (htmono.monotone (Fin.mk_le_mk.mpr (by omega)))

/-- A predicate true at `0` and false at `N` must flip somewhere: there is an index `i < N` with
`P i` true and `P (i + 1)` false.  (Discrete first-failure / boundary extraction, by induction on
`N`.) -/
theorem exists_index_predicate_break {P : ℕ → Prop} (h0 : P 0) :
    ∀ N, ¬ P N → ∃ i, i < N ∧ P i ∧ ¬ P (i + 1)
  | 0, hN => absurd h0 hN
  | N + 1, hN => by
    by_cases hPN : P N
    · exact ⟨N, Nat.lt_succ_self N, hPN, hN⟩
    · obtain ⟨i, hiN, hPi, hnPi⟩ := exists_index_predicate_break h0 N hPN
      exact ⟨i, hiN.trans (Nat.lt_succ_self N), hPi, hnPi⟩

open scoped Classical in
/-- **First obstruction to coherence — the Peterfalvi (6.2) `S₁`/`S₂` decomposition.**

Given conjugation-closed sets `Sa ⊆ Sb` of irreducible characters of `↥L`, with `Sb` finite and
real-free, if `Sa` is coherent for an integral character map `τ` (on the support set `A`) but `Sb`
is not, then there is an intermediate conjugation-closed set `S₁` (`Sa ⊆ S₁ ⊆ Sb`) and a character
`ψ ∈ Sb` such that `S₁` is coherent but adjoining the conjugate pair `{ψ, ψ̄}` destroys coherence:
`S₁ ∪ {ψ, ψ̄}` is not coherent.

This is the decomposition cited at the start of the (6.2) proof ("By (b), there are sets `S₁` and
`S₂ = {ψ, ψ̄}` … such that `S₁` is coherent but `S₁ ∪ S₂` is not coherent").  Construction:
enumerate `Sb ∖ Sa` as conjugate pairs (`exists_conjugatePairCover`), so the running union
`pairUnion Sa pair i` rises from `Sa` (coherent) to `Sb` (not), and take the first pair whose
adjunction breaks coherence (`exists_index_predicate_break`). -/
theorem exists_coherentBreakPair
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G) {A : Set ↥L}
    {Sa Sb : Set (ClassFunction ↥L ℂ)}
    (hsub : Sa ⊆ Sb) (hSbfin : Sb.Finite)
    (hSbconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Sb)
    (hSbreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters Sb)
    (hSbirr : ∀ χ ∈ Sb, IsIrreducibleCharacter χ)
    (hSaconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Sa)
    (hSacoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ Sa A))
    (hSbncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ Sb A)) :
    ∃ (S₁ : Set (ClassFunction ↥L ℂ)) (ψ : ClassFunction ↥L ℂ),
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ ∧ Sa ⊆ S₁ ∧ S₁ ⊆ Sb ∧ ψ ∈ Sb ∧
      ψ ∉ S₁ ∧ ψ.conj ∉ S₁ ∧
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A) ∧
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (S₁ ∪ {ψ, ψ.conj}) A) := by
  classical
  obtain ⟨e, pair, N, hpairχ, hsurj, hpairs, hcoverIdx, hpair0, hpair1, hdisj, _hmono⟩ :=
    exists_conjugatePairCover hSbfin hSbconj hSbreal hSbirr hSaconj
  -- the running union reaches `Sb` after `N` steps
  have hUN : OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair N = Sb :=
    OddOrder.Peterfalvi.S07.pairUnion_eq_of_enumCover hsurj hsub hpairs hcoverIdx
  -- the coherence predicate along the chain rises from `Sa` (true) to `Sb` (false)
  have hP0 : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair 0) A) := by
    rw [OddOrder.Peterfalvi.S07.pairUnion_zero]; exact hSacoh
  have hPN : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair N) A) := by
    rw [hUN]; exact hSbncoh
  obtain ⟨i, hiN, hPi, hnPi⟩ := exists_index_predicate_break
    (P := fun i => Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair i) A)) hP0 N hPN
  -- the breaking pair `{ψ, ψ̄}` lies in `Sb` and is disjoint from the prefix `S₁`
  have hψpair : (pair i).1 ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet]
  have hconj2 : (pair i).2 = ((pair i).1).conj := by rw [hpair1 i hiN, hpair0 i hiN]
  have hψcpair : ((pair i).1).conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    rw [← hconj2]; simp [OddOrder.Peterfalvi.S07.pairSet]
  refine ⟨OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair i, (pair i).1,
    ?_, ?_, ?_, hpairs i hiN hψpair,
    Set.disjoint_left.mp (hdisj i hiN) hψpair,
    Set.disjoint_left.mp (hdisj i hiN) hψcpair, hPi, ?_⟩
  · -- `S₁` is closed under conjugation (base `Sa` is, each adjoined pair is)
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl (hSaconj hbase))
    · have hjN : j < N := hji.trans hiN
      have hpair_conj : φ.conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hjpair ⊢
        rcases hjpair with hφ' | hφ'
        · right; rw [hφ', hpair0 j hjN, hpair1 j hjN]
        · left; rw [hφ', hpair1 j hjN, hpair0 j hjN]; simp
      exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hji, hpair_conj⟩)
  · -- `Sa ⊆ S₁`
    exact fun φ hφ => OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hφ)
  · -- `S₁ ⊆ Sb`
    rw [← hUN]; exact OddOrder.Peterfalvi.S07.pairUnion_mono Sa pair hiN.le
  · -- `S₁ ∪ {ψ, ψ̄}` is not coherent (it is the next accumulator, where coherence fails)
    have hsplit : OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair (i + 1) =
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair i ∪ {(pair i).1, ((pair i).1).conj} :=
      OddOrder.Peterfalvi.S07.pairUnion_succ_eq_union_pair rfl hconj2
    rw [← hsplit]; exact hnPi

/-- **First obstruction to coherence without the irreducibility hypothesis** — the (6.8.3)/case-(c2)
generalization of `exists_coherentBreakPair`.  `Sb` need only be conjugation-closed and real-free (NOT
required irreducible), at the cost that the breaking character `ψ ∈ Sb` may itself be reducible.  Used
in (6.8.3) for case (c2), where `S` contains the `w₂ − 1` reducible induced characters; the downstream
degree bound then uses the norm-weighted sum `χ(1)²/‖χ‖²` (valid for reducibles). -/
theorem exists_coherentBreakPair_general
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G) {A : Set ↥L}
    {Sa Sb : Set (ClassFunction ↥L ℂ)}
    (hsub : Sa ⊆ Sb) (hSbfin : Sb.Finite)
    (hSbconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Sb)
    (hSbreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters Sb)
    (hSaconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Sa)
    (hSacoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ Sa A))
    (hSbncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ Sb A)) :
    ∃ (S₁ : Set (ClassFunction ↥L ℂ)) (ψ : ClassFunction ↥L ℂ),
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ ∧ Sa ⊆ S₁ ∧ S₁ ⊆ Sb ∧ ψ ∈ Sb ∧
      ψ ∉ S₁ ∧ ψ.conj ∉ S₁ ∧
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A) ∧
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (S₁ ∪ {ψ, ψ.conj}) A) := by
  classical
  obtain ⟨e, pair, N, hsurj, hpairs, hcoverIdx, hconjrel, hdisj, _hmono⟩ :=
    exists_conjugatePairCover_general hSbfin hSbconj hSbreal hSaconj
  have hUN : OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair N = Sb :=
    OddOrder.Peterfalvi.S07.pairUnion_eq_of_enumCover hsurj hsub hpairs hcoverIdx
  have hP0 : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair 0) A) := by
    rw [OddOrder.Peterfalvi.S07.pairUnion_zero]; exact hSacoh
  have hPN : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair N) A) := by
    rw [hUN]; exact hSbncoh
  obtain ⟨i, hiN, hPi, hnPi⟩ := exists_index_predicate_break
    (P := fun i => Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair i) A)) hP0 N hPN
  have hψpair : (pair i).1 ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet]
  have hconj2 : (pair i).2 = ((pair i).1).conj := hconjrel i hiN
  have hψcpair : ((pair i).1).conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    rw [← hconj2]; simp [OddOrder.Peterfalvi.S07.pairSet]
  refine ⟨OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair i, (pair i).1,
    ?_, ?_, ?_, hpairs i hiN hψpair,
    Set.disjoint_left.mp (hdisj i hiN) hψpair,
    Set.disjoint_left.mp (hdisj i hiN) hψcpair, hPi, ?_⟩
  · intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl (hSaconj hbase))
    · have hjN : j < N := hji.trans hiN
      have hpair_conj : φ.conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hjpair ⊢
        rcases hjpair with hφ' | hφ'
        · right; rw [hφ', hconjrel j hjN]
        · left; rw [hφ', hconjrel j hjN, ClassFunction.conj_conj]
      exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hji, hpair_conj⟩)
  · exact fun φ hφ => OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hφ)
  · rw [← hUN]; exact OddOrder.Peterfalvi.S07.pairUnion_mono Sa pair hiN.le
  · have hsplit : OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair (i + 1) =
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair i ∪ {(pair i).1, ((pair i).1).conj} :=
      OddOrder.Peterfalvi.S07.pairUnion_succ_eq_union_pair rfl hconj2
    rw [← hsplit]; exact hnPi

/-- **In a finite nilpotent group, a nontrivial normal subgroup meets the centre.**
If `N ◁ G` is nontrivial and `G` is finite nilpotent, then `N ⊓ Z(G) ≠ ⊥`.  Proof: take the least
`m` with `N ⊓ ζₘ ≠ ⊥` (the upper central series reaches `⊤`, so `m` exists; `m = k+1 > 0`); a
nontrivial `x ∈ N ⊓ ζ_{k+1}` has `x·y·x⁻¹·y⁻¹ ∈ ζₖ` (definition of `ζ_{k+1}`) and `∈ N` (`N`
normal), so `∈ N ⊓ ζₖ = ⊥` by minimality; hence `x` is central, `x ∈ N ⊓ Z(G)`.

This is the nilpotency central step of Peterfalvi (6.3): `H/M` nilpotent and `A/B` a nontrivial
normal subgroup give `(A/B) ⊓ Z(H/B) ≠ 1`, which (with maximality of `B`) forces `A/B ⊆ Z(H/B)`. -/
theorem isNilpotent_normal_inf_center_ne_bot {Γ : Type*} [Group Γ] [Finite Γ]
    [Group.IsNilpotent Γ] {N : Subgroup Γ} (hN : N.Normal) (hNne : N ≠ ⊥) :
    N ⊓ Subgroup.center Γ ≠ ⊥ := by
  classical
  have hexists : ∃ i, N ⊓ Subgroup.upperCentralSeries Γ i ≠ ⊥ := by
    refine ⟨Group.nilpotencyClass Γ, ?_⟩
    rw [Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr (le_refl _), inf_top_eq]
    exact hNne
  have hm := Nat.find_spec hexists
  have hm0 : Nat.find hexists ≠ 0 := by
    intro h0
    rw [h0, Subgroup.upperCentralSeries_zero, inf_bot_eq] at hm
    exact hm rfl
  obtain ⟨k, hk_eq⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hkbot : N ⊓ Subgroup.upperCentralSeries Γ k = ⊥ := by
    by_contra h
    exact Nat.find_min hexists (m := k) (by rw [hk_eq]; exact Nat.lt_succ_self k) h
  rw [hk_eq] at hm
  obtain ⟨⟨x, hxmem⟩, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hm
  have hx1 : x ≠ 1 := fun h => hxne (Subtype.ext h)
  rw [Subgroup.mem_inf] at hxmem
  obtain ⟨hxN, hxU⟩ := hxmem
  have hxcenter : x ∈ Subgroup.center Γ := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hcomm_U : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.upperCentralSeries Γ k :=
      Subgroup.mem_upperCentralSeries_succ_iff.mp hxU y
    have hcomm_N : x * y * x⁻¹ * y⁻¹ ∈ N := by
      have hconj : y * x⁻¹ * y⁻¹ ∈ N := hN.conj_mem x⁻¹ (N.inv_mem hxN) y
      have := N.mul_mem hxN hconj
      rwa [← mul_assoc, ← mul_assoc] at this
    have hbot : x * y * x⁻¹ * y⁻¹ = 1 := by
      have hin : x * y * x⁻¹ * y⁻¹ ∈ N ⊓ Subgroup.upperCentralSeries Γ k :=
        Subgroup.mem_inf.mpr ⟨hcomm_N, hcomm_U⟩
      rw [hkbot, Subgroup.mem_bot] at hin
      exact hin
    have h2 : x * y * x⁻¹ = y := mul_inv_eq_one.mp hbot
    conv_lhs => rw [← h2]
    group
  intro hbot
  have : x ∈ N ⊓ Subgroup.center Γ := Subgroup.mem_inf.mpr ⟨hxN, hxcenter⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hx1 this

/-- **A maximal normal subgroup strictly between `M` and `A`.**
For a finite group, if `M < A` (with `M` normal) there is a normal `B` with `M ≤ B < A` that is
maximal with this property: any normal `C` with `B ≤ C < A` equals `B`.  This is the maximal-`B`
step of the Peterfalvi (6.3) minimal-`A` induction (find a maximal proper normal subgroup below the
minimal coherent `A`). -/
theorem exists_maximal_normal_between {Γ : Type*} [Group Γ] [Finite Γ] {M A : Subgroup Γ}
    [M.Normal] (hMA : M < A) :
    ∃ B : Subgroup Γ, B.Normal ∧ M ≤ B ∧ B < A ∧
      ∀ C : Subgroup Γ, C.Normal → B ≤ C → C < A → C = B := by
  classical
  haveI : Finite (Subgroup Γ) := Finite.of_injective (fun H : Subgroup Γ => (H : Set Γ))
    (fun _ _ h => SetLike.coe_injective h)
  obtain ⟨B, hBmem, hBmax⟩ :=
    Set.Finite.exists_maximalFor (id : Subgroup Γ → Subgroup Γ)
      {N | N.Normal ∧ M ≤ N ∧ N < A} (Set.toFinite _) ⟨M, ‹M.Normal›, le_refl M, hMA⟩
  obtain ⟨hBnorm, hMB, hBA⟩ := hBmem
  refine ⟨B, hBnorm, hMB, hBA, fun C hCnorm hBC hCA => ?_⟩
  exact le_antisymm (hBmax ⟨hCnorm, hMB.trans hBC, hCA⟩ hBC) hBC

/-- **Maximality forces centrality** — the central step of Peterfalvi (6.3).

If `H ◁ Γ` is nilpotent and `A`, `B` are normal subgroups of `Γ` with `B < A ≤ H`, where `B` is
maximal among normal subgroups of `Γ` strictly below `A`, then `A/B ⊆ Z(H/B)`.

Indeed `A/B` is a nontrivial normal subgroup of the nilpotent group `H/B`, so `(A/B) ⊓ Z(H/B) ≠ 1`
(`isNilpotent_normal_inf_center_ne_bot`).  Its full preimage `C` in `Γ` is a normal subgroup with
`B < C ≤ A` (`C` is normal because conjugation by `Γ` preserves both `A/B` and the centre of `H/B`);
by maximality of `B`, `C = A`, i.e. `A/B ⊆ Z(H/B)`.

This discharges the `hcentral` hypothesis of `six_three_index_bound` in the minimal-`A`/maximal-`B`
induction of Peterfalvi (6.3). -/
theorem normal_central_of_maximal_normal_below {Γ : Type*} [Group Γ] [Finite Γ]
    {H A B : Subgroup Γ} (hH : H.Normal) [Group.IsNilpotent ↥H]
    [A.Normal] [B.Normal] (hAH : A ≤ H) (hBA : B < A)
    (hmax : ∀ C : Subgroup Γ, C.Normal → B ≤ C → C < A → C = B) :
    (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) ≤
      Subgroup.center (↥H ⧸ B.subgroupOf H) := by
  classical
  haveI hNnorm : (B.subgroupOf H).Normal := (‹B.Normal›).subgroupOf H
  haveI hANnorm : (A.subgroupOf H).Normal := (‹A.Normal›).subgroupOf H
  have hBH : B ≤ H := hBA.le.trans hAH
  -- `mk' (B.subgroupOf H) a = 1 ↔ a ∈ B.subgroupOf H`
  have mk_eq_one : ∀ a : ↥H,
      QuotientGroup.mk' (B.subgroupOf H) a = 1 ↔ a ∈ B.subgroupOf H := by
    intro a; rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  -- centrality of `mk' x` ⟺ all commutators `h x h⁻¹ x⁻¹` land in `B.subgroupOf H`
  have center_iff : ∀ x : ↥H,
      QuotientGroup.mk' (B.subgroupOf H) x ∈ Subgroup.center (↥H ⧸ B.subgroupOf H) ↔
        ∀ h : ↥H, h * x * h⁻¹ * x⁻¹ ∈ B.subgroupOf H := by
    intro x
    rw [Subgroup.mem_center_iff]
    refine ⟨fun hx h => ?_, fun hx q => ?_⟩
    · have h2 := hx (QuotientGroup.mk' (B.subgroupOf H) h)
      rw [← mk_eq_one]
      simp only [map_mul, map_inv]
      rw [h2]; group
    · obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf H) q
      have hcomm := (mk_eq_one (h * x * h⁻¹ * x⁻¹)).2 (hx h)
      simp only [map_mul, map_inv] at hcomm
      calc QuotientGroup.mk' (B.subgroupOf H) h * QuotientGroup.mk' (B.subgroupOf H) x
          = (QuotientGroup.mk' (B.subgroupOf H) h * QuotientGroup.mk' (B.subgroupOf H) x *
              (QuotientGroup.mk' (B.subgroupOf H) h)⁻¹ *
              (QuotientGroup.mk' (B.subgroupOf H) x)⁻¹) *
              (QuotientGroup.mk' (B.subgroupOf H) x * QuotientGroup.mk' (B.subgroupOf H) h) := by
            group
        _ = QuotientGroup.mk' (B.subgroupOf H) x * QuotientGroup.mk' (B.subgroupOf H) h := by
            rw [hcomm, one_mul]
  -- `A/B` is nontrivial in `H/B`
  have hAbar_ne : (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    have hAB : A ≤ B := by
      intro y hy
      have hy' : (⟨y, hAH hy⟩ : ↥H) ∈ A.subgroupOf H := Subgroup.mem_subgroupOf.mpr hy
      exact Subgroup.mem_subgroupOf.mp (hbot hy')
    exact lt_irrefl _ (hBA.trans_le hAB)
  -- nilpotency: `(A/B) ⊓ Z(H/B) ≠ 1`
  have hinf := isNilpotent_normal_inf_center_ne_bot
    (Subgroup.Normal.map hANnorm (QuotientGroup.mk' (B.subgroupOf H))
      (QuotientGroup.mk'_surjective _)) hAbar_ne
  -- the pullback subgroup of `Γ`
  set Zc := (Subgroup.center (↥H ⧸ B.subgroupOf H)).comap (QuotientGroup.mk' (B.subgroupOf H))
    with hZc
  set CH := A.subgroupOf H ⊓ Zc with hCH
  set C := CH.map H.subtype with hC
  -- `B ≤ C`
  have hBC : B ≤ C := by
    rw [hC, ← Subgroup.map_subgroupOf_eq_of_le hBH]
    apply Subgroup.map_mono
    rw [hCH]
    refine le_inf (Subgroup.subgroupOf_mono H hBA.le) (fun x hx => ?_)
    rw [hZc, Subgroup.mem_comap, (mk_eq_one x).2 hx]
    exact Subgroup.one_mem _
  -- `C ≤ A`
  have hCA : C ≤ A := by
    rw [hC, ← Subgroup.map_subgroupOf_eq_of_le hAH]
    exact Subgroup.map_mono (by rw [hCH]; exact inf_le_left)
  -- `C` is normal in `Γ`
  have hCnorm : C.Normal := by
    rw [hC]
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_map] at hn
    obtain ⟨c, hcCH, rfl⟩ := hn
    rw [hCH, Subgroup.mem_inf] at hcCH
    obtain ⟨hcA, hcZ⟩ := hcCH
    have hc_center : ∀ k : ↥H, k * c * k⁻¹ * c⁻¹ ∈ B.subgroupOf H := by
      apply (center_iff c).mp
      rw [hZc] at hcZ; exact Subgroup.mem_comap.mp hcZ
    have hc'H : g * (c : Γ) * g⁻¹ ∈ H := hH.conj_mem _ c.2 g
    rw [Subgroup.mem_map]
    refine ⟨⟨g * (c : Γ) * g⁻¹, hc'H⟩, ?_, rfl⟩
    rw [hCH, Subgroup.mem_inf]
    refine ⟨Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact (‹A.Normal›).conj_mem _ (Subgroup.mem_subgroupOf.mp hcA) g
    · rw [hZc, Subgroup.mem_comap, center_iff]
      intro h
      have hkH : g⁻¹ * (h : Γ) * g ∈ H := by
        have := hH.conj_mem (h : Γ) h.2 g⁻¹; rwa [inv_inv] at this
      have hk := hc_center ⟨g⁻¹ * (h : Γ) * g, hkH⟩
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      have hrel : (((h * ⟨g * (c : Γ) * g⁻¹, hc'H⟩ * h⁻¹ *
            (⟨g * (c : Γ) * g⁻¹, hc'H⟩ : ↥H)⁻¹ : ↥H) : Γ))
          = g * (((⟨g⁻¹ * (h : Γ) * g, hkH⟩ * c *
              (⟨g⁻¹ * (h : Γ) * g, hkH⟩ : ↥H)⁻¹ * c⁻¹ : ↥H) : Γ)) * g⁻¹ := by
        push_cast
        group
      rw [hrel]
      exact (‹B.Normal›).conj_mem _ hk g
  -- a nontrivial element of `(A/B) ⊓ Z(H/B)` gives `B ≠ C`
  obtain ⟨⟨q, hqmem⟩, hqne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinf
  rw [Subgroup.mem_inf] at hqmem
  obtain ⟨hqA, hqZ⟩ := hqmem
  rw [Subgroup.mem_map] at hqA
  obtain ⟨c₀, hc₀A, hc₀q⟩ := hqA
  have hq1 : q ≠ 1 := fun hq => hqne (Subtype.ext hq)
  have hc₀CH : c₀ ∈ CH := by
    rw [hCH, Subgroup.mem_inf]
    exact ⟨hc₀A, by rw [hZc, Subgroup.mem_comap, hc₀q]; exact hqZ⟩
  have hc₀C : (c₀ : Γ) ∈ C := by
    rw [hC]; exact Subgroup.mem_map_of_mem H.subtype hc₀CH
  have hc₀notB : (c₀ : Γ) ∉ B := by
    intro hb
    exact hq1 (by rw [← hc₀q]; exact (mk_eq_one c₀).2 (Subgroup.mem_subgroupOf.mpr hb))
  have hBneC : B ≠ C := fun heq => hc₀notB (heq.symm ▸ hc₀C)
  have hBC_lt : B < C := lt_of_le_of_ne hBC hBneC
  have hCeqA : C = A := by
    rcases eq_or_lt_of_le hCA with h | h
    · exact h
    · exact absurd (hmax C hCnorm hBC h) (Ne.symm (ne_of_lt hBC_lt))
  have hCHmap : CH.map H.subtype = A := by rw [← hC, hCeqA]
  have hCHeq : CH = A.subgroupOf H := by
    rw [← Subgroup.map_subtype_inj, hCHmap, Subgroup.map_subgroupOf_eq_of_le hAH]
  have hle : A.subgroupOf H ≤ Zc := by
    rw [← hCHeq, hCH]; exact inf_le_right
  rw [Subgroup.map_le_iff_le_comap, ← hZc]
  exact hle

/-- For `H ≤ G`, the commutator subgroup of the subtype group `↥H` is the `subgroupOf` of the
ambient commutator `⁅H, H⁆`.  In particular `Abelianization ↥H = ↥H ⧸ ⁅H, H⁆.subgroupOf H`, so the
index `|H : ⁅H,H⁆|` equals `|Abelianization ↥H|`. -/
theorem commutator_subgroupOf_self {G : Type*} [Group G] (H : Subgroup G) :
    (⁅H, H⁆ : Subgroup G).subgroupOf H = _root_.commutator ↥H := by
  have htop : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 : (_root_.commutator ↥H).map H.subtype = ⁅H, H⁆ := by
    show (⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆).map H.subtype = ⁅H, H⁆
    rw [Subgroup.map_commutator, htop]
  rw [← h1]
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

/-- For a finite `p`-group `K`, every irreducible character has degree a power of `p`
(its degree divides `|K| = pⁿ`).  This supplies the `θ = p^m` source-degree fields of the X-chain
step data once `H` is known to be a `p`-group (Peterfalvi (6.5)/(6.6)). -/
theorem exists_primePow_natDegree_of_isPGroup {K : Type*} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hK : IsPGroup p K) (θ : IrreducibleCharacter K) :
    ∃ k : ℕ, (θ : ClassFunction K ℂ) 1 = ((p ^ k : ℕ) : ℂ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, _hpos, hval, hdvd⟩ := θ.isIrreducible.exists_natDegree_charValue_one_dvd_card
  obtain ⟨N, hN⟩ := hK.exists_card_eq
  rw [hN] at hdvd
  obtain ⟨k, _hk_le, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨k, by rw [hval, hk]⟩

/-- A nontrivial finite `p`-group of odd order has `p ≥ 3` (its order `pⁿ` is odd, so `p` is odd).
Supplies the `3 ≤ p` field of the X-chain step data (in the (6.8) setup `|L|`, hence `|H|`, is
odd). -/
theorem three_le_prime_of_isPGroup_of_odd {K : Type*} [Group K] [Finite K] [Nontrivial K]
    {p : ℕ} (hp : p.Prime) (hK : IsPGroup p K) (hodd : Odd (Nat.card K)) : 3 ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have hcard : Nat.card K ≠ 1 := by
    simpa using (Finite.one_lt_card (α := K)).ne'
  have hn0 : n ≠ 0 := by rintro rfl; rw [pow_zero] at hn; exact hcard hn
  have hpdvd : p ∣ Nat.card K := hn ▸ dvd_pow_self p hn0
  obtain ⟨m, hm⟩ := Odd.of_dvd_nat hodd hpdvd
  have := hp.two_le
  omega

/-- A quotient of a finite `p`-group is a `p`-group, so its order is a power of `p`.  In the (6.6)
setup this gives `|H:Z| = p^k` (`H` a `p`-group), the key to `θχ(1)² ∣ |H:Z|` (both `p`-powers). -/
theorem exists_primePow_card_quotient_of_isPGroup {K : Type*} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hK : IsPGroup p K) (N : Subgroup K) [N.Normal] :
    ∃ k : ℕ, Nat.card (K ⧸ N) = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact (hK.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)).exists_card_eq

/-- Peterfalvi (6.1): the filtration `S(A)` attached to the base character set
`S`.  In the text, larger kernel conditions give smaller subsets:
if `A ≤ B`, then `S(B) ⊆ S(A)`. -/
structure FiltrationData (S : Set (ClassFunction L ℂ)) where
  carrier : Subgroup L → Set (ClassFunction L ℂ)
  subset_base : ∀ A, carrier A ⊆ S
  mono : ∀ ⦃A B : Subgroup L⦄, A ≤ B → carrier B ⊆ carrier A

namespace FiltrationData

variable {S : Set (ClassFunction L ℂ)}

theorem subset_base_apply (F : FiltrationData (L := L) S) (A : Subgroup L) :
    F.carrier A ⊆ S :=
  F.subset_base A

theorem mem_base (F : FiltrationData (L := L) S) {A : Subgroup L}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ F.carrier A) : χ ∈ S :=
  F.subset_base A hχ

theorem mono_apply (F : FiltrationData (L := L) S) {A B : Subgroup L}
    (hAB : A ≤ B) : F.carrier B ⊆ F.carrier A :=
  F.mono hAB

theorem zSupportedSpan_subset_base (F : FiltrationData (L := L) S)
    (A : Subgroup L) (B : Set L) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) (F.carrier A) B ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S B := by
  intro φ hφ
  exact OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left (L := L)
    (F.subset_base A) hφ

theorem zSupportedSpan_mono_apply (F : FiltrationData (L := L) S)
    {A₁ A₂ : Subgroup L} (hA : A₁ ≤ A₂) (B : Set L) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) (F.carrier A₂) B ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) (F.carrier A₁) B := by
  intro φ hφ
  exact OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left (L := L)
    (F.mono hA) hφ

end FiltrationData

/-- Peterfalvi (6.1): solvable-normal filtration setup for applying coherence
descent. -/
structure DescentHypothesis (S : Set (ClassFunction L ℂ)) (A : Set L)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  coherence : OddOrder.Peterfalvi.S07.Hypothesis (L := L) (G := G) S A
  K : Subgroup L
  K_normal : K.Normal
  K_solvable : IsSolvable K
  filtration : FiltrationData (L := L) S

namespace DescentHypothesis

variable {S : Set (ClassFunction L ℂ)} {A : Set L}
variable [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

theorem filtration_subset_base (hyp : DescentHypothesis (L := L) (G := G) S A)
    (A' : Subgroup L) : hyp.filtration.carrier A' ⊆ S :=
  hyp.filtration.subset_base A'

theorem filtration_mem_base (hyp : DescentHypothesis (L := L) (G := G) S A)
    {A' : Subgroup L} {χ : ClassFunction L ℂ}
    (hχ : χ ∈ hyp.filtration.carrier A') : χ ∈ S :=
  hyp.filtration.mem_base hχ

theorem filtration_mono (hyp : DescentHypothesis (L := L) (G := G) S A)
    {A₁ A₂ : Subgroup L} (hA : A₁ ≤ A₂) :
    hyp.filtration.carrier A₂ ⊆ hyp.filtration.carrier A₁ :=
  hyp.filtration.mono hA

theorem filtration_zSupportedSpan_subset_base
    (hyp : DescentHypothesis (L := L) (G := G) S A)
    (A' : Subgroup L) (B : Set L) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := L)
        (hyp.filtration.carrier A') B ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S B :=
  hyp.filtration.zSupportedSpan_subset_base A' B

theorem filtration_zSupportedSpan_mono
    (hyp : DescentHypothesis (L := L) (G := G) S A)
    {A₁ A₂ : Subgroup L} (hA : A₁ ≤ A₂) (B : Set L) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := L)
        (hyp.filtration.carrier A₂) B ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L)
        (hyp.filtration.carrier A₁) B :=
  hyp.filtration.zSupportedSpan_mono_apply hA B

end DescentHypothesis

/-- Peterfalvi (6.4): the odd-order specialization used before (6.5)-(6.6). -/
structure OddOrderSpecialization (S : Set (ClassFunction L ℂ)) (A : Set L)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] : Type _ extends
    DescentHypothesis (L := L) (G := G) S A where
  card_L_odd : Odd (Nat.card L)
  M : Subgroup L
  M_le_K : M ≤ K
  quotient_nilpotent : Prop

-- The legacy `SibleySetup`/`CoherenceTarget` (which carried an opaque `coherence.tau` with a
-- *global* `IsIntegralIsometry`, nonexistent in Feit–Thompson) is replaced by the Dade-based
-- `SibleyDadeHypothesis` below (T1; see issue 0046 / notes/peterfalvi/s08_6_8_assembly_plan.md).

/-- `H^# = H ∖ {1}` viewed as a subset of the ambient group `G`, for `H ≤ L ≤ G`.  This is the
support set `A` of the §4 Dade hypothesis in Peterfalvi (6.8): the nonidentity elements of `H`,
mapped from `↥L` into `G` along the inclusions. -/
def sharpImage {G : Type*} [Group G] {L : Subgroup G} (H : Subgroup ↥L) : Set G :=
  ((Subgroup.map L.subtype H : Subgroup G) : Set G) \ {1}

/-- **(5.6.1) supported-difference pairing: the Dade map `τ` pairs with the coherent extension `ν`
as the source inner product.**

For a supported `u` (`u.support ⊆ A`, e.g. the degree-matched difference `χ − a·χ₁`) and a
*supported* lattice element `δ ∈ ℤ[S₁] ∩ CF(L,A)` (e.g. a member difference `χⱼ − aⱼ·χ₁`), the Dade
image of `u` pairs with the running extension `ν = hS₁.extension` of `δ` exactly as the source pair:
`⟨τ u, ν δ⟩ = ⟨u, δ⟩`.

This is the recurring move of the (5.6.1) coefficient computation (mmd 04.7 L79): the cross terms
`⟨(χ − a·χ₁)^τ, (χⱼ − aⱼ·χ₁)^τ⟩` are evaluated by the Dade isometry on the supported pair, with
`(χⱼ − aⱼ·χ₁)^τ = (χⱼ − aⱼ·χ₁)^{τ₁} = ν δ` since `δ` is supported (`ν = τ` there,
`extends_on_supported`).

Note this does **not** apply with `δ = χ₁` itself: the induced anchor `χ₁ = Ind θ` is *unsupported*
(`χ₁(1) ≠ 0`, so `1 ∈ supp χ₁ ∉ A`), which is precisely why crux1 `⟨τ(χ − a·χ₁), ν χ₁⟩ = −a` is not
a direct corollary but needs the full (5.6.1)→(5.6.2) `Y`-collapse. -/
theorem inner_dade_extension_of_supported
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    {u : ClassFunction ↥L ℂ}
    (husupp : u.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {δ : ClassFunction ↥L ℂ}
    (hδ : δ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L)) :
    ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj) u)
        (hS₁.extension δ) =
      ClassFunction.inner u δ := by
  -- `ν δ = τ δ` since `δ` is supported (the coherent extension agrees with `τ` on `CF(L,A)`).
  rw [hS₁.extends_on_supported δ hδ]
  -- Dade isometry on the supported pair `{u, δ}`.
  have hδsupp : δ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L :=
    (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hδ).2
  refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hconj
    (S := {u, δ}) ?_ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  · exact husupp
  · exact hδsupp

/-- **crux1 from the (5.6.2) `Y`-collapse.**  The bridge `retarget_isCoherent_of_extensionImage`
consumes `crux1 : ⟨τ(χ − a·χ₁), ν χ₁⟩ = −a`.  This lemma reduces crux1 to its two genuine
ingredients, isolating the remaining (5.6.1)/(5.6.2) content:

* `hcollapse : Y = a·(ν χ₁)` — the (5.6.2) collapse `Da.Y = a·χ₁^{τ₁}` (mmd 04.7 (5.6.2)), where
  `Y` is the orthogonal residual of `τ(χ − a·χ₁) = X − Y` against `R(χ)`;
* `hXortho : ⟨X, ν χ₁⟩ = 0` — the (5.2.e) orthogonality `R(χ) ⊥ R(χ₁)` (since `X ∈ ℤ[R(χ)]` and
  `ν χ₁ ∈ ℤ[R(χ₁)]`).

Given `himg : τ(χ − a·χ₁) = X − Y` (the decomposition, from `Da.tau1_image` with `Da.tau1 = τ`) and
the unit norm `‖ν χ₁‖² = 1` (from the ν-isometry, `⟨χ₁, χ₁⟩ = 1`), crux1 is then pure inner-product
algebra: `⟨X − a·νχ₁, νχ₁⟩ = ⟨X, νχ₁⟩ − a·‖νχ₁‖² = 0 − a = −a`.

Stated abstractly over `G` (no Dade/coherence structure): the remaining work is to *produce*
`hcollapse` (the λ-form `Y = a·νχ₁ − λ·∑ rᵢ·νχᵢ + Z` collapsed via `lambda_eq_zero_and_Z_eq_zero`)
and `hXortho` (per-`α` member orthogonality summed over `R(χ)`). -/
theorem crux1_of_collapse {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {w X Y νchi1 : ClassFunction G ℂ} {a : ℕ}
    (himg : w = X - Y)
    (hcollapse : Y = a • νchi1)
    (hXortho : ClassFunction.inner X νchi1 = 0)
    (hνnorm : ClassFunction.inner νchi1 νchi1 = 1) :
    ClassFunction.inner w νchi1 = -(a : ℂ) := by
  rw [himg, hcollapse, ClassFunction.inner_sub_left, hXortho,
    ← Nat.cast_smul_eq_nsmul ℂ a νchi1, ClassFunction.inner_smul_left, hνnorm]
  ring

/-- **(5.2.e) member R-orthogonality `⟨X, ν χ₁⟩ = 0` — the `hXortho` ingredient of `crux1_of_collapse`.**

The `R(χ)`-part `X = D.X ∈ ℤ[R(χ)]` of the χ-decomposition `D` is orthogonal to the running image
`ν χ₁ = hS₁.extension χ₁` of any member `χ₁ ∈ S₁`, given the member's own `ψ = 0` decomposition `D'`
(so `ν χ₁ = D'.X ∈ ℤ[R(χ₁)]` by (5.5)) and the family orthogonality `R(χ₁) ⊥ R(χ)` ((5.2.e)).

Per-`α` orthogonality `⟨ν χ₁, α⟩ = 0` for `α ∈ R(χ)` (`inner_extension_member_orthogonal_imageSet`,
from `D'`/`hortho`/`htau1`) is summed over `R(χ)` by `inner_X_eq_zero_of_orthogonal_imageSet` to give
`⟨ν χ₁, X⟩ = 0`; conjugate symmetry flips it to `⟨X, ν χ₁⟩ = 0`.  The remaining work for the actual
`hXortho` is to *build* `D'` (the member ν-aux decomposition, needing `ν χ₁ ∈ ZIrr` injected since
`IsCoherent` carries no ZIrr-codomain) and `hortho` (the Dade `R(·)`-family orthogonality). -/
theorem inner_decomposition_X_extension_member_eq_zero
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Type*} [Group L] [Fintype L] [Invertible (Nat.card L : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    {S₁ : Set (ClassFunction L ℂ)} {A' : Set L}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A')
    {χ ψ chi1 : ClassFunction L ℂ}
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    (D' : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := L) (G := G) τ chi1 0)
    (hortho : D'.imageFamily.Orthogonal D.imageFamily)
    (htau1 : D'.tau1 chi1 = hS₁.extension chi1) :
    ClassFunction.inner D.X (hS₁.extension chi1) = 0 := by
  have h1 : ClassFunction.inner (hS₁.extension chi1) D.X = 0 :=
    D.inner_X_eq_zero_of_orthogonal_imageSet
      (fun α hα => OddOrder.Peterfalvi.S07.inner_extension_member_orthogonal_imageSet
        hS₁ D.imageFamily D' hortho htau1 hα)
  rw [OddOrder.RepresentationTheory.inner_conj_symm, h1, star_zero]

/-- **(5.5) member ν-aux decomposition: the running extension `ν` as the auxiliary isometry `τ₁`.**

For a member `χ ∈ S₁` (non-real irreducible, with `χ̄ ∈ S₁` and `χ̄ − χ` supported), builds the (5.5)
`ψ = 0` decomposition `D' : CharacterPsiDecomposition τ χ 0` whose **auxiliary isometry `τ₁` is the
running extension `ν = hS₁.extension`** (not the Dade base map `τ`).  Then `D'.tau1 χ = ν χ`
(definitionally) and, via (5.5) (`eq_sum_of_psi_eq_zero`), `ν χ = D'.X ∈ ℤ[R(χ)]`.

This is the member family input that discharges the `D'`/`htau1` hypotheses of
`inner_decomposition_X_extension_member_eq_zero` (and the (5.6.1) λ-form), built from the Dade
`R(χ)` family (`dadeOrthonormalCharacterImageFamilyOfDiff`) and the coherent extension:

* `htau1_inner_eq` — `ν` is a `ℤ[χ−χ̄, χ]`-isometry: both generators lie in `ℤ[S₁]` (since
  `χ, χ̄ ∈ S₁`), where `hS₁.extension_inner_eq` applies;
* `htau1_agrees` — `ν(χ−χ̄) = τ(χ−χ̄)` since `χ−χ̄` is supported (`extends_on_supported`);
* `htau1_mem` — `ν χ ∈ ZIrr G` is the hypothesis `hνZ`.  Since `IsCoherent` gained the
  `extension_mem_ZIrr` field (route A), this is now derivable from `χ ∈ S₁ ⊆ ℤ[S₁]` via
  `hS₁.extension_mem_ZIrr`; callers discharge it from the field (it is kept as an explicit argument
  here only because this `def` predates the field).

The remaining (5.4) orthogonality scalars `⟨χ, 0⟩ = ⟨χ̄, 0⟩ = 0` are trivial and `⟨χ, χ̄⟩ = 0` is
`hχχbar`. -/
noncomputable def memberExtensionDecomposition
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L)
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsupp : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχ_S1 : (χ : ClassFunction ↥L ℂ) ∈ S₁)
    (hχbar_S1 : (χ : ClassFunction ↥L ℂ).conj ∈ S₁)
    (hνZ : hS₁.extension (χ : ClassFunction ↥L ℂ) ∈ ZIrr G)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (χ : ClassFunction ↥L ℂ) 0 := by
  classical
  have hχmem : (χ : ClassFunction ↥L ℂ) ∈ Submodule.span ℤ S₁ := Submodule.subset_span hχ_S1
  have hχbarmem : (χ : ClassFunction ↥L ℂ).conj ∈ Submodule.span ℤ S₁ :=
    Submodule.subset_span hχbar_S1
  -- The (5.4) sponsoring set `{χ − χ̄, χ − 0}` lies in `ℤ[S₁]`.
  have hle : Submodule.span ℤ ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
      (χ : ClassFunction ↥L ℂ) - 0} : Set (ClassFunction ↥L ℂ)) ≤ Submodule.span ℤ S₁ := by
    rw [Submodule.span_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact Submodule.sub_mem _ hχmem hχbarmem
    · rw [sub_zero]; exact hχmem
  -- `χ − χ̄` is supported (vanishes off `A`), hence in `ℤ[S₁] ∩ CF(L,A)`.
  have hdiffsupported : (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) :=
    OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
      ⟨Submodule.sub_mem _ hχmem hχbarmem, by
        rw [show (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj =
            -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) by abel,
          ClassFunction.support_neg]
        exact hdiffsupp⟩
  exact OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
    (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp hconj χ hreal hdiffsupp)
    hS₁.extension
    (fun φ ζ hφ hζ => hS₁.extension_inner_eq φ ζ (hle hφ) (hle hζ))
    (hS₁.extends_on_supported _ hdiffsupported)
    (by rw [sub_zero]; exact hνZ)
    (by simp)
    (by simp)
    hχχbar

/-- **(5.2.e) conjugate-difference orthogonality via *difference* supports (induced case).**

`⟨(x − x̄)^τ, (χ − χ̄)^τ⟩ = 0` whenever the **conjugate differences** `x̄ − x` and `χ̄ − χ` are
supported in `CF(L,A)` and `x, x̄ ⊥ χ, χ̄`.  Unlike
`dadeIntegralCharacterMap_inner_conjDifference_eq_zero` (which needs the *individual* supports of
`x, x̄, χ, χ̄`), this evaluates the Dade isometry directly on the two supported differences `x − x̄`,
`χ − χ̄` (`dadeIntegralCharacterMap_inner_eq_on_supported_span` on the set `{x − x̄, χ − χ̄}`), so it
applies to **induced** `x = Ind θ`, `χ = Ind θ'` whose individual values at `1` are nonzero.  The
reduced source pairing `⟨x − x̄, χ − χ̄⟩` expands to the four cross terms, all zero. -/
theorem inner_dadeDiff_conjDifference_eq_zero
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {x χ : ClassFunction ↥L ℂ}
    (hxdiffsupp : (x.conj - x).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχdiffsupp : (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hxχ : ClassFunction.inner x χ = 0) (hxχbar : ClassFunction.inner x χ.conj = 0)
    (hxbarχ : ClassFunction.inner x.conj χ = 0) (hxbarχbar : ClassFunction.inner x.conj χ.conj = 0) :
    ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
          (x - x.conj))
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
          (χ - χ.conj)) = 0 := by
  classical
  have hS : ∀ s ∈ ({x - x.conj, χ - χ.conj} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [show x - x.conj = -(x.conj - x) by abel, ClassFunction.support_neg]; exact hxdiffsupp
    · rw [show χ - χ.conj = -(χ.conj - χ) by abel, ClassFunction.support_neg]; exact hχdiffsupp
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hconj hS
    (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    hxχ, hxχbar, hxbarχ, hxbarχbar, sub_zero, sub_self]

/-- **(5.2.e) Dade `R(·)`-family orthogonality via *difference* supports (induced case).**

`R(x) ⊥ R(χ)` for the difference-support Dade families `dadeOrthonormalCharacterImageFamilyOfDiff`
whenever `x, x̄ ⊥ χ, χ̄`.  Mirrors `dadeOrthonormalCharacterImageFamily_orthogonal` but reduces — via
`toOrthonormalImage_orthogonal` and `orthogonal_of_signedDifference_inner_eq_zero` — to the
*difference-support* orthogonality `inner_dadeDiff_conjDifference_eq_zero`, so it applies to the
**unsupported induced** X-members.  This is the `hortho` ingredient of
`inner_decomposition_X_extension_member_eq_zero`. -/
theorem dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {x χ : IrreducibleCharacter ↥L}
    (hxreal : ¬ ClassFunction.IsReal (x : ClassFunction ↥L ℂ))
    (hxdiffsupp : ((x : ClassFunction ↥L ℂ).conj - (x : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hχdiffsupp : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hxχ : ClassFunction.inner (x : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 0)
    (hxχbar : ClassFunction.inner (x : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hxbarχ : ClassFunction.inner (x : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hxbarχbar :
      ClassFunction.inner (x : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ).conj = 0) :
    (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp hconj x hxreal
        hxdiffsupp).Orthogonal
      (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp hconj χ hreal
        hχdiffsupp) := by
  unfold OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
  refine OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage_orthogonal _ _
    (OddOrder.Peterfalvi.S07.CharacterDifferenceImage.orthogonal_of_signedDifference_inner_eq_zero
      _ _ ?_)
  rw [← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference,
    ← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference]
  exact inner_dadeDiff_conjDifference_eq_zero hyp hconj hxdiffsupp hχdiffsupp
    hxχ hxχbar hxbarχ hxbarχbar

/-- **Member-side R-orthogonality `⟨Da.X, ν χ₁⟩ = 0`, fully assembled for the induced `Da`.**

The `hXortho` ingredient of `crux1_of_collapse`, with *every* member-side input discharged from the
injected data: `Da = decompositionDaFromDadeOfDiff` (the χ-decomposition), the member ν-aux
decomposition `D' = memberExtensionDecomposition` of `χ₁` (so `ν χ₁ = D'.X ∈ ℤ[R(χ₁)]` and
`D'.tau1 χ₁ = ν χ₁` definitionally), and the difference-support family orthogonality `R(χ₁) ⊥ R(χ)`
(`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`).  Chained through
`inner_decomposition_X_extension_member_eq_zero`.

This leaves only the (5.6.1)/(5.6.2) `Y`-collapse `Da.Y = a·ν χ₁` as the remaining input for crux1
(via `crux1_of_collapse` + `Da.tau1_image`). -/
theorem inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ chi1 : IrreducibleCharacter ↥L) {a : ℕ}
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (chi1 : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - a • (chi1 : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (hχaχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (a • (chi1 : ClassFunction ↥L ℂ)) = 0)
    (hχbaraχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (a • (chi1 : ClassFunction ↥L ℂ)) = 0)
    (hχχbar' : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hrealc1 : ¬ ClassFunction.IsReal (chi1 : ClassFunction ↥L ℂ))
    (hdiffsuppc1 : ((chi1 : ClassFunction ↥L ℂ).conj - (chi1 : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hc1S1 : (chi1 : ClassFunction ↥L ℂ) ∈ S₁) (hc1barS1 : (chi1 : ClassFunction ↥L ℂ).conj ∈ S₁)
    (hνZc1 : hS₁.extension (chi1 : ClassFunction ↥L ℂ) ∈ ZIrr G)
    (hc1c1bar : ClassFunction.inner (chi1 : ClassFunction ↥L ℂ)
      (chi1 : ClassFunction ↥L ℂ).conj = 0)
    (hc1χ : ClassFunction.inner (chi1 : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 0)
    (hc1χbar : ClassFunction.inner (chi1 : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hc1barχ : ClassFunction.inner (chi1 : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hc1barχbar : ClassFunction.inner (chi1 : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 0) :
    ClassFunction.inner
        (OddOrder.Peterfalvi.S07.decompositionDaFromDadeOfDiff hyp hconj χ hrealχ hdiffsuppχ
          hdiffasuppχ htau1_memaχ hχaχ1 hχbaraχ1 hχχbar').X
        (hS₁.extension (chi1 : ClassFunction ↥L ℂ)) = 0 :=
  inner_decomposition_X_extension_member_eq_zero hS₁
    (OddOrder.Peterfalvi.S07.decompositionDaFromDadeOfDiff hyp hconj χ hrealχ hdiffsuppχ
      hdiffasuppχ htau1_memaχ hχaχ1 hχbaraχ1 hχχbar')
    (memberExtensionDecomposition hyp hconj hS₁ chi1 hrealc1 hdiffsuppc1 hc1S1 hc1barS1 hνZc1
      hc1c1bar)
    (dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal hyp hconj hrealc1 hdiffsuppc1 hrealχ
      hdiffsuppχ hc1χ hc1χbar hc1barχ hc1barχbar)
    rfl

/-- **(5.6.1) member coefficient `⟨Da.Y, ν χⱼ⟩` — the heart of the λ-form.**

The (5.6.1) projection coefficient (mmd 04.7 L79): for a member `χⱼ` with degree-matched difference
`χⱼ − aⱼ·χ₁` (the value enters via `hfound`, `inner_dade_extension_of_supported` applied to the
supported `δ = χⱼ − aⱼ·χ₁`),

`⟨Y, ν χⱼ⟩ = a·⟨χ₁, χⱼ⟩ − (a + μ)·aⱼ`,    where `Y = X − τ(χ − a·χ₁)`, `μ = ⟨τ(χ − a·χ₁), ν χ₁⟩`.

The computation: `⟨Y, νχⱼ⟩ = −⟨τ(χ−a·χ₁), νχⱼ⟩` (since `⟨X, νχⱼ⟩ = 0`, the member R-orthogonality);
split `νχⱼ = ν(χⱼ − aⱼ·χ₁) + aⱼ·νχ₁` (ν is `ℤ`-linear); the first part is `⟨χ − a·χ₁, χⱼ − aⱼ·χ₁⟩`
(`hfound`), which expands via `χ ⊥ χⱼ, χ₁` and `‖χ₁‖² = 1` to `−a·⟨χ₁, χⱼ⟩ + a·aⱼ`; the second is
`aⱼ·μ`.  With `λ := a + μ` this is `a·⟨χ₁,χⱼ⟩ − λ·aⱼ`, the `lambda_eq_zero_and_Z_eq_zero`
coefficient (`χ₁,χⱼ` orthonormal ⟹ `⟨χ₁,χⱼ⟩ = δ`, giving `a·[j=1] − λ·aⱼ`). -/
theorem inner_Y_extension_member_eq
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : ClassFunction ↥L ℂ) {chi1 cj : ClassFunction ↥L ℂ} {a aj : ℕ} {Xχ Y : ClassFunction G ℂ}
    (hYeq : Y = Xχ - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj) ((χ : ClassFunction ↥L ℂ) - a • chi1))
    (hXortho : ClassFunction.inner Xχ (hS₁.extension cj) = 0)
    (hfound : ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
          ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension (cj - aj • chi1)) =
      ClassFunction.inner ((χ : ClassFunction ↥L ℂ) - a • chi1) (cj - aj • chi1))
    (hχcj : ClassFunction.inner (χ : ClassFunction ↥L ℂ) cj = 0)
    (hχchi1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ) chi1 = 0)
    (hchi1chi1 : ClassFunction.inner chi1 chi1 = 1) :
    ClassFunction.inner Y (hS₁.extension cj) =
      (a : ℂ) * ClassFunction.inner chi1 cj -
        ((a : ℂ) + ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
            ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension chi1)) * (aj : ℂ) := by
  -- `ν cj = ν(cj − aⱼ·χ₁) + aⱼ·ν χ₁` (ν is ℤ-linear).
  have hνcj : hS₁.extension cj
      = hS₁.extension (cj - aj • chi1) + aj • hS₁.extension chi1 := by
    rw [map_sub, map_nsmul]; abel
  -- The source-side expansion `⟨χ − a·χ₁, χⱼ − aⱼ·χ₁⟩ = −a·⟨χ₁, χⱼ⟩ + a·aⱼ`.
  have hsrc : ClassFunction.inner ((χ : ClassFunction ↥L ℂ) - a • chi1) (cj - aj • chi1)
      = -(a : ℂ) * ClassFunction.inner chi1 cj + (a : ℂ) * (aj : ℂ) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a chi1, ← Nat.cast_smul_eq_nsmul ℂ aj chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχcj, hχchi1, hchi1chi1, star_natCast]
    ring
  -- The χ₁-side `⟨τ(χ − a·χ₁), aⱼ·ν χ₁⟩ = aⱼ·μ`.
  have hsmul : ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
          ((χ : ClassFunction ↥L ℂ) - a • chi1)) (aj • hS₁.extension chi1) =
      (aj : ℂ) * ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
          ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension chi1) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ aj (hS₁.extension chi1),
      OddOrder.RepresentationTheory.inner_smul_right, star_natCast]
  rw [hYeq, ClassFunction.inner_sub_left, hXortho, zero_sub, hνcj,
    ClassFunction.inner_add_right, hfound, hsrc, hsmul]
  ring

open scoped Classical in
/-- **Indexed integral orthogonal projection onto a ZIrr-orthonormal family.**

The `ι`-indexed form of `exists_intProjection_of_orthonormal_ZIrr`, the shape the (5.6.2)
integer-forcing `lambda_eq_zero_and_Z_eq_zero` consumes: for `φ ∈ ZIrr G` and an **injective**
orthonormal family `vc : ι → CF G` over `s : Finset ι` (each `vc i ∈ ZIrr G`), there are integer
coefficients `c i = ⟨φ, vc i⟩` and an orthogonal residual `Z` with

`φ = (∑_{i ∈ s} c i • vc i) + Z`    and    `⟨Z, vc i⟩ = 0`.

Reindexes the image-indexed primitive (`R = s.image vc`, `Finset.sum_image` with `hvcinj`). -/
theorem exists_indexed_intProjection_of_orthonormal_ZIrr
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    {ι : Type*} (s : Finset ι) (vc : ι → ClassFunction G ℂ)
    (hvcZ : ∀ i ∈ s, vc i ∈ ZIrr G)
    (hvcinj : ∀ i ∈ s, ∀ j ∈ s, vc i = vc j → i = j)
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (vc i) (vc j) = if i = j then (1 : ℂ) else 0) :
    ∃ (c : ι → ℤ) (Z : ClassFunction G ℂ),
      (∀ i ∈ s, ClassFunction.inner φ (vc i) = (c i : ℂ)) ∧
      φ = (∑ i ∈ s, (c i : ℂ) • vc i) + Z ∧
      ∀ i ∈ s, ClassFunction.inner Z (vc i) = 0 := by
  classical
  have hZR : ∀ α ∈ s.image vc, α ∈ ZIrr G := by
    intro α hα; rw [Finset.mem_image] at hα; obtain ⟨i, hi, rfl⟩ := hα; exact hvcZ i hi
  have horthR : ∀ α ∈ s.image vc, ∀ β ∈ s.image vc,
      ClassFunction.inner α β = if α = β then (1 : ℂ) else 0 := by
    intro α hα β hβ
    rw [Finset.mem_image] at hα hβ
    obtain ⟨i, hi, rfl⟩ := hα; obtain ⟨j, hj, rfl⟩ := hβ
    rw [horth i hi j hj]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · rw [if_neg hij, if_neg (fun h => hij (hvcinj i hi j hj h))]
  obtain ⟨c, Y, hcoeff, hsum, hY⟩ :=
    ClassFunction.exists_intProjection_of_orthonormal_ZIrr hφ hZR horthR
  refine ⟨fun i => c (vc i), Y, fun i hi => hcoeff (vc i) (Finset.mem_image_of_mem vc hi), ?_,
    fun i hi => hY (vc i) (Finset.mem_image_of_mem vc hi)⟩
  rw [hsum, Finset.sum_image hvcinj]

open scoped Classical in
/-- **(5.6.1)/(5.6.2) crux1 from the member family: `⟨τ(χ − a·χ₁), ν χ₁⟩ = −a`.**

The capstone of the crux1 discharge — the genuine (5.6.1)/(5.6.2) `Y`-collapse for the induced
X-family, producing crux1 directly.  Given the finite orthonormal member family `{χᵢ = χmem i}` (all
in `S₁`, `‖χᵢ‖² = 1` — the case-A `X ⊆ Irr L`), the per-member (5.6.1) coefficient values
`hcoeffval` (from `inner_Y_extension_member_eq`), `a₁ = 1`, and the (6.6) degree inequality
`2a < ∑ aᵢ²`:

* the indexed projection (`exists_indexed_intProjection_of_orthonormal_ZIrr`) writes
  `Da.Y = ∑ᵢ (cᵢ:ℂ)·νχᵢ + Z` with integer `cᵢ = ⟨Da.Y, νχᵢ⟩`;
* `hcoeffval` identifies `cᵢ = a·[i=i₁] − λ·aᵢ` with the integer `λ = a + μ`, `μ = ⟨τ(χ−a·χ₁), νχ₁⟩`
  (an integer since both are virtual characters);
* the (5.6.2) integer-forcing `lambda_eq_zero_and_Z_eq_zero` then forces `λ = 0` (`Z = 0`), i.e.
  `μ = −a` — which **is** crux1.

`μ ∈ ℤ` is the load-bearing fact making `λ = a + μ` an integer; the degree inequality (6.6) is what
forces it to vanish. -/
theorem crux1_of_memberFamily
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hτ : τ = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent τ S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L) {a : ℕ}
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G) τ
      (χ : ClassFunction ↥L ℂ) (a • χmem i₁))
    (hDaY_ZIrr : Da.Y ∈ ZIrr G)
    (hmemS1 : ∀ i ∈ s, χmem i ∈ S₁)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i) (χmem j) = if i = j then (1 : ℂ) else 0)
    (hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y (hS₁.extension (χmem i)) =
      (a : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) + ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁))
          (hS₁.extension (χmem i₁))) * (deg i : ℂ))
    (hμZ : τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2) :
    ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁))
      (hS₁.extension (χmem i₁)) = -(a : ℂ) := by
  classical
  -- `hνZ` is derived (route A): `χmem i ∈ S₁ ⊆ ℤ[S₁]`, so `ν (χmem i) ∈ ℤ[Irr G]` by the
  -- `IsCoherent.extension_mem_ZIrr` field — it need not be injected as a hypothesis.
  have hνZ : ∀ i ∈ s, hS₁.extension (χmem i) ∈ ZIrr G :=
    fun i hi => hS₁.extension_mem_ZIrr (χmem i) (Submodule.subset_span (hmemS1 i hi))
  obtain ⟨μ, hμeq⟩ := ClassFunction.inner_mem_ZIrr_int hμZ (hνZ i₁ hi₁)
  -- Orthonormality of the family `vc i = ν χᵢ` (ν isometry on `ℤ[S₁]` + member orthonormality).
  have horth : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (hS₁.extension (χmem i)) (hS₁.extension (χmem j)) =
        if i = j then (1 : ℂ) else 0 := by
    intro i hi j hj
    rw [hS₁.extension_inner_eq (χmem i) (χmem j) (Submodule.subset_span (hmemS1 i hi))
      (Submodule.subset_span (hmemS1 j hj)), hmemortho i hi j hj]
  have hvcinj : ∀ i ∈ s, ∀ j ∈ s,
      hS₁.extension (χmem i) = hS₁.extension (χmem j) → i = j := by
    intro i hi j hj hij
    by_contra hne
    have h0 := horth i hi j hj
    rw [if_neg hne, hij, horth j hj j hj, if_pos rfl] at h0
    exact one_ne_zero h0
  obtain ⟨c, Z, hc_coeff, hYsum, hZortho⟩ :=
    exists_indexed_intProjection_of_orthonormal_ZIrr hDaY_ZIrr s
      (fun i => hS₁.extension (χmem i)) hνZ hvcinj horth
  -- Coefficient identification `(c i : ℂ) = a·[i=i₁] − (a+μ)·aᵢ`.
  have hcoeff_eq : ∀ i ∈ s, (c i : ℂ) =
      (((a : ℝ) * (if i = i₁ then 1 else 0) - ((a : ℤ) + μ : ℤ) * (deg i : ℝ) : ℝ) : ℂ) := by
    intro i hi
    rw [← hc_coeff i hi, hcoeffval i hi, hμeq]
    by_cases h : i = i₁
    · simp only [if_pos h]; push_cast; ring
    · simp only [if_neg h]; push_cast; ring
  -- The (5.6.1) λ-form and the (5.6.2) integer-forcing.
  have hY : Da.Y =
      (∑ i ∈ s, (((a : ℝ) * (if i = i₁ then 1 else 0) - ((a : ℤ) + μ : ℤ) * (deg i : ℝ) : ℝ) : ℂ)
        • hS₁.extension (χmem i)) + Z := by
    rw [hYsum]; congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [hcoeff_eq i hi]
  have hψ : (ClassFunction.inner (a • χmem i₁ : ClassFunction ↥L ℂ) (a • χmem i₁)).re
      = (a : ℝ) ^ 2 * 1 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁), ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hmemortho i₁ hi₁ i₁ hi₁, if_pos rfl,
      star_natCast, mul_one,
      show (a : ℂ) * (a : ℂ) = (((a : ℝ) ^ 2 * 1 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  obtain ⟨hlam0, -⟩ := Da.lambda_eq_zero_and_Z_eq_zero s i₁ hi₁ (a : ℝ) ((a : ℤ) + μ) Z
    (fun i => hS₁.extension (χmem i)) (fun _ => 1) (fun i => (deg i : ℝ))
    hY horth hZortho hψ (by simp [ha1]) (by positivity)
    (by simp only [mul_one]; exact hDeg)
  -- `λ = a + μ = 0 ⟹ μ = −a`, which is crux1.
  have hμval : μ = -(a : ℤ) := by omega
  rw [hμeq, hμval]; push_cast; ring

/-- **(T8.11 surgery, option A) coherence from the corrected extension image.**

The (5.6) adjoining step for the *induced (unsupported)* X-family.  Instead of mapping the new pair
`{χ, χ̄}` to a supported `ψ = 0` decomposition image (which needs `τχ ∈ ZIrr`, false for the
unsupported `χ = Ind θ`), `χ` is mapped to the **corrected extension image**
`X := τ(χ − a·χ₁) + a·νχ₁` (both terms integral).  This makes the (5.6.2) image equation `himg`
definitional, **bypassing** the `htau1_chi1` requirement `τχ₁ = νχ₁` that fails for unsupported `χ₁`.

Every remaining obligation of `retarget_isCoherent` is discharged from the source/Dade/ν isometries
plus the two crux inner products `hcrux1 : ⟨τ(χ−a·χ₁), νχ₁⟩ = −a` and `hcrux2 : ⟨τ(χ−χ̄), νχ₁⟩ = 0`
(the genuine (5.6) Feit–Sibley content, to be discharged separately via the degree inequality).  The
lattice orthogonality `hX_ortho`/`hXbar_ortho` is a span induction over
`ℤ[S₁] ⊆ span(ℤ[S₁,A] ∪ {χ₁})` (`hSgen`): clean on a supported `ξ` (`νξ = τξ` + Dade isometry) and
on `χ₁` via `hcrux1`/`hcrux2`. -/
noncomputable def retarget_isCoherent_of_extensionImage
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hτ : τ = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      τ S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L) {chi1 : ClassFunction ↥L ℂ} {a : ℕ}
    (hdiffsupp : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hdiffasupp : ((χ : ClassFunction ↥L ℂ) - a • chi1).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hchi1chi1 : ClassFunction.inner chi1 chi1 = 1)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    (hchi1 : chi1 ∈ S₁)
    (hτaχ1Z : τ ((χ : ClassFunction ↥L ℂ) - a • chi1) ∈ ZIrr G)
    (hτdiffZ : τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj) ∈ ZIrr G)
    (hcrux1 : ClassFunction.inner
      (τ
        ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension chi1) = -(a : ℂ))
    (hcrux2 : ClassFunction.inner
      (τ
        ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) (hS₁.extension chi1) = 0)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {chi1}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • chi1})) :
    OddOrder.Peterfalvi.S07.IsCoherent
      τ
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  classical
  -- `χ₁ ⊥ χ, χ̄` (both directions, from `hχ_S1`/`hχbar_S1` and conjugate symmetry).
  have hχchi1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ) chi1 = 0 := hχ_S1 chi1 hchi1
  have hchi1χ : ClassFunction.inner chi1 (χ : ClassFunction ↥L ℂ) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχchi1, star_zero]
  have hχbarchi1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj chi1 = 0 := hχbar_S1 chi1 hchi1
  have hchi1χbar : ClassFunction.inner chi1 (χ : ClassFunction ↥L ℂ).conj = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbarchi1, star_zero]
  -- The supported difference lattice `{χ−χ̄, χ−a·χ₁}` and the Dade isometry on it.
  have hSdiff : ∀ s ∈ ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
      (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [show (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj =
          -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) from by abel,
        ClassFunction.support_neg]
      exact hdiffsupp
    · exact hdiffasupp
  have hmemu : (χ : ClassFunction ↥L ℂ) - a • chi1 ∈ Submodule.span ℤ
      ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
        (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) :=
    Submodule.subset_span (by simp)
  have hmemd : (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj ∈ Submodule.span ℤ
      ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
        (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) :=
    Submodule.subset_span (by simp)
  have hdade : ∀ φ ψ, φ ∈ Submodule.span ℤ
        ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
          (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) →
      ψ ∈ Submodule.span ℤ
        ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
          (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) →
      ClassFunction.inner (τ φ) (τ ψ) = ClassFunction.inner φ ψ := fun φ ψ hφ hψ => by
    rw [hτ]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hconj
      hSdiff hφ hψ
  -- Dade-image inner products (Dade isometry + source orthonormality).
  have huu : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • chi1))
      (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) = 1 + (a : ℂ) ^ 2 := by
    rw [hdade _ _ hmemu hmemu, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχχ, hχchi1, hchi1χ, hchi1chi1, star_natCast]
    ring
  have hud : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • chi1))
      (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 1 := by
    rw [hdade _ _ hmemu hmemd, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχχ, hχχbar, hchi1χ, hchi1χbar, star_natCast]
    ring
  have hdd : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj))
      (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 2 := by
    rw [hdade _ _ hmemd hmemd]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      hχχ, hχχbar, hχbarχ, hχbarχbar]
    ring
  have hdu : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj))
      (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) = 1 := by
    rw [hdade _ _ hmemd hmemu, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχχ, hχchi1, hχbarχ, hχbarchi1, star_natCast]
    ring
  -- `hS₁.extension χ₁` norm and the conjugates of the two crux inner products.
  have hvv : ClassFunction.inner (hS₁.extension chi1) (hS₁.extension chi1) = 1 := by
    rw [hS₁.extension_inner_eq chi1 chi1 (Submodule.subset_span hchi1)
      (Submodule.subset_span hchi1), hchi1chi1]
  have hvu : ClassFunction.inner (hS₁.extension chi1)
      (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) = -(a : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcrux1]; simp
  have hvd : ClassFunction.inner (hS₁.extension chi1)
      (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcrux2, star_zero]
  set X : ClassFunction G ℂ :=
    τ ((χ : ClassFunction ↥L ℂ) - a • chi1) + a • hS₁.extension chi1 with hX
  set Xbar : ClassFunction G ℂ := X - τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)
    with hXbar
  -- `X, X̄ ∈ ℤ[Irr G]`: the supported Dade images `(χ−a·χ₁)^τ`, `(χ−χ̄)^τ` are virtual (hypotheses),
  -- and `ν χ₁ ∈ ZIrr` is now recorded by the coherence's `extension_mem_ZIrr` field (`χ₁ ∈ S₁`).
  have hνchi1Z : hS₁.extension chi1 ∈ ZIrr G :=
    hS₁.extension_mem_ZIrr chi1 (Submodule.subset_span hchi1)
  have hXZ : X ∈ ZIrr G := by
    rw [hX]
    refine Submodule.add_mem _ hτaχ1Z ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ a (hS₁.extension chi1)]
    exact Submodule.smul_mem _ (a : ℤ) hνchi1Z
  have hXbarZ : Xbar ∈ ZIrr G := by rw [hXbar]; exact Submodule.sub_mem _ hXZ hτdiffZ
  -- `‖X‖² = 1`.
  have hXX : ClassFunction.inner X X = 1 := by
    rw [hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hcrux1, hvu, hvv, star_natCast]
    ring
  -- `‖X̄‖² = 1`.
  have hXbarXbar : ClassFunction.inner Xbar Xbar = 1 := by
    rw [hXbar, hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hud, hdu, hdd, hcrux1, hcrux2, hvu, hvd, hvv, star_natCast]
    ring
  -- `⟨X, X̄⟩ = 0`.
  have hXXbar : ClassFunction.inner X Xbar = 0 := by
    rw [hXbar, hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hud, hdu, hcrux1, hcrux2, hvu, hvd, hvv, star_natCast]
    ring
  -- `⟨X̄, X⟩ = 0`.
  have hXbarX : ClassFunction.inner Xbar X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXXbar, star_zero]
  -- `⟨ντ, τ(χ−a·χ₁)⟩ = −a·⟨ξ, χ₁⟩` on the generating set `ℤ[S₁,A] ∪ {χ₁}`, then on `ℤ[S₁]`.
  have hkey : ∀ ξ ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {chi1}),
      ClassFunction.inner (hS₁.extension ξ) (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) =
        -(a : ℂ) * ClassFunction.inner ξ chi1 := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hsupp | hy1
        · have hmem := OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hsupp
          have hνy : hS₁.extension y = τ y := hS₁.extends_on_supported y hsupp
          have hχy : ClassFunction.inner (χ : ClassFunction ↥L ℂ) y = 0 :=
            OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχ_S1 hmem.1
          have hyχ : ClassFunction.inner y (χ : ClassFunction ↥L ℂ) = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχy, star_zero]
          have hySdiff : ∀ s ∈ ({y, (χ : ClassFunction ↥L ℂ) - a • chi1} :
              Set (ClassFunction ↥L ℂ)),
              s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
            intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl
            · exact hmem.2
            · exact hdiffasupp
          rw [hνy, hτ, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
            hyp hconj hySdiff (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)),
            ← Nat.cast_smul_eq_nsmul ℂ a chi1]
          simp only [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
            hyχ, star_natCast]
          ring
        · rw [Set.mem_singleton_iff.mp hy1, hvu, hchi1chi1, mul_one]
    | zero => simp
    | add y z _ _ ihy ihz =>
        rw [map_add, ClassFunction.inner_add_left, ihy, ihz, ClassFunction.inner_add_left]; ring
    | smul c y _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ c (hS₁.extension y),
          ClassFunction.inner_smul_left, ih,
          ← Int.cast_smul_eq_zsmul ℂ c y, ClassFunction.inner_smul_left]; ring
  have hX_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (hS₁.extension ξ) X = 0 := by
    intro ξ hξ
    rw [hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1), ClassFunction.inner_add_right,
      OddOrder.RepresentationTheory.inner_smul_right, hkey ξ (hSgen hξ),
      hS₁.extension_inner_eq ξ chi1 hξ (Submodule.subset_span hchi1)]
    simp only [star_natCast]; ring
  -- `⟨hS₁.extension ξ, τ(χ−χ̄)⟩ = 0` on `ℤ[S₁]` (similar span induction; clean — no `χ₁` term).
  have hkeyd : ∀ ξ ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {chi1}),
      ClassFunction.inner (hS₁.extension ξ)
        (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 0 := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hsupp | hy1
        · have hmem := OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hsupp
          have hνy : hS₁.extension y = τ y := hS₁.extends_on_supported y hsupp
          have hχy : ClassFunction.inner (χ : ClassFunction ↥L ℂ) y = 0 :=
            OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχ_S1 hmem.1
          have hχbary : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj y = 0 :=
            OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχbar_S1 hmem.1
          have hyχ : ClassFunction.inner y (χ : ClassFunction ↥L ℂ) = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχy, star_zero]
          have hyχbar : ClassFunction.inner y (χ : ClassFunction ↥L ℂ).conj = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbary, star_zero]
          have hySdiff : ∀ s ∈ ({y, (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj} :
              Set (ClassFunction ↥L ℂ)),
              s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
            intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl
            · exact hmem.2
            · rw [show (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj =
                  -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) from by abel,
                ClassFunction.support_neg]
              exact hdiffsupp
          rw [hνy, hτ, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
            hyp hconj hySdiff (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))]
          simp only [ClassFunction.inner_sub_right, hyχ, hyχbar, sub_zero]
        · rw [Set.mem_singleton_iff.mp hy1, hvd]
    | zero => simp
    | add y z _ _ ihy ihz => rw [map_add, ClassFunction.inner_add_left, ihy, ihz, add_zero]
    | smul c y _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ c (hS₁.extension y),
          ClassFunction.inner_smul_left, ih,
          mul_zero]
  have hXbar_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (hS₁.extension ξ) Xbar = 0 := by
    intro ξ hξ
    rw [hXbar, ClassFunction.inner_sub_right, hX_ortho ξ hξ, hkeyd ξ (hSgen hξ), sub_zero]
  have himg : τ ((χ : ClassFunction ↥L ℂ) - a • chi1) = X - a • hS₁.extension chi1 := by
    rw [hX]; abel
  exact OddOrder.Peterfalvi.S07.retarget_isCoherent hS₁ hχχ hχbarχbar hχχbar hχbarχ
    hXX hXbarXbar hXXbar hXbarX hXZ hXbarZ hX_ortho hXbar_ortho rfl hχ_S1 hχbar_S1 hchi1 himg hgen

open scoped Classical in
/-- **(T-A1) Per-step X-family coherence adjoin from a member family.** (`noncomputable def`: the
conclusion `IsCoherent` lives in `Type`, carrying the new extension `ν`.)

The (5.6)/(6.6) per-step adjoining of a new induced X-pair `{χ, χ̄}` to a coherent set `S₁`, packaged
as a function of the member-family enumeration data.  This wires the landed crux1 chain (the genuine
(5.6.1)/(5.6.2) `Y`-collapse, `crux1_of_memberFamily`) into the adjoining bridge
(`retarget_isCoherent_of_extensionImage`).

Inputs: `IsCoherent τ S₁ A` for the Dade map `τ`, a non-real irreducible `χ` orthogonal to all of
`S₁` (with `χ̄` likewise), and a finite orthonormal member family `{χmem i}ᵢ∈ₛ ⊆ S₁` with degree
ratios `deg i` (base member `i₁` of ratio `1`), the degree-matched supported differences
`χmem i − deg i·χmem i₁` and `χ − a·χmem i₁`, and the supported Dade-image ZIrr fact
`(χ − a·χmem i₁)^τ ∈ ZIrr`.  The members' ZIrr-codomain `ν χmem i ∈ ZIrr` is read off the
`IsCoherent.extension_mem_ZIrr` field (route A: `χmem i ∈ S₁ ⊆ ℤ[S₁]`), not passed as a hypothesis.
The construction:

* `Da := decompositionDaFromDadeOfDiff …` (the χ-decomposition for `χ − a·χ₁`), with `Da.Y ∈ ZIrr`
  derived from `Da.X ∈ ℤ[R(χ)]` and `(χ − a·χ₁)^τ ∈ ZIrr`;
* per member `i`, the (5.2.e) orthogonality `⟨Da.X, ν χᵢ⟩ = 0`
  (`inner_decomposition_X_extension_member_eq_zero`) and the (5.6.1) cross-term `hfound`
  (`inner_dade_extension_of_supported`) assemble the coefficient `⟨Da.Y, ν χᵢ⟩`
  (`inner_Y_extension_member_eq`);
* `crux1_of_memberFamily` collapses the λ-form (degree inequality `2a < ∑ aᵢ²`) into
  crux1 `⟨τ(χ − a·χ₁), ν χ₁⟩ = −a`;
* crux2 `⟨τ(χ − χ̄), ν χ₁⟩ = 0` is clean from `R(χ) ⊥ R(χ₁)`;
* the bridge concludes `IsCoherent τ (S₁ ∪ {χ, χ̄}) A`.

The lattice-generation conditions `hSgen`/`hgen` (structural facts about the accumulator `S₁`) are
threaded to the bridge; the chain fold (`xChainCoherent`) discharges them from the X-family
enumeration. -/
noncomputable def xAdjoinStep
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → IrreducibleCharacter ↥L) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ i ∈ s, ¬ ClassFunction.IsReal (χmem i : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ).conj - (χmem i : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (hmembarS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ).conj ∈ S₁)
    (hmemconjortho : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χmem i : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (1 : ℂ) else 0)
    {a : ℕ}
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)})) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  classical
  -- The ZIrr-codomain of each member is now recorded by the coherence's `extension_mem_ZIrr` field
  -- (`χmem i ∈ S₁ ⊆ ℤ[S₁]`), so it need not be passed as a hypothesis (route A).
  have hmemνZ : ∀ i ∈ s, hS₁.extension (χmem i : ClassFunction ↥L ℂ) ∈ ZIrr G :=
    fun i hi => hS₁.extension_mem_ZIrr _ (Submodule.subset_span (hmemS1 i hi))
  -- The trivially-derived orthogonalities `χ, χ̄ ⊥ a·χ₁` for the χ-decomposition `Da`.
  have hχaχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ)
      (a • (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁ : ClassFunction ↥L ℂ),
      OddOrder.RepresentationTheory.inner_smul_right, hχ_S1 _ (hmemS1 i₁ hi₁), mul_zero]
  have hχbaraχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (a • (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁ : ClassFunction ↥L ℂ),
      OddOrder.RepresentationTheory.inner_smul_right, hχbar_S1 _ (hmemS1 i₁ hi₁), mul_zero]
  -- The χ-decomposition for the degree-matched difference `χ − a·χ₁`.
  -- (`let`, not `have`/`set`, so `Da.tau1 = τ` / `Da.imageFamily = R(χ)` reduce definitionally.)
  let Da := OddOrder.Peterfalvi.S07.decompositionDaFromDadeOfDiff hyp hconj χ hrealχ hdiffsuppχ
    hdiffasuppχ htau1_memaχ hχaχ1 hχbaraχ1 hχχbar
  -- `Da.X ∈ ZIrr` (integer combination of the orthonormal `R(χ)` family) ⟹ `Da.Y ∈ ZIrr`.
  have hDaX_ZIrr : Da.X ∈ ZIrr G := by
    rw [Da.X_eq]
    refine Submodule.sum_mem _ (fun α hα => ?_)
    rw [Int.cast_smul_eq_zsmul ℂ (Da.coeff α) α]
    exact Submodule.smul_mem _ (Da.coeff α) (Da.imageFamily.mem_ZIrr α hα)
  have hYeq : Da.Y = Da.X - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) := by
    have h : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) = Da.X - Da.Y :=
      Da.tau1_image
    rw [h]; abel
  have hDaY_ZIrr : Da.Y ∈ ZIrr G := by
    rw [hYeq]; exact Submodule.sub_mem _ hDaX_ZIrr htau1_memaχ
  have hchi1chi1 : ClassFunction.inner (χmem i₁ : ClassFunction ↥L ℂ)
      (χmem i₁ : ClassFunction ↥L ℂ) = 1 := by rw [hmemortho i₁ hi₁ i₁ hi₁]; simp
  -- The four `χmem i ⊥ {χ, χ̄}` orthogonalities (conjugate symmetry of `hχ_S1`/`hχbar_S1`).
  have hmemχ : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χ : ClassFunction ↥L ℂ) = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 _ (hmemS1 i hi), star_zero]
  have hmemχbar : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χ : ClassFunction ↥L ℂ).conj = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 _ (hmemS1 i hi), star_zero]
  have hmembarχ : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ) = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 _ (hmembarS1 i hi), star_zero]
  have hmembarχbar : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 _ (hmembarS1 i hi), star_zero]
  -- Per-member ν-aux decomposition `D'` and the (5.2.e) family orthogonality `R(χᵢ) ⊥ R(χ)`.
  -- (`let`, not `have`, so `(Dmem i hi).tau1 = ν` reduces definitionally for the `rfl` arguments.)
  let Dmem : ∀ i, i ∈ s → OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (χmem i : ClassFunction ↥L ℂ) 0 := fun i hi =>
    memberExtensionDecomposition hyp hconj hS₁ (χmem i) (hmemreal i hi) (hmemdiffsupp i hi)
      (hmemS1 i hi) (hmembarS1 i hi) (hmemνZ i hi) (hmemconjortho i hi)
  have hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal Da.imageFamily :=
    fun i hi =>
      dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal hyp hconj (hmemreal i hi)
        (hmemdiffsupp i hi) hrealχ hdiffsuppχ (hmemχ i hi) (hmemχbar i hi) (hmembarχ i hi)
        (hmembarχbar i hi)
  -- (5.2.e) `⟨Da.X, ν χᵢ⟩ = 0` per member.
  have hXortho : ∀ i ∈ s, ClassFunction.inner Da.X (hS₁.extension (χmem i : ClassFunction ↥L ℂ)) = 0 :=
    fun i hi => inner_decomposition_X_extension_member_eq_zero hS₁ Da (Dmem i hi) (hortho_mem i hi) rfl
  -- (5.6.1) cross-term `hfound` per member (`inner_dade_extension_of_supported`).
  have hfound : ∀ i ∈ s, ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
      (hS₁.extension ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ))) =
      ClassFunction.inner ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ))
        ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)) := fun i hi => by
    refine inner_dade_extension_of_supported hyp hconj hS₁ hdiffasuppχ ?_
    refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr ⟨?_, hmemdegdiffsupp i hi⟩
    refine Submodule.sub_mem _ (Submodule.subset_span (hmemS1 i hi)) ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ (deg i) (χmem i₁ : ClassFunction ↥L ℂ)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hmemS1 i₁ hi₁))
  -- The (5.6.1) member coefficient `⟨Da.Y, ν χᵢ⟩` in the `lambda_eq_zero_and_Z_eq_zero` form.
  have hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y
      (hS₁.extension (χmem i : ClassFunction ↥L ℂ)) =
      (a : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) + ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
            ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
          (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ))) * (deg i : ℂ) := by
    intro i hi
    have key := inner_Y_extension_member_eq hyp hconj hS₁ χ hYeq (hXortho i hi) (hfound i hi)
      (hχ_S1 _ (hmemS1 i hi)) (hχ_S1 _ (hmemS1 i₁ hi₁)) hchi1chi1
    rw [hmemortho i₁ hi₁ i hi] at key
    rw [key]
    rcases eq_or_ne i i₁ with h | h
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc : i₁ = i => h hc.symm)]
  -- crux1 via the λ-form collapse.
  have hcrux1 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
      (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ)) = -(a : ℂ) :=
    crux1_of_memberFamily hyp hconj
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) rfl
      hS₁ χ s (fun i => (χmem i : ClassFunction ↥L ℂ)) deg i₁ hi₁ Da hDaY_ZIrr hmemS1
      hmemortho hcoeffval htau1_memaχ ha1 hDeg
  -- crux2 clean: `⟨τ(χ − χ̄), ν χ₁⟩ = 0` from `R(χ) ⊥ R(χ₁)`.
  have hcrux2 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj))
      (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, Da.imageFamily.image_eq,
      OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_eq_zero (fun α hα =>
        OddOrder.Peterfalvi.S07.inner_extension_member_orthogonal_imageSet hS₁ Da.imageFamily
          (Dmem i₁ hi₁) (hortho_mem i₁ hi₁) rfl hα), star_zero]
  -- `(χ − χ̄)^τ ∈ ZIrr` from the `R(χ)` family (`image_eq`); `(χ − a·χ₁)^τ ∈ ZIrr` is `htau1_memaχ`.
  have hτdiffZ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj) ∈ ZIrr G := by
    rw [Da.imageFamily.image_eq]
    exact Submodule.sum_mem _ (fun α hα => Da.imageFamily.mem_ZIrr α hα)
  -- Adjoin via the (T8.11 option A) bridge.
  exact retarget_isCoherent_of_extensionImage hyp hconj
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) rfl
    hS₁ χ hdiffsuppχ hdiffasuppχ hχχ hχbarχbar hχχbar hχbarχ hchi1chi1 hχ_S1 hχbar_S1
    (hmemS1 i₁ hi₁) htau1_memaχ hτdiffZ hcrux1 hcrux2 hSgen hgen

open scoped Classical in
/-- **Peterfalvi (5.6)** — quantitative coherence, contrapositive form ("B1").

The converse of the forward adjoining engine `xAdjoinStep`: under the same Dade /
member-family hypotheses, if `S₁ ∪ {χ, χ̄}` fails to be coherent then the degree
sum is bounded by `∑ᵢ (deg i)² ≤ 2 a`.  Writing `a = ψ(1)/χ₁(1)` and
`deg i = χᵢ(1)/χ₁(1)` this is Peterfalvi's non-coherence bound
`∑_{χ∈S₁} χ(1)² ≤ 2 ψ(1) χ₁(1)`, the quantitative input consumed by (6.2) on the
way to the degree bound (6.3)/(6.5).  Proof: contrapose `xAdjoinStep` over its
degree hypothesis `hDeg : 2 a < ∑ᵢ (deg i)²`. -/
theorem coherentDegreeSumBound_of_not_coherent
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → IrreducibleCharacter ↥L) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ i ∈ s, ¬ ClassFunction.IsReal (χmem i : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ).conj - (χmem i : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (hmembarS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ).conj ∈ S₁)
    (hmemconjortho : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χmem i : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (1 : ℂ) else 0)
    {a : ℕ}
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)}))
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))) :
    ∑ i ∈ s, ((deg i : ℝ)) ^ 2 ≤ 2 * (a : ℝ) := by
  by_contra hlt
  push_neg at hlt
  exact hnc ⟨xAdjoinStep hyp hconj hS₁ χ hrealχ hdiffsuppχ hχχ hχbarχbar hχχbar hχbarχ
    hχ_S1 hχbar_S1 s χmem deg i₁ hi₁ hmemreal hmemdiffsupp hmemdegdiffsupp hmemS1 hmembarS1
    hmemconjortho hmemortho hdiffasuppχ htau1_memaχ ha1 hlt hSgen hgen⟩

open scoped Classical in
/-- **Peterfalvi (6.2), step (ii) — the `S(A)` degree-sum (B2 assembled).**
For `H ⊴ G`, `A ⊴ G`, `A ≤ H`, the induced family
`S(A) = {Ind_H^G θ | θ ∈ Irr H, A ⊆ Ker θ, θ ≠ 1}` satisfies
`∑_{χ ∈ S(A)} χ(1)²/‖χ‖² = [G:H]·(|H : A| − 1)`.

This assembles the orbit-counted identity `sum_div_normSq_induce_image_eq`
(`∑ = [G:H]·∑_{θ∈T}θ(1)²`, fibres of `θ ↦ Ind θ` are `G`-conjugacy orbits) with the inflation
degree-sum `sumInflatedDegreeSq_ntrivial` (`∑_{θ∈T}θ(1)² = |H ⧸ A| − 1`, Burnside on `H ⧸ A`).
The index set `T = {θ ∈ Irr H | A ⊆ Ker θ, θ ≠ 1}` is `G`-conjugation-invariant because `A ⊴ G`:
`Ker(θ^g) = g·(Ker θ)·g⁻¹ ⊇ g·A·g⁻¹ = A`.  This is the (6.2) input "step (ii)" that, with the
(5.6) bound B1 and the θ-bound, yields `2|L:C|√|C:D| ≥ |K:A| − 1`. -/
theorem sum_div_normSq_induce_kernelFilter_eq {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {H : Subgroup G} [H.Normal] [Invertible (Nat.card ↥H : ℂ)]
    {A : Subgroup G} [A.Normal] :
    ∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction),
        χ 1 ^ 2 / ClassFunction.inner χ χ
      = (H.index : ℂ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℂ) - 1) := by
  classical
  have hconj : ∀ θ ∈ Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
      (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H),
      ∀ g : G, IrreducibleCharacter.conjBy g θ ∈ Finset.univ.filter
        (fun θ : IrreducibleCharacter ↥H =>
          (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H) := by
    intro θ hθ g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ ⊢
    obtain ⟨hker, hne⟩ := hθ
    refine ⟨?_, ?_⟩
    · -- `A ⊆ Ker(θ^g)`: each `a ∈ A` has `g·a·g⁻¹ ∈ A ⊆ Ker θ`.
      intro a ha
      have hmemA : (⟨g * (a : G) * g⁻¹, ‹H.Normal›.conj_mem (a : G) a.2 g⟩ : ↥H)
          ∈ A.subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        exact ‹A.Normal›.conj_mem (a : G) (Subgroup.mem_subgroupOf.mp ha) g
      have hk := hker hmemA
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel] at hk
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def, conjBy_apply_one,
        IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply, hk,
        OddOrder.Peterfalvi.S03.characterDegree_def]
    · -- `θ^g ≠ 1`: conjugation is injective and fixes the trivial character.
      intro hc
      apply hne
      have h1 : IrreducibleCharacter.conjBy g⁻¹ (IrreducibleCharacter.conjBy g θ) = θ := by
        rw [← IrreducibleCharacter.conjBy_mul, mul_inv_cancel, IrreducibleCharacter.conjBy_one]
      rw [← h1, hc, IrreducibleCharacter.ext_iff]
      ext h
      rw [IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply]
      simp
  rw [sum_div_normSq_induce_image_eq _ hconj]
  congr 1
  exact sumInflatedDegreeSq_ntrivial (N := A.subgroupOf H)

open scoped Classical in
/-- **(T-A2 input) Per-step `xAdjoinStep` data bundle.**

Bundles the `xAdjoinStep` premises for one adjoining step of the X-family chain — the member family
`{χmem i}ᵢ∈ₛ ⊆ S₁` (orthonormal, with the ZIrr-codomain injections `ν χmem i ∈ ZIrr`), the new
character `χ`, the degree data, and the anchor-generation condition `hSgen` — into a single
structure, so the chain fold `xChainCoherent` can take the per-step data as a function of the
(inductively produced) accumulator coherence `hS₁`.  The full `hgen` field is derived in `adjoin`
from `hSgen` and the degree-matched support of `χ - aχ₁`.  The index type `ι` is a field (each step
has its own enumerated family). -/
structure XAdjoinStepInput
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L) where
  hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ)
  hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1
  hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ).conj = 1
  hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0
  hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0
  hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0
  hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0
  ι : Type
  s : Finset ι
  χmem : ι → IrreducibleCharacter ↥L
  deg : ι → ℕ
  i₁ : ι
  hi₁ : i₁ ∈ s
  hmemreal : ∀ i ∈ s, ¬ ClassFunction.IsReal (χmem i : ClassFunction ↥L ℂ)
  hmemdiffsupp : ∀ i ∈ s,
    ((χmem i : ClassFunction ↥L ℂ).conj - (χmem i : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L
  hmemdegdiffsupp : ∀ i ∈ s,
    ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L
  hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁
  hmembarS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ).conj ∈ S₁
  hmemconjortho : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
    (χmem i : ClassFunction ↥L ℂ).conj = 0
  hmemortho : ∀ i ∈ s, ∀ j ∈ s,
    ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
      if i = j then (1 : ℂ) else 0
  a : ℕ
  hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
    (hyp.fullDadeIsometryData hconj)
    ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G
  ha1 : deg i₁ = 1
  hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2
  hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
    (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)})

/-- `xAdjoinStep` applied to a bundled `XAdjoinStepInput`, concluding coherence of
`S₁ ∪ {χ, χ̄}`. -/
noncomputable def XAdjoinStepInput.adjoin
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    {hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L} {hconj : hyp.HConjInvariant}
    {S₁ : Set (ClassFunction ↥L ℂ)}
    {hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L)}
    {χ : IrreducibleCharacter ↥L} (inp : XAdjoinStepInput hyp hconj hS₁ χ) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  have h1notA : (1 : G) ∉ A := by
    intro h
    exact hyp.ne_one h rfl
  have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
    intro h
    exact h1notA (by simpa using h)
  have hdegχ : ((χ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 =
      (inp.a : ℂ) * ((inp.χmem inp.i₁ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := by
    have hzero :
        (((χ : ClassFunction ↥L ℂ) - inp.a •
          (inp.χmem inp.i₁ : ClassFunction ↥L ℂ)) : ClassFunction ↥L ℂ) 1 = 0 := by
      by_contra h
      exact h1A (inp.hdiffasuppχ (ClassFunction.mem_support.mpr h))
    rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ inp.a
      (inp.χmem inp.i₁ : ClassFunction ↥L ℂ), ClassFunction.smul_apply] at hzero
    exact sub_eq_zero.mp hzero
  have hchi1_ne : ((inp.χmem inp.i₁ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 ≠ 0 := by
    obtain ⟨d, hd, hd1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (inp.χmem inp.i₁)
    rw [hd1]
    exact_mod_cast hd.ne'
  have hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - inp.a •
          (inp.χmem inp.i₁ : ClassFunction ↥L ℂ)}) :=
    OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
      (L := ↥L) (S₁ := S₁)
      (A := OddOrder.Peterfalvi.S04.supportInSubgroup A L)
      (χ := (χ : ClassFunction ↥L ℂ)) (chibar := (χ : ClassFunction ↥L ℂ).conj)
      (chi1 := (inp.χmem inp.i₁ : ClassFunction ↥L ℂ)) (a := inp.a)
      inp.hSgen hdegχ (OddOrder.Peterfalvi.S07.irreducibleCharacter_conj_apply_one χ)
      hchi1_ne h1A
  exact xAdjoinStep hyp hconj hS₁ χ inp.hrealχ inp.hdiffsuppχ inp.hχχ inp.hχbarχbar
    inp.hχχbar inp.hχbarχ inp.hχ_S1 inp.hχbar_S1 inp.s inp.χmem inp.deg inp.i₁ inp.hi₁
    inp.hmemreal inp.hmemdiffsupp inp.hmemdegdiffsupp inp.hmemS1 inp.hmembarS1
    inp.hmemconjortho inp.hmemortho inp.hdiffasuppχ inp.htau1_memaχ inp.ha1 inp.hDeg
    inp.hSgen hgen

/-- **(T-A2) The X-family coherence chain fold.**

Folds the per-step adjoining `xAdjoinStep` (via `XAdjoinStepInput.adjoin`) over a degree-monotone
conjugate-pair cover of `X` using the `coherentOfPairChainCover` engine: the base `S₀` is coherent
(`h0`), the `i`-th step adjoins the pair `(pair i) = (χₛ i, (χₛ i)̄)` to the accumulator
`pairUnion S₀ pair i` via `hstep i`, and the cover (`hS₀`/`hpairs`/`hcover`) recovers `X`.

This is the route-B custom fold of the §J.3.6 plan: rather than strengthening `IsCoherent` with a
ZIrr-codomain field (route A, T-A3), the per-step ZIrr-codomain facts are carried as fields of
`XAdjoinStepInput hyp hconj hcoh (χₛ i)`, supplied as a function of the *inductively produced*
accumulator coherence `hcoh`.  The construction of `hstep` from the actual degree-monotone
enumeration of `X` (the `exists_conjugatePairCover` data) is the remaining T-A4 wiring. -/
noncomputable def xChainCoherent
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {X S₀ : Set (ClassFunction ↥L ℂ)}
    (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
    (χs : ℕ → IrreducibleCharacter ↥L)
    (hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ))
    (hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj)
    (hS₀ : S₀ ⊆ X)
    (hpairs : ∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ X)
    (hcover : ∀ χ ∈ X, χ ∈ S₀ ∨ ∃ j, j < N ∧ χ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
    (h0 : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₀ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (hstep : ∀ i, i < N → ∀ (hcoh : OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) S₀ pair i)
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L)),
      XAdjoinStepInput hyp hconj hcoh (χs i)) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      X (OddOrder.Peterfalvi.S04.supportInSubgroup A L) :=
  OddOrder.Peterfalvi.S07.coherentOfPairChainCover pair N hS₀ hpairs hcover h0
    (fun i hi hcoh => by
      rw [OddOrder.Peterfalvi.S07.pairUnion_succ_eq_union_pair (hpair0 i hi) (hpair1 i hi)]
      exact (hstep i hi hcoh).adjoin)

/-- A pair disjoint from the accumulated prefix is orthogonal to that prefix.

This is the set-to-inner-product bridge used by the X-chain per-step builder: once the
conjugate-pair cover has proved `pairSet pair i` is disjoint from `pairUnion S0 pair i`, every
irreducible member of the prefix is distinct from both `χ_i` and `χ_i.conj`, so row
orthogonality gives the two `XAdjoinStepInput` fields `hχ_S1` and `hχbar_S1`. -/
theorem pairCover_orthogonal_to_prefix
    {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]
    {X S₀ : Set (ClassFunction Γ ℂ)} {pair : ℕ → ClassFunction Γ ℂ × ClassFunction Γ ℂ}
    {N i : ℕ} {χ : IrreducibleCharacter Γ}
    (hXirr : ∀ φ ∈ X, IsIrreducibleCharacter φ)
    (hS₀X : S₀ ⊆ X)
    (hpairs : ∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j ⊆ X)
    (hpair0 : (pair i).1 = (χ : ClassFunction Γ ℂ))
    (hpair1 : (pair i).2 = (χ : ClassFunction Γ ℂ).conj)
    (hdisj : Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair i)
      (OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair i))
    (hi : i < N) :
    (∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair i,
        ClassFunction.inner (χ : ClassFunction Γ ℂ) x = 0) ∧
      (∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair i,
        ClassFunction.inner (χ : ClassFunction Γ ℂ).conj x = 0) := by
  classical
  have hprefixX : OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair i ⊆ X := by
    intro x hx
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hx with hbase | ⟨j, hji, hjpair⟩
    · exact hS₀X hbase
    · exact hpairs j (hji.trans hi) hjpair
  have hχpair : (χ : ClassFunction Γ ℂ) ∈ OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0]
  have hχbarpair : (χ : ClassFunction Γ ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair1]
  have hχbarIrr : IsIrreducibleCharacter (χ : ClassFunction Γ ℂ).conj :=
    hXirr _ (hpairs i hi hχbarpair)
  have hdisj_left := Set.disjoint_left.mp hdisj
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxirr : IsIrreducibleCharacter x := hXirr x (hprefixX hx)
    let ψ : IrreducibleCharacter Γ := ⟨x, hxirr⟩
    have hne : χ ≠ ψ := by
      intro hEq
      have hx_eq : x = (χ : ClassFunction Γ ℂ) :=
        (congrArg (fun η : IrreducibleCharacter Γ => (η : ClassFunction Γ ℂ)) hEq).symm
      have hxpair : x ∈ OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair i := by
        simpa [hx_eq] using hχpair
      exact hdisj_left hxpair hx
    simpa [ψ, hne] using irreducibleCharacter_inner_eq_ite χ ψ
  · intro x hx
    have hxirr : IsIrreducibleCharacter x := hXirr x (hprefixX hx)
    let χbar : IrreducibleCharacter Γ := ⟨(χ : ClassFunction Γ ℂ).conj, hχbarIrr⟩
    let ψ : IrreducibleCharacter Γ := ⟨x, hxirr⟩
    have hne : χbar ≠ ψ := by
      intro hEq
      have hx_eq : x = (χ : ClassFunction Γ ℂ).conj :=
        (congrArg (fun η : IrreducibleCharacter Γ => (η : ClassFunction Γ ℂ)) hEq).symm
      have hxpair : x ∈ OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair i := by
        simpa [hx_eq] using hχbarpair
      exact hdisj_left hxpair hx
    simpa [χbar, ψ, hne] using irreducibleCharacter_inner_eq_ite χbar ψ

/-- **Peterfalvi (6.3) degree-bound arithmetic core.**  The real/integer inequality at the heart of
Theorem (6.3) (mmd 04.8 L33): from the (6.2) consequence `b·x − 1 ≤ 2·a·b·√x` (with `a = |L:K|`,
`b = |K:H| ≥ 1`, `x = |H:A| ≥ 1`) one gets `x ≤ 4a² + 1`.

Proof: dividing by `b` and using `b ≥ 1` gives `x − 1 ≤ 2a√x`; squaring (`x − 1 ≥ 0`) gives
`(x − 1)² ≤ 4a²x`, i.e. `x² − (4a² + 2)x + 1 ≤ 0`; for a natural `x`, `x ≥ 4a² + 2` would give
`x² − (4a² + 2)x + 1 = x·(x − (4a² + 2)) + 1 ≥ 1 > 0`, a contradiction.  This is what (6.3) combines
with its hypothesis `|H:H₁| > 4|L:K|² + 1 ≤ x` to reach a contradiction (so `𝒮(M)` is coherent). -/
theorem degreeBound_le_of_sqrt_bound {a b x : ℕ} (hb : 1 ≤ b) (hx : 1 ≤ x)
    (h : (b : ℝ) * x - 1 ≤ 2 * a * b * Real.sqrt x) : x ≤ 4 * a ^ 2 + 1 := by
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hsx : Real.sqrt x ^ 2 = (x : ℝ) := Real.sq_sqrt hx0
  have hsx0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  -- `x − 1 ≤ 2a√x` (divide `h` by `b`, drop `1/b ≤ 1`).
  have key : (x : ℝ) - 1 ≤ 2 * a * Real.sqrt x := by
    have hbx : (b : ℝ) * ((x : ℝ) - 1) ≤ (b : ℝ) * (2 * a * Real.sqrt x) := by
      have e1 : (b : ℝ) * ((x : ℝ) - 1) = (b : ℝ) * x - b := by ring
      have e2 : (b : ℝ) * (2 * a * Real.sqrt x) = 2 * a * b * Real.sqrt x := by ring
      rw [e1, e2]; nlinarith [h, hb1]
    exact le_of_mul_le_mul_left hbx hbpos
  -- `(x − 1)² ≤ (2a√x)² = 4a²x`.
  have hkey0 : (0 : ℝ) ≤ (x : ℝ) - 1 := by linarith
  have hrhs0 : (0 : ℝ) ≤ 2 * a * Real.sqrt x := by positivity
  have hsq : ((x : ℝ) - 1) ^ 2 ≤ 4 * (a : ℝ) ^ 2 * x := by
    have hprod := mul_le_mul key key hkey0 hrhs0
    have hrw : (2 * (a : ℝ) * Real.sqrt x) * (2 * (a : ℝ) * Real.sqrt x) = 4 * (a : ℝ) ^ 2 * x := by
      rw [show (2 * (a : ℝ) * Real.sqrt x) * (2 * (a : ℝ) * Real.sqrt x)
          = 4 * (a : ℝ) ^ 2 * (Real.sqrt x * Real.sqrt x) by ring, Real.mul_self_sqrt hx0]
    rw [hrw] at hprod
    nlinarith [hprod]
  -- `x² − 2x + 1 ≤ 4a²x` gives `x² < (4a²+2)x`, so `x < 4a²+2`, i.e. `x ≤ 4a²+1`.
  have hxlt : (x : ℝ) < 4 * (a : ℝ) ^ 2 + 2 := by
    have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
    nlinarith [hsq, hxpos]
  have hxltN : x < 4 * a ^ 2 + 2 := by exact_mod_cast hxlt
  omega

/-- **Peterfalvi (6.5)(a) chief-factor arithmetic.**  If `c` and `a` are odd, `c ∣ a − 1`, and
`a > 1`, then `a ≥ 2c + 1` (mmd 04.8 L40).  Indeed `a − 1 = c·m` is even (as `a` is odd) and `c` is
odd, so `m` is even and nonzero, hence `m ≥ 2` and `a − 1 = c·m ≥ 2c`.

This is the step in (6.5)(a) ruling out an intermediate normal subgroup `H₁ ⊊ H₂ ⊊ K`: with
`a = |K : H₂|` (odd, dividing the odd `|L|`) and `c = |L : K|`, hypothesis (6.4.c) gives `c ∣ a − 1`,
so `|K : H₂| ≥ 2|L : K| + 1`; likewise `|H₂ : H₁| ≥ 2|L : K| + 1`, whence
`|K : H₁| ≥ (2|L : K| + 1)² > 4|L : K|² + 1`, contradicting the (6.3) bound. -/
theorem two_mul_add_one_le_of_odd_dvd {c a : ℕ} (hc : Odd c) (ha : Odd a) (hdvd : c ∣ a - 1)
    (ha1 : 1 < a) : 2 * c + 1 ≤ a := by
  obtain ⟨m, hm⟩ := hdvd
  have hcodd : c % 2 = 1 := Nat.odd_iff.mp hc
  have haodd : a % 2 = 1 := Nat.odd_iff.mp ha
  have hmeven : m % 2 = 0 := by
    have h1 : (c * m) % 2 = 0 := by
      have h2 : (a - 1) % 2 = 0 := by omega
      rwa [hm] at h2
    rw [Nat.mul_mod, hcodd, one_mul] at h1
    omega
  have hm2 : 2 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hz | hpos
    · rw [hz, mul_zero] at hm; omega
    · omega
  have h2c : 2 * c ≤ c * m := by nlinarith [hm2]
  omega

/-- **Peterfalvi (6.3)** index reduction.  From the degree bound (6.2) applied
with `C = H, D = A`, in index form `|K:H|·|H:A| − 1 ≤ 2·|L:K|·|K:H|·√|H:A|`,
together with `|H:H₁| ≤ |H:A|` (from `A ⊆ H₁`), the index `|H:H₁|` is at most
`4|L:K|² + 1`.  (Peterfalvi states the contrapositive: `|H:H₁| > 4|L:K|² + 1`
forces `S(M)` coherent.)  The `√`-manipulation is `degreeBound_le_of_sqrt_bound`
with `a = |L:K|, b = |K:H|, x = |H:A|`. -/
theorem six_three_HH1_le {LK KH HA HH1 : ℕ} (hKH : 1 ≤ KH) (hHH1le : HH1 ≤ HA)
    (hbound : (KH : ℝ) * (HA : ℝ) - 1 ≤ 2 * (LK : ℝ) * (KH : ℝ) * Real.sqrt (HA : ℝ)) :
    HH1 ≤ 4 * LK ^ 2 + 1 := by
  rcases Nat.eq_zero_or_pos HA with hHA0 | hHA
  · subst hHA0; omega
  · have hx := degreeBound_le_of_sqrt_bound hKH hHA hbound
    omega

/-- Arithmetic core of **Peterfalvi (6.5)(a),(c)**: since
`(2c+1)² = 4c²+4c+1 > 4c²+1` for `c ≥ 1`, an index `n` cannot satisfy both
`(2c+1)² ≤ n` and `n ≤ 4c²+1`. -/
theorem six_five_index_contradiction {LK n : ℕ} (hLK : 1 ≤ LK)
    (hge : (2 * LK + 1) * (2 * LK + 1) ≤ n) (hle : n ≤ 4 * LK ^ 2 + 1) : False := by
  nlinarith [hge, hle, hLK]

/-- **Peterfalvi (6.5)(a)** chief-factor step.  If a normal subgroup `H₂` sits
strictly between `H₁` and `K`, then (6.4.c) + odd order force
`|K:H₂|, |H₂:H₁| ≥ 2|L:K|+1` (via `two_mul_add_one_le_of_odd_dvd`), so
`|K:H₁| = |K:H₂|·|H₂:H₁| ≥ (2|L:K|+1)² > 4|L:K|²+1`, contradicting the (6.3)
bound `|K:H₁| ≤ 4|L:K|²+1`.  Hence `K/H₁` is a chief factor of `L`. -/
theorem six_five_chief_factor_contradiction {LK KH2 H2H1 KH1 : ℕ} (hLK : 1 ≤ LK)
    (hKH2 : 2 * LK + 1 ≤ KH2) (hH2H1 : 2 * LK + 1 ≤ H2H1)
    (hmul : KH1 = KH2 * H2H1) (hKH1le : KH1 ≤ 4 * LK ^ 2 + 1) :
    False :=
  six_five_index_contradiction hLK
    (by rw [hmul]; exact Nat.mul_le_mul hKH2 hH2H1) hKH1le

/-- **Peterfalvi (6.5)(c)** : `|L:K|` does not divide `p − 1`.  If it did then
`p ≥ 2|L:K|+1` (`two_mul_add_one_le_of_odd_dvd`), and since `K/M` is a
non-abelian `p`-group `|K:H₁| ≥ p² ≥ (2|L:K|+1)² > 4|L:K|²+1`, contradicting the
(6.5)(a) bound `|K:H₁| ≤ 4|L:K|²+1`. -/
theorem six_five_c_contradiction {LK p KH1 : ℕ} (hLK : 1 ≤ LK)
    (hpge : 2 * LK + 1 ≤ p) (hp2 : p * p ≤ KH1) (hKH1le : KH1 ≤ 4 * LK ^ 2 + 1) :
    False :=
  six_five_index_contradiction hLK (le_trans (Nat.mul_le_mul hpge hpge) hp2) hKH1le

/-- **Extension of `p`-groups is a `p`-group.**  If a normal subgroup `N` and the quotient `Γ ⧸ N`
are both `p`-groups (and `Γ` is finite), then `Γ` is a `p`-group: `|Γ| = |Γ ⧸ N|·|N| = p^b·p^a`
(Lagrange, `card_eq_card_quotient_mul_card_subgroup`), so `|Γ|` is a `p`-power (`IsPGroup.iff_card`).

A general group-theory brick; used by Peterfalvi (6.5)(b) to assemble "`K/M` is a `p`-group" from
its commutator subgroup `H₁/M` and the chief factor `K/H₁` (a `p`-group). -/
theorem isPGroup_of_quotient_of_subgroup {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ] [Finite Γ]
    {N : Subgroup Γ} [N.Normal] (hN : IsPGroup p ↥N) (hQ : IsPGroup p (Γ ⧸ N)) :
    IsPGroup p Γ := by
  rw [IsPGroup.iff_card] at hN hQ ⊢
  obtain ⟨a, ha⟩ := hN
  obtain ⟨b, hb⟩ := hQ
  exact ⟨b + a, by rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hb, ha, pow_add]⟩

/-- `Abelianization.map` of a surjective homomorphism is surjective. -/
theorem Abelianization.map_surjective {Γ Δ : Type*} [Group Γ] [Group Δ] {f : Γ →* Δ}
    (hf : Function.Surjective f) : Function.Surjective (Abelianization.map f) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | _ b =>
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨Abelianization.of a, Abelianization.map_of f a⟩

/-- A finite `p`-group whose order is coprime to `p` is trivial. -/
theorem subsingleton_of_isPGroup_of_not_dvd {p : ℕ} [Fact p.Prime] {Δ : Type*} [Group Δ] [Finite Δ]
    (hΔ : IsPGroup p Δ) (hnd : ¬ p ∣ Nat.card Δ) : Subsingleton Δ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hΔ
  have hk0 : k = 0 := by
    by_contra hk0
    exact hnd (by rw [hk]; exact dvd_pow_self p hk0)
  rw [hk0, pow_zero] at hk
  exact (Nat.card_eq_one_iff_unique.mp hk).1

/-- **Peterfalvi (6.5)(b) reduction core: a finite nilpotent group with `p`-group abelianization is
a `p`-group.**

Let `P` be the Sylow `p`-subgroup, normal since `Γ` is nilpotent.  The quotient `Q = Γ ⧸ P` has order
`[Γ:P]` coprime to `p`, so `Abelianization Q` — both a `p`-group (a homomorphic image of
`Abelianization Γ`, `Abelianization.map` of `Γ ↠ Q`) and of order dividing `[Γ:P]` — is trivial.
Hence `Q` is perfect (`commutator Q = ⊤`); being nilpotent (a quotient of `Γ`) and hence solvable, it
is therefore trivial (`commutator_lt_top` for a nontrivial solvable group).  So `P = ⊤` and `Γ` is a
`p`-group (`isPGroup_of_quotient_of_subgroup`).

This is the (6.5)(b) step "since `K/M` is nilpotent with commutator `H₁/M` and `K/H₁` a chief factor,
`K/M` is a `p`-group" (mmd 04.8 L45). -/
theorem isPGroup_of_isNilpotent_of_isPGroup_abelianization {p : ℕ} [Fact p.Prime]
    {Γ : Type*} [Group Γ] [Finite Γ] [Group.IsNilpotent Γ]
    (h : IsPGroup p (Abelianization Γ)) : IsPGroup p Γ := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow p Γ) := inferInstance
  haveI hPnormal : (↑P : Subgroup Γ).Normal := by
    have htfae := (isNilpotent_of_finite_tfae (G := Γ)).out 0 3
    exact htfae.mp ‹_› p ‹_› P
  -- `Abelianization Q` is a `p`-group (image of `Abelianization Γ`).
  have hQab_p : IsPGroup p (Abelianization (Γ ⧸ (↑P : Subgroup Γ))) :=
    h.of_surjective _ (Abelianization.map_surjective (QuotientGroup.mk'_surjective _))
  -- ... and trivial: its order divides `Nat.card Q = [Γ:P]`, coprime to `p`.
  have hofsurj : Function.Surjective (Abelianization.of :
      (Γ ⧸ (↑P : Subgroup Γ)) →* Abelianization (Γ ⧸ (↑P : Subgroup Γ))) :=
    fun y => QuotientGroup.induction_on y fun a => ⟨a, rfl⟩
  haveI hQab_triv : Subsingleton (Abelianization (Γ ⧸ (↑P : Subgroup Γ))) :=
    subsingleton_of_isPGroup_of_not_dvd hQab_p
      (fun hp => P.not_dvd_index (hp.trans (Subgroup.card_dvd_of_surjective _ hofsurj)))
  -- `Abelianization Q` trivial ⟹ `commutator Q = ⊤` ⟹ (nilpotent ⟹ solvable) `Q` trivial.
  haveI hQ_triv : Subsingleton (Γ ⧸ (↑P : Subgroup Γ)) := by
    rcases subsingleton_or_nontrivial (Γ ⧸ (↑P : Subgroup Γ)) with hs | hns
    · exact hs
    · exfalso
      haveI := hns
      have hlt : commutator (Γ ⧸ (↑P : Subgroup Γ)) < ⊤ :=
        IsSolvable.commutator_lt_top_of_nontrivial (G := Γ ⧸ (↑P : Subgroup Γ))
      refine absurd ?_ hlt.ne
      rw [← Subgroup.index_eq_one]
      exact @Nat.card_of_subsingleton (Abelianization (Γ ⧸ (↑P : Subgroup Γ))) 1 hQab_triv
  -- `Q` trivial ⟹ `Γ` is a `p`-group (Sylow `P` is `p`, quotient `Q` trivially `p`).
  refine isPGroup_of_quotient_of_subgroup P.isPGroup' ?_
  rw [IsPGroup.iff_card]
  exact ⟨0, by rw [pow_zero]; exact @Nat.card_of_subsingleton (Γ ⧸ (↑P : Subgroup Γ)) 1 hQ_triv⟩

/-- **Group-theory core of Peterfalvi (6.5)(a),(b): a Frobenius-acted abelian section obeying the
(6.3) index bound is a `p`-group.**

Let a finite group `R` act on a finite abelian group `A` by automorphisms, *fixed-point-freely*
(`IsFrobeniusAction R A`: no nonidentity `r ∈ R` fixes a nonidentity `a ∈ A`).  If `|A|` and `|R|`
are odd and `|A| ≤ 4|R|² + 1`, then `A` is a `p`-group for some prime `p`.

This is the abstract content of Peterfalvi (6.5).  In the Sibley setting `A = K/H₁` is the
abelianization section and `R = L/K` is the Frobenius complement; (6.5)(a) says `K/H₁` is a chief
factor.  Here the chief-factor argument is run through the `p`-primary component: if `A` had a prime
divisor `p` whose Sylow subgroup `P` were proper (i.e. `A` were not a `p`-group), then `P`
(characteristic in the abelian `A`, hence `R`-invariant) and the quotient index `|A : P|` would both
be nontrivial, odd, and `≡ 1 (mod |R|)` — the first two by Frobenius `card_modEq_one` applied to the
whole action and the restricted action on `P` (`IsFrobeniusAction.subgroup`), the index by the
arithmetic `|A| = |A:P|·|P|`, `|A| ≡ |P| ≡ 1`.  Oddness then forces `|P|, |A:P| ≥ 2|R| + 1`
(`two_mul_add_one_le_of_odd_dvd`), so `|A| = |A:P|·|P| ≥ (2|R|+1)² > 4|R|² + 1`, contradicting the
bound (`six_five_chief_factor_contradiction`).

The `|A| ≤ 4|R|² + 1` bound is the single character-theoretic input ((6.2)/(6.3); in the Sibley
setup supplied by `theta_degree_le_index_mul_sqrt_index`).  Everything else is discharged here. -/
theorem isPGroup_of_card_le_of_isFrobeniusAction {A R : Type*} [CommGroup A] [Finite A]
    [Group R] [Finite R] [MulDistribMulAction R A]
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusAction R A)
    (hAodd : Odd (Nat.card A)) (hRodd : Odd (Nat.card R))
    (hbound : Nat.card A ≤ 4 * Nat.card R ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p A := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype R := Fintype.ofFinite R
  by_contra hcon
  -- `A` is nontrivial: a trivial group is a `p`-group for every prime.
  rcases eq_or_ne (Nat.card A) 1 with hA1 | hA1
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hcon ⟨2, Nat.prime_two, IsPGroup.iff_card.mpr ⟨0, by rw [pow_zero, hA1]⟩⟩
  -- Otherwise take a prime divisor `p` of `|A|` and its Sylow `p`-subgroup `P`.
  obtain ⟨p, hp, hpdvd⟩ := (Nat.card A).exists_prime_and_dvd hA1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p A) := inferInstance
  -- `|P| > 1` because `p ∣ |P|`.
  have hpP : p ∣ Nat.card (P : Subgroup A) := P.dvd_card_of_dvd_card hpdvd
  have hcardP : 1 < Nat.card (P : Subgroup A) :=
    lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd Nat.card_pos hpP)
  -- `P` is normal (abelian ambient), hence characteristic.
  have hPnormal : (P : Subgroup A).Normal :=
    ⟨fun n hn g => by
      have heq : g * n * g⁻¹ = n := by rw [mul_comm g n, mul_assoc, mul_inv_cancel, mul_one]
      rw [heq]; exact hn⟩
  have hPchar : (P : Subgroup A).Characteristic := P.characteristic_of_normal hPnormal
  -- `R` acts by automorphisms, which fix the characteristic `P` setwise: `P` is `R`-invariant.
  have hinv : ∀ r : R, ∀ m ∈ (P : Subgroup A), r • m ∈ (P : Subgroup A) := by
    intro r m hm
    have hmap : (P : Subgroup A).map (MulDistribMulAction.toMulAut R A r).toMonoidHom
        = (P : Subgroup A) :=
      Subgroup.characteristic_iff_map_eq.mp hPchar (MulDistribMulAction.toMulAut R A r)
    have hmem : (MulDistribMulAction.toMulAut R A r).toMonoidHom m ∈ (P : Subgroup A) := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  -- `A` not a `p`-group ⟹ `P ≠ ⊤` ⟹ `|A : P| > 1`.
  have hindex : 1 < (P : Subgroup A).index := by
    by_contra hle
    have h : (P : Subgroup A).index ≤ 1 := Nat.not_lt.mp hle
    have hidxpos : 0 < (P : Subgroup A).index := by
      have hmc := Subgroup.index_mul_card (P : Subgroup A)
      rcases Nat.eq_zero_or_pos (P : Subgroup A).index with h0 | h0
      · rw [h0, zero_mul] at hmc; exact absurd hmc.symm Nat.card_pos.ne'
      · exact h0
    have hidx1 : (P : Subgroup A).index = 1 := by omega
    have hPtop : (P : Subgroup A) = ⊤ := Subgroup.index_eq_one.mp hidx1
    have hcardeq : Nat.card (P : Subgroup A) = Nat.card A := by
      rw [hPtop]; exact Nat.card_congr (Subgroup.topEquiv).toEquiv
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    exact hcon ⟨p, hp, IsPGroup.iff_card.mpr ⟨n, by rw [← hcardeq, hn]⟩⟩
  -- Frobenius `card ≡ 1 (mod |R|)` for the whole action and the restricted action on `P`.
  haveI : Fintype (P : Subgroup A) := Fintype.ofFinite _
  have hAmod : Nat.card A ≡ 1 [MOD Nat.card R] := by
    simpa only [Fintype.card_eq_nat_card] using hFrob.card_modEq_one
  letI instP : MulDistribMulAction R (P : Subgroup A) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantSubgroupMulDistribMulAction
      (P : Subgroup A) hinv
  have hFrobP : @OddOrder.Isaacs.Ch06.IsFrobeniusAction R (P : Subgroup A) _ _ instP :=
    hFrob.subgroup (P : Subgroup A) hinv
  have hPmod : Nat.card (P : Subgroup A) ≡ 1 [MOD Nat.card R] := by
    simpa only [Fintype.card_eq_nat_card] using hFrobP.card_modEq_one
  -- `|R| ∣ |P| - 1` and (via `|A| = |A:P|·|P|`) `|R| ∣ |A:P| - 1`.
  have hRdvdP : Nat.card R ∣ Nat.card (P : Subgroup A) - 1 :=
    (Nat.modEq_iff_dvd' (by omega)).mp hPmod.symm
  have hmul : (P : Subgroup A).index * Nat.card (P : Subgroup A) = Nat.card A :=
    Subgroup.index_mul_card _
  have hidxmod : (P : Subgroup A).index ≡ 1 [MOD Nat.card R] := by
    have h1 : (P : Subgroup A).index * Nat.card (P : Subgroup A)
        ≡ (P : Subgroup A).index * 1 [MOD Nat.card R] := Nat.ModEq.mul_left _ hPmod
    rw [mul_one, hmul] at h1
    exact h1.symm.trans hAmod
  have hRdvdidx : Nat.card R ∣ (P : Subgroup A).index - 1 :=
    (Nat.modEq_iff_dvd' (by omega)).mp hidxmod.symm
  -- Oddness of both factors (they multiply to the odd `|A|`).
  have hAodd' : Odd ((P : Subgroup A).index * Nat.card (P : Subgroup A)) := by
    rw [hmul]; exact hAodd
  obtain ⟨hidxodd, hcardPodd⟩ := Nat.odd_mul.mp hAodd'
  -- Each factor is `≥ 2|R| + 1`; their product exceeds the bound — contradiction.
  have hbP : 2 * Nat.card R + 1 ≤ Nat.card (P : Subgroup A) :=
    two_mul_add_one_le_of_odd_dvd hRodd hcardPodd hRdvdP hcardP
  have hbidx : 2 * Nat.card R + 1 ≤ (P : Subgroup A).index :=
    two_mul_add_one_le_of_odd_dvd hRodd hidxodd hRdvdidx hindex
  exact six_five_chief_factor_contradiction Nat.card_pos hbidx hbP hmul.symm hbound

/-- **Peterfalvi (6.5)(b) reduction: `H` is a `p`-group.**  Assemble the chief-factor core
`isPGroup_of_card_le_of_isFrobeniusAction` (the abelianization `Abelianization H` is a `p`-group)
with `isPGroup_of_isNilpotent_of_isPGroup_abelianization` (a nilpotent group with `p`-group
abelianization is a `p`-group).

Let `H` be a finite nilpotent group whose abelianization `Abelianization H` carries a
fixed-point-free action of a finite group `R` (in the Sibley setting `R = L/H` is the Frobenius
complement acting on `H/H'` by conjugation), with `|Abelianization H|` and `|R|` odd and
`|Abelianization H| ≤ 4|R|² + 1`.  Then `H` is a `p`-group for some prime `p`.

This is the group-theory conclusion of Peterfalvi (6.5) ("we may assume `H` is a non-abelian
`p`-group") in the form the (6.8) capstone consumes; the `≤ 4|R|² + 1` bound is the single
character-theoretic input ((6.2)/(6.3)), and the fixed-point-free `R`-action on `Abelianization H`
is supplied from the Frobenius alternative (6.8)(c1) / (6.4.c). -/
theorem isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization
    {H : Type*} [Group H] [Finite H] [Group.IsNilpotent H]
    {R : Type*} [Group R] [Finite R] [MulDistribMulAction R (Abelianization H)]
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusAction R (Abelianization H))
    (hHodd : Odd (Nat.card (Abelianization H))) (hRodd : Odd (Nat.card R))
    (hbound : Nat.card (Abelianization H) ≤ 4 * Nat.card R ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p H := by
  obtain ⟨p, hp, hPab⟩ :=
    isPGroup_of_card_le_of_isFrobeniusAction hFrob hHodd hRodd hbound
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, isPGroup_of_isNilpotent_of_isPGroup_abelianization hPab⟩

/-- **Peterfalvi (6.5)(b) reduction in the Frobenius case (6.8)(c1): the kernel is a `p`-group.**
If `G = N ⋊ A` is a Frobenius group with nilpotent kernel `N`, `|Abelianization N|` and `|A|` are
odd, and `|Abelianization N| ≤ 4|A|² + 1`, then `N` is a `p`-group for some prime `p`.

This is `isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization` with the fixed-point-free
`A`-action on `Abelianization N` supplied directly from the Frobenius group: `A` acts
fixed-point-freely on `N` by conjugation (`toFrobeniusAction`), and since `⁅N,N⁆` is characteristic
in `N` (hence `A`-invariant), the action descends fixed-point-freely to the abelianization
`N / ⁅N,N⁆` (`IsFrobeniusAction.quotient`).  In the (6.8) capstone this is the Frobenius alternative
`hyp.cases.inl : IsFrobeniusGroup ↥L H W₁` (with `N = H`, `A = W₁`); the only remaining input is the
`≤ 4|W₁|² + 1` bound from the character theory ((6.2)/(6.3)). -/
theorem isPGroup_of_isFrobeniusGroup_of_card_le {G : Type*} [Group G] [Finite G]
    {N A : Subgroup G} [Group.IsNilpotent ↥N]
    (h : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G N A)
    (hHodd : Odd (Nat.card (Abelianization ↥N))) (hAodd : Odd (Nat.card ↥A))
    (hbound : Nat.card (Abelianization ↥N) ≤ 4 * Nat.card ↥A ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p ↥N := by
  letI : N.Normal := h.isNormal
  letI actN : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp A.subtype)
  have hFrobN : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥A ↥N := h.toFrobeniusAction
  -- `⁅N,N⁆` is characteristic in `N`, hence preserved by the automorphism `A`-action.
  have hM : ∀ a : ↥A, ∀ m ∈ commutator ↥N, a • m ∈ commutator ↥N := by
    intro a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (commutator ↥N).Characteristic) (MulDistribMulAction.toMulAut ↥A ↥N a)
    have hmem : (MulDistribMulAction.toMulAut ↥A ↥N a).toMonoidHom m ∈ commutator ↥N := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  -- The fixed-point-free action descends to the abelianization quotient.
  letI actAb : MulDistribMulAction ↥A (Abelianization ↥N) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantQuotientMulDistribMulAction (commutator ↥N) hM
  have hFrobAb : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥A (Abelianization ↥N) :=
    hFrobN.quotient (commutator ↥N) hM
  exact isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization hFrobAb hHodd hAodd hbound

/-- **Peterfalvi (6.5)(b) reduction in the certain-type case (6.8)(c2): the kernel is a `p`-group.**
If a finite group `W` acts on a finite nilpotent group `H` with `(|W|, |H|) = 1`, such that for
every nonidentity `w ∈ W` the `w`-fixed points of `H` lie in `⁅H,H⁆` (the certain-type centralizer
condition `C_H(x) = W₂ ⊆ ⁅H,H⁆`), and `|Abelianization H|`, `|W|` are odd with
`|Abelianization H| ≤ 4|W|² + 1`, then `H` is a `p`-group for some prime `p`.

This is the (6.8)(c2) analogue of `isPGroup_of_isFrobeniusGroup_of_card_le`.  Here `W` does *not*
act fixed-point-freely on `H` (the fixed points `C_H(x) = W₂` are nontrivial), but since
`W₂ ⊆ ⁅H,H⁆` the action descends fixed-point-freely to `Abelianization H` (`IsFrobeniusAction`'s
`quotient_of_fixedPoints_le`, via the coprime fixed-point lifting Isaacs Cor 3.28); then the
(6.5)(b) reduction `isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization` applies.  In the
(6.8) capstone the fixed-points hypothesis is discharged from the certain-type fields
`centralizer_W2` (`C_L(x) ⊓ H = W₂`) and `W₂ ⊆ ⁅H,H⁆`, and the coprimality from the Hall datum
`gcd(|H|, |W₁|) = 1`. -/
theorem isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator {H W : Type*}
    [Group H] [Finite H] [Group.IsNilpotent H] [Group W] [Finite W] [MulDistribMulAction W H]
    (hCop : Nat.Coprime (Nat.card W) (Nat.card H))
    (hfix : ∀ w : W, w ≠ 1 → ∀ x : H, w • x = x → x ∈ commutator H)
    (hHodd : Odd (Nat.card (Abelianization H))) (hWodd : Odd (Nat.card W))
    (hbound : Nat.card (Abelianization H) ≤ 4 * Nat.card W ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p H := by
  have hMinv : ∀ a : W, ∀ m ∈ commutator H, a • m ∈ commutator H := by
    intro a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (commutator H).Characteristic) (MulDistribMulAction.toMulAut W H a)
    have hmem : (MulDistribMulAction.toMulAut W H a).toMonoidHom m ∈ commutator H := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  letI actAb : MulDistribMulAction W (Abelianization H) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantQuotientMulDistribMulAction (commutator H) hMinv
  have hFrobAb : OddOrder.Isaacs.Ch06.IsFrobeniusAction W (Abelianization H) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.quotient_of_fixedPoints_le hCop (commutator H) hMinv hfix
  exact isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization hFrobAb hHodd hWodd hbound

/-- A finite group with non-trivial abelianization carries a non-trivial linear character
`Γ →* ℂˣ`. Equivalently (via `IsSolvable.commutator_lt_top_of_nontrivial`) every non-trivial
finite solvable group has one.

This is the existence ingredient feeding **Peterfalvi (6.2)**: the section `K/A` (solvable and
non-trivial, since `A ⊊ K`) carries an irreducible character of degree `1`, which is what makes
`S(A)` non-empty so the degree bound `2|L:C|√|C:D| ≥ |K:A| − 1` has content. The proof reduces to
the abelianization `Γ ⧸ ⁅Γ,Γ⁆` (non-trivial exactly when `⁅Γ,Γ⁆ ≠ ⊤`) and uses that `ℂ` is
separably closed of characteristic zero, hence has enough roots of unity
(`IsSepClosed.hasEnoughRootsOfUnity`, instantiated at `n = exponent` via the supplied `NeZero`). -/
theorem exists_monoidHom_units_ne_one_of_commutator_ne_top {Γ : Type*} [Group Γ] [Finite Γ]
    (h : commutator Γ ≠ ⊤) : ∃ χ : Γ →* ℂˣ, χ ≠ 1 := by
  -- `Abelianization Γ = Γ ⧸ ⁅Γ,Γ⁆` is non-trivial precisely because `⁅Γ,Γ⁆ ≠ ⊤`.
  haveI : Nontrivial (Abelianization Γ) := by
    by_contra hns
    rw [not_nontrivial_iff_subsingleton] at hns
    exact h (by
      rw [← Subgroup.index_eq_one]
      exact @Nat.card_of_subsingleton (Abelianization Γ) 1 hns)
  obtain ⟨a, ha⟩ := exists_ne (1 : Abelianization Γ)
  -- `ℂ` separably closed + characteristic zero ⟹ enough roots of unity at `n = exponent`.
  haveI : NeZero ((Monoid.exponent (Abelianization Γ) : ℂ)) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨φ, hφ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Abelianization Γ) ℂ ha
  -- Pull `φ` back along the surjection `Abelianization.of`; non-triviality transports.
  refine ⟨φ.comp Abelianization.of, fun hcon => hφ ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g : Γ, Abelianization.of g = a := QuotientGroup.mk_surjective a
  simpa using DFunLike.congr_fun hcon g

/-- A finite group with non-trivial abelianization carries a non-trivial **degree-one irreducible
character**. This is the `IrreducibleCharacter`-level form of the **Peterfalvi (6.2)** existence
ingredient: bridging `exists_monoidHom_units_ne_one_of_commutator_ne_top` through the linear
character functor `linearIrreducibleCharacter`. Applied to the section `K/A` (non-trivial solvable)
and inflated to `K`, it furnishes a non-trivial `θ ∈ Irr K` with `A ⊆ ker θ`, i.e. a member of
`S(A)`. -/
theorem exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top {Γ : Type*}
    [Group Γ] [Finite Γ] (h : commutator Γ ≠ ⊤) :
    ∃ χ : IrreducibleCharacter Γ,
      χ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ ∧
      (χ : ClassFunction Γ ℂ) (1 : Γ) = 1 := by
  obtain ⟨φ, hφ⟩ := exists_monoidHom_units_ne_one_of_commutator_ne_top h
  refine ⟨OddOrder.RepresentationTheory.linearIrreducibleCharacter φ, ?_,
    OddOrder.RepresentationTheory.linearIrreducibleCharacter_apply_one φ⟩
  rw [Ne, OddOrder.RepresentationTheory.linearIrreducibleCharacter_eq_trivial_iff]
  exact hφ

/-- **Peterfalvi (6.2): `S(A)` is non-empty when `K/A` is non-trivial.**  If `A ◁ K` is normal with
`K/A` of non-trivial abelianization (in particular when `K/A` is a non-trivial solvable group, e.g.
`A ⊊ K` with `K` solvable), then `K` carries a non-trivial irreducible character `θ` of degree `1`
with `A ⊆ ker θ` — i.e. a member of `S(A) = {Ind_K^L θ | θ ∈ Irr K, A ⊆ ker θ, θ ≠ 1}`.

This is the concrete, `(K, A)`-level existence ingredient for the (6.2) degree bound: it inflates
the degree-one character produced on the section `K/A`
(`exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top`) back up to `K` via
`OddOrder.RepresentationTheory.inflate`, transporting non-triviality
(`inflate_eq_trivial_iff`), the kernel containment (`subset_characterKernel_inflate`) and the
degree (`inflate_apply_one`). -/
theorem exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top {K : Type*}
    [Group K] [Finite K] (N : Subgroup K) [N.Normal] (h : commutator (K ⧸ N) ≠ ⊤) :
    ∃ θ : IrreducibleCharacter K,
      θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter K ∧
      (N : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction K ℂ) ∧
      (θ : ClassFunction K ℂ) (1 : K) = 1 := by
  obtain ⟨χbar, hne, hdeg⟩ :=
    exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top h
  refine ⟨OddOrder.RepresentationTheory.inflate N χbar, ?_,
    OddOrder.RepresentationTheory.subset_characterKernel_inflate N χbar, ?_⟩
  · rw [Ne, OddOrder.RepresentationTheory.inflate_eq_trivial_iff]; exact hne
  · rw [OddOrder.RepresentationTheory.inflate_apply_one]; exact hdeg

/-- **Peterfalvi (6.8): Dade-based carrier** (T1, faithful replacement of `SibleySetup`).

The legacy `SibleySetup` carried an opaque `coherence.tau` with a *global* `IsIntegralIsometry`,
which does not exist in Feit–Thompson (`dim CF(L) > dim CF(G)`); its `CoherenceTarget` was
therefore undischargeable. This carrier instead packages the genuine §4 Dade datum
`dade : S04.Hypothesis G H^# L`, so the coherence map `tau` is the **real**
`dadeIntegralCharacterMap` and `CoherenceTarget` is `IsCoherent` for that map — exactly the shape
the §7 coherence engine produces (`coherentUnion_of_glued`, `coherentEqualDegree_fromDade`, …),
realizing "τ coincides with the Dade isometry relative to (A,L,G)" (mmd 04.8 L150).

**Migration status (T1, `notes/peterfalvi/s08_6_8_assembly_plan.md`)**: this commit lands the
re-parametrization (`L : Subgroup G`, source type `↥L`) and the real-`tau` `CoherenceTarget`. The
remaining (6.8) hypotheses — `S = {Ind_H^L θ | θ ≠ 1}`, the split `L = H ⋊ W₁`, `H` nilpotent, and
the case (c1)/(c2) disjunction (`S06.CertainTypeHypothesis`) — are added next, after which
`sibleySetup_is_coherent` is restated against this carrier and the legacy `SibleySetup` removed. -/
structure SibleyDadeHypothesis (G : Type*) [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (L : Subgroup G) [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    (H : Subgroup ↥L) [Invertible (Nat.card ↥H : ℂ)] where
  /-- A complement-side subgroup `W₁`; the split `L = H ⋊ W₁` is added in the next migration step. -/
  W1 : Subgroup ↥L
  H_ne_bot : H ≠ ⊥
  H_normal : H.Normal
  /-- `H` is nilpotent (Peterfalvi (6.8.a)). -/
  H_nilpotent : Group.IsNilpotent ↥H
  /-- `L = H ⋊ W₁`: `W₁` is a complement to the normal `H` (Peterfalvi (6.8.a)). -/
  split : Subgroup.IsComplement' H W1
  W1_nontrivial : W1 ≠ ⊥
  card_L_odd : Odd (Nat.card L)
  /-- `H^#` is a TI-subset of `G` relative to `L` (corrected ambient: TI in `G`, not in `↥L`). -/
  H_sharp_ti : OddOrder.GroupTheory.IsTISubset (sharpImage H) L
  /-- The §4 Dade datum on `A = H^#`; its Dade isometry *is* `tau`. -/
  dade : OddOrder.Peterfalvi.S04.Hypothesis G (sharpImage H) L
  hconj : dade.HConjInvariant
  /-- In the TI situation ((6.8.a): `H^#` is a TI-subset of `G` with normalizer `L`), the §4 Dade
  datum's local subgroups are trivial, `dade.H a = ⊥` — i.e. `dade` is the Dade map of the
  TI-subset construction (`S04.of_isTISubset`, whose `H a = ⊥`, S04:308).  This faithful (6.8.a)
  fact makes the Dade map agree with `Ind_L^G` on the supported lattice, yielding the (2.7)
  reciprocity `⟨α^τ, ψ⟩_G = ⟨α, Res_L^G ψ⟩_L` (`inner_tau_eq_inner_restrict`), the gateway to the
  (6.8.1) `Res_L(η₁^{τ₁})` decomposition. -/
  dade_H_eq_bot : ∀ a : {a : G // a ∈ sharpImage H}, dade.H a = ⊥
  /-- The base character set `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` (Peterfalvi (6.8.b)). -/
  S : Set (ClassFunction ↥L ℂ)
  /-- `S` is exactly the set of characters induced from nontrivial irreducibles of `H`. -/
  S_eq : S = {φ : ClassFunction ↥L ℂ | ∃ θ : IrreducibleCharacter ↥H,
    θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
    φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ)}
  /-- Peterfalvi (6.8)(c): the configuration is one of two cases.

  * **(c1)** `L` is a Frobenius group with kernel `H` and complement `W₁`.
  * **(c2)** Hypothesis (4.6) holds — encoded **faithfully** by a `S06.Hypothesis46` (the *full*
    (4.6): the (4.2) structure plus the ambient (3.1) TI-cyclic `tic` for `(G, W)` (4.6.b), the
    covering `A_covers` (4.6.d), and the enlarged Dade datum `dade0`/`tau` on `A₀ = A ∪ Vᴸ`) on
    the *same* Dade datum (`h46.dade = dade`) whose kernel is `K = H` — with `w₂ = |W₂|` prime,
    `W₂ ⊆ [H,H]`, and the Hall coprimality `gcd(|H|, |W₁|) = 1` (Peterfalvi (4.2.a): `W₁` is a
    cyclic *Hall* subgroup of `L = H ⋊ W₁`, so its order is coprime to `|H| = [L : W₁]`).  This
    coprimality is the input to Isaacs (3.28) that lifts a `W₁`-fixed coset of `H/[H,H]` to a
    `W₁`-fixed element of `H`.

  The (4.6)↔(6.8) renaming sets the (4.6)-kernel `K` to the (6.8) `H` (hence `h46.K = H`), and the
  (4.2)/(6.8) complement is shared (`h46.W1 = W1`, both giving `L = H ⋊ W₁`).

  **Faithfulness note (2026-06-13):** the textbook (6.8)(c2) literally reads "Hypothesis (4.6)
  holds" (mmd 04.8 L146), and (4.6) (mmd 04.6 L53-63) includes (4.6.b) "G and W satisfy (3.1)" —
  i.e. the ambient TI-cyclic on `W − W₂`.  This is *not* derivable from a bare
  `CertainTypeHypothesis` (which carries only the (4.2) structure on `↥L` plus the §4 Dade datum on
  `A`): TI in the ambient `G` quantifies over all of `G`, not just `↥L`, so it cannot be lifted from
  the (4.3.a) TI in `↥L`.  The earlier `cases` encoding used the *weaker* `CertainTypeHypothesis`,
  which made the c2 X-coherence un-constructible (the impossible "build the ambient TI from
  nothing").  Strengthening `cases` to `Hypothesis46` restores faithfulness and moves the
  (4.6)-construction obligation to the `SibleyDadeHypothesis` *producer* (the §9 (7.10) application,
  where the maximal-subgroup structure supplies it), exactly as the textbook does. -/
  cases :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H W1 ∨
    ∃ h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L,
      h46.dade = dade ∧ h46.K = H ∧ h46.W1 = W1 ∧
        (Nat.card h46.W2).Prime ∧ h46.W2 ≤ ⁅H, H⁆ ∧
        Nat.Coprime (Nat.card ↥H) (Nat.card W1)

/-- **(T7-c2 case A, brick ①)** A multiplicative `ℂ`-valued function `f` (e.g. a linear character)
that is *invariant* under a fixed-point-free endomorphism `σ` is identically `1`.  Indeed
`z ↦ z·(σ z)⁻¹` is surjective (`MonoidHom.FixedPointFree.commutatorMap_surjective`), and
`f (z₀·(σ z₀)⁻¹) = f z₀ · f (σ z₀)⁻¹ = f z₀ · (f z₀)⁻¹ = 1` using `f ∘ σ = f`. -/
theorem eq_one_of_fixedPointFree_invariant {Z : Type*} [Group Z] [Finite Z]
    {F : Type*} [FunLike F Z Z] [MonoidHomClass F Z Z] {σ : F}
    (hσ : MonoidHom.FixedPointFree σ)
    {f : Z → ℂ} (hf_mul : ∀ a b, f (a * b) = f a * f b) (hf_one : f 1 = 1)
    (hinv : ∀ z, f (σ z) = f z) (z : Z) : f z = 1 := by
  have hne : ∀ a : Z, f a ≠ 0 := fun a ha => one_ne_zero
    (show (1 : ℂ) = 0 by rw [← hf_one, ← mul_inv_cancel a, hf_mul, ha, zero_mul])
  have hf_inv : ∀ a : Z, f a⁻¹ = (f a)⁻¹ := fun a =>
    eq_inv_of_mul_eq_one_right (by rw [← hf_mul, mul_inv_cancel, hf_one])
  obtain ⟨z₀, hz₀⟩ := hσ.commutatorMap_surjective z
  rw [MonoidHom.commutatorMap_apply, div_eq_mul_inv] at hz₀
  calc f z = f (z₀ * (σ z₀)⁻¹) := by rw [hz₀]
    _ = f z₀ * f (σ z₀)⁻¹ := hf_mul _ _
    _ = f z₀ * (f (σ z₀))⁻¹ := by rw [hf_inv]
    _ = f z₀ * (f z₀)⁻¹ := by rw [hinv]
    _ = 1 := mul_inv_cancel₀ (hne z₀)

/-- A subgroup contained in a **prime-order** subgroup is either trivial or the whole subgroup.

Group-theoretic core of the math-case (A)/(B) dichotomy of Peterfalvi (6.8): with `|W₂|` prime
and `Z(H) ⊓ W₂ ≤ W₂`, the intersection is `⊥` (case A, `Z(H) ∩ W₂ = 1`) or `W₂` (case B, forcing
`W₂ ⊆ Z(H)`). -/
theorem eq_bot_or_eq_of_le_of_card_prime {Γ : Type*} [Group Γ] {K W : Subgroup Γ}
    [Finite W] (hle : K ≤ W) (hp : (Nat.card W).Prime) : K = ⊥ ∨ K = W := by
  rcases (Nat.dvd_prime hp).mp (Subgroup.card_dvd_of_le hle) with h1 | hcard
  · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h1)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hle hcard.ge)

/-- **(T8.11p0) natural degree witnesses for one X-adjoin member family.**

This packages the positive natural degree of the new character, the anchor, and every member of a
finite accumulator family, together with the member square-sum `D`.  The hypothesis `i₁ ∈ s`
ensures `D` is positive. -/
theorem exists_natDegreeData_for_xAdjoinMemberFamily
    {G : Type*} [Group G] {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {i₁ : ι} (hi₁ : i₁ ∈ s) :
    ∃ dχ d₁ D : ℕ, ∃ dmem : ι → ℕ,
      (χ : ClassFunction G ℂ) 1 = (dχ : ℂ) ∧
      (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ) ∧
      (∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ)) ∧
      (∑ i ∈ s, dmem i * dmem i = D) ∧
      0 < d₁ ∧ 0 < D := by
  classical
  obtain ⟨dχ, _hdχpos, hχone⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  obtain ⟨d₁, hd₁pos, hχ₁one⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ₁
  let dmem : ι → ℕ := fun i =>
    (irreducibleCharacter_apply_one_eq_pos_natCast (χmem i)).choose
  have hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ) := by
    intro i _hi
    exact (irreducibleCharacter_apply_one_eq_pos_natCast (χmem i)).choose_spec.2
  let D : ℕ := ∑ i ∈ s, dmem i * dmem i
  have hDsum : ∑ i ∈ s, dmem i * dmem i = D := rfl
  have hDpos : 0 < D := by
    have hpos_i₁ : 0 < dmem i₁ :=
      (irreducibleCharacter_apply_one_eq_pos_natCast (χmem i₁)).choose_spec.1
    have hterm_pos : 0 < dmem i₁ * dmem i₁ := Nat.mul_pos hpos_i₁ hpos_i₁
    have hsum_pos : 0 < ∑ i ∈ s, dmem i * dmem i := by
      exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨i₁, hi₁, hterm_pos⟩
    simpa [D] using hsum_pos
  exact ⟨dχ, d₁, D, dmem, hχone, hχ₁one, hmemone, hDsum, hd₁pos, hDpos⟩

/-- A natural witness for the degree of an irreducible character is positive. -/
theorem natDegree_pos_of_irreducibleCharacter_apply_one_eq
    {G : Type*} [Group G] {χ : IrreducibleCharacter G} {d : ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (d : ℂ)) : 0 < d := by
  obtain ⟨e, hepos, heq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  have hde : d = e := Nat.cast_injective (hχone.symm.trans heq)
  rwa [hde]

/-- A common index in a factorization of an irreducible character degree is positive. -/
theorem commonIndex_pos_of_natDegree_factor
    {G : Type*} [Group G] {χ : IrreducibleCharacter G} {idx d θ : ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (d : ℂ)) (hd : d = idx * θ) :
    0 < idx := by
  have hdpos : 0 < d := natDegree_pos_of_irreducibleCharacter_apply_one_eq hχone
  by_contra hidx
  have hidx0 : idx = 0 := Nat.eq_zero_of_not_pos hidx
  have hd0 : d = 0 := by simp [hd, hidx0]
  omega

/-- A common index coprime to `p` is coprime to any residual degree that is a power of `p`. -/
theorem coprime_commonIndex_primePower
    {idx p θ m : ℕ} (hidx_p : Nat.Coprime idx p) (hθ : θ = p ^ m) :
    Nat.Coprime idx θ := by
  rw [hθ]
  exact hidx_p.pow_right m

/-- A member-family square sum is positive once it contains one irreducible character. -/
theorem natDegreeSquareSum_pos_of_memberFamily
    {G : Type*} [Group G] {ι : Type*} {s : Finset ι}
    {χmem : ι → IrreducibleCharacter G} {i₁ : ι} {D : ℕ} {dmem : ι → ℕ}
    (hi₁ : i₁ ∈ s)
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D) :
    0 < D := by
  have hpos_i₁ : 0 < dmem i₁ :=
    natDegree_pos_of_irreducibleCharacter_apply_one_eq (hmemone i₁ hi₁)
  have hterm_pos : 0 < dmem i₁ * dmem i₁ := Nat.mul_pos hpos_i₁ hpos_i₁
  have hsum_pos : 0 < ∑ i ∈ s, dmem i * dmem i := by
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨i₁, hi₁, hterm_pos⟩
  exact hDsum ▸ hsum_pos

/-- A common-index factorization of every member degree makes the common-index square divide the
member degree square sum. -/
theorem sq_dvd_natDegreeSquareSum_of_commonIndex
    {ι : Type*} {s : Finset ι} {idx D : ℕ}
    {dmem θmem : ι → ℕ}
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hdmem : ∀ i ∈ s, dmem i = idx * θmem i) :
    idx * idx ∣ D := by
  rw [← hDsum]
  apply Finset.dvd_sum
  intro i hi
  refine ⟨θmem i * θmem i, ?_⟩
  rw [hdmem i hi]
  ring



end OddOrder.Peterfalvi.S08
